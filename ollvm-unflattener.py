# MiasmUnflattener/__init__.py or main.py

import ida_idaapi
import ida_kernwin
import ida_funcs
import ida_bytes
import ida_auto
import ida_nalt    # For get_imagebase
import ida_segment # For segment handling
import idc         # For legacy IDA API fallbacks
import ida_ida
import idaapi

import sys
import os
import io          # For potential memory stream handling later
import logging     # Use standard logging for unflattener core


from miasm.core.locationdb import LocationDB
from miasm.analysis.binary import Container

from MiasmUnflattener.unflattener import Unflattener

# --- Configuration ---
PLUGIN_NAME = "OLLVM Unflattener"
PLUGIN_VERSION = "1.0.0" # Version update for completion
PLUGIN_AUTHOR = "maskelihileci"
UNFLATTENER_AUTHOR = "cdong1012 -> https://github.com/cdong1012"
PLUGIN_COMMENT = "Unflattens OLLVM control flow flattening using Miasm."
PLUGIN_HELP = "Right-click on a function start or inside a function in Disassembly or Functions view."
WANTED_HOTKEY = "" # Assign hotkey later if desired

# Action names (must be unique)
ACTION_UNFLATTEN = "miasm_unflattener:unflatten"
ACTION_UNFLATTEN_RECURSIVE = "miasm_unflattener:unflatten_recursive"

# --- Logging Setup ---
# Configure logging to send messages from the unflattener core to IDA output window
core_logger = logging.getLogger("unflattener") # Match the logger name in unflattener.py
logger = logging.getLogger(__name__)
# Clear existing handlers if any during reload
for handler in core_logger.handlers[:]:
    core_logger.removeHandler(handler)

ida_handler = None # Define globally to remove in term()
class IdaLogHandler(logging.Handler):
    def emit(self, record):
        try:
            log_entry = self.format(record)
            if record.levelno >= logging.ERROR: ida_kernwin.warning(f"[{record.name}] {log_entry}\n")
            elif record.levelno >= logging.WARNING: ida_kernwin.warning(f"[{record.name}] {log_entry}\n")
            elif record.levelno >= logging.INFO: ida_kernwin.msg(f"[{record.name}] {log_entry}\n")
            else: ida_kernwin.msg(f"[{record.name}] DEBUG: {log_entry}\n")
        except Exception as e: print(f"Error in IdaLogHandler: {e}")

log_formatter = logging.Formatter('%(levelname)s: %(message)s')
ida_handler = IdaLogHandler()
ida_handler.setFormatter(log_formatter)
core_logger.addHandler(ida_handler)
core_logger.setLevel(logging.DEBUG) # Set default level to DEBUG for more details
core_logger.propagate = False

# --- Check for Miasm Dependency and Load Unflattener ---
MIASM_AVAILABLE = True


# --- Action Handlers ---
class UnflattenActionHandler(ida_kernwin.action_handler_t):
    def __init__(self, recursive=False):  # -> Sınıfın yapıcı metodu, recursive parametresi alır
        ida_kernwin.action_handler_t.__init__(self)  # -> Üst sınıfın yapıcısını çağırır
        self.recursive = recursive  # -> Recursive işlem yapılıp yapılmayacağını saklar
        self.action_name = ACTION_UNFLATTEN_RECURSIVE if recursive else ACTION_UNFLATTEN  # -> Aksiyon ismini recursive durumuna göre ayarlar


    def set_ida_context(self,unflattener_instance, code_start_va: int, code_size: int, image_base: int):
        """Set IDA Pro segment information and calculate binary_base_va."""
        logger.debug(f"Setting IDA context: start_va=0x{code_start_va:X}, size=0x{code_size:X}, image_base=0x{image_base:X}")
        unflattener_instance.code_start_va = code_start_va
        unflattener_instance.code_size = code_size
        unflattener_instance.image_base = image_base
        # binary_base_va'yı doğru şekilde ayarla
        # IDA VA'sı ile Miasm offset'i arasındaki fark
        if hasattr(unflattener_instance.container, 'bin_stream') and hasattr(unflattener_instance.container.bin_stream, 'offset'):
          unflattener_instance.binary_base_va = unflattener_instance.code_start_va - unflattener_instance.container.bin_stream.offset
        else:
          unflattener_instance.binary_base_va = unflattener_instance.image_base
        logger.debug(f"Set binary_base_va for VA conversion: 0x{unflattener_instance.binary_base_va:X} (code_start_va: 0x{unflattener_instance.code_start_va:X})")
        logger.debug(f"Set binary_base_va for VA conversion: 0x{unflattener_instance.binary_base_va:X}")

        unflattener_instance.text_section_range['lower'] = code_start_va
        unflattener_instance.text_section_range['upper'] = code_start_va + code_size
        logger.debug(f"Text section range (approx): 0x{unflattener_instance.text_section_range['lower']:X} - 0x{unflattener_instance.text_section_range['upper']:X}")



    def get_all_bytes_from_segments(self):  # -> Tüm segmentlerden byte verilerini alan fonksiyon
        """Gets all bytes from all segments."""  # -> Açıklama
        all_bytes = b""  # -> Tüm segmentlerin birleşik byte verisi
        min_ea = idaapi.BADADDR  # -> Segmentlerin en küçük adresi, başlangıçta BADADDR
        max_ea = 0  # -> Segmentlerin en büyük adresi, başlangıçta sıfır
        for i in range(ida_segment.get_segm_qty()):  # -> Segment sayısı kadar döngü
            seg = ida_segment.getnseg(i)  # -> i. segmenti al
            if not seg:  # -> Segment yoksa
                continue  # -> Sonraki segmente geç
            seg_bytes = ida_bytes.get_bytes(seg.start_ea, seg.end_ea - seg.start_ea)  # -> Segmentin tüm byte verisini al
            if seg_bytes is None:  # -> Veri alınamazsa
                continue  # -> Sonraki segmente geç
            all_bytes += seg_bytes  # -> Segment verisini tüm verilere ekle
            if seg.start_ea < min_ea:  # -> Segmentin başlangıcı mevcut minimumdan küçükse
                min_ea = seg.start_ea  # -> Yeni minimum yap
            if seg.end_ea > max_ea:  # -> Segmentin sonu mevcut maksimumdan büyükse
                max_ea = seg.end_ea  # -> Yeni maksimum yap
        return all_bytes, min_ea, max_ea  # -> Tüm veriyi, minimum ve maksimum adresleri döner

    def get_full_input_file_bytes(self):  # -> PE dosyasının tamamını okuyan fonksiyon
        """PE dosyasının tamamını okur."""  # -> Açıklama
        import os  # -> os modülünü içeri aktar
        pe_path = ida_nalt.get_input_file_path()  # -> IDA'da açık olan dosyanın yolunu al
        if not os.path.isfile(pe_path):  # -> Dosya mevcut değilse
            raise RuntimeError(f"PE dosyası bulunamadı: {pe_path}")  # -> Hata fırlat
        with open(pe_path, 'rb') as f:  # -> Dosyayı ikili okuma modunda aç
            data = f.read()  # -> Tüm içeriği oku
        return data  # -> Okunan byte verisini döner

    def activate(self, ctx):
        """Called when the action is triggered."""
        prefix = f"{PLUGIN_NAME} ({'Recursive' if self.recursive else 'Single'}): "
        
        try:
            # Get target function
            target_address = self._get_target_function(ctx)
            if target_address == ida_idaapi.BADADDR:
                return 0

            # Show wait box
            ida_kernwin.show_wait_box(f"HIDECANCEL\n{PLUGIN_NAME}: Processing...")

            # Get all binary data
            ida_kernwin.msg(f"{prefix}Reading binary data...\n")
            binary_data = self.get_full_input_file_bytes()
            _, min_ea, max_ea = self.get_all_bytes_from_segments()
            if not binary_data:
                raise RuntimeError("Failed to read binary data from segments")

            # Create LocationDB and stream
            self.loc_db: LocationDB = LocationDB()
            stream = io.BytesIO(binary_data)
            
            # Get architecture info
            info = ida_ida.inf_get_procname().lower()
            if info.startswith("metapc"):
                arch = "x86_64" if ida_ida.inf_is_64bit() else "x86_32"
            elif info.startswith("arm"):
                arch = "aarch64" if ida_ida.inf_is_64bit() else "arm"
                 
                
            ida_kernwin.msg(f"{prefix}Architecture: {arch}\n")
            
            # Create container 
            container = Container.from_stream(stream, self.loc_db)
            
            # Create unflattener instance
            unflattener_instance = Unflattener(container, binary_data , arch=arch)
            self.set_ida_context(unflattener_instance,min_ea, len(binary_data), ida_nalt.get_imagebase())
            
            # Process function
            if not self.recursive:
                print("single_function_start")
                result = self._process_single_function(unflattener_instance, target_address)
            else:
                print("_process_recursive_start")
                result = self._process_recursive(unflattener_instance, target_address)

            return 1 if result else 0

        except Exception as e:
            core_logger.exception("Error in activate")
            ida_kernwin.warning(f"{prefix}Error: {str(e)}")
            return 0
        finally:
            ida_kernwin.hide_wait_box()

    def update(self, ctx):
        """Enable/disable action based on context."""
        # Enable only if Miasm loaded OK and we are in a suitable view/context
        if MIASM_AVAILABLE:
             widget_type = ida_kernwin.get_widget_type(ctx.widget)
             if widget_type in [ida_kernwin.BWN_DISASM, ida_kernwin.BWN_FUNCS]:
                 ea = ctx.cur_ea;
                 if ea == ida_idaapi.BADADDR: ea = ida_kernwin.get_screen_ea()
                 if ea != ida_idaapi.BADADDR and ida_funcs.get_func(ea): return ida_kernwin.AST_ENABLE_FOR_WIDGET
                 elif widget_type == ida_kernwin.BWN_FUNCS:
                     sel = ida_kernwin.get_highlight(ctx.widget);
                     if sel and sel[0]: return ida_kernwin.AST_ENABLE_FOR_WIDGET
        return ida_kernwin.AST_DISABLE_FOR_WIDGET

    def _get_target_function(self, ctx) -> int:
        """Gets the target function address from context or user selection."""
        try:
            # First try to get address from context
            if ctx.cur_func:
                return ctx.cur_func.start_ea
            
            # Try to get from current screen position
            ea = ida_kernwin.get_screen_ea()
            if ea != ida_idaapi.BADADDR:
                func = ida_funcs.get_func(ea)
                if func:
                    return func.start_ea
            
            # If no valid address found, ask user
            target = ida_kernwin.ask_addr(
                ida_idaapi.BADADDR,
                "Please enter function start address (hex)"
            )
            
            if target != ida_idaapi.BADADDR:
                func = ida_funcs.get_func(target)
                if func:
                    return func.start_ea
                else:
                    ida_kernwin.warning(f"{PLUGIN_NAME}: Address 0x{target:X} is not a function start.")
            
            return ida_idaapi.BADADDR
            
        except Exception as e:
            core_logger.error(f"Error getting target function: {e}")
            return ida_idaapi.BADADDR

    def get_interval_hull(self,func_interval):
        """
        Calculates the hull (min start, max end) from various interval representations.

        Args:
            func_interval: Can be an object with .hull(), a list/tuple of (start, end),
                        or an intervaltree Interval object.

        Returns:
            tuple[int, int] | None: (hull_start, hull_end) or None if invalid.
        """
        if hasattr(func_interval, 'hull') and callable(func_interval.hull):
            # intervaltree.IntervalTree likely
            hull = func_interval.hull()
            if hull:
                return int(hull[0]), int(hull[1]) # hull() returns [begin, end)
            else:
                logger.warning("func_interval.hull() returned empty.")
                return None
        elif hasattr(func_interval, 'begin') and hasattr(func_interval, 'end'):
            # intervaltree.Interval likely
            return int(func_interval.begin), int(func_interval.end)
        elif isinstance(func_interval, (list, tuple)):
            if not func_interval:
                logger.warning("func_interval list/tuple is empty.")
                return None
            # Check if it's a single interval [start, end] or [(start, end)]
            if len(func_interval) == 2 and isinstance(func_interval[0], int) and isinstance(func_interval[1], int):
                # Assume it's a single interval [start, end]
                return int(func_interval[0]), int(func_interval[1])
            elif all(isinstance(item, (list, tuple)) and len(item) == 2 for item in func_interval):
                # List of intervals [(start1, end1), (start2, end2), ...]
                min_start = min(int(iv[0]) for iv in func_interval)
                max_end = max(int(iv[1]) for iv in func_interval)
                return min_start, max_end
            else:
                logger.error(f"Unrecognized format within func_interval list/tuple: {func_interval}")
                return None
        else:
            logger.error(f"Cannot determine hull from func_interval type: {type(func_interval)}")
            return None


    def apply_ida_patches(self, unflattener_obj: Unflattener, target_address: int, mode_all: bool):
        """
        Temizlenmiş fonksiyon kodunu doğrudan IDA'ya yamalar. Tek veya çoklu fonksiyon
        modunu destekler. Yama öncesi temizlik, yama sonrası analiz ve fonksiyon
        tanımlama adımlarını içerir. (ida_auto kullanımı düzeltildi)

        Args:
            unflattener_obj (Unflattener): Unflattener sınıfından nesne.
            target_address (int): Yeniden inşa edilecek ilk fonksiyonun başlangıç adresi.
            mode_all (bool): True ise `unflat_follow_calls` ile erişilebilir tüm
                             flatten edilmiş fonksiyonları bulur ve yamalar. False ise
                             sadece `target_address`'teki fonksiyonu yamalar.
        """
        logger.info(f"Starting rebuild process. Target: 0x{target_address:X}, Mode All: {mode_all}")

        patch_data_to_process = [] # İşlenecek (patch_bytes, func_interval, original_ea) tuple listesi

        try:
            # 1. Yama verisini al (Bu kısım aynı kaldı)
            if not mode_all:
                logger.info(f"Attempting to unflatten single function at 0x{target_address:X}")
                patch_bytes, func_interval = unflattener_obj.unflat(target_address)
                if patch_bytes is not None and func_interval is not None:
                    patch_data_to_process = [(patch_bytes, func_interval, target_address)]
                # ... (hata/atlama logları) ...
            else:
                logger.info(f"Attempting to unflatten target 0x{target_address:X} and follow calls.")
                patch_data_list_raw = unflattener_obj.unflat_follow_calls(target_address, None)
                if patch_data_list_raw:
                    logger.info(f"Found {len(patch_data_list_raw)} potential functions via follow_calls.")
                    for item in patch_data_list_raw:
                        if isinstance(item, tuple) and len(item) == 3:
                            patch_data_to_process.append(item)
                        elif isinstance(item, tuple) and len(item) == 2:
                            logger.warning(f"Patch data missing original_ea, using None placeholder.")
                            patch_data_to_process.append((item[0], item[1], None))
                        else:
                            logger.error(f"Invalid item format from unflat_follow_calls: {item}. Skipping.")
                else:
                    logger.info(f"No functions found via follow_calls from 0x{target_address:X}.")
                    print(f"No functions found via follow_calls from 0x{target_address:X}.")

        except Exception as e:
            logger.error(f"Error during unflattening phase (target 0x{target_address:X}): {e}", exc_info=True)
            print(f"Error during unflattening phase for 0x{target_address:X}: {e}")
            return

        if not patch_data_to_process:
            logger.info("No valid patch data found. Exiting.")
            print("No patches to apply.")
            return
        
        num_functions_to_patch = len(patch_data_to_process)

        confirmation_message = (f"Found {num_functions_to_patch} function(s) to patch.\n"
                                    f"This will modify the database by undefining code, "
                                    f"filling with NOPs, applying patches, and re-analyzing.\n\n"
                                    f"Proceed with patching?")

        logger.info(f"Requesting user confirmation to patch {num_functions_to_patch} function(s).")
        # ask_yn: 1 = Yes, 0 = No, -1 = Cancel/Close
        # Varsayılan olarak 'No' seçili olsun (0)
        user_choice = ida_kernwin.ask_yn(0, confirmation_message)

        if user_choice != 1: # Eğer kullanıcı 'Yes' demediyse
            logger.info("User cancelled the patching operation.")
            print("Patching operation cancelled by user.")
            return # Fonksiyondan çık


        # --- Her fonksiyonun yama verisini işle ---
        total_patched_bytes = 0
        functions_patched_count = 0
        functions_failed_count = 0

        for patch_bytes, func_interval, original_ea in patch_data_to_process:

            current_target_desc = f"function (start unknown)"
            effective_start_addr = None
            if original_ea:
                current_target_desc = f"function originally at 0x{original_ea:X}"
                effective_start_addr = original_ea

            logger.info(f"--- Processing patch for {current_target_desc} ---")

            if not patch_bytes or not func_interval:
                 logger.warning(f"Skipping invalid data for {current_target_desc}.")
                 functions_failed_count += 1
                 continue

            # 2. Hull belirle (Bu kısım aynı kaldı)
            hull = self.get_interval_hull(func_interval) # Placeholder - Gerçek kodu kullanın
            if hull is None:
                 logger.error(f"Could not determine hull for {current_target_desc}. Trying fallback.")
                 # ... (Fallback logic) ...
                 func = None
                 if original_ea: func = ida_funcs.get_func(original_ea)
                 if func:
                     hull = (func.start_ea, func.end_ea)
                     if effective_start_addr is None: effective_start_addr = func.start_ea
                     logger.warning(f"Using IDA bounds fallback: 0x{hull[0]:X}-0x{hull[1]:X}")
                     print(f"Warning: Using IDA bounds fallback for {current_target_desc}")
                 else:
                     logger.error(f"Fallback failed for {current_target_desc}. Cannot patch.")
                     print(f"Error: Fallback failed for {current_target_desc}. Cannot patch.")
                     functions_failed_count += 1
                     continue

            hull_start, hull_end = hull
            hull_length = hull_end - hull_start

            if effective_start_addr is None: # Hala başlangıç adresi yoksa hull başını kullan
                effective_start_addr = hull_start
                logger.warning(f"Using hull start 0x{hull_start:X} as effective start for {current_target_desc}")

            if hull_length <= 0:
                logger.error(f"Invalid hull range for {current_target_desc}. Skipping.")
                print(f"Error: Invalid hull range for {current_target_desc}. Skipping.")
                functions_failed_count += 1
                continue

            logger.info(f"Original hull: 0x{hull_start:X}-0x{hull_end:X}. Effective start: 0x{effective_start_addr:X}")


            # 3. Tanımları Kaldır, NOP'la ve Yama Yap (Bu kısım aynı kaldı)
            patch_len = len(patch_bytes)
            patching_succeeded = False
            try:
                logger.info(f"Undefining items in hull 0x{hull_start:X}-0x{hull_end:X}")
                ida_bytes.del_items(hull_start, ida_bytes.DELIT_SIMPLE, hull_length)

                nop_fill = b"\xCC" * hull_length
                ida_bytes.patch_bytes(hull_start, nop_fill)
                logger.info(f"Filled hull 0x{hull_start:X}-0x{hull_end:X} with 0xCC.")

                ida_bytes.patch_bytes(effective_start_addr, patch_bytes)
                hex_addr = f"0x{effective_start_addr:X}"
                # ... (Patch byte loglama) ...
                logger.info(f"Patched {patch_len} bytes at {hex_addr} for {current_target_desc}.")
                print(f"Patched {patch_len} bytes at {hex_addr} for {current_target_desc}")
                patching_succeeded = True

            except Exception as e:
                 logger.error(f"Error during patching phase for {current_target_desc}: {e}", exc_info=True)
                 print(f"Error during patching phase for {current_target_desc}: {e}")
                 functions_failed_count += 1
                 continue

            # 4. Yamalanan Alanı Yeniden Analiz Et ve Fonksiyonu Tanımla (DÜZELTİLDİ)
            analysis_succeeded = False
            if patching_succeeded:
                try:
                    # Adım 4a: Yamalanan alanı analiz kuyruğuna ekle
                    analysis_start = effective_start_addr
                    analysis_end = effective_start_addr + patch_len
                    logger.info(f"Requesting analysis for range 0x{analysis_start:X} - 0x{analysis_end:X}")
                    ida_auto.plan_range(analysis_start, analysis_end)

                    # Adım 4b: Analiz kuyruğunun işlenmesini bekle
                    logger.info("Waiting for autoanalysis to complete...")
                    ida_auto.auto_wait() # Bu fonksiyon analiz bitene kadar bekler
                    # auto_wait doğrudan başarı durumu döndürmez,
                    # eğer hata olmadan biterse başarılı varsayılır.
                    logger.info("Autoanalysis finished.")
                    analysis_succeeded = True # Hata fırlatmadıysa başarılı sayalım

                    # Adım 4c: Fonksiyonu yeniden tanımlamayı dene (analiz başarılıysa)
                    if analysis_succeeded:
                        # Eski tanımı sil (varsa ve farklıysa)
                        if original_ea and original_ea != analysis_start:
                            try:
                                if ida_funcs.del_func(original_ea): logger.info(f"Deleted old func at 0x{original_ea:X}")
                            except: pass # Hata olsa da devam et
                        elif ida_funcs.get_func(analysis_start): # Yeni adreste zaten varsa
                             try:
                                if ida_funcs.del_func(analysis_start): logger.info(f"Deleted existing func at 0x{analysis_start:X}")
                             except: pass

                        # Yeni fonksiyonu ekle
                        logger.info(f"Attempting to define function at 0x{analysis_start:X}")
                        try:
                            if ida_funcs.add_func(analysis_start, idc.BADADDR):
                                logger.info(f"Successfully defined function start at 0x{analysis_start:X}")
                            else:
                                logger.warning(f"Could not add function definition at 0x{analysis_start:X}")
                        except Exception as add_e:
                             logger.error(f"Error adding function at 0x{analysis_start:X}: {add_e}")
                    else:
                         # Bu durum auto_wait hata verirse veya ileride kontrol eklenirse olabilir.
                         logger.warning(f"Analysis was not considered successful for 0x{analysis_start:X}, skipping function definition.")


                except Exception as e:
                    logger.error(f"Error during analysis/definition phase for {current_target_desc}: {e}", exc_info=True)
                    print(f"Error during analysis/definition for {current_target_desc}: {e}")
                    # Analiz/tanımlama başarısız olsa bile patch uygulanmış olabilir.

            # 5. Bu fonksiyon için özeti logla (Bu kısım aynı kaldı)
            if patching_succeeded:
                if analysis_succeeded:
                    logger.info(f"Successfully patched and analyzed {current_target_desc}. Patch size: {patch_len} bytes.")
                    functions_patched_count += 1
                else:
                    logger.warning(f"Patched {current_target_desc} (size {patch_len}), but analysis failed/skipped.")
                    functions_patched_count += 1 # Yama yapıldıysa yine de başarılı sayabiliriz

                total_patched_bytes += patch_len
                # ... (Patch boyutu ve hull karşılaştırma logları) ...

            # --- Tek bir fonksiyon için döngü sonu ---

        # --- Genel Özet ---
        logger.info("="*40)
        logger.info(f"Patching process finished.")
        logger.info(f"Successfully patched functions: {functions_patched_count}")
        if functions_failed_count > 0:
             logger.warning(f"Failed/Skipped functions: {functions_failed_count}")
        logger.info(f"Total bytes written in patches: {total_patched_bytes}")
        print("="*40)
        print(f"Patching process finished.")
        print(f"Successfully patched: {functions_patched_count}")
        if functions_failed_count > 0:
             print(f"Failed/Skipped: {functions_failed_count}")
        print(f"Total patch bytes written: {total_patched_bytes}")
        logger.info("="*40)


    def _process_single_function(self, unflattener, target_address: int) -> bool:
        """Process a single function."""
        try:
            self.apply_ida_patches(unflattener, target_address,False)
            return True
        except Exception as e:
            core_logger.error(f"Error processing single function at 0x{target_address:X}: {e}")
            return False

    def _process_recursive(self, unflattener, target_address: int) -> bool:
        """Process function recursively including called functions."""
        try:
            # Özyinelemeli işlem için doğru patch toplama fonksiyonunu çağır
            # unflat_recursive_collect_patches, (patch_dict, interval) formatında liste döndürür.
            self.apply_ida_patches(unflattener,target_address,True)
            return True
        except Exception as e:
            core_logger.error(f"Error processing function recursively at 0x{target_address:X}: {e}")
            return False





# --- Hooks for Pop-up Menu ---
class GuiHooks(ida_kernwin.UI_Hooks):
    # ... (Function content identical to previous correct version) ...
    def finish_populating_widget_popup(self, widget, popup_handle):
        widget_type = ida_kernwin.get_widget_type(widget); menu_path = f"{PLUGIN_NAME}/"
        if widget_type in [ida_kernwin.BWN_DISASM, ida_kernwin.BWN_FUNCS]:
            if MIASM_AVAILABLE:
                ida_kernwin.attach_action_to_popup(widget, popup_handle, ACTION_UNFLATTEN, menu_path)
                ida_kernwin.attach_action_to_popup(widget, popup_handle, ACTION_UNFLATTEN_RECURSIVE, menu_path)


# --- Plugin Class ---
class MiasmUnflattenerPlugin(ida_idaapi.plugin_t):
    # ... (flags, comment, help, wanted_name, wanted_hotkey same) ...
    flags = ida_idaapi.PLUGIN_MOD | ida_idaapi.PLUGIN_PROC
    comment = PLUGIN_COMMENT; help = PLUGIN_HELP; wanted_name = PLUGIN_NAME; wanted_hotkey = WANTED_HOTKEY
    def __init__(self): self.hooks = None

    def init(self):
        """Called when IDA loads the plugin."""
        # ... (Function content identical to previous correct version) ...
        prefix = f"{PLUGIN_NAME} init v{PLUGIN_VERSION}: "; ida_kernwin.msg(f"\n{prefix}Initializing...\n")
        log_level_str = os.environ.get("MIASM_UNFLATTENER_LOGLEVEL", "INFO").upper(); log_level = getattr(logging, log_level_str, logging.INFO)
        core_logger.setLevel(logging.DEBUG)  # Set to DEBUG for more detailed output
        ida_kernwin.msg(f"  Core log level: {logging.getLevelName(core_logger.level)}\n")
        if not MIASM_AVAILABLE: ida_kernwin.warning(f"{prefix}Plugin disabled (missing dependencies).\n"); return ida_idaapi.PLUGIN_OK
        actions = [ ida_kernwin.action_desc_t(ACTION_UNFLATTEN, 'Unflatten Function', UnflattenActionHandler(False), WANTED_HOTKEY or None, 'Unflatten function using Miasm', 199),
                    ida_kernwin.action_desc_t(ACTION_UNFLATTEN_RECURSIVE, 'Unflatten Function (Recursive)', UnflattenActionHandler(True), None, 'Unflatten function and calls using Miasm', 199) ]
        register_ok = all(ida_kernwin.register_action(action) for action in actions)
        if not register_ok: ida_kernwin.warning(f"{prefix}Action registration failed. Skipping load.\n"); self.term(); return ida_idaapi.PLUGIN_SKIP
        try:
            self.hooks = GuiHooks()
            if not self.hooks.hook(): raise RuntimeError("UI Hook installation failed.")
            ida_kernwin.msg(f"{prefix}UI hooks installed.\n")
        except Exception as hook_ex:
             ida_kernwin.warning(f"{prefix}UI hook exception: {hook_ex}. Cleaning up.\n"); core_logger.exception("UI Hook failed")
             if self.hooks: self.hooks.unhook(); self.hooks = None
             self.term(); return ida_idaapi.PLUGIN_SKIP
        ida_kernwin.msg(f"{prefix}Initialization complete.\n"); return ida_idaapi.PLUGIN_KEEP

    def run(self, arg):
        """Called from Edit/Plugins menu."""
        # ... (Function content identical to previous correct version) ...
        ida_kernwin.info(f"{PLUGIN_NAME} v{PLUGIN_VERSION}\nUse right-click menus.")

    def term(self):
        """Called when IDA unloads the plugin."""
        # ... (Function content identical to previous correct version) ...
        prefix = f"{PLUGIN_NAME} term: "; ida_kernwin.msg(f"\n{prefix}Unloading...\n")
        if self.hooks:
            try: self.hooks.unhook(); # ida_kernwin.msg(f"{prefix}UI hooks removed.\n")
            except Exception: pass
            self.hooks = None
        for action_name in [ACTION_UNFLATTEN, ACTION_UNFLATTEN_RECURSIVE]: ida_kernwin.unregister_action(action_name)
        plugin_dir = os.path.dirname(__file__)
        if plugin_dir in sys.path:
            try: sys.path.remove(plugin_dir)
            except ValueError: pass
        global core_logger, ida_handler
        if core_logger and ida_handler:
            try: core_logger.removeHandler(ida_handler); ida_handler = None
            except Exception: pass
        ida_kernwin.msg(f"{prefix}Unloaded.\n")

# --- Plugin Entry Point ---
def PLUGIN_ENTRY():
    return MiasmUnflattenerPlugin()