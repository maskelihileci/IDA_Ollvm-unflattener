from collections import defaultdict
import pprint
from typing import List
from miasm.core.locationdb import LocationDB
from miasm.analysis.binary import Container
import logging as logger
from miasm.analysis.machine import Machine
from miasm.core.asmblock import AsmCFG, AsmBlock
from miasm.ir.ir import IRCFG
from miasm.arch.ppc.regs import *
from miasm.analysis.simplifier import *
from miasm.expression.expression import *
from miasm.ir.symbexec import SymbolicExecutionEngine
import graphviz
from miasm.arch.x86.arch import instruction_x86, mn_x86
from miasm.arch.x86.disasm import dis_x86_32
from miasm.core.interval import interval
from miasm.loader.elf_init import ELF
from miasm.loader.pe_init import PE
from MiasmUnflattener.binrewrite import BinaryRewriter

from typing import List, Tuple, Optional, Dict, Set

def calc_flattening_score(asm_graph: AsmCFG) -> float:  # -> Bir fonksiyonun flattening (düzleştirme) skorunu hesaplar
    """Function to calculate flatenning score  # -> Flattening skorunu hesaplayan fonksiyon

    https://gist.github.com/mrphrazer/da32217f231e1dd842986f94aa6d9d37#file-flattening_heuristic-py  # -> Kullanılan algoritmanın kaynağı

    Args:  # -> Parametreler
        asm_graph (AsmCFG): Function's asm CFG  # -> Fonksiyonun assembly kontrol akış grafiği

    Returns:  # -> Dönen değer
        float: Function's flattening score  # -> Fonksiyonun flattening skoru
    """
    
    # init score  # -> Skor değişkeni başlatılır
    score = 0.0  # -> Başlangıçta skor 0.0
    
    # walk over all entry nodes in the graph  # -> CFG'deki tüm giriş noktaları üzerinde döner
    for head in asm_graph.heads_iter():  # -> Her giriş noktası için
        # since miasm breaks basic block into multiple ones separated by CALL instruction  # -> miasm, CALL komutlarında blokları böldüğü için
        # need to move this head to the final successor whose last instruction is not a CALL instruction  # -> CALL ile bitmeyen son ardıla kadar ilerlemek gerekir
        # basically the tail of this head block  # -> Bu, giriş bloğunun kuyruğu olur
        skipped_head_loc_count = 0  # -> Atlanan CALL blok sayısı sayacı
        while asm_graph.loc_key_to_block(head).lines[-1].name == 'CALL':  # -> Son komut CALL ise
            skipped_head_loc_count += 1  # -> Sayaç artırılır
            head = asm_graph.successors(head)[0]  # -> İlk ardıla geçilir
        
        # compute dominator tree  # -> Bu giriş noktası için dominator ağacı hesaplanır
        dominator_tree = asm_graph.compute_dominator_tree(head)  # -> Dominator ağacı alınır
        
        # walk over all basic blocks  # -> Tüm temel bloklar üzerinde döner
        for block in asm_graph.blocks:  # -> Her blok için
            # get location key for basic block via basic block address  # -> Blok adresinden konum anahtarı alınır
            block_key = asm_graph.loc_db.get_offset_location(block.lines[0].offset)  # -> Blok konum anahtarı
            
            # get all blocks that are dominated by the current block  # -> Bu blok tarafından domine edilen tüm bloklar alınır
            dominated = set(  # -> Domine edilen bloklar kümesi
                [block_key] + [b for b in dominator_tree.walk_depth_first_forward(block_key)])  # -> Blok ve onun altındaki tüm bloklar
            
            # check for a back edge  # -> Döngü oluşturan geri kenar var mı kontrol edilir
            if not any([b in dominated for b in asm_graph.predecessors(block_key)]):  # -> Eğer geri kenar yoksa
                continue  # -> Bu blok atlanır
            
            # calculate relation of dominated blocks to the blocks in the graph  # -> Domine edilen blokların toplam bloğa oranı hesaplanır
            score = max(score, len(dominated)/(len(asm_graph.nodes()) - skipped_head_loc_count))  # -> Skor, mevcut skor ve yeni oranın maksimumu olur
    return score  # -> Hesaplanan flattening skoru döndürülür

class Unflattener:
    """
    Class for the unflattener engine
    """
    
    def __init__(self, container: Container, binary_data: bytes , arch: str):
        """Constructor for the unflattener engine

        Args:
            filename (str): deobfuscated binary path
        """

        self.container = container
        self.binary_data = binary_data
        self.loc_db = container.loc_db
        self.arch = arch

        self.code_start_va: Optional[int] = None
        self.code_size: Optional[int] = None
        self.image_base: Optional[int] = None
        self.patches: Optional[Dict[int, bytes]] = None
        self.func_interval: Optional[interval] = None
        self.text_section_range: Dict[str, int] = {'lower': 0, 'upper': 0}

        
        self.machine: Machine = Machine(self.container.arch)
        self.mdis = self.machine.dis_engine(self.container.bin_stream, loc_db=self.loc_db)
        self.original_filename: str = None
        self.flatten_func_queue: list = []
        self.flatten_func_encountered: list = []
        self.text_section_Shdr = None  # Store section header for later use
        self.binary_base_va = None     # Store binary base virtual address
    
    def unflat(self, target_address: int) -> tuple[bytes, interval]:
        """Unflatten the CFG of a function

        Args:
            target_address (int): Target function address
        Returns:
            tuple[bytes, interval]: Function patch & function interval
        """
        
        # get text section range & binary base virtual address
        if isinstance(self.container.executable, PE):
            text_section_Shdr = self.container.executable.getsectionbyvad(target_address)
            self.binary_base_va = self.container.executable.NThdr.ImageBase + (text_section_Shdr.addr - text_section_Shdr.offset)
            self.text_section_range = {'lower': self.container.executable.NThdr.ImageBase + text_section_Shdr.addr,
                                       'upper': self.container.executable.NThdr.ImageBase + text_section_Shdr.addr + text_section_Shdr.size}
        elif isinstance(self.container.executable, ELF):
            text_section_Shdr = self.container.executable.getsectionbyvad(target_address).sh
            self.binary_base_va = text_section_Shdr.addr - text_section_Shdr.offset
            
            self.text_section_range = {'lower': text_section_Shdr.addr,
                                       'upper': text_section_Shdr.addr + text_section_Shdr.size}
        else:
            raise Exception('Unsupported binary type')

        self.asmcfg: AsmCFG = self.mdis.dis_multiblock(target_address)
        self.lifter = self.machine.lifter_model_call(self.mdis.loc_db)
        self.ircfg: IRCFG = self.lifter.new_ircfg_from_asmcfg(self.asmcfg)
        score = calc_flattening_score(self.asmcfg)
        
        if score < 0.9:
            return (None, None)
        patch = self.recover_CFG(target_address)
        func_interval = interval(block.get_range() for block in self.asmcfg.blocks)
        return (patch, func_interval)
    
    def unflat_follow_calls(self, target_address: int, out_filename: str) -> list[tuple[bytes, interval]]:  # -> Hedef fonksiyonu ve çağırdığı diğer obfuscate edilmiş fonksiyonları unflatten eder
        """Unflat the target function & all calls to unflat other obfuscated functions   # -> Hedef fonksiyon ve çağrılan diğer obfuscate edilmiş fonksiyonları unflatten eder
     
        Args:  # -> Parametreler
            target_address (int): Target function address  # -> Hedef fonksiyon adresi
            out_filename (str): Deobfuscate edilmiş çıktı dosya yolu  # -> Çıktı dosya yolu
        Returns:  # -> Dönen değer
            list[tuple[bytes, interval]]: List of function patch & function interval  # -> Fonksiyon yamaları ve aralıkları listesi
        """
        self.flatten_func_queue: list[int] = [target_address]  # -> İşlem kuyruğu, ilk olarak hedef fonksiyon adresi eklenir
        processed_flatten_func_list: list[int] = []  # -> İşlenmiş fonksiyon adresleri listesi
        
        patch_data_list: list[tuple[bytes, interval]] = []  # -> Yama ve aralık listesini tutar
        while len(self.flatten_func_queue) != 0:  # -> Kuyruk boşalana kadar devam et
            flatten_func_addr = self.flatten_func_queue.pop()  # -> Kuyruktan bir fonksiyon adresi al
            
            if flatten_func_addr in processed_flatten_func_list:  # -> Eğer bu fonksiyon daha önce işlendiyse
                # do not try to flatten the same function again  # -> Aynı fonksiyonu tekrar unflatten etme
                continue  # -> Atla
            
            logger.info("Unflattening function {}".format(hex(flatten_func_addr)))  # -> Logla
            try:
                patch, func_interval = self.unflat(flatten_func_addr)  # -> Fonksiyonu unflatten et
                if patch is not None:  # -> Eğer yama üretildiyse
                    logger.info("Generate patch for {} successfully".format(hex(target_address)))  # -> Başarı logu
                    patch_data_list.append((patch, func_interval))  # -> Listeye ekle
                else:  # -> Eğer yama yoksa
                    logger.info("Function {} is not flattened".format(hex(target_address)))  # -> Zaten flatten edilmemiş logu
            except:  # -> Hata olursa
                logger.info("Fail to unflat function {}".format(hex(flatten_func_addr)))  # -> Başarısız logu
        return patch_data_list  # -> Tüm yamalar ve aralıklar listesi döndürülür
    
    def render(self, dot_filename: str, image_filename: str):  # -> CFG'yi DOT ve PNG dosyasına render eder
        """Render the function's CFG into a DOT and PNG file  # -> Fonksiyonun CFG'sini DOT ve PNG dosyasına çizer
     
        Args:  # -> Parametreler
            dot_filename (str): DOT file path  # -> DOT dosya yolu
            image_filename (str): PNG file path  # -> PNG dosya yolu
        """
        with open(dot_filename, 'w') as f:  # -> DOT dosyasını yazmak için aç
            f.write(self.asmcfg.dot())  # -> CFG'yi DOT formatında dosyaya yaz
        graphviz.render('dot', 'png', dot_filename, outfile=image_filename)  # -> DOT dosyasını PNG'ye dönüştür
    
    def print_block(self, loc_key: LocKey):  # -> Belirtilen konumdaki bloğu yazdırır
        """Print a block at the specified location  # -> Belirtilen konumdaki bloğu yazdırır
     
        Args:  # -> Parametreler
            loc_key (LocKey): Location key  # -> Blok konum anahtarı
        """
        print('{} {}'.format(str(loc_key), str(self.asmcfg.loc_key_to_block(loc_key))))  # -> loc_key ve karşılık gelen blok bilgisini yazdırır
    
    def to_loc_key(self, expr) -> LocKey:  # -> Bir ifadeyi konum anahtarına çevirir
        """Convert an expression into a location key  # -> İfadeyi konum anahtarına dönüştürür
     
        Args:  # -> Parametreler
            expr : Target expression  # -> Hedef ifade
     
        Returns:  # -> Dönen değer
            LocKey: Location key  # -> Konum anahtarı
        """
        if isinstance(expr, LocKey):  # -> Eğer zaten LocKey ise
            return expr  # -> Olduğu gibi döndür
        if isinstance(expr, ExprLoc):  # -> Eğer ExprLoc ise
            return expr.loc_key  # -> İçindeki loc_key'i döndür
        if isinstance(expr, ExprInt):
            return self.container.loc_db.get_offset_location(int(expr))
        if isinstance(expr, int):
            return self.container.loc_db.get_offset_location(expr)
        return None

    def find_backbone_blocks(self, predispatcher_loc: LocKey) -> List[LocKey]:  # -> Omurga bloklarını (orijinal programdan kod içeren bloklar) bulur
        """Find all backbone blocks (blocks with code from the original program)  # -> Omurga bloklarını bulur
    
        Args:  # -> Parametreler
            predispatcher_loc (LocKey): predispatcher konum anahtarı  # -> predispatcher bloğunun konum anahtarı
    
        Returns:  # -> Dönen değer
            List[LocKey]: List of backbone location keys  # -> Omurga bloklarının konum anahtarları listesi
        """
        backbone_blocks = []  # -> Omurga bloklarını tutacak liste
        for block_loc in self.asmcfg.predecessors(predispatcher_loc):  # -> predispatcher'ın tüm ebeveyn blokları için
            # each parent block of the predispatcher is a backbone block  # -> Her ebeveyn blok bir omurga bloğudur
            last_predecessor_loc = block_loc  # -> Son ebeveyn konumu
            curr_predecessor_loc = self.asmcfg.predecessors(block_loc)[0]  # -> Bu bloğun ebeveyni
            backbone_blocks.append(last_predecessor_loc)  # -> Omurga listesine eklenir
            
            # traverse upward from each backbone block to find all backbone blocks above it  # -> Yukarı doğru tüm omurga bloklarını bulmak için gezin
            # this is due to CALL instructions breaking up basic block into multiple ones  # -> CALL komutları temel blokları böldüğü için
            while True:  # -> Sonsuz döngü, çıkış içeride
                curr_predecessor_block = self.asmcfg.loc_key_to_block(curr_predecessor_loc)  # -> Ebeveyn blok alınır
                if curr_predecessor_block.lines[-1].name in ['JZ', 'JMP', 'JNZ']:  # -> Son komut dallanma ise
                    break  # -> Döngüden çık
                backbone_blocks.append(curr_predecessor_loc)  # -> Omurga listesine ekle
                curr_predecessor_loc = self.asmcfg.predecessors(curr_predecessor_loc)[0]  # -> Bir üst ebeveyne geç
            
        # add function's tail (block with no successor) to backbone blocks  # -> Fonksiyonun kuyruğu (ardılı olmayan blok) omurgaya eklenir
        for block in self.asmcfg.blocks:  # -> Tüm bloklar için
            if len(self.asmcfg.successors(block.loc_key)) == 0:  # -> Eğer ardılı yoksa (son blok)
                last_tail_loc = block.loc_key  # -> Kuyruk bloğu konumu
                backbone_blocks.append(last_tail_loc)  # -> Omurgaya ekle
                
                # traverse upward from each backbone block to find all backbone blocks above it  # -> Yukarı doğru tüm omurga bloklarını bulmak için gezin
                # this is due to CALL instructions breaking up basic block into multiple ones  # -> CALL komutları temel blokları böldüğü için
                curr_predecessor_tail_loc = self.asmcfg.predecessors(last_tail_loc)[0]  # -> Kuyruk bloğun ebeveyni
                while True:  # -> Sonsuz döngü
                    curr_predecessor_tail_block = self.asmcfg.loc_key_to_block(curr_predecessor_tail_loc)  # -> Ebeveyn blok alınır
                    if curr_predecessor_tail_block.lines[-1].name in ['JZ', 'JMP', 'JNZ']:  # -> Son komut dallanma ise
                        break  # -> Döngüden çık
                    backbone_blocks.append(curr_predecessor_tail_loc)  # -> Omurgaya ekle
                    curr_predecessor_tail_loc = self.asmcfg.predecessors(curr_predecessor_tail_loc)[0]  # -> Bir üst ebeveyne geç
    
        return backbone_blocks  # -> Omurga bloklarının listesi döndürülür

    def symbex_block(self, symbex_engine: SymbolicExecutionEngine, loc_key: LocKey) -> Expr:  # -> Bir bloğu sembolik olarak yürütür, sonuçta bir ifade döner
        """symbolically executing a block  # -> Bir bloğun sembolik yürütülmesi

        Args:  # -> Argümanlar
            symbex_engine (SymbolicExecutionEngine): Symbolic execution engine  # -> Sembolik yürütme motoru
            loc_key (LocKey): Location key to execute  # -> Yürütülecek blok konum anahtarı

        Returns:  # -> Dönen değer
            Expr: Result symbolic expression  # -> Sembolik yürütme sonucu ifade
        """
        curr_block = self.asmcfg.loc_key_to_block(loc_key)  # -> loc_key'e karşılık gelen assembly bloğu alınır
        
        if curr_block is None:  # -> Eğer blok yoksa
            return symbex_engine.run_block_at(self.ircfg, loc_key)  # -> IR seviyesinde bloğu çalıştır ve sonucu döndür
        
        # retrieve the cmp/test instruction & cmovcc instruction  # -> Blok içindeki CMP/TEST ve CMOVcc talimatlarını bul
        cmp_instruction = None  # -> CMP veya TEST komutu için değişken
        cmov_instruction = None  # -> CMOVcc komutu için değişken
        
        for instruction in curr_block.lines:  # -> Bloktaki tüm assembly komutlarını dolaş
            if instruction.name in ['CMP', 'TEST']:  # -> Eğer komut CMP veya TEST ise
                cmp_instruction = instruction  # -> cmp_instruction olarak ata
            if 'CMOV' in instruction.name:  # -> Eğer komut CMOV içeriyorsa
                cmov_instruction = instruction  # -> cmov_instruction olarak ata
                break  # -> İlk bulunan CMOV sonrası döngüden çık
        
        if curr_block.lines[-1].name == 'CALL':  # -> Eğer blok CALL komutuyla bitiyorsa
            # process call regularly but we reset RSP/RBP to old RSP/RBP instead   # -> Çağrıyı normal çalıştır ama RSP/RBP'yi eski haline getir
            #   of an ExprMem depending on miasm's call_func_stack  # -> miasm'ın call_func_stack'ine bağlı ExprMem yerine
            #   basically overwriting the execution result of the CALL IR instruction.  # -> CALL sonrası oluşan stack değişimini yok say
            #   Here, we assume that the CALL IR does not impact the stack pointer  # -> CALL komutunun stack pointer'ı değiştirmediği varsayılır
            original_rsp = symbex_engine.symbols[ExprId('RSP', 64)]  # -> RSP'nin orijinal değeri saklanır
            original_rbp = symbex_engine.symbols[ExprId('RBP', 64)]  # -> RBP'nin orijinal değeri saklanır
            original_esp = symbex_engine.symbols[ExprId('ESP', 32)]  # -> ESP'nin orijinal değeri saklanır
            original_ebp = symbex_engine.symbols[ExprId('EBP', 32)]  # -> EBP'nin orijinal değeri saklanır
            result = symbex_engine.run_block_at(self.ircfg, loc_key)  # -> Bloğu IR seviyesinde çalıştır
            if self.container.arch == 'x86_32':  # -> 32-bit mimari için
                symbex_engine.symbols[ExprId('ESP', 32)] = original_esp  # -> ESP eski haline getirilir
                symbex_engine.symbols[ExprId('EBP', 32)] = original_ebp  # -> EBP eski haline getirilir
            elif self.container.arch == 'x86_64':  # -> 64-bit mimari için
                symbex_engine.symbols[ExprId('RSP', 64)] = original_rsp  # -> RSP eski haline getirilir
                symbex_engine.symbols[ExprId('RBP', 64)] = original_rbp  # -> RBP eski haline getirilir
            return result  # -> Sonuç döndürülür
         
        # is an ollvm condition block if CMP instruction is followed by CMOVCC instruction  # -> Eğer CMP/TEST sonrası CMOVcc varsa, bu bir OLLVM koşul bloğudur
        if cmov_instruction is not None and cmp_instruction is not None\
            and curr_block.lines.index(cmp_instruction) < curr_block.lines.index(cmov_instruction):  # -> CMP, CMOV'dan önce geliyorsa
                curr_loc = loc_key  # -> Başlangıç konumu atanır

                while True:  # -> Sonsuz döngü, çıkış içeride
                    # continue to simulate to check each IR block  # -> Her IR bloğu için simülasyona devam
                    # this is because condition-generating instructions (idiv, cmov)  # -> Çünkü koşul üreten komutlar
                    #  split a single asm block into multiple IR blocks  # -> Tek bir assembly bloğunu birden fazla IR bloğuna böler
                    curr_ir_block: IRBlock = self.ircfg.get_block(curr_loc)  # -> Geçerli IR bloğu alınır
                    if curr_ir_block is None:  # -> Eğer IR bloğu yoksa
                        return symbex_engine.run_block_at(self.ircfg, loc_key)  # -> IR seviyesinde çalıştır ve sonucu döndür
                    
                    for assign_block in curr_ir_block:  # -> IR bloğundaki tüm atama bloklarını dolaş
                        # once found the IR assign block for the CMOV instruction  # -> CMOV komutuna karşılık gelen atama bloğu bulunduğunda
                        if 'CMOV' in assign_block.instr.name:  # -> Eğer atama CMOV içeriyorsa
                            # symbex the block as normal  # -> Bloğu normal şekilde sembolik yürüt
                            symbex_engine.run_block_at(self.ircfg, curr_loc)
                             
                            # NOTE: We don't return the condition produced by symbex_engine.run_block_at here.  # -> Burada sembolik yürütmenin ürettiği koşulu döndürmüyoruz
                            #   This is because if the condition is deterministic(in a for loop for example)  # -> Çünkü koşul deterministikse (örneğin döngüde)
                            #       symbex_engine.run_block_at will evaluate the cond automatically  # -> symbex otomatik olarak koşulu hesaplar
                            #       and return ExprInt for the address  # -> ve adres için ExprInt döner
                            #   We don't want this as we want to still split the IR path into two  # -> Biz ise IR yolunu ikiye bölmek istiyoruz
                            #       so we have to get the ExprCond directly from the assign block  # -> Bu yüzden koşulu doğrudan atama bloğundan almalıyız
                            cmov_cond_expr = assign_block.values()[-1]  # -> CMOV koşul ifadesi alınır
                             
                            # example: CMOVNZ -> JNZ  # -> Örnek: CMOVNZ, JNZ'ye karşılık gelir
                            if 'CMOVN' in cmov_instruction.name:  # -> CMOVN içeriyorsa
                                return cmov_cond_expr.copy()  # -> Koşul ifadesinin kopyası döndürülür
                             
                            # example: CMOVZ -> JZ   # -> Örnek: CMOVZ, JZ'ye karşılık gelir
                            # need to flip the condition src fields  # -> Koşulun kaynak alanları ters çevrilmeli
                            return ExprCond(cmov_cond_expr._cond.copy(),  # -> Koşul kopyalanır
                                cmov_cond_expr._src2.copy(),  # -> src2 kopyalanır (ters çevrilir)
                                cmov_cond_expr._src1.copy())  # -> src1 kopyalanır (ters çevrilir)
                    curr_loc = symbex_engine.run_block_at(self.ircfg, curr_loc)  # -> Sonraki IR bloğuna geç
                    continue  # -> Döngü devam etsin
        else:  # -> Eğer OLLVM koşul bloğu değilse
            # just a regular block, symbex normally  # -> Normal blok, sembolik yürütme yapılır
            return symbex_engine.run_block_at(self.ircfg, loc_key)  # -> Sonuç döndürülür
                    
    def recover_CFG(self, target_address: int):  # -> Kontrol akış grafiğini (CFG) geri kazanır
        """Recover the function's CFG  # -> Fonksiyonun CFG'sini geri kazanır
    
        Args:  # -> Argümanlar açıklaması
            target_address (int): Target function address  # -> Hedef fonksiyon adresi
        """  # -> Docstring sonu
        
        # predispatcher is the block with the most number of parents  # -> En çok ebeveyni olan blok predispatcher olarak seçilir
        predispatcher = sorted(self.asmcfg.blocks, key=lambda key: len(self.asmcfg.predecessors(key.loc_key)), reverse=True)[0]  # -> Blokları ebeveyn sayısına göre azalan sırayla sıralar, ilkini alır
        predispatcher_loc = predispatcher.loc_key  # -> predispatcher bloğunun konum anahtarı alınır

        # dispatcher is the only child of the predispatcher   # -> predispatcher'ın tek çocuğu dispatcher'dır
        dispatcher_loc = self.asmcfg.successors(predispatcher_loc)[0]  # -> predispatcher'ın ilk ardılı dispatcher olarak alınır
    
        # backbone: everything that is needed in the final asmcfg (except the head)  # -> Omurga blokları, son CFG'de gerekli tüm bloklar (baş hariç)
        backbone_loc_list = self.find_backbone_blocks(predispatcher_loc)  # -> predispatcher'dan başlayarak omurga bloklarını bulur

        # state var is the seceond expr in the first instructions of the dispatcher  # -> dispatcher'ın ilk komutundaki ikinci ifade, durum değişkenidir
        dispatcher_block = self.asmcfg.loc_key_to_block(dispatcher_loc)  # -> dispatcher bloğu alınır
        state_var_expr = dispatcher_block.lines[0].get_args_expr()[1]  # -> İlk satırdaki ikinci argüman (durum değişkeni) alınır
        logger.debug('State var: ' + str(state_var_expr))  # -> Durum değişkeni debug loguna yazılır

        # symbols for symbex  # -> Sembolik yürütme için başlangıç sembolleri
        init_symbols =  {}  # -> Boş sembol tablosu oluşturulur
        for i, r in enumerate(all_regs_ids):  # -> Tüm kayıtlar üzerinde döner
            init_symbols[r] = all_regs_ids_init[i]  # -> Her kaydın başlangıç değerini atar
        
        # parent loc -> [children loc]  # -> Ebeveyn konumdan çocuk konumlara harita
        loc_successors_map = defaultdict(list)  # -> Varsayılan boş liste olan sözlük
        
        # exec_queue: queue containing (address/loc to exec, symbex engine symbols, current state value)  # -> Yürütülecek konumlar, semboller ve durum değerleri kuyruğu
        exec_queue = []  # -> Boş kuyruk oluşturulur
        exec_queue.append((self.to_loc_key(target_address), init_symbols, None))  # -> Hedef adres, başlangıç sembolleri ve durum değeri None olarak kuyruğa eklenir
        
        # starting state val for traversal  # -> İlk durum değeri (başlangıçta None)
        first_state_val = None  # -> İlk durum değeri tanımlanır
        
        # curr state -> [next state/states]  # -> Mevcut durumdan sonraki durumlara harita
        state_order_map = defaultdict(list)  # -> Varsayılan boş liste olan sözlük
        
        # state value -> [loc key/loc keys]  # -> Durum değerinden konumlara harita
        state_to_lockey_map = defaultdict(list)  # -> Varsayılan boş liste olan sözlük
        
        # list to track all backbone blocks encountered  # -> Ziyaret edilen omurga bloklarının listesi
        backbone_encountered_list = []  # -> Boş liste oluşturulur

        while len(exec_queue) != 0:  # -> Kuyruk boşalana kadar döngü
            # pop a loc_key to start symbex  # -> Kuyruktan bir eleman çıkarılır
            curr_loc, symbols, curr_state_val = exec_queue.pop()  # -> Mevcut konum, semboller ve durum değeri alınır
            symbex_engine = SymbolicExecutionEngine(self.lifter, symbols)  # -> Yeni sembolik yürütme motoru başlatılır
            
            while True:  # -> Sonsuz döngü, çıkış koşulları içeride
                # if current loc is a backbone block   # -> Eğer mevcut blok omurga bloğuysa
                if curr_loc in backbone_loc_list:
                    if curr_loc in backbone_encountered_list:  # -> Daha önce ziyaret edildiyse
                        # if we already process all backbones, stop symbex  # -> Sembolik yürütmeyi durdur
                        break
                    backbone_encountered_list.append(curr_loc)  # -> Ziyaret edilenlere ekle
                    
                    # get the current value for the state variable  # -> Durum değişkeninin mevcut değeri alınır
                    curr_state_val = int(symbex_engine.eval_expr(state_var_expr))  # -> Durum değişkeni hesaplanır
                    
                    # map state val -> [current loc]  # -> Durum değerinden mevcut konuma haritalama yapılır
                    if curr_loc not in state_to_lockey_map[curr_state_val]:
                        state_to_lockey_map[curr_state_val].append(curr_loc)  # -> Listeye eklenir
                    
                    # get first state val for later traversal  # -> İlk durum değeri henüz alınmadıysa kaydedilir
                    if first_state_val is None:
                        first_state_val = curr_state_val  # -> İlk durum değeri atanır
                
                # predispatcher processing  # -> predispatcher bloğu işleniyor
                if curr_loc == predispatcher_loc:
                    # evaluate next state var   # -> Sonraki durum değişkeni hesaplanır
                    next_state_val = int(symbex_engine.eval_expr(state_var_expr))  # -> Yeni durum değeri alınır
                    
                    # map curr state val -> next state val  # -> Mevcut durumdan sonraki duruma haritalama yapılır
                    if next_state_val not in state_order_map[curr_state_val]:
                        state_order_map[curr_state_val].append(next_state_val)  # -> Listeye eklenir

                    # reset curr state val  # -> Mevcut durum değeri sıfırlanır
                    curr_state_val = None
                
                # for flatten while following calls  # -> Çağrıları takip ederken düzleştirme için
                # if this block ends with a CALL, extract the call destination and add to self.flatten_func_queue  # -> Eğer blok CALL ile bitiyorsa, hedef adresi al ve kuyruğa ekle
                curr_block = self.asmcfg.loc_key_to_block(curr_loc)  # -> Mevcut blok alınır
                if curr_block is not None:
                    last_instruction = curr_block.lines[-1]  # -> Son komut alınır
                    if last_instruction.name == 'CALL':  # -> Eğer komut CALL ise
                        destination_loc = symbex_engine.eval_expr(last_instruction.args[0])  # -> Çağrı hedefi hesaplanır
                        
                        if isinstance(destination_loc, ExprInt):  # -> Eğer hedef sabit sayı ise
                            destination_loc = int(destination_loc)  # -> Tam sayıya çevrilir
                            # only follows calls that are in the .text section only (avoid library calls)  # -> Sadece .text segmentindeki çağrılar takip edilir
                            if self.text_section_range['lower'] <= destination_loc <= self.text_section_range['upper']:
                                if destination_loc not in self.flatten_func_encountered:  # -> Daha önce takip edilmediyse
                                    self.flatten_func_queue.append(int(destination_loc))  # -> Kuyruğa eklenir
                                    self.flatten_func_encountered.append(destination_loc)  # -> Takip edilenlere eklenir
                
                # symbex block at current loc_key  # -> Mevcut blokta sembolik yürütme yapılır
                symbex_expr_result = self.symbex_block(symbex_engine, curr_loc)  # -> Sonuç alınır
                
                # if reach the end (ret), stop this path traversal  # -> Eğer dönüş noktasıysa, döngüden çık
                if symbex_expr_result is None:
                    break

                if isinstance(symbex_expr_result, ExprCond):  # -> Eğer sonuç koşullu ifade ise
                    # if we reach a conditional expression  # -> Koşullu dallanma noktası

                    # Evaluate the jump addresses if the branch is taken or not  # -> Koşul sağlandığında ve sağlanmadığında atlanacak adresler hesaplanır
                    cond_true  = {symbex_expr_result.cond: ExprInt(1, 32)}  # -> Koşul doğru kabul edilerek ifade hazırlanır
                    cond_false  = {symbex_expr_result.cond: ExprInt(0, 32)}  # -> Koşul yanlış kabul edilerek ifade hazırlanır
                    addr_true = expr_simp(
                            symbex_engine.eval_expr(symbex_expr_result.replace_expr(cond_true), {}))  # -> Koşul doğruysa hedef adres
                    addr_false = expr_simp(
                            symbex_engine.eval_expr(symbex_expr_result.replace_expr(cond_false), {}))  # -> Koşul yanlışsa hedef adres
                    
                    addr_true = self.to_loc_key(addr_true)  # -> Adres loc_key'e çevrilir
                    addr_false = self.to_loc_key(addr_false)  # -> Adres loc_key'e çevrilir
                    
                    # stash false path away  # -> Yanlış dal kuyrukta saklanır
                    exec_queue.append((addr_false, symbex_engine.symbols.copy(), curr_state_val))  # -> Yanlış dal kuyruğa eklenir
                    
                    # map curr loc -> [addr true]  # -> Doğru dal mevcut konumun ardılı olarak eklenir
                    loc_successors_map[curr_loc].append(addr_true)
                    
                    # next loc_key we're jumping to  # -> Sonraki adım doğru dal olur
                    next_loc = addr_true
                else:  # -> Koşullu değilse
                    # find next loc_key we're jumping to  # -> Sonraki konum hesaplanır
                    next_loc = expr_simp(symbex_engine.eval_expr(symbex_expr_result))

                    # map exec states <cur loc> -> [next_loc]  # -> Mevcut konumdan sonraki konuma haritalama yapılır
                    next_loc = self.to_loc_key(next_loc)
                    if next_loc not in loc_successors_map[curr_loc]:
                        loc_successors_map[curr_loc].append(next_loc)

                # update current loc_key to the next loc_key  # -> Mevcut konum güncellenir
                curr_loc = next_loc

        # logger.info('loc_successors_map')  # -> Debug için yorum satırı
        # pprint.pprint(loc_successors_map)  # -> Debug için yorum satırı
        # logger.info('state order map')  # -> Debug için yorum satırı
        # pprint.pprint(state_order_map)  # -> Debug için yorum satırı
        # logger.info('state to loc_key_map')  # -> Debug için yorum satırı
        # pprint.pprint(state_to_lockey_map)  # -> Debug için yorum satırı
        
        # NOTE: not all backbone loc_key is relevant. Only take the ones from state_to_lockey_map  # -> Sadece state_to_lockey_map içindeki omurga blokları alınır
        backbone_loc_list = [loc for sublist in state_to_lockey_map.values() for loc in sublist]  # -> Tüm alt listeler birleştirilir
        
        # add prologue blocks to backbone list  # -> Prolog blokları omurgaya eklenir
        state_order_map[0].append(first_state_val)  # -> İlk durum değeri 0 durumuna eklenir
        prologue_tail_loc = None  # -> Prolog kuyruğu tanımlanır
        for block_loc in self.asmcfg.predecessors(dispatcher_loc):  # -> Dispatcher'ın tüm ebeveynleri üzerinde döner
            # head block is the other predecessor of dispatcher beside the predispatcher  # -> predispatcher dışındaki diğer ebeveyn baş bloktur
            if block_loc == predispatcher_loc:
                continue  # -> predispatcher atlanır
            
            # add head to backbone  # -> Baş blok omurgaya eklenir
            prologue_tail_loc = block_loc
            backbone_loc_list.append(prologue_tail_loc)
            state_to_lockey_map[0].append(prologue_tail_loc)
            
            # add all prologue blocks above the prologue tail  # -> Prolog kuyruğunun üstündeki tüm bloklar eklenir
            curr_prologue_loc = prologue_tail_loc
            while len(self.asmcfg.predecessors(curr_prologue_loc)) != 0:  # -> Ebeveyni oldukça devam et
                prev_prologue_block = self.asmcfg.predecessors(curr_prologue_loc)[0]  # -> Önceki blok alınır
                backbone_loc_list.append(prev_prologue_block)  # -> Omurgaya eklenir
                state_to_lockey_map[0].append(prev_prologue_block)  # -> Haritaya eklenir
                curr_prologue_loc = prev_prologue_block  # -> Güncel blok yapılır
            break  # -> Sadece bir baş blok olduğu varsayılır, döngü kırılır
        
        # state value 0 is associated with the prologue blocks  # -> Durum 0 prolog blokları ile ilişkilendirilir
        
        # since we add from the prologue tail up to the prologue head  # -> Kuyruktan başa doğru eklendiği için
        # need to flip the order before we reorder the CFG  # -> CFG yeniden sıralanmadan önce sıra ters çevrilir
        state_to_lockey_map[0] = state_to_lockey_map[0][::-1]  # -> Liste ters çevrilir
        
        # irrelevant blocks are original blocks that are not a backbone block  # -> Omurgada olmayan bloklar ilgisizdir
        irrelevant_loc_list = [original_block.loc_key for original_block in self.asmcfg.blocks if original_block.loc_key not in backbone_loc_list]  # -> İlgisiz bloklar listelenir
        
        # delete all irrelevant blocks  # -> İlgisiz bloklar silinir
        for loc_key in irrelevant_loc_list:
            self.asmcfg.del_block(self.asmcfg.loc_key_to_block(loc_key))  # -> Blok silinir
        
        # init BinaryRewriter to reorder the CFG and generate a patch for rewriting  # -> CFG'yi yeniden sıralamak ve yama oluşturmak için BinaryRewriter başlatılır
        rewriter = BinaryRewriter(self.asmcfg, self.container.arch)  # -> BinaryRewriter nesnesi oluşturulur
        rewriter.init_CFF_data(state_order_map, state_to_lockey_map, symbex_engine)  # -> Durum ve blok haritaları verilir
        rewriter.reorder_blocks(target_address)  # -> Bloklar yeniden sıralanır
        return rewriter.generate_patch()  # -> Yama verisi döndürülür
    
    def apply_patches(self, patch_data_list: list[tuple[bytes, interval]], out_filename: str) -> bool:
        """Apply patches to deobfuscated output file
        
        Args:
            patch_data_list: List of (patch bytes, function interval)
            out_filename: Output file path
            
        Returns:
            bool: True if successful
        """
        try:
            # Copy original file contents
            with open(self.original_filename, 'rb') as in_file, open(out_filename, 'wb') as out_file:
                out_file.write(in_file.read())

            # Apply patches
            with open(out_filename, 'r+b') as out_file:
                for patch, func_interval in patch_data_list:
                    func_start, func_end = func_interval.hull()
                    length = func_end - func_start

                    # Calculate physical offset
                    if isinstance(self.container.executable, PE):
                        physical_offset = (func_start - self.container.executable.NThdr.ImageBase
                                          + self.text_section_Shdr.PointerToRawData)
                    elif isinstance(self.container.executable, ELF):
                        physical_offset = (func_start - self.text_section_Shdr.addr
                                          + self.text_section_Shdr.offset)
                    else:
                        raise ValueError("Unsupported binary format")

                    # NOP the original function body
                    out_file.seek(physical_offset)
                    out_file.write(b"\xCC" * length)

                    # Write actual patch at calculated VA
                    patch_offset = func_start - self.binary_base_va
                    out_file.seek(patch_offset)
                    out_file.write(patch)

            return True
        except Exception as e:
            logger.error(f"Patch application failed: {str(e)}")
            return False
