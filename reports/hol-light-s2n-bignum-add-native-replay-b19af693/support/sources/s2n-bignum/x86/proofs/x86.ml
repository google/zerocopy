(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Simplified model of x86 semantics.                                        *)
(* ========================================================================= *)

let x86_print_log = ref false;;

(* ------------------------------------------------------------------------- *)
(* Size in bits corresponding to the tags.                                   *)
(* ------------------------------------------------------------------------- *)

let bytesize = define
 `bytesize Byte = 8 /\
  bytesize Word = 16 /\
  bytesize Doubleword = 32 /\
  bytesize Quadword = 64 /\
  bytesize Word128 = 128 /\
  bytesize Word256 = 256`;;

let regsize = define
 `regsize Full_64 = 64 /\
  regsize Lower_32 = 32 /\
  regsize Lower_16 = 16 /\
  regsize Upper_8 = 8 /\
  regsize Lower_8 = 8`;;

let simdregsize = define
 `simdregsize Full_512 = 512 /\
  simdregsize Lower_256 = 256 /\
  simdregsize Lower_128 = 128`;;

let register_size = define
 `register_size (Gpr n w) = regsize w`;;

let simdregister_size = define
 `simdregister_size (Simdreg n w) = simdregsize w`;;

let operand_size = define
 `operand_size (Register r) = register_size r /\
  operand_size (Simdregister s) = simdregister_size s /\
  operand_size (Imm8 i8) = 8 /\
  operand_size (Imm16 i16) = 16 /\
  operand_size (Imm32 i32) = 32 /\
  operand_size (Imm64 i64) = 64 /\
  operand_size (Memop w b) = bytesize w`;;

(* ------------------------------------------------------------------------- *)
(* The semantics.                                                            *)
(* ------------------------------------------------------------------------- *)

(*** Note: we currently treat memory as a full 64-bit address space.
 *** In current processors, especially AMD, there are some canonicality
 *** assumptions (address must be sign-extended 48 bit value, i.e. the
 *** top 16 bits must be all 0s or all 1s). We can add those later when
 *** considering general memory protection properly.
 ***)

let x86state_INDUCT,x86state_RECURSION,x86state_COMPONENTS =
  define_auto_record_type
   "x86state =
     { RIP : int64;                       // instruction pointer (RIP)
       registers : (4)word -> (64)word;   // 2^4=16 GP registers, 64 bits each
       simdregisters: (5)word->(512)word; // 2^5=32 ZMM registers, 512 bits each
       maskregisters: (3)word->(64)word;  // 2^3=8 opmasks, can be up to 64-bit
       rflags : int64;                    // rflags register (top 32 reserved)
       memory : int64 -> byte;            // Memory
       events: uarch_event list           // Observable uarch events
     }";;

let FORALL_X86STATE = prove
 (`!P. (!i r z k f m l. P(x86state_RECORD i r z k f m l)) <=> (!s. P s)`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[x86state_INDUCT]);;

loadt "common/code_loading.ml";;

(* ------------------------------------------------------------------------- *)
(* Tweak for bytes_loaded s (word pc) (APPEND program data)                  *)
(* ------------------------------------------------------------------------- *)

let BYTES_LOADED_APPEND_CLAUSE = prove
 (`bytes_loaded s (word pc) (APPEND prog data) /\
   read RIP s = pcin /\
   rest <=>
   bytes_loaded s (word pc) prog /\
   read RIP s = pcin /\
   bytes_loaded s (word(pc + LENGTH prog)) data /\
   rest`,
  REWRITE_TAC[bytes_loaded_append; GSYM WORD_ADD; CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Shorthands for individual flags.                                          *)
(* ------------------------------------------------------------------------- *)

(*** Note: this does not build in the conception that some bits
 *** (e.g. 1) are "reserved" and always 0 or 1. That could be added
 *** to the semantics of any instructions operating on the flags register.
 ***
 *** We include DF because in principle it affects the MOVSB semantics;
 *** no instruction actually sets it and usual ABIs assume it is clear.
 ***)

let CF = define `CF = rflags :> bitelement 0`;;

let PF = define `PF = rflags :> bitelement 2`;;

let AF = define `AF = rflags :> bitelement 4`;;

let ZF = define `ZF = rflags :> bitelement 6`;;

let SF = define `SF = rflags :> bitelement 7`;;

let OF = define `OF = rflags :> bitelement 11`;;

let DF = define `DF = rflags :> bitelement 10`;;

add_component_alias_thms [CF; PF; AF; ZF; SF; OF; DF];;

(* ------------------------------------------------------------------------- *)
(* Shorthands for the general-purpose registers.                             *)
(* ------------------------------------------------------------------------- *)

let RAX = define `RAX = registers :> element (word  0)`
and RCX = define `RCX = registers :> element (word  1)`
and RDX = define `RDX = registers :> element (word  2)`
and RBX = define `RBX = registers :> element (word  3)`
and RSP = define `RSP = registers :> element (word  4)`
and RBP = define `RBP = registers :> element (word  5)`
and RSI = define `RSI = registers :> element (word  6)`
and RDI = define `RDI = registers :> element (word  7)`
and  R8 = define ` R8 = registers :> element (word  8)`
and  R9 = define ` R9 = registers :> element (word  9)`
and R10 = define `R10 = registers :> element (word 10)`
and R11 = define `R11 = registers :> element (word 11)`
and R12 = define `R12 = registers :> element (word 12)`
and R13 = define `R13 = registers :> element (word 13)`
and R14 = define `R14 = registers :> element (word 14)`
and R15 = define `R15 = registers :> element (word 15)`;;

add_component_alias_thms
 [RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI;
   R8;  R9; R10; R11; R12; R13; R14; R15];;

let  EAX = define ` EAX = RAX :> bottom_32`
and  ECX = define ` ECX = RCX :> bottom_32`
and  EDX = define ` EDX = RDX :> bottom_32`
and  EBX = define ` EBX = RBX :> bottom_32`
and  ESP = define ` ESP = RSP :> bottom_32`
and  EBP = define ` EBP = RBP :> bottom_32`
and  ESI = define ` ESI = RSI :> bottom_32`
and  EDI = define ` EDI = RDI :> bottom_32`
and  R8D = define ` R8D =  R8 :> bottom_32`
and  R9D = define ` R9D =  R9 :> bottom_32`
and R10D = define `R10D = R10 :> bottom_32`
and R11D = define `R11D = R11 :> bottom_32`
and R12D = define `R12D = R12 :> bottom_32`
and R13D = define `R13D = R13 :> bottom_32`
and R14D = define `R14D = R14 :> bottom_32`
and R15D = define `R15D = R15 :> bottom_32`;;

add_component_alias_thms
  [ EAX;  ECX;  EDX;  EBX;  ESP;  EBP;  ESI;  EDI;
    R8D;  R9D; R10D; R11D; R12D; R13D; R14D; R15D];;

let AX = define `AX = EAX :> bottom_16`
and CX = define `CX = ECX :> bottom_16`
and DX = define `DX = EDX :> bottom_16`
and BX = define `BX = EBX :> bottom_16`
and SP = define `SP = ESP :> bottom_16`
and BP = define `BP = EBP :> bottom_16`
and SI = define `SI = ESI :> bottom_16`
and DI = define `DI = EDI :> bottom_16`;;

add_component_alias_thms [AX; CX; DX; BX; SP; BP; SI; DI];;

let AH = define `AH = AX :> top_8`;;
let AL = define `AL = AX :> bottom_8`;;
let BH = define `BH = BX :> top_8`;;
let BL = define `BL = BX :> bottom_8`;;
let CH = define `CH = CX :> top_8`;;
let CL = define `CL = CX :> bottom_8`;;
let DH = define `DH = DX :> top_8`;;
let DL = define `DL = DX :> bottom_8`;;
let SPL = define `SPL = SP :> bottom_8`;;
let BPL = define `BPL = BP :> bottom_8`;;
let SIL = define `SIL = SI :> bottom_8`;;
let DIL = define `DIL = DI :> bottom_8`;;

add_component_alias_thms
  [AH; AL; BH; BL; CH; CL; DH; DL; SPL; BPL; SIL; DIL];;

(* ------------------------------------------------------------------------- *)
(* Shorthands for the SIMD registers.                                        *)
(*                                                                           *)
(* Note that the treatment of XMMs within YMMs within ZMMs zero-extends      *)
(* all writes, e.g. a 128-bit XMM operation will set the top 384 bits        *)
(* of the ZMM register to zero. This is the specified behavior               *)
(* *WHEN THE XMM OPERATION IS VEX-ENCODED*, which is the default form of     *)
(* XMM operation in the decoder. See the next section for an alternative     *)
(* behaviour for SSE and AESNI instructions. See section 15.5 of Intel's     *)
(* ISA Combined Manual, "Accessing XMM, YMM and ZMM Registers"               *)
(* ------------------------------------------------------------------------- *)

let ZMM0  = define `ZMM0  = simdregisters :> element(word 0)`
and ZMM1  = define `ZMM1  = simdregisters :> element(word 1)`
and ZMM2  = define `ZMM2  = simdregisters :> element(word 2)`
and ZMM3  = define `ZMM3  = simdregisters :> element(word 3)`
and ZMM4  = define `ZMM4  = simdregisters :> element(word 4)`
and ZMM5  = define `ZMM5  = simdregisters :> element(word 5)`
and ZMM6  = define `ZMM6  = simdregisters :> element(word 6)`
and ZMM7  = define `ZMM7  = simdregisters :> element(word 7)`
and ZMM8  = define `ZMM8  = simdregisters :> element(word 8)`
and ZMM9  = define `ZMM9  = simdregisters :> element(word 9)`
and ZMM10 = define `ZMM10 = simdregisters :> element(word 10)`
and ZMM11 = define `ZMM11 = simdregisters :> element(word 11)`
and ZMM12 = define `ZMM12 = simdregisters :> element(word 12)`
and ZMM13 = define `ZMM13 = simdregisters :> element(word 13)`
and ZMM14 = define `ZMM14 = simdregisters :> element(word 14)`
and ZMM15 = define `ZMM15 = simdregisters :> element(word 15)`
and ZMM16 = define `ZMM16 = simdregisters :> element(word 16)`
and ZMM17 = define `ZMM17 = simdregisters :> element(word 17)`
and ZMM18 = define `ZMM18 = simdregisters :> element(word 18)`
and ZMM19 = define `ZMM19 = simdregisters :> element(word 19)`
and ZMM20 = define `ZMM20 = simdregisters :> element(word 20)`
and ZMM21 = define `ZMM21 = simdregisters :> element(word 21)`
and ZMM22 = define `ZMM22 = simdregisters :> element(word 22)`
and ZMM23 = define `ZMM23 = simdregisters :> element(word 23)`
and ZMM24 = define `ZMM24 = simdregisters :> element(word 24)`
and ZMM25 = define `ZMM25 = simdregisters :> element(word 25)`
and ZMM26 = define `ZMM26 = simdregisters :> element(word 26)`
and ZMM27 = define `ZMM27 = simdregisters :> element(word 27)`
and ZMM28 = define `ZMM28 = simdregisters :> element(word 28)`
and ZMM29 = define `ZMM29 = simdregisters :> element(word 29)`
and ZMM30 = define `ZMM30 = simdregisters :> element(word 30)`
and ZMM31 = define `ZMM31 = simdregisters :> element(word 31)`;;

add_component_alias_thms
 [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
  ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15;
  ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23;
  ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31];;

let YMM0  = define `YMM0  = ZMM0  :> zerotop_256`
and YMM1  = define `YMM1  = ZMM1  :> zerotop_256`
and YMM2  = define `YMM2  = ZMM2  :> zerotop_256`
and YMM3  = define `YMM3  = ZMM3  :> zerotop_256`
and YMM4  = define `YMM4  = ZMM4  :> zerotop_256`
and YMM5  = define `YMM5  = ZMM5  :> zerotop_256`
and YMM6  = define `YMM6  = ZMM6  :> zerotop_256`
and YMM7  = define `YMM7  = ZMM7  :> zerotop_256`
and YMM8  = define `YMM8  = ZMM8  :> zerotop_256`
and YMM9  = define `YMM9  = ZMM9  :> zerotop_256`
and YMM10 = define `YMM10 = ZMM10 :> zerotop_256`
and YMM11 = define `YMM11 = ZMM11 :> zerotop_256`
and YMM12 = define `YMM12 = ZMM12 :> zerotop_256`
and YMM13 = define `YMM13 = ZMM13 :> zerotop_256`
and YMM14 = define `YMM14 = ZMM14 :> zerotop_256`
and YMM15 = define `YMM15 = ZMM15 :> zerotop_256`;;

add_component_alias_thms
 [YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7;
  YMM8; YMM9; YMM10; YMM11; YMM12; YMM13; YMM14; YMM15];;

let XMM0  = define `XMM0  = YMM0  :> zerotop_128`
and XMM1  = define `XMM1  = YMM1  :> zerotop_128`
and XMM2  = define `XMM2  = YMM2  :> zerotop_128`
and XMM3  = define `XMM3  = YMM3  :> zerotop_128`
and XMM4  = define `XMM4  = YMM4  :> zerotop_128`
and XMM5  = define `XMM5  = YMM5  :> zerotop_128`
and XMM6  = define `XMM6  = YMM6  :> zerotop_128`
and XMM7  = define `XMM7  = YMM7  :> zerotop_128`
and XMM8  = define `XMM8  = YMM8  :> zerotop_128`
and XMM9  = define `XMM9  = YMM9  :> zerotop_128`
and XMM10 = define `XMM10 = YMM10 :> zerotop_128`
and XMM11 = define `XMM11 = YMM11 :> zerotop_128`
and XMM12 = define `XMM12 = YMM12 :> zerotop_128`
and XMM13 = define `XMM13 = YMM13 :> zerotop_128`
and XMM14 = define `XMM14 = YMM14 :> zerotop_128`
and XMM15 = define `XMM15 = YMM15 :> zerotop_128`;;

add_component_alias_thms
 [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
  XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15];;

(*** Note that K0 is actually hardwired to all-1s              ***)
(*** So strictly we should have left it out of the state above ***)

let K0 = define `K0:(x86state,(64)word)component = rvalue(word_not(word 0))`;;
let K1 = define `K1 = maskregisters :> element(word 1)`;;
let K2 = define `K2 = maskregisters :> element(word 2)`;;
let K3 = define `K3 = maskregisters :> element(word 3)`;;
let K4 = define `K4 = maskregisters :> element(word 4)`;;
let K5 = define `K5 = maskregisters :> element(word 5)`;;
let K6 = define `K6 = maskregisters :> element(word 6)`;;
let K7 = define `K7 = maskregisters :> element(word 7)`;;

(* ------------------------------------------------------------------------- *)
(* Shorthands for the SSE&AESNI SIMD registers                               *)
(*                                                                           *)
(* Note that when writing to the lowerhalf (XMM of YMM) of SIMD registers,   *)
(* SSE and AESNI instructions will keep the upperhalf as is. This is         *)
(* different from the behaviour *WHEN THE XMM OPERATION IS VEX-ENCODED*.     *)
(* Interally, the symbolic simulation will reduce reads of SSE SIMD          *)
(* registers to reads of VEX registers using READ_YMM_SSE_EQUIV theorems.    *)
(* See section 15.5 of Intel's ISA Combined Manual,                          *)
(* "Accessing XMM, YMM and ZMM Registers"                                    *)
(* ------------------------------------------------------------------------- *)

let YMM0_SSE  = define `YMM0_SSE  = ZMM0  :> bottom_256`
and YMM1_SSE  = define `YMM1_SSE  = ZMM1  :> bottom_256`
and YMM2_SSE  = define `YMM2_SSE  = ZMM2  :> bottom_256`
and YMM3_SSE  = define `YMM3_SSE  = ZMM3  :> bottom_256`
and YMM4_SSE  = define `YMM4_SSE  = ZMM4  :> bottom_256`
and YMM5_SSE  = define `YMM5_SSE  = ZMM5  :> bottom_256`
and YMM6_SSE  = define `YMM6_SSE  = ZMM6  :> bottom_256`
and YMM7_SSE  = define `YMM7_SSE  = ZMM7  :> bottom_256`
and YMM8_SSE  = define `YMM8_SSE  = ZMM8  :> bottom_256`
and YMM9_SSE  = define `YMM9_SSE  = ZMM9  :> bottom_256`
and YMM10_SSE = define `YMM10_SSE = ZMM10 :> bottom_256`
and YMM11_SSE = define `YMM11_SSE = ZMM11 :> bottom_256`
and YMM12_SSE = define `YMM12_SSE = ZMM12 :> bottom_256`
and YMM13_SSE = define `YMM13_SSE = ZMM13 :> bottom_256`
and YMM14_SSE = define `YMM14_SSE = ZMM14 :> bottom_256`
and YMM15_SSE = define `YMM15_SSE = ZMM15 :> bottom_256`;;

add_component_alias_thms
 [YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE;
  YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE;
  YMM8_SSE; YMM9_SSE; YMM10_SSE; YMM11_SSE;
  YMM12_SSE; YMM13_SSE; YMM14_SSE; YMM15_SSE];;

let READ_YMM_SSE_TAC SSE_fn fn =
  STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; SSE_fn; fn;
    READ_SUBWORD; DIMINDEX_256; bottom_256; zerotop_256;
    bottomhalf; through; read] THEN
  (* BITBLAST_TAC works too *)
  MATCH_MP_TAC WORD_SUBWORD_EQUAL_WORD_ZX_POS0 THEN
  REWRITE_TAC[DIMINDEX_256; DIMINDEX_512] THEN
  CONV_TAC(NUM_REDUCE_CONV) ;;

let READ_YMM_SSE_EQUIV:thm list = map (fun (goal,ssereg,reg) ->
  prove(goal, READ_YMM_SSE_TAC ssereg reg))
   [(`!s:x86state. read YMM0_SSE s = read YMM0 s`,YMM0_SSE,YMM0);
    (`!s:x86state. read YMM1_SSE s = read YMM1 s`,YMM1_SSE,YMM1);
    (`!s:x86state. read YMM2_SSE s = read YMM2 s`,YMM2_SSE,YMM2);
    (`!s:x86state. read YMM3_SSE s = read YMM3 s`,YMM3_SSE,YMM3);
    (`!s:x86state. read YMM4_SSE s = read YMM4 s`,YMM4_SSE,YMM4);
    (`!s:x86state. read YMM5_SSE s = read YMM5 s`,YMM5_SSE,YMM5);
    (`!s:x86state. read YMM6_SSE s = read YMM6 s`,YMM6_SSE,YMM6);
    (`!s:x86state. read YMM7_SSE s = read YMM7 s`,YMM7_SSE,YMM7);
    (`!s:x86state. read YMM8_SSE s = read YMM8 s`,YMM8_SSE,YMM8);
    (`!s:x86state. read YMM9_SSE s = read YMM9 s`,YMM9_SSE,YMM9);
    (`!s:x86state. read YMM10_SSE s = read YMM10 s`,YMM10_SSE,YMM10);
    (`!s:x86state. read YMM11_SSE s = read YMM11 s`,YMM11_SSE,YMM11);
    (`!s:x86state. read YMM12_SSE s = read YMM12 s`,YMM12_SSE,YMM12);
    (`!s:x86state. read YMM13_SSE s = read YMM13 s`,YMM13_SSE,YMM13);
    (`!s:x86state. read YMM14_SSE s = read YMM14 s`,YMM14_SSE,YMM14);
    (`!s:x86state. read YMM15_SSE s = read YMM15 s`,YMM15_SSE,YMM15);]

let XMM0_SSE  = define `XMM0_SSE  = YMM0_SSE  :> bottom_128`
and XMM1_SSE  = define `XMM1_SSE  = YMM1_SSE  :> bottom_128`
and XMM2_SSE  = define `XMM2_SSE  = YMM2_SSE  :> bottom_128`
and XMM3_SSE  = define `XMM3_SSE  = YMM3_SSE  :> bottom_128`
and XMM4_SSE  = define `XMM4_SSE  = YMM4_SSE  :> bottom_128`
and XMM5_SSE  = define `XMM5_SSE  = YMM5_SSE  :> bottom_128`
and XMM6_SSE  = define `XMM6_SSE  = YMM6_SSE  :> bottom_128`
and XMM7_SSE  = define `XMM7_SSE  = YMM7_SSE  :> bottom_128`
and XMM8_SSE  = define `XMM8_SSE  = YMM8_SSE  :> bottom_128`
and XMM9_SSE  = define `XMM9_SSE  = YMM9_SSE  :> bottom_128`
and XMM10_SSE = define `XMM10_SSE = YMM10_SSE :> bottom_128`
and XMM11_SSE = define `XMM11_SSE = YMM11_SSE :> bottom_128`
and XMM12_SSE = define `XMM12_SSE = YMM12_SSE :> bottom_128`
and XMM13_SSE = define `XMM13_SSE = YMM13_SSE :> bottom_128`
and XMM14_SSE = define `XMM14_SSE = YMM14_SSE :> bottom_128`
and XMM15_SSE = define `XMM15_SSE = YMM15_SSE :> bottom_128`;;

add_component_alias_thms
 [XMM0_SSE; XMM1_SSE; XMM2_SSE; XMM3_SSE;
  XMM4_SSE; XMM5_SSE; XMM6_SSE; XMM7_SSE;
  XMM8_SSE; XMM9_SSE; XMM10_SSE; XMM11_SSE;
  XMM12_SSE; XMM13_SSE; XMM14_SSE; XMM15_SSE];;

(* ------------------------------------------------------------------------- *)
(* Semantics of conditions.                                                  *)
(* ------------------------------------------------------------------------- *)

let condition_semantics = define
 `(condition_semantics Unconditional s <=>
        T) /\
  (condition_semantics Condition_B s <=>
        read CF s) /\
  (condition_semantics Condition_BE s <=>
        read CF s \/ read ZF s) /\
  (condition_semantics Condition_L s <=>
        ~(read SF s <=> read OF s)) /\
  (condition_semantics Condition_LE s <=>
        ~(read SF s <=> read OF s) \/ read ZF s) /\
  (condition_semantics Condition_NB s <=>
        ~read CF s) /\
  (condition_semantics Condition_NBE s <=>
        ~(read CF s \/ read ZF s)) /\
  (condition_semantics Condition_NL s <=>
        (read SF s <=> read OF s)) /\
  (condition_semantics Condition_NLE s <=>
        (read SF s <=> read OF s) /\ ~read ZF s) /\
  (condition_semantics Condition_NO s <=>
        ~read OF s) /\
  (condition_semantics Condition_NP s <=>
        ~read PF s) /\
  (condition_semantics Condition_NS s <=>
        ~read SF s) /\
  (condition_semantics Condition_NZ s <=>
        ~read ZF s) /\
  (condition_semantics Condition_O s <=>
        read OF s) /\
  (condition_semantics Condition_P s <=>
        read PF s) /\
  (condition_semantics Condition_S s <=>
        read SF s) /\
  (condition_semantics Condition_Z s <=>
        read ZF s)`;;

(* ------------------------------------------------------------------------- *)
(* Exceptions. Currently the semantics is basically "some arbitrary state".  *)
(* But we distinguish things so this can become a more accurate model later. *)
(* In general there is also a 64-bit data field with some exceptions         *)
(* ------------------------------------------------------------------------- *)

let raise_exception = new_definition
 `raise_exception (b:byte) :x86state->x86state->bool =
    ASSIGNS entirety`;;

let raise_exception_with = new_definition
 `raise_exception_with (b:byte) (d:int64) :x86state->x86state->bool =
    ASSIGNS entirety`;;

let x86_Exception_DE = new_definition
  `x86_Exception_DE = (word 0x00 :byte)`;;

let x86_Exception_DB = new_definition
  `x86_Exception_DB = (word 0x01 :byte)`;;

let x86_Exception_NMI = new_definition
  `x86_Exception_NMI = (word 0x02 :byte)`;;

let x86_Exception_BP = new_definition
  `x86_Exception_BP = (word 0x03:byte)`;;

let x86_Exception_OF = new_definition
  `x86_Exception_OF = (word 0x04 :byte)`;;

let x86_Exception_BR = new_definition
  `x86_Exception_BR = (word 0x05 :byte)`;;

let x86_Exception_UD = new_definition
  `x86_Exception_UD = (word 0x06 :byte)`;;

let x86_Exception_NM = new_definition
  `x86_Exception_NM = (word 0x07 :byte)`;;

let x86_Exception_DF = new_definition
  `x86_Exception_DF = (word 0x08 :byte)`;;

let x86_Exception_TS = new_definition
  `x86_Exception_TS = (word 0x0A :byte)`;;

let x86_Exception_NP = new_definition
  `x86_Exception_NP = (word 0x0B :byte)`;;

let x86_Exception_SS = new_definition
  `x86_Exception_SS = (word 0x0C :byte)`;;

let x86_Exception_GP = new_definition
  `x86_Exception_GP = (word 0x0D :byte)`;;

let x86_Exception_PF = new_definition
  `x86_Exception_PF = (word 0x0E :byte)`;;

let x86_Exception_MF = new_definition
  `x86_Exception_MF = (word 0x10 :byte)`;;

let x86_Exception_AC = new_definition
  `x86_Exception_AC = (word 0x11 :byte)`;;

let x86_Exception_MC = new_definition
  `x86_Exception_MC = (word 0x12 :byte)`;;

let x86_Exception_XF = new_definition
  `x86_Exception_XF = (word 0x13 :byte)`;;

let x86_Exception_VE = new_definition
  `x86_Exception_VE = (word 0x14 :byte)`;;

let x86_Exception_SX = new_definition
  `x86_Exception_SX = (word 0x1E :byte)`;;

(* ------------------------------------------------------------------------- *)
(* An auxiliary function used to define the MOVSB semantics. This            *)
(* gives a specific sequential semantics to the iterated moves,              *)
(* and proceeds either down or up depending on the "df" (down                *)
(* flag / direction flag) setting. Thus unlike C memcpy it is                *)
(* well-defined for overlapping regions, but not in a way that               *)
(* is comparable to memmove. We then prove that it can be considered         *)
(* as a function ("x86_stringcopy") of the two input buffers, and in         *)
(* the nonoverlapping case has the simple assignment semantics.              *)
(* ------------------------------------------------------------------------- *)

let x86_movsb1 = define
 `x86_movsb1 a b n s =
        write (memory :> bytes8(word_add b (word n)))
              (read (memory :> bytes8(word_add a (word n))) s) s`;;

let x86_movsb = define
 `x86_movsb df a b 0 = I /\
  x86_movsb df a b (SUC n) =
        if df then x86_movsb df a b n o x86_movsb1 a b n
        else x86_movsb1 a b n o x86_movsb df a b n`;;

let X86STATE_EQ = prove
 (`!s s'.
        s = s' <=>
        read RIP s = read RIP s' /\
        read registers s = read registers s' /\
        read simdregisters s = read simdregisters s' /\
        read maskregisters s = read maskregisters s' /\
        read rflags s = read rflags s' /\
        read memory s = read memory s' /\
        read events s = read events s'`,
  REPEAT(MATCH_MP_TAC x86state_INDUCT ORELSE GEN_TAC) THEN
  REWRITE_TAC[x86state_COMPONENTS; injectivity "x86state"]);;

let READ_ORTHOGONAL_COMPONENT_MOVSB = prove
 (`!(c:(x86state,A)component) df a b n s.
        n < 2 EXP 64 /\
        orthogonal_components c (memory :> bytes(b,n))
        ==> read c (x86_movsb df a b n s) = read c s`,
  REPLICATE_TAC 4 GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[x86_movsb; I_THM] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN X_GEN_TAC `s:x86state` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[o_THM; x86_movsb1; bytes8] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `SUC n < a ==> n < a`)) THENL
   [FIRST_X_ASSUM(fun th ->
      W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd));
    FIRST_X_ASSUM(fun th ->
      W(MP_TAC o PART_MATCH (lhand o rand) (GSYM th) o rand o snd))] THEN
  (ANTS_TAC THENL
    [MP_TAC(ISPECL [`b:int64`; `n:num`; `SUC n`]
       PREFIX_BYTES_AS_SUBCOMPONENT) THEN
     REWRITE_TAC[LE; LE_REFL] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
     ASM_SIMP_TAC[COMPONENT_COMPOSE_ASSOC; ORTHOGONAL_COMPONENTS_SUB_RIGHT];
     DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC READ_WRITE_ORTHOGONAL_COMPONENTS THEN
   MP_TAC(ISPECL
    [`word_add b (word n):int64`; `b:int64`; `1`; `SUC n`]
    CONTAINED_BYTES_AS_SUBCOMPONENT_GEN) THEN
   ASM_SIMP_TAC[DIMINDEX_64; LT_IMP_LE] THEN
   REWRITE_TAC[WORD_RULE `word_sub (word_add b n) b = n`] THEN
   ASM_SIMP_TAC[VAL_WORD; MOD_LT; ADD1; LE_REFL; DIMINDEX_64] THEN
   DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[GSYM ADD1] THEN
   ASM_SIMP_TAC[COMPONENT_COMPOSE_ASSOC; ORTHOGONAL_COMPONENTS_SUB_RIGHT]));;

let X86_STRINGCOPY_BOUND,READ_X86_MOVSB =
  let lemma1 = prove
   (`!df a b n m s s'.
          m < n /\ n < 2 EXP 64 /\
          read (memory :> bytes (a,n)) s = read (memory :> bytes (a,n)) s' /\
          read (memory :> bytes (b,n)) s = read (memory :> bytes (b,n)) s'
          ==> read (memory :> bytes (a,n)) (x86_movsb1 a b m s) =
              read (memory :> bytes (a,n)) (x86_movsb1 a b m s') /\
              read (memory :> bytes (b,n)) (x86_movsb1 a b m s) =
              read (memory :> bytes (b,n)) (x86_movsb1 a b m s')`,
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[GEN_REWRITE_RULE
      (RAND_CONV o BINDER_CONV o RAND_CONV o BINOP_CONV)
      [GSYM READ_ELEMENT] (SPEC_ALL READ_BYTES_EQ)] THEN
    REWRITE_TAC[x86_movsb1; READ_COMPONENT_COMPOSE;
          WRITE_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[REWRITE_RULE[valid_component]
      (VALID_COMPONENT_CONV `valid_component memory`)] THEN
    REWRITE_TAC[READ_ELEMENT_WRITE_BYTES8] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BYTES8_ELEMENT] THEN ASM_MESON_TAC[]) in
  let lemma2 = prove
   (`!df a b n m s s'.
          m <= n /\ n < 2 EXP 64 /\
          read (memory :> bytes (a,n)) s = read (memory :> bytes (a,n)) s' /\
          read (memory :> bytes (b,n)) s = read (memory :> bytes (b,n)) s'
          ==> read (memory :> bytes (a,n)) (x86_movsb df a b m s) =
              read (memory :> bytes (a,n)) (x86_movsb df a b m s') /\
              read (memory :> bytes (b,n)) (x86_movsb df a b m s) =
              read (memory :> bytes (b,n)) (x86_movsb df a b m s')`,
    GEN_REWRITE_TAC I [FORALL_BOOL_THM] THEN CONJ_TAC THEN
    REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN
    ASM_SIMP_TAC[x86_movsb; I_THM; o_THM] THEN
    REWRITE_TAC[LE_SUC_LT] THEN ASM_MESON_TAC[lemma1; LT_IMP_LE]) in
  let lemma3 = prove
   (`?f. !df a b n s.
          n < 2 EXP 64
          ==> read (memory :> bytes(b,n)) (x86_movsb df a b n s) =
              f df a b n
                (read (memory :> bytes(a,n)) s)
                (read (memory :> bytes(b,n)) s)`,
    REWRITE_TAC[GSYM SKOLEM_THM] THEN
    GEN_REWRITE_TAC I [FORALL_BOOL_THM] THEN REPEAT STRIP_TAC THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNCURRY] THEN
    ASM_CASES_TAC `n < 2 EXP 64` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
    GEN_REWRITE_TAC (BINDER_CONV o BINOP_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[GSYM FUNCTION_FACTORS_LEFT] THEN
    REWRITE_TAC[o_DEF; PAIR_EQ] THEN ASM_MESON_TAC[lemma2; LE_REFL]) in
  let th = prove
   (`?f. (!df a b n abuf bbuf. f df a b n abuf bbuf < 2 EXP (8 * n)) /\
         (!df a b n s.
            n < 2 EXP 64
            ==> read (memory :> bytes(b,n)) (x86_movsb df a b n s) =
                f df a b n
                  (read (memory :> bytes(a,n)) s)
                  (read (memory :> bytes(b,n)) s))`,
    X_CHOOSE_TAC `f:bool->int64->int64->num->num->num->num`
     (GSYM lemma3) THEN
    EXISTS_TAC
      `\(df:bool) (a:int64) (b:int64) n (abuf:num) (bbuf:num).
        (f df a b n abuf bbuf) MOD 2 EXP (8 * n)` THEN
    SIMP_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD_LEN]) in
  CONJ_PAIR(new_specification ["x86_stringcopy"] th);;

let x86_stringcopy = prove
 (`!df a b n s.
        n < 2 EXP 64
        ==> x86_movsb df a b n s =
            write (memory :> bytes (b,n))
                  (x86_stringcopy df a b n
                      (read (memory :> bytes (a,n)) s)
                      (read (memory :> bytes (b,n)) s))
                  s`,
  MP_TAC READ_X86_MOVSB THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  ASM_CASES_TAC `n < 2 EXP 64` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[X86STATE_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC READ_ORTHOGONAL_COMPONENT_MOVSB THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC ORTHOGONAL_COMPONENTS_CONV) THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `c:int64` THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM READ_ELEMENT] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[REWRITE_RULE[valid_component]
    (VALID_COMPONENT_CONV `valid_component memory`)] THEN
  REWRITE_TAC[READ_ELEMENT_WRITE_BYTES] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[limb; READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[READ_BYTES_DIV] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 2 EXP (8 * 1)`; READ_BYTES_MOD] THEN
    REWRITE_TAC[WORD_RULE `word_add b (word(val(word_sub c b))) = c`] THEN
    ASM_SIMP_TAC[ARITH_RULE `a < b ==> MIN (b - a) 1 = 1`] THEN
    REWRITE_TAC[READ_BYTES_1; WORD_VAL];
    GEN_REWRITE_TAC LAND_CONV [GSYM READ_ELEMENT] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    MATCH_MP_TAC READ_ORTHOGONAL_COMPONENT_MOVSB THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN
    CONJ_TAC THENL [CONV_TAC VALID_COMPONENT_CONV; ALL_TAC] THEN
    REWRITE_TAC[GSYM BYTES8_ELEMENT] THEN REWRITE_TAC[bytes8] THEN
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES] THEN
    REWRITE_TAC[NONOVERLAPPING_MODULO; WORD_VAL; NONOVERLAPPING_QFREE] THEN
    REWRITE_TAC[VAL_BOUND; ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    ASM_ARITH_TAC]);;

let READ_X86_MOVSB_NONOVERLAPPING = prove
 (`!df a b n s.
        n < 2 EXP 64 /\
        nonoverlapping (a,n) (b,n)
        ==> read (memory :> bytes(b,n)) (x86_movsb df a b n s) =
            read (memory :> bytes(a,n)) s`,
  GEN_REWRITE_TAC I [FORALL_BOOL_THM] THEN CONJ_TAC THEN
  REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[x86_movsb; I_THM; READ_MEMORY_BYTES_TRIVIAL] THEN
  X_GEN_TAC `s:x86state` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `SUC n < a ==> n < a`)) THEN
  (SUBGOAL_THEN `nonoverlapping(a:int64,n) (b,n)` ASSUME_TAC THENL
   [NONOVERLAPPING_TAC; ALL_TAC]) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; ADD1; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  (BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC]) THEN
  ASM_SIMP_TAC[o_THM] THEN REWRITE_TAC[x86_movsb1] THEN
  TRY(MATCH_MP_TAC(MESON[]
       `read c (write d y s) = read c s /\ read c s = z
         ==> read c (write d y s) = z`) THEN
      CONJ_TAC THENL
       [READ_OVER_WRITE_ORTHOGONAL_TAC; ASM_SIMP_TAC[] THEN NO_TAC])
  THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) READ_ORTHOGONAL_COMPONENT_MOVSB o
        lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ORTHOGONAL_COMPONENTS_TAC; DISCH_THEN SUBST1_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(MESON[]
   `read c (write c y s) = y /\ y = z ==> read c (write c y s) = z`) THEN
  (CONJ_TAC THENL [READ_OVER_WRITE_TAC; REWRITE_TAC[]]) THEN
  MATCH_MP_TAC READ_ORTHOGONAL_COMPONENT_MOVSB THEN ASM_REWRITE_TAC[] THEN
  ORTHOGONAL_COMPONENTS_TAC);;

let X86_STRINGCOPY_NONOVERLAPPING = prove
 (`!df a b n s.
        n < 2 EXP 64 /\
        nonoverlapping (a,n) (b,n)
        ==> x86_stringcopy df a b n
             (read (memory :> bytes (a,n)) s)
             (read (memory :> bytes (b,n)) s) =
            read (memory :> bytes (a,n)) s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM READ_X86_MOVSB] THEN
  ASM_SIMP_TAC[READ_X86_MOVSB_NONOVERLAPPING]);;

let READ_WRITE_X86_STRINGCOPY = prove
 (`!df a b n s s'.
        n < 2 EXP 64
        ==> read (memory :> bytes(b,n))
                 (write (memory :> bytes(b,n))
                        (x86_stringcopy df a b n
                          (read (memory :> bytes (a,n)) s)
                          (read (memory :> bytes (b,n)) s))
                        s') =
            x86_stringcopy df a b n
             (read (memory :> bytes (a,n)) s)
             (read (memory :> bytes (b,n)) s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[REWRITE_RULE[valid_component]
    (VALID_COMPONENT_CONV `valid_component memory`)] THEN
  ASM_SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64; LT_IMP_LE] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_SIMP_TAC[GSYM READ_X86_MOVSB] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* The core operations with generic sizes, to be instantiated to any of      *)
(* 8, 16, 32 or 64. In effect this is a kind of shallow embedding of x86.    *)
(* ------------------------------------------------------------------------- *)

let x86_ADC = new_definition
 `x86_ADC dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(val x + val y + c = val z) ,,
         OF := ~(ival x + ival y + &c = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) + c =
                 val(word_zx z:nybble))) s`;;

let x86_ADCX = new_definition
 `x86_ADCX dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:N word) ,,
         CF := ~(val x + val y + c = val z)) s`;;

let x86_ADD = new_definition
 `x86_ADD dest src s =
        let x = read dest s and y = read src s in
        let z = word_add x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(val x + val y = val z) ,,
         OF := ~(ival x + ival y = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) =
                 val(word_zx z:nybble))) s`;;

let x86_ADOX = new_definition
 `x86_ADOX dest src s =
        let x = read dest s and y = read src s and c = bitval(read OF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:N word) ,,
         OF := ~(val x + val y + c = val z)) s`;;

(* AESENC does not modify DEST[MAXVL-1:128] *)
let x86_AESENC = new_definition
  `x86_AESENC dest src s =
     let state = read dest s and roundkey = read src s in
     let new_state = aesenc state roundkey in
     (dest := new_state) s`;;

(* AESENCLAST does not modify DEST[MAXVL-1:128] *)
let x86_AESENCLAST = new_definition
  `x86_AESENCLAST dest src s =
     let state = read dest s and roundkey = read src s in
     let new_state = aesenclast state roundkey in
     (dest := new_state) s`;;

(* AESDEC does not modify DEST[MAXVL-1:128] *)
let x86_AESDEC = new_definition
  `x86_AESDEC dest src s =
     let state = read dest s and roundkey = read src s in
     let new_state = aesdec state roundkey in
     (dest := new_state) s`;;

(* AESDECLAST does not modify DEST[MAXVL-1:128] *)
let x86_AESDECLAST = new_definition
  `x86_AESDECLAST dest src s =
     let state = read dest s and roundkey = read src s in
     let new_state = aesdeclast state roundkey in
     (dest := new_state) s`;;

(* AESDECLAST does not modify DEST[MAXVL-1:128] *)
let x86_AESKEYGENASSIST = new_definition
  `x86_AESKEYGENASSIST dest src imm8 s =
     let x = read src s in
     let imm8 = read imm8 s in
     let res = aeskeygenassist x imm8 in
     (dest := res) s`;;

let x86_AND = new_definition
 `x86_AND dest src s =
        let x = read dest s and y = read src s in
        let z = word_and x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

(*** These are similar to TZCNT and (less so, dual) LZCNT. Besides one
 *** being dualized, they are officially undefined on zero inputs.
 *** The flag settings are also different: the input determines ZF and
 *** the others are undefined (on TZCNT/LZCNT the output determines ZF).
 *** They have the merit of being pure x86-64 and not needing even
 *** moderately recent extensions.
 ***)

let x86_BSF = new_definition
 `x86_BSF dest src s =
        let x:N word = read src s in
        let z:N word = word(word_ctz x) in
        ((if x = word 0 then UNDEFINED_VALUES[dest] else dest := (z:N word)) ,,
         ZF := (val x = 0) ,,
         UNDEFINED_VALUES[CF;OF;SF;PF;AF]) s`;;

let x86_BSR = new_definition
 `x86_BSR dest src s =
        let x:N word = read src s in
        let z:N word = word(dimindex(:N) - 1 - word_clz x) in
        ((if x = word 0 then UNDEFINED_VALUES[dest] else dest := (z:N word)) ,,
         ZF := (val x = 0) ,,
         UNDEFINED_VALUES[CF;OF;SF;PF;AF]) s`;;

let x86_BSWAP = new_definition
 `x86_BSWAP dest s =
        let x:((((N)tybit0)tybit0)tybit0)word = read dest s in
        let x' = word_bytereverse x in
        (dest := x') s`;;

(*** These four amount to the core operations for BT, BTC, BTR and BTS.
 *** When the first operand is a register this is the entire thing.
 *** With memory operands however, the upper part is used to offset the
 *** address (presumably DIV means Euclidean division?) and sometimes
 *** assemblers even support that kind of thing for immediates. So the
 *** dispatch needs to treat different operands differently, unless we
 *** choose to define some more generic "bit" of a state components.
 ***)

let x86_BT = new_definition
 `x86_BT dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_BTC = new_definition
 `x86_BTC dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest :> bitelement c := ~b ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_BTR = new_definition
 `x86_BTR dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest :> bitelement c := F ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_BTS = new_definition
 `x86_BTS dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest :> bitelement c := T ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`;;

let x86_CLC = new_definition
 `x86_CLC s =
        (CF := F) s`;;

let x86_CLD = new_definition
 `x86_CLD s =
        (DF := F) s`;;

let x86_CMC = new_definition
 `x86_CMC s =
        let c = read CF s in
        (CF := ~c) s`;;

let x86_CMOV = new_definition
 `x86_CMOV cc dest src s =
        (dest := (if condition_semantics cc s then read src s
                  else read dest s)) s`;;

let x86_CMP = new_definition
 `x86_CMP dest src s =
        let x = read dest s and y = read src s in
        let (z:N word) = word_sub x y in
        (ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(&(val x) - &(val y):int = &(val z)) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`;;

let x86_DEC = new_definition
 `x86_DEC dest s =
        let x = read dest s in
        let z = word_sub x (word 1) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         OF := ~(ival x - &1 = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &1:int =
                 &(val(word_zx z:nybble)))) s`;;

(*** This is the ENDBR64 instruction, which is treated as a NOP. On
 *** machines without CET enabled, including older machines from
 *** before the feature existed, this is indeed how it behaves. We
 *** do not attempt to model the restrictions that are imposed when
 *** CET is enabled, and such restrictions arguably belong on the
 *** indirect branches themselves, of which there are none in
 *** s2n-bignum itself.
 ***)

let x86_ENDBR64 = new_definition
 `x86_ENDBR64 (s:x86state) = \s'. s = s'`;;

let x86_VZEROUPPER = new_definition
 `x86_VZEROUPPER (s:x86state) =
  (YMM0  := word_zx(word_subword (read YMM0  s) (0,128):int128) ,,
   YMM1  := word_zx(word_subword (read YMM1  s) (0,128):int128) ,,
   YMM2  := word_zx(word_subword (read YMM2  s) (0,128):int128) ,,
   YMM3  := word_zx(word_subword (read YMM3  s) (0,128):int128) ,,
   YMM4  := word_zx(word_subword (read YMM4  s) (0,128):int128) ,,
   YMM5  := word_zx(word_subword (read YMM5  s) (0,128):int128) ,,
   YMM6  := word_zx(word_subword (read YMM6  s) (0,128):int128) ,,
   YMM7  := word_zx(word_subword (read YMM7  s) (0,128):int128) ,,
   YMM8  := word_zx(word_subword (read YMM8  s) (0,128):int128) ,,
   YMM9  := word_zx(word_subword (read YMM9  s) (0,128):int128) ,,
   YMM10 := word_zx(word_subword (read YMM10 s) (0,128):int128) ,,
   YMM11 := word_zx(word_subword (read YMM11 s) (0,128):int128) ,,
   YMM12 := word_zx(word_subword (read YMM12 s) (0,128):int128) ,,
   YMM13 := word_zx(word_subword (read YMM13 s) (0,128):int128) ,,
   YMM14 := word_zx(word_subword (read YMM14 s) (0,128):int128) ,,
   YMM15 := word_zx(word_subword (read YMM15 s) (0,128):int128)) s`;;

(*** There are really four different multiplies here.
 ***
 *** 1. x86_IMUL: a signed multiply with the same length for operands
 ***    and result, corresponding to the "two operand" and "three operand"
 ***    forms in the manual, with three operands to allow flexibility at this
 ***    level. Note that as usual the result is signed/unsigned-agnostic in
 ***    this setting. But the overflow and carry settings are *both* signed.

 *** 2. x86_IMUL2: A signed two-part multiply, corresponding to the
 ***    "one-operand form" in the manuals. The carry and overflow seem to
 ***    be set in the same way and as one would expect, according to recent
 ***    documentation and a few experiments. However much older manuals say
 ***    something different. (Whether the top is something other than all
 ***    0s or all 1s --- implying for example 2^31 * 2^32 would not set it.)

 *** 3. x86_MUL2: An unsigned two-part signed multiply. The detection of
 ***    CF=OF is based on whether the top is nonzero. The code for this is
 ***    further below following alphabetical order.

 *** 4. x86_MULX4: An unsigned 2-part multiply without affecting flags. In
 ***    the final dispatch the first source is explicit (edx/rdx). Note that
 ***    it's important to assign the high part *second* to match the ISA
 ***    manual "if the first and second operands are identical, it will contain
 ***    the high half of the multiplication results". In others we happen to
 ***    do it the other way round, but maybe for uniformity should change that.
 ***)

let x86_IMUL3 = new_definition
 `x86_IMUL3 dest (src1,src2) s =
        let x = read src1 s and y = read src2 s in
        let z = word_mul x y in
        (dest := (z:N word) ,,
         CF := ~(ival x * ival y = ival z) ,,
         OF := ~(ival x * ival y = ival z) ,,
         UNDEFINED_VALUES[ZF;SF;PF;AF]) s`;;

let x86_IMUL = new_definition
 `x86_IMUL dest src = x86_IMUL3 dest (dest,src)`;;

let x86_IMUL2 = new_definition
 `x86_IMUL2 (dest_hi,dest_lo) src s =
        let (x:N word) = read dest_lo s and (y:N word) = read src s in
        let z = iword(ival x * ival y):(N tybit0)word in
        let z_hi:N word = word_zx (word_ushr z (dimindex(:N)))
        and z_lo:N word = word_zx z in
        (dest_hi := z_hi ,,
         dest_lo := z_lo ,,
         CF := ~(ival x * ival y = ival z_lo) ,,
         OF := ~(ival x * ival y = ival z_lo) ,,
         UNDEFINED_VALUES[ZF;SF;PF;AF]) s`;;

let x86_INC = new_definition
 `x86_INC dest s =
        let x = read dest s in
        let z = word_add x (word 1) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         OF := ~(ival x + &1 = ival z) ,,
         AF := ~(val(word_zx x:nybble) + 1 =
                 val(word_zx z:nybble))) s`;;

(*** At this level this is trivial: the EA is from operand decoding ***)

let x86_LEA = new_definition
 `x86_LEA dest ea s =
        (dest := ea) s`;;

let x86_LZCNT = new_definition
 `x86_LZCNT dest src s =
        let x:N word = read src s in
        let z:N word = word(word_clz x) in
        (dest := (z:N word) ,,
         CF := (val x = 0) ,,
         ZF := (val z = 0) ,,
         UNDEFINED_VALUES[OF;SF;PF;AF]) s`;;

let x86_MOV = new_definition
 `x86_MOV dest src s =
        let x = read src s in (dest := x) s`;;

let x86_MOVAPS = new_definition
 `x86_MOVAPS dest src s =
    let x = read src s in (dest := x) s`;;

let x86_MOVDQA = new_definition
 `x86_MOVDQA dest src s =
    let x = read src s in (dest := x) s`;;

let x86_MOVDQU = new_definition
`x86_MOVDQU dest src s =
   let x = read src s in (dest := x) s`;;

let x86_MOVD = new_definition
 `x86_MOVD dest src s =
    let (x:M word) = read src s in
    let (x':N word) = word_zx x in
    (dest := x') s`;;

(*** The intermediate forcing to 64 bits is for MOVQ xmmM, xmmN  ***)

let x86_MOVQ = new_definition
 `x86_MOVQ dest src s =
    let (x:M word) = read src s in
    let (x':64 word) = word_zx x in
    let (x'':N word) = word_zx x' in
    (dest := x'') s`;;

let x86_VMOVD = new_definition
 `x86_VMOVD dest src s =
    let (x:M word) = read src s in
    let (x':N word) = word_zx x in
    (dest := x') s`;;

(*** The intermediate forcing to 64 bits is for VMOVQ xmmM, xmmN  ***)

let x86_VMOVQ = new_definition
 `x86_VMOVQ dest src s =
    let (x:M word) = read src s in
    let (x':64 word) = word_zx x in
    let (x'':N word) = word_zx x' in
    (dest := x'') s`;;

let x86_VMOVHPD = new_definition
 `x86_VMOVHPD dest src s =
    let (x:128 word) = read src s in
    let (x':64 word) = word_subword x (64, 64) in
    (dest := x') s`;;

let x86_MOVUPS = new_definition
 `x86_MOVUPS dest src s =
    let x = read src s in (dest := x) s`;;

(*** This has a complicated iterative semantics via the
 *** auxiliary function x86_movsb (in lowercase). Here
 *** the "rept" argument is true iff this is a repeated
 *** instance REP MOVSB.
 ***)

let x86_MOVSB = new_definition
 `x86_MOVSB rept dest src size s =
        let sptr = read src s
        and dptr = read dest s
        and n:int64 = read size s
        and df = read DF s in
        let sbuf = if df then word_sub sptr (word_sub n (word 1)) else sptr
        and dbuf = if df then word_sub dptr (word_sub n (word 1)) else dptr in
        (events := CONS (EventStore(dbuf,val n))
                        (CONS (EventLoad(sbuf,val n)) (read events s)) ,,
         (\s s'. x86_movsb df sbuf dbuf (val n) s = s') ,,
         src := (if df then word_sub sptr n else word_add sptr n) ,,
         dest := (if df then word_sub dptr n else word_add dptr n) ,,
         (if rept then size := word 0 else (=))) s`;;

(*** These are rare cases with distinct source and destination
 *** operand sizes. There is a 32-bit to 64-bit version of MOVSX(D),
 *** whereas the corresponding MOVZX is not encodable; the operation
 *** can be done anyway by the usual 32-bit MOV in 64-bit mode.
 ***
 *** A bit bizarrely there are same-size versions of MOVSXD.
 *** These are really just freaks of decoding, with semantics
 *** equivalent to MOV, and use is actively discouraged in
 *** the Intel manuals ("The use of MOVSXD without REX.W in
 *** 64-bit mode is discouraged".) However, we do handle
 *** the 32->32 case anyway, though not the 16->16 case, in
 *** line with the general policy of rejecting operand size
 *** override prefixes unless the instructions are useful.
 ***)

let x86_MOVSX = new_definition
 `x86_MOVSX dest src s =
        let (x:M word) = read src s in
        let (x':N word) = word_sx x in
        (dest := x') s`;;

let x86_MOVZX = new_definition
 `x86_MOVZX dest src s =
        let (x:M word) = read src s in
        let (x':N word) = word_zx x in
        (dest := x') s`;;

(*** See comments above for IMUL. No other version of unsigned mul ***)

let x86_MULX4 = new_definition
 `x86_MULX4 (dest_hi,dest_lo) (src1,src2) s =
        let (x:N word) = read src1 s and (y:N word) = read src2 s in
        let z = word(val x * val y):(N tybit0)word in
        let z_hi:N word = word_zx (word_ushr z (dimindex(:N)))
        and z_lo:N word = word_zx z in
        (dest_lo := z_lo ,,
         dest_hi := z_hi) s`;;

let x86_MUL2 = new_definition
 `x86_MUL2 (dest_hi,dest_lo) src s =
        let (x:N word) = read dest_lo s and (y:N word) = read src s in
        let z = word(val x * val y):(N tybit0)word in
        let z_hi:N word = word_zx (word_ushr z (dimindex(:N)))
        and z_lo:N word = word_zx z in
        (dest_hi := z_hi ,,
         dest_lo := z_lo ,,
         CF := ~(z_hi = word 0) ,,
         OF := ~(z_hi = word 0) ,,
         UNDEFINED_VALUES[ZF;SF;PF;AF]) s`;;

(*** Note that the Intel documentation states the CF setting very explicitly
 *** as "the source operand is nonzero". So I copy that here. But it is just
 *** the same as the uniform value you'd get from 0 - x

  WORD_ARITH
   `&(val(word_sub x y)):int = &(val x) - &(val y) <=> val y <= val x`;;

  WORD_ARITH
    `-- (&(val x)):int = &(val(word_neg x)) <=> x = word 0`;;

 ***)

let x86_NEG = new_definition
 `x86_NEG dest s =
        let x = read dest s in
        let z = word_neg x in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(x = word 0) ,,
         OF := ~(-- ival x = ival z) ,,
         AF := ~(-- &(val(word_zx x:nybble)):int =
                 &(val(word_zx z:nybble)))) s`;;

let x86_NOP = new_definition
 `x86_NOP (s:x86state) = \s'. s = s'`;;

(*
  The multi-byte form of NOP is available on processors with model encoding:
  CPUID.01H.EAX[Bytes 11:8] = 0110B or 1111B
*)
let x86_NOP_N = new_definition
 `x86_NOP_N dest (s:x86state) = \s'. s = s'`;;

(*** In contrast to most logical ops, NOT doesn't affect any flags ***)

let x86_NOT = new_definition
 `x86_NOT dest s =
        let x = read dest s in
        let z = word_not x in
        (dest := (z:N word)) s`;;

let x86_OR = new_definition
 `x86_OR dest src s =
        let x = read dest s and y = read src s in
        let z = word_or x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

let x86_PADDD = new_definition
  `x86_PADDD dest src s =
    let x = read dest s in
    let y = read src s in
    let res:(128)word = simd4 word_add x y in
    (dest := res) s`;;

let x86_PADDQ = new_definition
  `x86_PADDQ dest src s =
    let x = read dest s in
    let y = read src s in
    let res:(128)word = simd2 word_add x y in
    (dest := res) s`;;

let x86_PAND = new_definition
  `x86_PAND dest src s =
    let x = read dest s in
    let y = read src s in
    (dest := word_and x y) s`;;

let x86_PBLENDW = new_definition
 `x86_PBLENDW dest src imm8 (s:x86state) =
     let x:int128 = read dest s
     and y:int128 = read src s
     and imm8:byte = read imm8 s in
     let fn = \(i:1 word) (x:16 word) (y:16 word). if i = word 1 then y else x in
     let res = msimd8 fn imm8 x y in
     (dest := res) s`;;

let x86_PCMPGTD = new_definition
  `x86_PCMPGTD dest src s =
    let x = read dest s in
    let y = read src s in
    let res:(128)word = simd4 (\(x:32 word) (y:32 word).
        if word_igt x y then (word 0xffffffff) else (word 0))
        x y in
    (dest := res) s`;;

let x86_PCMPGTW = new_definition
  `x86_PCMPGTW dest src s =
    let x = read dest s in
    let y = read src s in
    let res:(128)word = simd8 (\(x:16 word) (y:16 word).
        if word_igt x y then (word 0xffff) else (word 0))
        x y in
    (dest := res) s`;;

let x86_PEXT = new_definition
  `x86_PEXT dest src1 src2 (s:x86state) =
    let x:N word = read src1 s
    and y:N word = read src2 s in
    let res = word_condense x y in
    (events := CONS (EventX86PEXT(word_zx x, word_zx y, dimindex(:N)))
                    (read events s) ,,
     dest := res) s`;;

let x86_PINSRD = new_definition
 `x86_PINSRD dest src imm8 (s:x86state) =
    let x:int128 = read dest s
    and w:int32 = read src s
    and sel = val(read imm8 s:byte) MOD 4 in
    let res = word_insert x (32 * sel,32) w in
    (dest := res) s`;;

let x86_PINSRQ = new_definition
 `x86_PINSRQ dest src imm8 (s:x86state) =
    let x:int128 = read dest s
    and w:int64 = read src s
    and sel = val(read imm8 s:byte) MOD 2 in
    let res = word_insert x (64 * sel,64) w in
    (dest := res) s`;;

let x86_PMOVMSKB = new_definition
 `x86_PMOVMSKB dest src (s:x86state) =
    let x:int128 = read src s in
    let res:int16 = usimd16 (\x. if bit 7 x then word 1 else word 0) x in
    (dest := word_zx res:N word) s`;;

let x86_VMOVMSKPS = new_definition
 `x86_VMOVMSKPS dest src (s:x86state) =
    let x:int256 = read src s in
    let res:byte = word(
      bitval(bit 31 (word_subword x (0,32):int32)) +
      2 * bitval(bit 31 (word_subword x (32,32):int32)) +
      4 * bitval(bit 31 (word_subword x (64,32):int32)) +
      8 * bitval(bit 31 (word_subword x (96,32):int32)) +
      16 * bitval(bit 31 (word_subword x (128,32):int32)) +
      32 * bitval(bit 31 (word_subword x (160,32):int32)) +
      64 * bitval(bit 31 (word_subword x (192,32):int32)) +
      128 * bitval(bit 31 (word_subword x (224,32):int32))) in
    (dest := word_zx res:int32) s`;;

let x86_VPMOVMSKB = new_definition
 `x86_VPMOVMSKB dest src (s:x86state) =
    let x:int256 = read src s in
    (dest := word(nsum (0..31)
                   (\i. 2 EXP i *
                        bitval(bit 7 (word_subword x (8 * i,8):byte))))
            :int32) s`;;

(*** Push and pop are a bit odd in several ways. First of all, there is  ***)
(*** an implicit memory operand so this doesn't have quite the same      ***)
(*** "shallowness": we refer to the memory component explicitly. And we  ***)
(*** need to adjust the sizes dynamically and hence use x:num inside.    ***)
(*** Note that in 64-bit mode you can only have sizes 16 or 64 so the    ***)
(*** full genericity of this function is not used in our setting.        ***)
(*** Finally, we ignore all the versions with segment registers.         ***)
(*** The handling of pushing and popping RSP itself is an obvious corner ***)
(*** case in which the documentation is poor, and completely different   ***)
(*** (at least in style if not intended meaning) in the Intel and AMD    ***)
(*** manuals. Nevertheless I believe the treatment here is right.        ***)

let x86_POP = new_definition
 `x86_POP dest s =
        let n = dimindex(:N) DIV 8 in
        let p = read RSP s in
        let x:N word = word(read (memory :> bytes(p,n)) s) in
        let p' = word_add p (word n) in
        (events := CONS (EventLoad (p, n)) (read events s) ,,
         RSP := p' ,,
         dest := x) s`;;

let x86_POPCNT = new_definition
 `x86_POPCNT dest src s =
    let x:N word = read src s in
    let z:N word = word(word_popcount x) in
     (events := CONS (EventX86POPCNT(word_zx x, dimindex(:N)))
                     (read events s) ,,
      dest := (z:N word) ,,
      OF := F ,,
      SF := F ,,
      AF := F ,,
      CF := F ,,
      PF := F ,,
      ZF := (val x = 0)) s`;;

let x86_PUSH = new_definition
 `x86_PUSH src s =
        let n = dimindex(:N) DIV 8 in
        let p = read RSP s
        and x = val(read src s:N word) in
        let p' = word_sub p (word n) in
        (events := CONS (EventStore (p', n)) (read events s) ,,
         RSP := p' ,,
         memory :> bytes(p',n) := x) s`;;

let x86_PSHUFB = new_definition
  `x86_PSHUFB dest src (s:x86state) =
      let x:int128 = read dest s
      and ix = read src s in
      let f8 = (\i:byte.
        if bit 7 i then word 0
        else word_subword x (8 * val(word_subword i (0,4):nybble),8)) in
      let res = usimd16 f8 ix in
      (dest := res) s`;;

let x86_PSHUFD = new_definition
 `x86_PSHUFD dest src imm8 s =
    let src = read src s in
    let od = read imm8 s in
    let res:(128)word = usimd4 (\(od:(2)word).
        word_subword src ((val od)*32,32)) od in
    (dest := res) s`;;

let x86_PSRAD = new_definition
  `x86_PSRAD dest imm8 s =
    let d = read dest s in
    let count = val (read imm8 s) in
    let res:(128)word = usimd4 (\x. word_ishr x count) d in
    (dest := res) s`;;

let x86_PSRLW = new_definition
  `x86_PSRLW dest imm8 s =
    let d = read dest s in
    let count = val (read imm8 s) in
    let res:(128)word = usimd8 (\x. word_ushr x count) d in
    (dest := res) s`;;

let x86_PXOR = new_definition
  `x86_PXOR dest src s =
    let x = read dest s in
    let y = read src s in
    (dest := word_xor x y) s`;;

(*** Out of alphabetical order as PUSH is a subroutine ***)

let x86_CALL = new_definition
 `x86_CALL target s =
    (events := CONS (EventJump (read RIP s, target)) (read events s) ,,
     x86_PUSH RIP ,,
     RIP := target) s`;;

(*** We don't distinguish near/far and don't have the form with the ***)
(*** additional "release more bytes" argument, so it's quite simple ***)

let x86_RET = new_definition
 `x86_RET s =
        let p = read RSP s in
        let p' = word_add p (word 8)
        and ip' = read (memory :> bytes64 p) s in
        (events := CONS (EventJump (read RIP s, ip'))
            (CONS (EventLoad (p,8)) (read events s)) ,,
         RSP := p' ,, RIP := ip') s`;;

(*** Shift and rotate operations mask to 5 bits, or 6 bits in 64-bit     ***)
(*** Actually it's even more complicated for RCL and RCR in general:     ***)
(*** for sizes 8 and 16 they go mod 9 and 17 (natural enough) but then   ***)
(*** 32-bit and 64-bit forms just mask as in the others. Not generic.    ***)

(*** It's not quite enough to just use the native size, as certain       ***)
(*** things are different in case masked_shift IN {0,1} (e.g. OF)        ***)
(*** We assume that the masked value comes in from the decoder           ***)
(*** Our underlying rotate functions are modulo anyway.                  ***)
(*** It is at least clearly stated that SF, ZF, AF, PF are unaffected    ***)
(*** It's also stated that no flags are affected for zero masked count   ***)
(*** The manual is confusing about "affected" versus "defined" on the    ***)
(*** OF result for counts > 1.                                           ***)

(*** Note that in the unpacking of the actual instructions below we can  ***)
(*** assume the shift is an 8-bit operand (an immediate or CL, in fact   ***)
(*** in the actual encodings.)                                           ***)

(*** Note that RCL and RCR don't special case the zero for CF, since     ***)
(*** it will anyway be the input CF in that case                         ***)

(*** The OF definitions are confusing but I hope correct.                ***)

let x86_RCL = new_definition
 `x86_RCL dest c s =
        let x = read dest s
        and cin = read CF s in
        let xx:((1,N)finite_sum)word = word_join (word(bitval cin):1 word) x in
        let zz = word_rol xx c in
        let z = word_subword zz (0,dimindex(:N))
        and cout = bit (dimindex(:N)) zz in
        (dest := (z:N word) ,,
         CF := cout ,,
         (if c = 0 then
               OF := read OF s
          else if c = 1 then
               OF := ~(bit (dimindex(:N)-1) z = cout)
          else UNDEFINED_VALUES[OF])) s`;;

let x86_RCR = new_definition
 `x86_RCR dest c s =
        let x = read dest s
        and cin = read CF s in
        let xx:((1,N)finite_sum)word = word_join (word(bitval cin):1 word) x in
        let zz = word_ror xx c in
        let z = word_subword zz (0,dimindex(:N))
        and cout = bit (dimindex(:N)) zz in
        (dest := (z:N word) ,,
         CF := cout ,,
         (if c = 0 then
            OF := read OF s
          else if c = 1 then
            OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-2) z)
          else UNDEFINED_VALUES[OF])) s`;;

let x86_ROL = new_definition
 `x86_ROL dest c s =
        let x = read dest s in
        let z = word_rol x c in
        (dest := (z:N word) ,,
         CF := (if c = 0 then read CF s else bit 0 z) ,,
         (if c = 0 then
            OF := read OF s
          else if c = 1 then
            OF := ~(bit (dimindex(:N)-1) z = bit 0 z)
          else UNDEFINED_VALUES[OF])) s`;;

let x86_ROR = new_definition
 `x86_ROR dest c s =
        let x = read dest s in
        let z = word_ror x c in
        (dest := (z:N word) ,,
         CF := (if c = 0 then read CF s else bit (dimindex(:N)-1) z) ,,
         (if c = 0 then
            OF := read OF s
          else if c = 1 then
            OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-2) z)
          else UNDEFINED_VALUES[OF])) s`;;

(*** Note that SAL and SHL are the same thing ***)

let x86_SAR = new_definition
 `x86_SAR dest c s =
      let x = read dest s in
      let z = word_ishr x c in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit 0 (word_ishr x (c - 1))) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := F
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SBB = new_definition
 `x86_SBB dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_sub x (word_add y (word c)) in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(&(val x) - (&(val y) + &c):int = &(val z)) ,,
         OF := ~(ival x - (ival y + &c) = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) -
                 (&(val(word_zx y:nybble)) + &c):int =
                 &(val(word_zx z:nybble)))) s`;;

(*** Note: SET is only ever applied to 8-bit operands, so we build
 *** this into the type, in contrast to most of the other cases where
 *** this is generic
 ***)

let x86_SET = new_definition
 `x86_SET cc dest s =
          (dest := (if condition_semantics cc s then
                    word 1:byte else word 0)) s`;;

let x86_SHL = new_definition
 `x86_SHL dest c s =
      let x = read dest s in
      let z = word_shl x c in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s
              else bit (dimindex(:N)-1) (word_shl x (c - 1))) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := ~(bit (dimindex(:N)-1) x = bit (dimindex(:N)-2) x)
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SHLD = new_definition
 `x86_SHLD dest src c s =
      let h:N word = read dest s
      and l:N word = read src s in
      let concat:(N tybit0)word = word_join h l in
      let z:N word = word_subword concat (dimindex(:N) - c,dimindex(:N)) in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit (dimindex(:N) - c) h) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-1) h)
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SHR = new_definition
 `x86_SHR dest c s =
      let x = read dest s in
      let z = word_ushr x c in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit 0 (word_ushr x (c - 1))) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := bit (dimindex(:N)-1) x
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_SHRD = new_definition
 `x86_SHRD dest src c s =
      let h:N word = read src s
      and l:N word = read dest s in
      let concat:(N tybit0)word = word_join h l in
      let z:N word = word_subword concat (c,dimindex(:N)) in
      (dest := (z:N word) ,,
       ZF := (if c = 0 then read ZF s else val z = 0) ,,
       SF := (if c = 0 then read SF s else ival z < &0) ,,
       PF := (if c = 0 then read PF s else word_evenparity(word_zx z:byte)) ,,
       CF := (if c = 0 then read CF s else bit (c - 1) l) ,,
       (if c = 0 then
          OF := read OF s
        else if c = 1 then
          OF := ~(bit (dimindex(:N)-1) z = bit (dimindex(:N)-1) l)
        else UNDEFINED_VALUES[OF]) ,,
       (if c = 0 then
          AF := read AF s
        else UNDEFINED_VALUES[AF])) s`;;

let x86_STC = new_definition
 `x86_STC s =
        (CF := T) s`;;

let x86_STD = new_definition
 `x86_STD s =
        (DF := T) s`;;

let x86_SUB = new_definition
 `x86_SUB dest src s =
        let x = read dest s and y = read src s in
        let z = word_sub x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := ~(&(val x) - &(val y):int = &(val z)) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`;;

let x86_VMOVSLDUP = new_definition
  `x86_VMOVSLDUP dest src (s:x86state) =
      let (x:N word) = read src s in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd4 (\(pair:64 word).
          word_duplicate (word_subword pair (0,32):(32)word):(64)word)
          (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd2 (\(pair:64 word).
          word_duplicate (word_subword pair (0,32):(32)word):(64)word)
          (word_zx x) in
        (dest := (word_zx res):N word) s`;;

let x86_VMOVDQA = new_definition
  `x86_VMOVDQA dest src (s:x86state) =
      let (x:N word) = read src s in (dest := x) s`;;

let x86_VMOVDQU = new_definition
  `x86_VMOVDQU dest src (s:x86state) =
      let (x:N word) = read src s in (dest := x) s`;;

let x86_VMOVSHDUP = new_definition
  `x86_VMOVSHDUP dest src (s:x86state) =
      let (x:N word) = read src s in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd4 (\(pair:64 word).
          word_duplicate (word_subword pair (32,32):(32)word):(64)word)
          (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd2 (\(pair:64 word).
          word_duplicate (word_subword pair (32,32):(32)word):(64)word)
          (word_zx x) in
        (dest := (word_zx res):N word) s`;;

let x86_VPADDB = new_definition
  `x86_VPADDB dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let res:(256)word = simd32 word_add (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd16 word_add (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPADDD = new_definition
  `x86_VPADDD dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let res:(256)word = simd8 word_add (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd4 word_add (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPADDQ = new_definition
  `x86_VPADDQ dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let res:(256)word = simd4 word_add (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd2 word_add (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPADDW = new_definition
  `x86_VPADDW dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let res:(256)word = simd16 word_add (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd8 word_add (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPBLENDD = new_definition
  `x86_VPBLENDD dest src1 src2 imm8 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s
      and imm8 = read imm8 s in
      let fn = \(i:1 word) (x:32 word) (y:32 word). if i = word 1 then y else x in
      if dimindex(:N) = 256 then
        let res:(256)word = msimd8 fn (word_zx imm8) (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = msimd4 fn (word_zx imm8) (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPBLENDW = new_definition
  `x86_VPBLENDW dest src1 src2 imm8 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s
      and imm8 = read imm8 s in
      let fn = \(i:1 word) (x:16 word) (y:16 word). if i = word 1 then y else x in
      if dimindex(:N) = 256 then
        let res:(256)word = msimd16 fn (word_join imm8 imm8) (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = msimd8 fn (word_zx imm8) (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPCLMULQDQ = new_definition
  `x86_VPCLMULQDQ dest src1 src2 ibyte (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s
      and imm:byte = read ibyte s in
      let f = \(x:128 word) (y:128 word).
        let a:int64 = if bit 0 imm
                      then word_subword x (64,64)
                      else word_subword x (0,64)
        and b:int64 = if bit 4 imm
                      then word_subword y (64,64)
                      else word_subword y (0,64) in
        (word_pmul a b:128 word) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd2 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPBROADCASTD = new_definition
  `x86_VPBROADCASTD (dest:(x86state,(N)word)component) src (s:x86state) =
      let (x:M word) = read src s in
      let dw = word_subword x (0,32):(32)word in
      let res:N word = word_duplicate dw in
      (dest := res) s`;;

let x86_VPBROADCASTQ = new_definition
  `x86_VPBROADCASTQ (dest:(x86state,(N)word)component) src (s:x86state) =
      let (x:M word) = read src s in
      let qw = word_subword x (0,64):(64)word in
      let res:N word = word_duplicate qw in
      (dest := res) s`;;

let x86_VPBROADCASTW = new_definition
  `x86_VPBROADCASTW (dest:(x86state,(N)word)component) src (s:x86state) =
      let (x:M word) = read src s in
      let ww = word_subword x (0,16):(16)word in
      let res:N word = word_duplicate ww in
      (dest := res) s`;;

let x86_VPBLENDVB = new_definition
  `x86_VPBLENDVB dest src1 src2 mask (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s
      and (m:N word) = read mask s in
      if dimindex(:N) = 256 then
        let x256:(256)word = word_zx x in
        let y256:(256)word = word_zx y in
        let m256:(256)word = word_zx m in
        let res:(256)word = word
          (nsum (0..31) (\i.
            val(if bit (8*i+7) m256
                then (word_subword y256 (8*i,8):byte)
                else (word_subword x256 (8*i,8):byte)) * 2 EXP (8*i))) in
        (dest := (word_zx res):N word) s
      else
        let x128:(128)word = word_zx x in
        let y128:(128)word = word_zx y in
        let m128:(128)word = word_zx m in
        let res:(128)word = word
          (nsum (0..15) (\i.
            val(if bit (8*i+7) m128
                then (word_subword y128 (8*i,8):byte)
                else (word_subword x128 (8*i,8):byte)) * 2 EXP (8*i))) in
        (dest := (word_zx res):N word) s`;;

let x86_VPABSD = new_definition
  `x86_VPABSD dest src (s:x86state) =
      let (x:N word) = read src s in
      let f = (\(a:int32).
          if word_igt (word 0:int32) a then word_neg a else a) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd8 f (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd4 f (word_zx x) in
        (dest := (word_zx res):N word) s`;;

let x86_VPACKUSWB = new_definition
  `x86_VPACKUSWB dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      let sat = (\(w:int16).
        word(MIN (if bit 15 w then 0 else val w) 255):byte) in
      if dimindex(:N) = 256 then
        let x256:(256)word = word_zx x in
        let y256:(256)word = word_zx y in
        let res:(256)word = word
          (nsum (0..7) (\i. val(sat(word_subword x256 (16*i,16))) * 2 EXP (8*i)) +
           nsum (0..7) (\i. val(sat(word_subword y256 (16*i,16))) * 2 EXP (8*(i+8))) +
           nsum (0..7) (\i. val(sat(word_subword x256 (128+16*i,16))) * 2 EXP (8*(i+16))) +
           nsum (0..7) (\i. val(sat(word_subword y256 (128+16*i,16))) * 2 EXP (8*(i+24)))) in
        (dest := (word_zx res):N word) s
      else
        let x128:(128)word = word_zx x in
        let y128:(128)word = word_zx y in
        let res:(128)word = word
          (nsum (0..7) (\i. val(sat(word_subword x128 (16*i,16))) * 2 EXP (8*i)) +
           nsum (0..7) (\i. val(sat(word_subword y128 (16*i,16))) * 2 EXP (8*(i+8)))) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMADDUBSW = new_definition
  `x86_VPMADDUBSW dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      let f = (\(x:16 word) (y:16 word).
        let prod1:int32 =
          word_mul (word_zx ((word_subword:int16->num#num->byte) x (0,8)))
                   (word_sx ((word_subword:int16->num#num->byte) y (0,8))) in
        let prod2:int32 =
          word_mul (word_zx ((word_subword:int16->num#num->byte) x (8,8)))
                   (word_sx ((word_subword:int16->num#num->byte) y (8,8))) in
        let tot:int32 = word_add prod1 prod2 in
        if bit 31 tot = bit 15 tot
        then (word_subword:int32->num#num->int16) tot (0,16)
        else if bit 31 tot then (word 32768:int16)
        else (word 32767:int16)) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd16 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd8 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMADDWD = new_definition
  `x86_VPMADDWD dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      let f = (\(x:32 word) (y:32 word).
        word_add
          (word_mul (word_sx ((word_subword:int32->num#num->int16) x (0,16)))
                    (word_sx ((word_subword:int32->num#num->int16) y (0,16))))
          (word_mul (word_sx ((word_subword:int32->num#num->int16) x (16,16)))
                    (word_sx ((word_subword:int32->num#num->int16) y (16,16))))) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd8 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd4 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMULDQ = new_definition
  `x86_VPMULDQ dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      let f =
        \x y. word_mul
          (word_sx ((word_subword:int64->num#num->int32) x (0,32)))
          (word_sx ((word_subword:int64->num#num->int32) y (0,32))) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd4 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd2 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMOVZXBD = new_definition
  `x86_VPMOVZXBD dest src (s:x86state) =
      let (x:M word) = read src s in
      let f = \(b:byte). word_zx b:int32 in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd8 f (word_zx x:int64) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd4 f (word_zx x:int32) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMOVZXBW = new_definition
  `x86_VPMOVZXBW dest src (s:x86state) =
      let (x:M word) = read src s in
      let f = \(b:byte). word_zx b:16 word in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd16 f (word_zx x:int128) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd8 f (word_zx x:int64) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMOVSXBD = new_definition
  `x86_VPMOVSXBD dest src (s:x86state) =
      let (x:M word) = read src s in
      let f = \(b:byte). word_sx b:int32 in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd8 f (word_zx x:int64) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd4 f (word_zx x:int32) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMULHRSW = new_definition
  `x86_VPMULHRSW dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      let f = (\(x:16 word) (y:16 word).
               let prod:int32 = word_mul (word_sx x) (word_sx y) in
               word_subword (word_add (word_ushr prod 14) (word 1:int32)) (1,16)) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd16 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd8 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMULHW = new_definition
  `x86_VPMULHW dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      let f = (\(x:16 word) (y:16 word). word_subword (word_mul ((word_sx x):int32) ((word_sx y):int32)) (16,16)) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd16 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd8 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMULHUW = new_definition
  `x86_VPMULHUW dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      let f = (\(x:16 word) (y:16 word). word_subword (word_mul ((word_zx x):int32) ((word_zx y):int32)) (16,16)) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd16 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd8 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMULLD = new_definition
  `x86_VPMULLD dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let res:(256)word = simd8 word_mul (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd4 word_mul (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPMULLW = new_definition
  `x86_VPMULLW dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let res:(256)word = simd16 word_mul (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd8 word_mul (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPSLLVD = new_definition
  `x86_VPSLLVD dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (c:N word) = read src2 s in
      let f = (\(x:32 word) (c:32 word). word_shl x (MIN (val c) 32)) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd8 f (word_zx x) (word_zx c) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd4 f (word_zx x) (word_zx c) in
        (dest := (word_zx res):N word) s`;;

(* Only VPSLLD version where shift count is an immediate value is supported *)
let x86_VPSLLD = new_definition
  `x86_VPSLLD dest src imm8 (s:x86state) =
      let (x:N word) = read src s in
      let count = val (read imm8 s) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd8 (\z. word_shl z count) (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd4 (\z. word_shl z count) (word_zx x) in
        (dest := (word_zx res):N word) s`;;

let x86_VPSLLQ = new_definition
  `x86_VPSLLQ dest src imm8 (s:x86state) =
      let (x:N word) = read src s in
      let count = val (read imm8 s) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd4 (\z. word_shl z count) (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd2 (\z. word_shl z count) (word_zx x) in
        (dest := (word_zx res):N word) s`;;

(* Only VPSLLW version where shift count is an immediate value is supported *)
let x86_VPSLLW = new_definition
  `x86_VPSLLW dest src imm8 (s:x86state) =
      let (x:N word) = read src s in
      let count = val (read imm8 s) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd16 (\z. word_shl z count) (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd8 (\z. word_shl z count) (word_zx x) in
        (dest := (word_zx res):N word) s`;;

let x86_VPERMD = new_definition
  `x86_VPERMD dest src1 src2 (s:x86state) =
      let ix:int256 = read src1 s
      and x:int256 = read src2 s in
      let res:int256 = usimd8
       (\i. word_subword x (32 * val(word_subword i (0,3):3 word),32)) ix in
      (dest := res) s`;;

let x86_VPERMQ = new_definition
  `x86_VPERMQ dest src imm8 (s:x86state) =
      let (x:N word) = read src s
      and od = read imm8 s in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd4 (\(od:(2)word).
            (word_subword:int256->num#num->int64) (word_zx x) ((val od)*64,64)) od in
        (dest := (word_zx res):N word) s
      else
        raise_exception x86_Exception_UD s`;;

let x86_VPERM2I128 = new_definition
  `x86_VPERM2I128 dest src1 src2 imm8 (s:x86state) =
      let (x1:N word) = read src1 s
      and (x2:N word) = read src2 s
      and od = read imm8 s in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd2 (\(od:(4)word).
            let sel = val od in
            let zero_flag = (sel DIV 8) MOD 2 = 1 in
            if zero_flag then (word 0):int128
            else
              let lane_sel = sel MOD 4 in
              if lane_sel = 0 then (word_subword:int256->num#num->int128) (word_zx x1) (0,128)
              else if lane_sel = 1 then (word_subword:int256->num#num->int128) (word_zx x1) (128,128)
              else if lane_sel = 2 then (word_subword:int256->num#num->int128) (word_zx x2) (0,128)
              else (word_subword:int256->num#num->int128) (word_zx x2) (128,128)) od in
        (dest := (word_zx res):N word) s
      else
        raise_exception x86_Exception_UD s`;;

let x86_VPINSRD = new_definition
 `x86_VPINSRD dest src1 src2 imm8 (s:x86state) =
    let x:int128 = read src1 s
    and w:int32 = read src2 s
    and sel = val(read imm8 s:byte) MOD 4 in
    let res = word_insert x (32 * sel,32) w in
    (dest := res) s`;;

let x86_VPINSRQ = new_definition
 `x86_VPINSRQ dest src1 src2 imm8 (s:x86state) =
    let x:int128 = read src1 s
    and w:int64 = read src2 s
    and sel = val(read imm8 s:byte) MOD 2 in
    let res = word_insert x (64 * sel,64) w in
    (dest := res) s`;;

let x86_VPINSRW = new_definition
 `x86_VPINSRW dest src1 src2 imm8 (s:x86state) =
    let x:int128 = read src1 s
    and w:int16 = word_subword (read src2 s:M word) (0,16)
    and sel = val(read imm8 s:byte) MOD 8 in
    let res = word_insert x (16 * sel,16) w in
    (dest := res) s`;;

let x86_VPEXTRD = new_definition
 `x86_VPEXTRD dest src imm8 (s:x86state) =
    let x:int128 = read src s
    and sel = val(read imm8 s:byte) MOD 4 in
    let res = word_subword x (32 * sel, 32) in
    (dest := res) s`;;

let x86_VPEXTRQ = new_definition
 `x86_VPEXTRQ dest src imm8 (s:x86state) =
    let x:int128 = read src s
    and sel = val(read imm8 s:byte) MOD 2 in
    let res = word_subword x (64 * sel, 64) in
    (dest := res) s`;;

let x86_VPEXTRW = new_definition
 `x86_VPEXTRW dest src imm8 (s:x86state) =
    let x:int128 = read src s
    and sel = val(read imm8 s:byte) MOD 8 in
    let (res:int16) = word_subword x (16 * sel, 16) in
    let (r:N word) = word_zx res in
    (dest := r) s`;;

let x86_VINSERTI128 = new_definition
 `x86_VINSERTI128 dest src1 src2 imm8 (s:x86state) =
    let x:int256 = read src1 s
    and w:int128 = read src2 s
    and sel = val(read imm8 s:byte) MOD 2 in
    let res = word_insert x (128 * sel,128) w in
    (dest := res) s`;;

let x86_VEXTRACTI128 = new_definition
 `x86_VEXTRACTI128 dest src imm8 (s:x86state) =
    let x:int256 = read src s
    and sel = val(read imm8 s:byte) MOD 2 in
    let res = word_subword x (128 * sel, 128) in
    (dest := res) s`;;

let x86_VPSHUFB = new_definition
  `x86_VPSHUFB dest src1 src2 (s:x86state) =
      let x:N word = read src1 s
      and ix:N word = read src2 s in
      let f8 = (\(w:int128) (i:byte).
        if bit 7 i then word 0
        else word_subword (w:int128)
                          (8 * val(word_subword i (0,4):nybble),8)) in
      let f128 = \w y. usimd16 (f8 w) y in
      if dimindex(:N) = 256 then
        let res = simd2 f128 (word_zx x) (word_zx ix) in
        (dest := (word_zx res):N word) s
      else
        let res = f128 (word_zx x) (word_zx ix) in
        (dest := (word_zx res):N word) s`;;

let x86_VPSUBB = new_definition
  `x86_VPSUBB dest src1 src2 (s:x86state) =
      let x:N word = read src1 s
      and y:N word = read src2 s in
      let fb = \(a:byte) (b:byte). word_sub a b in
      let f128 = \(w1:int128) (w2:int128). simd16 fb w1 w2 in
      if dimindex(:N) = 256 then
        let res = simd2 f128 (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res = f128 (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPSUBD = new_definition
  `x86_VPSUBD dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let res:(256)word = simd8 word_sub (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd4 word_sub (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPSUBQ = new_definition
  `x86_VPSUBQ dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let res:(256)word = simd4 word_sub (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd2 word_sub (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPSUBW = new_definition
  `x86_VPSUBW dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let res:(256)word = simd16 word_sub (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd8 word_sub (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPCMPGTD = new_definition
  `x86_VPCMPGTD dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      let f = (\(a:32 word) (b:32 word).
          if word_igt a b then (word 0xffffffff) else (word 0)) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd8 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd4 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

let x86_VPCMPGTW = new_definition
  `x86_VPCMPGTW dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      let f = (\(a:16 word) (b:16 word).
          if word_igt a b then (word 0xffff) else (word 0)) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd16 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd8 f (word_zx x) (word_zx y) in
        (dest := (word_zx res):N word) s`;;

(* Only VPSRAD version where shift count is an immediate value is supported *)
let x86_VPSRAD = new_definition
  `x86_VPSRAD dest src imm8 (s:x86state) =
      let (x:N word) = read src s in
      let count = val (read imm8 s) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd8 (\z. word_ishr z count) (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd4 (\z. word_ishr z count) (word_zx x) in
        (dest := (word_zx res):N word) s`;;

let x86_VPSRLVD = new_definition
  `x86_VPSRLVD dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (c:N word) = read src2 s in
      let f = (\(x:32 word) (c:32 word). word_ushr x (MIN (val c) 32)) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd8 f (word_zx x) (word_zx c) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd4 f (word_zx x) (word_zx c) in
        (dest := (word_zx res):N word) s`;;

(* VPSRLVQ: variable right shift on 64-bit lanes, following VPSRLVD/VPMULDQ *)
let x86_VPSRLVQ = new_definition
  `x86_VPSRLVQ dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (c:N word) = read src2 s in
      let f = (\(x:64 word) (c:64 word). word_ushr x (MIN (val c) 64)) in
      if dimindex(:N) = 256 then
        let res:(256)word = simd4 f (word_zx x) (word_zx c) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = simd2 f (word_zx x) (word_zx c) in
        (dest := (word_zx res):N word) s`;;

(* Only VPSRLD version where shift count is an immediate value is supported *)
let x86_VPSRLD = new_definition
  `x86_VPSRLD dest src imm8 (s:x86state) =
      let (x:N word) = read src s in
      let count = val (read imm8 s) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd8 (\z. word_ushr z count) (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd4 (\z. word_ushr z count) (word_zx x) in
        (dest := (word_zx res):N word) s`;;

(* Only VPSRLQ version where shift count is an immediate value is supported *)
let x86_VPSRLQ = new_definition
  `x86_VPSRLQ dest src imm8 (s:x86state) =
      let (x:N word) = read src s in
      let count = val (read imm8 s) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd4 (\z. word_ushr z count) (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd2 (\z. word_ushr z count) (word_zx x) in
        (dest := (word_zx res):N word) s`;;

let x86_VPSRLDQ = new_definition
  `x86_VPSRLDQ dest src imm8 (s:x86state) =
      let (x:N word) = read src s in
      let count = 8 * val (read imm8 s) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd2 (\z. word_ushr z count) (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let x128:(128)word = word_zx x in
        let res:(128)word = word_ushr x128 count in
        (dest := (word_zx res):N word) s`;;

(* Only VPSRAW version where shift count is an immediate value is supported *)
let x86_VPSRAW = new_definition
  `x86_VPSRAW dest src imm8 (s:x86state) =
      let (x:N word) = read src s in
      let count = val (read imm8 s) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd16 (\z. word_ishr z count) (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd8 (\z. word_ishr z count) (word_zx x) in
        (dest := (word_zx res):N word) s`;;

(* Only VPSRLW version where shift count is an immediate value is supported *)
let x86_VPSRLW = new_definition
  `x86_VPSRLW dest src imm8 (s:x86state) =
      let (x:N word) = read src s in
      let count = val (read imm8 s) in
      if dimindex(:N) = 256 then
        let res:(256)word = usimd16 (\z. word_ushr z count) (word_zx x) in
        (dest := (word_zx res):N word) s
      else
        let res:(128)word = usimd8 (\z. word_ushr z count) (word_zx x) in
        (dest := (word_zx res):N word) s`;;

let x86_VPTEST = new_definition
 `x86_VPTEST src1 src2 (s:x86state) =
        let (x:N word) = read src1 s
        and (y:N word) = read src2 s in
        (ZF := (val(word_and x y) = 0) ,,
         CF := (val(word_and y (word_not x)) = 0) ,,
         AF := F ,,
         OF := F ,,
         PF := F ,,
         SF := F) s`;;

let x86_VPUNPCKHQDQ = new_definition
  `x86_VPUNPCKHQDQ dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let x_low_high = (word_subword:int256->num#num->int64) (word_zx x) (64,64)
        and x_high_high = (word_subword:int256->num#num->int64) (word_zx x) (192,64)
        and y_low_high = (word_subword:int256->num#num->int64) (word_zx y) (64,64)
        and y_high_high = (word_subword:int256->num#num->int64) (word_zx y) (192,64) in
        let res = (word_join:int128->int128->int256)
          ((word_join:int64->int64->int128) y_high_high x_high_high)
          ((word_join:int64->int64->int128) y_low_high x_low_high) in
        (dest := (word_zx res):N word) s
      else
        let x_high = (word_subword:int128->num#num->int64) (word_zx x) (64,64)
        and y_high = (word_subword:int128->num#num->int64) (word_zx y) (64,64) in
        let res = (word_join:int64->int64->int128) y_high x_high in
        (dest := (word_zx res):N word) s`;;

let x86_VPUNPCKLQDQ = new_definition
  `x86_VPUNPCKLQDQ dest src1 src2 (s:x86state) =
      let (x:N word) = read src1 s
      and (y:N word) = read src2 s in
      if dimindex(:N) = 256 then
        let x_low = (word_subword:int256->num#num->int64) (word_zx x) (0,64)
        and x_high = (word_subword:int256->num#num->int64) (word_zx x) (128,64)
        and y_low = (word_subword:int256->num#num->int64) (word_zx y) (0,64)
        and y_high = (word_subword:int256->num#num->int64) (word_zx y) (128,64) in
        let res = (word_join:int128->int128->int256)
          ((word_join:int64->int64->int128) y_high x_high)
          ((word_join:int64->int64->int128) y_low x_low) in
        (dest := (word_zx res):N word) s
      else
        let x_low = (word_subword:int128->num#num->int64) (word_zx x) (0,64)
        and y_low = (word_subword:int128->num#num->int64) (word_zx y) (0,64) in
        let res = (word_join:int64->int64->int128) y_low x_low in
        (dest := (word_zx res):N word) s`;;

(*** This is roughly AND just for some condition codes ***)

let x86_TEST = new_definition
 `x86_TEST dest src s =
        let x = read dest s and y = read src s in
        let z = word_and x y in
        (ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

let x86_TZCNT = new_definition
 `x86_TZCNT dest src s =
        let x:N word = read src s in
        let z:N word = word(word_ctz x) in
        (dest := (z:N word) ,,
         CF := (val x = 0) ,,
         ZF := (val z = 0) ,,
         UNDEFINED_VALUES[OF;SF;PF;AF]) s`;;

let x86_VPAND = new_definition
 `x86_VPAND dest src1 src2 (s:x86state) =
        let x = read src1 s
        and y = read src2 s in
        let z = word_and x y in
        (dest := (z:N word)) s`;;

let x86_VPANDN = new_definition
 `x86_VPANDN dest src1 src2 (s:x86state) =
        let x = read src1 s
        and y = read src2 s in
        let z = word_and (word_not x) y in
        (dest := (z:N word)) s`;;

let x86_VPOR = new_definition
 `x86_VPOR dest src1 src2 (s:x86state) =
        let x = read src1 s
        and y = read src2 s in
        let z = word_or x y in
        (dest := (z:N word)) s`;;

let x86_VPXOR = new_definition
 `x86_VPXOR dest src1 src2 (s:x86state) =
        let x = read src1 s
        and y = read src2 s in
        let z = word_xor x y in
        (dest := (z:N word)) s`;;

(* Only deal with register-register exchange *)
let x86_XCHG = new_definition
 `x86_XCHG dest src s =
    let temp = read dest s in
    (dest := read src s ,, src := temp) s`;;

let x86_XOR = new_definition
 `x86_XOR dest src s =
        let x = read dest s and y = read src s in
        let z = word_xor x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;

(* ------------------------------------------------------------------------- *)
(* State components of various sizes corresponding to GPRs.                  *)
(* We also have a generic one "GPR" mapping to a number in all cases.        *)
(* ------------------------------------------------------------------------- *)

let GPR8 = define
 `GPR8 (Gpr reg Upper_8) =
        registers :> element reg :> bottom_32 :> bottom_16 :> top_8  /\
  GPR8 (Gpr reg Lower_8) =
        registers :> element reg :> bottom_32 :> bottom_16 :> bottom_8 `;;

let GPR16 = define
 `GPR16 (Gpr reg Lower_16) =
        registers :> element reg :> bottom_32 :> bottom_16`;;

let GPR32 = define
 `GPR32 (Gpr reg Lower_32) = registers :> element reg :> bottom_32`;;

(*** This is the behavior in 64-bit mode. ***)

let GPR32_Z = define
 `GPR32_Z (Gpr reg Lower_32) = registers :> element reg :> zerotop_32`;;

let GPR64 = define
 `GPR64 (Gpr reg Full_64) = registers :> element reg`;;

let GPR = define
  `GPR (Gpr reg Full_64) =
        registers :> element reg :> asnumber /\
   GPR (Gpr reg Lower_32) =
        registers :> element reg :> bottom_32 :> asnumber /\
   GPR (Gpr reg Lower_16) =
        registers :> element reg :> bottom_32 :> bottom_16 :> asnumber /\
   GPR (Gpr reg Upper_8) =
        registers :> element reg :>
            bottom_32 :> bottom_16 :> top_8 :> asnumber /\
   GPR (Gpr reg Lower_8) =
        registers :> element reg :>
            bottom_32 :> bottom_16 :> bottom_8 :> asnumber`;;

(*** The zero-top-on-write behavior when VEX-encoded, which we assume ***)

let SIMD256 = define
 `SIMD256 (Simdreg reg Lower_256) =
      simdregisters :> element reg :> zerotop_256`;;

let SIMD128 = define
 `SIMD128 (Simdreg reg Lower_128) =
    simdregisters :> element reg :> zerotop_256 :> zerotop_128`;;

let SIMD128_SSE = define
 `SIMD128_SSE (Simdreg reg Lower_128) =
    simdregisters :> element reg :> bottom_256 :> bottom_128`;;

(* ------------------------------------------------------------------------- *)
(* Decoding of a bsid address, always returning a 64-bit word.               *)
(* ------------------------------------------------------------------------- *)

let bsid_semantics = define
 `bsid_semantics(Bsid obase oind scl disp) s =
   (let bv = match obase with SOME base -> read (GPR base) s | NONE -> 0
    and iv = match oind with SOME ind -> read (GPR ind) s | NONE -> 0 in
    word(bv + 2 EXP (val scl) * iv + val disp):64 word) /\
  bsid_semantics(Riprel off) s = word(val(read RIP s) + val off)`;;

(* ------------------------------------------------------------------------- *)
(* Translate an operand to a state component of given size.                  *)
(* Generally, the only "type casts" we want are for immediates,              *)
(* which are always sign-extended. Leave other things undefined.             *)
(* Note: this is in 64-bit mode only. Of course things are different in      *)
(* other modes; particularly the "zerotop" stuff does not apply then.        *)
(* ------------------------------------------------------------------------- *)

let OPERAND256 = define
 `OPERAND256 (Simdregister r) s =
        (if simdregister_size r = 256 then SIMD256 r else ARB) /\
  OPERAND256 (Memop w ea) s =
       (if w = Word256 then memory :> bytes256 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND128 = define
 `OPERAND128 (Simdregister r) s =
        (if simdregister_size r = 128 then SIMD128 r else ARB) /\
  OPERAND128 (Memop w ea) s =
       (if w = Word128 then memory :> bytes128 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND128_SSE = define
 `OPERAND128_SSE (Simdregister r) s =
        (if simdregister_size r = 128 then SIMD128_SSE r else ARB) /\
  OPERAND128_SSE (Memop w ea) s =
       (if w = Word128 then memory :> bytes128 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND64 = define
 `OPERAND64 (Register r) s =
        (if register_size r = 64 then GPR64 r else ARB) /\
  OPERAND64 (Imm8 imm8) s = rvalue(word_sx imm8) /\
  OPERAND64 (Imm16 imm16) s = rvalue(word_sx imm16) /\
  OPERAND64 (Imm32 imm32) s = rvalue(word_sx imm32) /\
  OPERAND64 (Imm64 imm64) s = rvalue imm64 /\
  OPERAND64 (Memop w ea) s =
       (if w = Quadword then memory :> bytes64 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND32 = define
 `OPERAND32 (Register r) s =
        (if register_size r = 32 then GPR32_Z r else ARB) /\
  OPERAND32 (Imm8 imm8) s = rvalue(word_sx imm8) /\
  OPERAND32 (Imm16 imm16) s = rvalue(word_sx imm16) /\
  OPERAND32 (Imm32 imm32) s = rvalue imm32 /\
  OPERAND32 (Memop w ea) s =
       (if w = Doubleword then memory :> bytes32 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND16 = define
 `OPERAND16 (Register r) s =
        (if register_size r = 16 then GPR16 r else ARB) /\
  OPERAND16 (Imm8 imm8) s = rvalue(word_sx imm8) /\
  OPERAND16 (Imm16 imm16) s = rvalue imm16 /\
  OPERAND16 (Memop w ea) s =
       (if w = Word then memory :> bytes16 (bsid_semantics ea s)
        else ARB)`;;

let OPERAND8 = define
 `OPERAND8 (Register r) s =
        (if register_size r = 8 then GPR8 r else ARB) /\
  OPERAND8 (Imm8 imm8) s = rvalue imm8 /\
  OPERAND8 (Memop w ea) s =
       (if w = Byte then memory :> bytes8 (bsid_semantics ea s)
        else ARB)`;;

let aligned_OPERAND128 = define
 `(aligned_OPERAND128 (Simdregister r) s <=> T) /\
  (aligned_OPERAND128 (Memop w ea) s <=> aligned 16 (bsid_semantics ea s))`;;

let aligned_OPERAND256 = define
 `(aligned_OPERAND256 (Simdregister r) s <=> T) /\
  (aligned_OPERAND256 (Memop w ea) s <=> aligned 32 (bsid_semantics ea s))`;;

(* ------------------------------------------------------------------------- *)
(* Stating assumptions about instruction decoding                            *)
(* ------------------------------------------------------------------------- *)

let x86_decode = new_definition `x86_decode s pc (len,inst) <=>
  ?l. bytes_loaded s pc l /\ LENGTH l = len /\ decode l = SOME (inst, [])`;;

let X86_DECODE_CONS = prove
 (`!s pc l i l' n.
   bytes_loaded s (word pc) l ==> decode_len l (n,i) l' ==>
   x86_decode s (word pc) (n,i) /\ bytes_loaded s (word (pc + n)) l'`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun bl -> DISCH_THEN (fun th ->
    let th1,th2 = CONJ_PAIR (REWRITE_RULE [decode_len] th) in
    let th1 = MATCH_MP
      (REWRITE_RULE [list_linear_f; list_linear] list_linear_decode) th1 in
    C CHOOSE_THEN th1 (fun th ->
      let th3,th4 = CONJ_PAIR th in
      REWRITE_TAC [SYM (REWRITE_RULE [EQ_ADD_LCANCEL]
        (CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [ADD_SYM]))
          ((REWRITE_RULE [th3; LENGTH_APPEND] th2))))] THEN
      let bl1,bl2 = CONJ_PAIR (REWRITE_RULE [th3; bytes_loaded_append] bl) in
      REWRITE_TAC [x86_decode; WORD_ADD; bl2] THEN
      EXISTS_TAC `l'':byte list` THEN REWRITE_TAC [bl1;
        REWRITE_RULE [APPEND_NIL] (SPEC `[]:byte list` th4)]))));;

let x86_decode_unique = prove
 (`!s pc x y. x86_decode s pc x ==> x86_decode s pc y ==> x = y`,
  REWRITE_TAC [FORALL_PAIR_THM; x86_decode] THEN REPEAT GEN_TAC THEN
  SPECL_TAC [`p1:num`; `p1':num`; `p2:instruction`; `p2':instruction`] THEN
  MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL [METIS_TAC []; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM_LIST (fun [d2;l2;b2; d1;l1;b1; h] ->
    let th = MATCH_MP exists_list_split (REWRITE_RULE [SYM l2] h) in
    REPEAT_TCL CHOOSE_THEN (fun th ->
      let th1,th2 = CONJ_PAIR th in
      let th3,th4 = CONJ_PAIR (REWRITE_RULE [th1; bytes_loaded_append] b2) in
      let th = MP (MATCH_MP (MATCH_MP bytes_loaded_unique b1) th3)
        (TRANS l1 (SYM th2)) in
      let d1 = REWRITE_RULE [th; APPEND_NIL; UNWIND_THM1] (MATCH_MP
        (REWRITE_RULE [list_linear_f; list_linear] list_linear_decode) d1) in
      let d2 = REWRITE_RULE [th1; d1; OPTION_INJ; PAIR_EQ] d2 in
      REWRITE_TAC [d2;
        REWRITE_RULE [th1; d2; APPEND_NIL; SYM th; l1] l2]) th));;

(* A useful lemma to recover the APPEND form of mc from the CONS form which was
   enforced by define_relocated_mc. This helps x86 decoder work well.
   Looks horrendous, but it works... *)
let BYTELIST_OF_INT_APPEND = prove(`
  CONS
    (word (num_of_int (x rem &(256 EXP SUC (SUC (SUC (SUC 0))))) MOD 256)
      :(8)word)
  (CONS
    (word (
      (num_of_int (x rem &(256 EXP SUC (SUC (SUC (SUC 0))))) DIV 256) MOD 256
    ):(8)word)
  (CONS
    (word (
      (num_of_int (x rem &(256 EXP SUC (SUC (SUC (SUC 0))))) DIV 256 DIV 256)
      MOD 256
    ):(8)word)
  (CONS
    (word (
      (num_of_int (x rem &(256 EXP SUC (SUC (SUC (SUC 0))))) DIV 256 DIV 256 DIV 256)
      MOD 256
    ):(8)word)
  y
  ))) =
  APPEND (bytelist_of_int 4 x) y`,
  CONV_TAC (RAND_CONV (TOP_DEPTH_CONV num_CONV)) THEN
  REWRITE_TAC[bytelist_of_int;bytelist_of_num;APPEND]);;

let X86_DECODES_THM =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + n = pc' ==>
     bytes_loaded s (word pc) l ==> decode_len l (n,i) l' ==>
     x86_decode s (word pc) (n,i') /\ bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC X86_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + m:num = p ==> (pc + n) + m = pc + p`
  and ei,ei' = `i:instruction`,`i':instruction`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and en,em,ep,epc,epc' = `n:num`,`m:num`,`p:num`,`pc:num`,`pc':num` in
  (* go returns a list of pairs of x86_decode theorem and its PC offset. *)
  let rec go th =
    let l = rand (concl th) in
    let th1 = DECODE_LEN_THM l in
    let (n,i),l' = (dest_pair o rand F_F I) (dest_comb (concl th1)) in
    let th2 = REWRITE_CONV X86_INSTRUCTION_ALIASES i in
    let i' = rhs (concl th2) in
    let pc = rand (lhand (concl th)) in
    let th3,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n)) in
      PROVE_HYP th (INST [pc,epc; a,en; n,em; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n)),`0` in
    let pc' = rhs (concl th3) in
    let th' = (PROVE_HYP th2 o PROVE_HYP th3 o PROVE_HYP th o PROVE_HYP th1)
      (INST [i,ei; i',ei'; pc,epc; n,en; pc',epc'; l,el; l',el'] pth) in
    match l' with
    | Const("NIL",_) -> [CONJUNCT1 th',pcofs]
    | _ -> let dth,bth = CONJ_PAIR th' in (dth,pcofs)::(go bth) in
  fun th ->
    let th = PURE_REWRITE_RULE[BYTELIST_OF_INT_APPEND] th in
    let decodes:(thm*term) list = (go o
      (fun dth -> EQ_MP dth (ASSUME (lhs (concl dth)))) o
      AP_TERM `bytes_loaded s (word pc)`) th in
    map (fun th,pcofs -> ((GENL [`s:x86state`; `pc:num`] o DISCH_ALL) th, pcofs))
      decodes;;

let X86_MK_EXEC_RULE th0 =
  let th0 = INST [`pc':num`,`pc:num`] (SPEC_ALL th0) in
  GEN_MK_EXEC_RULE
    [LENGTH_BYTELIST_OF_NUM; LENGTH_BYTELIST_OF_INT;
     LENGTH; LENGTH_APPEND]
    X86_DECODES_THM th0;;

(* ------------------------------------------------------------------------- *)
(* Helper functions for adding microarchitectural events.                    *)
(* ------------------------------------------------------------------------- *)

let add_store_event = define
  `(add_store_event: operand->x86state->x86state->x86state->bool) =
    \(op:operand) (s:x86state) (s0:x86state).
      match op with
      Memop w (bs:bsid) ->
        (events := CONS (EventStore (bsid_semantics bs s, (bytesize w) DIV 8))
                        (read events s0)) s0
      | _ -> (=) s0`;;

let add_load_event = define
  `(add_load_event: operand->x86state->x86state->x86state->bool) =
    \(op:operand) (s:x86state) (s0:x86state).
      match op with
      Memop w (bs:bsid) ->
        (events := CONS (EventLoad (bsid_semantics bs s, (bytesize w) DIV 8))
                        (read events s0)) s0
      | _ -> (=) s0`;;

(* ------------------------------------------------------------------------- *)
(* Execution of a single instruction.                                        *)
(* ------------------------------------------------------------------------- *)

(*** note that this is in 64-bit mode (e.g. matters for ROL masking) ***)

(*** We also only support relative jump  at the moment ***)

let x86_execute = define
 `x86_execute instr s =
    match instr with
      ADC dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_ADC (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADC (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_ADC (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_ADC (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | ADCX dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_ADCX (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADCX (OPERAND32 dest s) (OPERAND32 src s)) s)) s
    | ADD dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_ADD (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADD (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_ADD (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_ADD (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | ADOX dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_ADOX (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_ADOX (OPERAND32 dest s) (OPERAND32 src s)) s)) s
    | AESDEC dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (x86_AESDEC (OPERAND128_SSE dest s) (OPERAND128_SSE src s)) s)) s
    | AESDECLAST dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (x86_AESDECLAST (OPERAND128_SSE dest s) (OPERAND128_SSE src s)) s))
        s
    | AESENC dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (x86_AESENC (OPERAND128_SSE dest s) (OPERAND128_SSE src s)) s)) s
    | AESENCLAST dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (x86_AESENCLAST (OPERAND128_SSE dest s) (OPERAND128_SSE src s)) s))
        s
    | AESKEYGENASSIST dest src imm8 ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (x86_AESKEYGENASSIST (OPERAND128_SSE dest s) (OPERAND128_SSE src s)
                                  (OPERAND8 imm8 s)) s)) s
    | AND dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_AND (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_AND (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_AND (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_AND (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | BSF dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_BSF (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BSF (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BSF (OPERAND16 dest s) (OPERAND16 src s)) s)) s
    | BSR dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_BSR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BSR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BSR (OPERAND16 dest s) (OPERAND16 src s)) s)) s
    | BSWAP dest ->
        (add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_BSWAP (OPERAND64 dest s)
         | 32 -> x86_BSWAP (OPERAND32 dest s)) s)) s
    | BT dest src ->
        (add_load_event dest s ,, add_load_event src s ,,
        (\s. (match operand_size dest with
           64 -> x86_BT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BT (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BT (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | BTC dest src ->
        (add_load_event dest s ,, add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_BTC (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BTC (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BTC (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BTC (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | BTR dest src ->
        (add_load_event dest s ,, add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_BTR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BTR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BTR (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BTR (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | BTS dest src ->
        (add_load_event dest s ,, add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_BTS (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_BTS (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_BTS (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_BTS (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | CALL off ->
        (let ip' = word_add (read RIP s)
                            (read (OPERAND64 off s) s) in
         x86_CALL ip' s)
    | CALL_ABSOLUTE target ->
        x86_CALL target s
    | CLC ->
        x86_CLC s
    | CLD ->
        x86_CLD s
    | CMC ->
        x86_CMC s
    | CMOV cc dest src ->
        // "If the source operand is a memory operand, then it is always read,
        // regardless of whether or not the condition is met."
        (add_load_event dest s ,, add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_CMOV cc (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_CMOV cc (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_CMOV cc (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_CMOV cc (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | CMP dest src ->
        (add_load_event dest s ,, add_load_event src s ,,
        (\s. (match operand_size dest with
           64 -> x86_CMP (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_CMP (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_CMP (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_CMP (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | DEC dest ->
        (add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_DEC (OPERAND64 dest s)
         | 32 -> x86_DEC (OPERAND32 dest s)
         | 16 -> x86_DEC (OPERAND16 dest s)
         | 8 -> x86_DEC (OPERAND8 dest s)) s)) s
    | ENDBR64 ->
        x86_ENDBR64 s
    | IMUL3 dest (src1,src2) ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_IMUL3 (OPERAND64 dest s)
                           (OPERAND64 src1 s,OPERAND64 src2 s)
         | 32 -> x86_IMUL3 (OPERAND32 dest s)
                           (OPERAND32 src1 s, OPERAND32 src2 s)
         | 16 -> x86_IMUL3 (OPERAND16 dest s)
                           (OPERAND16 src1 s,OPERAND16 src2 s)
         | 8 -> x86_IMUL3 (OPERAND8 dest s)
                          (OPERAND8 src1 s,OPERAND8 src2 s)) s)) s
    | IMUL2 (dest1,dest2) src ->
        (add_load_event dest1 s ,, add_load_event src s ,,
         add_store_event dest1 s ,, add_store_event dest2 s ,,
        (\s. (match operand_size dest2 with
           64 -> x86_IMUL2 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                          (OPERAND64 src s)
         | 32 -> x86_IMUL2 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                          (OPERAND32 src s)
         | 16 -> x86_IMUL2 (OPERAND16 dest1 s,OPERAND16 dest2 s)
                          (OPERAND16 src s)
         | 8 -> x86_IMUL2 (OPERAND8 dest1 s,OPERAND8 dest2 s)
                          (OPERAND8 src s)) s)) s
    | INC dest ->
        (add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_INC (OPERAND64 dest s)
         | 32 -> x86_INC (OPERAND32 dest s)
         | 16 -> x86_INC (OPERAND16 dest s)
         | 8 -> x86_INC (OPERAND8 dest s)) s)) s
    | JUMP cc off ->
        (events := CONS
          (EventJump
            (read RIP s,
              (if condition_semantics cc s
               then word_add (read RIP s)
                             (read (OPERAND64 off s) s)
               else read RIP s)))
          (read events s) ,,
         RIP :=
           if condition_semantics cc s
           then word_add (read RIP s)
                         (read (OPERAND64 off s) s)
           else read RIP s) s
    | LEA dest bsid ->
        (add_store_event dest s ,,
        (\s. (match operand_size dest with
          64 -> (OPERAND64 dest s) := (bsid_semantics bsid s)
        | 32 -> (OPERAND32 dest s) := word_sx(bsid_semantics bsid s)
        | 16 -> (OPERAND16 dest s) := word_sx(bsid_semantics bsid s)
        | 8 -> (OPERAND8 dest s) := word_sx(bsid_semantics bsid s)) s)) s
    | LZCNT dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_LZCNT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_LZCNT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_LZCNT (OPERAND16 dest s) (OPERAND16 src s)) s)) s
    | MOV dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_MOV (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_MOV (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_MOV (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_MOV (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | MOVAPS dest src ->
        if aligned_OPERAND128 src s /\ aligned_OPERAND128 dest s
        then
          (add_load_event src s ,,
           add_store_event dest s ,,
          (\s. x86_MOVAPS (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
        else (\s'. F)
    | MOVDQA dest src ->
        if aligned_OPERAND128 src s /\ aligned_OPERAND128 dest s
        then
          (add_load_event src s ,,
           add_store_event dest s ,,
          (\s. x86_MOVDQA (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
        else (\s'. F)
    | MOVDQU dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. x86_MOVDQU (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
    | MOVD dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match (operand_size dest, operand_size src) with
          (32,128) -> x86_MOVD (OPERAND32 dest s) (OPERAND128_SSE src s)
        | (128,32) -> x86_MOVD (OPERAND128_SSE dest s) (OPERAND32 src s)) s)) s
    | MOVQ dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match (operand_size dest, operand_size src) with
          (64,128) -> x86_MOVQ (OPERAND64 dest s) (OPERAND128_SSE src s)
        | (128,64) -> x86_MOVQ (OPERAND128_SSE dest s) (OPERAND64 src s)
        | (128,128) -> x86_MOVQ (OPERAND128_SSE dest s) (OPERAND128_SSE src s)) s)) s
    | VMOVD dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match (operand_size dest, operand_size src) with
          (32,128) -> x86_VMOVD (OPERAND32 dest s) (OPERAND128 src s)
        | (128,32) -> x86_VMOVD (OPERAND128 dest s) (OPERAND32 src s)) s)) s
    | VMOVQ dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match (operand_size dest, operand_size src) with
          (64,128) -> x86_VMOVQ (OPERAND64 dest s) (OPERAND128 src s)
        | (128,64) -> x86_VMOVQ (OPERAND128 dest s) (OPERAND64 src s)
        | (128,128) -> x86_VMOVQ (OPERAND128 dest s) (OPERAND128 src s)) s)) s
    | VMOVHPD dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match (operand_size dest, operand_size src) with
          (64,128) -> x86_VMOVHPD (OPERAND64 dest s) (OPERAND128 src s)) s)) s
    | MOVSB rept dest src size ->
        (\s. x86_MOVSB rept (OPERAND64 dest s) (OPERAND64 src s) (OPERAND64 size s) s) s
    | MOVSX dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match (operand_size dest,operand_size src) with
           (64,32) -> x86_MOVSX (OPERAND64 dest s) (OPERAND32 src s)
         | (64,16) -> x86_MOVSX (OPERAND64 dest s) (OPERAND16 src s)
         | (64,8) -> x86_MOVSX (OPERAND64 dest s) (OPERAND8 src s)
         | (32,32) -> x86_MOVSX (OPERAND32 dest s) (OPERAND32 src s)
         | (32,16) -> x86_MOVSX (OPERAND32 dest s) (OPERAND16 src s)
         | (32,8) -> x86_MOVSX (OPERAND32 dest s) (OPERAND8 src s)
         | (16,8) -> x86_MOVSX (OPERAND16 dest s) (OPERAND8 src s)) s)) s
    | MOVUPS dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. x86_MOVUPS (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
    | MOVZX dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match (operand_size dest,operand_size src) with
           (64,16) -> x86_MOVZX (OPERAND64 dest s) (OPERAND16 src s)
         | (64,8) -> x86_MOVZX (OPERAND64 dest s) (OPERAND8 src s)
         | (32,16) -> x86_MOVZX (OPERAND32 dest s) (OPERAND16 src s)
         | (32,8) -> x86_MOVZX (OPERAND32 dest s) (OPERAND8 src s)
         | (16,8) -> x86_MOVZX (OPERAND16 dest s) (OPERAND8 src s)) s)) s
    | MUL2 (dest1,dest2) src ->
        (add_load_event src s ,, add_load_event dest2 s ,,
         add_store_event dest1 s ,, add_store_event dest2 s ,,
        (\s. (match operand_size dest2 with
           64 -> x86_MUL2 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                         (OPERAND64 src s)
         | 32 -> x86_MUL2 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                         (OPERAND32 src s)
         | 16 -> x86_MUL2 (OPERAND16 dest1 s,OPERAND16 dest2 s)
                         (OPERAND16 src s)
         | 8 -> x86_MUL2 (OPERAND8 dest1 s,OPERAND8 dest2 s)
                         (OPERAND8 src s)) s)) s
    | MULX4 (dest1,dest2) (src1,src2) ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest1 s ,, add_store_event dest2 s ,,
        (\s. (match operand_size dest2 with
           64 -> x86_MULX4 (OPERAND64 dest1 s,OPERAND64 dest2 s)
                           (OPERAND64 src1 s,OPERAND64 src2 s)
         | 32 -> x86_MULX4 (OPERAND32 dest1 s,OPERAND32 dest2 s)
                           (OPERAND32 src1 s,OPERAND32 src2 s)) s)) s
    | NEG dest ->
        (add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_NEG (OPERAND64 dest s)
         | 32 -> x86_NEG (OPERAND32 dest s)
         | 16 -> x86_NEG (OPERAND16 dest s)
         | 8 -> x86_NEG (OPERAND8 dest s)) s)) s
    | NOP ->
        x86_NOP s
    | NOP_N dest ->
        (match operand_size dest with
           32 -> x86_NOP_N (OPERAND32 dest s)
         | 16 -> x86_NOP_N (OPERAND16 dest s)) s
    | NOT dest ->
        (add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_NOT (OPERAND64 dest s)
         | 32 -> x86_NOT (OPERAND32 dest s)
         | 16 -> x86_NOT (OPERAND16 dest s)
         | 8 -> x86_NOT (OPERAND8 dest s)) s)) s
    | OR dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_OR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_OR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_OR (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_OR (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | PADDD dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. x86_PADDD (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
    | PADDQ dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. x86_PADDQ (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
    | PAND dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. x86_PAND (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
    | PBLENDW dest src imm8 ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. x86_PBLENDW (OPERAND128_SSE dest s) (OPERAND128_SSE src s)
                        (OPERAND8 imm8 s) s)) s
    | PCMPGTD dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. x86_PCMPGTD (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
    | PCMPGTW dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. x86_PCMPGTW (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
    | PEXT dest src1 src2 ->
       (add_load_event src1 s ,, add_load_event src2 s ,,
        add_store_event dest s ,,
       (\s. (match operand_size dest with
          64 -> x86_PEXT (OPERAND64 dest s) (OPERAND64 src1 s) (OPERAND64 src2 s)
        | 32 -> x86_PEXT (OPERAND32 dest s) (OPERAND32 src1 s) (OPERAND32 src2 s))
          s)) s
    | PINSRD dest src imm8 ->
       (add_load_event src s ,, add_load_event dest s ,,
        add_store_event dest s ,,
       (\s. x86_PINSRD (OPERAND128_SSE dest s) (OPERAND32 src s)
                       (OPERAND8 imm8 s) s)) s
    | PINSRQ dest src imm8 ->
       (add_load_event src s ,, add_load_event dest s ,,
        add_store_event dest s ,,
       (\s. x86_PINSRQ (OPERAND128_SSE dest s) (OPERAND64 src s)
                       (OPERAND8 imm8 s) s)) s
    | PMOVMSKB dest src ->
       (add_load_event src s ,, add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_PMOVMSKB (OPERAND64 dest s) (OPERAND128_SSE src s)
         | 32  -> x86_PMOVMSKB (OPERAND32 dest s) (OPERAND128_SSE src s)) s)) s
    | POP dest ->
       (add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_POP (OPERAND64 dest s)
         | 16 -> x86_POP (OPERAND16 dest s)) s)) s
    | POPCNT dest src ->
       (add_load_event src s ,, add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_POPCNT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_POPCNT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_POPCNT (OPERAND16 dest s) (OPERAND16 src s)) s)) s
    | PSHUFB dest src ->
       (add_load_event src s ,, add_load_event dest s ,,
        add_store_event dest s ,,
       (\s. x86_PSHUFB (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
    | PSHUFD dest src imm8 ->
       (add_load_event src s ,, add_load_event dest s ,,
        add_store_event dest s ,,
       (\s. x86_PSHUFD (OPERAND128_SSE dest s) (OPERAND128_SSE src s)
                       (OPERAND8 imm8 s) s)) s
    | PSRAD dest imm8 ->
       (add_load_event dest s ,, add_store_event dest s ,,
       (\s. x86_PSRAD (OPERAND128_SSE dest s) (OPERAND8 imm8 s) s)) s
    | PSRLW dest imm8 ->
       (add_load_event dest s ,, add_store_event dest s ,,
       (\s. x86_PSRLW (OPERAND128_SSE dest s) (OPERAND8 imm8 s) s)) s
    | PUSH src ->
       (add_load_event src s ,,
       (\s. (match operand_size src with
           64 -> x86_PUSH (OPERAND64 src s)
         | 16 -> x86_PUSH (OPERAND16 src s)) s)) s
    | PXOR dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. x86_PXOR (OPERAND128_SSE dest s) (OPERAND128_SSE src s) s)) s
    | RCL dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_RCL (OPERAND64 dest s)
                         (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_RCL (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_RCL (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_RCL (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s)) s
    | RCR dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_RCR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_RCR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_RCR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_RCR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s)) s
    | RET ->
        x86_RET s
    | ROL dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_ROL (OPERAND64 dest s)
                         (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_ROL (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_ROL (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_ROL (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s)) s
    | ROR dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_ROR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_ROR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_ROR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_ROR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s)) s
    | SAR dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_SAR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_SAR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_SAR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_SAR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s)) s
    | SBB dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_SBB (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_SBB (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_SBB (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_SBB (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | SET cc dest ->
       (add_store_event dest s ,,
       (\s. (match operand_size dest with
           8 -> x86_SET cc (OPERAND8 dest s)
         | _ -> ARB) s)) s
    | SHL dest src ->
       (add_load_event dest s ,, add_load_event src s ,,
        add_store_event dest s ,,
       (\s. (match operand_size dest with
           64 -> x86_SHL (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_SHL (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_SHL (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_SHL (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s)) s
    | SHLD dest src c ->
        (add_load_event dest s ,, add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_SHLD (OPERAND64 dest s) (OPERAND64 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 32 -> x86_SHLD (OPERAND32 dest s) (OPERAND32 src s)
                          (val(read (OPERAND8 c s) s) MOD 32)
         | 16 -> x86_SHLD (OPERAND16 dest s) (OPERAND16 src s)
                          (val(read (OPERAND8 c s) s) MOD 32)
         | 8 -> x86_SHLD (OPERAND8 dest s) (OPERAND8 src s)
                         (val(read (OPERAND8 c s) s) MOD 32)) s)) s
    | SHR dest src ->
        (add_load_event dest s ,, add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_SHR (OPERAND64 dest s)
                        (val(read (OPERAND8 src s) s) MOD 64)
         | 32 -> x86_SHR (OPERAND32 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 16 -> x86_SHR (OPERAND16 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)
         | 8 -> x86_SHR (OPERAND8 dest s)
                        (val(read (OPERAND8 src s) s) MOD 32)) s)) s
    | SHRD dest src c ->
        (add_load_event dest s ,, add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_SHRD (OPERAND64 dest s) (OPERAND64 src s)
                          (val(read (OPERAND8 c s) s) MOD 64)
         | 32 -> x86_SHRD (OPERAND32 dest s) (OPERAND32 src s)
                          (val(read (OPERAND8 c s) s) MOD 32)
         | 16 -> x86_SHRD (OPERAND16 dest s) (OPERAND16 src s)
                          (val(read (OPERAND8 c s) s) MOD 32)
         | 8 -> x86_SHRD (OPERAND8 dest s) (OPERAND8 src s)
                         (val(read (OPERAND8 c s) s) MOD 32)) s)) s
    | STCF ->
        x86_STC s
    | STD ->
        x86_STD s
    | SUB dest src ->
        (add_load_event dest s ,, add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_SUB (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_SUB (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_SUB (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_SUB (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | TEST dest src ->
        (add_load_event dest s ,, add_load_event src s ,,
        (\s. (match operand_size dest with
           64 -> x86_TEST (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_TEST (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_TEST (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_TEST (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | TZCNT dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_TZCNT (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_TZCNT (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_TZCNT (OPERAND16 dest s) (OPERAND16 src s)) s)) s
    | VMOVDQA dest src ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. match operand_size dest with
          256 -> if aligned_OPERAND256 src s /\ aligned_OPERAND256 dest s
                then x86_VMOVDQA (OPERAND256 dest s) (OPERAND256 src s) s
                else (\s'. F)
        | 128 -> if aligned_OPERAND128 src s /\ aligned_OPERAND128 dest s
                then x86_VMOVDQA (OPERAND128 dest s) (OPERAND128 src s) s
                else (\s'. F))) s
    | VMOVDQU dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VMOVDQU (OPERAND256 dest s) (OPERAND256 src s) s
        | 128 -> x86_VMOVDQU (OPERAND128 dest s) (OPERAND128 src s) s))) s
    | VMOVMSKPS dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. x86_VMOVMSKPS (OPERAND32 dest s) (OPERAND256 src s) s)) s
    | VPMOVMSKB dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. x86_VPMOVMSKB (OPERAND32 dest s) (OPERAND256 src s) s)) s
    | VMOVSHDUP dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VMOVSHDUP (OPERAND256 dest s) (OPERAND256 src s)
        | 128 -> x86_VMOVSHDUP (OPERAND128 dest s) (OPERAND128 src s)) s)) s
    | VMOVSLDUP dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VMOVSLDUP (OPERAND256 dest s) (OPERAND256 src s)
        | 128 -> x86_VMOVSLDUP (OPERAND128 dest s) (OPERAND128 src s)) s)) s
    | VPADDB dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
       (\s. (match operand_size dest with
          256 -> x86_VPADDB (OPERAND256 dest s) (OPERAND256 src1 s)
                            (OPERAND256 src2 s)
        | 128 -> x86_VPADDB (OPERAND128 dest s) (OPERAND128 src1 s)
                            (OPERAND128 src2 s)) s)) s
    | VPADDD dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPADDD (OPERAND256 dest s) (OPERAND256 src1 s)
                            (OPERAND256 src2 s)
        | 128 -> x86_VPADDD (OPERAND128 dest s) (OPERAND128 src1 s)
                            (OPERAND128 src2 s)) s)) s
    | VPADDQ dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPADDQ (OPERAND256 dest s) (OPERAND256 src1 s)
                            (OPERAND256 src2 s)
        | 128 -> x86_VPADDQ (OPERAND128 dest s) (OPERAND128 src1 s)
                            (OPERAND128 src2 s)) s)) s
    | VPADDW dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPADDW (OPERAND256 dest s) (OPERAND256 src1 s)
                            (OPERAND256 src2 s)
        | 128 -> x86_VPADDW (OPERAND128 dest s) (OPERAND128 src1 s)
                            (OPERAND128 src2 s)) s)) s
    | VPBLENDD dest src1 src2 imm8 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPBLENDD (OPERAND256 dest s) (OPERAND256 src1 s)
                              (OPERAND256 src2 s) (OPERAND8 imm8 s)
        | 128 -> x86_VPBLENDD (OPERAND128 dest s) (OPERAND128 src1 s)
                              (OPERAND128 src2 s) (OPERAND8 imm8 s)) s)) s
    | VPBLENDW dest src1 src2 imm8 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPBLENDW (OPERAND256 dest s) (OPERAND256 src1 s)
                              (OPERAND256 src2 s) (OPERAND8 imm8 s)
        | 128 -> x86_VPBLENDW (OPERAND128 dest s) (OPERAND128 src1 s)
                              (OPERAND128 src2 s) (OPERAND8 imm8 s)) s)) s
    | VPCLMULQDQ dest src1 src2 imm8 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPCLMULQDQ (OPERAND256 dest s) (OPERAND256 src1 s)
                                (OPERAND256 src2 s) (OPERAND8 imm8 s)
        | 128 -> x86_VPCLMULQDQ (OPERAND128 dest s) (OPERAND128 src1 s)
                                (OPERAND128 src2 s) (OPERAND8 imm8 s)) s)) s
    | VPBROADCASTD dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> (match operand_size src with
                    128 -> x86_VPBROADCASTD (OPERAND256 dest s) (OPERAND128 src s)
                  |  32 -> x86_VPBROADCASTD (OPERAND256 dest s) (OPERAND32 src s))
         | 128 -> (match operand_size src with
                    128 -> x86_VPBROADCASTD (OPERAND128 dest s) (OPERAND128 src s)
                  |  32 -> x86_VPBROADCASTD (OPERAND128 dest s) (OPERAND32 src s))) s)) s
    | VPBROADCASTQ dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> (match operand_size src with
                    128 -> x86_VPBROADCASTQ (OPERAND256 dest s) (OPERAND128 src s)
                  |  64 -> x86_VPBROADCASTQ (OPERAND256 dest s) (OPERAND64 src s))
         | 128 -> (match operand_size src with
                    128 -> x86_VPBROADCASTQ (OPERAND128 dest s) (OPERAND128 src s)
                  |  64 -> x86_VPBROADCASTQ (OPERAND128 dest s) (OPERAND64 src s))) s)) s
    | VPBROADCASTW dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> (match operand_size src with
                    128 -> x86_VPBROADCASTW (OPERAND256 dest s) (OPERAND128 src s)
                  |  16 -> x86_VPBROADCASTW (OPERAND256 dest s) (OPERAND16 src s))
         | 128 -> (match operand_size src with
                    128 -> x86_VPBROADCASTW (OPERAND128 dest s) (OPERAND128 src s)
                  |  16 -> x86_VPBROADCASTW (OPERAND128 dest s) (OPERAND16 src s))) s)) s
    | VPERMD dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           256 -> x86_VPERMD (OPERAND256 dest s) (OPERAND256 src1 s) (OPERAND256 src2 s)
         | 128 -> (\s s'. F)) s)) s
    | VPERMQ dest src imm8 ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPERMQ (OPERAND256 dest s) (OPERAND256 src s)
                            (OPERAND8 imm8 s)
        | 128 -> x86_VPERMQ (OPERAND128 dest s) (OPERAND128 src s)
                            (OPERAND8 imm8 s)) s)) s
    | VPERM2I128 dest src1 src2 imm8 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPERM2I128 (OPERAND256 dest s) (OPERAND256 src1 s)
                                (OPERAND256 src2 s) (OPERAND8 imm8 s)
        | 128 -> x86_VPERM2I128 (OPERAND128 dest s) (OPERAND128 src1 s)
                                (OPERAND128 src2 s) (OPERAND8 imm8 s)) s)) s
    | VPINSRD dest src1 src2 imm8 ->
       (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
       (\s. x86_VPINSRD (OPERAND128 dest s) (OPERAND128 src1 s) (OPERAND32 src2 s)
                       (OPERAND8 imm8 s) s)) s
    | VPINSRQ dest src1 src2 imm8 ->
       (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
       (\s. x86_VPINSRQ (OPERAND128 dest s) (OPERAND128 src1 s) (OPERAND64 src2 s)
                       (OPERAND8 imm8 s) s)) s
    | VPINSRW dest src1 src2 imm8 ->
       (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
       (\s. (match operand_size src2 with
               32 -> x86_VPINSRW (OPERAND128 dest s) (OPERAND128 src1 s) (OPERAND32 src2 s)
                                  (OPERAND8 imm8 s)
             | 16 -> x86_VPINSRW (OPERAND128 dest s) (OPERAND128 src1 s) (OPERAND16 src2 s)
                                  (OPERAND8 imm8 s)) s)) s
    | VPEXTRD dest src imm8 ->
       (add_load_event src s ,, add_store_event dest s ,,
       (\s. x86_VPEXTRD (OPERAND32 dest s) (OPERAND128 src s)
                       (OPERAND8 imm8 s) s)) s
    | VPEXTRQ dest src imm8 ->
       (add_load_event src s ,, add_store_event dest s ,,
       (\s. x86_VPEXTRQ (OPERAND64 dest s) (OPERAND128 src s)
                       (OPERAND8 imm8 s) s)) s
    | VPEXTRW dest src imm8 ->
       (add_load_event src s ,, add_store_event dest s ,,
       (\s. (match operand_size dest with
               32 -> x86_VPEXTRW (OPERAND32 dest s) (OPERAND128 src s)
                                 (OPERAND8 imm8 s)
             | 16 -> x86_VPEXTRW (OPERAND16 dest s) (OPERAND128 src s)
                                 (OPERAND8 imm8 s)) s)) s
    | VINSERTI128 dest src1 src2 imm8 ->
       (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
       (\s. x86_VINSERTI128 (OPERAND256 dest s) (OPERAND256 src1 s) (OPERAND128 src2 s)
                       (OPERAND8 imm8 s) s)) s
    | VEXTRACTI128 dest src imm8 ->
       (add_load_event src s ,, add_store_event dest s ,,
       (\s. x86_VEXTRACTI128 (OPERAND128 dest s) (OPERAND256 src s) (OPERAND8 imm8 s) s)) s
    | VPABSD dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPABSD (OPERAND256 dest s) (OPERAND256 src s)
        | 128 -> x86_VPABSD (OPERAND128 dest s) (OPERAND128 src s)) s)) s
    | VPACKUSWB dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPACKUSWB (OPERAND256 dest s) (OPERAND256 src1 s)
                               (OPERAND256 src2 s)
        | 128 -> x86_VPACKUSWB (OPERAND128 dest s) (OPERAND128 src1 s)
                               (OPERAND128 src2 s)) s)) s
    | VPBLENDVB dest src1 src2 mask ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_load_event mask s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPBLENDVB (OPERAND256 dest s) (OPERAND256 src1 s)
                               (OPERAND256 src2 s) (OPERAND256 mask s)
        | 128 -> x86_VPBLENDVB (OPERAND128 dest s) (OPERAND128 src1 s)
                               (OPERAND128 src2 s) (OPERAND128 mask s)) s)) s
    | VPMADDUBSW dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPMADDUBSW (OPERAND256 dest s) (OPERAND256 src1 s)
                                (OPERAND256 src2 s)
        | 128 -> x86_VPMADDUBSW (OPERAND128 dest s) (OPERAND128 src1 s)
                                (OPERAND128 src2 s)) s)) s
    | VPMADDWD dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPMADDWD (OPERAND256 dest s) (OPERAND256 src1 s)
                              (OPERAND256 src2 s)
        | 128 -> x86_VPMADDWD (OPERAND128 dest s) (OPERAND128 src1 s)
                              (OPERAND128 src2 s)) s)) s
    | VPMOVSXBD dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> (match operand_size src with
                    128 -> x86_VPMOVSXBD (OPERAND256 dest s) (OPERAND128 src s)
                  |  64 -> x86_VPMOVSXBD (OPERAND256 dest s) (OPERAND64 src s))
        | 128 -> (match operand_size src with
                    128 -> x86_VPMOVSXBD (OPERAND128 dest s) (OPERAND128 src s)
                  |  32 -> x86_VPMOVSXBD (OPERAND128 dest s) (OPERAND32 src s))) s)) s
    | VPMOVZXBD dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> (match operand_size src with
                    128 -> x86_VPMOVZXBD (OPERAND256 dest s) (OPERAND128 src s)
                  |  64 -> x86_VPMOVZXBD (OPERAND256 dest s) (OPERAND64 src s))
        | 128 -> (match operand_size src with
                    128 -> x86_VPMOVZXBD (OPERAND128 dest s) (OPERAND128 src s)
                  |  32 -> x86_VPMOVZXBD (OPERAND128 dest s) (OPERAND32 src s))) s)) s
    | VPMOVZXBW dest src ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> (match operand_size src with
                    256 -> x86_VPMOVZXBW (OPERAND256 dest s) (OPERAND256 src s)
                  |  128 -> x86_VPMOVZXBW (OPERAND256 dest s) (OPERAND128 src s))
        | 128 -> (match operand_size src with
                    128 -> x86_VPMOVZXBW (OPERAND128 dest s) (OPERAND128 src s)
                  |  64 -> x86_VPMOVZXBW (OPERAND128 dest s) (OPERAND64 src s))) s)) s
    | VPMULDQ dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPMULDQ (OPERAND256 dest s) (OPERAND256 src1 s)
                             (OPERAND256 src2 s)
        | 128 -> x86_VPMULDQ (OPERAND128 dest s) (OPERAND128 src1 s)
                             (OPERAND128 src2 s)) s)) s
    | VPMULHRSW dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPMULHRSW (OPERAND256 dest s) (OPERAND256 src1 s)
                                (OPERAND256 src2 s)
        | 128 -> x86_VPMULHRSW (OPERAND128 dest s) (OPERAND128 src1 s)
                                (OPERAND128 src2 s)) s)) s
    | VPMULHUW dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPMULHUW (OPERAND256 dest s) (OPERAND256 src1 s)
                              (OPERAND256 src2 s)
        | 128 -> x86_VPMULHUW (OPERAND128 dest s) (OPERAND128 src1 s)
                              (OPERAND128 src2 s)) s)) s
    | VPMULHW dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPMULHW (OPERAND256 dest s) (OPERAND256 src1 s)
                             (OPERAND256 src2 s)
        | 128 -> x86_VPMULHW (OPERAND128 dest s) (OPERAND128 src1 s)
                             (OPERAND128 src2 s)) s)) s
    | VPMULLD dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPMULLD (OPERAND256 dest s) (OPERAND256 src1 s)
                             (OPERAND256 src2 s)
        | 128 -> x86_VPMULLD (OPERAND128 dest s) (OPERAND128 src1 s)
                             (OPERAND128 src2 s)) s)) s
    | VPMULLW dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPMULLW (OPERAND256 dest s) (OPERAND256 src1 s)
                             (OPERAND256 src2 s)
        | 128 -> x86_VPMULLW (OPERAND128 dest s) (OPERAND128 src1 s)
                             (OPERAND128 src2 s)) s)) s
    | VPSHUFB dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSHUFB (OPERAND256 dest s) (OPERAND256 src1 s)
                             (OPERAND256 src2 s)
        | 128 -> x86_VPSHUFB (OPERAND128 dest s) (OPERAND128 src1 s)
                             (OPERAND128 src2 s)) s)) s
    | VPSLLVD dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSLLVD (OPERAND256 dest s) (OPERAND256 src1 s)
                             (OPERAND256 src2 s)
        | 128 -> x86_VPSLLVD (OPERAND128 dest s) (OPERAND128 src1 s)
                             (OPERAND128 src2 s)) s)) s
    | VPSLLD dest src imm8 ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSLLD (OPERAND256 dest s) (OPERAND256 src s)
                            (OPERAND8 imm8 s)
        | 128 -> x86_VPSLLD (OPERAND128 dest s) (OPERAND128 src s)
                            (OPERAND8 imm8 s)) s)) s
    | VPSLLQ dest src imm8 ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSLLQ (OPERAND256 dest s) (OPERAND256 src s)
                            (OPERAND8 imm8 s)
        | 128 -> x86_VPSLLQ (OPERAND128 dest s) (OPERAND128 src s)
                            (OPERAND8 imm8 s)) s)) s
    | VPSLLW dest src imm8 ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSLLW (OPERAND256 dest s) (OPERAND256 src s)
                            (OPERAND8 imm8 s)
        | 128 -> x86_VPSLLW (OPERAND128 dest s) (OPERAND128 src s)
                            (OPERAND8 imm8 s)) s)) s
    | VPCMPGTD dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPCMPGTD (OPERAND256 dest s) (OPERAND256 src1 s)
                               (OPERAND256 src2 s)
        | 128 -> x86_VPCMPGTD (OPERAND128 dest s) (OPERAND128 src1 s)
                               (OPERAND128 src2 s)) s)) s
    | VPCMPGTW dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPCMPGTW (OPERAND256 dest s) (OPERAND256 src1 s)
                               (OPERAND256 src2 s)
        | 128 -> x86_VPCMPGTW (OPERAND128 dest s) (OPERAND128 src1 s)
                               (OPERAND128 src2 s)) s)) s
    | VPSUBB dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSUBB (OPERAND256 dest s) (OPERAND256 src1 s)
                            (OPERAND256 src2 s)
        | 128 -> x86_VPSUBB (OPERAND128 dest s) (OPERAND128 src1 s)
                            (OPERAND128 src2 s)) s)) s
    | VPSUBD dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSUBD (OPERAND256 dest s) (OPERAND256 src1 s)
                            (OPERAND256 src2 s)
        | 128 -> x86_VPSUBD (OPERAND128 dest s) (OPERAND128 src1 s)
                            (OPERAND128 src2 s)) s)) s
    | VPSUBQ dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSUBQ (OPERAND256 dest s) (OPERAND256 src1 s)
                            (OPERAND256 src2 s)
        | 128 -> x86_VPSUBQ (OPERAND128 dest s) (OPERAND128 src1 s)
                            (OPERAND128 src2 s)) s)) s
    | VPSUBW dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSUBW (OPERAND256 dest s) (OPERAND256 src1 s)
                            (OPERAND256 src2 s)
        | 128 -> x86_VPSUBW (OPERAND128 dest s) (OPERAND128 src1 s)
                            (OPERAND128 src2 s)) s)) s
    | VPTEST src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
        (\s. (match operand_size src1 with
          256 -> x86_VPTEST (OPERAND256 src1 s) (OPERAND256 src2 s)
        | 128 -> x86_VPTEST (OPERAND128 src1 s) (OPERAND128 src2 s)) s)) s
    | VPSRAW dest src imm8 ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSRAW (OPERAND256 dest s) (OPERAND256 src s)
                            (OPERAND8 imm8 s)
        | 128 -> x86_VPSRAW (OPERAND128 dest s) (OPERAND128 src s)
                            (OPERAND8 imm8 s)) s)) s
    | VPSRLVD dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSRLVD (OPERAND256 dest s) (OPERAND256 src1 s)
                             (OPERAND256 src2 s)
        | 128 -> x86_VPSRLVD (OPERAND128 dest s) (OPERAND128 src1 s)
                             (OPERAND128 src2 s)) s)) s
    | VPSRLVQ dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSRLVQ (OPERAND256 dest s) (OPERAND256 src1 s)
                             (OPERAND256 src2 s)
        | 128 -> x86_VPSRLVQ (OPERAND128 dest s) (OPERAND128 src1 s)
                             (OPERAND128 src2 s)) s)) s
    | VPSRLD dest src imm8 ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSRLD (OPERAND256 dest s) (OPERAND256 src s)
                            (OPERAND8 imm8 s)
        | 128 -> x86_VPSRLD (OPERAND128 dest s) (OPERAND128 src s)
                            (OPERAND8 imm8 s)) s)) s
    | VPSRLDQ dest src imm8 ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSRLDQ (OPERAND256 dest s) (OPERAND256 src s)
                             (OPERAND8 imm8 s)
        | 128 -> x86_VPSRLDQ (OPERAND128 dest s) (OPERAND128 src s)
                             (OPERAND8 imm8 s)) s)) s
    | VPSRLQ dest src imm8 ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSRLQ (OPERAND256 dest s) (OPERAND256 src s)
                            (OPERAND8 imm8 s)
        | 128 -> x86_VPSRLQ (OPERAND128 dest s) (OPERAND128 src s)
                            (OPERAND8 imm8 s)) s)) s
    | VPSRLW dest src imm8 ->
        (add_load_event src s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSRLW (OPERAND256 dest s) (OPERAND256 src s)
                            (OPERAND8 imm8 s)
        | 128 -> x86_VPSRLW (OPERAND128 dest s) (OPERAND128 src s)
                            (OPERAND8 imm8 s)) s)) s
    | VPXOR dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPXOR (OPERAND256 dest s) (OPERAND256 src1 s)
                           (OPERAND256 src2 s)
        | 128 -> x86_VPXOR (OPERAND128 dest s) (OPERAND128 src1 s)
                           (OPERAND128 src2 s)) s)) s
    | VPAND dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPAND (OPERAND256 dest s) (OPERAND256 src1 s)
                           (OPERAND256 src2 s)
        | 128 -> x86_VPAND (OPERAND128 dest s) (OPERAND128 src1 s)
                           (OPERAND128 src2 s)) s)) s
    | VPANDN dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPANDN (OPERAND256 dest s) (OPERAND256 src1 s)
                           (OPERAND256 src2 s)
        | 128 -> x86_VPANDN (OPERAND128 dest s) (OPERAND128 src1 s)
                           (OPERAND128 src2 s)) s)) s
    | VPOR dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPOR (OPERAND256 dest s) (OPERAND256 src1 s) (OPERAND256 src2 s)
        | 128 -> x86_VPOR (OPERAND128 dest s) (OPERAND128 src1 s) (OPERAND128 src2 s)) s)) s
    | VPSRAD dest src imm8 ->
        (add_load_event src s ,, add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPSRAD (OPERAND256 dest s) (OPERAND256 src s) (OPERAND8 imm8 s)
        | 128 -> x86_VPSRAD (OPERAND128 dest s) (OPERAND128 src s) (OPERAND8 imm8 s)) s)) s
    | VPUNPCKHQDQ dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPUNPCKHQDQ (OPERAND256 dest s) (OPERAND256 src1 s) (OPERAND256 src2 s)
        | 128 -> x86_VPUNPCKHQDQ (OPERAND128 dest s) (OPERAND128 src1 s) (OPERAND128 src2 s)) s)) s
    | VPUNPCKLQDQ dest src1 src2 ->
        (add_load_event src1 s ,, add_load_event src2 s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
          256 -> x86_VPUNPCKLQDQ (OPERAND256 dest s) (OPERAND256 src1 s) (OPERAND256 src2 s)
        | 128 -> x86_VPUNPCKLQDQ (OPERAND128 dest s) (OPERAND128 src1 s) (OPERAND128 src2 s)) s)) s
    | VZEROUPPER ->
        x86_VZEROUPPER s
    | XCHG dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,, add_store_event src s ,,
        (\s. (match operand_size dest with
          64 -> x86_XCHG (OPERAND64 dest s) (OPERAND64 src s)
        | 32 -> x86_XCHG (OPERAND32 dest s) (OPERAND32 src s)
        | 16 -> x86_XCHG (OPERAND16 dest s) (OPERAND16 src s)
        | 8 -> x86_XCHG (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | XOR dest src ->
        (add_load_event src s ,, add_load_event dest s ,,
         add_store_event dest s ,,
        (\s. (match operand_size dest with
           64 -> x86_XOR (OPERAND64 dest s) (OPERAND64 src s)
         | 32 -> x86_XOR (OPERAND32 dest s) (OPERAND32 src s)
         | 16 -> x86_XOR (OPERAND16 dest s) (OPERAND16 src s)
         | 8 -> x86_XOR (OPERAND8 dest s) (OPERAND8 src s)) s)) s
    | _ -> (\s'. F)`;;

(* ------------------------------------------------------------------------- *)
(* Now the basic fetch-decode-execute cycle.                                 *)
(* ------------------------------------------------------------------------- *)

(*** Note that we *always* increment the instruction pointer first. This is
 *** consistent with the fact that relative offsets in JMP, CALL are
 *** relative to the *next* instruction, so we can use current PC in
 *** the execution of control flow instructions.
 ***)

let x86 = define
 `x86 s s' <=>
    ?len instr. x86_decode s (read RIP s) (len,instr) /\
                (RIP := word_add (read RIP s) (word len) ,,
                x86_execute instr) s s'`;;

(* ------------------------------------------------------------------------- *)
(* Shorthand for the set of all flags for modification lists.                *)
(* ------------------------------------------------------------------------- *)

let SOME_FLAGS = new_definition
 `SOME_FLAGS = [CF; PF; AF; ZF; SF; OF]`;;

(* ------------------------------------------------------------------------- *)
(* Standard System V AMD64 ABI as used on modern Unix/Linux/Mac OS.          *)
(* ------------------------------------------------------------------------- *)

(*** This is for the "System V AMD64 ABI", i.e. modern unixes     ***)
(*** We don't talk about the stack or FP arguments yet            ***)

let C_ARGUMENTS = define
 `(C_ARGUMENTS [a1;a2;a3;a4;a5;a6] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3 /\
        read RCX s = a4 /\ read  R8 s = a5 /\ read  R9 s = a6) /\
  (C_ARGUMENTS [a1;a2;a3;a4;a5] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3 /\
        read RCX s = a4 /\ read  R8 s = a5) /\
  (C_ARGUMENTS [a1;a2;a3;a4] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3 /\
        read RCX s = a4) /\
  (C_ARGUMENTS [a1;a2;a3] s <=>
        read RDI s = a1 /\ read RSI s = a2 /\ read RDX s = a3) /\
  (C_ARGUMENTS [a1;a2] s <=>
        read RDI s = a1 /\ read RSI s = a2) /\
  (C_ARGUMENTS [a1] s <=>
        read RDI s = a1) /\
  (C_ARGUMENTS [] s <=>
        T)`;;

let C_RETURN = define
 `C_RETURN = read RAX`;;

let PRESERVED_GPRS = define
 `PRESERVED_GPRS = [RSP; RBX; RBP; R12; R13; R14; R15]`;;

let MODIFIABLE_GPRS = define
 `MODIFIABLE_GPRS = [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11]`;;

let MODIFIABLE_ZMMS = define
 `MODIFIABLE_ZMMS =
   [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
    ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15;
    ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23;
    ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31]`;;

let MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI = REWRITE_RULE
    [SOME_FLAGS; MODIFIABLE_GPRS; MODIFIABLE_ZMMS]
 (new_definition `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI =
    MAYCHANGE [RIP] ,, MAYCHANGE MODIFIABLE_GPRS ,,
    MAYCHANGE MODIFIABLE_ZMMS ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`);;

(* ------------------------------------------------------------------------- *)
(* Microsoft x86 fastcall ABI (the return value is in fact the same).        *)
(* ------------------------------------------------------------------------- *)

let WINDOWS_C_ARGUMENTS = define
 `(WINDOWS_C_ARGUMENTS [a1;a2;a3;a4;a5;a6] s <=>
        read RCX s = a1 /\ read RDX s = a2 /\ read R8 s = a3 /\
        read R9 s = a4 /\
        read (memory :> bytes64 (word_add (read RSP s) (word 40))) s = a5 /\
        read (memory :> bytes64 (word_add (read RSP s) (word 48))) s = a6) /\
  (WINDOWS_C_ARGUMENTS [a1;a2;a3;a4;a5] s <=>
        read RCX s = a1 /\ read RDX s = a2 /\ read R8 s = a3 /\
        read R9 s = a4 /\
        read (memory :> bytes64 (word_add (read RSP s) (word 40))) s = a5) /\
  (WINDOWS_C_ARGUMENTS [a1;a2;a3;a4] s <=>
        read RCX s = a1 /\ read RDX s = a2 /\ read R8 s = a3 /\
        read R9 s = a4) /\
  (WINDOWS_C_ARGUMENTS [a1;a2;a3] s <=>
        read RCX s = a1 /\ read RDX s = a2 /\ read R8 s = a3) /\
  (WINDOWS_C_ARGUMENTS [a1;a2] s <=>
        read RCX s = a1 /\ read RDX s = a2) /\
  (WINDOWS_C_ARGUMENTS [a1] s <=>
        read RCX s = a1) /\
  (WINDOWS_C_ARGUMENTS [] s <=>
        T)`;;

let WINDOWS_C_RETURN = define
 `WINDOWS_C_RETURN = read RAX`;;

let WINDOWS_PRESERVED_GPRS = define
 `WINDOWS_PRESERVED_GPRS = [RSP; RBX; RBP; RSI; RDI; R12; R13; R14; R15]`;;

let WINDOWS_MODIFIABLE_GPRS = define
 `WINDOWS_MODIFIABLE_GPRS = [RAX; RCX; RDX; R8; R9; R10; R11]`;;

let WINDOWS_MODIFIABLE_ZMMS = define
 `WINDOWS_MODIFIABLE_ZMMS =
   [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5;
    ZMM16; ZMM17; ZMM18; ZMM19; ZMM20; ZMM21; ZMM22; ZMM23;
    ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30; ZMM31]`;;

let WINDOWS_MODIFIABLE_UPPER_ZMMS = define
 `WINDOWS_MODIFIABLE_UPPER_ZMMS =
   [ZMM6 :> tophalf; ZMM7 :> tophalf; ZMM8 :> tophalf; ZMM9 :> tophalf;
    ZMM10 :> tophalf; ZMM11 :> tophalf; ZMM12 :> tophalf; ZMM13 :> tophalf;
    ZMM14 :> tophalf; ZMM15 :> tophalf]`;;

let WINDOWS_MODIFIABLE_UPPER_YMMS = define
 `WINDOWS_MODIFIABLE_UPPER_YMMS =
   [ZMM6 :> bottomhalf :> tophalf; ZMM7 :> bottomhalf :> tophalf;
    ZMM8 :> bottomhalf :> tophalf; ZMM9 :> bottomhalf :> tophalf;
    ZMM10 :> bottomhalf :> tophalf; ZMM11 :> bottomhalf :> tophalf;
    ZMM12 :> bottomhalf :> tophalf; ZMM13 :> bottomhalf :> tophalf;
    ZMM14 :> bottomhalf :> tophalf; ZMM15 :> bottomhalf :> tophalf]`;;

let WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI = REWRITE_RULE
    [SOME_FLAGS; WINDOWS_MODIFIABLE_GPRS; WINDOWS_MODIFIABLE_ZMMS;
     WINDOWS_MODIFIABLE_UPPER_ZMMS; WINDOWS_MODIFIABLE_UPPER_YMMS]
 (new_definition `WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI =
    MAYCHANGE [RIP] ,, MAYCHANGE WINDOWS_MODIFIABLE_GPRS ,,
    MAYCHANGE WINDOWS_MODIFIABLE_ZMMS ,,
    MAYCHANGE WINDOWS_MODIFIABLE_UPPER_ZMMS ,,
    MAYCHANGE WINDOWS_MODIFIABLE_UPPER_YMMS ,,
    MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`);;

(* ------------------------------------------------------------------------- *)
(* Clausal theorems and other execution assistance.                          *)
(* ------------------------------------------------------------------------- *)

let OPERAND_SIZE_CASES = prove
 (`(match 256 with 256 -> a | 128 -> b) = a /\
   (match 128 with 256 -> a | 128 -> b) = b /\
   (match 128 with 128 -> a | 64 -> b) = a /\
   (match 64 with 128 -> a | 64 -> b) = b /\
   (match 128 with 128 -> a | 32 -> b) = a /\
   (match 32 with 128 -> a | 32 -> b) = b /\
   (match 64 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = a /\
   (match 32 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = b /\
   (match 16 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = c /\
   (match  8 with 64 -> a | 32 -> b | 16 -> c | 8 -> d) = d /\
   (match 64 with 64 -> a | 32 -> b | 16 -> c) = a /\
   (match 32 with 64 -> a | 32 -> b | 16 -> c) = b /\
   (match 16 with 64 -> a | 32 -> b | 16 -> c) = c /\
   (match 64 with 64 -> a | 32 -> b) = a /\
   (match 32 with 64 -> a | 32 -> b) = b /\
   (match 32 with 32 -> a | 16 -> b) = a /\
   (match 16 with 32 -> a | 16 -> b) = b /\
   (match (32,128) with (32,128) -> a | (128,32) -> b) = a /\
   (match (128,32) with (32,128) -> a | (128,32) -> b) = b /\
   (match (64,128) with (64,128) -> a | (128,64) -> b) = a /\
   (match (128,64) with (64,128) -> a | (128,64) -> b) = b /\
   (match (64,128) with (64,128) -> a | (128,64) -> b | (128,128) -> c) = a /\
   (match (128,64) with (64,128) -> a | (128,64) -> b | (128,128) -> c) = b /\
   (match (128,128) with (64,128) -> a | (128,64) -> b | (128,128) -> c) = c /\
   (match (64,32) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = a /\
   (match (64,16) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = b /\
   (match (64,8) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = c /\
   (match (32,32) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = d /\
   (match (32,16) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = e /\
   (match (32,8) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = f /\
   (match (16,8) with
      (64,32) -> a  | (64,16) -> b  | (64,8) -> c | (32,32) -> d
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = g /\
   (match (64,16) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = b /\
   (match (64,8) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = c /\
   (match (32,16) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = e /\
   (match (32,8) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = f /\
   (match (16,8) with
      (64,16) -> b  | (64,8) -> c
    | (32,16) -> e | (32,8) -> f  | (16,8) -> g) = g`,
  CONV_TAC(TOP_DEPTH_CONV MATCH_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let X86_EXECUTE =
  CONV_RULE (TOP_DEPTH_CONV let_CONV)
   (GEN_REWRITE_RULE LAND_CONV [ETA_AX]
     (GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]
        (GEN `s:x86state` x86_execute)));;

(* A set of theorems pre-evaluated to the corresponding match case.
  [("ADC",
    |- x86_execute (ADC a0 a1) =
       (\s.
            (add_load_event a1 s ,,
             add_load_event a0 s ,,
             add_store_event a0 s ,,
             (\s.
                  (match operand_size a0 with
                     64 -> x86_ADC (OPERAND64 a0 s) (OPERAND64 a1 s)
                   | 32 -> x86_ADC (OPERAND32 a0 s) (OPERAND32 a1 s)
                   | 16 -> x86_ADC (OPERAND16 a0 s) (OPERAND16 a1 s)
                   | 8 -> x86_ADC (OPERAND8 a0 s) (OPERAND8 a1 s))
                  s))
            s));
    ...]
*)
let X86_EXECUTE_CASES:(string * thm) list =
  let constructors =
    (conjuncts o fst o dest_imp o snd o strip_forall o concl)
    instruction_INDUCTION in
  let constructors = map (snd o strip_forall) constructors in
  let constructors = map rand constructors in
  map (fun inst ->
      let name = (name_of o fst o strip_comb) inst in
      let tapp = mk_comb (`x86_execute`,inst) in
      (* if inst is an operation with tuple arguments, unfold them.
        ex: MULX4 a0 a1 -> MUX4 (fst a0, snd a0) (fst a1, snd a1) *)
      let tapp_pairs_unfolded = ONCE_DEPTH_CONV
          (ONCE_REWRITE_CONV [GSYM PAIR]) tapp in
      let full_expr = REWRITE_CONV[X86_EXECUTE]
          (rhs (concl tapp_pairs_unfolded)) in
      (name,TRANS tapp_pairs_unfolded full_expr))
    constructors;;

let REGISTER_ALIASES =
 [rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
  r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
  eax; ecx; edx; ebx; esp; ebp; esi; edi;
  r8d; r9d; r10d; r11d; r12d; r13d; r14d; r15d;
  r8w; r9w; r10w; r11w; r12w; r13w; r14w; r15w;
  r8b; r9b; r10b; r11b; r12b; r13b; r14b; r15b;
  ax; cx; dx; bx; sp; bp; si; di; ah;
  al; ch; cl; dh; dl; bh; bl; spl; bpl; sil; dil;
  xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7;
  xmm8; xmm9; xmm10; xmm11; xmm12; xmm13; xmm14; xmm15;
  ymm0; ymm1; ymm2; ymm3; ymm4; ymm5; ymm6; ymm7;
  ymm8; ymm9; ymm10; ymm11;ymm12; ymm13; ymm14; ymm15];;

let OPERAND_SIZE_CONV =
  let topconv = GEN_REWRITE_CONV I [operand_size]
  and botconv = GEN_REWRITE_CONV TOP_DEPTH_CONV (QWORD::REGISTER_ALIASES)
  and midconv = GEN_REWRITE_CONV REPEATC
   [simdregister_size; register_size; bytesize; simdregsize; regsize] in
  fun tm ->
    match tm with
      Comb(Const("operand_size",_),_)->
          (botconv THENC topconv THENC midconv) tm
    | _ -> failwith "OPERAND_SIZE_CONV";;

let BSID_CLAUSES_GEN = prove
 (`bsid_semantics (Bsid (SOME(Gpr r1 Full_64)) (SOME(Gpr r2 Full_64)) k d) s =
   word_add (read (registers :> element r1) s)
            (word (2 EXP (val k) * val(read (registers :> element r2) s) +
                   val d)) /\
   bsid_semantics (Bsid NONE (SOME(Gpr r2 Full_64)) k d) s =
   word_add (word 0)
    (word (2 EXP (val k) * val(read (registers :> element r2) s) + val d)) /\
   bsid_semantics (Bsid (SOME(Gpr r1 Full_64)) NONE k d) s =
   word_add (read (registers :> element r1) s) d /\
   bsid_semantics(Riprel off) s = word(val(read RIP s) + val off)`,
  REWRITE_TAC[bsid_semantics; GPR] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[WORD_ADD_ASSOC; WORD_VAL] THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN TRY BINOP_TAC THEN
  REWRITE_TAC[WORD_MUL; WORD_VAL] THEN TRY AP_TERM_TAC THEN
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[read; asnumber; through] THEN REWRITE_TAC[WORD_VAL]);;

let BSID_SEMANTICS_CONV =
  let coreconv =
    GEN_REWRITE_CONV (LAND_CONV o TRY_CONV)
     [base_displacement; base_scaled_index;
      base_scaled_index_displacement] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
      r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15] THENC
    GEN_REWRITE_CONV I [BSID_CLAUSES_GEN] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     (map GSYM [RAX;  RCX;  RDX;  RBX;  RSP;  RBP;  RSI;  RDI;
                R8;   R9;  R10;  R11;  R12;  R13;  R14;  R15]) THENC
    ONCE_DEPTH_CONV WORD_VAL_CONV THENC
    ONCE_DEPTH_CONV NUM_REDUCE_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [ARITH_RULE `n + 0 = n`] in
  fun tm ->
   (match tm with
      Comb(Comb(Const("bsid_semantics",_),_),_) -> coreconv tm
    | _ -> failwith "BSID_SEMANTICS_CONV");;

let BSID_NORMALIZE_TAC =
  let pth_gen = prove
   (`word(8 * i + 0):int64 = word(8 * i) /\
     word(8 * i + 8):int64 = word(8 * (i + 1)) /\
     word(8 * i + 16):int64 = word(8 * (i + 2))`,
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ARITH_TAC)
  and pth_spc = prove
   (`0 < i ==> word(8 * i + 18446744073709551608):int64 = word(8 * (i - 1))`,
    SPEC_TAC(`i:num`,`i:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[LT_REFL; SUC_SUB1] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `8 * SUC i + 18446744073709551608 =
      1 * 2 EXP 64 + 8 * i`]) in
  let rule_spc = PART_MATCH (lhand o rand) pth_spc in
  let siderule =
    let siderule_1 asl tm = find (fun th -> concl th = tm) asl
    and rules = map (PART_MATCH rand o ARITH_RULE)
     [`1 <= n ==> 0 < n`; `~(n = 0) ==> 0 < n`;  `m < n ==> 0 < n - m`] in
    fun asl tm ->
      tryfind (fun rule ->
            let th = rule tm in
            MP th (siderule_1 asl (lhand(concl th)))) rules in
  let fullconv(asl,w) tm =
    if not(vfree_in tm w) then failwith "rule" else
    let th = rule_spc tm in
    MP th (siderule (map snd asl) (lhand(concl th))) in
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [pth_gen] THEN
  W(fun (asl,w) -> CONV_TAC(ONCE_DEPTH_CONV(fullconv(asl,w))));;

let BSID_CLAUSES = prove
 (`bsid_semantics (%%(rax,d)) s = word_add (read RAX s) (word d) /\
   bsid_semantics (%%(rcx,d)) s = word_add (read RCX s) (word d) /\
   bsid_semantics (%%(rdx,d)) s = word_add (read RDX s) (word d) /\
   bsid_semantics (%%(rbx,d)) s = word_add (read RBX s) (word d) /\
   bsid_semantics (%%(rsp,d)) s = word_add (read RSP s) (word d) /\
   bsid_semantics (%%(rbp,d)) s = word_add (read RBP s) (word d) /\
   bsid_semantics (%%(rsi,d)) s = word_add (read RSI s) (word d) /\
   bsid_semantics (%%(rdi,d)) s = word_add (read RDI s) (word d) /\
   bsid_semantics (%%( r8,d)) s = word_add (read  R8 s) (word d) /\
   bsid_semantics (%%( r9,d)) s = word_add (read  R9 s) (word d) /\
   bsid_semantics (%%(r10,d)) s = word_add (read R10 s) (word d) /\
   bsid_semantics (%%(r11,d)) s = word_add (read R11 s) (word d) /\
   bsid_semantics (%%(r12,d)) s = word_add (read R12 s) (word d) /\
   bsid_semantics (%%(r13,d)) s = word_add (read R13 s) (word d) /\
   bsid_semantics (%%(r14,d)) s = word_add (read R14 s) (word d) /\
   bsid_semantics (%%(r15,d)) s = word_add (read R15 s) (word d)`,
  REWRITE_TAC[rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
              r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
              RAX;  RCX;  RDX;  RBX;  RSP;  RBP;  RSI;  RDI;
              R8;   R9;  R10;  R11;  R12;  R13;  R14;  R15] THEN
  REWRITE_TAC[BSID_CLAUSES_GEN; base_displacement]);;

let OPERAND_CLAUSES = prove
 (`OPERAND128(%_% xmm0) s = YMM0 :> zerotop_128  /\
   OPERAND128(%_% xmm1) s = YMM1 :> zerotop_128  /\
   OPERAND128(%_% xmm2) s = YMM2 :> zerotop_128  /\
   OPERAND128(%_% xmm3) s = YMM3 :> zerotop_128  /\
   OPERAND128(%_% xmm4) s = YMM4 :> zerotop_128  /\
   OPERAND128(%_% xmm5) s = YMM5 :> zerotop_128  /\
   OPERAND128(%_% xmm6) s = YMM6 :> zerotop_128  /\
   OPERAND128(%_% xmm7) s = YMM7 :> zerotop_128  /\
   OPERAND128(%_% xmm8) s = YMM8 :> zerotop_128  /\
   OPERAND128(%_% xmm9) s = YMM9 :> zerotop_128  /\
   OPERAND128(%_% xmm10) s = YMM10 :> zerotop_128  /\
   OPERAND128(%_% xmm11) s = YMM11 :> zerotop_128  /\
   OPERAND128(%_% xmm12) s = YMM12 :> zerotop_128  /\
   OPERAND128(%_% xmm13) s = YMM13 :> zerotop_128  /\
   OPERAND128(%_% xmm14) s = YMM14 :> zerotop_128  /\
   OPERAND128(%_% xmm15) s = YMM15 :> zerotop_128  /\
   OPERAND128 (Memop Word128 bsid) s =
    memory :> bytes128 (bsid_semantics bsid s) /\
   OPERAND128_SSE(%_% xmm0) s = YMM0_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm1) s = YMM1_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm2) s = YMM2_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm3) s = YMM3_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm4) s = YMM4_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm5) s = YMM5_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm6) s = YMM6_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm7) s = YMM7_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm8) s = YMM8_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm9) s = YMM9_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm10) s = YMM10_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm11) s = YMM11_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm12) s = YMM12_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm13) s = YMM13_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm14) s = YMM14_SSE :> bottom_128  /\
   OPERAND128_SSE(%_% xmm15) s = YMM15_SSE :> bottom_128  /\
   OPERAND128_SSE (Memop Word128 bsid) s =
    memory :> bytes128 (bsid_semantics bsid s) /\
   OPERAND256(%_% ymm0) s = YMM0  /\
   OPERAND256(%_% ymm1) s = YMM1  /\
   OPERAND256(%_% ymm2) s = YMM2  /\
   OPERAND256(%_% ymm3) s = YMM3  /\
   OPERAND256(%_% ymm4) s = YMM4  /\
   OPERAND256(%_% ymm5) s = YMM5  /\
   OPERAND256(%_% ymm6) s = YMM6  /\
   OPERAND256(%_% ymm7) s = YMM7  /\
   OPERAND256(%_% ymm8) s = YMM8  /\
   OPERAND256(%_% ymm9) s = YMM9  /\
   OPERAND256(%_% ymm10) s = YMM10  /\
   OPERAND256(%_% ymm11) s = YMM11  /\
   OPERAND256(%_% ymm12) s = YMM12  /\
   OPERAND256(%_% ymm13) s = YMM13  /\
   OPERAND256(%_% ymm14) s = YMM14  /\
   OPERAND256(%_% ymm15) s = YMM15  /\
   OPERAND256 (Memop Word256 bsid) s =
    memory :> bytes256 (bsid_semantics bsid s) /\
   OPERAND64 (%rax) s = RAX /\
   OPERAND64 (%rcx) s = RCX /\
   OPERAND64 (%rdx) s = RDX /\
   OPERAND64 (%rbx) s = RBX /\
   OPERAND64 (%rsp) s = RSP /\
   OPERAND64 (%rbp) s = RBP /\
   OPERAND64 (%rsi) s = RSI /\
   OPERAND64 (%rdi) s = RDI /\
   OPERAND64 (% r8) s =  R8 /\
   OPERAND64 (% r9) s =  R9 /\
   OPERAND64 (%r10) s = R10 /\
   OPERAND64 (%r11) s = R11 /\
   OPERAND64 (%r12) s = R12 /\
   OPERAND64 (%r13) s = R13 /\
   OPERAND64 (%r14) s = R14 /\
   OPERAND64 (%r15) s = R15 /\
   OPERAND64 (## n) s = rvalue(word_sx(word n:32 word)) /\
   OPERAND64 (Imm64 w64) s = rvalue w64 /\
   OPERAND64 (Imm32 w32) s = rvalue(word_sx w32) /\
   OPERAND64 (Imm16 w16) s = rvalue(word_sx w16) /\
   OPERAND64 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND64 (QWORD bsid) s = memory :> bytes64 (bsid_semantics bsid s) /\
   OPERAND64 (Memop Quadword bsid) s =
    memory :> bytes64 (bsid_semantics bsid s) /\
   OPERAND32 (%eax) s = RAX :> zerotop_32 /\
   OPERAND32 (%ecx) s = RCX :> zerotop_32 /\
   OPERAND32 (%edx) s = RDX :> zerotop_32 /\
   OPERAND32 (%ebx) s = RBX :> zerotop_32 /\
   OPERAND32 (%esp) s = RSP :> zerotop_32 /\
   OPERAND32 (%ebp) s = RBP :> zerotop_32 /\
   OPERAND32 (%esi) s = RSI :> zerotop_32 /\
   OPERAND32 (%edi) s = RDI :> zerotop_32 /\
   OPERAND32 (%r8d) s =  R8 :> zerotop_32 /\
   OPERAND32 (%r9d) s =  R9 :> zerotop_32 /\
   OPERAND32 (%r10d) s = R10 :> zerotop_32 /\
   OPERAND32 (%r11d) s = R11 :> zerotop_32 /\
   OPERAND32 (%r12d) s = R12 :> zerotop_32 /\
   OPERAND32 (%r13d) s = R13 :> zerotop_32 /\
   OPERAND32 (%r14d) s = R14 :> zerotop_32 /\
   OPERAND32 (%r15d) s = R15 :> zerotop_32 /\
   OPERAND32 (## n) s = rvalue(word n:32 word) /\
   OPERAND32 (Imm32 w32) s = rvalue w32 /\
   OPERAND32 (Imm16 w16) s = rvalue(word_sx w16) /\
   OPERAND32 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND32 (Memop Doubleword bsid) s =
    memory :> bytes32 (bsid_semantics bsid s) /\
   OPERAND16 (%ax) s = RAX :> bottom_32 :> bottom_16 /\
   OPERAND16 (%cx) s = RCX :> bottom_32 :> bottom_16 /\
   OPERAND16 (%dx) s = RDX :> bottom_32 :> bottom_16 /\
   OPERAND16 (%bx) s = RBX :> bottom_32 :> bottom_16 /\
   OPERAND16 (%sp) s = RSP :> bottom_32 :> bottom_16 /\
   OPERAND16 (%bp) s = RBP :> bottom_32 :> bottom_16 /\
   OPERAND16 (%si) s = RSI :> bottom_32 :> bottom_16 /\
   OPERAND16 (%di) s = RDI :> bottom_32 :> bottom_16 /\
   OPERAND16 (Imm16 w16) s = rvalue w16 /\
   OPERAND16 (Imm8 w8) s = rvalue(word_sx w8) /\
   OPERAND16 (Memop Word bsid) s =
    memory :> bytes16 (bsid_semantics bsid s) /\
   OPERAND8 (%al) s = RAX :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%cl) s = RCX :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%dl) s = RDX :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%bl) s = RBX :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%spl) s = RSP :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%bpl) s = RBP :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%sil) s = RSI :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%dil) s = RDI :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (% r8b) s =  R8 :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (% r9b) s =  R9 :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%r10b) s = R10 :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%r11b) s = R11 :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%r12b) s = R12 :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%r13b) s = R13 :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%r14b) s = R14 :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%r15b) s = R15 :> bottom_32 :> bottom_16 :> bottom_8 /\
   OPERAND8 (%ah) s = RAX :> bottom_32 :> bottom_16 :> top_8 /\
   OPERAND8 (%ch) s = RCX :> bottom_32 :> bottom_16 :> top_8 /\
   OPERAND8 (%dh) s = RDX :> bottom_32 :> bottom_16 :> top_8 /\
   OPERAND8 (%bh) s = RBX :> bottom_32 :> bottom_16 :> top_8 /\
   OPERAND8 (Imm8 w8) s = rvalue w8 /\
   OPERAND8 (Memop Byte bsid) s =
    memory :> bytes8 (bsid_semantics bsid s)`,
  REWRITE_TAC[rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
              r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
              RAX;  RCX;  RDX;  RBX;  RSP;  RBP;  RSI;  RDI;
              R8;   R9;  R10;  R11;  R12;  R13;  R14;  R15;
              eax; ecx; edx; ebx; esp; ebp; esi; edi;
              r8d; r9d; r10d; r11d; r12d; r13d; r14d; r15d;
              ax; cx; dx; bx; sp; bp; si; di; ah;
              al; ch; cl; dh; dl; bh; bl; spl; bpl; sil; dil;
              r8b; r9b; r10b; r11b; r12b; r13b; r14b; r15b;
              EAX; ECX; EDX; EBX; ESP; EBP; ESI; EDI;
              R8D; R9D; R10D; R11D; R12D; R13D; R14D; R15D;
              AX; CX; DX; BX; SP; BP; SI; DI;
              AH; AL; BH; BL; CH; CL; DH; DL;
              SPL; BPL; SIL; DIL;
              xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7;
              xmm8; xmm9; xmm10; xmm11; xmm12; xmm13; xmm14; xmm15;
              XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8;
              XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15;
              XMM0_SSE; XMM1_SSE; XMM2_SSE; XMM3_SSE;
              XMM4_SSE; XMM5_SSE; XMM6_SSE; XMM7_SSE;
              XMM8_SSE; XMM9_SSE; XMM10_SSE; XMM11_SSE;
              XMM12_SSE; XMM13_SSE; XMM14_SSE; XMM15_SSE;
              ymm0; ymm1; ymm2; ymm3; ymm4; ymm5; ymm6; ymm7;
              ymm8; ymm9; ymm10; ymm11; ymm12; ymm13; ymm14; ymm15;
              YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7; YMM8;
              YMM9; YMM10; YMM11; YMM12; YMM13; YMM14; YMM15;
              YMM0_SSE; YMM1_SSE; YMM2_SSE; YMM3_SSE;
              YMM4_SSE; YMM5_SSE; YMM6_SSE; YMM7_SSE;
              YMM8_SSE; YMM9_SSE; YMM10_SSE; YMM11_SSE;
              YMM12_SSE; YMM13_SSE; YMM14_SSE; YMM15_SSE;
              ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8;
              ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] THEN
  REWRITE_TAC[simple_immediate; base_displacement; QWORD] THEN
  REWRITE_TAC[OPERAND256; OPERAND128; OPERAND128_SSE; OPERAND64; OPERAND32; OPERAND16; OPERAND8;
              register_size; regsize; simdregister_size; simdregsize;
              SIMD256; SIMD128; SIMD128_SSE; GPR64; GPR32_Z; GPR32; GPR16; GPR8] THEN
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Some forms with a comprehensible carry flag; currently 64-bit only.       *)
(* Also 64-bit instantiations of PUSH and POP are much simpler to work with. *)
(* ------------------------------------------------------------------------- *)

let x86_ADC_ALT = prove
 (`x86_ADC dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (2 EXP 64 <= val x + val y + c) ,,
         OF := ~(ival x + ival y + &c = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) + c =
                 val(word_zx z:nybble))) s`,
  REWRITE_TAC[x86_ADC] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let x86_ADCX_ALT = prove
 (`x86_ADCX dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:64 word) ,,
         CF := (2 EXP 64 <= val x + val y + c)) s`,
  REWRITE_TAC[x86_ADCX] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let x86_ADOX_ALT = prove
 (`x86_ADOX dest src s =
        let x = read dest s and y = read src s and c = bitval(read OF s) in
        let z = word_add (word_add x y) (word c) in
        (dest := (z:64 word) ,,
         OF := (2 EXP 64 <= val x + val y + c)) s`,
  REWRITE_TAC[x86_ADOX] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADC]);;

let x86_ADD_ALT = prove
 (`x86_ADD dest src s =
        let x = read dest s and y = read src s in
        let z = word_add x y in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (2 EXP 64 <= val x + val y) ,,
         OF := ~(ival x + ival y = ival z) ,,
         AF := ~(val(word_zx x:nybble) + val(word_zx y:nybble) =
                 val(word_zx z:nybble))) s`,
  REWRITE_TAC[x86_ADD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_ADD]);;

let x86_SBB_ALT = prove
 (`x86_SBB dest src s =
        let x = read dest s and y = read src s and c = bitval(read CF s) in
        let z = word_sub x (word_add y (word c)) in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (val x < val y + c) ,,
         OF := ~(ival x - (ival y + &c) = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) -
                 (&(val(word_zx y:nybble)) + &c):int =
                 &(val(word_zx z:nybble)))) s`,
  REWRITE_TAC[x86_SBB] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_SBB]);;

let x86_SUB_ALT = prove
 (`x86_SUB dest src s =
        let x = read dest s and y = read src s in
        let z = word_sub x y in
        (dest := (z:64 word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (val x < val y) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`,
  REWRITE_TAC[x86_SUB] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_SUB]);;

let x86_CMP_ALT = prove
 (`x86_CMP dest src s =
        let x = read dest s and y = read src s in
        let (z:64 word) = word_sub x y in
        (ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := (val x < val y) ,,
         OF := ~(ival x - ival y = ival z) ,,
         AF := ~(&(val(word_zx x:nybble)) - &(val(word_zx y:nybble)):int =
                 &(val(word_zx z:nybble)))) s`,
  REWRITE_TAC[x86_CMP] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CARRY64_SUB]);;

let x86_POP_ALT = prove
 (`x86_POP dest s =
        let p = read RSP s in
        let x = read (memory :> bytes64 p) s in
        let p' = word_add p (word 8) in
        (events := CONS (EventLoad (p, 8)) (read events s) ,,
         RSP := p' ,,
         dest := x) s`,
  REWRITE_TAC[x86_POP; DIMINDEX_64; bytes64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; asword; through; read; write]);;

let x86_PUSH_ALT = prove
 (`x86_PUSH src s =
        let p = read RSP s
        and x = read src s in
        let p' = word_sub p (word 8) in
        (events := CONS (EventStore (p', 8)) (read events s) ,,
         RSP := p' ,,
         memory :> bytes64 p' := x) s`,
  REWRITE_TAC[x86_PUSH; DIMINDEX_64; bytes64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE; asword; through; read; write; seq;
              assign]);;

let x86_CALL_ALT = prove
 (`x86_CALL target s =
        let p = read RSP s
        and x = read RIP s
        and e0 = read events s in
        let p' = word_sub p (word 8) in
        (events := CONS (EventStore (p', 8)) (CONS (EventJump (x, target)) e0) ,,
         RSP := p' ,,
         memory :> bytes64 p' := x ,,
         RIP := target) s`,
  REWRITE_TAC[x86_CALL] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[x86_PUSH_ALT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; seq; assign] THEN
  STRIP_TAC THEN
  REWRITE_TAC[METIS[] `(exists (x:A). y = x /\ Q x) <=> Q y`] THEN
  CONV_TAC (ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV) THEN
  CONV_TAC (ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC (ONCE_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  REFL_TAC);;

(*** More alternatives that are nicer to work with ***)

let x86_BTC_ALT = prove
 (`x86_BTC dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest := word_xor x (word_shl (word 1) c) ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`,
  REWRITE_TAC[x86_BTC] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; seq; assign; UNWIND_THM1] THEN
  X_GEN_TAC `s':x86state` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN] THEN
  SIMP_TAC[READ_BITELEMENT; BIT_WORD_XOR; BIT_WORD_SHL; BIT_WORD_1] THEN
  REWRITE_TAC[MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ARITH_RULE `j <= i /\ i - j = 0 <=> i = j`] THEN
  MESON_TAC[]);;

let x86_BTR_ALT = prove
 (`x86_BTR dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest := word_and x (word_not(word_shl (word 1) c)) ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`,
  REWRITE_TAC[x86_BTR] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; seq; assign; UNWIND_THM1] THEN
  X_GEN_TAC `s':x86state` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN] THEN
  SIMP_TAC[READ_BITELEMENT; BIT_WORD_AND; BIT_WORD_NOT;
           BIT_WORD_SHL; BIT_WORD_1] THEN
  REWRITE_TAC[MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ARITH_RULE `j <= i /\ i - j = 0 <=> i = j`] THEN
  MESON_TAC[]);;

let x86_BTS_ALT = prove
 (`x86_BTS dest src s =
        let (x:N word) = read dest s and y = read src s in
        let c = val y MOD dimindex(:N) in
        let b = bit c x in
        (dest := word_or x (word_shl (word 1) c) ,,
         CF := b ,,
         UNDEFINED_VALUES[SF;PF;OF;AF]) s`,
  REWRITE_TAC[x86_BTS] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM; seq; assign; UNWIND_THM1] THEN
  X_GEN_TAC `s':x86state` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[GSYM READ_BITELEMENT; READ_WRITE_BITELEMENT_GEN] THEN
  SIMP_TAC[READ_BITELEMENT; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_1] THEN
  REWRITE_TAC[MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[ARITH_RULE `j <= i /\ i - j = 0 <=> i = j`] THEN
  MESON_TAC[]);;

let x86_MOVSB_ALT = prove
 (`x86_MOVSB rept dest src size s =
        let sptr = read src s
        and dptr = read dest s
        and n:int64 = read size s
        and df = read DF s in
        let sbuf = if df then word_sub sptr (word_sub n (word 1)) else sptr
        and dbuf = if df then word_sub dptr (word_sub n (word 1)) else dptr in
        (events := CONS (EventStore (dbuf,val n))
                        (CONS (EventLoad (sbuf,val n)) (read events s)) ,,
         (\s. (memory :> bytes (dbuf,val n) :=
                 x86_stringcopy df sbuf dbuf (val n)
                   (read (memory :> bytes (sbuf,val n)) s)
                   (read (memory :> bytes (dbuf,val n)) s)) s) ,,
         src := (if df then word_sub sptr n else word_add sptr n) ,,
         dest := (if df then word_sub dptr n else word_add dptr n) ,,
         (if rept then size := word 0 else (=))) s`,
  ASM_SIMP_TAC[x86_MOVSB; x86_stringcopy; VAL_BOUND_64] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; assign; seq]);;

(*** Simplify word operations in SIMD instructions ***)

let all_simd_rules =
   [usimd16;usimd8;usimd4;usimd2;simd32;simd16;simd8;simd4;simd2;msimd16;msimd8;msimd4;msimd2];;

let EXPAND_SIMD_RULE =
  CONV_RULE (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) o
  CONV_RULE (DEPTH_CONV DIMINDEX_CONV) o REWRITE_RULE all_simd_rules;;

let x86_PADDD_ALT = EXPAND_SIMD_RULE x86_PADDD;;
let x86_PADDQ_ALT = EXPAND_SIMD_RULE x86_PADDQ;;
let x86_PBLENDW_ALT = EXPAND_SIMD_RULE x86_PBLENDW;;
let x86_PCMPGTD_ALT = EXPAND_SIMD_RULE x86_PCMPGTD;;
let x86_PCMPGTW_ALT = EXPAND_SIMD_RULE x86_PCMPGTW;;

let x86_PEXT_ALT =
  (end_itlist CONJ o map
    (CONV_RULE NUM_REDUCE_CONV o
     CONV_RULE(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) o
     (REWRITE_RULE[DIMINDEX_32; DIMINDEX_64; ARITH])))
  [INST_TYPE[`:32`,`:N`] x86_PEXT;
   INST_TYPE[`:64`,`:N`] x86_PEXT];;

let x86_PMOVMSKB_ALT = EXPAND_SIMD_RULE x86_PMOVMSKB;;
let x86_PSHUFB_ALT = EXPAND_SIMD_RULE x86_PSHUFB;;
let x86_PSHUFD_ALT = EXPAND_SIMD_RULE x86_PSHUFD;;
let x86_PSRAD_ALT = EXPAND_SIMD_RULE x86_PSRAD;;
let x86_PSRLW_ALT = EXPAND_SIMD_RULE x86_PSRLW;;
let x86_VMOVDQA_ALT = EXPAND_SIMD_RULE x86_VMOVDQA;;
let x86_VMOVDQU_ALT = EXPAND_SIMD_RULE x86_VMOVDQU;;
let x86_VMOVSHDUP_ALT = EXPAND_SIMD_RULE x86_VMOVSHDUP;;
let x86_VMOVSLDUP_ALT = EXPAND_SIMD_RULE x86_VMOVSLDUP;;
let x86_VPADDB_ALT = EXPAND_SIMD_RULE x86_VPADDB;;
let x86_VPADDD_ALT = EXPAND_SIMD_RULE x86_VPADDD;;
let x86_VPADDQ_ALT = EXPAND_SIMD_RULE x86_VPADDQ;;
let x86_VPADDW_ALT = EXPAND_SIMD_RULE x86_VPADDW;;
let x86_VPBLENDD_ALT = EXPAND_SIMD_RULE x86_VPBLENDD;;
let x86_VPBLENDW_ALT = EXPAND_SIMD_RULE x86_VPBLENDW;;
let x86_VPCLMULQDQ_ALT = EXPAND_SIMD_RULE x86_VPCLMULQDQ;;
let x86_VPBROADCASTD_ALT = EXPAND_SIMD_RULE x86_VPBROADCASTD;;
let x86_VPBROADCASTQ_ALT = EXPAND_SIMD_RULE x86_VPBROADCASTQ;;
let x86_VPBROADCASTW_ALT = EXPAND_SIMD_RULE x86_VPBROADCASTW;;
let x86_VPERMD_ALT = EXPAND_SIMD_RULE x86_VPERMD;;
let x86_VPERMQ_ALT = EXPAND_SIMD_RULE x86_VPERMQ;;
let x86_VPERM2I128_ALT = EXPAND_SIMD_RULE x86_VPERM2I128;;
let x86_VPCMPGTD_ALT = EXPAND_SIMD_RULE x86_VPCMPGTD;;
let x86_VPCMPGTW_ALT = EXPAND_SIMD_RULE x86_VPCMPGTW;;
let x86_VPACKUSWB_ALT =
  (CONV_RULE (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) o
   CONV_RULE NUM_REDUCE_CONV o
   CONV_RULE (TOP_DEPTH_CONV EXPAND_NSUM_CONV) o
   CONV_RULE (DEPTH_CONV DIMINDEX_CONV)) x86_VPACKUSWB;;
let x86_VPBLENDVB_ALT =
  (CONV_RULE (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) o
   CONV_RULE NUM_REDUCE_CONV o
   CONV_RULE (TOP_DEPTH_CONV EXPAND_NSUM_CONV) o
   CONV_RULE (DEPTH_CONV DIMINDEX_CONV)) x86_VPBLENDVB;;
let x86_VPMADDUBSW_ALT = EXPAND_SIMD_RULE x86_VPMADDUBSW;;
let x86_VPMADDWD_ALT = EXPAND_SIMD_RULE x86_VPMADDWD;;
let x86_VMOVMSKPS_ALT = x86_VMOVMSKPS;;
let x86_VPABSD_ALT = EXPAND_SIMD_RULE x86_VPABSD;;
let x86_VPMOVMSKB_ALT =
  (CONV_RULE
     (TOP_DEPTH_CONV let_CONV THENC
      ONCE_DEPTH_CONV EXPAND_NSUM_CONV THENC
      NUM_REDUCE_CONV THENC
      GEN_REWRITE_CONV TOP_DEPTH_CONV [MULT_CLAUSES])) x86_VPMOVMSKB;;
let x86_VPMOVSXBD_ALT = EXPAND_SIMD_RULE x86_VPMOVSXBD;;
let x86_VPMOVZXBD_ALT = EXPAND_SIMD_RULE x86_VPMOVZXBD;;
let x86_VPMOVZXBW_ALT = EXPAND_SIMD_RULE x86_VPMOVZXBW;;
let x86_VPTEST_ALT = x86_VPTEST;;
let x86_VZEROUPPER_ALT = x86_VZEROUPPER;;
let x86_VPMULDQ_ALT = EXPAND_SIMD_RULE x86_VPMULDQ;;
let x86_VPMULHRSW_ALT = EXPAND_SIMD_RULE x86_VPMULHRSW;;
let x86_VPMULHUW_ALT = EXPAND_SIMD_RULE x86_VPMULHUW;;
let x86_VPMULHW_ALT = EXPAND_SIMD_RULE x86_VPMULHW;;
let x86_VPMULLD_ALT = EXPAND_SIMD_RULE x86_VPMULLD;;
let x86_VPMULLW_ALT = EXPAND_SIMD_RULE x86_VPMULLW;;
let x86_VPSHUFB_ALT = EXPAND_SIMD_RULE x86_VPSHUFB;;
let x86_VPSLLD_ALT = EXPAND_SIMD_RULE x86_VPSLLD;;
let x86_VPSLLVD_ALT = EXPAND_SIMD_RULE x86_VPSLLVD;;
let x86_VPSLLQ_ALT = EXPAND_SIMD_RULE x86_VPSLLQ;;
let x86_VPSLLW_ALT = EXPAND_SIMD_RULE x86_VPSLLW;;
let x86_VPSUBB_ALT = EXPAND_SIMD_RULE x86_VPSUBB;;
let x86_VPSUBD_ALT = EXPAND_SIMD_RULE x86_VPSUBD;;
let x86_VPSUBQ_ALT = EXPAND_SIMD_RULE x86_VPSUBQ;;
let x86_VPSUBW_ALT = EXPAND_SIMD_RULE x86_VPSUBW;;
let x86_VPSRAD_ALT = EXPAND_SIMD_RULE x86_VPSRAD;;
let x86_VPSRLD_ALT = EXPAND_SIMD_RULE x86_VPSRLD;;
let x86_VPSRLVD_ALT = EXPAND_SIMD_RULE x86_VPSRLVD;;
let x86_VPSRLVQ_ALT = EXPAND_SIMD_RULE x86_VPSRLVQ;;
let x86_VPSRLDQ_ALT = EXPAND_SIMD_RULE x86_VPSRLDQ;;
let x86_VPSRLQ_ALT = EXPAND_SIMD_RULE x86_VPSRLQ;;
let x86_VPSRAW_ALT = EXPAND_SIMD_RULE x86_VPSRAW;;
let x86_VPSRLW_ALT = EXPAND_SIMD_RULE x86_VPSRLW;;
let x86_VPUNPCKHQDQ_ALT = EXPAND_SIMD_RULE x86_VPUNPCKHQDQ;;
let x86_VPUNPCKLQDQ_ALT = EXPAND_SIMD_RULE x86_VPUNPCKLQDQ;;

let X86_OPERATION_CLAUSES =
  map (CONV_RULE (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) o
       REWRITE_RULE[WORD_ZX_TRIVIAL] o
       CONV_RULE(TOP_DEPTH_CONV let_CONV) o SPEC_ALL)
   [x86_ADC_ALT; x86_ADCX_ALT; x86_ADOX_ALT; x86_ADD_ALT;
    x86_AESDEC; x86_AESDECLAST; x86_AESENC; x86_AESENCLAST;
    x86_AESKEYGENASSIST; x86_AND;
    x86_BSF; x86_BSR; x86_BSWAP; x86_BT; x86_BTC_ALT; x86_BTR_ALT; x86_BTS_ALT;
    x86_CALL_ALT; x86_CLC; x86_CLD; x86_CMC; x86_CMOV; x86_CMP_ALT; x86_DEC;
    x86_ENDBR64; x86_IMUL; x86_IMUL2; x86_IMUL3; x86_INC; x86_LEA; x86_LZCNT;
    x86_MOV; x86_MOVAPS; x86_MOVDQA; x86_MOVDQU; x86_MOVD; x86_MOVQ; x86_VMOVD; x86_VMOVQ;
    x86_VMOVHPD; x86_MOVSX; x86_MOVUPS; x86_MOVSB_ALT;
    x86_MOVZX; x86_MUL2; x86_MULX4; x86_NEG; x86_NOP; x86_NOP_N; x86_NOT; x86_OR;
    x86_PADDD_ALT; x86_PADDQ_ALT; x86_PAND; x86_PBLENDW_ALT; x86_PCMPGTD_ALT; x86_PCMPGTW_ALT;
    x86_PEXT_ALT; x86_PINSRD; x86_PINSRQ; x86_PMOVMSKB_ALT; x86_POP_ALT; x86_POPCNT;
    x86_PSHUFB_ALT; x86_PSHUFD_ALT; x86_PSRAD_ALT; x86_PSRLW_ALT; x86_PUSH_ALT; x86_PXOR;
    x86_RCL; x86_RCR; x86_RET; x86_ROL; x86_ROR;
    x86_SAR; x86_SBB_ALT; x86_SET; x86_SHL; x86_SHLD; x86_SHR; x86_SHRD;
    x86_STC; x86_STD; x86_SUB_ALT; x86_TEST; x86_TZCNT; x86_XCHG; x86_XOR;
    (*** AVX2 instructions ***)
    x86_VPADDB_ALT; x86_VPADDD_ALT; x86_VPADDQ_ALT; x86_VPADDW_ALT; x86_VPMULHRSW_ALT; x86_VPMULHUW_ALT; x86_VPMULHW_ALT; x86_VPINSRD; x86_VPINSRQ; x86_VPINSRW; x86_VINSERTI128; x86_VEXTRACTI128;
    x86_VPCMPGTD_ALT; x86_VPCMPGTW_ALT;
    x86_VPEXTRD; x86_VPEXTRQ; x86_VPEXTRW; x86_VPMULLD_ALT; x86_VPMULLW_ALT; x86_VPSUBD_ALT; x86_VPSUBQ_ALT; x86_VPSUBW_ALT; x86_VPXOR;
    x86_VPAND; x86_VPANDN; x86_VPOR; x86_VPSRAD_ALT; x86_VPSRAW_ALT; x86_VPSRLD_ALT; x86_VPSRLDQ_ALT; x86_VPSRLVD_ALT; x86_VPSRLVQ_ALT; x86_VPSRLQ_ALT;
    x86_VPSRLW_ALT; x86_VPBROADCASTD_ALT; x86_VPBROADCASTW_ALT; x86_VPSLLD_ALT; x86_VPSLLVD_ALT; x86_VPSLLQ_ALT; x86_VPSLLW_ALT;
    x86_VMOVDQA_ALT; x86_VMOVDQU_ALT; x86_VPMADDUBSW_ALT; x86_VPMADDWD_ALT; x86_VPMULDQ_ALT; x86_VMOVSHDUP_ALT; x86_VMOVSLDUP_ALT;
    x86_VPACKUSWB_ALT; x86_VPBLENDVB_ALT;
    x86_VPBLENDD_ALT; x86_VPBLENDW_ALT; x86_VPCLMULQDQ_ALT; x86_VPERMD_ALT; x86_VPERMQ_ALT; x86_VPSHUFB_ALT;
    x86_VPUNPCKLQDQ_ALT; x86_VPUNPCKHQDQ_ALT; x86_VPBROADCASTQ_ALT; x86_VPERM2I128_ALT;
    x86_VMOVMSKPS_ALT; x86_VPABSD_ALT; x86_VPMOVMSKB_ALT; x86_VPMOVSXBD_ALT;
    x86_VPMOVZXBD_ALT; x86_VPMOVZXBW_ALT; x86_VPSUBB_ALT; x86_VPTEST_ALT; x86_VZEROUPPER_ALT;
    (*** 32/8-bit backups since the ALT forms are 64-bit only ***)
    INST_TYPE[`:32`,`:N`] x86_ADC;
    INST_TYPE[`:32`,`:N`] x86_ADCX;
    INST_TYPE[`:32`,`:N`] x86_ADOX;
    INST_TYPE[`:32`,`:N`] x86_ADD;
    INST_TYPE[`:32`,`:N`] x86_CMP;
    INST_TYPE[`:8`,`:N`] x86_CMP;
    INST_TYPE[`:32`,`:N`] x86_SBB;
    INST_TYPE[`:32`,`:N`] x86_SUB];;

(* ------------------------------------------------------------------------- *)
(* Trivial reassociation and reduction of "word((pc + m) + n)"               *)
(* ------------------------------------------------------------------------- *)

let WORD_NUM_ASSOC_AND_ADD_CONV =
  GEN_REWRITE_CONV I
   [MESON[ADD_ASSOC] `word((pc + m) + n) = word(pc + m + n)`] THENC
  RAND_CONV(RAND_CONV NUM_ADD_CONV);;

(* ------------------------------------------------------------------------- *)
(* Perform symbolic execution of one instruction to reach named state.       *)
(* ------------------------------------------------------------------------- *)

let X86_THM =
  let pth = prove
   (`read RIP s = word pc ==> x86_decode s (word pc) (n,instr) ==>
     (x86 s s' <=> (RIP := word (pc + n) ,, x86_execute instr) s s')`,
    REPEAT STRIP_TAC THEN REWRITE_TAC [x86] THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_MESON_TAC[PAIR_EQ; x86_decode_unique]) in
  fun (execth2:thm option array) loaded_mc_th pc_th ->
    let th = MATCH_MP pth pc_th in
    let pc_ofs:int =
      let pc_expr = snd (dest_comb (snd (dest_eq (concl pc_th)))) in
      if is_var pc_expr then 0
      else try
        let pc_base,ofs = dest_binary "+" pc_expr in
        dest_small_numeral ofs
      with Failure _ ->
        failwith ("X86_THM: Cannot decompose PC expression: " ^
                  string_of_term (concl pc_th)) in
    let _ = if !x86_print_log then
      let opt = option_get execth2.(pc_ofs) in
      (* opt: |- forall ... bytes_loaded .. ==> x86_decode .. (INST ..) *)
      let t = snd (strip_forall (concl (opt))) in
      let t = snd (dest_imp t) in
      let term = snd (dest_comb t) in
      Printf.printf "Instruction at `pc + %d (%#x)`: `%s`\n" pc_ofs pc_ofs
          (string_of_term term)
    in
    CONV_RULE
      (ONCE_DEPTH_CONV
        (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV))
      (MATCH_MP th (MATCH_MP (option_get execth2.(pc_ofs)) loaded_mc_th));;

let X86_ENSURES_SUBLEMMA_TAC =
  ENSURES_SUBLEMMA_TAC o MATCH_MP bytes_loaded_update o CONJUNCT1;;

let X86_ENSURES_SUBSUBLEMMA_TAC =
  ENSURES_SUBSUBLEMMA_TAC o map (MATCH_MP bytes_loaded_update o CONJUNCT1);;

let X86_UNDEFINED_GEN_TAC =
  (* Globally assign a unique number to the undefined variable.
     If variable names overlap, this can cause a very weird error
     'Exception: Failure "ABS"'.
     Not scanning the assumptions is also beneficial for the speed
     of this tactic. *)
  let undef_n = ref 1 in
  let rec chundef () =
    let v = "undefined_"^string_of_int !undef_n in
    undef_n := 1 + !undef_n;
    v in
  fun (asl,w) ->
    try let ty = snd(dest_var(fst(dest_forall w))) in
        let x' = chundef () in
        X_GEN_TAC (mk_var(x',ty)) (asl,w)
      with Failure _ -> failwith "X86_UNDEFINED_GEN_TAC";;

let X86_UNDEFINED_CHOOSE_TAC =
  GEN_REWRITE_TAC I [LEFT_IMP_EXISTS_THM] THEN X86_UNDEFINED_GEN_TAC;;

(*** This is to force more aggressive use of assumptions and
 *** simplification if we have a conditional indicative of a
 *** possible exception. Currently this only arises in the
 *** division instruction for cases we are verifying and in
 *** if conditions that checks for alignment in
 *** MOVAPS and MOVDQA
 ***)

let X86_FORCE_CONDITIONAL_CONV =
  let trigger t = is_comb t && is_cond(rator t) in
  fun ths ->
     let baseconv =
       GEN_REWRITE_CONV
        (RATOR_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV) ths THENC
       RATOR_CONV(RATOR_CONV(LAND_CONV
         (ONCE_DEPTH_CONV DIMINDEX_CONV))) THENC
       RATOR_CONV(RATOR_CONV(LAND_CONV
         (DEPTH_CONV WORD_NUM_RED_CONV))) THENC
       ALIGNED_WORD_CONV ths THENC
       TRY_CONV (GEN_REWRITE_CONV
        (RATOR_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV) ths) THENC
       TRY_CONV (GEN_REWRITE_CONV RATOR_CONV [COND_CLAUSES]) in
     let chconv t = if trigger t then baseconv t else failwith "baseconv" in
     fun tm -> if trigger tm then (REPEATC chconv THENC TRY_CONV BETA_CONV) tm
               else REFL tm;;

let ASSIGNS_PULL_ZEROTOP_THM = prove
 (`(!P c y. (if P then ASSIGNS (c :> zerotop_32) else c := y) =
            (\s s'. ?d:int32. (c := if P then word_zx d else y) s s')) /\
   (!P c y. (if P then ASSIGNS (c :> zerotop_128) else c := y) =
              (\s s'. ?d:int128. (c := if P then word_zx d else y) s s'))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
  REWRITE_TAC[ASSIGNS; ASSIGN_ZEROTOP_32; ASSIGN_ZEROTOP_128; FUN_EQ_THM] THEN
  MESON_TAC[]);;

(* returns true if t is `read RIP <state>`. *)
let is_read_rip = is_read_named_component "RIP";;

(* For compatibility with is_read_pc in Arm *)
let is_read_pc = is_read_rip;;

(* returns true if t is `read events <state>`. *)
let is_read_events = is_read_named_component "events";;

(*** decode_ths is an array from int offset i to
 ***   Some `|- !s pc. bytes_loaded s pc *_mc
 ***            ==> x86_decode s (word (pc+i)) (..inst..)`
 *** .. if it is a valid byte sequence, or None otherwise.
 ***)

let X86_CONV (decode_ths:thm option array) ths tm =
  (* Find `read RIP .. = ..` from ths (assumptions). *)
  let pc_th = try find
    (fun th ->
      let c = concl th in
      is_eq c && is_read_rip (fst (dest_eq c)))
    ths with Failure _ ->
      failwith "X86_CONV: can't find `read RIP .. = ..` from ths" in

  (* Find `bytes_loaded ..`. *)
  let bytes_loaded_mc_ths:thm list =
    (* Pick the _mc const from decode_ths, if decode_ths[0] != None, which is
       likely to be true. *)
    let the_mc:term option = option_bind decode_ths.(0)
      (fun th ->
        (* th is `forall .., bytes_loaded ... _mc ==> x86_decode ..`. *)
        let t = concl th in
        let bytes_loaded_term = fst (dest_imp (snd (strip_forall t))) in
        let the_mc = last (snd (strip_comb bytes_loaded_term)) in
        (* if _mc contains relocations, the_mc is `.._mc args`. In this
           case, return None. *)
        if is_const the_mc then Some the_mc else None) in
    let bytes_loaded_tm = `bytes_loaded` in
    let res = filter (fun th ->
        let cc = concl th in is_comb cc && (
        let c,args = strip_comb (concl th) in
        c = bytes_loaded_tm &&
          (the_mc = None || last args = option_get the_mc)))
      ths in
    if res = [] then failwith
        ("X86_CONV: can't find `bytes_loaded .. .. " ^
          (if the_mc <> None then string_of_term (option_get the_mc) else "..")
          ^ "` from ths")
    else res in

  let eth = tryfind (fun loaded_mc_th ->
      GEN_REWRITE_CONV I [X86_THM decode_ths loaded_mc_th pc_th] tm)
    bytes_loaded_mc_ths in
  (* Pick the right rules. It will be a singleton in most cases... *)
  let x86_execute_case_rules:thm list =
    let ts = find_terms is_const (concl eth) in
    filter_map (fun t ->
      try Some ((assoc (name_of t) X86_EXECUTE_CASES)) with Failure _ -> None) ts in
  (K eth THENC
   PURE_ONCE_REWRITE_CONV(x86_execute_case_rules) THENC
   REWRITE_CONV[add_store_event;add_load_event;SEQ_ID] THENC
   ONCE_DEPTH_CONV OPERAND_SIZE_CONV THENC
   REWRITE_CONV[condition_semantics; aligned_OPERAND128; aligned_OPERAND256] THENC
   REWRITE_CONV[OPERAND_SIZE_CASES] THENC
   REWRITE_CONV[OPERAND_CLAUSES] THENC
   ONCE_DEPTH_CONV BSID_SEMANTICS_CONV THENC
   REWRITE_CONV X86_OPERATION_CLAUSES THENC
   REWRITE_CONV[READ_RVALUE;
                ASSIGN_ZEROTOP_32; READ_ZEROTOP_32; WRITE_ZEROTOP_32;
                ASSIGN_ZEROTOP_128; READ_ZEROTOP_128; WRITE_ZEROTOP_128;
                READ_BOTTOM_128] THENC
   DEPTH_CONV WORD_NUM_RED_CONV THENC
   REWRITE_CONV[SEQ; condition_semantics] THENC
   REWRITE_CONV[bytesize] THENC (* bytesize in add_{load,store}_event *)
   GEN_REWRITE_CONV TOP_DEPTH_CONV
    [UNDEFINED_VALUE; UNDEFINED_VALUES; SEQ_ID] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV
    [ASSIGNS_PULL_ZEROTOP_THM; ASSIGNS_PULL_THM] THENC
   REWRITE_CONV[ASSIGNS_THM] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [SEQ_PULL_THM; BETA_THM] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV[assign; seq; UNWIND_THM1; BETA_THM] THENC
   TRY_CONV(REWRITE_CONV[WRITE_BOTTOM_128]) THENC
   TRY_CONV(REWRITE_CONV READ_YMM_SSE_EQUIV) THENC
   REWRITE_CONV[] THENC REWRITE_CONV[WRITE_SHORT; READ_SHORT] THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   X86_FORCE_CONDITIONAL_CONV ths THENC
   ONCE_DEPTH_CONV
    (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
     GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
     RAND_CONV NUM_REDUCE_CONV) THENC
   TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
   GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL] THENC
   ONCE_DEPTH_CONV WORD_PC_PLUS_CONV THENC
   DEPTH_CONV WORD_NUM_RED_CONV THENC
   ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV
 ) tm;;

let X86_BASIC_STEP_TAC =
  GEN_BASIC_STEP_TAC "X86" `x86` `:x86state` X86_CONV
    (REPEAT X86_UNDEFINED_CHOOSE_TAC);;

let X86_STEP_TAC (mc_length_th,decode_ths) subths sname
      (store_inst_term_to: term ref option)
      (strip_component_tac: thm_tactic) =
  GEN_STEP_TAC X86_BASIC_STEP_TAC ALL_TAC bytes_loaded_update
    (fun _ _ -> ()) (mc_length_th,decode_ths) subths sname
    store_inst_term_to strip_component_tac;;

let X86_VERBOSE_STEP_TAC =
  GEN_VERBOSE_STEP_TAC X86_STEP_TAC;;

let X86_VERBOSE_SUBSTEP_TAC =
  GEN_VERBOSE_SUBSTEP_TAC X86_STEP_TAC;;

(* ------------------------------------------------------------------------- *)
(* Throw away assumptions according to patterns.                             *)
(* ------------------------------------------------------------------------- *)

let DISCARD_FLAGS_TAC =
  DISCARD_MATCHING_ASSUMPTIONS
   [`read CF s = y`; `read PF s = y`; `read AF s = y`;
    `read ZF s = y`; `read SF s = y`; `read OF s = y`];;

let DISCARD_STATE_TAC =
  GEN_DISCARD_STATE_TAC `:x86state`;;

let DISCARD_OLDSTATE_TAC =
  GEN_DISCARD_OLDSTATE_TAC `:x86state` x86_print_log;;

(* ------------------------------------------------------------------------- *)
(* More convenient stepping tactics, optionally with accumulation.           *)
(* ------------------------------------------------------------------------- *)

let X86_SINGLE_STEP_TAC =
  GEN_SINGLE_STEP_TAC X86_VERBOSE_STEP_TAC DISCARD_OLDSTATE_TAC;;

let X86_VACCSTEP_TAC =
  GEN_VACCSTEP_TAC X86_VERBOSE_STEP_TAC;;

let X86_XACCSTEP_TAC =
  GEN_XACCSTEP_TAC X86_SINGLE_STEP_TAC;;

(* X86_GEN_ACCSTEP_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC. This is
   useful when the output goal of X86_SINGLE_STEP_TAC needs additional rewrites
   for accumulator to recognize it. *)
let X86_GEN_ACCSTEP_TAC =
  GEN_ACCSTEP_TAC X86_SINGLE_STEP_TAC;;

let X86_ACCSTEP_TAC th aflag s = X86_GEN_ACCSTEP_TAC ALL_TAC th aflag s;;

let X86_VSTEPS_TAC =
  GEN_VSTEPS_TAC X86_VERBOSE_STEP_TAC;;

let X86_STEPS_TAC =
  GEN_STEPS_TAC X86_SINGLE_STEP_TAC;;

let X86_VACCSTEPS_TAC =
  GEN_VACCSTEPS_TAC X86_VACCSTEP_TAC;;

let X86_XACCSTEPS_TAC =
  GEN_XACCSTEPS_TAC X86_XACCSTEP_TAC;;

(* X86_GEN_ACCSTEPS_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC.
   acc_preproc is a function from string (which is a state name) to tactic. *)
let X86_GEN_ACCSTEPS_TAC =
  GEN_ACCSTEPS_TAC X86_GEN_ACCSTEP_TAC;;

let X86_ACCSTEPS_TAC th anums snums =
  X86_GEN_ACCSTEPS_TAC (fun _ -> ALL_TAC) th anums snums;;

let X86_QUICKSTEP_TAC th pats =
  let pats' =
   [`nonoverlapping_modulo a b c`; `bytes_loaded a b c`;
    `MAYCHANGE a b c`; `(a ,, b) c d`; `read RIP s = x`] @ pats in
  fun s -> time (X86_VERBOSE_STEP_TAC th s) THEN
           DISCARD_NONMATCHING_ASSUMPTIONS pats' THEN
           DISCARD_OLDSTATE_TAC s THEN
           CLARIFY_TAC;;

let X86_QUICKSTEPS_TAC th pats snums =
  MAP_EVERY (X86_QUICKSTEP_TAC th pats) (statenames "s" snums);;

let X86_QUICKSIM_TAC execth pats snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN X86_QUICKSTEPS_TAC execth pats snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* More convenient wrappings of basic simulation flow.                       *)
(* ------------------------------------------------------------------------- *)

let X86_SIM_TAC ?(preprocess_tac:tactic option) ?(canonicalize_pc_diff=true)
    execth snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  (match preprocess_tac with Some t -> t | None -> ALL_TAC) THEN
  X86_STEPS_TAC execth snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  (if canonicalize_pc_diff then
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[]
   else ALL_TAC);;

let X86_ACCSIM_TAC execth anums snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN X86_ACCSTEPS_TAC execth anums snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Simulate through a lemma in ?- ensures step P Q C ==> eventually R s      *)
(* ------------------------------------------------------------------------- *)

let (X86_BIGSTEP_TAC:(thm*thm option array)->string->tactic) =
  GEN_BIGSTEP_TAC "X86" bytes_loaded_update DISCARD_OLDSTATE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Go from |- bytes_loaded s (word pc) mc or the equivalent                  *)
(*         |- bytes_loaded s (word(pc + 0)) mc                               *)
(* to      |- bytes_loaded s (word(pc + n)) mc'                              *)
(* where mc' is an appropriate sublist of the list mc.                       *)
(* ------------------------------------------------------------------------- *)

let BYTES_LOADED_OFFSET_RULE =
  let pth = prove
   (`bytes_loaded s (word(pc + n)) (CONS h t)
     ==> bytes_loaded s (word(pc + SUC n)) t`,
    ONCE_REWRITE_TAC[GSYM APPEND_SING] THEN
    SIMP_TAC[bytes_loaded_append; LENGTH; GSYM WORD_ADD; ADD_CLAUSES]) in
  let rule1 = CONV_RULE (LAND_CONV(RAND_CONV(RAND_CONV NUM_SUC_CONV))) o
              MATCH_MP pth in
  let rec rule offset th =
    if offset >= 1 then rule (offset - 1) (rule1 th)
    else th in
  fun n th ->
    try rule n (CONV_RULE (TRY_CONV TWEAK_PC_OFFSET_CONV) th)
    with Failure _ -> failwith "BYTES_LOADED_OFFSET_RULE: code too short";;

(* ------------------------------------------------------------------------- *)
(* Prove |- bytes_loaded s wpc mc ==> bytes_loaded s wpc mc' where           *)
(* mc' is a sublist of mc, modulo arithmetic simplifications.                *)
(* ------------------------------------------------------------------------- *)

let BYTES_LOADED_SUBLIST_RULE =
  let prule = (PART_MATCH rand o prove)
   (`(?r. l = APPEND t r)
     ==> bytes_loaded s wpc l ==> bytes_loaded s wpc t`,
    SIMP_TAC[LEFT_IMP_EXISTS_THM; bytes_loaded_append]) in
  fun tm1 tm2 ->
    let th = prule(mk_imp(tm1,tm2)) in
    MP th (BYTELIST_SUBLIST_CONV(lhand(concl th)));;

(* ------------------------------------------------------------------------- *)
(* Given two machine code definitions of the form                            *)
(* |- [forall pc, args1] mc1 pc args1 = [b1; ...; bn]                        *)
(* |- [forall pc, args2] mc2 pc args2 = [b1; ...; bn]                        *)
(* and an offset value, creates a theorem of the form                        *)
(* |- bytes_loaded (word pc) (mc1 pc args1)                                  *)
(*    ==> bytes_loaded (word(pc + offset)) (mc2 s args2)                     *)
(* If the input theorems are not quantified, it's assumed that               *)
(* the left-hand sides are already fully instantiated.                       *)
(* ------------------------------------------------------------------------- *)

let BYTES_LOADED_SUBPROGRAM_RULE =
  let abl_tm = `bytes_loaded s`
  and wpc_tm = `word pc:int64`
  and pc_tm = `pc:num`
  and pcp_tm = `(+) (pc:num)`
  and wd_tm = `word:num->int64`
  and s_tm = `s:x86state` in
  let topvars = [s_tm; pc_tm] in
  fun mc1 mc2 offset ->
    let nptm = mk_comb(pcp_tm,mk_small_numeral offset) in
    let wnptm = mk_comb(wd_tm,nptm) in
    let th1 = if is_forall(concl mc1) then SPEC_ALL(SPEC pc_tm mc1) else mc1
    and th2 =
      if is_forall(concl mc2) then
      SPEC_ALL(SPEC nptm mc2) else mc2 in
    let eth1 = AP_TERM (mk_comb(abl_tm,wpc_tm)) th1
    and eth2 = AP_TERM (mk_comb(abl_tm,wnptm)) th2 in
    let ath1 = UNDISCH(fst(EQ_IMP_RULE eth1)) in
    let oth1 = BYTES_LOADED_OFFSET_RULE offset ath1 in
    let sth =  BYTES_LOADED_SUBLIST_RULE (concl oth1) (rand(concl eth2)) in
    let ith = DISCH_ALL(EQ_MP (SYM eth2) (MP sth oth1)) in
    let avs = subtract (frees(concl ith)) topvars in
    GENL (topvars @ avs) ith;;

(* ------------------------------------------------------------------------- *)
(* Simulate a subroutine, instantiating it from the state.                   *)
(* ------------------------------------------------------------------------- *)

let RIP_PLUS_CONV =
  GEN_REWRITE_CONV I [MESON[ADD_ASSOC]
      `read RIP s = word((pc + m) + n) <=>
       read RIP s = word(pc + m + n)`] THENC
  funpow 3 RAND_CONV NUM_ADD_CONV;;

let X86_SUBROUTINE_SIM_TAC ?(is_safety_thm=false)
    (machinecode,execth,offset,submachinecode,subth) =
  let subimpth =
    try
      BYTES_LOADED_SUBPROGRAM_RULE machinecode submachinecode offset
    with Failure _ ->
      failwith ("X86_SUBROUTINE_SIM_TAC: submachinecode (4th of input tuple) isn't " ^
        "at offset " ^ (string_of_int offset) ^ " of machinecode (1st of tuple)") in
  fun ilist0 n ->
    let sname = "s"^string_of_int(n-1)
    and sname' = "s"^string_of_int n in
    let svar = mk_var(sname,`:x86state`)
    and svar0 = mk_var("s",`:x86state`) in
    let ilist = map (vsubst[svar,svar0]) ilist0 in
    let subth_specl =
      try SPECL ilist subth with Failure _ -> begin
        (if (!x86_print_log) then
          (Printf.printf "ilist and subth's forall vars do not match\n";
           Printf.printf "ilist: [%s]\n" (end_itlist
            (fun s s2 -> s ^ "; " ^ s2) (map string_of_term ilist));
           Printf.printf "subth's forall vars: [%s]\n"
              (end_itlist (fun s s2 -> s ^ "; " ^ s2)
                (map string_of_term (fst (strip_forall (concl subth)))))));
        failwith "X86_SUBROUTINE_SIM_TAC: subth vars don't not match ilist0"
      end in
    MP_TAC(TWEAK_PC_OFFSET subth_specl) THEN
    (* is_forall + SPEC_ALL handles relocatable mcs (e.g. those defined via
       define_assert_relocs_from_elf, which are forall-quantified over
       pc/rodata). *)
    REWRITE_TAC[COMPUTE_LENGTH_RULE
                  (if is_forall(concl submachinecode)
                   then SPEC_ALL submachinecode
                   else submachinecode)] THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REWRITE_TAC[fst execth] THEN
    REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
    (if is_safety_thm then
      (* Turn '(forall e_stack_spill. ..) ==> ...' to
        'exists e_stack_spill. .. ==> ...' *)
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
      META_EXISTS_TAC
      else ALL_TAC) THEN
    (* at this point, there must be no universal quantification at LHS of
        '==>' in conclusion. *)
    (W (fun (_,w) ->
      if is_forall (fst (dest_imp w)) then
        PRINT_GOAL_TAC THEN
        failwith ("Universal quantification still exists at LHS of '==>'. " ^
            "Did you forget to pass ~is_safety_thm:true?")
      else ALL_TAC)) THEN

    TRY(ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      (* Normalize `(pc + n) + m` to `pc + (n+m)` (both num and int forms)
         so that `riprel32_within_bounds`/`(word(pc+n), len)` etc. line up
         with the outer assumptions when the inner subroutine starts at
         a non-zero offset within the outer mc. *)
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ADD_ADD_CONV) THEN
      REPEAT CONJ_TAC THEN
      TRY(CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN NO_TAC) THEN
      TRY(FIRST_X_ASSUM ACCEPT_TAC) THEN
      (NONOVERLAPPING_TAC ORELSE
       DISJ1_TAC THEN NONOVERLAPPING_TAC ORELSE
       DISJ2_TAC THEN NONOVERLAPPING_TAC);
      ALL_TAC]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV RIP_PLUS_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    X86_BIGSTEP_TAC execth sname' THENL
     [(* Precondition of subth *)
      FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP subimpth) ORELSE
      (CONJ_TAC THENL [
          FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP subimpth);
          ALL_TAC]) ORELSE
      (PRINT_GOAL_TAC THEN FAIL_TAC
        "Could not discharge precond (subgoal after X86_BIGSTEP_TAC)");
      ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV));;

let X86_SUBROUTINE_SIM_ABBREV_TAC tupper ilist0 =
  let tac = X86_SUBROUTINE_SIM_TAC tupper ilist0 in
  fun comp0 abn n (asl,w) ->
    let svar0 = mk_var("s",`:x86state`)
    and svar0' = mk_var("s'",`:x86state`)
    and svar = mk_var("s"^string_of_int(n-1),`:x86state`)
    and svar' = mk_var("s"^string_of_int n,`:x86state`) in
    let comp1 =
      rand(concl(PURE_ONCE_REWRITE_CONV (map snd asl)
        (vsubst[svar,svar0;svar',svar0'] comp0))) in
    (tac n THEN
     ABBREV_TAC(mk_eq(mk_var(abn,type_of comp1),comp1))) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Simulate a macro, generating subgoal from a template                      *)
(* ------------------------------------------------------------------------- *)

let X86_MACRO_SIM_ABBREV_TAC =
  let dest_pc tm =
    match tm with
      Comb(Const("word",_),Var("pc",_)) -> 0
    | Comb(Const("word",_),Comb(Comb(Const("+",_),Var("pc",_)),n)) ->
          dest_small_numeral n
    | _ -> failwith "dest_pc"
  and mk_pc =
    let pat0 = `word pc:int64`
    and patn = `word(pc + n):int64`
    and pan = `n:num` in
    fun n ->  if n = 0 then pat0
              else vsubst[mk_small_numeral n,pan] patn
  and grab_dest =
    let pat = `read (memory :> bytes(p,8 * n))` in
    fun th ->
      let cortm = rand(body(lhand(repeat (snd o dest_imp) (concl th)))) in
      hd(find_terms (can (term_match [] pat)) cortm)
  and extract_offsets =
    let rec exfn p acc l =
      match l with
       [] -> rev (p::acc)
      | (n,_)::t -> exfn (p+n) (p::acc) t in
    fun mc -> exfn 0 [] (decode_all(rand(concl mc))) in
  let rec skip_to_offset p offl =
    match offl with
     [] -> failwith "skip_to_offset"
    | (n::t) -> if n > p then failwith "skip_to_offset"
                else if n = p then offl
                else skip_to_offset p t in
  let get_statenpc =
    let fils = can (term_match [] `read RIP s = word n`) o concl o snd in
    fun asl ->
      let rips = concl(snd(find fils asl)) in
      rand(lhand rips),dest_pc(rand rips) in
  let simprule =
    CONV_RULE (ONCE_DEPTH_CONV NORMALIZE_ADD_SUBTRACT_WORD_CONV) o
    GEN_REWRITE_RULE ONCE_DEPTH_CONV
     [WORD_RULE `word_add z (word 0):int64 = z`] in
  fun mc ->
    (* For mcs that contain rodata relocations the bytelist representation
       contains four explicit per-byte CONSes computed from the raw integer
       displacement; collapse them back into `APPEND (bytelist_of_int 4 _) _`
       so that the decode and execution machinery can see the displacement
       as a single 4-byte hole. *)
    let mc = PURE_REWRITE_RULE[BYTELIST_OF_INT_APPEND] mc in
    let offl = extract_offsets mc in
    let execth = X86_MK_EXEC_RULE mc in
    fun codelen localvars template core_tac prep ilist ->
      let main_tac (asl,w) =
        let svp,pc = get_statenpc asl in
        let gv = genvar(type_of svp) in
        let n = int_of_string(implode(tl(explode(fst(dest_var svp))))) + 1 in
        let svn = mk_var("s"^string_of_int n,`:x86state`) in
        let pc' = hd(snd(chop_list codelen (skip_to_offset pc offl))) in
        let svs = svp::(mk_pc pc)::(mk_pc pc')::
                  end_itlist (@) (map (C assoc localvars) ilist) in
        let rawsg = simprule(SPECL svs (ASSUME template)) in
        let asimprule = PURE_REWRITE_RULE
         (filter (is_eq o concl) (map snd asl)) in
        let insig = (asimprule o simprule o asimprule) rawsg in
        let subg = mk_forall(gv,vsubst[gv,svp] (concl(simprule insig))) in
        let avoids = itlist (union o thm_frees o snd) asl (frees w) in
        let abv = mk_primed_var avoids (mk_var(hd ilist,`:num`)) in
        (SUBGOAL_THEN subg MP_TAC THENL
         [X_GEN_TAC gv THEN POP_ASSUM_LIST(K ALL_TAC) THEN
          REPEAT(GEN_TAC THEN DISCH_THEN(K ALL_TAC o SYM)) THEN
          core_tac THEN NO_TAC;
          ALL_TAC] THEN
         DISCH_THEN(MP_TAC o SPEC svp) THEN
         GEN_REWRITE_TAC (REPEATC o LAND_CONV) [FORALL_UNWIND_THM1] THEN
         DISCH_THEN(fun subth ->
          let dest = grab_dest subth in
          X86_SUBROUTINE_SIM_TAC(mc,execth,0,mc,subth) [] n THEN
          ABBREV_TAC (mk_eq(abv,mk_comb(dest,svn)))))
        (asl,w) in
     fun (asl,w) ->
        let sv,_ = get_statenpc asl in
        let n = int_of_string(implode(tl(explode(fst(dest_var sv))))) in
        (X86_STEPS_TAC execth ((n+1)--(n+prep)) THEN main_tac) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Fix up call/return boilerplate given core correctness.                    *)
(* ------------------------------------------------------------------------- *)

(* The stack pointer and return address loaded from the caller stack are
   recovered from initial-state equations during ABI promotion. Require their
   names to be explicit outer quantifiers before the tactic reorders them. *)
let check_forallvars_tac:tactic =
  GEN_CHECK_FORALLVARS_TAC
    [`read RSP s`; `read (memory :> bytes64 stackpointer) s`];;

let X86_ADD_RETURN_NOSTACK_TAC =
  let lemma1 = prove
   (`ensures step P Q R /\
     (!s s'. P s /\ Q s' /\ R s s' ==> Q' s')
     ==> ensures step P (\s. Q s /\ Q' s) R`,
    ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
    REWRITE_TAC[SUBSUMED_REFL] THEN ASM_MESON_TAC[]) in
  let lemma2 = prove
   (`C' subsumed C /\
     C ,, C = C /\
     (!s s'. progdata s /\ pcdata s /\ stackdata s /\ retdata s /\ P s /\
             Q s' /\ C' s s'
             ==> progdata s' /\ stackdata s' /\ retdata s') /\
     ensures step (\s. progdata s /\ stackdata s /\ retdata s /\ Q s) R C
     ==> ensures step (\s. progdata s /\ pcdata s /\ P s) Q C'
          ==> ensures step
               (\s. progdata s /\ pcdata s /\ stackdata s /\ retdata s /\ P s)
               R C`,
    ONCE_REWRITE_TAC[TAUT
     `a /\ b /\ p /\ q ==> r ==> s <=> a ==> b ==> p ==> r ==> q ==> s`] THEN
    DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE
     [TAUT `p /\ q /\ r ==> s <=> p /\ q ==> r ==> s`]
     ENSURES_TRANS_SIMPLE) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          ENSURES_FRAME_SUBSUMED)) THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
     [TAUT `p /\ q /\ r /\ s <=> s /\ p /\ q /\ r`] THEN
    MATCH_MP_TAC lemma1 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          ENSURES_PRECONDITION_THM)) THEN
    SIMP_TAC[]) in
  fun execth coreth ->
    let coreth =
      REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
      coreth in
    let is_coreth_safety = is_exists (concl coreth) in

    (* is_coreth_safety must hold iff the current goalstate is
       `exists ...`. *)
    (fun (asl,w) ->
      if is_coreth_safety <> (is_exists w) then
        failwith "coreth must be `exists ..` iff the conclusion is"
      else ALL_TAC (asl,w)) THEN

    REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    (* If coreth was a safety property, coreth is `exists f_events. ...`. *)
    (if is_coreth_safety then
      ASSUME_CALLEE_SAFETY_TAC coreth "" THEN
      (* f_events of the current goal will have additional args, compared to
         f_events of coreth: returnaddress and stackpointer. This will be
         filled in later. *)
      META_EXISTS_TAC THEN
      check_forallvars_tac THEN
      FIRST_X_ASSUM MP_TAC
     else
      (* th is functional correctness *) MP_TAC coreth) THEN

    REWRITE_TAC[fst execth] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    MATCH_MP_TAC lemma2 THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MAYCHANGE_IDEMPOT_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      (* Strip all clauses of conjunctions in the LHS of ==> other than the
         last MAYCHANGE predicate *)
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ASSIGNS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      NONSELFMODIFYING_STATE_UPDATE_TAC
       (MATCH_MP bytes_loaded_update (fst execth)) THEN
      ASSUMPTION_STATE_UPDATE_TAC THEN
      DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check
       (can (term_match [] `read PC s = a \/ Q` o concl)))) THEN
      (* Break 'exists e2. ...' for safety proofs *)
      REPEAT(STRIP_EXISTS_ASSUM_TAC) THEN
      X86_STEPS_TAC execth [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Version with register save/restore and stack adjustment.                  *)
(* ------------------------------------------------------------------------- *)

(* Useful lemmas *)
let swap_forall = prove
   (`(forall (e_stack_spill:A) (y:B). P e_stack_spill y) <=>
     (forall y e_stack_spill. P e_stack_spill y)`,
    MESON_TAC[SWAP_FORALL_THM]) and
  swap_forall3 = prove
   (`(forall (e_stack_spill:A) (y:B) (z:C). P e_stack_spill y z) <=>
     (forall y e_stack_spill z. P e_stack_spill y z)`,
    MESON_TAC[SUBROUTINE_SWAP_FORALL3]) and
  append_lemma = prove
   (`(forall (e:(A)list). P e) <=>
     (forall e_stack_spill e. P (APPEND e_stack_spill e))`,
    MESON_TAC[SUBROUTINE_APPEND_FORALL]) and
  mono2lemma = prove
   (`(!(x:A). (!(y:B). P x y) ==> (!(z:C). Q x z))
     ==> (!x y. P x y) ==> (!x z. Q x z)`,
    MESON_TAC[SUBROUTINE_MONO_FORALL2]) and
  mono3lemma = prove
   (`(!(x:A). (!(y:B) (y':C). P x y y') ==>
      (!(z:D) (z':E). Q x z z'))
     ==> (!x y y'. P x y y') ==> (!x z z'. Q x z z')`,
    MESON_TAC[SUBROUTINE_MONO_FORALL3]);;


let GEN_X86_ADD_RETURN_STACK_TAC =
  fun execth coreth reglist stackoff (n,m) ->
    let regs = dest_list reglist in
    (* If coreth was a safety property, coreth is `exists f_events. ...`. *)
    let is_coreth_safety = is_exists (concl coreth) in

    (* is_coreth_safety must hold iff the current goalstate is
       `exists ...`. *)
    (fun (asl,w) ->
      if is_coreth_safety <> (is_exists w) then
        failwith "coreth must be `exists ..` iff the conclusion is"
      else ALL_TAC (asl,w)) THEN

    (if is_coreth_safety then
      ASSUME_CALLEE_SAFETY_TAC coreth "" THEN
      (* f_events of the current goal will have additional args, compared to
         f_events of coreth: returnaddress and stackpointer. This will be
         filled in later. *)
      META_EXISTS_TAC THEN
      check_forallvars_tac THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (ONCE_REWRITE_RULE[append_lemma]th)) THEN
      (* push e_stack_spill to the innermost var of forall *)
      REPEAT(CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall])) THEN
             MATCH_MP_TAC mono3lemma THEN GEN_TAC) THEN
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall]))
     else
      (* th is functional correctness *)
      check_forallvars_tac THEN
      MP_TAC coreth THEN
      REPEAT(MATCH_MP_TAC mono2lemma THEN GEN_TAC)) THEN

    REWRITE_TAC[fst execth] THEN
    REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                 WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    (if vfree_in `RSP` (concl coreth) then
      DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
     else
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(fun th ->
        WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    (if is_coreth_safety then
      (* Finally turn '(forall e_stack_spill. ..) ==> ...' to
         'exists e_stack_spill. .. ==> ...' *)
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
      META_EXISTS_TAC
     else
      ALL_TAC) THEN
    (* If coreth has remaining assumptions to discharge
       (usually nonoverlapping conditions), prove them *)
    W(fun (asl,w) ->
      let coreth_stmt,_ = dest_imp w in
      if is_imp coreth_stmt then
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC THEN
          (* All assumptions must have been discharged at this point *)
          (PRINT_GOAL_TAC THEN
          FAIL_TAC "Could not discharge assumptions of coreth");
          ALL_TAC]
      else ALL_TAC) THEN
    DISCH_THEN(fun th ->
      MAP_EVERY (fun c -> ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
                regs THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC execth (1--n) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC execth ("s"^string_of_int(n+1)) THEN
    (* X86_BIGSTEP_TAC may leave an additional subgoal about precondition.
       If the precondition is about event trace, solve here. *)
    (if is_coreth_safety then
     TRY (CONV_TAC (LAND_CONV CONS_TO_APPEND_CONV) THEN
         BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN
         NO_TAC)
     else ALL_TAC) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    X86_STEPS_TAC execth ((n+2)--(m+n+1)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let X86_ADD_RETURN_STACK_TAC execth coreth reglist stackoff =
  let n0 = length(dest_list reglist) in
  let n = if 8 * n0 = stackoff then n0 else n0 + 1 in
  GEN_X86_ADD_RETURN_STACK_TAC execth coreth reglist stackoff (n,n+1);;

(* ------------------------------------------------------------------------- *)
(* Additional tools for refined "bytes_loaded ... (BUTLAST l)" variants.     *)
(* ------------------------------------------------------------------------- *)

let X86_TRIM_EXEC_RULE =
  let trimth = AP_TERM `BUTLAST:byte list->byte list`
  and pushr = GEN_REWRITE_RULE (RAND_CONV o TOP_SWEEP_CONV)
               [BUTLAST_CLAUSES] in
  pushr o trimth;;

let X86_MK_CORE_EXEC_RULE = X86_MK_EXEC_RULE o X86_TRIM_EXEC_RULE;;

let X86_CORE_PROMOTE =
  let lemma = prove
   (`(ensures x86 (\s. bytes_loaded s (word pc) (BUTLAST l) /\ P s) Q C
      ==> ensures x86 (\s. bytes_loaded s (word pc) l /\ P s) Q C) /\
     ((A ==> ensures x86 (\s. bytes_loaded s (word pc) (BUTLAST l) /\ P s) Q C)
      ==> A ==> ensures x86 (\s. bytes_loaded s (word pc) l /\ P s) Q C)`,
    MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN
    CONJ_TAC THENL [CONV_TAC TAUT; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
    GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC MONO_AND THEN
    REWRITE_TAC[BYTES_LOADED_BUTLAST]) in
  let rule1 = MATCH_MP(CONJUNCT1 lemma)
  and rule2 = MATCH_MP(CONJUNCT2 lemma) in
  fun th ->
    (* If th is a functional correctness property *)
    if is_forall (concl th) then
      let avs,bod = strip_forall(concl th) in
      let sth = SPECL avs th in
      let gth = try rule2 sth with Failure _ -> rule1 sth in
      GENL avs gth
    else
      if not (is_exists (concl th))
      then failwith ("X86_CORE_PROMOTE: th is neither forall " ^
          "(functional correctness) nor exists (safety property)") else
      (* th is a safety property *)
      let the_goal = concl th in
      let ex_var,body = dest_exists the_goal in (* ex_var is f_events *)
      let univ_vars,body = strip_forall body in
      let new_body:term =
        concl (try rule2 (ASSUME body) with Failure _ -> rule1 (ASSUME body)) in
      let new_goal = mk_exists (ex_var, list_mk_forall (univ_vars,new_body)) in
      prove(new_goal,
        MP_TAC th THEN STRIP_TAC THEN
        (* exists f_events ... *)
        EXISTS_TAC ex_var THEN
        (* unify all forall x.. *)
        FIRST_X_ASSUM MP_TAC THEN
        REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
        STRIP_TAC THEN
        (* The interesting part *)
        ((MATCH_MP_TAC (CONJUNCT2 lemma)) ORELSE
         (MATCH_MP_TAC (CONJUNCT1 lemma))) THEN FIRST_X_ASSUM ACCEPT_TAC);;


let X86_PROMOTE_RETURN_NOSTACK_TAC mc core =
  X86_ADD_RETURN_NOSTACK_TAC (X86_MK_EXEC_RULE mc) (X86_CORE_PROMOTE core);;

let X86_PROMOTE_RETURN_STACK_TAC mc core regs off =
  X86_ADD_RETURN_STACK_TAC
    (X86_MK_EXEC_RULE mc) (X86_CORE_PROMOTE core) regs off;;

(* ------------------------------------------------------------------------- *)
(* Wrap up function for the Windows ABI                                      *)
(* ------------------------------------------------------------------------- *)

let WINDOWS_ABI_STACK_THM = prove
 (`(read RSP s = stackpointer /\ P /\
    WINDOWS_C_ARGUMENTS [a1; a2; a3; a4; a5] s /\ Q <=>
    read RSP s = stackpointer /\ P /\
    (WINDOWS_C_ARGUMENTS [a1; a2; a3; a4] s /\
     read (memory :> bytes64 (word_add stackpointer (word 40))) s = a5) /\
    Q) /\
   (read RSP s = stackpointer /\ P /\
    WINDOWS_C_ARGUMENTS [a1; a2; a3; a4; a5; a6] s /\ Q <=>
    read RSP s = stackpointer /\ P /\
    (WINDOWS_C_ARGUMENTS [a1; a2; a3; a4] s /\
     read (memory :> bytes64 (word_add stackpointer (word 40))) s = a5 /\
     read (memory :> bytes64 (word_add stackpointer (word 48))) s = a6) /\
    Q) /\
   (read RSP s = stackpointer /\ P /\
    WINDOWS_C_ARGUMENTS [a1; a2; a3; a4; a5] s <=>
    read RSP s = stackpointer /\ P /\
    (WINDOWS_C_ARGUMENTS [a1; a2; a3; a4] s /\
     read (memory :> bytes64 (word_add stackpointer (word 40))) s = a5)) /\
   (read RSP s = stackpointer /\ P /\
    WINDOWS_C_ARGUMENTS [a1; a2; a3; a4; a5; a6] s <=>
    read RSP s = stackpointer /\ P /\
    (WINDOWS_C_ARGUMENTS [a1; a2; a3; a4] s /\
     read (memory :> bytes64 (word_add stackpointer (word 40))) s = a5 /\
     read (memory :> bytes64 (word_add stackpointer (word 48))) s = a6))`,
  REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN MESON_TAC[]);;

let WINDOWS_X86_WRAP_NOSTACK_TAC =
  let pcofflemma = MESON[]
    `!n:num. (!x. P(x + n) ==> Q x) ==> (!x. P x) ==> (!x. Q x)`
  and pcplusplus_conv =
    GEN_REWRITE_CONV I
     [MESON[ADD_ASSOC] `word((pc + m) + n) = word(pc + m + n)`] THENC
    RAND_CONV(RAND_CONV NUM_ADD_CONV)
  and count_args =
    let argy = `WINDOWS_C_ARGUMENTS` in
    let is_nargle t = is_comb t && rator t = argy in
    length o dest_list o rand o find_term is_nargle in
  fun winmc stdmc coreth (asl,w) ->
    let nargs = count_args w in
    let prolog_len = 2 + nargs
    and epilog_len = 3
    and stackoff = 16
    and pcoff = match nargs with
      1 -> 5 | 2 -> 8 | 3 -> 11 | 4 -> 14 | 5 -> 19 | 6 -> 24 | _ -> 0 in
    let interstate = "s"^string_of_int(prolog_len+1)
    and subimpth =
      CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE [LENGTH]
        (MATCH_MP bytes_loaded_of_append3
          (TRANS winmc (N_SUBLIST_CONV
             (SPEC_ALL (X86_TRIM_EXEC_RULE stdmc)) pcoff
             (rhs(concl winmc))))))
    and winexecth = X86_MK_EXEC_RULE winmc in
    (* If coreth was a safety property, coreth is `exists f_events. ...`. *)
    let is_coreth_safety = is_exists (concl coreth) in
    let coreth = REWRITE_RULE
      [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] coreth in
    (* If coreth was a safety property, coreth is `exists f_events. ...`. *)
    let is_coreth_safety = is_exists (concl coreth) in
    (* is_coreth_safety must hold iff the current goalstate is
       `exists ...`. *)
    let check_safety_match_tac:tactic =
      fun (asl,w) ->
        if is_coreth_safety <> (is_exists w) then
          failwith "coreth must be `exists ..` iff the conclusion is"
        else ALL_TAC (asl,w) in

   (check_safety_match_tac THEN
    REWRITE_TAC [WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    PURE_REWRITE_TAC[WINDOWS_ABI_STACK_THM] THEN
    (if is_coreth_safety then
      ASSUME_CALLEE_SAFETY_TAC coreth "" THEN
      (* f_events of the current goal will have additional args, compared to
         f_events of coreth: returnaddress and stackpointer. This will be
         filled in later. *)
      META_EXISTS_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (ONCE_REWRITE_RULE[append_lemma]th)) THEN
      (* push e_stack_spill to the innermost var of forall *)
      REPEAT(CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall])) THEN
             MATCH_MP_TAC mono3lemma THEN GEN_TAC) THEN
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall]))
     else
      (* th is functional correctness *) MP_TAC coreth THEN
      REPEAT(MATCH_MP_TAC mono2lemma THEN GEN_TAC)) THEN

    REWRITE_TAC[fst winexecth] THEN
    MATCH_MP_TAC pcofflemma THEN
    EXISTS_TAC (mk_small_numeral pcoff) THEN GEN_TAC THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV pcplusplus_conv)) THEN
    DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
        REPEAT GEN_TAC THEN
        TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
        MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    (if is_coreth_safety then
      (* Finally turn '(forall e_stack_spill. ..) ==> ...' to
         'exists e_stack_spill. .. ==> ...' *)
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
      META_EXISTS_TAC
     else
      ALL_TAC) THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
        ENSURES_PRESERVED_TAC "init_rsi" `RSI` THEN
        ENSURES_PRESERVED_TAC "init_rdi" `RDI` THEN
        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC winexecth (1--prolog_len) THEN
        MP_TAC th) THEN
    X86_BIGSTEP_TAC winexecth interstate THENL
     [(if is_coreth_safety then
        CONJ_TAC THENL [ALL_TAC;
          TRY (CONV_TAC (LAND_CONV CONS_TO_APPEND_CONV) THEN
            BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN
            NO_TAC)]
        else ALL_TAC) THEN
      MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC winexecth ((prolog_len+2)--(prolog_len+epilog_len+1)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) (asl,w);;

let WINDOWS_X86_WRAP_STACK_TAC =
  let monopsrlemma = MESON[]
     `(!x. P x ==> !p s r. Q x p s r)
      ==> (!x. P x) ==> (!x p s r. Q x p s r)`
  and pcofflemma = MESON[]
    `!n:num. (!x. P(x + n) ==> Q x) ==> (!x. P x) ==> (!x. Q x)`
  and pcplusplus_conv =
    GEN_REWRITE_CONV I
     [MESON[ADD_ASSOC] `word((pc + m) + n) = word(pc + m + n)`] THENC
    RAND_CONV(RAND_CONV NUM_ADD_CONV)
  and count_args =
    let argy = `WINDOWS_C_ARGUMENTS` in
    let is_nargle t = is_comb t && rator t = argy in
    fun t -> try
        (length o dest_list o rand o find_term is_nargle) t
      with Failure _ -> failwith "Could not find WINDOWS_C_ARGUMENTS" in
  fun winmc stdmc coreth reglist stdstackoff (asl,w) ->
    let stdregs = dest_list reglist in
    let n =
      let n0 = length stdregs in if 8 * n0 = stdstackoff then n0 else n0 + 1 in
    let regs = [`RSI`; `RDI`] @ stdregs
    and stackoff = stdstackoff + 16 in
    let nargs = count_args w in
    let prolog_len = 2 + nargs + n
    and epilog_len = 3 + n in
    let pcoff =  match nargs with
      1 -> 5 | 2 -> 8 | 3 -> 11 | 4 -> 14 | 5 -> 19 | 6 -> 24 | _ -> 0 in
    let interstate = "s"^string_of_int(prolog_len+1)
    and subimpth =
      CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE [LENGTH]
        (MATCH_MP bytes_loaded_of_append3
          (TRANS winmc (N_SUBLIST_CONV
             (SPEC_ALL (X86_TRIM_EXEC_RULE stdmc)) pcoff
             (rhs(concl winmc))))))
    and winexecth = X86_MK_EXEC_RULE winmc in
    (* If coreth was a safety property, coreth is `exists f_events. ...`. *)
    let is_coreth_safety = is_exists (concl coreth) in
    (* is_coreth_safety must hold iff the current goalstate is
       `exists ...`. *)
    let check_safety_match_tac:tactic =
      fun (asl,w) ->
        if is_coreth_safety <> (is_exists w) then
          failwith "coreth must be `exists ..` iff the conclusion is"
        else ALL_TAC (asl,w) in

   (check_safety_match_tac THEN
    REWRITE_TAC [WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    PURE_REWRITE_TAC[WINDOWS_ABI_STACK_THM] THEN
    (* If coreth was a safety property, coreth is `exists f_events. ...`. *)
    (if is_coreth_safety then
      ASSUME_CALLEE_SAFETY_TAC coreth "" THEN
      (* f_events of the current goal will have additional args, compared to
         f_events of coreth: returnaddress and stackpointer. This will be
         filled in later. *)
      META_EXISTS_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (ONCE_REWRITE_RULE[append_lemma]th)) THEN
      (* push e_stack_spill to the innermost var of forall *)
      REPEAT(CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall])) THEN
             MATCH_MP_TAC monopsrlemma THEN GEN_TAC) THEN
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall]))
     else
      (* th is functional correctness *) MP_TAC coreth THEN
      REPEAT(MATCH_MP_TAC monopsrlemma THEN GEN_TAC)) THEN

    REWRITE_TAC[fst winexecth] THEN
    MATCH_MP_TAC pcofflemma THEN
    EXISTS_TAC (mk_small_numeral pcoff) THEN GEN_TAC THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV pcplusplus_conv)) THEN
    (if vfree_in `RSP` (concl coreth) then
      (if is_coreth_safety then
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall]))
      else ALL_TAC) THEN
     DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
     MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
    else
     DISCH_THEN(fun th ->
       WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
        REPEAT GEN_TAC THEN
        TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
        MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    (if is_coreth_safety then
      (* Finally turn '(forall e_stack_spill. ..) ==> ...' to
         'exists e_stack_spill. .. ==> ...' *)
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
      META_EXISTS_TAC
     else
      ALL_TAC) THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
     DISCH_THEN(fun th ->
      MAP_EVERY (fun c ->
                    ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
                regs THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC winexecth (1--prolog_len) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC winexecth interstate THENL
     [(if is_coreth_safety then
        CONJ_TAC THENL [ALL_TAC;
          TRY (CONV_TAC (LAND_CONV CONS_TO_APPEND_CONV) THEN
            BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN
            NO_TAC)]
        else ALL_TAC) THEN
      MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC winexecth ((prolog_len+2)--(prolog_len+epilog_len+1)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Generalize MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI where the            *)
(* standard ABI form is used as a Windows subroutine, basically by repeating *)
(* the standard subroutine wrapper process on a modified version.            *)
(* This is useful where the core subroutine does not use SIMD registers      *)
(* since MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI doesn't imply that.       *)
(* ------------------------------------------------------------------------- *)

let X86_SIMD_SHARPEN_RULE =
  let subfn = subst
   [`MAYCHANGE [RIP] ,,
     MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
     MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events]`,
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`] in
  fun stdthm tac ->
    let stdthm' = subfn(concl stdthm) in prove(stdthm',tac);;

(* ------------------------------------------------------------------------- *)
(* Tweak a standard correctness theorem to use the version with an           *)
(* initial ENDBR64 before the same code, assuming they are defined           *)
(* together in the standard way.                                             *)
(* ------------------------------------------------------------------------- *)

let IBT_WRAP_THM = prove
 (`R ,, R = R /\ MAYCHANGE [RIP] subsumed R /\
   (!s y. P(write RIP y s) <=> P s) /\
   ensures x86
    (\s. bytes_loaded s (word (pc + 4)) mc /\
         read RIP s = word (pc + 4) /\
         P s) Q R
   ==> ensures x86
        (\s. bytes_loaded s (word pc)
               (APPEND [word 0xf3; word 0x0f; word 0x1e; word 0xfa] mc) /\
             read RIP s = word pc /\
             P s) Q R`,
  let execlen =
    REWRITE_CONV[LENGTH_APPEND; LENGTH; ARITH]
     `LENGTH(APPEND [word 0xf3:byte; word 0x0f; word 0x1e; word 0xfa] mc)`
  and execstart = prove
   (`!s pc. bytes_loaded s (word pc)
                    (APPEND [word 0xf3; word 0x0f; word 0x1e; word 0xfa] mc)
            ==> x86_decode s (word pc) (4,ENDBR64)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[bytes_loaded_append] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    let Some th = (snd(X86_MK_EXEC_RULE
     (REFL `[word 243; word 15; word 30; word 250]:byte list`))).(0) in
    REWRITE_TAC[th]) in
  let execth = (execlen,[|Some execstart; None; None; None|]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `(MAYCHANGE [RIP] ,, R):x86state->x86state->bool` THEN
  ASM_SIMP_TAC[SUBSUMED_FOR_SEQ; SUBSUMED_REFL] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN
  EXISTS_TAC `\s. bytes_loaded s (word (pc + 4)) mc /\
                  read RIP s = word (pc + 4) /\
                  P s` THEN
  ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[bytes_loaded_append]) THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN REWRITE_TAC[WORD_ADD];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE
        (RATOR_CONV o RATOR_CONV) [MAYCHANGE_SING]) THEN
    REWRITE_TAC[ASSIGNS; assign] THEN ASM_MESON_TAC[]]);;

(* Shared bits between the unparametrized and parametrized variants of
   ADD_IBT_TAC. *)

(* If the goal is `exists f_events. ..`, instantiate f_events using the
   f_events in `th_noexists`, replacing pc with `pc + 4`. *)
let WITNESS_F_EVENTS_TAC (th_noexists:thm): tactic =
  W (fun (asl,w) ->
    if not (is_exists w) then ALL_TAC else
    let f_events_term = find_term (fun t ->
      is_comb t && name_of(fst(strip_comb t)) = "f_events")
      (concl th_noexists) in
    let f_events,args = strip_comb f_events_term in
    let new_argdecls,new_args = unzip (map (fun t ->
      if is_var t && name_of t = "pc" then (t,mk_binary "+" (t,`4`))
      else let newvar = genvar(type_of t) in (newvar,newvar)) args) in
    let new_f_events = list_mk_abs
      (new_argdecls,list_mk_comb(f_events,new_args)) in
    EXISTS_TAC new_f_events);;

(* Strip a leading `exists f_events.` from `th` (yielding `th_noexists`),
   correspondingly instantiate the goal's `exists`, and run [k th_noexists]
   on the resulting body. For functional-correctness theorems (no leading
   `exists`), [k th] runs directly. *)
let ADD_IBT_OPEN_EXISTS th (k:thm->tactic): tactic =
  if is_exists (concl th) then
    MP_TAC th THEN STRIP_TAC THEN
    FIRST_X_ASSUM (fun th_noexists ->
      WITNESS_F_EVENTS_TAC th_noexists THEN k th_noexists)
  else
    k th;;

(* The four IBT_WRAP_THM subgoals shared by both variants. The fourth
   subgoal (discharging the inner `ensures ... at pc+4`) differs: the
   unparametrized version uses MAP_EVERY X_GEN_TAC + MP_TAC SPECL inline,
   while the parametrized version takes a tactic argument. *)
let IBT_WRAP_TAC (discharge_inner:tactic): tactic =
  MATCH_MP_TAC IBT_WRAP_THM THEN REPEAT CONJ_TAC THENL [
    (* (1) MAYCHANGE R is idempotent. *)
    MAYCHANGE_IDEMPOT_TAC;
    (* (2) MAYCHANGE [RIP] is subsumed by R. *)
    SUBSUMED_MAYCHANGE_TAC;
    (* (3) writing RIP doesn't affect the precondition components. *)
    REPEAT GEN_TAC THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN;
                WINDOWS_C_ARGUMENTS; bytes_loaded] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REFL_TAC;
    (* (4) caller-supplied: discharge `ensures ... at pc+4`. *)
    discharge_inner
  ];;

let ADD_IBT_TAC =
  let tweak = subst[`pc + 4`,`pc:num`]
  and EXPAND_TRIMMED_RULE =
    let pth = prove
     (`CONS (a:byte) (CONS b (CONS c (CONS d l))) = APPEND [a;b;c;d] l`,
      REWRITE_TAC[APPEND]) in
    fun fullmc trimc ->
     GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [GSYM trimc]
     (GEN_REWRITE_RULE RAND_CONV [pth] fullmc) in
  fun fullmc trimc th ->
    let expth = EXPAND_TRIMMED_RULE fullmc trimc in
    ADD_IBT_OPEN_EXISTS th (fun th_inner ->
      MP_TAC th_inner THEN
      DISCH_THEN (fun th -> W(fun (asl,w) ->
        let avs = fst(strip_forall w) in
        MAP_EVERY X_GEN_TAC avs THEN
        MP_TAC(SPECL (map tweak avs) th))) THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN
      REWRITE_TAC[C_ARGUMENTS; C_RETURN;
                  MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                  WINDOWS_C_ARGUMENTS; ALL; ALLPAIRS;
                  WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      TRY(MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
       [REPEAT(REWRITE_TAC[] THEN
               ((MATCH_MP_TAC MONO_AND THEN CONJ_TAC) ORELSE
                (MATCH_MP_TAC MONO_OR THEN CONJ_TAC))) THEN
        REWRITE_TAC[expth; LENGTH; ARITH; LENGTH_APPEND] THEN
        REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
        MATCH_MP_TAC(ONCE_REWRITE_RULE [IMP_CONJ_ALT]
          NONOVERLAPPING_MODULO_SUBREGIONS) THEN
        REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL] THEN
        MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN ARITH_TAC;
        ALL_TAC]) THEN
      DISCH_TAC THEN REWRITE_TAC[expth; GSYM APPEND_ASSOC] THEN
      IBT_WRAP_TAC
        (FIRST_X_ASSUM ACCEPT_TAC ORELSE
         ((* When the goal contains LENGTH .._mc and LENGTH .._tmc . *)
          FIRST_X_ASSUM MP_TAC THEN
          REWRITE_TAC[LENGTH_APPEND] THEN
          CONV_TAC (ONCE_DEPTH_CONV LENGTH_CONV) THEN
          ASM_REWRITE_TAC[ADD_ASSOC] THEN NO_TAC)));;

(* Tactic for the parametrized case: directly apply IBT_WRAP_THM after
   rewriting with the user-supplied bridge thm
     `forall args. mc args = APPEND [endbr64] (tmc (pc+4) <rest>)`,
   then discharge the resulting `ensures ... at pc+4` using the input NOIBT
   theorem instantiated with `pc -> pc+4`.

   For safety theorems (`exists f_events. forall ...`), the goal also has
   `exists f_events.` at the head; ADD_IBT_OPEN_EXISTS takes care of that. *)
let ADD_IBT_TAC_PARAMETRIZED bridge_th th =
  ADD_IBT_OPEN_EXISTS th (fun th_inner ->
    REPEAT GEN_TAC THEN REWRITE_TAC[bridge_th] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS;
                C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
                WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT STRIP_TAC THEN
    IBT_WRAP_TAC
      (W (fun (asl,w) ->
        let avs,_ = strip_forall (concl th_inner) in
        let new_avs = map (fun v ->
          if is_var v && name_of v = "pc" then mk_binary "+" (v,`4`)
          else v) avs in
        MP_TAC (REWRITE_RULE[C_ARGUMENTS; C_RETURN; WINDOWS_C_ARGUMENTS;
                              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                              SOME_FLAGS]
                (SPECL new_avs th_inner))) THEN
       CONV_TAC(ONCE_DEPTH_CONV
         (REWR_CONV(ARITH_RULE `(pc + 4) + n:num = pc + (n + 4)`) THENC
          RAND_CONV NUM_ADD_CONV)) THEN
       REWRITE_TAC[
         WORD_RULE `word(pc+4):int64 = word_add (word pc) (word 4)`] THEN
       DISCH_THEN MATCH_MP_TAC THEN
       POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
       REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
       REPEAT CONJ_TAC THEN
       TRY (FIRST_X_ASSUM ACCEPT_TAC) THEN
       NONOVERLAPPING_TAC));;

(* For unparametrized (constant) mcs, ADD_IBT_RULE infers everything from
   the definitions. For parametrized mcs (e.g. `mc pc tables` produced by
   define_assert_relocs_from_elf + define_trimmed), the caller must supply
   the bridge equation
     `forall args. mc args = APPEND [endbr64] (tmc (pc+4) <rest>)`
   via the optional `~bridge` argument. *)
let ADD_IBT_RULE ?(bridge:thm option = None) th =
  let the_concl = concl th in
  (* If th is safety property, it starts with `exists f_events. ...` *)
  let the_concl = if is_exists the_concl then
    snd (dest_exists the_concl) else the_concl in
  let bldat =
   rand(lhand(body(lhand(rator
    (repeat (snd o dest_imp) (snd(strip_forall(the_concl)))))))) in
  (* The mc inside bytes_loaded can take three forms:
       (a) a bare constant `tmc` (legacy non-rodata, no inline data),
       (b) `APPEND tmc data` (legacy non-rodata with inline data section),
       (c) `tmc pc tables` from define_assert_relocs_from_elf (rodata-aware).
     Only (c) is "parametrized" w.r.t. ADD_IBT_RULE — for (a) and (b) the
     trimmed mc constant can be looked up directly in the_definitions. *)
  let parametrized =
    if is_const bldat then false
    else if is_comb bldat &&
            is_const (fst (strip_comb bldat)) &&
            name_of (fst (strip_comb bldat)) = "APPEND" then
      false  (* legacy `APPEND tmc data` form *)
    else true in
  match bridge, parametrized with
  | None, true ->
    (* Parametrized mc with no bridge: we cannot derive the bridge from the
       definitions alone (define_trimmed re-quantifies and shifts pc), so ask
       the caller to provide it. *)
    let trim_head_const = fst (strip_comb bldat) in
    failwith ("ADD_IBT_RULE: input theorem uses parametrized mc " ^
              name_of trim_head_const ^
              "; please supply ~bridge:thm of shape " ^
              "`forall args. mc args = APPEND [endbr64] (tmc (pc+4) <rest>)`")
  | None, false ->
    (* Legacy non-rodata path: tmc was defined as `tmc = TRIM_LIST(4,0) mc`,
       and bldat is either `tmc` (case a) or `APPEND tmc data` (case b). *)
    let trimctm = if is_const bldat then bldat else lhand bldat in
    let trimcd = find ((=) trimctm o lhand o concl) (definitions()) in
    let fullmctm = rand(rand(concl trimcd)) in
    let fullmc = find ((=) fullmctm o lhand o concl) (definitions()) in
    let trimc =
      CONV_RULE (RAND_CONV TRIM_LIST_CONV)
       (GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [fullmc] trimcd) in
    let rec adjust tm =
      match tm with
        Comb(Comb(Const(",",_),Comb(Const("word",_),Var("pc",_))) as rat,off)
            when is_numeral off ->
          mk_comb(rat,mk_numeral(num 4 +/ dest_numeral off))
      | Comb(s,t) -> mk_comb(adjust s,adjust t)
      | Abs(x,t) -> mk_abs(x,adjust t)
      | _ -> if tm = trimctm then fullmctm else tm in
    prove(adjust (concl th), ADD_IBT_TAC fullmc trimc th)
  | Some bridge_th, _ ->
    (* Parametrized path: read mc/tmc head constants from the bridge, sanity-
       check the tmc head matches the input theorem, then bump every numeric
       offset (`pc + n` and `(word pc, n)`) by 4 to form the IBT goal and
       discharge it via ADD_IBT_TAC_PARAMETRIZED. *)
    if not parametrized then
      failwith "ADD_IBT_RULE: bridge supplied but mc is not parametrized" else
    let trim_head_const = fst (strip_comb bldat) in
    let bridge_eq = SPEC_ALL bridge_th in
    let mc_app = lhand (concl bridge_eq) in
    let trimcall = rand (rand (concl bridge_eq)) in
    let fullmctm = fst (strip_comb mc_app) in
    let bridge_trimctm = fst (strip_comb trimcall) in
    if bridge_trimctm <> trim_head_const then
      failwith ("ADD_IBT_RULE: bridge thm's trimmed mc " ^
                name_of bridge_trimctm ^ " does not match input theorem's mc "
                ^ name_of trim_head_const)
    else
    let rec adjust tm =
      match tm with
      | Comb(Comb(Const(",",_),Comb(Const("word",_),Var("pc",_))) as rat,off)
          when is_numeral off ->
          mk_comb(rat,mk_numeral(num 4 +/ dest_numeral off))
      | Comb(Comb(Const("+",_),Var("pc",_)) as p,off)
          when is_numeral off ->
          mk_comb(p,mk_numeral(num 4 +/ dest_numeral off))
      | Comb(s,t) -> mk_comb(adjust s,adjust t)
      | Abs(x,t) -> mk_abs(x,adjust t)
      | _ -> if tm = trim_head_const then fullmctm else tm in
    prove(adjust (concl th), ADD_IBT_TAC_PARAMETRIZED bridge_th th);;

let READ_ZMM_BOTTOM_QUARTER = prove
 (`!zmmx:(S,512 word)component s.
     read (zmmx :> bottomhalf :> bottomhalf) s = word_zx (read zmmx s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bottomhalf; READ_SUBWORD] THEN
  REWRITE_TAC[DIMINDEX_512; DIMINDEX_256; DIMINDEX_128] THEN
  CONV_TAC WORD_BLAST);;

let READ_ZMM_BOTTOM_QUARTER' = prove
 (`!zmmx:(S,512 word)component s.
     read (zmmx :> bottomhalf :> bottomhalf) s =
     word_zx (read (zmmx :> zerotop_256) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bottomhalf; READ_SUBWORD;
              READ_ZEROTOP_256] THEN
  REWRITE_TAC[DIMINDEX_512; DIMINDEX_256; DIMINDEX_128] THEN
  CONV_TAC WORD_BLAST);;

let MAYCHANGE_ZMM_QUARTER = prove
 (`MAYCHANGE [ZMM6] =
   MAYCHANGE [ZMM6 :> tophalf] ,,
   MAYCHANGE [ZMM6 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM6 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [ZMM7] =
   MAYCHANGE [ZMM7 :> tophalf] ,,
   MAYCHANGE [ZMM7 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM7 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM8] =
   MAYCHANGE [ZMM8 :> tophalf] ,,
   MAYCHANGE [ZMM8 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM8 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM9] =
   MAYCHANGE [ZMM9 :> tophalf] ,,
   MAYCHANGE [ZMM9 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM9 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM10] =
   MAYCHANGE [ZMM10 :> tophalf] ,,
   MAYCHANGE [ZMM10 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM10 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM11] =
   MAYCHANGE [ZMM11 :> tophalf] ,,
   MAYCHANGE [ZMM11 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM11 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM12] =
   MAYCHANGE [ZMM12 :> tophalf] ,,
   MAYCHANGE [ZMM12 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM12 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM13] =
   MAYCHANGE [ZMM13 :> tophalf] ,,
   MAYCHANGE [ZMM13 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM13 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM14] =
   MAYCHANGE [ZMM14 :> tophalf] ,,
   MAYCHANGE [ZMM14 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM14 :> bottomhalf :> bottomhalf] /\
  MAYCHANGE [ZMM15] =
   MAYCHANGE [ZMM15 :> tophalf] ,,
   MAYCHANGE [ZMM15 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM15 :> bottomhalf :> bottomhalf]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_SING] THEN
  (W(MP_TAC o PART_MATCH (rand o rand) ASSIGNS_TOPHALF_BOTTOMHALF o
    lhand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV ; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) ASSIGNS_TOPHALF_BOTTOMHALF o
    lhand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV ; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC]));;

let MAYCHANGE_YMM_SSE_QUARTER = prove
 (`MAYCHANGE [YMM6_SSE] =
   MAYCHANGE [ZMM6 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM6 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM7_SSE] =
   MAYCHANGE [ZMM7 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM7 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM8_SSE] =
   MAYCHANGE [ZMM8 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM8 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM9_SSE] =
   MAYCHANGE [ZMM9 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM9 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM10_SSE] =
   MAYCHANGE [ZMM10 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM10 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM11_SSE] =
   MAYCHANGE [ZMM11 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM11 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM12_SSE] =
   MAYCHANGE [ZMM12 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM12 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM13_SSE] =
   MAYCHANGE [ZMM13 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM13 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM14_SSE] =
   MAYCHANGE [ZMM14 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM14 :> bottomhalf :> bottomhalf] /\
   MAYCHANGE [YMM15_SSE] =
   MAYCHANGE [ZMM15 :> bottomhalf :> tophalf] ,,
   MAYCHANGE [ZMM15 :> bottomhalf :> bottomhalf]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bottom_256; YMM6_SSE; YMM7_SSE; YMM8_SSE; YMM9_SSE;
    YMM10_SSE; YMM11_SSE; YMM12_SSE; YMM13_SSE;
    YMM14_SSE; YMM15_SSE] THEN
  CONV_TAC SYM_CONV THEN
  REWRITE_TAC[MAYCHANGE_SING; COMPONENT_COMPOSE_ASSOC] THEN
  MATCH_MP_TAC ASSIGNS_TOPHALF_BOTTOMHALF THEN
  CONV_TAC VALID_COMPONENT_CONV);;
