(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Simplified definition of x86 assembly instructions.                       *)
(* ========================================================================= *)

let wordsize_INDUCT,wordsize_RECURSION = define_type
 "wordsize = Word512 | Word256 | Word128 |
             Quadword | Doubleword | Word | Byte";;

(* ------------------------------------------------------------------------- *)
(* The general-purpose registers                                             *)
(* ------------------------------------------------------------------------- *)

let regsize_INDUCT,regsize_RECURSION = define_type
 "regsize = Full_64 | Lower_32 | Lower_16 | Upper_8 | Lower_8";;

(*** There are some not actually addressable ones here ***)
(*** But it keeps things uniform to use this pattern   ***)

let gpr_INDUCT,gpr_RECURSION = define_type
 "gpr = Gpr (4 word) regsize";;

let rax = define `rax = Gpr (word  0) Full_64`
and rcx = define `rcx = Gpr (word  1) Full_64`
and rdx = define `rdx = Gpr (word  2) Full_64`
and rbx = define `rbx = Gpr (word  3) Full_64`
and rsp = define `rsp = Gpr (word  4) Full_64`
and rbp = define `rbp = Gpr (word  5) Full_64`
and rsi = define `rsi = Gpr (word  6) Full_64`
and rdi = define `rdi = Gpr (word  7) Full_64`
and  r8 = define ` r8 = Gpr (word  8) Full_64`
and  r9 = define ` r9 = Gpr (word  9) Full_64`
and r10 = define `r10 = Gpr (word 10) Full_64`
and r11 = define `r11 = Gpr (word 11) Full_64`
and r12 = define `r12 = Gpr (word 12) Full_64`
and r13 = define `r13 = Gpr (word 13) Full_64`
and r14 = define `r14 = Gpr (word 14) Full_64`
and r15 = define `r15 = Gpr (word 15) Full_64`;;

let  eax = define ` eax = Gpr (word 0) Lower_32`
and  ecx = define ` ecx = Gpr (word 1) Lower_32`
and  edx = define ` edx = Gpr (word 2) Lower_32`
and  ebx = define ` ebx = Gpr (word 3) Lower_32`
and  esp = define ` esp = Gpr (word 4) Lower_32`
and  ebp = define ` ebp = Gpr (word 5) Lower_32`
and  esi = define ` esi = Gpr (word 6) Lower_32`
and  edi = define ` edi = Gpr (word 7) Lower_32`
and  r8d = define ` r8d = Gpr (word  8) Lower_32`
and  r9d = define ` r9d = Gpr (word  9) Lower_32`
and r10d = define `r10d = Gpr (word 10) Lower_32`
and r11d = define `r11d = Gpr (word 11) Lower_32`
and r12d = define `r12d = Gpr (word 12) Lower_32`
and r13d = define `r13d = Gpr (word 13) Lower_32`
and r14d = define `r14d = Gpr (word 14) Lower_32`
and r15d = define `r15d = Gpr (word 15) Lower_32`

and ax = define `ax = Gpr (word 0) Lower_16`
and cx = define `cx = Gpr (word 1) Lower_16`
and dx = define `dx = Gpr (word 2) Lower_16`
and bx = define `bx = Gpr (word 3) Lower_16`
and sp = define `sp = Gpr (word 4) Lower_16`
and bp = define `bp = Gpr (word 5) Lower_16`
and si = define `si = Gpr (word 6) Lower_16`
and di = define `di = Gpr (word 7) Lower_16`
and  r8w = define ` r8w = Gpr (word  8) Lower_16`
and  r9w = define ` r9w = Gpr (word  9) Lower_16`
and r10w = define `r10w = Gpr (word 10) Lower_16`
and r11w = define `r11w = Gpr (word 11) Lower_16`
and r12w = define `r12w = Gpr (word 12) Lower_16`
and r13w = define `r13w = Gpr (word 13) Lower_16`
and r14w = define `r14w = Gpr (word 14) Lower_16`
and r15w = define `r15w = Gpr (word 15) Lower_16`;;

let ah = define `ah = Gpr (word 0) Upper_8`
and al = define `al = Gpr (word 0) Lower_8`
and ch = define `ch = Gpr (word 1) Upper_8`
and cl = define `cl = Gpr (word 1) Lower_8`
and dh = define `dh = Gpr (word 2) Upper_8`
and dl = define `dl = Gpr (word 2) Lower_8`
and bh = define `bh = Gpr (word 3) Upper_8`
and bl = define `bl = Gpr (word 3) Lower_8`
and spl = define `spl = Gpr (word 4) Lower_8`
and bpl = define `bpl = Gpr (word 5) Lower_8`
and sil = define `sil = Gpr (word 6) Lower_8`
and dil = define `dil = Gpr (word 7) Lower_8`
and r8b  = define ` r8b = Gpr (word  8) Lower_8`
and r9b  = define ` r9b = Gpr (word  9) Lower_8`
and r10b = define `r10b = Gpr (word 10) Lower_8`
and r11b = define `r11b = Gpr (word 11) Lower_8`
and r12b = define `r12b = Gpr (word 12) Lower_8`
and r13b = define `r13b = Gpr (word 13) Lower_8`
and r14b = define `r14b = Gpr (word 14) Lower_8`
and r15b = define `r15b = Gpr (word 15) Lower_8`;;

(* ------------------------------------------------------------------------- *)
(* XMM/YMM/ZMM registers and opmask registers.                               *)
(* ------------------------------------------------------------------------- *)

let simdregsize_INDUCT,simdregsize_RECURSION = define_type
 "simdregsize = Full_512 | Lower_256 | Lower_128";;

(*** Again xmm / ymm aren't addressable for 16..31, but this is uniform ***)

let simdreg_INDUCT,simdreg_RECURSION = define_type
 "simdreg = Simdreg (5 word) simdregsize";;

let xmm0  = define `xmm0  = Simdreg (word 0) Lower_128`
and xmm1  = define `xmm1  = Simdreg (word 1) Lower_128`
and xmm2  = define `xmm2  = Simdreg (word 2) Lower_128`
and xmm3  = define `xmm3  = Simdreg (word 3) Lower_128`
and xmm4  = define `xmm4  = Simdreg (word 4) Lower_128`
and xmm5  = define `xmm5  = Simdreg (word 5) Lower_128`
and xmm6  = define `xmm6  = Simdreg (word 6) Lower_128`
and xmm7  = define `xmm7  = Simdreg (word 7) Lower_128`
and xmm8  = define `xmm8  = Simdreg (word 8) Lower_128`
and xmm9  = define `xmm9  = Simdreg (word 9) Lower_128`
and xmm10 = define `xmm10 = Simdreg (word 10) Lower_128`
and xmm11 = define `xmm11 = Simdreg (word 11) Lower_128`
and xmm12 = define `xmm12 = Simdreg (word 12) Lower_128`
and xmm13 = define `xmm13 = Simdreg (word 13) Lower_128`
and xmm14 = define `xmm14 = Simdreg (word 14) Lower_128`
and xmm15 = define `xmm15 = Simdreg (word 15) Lower_128`;;

let ymm0  = define `ymm0  = Simdreg (word 0) Lower_256`
and ymm1  = define `ymm1  = Simdreg (word 1) Lower_256`
and ymm2  = define `ymm2  = Simdreg (word 2) Lower_256`
and ymm3  = define `ymm3  = Simdreg (word 3) Lower_256`
and ymm4  = define `ymm4  = Simdreg (word 4) Lower_256`
and ymm5  = define `ymm5  = Simdreg (word 5) Lower_256`
and ymm6  = define `ymm6  = Simdreg (word 6) Lower_256`
and ymm7  = define `ymm7  = Simdreg (word 7) Lower_256`
and ymm8  = define `ymm8  = Simdreg (word 8) Lower_256`
and ymm9  = define `ymm9  = Simdreg (word 9) Lower_256`
and ymm10 = define `ymm10 = Simdreg (word 10) Lower_256`
and ymm11 = define `ymm11 = Simdreg (word 11) Lower_256`
and ymm12 = define `ymm12 = Simdreg (word 12) Lower_256`
and ymm13 = define `ymm13 = Simdreg (word 13) Lower_256`
and ymm14 = define `ymm14 = Simdreg (word 14) Lower_256`
and ymm15 = define `ymm15 = Simdreg (word 15) Lower_256`;;

let zmm0  = define `zmm0  = Simdreg (word 0) Full_512`
and zmm1  = define `zmm1  = Simdreg (word 1) Full_512`
and zmm2  = define `zmm2  = Simdreg (word 2) Full_512`
and zmm3  = define `zmm3  = Simdreg (word 3) Full_512`
and zmm4  = define `zmm4  = Simdreg (word 4) Full_512`
and zmm5  = define `zmm5  = Simdreg (word 5) Full_512`
and zmm6  = define `zmm6  = Simdreg (word 6) Full_512`
and zmm7  = define `zmm7  = Simdreg (word 7) Full_512`
and zmm8  = define `zmm8  = Simdreg (word 8) Full_512`
and zmm9  = define `zmm9  = Simdreg (word 9) Full_512`
and zmm10 = define `zmm10 = Simdreg (word 10) Full_512`
and zmm11 = define `zmm11 = Simdreg (word 11) Full_512`
and zmm12 = define `zmm12 = Simdreg (word 12) Full_512`
and zmm13 = define `zmm13 = Simdreg (word 13) Full_512`
and zmm14 = define `zmm14 = Simdreg (word 14) Full_512`
and zmm15 = define `zmm15 = Simdreg (word 15) Full_512`
and zmm16 = define `zmm16 = Simdreg (word 16) Full_512`
and zmm17 = define `zmm17 = Simdreg (word 17) Full_512`
and zmm18 = define `zmm18 = Simdreg (word 18) Full_512`
and zmm19 = define `zmm19 = Simdreg (word 19) Full_512`
and zmm20 = define `zmm20 = Simdreg (word 20) Full_512`
and zmm21 = define `zmm21 = Simdreg (word 21) Full_512`
and zmm22 = define `zmm22 = Simdreg (word 22) Full_512`
and zmm23 = define `zmm23 = Simdreg (word 23) Full_512`
and zmm24 = define `zmm24 = Simdreg (word 24) Full_512`
and zmm25 = define `zmm25 = Simdreg (word 25) Full_512`
and zmm26 = define `zmm26 = Simdreg (word 26) Full_512`
and zmm27 = define `zmm27 = Simdreg (word 27) Full_512`
and zmm28 = define `zmm28 = Simdreg (word 28) Full_512`
and zmm29 = define `zmm29 = Simdreg (word 29) Full_512`
and zmm30 = define `zmm30 = Simdreg (word 30) Full_512`
and zmm31 = define `zmm31 = Simdreg (word 31) Full_512`;;

let opmaskreg_INDUCT,opmaskreg_RECURSION = define_type
 "opmaskreg = Opmaskreg (3 word)";;

let kmask0 = define `kmask0 = Opmaskreg (word 0)`;;
let kmask1 = define `kmask1 = Opmaskreg (word 1)`;;
let kmask2 = define `kmask2 = Opmaskreg (word 2)`;;
let kmask3 = define `kmask3 = Opmaskreg (word 3)`;;
let kmask4 = define `kmask4 = Opmaskreg (word 4)`;;
let kmask5 = define `kmask5 = Opmaskreg (word 5)`;;
let kmask6 = define `kmask6 = Opmaskreg (word 6)`;;
let kmask7 = define `kmask7 = Opmaskreg (word 7)`;;

(* ------------------------------------------------------------------------- *)
(* Condition codes for conditional operations.                               *)
(* ------------------------------------------------------------------------- *)

(*** We leave out Condition_CXZ and Condition_ECXZ for now ***)

let condition_INDUCTION,condition_RECURSION = define_type
   "condition =
      Unconditional
    | Condition_B               // JB, JNAE, JC
    | Condition_BE              // JBE, JNA
    | Condition_L               // JL, JNGE
    | Condition_LE              // JLE, JNG
    | Condition_NB              // JNB, JAE, JNC
    | Condition_NBE             // JA, JNBE
    | Condition_NL              // JGE, JNL
    | Condition_NLE             // JG, JNLE
    | Condition_NO              // JNO
    | Condition_NP              // JNP, JPO
    | Condition_NS              // JNS
    | Condition_NZ              // JNE, JNZ
    | Condition_O               // JO
    | Condition_P               // JP, JPE
    | Condition_S               // JS
    | Condition_Z               // JE, JZ
   ";;

(* ------------------------------------------------------------------------- *)
(* The basic BSID is base + index<<scale + displacement.                     *)
(* We also allow RIP-relative addressing, using a separate constructor.      *)
(* In all cases the displacement is a 64-bit word; the shorter ones actually *)
(* in the various encodings can be sign-extended.                            *)
(* ------------------------------------------------------------------------- *)

let bsid_INDUCTION,bsid_RECURSION = define_type
 "bsid = Bsid (gpr option) (gpr option) (2 word) (64 word)
       | Riprel (64 word)";;

(* ------------------------------------------------------------------------- *)
(* Operands.                                                                 *)
(* ------------------------------------------------------------------------- *)

let operand_INDUCTION,operand_RECURSION = define_type
 "operand =
    Register gpr
  | Simdregister simdreg
  | Imm8 (8 word)
  | Imm16 (16 word)
  | Imm32 (32 word)
  | Imm64 (64 word)
  | Memop wordsize bsid";;

(* ------------------------------------------------------------------------- *)
(* Instructions.                                                             *)
(* ------------------------------------------------------------------------- *)

(*** We call "STC" "STCF" to avoid clashing with symmetric closure of relation
 *** The "DIV" have numeric suffixes anyway to express implicit operands.
 ***)

let instruction_INDUCTION,instruction_RECURSION = define_type
 "instruction =
     ADC operand operand
   | ADCX operand operand
   | ADD operand operand
   | ADOX operand operand
   | AESDEC operand operand
   | AESDECLAST operand operand
   | AESENC operand operand
   | AESENCLAST operand operand
   | AESKEYGENASSIST operand operand operand
   | AND operand operand
   | BSF operand operand
   | BSR operand operand
   | BSWAP operand
   | BT operand operand
   | BTC operand operand
   | BTR operand operand
   | BTS operand operand
   | CALL operand
   | CALL_ABSOLUTE (64 word)
   | CLC
   | CLD
   | CMC
   | CMOV condition operand operand
   | CMP operand operand
   | DEC operand
   | ENDBR64
   | IMUL3 operand (operand#operand)
   | IMUL2 (operand#operand) operand
   | INC operand
   | JUMP condition operand
   | LEA operand bsid
   | LZCNT operand operand
   | MOV operand operand
   | MOVD operand operand
   | MOVQ operand operand
   | MOVSB bool operand operand operand
   | MOVSX operand operand
   | MOVZX operand operand
   | MOVAPS operand operand
   | MOVDQA operand operand
   | MOVDQU operand operand
   | MOVUPS operand operand
   | MUL2 (operand#operand) operand
   | MULX4 (operand#operand) (operand#operand)
   | NEG operand
   | NOP
   | NOP_N operand
   | NOT operand
   | OR operand operand
   | PADDD operand operand
   | PADDQ operand operand
   | PAND operand operand
   | PBLENDW operand operand operand
   | PCMPGTD operand operand
   | PCMPGTW operand operand
   | PEXT operand operand operand
   | PINSRD operand operand operand
   | PINSRQ operand operand operand
   | PMOVMSKB operand operand
   | POP operand
   | POPCNT operand operand
   | PSHUFB operand operand
   | PSHUFD operand operand operand
   | PSRAD operand operand
   | PSRLW operand operand
   | PUSH operand
   | PXOR operand operand
   | RCL operand operand
   | RCR operand operand
   | RET
   | ROL operand operand
   | ROR operand operand
   | SAR operand operand
   | SBB operand operand
   | SET condition operand
   | SHL operand operand
   | SHR operand operand
   | SHLD operand operand operand
   | SHRD operand operand operand
   | STCF
   | STD
   | SUB operand operand
   | TEST operand operand
   | TZCNT operand operand
   | VMOVD operand operand
   | VMOVMSKPS operand operand
   | VMOVQ operand operand
   | VMOVDQA operand operand
   | VMOVDQU operand operand
   | VMOVHPD operand operand
   | VMOVSHDUP operand operand
   | VMOVSLDUP operand operand
   | VPADDB operand operand operand
   | VPADDW operand operand operand
   | VPADDD operand operand operand
   | VPADDQ operand operand operand
   | VPAND operand operand operand
   | VPANDN operand operand operand
   | VPBLENDD operand operand operand operand
   | VPBLENDW operand operand operand operand
   | VPCLMULQDQ operand operand operand operand
   | VPBROADCASTD operand operand
   | VPBROADCASTQ operand operand
   | VPBROADCASTW operand operand
   | VPERMD operand operand operand
   | VPERMQ operand operand operand
   | VPERM2I128 operand operand operand operand
   | VPEXTRD operand operand operand
   | VPEXTRQ operand operand operand
   | VPEXTRW operand operand operand
   | VPINSRD operand operand operand operand
   | VPINSRQ operand operand operand operand
   | VPINSRW operand operand operand operand
   | VEXTRACTI128 operand operand operand
   | VINSERTI128 operand operand operand operand
   | VPABSD operand operand
   | VPACKUSWB operand operand operand
   | VPCMPGTD operand operand operand
   | VPCMPGTW operand operand operand
   | VPBLENDVB operand operand operand operand
   | VPMADDUBSW operand operand operand
   | VPMADDWD operand operand operand
   | VPMOVMSKB operand operand
   | VPMOVSXBD operand operand
   | VPMOVZXBD operand operand
   | VPMOVZXBW operand operand
   | VPMULDQ operand operand operand
   | VPMULHRSW operand operand operand
   | VPMULHUW operand operand operand
   | VPMULHW operand operand operand
   | VPMULLD operand operand operand
   | VPMULLW operand operand operand
   | VPOR operand operand operand
   | VPSHUFB operand operand operand
   | VPSLLD operand operand operand
   | VPSLLVD operand operand operand
   | VPSLLQ operand operand operand
   | VPSLLW operand operand operand
   | VPSRAD operand operand operand
   | VPSRAW operand operand operand
   | VPSRLD operand operand operand
   | VPSRLDQ operand operand operand
   | VPSRLVD operand operand operand
   | VPSRLVQ operand operand operand
   | VPSRLQ operand operand operand
   | VPSRLW operand operand operand
   | VPSUBB operand operand operand
   | VPSUBD operand operand operand
   | VPSUBQ operand operand operand
   | VPSUBW operand operand operand
   | VPTEST operand operand
   | VPUNPCKHQDQ operand operand operand
   | VPUNPCKLQDQ operand operand operand
   | VPXOR operand operand operand
   | VZEROUPPER
   | XCHG operand operand
   | XOR operand operand";;

(* ------------------------------------------------------------------------- *)
(* Some shorthands for addressing modes etc.                                 *)
(* ------------------------------------------------------------------------- *)

override_interface("%",`Register`);;
override_interface("%_%",`Simdregister`);;

let  base_displacement = define
  `%%(r,d) = Bsid (SOME r) NONE (word 0) (word d)`

and base_scaled_index = define
 `%%%(r,s,i) = Bsid (SOME r) (SOME i) (word s) (word 0)`

and base_scaled_index_displacement = define
 `%%%%(r,s,i,d) = Bsid (SOME r) (SOME i) (word s) (iword d)`

and simple_immediate = define
 `## n = Imm32(word n)`;;

let QWORD = define
 `QWORD = Memop Quadword`;;

(* ------------------------------------------------------------------------- *)
(* Instruction shorthands specific to my setup                               *)
(* ------------------------------------------------------------------------- *)

let IMUL = new_definition `IMUL dest src = IMUL3 dest (dest,src)`;;

(* ------------------------------------------------------------------------- *)
(* Standard opcodes for conditional combinations (not unique, i.e. there are *)
(* often multiple ways of getting the same instruction).                     *)
(* ------------------------------------------------------------------------- *)

let CMOVB = define `CMOVB = CMOV Condition_B`;;

let CMOVNAE = define `CMOVNAE = CMOV Condition_B`;;

let CMOVC = define `CMOVC = CMOV Condition_B`;;

let CMOVBE = define `CMOVBE = CMOV Condition_BE`;;

let CMOVNA = define `CMOVNA = CMOV Condition_BE`;;

let CMOVL = define `CMOVL = CMOV Condition_L`;;

let CMOVNGE = define `CMOVNGE = CMOV Condition_L`;;

let CMOVLE = define `CMOVLE = CMOV Condition_LE`;;

let CMOVNG = define `CMOVNG = CMOV Condition_LE`;;

let CMOVNB = define `CMOVNB = CMOV Condition_NB`;;

let CMOVAE = define `CMOVAE = CMOV Condition_NB`;;

let CMOVNC = define `CMOVNC = CMOV Condition_NB`;;

let CMOVA = define `CMOVA = CMOV Condition_NBE`;;

let CMOVNBE = define `CMOVNBE = CMOV Condition_NBE`;;

let CMOVGE = define `CMOVGE = CMOV Condition_NL`;;

let CMOVNL = define `CMOVNL = CMOV Condition_NL`;;

let CMOVG = define `CMOVG = CMOV Condition_NLE`;;

let CMOVNLE = define `CMOVNLE = CMOV Condition_NLE`;;

let CMOVNO = define `CMOVNO = CMOV Condition_NO`;;

let CMOVNP = define `CMOVNP = CMOV Condition_NP`;;

let CMOVPO = define `CMOVPO = CMOV Condition_NP`;;

let CMOVNS = define `CMOVNS = CMOV Condition_NS`;;

let CMOVNE = define `CMOVNE = CMOV Condition_NZ`;;

let CMOVNZ = define `CMOVNZ = CMOV Condition_NZ`;;

let CMOVO = define `CMOVO = CMOV Condition_O`;;

let CMOVP = define `CMOVP = CMOV Condition_P`;;

let CMOVPE = define `CMOVPE = CMOV Condition_P`;;

let CMOVS = define `CMOVS = CMOV Condition_S`;;

let CMOVE = define `CMOVE = CMOV Condition_Z`;;

let CMOVZ = define `CMOVZ = CMOV Condition_Z`;;

let JMP = define `JMP = JUMP Unconditional`;;

let JB = define `JB = JUMP Condition_B`;;

let JNAE = define `JNAE = JUMP Condition_B`;;

let JC = define `JC = JUMP Condition_B`;;

let JBE = define `JBE = JUMP Condition_BE`;;

let JNA = define `JNA = JUMP Condition_BE`;;

let JL = define `JL = JUMP Condition_L`;;

let JNGE = define `JNGE = JUMP Condition_L`;;

let JLE = define `JLE = JUMP Condition_LE`;;

let JNG = define `JNG = JUMP Condition_LE`;;

let JNB = define `JNB = JUMP Condition_NB`;;

let JAE = define `JAE = JUMP Condition_NB`;;

let JNC = define `JNC = JUMP Condition_NB`;;

let JA = define `JA = JUMP Condition_NBE`;;

let JNBE = define `JNBE = JUMP Condition_NBE`;;

let JGE = define `JGE = JUMP Condition_NL`;;

let JNL = define `JNL = JUMP Condition_NL`;;

let JG = define `JG = JUMP Condition_NLE`;;

let JNLE = define `JNLE = JUMP Condition_NLE`;;

let JNO = define `JNO = JUMP Condition_NO`;;

let JNP = define `JNP = JUMP Condition_NP`;;

let JPO = define `JPO = JUMP Condition_NP`;;

let JNS = define `JNS = JUMP Condition_NS`;;

let JNE = define `JNE = JUMP Condition_NZ`;;

let JNZ = define `JNZ = JUMP Condition_NZ`;;

let JO = define `JO = JUMP Condition_O`;;

let JP = define `JP = JUMP Condition_P`;;

let JPE = define `JPE = JUMP Condition_P`;;

let JS = define `JS = JUMP Condition_S`;;

let JE = define `JE = JUMP Condition_Z`;;

let JZ = define `JZ = JUMP Condition_Z`;;

let SETB = define `SETB = SET Condition_B`;;

let SETNAE = define `SETNAE = SET Condition_B`;;

let SETC = define `SETC = SET Condition_B`;;

let SETBE = define `SETBE = SET Condition_BE`;;

let SETNA = define `SETNA = SET Condition_BE`;;

let SETL = define `SETL = SET Condition_L`;;

let SETNGE = define `SETNGE = SET Condition_L`;;

let SETLE = define `SETLE = SET Condition_LE`;;

let SETNG = define `SETNG = SET Condition_LE`;;

let SETNB = define `SETNB = SET Condition_NB`;;

let SETAE = define `SETAE = SET Condition_NB`;;

let SETNC = define `SETNC = SET Condition_NB`;;

let SETA = define `SETA = SET Condition_NBE`;;

let SETNBE = define `SETNBE = SET Condition_NBE`;;

let SETGE = define `SETGE = SET Condition_NL`;;

let SETNL = define `SETNL = SET Condition_NL`;;

let SETG = define `SETG = SET Condition_NLE`;;

let SETNLE = define `SETNLE = SET Condition_NLE`;;

let SETNO = define `SETNO = SET Condition_NO`;;

let SETNP = define `SETNP = SET Condition_NP`;;

let SETPO = define `SETPO = SET Condition_NP`;;

let SETNS = define `SETNS = SET Condition_NS`;;

let SETNE = define `SETNE = SET Condition_NZ`;;

let SETNZ = define `SETNZ = SET Condition_NZ`;;

let SETO = define `SETO = SET Condition_O`;;

let SETP = define `SETP = SET Condition_P`;;

let SETPE = define `SETPE = SET Condition_P`;;

let SETS = define `SETS = SET Condition_S`;;

let SETE = define `SETE = SET Condition_Z`;;

let SETZ = define `SETZ = SET Condition_Z`;;

let X86_INSTRUCTION_ALIASES =
 [CMOVB; CMOVNAE; CMOVC; CMOVBE; CMOVNA; CMOVL; CMOVNGE;
  CMOVLE; CMOVNG; CMOVNB; CMOVAE; CMOVNC; CMOVA; CMOVNBE;
  CMOVGE; CMOVNL; CMOVG; CMOVNLE; CMOVNO; CMOVNP; CMOVPO;
  CMOVNS; CMOVNE; CMOVNZ; CMOVO; CMOVP; CMOVPE; CMOVS; CMOVE;
  CMOVZ; JMP; JB; JNAE; JC; JBE; JNA; JL; JNGE; JLE; JNG;
  JNB; JAE; JNC; JA; JNBE; JGE; JNL; JG; JNLE; JNO; JNP; JPO;
  JNS; JNE; JNZ; JO; JP; JPE; JS; JE; JZ; SETB; SETNAE; SETC;
  SETBE; SETNA; SETL; SETNGE; SETLE; SETNG; SETNB; SETAE; SETNC;
  SETA; SETNBE; SETGE; SETNL; SETG; SETNLE; SETNO; SETNP; SETPO;
  SETNS; SETNE; SETNZ; SETO; SETP; SETPE; SETS; SETE; SETZ;
  IMUL];;
