(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

let decode_print_log = ref false;;

(* ========================================================================= *)
(* x86 instruction decoding.                                                 *)
(* ========================================================================= *)

let rep_pfx_INDUCTION,rep_pfx_RECURSION = define_type
  "rep_pfx = Rep0 | RepZ | RepNZ";;

(*
  We only model segment override values that
  could be used for extending NOP for alignment.

  See "Optimizing subroutines in assembly language
   An optimization guide for x86 platforms."
  Chap 10.6 "Making instructions longer for the sake of alignment"
 *)
let seg_pfx_INDUCTION,seg_pfx_RECURSION = define_type
  "seg_pfx = SG0 | CS | SS | DS | ES";;

new_type_abbrev("pfxs",`:bool # rep_pfx # seg_pfx`);;

let has_pfxs = new_definition `has_pfxs pfxs <=> ~(pfxs = (F, Rep0, SG0))`;;

let has_unhandled_pfxs = new_definition
 `has_unhandled_pfxs (pfxs:pfxs)
   <=> ~(FST (SND pfxs) = Rep0) \/ ~(SND (SND pfxs) = SG0)`;;

let has_operand_override = new_definition
  `has_operand_override (pfxs:pfxs) = FST pfxs`;;

(*
  The operation override prefix,
  also a mandatory prefix on some instructions.

  For extending an instruction for the sake of alignment,
  multiple 66H prefix could be added to the instruction.
  Therefore we allow an arbitrary number of 66H prefix to be set.
*)
let pfxs_set_opo = new_definition `pfxs_set_opo (opo, rep, seg) =
  SOME (T, rep, seg)`;;

(* The REPZ prefix,
   also a mandatory prefix on some instructions *)
let pfxs_set_repz = new_definition `pfxs_set_repz (opo, rep, seg) =
  if rep = Rep0 then SOME (opo, RepZ, seg) else NONE`;;

(* The REPNZ prefix,
   also a mandatory prefix on some instructions *)
let pfxs_set_repnz = new_definition `pfxs_set_repnz (opo, rep, seg) =
  if rep = Rep0 then SOME (opo, RepNZ, seg) else NONE`;;

(* The CS segment override prefix,
   also branch not taken (used only with Jcc instructions) prefix. *)
let pfxs_set_cs = new_definition `pfxs_set_cs (opo, rep, seg) =
  if seg = SG0 then SOME (opo, rep, CS) else NONE`;;

(* The DS segment override prefix,
   also branch taken (used only with Jcc instructions) prefix. *)
let pfxs_set_ds = new_definition `pfxs_set_ds (opo, rep, seg) =
  if seg = SG0 then SOME (opo, rep, DS) else NONE`;;

(* The ES segment override prefix *)
let pfxs_set_es = new_definition `pfxs_set_es (opo, rep, seg) =
  if seg = SG0 then SOME (opo, rep, ES) else NONE`;;

(* The SS segment override prefix *)
let pfxs_set_ss = new_definition `pfxs_set_ss (opo, rep, seg) =
  if seg = SG0 then SOME (opo, rep, SS) else NONE`;;

let read_prefixes = new_recursive_definition list_RECURSION
  `(!p. read_prefixes [] p = NONE) /\
   (!b l p. read_prefixes (CONS b l) p =
    bitmatch b:byte with
    | [0x66:8] -> pfxs_set_opo p >>= read_prefixes l
    | [0xf2:8] -> pfxs_set_repnz p >>= read_prefixes l
    | [0xf3:8] -> pfxs_set_repz p >>= read_prefixes l
    | [0x2e:8] -> pfxs_set_cs p >>= read_prefixes l
    | [0x36:8] -> pfxs_set_ss p >>= read_prefixes l
    | [0x3e:8] -> pfxs_set_ds p >>= read_prefixes l
    | [0x26:8] -> pfxs_set_es p >>= read_prefixes l
    // Even though we are not using any of these prefixes,
    // we need to know that they are prefix bytes to avoid
    // misinterpreting them as another instruction.
    | [0xf0:8] -> NONE // LOCK prefix
    | [0x64:8] -> NONE // FS segment prefix
    | [0x65:8] -> NONE // GS segment prefix
    | [0x67:8] -> NONE // address override prefix
    | _ -> SOME (p,CONS b l))`;;

let read_REX_prefix = define
  `read_REX_prefix [] = (NONE,[]) /\
   (!b l. read_REX_prefix (CONS b l) =
    bitmatch b:byte with
    | [0x4:4; rex:4] -> (SOME rex, l)
    | _ -> (NONE, CONS b l))`;;

let rex_num = define
  `rex_num NONE = word 0 /\
   (!n:4 word. rex_num (SOME n) = n)`;;

let rex_B = new_definition `rex_B rex = bit 0 (rex_num rex)`
and rex_X = new_definition `rex_X rex = bit 1 (rex_num rex)`
and rex_R = new_definition `rex_R rex = bit 2 (rex_num rex)`
and rex_W = new_definition `rex_W rex = bit 3 (rex_num rex)`;;

let regsize8 = define `regsize8 F = Upper_8 /\ regsize8 T = Lower_8`;;
let op_size = new_definition `op_size have_rex w v pfxs =
  if ~v then regsize8 have_rex
  else if w then Full_64
  else if has_operand_override pfxs then Lower_16
  else Lower_32`;;

let adx = define
 `adx Byte = %ah,%al /\
  adx Word = %dx,%ax /\
  adx Doubleword = %edx,%eax /\
  adx Quadword = %rdx,%rax`;;

let to_wordsize = define
 `to_wordsize Lower_8 = Byte /\
  to_wordsize Upper_8 = Byte /\
  to_wordsize Lower_16 = Word /\
  to_wordsize Lower_32 = Doubleword /\
  to_wordsize Full_64 = Quadword`;;

let simd_to_wordsize = define
 `simd_to_wordsize Lower_128 = Word128 /\
  simd_to_wordsize Lower_256 = Word256 /\
  simd_to_wordsize Full_512 = Word512`;;

let op_size_W = new_definition `op_size_W rex =
  op_size (is_some rex) (rex_W rex)`;;

let rex_reg = new_definition `rex_reg b (reg:3 word) =
  word_join (word1 b) reg: 4 word`;;

let read_imm = define
 `(!l. read_imm Byte l = read_byte l >>= \(b,l). SOME(Imm8 b,l)) /\
  (!l. read_imm Word l = read_int16 l >>= \(b,l). SOME(Imm16 b,l)) /\
  (!l. read_imm Doubleword l = read_int32 l >>= \(b,l). SOME(Imm32 b,l)) /\
  (!l. read_imm Quadword l = read_int32 l >>= \(b,l). SOME(Imm32 b,l)) /\
  (!l. read_imm Word128 l = read_int32 l >>= \(b,l). NONE) /\
  (!l. read_imm Word256 l = read_int32 l >>= \(b,l). NONE) /\
  (!l. read_imm Word512 l = read_int32 l >>= \(b,l). NONE)`;;

let read_full_imm = define
 `(!l. read_full_imm Byte l = read_byte l >>= \(b,l). SOME(Imm8 b,l)) /\
  (!l. read_full_imm Word l = read_int16 l >>= \(b,l). SOME(Imm16 b,l)) /\
  (!l. read_full_imm Doubleword l = read_int32 l >>= \(b,l). SOME(Imm32 b,l)) /\
  (!l. read_full_imm Quadword l = read_int64 l >>= \(b,l). SOME(Imm64 b,l)) /\
  (!l. read_full_imm Word128 l = read_int64 l >>= \(b,l). NONE) /\
  (!l. read_full_imm Word256 l = read_int64 l >>= \(b,l). NONE) /\
  (!l. read_full_imm Word512 l = read_int64 l >>= \(b,l). NONE)`;;

let read_displacement = new_definition `read_displacement (md:2 word) l =
  match val md with
  | 0 -> SOME(word 0:int64,l)
  | 1 -> read_byte l >>= \(b,l). SOME(word_sx b,l)
  | 2 -> read_int32 l >>= \(w,l). SOME(word_sx w,l)
  | _ -> NONE`;;

let RM_INDUCTION,RM_RECURSION = define_type
 "RM = RM_reg (4 word) | RM_mem bsid";;

let read_sib_displacement = new_definition
 `read_sib_displacement (md:2 word) (reg:4 word) l =
  if reg = word 5 /\ md = word 0 then
    read_int32 l >>= \(w,l).
    SOME((word_sx w,NONE),l)
  else
    read_displacement md l >>= \(w,l).
    SOME((w,SOME (Gpr reg Full_64)),l)`;;

let read_SIB = define
 `read_SIB rex md [] = NONE /\
  (!b l. read_SIB rex md (CONS b l) =
   bitmatch b:byte with
   | [ss:2; ix:3; bs:3] ->
     let bs = rex_reg (rex_B rex) bs in
     let ix = rex_reg (rex_X rex) ix in
     let s,i =
       if ix = word 4 then word 0,NONE
       else ss,SOME (Gpr ix Full_64) in
     read_sib_displacement md bs l >>= \((d,b),l).
     SOME(Bsid b i s d, l))`;;

let read_ModRM = define
 `read_ModRM rex [] = NONE /\
  (!b l. read_ModRM rex (CONS b l) =
   bitmatch b:byte with
   | [0b00:2; reg:3; 0b101:3] ->
     read_int32 l >>= \(i,l).
     SOME((rex_reg (rex_R rex) reg,RM_mem (Riprel (word_sx i))), l)
   | [0b11:2; reg:3; rm:3] ->
     SOME((rex_reg (rex_R rex) reg, RM_reg (rex_reg (rex_B rex) rm)), l)
   | [md:2; reg:3; 0b100:3] ->
     read_SIB rex md l >>= \(sib,l).
     SOME((rex_reg (rex_R rex) reg, RM_mem sib), l)
   | [md:2; reg:3; rm:3] ->
     read_displacement md l >>= \(disp,l).
     SOME((rex_reg (rex_R rex) reg,
           RM_mem (%%(Gpr (rex_reg (rex_B rex) rm) Full_64,val disp))), l))`;;

let gpr_adjust = new_definition `!sz reg. gpr_adjust (reg:4 word) sz =
  if sz = Upper_8 then
    if val reg < 4 then Gpr reg Lower_8
    else if val reg < 8 then Gpr (word (val reg - 4)) Upper_8
    else ARB
  else Gpr reg sz`;;

let operand_of_RM = define
 `(!reg. operand_of_RM sz (RM_reg reg) = %(gpr_adjust reg sz)) /\
  (!ea. operand_of_RM sz (RM_mem ea) = Memop (to_wordsize sz) ea)`;;

let mmreg = new_definition
 `mmreg (reg:4 word) sz = %_%(Simdreg (word_zx reg) sz)`;;

let simd_of_RM = define
 `(!reg. simd_of_RM sz (RM_reg reg) =
         %_%(Simdreg (word_zx reg) sz)) /\
  (!ea. simd_of_RM sz (RM_mem ea) = Memop (simd_to_wordsize sz) ea)`;;

let is_memop = define
 `(!reg. is_memop (RM_reg reg) = F) /\
  (!ea. is_memop (RM_mem ea) = T)`;;

let read_ModRM_operand = new_definition
 `read_ModRM_operand rex sz l =
  read_ModRM rex l >>= \((reg,rm),l).
  SOME ((%(gpr_adjust reg sz), operand_of_RM sz rm), l)`;;

let read_opcode_ModRM = new_definition
 `read_opcode_ModRM rex l =
  read_ModRM rex l >>= \((rn,rm),l). SOME((word_zx rn:3 word,rm),l)`;;

let read_opcode_ModRM_operand = new_definition
 `read_opcode_ModRM_operand rex sz l =
  read_opcode_ModRM rex l >>= \((opc,rm),l).
  SOME ((opc, operand_of_RM sz rm), l)`;;

let VEXM_INDUCTION,VEXM_RECURSION = define_type
 "VEXM = VEXM_0F | VEXM_0F38 | VEXM_0F3A";;

let read_VEXM = new_definition `read_VEXM (m:5 word) =
  bitmatch m with
  | [1:5] -> SOME VEXM_0F
  | [2:5] -> SOME VEXM_0F38
  | [3:5] -> SOME VEXM_0F3A
  | _ -> NONE`;;

let read_VEXP = new_definition `read_VEXP (p:2 word) =
  bitmatch p with
  | [0:2] -> (F, Rep0, SG0)
  | [1:2] -> (T, Rep0, SG0)
  | [2:2] -> (F, RepZ, SG0)
  | [3:2] -> (F, RepNZ, SG0)`;;

let read_VEX = define
 `(!l. read_VEX T l =
   read_byte l >>= \(b,l). bitmatch b with [r:1; v:4; L; p:2] ->
   SOME((SOME(word_shl (word_zx (word_not r)) 2),
     VEXM_0F, word_not v, L, read_VEXP p), l)) /\
  (!l. read_VEX F l =
   read_byte l >>= \(b,l). bitmatch b with [rxb:3; m:5] ->
   read_byte l >>= \(b,l). bitmatch b with [w; v:4; L; p:2] ->
   read_VEXM m >>= \m.
   SOME((SOME(rex_reg w (word_not rxb)), m, word_not v, L, read_VEXP p), l))`;;

let vexL_size = define
 `vexL_size F = Lower_128 /\
  vexL_size T = Lower_256`;;

let decode_condition = new_definition
 `decode_condition (n:4 word) =
  match val n with
  | 0x0 -> Condition_O   | 0x1 -> Condition_NO
  | 0x2 -> Condition_B   | 0x3 -> Condition_NB
  | 0x4 -> Condition_Z   | 0x5 -> Condition_NZ
  | 0x6 -> Condition_BE  | 0x7 -> Condition_NBE
  | 0x8 -> Condition_S   | 0x9 -> Condition_NS
  | 0xA -> Condition_P   | 0xB -> Condition_NP
  | 0xC -> Condition_L   | 0xD -> Condition_NL
  | 0xE -> Condition_LE  | 0xF -> Condition_NLE`;;

let decode_binop = new_definition
 `decode_binop (n:4 word) =
  match val n with
  | 0x0 -> ADD  | 0x1 -> OR   | 0x2 -> ADC  | 0x3 -> SBB
  | 0x4 -> AND  | 0x5 -> SUB  | 0x6 -> XOR  | 0x7 -> CMP
  | 0x8 -> ROL  | 0x9 -> ROR  | 0xA -> RCL  | 0xB -> RCR
  | 0xC -> SHL  | 0xD -> SHR  | 0xE -> TEST | 0xF -> SAR`;;

let decode_BT = new_definition `decode_BT (n:2 word) =
  match val n with 0 -> BT | 1 -> BTS | 2 -> BTR | 3 -> BTC`;;

let decode_hi = new_definition `decode_hi x v sz (opc:3 word) rm l =
  match x,v,val opc with
  | F,_,0 -> read_imm sz l >>= \(imm,l). SOME (TEST rm imm,l)
  | F,_,2 -> SOME (NOT rm,l)
  | F,_,3 -> SOME (NEG rm,l)
  | F,_,4 -> SOME (MUL2 (adx sz) rm,l)
  | F,_,5 -> SOME (IMUL2 (adx sz) rm,l)
  // | F,_,6 -> let hi,lo = adx sz in SOME (DIV2 (lo,hi) (hi,lo) rm,l)
  // | F,_,7 -> SOME (IDIV rm,l)
  | T,_,0 -> SOME (INC rm,l)
  | T,_,1 -> SOME (DEC rm,l)
  | T,T,2 -> SOME (CALL rm,l)
  | T,T,4 -> SOME (JMP rm,l)
  | T,T,6 -> SOME (PUSH rm,l)
  | _ -> NONE`;;

let decode_aux = new_definition `!pfxs rex l. decode_aux pfxs rex l =
  read_byte l >>= \(b,l).
  bitmatch b with
  | [0b00:2; opc:3; 0b0:1; d; v] -> if has_unhandled_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_ModRM_operand rex sz l >>= \((reg,rm),l).
    let dest,src = if d then reg,rm else rm,reg in
    SOME (decode_binop (word_zx opc) dest src,l)
  | [0b00:2; opc:3; 0b10:2; v] -> if has_unhandled_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_imm (to_wordsize sz) l >>= \(imm,l).
    SOME (decode_binop (word_zx opc) (%(gpr_adjust (word 0) sz)) imm,l)
  | [0x0f:8] -> read_byte l >>= \(b,l).
    (bitmatch b with
    | [0b0001000:7; d] -> if has_pfxs pfxs then NONE else
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      let reg = mmreg reg sz in
      let rm = simd_of_RM sz rm in
      let dest,src = if d then rm,reg else reg,rm in
      SOME (MOVUPS dest src, l)
    | [0x1e:8] ->
        read_byte l >>= \(b,l).
        (bitmatch b with
         | [0xfa:8] ->
           (match pfxs with
            | (F, RepZ, SG0) -> SOME (ENDBR64,l)
            | _ -> NONE)
         | _ -> NONE)
    | [0x1f:8] ->
      let sz = op_size_W rex T pfxs in
      read_ModRM_operand rex sz l >>= \((_,rm),l).
      (match pfxs with
        | (F, Rep0, SG0) -> SOME (NOP_N rm,l)
        | (F, Rep0, CS) -> SOME (NOP_N rm,l)
        | (F, Rep0, DS) -> SOME (NOP_N rm,l)
        | (F, Rep0, ES) -> SOME (NOP_N rm,l)
        | (F, Rep0, SS) -> SOME (NOP_N rm,l)
        | (T, Rep0, SG0) -> SOME (NOP_N rm,l)
        | (T, Rep0, CS) -> SOME (NOP_N rm,l)
        | (T, Rep0, DS) -> SOME (NOP_N rm,l)
        | (T, Rep0, ES) -> SOME (NOP_N rm,l)
        | (T, Rep0, SS) -> SOME (NOP_N rm,l)
        | _ -> NONE)
    | [0b0010100:7; d] -> if has_pfxs pfxs then NONE else
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      let reg = mmreg reg sz in
      let rm = simd_of_RM sz rm in
      let dest,src = if d then rm,reg else reg,rm in
      SOME (MOVAPS dest src, l)
    | [0x38:8] -> read_byte l >>= \(b,l).
      (bitmatch b with
      | [0x00:8] -> if has_unhandled_pfxs pfxs then NONE else
        let sz = Lower_128 in
        read_ModRM rex l >>= \((reg,rm),l).
        SOME (PSHUFB (mmreg reg sz) (simd_of_RM sz rm), l)
      | [0xdc:8] -> if has_unhandled_pfxs pfxs then NONE else
        let sz = Lower_128 in
        read_ModRM rex l >>= \((reg,rm),l).
        SOME (AESENC (mmreg reg sz) (simd_of_RM sz rm), l)
      | [0xdd:8] -> if has_unhandled_pfxs pfxs then NONE else
        let sz = Lower_128 in
        read_ModRM rex l >>= \((reg,rm),l).
        SOME (AESENCLAST (mmreg reg sz) (simd_of_RM sz rm), l)
      | [0xde:8] -> if has_unhandled_pfxs pfxs then NONE else
        let sz = Lower_128 in
        read_ModRM rex l >>= \((reg,rm),l).
        SOME (AESDEC (mmreg reg sz) (simd_of_RM sz rm), l)
      | [0xdf:8] -> if has_unhandled_pfxs pfxs then NONE else
        let sz = Lower_128 in
        read_ModRM rex l >>= \((reg,rm),l).
        SOME (AESDECLAST (mmreg reg sz) (simd_of_RM sz rm), l)
      | [0xf6:8] ->
        let sz = op_size T (rex_W rex) T pfxs in
        read_ModRM_operand rex sz l >>= \((reg,rm),l).
        (match pfxs with
        | (T, Rep0, SG0) -> SOME (ADCX reg rm,l)
        | (F, RepZ, SG0) -> SOME (ADOX reg rm,l)
        | _ -> NONE)
      | _ -> NONE)
    | [0x3a:8] -> read_byte l >>= \(b,l).
      (bitmatch b with
      | [0x0e:8] -> if has_unhandled_pfxs pfxs then NONE else
        let sz = Lower_128 in
        read_ModRM rex l >>= \((reg,rm),l).
        read_imm Byte l >>= \(imm8,l).
        SOME (PBLENDW (mmreg reg sz) (simd_of_RM sz rm) imm8, l)
      | [0x22:8] -> if has_unhandled_pfxs pfxs then NONE else
        read_ModRM rex l >>= \((reg,rm),l).
        read_imm Byte l >>= \(imm8,l).
        let dest = mmreg reg Lower_128 in
        let sz = if rex_W rex then Full_64 else Lower_32 in
        let src = operand_of_RM sz rm in
        (match pfxs with
         | (T, Rep0, SG0) ->
           if rex_W rex then SOME (PINSRQ dest src imm8, l)
           else SOME (PINSRD dest src imm8, l)
         | _ -> NONE)
      | [0xdf:8] -> if has_unhandled_pfxs pfxs then NONE else
        let sz = Lower_128 in
        read_ModRM rex l >>= \((reg,rm),l).
        read_imm Byte l >>= \(imm8,l).
        SOME (AESKEYGENASSIST (mmreg reg sz) (simd_of_RM sz rm) imm8, l)
      | _ -> NONE)
    | [0x4:4; c:4] -> if has_pfxs pfxs then NONE else
      let sz = op_size T (rex_W rex) T pfxs in
      read_ModRM_operand rex sz l >>= \((reg,rm),l).
      SOME (CMOV (decode_condition c) reg rm,l)
    | [0x65:8] -> if has_unhandled_pfxs pfxs then NONE else
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      SOME (PCMPGTW (mmreg reg sz) (simd_of_RM sz rm), l)
    | [0x66:8] -> if has_unhandled_pfxs pfxs then NONE else
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      SOME (PCMPGTD (mmreg reg sz) (simd_of_RM sz rm), l)
    | [0x6e:8] -> if has_unhandled_pfxs pfxs then NONE else
      read_ModRM rex l >>= \((reg,rm),l).
      let dest = mmreg reg Lower_128 in
      let sz = if rex_W rex then Full_64 else Lower_32 in
      let src = operand_of_RM sz rm in
      (match pfxs with
      | (T, Rep0, SG0) ->
        if rex_W rex then SOME (MOVQ dest src, l) else SOME (MOVD dest src, l)
      | _ -> NONE)
    | [0b011:3; d; 0b1111:4] ->
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      let reg = mmreg reg sz in
      let rm = simd_of_RM sz rm in
      let dest,src = if d then rm,reg else reg,rm in
      (match pfxs with
      | (T, Rep0, SG0) -> SOME (MOVDQA dest src, l)
      | (F, RepZ, SG0) -> SOME (MOVDQU dest src, l)
      | _ -> NONE)
    | [0x70:8] -> if has_unhandled_pfxs pfxs then NONE else
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      read_imm Byte l >>= \(imm8,l).
      SOME (PSHUFD (mmreg reg sz) (simd_of_RM sz rm) imm8, l)
    | [0x71:8] -> if has_unhandled_pfxs pfxs then NONE else
      let sz = Lower_128 in
      (read_ModRM rex l >>= \((reg,rm),l).
       match rm with
       | RM_reg _ -> if (word_zx reg):(3 word) = word 0b010 then
         (read_imm Byte l >>= \(imm8,l).
          SOME (PSRLW (simd_of_RM sz rm) imm8, l))
         else NONE
       | _ -> NONE)
    | [0x72:8] -> if has_unhandled_pfxs pfxs then NONE else
      let sz = Lower_128 in
      (read_ModRM rex l >>= \((reg,rm),l).
       match rm with
       | RM_reg _ -> if (word_zx reg):(3 word) = word 0b100 then
         (read_imm Byte l >>= \(imm8,l).
          SOME (PSRAD (simd_of_RM sz rm) imm8, l))
         else NONE
       | _ -> NONE)
    | [0x7e:8] ->
      (read_ModRM rex l >>= \((reg,rm),l).
      match pfxs with
      | (T, Rep0, SG0) ->
        if rex_W rex then
          let src = mmreg reg Lower_128 in
          let dst = operand_of_RM Full_64 rm in
          SOME (MOVQ dst src, l)
        else
          let src = mmreg reg Lower_128 in
          let dst = operand_of_RM Lower_32 rm in
          SOME (MOVD dst src, l)
    | (F, RepZ, SG0) ->
          let src = if is_memop rm then operand_of_RM Full_64 rm
                  else simd_of_RM Lower_128 rm in
          let dst = mmreg reg Lower_128 in
          SOME (MOVQ dst src, l)
        | _ -> NONE)
    | [0x8:4; c:4] -> if has_pfxs pfxs then NONE else
      read_int32 l >>= \(imm,l).
      SOME (JUMP (decode_condition c) (Imm32 imm),l)
    | [0x9:4; c:4] -> if has_pfxs pfxs then NONE else
      let sz = regsize8 (is_some rex) in
      read_ModRM_operand rex sz l >>= \((_,rm),l).
      SOME (SET (decode_condition c) rm,l)
    | [0b101:3; op:2; 0b011:3] -> if has_pfxs pfxs then NONE else
      let sz = op_size_W rex T pfxs in
      read_ModRM_operand rex sz l >>= \((reg,rm),l).
      SOME (decode_BT op rm reg,l)
    | [0xa:4; x; 0b100:3] -> if has_pfxs pfxs then NONE else
      let sz = op_size_W rex T pfxs in
      read_ModRM_operand rex sz l >>= \((reg,rm),l).
      read_byte l >>= \(b,l).
      SOME ((if x then SHRD else SHLD) rm reg (Imm8 b),l)
    | [0xa:4; x; 0b101:3] -> if has_pfxs pfxs then NONE else
      let sz = op_size_W rex T pfxs in
      read_ModRM_operand rex sz l >>= \((reg,rm),l).
      SOME ((if x then SHRD else SHLD) rm reg (%cl),l)
    | [0xaf:8] -> if has_pfxs pfxs then NONE else
      let sz = op_size_W rex T pfxs in
      read_ModRM_operand rex sz l >>= \((reg,rm),l).
      SOME (IMUL reg rm,l)
    | [0xb8:8] ->
      let sz = op_size_W rex T pfxs in
      read_ModRM_operand rex sz l >>= \((reg,rm),l).
      (match pfxs with
      | (F, RepZ, SG0) -> SOME (POPCNT reg rm,l)
      | _ -> NONE)
    | [0xba:8] -> if has_pfxs pfxs then NONE else
      let sz = op_size_W rex T pfxs in
      read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
      (bitmatch opc with
      | [1:1; op:2] ->
        read_byte l >>= \(b,l).
        SOME (decode_BT op rm (Imm8 b),l)
      | _ -> NONE)
    | [0xbc:8] ->
      let sz = op_size_W rex T pfxs in
      read_ModRM_operand rex sz l >>= \((reg,rm),l).
      (match pfxs with
      | (F, Rep0, SG0) -> SOME (BSF reg rm,l)
      | (F, RepZ, SG0) -> SOME (TZCNT reg rm,l)
      | _ -> NONE)
    | [0xbd:8] ->
      let sz = op_size_W rex T pfxs in
      read_ModRM_operand rex sz l >>= \((reg,rm),l).
      (match pfxs with
      | (F, Rep0, SG0) -> SOME (BSR reg rm,l)
      | (F, RepZ, SG0) -> SOME (LZCNT reg rm,l)
      | _ -> NONE)
    | [0xb:4; s; 0b11:2; v] -> if has_pfxs pfxs then NONE else
      let sz2 = op_size_W rex T pfxs in
      let sz = if v then Lower_16 else regsize8 (is_some rex) in
      read_ModRM rex l >>= \((reg,rm),l).
      let op = if s then MOVSX else MOVZX in
      SOME (op (%(gpr_adjust reg sz2)) (operand_of_RM sz rm),l)
    | [0b11001:5; r:3] -> if has_pfxs pfxs then NONE else
      let sz = op_size_W rex T pfxs in
      let reg = rex_reg (rex_B rex) r in
      SOME (BSWAP (%(gpr_adjust reg sz)),l)
    | [0xd4:8] -> if has_unhandled_pfxs pfxs then NONE else
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      SOME (PADDQ (mmreg reg sz) (simd_of_RM sz rm), l)
    | [0xd6:8] ->
      (read_ModRM rex l >>= \((reg,rm),l).
        match pfxs with
        | (T, Rep0, SG0) ->
            let src = mmreg reg Lower_128 in
            let dst = if is_memop rm then operand_of_RM Full_64 rm
                    else simd_of_RM Lower_128 rm in
            SOME (MOVQ dst src, l)
        | _ -> NONE)
    | [0xd7:8] -> if has_unhandled_pfxs pfxs then NONE else
      read_ModRM rex l >>= \((reg,rm),l).
      let dest = %(gpr_adjust reg Lower_32) in
      let src = simd_of_RM Lower_128 rm in
      SOME (PMOVMSKB dest src, l)
    | [0xdb:8] -> if has_unhandled_pfxs pfxs then NONE else
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      SOME (PAND (mmreg reg sz) (simd_of_RM sz rm), l)
    | [0xef:8] -> if has_unhandled_pfxs pfxs then NONE else
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      SOME (PXOR (mmreg reg sz) (simd_of_RM sz rm), l)
    | [0xfe:8] -> if has_unhandled_pfxs pfxs then NONE else
      let sz = Lower_128 in
      read_ModRM rex l >>= \((reg,rm),l).
      SOME (PADDD (mmreg reg sz) (simd_of_RM sz rm), l)
    | _ -> NONE)
  | [0b01010:5; r:3] -> if has_pfxs pfxs then NONE else
    SOME (PUSH (%(Gpr (rex_reg (rex_B rex) r) Full_64)),l)
  | [0b01011:5; r:3] -> if has_pfxs pfxs then NONE else
    SOME (POP (%(Gpr (rex_reg (rex_B rex) r) Full_64)),l)
  | [0x63:8] -> if has_pfxs pfxs then NONE else
    let sz2 = op_size_W rex T pfxs in
    read_ModRM rex l >>= \((reg,rm),l).
    SOME (MOVSX (%(gpr_adjust reg sz2)) (operand_of_RM Lower_32 rm),l)
  | [0b011010:6; x; 0b0:1] -> if has_pfxs pfxs then NONE else
    read_imm (if x then Byte else Quadword) l >>= \(imm,l).
    SOME (PUSH imm,l)
  | [0b011010:6; x; 0b1:1] -> if has_pfxs pfxs then NONE else
    let sz = op_size_W rex T pfxs in
    read_ModRM_operand rex sz l >>= \((reg,rm),l).
    read_imm (if x then Byte else Quadword) l >>= \(imm,l).
    SOME (IMUL3 reg (rm,imm),l)
  | [0x7:4; c:4] -> if has_pfxs pfxs then NONE else
    read_byte l >>= \(b,l).
    SOME (JUMP (decode_condition c) (Imm8 b),l)
  | [0b1000000:7; v] -> if has_unhandled_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
    read_imm (to_wordsize sz) l >>= \(imm,l).
    SOME (decode_binop (word_zx opc) rm imm,l)
  | [0x83:8] -> if has_unhandled_pfxs pfxs then NONE else
    let sz = op_size_W rex T pfxs in
    read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
    read_byte l >>= \(b,l).
    SOME (decode_binop (word_zx opc) rm (Imm8 b),l)
  | [0b1000010:7; v] -> if has_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_ModRM_operand rex sz l >>= \((reg,rm),l).
    SOME (TEST rm reg,l)
  | [0b1000011:7; v] -> if has_unhandled_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_ModRM_operand rex sz l >>= \((reg,rm),l).
    SOME (XCHG reg rm,l)
  | [0b100010:6; d; v] -> if has_unhandled_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_ModRM_operand rex sz l >>= \((reg,rm),l).
    let dest,src = if d then reg,rm else rm,reg in
    SOME (MOV dest src,l)
  | [0x8d:8] -> if has_pfxs pfxs then NONE else
    let sz = op_size T (rex_W rex) T pfxs in
    read_ModRM rex l >>= \((reg,rm),l).
    (match rm with
    | RM_mem ea -> SOME (LEA (%(gpr_adjust reg sz)) ea,l)
    | _ -> NONE)
  | [0x8f:8] -> if has_pfxs pfxs then NONE else
    let sz = op_size_W rex T pfxs in
    read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
    if opc = word 0 then
      SOME (POP rm,l)
    else NONE
  | [0x90:8] -> if has_unhandled_pfxs pfxs then NONE else
    SOME (NOP,l)
  | [0xa4:8] ->
    (match pfxs with
     | (F, Rep0, SG0) -> SOME (MOVSB F (%rdi) (%rsi) (Imm8(word 1)),l)
     | (F, RepZ, SG0) -> SOME (MOVSB T (%rdi) (%rsi) (%rcx),l)
     | (F, RepNZ, SG0) -> SOME (MOVSB T (%rdi) (%rsi) (%rcx),l)
     | _ -> NONE)
  | [0b1010100:7; v] -> if has_pfxs pfxs then NONE else
    let sz = op_size T (rex_W rex) v pfxs in
    read_imm (to_wordsize sz) l >>= \(imm,l).
    SOME (TEST (%(gpr_adjust (word 0) sz)) imm,l)
  | [0xb:4; v; r:3] -> if has_unhandled_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_full_imm (to_wordsize sz) l >>= \(imm,l).
    let reg = rex_reg (rex_B rex) r in
    SOME (MOV (%(gpr_adjust reg sz)) imm,l)
  | [0b1100000:7; v] -> if has_unhandled_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
    if opc = word 6 then NONE else
    read_byte l >>= \(b,l).
    SOME (decode_binop (rex_reg T opc) rm (Imm8 b),l)
  | [0xc3:8] -> if has_pfxs pfxs then NONE else
    SOME (RET,l)
  | [0b1100010:7; vl] -> if has_pfxs pfxs then NONE else
    if is_some rex then NONE else
    read_VEX vl l >>= \((rex,m,v,L,pfxs),l).
    (match m with
      VEXM_0F38 ->
        read_byte l >>= \(b,l).
        (bitmatch b with
        | [0x00:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPSHUFB (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x04:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMADDUBSW (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x0b:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMULHRSW (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x17:8] -> if word_not v = (word 0b1111:4 word) then
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPTEST (mmreg reg sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        else NONE
        | [0x1e:8] -> if word_not v = (word 0b1111:4 word) then
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPABSD (mmreg reg sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        else NONE
        | [0x21:8] -> if word_not v = (word 0b1111:4 word) then
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           let sop = if is_memop rm then
                       (if L then operand_of_RM Full_64 rm
                        else operand_of_RM Lower_32 rm)
                     else simd_of_RM Lower_128 rm in
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMOVSXBD (mmreg reg sz) sop,l)
           | _ -> NONE)
        else NONE
        | [0x28:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMULDQ (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x30:8] -> if word_not v = (word 0b1111:4 word) then
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           let sop = if is_memop rm then
                       (if L then simd_of_RM Lower_128 rm
                        else operand_of_RM Full_64 rm)
                     else simd_of_RM Lower_128 rm in
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMOVZXBW (mmreg reg sz) sop,l)
           | _ -> NONE)
        else NONE
        | [0x31:8] -> if word_not v = (word 0b1111:4 word) then
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           let sop = if is_memop rm then
                       (if L then operand_of_RM Full_64 rm
                        else operand_of_RM Lower_32 rm)
                     else simd_of_RM Lower_128 rm in
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMOVZXBD (mmreg reg sz) sop,l)
           | _ -> NONE)
        else NONE
        | [0x36:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           if rex_W rex then NONE else
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPERMD (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x45:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) ->
             if rex_W rex then
               SOME (VPSRLVQ (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
             else
               SOME (VPSRLVD (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x47:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           if rex_W rex then NONE else
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPSLLVD (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x58:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           if rex_W rex then NONE else
           match pfxs with
           | (T, Rep0, SG0) ->
             let sop = if is_memop rm then operand_of_RM Lower_32 rm
                       else simd_of_RM Lower_128 rm in
             SOME (VPBROADCASTD (mmreg reg sz) sop,l)
           | _ -> NONE)
        | [0x59:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           if rex_W rex then NONE else
          match pfxs with
           | (T, Rep0, SG0) ->
             let sop = if is_memop rm then operand_of_RM Full_64 rm
                       else simd_of_RM Lower_128 rm in
             SOME (VPBROADCASTQ (mmreg reg sz) sop,l)
           | _ -> NONE)
        | [0x79:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           if rex_W rex then NONE else
           match pfxs with
           | (T, Rep0, SG0) ->
             let sop = if is_memop rm then operand_of_RM Lower_16 rm
                       else simd_of_RM Lower_128 rm in
             SOME (VPBROADCASTW (mmreg reg sz) sop,l)
           | _ -> NONE)
        | [0x40:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMULLD (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xf5:8] ->
          let sz = op_size_W rex T pfxs in
          read_ModRM_operand rex sz l >>= \((reg,rm),l).
          (match pfxs with
          | (F, RepZ, SG0) ->
             if L then NONE
             else SOME (PEXT reg (%(Gpr v sz)) rm, l)
          | _ -> NONE)
        | [0xf6:8] ->
          let sz = op_size_W rex T pfxs in
          read_ModRM_operand rex sz l >>= \((reg,rm),l).
          (match pfxs with
          | (F, RepNZ, SG0) ->
             if L then NONE
             else SOME (MULX4 (reg, %(Gpr v sz)) (%(Gpr (word 2) sz), rm), l)
          | _ -> NONE)
        | _ -> NONE)
    | VEXM_0F ->
        read_byte l >>= \(b,l).
        (bitmatch b with
        | [0x12:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (F, RepZ, SG0) -> SOME (VMOVSLDUP (mmreg reg sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x50:8] -> if word_not v = (word 0b1111:4 word) /\ L then
          (read_ModRM rex l >>= \((reg,rm),l).
           let dest = %(gpr_adjust reg Lower_32) in
           let src = simd_of_RM Lower_256 rm in
           match pfxs with
           | (F, Rep0, SG0) -> SOME (VMOVMSKPS dest src, l)
           | _ -> NONE)
        else NONE
        | [0xd7:8] -> if word_not v = (word 0b1111:4 word) /\ L then
          (read_ModRM rex l >>= \((reg,rm),l).
           let dest = %(gpr_adjust reg Lower_32) in
           let src = simd_of_RM Lower_256 rm in
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMOVMSKB dest src, l)
           | _ -> NONE)
        else NONE
        | [0x16:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (F, RepZ, SG0) -> SOME (VMOVSHDUP (mmreg reg sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x17:8] -> if word_not v = (word 0b1111:4 word) then
          (if L then NONE else
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) ->
              let dst = operand_of_RM Full_64 rm in
              let src = mmreg reg Lower_128 in
              SOME (VMOVHPD dst src, l)
           | _ -> NONE))
        else NONE
        | [0x77:8] -> if word_not v = (word 0b1111:4 word) then
          (if L then NONE else
           match pfxs with
           | (F, Rep0, SG0) -> SOME (VZEROUPPER, l)
           | _ -> NONE)
        else NONE
        | [0x6c:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPUNPCKLQDQ (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x6d:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPUNPCKHQDQ (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x67:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPACKUSWB (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x6e:8] ->  if word_not v = (word 0b1111:4 word) then
          (if L then NONE else
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) ->
             if rex_W rex then
               let dst = mmreg reg Lower_128 in
               let src = operand_of_RM Full_64 rm in
               SOME (VMOVQ dst src, l)
             else
               let dst = mmreg reg Lower_128 in
               let src = operand_of_RM Lower_32 rm in
               SOME (VMOVD dst src, l)
           | _ -> NONE))
          else NONE
        | [0x6f:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME(VMOVDQA (mmreg reg sz) (simd_of_RM sz rm),l)
           | (F, RepZ, SG0) -> SOME(VMOVDQU (mmreg reg sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x7e:8] -> if word_not v = (word 0b1111:4 word) then
          (if L then NONE else
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) ->
             if rex_W rex then
               let src = mmreg reg Lower_128 in
               let dst = operand_of_RM Full_64 rm in
               SOME (VMOVQ dst src, l)
             else
               let src = mmreg reg Lower_128 in
               let dst = operand_of_RM Lower_32 rm in
               SOME (VMOVD dst src, l)
          | (F, RepZ, SG0) ->
               let src = if is_memop rm then operand_of_RM Full_64 rm
                       else simd_of_RM Lower_128 rm in
               let dst = mmreg reg Lower_128 in
               SOME (VMOVQ dst src, l)
          | _ -> NONE))
        else NONE
        | [0x7f:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME(VMOVDQA (simd_of_RM sz rm) (mmreg reg sz),l)
           | (F, RepZ, SG0) -> SOME(VMOVDQU (simd_of_RM sz rm) (mmreg reg sz),l)
           | _ -> NONE)
        | [0x65:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPCMPGTW (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x66:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPCMPGTD (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xd4:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPADDQ (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xd5:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMULLW (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xdb:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPAND (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xdf:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPANDN (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xe4:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMULHUW (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xe5:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMULHW (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xeb:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPOR (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xef:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPXOR (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xf5:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPMADDWD (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xf8:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPSUBB (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xf9:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPSUBW (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xfa:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPSUBD (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xfb:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPSUBQ (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xfc:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPADDB (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xfd:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPADDW (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0xfe:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPADDD (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm),l)
           | _ -> NONE)
        | [0x71:8] ->
          let sz = vexL_size L in
          read_ModRM rex l >>= (\((reg,rm),l).
            match rm with
            | RM_reg _ ->
              read_imm Byte l >>= (\(imm8,l).
              (let r3:3 word = word_zx reg in
               match pfxs with
               | (T, Rep0, SG0) ->
                 (bitmatch r3 with
               | [0b010:3] -> SOME (VPSRLW (mmreg v sz) (simd_of_RM sz rm) imm8,l)
               | [0b100:3] -> SOME (VPSRAW (mmreg v sz) (simd_of_RM sz rm) imm8,l)
                  | [0b110:3] -> SOME (VPSLLW (mmreg v sz) (simd_of_RM sz rm) imm8,l)
                  | _ -> NONE)
               | _ -> NONE))
            | _ -> NONE)
        | [0x72:8] ->
          let sz = vexL_size L in
          read_ModRM rex l >>= (\((reg,rm),l).
            match rm with
            | RM_reg _ ->
              read_imm Byte l >>= (\(imm8,l).
              (let r3:3 word = word_zx reg in
               match pfxs with
               | (T, Rep0, SG0) ->
                 (bitmatch r3 with
                  | [0b010:3] -> SOME (VPSRLD (mmreg v sz) (simd_of_RM sz rm) imm8,l)
               | [0b100:3] -> SOME (VPSRAD (mmreg v sz) (simd_of_RM sz rm) imm8,l)
                  | [0b110:3] -> SOME (VPSLLD (mmreg v sz) (simd_of_RM sz rm) imm8,l)
                  | _ -> NONE)
               | _ -> NONE))
            | _ -> NONE)
        | [0x73:8] ->
          let sz = vexL_size L in
          read_ModRM rex l >>= (\((reg,rm),l).
            match rm with
            | RM_reg _ ->
              read_imm Byte l >>= (\(imm8,l).
              (let r3:3 word = word_zx reg in
               match pfxs with
               | (T, Rep0, SG0) ->
                 (bitmatch r3 with
               | [0b010:3] -> SOME (VPSRLQ (mmreg v sz) (simd_of_RM sz rm) imm8,l)
               | [0b011:3] -> SOME (VPSRLDQ (mmreg v sz) (simd_of_RM sz rm) imm8,l)
               | [0b110:3] -> SOME (VPSLLQ (mmreg v sz) (simd_of_RM sz rm) imm8,l)
                  | _ -> NONE)
               | _ -> NONE))
            | _ -> NONE)
        | [0xc4:8] ->
            if L then NONE else
            read_ModRM rex l >>= \((reg,rm),l).
            read_imm Byte l >>= \(imm8,l).
            let dest = mmreg reg Lower_128 in
            let src1 = mmreg v Lower_128 in
            let src2 = if is_memop rm then operand_of_RM Lower_16 rm
                       else operand_of_RM Lower_32 rm in
            (match pfxs with
            | (T, Rep0, SG0) -> SOME (VPINSRW dest src1 src2 imm8, l)
            | _ -> NONE)
        | [0xc5:8] ->
           if word_not v = (word 0b1111:4 word) then
           (if L then NONE else
            read_ModRM rex l >>= \((reg,rm),l).
            if is_memop rm then NONE else
            read_imm Byte l >>= \(imm8,l).
            if rex_W rex then NONE else
            let dest = %(gpr_adjust reg Lower_32) in
            let src = simd_of_RM Lower_128 rm in
            match pfxs with
            | (T, Rep0, SG0) -> SOME (VPEXTRW dest src imm8, l)
            | _ -> NONE)
           else NONE
        | [0xd6:8] -> (if word_not v = (word 0b1111:4 word) then
          (if L then NONE else
          (read_ModRM rex l >>= \((reg,rm),l).
           match pfxs with
           | (T, Rep0, SG0) ->
              let src = mmreg reg Lower_128 in
              let dst = if is_memop rm then operand_of_RM Full_64 rm
                      else simd_of_RM Lower_128 rm in
              SOME (VMOVQ dst src, l)
           | _ -> NONE))
        else NONE)
      | _ -> NONE)
    | VEXM_0F3A ->
        read_byte l >>= \(b,l).
        (bitmatch b with
        | [0x00:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
          read_imm Byte l >>= \(imm8,l).
           if rex_W rex then
           (match pfxs with
            | (T, Rep0, SG0) -> SOME (VPERMQ (mmreg reg sz) (simd_of_RM sz rm) imm8,l)
            | _ -> NONE)
           else NONE)
        | [0x02:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
            read_imm Byte l >>= \(imm8,l).
            if rex_W rex then NONE else
            match pfxs with
            | (T, Rep0, SG0) -> SOME (VPBLENDD (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm) imm8,l)
            | _ -> NONE)
        | [0x0e:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
            read_imm Byte l >>= \(imm8,l).
            match pfxs with
            | (T, Rep0, SG0) -> SOME (VPBLENDW (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm) imm8,l)
            | _ -> NONE)
        | [0x15:8] ->
           if word_not v = (word 0b1111:4 word) then
           (if L then NONE else
            read_ModRM rex l >>= \((reg,rm),l).
            read_imm Byte l >>= \(imm8,l).
            if rex_W rex then NONE else
            let src = mmreg reg Lower_128 in
            let dest = if is_memop rm then operand_of_RM Lower_16 rm
                       else operand_of_RM Lower_32 rm in
            match pfxs with
            | (T, Rep0, SG0) -> SOME (VPEXTRW dest src imm8, l)
            | _ -> NONE)
          else NONE
        | [0x16:8] ->
           if word_not v = (word 0b1111:4 word) then
           (if L then NONE else
            read_ModRM rex l >>= \((reg,rm),l).
            read_imm Byte l >>= \(imm8,l).
            let src = mmreg reg Lower_128 in
            let sz = if rex_W rex then Full_64 else Lower_32 in
            let dest = operand_of_RM sz rm in
            (match pfxs with
            | (T, Rep0, SG0) ->
              if rex_W rex then SOME (VPEXTRQ dest src imm8, l)
              else SOME (VPEXTRD dest src imm8, l)
            | _ -> NONE))
          else NONE
        | [0x22:8] ->
            if L then NONE else
            read_ModRM rex l >>= \((reg,rm),l).
            read_imm Byte l >>= \(imm8,l).
            let dest = mmreg reg Lower_128 in
            let src1 = mmreg v Lower_128 in
            let sz = if rex_W rex then Full_64 else Lower_32 in
            let src2 = operand_of_RM sz rm in
            (match pfxs with
            | (T, Rep0, SG0) ->
              if rex_W rex then SOME (VPINSRQ dest src1 src2 imm8, l)
              else SOME (VPINSRD dest src1 src2 imm8, l)
            | _ -> NONE)
         | [0x38:8] ->
            (if L then
              let sz = vexL_size L in
              (read_ModRM rex l >>= \((reg,rm),l).
              read_imm Byte l >>= \(imm8,l).
              if rex_W rex then NONE else
              let dest = mmreg reg sz in
              let src1 = mmreg v sz in
              let src2 = simd_of_RM Lower_128 rm in
              match pfxs with
              | (T, Rep0, SG0) ->
                SOME (VINSERTI128 dest src1 src2 imm8, l)
              | _ -> NONE)
          else NONE)
        | [0x39:8] ->
          (if word_not v = (word 0b1111:4 word) then
            (if L then
              (let sz = vexL_size L in
              read_ModRM rex l >>= \((reg,rm),l).
              read_imm Byte l >>= \(imm8,l).
              if rex_W rex then NONE else
              let src = mmreg reg sz in
              let dest = simd_of_RM Lower_128 rm in
              match pfxs with
              | (T, Rep0, SG0) -> SOME (VEXTRACTI128 dest src imm8, l)
              | _ -> NONE)
              else NONE)
          else NONE)
        | [0x44:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
          read_imm Byte l >>= \(imm8,l).
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPCLMULQDQ (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm) imm8,l)
           | _ -> NONE)
        | [0x46:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
          read_imm Byte l >>= \(imm8,l).
           if rex_W rex then NONE else
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPERM2I128 (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm) imm8,l)
           | _ -> NONE)
        | [0x4c:8] ->
          let sz = vexL_size L in
          (read_ModRM rex l >>= \((reg,rm),l).
           read_byte l >>= \(imm,l). bitmatch imm with [mask_r:4; lo:4] ->
           if rex_W rex then NONE else
           match pfxs with
           | (T, Rep0, SG0) -> SOME (VPBLENDVB (mmreg reg sz) (mmreg v sz) (simd_of_RM sz rm) (mmreg mask_r sz),l)
           | _ -> NONE)
        | _ -> NONE)
    | _ -> NONE)
  | [0b1100011:7; v] -> if has_unhandled_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
    read_imm (to_wordsize sz) l >>= \(imm,l).
    SOME (MOV rm imm,l)
  | [0b110100:6; x; v] -> if has_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
    if opc = word 6 then NONE else
    let src = if x then %cl else Imm8 (word 1) in
    SOME (decode_binop (rex_reg T opc) rm src,l)
  | [0xe8:8] -> if has_pfxs pfxs then NONE else
    read_int32 l >>= \(w,l).
    SOME (CALL (Imm32 w),l)
  | [0b111010:6; x; 0b1:1] -> if has_pfxs pfxs then NONE else
    read_imm (if x then Byte else Quadword) l >>= \(imm,l).
    SOME (JMP imm,l)
  | [0xf5:8] -> if has_pfxs pfxs then NONE else
    SOME (CMC,l)
  | [0xf8:8] -> if has_pfxs pfxs then NONE else
    SOME (CLC,l)
  | [0xf9:8] -> if has_pfxs pfxs then NONE else
    SOME (STCF,l)
  | [0xfc:8] -> if has_pfxs pfxs then NONE else
    SOME (CLD,l)
  | [0xfd:8] -> if has_pfxs pfxs then NONE else
    SOME (STD,l)
  | [0xf:4; x; 0b11:2; v] -> if has_pfxs pfxs then NONE else
    let sz = op_size_W rex v pfxs in
    read_opcode_ModRM_operand rex sz l >>= \((opc,rm),l).
    decode_hi x v (to_wordsize sz) opc rm l
  | _ -> NONE`;;

let decode = new_definition `decode l =
  read_prefixes l (F, Rep0, SG0) >>= \(p,l).
  let rex,l = read_REX_prefix l in
  decode_aux p rex l`;;

(* ------------------------------------------------------------------------- *)
(* Decode tactics.                                                           *)
(* ------------------------------------------------------------------------- *)

let decode_aux_nil = prove (`decode_aux pfxs rex [] = NONE`,
  REWRITE_TAC [decode_aux; obind; read_byte_val]);;

let decode_aux_tree_A, decode_aux_tree =
  let pth = REWRITE_RULE [read_byte_val; obind]
    (SPECL [`pfxs:pfxs`;`rex:(4 word)option`;`CONS (h:byte) t`] decode_aux) in
  let tm = rhs (concl pth) in
  let cls = bm_analyze_clauses 8 (rand tm) @
    [bm_analyze_pat 8 `BITPAT [0x4:4; rex:4]`] in
  cls, bm_add_pos (map_dt (TRANS pth) (bm_build_tree' 8 cls tm)) tm;;

let decode_no_prefix,read_REX_no_prefix =
  let pth = prove (`!a:A option. a = SOME r ==> a = NONE ==> F`,
    STRIP_TAC THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN (ACCEPT_TAC o
      MATCH_MP (NOT_ELIM (SPEC_ALL OPTION_DISTINCT)) o SYM)) in
  let PROCESS_ASM th = match concl th with
  | Comb(Const("~",_),Comb(Comb(Const("=",_),_),_)) ->
    MATCH_MP_TAC (NOT_ELIM th)
  | Comb(Comb(Const("_UNGUARDED_PATTERN",_),_),_) ->
    ASSUME_TAC (CONJUNCT1 (REWRITE_RULE [_UNGUARDED_PATTERN] th))
  | _ -> ALL_TAC in

  let PROVE_DISJOINT tr th =
    let h = concl th in
    let sz = 8 in
    let a = bm_analyze_pat sz h in
    let stk,(th1,_) = get_dt a tr in
    match rhs (concl th1) with
    | Comb((Comb(Const("_BITMATCH",_),e) as m),cs) as tm ->
      let th1 = itlist (fun _,bit ->
        PROVE_HYP (pat_to_bit true (lhand bit) h)) stk th1 in
      let rec skip_all = function
      | Comb(Comb(Const("_SEQPATTERN",_),c),cs) ->
        let a' = bm_analyze_pat sz c in
        let i =
          let r = ref None in
          Array.iteri (fun i x -> match x,a'.(i),!r with
            | Some b, Some c, None when b != c -> r := Some i
            | _ -> ()) a;
          match !r with
          | Some i -> mk_numeral (num i)
          | _ -> failwith "PROVE_DISJOINT" in
        let th2 = PROVE_HYP (pat_to_bit true i h)
          (bm_skip_clause (pat_to_bit false i) tm) in
        TRANS th2 (skip_all cs)
      | cs -> BM_FIRST_CASE_CONV (mk_comb (m, cs)) in
      PROVE_HYP th (TRANS th1 (skip_all cs))
    | _ -> failwith "PROVE_DISJOINT" in

  prove
   (`!l. decode_aux pfxs rex l = SOME r ==>
     (!p. read_prefixes l p = SOME(p, l)) /\
     read_REX_prefix l = (NONE, l)`,
    LIST_INDUCT_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP pth) THEN
    REWRITE_TAC [decode_aux_nil] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [read_REX_prefix; read_prefixes;
      BITMATCH_SEQPATTERN; BITMATCH_ELSEPATTERN] THEN
    REPEAT (CHANGED_TAC (REWRITE_TAC[]) ORELSE COND_CASES_TAC) THEN
    SUBGOAL_THEN `F` CONTR_TAC THEN REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
    POP_ASSUM_LIST (MAP_EVERY PROCESS_ASM) THEN
    POP_ASSUM (ACCEPT_TAC o PROVE_DISJOINT decode_aux_tree)),
  prove
   (`!l. is_some (FST (read_REX_prefix l)) ==>
     !p. read_prefixes l p = SOME(p, l)`,
    LIST_INDUCT_TAC THENL [REWRITE_TAC[read_REX_prefix; is_some]; ALL_TAC] THEN
    REWRITE_TAC[read_REX_prefix;
      BITMATCH_SEQPATTERN; BITMATCH_ELSEPATTERN] THEN REPEAT STRIP_TAC THEN
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THENL
    [DISCH_THEN (K ALL_TAC); REWRITE_TAC [FST; is_some]] THEN
    REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
    POP_ASSUM PROCESS_ASM THEN REWRITE_TAC [read_prefixes] THEN
    POP_ASSUM (fun th -> CONV_TAC (fun tm ->
      let tm = lhs tm in
      let cls = bm_analyze_clauses 8 (rand tm) @
        [bm_analyze_pat 8 `BITPAT [0x4:4; rex:4]`] in
      PROVE_DISJOINT (bm_add_pos (bm_build_tree' 8 cls tm) tm) th)));;

let HAS_OPERAND_OVERRIDE_CONV =
  let pth = prove
   (`(has_operand_override(T,r) <=> T) /\
     (has_operand_override(F,r) <=> F)`,
    REWRITE_TAC[has_operand_override]) in
  GEN_REWRITE_CONV I [pth];;

let HAS_UNHANDLED_PFXS_CONV =
  let pth = prove
   (`(has_unhandled_pfxs(p,Rep0,SG0) <=> F) /\
     (has_unhandled_pfxs(p,Rep0,CS) <=> T) /\
     (has_unhandled_pfxs(p,Rep0,DS) <=> T) /\
     (has_unhandled_pfxs(p,Rep0,ES) <=> T) /\
     (has_unhandled_pfxs(p,Rep0,SS) <=> T) /\
     (has_unhandled_pfxs(p,RepZ,CS) <=> T) /\
     (has_unhandled_pfxs(p,RepZ,DS) <=> T) /\
     (has_unhandled_pfxs(p,RepZ,ES) <=> T) /\
     (has_unhandled_pfxs(p,RepZ,SS) <=> T) /\
     (has_unhandled_pfxs(p,RepNZ,CS) <=> T) /\
     (has_unhandled_pfxs(p,RepNZ,DS) <=> T) /\
     (has_unhandled_pfxs(p,RepNZ,ES) <=> T) /\
     (has_unhandled_pfxs(p,RepNZ,SS) <=> T)`,
    REWRITE_TAC[has_unhandled_pfxs] THEN
    REWRITE_TAC[distinctness "rep_pfx"] THEN
    REWRITE_TAC[distinctness "seg_pfx"]) in
  GEN_REWRITE_CONV I [pth];;

let READ_VEXM_CONV =
  let pths = Array.init 3 (fun i ->
    let n = mk_comb (`word:num->5 word`, mk_numeral (num (i+1))) in
    CONV_RULE (RAND_CONV BITMATCH_CONV) (SPEC n read_VEXM)) in
  function
  | Comb(Const("read_VEXM",_),Comb(Const("word",_),n)) ->
    (try pths.(Num.int_of_num (dest_numeral n) - 1)
    with Invalid_argument _ -> failwith "READ_VEXM_CONV")
  | _ -> failwith "READ_VEXM_CONV";;

let READ_VEXP_CONV =
  let pths = Array.init 4 (fun i ->
    let n = mk_comb (`word:num->2 word`, mk_numeral (num i)) in
    CONV_RULE (RAND_CONV BITMATCH_CONV) (SPEC n read_VEXP)) in
  function
  | Comb(Const("read_VEXP",_),Comb(Const("word",_),n)) ->
    (try pths.(Num.int_of_num (dest_numeral n))
    with Invalid_argument _ -> failwith "READ_VEXP_CONV")
  | _ -> failwith "READ_VEXP_CONV";;

let DECODE_BT_CONV =
  let pths =
    let th = CONV_RULE (BINDER_CONV(RAND_CONV MATCH_CONV')) decode_BT in
    Array.init 4 (fun i ->
      let n = mk_comb (`word:num->2 word`, mk_numeral (num i)) in
      let th = SPEC n th in
      CONV_RULE (
        REWRITE_CONV [WORD_RED_CONV (mk_comb (`val:2 word->num`, n))] THENC
        ONCE_DEPTH_CONV NUM_EQ_CONV THENC REWRITE_CONV []) th) in
  function
  | Comb(Const("decode_BT",_),Comb(Const("word",_),n)) ->
    (try pths.(Num.int_of_num (dest_numeral n))
    with Invalid_argument _ -> failwith "DECODE_BT_CONV")
  | _ -> failwith "DECODE_BT_CONV";;

let DECODE_BINOP_CONV =
  let pths =
    let th = CONV_RULE (BINDER_CONV(RAND_CONV MATCH_CONV')) decode_binop in
    Array.init 16 (fun i ->
      let n = mk_comb (`word:num->4 word`, mk_numeral (num i)) in
      let th = SPEC n th in
      CONV_RULE (
        REWRITE_CONV [WORD_RED_CONV (mk_comb (`val:4 word->num`, n))] THENC
        ONCE_DEPTH_CONV NUM_EQ_CONV THENC REWRITE_CONV []) th) in
  function
  | Comb(Const("decode_binop",_),Comb(Const("word",_),n)) ->
    (try pths.(Num.int_of_num (dest_numeral n))
    with Invalid_argument _ -> failwith "DECODE_BINOP_CONV")
  | _ -> failwith "DECODE_BINOP_CONV";;

let CONDITION_ALIAS_thms,DECODE_CONDITION_CONV =
  let pths =
    let th = CONV_RULE (BINDER_CONV(RAND_CONV MATCH_CONV')) decode_condition in
    Array.init 16 (fun i ->
      let n = mk_comb (`word:num->4 word`, mk_numeral (num i)) in
      let th = SPEC n th in
      CONV_RULE (
        REWRITE_CONV [WORD_RED_CONV (mk_comb (`val:4 word->num`, n))] THENC
        ONCE_DEPTH_CONV NUM_EQ_CONV THENC REWRITE_CONV []) th)
  and cmovs = [|CMOVO; CMOVNO; CMOVB; CMOVAE; CMOVE; CMOVNE; CMOVBE; CMOVA;
                CMOVS; CMOVNS; CMOVP; CMOVNP; CMOVL; CMOVGE; CMOVLE; CMOVG|]
  and jumps = [|JO; JNO; JB; JAE; JE; JNE; JBE; JA;
                JS; JNS; JP; JNP; JL; JGE; JLE; JG|]
  and sets =  [|SETO; SETNO; SETB; SETAE; SETE; SETNE; SETBE; SETA;
                SETS; SETNS; SETP; SETNP; SETL; SETGE; SETLE; SETG|] in
  let uncond A = function
  | Comb(Const("decode_condition",_),Comb(Const("word",_),n)) ->
    (try A.(Num.int_of_num (dest_numeral n))
    with Invalid_argument _ -> failwith "DECODE_CONDITION_CONV")
  | _ -> failwith "DECODE_CONDITION_CONV" in
  flat (map (fun A ->
    let l = Array.to_list A in
    let f i th = TRANS (AP_TERM (rator (rhs (concl th))) pths.(i)) (SYM th) in
    let _ = Array.iteri (fun i th -> A.(i) <- f i th) A in
    l) [cmovs;jumps;sets]),
  function
  | Comb(Const("CMOV",_),e) -> uncond cmovs e
  | Comb(Const("JUMP",_),e) -> uncond jumps e
  | Comb(Const("SET",_),e) -> uncond sets e
  | e -> uncond pths e;;

let WORD_ZX_34_CONV =
  let ty = `:3 word->4 word` in
  let pths = Array.init 8 (fun i -> WORD_RED_CONV
    (vsubst [mk_numeral (num i),`i:num`] `word_zx (word i:3 word):4 word`)) in
  function
  | Comb(Const("word_zx",ty'),Comb(Const("word",_),n)) as tm ->
    if ty' = ty then
      try pths.(Num.int_of_num (dest_numeral n))
      with Invalid_argument _ -> failwith "WORD_ZX_34_CONV"
    else WORD_RED_CONV tm
  | _ -> failwith "WORD_ZX_34_CONV";;

let bool_split pth =
  let pthT = pth `T` and pthF = pth `F` in
  function
  | Const("T",_) -> pthT
  | Const("F",_) -> pthF
  | e -> failwith "bool_split";;

let REGSIZE8_CONV =
  let pth = bool_split (fun x ->
    REWRITE_CONV [regsize8] (mk_comb (`regsize8`, x))) in
  function
  | Comb(Const("regsize8",_),x) -> pth x
  | _ -> failwith "REGSIZE8_CONV";;

let OP_SIZE_CONV =
  let pth0,pth1 = (CONJ_PAIR o prove)
    (`(op_size F F F p = Upper_8 /\
       op_size F T F p = Upper_8 /\
       op_size F T T p = Full_64 /\
       op_size T F F p = Lower_8 /\
       op_size T T F p = Lower_8 /\
       op_size T T T p = Full_64) /\
      op_size r F T p =
      (if has_operand_override p then Lower_16 else Lower_32)`,
     REWRITE_TAC[op_size; regsize8]) in
  GEN_REWRITE_CONV I [pth0] ORELSEC
  (GEN_REWRITE_CONV I [pth1] THENC
   RATOR_CONV(LAND_CONV HAS_OPERAND_OVERRIDE_CONV) THENC
   GEN_REWRITE_CONV I [COND_CLAUSES]);;

let rec OP_SIZE_W_CONV =
  let pth1 = (REWRITE_CONV [op_size_W; is_some; rex_W; rex_num] THENC
    DEPTH_CONV WORD_BIT_CONV) `op_size_W NONE`
  and pth2 =
    let pth = REWRITE_CONV [op_size_W; is_some; rex_W; rex_num]
      `op_size_W (SOME (word n))` in
    Array.init 16 (fun i ->
      let th = INST [mk_numeral (num i),`n:num`] pth in
      TRANS th (RAND_CONV WORD_BIT_CONV (rhs (concl th)))) in
  function
  | Comb(Const("op_size_W",_),Const("NONE",_)) -> pth1
  | Comb(Const("op_size_W",_),Comb(Const("SOME",_),Comb(Const("word",_),n))) ->
    pth2.(Num.int_of_num (dest_numeral n))
  | Comb(Comb(Const("op_size_W",_),_),_) as tm ->
    (RATOR_CONV OP_SIZE_W_CONV) tm
  | Comb(Comb(Comb(Const("op_size_W",_),_),_),_) as tm ->
    (RATOR_CONV(RATOR_CONV OP_SIZE_W_CONV) THENC OP_SIZE_CONV) tm
  | _ -> failwith "OP_SIZE_W_CONV";;

let REX_REG_CONV =
  let pths = bool_split (fun b ->
    Array.init 8 (fun i ->
      let n = mk_comb (`word:num->3 word`, mk_numeral (num i)) in
      let th = SPECL [b; n] rex_reg in
      CONV_RULE (REWRITE_CONV [word_join; word1; bitval] THENC REDEPTH_CONV
        (WORD_RED_CONV ORELSEC DIMINDEX_CONV ORELSEC NUM_RED_CONV)) th)) in
  function
  | Comb(Comb(Const("rex_reg",_),b),Comb(Const("word",_),n)) ->
    (try (pths b).(Num.int_of_num (dest_numeral n))
    with Invalid_argument _ -> failwith "REX_REG_CONV")
  | e -> failwith ("REX_REG_CONV " ^ string_of_term e);;

let REX_BIT_CONV =
  let none = mk_const ("NONE",[`:4 word`,aty])
  and some = mk_const ("SOME",[`:4 word`,aty])
  and word = mk_const ("word",[`:4`,`:N`])
  and conv = CONV_RULE (DEPTH_CONV WORD_BIT_CONV) o REWRITE_RULE [rex_num] in
  let mk_conv dth =
    let pth1 = conv (SPEC none dth)
    and pth2 = Array.init 16 (fun i ->
      conv (SPEC (mk_comb (some, mk_comb (word, mk_numeral (num i)))) dth)) in
    function
    | Const("NONE",_) -> pth1
    | Comb(Const("SOME",_),Comb(Const("word",_),n)) ->
      pth2.(Num.int_of_num (dest_numeral n))
    | _ -> failwith "REX_BIT_CONV" in
  let fB = mk_conv rex_B
  and fX = mk_conv rex_X
  and fR = mk_conv rex_R
  and fW = mk_conv rex_W in
  function
  | Comb(Const("rex_B",_),e) -> fB e
  | Comb(Const("rex_X",_),e) -> fX e
  | Comb(Const("rex_R",_),e) -> fR e
  | Comb(Const("rex_W",_),e) -> fW e
  | _ -> failwith "REX_BIT_CONV";;

let regsize_DISTINCT = prove_constructors_distinct regsize_RECURSION;;

let GPR_thms,GPR_CONV =
  let c64 = [|rax; rcx; rdx; rbx; rsp; rbp; rsi; rdi;
               r8;  r9; r10; r11; r12; r13; r14; r15|]
  and c32 = [|eax; ecx; edx; ebx; esp; ebp; esi; edi;
              r8d; r9d;r10d;r11d;r12d;r13d;r14d;r15d|]
  and c16 = [|ax;cx;dx;bx;sp;bp;si;di;
              r8w;r9w;r10w;r11w;r12w;r13w;r14w;r15w|]
  and u8  = [|ah;ch;dh;bh|]
  and c8  = [|al;cl;dl;bl;spl;bpl;sil;dil;
              r8b;r9b;r10b;r11b;r12b;r13b;r14b;r15b|] in
  flat (map (fun A ->
    let l = Array.to_list A in
    Array.iteri (fun i th -> A.(i) <- SYM th) A; l) [c64;c32;c16;u8;c8]),
  function
  | Comb(Comb(Const("Gpr",_),Comb(Const("word",_),i)),Const(sz,_)) ->
    let i' = Num.int_of_num (dest_numeral i) in
    (match sz with
    | "Full_64"  -> c64.(i')
    | "Lower_32" -> c32.(i')
    | "Lower_16" -> c16.(i')
    | "Lower_8"  -> c8.(i')
    | "Upper_8"  -> u8.(i')
    | _ -> failwith "GPR_CONV")
  | _ -> failwith "GPR_CONV";;

let simdregsize_DISTINCT = prove_constructors_distinct simdregsize_RECURSION;;

let SIMDREG_thms,SIMDREG_CONV =
  let c512 = [|zmm0; zmm1; zmm2; zmm3; zmm4; zmm5; zmm6; zmm7; zmm8; zmm9;
               zmm10; zmm11; zmm12; zmm13; zmm14; zmm15; zmm16; zmm17;
               zmm18; zmm19; zmm20; zmm21; zmm22; zmm23; zmm24; zmm25;
               zmm26; zmm27; zmm28; zmm29; zmm30; zmm31|]
  and c256 = [|ymm0; ymm1; ymm2; ymm3; ymm4; ymm5; ymm6; ymm7; ymm8; ymm9;
               ymm10; ymm11; ymm12; ymm13; ymm14; ymm15|]
  and c128 = [|xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7; xmm8; xmm9;
               xmm10; xmm11; xmm12; xmm13; xmm14; xmm15|] in
  flat (map (fun A ->
    let l = Array.to_list A in
    Array.iteri (fun i th -> A.(i) <- SYM th) A; l) [c512;c256;c128]),
  function
  | Comb(Comb(Const("Simdreg",_),Comb(Const("word",_),i)),Const(sz,_)) ->
    let i' = Num.int_of_num (dest_numeral i) in
    (match sz with
    | "Full_512"  -> c512.(i')
    | "Lower_256" -> c256.(i')
    | "Lower_128" -> c128.(i')
    | _ -> failwith "SIMDREG_CONV")
  | _ -> failwith "SIMDREG_CONV";;

let BSID_CONV =
  let bd = SYM base_displacement
  and bsi = SYM base_scaled_index
  and bsid = (UNDISCH o prove) (`ival n = d ==>
    Bsid (SOME r) (SOME i) (word s) n = %%%%(r,s,i,d)`,
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [base_scaled_index_displacement; IWORD_IVAL])
  and ival = mk_const ("ival", [`:64`,`:N`]) in

  function
  | Comb(Comb(Comb(Comb(Const("Bsid",_),Comb(Const("SOME",_),r)),
      Const("NONE",_)),Comb(Const("word",_),s)),Comb(Const("word",_),d))
      when dest_numeral s = num 0 ->
    INST [r,`r:gpr`; d,`d:num`] bd
  | Comb(Comb(Comb(Comb(Const("Bsid",_),
      Comb(Const("SOME",_),r)), Comb(Const("SOME",_),i)),
      Comb(Const("word",_),s)), (Comb(Const("word",_),d) as n)) ->
    let d' = dest_numeral d in
    if d' = num 0 then
      INST [r,`r:gpr`; s,`s:num`; i,`i:gpr`] bsi
    else
      let th = WORD_RED_CONV (mk_comb (ival, n)) in
      let d = rhs (concl th) in
      PROVE_HYP th (INST [r,`r:gpr`; s,`s:num`;
        i,`i:gpr`; n,`n:64 word`; d,`d:int`] bsid)
  | Comb(Comb(Comb(Comb(Const("Bsid",_),_),_),_),_) as t -> REFL t
  | _ -> failwith "BSID_CONV";;

let regsize_constructors =
  map rand (conjuncts (lhand (body (rand (concl regsize_INDUCT)))));;

let GPR_ADJUST_CONV =
  let word = mk_const ("word",[`:4`,`:N`])
  and reg = `reg:4 word` in
  let [c64;c32;c16;u8;c8] = map (fun c ->
    REWRITE_RULE [regsize_DISTINCT]
      (CONV_RULE (DEPTH_CONV let_CONV) (SPEC_ALL (SPEC c gpr_adjust))))
    regsize_constructors in
  let u8 = Array.init 8 (fun i ->
    CONV_RULE (REDEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV))
      (INST [mk_comb (word, mk_numeral (num i)),reg] u8)) in
  (function
  | Comb(Comb(Const("gpr_adjust",_),reg'),Const(sz,_)) -> (match sz with
    | "Full_64"  -> INST [reg',reg] c64
    | "Lower_32" -> INST [reg',reg] c32
    | "Lower_16" -> INST [reg',reg] c16
    | "Lower_8"  -> INST [reg',reg] c8
    | "Upper_8"  -> u8.(Num.int_of_num (dest_numeral (rand reg')))
    | _ -> failwith "GPR_ADJUST_CONV")
  | _ -> failwith "GPR_ADJUST_CONV") THENC GPR_CONV;;

let ADX_CONV =
  let pths = map (fun th -> rand (lhs (concl th)), th) (CONJUNCTS adx) in
  function
  | Comb(Const("adx",_),v) ->
    (try assoc v pths
    with Failure _ -> failwith "ADX_CONV")
  | _ -> failwith "ADX_CONV";;

let TO_WORDSIZE_CONV =
  let pths = map (fun th -> rand (lhs (concl th)), th)
    (CONJUNCTS to_wordsize) in
  function
  | Comb(Const("to_wordsize",_),v) ->
    (try assoc v pths
    with Failure _ -> failwith "TO_WORDSIZE_CONV")
  | _ -> failwith "TO_WORDSIZE_CONV";;

let SIMD_TO_WORDSIZE_CONV =
  let pths = map (fun th -> rand (lhs (concl th)), th)
    (CONJUNCTS simd_to_wordsize) in
  function
  | Comb(Const("simd_to_wordsize",_),v) ->
    (try assoc v pths
    with Failure _ -> failwith "SIMD_TO_WORDSIZE_CONV")
  | _ -> failwith "SIMD_TO_WORDSIZE_CONV";;

let VEXL_SIZE_CONV =
  let pths = map (fun th -> rand (lhs (concl th)), th)
    (CONJUNCTS vexL_size) in
  function
  | Comb(Const("vexL_size",_),v) ->
    (try assoc v pths
    with Failure _ -> failwith "VEXL_SIZE_CONV")
  | _ -> failwith "VEXL_SIZE_CONV";;

let operand_of_RM = define
 `(!reg. operand_of_RM sz (RM_reg reg) = %(gpr_adjust reg sz)) /\
  (!ea. operand_of_RM sz (RM_mem ea) = Memop (to_wordsize sz) ea)`;;

let OPERAND_OF_RM_CONV =
  let ga,ws,sz,sz2 = `gpr_adjust`,`to_wordsize`,`sz:regsize`,`sz2:wordsize`
  and reg,gpr,ea = `reg:4 word`,`gpr:gpr`,`ea:bsid`
  and pth1 = (UNDISCH o prove)
    (`gpr_adjust reg sz = gpr ==> operand_of_RM sz (RM_reg reg) = %gpr`,
      DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [operand_of_RM])
  and pth2 = (UNDISCH o prove)
  (`to_wordsize sz = sz2 ==> operand_of_RM sz (RM_mem ea) = Memop sz2 ea`,
    DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [operand_of_RM]) in
  function
  | Comb(Comb(Const("operand_of_RM",_),sz'),Comb(Const("RM_reg",_),reg')) ->
    let th = GPR_ADJUST_CONV (mk_comb (mk_comb (ga, reg'), sz')) in
    PROVE_HYP th (INST [sz',sz; reg',reg; rhs (concl th),gpr] pth1)
  | Comb(Comb(Const("operand_of_RM",_),sz'),Comb(Const("RM_mem",_),ea')) ->
    let th = TO_WORDSIZE_CONV (mk_comb (ws, sz')) in
    PROVE_HYP th (INST [sz',sz; ea',ea; rhs (concl th),sz2] pth2)
  | _ -> failwith "OPERAND_OF_RM_CONV";;

let SIMD_OF_RM_CONV =
  let conv1 =
    GEN_REWRITE_CONV I [CONJUNCT1 simd_of_RM] THENC
    RAND_CONV(LAND_CONV WORD_ZX_CONV THENC SIMDREG_CONV)
  and conv2 =
    GEN_REWRITE_CONV I [CONJUNCT2 simd_of_RM] THENC
    LAND_CONV SIMD_TO_WORDSIZE_CONV in
  fun tm -> match tm with
  | Comb(Comb(Const("simd_of_RM",_),sz'),Comb(Const("RM_reg",_),reg')) ->
    conv1 tm
  | Comb(Comb(Const("simd_of_RM",_),sz'),Comb(Const("RM_mem",_),ea')) ->
    conv2 tm
  | _ -> failwith "OPERAND_OF_RM_CONV";;

let IS_MEMOP_CONV = GEN_REWRITE_CONV I [is_memop];;

let MMREG_CONV =
  let conv =
    GEN_REWRITE_CONV I [mmreg] THENC
    RAND_CONV(LAND_CONV WORD_ZX_CONV THENC SIMDREG_CONV) in
  fun tm -> match tm with
  | Comb(Comb(Const("mmreg",_),_),_) -> conv tm
  | _ -> failwith "MMREG_CONV";;

let decode' = new_definition `decode' p rex l =
  if is_some rex then decode_aux p rex l else
  read_prefixes l p >>= \(p,l).
  let rex,l = read_REX_prefix l in
  decode_aux p rex l`;;

let decode_eq_decode' = prove (`decode = decode' (F, Rep0, SG0) NONE`,
  REWRITE_TAC [FUN_EQ_THM; decode'; decode; is_some]);;

let decode'_read_prefix = prove
 (`read_prefixes l p = read_prefixes l' p' ==>
   decode' p NONE l = decode' p' NONE l'`,
  DISCH_THEN (fun th -> REWRITE_TAC [decode'; is_some; th]));;

let decode'_opo = prove
 (`decode' (opo, rep, seg) NONE (CONS (word 0x66) l) =
   decode' (T, rep, seg) NONE l`,
  MATCH_MP_TAC decode'_read_prefix THEN
  REWRITE_TAC [read_prefixes] THEN
  CONV_TAC (LAND_CONV BITMATCH_CONV) THEN
  REWRITE_TAC [pfxs_set_opo; obind]);;

let decode'_repz = prove
 (`decode' (opo, Rep0, seg) NONE (CONS (word 0xf3) l) =
   decode' (opo, RepZ, seg) NONE l`,
  MATCH_MP_TAC decode'_read_prefix THEN
  REWRITE_TAC [read_prefixes] THEN
  CONV_TAC (LAND_CONV BITMATCH_CONV) THEN
  REWRITE_TAC [pfxs_set_repz; obind]);;

let decode'_repnz = prove
 (`decode' (opo, Rep0, seg) NONE (CONS (word 0xf2) l) =
   decode' (opo, RepNZ, seg) NONE l`,
  MATCH_MP_TAC decode'_read_prefix THEN
  REWRITE_TAC [read_prefixes] THEN
  CONV_TAC (LAND_CONV BITMATCH_CONV) THEN
  REWRITE_TAC [pfxs_set_repnz; obind]);;

let decode'_cs = prove
 (`decode' (opo, rep, SG0) NONE (CONS (word 0x2e) l) =
   decode' (opo, rep, CS) NONE l`,
  MATCH_MP_TAC decode'_read_prefix THEN
  REWRITE_TAC [read_prefixes] THEN
  CONV_TAC (LAND_CONV BITMATCH_CONV) THEN
  REWRITE_TAC [pfxs_set_cs; obind]);;

let decode'_ds = prove
 (`decode' (opo, rep, SG0) NONE (CONS (word 0x3e) l) =
   decode' (opo, rep, DS) NONE l`,
  MATCH_MP_TAC decode'_read_prefix THEN
  REWRITE_TAC [read_prefixes] THEN
  CONV_TAC (LAND_CONV BITMATCH_CONV) THEN
  REWRITE_TAC [pfxs_set_ds; obind]);;

let decode'_es = prove
 (`decode' (opo, rep, SG0) NONE (CONS (word 0x26) l) =
   decode' (opo, rep, ES) NONE l`,
  MATCH_MP_TAC decode'_read_prefix THEN
  REWRITE_TAC [read_prefixes] THEN
  CONV_TAC (LAND_CONV BITMATCH_CONV) THEN
  REWRITE_TAC [pfxs_set_es; obind]);;

let decode'_ss = prove
 (`decode' (opo, rep, SG0) NONE (CONS (word 0x36) l) =
   decode' (opo, rep, SS) NONE l`,
  MATCH_MP_TAC decode'_read_prefix THEN
  REWRITE_TAC [read_prefixes] THEN
  CONV_TAC (LAND_CONV BITMATCH_CONV) THEN
  REWRITE_TAC [pfxs_set_ss; obind]);;

let decode'_rex = prove
 (`pat_set (BITPAT [0x4:4; rex:4]) (val a) ==>
   decode' pfxs NONE (CONS a l) = decode' pfxs (SOME rex) l`,
  DISCH_TAC THEN REWRITE_TAC [decode'; is_some] THEN
  SUBGOAL_THEN `read_REX_prefix (CONS a l) = (SOME rex, l)` ASSUME_TAC THENL
  [REWRITE_TAC [read_REX_prefix] THEN CONV_TAC (BM_FIRST_CASE_CONV o lhs);
   IMP_REWRITE_TAC [read_REX_no_prefix; obind; is_some] THEN
   CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN REFL_TAC]);;

let decode'_of_aux = prove
 (`decode_aux pfxs rex l = SOME v ==> decode' pfxs rex l = SOME v`,
  SPEC1_TAC `rex:(4 word)option` THEN MATCH_MP_TAC option_INDUCT THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [is_some; decode'] THEN
  POP_ASSUM (fun th ->
    REWRITE_TAC [MATCH_MP decode_no_prefix th; obind] THEN
    CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC [th]));;

let read_disp_thms =
  let word2 = mk_const ("word", [`:2`,`:N`]) in
  let th = CONV_RULE (BINDER_CONV(BINDER_CONV(RAND_CONV MATCH_CONV'))) read_displacement in
  let A = Array.init 3 (fun md ->
    let md' = mk_comb (word2, mk_numeral (num md)) in
    let th = SPEC_ALL (SPEC md' th) in
    CONV_RULE (
      REWRITE_CONV [WORD_RED_CONV (mk_comb (`val:2 word->num`, md'))] THENC
      ONCE_DEPTH_CONV NUM_EQ_CONV THENC REWRITE_CONV []) th) in
  fun i -> A.(i);;

let mk_sib_disp_thm =
  let word2 = mk_const ("word", [`:2`,`:N`])
  and word4 = mk_const ("word", [`:4`,`:N`]) in
  fun md ->
    let md' = mk_comb (word2, mk_numeral (num md)) in
    let th = CONV_RULE
      (ONCE_DEPTH_CONV WORD_RED_CONV THENC
       REWRITE_CONV [read_disp_thms md; obind])
      (SPEC_ALL (SPEC md' read_sib_displacement)) in
    let conv = ONCE_DEPTH_CONV (WORD_RED_CONV ORELSEC GPR_CONV) THENC
      REWRITE_CONV [] in
    fun reg ->
      let reg' = mk_comb (word4, mk_numeral (num reg)) in
      CONV_RULE conv (INST [reg',`reg:4 word`] th);;

let mk_decode_hi_thms =
  let ifif = prove
    (`(if p then if p then a:A else b else c) = if p then a else c`,
     COND_CASES_TAC THEN REWRITE_TAC []) in
  let pth = CONV_RULE (REDEPTH_CONV MATCH_CONV THENC REWRITE_CONV [ifif])
    (SPEC_ALL decode_hi) in
  let word,vl = `word:num->3 word`,`val:3 word->num` in
  fun x ->
    let pth = REWRITE_RULE [ifif] (INST [x,`x:bool`] pth) in
    fun opc ->
      let opc' = mk_comb (word, mk_numeral (num opc)) in
      CONV_RULE
        (REWRITE_CONV [WORD_RED_CONV (mk_comb (vl, opc'))] THENC
          ONCE_DEPTH_CONV NUM_RED_CONV THENC REWRITE_CONV [])
        (INST [opc',`opc:3 word`] pth);;

let READ_SIB_CONV,READ_MODRM_CONV,READ_VEX_CONV,DECODE_CONV =
  let constructors =
    let constructors_of =
      let rec f = function
      | Const(s,_) -> s
      | Comb(tm,_) -> f tm
      | _ -> failwith "constructors_of" in
      map (f o rand o snd o strip_forall) o
      conjuncts o lhand o snd o dest_forall o concl in
    ["T";"F";",";"NONE";"SOME"] @
    ["%%";"%%%";"%%%%";"##"] @
    ["IMUL"; "JMP"] @
    constructors_of instruction_INDUCTION @
    constructors_of operand_INDUCTION @
    constructors_of rep_pfx_INDUCTION @
    constructors_of seg_pfx_INDUCTION @
    constructors_of RM_INDUCTION @
    constructors_of VEXM_INDUCTION @
    constructors_of regsize_INDUCT @
    constructors_of simdregsize_INDUCT @
    constructors_of wordsize_INDUCT @
    map (fst o dest_const o lhs o concl) GPR_thms @
    map (fst o dest_const o lhs o concl) SIMDREG_thms @
    map (fst o dest_const o lhs o concl) CONDITION_ALIAS_thms in

  let genvar =
    let gcounter = ref 0 in
    fun ty ->
      let count = !gcounter in
      (gcounter := count + 1;
      mk_var ("eval%"^(string_of_int count), ty)) in

  let pth_obind = (UNDISCH o prove)
   (`f = SOME (a:A) ==> (f >>= g) = g a:B option`,
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [obind])
  and pth_cond_T = (UNDISCH o prove)
   (`p = T ==> (if p then a else b:A) = a`,
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [])
  and pth_cond_F = (UNDISCH o prove)
   (`p = F ==> (if p then a else b:A) = b`,
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [])
  and pfxs0 = `F, Rep0, SG0`
  and pth_has_pfxs = (UNDISCH o prove)
   (`pfxs = (F, Rep0, SG0) ==> (if has_pfxs pfxs then NONE else a) = a: A option`,
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [has_pfxs])
  and pth_rmo =
    let th = SPEC_ALL read_ModRM_operand in
    let Comb(Comb(Comb(_,rex),sz),l) = lhs (concl th) in
    fun rex' sz' l' -> INST [rex',rex; sz',sz; l',l] th
  and pth_romo =
    let th = SPEC_ALL read_opcode_ModRM_operand in
    let Comb(Comb(Comb(_,rex),sz),l) = lhs (concl th) in
    fun rex' sz' l' -> INST [rex',rex; sz',sz; l',l] th
  and pth_rom =
    let th = SPEC_ALL read_opcode_ModRM in
    let Comb(Comb(_,rex),l) = lhs (concl th) in
    fun rex' l' -> INST [rex',rex; l',l] th
  and rep_pfx_constructors = [`Rep0`; `RepZ`; `RepNZ`]
  and seg_pfx_constructors = [`SG0`; `CS`; `SS`; `DS`; `ES`]
  and VEXM_constructors = [`VEXM_0F`; `VEXM_0F38`; `VEXM_0F3A`] in

  let rec eval_prod = function
  | Tyapp("prod",[A;B]) ->
    let tm1, f1 = eval_prod A in
    let tm2, f2 = eval_prod B in
    mk_pair (tm1, tm2),
    (function
    | Comb(Comb(Const(",",_),t1'),t2'),ls -> f1 (t1', f2 (t2', ls))
    | _ -> failwith "eval_prod")
  | A -> let v = genvar A in v, fun e,ls -> (e,v)::ls in

  let delay_if b t k conv =
    if b then
      let x, f = eval_prod (type_of t) in
      let g = k (ASSUME (mk_eq (t, x))) in
      fun ls ->
        let th' = conv (vsubst ls t) in
        PROVE_HYP th' (g (f (rhs (concl th'), ls)))
    else k (conv t)

  and eval_opt =
    let some = mk_const ("SOME", []) in
    fun tm F conv -> match type_of tm with
    | Tyapp("option",[A]) ->
      let tm', f = eval_prod A in
      let g = F (ASSUME (mk_eq (tm, mk_comb (inst [A,aty] some, tm')))) in
      fun ls ->
        let th = conv (vsubst ls tm) in
        (match rhs (concl th) with
        | Comb(Const("SOME",_),tm1) -> PROVE_HYP th (g (f (tm1, ls)))
        | Const("NONE",_) -> failwith "eval_opt got NONE"
        | _ -> failwith "eval_opt")
    | ty -> failwith ("eval_opt " ^ string_of_type ty) in

  let read_imm_func = (* overwritten below *)
    ref ((fun _ _ -> failwith "evaluate read_imm failed"),
         (fun _ _ -> failwith "evaluate read_full_imm failed"))
  and read_disp_func = (* overwritten below *)
    ref (fun _ _ -> failwith "evaluate read_displacement failed")
  and sib_disp_func = (* overwritten below *)
    ref (fun _ _ _ -> failwith "evaluate read_sib_displacement failed")
  and sib_func = (* overwritten below *)
    ref (fun _ -> failwith "evaluate read_SIB failed")
  and modRM_table = (* overwritten below *)
    Array.make 256 (fun _ -> failwith "evaluate read_ModRM failed")
  and read_vex_func = (* overwritten below *)
    ref ((fun _ -> failwith "evaluate read_VEX failed"),
         (fun _ -> failwith "evaluate read_VEX failed"))
  and decode_hi_func = (* overwritten below *)
    Array.make 8 (fun _ -> failwith "evaluate decode_hi failed"),
    Array.make 8 (fun _ -> failwith "evaluate decode_hi failed") in

  let READ_IMM_CONV = function
  | Comb(Comb(Const("read_imm",_),a),l) ->
    fst !read_imm_func a [l,`l:byte list`]
  | Comb(Comb(Const("read_full_imm",_),a),l) ->
    snd !read_imm_func a [l,`l:byte list`]
  | _ -> failwith "READ_IMM_CONV" in

  let READ_DISP_CONV = function
  | Comb(Comb(Const("read_displacement",_),Comb(Const("word",_),md)),l) ->
    !read_disp_func md [l,`l:byte list`]
  | _ -> failwith "READ_DISP_CONV" in

  let READ_SIB_CONV = function
  | Comb(Comb(Comb(Const("read_sib_displacement",_),
      Comb(Const("word",_),md)),Comb(Const("word",_),reg)),l) ->
    !sib_disp_func md reg [l,`l:byte list`]
  | Comb(Comb(Comb(Const("read_SIB",_),rex),md),
      Comb(Comb(Const("CONS",_),b),l)) ->
    !sib_func [b,`b:byte`; rex,`rex:(4 word)option`;
      md,`md:2 word`; l,`l:byte list`]
  | _ -> failwith "READ_SIB_CONV" in

  let READ_MODRM_CONV = function
  | Comb(Comb(Const("read_ModRM",_),rex),
      Comb(Comb(Const("CONS",_),Comb(Const("word",_),a)),l)) ->
    modRM_table.(Num.int_of_num (dest_numeral a))
      [rex,`rex:(4 word)option`; l,`l:byte list`]
  | _ -> failwith "READ_MODRM_CONV" in

  let READ_VEX_CONV = function
  | Comb(Comb(Const("read_VEX",_),Const("T",_)),l) ->
    fst !read_vex_func [l,`l:byte list`]
  | Comb(Comb(Const("read_VEX",_),Const("F",_)),l) ->
    snd !read_vex_func [l,`l:byte list`]
  | _ -> failwith "READ_VEX_CONV" in

  let DECODE_HI_CONV = function
  | Comb(Comb(Comb(Comb(Comb(Comb(Const("decode_hi",_),x),v),sz),
      Comb(Const("word",_),opc)),rm),l) ->
    (match x with
    | Const("T",_) -> fst decode_hi_func
    | Const("F",_) -> snd decode_hi_func
    | _ -> failwith "DECODE_HI_CONV")
      .(Num.int_of_num (dest_numeral opc))
      [sz,`sz:wordsize`; v,`v:bool`; rm,`rm:operand`; l,`l:byte list`]
  | _ -> failwith "DECODE_HI_CONV" in

  (* A wrapper function of the 'evaluate' function defined below.
     If decode_print_log reference variable is assigned true, this will print the
     current evaluation context and the term that is being reduced. *)
  let log_step =
    let print_assignments (ls:(term * term) list): unit =
      Printf.printf "  (assignments: [\n%s])\n%!"
        (String.concat "\n" (List.map
            (fun (t,x) ->
              "    - " ^ (string_of_term x) ^ " -> " ^ (string_of_term t))
              ls))
    in
    let eval_fresh_id = ref 0 in

    (* The main logger function.
      - 'op' is the current evaluation context and fn will print it
      - 'evaluate' must be the 'evaluate' function defined later.
      - 't_focus' and 'F' are the two arguments that the 'evaluate' function
        receive. *)
    let fn (op:string) (evaluate:term -> (thm -> (term * term) list -> thm)
                                      -> (term * term) list -> thm)
        (t_focus:term) (F:thm -> (term * term) list -> thm) =
      let eval_id = !eval_fresh_id in
      let _ = eval_fresh_id := 1 + eval_id in

      let eval_simplified = evaluate t_focus (fun th ->
        let f_partialeval = F th in
        fun ls ->
          if not !decode_print_log then f_partialeval ls else
          let _ = Printf.printf "decode: evaluate (\"%s\", eval id %d):"
            op eval_id in
          let _ = Printf.printf " evaluated to (assigns deferred): `%s`\n%!"
            (string_of_term (rhs (concl th))) in
          let _ = print_assignments ls in
          f_partialeval ls) in
      fun ls ->
        if not !decode_print_log then eval_simplified ls else
        let _ = Printf.printf "decode: evaluate (\"%s\", eval id %d):"
            op eval_id in
        let _ = Printf.printf " evaluating: `%s`\n%!"
            (string_of_term t_focus) in
        let _ = print_assignments ls in
        eval_simplified ls
    in fn
  in

 (* Evaluates term t in a continuation-passing style. The continuation
     'F thm binding' takes (1) thm: a rewrite rule that describes the
     equality `e = v` where `e` was the previous expression and `v` is the
     result of evaluation (2) binding: a list of free variables and
     their values.
     To understand this function further, you can start with the "LET"
     case which is HOL Light's let binding `let x = e1 in e2` that
     (1) evaluates e1, (2) takes `|- e1 = v1` and evaluates e2.
     The benefit of using this continuation-passing style over repetitively
     applying rewriting rules is its speed.
     To understand the data structure of HOL Light's terms, you will want
     to disable the term printer in OCaml REPL via
     "#remove_printer pp_print_qterm;;". This can be enabled by
     "#disable_printer pp_print_qterm;;" again. *)

  let rec evaluate t (F:thm->(term*term)list->thm): (term * term) list -> thm =
    match t with
  | Comb(Comb(Const(">>=",_),f),g) ->
    log_step "[e1] >>= e2" evaluate f (fun th ->
      match rhs (concl th) with
      | Comb(Const("SOME",_),a) ->
        let A,B = match type_of g with
        | Tyapp(_,[A;Tyapp(_,[B])]) -> A,B | _ -> fail() in
        let th' = PROVE_HYP th (PINST [A,aty; B,bty]
          [f,`f:A option`; a,`a:A`; g,`g:A->B option`] pth_obind) in
        log_step "v1 >>= [e2]" evaluate (rhs (concl th')) (F o TRANS th')
      | _ -> failwith "evaluate >>= did not get SOME a")
  | Comb(Comb(Comb(Const("COND",_),
      Comb(Const("has_pfxs",_),pfxs)),Const("NONE",Tyapp(_,[A]))),a) ->
    let th = PINST [A,aty] [pfxs,`pfxs:pfxs`; a,`a:A option`] pth_has_pfxs in
    let g = log_step "if has_pfxs pfxs then NONE else [ ]"
                     evaluate a (F o TRANS th) in
    fun ls ->
      if vsubst ls pfxs = pfxs0 then
        PROVE_HYP (REFL pfxs0) (g ls)
      else failwith "evaluate 'if has_pfxs pfxs then NONE...' failed"
  | Comb(Comb(Comb(Const("COND",_),e),a),b) ->
    log_step "if [e1] then e2 else e3" evaluate e (fun th ->
      let A = type_of a in
      let inst = PINST [A, aty] [e,`p:bool`; a,`a:A`; b,`b:A`] in
      match rhs (concl th) with
      | Const("T",_) ->
        log_step "if T then [e2] else e3" evaluate a
            (F o TRANS (PROVE_HYP th (inst pth_cond_T)))
      | Const("F",_) ->
        log_step "if F then e2 else [e3]" evaluate b
            (F o TRANS (PROVE_HYP th (inst pth_cond_F)))
      | e' ->
        let gT,gF =
          let gi (op:string) rhs r pth =
            let th = PROVE_HYP (TRANS th (ASSUME (mk_eq (e',r)))) (inst pth) in
            try log_step op evaluate rhs (F o TRANS th)
            with Failure _ as e -> fun _ -> raise e in
          gi "if T then [e2] else e3" a `T` pth_cond_T,
          gi "if F then e2 else [e3]" b `F` pth_cond_F in
        fun ls ->
          let th' = TRY_CONV WORD_RED_CONV (vsubst ls e') in
          match rhs (concl th') with
          | Const("T",_) -> PROVE_HYP th' (gT ls)
          | Const("F",_) -> PROVE_HYP th' (gF ls)
          | _ -> failwith "evaluate if..then failed")
  | Comb(Comb((Const("_BITMATCH",_) as f),(Var(_,ty) as e)),cs) ->
    let one_pattern = function
    | Comb(Comb(Const("_SEQPATTERN",_),_),
        Comb(Const("_ELSEPATTERN",_),Const(s,_))) -> mem s ["NONE"; "ARB"]
    | _ -> false in
    if one_pattern cs then
      let th = BM_FIRST_CASE_CONV t in
      let fn = inst_bitpat_numeral (hd (hyp th)) in
      let g = log_step "[bitmatch .. with | ..]"
                evaluate (rhs (concl th)) (F o TRANS th) in
      fun ls ->
        let ls', th' = fn (dest_numeral (rand (vsubst ls e))) in
        PROVE_HYP th' (g (ls' @ ls))
    else
     (match ty with
        Tyapp("word",[wty]) ->
        let w = try Num.int_of_num(dest_finty wty) with Failure _ -> 1000 in
        if w > 12 then raise (Invalid_argument
          ("Unsupported bitmatch size > 12 in " ^ string_of_term t)) else
        let _,tr = bm_build_pos_tree t in
        let gs = Array.init (1 lsl w) (fun n -> try
        let A = Array.init w (fun i -> Some (n land (1 lsl i) != 0)) in
        let th = hd (snd (snd (get_dt A tr))) in
        let ls, th1 = inst_bitpat_numeral (hd (hyp th)) (num n) in
        let th2 = PROVE_HYP th1 (INST ls th) in
        let e' = fst (hd ls) in
        let th = TRANS (AP_THM (AP_TERM f (ASSUME (mk_eq (e, e')))) cs) th2 in
        PROVE_HYP (REFL e') o
            log_step "[bitmatch .. with | ..]"
              evaluate (rhs (concl th)) (F o TRANS th)
        with Failure _ as e -> fun _ -> raise e) in
        fun ls -> gs.(Num.int_of_num (dest_numeral (rand (rev_assoc e ls)))) ls
      | _ -> raise (Invalid_argument ("Unknown " ^ string_of_term t)))

  | Comb(Comb((Const("_MATCH",_) as f),e),cs) ->
    if not (is_var e) then
      let th = CHANGED_CONV MATCH_CONV t in
      log_step "[match .. with | ..]"
          evaluate (rhs (concl th)) (F o TRANS th) else
    let one_pattern = function
    | Comb(Comb(Const("_SEQPATTERN",_),_),cs) ->
      (match cs with
      | Abs(_,Abs(_,Comb(Const("?",_),Abs(Var("_",_),
          Comb(Comb(Const("_UNGUARDED_PATTERN",_),_),
            Comb(Comb(Const("GEQ",_),Const(s,_)),_)))))) ->
        mem s ["NONE"; "ARB"]
      | _ -> false)
    | _ -> true in
    let ty = type_of e in
    if one_pattern cs then
      match snd (strip_exists (body (body (lhand cs)))) with
      | Comb(Comb(Const("_UNGUARDED_PATTERN",_),
          Comb(Comb(Const("GEQ",_),p),_)),_) ->
        let th = AP_THM (AP_TERM f (ASSUME (mk_eq (e, p)))) cs in
        let th = TRANS th (MATCH_CONV (rhs (concl th))) in
        let g = log_step "[match .. with | ..]"
                  evaluate (rhs (concl th)) (F o TRANS th) in
        fun ls ->
          let e' = vsubst ls e in
          let _,ls',_ = term_unify (frees p) p e' in
          PROVE_HYP (REFL e') (g (ls' @ ls))
      | _ -> failwith "unsupported match kind"
    else if ty = `:pfxs` then
      let gs = bool_split (fun a ->
        let rec go = function
        | [] -> []
        | (b, c)::bcs ->
          let ls = go bcs in
          let e' = mk_pair (a, (mk_pair (b, c))) in
          let th1 = AP_THM (AP_TERM f (ASSUME (mk_eq (e, e')))) cs in
          let th = TRANS th1 (REPEATC MATCH_CONV (rhs (concl th1))) in
          match rhs (concl th) with
          | Const("NONE",_) -> ls
          | r -> try
              ((b, c), (*todo: log_step*) evaluate r (F o TRANS th)) :: ls
            with Failure _ -> ls in
        C assoc (go (allpairs (fun x y -> (x, y)) rep_pfx_constructors seg_pfx_constructors))) in
      fun ls ->
        (match rev_assoc e ls with
        | Comb(Comb(Const(",",_),a),Comb(Comb(Const(",",_),b),c)) as e2 ->
          let g = try gs a (b, c) with Failure _ -> failwith "match pfxs failed" in
          PROVE_HYP (REFL e2) (g ls)
        | _ -> failwith "match pfxs failed")
    else if ty = `:VEXM` then
      let rec go = function
        | [] -> []
        | b::bs ->
          let ls = go bs in
          let th1 = AP_THM (AP_TERM f (ASSUME (mk_eq (e, b)))) cs in
          let th = TRANS th1 (REPEATC MATCH_CONV (rhs (concl th1))) in
          match rhs (concl th) with
          | Const("NONE",_) -> ls
          | r -> try (b, (*todo: log_step*)evaluate r (F o TRANS th)) :: ls
                 with Failure _ -> ls in
      let gs = C assoc (go VEXM_constructors) in
      fun ls ->
        (match rev_assoc e ls with
        | Const(_,_) as e2 ->
          let g = try gs e2 with Failure _ -> failwith "match VEXM failed" in
          PROVE_HYP (REFL e2) (g ls)
        | _ -> failwith "match VEXM failed")
    else
      raise (Invalid_argument ("Unknown match type " ^ string_of_type ty))
  | Comb((Const("decode_BT",_) as f),a) -> eval_unary f a F DECODE_BT_CONV
  | Comb((Const("decode_binop",_) as f),a) ->
    eval_unary f a F DECODE_BINOP_CONV
  | Comb((Const("CMOV",_) as f),Comb((Const("decode_condition",_) as g),a)) ->
    eval_unary' (AP_TERM f o AP_TERM g) a F DECODE_CONDITION_CONV
  | Comb((Const("JUMP",_) as f),Comb((Const("decode_condition",_) as g),a)) ->
    eval_unary' (AP_TERM f o AP_TERM g) a F DECODE_CONDITION_CONV
  | Comb((Const("SET",_) as f),Comb((Const("decode_condition",_) as g),a)) ->
    eval_unary' (AP_TERM f o AP_TERM g) a F DECODE_CONDITION_CONV
  | Comb((Const("decode_condition",_) as f),a) ->
    eval_unary f a F DECODE_CONDITION_CONV
  | Comb((Const("word_zx",_) as f),a) -> eval_unary f a F WORD_ZX_34_CONV
  | Comb((Const("word_sx",_) as f),a) -> eval_unary f a F
      (* Do TRY_CONV WORD_SX_CONV, not WORD_SX_CONV. if the immediate was a
         symbolic expression (which can happen for relocatable symbol address)
         WORD_SX_CONV will not be able to fold `word_sx <expr>` into
         a constant. *)
      (TRY_CONV WORD_SX_CONV)
  | Comb((Const("word_not",_) as f),a) -> eval_unary f a F WORD_NOT_CONV
  | Comb((Const("regsize8",_) as f),a) ->
    log_step "regsize8 [e]" evaluate a (fun th ->
      let th = AP_TERM f th in
      delay_if true (rhs (concl th)) (F o TRANS th) REGSIZE8_CONV)
  | Comb((Const("is_some",_) as f),a) ->
    eval_unary f a F (GEN_REWRITE_CONV I [is_some])
  | Comb(Const("has_operand_override",_) as f,a) ->
    eval_unary f a F HAS_OPERAND_OVERRIDE_CONV
  | Comb(Const("has_unhandled_pfxs",_) as f,a) ->
    eval_unary f a F HAS_UNHANDLED_PFXS_CONV
  | Comb(Comb(Comb((Comb(Const("op_size",_),_) as f),w),v),p) ->
    log_step "op_size .. [ ] .. .." evaluate w (fun th ->
      let th = AP_THM (AP_THM (AP_TERM f th) v) p in
      delay_if true (rhs (concl th)) (F o TRANS th) OP_SIZE_CONV)
  | Comb(Comb(Comb((Const("op_size_W",_) as f),a),b),c) ->
    eval_ternary f a b c F OP_SIZE_W_CONV
  | Comb(Comb(Comb(Const("read_sib_displacement",_),_),_),_) ->
    eval_opt t F READ_SIB_CONV
  | Comb(Comb(Comb(Const("read_SIB",_),_),_),_) -> eval_opt t F READ_SIB_CONV
  | Comb(Comb(Const("read_ModRM",_),_),_) -> eval_opt t F READ_MODRM_CONV
  | Comb(Const("read_VEXM",_),_) -> eval_opt t F READ_VEXM_CONV
  | Comb((Const("read_VEXP",_) as f),a) -> eval_unary f a F READ_VEXP_CONV
  | Comb(Comb(Const("read_VEX",_),_),_) -> eval_opt t F READ_VEX_CONV
  | Comb(Comb(Comb(Comb((Comb(Comb(Const("decode_hi",_),_),_)
      as f),sz),opc),rm),l) ->
    log_step "decode_hi .. .. [ ] .. .. .." evaluate sz (fun th ->
      let th = AP_THM (AP_THM (AP_THM (AP_TERM f th) opc) rm) l in
      eval_opt (rhs (concl th)) (F o TRANS th) DECODE_HI_CONV)
  | Comb(Const("read_byte",_),_) -> eval_opt t F READ_WORD_CONV
  | Comb(Const("read_int16",_),_) -> eval_opt t F READ_WORD_CONV
  | Comb(Const("read_int32",_),_) -> eval_opt t F READ_WORD_CONV
  | Comb(Const("read_int64",_),_) -> eval_opt t F READ_WORD_CONV
  | Comb(Comb((Const("read_imm",_) as f),a),l) ->
    log_step "read_imm [ ] .." evaluate a (fun th ->
      let th = AP_THM (AP_TERM f th) l in
      eval_opt (rhs (concl th)) (F o TRANS th) READ_IMM_CONV)
  | Comb(Comb((Const("read_full_imm",_) as f),a),l) ->
    log_step "read_full_imm [ ] .." evaluate a (fun th ->
      let th = AP_THM (AP_TERM f th) l in
      eval_opt (rhs (concl th)) (F o TRANS th) READ_IMM_CONV)
  | Comb(Comb(Const("read_displacement",_),_),_) -> eval_opt t F READ_DISP_CONV
  | Comb(Comb((Const("rex_reg",_) as f),a),b) ->
    eval_binary f a b F REX_REG_CONV
  | Comb((Const("rex_B",_) as f),a) -> eval_unary f a F REX_BIT_CONV
  | Comb((Const("rex_X",_) as f),a) -> eval_unary f a F REX_BIT_CONV
  | Comb((Const("rex_R",_) as f),a) -> eval_unary f a F REX_BIT_CONV
  | Comb((Const("rex_W",_) as f),a) -> eval_unary f a F REX_BIT_CONV
  | Comb(Comb((Const("gpr_adjust",_) as f),a),b) ->
    eval_binary f a b F GPR_ADJUST_CONV
  | Comb(Comb((Const("Gpr",_) as f),a),b) -> eval_binary f a b F GPR_CONV
  | Comb(Comb((Const("Simdreg",_) as f),a),b) ->
    eval_binary f a b F SIMDREG_CONV
  | Comb(Comb(Comb((Comb(Const("Bsid",_),_) as f),a),b),c) ->
    log_step "Bsid .. [ ] .. .." evaluate a (fun th ->
      let th = AP_THM (AP_THM (AP_TERM f th) b) c in
      delay_if true (rhs (concl th)) (F o TRANS th) BSID_CONV)
  | Comb(Const("Riprel",_) as f,a) -> eval_unary f a F ALL_CONV
  | Comb((Const("to_wordsize",_) as f),a) -> eval_unary f a F TO_WORDSIZE_CONV
  | Comb((Const("vexL_size",_) as f),a) -> eval_unary f a F VEXL_SIZE_CONV
  | Comb((Const("simd_to_wordsize",_) as f),a) -> eval_unary f a F SIMD_TO_WORDSIZE_CONV
  | Comb((Const("adx",_) as f),a) -> eval_unary f a F ADX_CONV
  | Comb((Const("is_memop",_) as f),a) -> eval_unary f a F IS_MEMOP_CONV
  | Comb(Comb((Const("operand_of_RM",_) as f),a),b) ->
    eval_binary f a b F OPERAND_OF_RM_CONV
  | Comb(Comb((Const("mmreg",_) as f),a),b) ->
    eval_binary f a b F MMREG_CONV
  | Comb(Comb((Const("simd_of_RM",_) as f),a),b) ->
    eval_binary f a b F SIMD_OF_RM_CONV
  | Comb(Comb(Comb(Const("read_ModRM_operand",_),rex),sz),l) ->
    let th = pth_rmo rex sz l in
    evaluate (rhs (concl th)) (F o TRANS th)
  | Comb(Comb(Comb(Const("read_opcode_ModRM_operand",_),rex),sz),l) ->
    let th = pth_romo rex sz l in
    evaluate (rhs (concl th)) (F o TRANS th)
  | Comb(Comb(Const("read_opcode_ModRM",_),rex),l) ->
    let th = pth_rom rex l in
    evaluate (rhs (concl th)) (F o TRANS th)
  | Comb(Const("@",_),_) -> failwith "ARB"
  | Const("ARB",_) -> failwith "ARB"
  | Comb(Comb((Const("word_shl",_) as f),a),b) -> eval_binary f a b F WORD_SHL_CONV
  | Comb(Comb((Const("=",_) as f),a),b) ->
   (let ty = type_of a in
    match ty with
    | Tyapp("word",_) -> eval_binary f a b F WORD_RED_CONV
    | Tyapp(tyname,_) ->
      let inequalities = CONJUNCTS(distinctness tyname) in
      eval_binary f a b F (GEN_REWRITE_CONV I (REFL_CLAUSE::inequalities)))
  | Comb(Comb((Const("/\\",_) as f),a),b) ->
    eval_binary f a b F (GEN_REWRITE_CONV I [AND_CLAUSES])
  | Comb((Const("val",_) as f),a) -> eval_unary f a F WORD_VAL_CONV
  | Comb((Const("ival",_) as f),a) -> eval_unary f a F WORD_IVAL_CONV
  | Comb(f,a) when (match f with
    | Comb(Const("GABS",_),_) -> true
    | Abs(_,_) -> true
    | _ -> false) ->
    log_step "(\x. e) [e2]" evaluate a (fun th ->
      let th1 = AP_TERM f th in
      let th2 = TRANS th1 (GEN_BETA_CONV (rhs (concl th1))) in
      log_step "[(\x. e) v]" evaluate (rhs (concl th2)) (F o TRANS th2))
  | Comb((Comb(Const("LET",_),_) as f),a) ->
    log_step "let x = [e1] in e2" evaluate a (fun th ->
      let th1 = AP_TERM f th in
      let th2 = TRANS th1 (let_CONV (rhs (concl th1))) in
      log_step "[let x = v1 in e2]" evaluate (rhs (concl th2)) (F o TRANS th2))
  | Comb(Const("word",_),a) when is_numeral a -> F (REFL t)
  | Comb(Const("NUMERAL",_),a) when is_numeral t -> F (REFL t)
  | Comb(f,a) ->
    log_step "[e1] e2" evaluate f (fun th ->
      log_step "(\x. e) [e2]" evaluate a (fun th' -> F (MK_COMB (th, th'))))
  | Const(s,_) -> if mem s constructors then F (REFL t) else
    raise (Invalid_argument ("evaluate: unknown function " ^ s))
  | Var(_,_) -> F (REFL t)
  | Abs(_,_) -> F (REFL t)
  and eval_unary' f a F conv =
    log_step "unary_op [e]" evaluate a (fun th ->
      let th1 = f th in
      let tm = rhs (concl th1) in
      delay_if (is_var (rand tm)) tm (F o TRANS th1) conv)
  and eval_unary f a F conv = eval_unary' (AP_TERM f) a F conv
  and eval_binary f a b F conv =
    log_step "[e1] binop e2" evaluate a (fun tha ->
      log_step "v1 binop [e2]" evaluate b (fun thb ->
        let th1 = MK_COMB (AP_TERM f tha, thb) in
        let tm = rhs (concl th1) in
        delay_if (is_var (lhand tm) || is_var (rand tm))
          tm (F o TRANS th1) conv))
  and eval_ternary f a b c F conv =
    log_step "ternary_op ([e1], e2, e3)" evaluate a (fun tha ->
      log_step "ternary_op (v1, [e2], e3)" evaluate b (fun thb ->
        log_step "ternary_op (v1, v2, [e3])" evaluate c (fun thc ->
          let th1 = MK_COMB (AP_TERM f tha, thb) in
          let tm = rhs (concl th1) in
          let th2 = MK_COMB(th1,thc) in
          let tm' = rhs (concl th2) in
          delay_if (is_var (lhand tm) || is_var (rand tm)
                                      || is_var(rand(concl thc)))
            tm' (F o TRANS th2) conv))) in
  let () =
    let mk_pths th =
      let f th =
        let l,r = dest_eq (concl th) in
        lhand l, evaluate r (C INST o TRANS th) in
      let fs = map (f o SPEC_ALL) (CONJUNCTS th) in
      fun a -> assoc a fs in
    read_imm_func := mk_pths read_imm, mk_pths read_full_imm in

  let () =
    let A = Array.init 3 (fun md ->
      let th = read_disp_thms md in
      evaluate (rhs (concl th)) (C INST o TRANS th)) in
    read_disp_func := fun md -> A.(Num.int_of_num (dest_numeral md)) in

  let () =
    let A = Array.init 3 (fun md ->
      let f = mk_sib_disp_thm md in
      Array.init 16 (fun reg -> let th = f reg in
        evaluate (rhs (concl th)) (C INST o TRANS th))) in
    sib_disp_func := fun md reg ->
      A.(Num.int_of_num (dest_numeral md))
       .(Num.int_of_num (dest_numeral reg)) in

  let () =
    let th = SPEC_ALL (CONJUNCT2 read_SIB) in
    sib_func := evaluate (rhs (concl th)) (C INST o TRANS th) in

  let () =
    let fn x th =
      let th = SPEC_ALL th in
      evaluate (rhs (concl th)) (C INST o TRANS th) in
    read_vex_func := (fn `T` F_F fn `F`) (CONJ_PAIR read_VEX) in

  let () =
    let fn x r =
      let f = mk_decode_hi_thms x in
      for opc = 0 to 7 do
        let th = f opc in
        r.(opc) <- try
          evaluate (rhs (concl th)) (C INST o TRANS th)
        with Failure _ as e -> fun _ -> raise e
      done in
    let t,f = decode_hi_func in fn `T` t; fn `F` f in

  let () =
    let pth = SPEC_ALL (CONJUNCT2 read_ModRM) in
    let f = bm_seq_numeral (rhs (concl pth))
    and b = `b:byte` in
    let check th = match rhs (concl th) with
    | Comb(Const("SOME",_),_) -> th
    | _ -> failwith "read_ModRM returned NONE" in
    for i = 0 to 255 do
        let e', th = f (num i) in
        let th = TRANS (INST [e',b] pth) th in
      modRM_table.(i) <- try
        evaluate (rhs (concl th)) (C INST o check o TRANS th)
      with Failure _ as e -> fun _ -> raise e
    done in

  let decode_table =
    let rex,pfxs,t = `rex:(4 word)option`,`pfxs:pfxs`,`t:byte list`
    and f = C INST o MATCH_MP decode'_of_aux in
    Array.init 256 (fun n -> try
      let A = Array.init 8 (fun i -> Some (n land (1 lsl i) != 0)) in
      let th = hd (snd (snd (get_dt A decode_aux_tree))) in
      let ls, th1 = inst_bitpat_numeral (hd (hyp th)) (num n) in
      let th = PROVE_HYP th1 (INST ls th) in
      let g = evaluate (rhs (concl th)) (f o TRANS th) in
      fun pfxs',rex',t' -> g [pfxs',pfxs; rex',rex; t',t]
    with Failure _ as e -> fun _ -> raise e) in

  let decoder pfxs rex = function
  | Comb(Comb(Const("CONS",_),Comb(Const("word",_),a)),l) ->
    decode_table.(Num.int_of_num (dest_numeral a)) (pfxs, rex, l)
  | _ -> failwith "decode: not a CONS" in

  let () =
    let opo,rep,seg,l,T = `opo:bool`,`rep:rep_pfx`,`seg:seg_pfx`,`l:byte list`,`T` in
    decode_table.(0x66) <- function
    | Comb(Comb((Const(",",_) as p),opo'),
        Comb(Comb((Const(",",_) as q),rep'),seg')),
      (Const("NONE",_) as rex), l' ->
      TRANS (INST [opo',opo; rep',rep; seg',seg; l',l] decode'_opo)
        (decoder (mk_comb (mk_comb (p, T),
                           mk_comb (mk_comb (q, rep'), seg'))) rex l')
    | _ -> failwith "decode 0x66 failed" in
  let () =
    let opo,seg,l,repz = `opo:bool`,`seg:seg_pfx`,`l:byte list`,`RepZ` in
    decode_table.(0xf3) <- function
    | Comb(Comb((Const(",",_) as p),opo'),
        Comb(Comb((Const(",",_) as q),Const("Rep0",_)),seg')),
      (Const("NONE",_) as rex), l' ->
      TRANS (INST [opo',opo; seg',seg; l',l] decode'_repz)
        (decoder (mk_comb (mk_comb (p, opo'),
                           mk_comb (mk_comb (q, repz), seg'))) rex l')
    | _ -> failwith "decode 0xf3 failed" in
  let () =
    let opo,seg,l,repnz = `opo:bool`,`seg:seg_pfx`,`l:byte list`,`RepNZ` in
    decode_table.(0xf2) <- function
    | Comb(Comb((Const(",",_) as p),opo'),
        Comb(Comb((Const(",",_) as q),Const("Rep0",_)),seg')),
      (Const("NONE",_) as rex), l' ->
      TRANS (INST [opo',opo; seg',seg; l',l] decode'_repnz)
        (decoder (mk_comb (mk_comb (p, opo'),
                           mk_comb (mk_comb (q, repnz), seg'))) rex l')
    | _ -> failwith "decode 0xf2 failed" in
  let () =
    let opo,rep,l,cs = `opo:bool`,`rep:rep_pfx`,`l:byte list`,`CS` in
    decode_table.(0x2e) <- function
    | Comb(Comb((Const(",",_) as p),opo'),
        Comb(Comb((Const(",",_) as q),rep'),Const("SG0",_))),
      (Const("NONE",_) as rex), l' ->
      TRANS (INST [opo',opo; rep',rep; l',l] decode'_cs)
        (decoder (mk_comb (mk_comb (p, opo'),
                           mk_comb (mk_comb (q, rep'), cs))) rex l')
    | _ -> failwith "decode 0x2e failed" in
  let () =
    let opo,rep,l,ss = `opo:bool`,`rep:rep_pfx`,`l:byte list`,`SS` in
    decode_table.(0x36) <- function
    | Comb(Comb((Const(",",_) as p),opo'),
        Comb(Comb((Const(",",_) as q),rep'),Const("SG0",_))),
      (Const("NONE",_) as rex), l' ->
      TRANS (INST [opo',opo; rep',rep; l',l] decode'_ss)
        (decoder (mk_comb (mk_comb (p, opo'),
                           mk_comb (mk_comb (q, rep'), ss))) rex l')
    | _ -> failwith "decode 0x36 failed" in
  let () =
    let opo,rep,l,ds = `opo:bool`,`rep:rep_pfx`,`l:byte list`,`DS` in
    decode_table.(0x3e) <- function
    | Comb(Comb((Const(",",_) as p),opo'),
        Comb(Comb((Const(",",_) as q),rep'),Const("SG0",_))),
      (Const("NONE",_) as rex), l' ->
      TRANS (INST [opo',opo; rep',rep; l',l] decode'_ds)
        (decoder (mk_comb (mk_comb (p, opo'),
                           mk_comb (mk_comb (q, rep'), ds))) rex l')
    | _ -> failwith "decode 0x3e failed" in
  let () =
    let opo,rep,l,es = `opo:bool`,`rep:rep_pfx`,`l:byte list`,`ES` in
    decode_table.(0x26) <- function
    | Comb(Comb((Const(",",_) as p),opo'),
        Comb(Comb((Const(",",_) as q),rep'),Const("SG0",_))),
      (Const("NONE",_) as rex), l' ->
      TRANS (INST [opo',opo; rep',rep; l',l] decode'_es)
        (decoder (mk_comb (mk_comb (p, opo'),
                           mk_comb (mk_comb (q, rep'), es))) rex l')
    | _ -> failwith "decode 0x26 failed" in
  let () =
    let pth = UNDISCH decode'_rex in
    let ps = hd (hyp pth) in let p = lhand ps in
    let some = `SOME:4 word->(4 word)option`
    and pfxs,l = `pfxs:pfxs`,`l:byte list` in
    for i = 0 to 255 do
      match bitpat_matches p (num i) with
      | Some _ -> ()
      | None ->
        let ls, th = inst_bitpat_numeral ps (num i) in
        let rex' = fst (hd (tl ls)) in
        let pth = PROVE_HYP th (INST ls pth) in
        decode_table.(i) <- function
        | pfxs', Const("NONE",_), l' ->
          TRANS (INST [pfxs',pfxs; l',l] pth)
            (decoder pfxs' (mk_comb (some, rex')) l')
        | _ -> failwith "decode REX failed"
    done in

  let DECODE_CONV =
    let pfxs0,rex0 = `F, Rep0, SG0`,`NONE:(4 word)option` in
    function
    | Comb(Comb(Comb(Const("decode'",_),pfxs),rex),l) -> decoder pfxs rex l
    | Comb(Const("decode",_),l) ->
      TRANS (AP_THM decode_eq_decode' l) (decoder pfxs0 rex0 l)
    | _ -> failwith "DECODE_CONV" in

  READ_SIB_CONV,READ_MODRM_CONV,READ_VEX_CONV,DECODE_CONV;;

(* ------------------------------------------------------------------------- *)
(* List linearity of the decode function.                                    *)
(* ------------------------------------------------------------------------- *)

let list_linear = new_definition `list_linear P <=> !l1 l2. P l1 l2 ==>
  ?l:A list. l1 = APPEND l l2 /\ !l2'. P (APPEND l l2') l2'`;;

let list_linear_exists = prove
 (`!P. (!x. list_linear (P x)) ==> list_linear (\l1 l2. ?x. P x l1 l2)`,
  REWRITE_TAC [list_linear] THEN MESON_TAC []);;

let list_linear_and = prove
 (`!p P. list_linear P ==>
   list_linear (\l1 l2:A list. p /\ P l1 l2)`,
  REWRITE_TAC [list_linear] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM_LIST (fun [th; hp; x] ->
    REWRITE_TAC [hp] THEN ACCEPT_TAC (MATCH_MP x th)));;

let list_linear_comp = prove
 (`!P Q. list_linear P /\ list_linear Q ==>
   list_linear (\l1 l2. ?l:A list. P l1 l /\ Q l l2)`,
  REWRITE_TAC [list_linear] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM_LIST (fun [th1; th2; x1; x2] ->
    MP_TAC (MATCH_MP x1 th1) THEN MP_TAC (MATCH_MP x2 th2)) THEN
  REWRITE_TAC [LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  REPEAT (GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC) THEN
  EXISTS_TAC `APPEND l' l'':A list` THEN
  REWRITE_TAC [APPEND_ASSOC] THEN
  GEN_TAC THEN EXISTS_TAC `APPEND l'' l2':A list` THEN
  ASM_REWRITE_TAC [GSYM APPEND_ASSOC]);;

let list_linear_f = new_definition `list_linear_f f <=>
  !b:B. list_linear (\l1 l2:A list. f l1 = SOME (b, l2))`;;

let list_linear_obind = prove
 (`!f g. list_linear_f f /\ (!b:B. list_linear_f (g b)) ==>
   list_linear_f (\l. f l >>= \(b,(l:A list)). g b l:(C#A list)option)`,
  REWRITE_TAC [list_linear_f; obind_eq_some; EXISTS_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC list_linear_exists THEN
  STRIP_TAC THEN REWRITE_TAC [] THEN
  POP_ASSUM (fun th2 -> POP_ASSUM (fun th1 ->
    let th = MATCH_MP list_linear_comp
      (CONJ (SPEC `p1:B` th1) (SPECL [`p1:B`; `b:C`] th2)) in
    ACCEPT_TAC (REWRITE_RULE [] th))));;

let read_prefixes_eq_cons = prove
 (`!l p l2. read_prefixes l p = SOME (b, l2) ==> ?c l3. l2 = CONS c l3`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [read_prefixes; OPTION_DISTINCT] THEN
  POP_ASSUM (fun th -> BITMATCH_ASM_CASES_TAC THEN
    REWRITE_TAC [read_prefixes; OPTION_DISTINCT; OPTION_INJ; PAIR_EQ] THENL
    let t = REWRITE_TAC [obind_eq_some] THEN
      REPEAT STRIP_TAC THEN POP_ASSUM (ACCEPT_TAC o MATCH_MP th) in
    [t; t; t; t; t; t; t; METIS_TAC []]));;

let list_linear_read_prefixes = prove
 (`!p b c. list_linear (\l1 l2. read_prefixes l1 p = SOME (b, CONS c l2))`,
  REWRITE_TAC [list_linear] THEN REPEAT GEN_TAC THEN
  SPECL_TAC [`l1:byte list`; `p:pfxs`] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC [read_prefixes; OPTION_DISTINCT] THEN
  let tac = POP_ASSUM_LIST (CONV_TAC o ONCE_DEPTH_CONV o BITMATCH_SIMP_CONV) in
  GEN_TAC THEN POP_ASSUM (fun th -> BITMATCH_ASM_CASES_TAC THENL
    let t1 = REWRITE_TAC [OPTION_INJ; PAIR_EQ; CONS_11; obind_eq_some] THEN
      STRIP_TAC THEN
      let f (th2,th3) th1 =
        EXISTS_TAC `CONS h l:byte list` THEN
        REWRITE_TAC [APPEND; th2; read_prefixes] THEN tac THEN
        REWRITE_TAC [th1; th3; obind] in
      POP_ASSUM (CHOOSE_THEN (POP_ASSUM o f o CONJ_PAIR) o MATCH_MP th)
    and t2 = REWRITE_TAC [OPTION_DISTINCT]
    and t3 = REWRITE_TAC [OPTION_INJ; PAIR_EQ; CONS_11] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
      EXISTS_TAC `[h:byte]` THEN REWRITE_TAC [APPEND; read_prefixes] THEN
      GEN_TAC THEN tac THEN REFL_TAC in
    [t1; t1; t1; t1; t1; t1; t1; t2; t2; t2; t2; t3]));;

let list_linear_read_REX_prefix = prove
 (`!a rex b. list_linear (\l1 l2.
   read_REX_prefix (CONS a l1) = rex,CONS b l2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [read_REX_prefix] THEN BITMATCH_CASES_TAC THEN
  REWRITE_TAC [PAIR_EQ; CONS_11] THEN
  REPEAT (MATCH_MP_TAC list_linear_and) THEN
  REWRITE_TAC [list_linear] THEN METIS_TAC [APPEND]);;

let list_linear_F = prove
 (`list_linear (\l1 l2:A list. F)`, REWRITE_TAC [list_linear]);;

let list_linear_eq = prove
 (`list_linear (=)`, REWRITE_TAC [list_linear] THEN MESON_TAC [APPEND]);;

let list_linear_none = prove
 (`list_linear_f (\l. NONE:(B#A list)option)`,
  REWRITE_TAC [list_linear_f; OPTION_DISTINCT; list_linear_F]);;

let list_linear_some = prove
 (`!b:B. list_linear_f (\l:A list. SOME(b,l))`,
  REWRITE_TAC [list_linear_f; OPTION_INJ; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN IMP_REWRITE_TAC [list_linear_and; list_linear_eq]);;

let list_linear_cond = prove
(`!p:bool f g. list_linear_f f /\ list_linear_f g ==>
  list_linear_f (\l. COND p (f l:(B#A list)option) (g l))`,
 REPEAT STRIP_TAC THEN
 BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC [] THEN
 CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC []);;

let list_linear_obind1 = prove
 (`!oa (f:C->A list->(B#A list)option). (!x. list_linear_f (f x)) ==>
   list_linear_f (\l. oa >>= \x. f x l)`,
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC [obind; list_linear_none] THEN
  CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN METIS_TAC []);;

let list_linear_let = prove
 (`!a (f:C->A list->(B#A list)option). (!x. list_linear_f (f x)) ==>
   list_linear_f (\l. let x = a in f x l)`,
  REPEAT STRIP_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV let_CONV THENC ONCE_DEPTH_CONV ETA_CONV) THEN
  ASM_REWRITE_TAC []);;

let list_linear_let2 = prove
 (`!a (f:C->D->A list->(B#A list)option). (!x y. list_linear_f (f x y)) ==>
   list_linear_f (\l. let x,y = a in f x y l)`,
  REWRITE_TAC [FORALL_PAIR_THM] THEN
  CONV_TAC (ONCE_DEPTH_CONV let_CONV THENC ONCE_DEPTH_CONV ETA_CONV) THEN
  MESON_TAC []);;

let forall_uncurry_when =
  let FST,SND = mk_const ("FST",[]), mk_const ("SND",[]) in
  fun P th ->
    let rec mk_ty = function
    | (Tyapp("prod",[A;B]) as t),C when P t -> mk_ty (A, mk_ty (B, C))
    | A,C -> mk_fun_ty A C in
    let rec go = function
    | f, (Tyapp("prod",[A;B]) as t), x when P t ->
      go (go (f, A, mk_icomb (FST, x)), B, mk_icomb (SND, x))
    | f, _, x -> mk_comb (f, x) in
    let A,C = dest_fun_ty (type_of (fst (dest_forall (concl th)))) in
    let f = mk_var ("f", mk_ty (A,C)) and x = mk_var ("x", A) in
    let tm = mk_abs (x, go (f, A, x)) in
    GEN f (REWRITE_RULE [] (SPEC tm th));;

let add_ll_tac,LL_TAC =
  let net = ref (itlist (enter [])
    [`NONE`, MATCH_ACCEPT_TAC list_linear_none;
     `SOME (b,l)`, MATCH_ACCEPT_TAC list_linear_some;
     `COND c a b`, MATCH_MP_TAC list_linear_cond THEN CONJ_TAC;
     `let x = a in b`, MATCH_MP_TAC list_linear_let THEN GEN_TAC;
     `let x,y = a in b`, MATCH_MP_TAC list_linear_let2 THEN REPEAT GEN_TAC;
     `_BITMATCH e cs`, BITMATCH_CASES_TAC;
     `_MATCH e cs`, WITH_GOAL (fun g ->
        let e = lhand (body (rand g)) in
        match type_of e with
        | Tyapp("RM",[]) ->
          SPEC_TAC (e, mk_var("x", type_of e)) THEN
          MATCH_MP_TAC RM_INDUCTION THEN
          CONV_TAC (BINOP2_CONV ((BINDER_CONV o RAND_CONV o BINDER_CONV) MATCH_CONV')
                                ((BINDER_CONV o RAND_CONV o BINDER_CONV) MATCH_CONV'))
        | _ -> CONV_TAC ((RAND_CONV o BINDER_CONV) MATCH_CONV'));
     `a >>= b`, MATCH_MP_TAC list_linear_obind1]
    empty_net) in
  (fun tm tac -> net := enter [] (tm,tac) !net),
  WITH_GOAL (function
  | Comb(Comb(Const("/\\",_),_),_) -> CONJ_TAC
  | Comb(Const("!",_),_) -> GEN_TAC
  | Comb(Const("list_linear_f",_),Abs(l,tm)) -> FIRST (lookup tm !net)
  | Comb(Const("list_linear_f",_),Comb(_,_)) -> CHANGED_TAC (REWRITE_TAC [])
  | _ -> failwith "LL_TAC");;

let add_ll_opt th =
  let th' = SPEC_ALL th in
  match concl th' with
  | Comb(Const("list_linear_f",_),tm) ->
    let th'' = forall_uncurry_when (fun t -> t <> `:pfxs`)
      (REWRITE_RULE [th'; FORALL_PAIR_THM] (ISPEC tm list_linear_obind)) in
    let () = add_ll_tac
      (mk_comb (tm, `l:byte list`))
      (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN MATCH_ACCEPT_TAC th') in
    let () = add_ll_tac
      (body (rand (snd (dest_imp (snd (strip_forall (concl th'')))))))
      (MATCH_MP_TAC th'' THEN REPEAT GEN_TAC) in
    th
  | _ -> failwith "add_ll_opt";;

let list_linear_read_byte = (add_ll_opt o prove)
 (`list_linear_f read_byte`,
  REWRITE_TAC [list_linear_f; list_linear] THEN REPEAT GEN_TAC THEN
  SPEC1_TAC `l1:byte list` THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC [read_byte_val; OPTION_DISTINCT; OPTION_INJ; PAIR_EQ] THEN
  DISCH_TAC THEN EXISTS_TAC `[h:byte]` THEN
  ASM_REWRITE_TAC [APPEND; read_byte_val]);;

let list_linear_f_split = prove
 (`!f. f [] = NONE:(B#byte list)option /\
     (!a. list_linear_f (\l. f (CONS a l))) ==>
   list_linear_f f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f = \l. read_byte l >>=
    \(a,l). f (CONS a l):(B#byte list)option` (fun th ->
    ONCE_REWRITE_TAC [th] THEN MATCH_MP_TAC list_linear_obind THEN
    ASM_REWRITE_TAC [list_linear_read_byte]) THEN
  REWRITE_TAC [FUN_EQ_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [read_byte_val; obind]);;

let list_linear_read_word_n = (add_ll_opt o prove)
 (`!n. list_linear_f (read_word_n n)`,
  UNETA_TAC `read_word_n n l` THEN
  INDUCT_TAC THEN REWRITE_TAC [read_word_n] THENL [LL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC list_linear_f_split THEN REWRITE_TAC [read_word_n] THEN
  GEN_TAC THEN MATCH_MP_TAC list_linear_obind THEN ASM_REWRITE_TAC [] THEN
  REPEAT LL_TAC);;

let list_linear_read_word = (add_ll_opt o prove)
 (`!n. list_linear_f (read_word n)`,
  UNETA_TAC `read_word n l` THEN REWRITE_TAC [read_word] THEN
  REPEAT LL_TAC);;

let list_linear_read_int16 = (add_ll_opt o prove) (`list_linear_f read_int16`,
  REWRITE_TAC [read_int16; list_linear_read_word])
and list_linear_read_int32 = (add_ll_opt o prove) (`list_linear_f read_int32`,
  REWRITE_TAC [read_int32; list_linear_read_word])
and list_linear_read_int64 = (add_ll_opt o prove) (`list_linear_f read_int64`,
  REWRITE_TAC [read_int64; list_linear_read_word]);;

let list_linear_read_imm = (add_ll_opt o prove)
 (`!sz. list_linear_f (read_imm sz)`,
  UNETA_TAC `read_imm sz l` THEN MATCH_MP_TAC wordsize_INDUCT THEN
  REWRITE_TAC [read_imm] THEN REPEAT LL_TAC);;

let list_linear_read_full_imm = (add_ll_opt o prove)
 (`!sz. list_linear_f (read_full_imm sz)`,
  UNETA_TAC `read_full_imm sz l` THEN MATCH_MP_TAC wordsize_INDUCT THEN
  REWRITE_TAC [read_full_imm] THEN REPEAT LL_TAC);;

let list_linear_read_displacement = (add_ll_opt o prove)
 (`!md. list_linear_f (read_displacement md)`,
  UNETA_TAC `read_displacement md l` THEN
  REWRITE_TAC [read_displacement] THEN REPEAT LL_TAC);;

let list_linear_read_sib_displacement = (add_ll_opt o prove)
 (`!md reg. list_linear_f (read_sib_displacement md reg)`,
  UNETA_TAC `read_sib_displacement md reg l` THEN
  REWRITE_TAC [read_sib_displacement] THEN REPEAT LL_TAC);;

let list_linear_read_SIB = (add_ll_opt o prove)
 (`!rex md. list_linear_f (read_SIB rex md)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC list_linear_f_split THEN
  REWRITE_TAC [read_SIB] THEN REPEAT LL_TAC);;

let list_linear_read_ModRM = (add_ll_opt o prove)
 (`!rex. list_linear_f (read_ModRM rex)`,
  UNETA_TAC `read_ModRM rex l` THEN
  GEN_TAC THEN MATCH_MP_TAC list_linear_f_split THEN
  REWRITE_TAC [read_ModRM] THEN REPEAT LL_TAC);;

let list_linear_read_ModRM_operand = (add_ll_opt o prove)
 (`!rex sz. list_linear_f (read_ModRM_operand rex sz)`,
  UNETA_TAC `read_ModRM_operand rex sz l` THEN
  REWRITE_TAC [read_ModRM_operand] THEN REPEAT LL_TAC);;

let list_linear_read_opcode_ModRM = (add_ll_opt o prove)
 (`!rex. list_linear_f (read_opcode_ModRM rex)`,
  UNETA_TAC `read_opcode_ModRM rex l` THEN
  REWRITE_TAC [read_opcode_ModRM] THEN REPEAT LL_TAC);;

let list_linear_read_opcode_ModRM_operand = (add_ll_opt o prove)
 (`!rex sz. list_linear_f (read_opcode_ModRM_operand rex sz)`,
  UNETA_TAC `read_opcode_ModRM_operand rex sz l` THEN
  REWRITE_TAC [read_opcode_ModRM_operand] THEN REPEAT LL_TAC);;

let list_linear_read_VEX = (add_ll_opt o prove)
 (`!vl. list_linear_f (read_VEX vl)`,
  MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC [read_VEX] THEN REPEAT LL_TAC);;

let list_linear_decode_hi = (add_ll_opt o prove)
 (`!x v sz opc rm. list_linear_f (decode_hi x v sz opc rm)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC [decode_hi] THEN REPEAT LL_TAC);;

let list_linear_decode_aux = prove
 (`!pfxs rex h. list_linear_f (\l. decode_aux pfxs rex (CONS h l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC [decode_aux; read_byte_val;
    obind; FORALL_PAIR_THM] THEN
  REPEAT LL_TAC);;

let list_linear_decode = prove (`list_linear_f decode`,
  REWRITE_TAC [list_linear_f; decode; obind_eq_some] THEN
  ONCE_REWRITE_TAC [EXISTS_PAIR_THM] THEN
  GEN_TAC THEN MATCH_MP_TAC list_linear_exists THEN
  GEN_TAC THEN REWRITE_TAC [] THEN
  CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  SUBGOAL_THEN
  `!l1 l2. (?l. read_prefixes l1 (F,Rep0,SG0) = SOME (p1,l) /\
    (let rex,l' = read_REX_prefix l in decode_aux p1 rex l') =
      SOME (b,l2)) <=>
  (?a rex c l3. read_prefixes l1 (F,Rep0,SG0) = SOME (p1,CONS a l3) /\
    (?l4. read_REX_prefix (CONS a l3) = rex, CONS c l4 /\
          decode_aux p1 rex (CONS c l4) = SOME (b,l2)))`
  (fun th -> REWRITE_TAC [th] THEN
    REPEAT (
      MATCH_MP_TAC list_linear_comp ORELSE
      (MATCH_MP_TAC list_linear_exists THEN GEN_TAC THEN REWRITE_TAC[])) THEN
    REWRITE_TAC [list_linear_read_prefixes] THEN
    MATCH_MP_TAC list_linear_comp THEN
    REWRITE_TAC [list_linear_read_REX_prefix;
      REWRITE_RULE [list_linear_f] list_linear_decode_aux]) THEN
  let th1 = read_prefixes_eq_cons in
  let th2 = prove
    (`!l rex l'. read_REX_prefix l = rex,l' ==>
      (let rex,l' = read_REX_prefix l in decode_aux p1 rex l') =
      decode_aux p1 rex l'`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN REFL_TAC) in
  let th3 = prove
    (`!p rex l. decode_aux p rex l = SOME (b,l2) ==> ?c l4. l = CONS c l4`,
    REPEAT GEN_TAC THEN DISJ_CASES_THEN
      (REPEAT_TCL CHOOSE_THEN (fun th ->
        REWRITE_TAC [th; decode_aux_nil; OPTION_DISTINCT]))
      (ISPEC `l:byte list` list_CASES) THEN MESON_TAC []) in
  MESON_TAC [th1; th2; th3; PAIR_SURJECTIVE]);;

(* ------------------------------------------------------------------------- *)
(* Decoding with length information.                                         *)
(* ------------------------------------------------------------------------- *)

let decode_len = new_definition `decode_len l (n,i) l' <=>
  decode l = SOME (i,l') /\ LENGTH l = LENGTH l' + n`;;

(* Given `l`, proves `|- decode_len l (n,i) l'` for suitable `n,i,l'` *)
let DECODE_LEN_THM =
  let ai = let b = `:byte` in
    fun i -> mk_var("a"^string_of_int i, b)
  and el = `l:byte list` in
  let pths =
    let pth = (UNDISCH o prove)
     (`SUC n = n' ==> LENGTH (CONS (a:byte) l) + n = LENGTH l + n'`,
      DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [LENGTH; ADD_CLAUSES])
    and pth2 = (UNDISCH_ALL o METIS [decode_len])
     `decode l' = SOME (i,l) ==> LENGTH l' = LENGTH l + n ==>
      decode_len l' (n,i) l`
    and pthapp =
      let th = prove
       (`LENGTH (l':byte list) = k ==>
         n + k = n' ==> LENGTH (APPEND l' l) + n = LENGTH l + n'`,
        REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
        REWRITE_TAC [ADD_AC; LENGTH_APPEND]) in
      W f_f_ (UNDISCH o MATCH_MP th)
        (SPECL [`4`; `a:num`] LENGTH_BYTELIST_OF_NUM,
         SPECL [`4`; `a:int`] LENGTH_BYTELIST_OF_INT) in
    let cons,suc = mk_const ("CONS",[`:byte`,`:A`]), `SUC`
    and el',ea,en,en' = `l':byte list`,`a:byte`,`n:num`,`n':num` in
    let rec mk_pths i lth =
      if i = 16 then
        (* The maximum length of an x86 instruction is 15 bytes *)
        fun _ -> failwith "DECODE_LEN_THM: too long"
      else
        let l',n = (rand F_F rand) (dest_eq (concl lth)) in
        let a = ai i in
        let lth' = INST [mk_comb (mk_comb (cons, a), el),el] lth in
        let th1 = NUM_RED_CONV (mk_comb (suc, n)) in
        let n' = rhs (concl th1) in
        let th = PROVE_HYP lth (INST [l',el'; n,en] pth2) in
        let gcons = mk_pths (i+1) (TRANS lth'
          (PROVE_HYP th1 (INST [a,ea; n,en; n',en'] pth)))
        and gnum,gint = C (W f_f_) pthapp (fun th ->
          if i >= 12 then fun _ _ -> failwith "DECODE_LEN_THM: too long" else
          let ea,th =
            let l' = rand (lhand (lhs (concl th))) in
            let th = TRANS (INST [l',el] lth) (INST [n,en] th) in
            let th2 = NUM_RED_CONV (lhs (hd (hyp th))) in
            let n' = rhs (concl th2) in
            let th3 = PROVE_HYP th2 (INST [n',en'] th) in
            rand (lhand l'), PROVE_HYP th3
              (INST [rand (lhs (concl th3)),el'; n',en] pth2) in
          fun a ls -> INST ((a,ea)::ls) th) in
        function
        | l,ls,l' when l' == l -> INST ls th
        | l,ls,Comb(Comb(Const("CONS",_),a'),tm') -> gcons (l, (a',a)::ls, tm')
        | l,ls,Comb(Comb(Const("APPEND",_),
            Comb(Comb(Const("bytelist_of_num",_),_),a)),l') when l' == l ->
          gnum a ls
        | l,ls,Comb(Comb(Const("APPEND",_),
            Comb(Comb(Const("bytelist_of_int",_),_),a)),l') when l' == l ->
          gint a ls
        | _ -> failwith "DECODE_LEN_THM" in
    mk_pths 0 (ARITH_RULE `LENGTH (l:byte list) = LENGTH l + 0`)
  and dec,ei = `decode`,`i:instruction` in
  fun tm ->
    let th = DECODE_CONV (mk_comb (dec, tm)) in
    let inst,l = (rand F_F I) (dest_comb (rand (rhs (concl th)))) in
    PROVE_HYP th (pths (l, [inst,ei; l,el], tm));;

(* ------------------------------------------------------------------------- *)
(* Testing and preparation.                                                  *)
(* ------------------------------------------------------------------------- *)

let decode_until_ret,decode_all =
  let rec go f = function
  | Const("NIL",_) -> []
  | tm ->
    let th = DECODE_CONV (mk_comb (`decode`, tm)) in
    let lhs,rhs = dest_eq (concl th) in
    let tm',next = dest_comb (rand rhs) in
    let rec len n = function
    | t when t == next -> n
    | Comb(Comb(Const("CONS",_),_),l) -> len (n+1) l
    | Comb(Comb(Const("APPEND",_),
        Comb(Comb(Const("bytelist_of_num",_),i),_)),l) ->
      len (n + Num.int_of_num (dest_numeral i)) l
    | Comb(Comb(Const("APPEND",_),
        Comb(Comb(Const("bytelist_of_int",_),i),_)),l) ->
      len (n + Num.int_of_num (dest_numeral i)) l
    | _ -> 0 in
    let a = len 0 (rand lhs), rand tm' in
    if f (snd a) then a :: go f next else [a] in
  go (fun t -> t <> `RET`), go (fun _ -> true);;

(* Asserts that the input term is the given list of bytes, and returns it. *)
let assert_word_list =
  let rec go = function
  | [], Const("NIL",_) -> ()
  | n::ls, Comb(Comb(Const("CONS",_),Comb(Const("word",_),a)),tm)
    when 0 <= n && n <= 255 && dest_numeral a = num n -> go (ls, tm)
  | _ -> failwith "assert_word_list" in
  fun tm ls ->
    if type_of tm = `:byte list` then go (ls, tm)
    else failwith "assert_word_list";
    tm;;

let define_assert_word_list name tm ls =
  define_word_list name (assert_word_list tm ls);;

(* define `name args = tm` where the type of tm is `:byte list` *)
let define_relocated_mc name (args, tm:term list * term): thm =
  let rec mk_tm_comb f A = function
  | [] -> f (name, A)
  | (v::vs) -> mk_comb (mk_tm_comb f (mk_fun_ty (type_of v) A) vs, v) in
  let args0,args = args,rev args in
  let mc_def =
    try new_definition (list_mk_forall
      (args0, mk_eq (mk_tm_comb mk_var `:byte list` args, tm)))
    with Failure _ ->
      new_definition (list_mk_forall
        (args0, mk_eq (mk_tm_comb mk_mconst `:byte list` args, tm))) in
  (* break APPEND(4-byte list, list) to 4 consecutive CONSs. *)
  let blth = (LAND_CONV (TOP_DEPTH_CONV num_CONV) THENC
      REWRITE_CONV[bytelist_of_int;bytelist_of_num])
      `bytelist_of_int 4 x` in
  REWRITE_RULE[APPEND; blth] mc_def;;

needs "common/elf.ml";;

let make_fn_word_list, make_fn_word_list_reloc =
  let rhs_col = 27 in
  let indent = "\n" ^ String.make rhs_col ' ' in
  let go next_rel start end_ (bs:bytes) dec =
    let buf = Buffer.create 1024 in
    Buffer.add_string buf start;
    let rec go pc prev_inst_printer = function
    | [] -> prev_inst_printer ""
    | ((n,inst)::l) ->
      let () = prev_inst_printer ";" in
      let pcnext = pc + n in
      go pcnext (fun s ->
        (* s is either "" or ";" *)
        Buffer.add_string buf "  ";
        let col = ref 2 in
        let rec bytes i prev_inst_printer =
          if i = pcnext then prev_inst_printer s else
          match next_rel i with
          | None ->
          (prev_inst_printer "; ";
            let nextbyte = int_of_char (Bytes.get bs i) in
            Printf.bprintf buf "0x%02x" nextbyte;
            col := !col + 4;
            bytes (i+1) (fun s ->
              Buffer.add_string buf s;
              col := !col + String.length s))

          | Some (X86_64_pc32,sym,addend) ->
          (prev_inst_printer "";
            Printf.bprintf buf "]; ADDR (\"%s\",(%d)); b[" sym addend;
            col := !col + String.length sym + 16;
            bytes (i+4) (fun _ -> ()))

          in
        bytes pc (fun _ -> ());
        Printf.bprintf buf "%s(* %s *)\n"
          (if !col < rhs_col then String.make (rhs_col - !col) ' ' else indent)
          (string_of_term inst)) l in
    go 0 (fun _ -> ()) dec;
    Printf.bprintf buf end_;
    Buffer.contents buf in
  (* make_fn_word_list *)
  go (fun _ -> None) "[\n" "];;\n",
  (* make_fn_word_list_reloc *)
  fun (bstext, constants, rels) ->
    let r = ref rels in
    let next_rel i = match !r with
    | (ty,(off,sym,add)) :: rels when off = i -> r := rels; Some (ty,sym,add)
    | _ -> None in
    go next_rel "(fun b ADDR -> [b[\n" "]]);;\n" bstext;;

let trim_ret_core dec =
  let m1 = Array.length dec - 1 in
  if m1 < 0 then failwith "trim_ret: empty" else
  let lr,r = dec.(m1) in
  if r <> `RET` then
    failwith "trim_ret: function does not end with RET" else
  let rec go a b i j =
    match if i < j then
      match dec.(i), dec.(j) with
      | (n,Comb(Const("PUSH",_),tm)), (m,Comb(Const("POP",_),tm'))
        when tm = tm' -> Some(a+n,b+m,tm)
      | _ -> None
    else None with
    | Some(a',b',tm) -> let ls,r = go a' b' (i+1) (j-1) in tm::ls, r
    | None -> [], (a, b, Array.sub dec i (j+1-i)) in
  go 0 lr 0 (m1-1);;

let trim_ret ((bs:term array), dec) =
  let ls,(a,b,dec) = trim_ret_core (Array.of_list dec) in
  ls, a, (Array.sub bs a (Array.length bs - b - a), Array.to_list dec);;

let rec dest_mc_list = function
| Const("NIL",_) -> []
| Comb(Comb(Const("CONS",_),a),t) -> a :: dest_mc_list t
| Comb(Comb(Const("APPEND",_),a),t) -> a :: dest_mc_list t
| _ -> failwith "dest_mc_list";;

let rec term_of_mc_list =
  let nil = `NIL:byte list`
  and cons = `CONS:byte->byte list->byte list`
  and append = `APPEND:byte list->byte list->byte list` in
  function
  | [] -> nil
  | (Comb(Const("word",_),_) as a) :: ls ->
    mk_comb (mk_comb (cons, a), term_of_mc_list ls)
  | a :: ls -> mk_comb (mk_comb (append, a), term_of_mc_list ls);;

let trim_ret_off tm =
  let _,n,bs = trim_ret (Array.of_list (dest_mc_list tm), decode_all tm) in
  n,term_of_mc_list (Array.to_list (fst bs));;

let trim_ret' = snd o trim_ret_off;;

let N_SUBLIST_CONV =
  let pth1,pth2 =
    W f_f_ (PART_MATCH lhs o SPEC_ALL) (CONJ_PAIR (GSYM APPEND))
  and pth3 = PART_MATCH lhs (SPEC_ALL APPEND_ASSOC) in
  fun th ->
    let rec right tm = function
    | Const("NIL",_) -> pth1 tm
    | Comb(Comb(Const("CONS",_),_),l) ->
      let f,tm' = dest_comb tm in
      let th = AP_TERM f (right tm' l) in
      TRANS th (pth2 (rhs (concl th)))
    | Comb(Comb(Const("APPEND",_),_),l) ->
      let f,tm' = dest_comb tm in
      let th = AP_TERM f (right tm' l) in
      TRANS th (pth3 (rhs (concl th)))
    | _ -> failwith "N_SUBLIST_CONV" in
    let rec left n tm = if n = 0 then
      let th = SYM th in
      let th1 = right tm (lhs (concl th)) in
      let th2 = CONV_RULE (RAND_CONV (LAND_CONV (K th))) th1 in
      TRANS th2 (pth1 (rhs (concl th2)))
    else
      let f,tm' = dest_comb tm in
      let th = AP_TERM f (left (n-1) tm') in
      TRANS th (pth2 (rhs (concl th))) in
    left;;

let define_trim_ret_thm name th =
  let th = SPEC_ALL th in
  let df,tm1 = dest_eq (concl th) in
  let n, tm = trim_ret_off tm1 in
  let rec args ls = function
  | Comb(f,v) -> args (v::ls) f
  | _ -> ls in
  let defn = define_relocated_mc name (args [] df, tm) in
  defn, TRANS th (N_SUBLIST_CONV (SPEC_ALL defn) n tm1);;

let define_from_elf name file =
  define_word_list name (term_of_bytes (load_elf_contents_x86 file));;

let define_assert_from_elf name file =
  define_assert_word_list name (term_of_bytes (load_elf_contents_x86 file));;

let print_literal_from_elf file =
  let bs:bytes = load_elf_contents_x86 file in
  let bsarr = array_of_bytes bs in
  print_string (make_fn_word_list bs (decode_all (term_of_array bsarr)));;

let save_literal_from_elf deffile objfile =
  let bs:bytes = load_elf_contents_x86 objfile in
  let bsarr = array_of_bytes bs in
  let ls = make_fn_word_list bs (decode_all (term_of_array bsarr)) in
  file_of_string deffile ls;;

(*** Define a variant with initial ENDBR64 trimmed away ***)

(* Define `<name> = TRIM_LIST(4,0)(<mc>)` to skip past the leading ENDBR64.
   Backward-compatible for plain `mc = [bytes]` definitions. For mc theorems
   parameterised over `pc` and rodata symbols (as produced by
   define_assert_relocs_from_elf), the new definition is keyed on the post-
   ENDBR64 entry pc: any literal `&pc + &n` reference inside the bytelist is
   shifted by -4 so that, when the trimmed bytes are loaded at the post-
   ENDBR64 pc, RIP-relative displacements still resolve to the same absolute
   targets as the original mc. *)

let define_trimmed =
  let trim_size = 4 in
  let trim_tm = `TRIM_LIST(4,0):byte list->byte list`
  and bl_ty = `:byte list` in
  fun name th ->
    let avs,_ = strip_forall(concl th) in
    if avs = [] then
      let eth = CONV_RULE(RAND_CONV TRIM_LIST_CONV) (AP_TERM trim_tm th) in
      let ldef =
        try mk_mconst(name,bl_ty) with Failure _ -> mk_var(name,bl_ty) in
      let def' = mk_eq(ldef,lhand(concl eth)) in
      TRANS (new_definition def') eth
    else
      let th_unq = SPEC_ALL th in
      let eth = CONV_RULE(RAND_CONV TRIM_LIST_CONV) (AP_TERM trim_tm th_unq) in
      let trimmed_body = rand (concl eth) in
      let pc_var = List.hd avs in
      let pc_int = mk_comb(`int_of_num`, pc_var) in
      let subst_body =
        let rec walk t =
          try
            let l,r = dest_binop `(+):int->int->int` t in
            if l = pc_int then
              let _,n = dest_comb r in
              if is_numeral n then
                let nv = dest_numeral n in
                if nv >=/ num trim_size then
                  mk_binop `(+):int->int->int` pc_int
                    (mk_comb(`int_of_num`, mk_numeral (nv -/ num trim_size)))
                else t
              else t
            else
              (match t with
               | Comb(f,x) -> mk_comb(walk f, walk x)
               | Abs(v,b) -> mk_abs(v, walk b)
               | _ -> t)
          with Failure _ ->
            (match t with
             | Comb(f,x) -> mk_comb(walk f, walk x)
             | Abs(v,b) -> mk_abs(v, walk b)
             | _ -> t)
        in walk trimmed_body in
      let arg_tys = List.map type_of avs in
      let new_const_ty =
        List.fold_right (fun t acc -> mk_fun_ty t acc) arg_tys bl_ty in
      let ldef =
        try mk_mconst(name,new_const_ty)
        with Failure _ -> mk_var(name,new_const_ty) in
      let lhs_named = List.fold_left (fun acc v -> mk_comb(acc,v)) ldef avs in
      let def' = mk_eq(lhs_named, subst_body) in
      let def_th = new_definition def' in
      GENL avs (SPEC_ALL def_th);;

let mk_bytelist = C (curry mk_list) `:byte`;;

let extract_coda_from_elf =
  let rec try_decode_all = function
    | Const("NIL",_) -> []
    | tm ->
      try let th = DECODE_CONV (mk_comb (`decode`, tm)) in
          let lhs,rhs = dest_eq (concl th) in
          let tm',next = dest_comb (rand rhs) in
          let rec len n = function
          | t when t == next -> n
          | Comb(Comb(Const("CONS",_),_),l) -> len (n+1) l
          | Comb(Comb(Const("APPEND",_),
              Comb(Comb(Const("bytelist_of_num",_),i),_)),l) ->
            len (n + Num.int_of_num (dest_numeral i)) l
          | Comb(Comb(Const("APPEND",_),
              Comb(Comb(Const("bytelist_of_int",_),i),_)),l) ->
            len (n + Num.int_of_num (dest_numeral i)) l
          | _ -> 0 in
          let a = len 0 (rand lhs), rand tm' in
          a :: try_decode_all next
      with Failure _ -> [] in
  fun possize file ->
    let bs = load_elf_contents_x86 file in
    let bt = term_of_bytes bs in
    let bl = dest_list bt in
    let codesize = if 0 <= possize && possize <= length bl then possize
                   else  itlist ((+) o fst) (try_decode_all bt) 0 in
    (mk_bytelist F_F mk_bytelist) (chop_list codesize bl);;

let stringize_coda_from_elf possize file =
  let bs:bytes = load_elf_contents_x86 file in
  let ct,dt = extract_coda_from_elf possize file in
  let cs = make_fn_word_list bs (decode_all ct) in
  let ds = string_of_term(mk_list(map rand (dest_list dt),`:num`)) in
  cs ^ ds ^ ";;\n";;

let print_coda_from_elf possize file =
  Format.print_string (stringize_coda_from_elf possize file);;

let save_coda_from_elf deffile possize objfile =
  file_of_string deffile (stringize_coda_from_elf possize objfile);;

let define_coda_from_elf possize codename dataname file =
  let ct,dt = extract_coda_from_elf possize file in
  let cdef = define_word_list codename ct in
  let ddef = define_word_list dataname dt in
  cdef,ddef;;

let define_coda_literal_from_elf codename dataname file codelist datalist =
  let ct,dt = extract_coda_from_elf (length codelist) file in
  let databytes =
    mk_bytelist
     (map (curry mk_comb `word:num->byte` o mk_small_numeral) datalist) in
  if databytes <> dt then failwith "data part mismatch" else
  let cdef = define_assert_word_list codename ct codelist in
  let ddef = define_word_list dataname dt in
  cdef,ddef;;

let mk_small_int =
  let caster = `(&):num->int`
  and negator = `(--):int->int` in
  fun (i:int) ->
    if i > 0
    then mk_comb (caster,(mk_small_numeral i))
    else mk_comb (negator,(mk_comb (caster, mk_small_numeral (-i))));;

(* Usage:
Use
  print_literal_from_elf "x86/generic/bignum_madd.o";;
to print the assembly listing, and copy it into the code below:

let bignum_madd_subroutine =
define_assert_from_elf "bignum_madd_subroutine" "x86/generic/bignum_madd.o" [
  0x53;                    (* PUSH (% rbx) *)
...
  0xc3                     (* RET *)
];;

let bignum_madd_mc = define_word_list "bignum_madd_mc"
  (trim_ret' (rhs (concl bignum_madd_subroutine)));; *)

(*** term_of_relocs_x86 returns a pair
    (a list of new HOL Light variables that represent the symbolic addresses,
     a HOL Light term that represents the 'symbolic' byte list).

    assert_relocs takes a pair
    (a list of HOL Light vars for the symbolic addresses,
     the symbolic byte list term)
    as well as the large OCaml function printed by print_literal_relocs_from_elf
    and checks whether the OCaml function matches the symbolic byte list term.
 ***)
let term_of_relocs_x86, assert_relocs =
  (* X86_64_PC32 *)
  let reloc = `APPEND (bytelist_of_int 4 (&v - (x:int)))` in
  let tm_plus = `(+):int->int->int` in
  let append_reloc (sym, add) = curry mk_comb (vsubst
      [sym,`v:num`;
       (mk_binop tm_plus `&(pc:num):int` (mk_small_int add)),
      `x:int`] reloc) in

  ((* term_of_relocs_x86 *)
   term_of_relocs (fun bstext,ty,off,sym,add ->
    if get_int_le bstext off 4 <> 0 then
      failwith "unexpected data in relocation" else
    4,
    if ty = X86_64_pc32 then
      append_reloc (sym, off - add)

    else failwith "unsupported relocation kind")),

  ((* assert_relocs *)
    let rec consume_bytes = function
    | [] -> I
    | n::ls -> function
      | pc, Comb(Comb(Const("CONS",_),Comb(Const("word",_),a)),tm)
        when 0 <= n && n <= 255 && dest_numeral a = num n ->
        consume_bytes ls (pc+1,tm)
      | pc, unknown_term ->
          let _ = if !decode_print_log then
           (Format.printf "assert_relocs: const byte mismatch from";
            Format.printf " pc 0x%x\n" pc;
            Format.printf "  remaining bytes: `%a`\n" pp_print_colored_term
                unknown_term)
          in failwith
            (Printf.sprintf
              "assert_relocs: const byte mismatch from pc 0x%x" pc) in

    let ptm = `bytelist_of_int 4 (&v - (&pc + i))` in
    let rec consume_reloc (sym,addend) = function
      | pc, Comb(Comb(Const("APPEND",_),v),tm) when
          v = vsubst [mk_var(sym,`:num`),`v:num`;
            mk_small_int (pc - addend),`i:int`] ptm ->
        (* pass *) (pc+4,tm)
      | pc, unknown_term ->
          let _ = if !decode_print_log then
           (Format.printf "assert_relocs: relocation info mismatch from";
            Format.printf " pc 0x%x\n" pc;
            Format.printf "  remaining bytes: `%a`\n" pp_print_colored_term
                unknown_term)
          in failwith
            (Printf.sprintf
              "assert_relocs: relocation info mismatch from pc 0x%x" pc) in
    (* opcode_fn is the large OCaml function printed by
       print_literal_relocs_from_elf *)
    fun (args,tm) opcode_fn ->
      let opcode_fn_implemented = opcode_fn
          (* This order should match the fn args printed by
            make_fn_word_list_reloc *)
          consume_bytes (* "b" *)
          consume_reloc (* ADDR *) in
      if type_of tm = `:byte list` then
        match rev_itlist I (opcode_fn_implemented) (0,tm) with
        | _,Const("NIL",_) -> ()
        | _ -> failwith "assert_relocs"
      else failwith "assert_relocs";
      (args,tm));;

let define_assert_relocs name (tm:term list * term) printed_opcodes_fn
    (constants:(string * bytes) list)
    :(thm(*machine code def*) * thm list(*data definitions of constants*)) =
  assert_relocs tm printed_opcodes_fn;
  let mc_def = define_relocated_mc name tm in
  let datatype = `:((8)word)list` in
  (mc_def,
   map (fun (name,data) ->
      let dataterm = term_of_bytes data in (* returns (8)word list *)
      (try new_definition(mk_eq(mk_var(name,datatype), dataterm))
        with Failure _ ->
            new_definition(mk_eq(mk_mconst(name,datatype), dataterm)))
    ) constants);;

let assert_relocs_from_elf
    ?(map_symbol_name=(fun str -> str ^ "_data"))
    (file:string) printed_opcodes_fn =
  let filebytes = load_file file in
  let text,constants,rel = load_elf_x86 filebytes in

  let constants = map (fun (name,y) -> (map_symbol_name name, y)) constants in
  let rel = map (fun (a,(b,name,c)) -> (a,(b,map_symbol_name name,c))) rel in

  assert_relocs (term_of_relocs_x86 (text,constants,rel)) printed_opcodes_fn;;

let define_assert_relocs_from_elf
    ?(map_symbol_name=(fun str -> str ^ "_data"))
    name (file:string) printed_opcodes_fn =
  let filebytes = load_file file in
  let text,constants,rel = load_elf_x86 filebytes in

  let constants = map (fun (name,y) -> (map_symbol_name name, y)) constants in
  let rel = map (fun (a,(b,name,c)) -> (a,(b,map_symbol_name name,c))) rel in

  let mc_def,constants_data_defs = define_assert_relocs
      name (term_of_relocs_x86 (text,constants,rel)) printed_opcodes_fn
      constants in
  (mc_def,constants_data_defs);;

let print_literal_relocs_from_elf
    ?(map_symbol_name=(fun str -> str ^ "_data"))
    (file:string) =
  let filebytes = load_file file in
  let text,constants,rel = load_elf_x86 filebytes in

  let constants = map (fun (name,y) -> (map_symbol_name name, y)) constants in
  let rel = map (fun (a,(b,name,c)) -> (a,(b,map_symbol_name name,c))) rel in

  print_string (make_fn_word_list_reloc (text,constants,rel)
    (decode_all (snd (term_of_relocs_x86 (text,constants,rel)))));;

let save_literal_relocs_from_elf
    ?(map_symbol_name=(fun str -> str ^ "_data"))
    (deffile:string) (objfile:string) =
  let filebytes = load_file objfile in
  let text,constants,rel = load_elf_x86 filebytes in

  let constants = map (fun (name,y) -> (map_symbol_name name, y)) constants in
  let rel = map (fun (a,(b,name,c)) -> (a,(b,map_symbol_name name,c))) rel in

  let ls = make_fn_word_list_reloc (text,constants,rel)
   (decode_all (snd (term_of_relocs_x86 (text,constants,rel)))) in
  file_of_string deffile ls;;

(* ------------------------------------------------------------------------- *)
(* A very specific form of lemma for simplifying expression representing     *)
(* the location of a symbol (in RIP-relative form)                           *)
(* ------------------------------------------------------------------------- *)

let riprel32_within_bounds = new_definition (
    `riprel32_within_bounds (tgt:num) (pc:num) <=>
      -- (&(2 EXP 31):int) <= (&tgt:int) - &pc /\
      (&tgt:int) - &pc < (&(2 EXP 31):int)`);;

let WORD32_ADD_SUB_OF_LT = prove
   (`forall pc tgt.
      riprel32_within_bounds tgt pc ==>
      word_add (word pc) (word_sx (iword (&tgt - &pc):int32)):int64 = word tgt`,
    IMP_REWRITE_TAC [riprel32_within_bounds; word_sx; IVAL_IWORD; WORD_IWORD;
      GSYM IWORD_INT_ADD; INT_SUB_ADD2; DIMINDEX_32; ARITH] THEN
    CONV_TAC INT_REDUCE_CONV);;

let RIP_REL_ADDR_FOLD = prove
 (`forall pc ofs ofs2 tgt.
  // For LEA
  (riprel32_within_bounds tgt (pc + ofs) ==>
    word (
      val (word (pc+ofs):(64)word) +
      val (word_sx (iword (&tgt - (&pc + &ofs)):int32):(64)word)):int64 =
    word tgt) /\
  // For LEA when referencing a local symbol
  (riprel32_within_bounds (tgt + (ofs + ofs2)) (pc + ofs) ==>
    word (
      val (word (pc+ofs):(64)word) +
      val (word_sx (iword (&tgt - (&pc + -- &ofs2)):int32):(64)word)):int64 =
    word (tgt + (ofs + ofs2))) /\
  // For calls
  (riprel32_within_bounds tgt pc ==>
   word_add (word pc) (word_sx (iword (&tgt - &pc):int32)):int64 = word tgt)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD32_ADD_SUB_OF_LT] THEN

  CONJ_TAC THENL [
    REWRITE_TAC[INT_OF_NUM_ADD] THEN
    MESON_TAC[WORD_ADD;WORD_VAL;WORD32_ADD_SUB_OF_LT];

    REWRITE_TAC[riprel32_within_bounds] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD;WORD_ADD;WORD_VAL] THEN
    REWRITE_TAC[word_sx;WORD_IWORD] THEN
    IMP_REWRITE_TAC[IVAL_IWORD] THEN
    REWRITE_TAC[GSYM IWORD_INT_ADD;DIMINDEX_32] THEN
    CONV_TAC (NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
    REWRITE_TAC[INT_ARITH`((x:int) + y + z) - (w + y) = x + z - w`;
        INT_ARITH`((x:int) - (y + -- z)) = x + z - y`] THEN
    DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN 
    AP_TERM_TAC THEN INT_ARITH_TAC
  ]);;
