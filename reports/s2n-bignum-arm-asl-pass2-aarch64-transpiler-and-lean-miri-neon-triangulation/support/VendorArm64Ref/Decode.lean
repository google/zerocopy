-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import VendorArm64Ref.Types

/-!
# `VendorArm64Ref.Decode`

Deterministic 32-bit AArch64 instruction decoder derived from
`awslabs/s2n-bignum@d4518712` (`arm/proofs/decode.ml`) augmented with:
1. Normative Armv8-A/v9-A ASL decode-legality guards rejecting constrained-unpredictable
   register overlaps (`LDP` `Rt == Rt2` including `XZR`, load/store writeback
   `Rn == Rt`, `STLXR` `Rs == Rt` or `Rs == Rn`) that `s2n-bignum` accepts into
   `ASSIGNS entirety`; and
2. The missing scalar/atomic/CRC32/NEON encodings (`UDIV`/`SDIV`, `LDAR`/`STLR`/
   `LDAXR`/`STLXR`/`CLREX`, `CRC32*`, `UDF`, `BTI`, `CMEQ`, `CMLT #0`, `UQADD`,
   `UQSUB`, `SQADD`, `SQSUB`, `SSHL`, `ADDP`, `UMINV`, `BSL`, 64-bit `REV64`/`UADDLP`,
   and `.b`/`.h` `UMOV`) emitted by `rustc -O3`.
-/

namespace VendorArm64Ref

def bits (w : BitVec 32) (lo len : Nat) : BitVec len :=
  BitVec.extractLsb' lo len w

def bit (w : BitVec 32) (idx : Nat) : Bool :=
  w.getLsbD idx

def decodeShift (sty : BitVec 2) : ShiftKind :=
  match sty.toNat with
  | 0 => .lsl
  | 1 => .lsr
  | 2 => .asr
  | _ => .ror

def decodeExtend (opt : BitVec 3) : ExtendKind :=
  match opt.toNat with
  | 0 => .uxtb | 1 => .uxth | 2 => .uxtw | 3 => .uxtx
  | 4 => .sxtb | 5 => .sxth | 6 => .sxtw | _ => .sxtx

/-- `Nat.rec`-total highest-set-bit index for `7`-bit `N:¬imms` (`decode.ml:176`). -/
def highestSetBit7 (v : BitVec 7) : Option Nat :=
  if v.getLsbD 6 then some 6
  else if v.getLsbD 5 then some 5
  else if v.getLsbD 4 then some 4
  else if v.getLsbD 3 then some 3
  else if v.getLsbD 2 then some 2
  else if v.getLsbD 1 then some 1
  else if v.getLsbD 0 then some 0
  else none

/-- Armv8-A `DecodeBitMasks` (`decode.ml:175-183`), implemented via `Nat.rec` (`0` `isPartial`). -/
def buildBitmask64 (esize sVal rVal : Nat) : BitVec 64 :=
  Nat.rec (motive := fun _ => BitVec 64)
    0#64
    (fun i acc =>
      if ((i + rVal) % esize) <= sVal then
        acc ||| (1#64 <<< i)
      else acc)
    64

def decodeBitmask (w : GpWidth) (nBit : Bool) (immr imms : BitVec 6) : Option (BitVec 64) :=
  if w == .w32 && nBit then none
  else
    let top : BitVec 1 := if nBit then 1#1 else 0#1
    let combined : BitVec 7 := top ++ (~~~imms)
    match highestSetBit7 combined with
    | none => none
    | some len =>
      if len < 1 then none
      else
        let esize := 2 ^ len
        let sVal := imms.toNat % esize
        let rVal := immr.toNat % esize
        if sVal == esize - 1 then none
        else
          let mask := buildBitmask64 esize sVal rVal
          some (maskWidth w mask)

def elemSizeOf2 (sz : BitVec 2) : Option ElemSize :=
  match sz.toNat with
  | 0 => some .e8
  | 1 => some .e16
  | 2 => some .e32
  | _ => some .e64

def decodeAluOp (op sBit : Bool) : AluOp :=
  match op, sBit with
  | false, false => .add
  | false, true  => .adds
  | true,  false => .sub
  | true,  true  => .subs

def decodeLogOp (opc : BitVec 2) (nBit : Bool) : LogOp :=
  match opc.toNat, nBit with
  | 0, false => .and_ | 0, true => .bic
  | 1, false => .orr  | 1, true => .orn
  | 2, false => .eor  | 2, true => .eon
  | _, false => .ands | _, true => .bics

def decodeSysBranch (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let sf : Bool := bit w 31
  let gpw : GpWidth := if sf then .x64 else .w32

  -- 1. Permanently UNDEFINED (`UDF #imm16`: `w[31:16] == 0`)
  if bits w 16 16 == 0#16 then
    some (.error .undefinedEncoding)

  -- 2. System hints (`NOP`, `BTI`) & `CLREX` & `RET`
  else if w == 0xd503201f#32 then
    some (.ok .hintNop)
  else if (w &&& 0xffffff3f#32) == 0xd503241f#32 then
    some (.ok .hintNop)
  else if (w &&& 0xfffff0ff#32) == 0xd503305f#32 then
    some (.ok .clrex)
  else if (bits w 10 22 == 0b1101011001011111000000#22) && (rd == 0#5) then
    some (.ok (.ret rn))

  -- 3. PC-relative `ADR` / `ADRP` (`decode.ml:328-331`)
  else if bits w 24 5 == 0b10000#5 then
    let page := bit w 31
    let immlo := bits w 29 2
    let immhi := bits w 5 19
    let imm21 : BitVec 21 := immhi ++ immlo
    let off := if page then (imm21 ++ 0#12).signExtend 64 else imm21.signExtend 64
    some (.ok (.adr page rd off))

  -- 4. Unconditional / Conditional / Compare / Test Branches (`decode.ml:254-266`)
  else if bits w 26 5 == 0b00101#5 then
    let link := bit w 31
    let imm26 := bits w 0 26
    some (.ok (.branchImm link ((imm26 ++ 0#2).signExtend 64)))
  else if (bits w 24 8 == 0b01010100#8) && !(bit w 4) then
    let imm19 := bits w 5 19
    let cond  := bits w 0 4
    some (.ok (.branchCond cond ((imm19 ++ 0#2).signExtend 64)))
  else if bits w 25 6 == 0b011010#6 then
    let nz := bit w 24
    let imm19 := bits w 5 19
    some (.ok (.cbz gpw nz rd ((imm19 ++ 0#2).signExtend 64)))
  else if bits w 25 6 == 0b011011#6 then
    let nz := bit w 24
    let b5 := bit w 31
    let b40 := (bits w 19 5).toNat
    let imm14 := bits w 5 14
    some (.ok (.tbz nz rd ((if b5 then 32 else 0) + b40) ((imm14 ++ 0#2).signExtend 64)))
  else none

def decodeDpImm (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5
  let sf : Bool := bit w 31
  let gpw : GpWidth := if sf then .x64 else .w32

  -- 5. Scalar Add/Sub Immediate (`decode.ml:213-219`)
  if bits w 23 6 == 0b100010#6 then
    let sh := bit w 22
    let imm12 := (bits w 10 12).zeroExtend 64
    let imm := if sh then imm12 <<< 12 else imm12
    some (.ok (.aluImm gpw (decodeAluOp (bit w 30) (bit w 29)) rd rn imm))

  -- 6. Scalar Logical Immediate (`decode.ml:243-253`)
  else if bits w 23 6 == 0b100100#6 then
    let opc := bits w 29 2
    let nBit := bit w 22
    let immr := bits w 16 6
    let imms := bits w 10 6
    some (match decodeBitmask gpw nBit immr imms with
      | some mask => .ok (.logImm gpw (decodeLogOp opc false) rd rn mask)
      | none => .error .undefinedEncoding)

  -- 7. Scalar Move Wide `MOVN`/`MOVZ`/`MOVK` (`decode.ml:285-288`)
  else if bits w 23 6 == 0b100101#6 then
    let opc := bits w 29 2
    let hw := (bits w 21 2).toNat
    let imm16 := bits w 5 16
    some (if !sf && hw >= 2 then .error .undefinedEncoding
      else
        match opc.toNat with
        | 0 => .ok (.moveWide gpw .movn rd imm16 (hw * 16))
        | 2 => .ok (.moveWide gpw .movz rd imm16 (hw * 16))
        | 3 => .ok (.moveWide gpw .movk rd imm16 (hw * 16))
        | _ => .error .undefinedEncoding)

  -- 8. Bitfield `SBFM` / `BFM` / `UBFM` (`decode.ml:297-306`) & `EXTR` (`289-293`)
  else if bits w 23 6 == 0b100110#6 then
    let opc := bits w 29 2
    let nBit := bit w 22
    let immr := (bits w 16 6).toNat
    let imms := (bits w 10 6).toNat
    some (if sf != nBit then .error .undefinedEncoding
      else if !sf && (immr >= 32 || imms >= 32) then .error .undefinedEncoding
      else
        match opc.toNat with
        | 0 => .ok (.bitfield gpw .sbfm rd rn immr imms)
        | 1 => .ok (.bitfield gpw .bfm  rd rn immr imms)
        | 2 => .ok (.bitfield gpw .ubfm rd rn immr imms)
        | _ => .error .undefinedEncoding)
  else if (bits w 23 8 == 0b00100111#8) && !(bit w 21) then
    let nBit := bit w 22
    let imms := (bits w 10 6).toNat
    some (if sf != nBit then .error .undefinedEncoding
      else if !sf && imms >= 32 then .error .undefinedEncoding
      else .ok (.extr gpw rd rn rm imms))
  else none

def decodeDpReg (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5
  let sf : Bool := bit w 31
  let gpw : GpWidth := if sf then .x64 else .w32

  -- 9. Scalar Add/Sub Shifted & Extended Register (`decode.ml:220-242`)
  if (bits w 24 5 == 0b01011#5) && !(bit w 21) then
    let sty := bits w 22 2
    let sam := (bits w 10 6).toNat
    some (if sty == 3#2 then .error .undefinedEncoding
      else if !sf && sam >= 32 then .error .undefinedEncoding
      else .ok (.aluShift gpw (decodeAluOp (bit w 30) (bit w 29)) rd rn rm (decodeShift sty) sam))
  else if bits w 21 8 == 0b01011001#8 then
    let opt := bits w 13 3
    let imm3 := (bits w 10 3).toNat
    some (if imm3 > 4 then .error .undefinedEncoding
      else .ok (.aluExt gpw (decodeAluOp (bit w 30) (bit w 29)) rd rn rm (decodeExtend opt) imm3))

  -- 10. Scalar Logical Shifted Register (`decode.ml:277-284`)
  else if bits w 24 5 == 0b01010#5 then
    let opc := bits w 29 2
    let sty := bits w 22 2
    let nBit := bit w 21
    let sam := (bits w 10 6).toNat
    some (if !sf && sam >= 32 then .error .undefinedEncoding
      else .ok (.logShift gpw (decodeLogOp opc nBit) rd rn rm (decodeShift sty) sam))

  -- 11. Add/Sub with Carry (`ADC`/`ADCS`/`SBC`/`SBCS`, `decode.ml:210-212`)
  else if (bits w 21 8 == 0b11010000#8) && (bits w 10 6 == 0#6) then
    let cop : CarryOp := match bit w 30, bit w 29 with
      | false, false => .adc | false, true => .adcs
      | true,  false => .sbc | true,  true => .sbcs
    some (.ok (.aluCarry gpw cop rd rn rm))

  -- 12. Conditional Compare (`CCMN`/`CCMP`, `decode.ml:271-276`) & Select (`CSEL`.., `267-270`)
  else if (bits w 21 9 == 0b111010010#9) && !(bit w 4) && !(bit w 10) then
    let sub := bit w 30
    let cond := bits w 12 4
    let nzcv := bits w 0 4
    let isImm := bit w 11
    let rhs := if isImm then Sum.inr (bits w 16 5) else Sum.inl rm
    some (.ok (.condCmp gpw sub rn rhs nzcv cond))
  else if (bits w 21 9 == 0b011010100#9) && !(bit w 11) then
    let cop : CondSelOp := match bit w 30, bit w 10 with
      | false, false => .csel  | false, true => .csinc
      | true,  false => .csinv | true,  true => .csneg
    some (.ok (.condSel gpw cop rd rn rm (bits w 12 4)))

  -- 13. Data-processing 2-source (`UDIV`/`SDIV`, `LSLV`/`LSRV`/`ASRV`/`RORV`, `CRC32*`)
  else if bits w 21 10 == 0b0011010110#10 then
    let opcode2 := bits w 10 6
    some (if opcode2 == 0b000010#6 then .ok (.divInt gpw false rd rn rm)
      else if opcode2 == 0b000011#6 then .ok (.divInt gpw true rd rn rm)
      else if bits w 12 4 == 0b0010#4 then
        let sh := decodeShift (bits w 10 2)
        .ok (.shiftVar gpw sh rd rn rm)
      else if bit w 14 && (bits w 13 3 == 0b010#3) then
        let castagnoli := bit w 12
        let sz := (bits w 10 2).toNat
        if sf && sz != 3 then .error .undefinedEncoding
        else if !sf && sz == 3 then .error .undefinedEncoding
        else .ok (.crc32 castagnoli (2 ^ sz) rd rn rm)
      else .error .undefinedEncoding)

  -- 14. Data-processing 1-source (`CLZ`, `REV`, `decode.ml:307-320`) & 3-source (`MADD`.., `310-327`)
  else if bits w 10 21 == 0b101101011000000000100#21 then
    some (.ok (.clz gpw rd rn))
  else if bits w 11 20 == 0b10110101100000000001#20 then
    some (if sf != bit w 10 then .error .undefinedEncoding
      else .ok (.revBytes gpw rd rn))
  else if bits w 21 10 == 0b0011011000#10 then
    let ra : Reg5 := bits w 10 5
    some (.ok (.madd gpw (bit w 15) rd rn rm ra))
  else if (bits w 21 11 == 0b10011011010#11) && (bits w 10 6 == 0b011111#6) then
    some (.ok (.mulHigh true rd rn rm))
  else if (bits w 21 11 == 0b10011011110#11) && (bits w 10 6 == 0b011111#6) then
    some (.ok (.mulHigh false rd rn rm))
  else if bits w 21 11 == 0b10011011101#11 then
    let ra : Reg5 := bits w 10 5
    some (.ok (.umaddl (bit w 15) rd rn rm ra))
  else none

def decodeLoadsStores (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5

  -- 15. Load-Acquire / Store-Release & Exclusive Monitor (`LDAR`, `STLR`, `LDAXR`, `STLXR`)
  if (bits w 24 6 == 0b001000#6) && bit w 31 then
    let wSz : GpWidth := if bit w 30 then .x64 else .w32
    let o2 := bit w 23
    let lBit := bit w 22
    let o1 := bit w 21
    let rs : Reg5 := bits w 16 5
    let o0 := bit w 15
    let rt2 : Reg5 := bits w 10 5
    some (if o1 || (rt2 != reg31) then .error .undefinedEncoding
      else if o2 && lBit && o0 && (rs == reg31) then
        .ok (.ldar wSz false rd rn)
      else if o2 && !lBit && o0 && (rs == reg31) then
        .ok (.stlr wSz rd rn)
      else if !o2 && lBit && o0 && (rs == reg31) then
        .ok (.ldar wSz true rd rn)
      else if !o2 && !lBit && o0 then
        if (rs == rd) || (rs == rn && rn != reg31) then
          .error .constrainedUnpredictable
        else
          .ok (.stlxr wSz rs rd rn)
      else .error .undefinedEncoding)

  -- 16. Load/Store Pair GP & SIMD (`LDP` / `STP`, `decode.ml:99-105`, `instruction.ml:3069`)
  else if (bits w 27 3 == 0b101#3) && !(bit w 25) then
    let opc := bits w 30 2
    let isSimd := bit w 26
    let idxKind := (bits w 23 2).toNat
    let load := bit w 22
    let imm7 := bits w 15 7
    let rt2 : Reg5 := bits w 10 5
    some (if idxKind == 0 then .error .undefinedEncoding
      else if !isSimd && opc == 0b01#2 then .error .undefinedEncoding
      else if !isSimd && opc == 0b11#2 then .error .undefinedEncoding
      else if isSimd && opc == 0b11#2 then .error .undefinedEncoding
      else
        let scale := if isSimd then (if opc == 0b10#2 then 4 else if opc == 0b01#2 then 3 else 2)
                     else (if opc == 0b10#2 then 3 else 2)
        let off64 : BitVec 64 := (imm7.signExtend 64) <<< scale
        let mode : AddrMode :=
          if idxKind == 1 then .postIndex off64
          else if idxKind == 3 then .preIndex off64
          else .unsignedOff off64
        let wback := (idxKind == 1) || (idxKind == 3)
        if load && (rd == rt2) then
          .error .constrainedUnpredictable
        else if !isSimd && wback && (rn != reg31) && (rn == rd || rn == rt2) then
          .error .constrainedUnpredictable
        else if isSimd then
          if opc == 0b00#2 then .error .undefinedEncoding
          else
            let vw : VecWidth := if opc == 0b10#2 then .q128 else .d64
            .ok (.ldstPairSimd load vw rd rt2 rn mode)
        else
          let pw : GpWidth := if opc == 0b10#2 then .x64 else .w32
          .ok (.ldstPairGp load pw rd rt2 rn mode))

  -- 17. Single-Register Load/Store GP & SIMD (`LDR`/`STR`/`LDRB`/`LDRH`/`LDRSB`/`LDRSH`)
  else if bits w 27 3 == 0b111#3 then
    let sz2 := (bits w 30 2).toNat
    let isSimd := bit w 26
    let isUnsignedImm := bit w 24
    let opc := (bits w 22 2).toNat
    some (if isSimd then
        let qForm := (sz2 == 0) && (opc == 2 || opc == 3)
        let dForm := (sz2 == 3) && (opc == 0 || opc == 1)
        if !qForm && !dForm then .error .undefinedEncoding
        else
          let load := (opc % 2) == 1
          let vw : VecWidth := if qForm then .q128 else .d64
          let scale := if qForm then 4 else 3
          if isUnsignedImm then
            let off := ((bits w 10 12).zeroExtend 64) <<< scale
            .ok (.ldstSimd load vw rd rn (.unsignedOff off))
          else if !(bit w 21) then
            let idx2 := (bits w 10 2).toNat
            let off := (bits w 12 9).signExtend 64
            match idx2 with
            | 0 => .ok (.ldstSimd load vw rd rn (.unscaledOff off))
            | 1 => .ok (.ldstSimd load vw rd rn (.postIndex off))
            | 3 => .ok (.ldstSimd load vw rd rn (.preIndex off))
            | _ => .error .undefinedEncoding
          else .error .undefinedEncoding
      else
        let mszOpt : Option (Bool × MemSize × Nat) :=
          match sz2, opc with
          | 0, 0 => some (false, .b8, 0)
          | 0, 1 => some (true,  .b8, 0)
          | 0, 2 => some (true,  .sb8_64, 0)
          | 0, 3 => some (true,  .sb8_32, 0)
          | 1, 0 => some (false, .h16, 1)
          | 1, 1 => some (true,  .h16, 1)
          | 1, 2 => some (true,  .sh16_64, 1)
          | 1, 3 => some (true,  .sh16_32, 1)
          | 2, 0 => some (false, .w32, 2)
          | 2, 1 => some (true,  .w32, 2)
          | 3, 0 => some (false, .x64, 3)
          | 3, 1 => some (true,  .x64, 3)
          | _, _ => none
        match mszOpt with
        | none => .error .undefinedEncoding
        | some (load, msz, scale) =>
          if isUnsignedImm then
            let off := ((bits w 10 12).zeroExtend 64) <<< scale
            .ok (.ldstGp load msz rd rn (.unsignedOff off))
          else if !(bit w 21) then
            let idx2 := (bits w 10 2).toNat
            let off := (bits w 12 9).signExtend 64
            let wback := (idx2 == 1) || (idx2 == 3)
            if wback && (rn != reg31) && (rn == rd) then
              .error .constrainedUnpredictable
            else
              match idx2 with
              | 0 => .ok (.ldstGp load msz rd rn (.unscaledOff off))
              | 1 => .ok (.ldstGp load msz rd rn (.postIndex off))
              | 3 => .ok (.ldstGp load msz rd rn (.preIndex off))
              | _ => .error .undefinedEncoding
          else if bits w 10 2 == 0b10#2 then
            let opt := bits w 13 3
            let sBit := bit w 12
            if (opt.toNat % 4) == 0 || (opt.toNat % 4) == 1 then .error .undefinedEncoding
            else
              let sh := if sBit then scale else 0
              .ok (.ldstGp load msz rd rn (.regOff rm (decodeExtend opt) sh))
          else .error .undefinedEncoding)

  -- 18. Scalar `FMOV` GP <-> SIMD (`0x1e260000`, `0x1e270000`, `0x9e660000`, `0x9e670000`)
  else if (w &&& 0xfffffc00#32) == 0x1e260000#32 then
    some (.ok (.fmovVecToGp .w32 rd rn))
  else if (w &&& 0xfffffc00#32) == 0x9e660000#32 then
    some (.ok (.fmovVecToGp .x64 rd rn))
  else if (w &&& 0xfffffc00#32) == 0x1e270000#32 then
    some (.ok (.fmovGpToVec .w32 rd rn))
  else if (w &&& 0xfffffc00#32) == 0x9e670000#32 then
    some (.ok (.fmovGpToVec .x64 rd rn))
  else none

def decodeCryptoExt (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5
  -- 19. Armv8 AES & SHA-256 & SHA-512 Cryptographic Extensions (`decode.ml:1069-1116`)
  if bits w 10 22 == 0b0100111000101000010010#22 then some (.ok (.cryptoAes .aese rd rn))
  else if bits w 10 22 == 0b0100111000101000011010#22 then some (.ok (.cryptoAes .aesmc rd rn))
  else if bits w 10 22 == 0b0100111000101000010110#22 then some (.ok (.cryptoAes .aesd rd rn))
  else if bits w 10 22 == 0b0100111000101000011110#22 then some (.ok (.cryptoAes .aesimc rd rn))
  else if (bits w 21 11 == 0b01011110000#11) && (bits w 10 6 == 0b010000#6) then some (.ok (.cryptoSha256 .h rd rn rm))
  else if (bits w 21 11 == 0b01011110000#11) && (bits w 10 6 == 0b010100#6) then some (.ok (.cryptoSha256 .h2 rd rn rm))
  else if bits w 10 22 == 0b0101111000101000001010#22 then some (.ok (.cryptoSha256 .su0 rd rn 0#5))
  else if (bits w 21 11 == 0b01011110000#11) && (bits w 10 6 == 0b011000#6) then some (.ok (.cryptoSha256 .su1 rd rn rm))
  else if (bits w 21 11 == 0b11001110011#11) && (bits w 10 6 == 0b100000#6) then some (.ok (.cryptoSha512 .h rd rn rm))
  else if (bits w 21 11 == 0b11001110011#11) && (bits w 10 6 == 0b100001#6) then some (.ok (.cryptoSha512 .h2 rd rn rm))
  else if bits w 10 22 == 0b1100111011000000100000#22 then some (.ok (.cryptoSha512 .su0 rd rn 0#5))
  else if (bits w 21 11 == 0b11001110011#11) && (bits w 10 6 == 0b100010#6) then some (.ok (.cryptoSha512 .su1 rd rn rm))
  else none

def decodeNeon (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5
  -- 20. Advanced SIMD (`NEON`) Instructions (`w[28:25] == 0b0111` and `w[31] == 0`)
  if !(bit w 31) && (bits w 25 4 == 0b0111#4) then
    let q := bit w 30
    let u := bit w 29
    let vw : VecWidth := if q then .q128 else .d64
    let sz2 := bits w 22 2
    some (
      -- 20a. `EXT`
      if u && (bits w 21 8 == 0b01110000#8) && !(bit w 15) && !(bit w 10) then
        let imm4 := (bits w 11 4).toNat
        if !q && imm4 >= 8 then .error .undefinedEncoding
        else .ok (.neonExt vw rd rn rm imm4)
      -- 20b. `TBL` 1-register
      else if !u && (bits w 21 8 == 0b01110000#8) && (bits w 10 6 == 0b000000#6) then
        .ok (.neonTbl1 vw rd rn rm)
      -- 20c. `DUP` general / `UMOV` / `INS` general
      else if (bits w 21 8 == 0b01110000#8) && !(bit w 15) && (bit w 10) then
        let imm5 := bits w 16 5
        let op4  := (bits w 11 4).toNat
        let imm5Nat := imm5.toNat
        let laneInfo : Option (ElemSize × Nat) :=
          if (imm5Nat % 2) == 1 then some (.e8, imm5Nat / 2)
          else if (imm5Nat % 4) == 2 then some (.e16, imm5Nat / 4)
          else if (imm5Nat % 8) == 4 then some (.e32, imm5Nat / 8)
          else if (imm5Nat % 16) == 8 then some (.e64, imm5Nat / 16)
          else none
        match laneInfo with
        | none => .error .undefinedEncoding
        | some (es, idx) =>
          if !u && op4 == 0b0001 then
            if !q && es == .e64 then .error .undefinedEncoding
            else .ok (.neonDupGp vw es rd rn)
          else if !u && op4 == 0b0011 && q then
            .ok (.neonInsGp es rd rn idx)
          else if !u && op4 == 0b0111 then
            if (es == .e64 && !q) || (es != .e64 && q) then .error .undefinedEncoding
            else .ok (.neonUmov es rd rn idx)
          else .error .undefinedEncoding
      -- 20d. `INS` element
      else if q && u && (bits w 21 8 == 0b01110000#8) && !(bit w 15) && (bit w 10) then
        .error .undefinedEncoding
      -- 20e. Shift by immediate & Modified Immediate `MOVI`
      else if bit w 24 then
        let immh := bits w 19 4
        let immb := bits w 16 3
        let op6  := bits w 10 6
        if immh == 0#4 then
          if bits w 10 2 == 0b01#2 then
            let cmode := (bits w 12 4).toNat
            let abcdefgh : BitVec 8 := (bits w 16 3) ++ (bits w 5 5)
            if u && cmode == 0b1110 then
              let b0 : BitVec 8 := if abcdefgh.getLsbD 0 then 0xff#8 else 0#8
              let b1 : BitVec 8 := if abcdefgh.getLsbD 1 then 0xff#8 else 0#8
              let b2 : BitVec 8 := if abcdefgh.getLsbD 2 then 0xff#8 else 0#8
              let b3 : BitVec 8 := if abcdefgh.getLsbD 3 then 0xff#8 else 0#8
              let b4 : BitVec 8 := if abcdefgh.getLsbD 4 then 0xff#8 else 0#8
              let b5 : BitVec 8 := if abcdefgh.getLsbD 5 then 0xff#8 else 0#8
              let b6 : BitVec 8 := if abcdefgh.getLsbD 6 then 0xff#8 else 0#8
              let b7 : BitVec 8 := if abcdefgh.getLsbD 7 then 0xff#8 else 0#8
              let imm64 : BitVec 64 := ((b7 ++ b6) ++ (b5 ++ b4)) ++ ((b3 ++ b2) ++ (b1 ++ b0))
              .ok (.neonMovi vw rd imm64)
            else if !u && cmode == 0b1110 then
              let imm16 : BitVec 16 := abcdefgh ++ abcdefgh
              let imm32 : BitVec 32 := imm16 ++ imm16
              .ok (.neonMovi vw rd (imm32 ++ imm32))
            else if !u && (cmode == 0b0000 || cmode == 0b0010 || cmode == 0b0100 || cmode == 0b0110) then
              let sh := (cmode / 2) * 8
              let imm32 : BitVec 32 := (abcdefgh.zeroExtend 32) <<< sh
              .ok (.neonMovi vw rd (imm32 ++ imm32))
            else .error .undefinedEncoding
          else .error .undefinedEncoding
        else
          if immh.getLsbD 3 && !q then .error .undefinedEncoding
          else
            let (es, esBits) : ElemSize × Nat :=
              if immh.getLsbD 3 then (.e64, 64)
              else if immh.getLsbD 2 then (.e32, 32)
              else if immh.getLsbD 1 then (.e16, 16)
              else (.e8, 8)
            let imm7 := ((immh ++ immb) : BitVec 7).toNat
            if !u && op6 == 0b010101#6 then
              .ok (.neonShiftImm vw es .shl rd rn (imm7 - esBits))
            else if op6 == 0b000001#6 then
              let sop : NeonShiftImmOp := if u then .ushr else .sshr
              .ok (.neonShiftImm vw es sop rd rn (2 * esBits - imm7))
            else .error .undefinedEncoding
      -- 20f..20h. Disjoint dispatch when `bit w 21 == true` (`!(bit w 24)`)
      else if bit w 21 then
        let op6 := bits w 10 6
        let lo2 := bits w 10 2
        if lo2 == 0b00#2 then
          if !u && op6 == 0b111000#6 then
            if sz2 == 0b00#2 then .ok (.neonPmull q .e8 rd rn rm)
            else if sz2 == 0b11#2 then .ok (.neonPmull q .e64 rd rn rm)
            else .error .undefinedEncoding
          else .error .undefinedEncoding
        else if lo2 == 0b10#2 then
          let hi4 := bits w 17 4
          let op5 := (bits w 12 5).toNat
          match elemSizeOf2 sz2 with
          | none => .error .undefinedEncoding
          | some es =>
            if hi4 == 0b0000#4 then
              if !u && op5 == 0b00000 && es != .e64 then
                .ok (.neonRev64 vw es rd rn)
              else if u && op5 == 0b00010 && es != .e64 then
                .ok (.neonUaddlp vw es rd rn)
              else if !u && op5 == 0b00101 && es == .e8 then
                .ok (.neonCnt vw rd rn)
              else if !u && op5 == 0b01001 then
                if es == .e64 && !q then .error .undefinedEncoding
                else .ok (.neonCmp vw es .cmeqZero rd rn 0#5)
              else if !u && op5 == 0b01010 then
                if es == .e64 && !q then .error .undefinedEncoding
                else .ok (.neonCmp vw es .cmltZero rd rn 0#5)
              else .error .undefinedEncoding
            else if hi4 == 0b1000#4 then
              if es == .e64 || (es == .e32 && !q) then .error .undefinedEncoding
              else if u && op5 == 0b00011 then
                .ok (.neonReduce vw es .uaddlv rd rn)
              else if !u && op5 == 0b11011 then
                .ok (.neonReduce vw es .addv rd rn)
              else if u && op5 == 0b01010 then
                .ok (.neonReduce vw es .umaxv rd rn)
              else if u && op5 == 0b11010 then
                .ok (.neonReduce vw es .uminv rd rn)
              else .error .undefinedEncoding
            else .error .undefinedEncoding
        else if op6 == 0b000111#6 then
          match u, sz2.toNat with
          | false, 0 => .ok (.neonLogic vw .and_ rd rn rm)
          | false, 1 => .ok (.neonLogic vw .bic  rd rn rm)
          | false, 2 => .ok (.neonLogic vw .orr  rd rn rm)
          | true,  0 => .ok (.neonLogic vw .eor  rd rn rm)
          | true,  1 => .ok (.neonLogic vw .bsl  rd rn rm)
          | true,  2 => .ok (.neonLogic vw .bit_ rd rn rm)
          | true,  3 => .ok (.neonLogic vw .bif_ rd rn rm)
          | _, _     => .error .undefinedEncoding
        else
          match elemSizeOf2 sz2 with
          | none => .error .undefinedEncoding
          | some es =>
            if es == .e64 && !q then .error .undefinedEncoding
            else if op6 == 0b100001#6 then
              .ok (.neonArith vw es (if u then .sub else .add) rd rn rm)
            else if op6 == 0b000011#6 then
              .ok (.neonArith vw es (if u then .uqadd else .sqadd) rd rn rm)
            else if op6 == 0b001011#6 then
              .ok (.neonArith vw es (if u then .uqsub else .sqsub) rd rn rm)
            else if !u && op6 == 0b101111#6 then
              .ok (.neonArith vw es .addp rd rn rm)
            else if u && op6 == 0b100011#6 then
              .ok (.neonCmp vw es .cmeq rd rn rm)
            else if op6 == 0b001101#6 then
              .ok (.neonCmp vw es (if u then .cmhi else .cmgt) rd rn rm)
            else if !u && op6 == 0b001111#6 then
              .ok (.neonCmp vw es .cmge rd rn rm)
            else if op6 == 0b010001#6 then
              .ok (.neonShiftVar vw es (!u) rd rn rm)
            else if u && op6 == 0b100111#6 && es == .e8 then
              .ok (.neonPmul vw rd rn rm)
            else .error .undefinedEncoding
      else .error .undefinedEncoding)
  else none

def decodeWord32 (w : BitVec 32) : Except ArmFault Instr :=
  match decodeSysBranch w with
  | some r => r
  | none =>
    match decodeDpImm w with
    | some r => r
    | none =>
      match decodeDpReg w with
      | some r => r
      | none =>
        match decodeLoadsStores w with
        | some r => r
        | none =>
          match decodeCryptoExt w with
          | some r => r
          | none =>
            match decodeNeon w with
            | some r => r
            | none => .error .undefinedEncoding

end VendorArm64Ref
