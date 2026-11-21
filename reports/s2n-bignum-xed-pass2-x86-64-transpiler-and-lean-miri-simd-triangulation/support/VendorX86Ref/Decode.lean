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
import Init.Data.List.TakeDrop
import Init.Data.Nat.Basic
import VendorX86Ref.Types

/-!
# `VendorX86Ref.Decode`

Total 16-byte fetch-window x86-64 decoder combining `awslabs/s2n-bignum@d4518712`
opcode structure with the `intelxed/xed@0bcb6237` legality overlay:
1. Iterative legacy + REX prefix scanner enforcing REX nullification by trailing
   legacy prefixes (`41 66 90 -> NOP 3`) and consecutive REX last-wins (`41 40 90`).
2. Strict 15-byte instruction-length cap (`len > 15 -> .fault .gp0LengthExceeds15`).
3. VEX/EVEX prefix exclusions (`LOCK`/`66`/`F2`/`F3`/`REX` before VEX/EVEX ->
   `.fault .udVexPrefix`, while segment/`67H` prefixes remain legal per Intel SDM).
4. `LOCK` (`0xF0`) memory-destination `LOCKABLE` table (`#UD` on register forms
   or non-lockable opcodes).
5. VEX `vvvv = 1111` (`NOVSR`) and `L` (`VL128`/`VL256`) `#UD` field checks.
-/

namespace VendorX86Ref

inductive RepPfx where
  | none | repz | repnz
  deriving DecidableEq, Repr

structure PrefixState where
  has66      : Bool := false
  rep        : RepPfx := .none
  hasLock    : Bool := false
  hasSegOr67 : Bool := false
  rex        : Option (BitVec 4) := none
  count      : Nat := 0
  deriving DecidableEq, Repr

def rexBit (rex : Option (BitVec 4)) (idx : Nat) : Bool :=
  match rex with
  | none => false
  | some r => r.getLsbD idx

def rexB (rex : Option (BitVec 4)) : Bool := rexBit rex 0
def rexX (rex : Option (BitVec 4)) : Bool := rexBit rex 1
def rexR (rex : Option (BitVec 4)) : Bool := rexBit rex 2
def rexW (rex : Option (BitVec 4)) : Bool := rexBit rex 3

def opSizeOf (rex : Option (BitVec 4)) : OpSize :=
  if rexW rex then .s64 else .s32

def mkRegIdx (hiBit : Bool) (lo3 : BitVec 3) : Nat :=
  (if hiBit then 8 else 0) + lo3.toNat

def readLe16? : List (BitVec 8) → Option (BitVec 16 × List (BitVec 8))
  | b0 :: b1 :: rest => some (b1 ++ b0, rest)
  | _ => none

def readLe32? : List (BitVec 8) → Option (BitVec 32 × List (BitVec 8))
  | b0 :: b1 :: b2 :: b3 :: rest => some (b3 ++ (b2 ++ (b1 ++ b0)), rest)
  | _ => none

def readLe64? : List (BitVec 8) → Option (BitVec 64 × List (BitVec 8))
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    some (pack8Bytes b0 b1 b2 b3 b4 b5 b6 b7, rest)
  | _ => none

/-- Bounded iterative prefix scanner (at most 16 bytes inspected), expressed via
    `Nat.rec` so Lean emits zero `*._unsafe_rec` (`isPartial`) codegen helpers. -/
def scanPrefixes (fuel : Nat) (st : PrefixState) (bs : List (BitVec 8)) :
    PrefixState × List (BitVec 8) :=
  Nat.rec (motive := fun _ => PrefixState → List (BitVec 8) → PrefixState × List (BitVec 8))
    (fun s rem => (s, rem))
    (fun _ ih s rem =>
      match rem with
      | [] => (s, [])
      | b :: rest =>
        if b == 0x66#8 then
          ih { s with has66 := true, rex := none, count := s.count + 1 } rest
        else if b == 0xF2#8 then
          ih { s with rep := .repnz, rex := none, count := s.count + 1 } rest
        else if b == 0xF3#8 then
          ih { s with rep := .repz, rex := none, count := s.count + 1 } rest
        else if b == 0xF0#8 then
          ih { s with hasLock := true, rex := none, count := s.count + 1 } rest
        else if b == 0x2E#8 || b == 0x36#8 || b == 0x3E#8 || b == 0x26#8 ||
                b == 0x64#8 || b == 0x65#8 || b == 0x67#8 then
          ih { s with hasSegOr67 := true, rex := none, count := s.count + 1 } rest
        else if (b &&& 0xF0#8) == 0x40#8 then
          ih { s with rex := some (BitVec.extractLsb' 0 4 b), count := s.count + 1 } rest
        else
          (s, b :: rest))
    fuel st bs

def condOfNib (n : Nat) : Cond :=
  match n % 16 with
  | 0  => .o  | 1  => .no | 2  => .b  | 3  => .ae
  | 4  => .e  | 5  => .ne | 6  => .be | 7  => .a
  | 8  => .s  | 9  => .ns | 10 => .p  | 11 => .np
  | 12 => .l  | 13 => .ge | 14 => .le | _  => .g

def aluOpOfIdx (idx : Nat) : Option AluOp :=
  match idx with
  | 0 => some .add | 1 => some .or  | 2 => some .adc | 3 => some .sbb
  | 4 => some .and | 5 => some .sub | 6 => some .xor | 7 => some .cmp
  | _ => none

/-- Parse ModR/M (+ optional SIB + displacement), returning `(regIdx, RmOp, consumedBytes, rest)`. -/
def parseModRm (rBit xBit bBit : Bool) :
    List (BitVec 8) → Option (Nat × RmOp × Nat × List (BitVec 8))
  | [] => none
  | mrm :: rest =>
    let mod2 := (BitVec.extractLsb' 6 2 mrm).toNat
    let reg3 := BitVec.extractLsb' 3 3 mrm
    let rm3  := BitVec.extractLsb' 0 3 mrm
    let regIdx := mkRegIdx rBit reg3
    let rmIdx  := mkRegIdx bBit rm3
    if mod2 == 3 then
      some (regIdx, .reg (gprOfNat rmIdx), 1, rest)
    else if rm3.toNat == 4 then
      match rest with
      | [] => none
      | sib :: restSib =>
        let scale2 := (BitVec.extractLsb' 6 2 sib).toNat
        let idx3   := BitVec.extractLsb' 3 3 sib
        let base3  := BitVec.extractLsb' 0 3 sib
        let idxFull := mkRegIdx xBit idx3
        let baseFull := mkRegIdx bBit base3
        let indexOpt : Option (Gpr × Nat) :=
          if idxFull == 4 then none else some (gprOfNat idxFull, scale2)
        if mod2 == 0 && base3.toNat == 5 then
          match readLe32? restSib with
          | none => none
          | some (d32, restD) =>
            some (regIdx, .mem { base := none, index := indexOpt, disp := sext32To64 d32 }, 6, restD)
        else if mod2 == 0 then
          some (regIdx, .mem { base := some (gprOfNat baseFull), index := indexOpt, disp := 0#64 }, 2, restSib)
        else if mod2 == 1 then
          match restSib with
          | [] => none
          | d8 :: restD =>
            some (regIdx, .mem { base := some (gprOfNat baseFull), index := indexOpt, disp := sext8To64 d8 }, 3, restD)
        else
          match readLe32? restSib with
          | none => none
          | some (d32, restD) =>
            some (regIdx, .mem { base := some (gprOfNat baseFull), index := indexOpt, disp := sext32To64 d32 }, 6, restD)
    else if mod2 == 0 && rm3.toNat == 5 then
      match readLe32? rest with
      | none => none
      | some (d32, restD) =>
        some (regIdx, .mem { base := none, index := none, disp := sext32To64 d32, ripRel := true }, 5, restD)
    else if mod2 == 0 then
      some (regIdx, .mem { base := some (gprOfNat rmIdx), index := none, disp := 0#64 }, 1, rest)
    else if mod2 == 1 then
      match rest with
      | [] => none
      | d8 :: restD =>
        some (regIdx, .mem { base := some (gprOfNat rmIdx), index := none, disp := sext8To64 d8 }, 2, restD)
    else
      match readLe32? rest with
      | none => none
      | some (d32, restD) =>
        some (regIdx, .mem { base := some (gprOfNat rmIdx), index := none, disp := sext32To64 d32 }, 5, restD)

def rmToXmm (rm : RmOp) (bBit : Bool) (mrmByte : BitVec 8) : XmmRmOp :=
  match rm with
  | .reg _ => .reg (ymmIdxOfNat (mkRegIdx bBit (BitVec.extractLsb' 0 3 mrmByte)))
  | .mem a => .mem a

def finishLen (totalLen : Nat) (ins : Instr) : DecodeResult :=
  if totalLen > 15 then .fault .gp0LengthExceeds15 else .ok ins totalLen

/-- Decode VEX body (`mapSel ∈ {1 (0F), 2 (0F38), 3 (0F3A)}`, `pp ∈ {0 (NP), 1 (66), 2 (F3), 3 (F2)}`). -/
def decodeVexBody (pfxLen vexHdrLen : Nat) (rBit xBit bBit wBit lBit : Bool)
    (vvvv : Nat) (mapSel pp : Nat) (rest : List (BitVec 8)) : DecodeResult :=
  let baseLen := pfxLen + vexHdrLen
  let simdW : SimdWidth := if lBit then .v256 else .v128
  let opSz  : OpSize    := if wBit then .s64 else .s32
  match rest with
  | [] => .fault .udUnmapped
  | opc :: afterOpc =>
    if mapSel == 1 && opc == 0x77#8 then
      if pp == 0 && !lBit && vvvv == 0 then finishLen (baseLen + 1) .vzeroupper
      else .fault .udVexField
    else
      match afterOpc with
      | [] => .fault .udUnmapped
      | mrmPeek :: _ =>
        match parseModRm rBit xBit bBit afterOpc with
        | none => .fault .udUnmapped
        | some (regIdx, rmOp, mrmLen, postMrm) =>
          let dstY  := ymmIdxOfNat regIdx
          let src1Y := ymmIdxOfNat vvvv
          let rmX   := rmToXmm rmOp bBit mrmPeek
          let lenNoImm := baseLen + 1 + mrmLen
          if mapSel == 1 then
            if opc == 0x6F#8 && (pp == 1 || pp == 2) then
              if vvvv != 0 then .fault .udVexField else finishLen lenNoImm (.vmovdqLoad simdW dstY rmX)
            else if opc == 0x7F#8 && (pp == 1 || pp == 2) then
              if vvvv != 0 then .fault .udVexField
              else match rmOp with
                | .mem a => finishLen lenNoImm (.vmovdqStore simdW a dstY)
                | .reg _ => finishLen lenNoImm (.vmovdqLoad simdW (ymmIdxOfNat (mkRegIdx bBit (BitVec.extractLsb' 0 3 mrmPeek))) (.reg dstY))
            else if opc == 0x6E#8 && pp == 1 then
              if lBit || vvvv != 0 then .fault .udVexField
              else finishLen lenNoImm (.vmovGprToXmm wBit dstY rmOp)
            else if opc == 0xFC#8 && pp == 1 then finishLen lenNoImm (.vpadd simdW .e8  dstY src1Y rmX)
            else if opc == 0xFD#8 && pp == 1 then finishLen lenNoImm (.vpadd simdW .e16 dstY src1Y rmX)
            else if opc == 0xFE#8 && pp == 1 then finishLen lenNoImm (.vpadd simdW .e32 dstY src1Y rmX)
            else if opc == 0xD4#8 && pp == 1 then finishLen lenNoImm (.vpadd simdW .e64 dstY src1Y rmX)
            else if opc == 0xF8#8 && pp == 1 then finishLen lenNoImm (.vpsub simdW .e8  dstY src1Y rmX)
            else if opc == 0xF9#8 && pp == 1 then finishLen lenNoImm (.vpsub simdW .e16 dstY src1Y rmX)
            else if opc == 0xFA#8 && pp == 1 then finishLen lenNoImm (.vpsub simdW .e32 dstY src1Y rmX)
            else if opc == 0xFB#8 && pp == 1 then finishLen lenNoImm (.vpsub simdW .e64 dstY src1Y rmX)
            else if opc == 0xED#8 && pp == 1 then finishLen lenNoImm (.vpaddsw simdW dstY src1Y rmX)
            else if opc == 0xD8#8 && pp == 1 then finishLen lenNoImm (.vpsubusb simdW dstY src1Y rmX)
            else if (opc == 0xDB#8 && pp == 1) || (opc == 0x54#8 && pp == 0) then
              finishLen lenNoImm (.vpand simdW dstY src1Y rmX)
            else if (opc == 0xEB#8 && pp == 1) || (opc == 0x56#8 && pp == 0) then
              finishLen lenNoImm (.vpor simdW dstY src1Y rmX)
            else if (opc == 0xEF#8 && pp == 1) || (opc == 0x57#8 && pp == 0) then
              finishLen lenNoImm (.vpxor simdW dstY src1Y rmX)
            else if opc == 0xDF#8 && pp == 1 then finishLen lenNoImm (.vpandn simdW dstY src1Y rmX)
            else if opc == 0x74#8 && pp == 1 then finishLen lenNoImm (.vpcmpeq simdW .e8  dstY src1Y rmX)
            else if opc == 0x75#8 && pp == 1 then finishLen lenNoImm (.vpcmpeq simdW .e16 dstY src1Y rmX)
            else if opc == 0x64#8 && pp == 1 then finishLen lenNoImm (.vpcmpgt simdW .e8  dstY src1Y rmX)
            else if opc == 0x66#8 && pp == 1 then finishLen lenNoImm (.vpcmpgt simdW .e32 dstY src1Y rmX)
            else if opc == 0xD7#8 && pp == 1 then
              if vvvv != 0 then .fault .udVexField
              else match rmX with
                | .reg srcY => finishLen lenNoImm (.vpmovmskb simdW (gprOfNat regIdx) srcY)
                | .mem _    => .fault .udVexField
            else if opc == 0x70#8 && pp == 1 then
              if vvvv != 0 then .fault .udVexField
              else match postMrm with
                | imm8 :: _ => finishLen (lenNoImm + 1) (.vpshufd simdW dstY rmX imm8)
                | [] => .fault .udUnmapped
            else if opc == 0xF5#8 && pp == 1 then finishLen lenNoImm (.vpmaddwd simdW dstY src1Y rmX)
            else if opc == 0xF6#8 && pp == 1 then finishLen lenNoImm (.vpsadbw simdW dstY src1Y rmX)
            else if opc == 0xF2#8 && pp == 1 then finishLen lenNoImm (.vpslldXmm simdW dstY src1Y rmX)
            else if opc == 0x72#8 && pp == 1 then
              match rmX, postMrm with
              | .reg srcRmY, imm8 :: _ =>
                let subop := (BitVec.extractLsb' 3 3 mrmPeek).toNat
                if subop == 6 then finishLen (lenNoImm + 1) (.vpshiftImmD simdW .sll src1Y srcRmY imm8)
                else if subop == 2 then finishLen (lenNoImm + 1) (.vpshiftImmD simdW .srl src1Y srcRmY imm8)
                else if subop == 4 then finishLen (lenNoImm + 1) (.vpshiftImmD simdW .sra src1Y srcRmY imm8)
                else .fault .udVexField
              | _, _ => .fault .udVexField
            else .fault .udUnmapped
          else if mapSel == 2 then
            if opc == 0x00#8 && pp == 1 then finishLen lenNoImm (.vpshufb simdW dstY src1Y rmX)
            else if opc == 0x04#8 && pp == 1 then finishLen lenNoImm (.vpmaddubsw simdW dstY src1Y rmX)
            else if opc == 0x47#8 && pp == 1 && !wBit then finishLen lenNoImm (.vpshiftVarD simdW .sll dstY src1Y rmX)
            else if opc == 0x45#8 && pp == 1 && !wBit then finishLen lenNoImm (.vpshiftVarD simdW .srl dstY src1Y rmX)
            else if ((opc == 0x36#8 || opc == 0x16#8) && pp == 1) && !wBit then
              if !lBit then .fault .udVexField else finishLen lenNoImm (.vpermd dstY src1Y rmX)
            else if opc == 0xDC#8 && pp == 1 then
              if lBit then .fault .udVexField else finishLen lenNoImm (.vaesenc dstY src1Y rmX)
            else if opc == 0x17#8 && pp == 1 then
              if vvvv != 0 then .fault .udVexField else finishLen lenNoImm (.vptest simdW dstY rmX)
            -- BMI1/BMI2 scalar VEX instructions require L = 0 (`VL128` in XED)
            else if opc == 0xF6#8 && pp == 3 then
              if lBit then .fault .udVexField
              else finishLen lenNoImm (.mulx opSz (gprOfNat regIdx) (gprOfNat vvvv) rmOp)
            else if opc == 0xF2#8 && pp == 0 then
              if lBit then .fault .udVexField
              else finishLen lenNoImm (.andn opSz (gprOfNat regIdx) (gprOfNat vvvv) rmOp)
            else if opc == 0xF7#8 && pp == 3 then
              if lBit then .fault .udVexField
              else finishLen lenNoImm (.shrx opSz (gprOfNat regIdx) rmOp (gprOfNat vvvv))
            else if opc == 0xF7#8 && pp == 1 then
              if lBit then .fault .udVexField
              else finishLen lenNoImm (.shlx opSz (gprOfNat regIdx) rmOp (gprOfNat vvvv))
            else if opc == 0xF7#8 && pp == 2 then
              if lBit then .fault .udVexField
              else finishLen lenNoImm (.sarx opSz (gprOfNat regIdx) rmOp (gprOfNat vvvv))
            else if opc == 0xF5#8 && pp == 0 then
              if lBit then .fault .udVexField
              else finishLen lenNoImm (.bzhi opSz (gprOfNat regIdx) rmOp (gprOfNat vvvv))
            else if opc == 0xF5#8 && pp == 3 then
              if lBit then .fault .udVexField
              else finishLen lenNoImm (.pdep opSz (gprOfNat regIdx) (gprOfNat vvvv) rmOp)
            else if opc == 0xF5#8 && pp == 2 then
              if lBit then .fault .udVexField
              else finishLen lenNoImm (.pext opSz (gprOfNat regIdx) (gprOfNat vvvv) rmOp)
            else .fault .udUnmapped
          else if mapSel == 3 then
            match postMrm with
            | [] => .fault .udUnmapped
            | imm8 :: _ =>
              let lenImm := lenNoImm + 1
              if opc == 0x16#8 && pp == 1 && wBit then
                if lBit || vvvv != 0 then .fault .udVexField
                else match rmOp with
                  | .reg dstG => finishLen lenImm (.vpextrq dstG dstY imm8)
                  | .mem _    => .fault .udVexField
              else if opc == 0x00#8 && pp == 1 && wBit then
                if !lBit || vvvv != 0 then .fault .udVexField
                else finishLen lenImm (.vpermq dstY rmX imm8)
              else if ((opc == 0x46#8 || opc == 0x06#8) && pp == 1) && !wBit then
                if !lBit then .fault .udVexField
                else finishLen lenImm (.vperm2x128 dstY src1Y rmX imm8)
              else if ((opc == 0x39#8 || opc == 0x19#8) && pp == 1) && !wBit then
                if !lBit || vvvv != 0 then .fault .udVexField
                else finishLen lenImm (.vextract128 rmX dstY imm8)
              else if opc == 0x44#8 && pp == 1 then
                if lBit then .fault .udVexField
                else finishLen lenImm (.vpclmulqdq dstY src1Y rmX imm8)
              else .fault .udUnmapped
          else .fault .udVexField

/-- Decode 4-byte EVEX (`0x62 p0 p1 p2`) AVX-512VL 128/256-bit instructions (`VPROLVD`, `VPTERNLOGD`). -/
def decodeEvex (pfxLen : Nat) (rest : List (BitVec 8)) : DecodeResult :=
  match rest with
  | p0 :: p1 :: p2 :: opc :: afterOpc =>
    let mm   := (BitVec.extractLsb' 0 3 p0).toNat
    let rBit := !(p0.getLsbD 7)
    let xBit := !(p0.getLsbD 6)
    let bBit := !(p0.getLsbD 5)
    let rPrim := !(p0.getLsbD 4)
    let p0Bit3 := p0.getLsbD 3
    let wBit := p1.getLsbD 7
    let vvvv := (BitVec.extractLsb' 3 4 (~~~p1)).toNat
    let p1Bit2 := p1.getLsbD 2
    let pp   := (BitVec.extractLsb' 0 2 p1).toNat
    let zBit := p2.getLsbD 7
    let ll   := (BitVec.extractLsb' 5 2 p2).toNat
    let bBc  := p2.getLsbD 4
    let vPrim := !(p2.getLsbD 3)
    let aaa  := (BitVec.extractLsb' 0 3 p2).toNat
    -- Restrict to unmasked (`aaa = 0`, `z = 0`, `!bBc`), XMM0..15 (`!rPrim`, `!vPrim`, `p0[3]=0`, `p1[2]=1`), 128/256b
    if p0Bit3 || !p1Bit2 || rPrim || vPrim || zBit || bBc || aaa != 0 || ll >= 2 then
      .fault .udEvexField
    else
      let simdW : SimdWidth := if ll == 1 then .v256 else .v128
      match afterOpc with
      | [] => .fault .udUnmapped
      | mrmPeek :: _ =>
        match parseModRm rBit xBit bBit afterOpc with
        | none => .fault .udUnmapped
        | some (regIdx, rmOp, mrmLen, postMrm) =>
          let dstY  := ymmIdxOfNat regIdx
          let src1Y := ymmIdxOfNat vvvv
          let rmX   := rmToXmm rmOp bBit mrmPeek
          let lenNoImm := pfxLen + 5 + mrmLen
          if mm == 2 && pp == 1 && !wBit && opc == 0x15#8 then
            finishLen lenNoImm (.vprolvd simdW dstY src1Y rmX)
          else if mm == 3 && pp == 1 && !wBit && opc == 0x25#8 then
            match postMrm with
            | imm8 :: _ => finishLen (lenNoImm + 1) (.vpternlogd simdW dstY src1Y rmX imm8)
            | [] => .fault .udUnmapped
          else .fault .udUnmapped
  | _ => .fault .udUnmapped

/-- Main total x86-64 byte decoder over an arbitrary byte stream (16-byte fetch window). -/
def decodeRef (bytes : List (BitVec 8)) : DecodeResult :=
  let window := bytes.take 16
  let (pfx, rem) := scanPrefixes 16 {} window
  if pfx.count >= 16 then
    .fault .gp0LengthExceeds15
  else
    match rem with
    | [] => .fault .udUnmapped
    | opc :: afterOpc =>
      -- 1. VEX2 (`0xC5`), VEX3 (`0xC4`), and EVEX (`0x62`)
      if opc == 0xC5#8 then
        if pfx.hasLock || pfx.has66 || pfx.rep != .none || pfx.rex.isSome then
          .fault .udVexPrefix
        else
          match afterOpc with
          | b1 :: rest =>
            let rBit := !(b1.getLsbD 7)
            let vvvv := (BitVec.extractLsb' 3 4 (~~~b1)).toNat
            let lBit := b1.getLsbD 2
            let pp   := (BitVec.extractLsb' 0 2 b1).toNat
            decodeVexBody pfx.count 2 rBit false false false lBit vvvv 1 pp rest
          | [] => .fault .udUnmapped
      else if opc == 0xC4#8 then
        if pfx.hasLock || pfx.has66 || pfx.rep != .none || pfx.rex.isSome then
          .fault .udVexPrefix
        else
          match afterOpc with
          | b1 :: b2 :: rest =>
            let rBit   := !(b1.getLsbD 7)
            let xBit   := !(b1.getLsbD 6)
            let bBit   := !(b1.getLsbD 5)
            let mapSel := (BitVec.extractLsb' 0 5 b1).toNat
            let wBit   := b2.getLsbD 7
            let vvvv   := (BitVec.extractLsb' 3 4 (~~~b2)).toNat
            let lBit   := b2.getLsbD 2
            let pp     := (BitVec.extractLsb' 0 2 b2).toNat
            decodeVexBody pfx.count 3 rBit xBit bBit wBit lBit vvvv mapSel pp rest
          | _ => .fault .udUnmapped
      else if opc == 0x62#8 then
        if pfx.hasLock || pfx.has66 || pfx.rep != .none || pfx.rex.isSome then
          .fault .udVexPrefix
        else
          decodeEvex pfx.count afterOpc
      -- 2. Legacy / REX / 0F / 0F38 instructions
      else
        let rBit := rexR pfx.rex
        let xBit := rexX pfx.rex
        let bBit := rexB pfx.rex
        let sz   := opSizeOf pfx.rex
        -- Privileged Ring-3 `#GP(0)` trap (`CLI` = `0xFA`)
        if opc == 0xFA#8 then
          if pfx.count + 1 > 15 then .fault .gp0LengthExceeds15
          else if pfx.hasLock then .fault .udIllegalLock
          else .fault .gp0Privilege
        -- `0x90..0x97`: `NOP` / `PAUSE` / `XCHG rAX, rReg`
        else if (opc &&& 0xF8#8) == 0x90#8 then
          if pfx.hasLock then
            if pfx.count + 1 > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
          else
            let regIdx := mkRegIdx bBit (BitVec.extractLsb' 0 3 opc)
            if regIdx == 0 then
              finishLen (pfx.count + 1) .nop
            else
              let wBits := if rexW pfx.rex then 64 else if pfx.has66 then 16 else 32
              finishLen (pfx.count + 1) (.xchgRegReg wBits .rax (gprOfNat regIdx))
        -- `PUSH` (`0x50..0x57`) / `POP` (`0x58..0x5F`)
        else if (opc &&& 0xF8#8) == 0x50#8 then
          if pfx.hasLock then .fault .udIllegalLock
          else finishLen (pfx.count + 1) (.pushReg (gprOfNat (mkRegIdx bBit (BitVec.extractLsb' 0 3 opc))))
        else if (opc &&& 0xF8#8) == 0x58#8 then
          if pfx.hasLock then .fault .udIllegalLock
          else finishLen (pfx.count + 1) (.popReg (gprOfNat (mkRegIdx bBit (BitVec.extractLsb' 0 3 opc))))
        -- `RET` (`0xC3`)
        else if opc == 0xC3#8 then
          if pfx.hasLock then .fault .udIllegalLock else finishLen (pfx.count + 1) .ret
        -- `CALL rel32` (`0xE8`), `JMP rel32` (`0xE9`), `JMP rel8` (`0xEB`), `Jcc rel8` (`0x70..0x7F`)
        else if opc == 0xE8#8 then
          if pfx.hasLock then .fault .udIllegalLock
          else match readLe32? afterOpc with
            | some (d32, _) => finishLen (pfx.count + 5) (.callRel32 (sext32To64 d32))
            | none => .fault .udUnmapped
        else if opc == 0xE9#8 then
          if pfx.hasLock then .fault .udIllegalLock
          else match readLe32? afterOpc with
            | some (d32, _) => finishLen (pfx.count + 5) (.jmpRel (sext32To64 d32))
            | none => .fault .udUnmapped
        else if opc == 0xEB#8 then
          if pfx.hasLock then .fault .udIllegalLock
          else match afterOpc with
            | d8 :: _ => finishLen (pfx.count + 2) (.jmpRel (sext8To64 d8))
            | [] => .fault .udUnmapped
        else if (opc &&& 0xF0#8) == 0x70#8 then
          if pfx.hasLock then .fault .udIllegalLock
          else match afterOpc with
            | d8 :: _ => finishLen (pfx.count + 2) (.jccRel (condOfNib (opc &&& 0x0F#8).toNat) (sext8To64 d8))
            | [] => .fault .udUnmapped
        -- `MOV reg, imm32 / imm64` (`0xB8..0xBF`)
        else if (opc &&& 0xF8#8) == 0xB8#8 then
          if pfx.hasLock then .fault .udIllegalLock
          else
            let dst := gprOfNat (mkRegIdx bBit (BitVec.extractLsb' 0 3 opc))
            if rexW pfx.rex then
              match readLe64? afterOpc with
              | some (imm64, _) => finishLen (pfx.count + 9) (.movImm .s64 dst imm64)
              | none => .fault .udUnmapped
            else
              match readLe32? afterOpc with
              | some (imm32, _) => finishLen (pfx.count + 5) (.movImm .s32 dst (imm32.zeroExtend 64))
              | none => .fault .udUnmapped
        -- Two-byte `0x0F` escape
        else if opc == 0x0F#8 then
          match afterOpc with
          | [] => .fault .udUnmapped
          | opc2 :: rest2 =>
            if opc2 == 0x0B#8 then
              if pfx.count + 2 > 15 then .fault .gp0LengthExceeds15 else .fault .udExplicit
            else if opc2 == 0x1E#8 then
              if pfx.hasLock then .fault .udIllegalLock
              else match rest2 with
                | 0xFA#8 :: _ =>
                  if pfx.rep == .repz then finishLen (pfx.count + 3) .endbr64
                  else finishLen (pfx.count + 3) .nop
                | _ =>
                  match parseModRm rBit xBit bBit rest2 with
                  | some (_, _, mLen, _) => finishLen (pfx.count + 2 + mLen) .nop
                  | none => .fault .udUnmapped
            else if opc2 == 0x1F#8 then
              if pfx.hasLock then .fault .udIllegalLock
              else match parseModRm rBit xBit bBit rest2 with
                | some (0, _, mLen, _) => finishLen (pfx.count + 2 + mLen) .nop
                | _ => .fault .udUnmapped
            else if (opc2 &&& 0xF8#8) == 0xC8#8 then
              if pfx.hasLock then .fault .udIllegalLock
              else finishLen (pfx.count + 2) (.bswap sz (gprOfNat (mkRegIdx bBit (BitVec.extractLsb' 0 3 opc2))))
            else if (opc2 &&& 0xF0#8) == 0x80#8 then
              if pfx.hasLock then .fault .udIllegalLock
              else match readLe32? rest2 with
                | some (d32, _) => finishLen (pfx.count + 6) (.jccRel (condOfNib (opc2 &&& 0x0F#8).toNat) (sext32To64 d32))
                | none => .fault .udUnmapped
            else if opc2 == 0x38#8 then
              match rest2 with
              | opc3 :: rest3 =>
                if opc3 == 0xF6#8 && !pfx.hasLock then
                  match parseModRm rBit xBit bBit rest3 with
                  | some (regIdx, rmOp, mLen, _) =>
                    if pfx.has66 && pfx.rep == .none then
                      finishLen (pfx.count + 3 + mLen) (.adcx sz (gprOfNat regIdx) rmOp)
                    else if !pfx.has66 && pfx.rep == .repz then
                      finishLen (pfx.count + 3 + mLen) (.adox sz (gprOfNat regIdx) rmOp)
                    else .fault .udUnmapped
                  | none => .fault .udUnmapped
                else .fault .udUnmapped
              | [] => .fault .udUnmapped
            else
              match parseModRm rBit xBit bBit rest2 with
              | none => .fault .udUnmapped
              | some (regIdx, rmOp, mLen, _) =>
                let len2 := pfx.count + 2 + mLen
                let dstG := gprOfNat regIdx
                if opc2 == 0xAF#8 then
                  if pfx.hasLock then .fault .udIllegalLock
                  else finishLen len2 (.imul2 sz dstG rmOp)
                else if opc2 == 0xBC#8 then
                  if pfx.hasLock then .fault .udIllegalLock
                  else if pfx.rep == .repz then finishLen len2 (.tzcnt sz dstG rmOp)
                  else finishLen len2 (.bsf sz dstG rmOp)
                else if opc2 == 0xBD#8 then
                  if pfx.hasLock then .fault .udIllegalLock
                  else if pfx.rep == .repz then finishLen len2 (.lzcnt sz dstG rmOp)
                  else finishLen len2 (.bsr sz dstG rmOp)
                else if opc2 == 0xB8#8 && pfx.rep == .repz then
                  if pfx.hasLock then .fault .udIllegalLock
                  else finishLen len2 (.popcnt sz dstG rmOp)
                else if (opc2 &&& 0xF0#8) == 0x40#8 then
                  if pfx.hasLock then .fault .udIllegalLock
                  else finishLen len2 (.cmovcc sz (condOfNib (opc2 &&& 0x0F#8).toNat) dstG rmOp)
                else if (opc2 &&& 0xF0#8) == 0x90#8 then
                  if pfx.hasLock then .fault .udIllegalLock
                  else finishLen len2 (.setcc (condOfNib (opc2 &&& 0x0F#8).toNat) rmOp)
                else if opc2 == 0xB6#8 then
                  if pfx.hasLock then .fault .udIllegalLock
                  else finishLen len2 (.movzxByte sz dstG rmOp)
                else if opc2 == 0xB7#8 then
                  if pfx.hasLock then .fault .udIllegalLock
                  else finishLen len2 (.movzxWord sz dstG rmOp)
                else if opc2 == 0xC1#8 then
                  match rmOp with
                  | .mem a =>
                    if pfx.hasLock then finishLen len2 (.lockXadd sz a dstG)
                    else .fault .udUnmapped
                  | .reg _ => if pfx.hasLock then .fault .udIllegalLock else .fault .udUnmapped
                else if opc2 == 0xB1#8 then
                  match rmOp with
                  | .mem a =>
                    if pfx.hasLock then finishLen len2 (.lockCmpxchg sz a dstG)
                    else .fault .udUnmapped
                  | .reg _ => if pfx.hasLock then .fault .udIllegalLock else .fault .udUnmapped
                else .fault .udUnmapped
        -- One-byte ModR/M opcodes
        else
          match parseModRm rBit xBit bBit afterOpc with
          | none => .fault .udUnmapped
          | some (regIdx, rmOp, mLen, postMrm) =>
            let len1 := pfx.count + 1 + mLen
            let regG := gprOfNat regIdx
            -- Binary ALU `rm, reg` (`01, 09, 11, 19, 21, 29, 31, 39`)
            if (opc &&& 0xC7#8) == 0x01#8 then
              let idx := (BitVec.extractLsb' 3 3 opc).toNat
              match aluOpOfIdx idx with
              | none => .fault .udUnmapped
              | some aop =>
                if pfx.hasLock then
                  match rmOp with
                  | .mem a =>
                    if aop == .cmp then
                      if len1 > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
                    else finishLen len1 (.lockAluReg sz aop a regG)
                  | .reg _ =>
                    if len1 > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
                else finishLen len1 (.aluRmReg sz aop rmOp regG)
            -- Binary ALU `reg, rm` (`03, 0B, 13, 1B, 23, 2B, 33, 3B`)
            else if (opc &&& 0xC7#8) == 0x03#8 then
              let idx := (BitVec.extractLsb' 3 3 opc).toNat
              match aluOpOfIdx idx with
              | none => .fault .udUnmapped
              | some aop =>
                if pfx.hasLock then
                  if len1 > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
                else finishLen len1 (.aluRegRm sz aop regG rmOp)
            -- `83 /digit ib` sign-extended imm8 ALU
            else if opc == 0x83#8 then
              match afterOpc, postMrm with
              | mrmByte :: _, imm8 :: _ =>
                let subop := (BitVec.extractLsb' 3 3 mrmByte).toNat
                match aluOpOfIdx subop with
                | none => .fault .udUnmapped
                | some aop =>
                  let lenImm := len1 + 1
                  if pfx.hasLock then
                    match rmOp with
                    | .mem a =>
                      if aop == .cmp then
                        if lenImm > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
                      else finishLen lenImm (.lockAluImm sz aop a (sext8To64 imm8))
                    | .reg _ =>
                      if lenImm > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
                  else finishLen lenImm (.aluRmImm sz aop rmOp (sext8To64 imm8))
              | _, _ => .fault .udUnmapped
            -- `TEST rm, reg` (`0x85`)
            else if opc == 0x85#8 then
              if pfx.hasLock then
                if len1 > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
              else finishLen len1 (.aluRmReg sz .test rmOp regG)
            -- `MOV rm, reg` (`0x89`), `MOV reg, rm` (`0x8B`), `MOVSXD` (`0x63`), `LEA` (`0x8D`), `XCHG` (`0x87`)
            else if opc == 0x89#8 then
              if pfx.hasLock then
                if len1 > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
              else finishLen len1 (.movRmReg sz rmOp regG)
            else if opc == 0x8B#8 then
              if pfx.hasLock then
                if len1 > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
              else finishLen len1 (.movRegRm sz regG rmOp)
            else if opc == 0x63#8 && rexW pfx.rex then
              if pfx.hasLock then .fault .udIllegalLock
              else finishLen len1 (.movsxd regG rmOp)
            else if opc == 0x8D#8 then
              if pfx.hasLock then
                if len1 > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
              else match rmOp with
                | .mem a => finishLen len1 (.lea sz regG a)
                | .reg _ => .fault .udUnmapped
            else if opc == 0x87#8 then
              match rmOp with
              | .reg r2 =>
                if pfx.hasLock then
                  if len1 > 15 then .fault .gp0LengthExceeds15 else .fault .udIllegalLock
                else
                  let wBits := if rexW pfx.rex then 64 else if pfx.has66 then 16 else 32
                  finishLen len1 (.xchgRegReg wBits regG r2)
              | .mem _ => .fault .udUnmapped
            -- `IMUL reg, rm, imm8` (`0x6B`)
            else if opc == 0x6B#8 then
              if pfx.hasLock then .fault .udIllegalLock
              else match postMrm with
                | imm8 :: _ => finishLen (len1 + 1) (.imul3 sz regG rmOp (sext8To64 imm8))
                | [] => .fault .udUnmapped
            -- `FF /0` (`INC`), `FF /1` (`DEC`)
            else if opc == 0xFF#8 then
              match afterOpc with
              | mrmByte :: _ =>
                let subop := (BitVec.extractLsb' 3 3 mrmByte).toNat
                if subop == 0 then
                  if pfx.hasLock then
                    match rmOp with
                    | .mem a => finishLen len1 (.lockInc sz a)
                    | .reg _ => .fault .udIllegalLock
                  else finishLen len1 (.unaryRm sz .inc rmOp)
                else if subop == 1 then
                  if pfx.hasLock then .fault .udIllegalLock
                  else finishLen len1 (.unaryRm sz .dec rmOp)
                else .fault .udUnmapped
              | [] => .fault .udUnmapped
            -- `F7 /2` (`NOT`), `F7 /3` (`NEG`), `F7 /4` (`MUL`)
            else if opc == 0xF7#8 then
              if pfx.hasLock then .fault .udIllegalLock
              else match afterOpc with
                | mrmByte :: _ =>
                  let subop := (BitVec.extractLsb' 3 3 mrmByte).toNat
                  if subop == 2 then finishLen len1 (.unaryRm sz .not rmOp)
                  else if subop == 3 then finishLen len1 (.unaryRm sz .neg rmOp)
                  else if subop == 4 then finishLen len1 (.mulUnsigned sz rmOp)
                  else .fault .udUnmapped
                | [] => .fault .udUnmapped
            -- `C1 ib`, `D1 1`, `D3 CL` shifts & rotates
            else if opc == 0xC1#8 || opc == 0xD1#8 || opc == 0xD3#8 then
              if pfx.hasLock then .fault .udIllegalLock
              else match afterOpc with
                | mrmByte :: _ =>
                  let subop := (BitVec.extractLsb' 3 3 mrmByte).toNat
                  let sop? : Option ShiftOp :=
                    if subop == 0 then some .rol
                    else if subop == 1 then some .ror
                    else if subop == 4 then some .shl
                    else if subop == 5 then some .shr
                    else if subop == 7 then some .sar
                    else none
                  match sop? with
                  | none => .fault .udUnmapped
                  | some sop =>
                    if opc == 0xC1#8 then
                      match postMrm with
                      | imm8 :: _ => finishLen (len1 + 1) (.shiftRm sz sop rmOp (.imm imm8))
                      | [] => .fault .udUnmapped
                    else if opc == 0xD1#8 then
                      finishLen len1 (.shiftRm sz sop rmOp (.imm 1#8))
                    else
                      finishLen len1 (.shiftRm sz sop rmOp .cl)
                | [] => .fault .udUnmapped
            else .fault .udUnmapped

/-- Every successful decode consumes at most 15 architectural bytes (`#GP(0)` cap). -/
theorem finishLen_le_15 {n : Nat} {ins : Instr} {outIns : Instr} {outLen : Nat}
    (h : finishLen n ins = .ok outIns outLen) : outLen ≤ 15 := by
  unfold finishLen at h
  split at h
  · cases h
  · injection h with _ hlen
    omega

/-- `decodeRef` depends strictly on `bytes.take 16`, so any bytes beyond the
    16-byte architectural fetch window never alter decoding. -/
theorem decodeRef_window16_invariant (bytes : List (BitVec 8)) :
    decodeRef (bytes.take 16) = decodeRef bytes := by
  unfold decodeRef
  rw [List.take_take, Nat.min_self]

end VendorX86Ref
