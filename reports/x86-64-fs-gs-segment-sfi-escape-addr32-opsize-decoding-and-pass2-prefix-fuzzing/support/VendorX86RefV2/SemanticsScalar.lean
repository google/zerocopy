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
import Init.Data.Nat.Basic
import VendorX86RefV2.Types

/-!
# `VendorX86RefV2.SemanticsScalar`

Repaired scalar GP ALU (`.s16`/`.s32`/`.s64`), shifts/rotates, multiply/ADX,
bit-scan (`BSF`/`BSR` with `UNDEFINED_VALUES[destx]` on zero), BMI1/BMI2,
`CMOVcc`/`SETcc`, non-flat `FS`/`GS` + `0x67` `addr32` linear-address
computation (`evalEffectiveAddr` vs `evalLinearAddr`), `0x66` 16-bit stack
`PUSH`/`POP`/`LEAVE`, and `CMPXCHG`/`LOCK` atomic RMW semantics.
-/

namespace VendorX86RefV2

def parity8 (lo : BitVec 8) : Bool :=
  !(lo.getLsbD 0 ^^ lo.getLsbD 1 ^^ lo.getLsbD 2 ^^ lo.getLsbD 3 ^^
    lo.getLsbD 4 ^^ lo.getLsbD 5 ^^ lo.getLsbD 6 ^^ lo.getLsbD 7)

def evalCond (cc : Cond) (f : RFlags) : Bool :=
  match cc with
  | .o  => f.of
  | .no => !f.of
  | .b  => f.cf
  | .ae => !f.cf
  | .e  => f.zf
  | .ne => !f.zf
  | .be => f.cf || f.zf
  | .a  => !f.cf && !f.zf
  | .s  => f.sf
  | .ns => !f.sf
  | .p  => f.pf
  | .np => !f.pf
  | .l  => f.sf != f.of
  | .ge => f.sf == f.of
  | .le => f.zf || (f.sf != f.of)
  | .g  => !f.zf && (f.sf == f.of)

/-- Resolve segment base (`0` for flat `CS`/`DS`/`ES`/`SS`, `fsBase` for `FS`, `gsBase` for `GS`). -/
def segBaseOf (s : MachineState) : Option SegReg → BitVec 64
  | none     => 0#64
  | some .fs => s.fsBase
  | some .gs => s.gsBase

/-- Compute effective address offset (truncating to 32 bits when `a.addr32 = true`,
    used directly by `LEA` which ignores `FS`/`GS` segment base). -/
def evalEffectiveAddr (s : MachineState) (nextRip : BitVec 64) (a : MemAddr) : BitVec 64 :=
  let baseVal := if a.ripRel then nextRip else match a.base with | some r => s.gpr r | none => 0#64
  let idxVal  := match a.index with | some (r, sc) => (s.gpr r) <<< sc | none => 0#64
  let raw     := baseVal + idxVal + a.disp
  if a.addr32 then (BitVec.extractLsb' 0 32 raw).zeroExtend 64 else raw

/-- Compute 64-bit linear memory address `segBase + effectiveAddr`. -/
def evalLinearAddr (s : MachineState) (nextRip : BitVec 64) (a : MemAddr) : BitVec 64 :=
  segBaseOf s a.seg + evalEffectiveAddr s nextRip a

def readGprZext (sz : OpSize) (regs : Gpr → BitVec 64) (r : Gpr) : BitVec 64 :=
  match sz with
  | .s64 => regs r
  | .s32 => (BitVec.extractLsb' 0 32 (regs r)).zeroExtend 64
  | .s16 => (BitVec.extractLsb' 0 16 (regs r)).zeroExtend 64

def readMemZext (sz : OpSize) (m : ByteMem) (addr : BitVec 64) : BitVec 64 :=
  match sz with
  | .s64 => readMem64 m addr
  | .s32 => (readMem32 m addr).zeroExtend 64
  | .s16 => (readMem16 m addr).zeroExtend 64

def readRm (sz : OpSize) (s : MachineState) (nextRip : BitVec 64) (rm : RmOp) : BitVec 64 :=
  match rm with
  | .reg r => readGprZext sz s.gpr r
  | .mem a => readMemZext sz s.mem (evalLinearAddr s nextRip a)

def writeGprSz (sz : OpSize) (regs : Gpr → BitVec 64) (r : Gpr) (v : BitVec 64) : Gpr → BitVec 64 :=
  match sz with
  | .s64 => gprUpd regs r v
  | .s32 => gprUpd regs r ((BitVec.extractLsb' 0 32 v).zeroExtend 64)
  | .s16 => gprUpd regs r (mergeLow16 (regs r) (BitVec.extractLsb' 0 16 v))

def writeMemSz (sz : OpSize) (m : ByteMem) (addr : BitVec 64) (v : BitVec 64) : ByteMem :=
  match sz with
  | .s64 => writeMem64 m addr v
  | .s32 => writeMem32 m addr (BitVec.extractLsb' 0 32 v)
  | .s16 => writeMem16 m addr (BitVec.extractLsb' 0 16 v)

def writeRm (sz : OpSize) (s : MachineState) (nextRip : BitVec 64) (rm : RmOp) (v : BitVec 64) : MachineState :=
  match rm with
  | .reg r => { s with gpr := writeGprSz sz s.gpr r v }
  | .mem a =>
    let addr := evalLinearAddr s nextRip a
    { s with mem := writeMemSz sz s.mem addr v }

def evalAlu64 (op : AluOp) (a b : BitVec 64) (oldF : RFlags) (nd : RFlags) : BitVec 64 × RFlags :=
  let cin : Nat := if oldF.cf then 1 else 0
  let res : BitVec 64 :=
    match op with
    | .add => a + b
    | .adc => BitVec.ofNat 64 (a.toNat + b.toNat + cin)
    | .sub | .cmp => a - b
    | .sbb => BitVec.ofNat 64 ((a.toNat + 2^64 - (b.toNat + cin)) % 2^64)
    | .and | .test => a &&& b
    | .or  => a ||| b
    | .xor => a ^^^ b
  let pf := parity8 (byteOf64 res 0)
  let zf := res == 0#64
  let sf := res.msb
  match op with
  | .add =>
    let cf := decide (a.toNat + b.toNat ≥ 2^64)
    let af := decide ((a &&& 0xF#64).toNat + (b &&& 0xF#64).toNat ≥ 16)
    let of := (a.msb == b.msb) && (res.msb != a.msb)
    (res, { cf, pf, af, zf, sf, of })
  | .adc =>
    let cf := decide (a.toNat + b.toNat + cin ≥ 2^64)
    let af := decide ((a &&& 0xF#64).toNat + (b &&& 0xF#64).toNat + cin ≥ 16)
    let of := (a.msb == b.msb) && (res.msb != a.msb)
    (res, { cf, pf, af, zf, sf, of })
  | .sub | .cmp =>
    let cf := decide (a.toNat < b.toNat)
    let af := decide ((a &&& 0xF#64).toNat < (b &&& 0xF#64).toNat)
    let of := (a.msb != b.msb) && (res.msb != a.msb)
    (res, { cf, pf, af, zf, sf, of })
  | .sbb =>
    let cf := decide (a.toNat < b.toNat + cin)
    let af := decide ((a &&& 0xF#64).toNat < (b &&& 0xF#64).toNat + cin)
    let of := (a.msb != b.msb) && (res.msb != a.msb)
    (res, { cf, pf, af, zf, sf, of })
  | .and | .or | .xor | .test =>
    (res, { cf := false, pf, af := nd.af, zf, sf, of := false })

def evalAlu32 (op : AluOp) (a64 b64 : BitVec 64) (oldF : RFlags) (nd : RFlags) : BitVec 64 × RFlags :=
  let a : BitVec 32 := BitVec.extractLsb' 0 32 a64
  let b : BitVec 32 := BitVec.extractLsb' 0 32 b64
  let cin : Nat := if oldF.cf then 1 else 0
  let res : BitVec 32 :=
    match op with
    | .add => a + b
    | .adc => BitVec.ofNat 32 (a.toNat + b.toNat + cin)
    | .sub | .cmp => a - b
    | .sbb => BitVec.ofNat 32 ((a.toNat + 2^32 - (b.toNat + cin)) % 2^32)
    | .and | .test => a &&& b
    | .or  => a ||| b
    | .xor => a ^^^ b
  let pf := parity8 (BitVec.extractLsb' 0 8 res)
  let zf := res == 0#32
  let sf := res.msb
  let res64 := res.zeroExtend 64
  match op with
  | .add =>
    let cf := decide (a.toNat + b.toNat ≥ 2^32)
    let af := decide ((a &&& 0xF#32).toNat + (b &&& 0xF#32).toNat ≥ 16)
    let of := (a.msb == b.msb) && (res.msb != a.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .adc =>
    let cf := decide (a.toNat + b.toNat + cin ≥ 2^32)
    let af := decide ((a &&& 0xF#32).toNat + (b &&& 0xF#32).toNat + cin ≥ 16)
    let of := (a.msb == b.msb) && (res.msb != a.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .sub | .cmp =>
    let cf := decide (a.toNat < b.toNat)
    let af := decide ((a &&& 0xF#32).toNat < (b &&& 0xF#32).toNat)
    let of := (a.msb != b.msb) && (res.msb != a.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .sbb =>
    let cf := decide (a.toNat < b.toNat + cin)
    let af := decide ((a &&& 0xF#32).toNat < (b &&& 0xF#32).toNat + cin)
    let of := (a.msb != b.msb) && (res.msb != a.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .and | .or | .xor | .test =>
    (res64, { cf := false, pf, af := nd.af, zf, sf, of := false })

def evalAlu16 (op : AluOp) (a64 b64 : BitVec 64) (oldF : RFlags) (nd : RFlags) : BitVec 64 × RFlags :=
  let a : BitVec 16 := BitVec.extractLsb' 0 16 a64
  let b : BitVec 16 := BitVec.extractLsb' 0 16 b64
  let cin : Nat := if oldF.cf then 1 else 0
  let res : BitVec 16 :=
    match op with
    | .add => a + b
    | .adc => BitVec.ofNat 16 (a.toNat + b.toNat + cin)
    | .sub | .cmp => a - b
    | .sbb => BitVec.ofNat 16 ((a.toNat + 2^16 - (b.toNat + cin)) % 2^16)
    | .and | .test => a &&& b
    | .or  => a ||| b
    | .xor => a ^^^ b
  let pf := parity8 (BitVec.extractLsb' 0 8 res)
  let zf := res == 0#16
  let sf := res.msb
  let res64 := res.zeroExtend 64
  match op with
  | .add =>
    let cf := decide (a.toNat + b.toNat ≥ 2^16)
    let af := decide ((a &&& 0xF#16).toNat + (b &&& 0xF#16).toNat ≥ 16)
    let of := (a.msb == b.msb) && (res.msb != a.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .adc =>
    let cf := decide (a.toNat + b.toNat + cin ≥ 2^16)
    let af := decide ((a &&& 0xF#16).toNat + (b &&& 0xF#16).toNat + cin ≥ 16)
    let of := (a.msb == b.msb) && (res.msb != a.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .sub | .cmp =>
    let cf := decide (a.toNat < b.toNat)
    let af := decide ((a &&& 0xF#16).toNat < (b &&& 0xF#16).toNat)
    let of := (a.msb != b.msb) && (res.msb != a.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .sbb =>
    let cf := decide (a.toNat < b.toNat + cin)
    let af := decide ((a &&& 0xF#16).toNat < (b &&& 0xF#16).toNat + cin)
    let of := (a.msb != b.msb) && (res.msb != a.msb)
    (res64, { cf, pf, af, zf, sf, of })
  | .and | .or | .xor | .test =>
    (res64, { cf := false, pf, af := nd.af, zf, sf, of := false })

def evalAlu (sz : OpSize) (op : AluOp) (a b : BitVec 64) (oldF nd : RFlags) : BitVec 64 × RFlags :=
  match sz with
  | .s64 => evalAlu64 op a b oldF nd
  | .s32 => evalAlu32 op a b oldF nd
  | .s16 => evalAlu16 op a b oldF nd

def aluWritesDst : AluOp → Bool
  | .cmp | .test => false
  | _ => true

def evalUnary64 (op : UnaryOp) (a : BitVec 64) (oldF : RFlags) : BitVec 64 × RFlags :=
  match op with
  | .inc =>
    let (res, f) := evalAlu64 .add a 1#64 oldF oldF
    (res, { f with cf := oldF.cf })
  | .dec =>
    let (res, f) := evalAlu64 .sub a 1#64 oldF oldF
    (res, { f with cf := oldF.cf })
  | .neg =>
    let (res, f) := evalAlu64 .sub 0#64 a oldF oldF
    (res, { f with cf := a != 0#64 })
  | .not => (~~~a, oldF)

def evalShift64 (op : ShiftOp) (a : BitVec 64) (rawCnt : Nat) (oldF nd : RFlags) : BitVec 64 × RFlags :=
  let c := rawCnt % 64
  if c == 0 then (a, oldF)
  else
    match op with
    | .shl =>
      let res := a <<< c
      let cf := a.getLsbD (64 - c)
      let of := if c == 1 then res.msb != cf else nd.of
      (res, { cf, pf := parity8 (byteOf64 res 0), af := nd.af, zf := res == 0#64, sf := res.msb, of })
    | .shr =>
      let res := a >>> c
      let cf := a.getLsbD (c - 1)
      let of := if c == 1 then a.msb else nd.of
      (res, { cf, pf := parity8 (byteOf64 res 0), af := nd.af, zf := res == 0#64, sf := res.msb, of })
    | .sar =>
      let res := BitVec.sshiftRight a c
      let cf := a.getLsbD (c - 1)
      let of := if c == 1 then false else nd.of
      (res, { cf, pf := parity8 (byteOf64 res 0), af := nd.af, zf := res == 0#64, sf := res.msb, of })
    | .rol =>
      let res := BitVec.rotateLeft a c
      let cf := res.getLsbD 0
      let of := if c == 1 then res.msb != cf else nd.of
      (res, { oldF with cf, of })
    | .ror =>
      let res := BitVec.rotateRight a c
      let cf := res.msb
      let of := if c == 1 then res.msb != res.getLsbD 62 else nd.of
      (res, { oldF with cf, of })

def sext64To128 (v : BitVec 64) : BitVec 128 :=
  (if v.msb then 0xFFFFFFFFFFFFFFFF#64 else 0#64) ++ v

def evalImul64 (a b : BitVec 64) (nd : RFlags) : BitVec 64 × RFlags :=
  let res := a * b
  let p128 := sext64To128 a * sext64To128 b
  let ovf := p128 != sext64To128 res
  (res, { cf := ovf, pf := nd.pf, af := nd.af, zf := nd.zf, sf := nd.sf, of := ovf })

def ctzLoop (fuel : Nat) (idx : Nat) (x : BitVec 64) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun acc => acc)
    (fun _ ih i => if x.getLsbD i then i else ih (i + 1))
    fuel idx

def clzLoop (fuel : Nat) (x : BitVec 64) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    64
    (fun k ih => if x.getLsbD k then 63 - k else ih)
    fuel

def popcntLoop (fuel : Nat) (acc : Nat) (x : BitVec 64) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun a => a)
    (fun k ih a => ih (a + (if x.getLsbD k then 1 else 0)))
    fuel acc

def pdepLoop (fuel bitIdx srcIdx : Nat) (src mask acc : BitVec 64) : BitVec 64 :=
  Nat.rec (motive := fun _ => Nat → Nat → BitVec 64 → BitVec 64)
    (fun _ _ a => a)
    (fun _ ih bIdx sIdx a =>
      if mask.getLsbD bIdx then
        let a' := if src.getLsbD sIdx then a ||| (1#64 <<< bIdx) else a
        ih (bIdx + 1) (sIdx + 1) a'
      else
        ih (bIdx + 1) sIdx a)
    fuel bitIdx srcIdx acc

def pextLoop (fuel bitIdx outIdx : Nat) (src mask acc : BitVec 64) : BitVec 64 :=
  Nat.rec (motive := fun _ => Nat → Nat → BitVec 64 → BitVec 64)
    (fun _ _ a => a)
    (fun _ ih bIdx oIdx a =>
      if mask.getLsbD bIdx then
        let a' := if src.getLsbD bIdx then a ||| (1#64 <<< oIdx) else a
        ih (bIdx + 1) (oIdx + 1) a'
      else
        ih (bIdx + 1) oIdx a)
    fuel bitIdx outIdx acc

def bswap64 (v : BitVec 64) : BitVec 64 :=
  byteOf64 v 0 ++ (byteOf64 v 1 ++ (byteOf64 v 2 ++ (byteOf64 v 3 ++
  (byteOf64 v 4 ++ (byteOf64 v 5 ++ (byteOf64 v 6 ++ byteOf64 v 7))))))

def bswap32Zext64 (v : BitVec 64) : BitVec 64 :=
  let w32 : BitVec 32 := byteOf64 v 0 ++ (byteOf64 v 1 ++ (byteOf64 v 2 ++ byteOf64 v 3))
  w32.zeroExtend 64

/-- Execute scalar/atomic/control-flow instruction under demonic `UndefOracle`. -/
def execScalar (ins : Instr) (nextRip : BitVec 64) (oracle : UndefOracle) (s : MachineState) :
    Option MachineState :=
  let sRip := { s with rip := nextRip }
  match ins with
  | .nop | .endbr64 => some sRip
  | .ud2 => some { s with fault := some .udExplicit }
  | .cli => some { s with fault := some .gp0Privilege }
  | .aluRmReg sz op dst src =>
    let a := readRm sz s nextRip dst
    let b := readGprZext sz s.gpr src
    let (res, f') := evalAlu sz op a b s.flags oracle.flags
    let s1 := if aluWritesDst op then writeRm sz sRip nextRip dst res else sRip
    some { s1 with flags := f' }
  | .aluRegRm sz op dst src =>
    let a := readGprZext sz s.gpr dst
    let b := readRm sz s nextRip src
    let (res, f') := evalAlu sz op a b s.flags oracle.flags
    let regs' := if aluWritesDst op then writeGprSz sz s.gpr dst res else s.gpr
    some { sRip with gpr := regs', flags := f' }
  | .aluRmImm sz op dst imm =>
    let a := readRm sz s nextRip dst
    let (res, f') := evalAlu sz op a imm s.flags oracle.flags
    let s1 := if aluWritesDst op then writeRm sz sRip nextRip dst res else sRip
    some { s1 with flags := f' }
  | .unaryRm sz op dst =>
    let a := readRm sz s nextRip dst
    let (res, f') := evalUnary64 op a s.flags
    let s1 := writeRm sz sRip nextRip dst res
    some { s1 with flags := f' }
  | .bswap sz dst =>
    let v' := match sz with | .s64 => bswap64 (s.gpr dst) | _ => bswap32Zext64 (s.gpr dst)
    some { sRip with gpr := gprUpd s.gpr dst v' }
  | .shiftRm sz op dst cnt =>
    let a := readRm sz s nextRip dst
    let rawCnt := match cnt with | .imm i => i.toNat | .cl => (byteOf64 (s.gpr .rcx) 0).toNat
    let (res, f') := evalShift64 op a rawCnt s.flags oracle.flags
    let s1 := writeRm sz sRip nextRip dst res
    some { s1 with flags := f' }
  | .imul2 _ dst src =>
    let b := readRm .s64 s nextRip src
    let (res, f') := evalImul64 (s.gpr dst) b oracle.flags
    some { sRip with gpr := gprUpd s.gpr dst res, flags := f' }
  | .imul3 _ dst src imm =>
    let a := readRm .s64 s nextRip src
    let (res, f') := evalImul64 a imm oracle.flags
    some { sRip with gpr := gprUpd s.gpr dst res, flags := f' }
  | .mulUnsigned _ src =>
    let a128 : BitVec 128 := (s.gpr .rax).zeroExtend 128
    let b128 : BitVec 128 := (readRm .s64 s nextRip src).zeroExtend 128
    let prod := a128 * b128
    let lo := BitVec.extractLsb' 0 64 prod
    let hi := BitVec.extractLsb' 64 64 prod
    let ovf := hi != 0#64
    let regs1 := gprUpd (gprUpd s.gpr .rax lo) .rdx hi
    some { sRip with gpr := regs1, flags := { oracle.flags with cf := ovf, of := ovf } }
  | .mulx _ dstHi dstLo src =>
    let a128 : BitVec 128 := (s.gpr .rdx).zeroExtend 128
    let b128 : BitVec 128 := (readRm .s64 s nextRip src).zeroExtend 128
    let prod := a128 * b128
    let lo := BitVec.extractLsb' 0 64 prod
    let hi := BitVec.extractLsb' 64 64 prod
    let regs1 := gprUpd (gprUpd s.gpr dstLo lo) dstHi hi
    some { sRip with gpr := regs1 }
  | .adcx _ dst src =>
    let a := s.gpr dst
    let b := readRm .s64 s nextRip src
    let cin := if s.flags.cf then 1 else 0
    let sum := a.toNat + b.toNat + cin
    let res := BitVec.ofNat 64 sum
    some { sRip with gpr := gprUpd s.gpr dst res, flags := { s.flags with cf := decide (sum ≥ 2^64) } }
  | .adox _ dst src =>
    let a := s.gpr dst
    let b := readRm .s64 s nextRip src
    let oin := if s.flags.of then 1 else 0
    let sum := a.toNat + b.toNat + oin
    let res := BitVec.ofNat 64 sum
    some { sRip with gpr := gprUpd s.gpr dst res, flags := { s.flags with of := decide (sum ≥ 2^64) } }
  | .bsf sz dst src =>
    let x := readRm sz s nextRip src
    if x == 0#64 then
      some { sRip with gpr := gprUpd s.gpr dst oracle.gpr,
                       flags := { oracle.flags with zf := true } }
    else
      let res := BitVec.ofNat 64 (ctzLoop 64 0 x)
      some { sRip with gpr := writeGprSz sz s.gpr dst res,
                       flags := { oracle.flags with zf := false } }
  | .bsr sz dst src =>
    let x := readRm sz s nextRip src
    if x == 0#64 then
      some { sRip with gpr := gprUpd s.gpr dst oracle.gpr,
                       flags := { oracle.flags with zf := true } }
    else
      let res := BitVec.ofNat 64 (63 - clzLoop 64 x)
      some { sRip with gpr := writeGprSz sz s.gpr dst res,
                       flags := { oracle.flags with zf := false } }
  | .tzcnt sz dst src =>
    let x := readRm sz s nextRip src
    let w := match sz with | .s64 => 64 | .s32 => 32 | .s16 => 16
    let cnt := if x == 0#64 then w else ctzLoop w 0 x
    let res := BitVec.ofNat 64 cnt
    some { sRip with gpr := writeGprSz sz s.gpr dst res,
                     flags := { oracle.flags with cf := x == 0#64, zf := cnt == 0 } }
  | .lzcnt _ dst src =>
    let x := readRm .s64 s nextRip src
    let cnt := clzLoop 64 x
    let res := BitVec.ofNat 64 cnt
    some { sRip with gpr := gprUpd s.gpr dst res,
                     flags := { oracle.flags with cf := x == 0#64, zf := cnt == 0 } }
  | .popcnt _ dst src =>
    let x := readRm .s64 s nextRip src
    let cnt := popcntLoop 64 0 x
    some { sRip with gpr := gprUpd s.gpr dst (BitVec.ofNat 64 cnt),
                     flags := { cf := false, pf := false, af := false, zf := x == 0#64, sf := false, of := false } }
  | .andn _ dst src1 src2 =>
    let res := (~~~(s.gpr src1)) &&& (readRm .s64 s nextRip src2)
    some { sRip with gpr := gprUpd s.gpr dst res,
                     flags := { oracle.flags with cf := false, of := false, zf := res == 0#64, sf := res.msb } }
  | .shrx _ dst src cnt =>
    let x := readRm .s64 s nextRip src
    let c := (s.gpr cnt).toNat % 64
    some { sRip with gpr := gprUpd s.gpr dst (x >>> c) }
  | .shlx _ dst src cnt =>
    let x := readRm .s64 s nextRip src
    let c := (s.gpr cnt).toNat % 64
    some { sRip with gpr := gprUpd s.gpr dst (x <<< c) }
  | .sarx _ dst src cnt =>
    let x := readRm .s64 s nextRip src
    let c := (s.gpr cnt).toNat % 64
    some { sRip with gpr := gprUpd s.gpr dst (BitVec.sshiftRight x c) }
  | .bzhi _ dst src ctl =>
    let x := readRm .s64 s nextRip src
    let idx := (byteOf64 (s.gpr ctl) 0).toNat
    let res := if idx >= 64 then x else x &&& ((1#64 <<< idx) - 1#64)
    some { sRip with gpr := gprUpd s.gpr dst res,
                     flags := { oracle.flags with cf := decide (idx ≥ 64), of := false, zf := res == 0#64, sf := res.msb } }
  | .pdep _ dst src1 src2 =>
    let src := s.gpr src1
    let mask := readRm .s64 s nextRip src2
    let res := pdepLoop 64 0 0 src mask 0#64
    some { sRip with gpr := gprUpd s.gpr dst res }
  | .pext _ dst src1 src2 =>
    let src := s.gpr src1
    let mask := readRm .s64 s nextRip src2
    let res := pextLoop 64 0 0 src mask 0#64
    some { sRip with gpr := gprUpd s.gpr dst res }
  | .cmovcc sz cc dst src =>
    let srcVal := readRm sz s nextRip src
    if evalCond cc s.flags then
      some { sRip with gpr := writeGprSz sz s.gpr dst srcVal }
    else
      let cur := s.gpr dst
      let kept := match sz with
        | .s64 | .s16 => cur
        | .s32 => (BitVec.extractLsb' 0 32 cur).zeroExtend 64
      some { sRip with gpr := gprUpd s.gpr dst kept }
  | .setcc cc dst =>
    let byteVal : BitVec 8 := if evalCond cc s.flags then 1#8 else 0#8
    match dst with
    | .reg r =>
      let old := s.gpr r
      let v' := (BitVec.extractLsb' 8 56 old) ++ byteVal
      some { sRip with gpr := gprUpd s.gpr r v' }
    | .mem a =>
      some { sRip with mem := memUpd8 s.mem (evalLinearAddr s nextRip a) byteVal }
  | .movRmReg sz dst src =>
    some (writeRm sz sRip nextRip dst (s.gpr src))
  | .movRegRm sz dst src =>
    let v := readRm sz s nextRip src
    some { sRip with gpr := writeGprSz sz s.gpr dst v }
  | .movImm sz dst imm =>
    some { sRip with gpr := writeGprSz sz s.gpr dst imm }
  | .movzxByte _ dst src =>
    let b8 : BitVec 8 := match src with
      | .reg r => byteOf64 (s.gpr r) 0
      | .mem a => readMem8 s.mem (evalLinearAddr s nextRip a)
    some { sRip with gpr := gprUpd s.gpr dst (b8.zeroExtend 64) }
  | .movzxWord _ dst src =>
    let w16 : BitVec 16 := match src with
      | .reg r => BitVec.extractLsb' 0 16 (s.gpr r)
      | .mem a => readMem16 s.mem (evalLinearAddr s nextRip a)
    some { sRip with gpr := gprUpd s.gpr dst (w16.zeroExtend 64) }
  | .movsxd dst src =>
    let w32 : BitVec 32 := BitVec.extractLsb' 0 32 (readRm .s32 s nextRip src)
    some { sRip with gpr := gprUpd s.gpr dst (sext32To64 w32) }
  | .lea sz dst addr =>
    let ea := evalEffectiveAddr s nextRip addr
    some { sRip with gpr := writeGprSz sz s.gpr dst ea }
  | .xchgRegReg wBits r1 r2 =>
    let v1 := s.gpr r1
    let v2 := s.gpr r2
    if wBits == 64 then
      some { sRip with gpr := gprUpd (gprUpd s.gpr r1 v2) r2 v1 }
    else if wBits == 32 then
      let z1 := (BitVec.extractLsb' 0 32 v1).zeroExtend 64
      let z2 := (BitVec.extractLsb' 0 32 v2).zeroExtend 64
      some { sRip with gpr := gprUpd (gprUpd s.gpr r1 z2) r2 z1 }
    else
      let m1 := mergeLow16 v1 (BitVec.extractLsb' 0 16 v2)
      let m2 := mergeLow16 v2 (BitVec.extractLsb' 0 16 v1)
      some { sRip with gpr := gprUpd (gprUpd s.gpr r1 m1) r2 m2 }
  | .pushReg sz src =>
    match sz with
    | .s16 =>
      let newRsp := s.gpr .rsp - 2#64
      let v16 := BitVec.extractLsb' 0 16 (s.gpr src)
      some { sRip with gpr := gprUpd s.gpr .rsp newRsp, mem := writeMem16 s.mem newRsp v16 }
    | _ =>
      let newRsp := s.gpr .rsp - 8#64
      let v := s.gpr src
      some { sRip with gpr := gprUpd s.gpr .rsp newRsp, mem := writeMem64 s.mem newRsp v }
  | .popReg sz dst =>
    match sz with
    | .s16 =>
      let oldRsp := s.gpr .rsp
      let v := (readMem16 s.mem oldRsp).zeroExtend 64
      let regs1 := gprUpd s.gpr .rsp (oldRsp + 2#64)
      some { sRip with gpr := writeGprSz .s16 regs1 dst v }
    | _ =>
      let oldRsp := s.gpr .rsp
      let v := readMem64 s.mem oldRsp
      let regs1 := gprUpd s.gpr .rsp (oldRsp + 8#64)
      some { sRip with gpr := gprUpd regs1 dst v }
  | .leave sz =>
    let fp := s.gpr .rbp
    match sz with
    | .s16 =>
      let v := (readMem16 s.mem fp).zeroExtend 64
      let regs1 := gprUpd s.gpr .rsp (fp + 2#64)
      some { sRip with gpr := writeGprSz .s16 regs1 .rbp v }
    | _ =>
      let v := readMem64 s.mem fp
      let regs1 := gprUpd s.gpr .rsp (fp + 8#64)
      some { sRip with gpr := gprUpd regs1 .rbp v }
  | .callRel32 rel =>
    let newRsp := s.gpr .rsp - 8#64
    some { s with rip := nextRip + rel, gpr := gprUpd s.gpr .rsp newRsp,
                  mem := writeMem64 s.mem newRsp nextRip }
  | .ret =>
    let oldRsp := s.gpr .rsp
    let retAddr := readMem64 s.mem oldRsp
    some { s with rip := retAddr, gpr := gprUpd s.gpr .rsp (oldRsp + 8#64), halted := true }
  | .jmpRel rel =>
    some { s with rip := nextRip + rel }
  | .jccRel cc rel =>
    some { s with rip := if evalCond cc s.flags then nextRip + rel else nextRip }
  | .cmpxchg sz dst src =>
    let acc := readGprZext sz s.gpr .rax
    let cur := readRm sz s nextRip dst
    let (_, f') := evalAlu sz .cmp acc cur s.flags oracle.flags
    if acc == cur then
      some { writeRm sz sRip nextRip dst (s.gpr src) with flags := f' }
    else
      some { sRip with gpr := writeGprSz sz s.gpr .rax cur, flags := f' }
  | .lockAluReg sz op addr src =>
    let ea := evalLinearAddr s nextRip addr
    let oldM := readMemZext sz s.mem ea
    let b := readGprZext sz s.gpr src
    let (res, f') := evalAlu sz op oldM b s.flags oracle.flags
    some { sRip with mem := writeMemSz sz s.mem ea res, flags := f' }
  | .lockAluImm sz op addr imm =>
    let ea := evalLinearAddr s nextRip addr
    let oldM := readMemZext sz s.mem ea
    let (res, f') := evalAlu sz op oldM imm s.flags oracle.flags
    some { sRip with mem := writeMemSz sz s.mem ea res, flags := f' }
  | .lockInc _ addr =>
    let ea := evalLinearAddr s nextRip addr
    let oldM := readMem64 s.mem ea
    let (res, f') := evalUnary64 .inc oldM s.flags
    some { sRip with mem := writeMem64 s.mem ea res, flags := f' }
  | .lockXadd _ addr src =>
    let ea := evalLinearAddr s nextRip addr
    let oldM := readMem64 s.mem ea
    let oldR := s.gpr src
    let (sum, f') := evalAlu64 .add oldM oldR s.flags oracle.flags
    some { sRip with gpr := gprUpd s.gpr src oldM, mem := writeMem64 s.mem ea sum, flags := f' }
  | .lockCmpxchg sz addr src =>
    let ea := evalLinearAddr s nextRip addr
    let oldM := readMemZext sz s.mem ea
    let acc  := readGprZext sz s.gpr .rax
    let (_, f') := evalAlu sz .cmp acc oldM s.flags oracle.flags
    if acc == oldM then
      some { sRip with mem := writeMemSz sz s.mem ea (s.gpr src), flags := f' }
    else
      some { sRip with gpr := writeGprSz sz s.gpr .rax oldM, flags := f' }
  | _ => none

end VendorX86RefV2
