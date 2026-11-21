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

/-!
# `VendorArm64Ref.Types`

Mechanically emitted AArch64 Pass-2 reference types, architectural state,
register-31 (`XZR` vs `SP`) disambiguation, 32-bit `W`-write upper-32 zeroing,
64-bit NEON `D`-write upper-64 zeroing, Exclusive Monitor state, and fail-closed
fault taxonomy derived from `awslabs/s2n-bignum@d4518712` (`arm/proofs/*.ml`)
with Armv8-A/v9-A ASL decode-legality and alignment overlays.
-/

namespace VendorArm64Ref

abbrev Reg5 := BitVec 5
abbrev Vec5 := BitVec 5

def reg31 : Reg5 := 31#5
def reg30 : Reg5 := 30#5

inductive GpWidth where
  | w32
  | x64
  deriving DecidableEq, Repr

inductive VecWidth where
  | d64
  | q128
  deriving DecidableEq, Repr

inductive ElemSize where
  | e8
  | e16
  | e32
  | e64
  deriving DecidableEq, Repr

def ElemSize.bits : ElemSize → Nat
  | .e8  => 8
  | .e16 => 16
  | .e32 => 32
  | .e64 => 64

inductive ShiftKind where
  | lsl
  | lsr
  | asr
  | ror
  deriving DecidableEq, Repr

inductive ExtendKind where
  | uxtb | uxth | uxtw | uxtx
  | sxtb | sxth | sxtw | sxtx
  deriving DecidableEq, Repr

structure PStateFlags where
  nf : Bool := false
  zf : Bool := false
  cf : Bool := false
  vf : Bool := false
  deriving DecidableEq, Repr

abbrev ByteMem := BitVec 64 → BitVec 8
abbrev CodeMap := BitVec 64 → Option (BitVec 8)
abbrev ExclMonitor := Option (BitVec 64 × Nat)

/-- Architectural fault & constrained-unpredictable rejection taxonomy.
    Replaces `s2n-bignum`'s unsound `ASSIGNS entirety` (`instruction.ml:3064`)
    with fail-closed fault states. -/
inductive ArmFault where
  | unalignedPc
  | unmappedFetch
  | undefinedEncoding
  | constrainedUnpredictable
  | spAlignmentFault
  | alignmentFault
  deriving DecidableEq, Repr

inductive AddrMode where
  | unsignedOff (off : BitVec 64)
  | unscaledOff (off : BitVec 64)
  | preIndex    (off : BitVec 64)
  | postIndex   (off : BitVec 64)
  | regOff      (rm : Reg5) (ext : ExtendKind) (shift : Nat)
  deriving DecidableEq, Repr

inductive MemSize where
  | b8 | h16 | w32 | x64 | sb8_32 | sb8_64 | sh16_32 | sh16_64
  deriving DecidableEq, Repr

inductive AluOp where
  | add | adds | sub | subs
  deriving DecidableEq, Repr

inductive CarryOp where
  | adc | adcs | sbc | sbcs
  deriving DecidableEq, Repr

inductive LogOp where
  | and_ | bic | orr | orn | eor | eon | ands | bics
  deriving DecidableEq, Repr

inductive WideMovOp where
  | movn | movz | movk
  deriving DecidableEq, Repr

inductive BfmKind where
  | sbfm | bfm | ubfm
  deriving DecidableEq, Repr

inductive CondSelOp where
  | csel | csinc | csinv | csneg
  deriving DecidableEq, Repr

inductive NeonLogicOp where
  | and_ | bic | orr | eor | bsl | bit_ | bif_
  deriving DecidableEq, Repr

inductive NeonArithOp where
  | add | sub | uqadd | uqsub | sqadd | sqsub | addp
  deriving DecidableEq, Repr

inductive NeonCmpOp where
  | cmeq | cmgt | cmhi | cmge | cmeqZero | cmltZero
  deriving DecidableEq, Repr

inductive NeonShiftImmOp where
  | shl | ushr | sshr
  deriving DecidableEq, Repr

inductive NeonReduceOp where
  | uaddlv | addv | umaxv | uminv
  deriving DecidableEq, Repr

inductive AesOp where
  | aese | aesmc | aesd | aesimc
  deriving DecidableEq, Repr

inductive ShaOp where
  | h | h2 | su0 | su1
  deriving DecidableEq, Repr

inductive Instr where
  -- Scalar GP ALU
  | aluImm     (w : GpWidth) (op : AluOp) (rd rn : Reg5) (imm : BitVec 64)
  | aluShift   (w : GpWidth) (op : AluOp) (rd rn rm : Reg5) (sh : ShiftKind) (amt : Nat)
  | aluExt     (w : GpWidth) (op : AluOp) (rd rn rm : Reg5) (ext : ExtendKind) (amt : Nat)
  | aluCarry   (w : GpWidth) (op : CarryOp) (rd rn rm : Reg5)
  | logImm     (w : GpWidth) (op : LogOp) (rd rn : Reg5) (mask : BitVec 64)
  | logShift   (w : GpWidth) (op : LogOp) (rd rn rm : Reg5) (sh : ShiftKind) (amt : Nat)
  | moveWide   (w : GpWidth) (op : WideMovOp) (rd : Reg5) (imm16 : BitVec 16) (pos : Nat)
  | bitfield   (w : GpWidth) (op : BfmKind) (rd rn : Reg5) (immr imms : Nat)
  | extr       (w : GpWidth) (rd rn rm : Reg5) (lsb : Nat)
  | shiftVar   (w : GpWidth) (sh : ShiftKind) (rd rn rm : Reg5)
  | clz        (w : GpWidth) (rd rn : Reg5)
  | revBytes   (w : GpWidth) (rd rn : Reg5)
  | madd       (w : GpWidth) (sub : Bool) (rd rn rm ra : Reg5)
  | mulHigh    (signed : Bool) (rd rn rm : Reg5)
  | umaddl     (sub : Bool) (rd rn rm ra : Reg5)
  | divInt     (w : GpWidth) (signed : Bool) (rd rn rm : Reg5)
  | condSel    (w : GpWidth) (op : CondSelOp) (rd rn rm : Reg5) (cond : BitVec 4)
  | condCmp    (w : GpWidth) (sub : Bool) (rn : Reg5) (rmOrImm : Sum Reg5 (BitVec 5)) (nzcv : BitVec 4) (cond : BitVec 4)
  -- PC-relative, Branches & Hints
  | adr        (page : Bool) (rd : Reg5) (off : BitVec 64)
  | branchImm  (link : Bool) (off : BitVec 64)
  | branchCond (cond : BitVec 4) (off : BitVec 64)
  | cbz        (w : GpWidth) (nz : Bool) (rt : Reg5) (off : BitVec 64)
  | tbz        (nz : Bool) (rt : Reg5) (bitIdx : Nat) (off : BitVec 64)
  | ret        (rn : Reg5)
  | hintNop
  -- Memory, Pairs, Atomics & CRC32
  | ldstGp     (load : Bool) (sz : MemSize) (rt rn : Reg5) (mode : AddrMode)
  | ldstPairGp (load : Bool) (w : GpWidth) (rt1 rt2 rn : Reg5) (mode : AddrMode)
  | ldstSimd   (load : Bool) (vw : VecWidth) (vt : Vec5) (rn : Reg5) (mode : AddrMode)
  | ldstPairSimd (load : Bool) (vw : VecWidth) (vt1 vt2 : Vec5) (rn : Reg5) (mode : AddrMode)
  | ldar       (w : GpWidth) (exclusive : Bool) (rt rn : Reg5)
  | stlr       (w : GpWidth) (rt rn : Reg5)
  | stlxr      (w : GpWidth) (rs rt rn : Reg5)
  | clrex
  | crc32      (castagnoli : Bool) (bytes : Nat) (rd rn rm : Reg5)
  -- NEON + Crypto
  | neonMovi   (vw : VecWidth) (vd : Vec5) (imm64 : BitVec 64)
  | neonDupGp  (vw : VecWidth) (es : ElemSize) (vd : Vec5) (rn : Reg5)
  | fmovGpToVec (w : GpWidth) (vd : Vec5) (rn : Reg5)
  | fmovVecToGp (w : GpWidth) (rd : Reg5) (vn : Vec5)
  | neonUmov   (es : ElemSize) (rd : Reg5) (vn : Vec5) (idx : Nat)
  | neonInsGp  (es : ElemSize) (vd : Vec5) (rn : Reg5) (idx : Nat)
  | neonInsElt (es : ElemSize) (vd vn : Vec5) (dstIdx srcIdx : Nat)
  | neonArith  (vw : VecWidth) (es : ElemSize) (op : NeonArithOp) (vd vn vm : Vec5)
  | neonLogic  (vw : VecWidth) (op : NeonLogicOp) (vd vn vm : Vec5)
  | neonCmp    (vw : VecWidth) (es : ElemSize) (op : NeonCmpOp) (vd vn vm : Vec5)
  | neonShiftImm (vw : VecWidth) (es : ElemSize) (op : NeonShiftImmOp) (vd vn : Vec5) (amt : Nat)
  | neonShiftVar (vw : VecWidth) (es : ElemSize) (signed : Bool) (vd vn vm : Vec5)
  | neonUaddlp (vw : VecWidth) (es : ElemSize) (vd vn : Vec5)
  | neonReduce (vw : VecWidth) (es : ElemSize) (op : NeonReduceOp) (vd vn : Vec5)
  | neonRev64  (vw : VecWidth) (es : ElemSize) (vd vn : Vec5)
  | neonExt    (vw : VecWidth) (vd vn vm : Vec5) (imm4 : Nat)
  | neonTbl1   (vw : VecWidth) (vd vn vm : Vec5)
  | neonCnt    (vw : VecWidth) (vd vn : Vec5)
  | neonPmul   (vw : VecWidth) (vd vn vm : Vec5)
  | neonPmull  (high : Bool) (es : ElemSize) (vd vn vm : Vec5)
  | cryptoAes  (op : AesOp) (vd vn : Vec5)
  | cryptoSha256 (op : ShaOp) (vd vn vm : Vec5)
  | cryptoSha512 (op : ShaOp) (vd vn vm : Vec5)
  deriving DecidableEq, Repr

structure MachineState where
  pc     : BitVec 64 := 0#64
  xreg   : Reg5 → BitVec 64 := fun _ => 0#64
  sp     : BitVec 64 := 0#64
  vreg   : Vec5 → BitVec 128 := fun _ => 0#128
  flags  : PStateFlags := {}
  mem    : ByteMem := fun _ => 0#8
  excl   : ExclMonitor := none
  halted : Bool := false
  fault  : Option ArmFault := none

def maskWidth (w : GpWidth) (v : BitVec 64) : BitVec 64 :=
  match w with
  | .x64 => v
  | .w32 => (BitVec.extractLsb' 0 32 v).zeroExtend 64

/-- `XREG` (`instruction.ml:85`) / `WREG` (`instruction.ml:147`):
    register 31 is `XZR`/`WZR` (reads `0`, discards writes); 32-bit writes zero
    bits `[63:32]`. -/
def readXzr (w : GpWidth) (s : MachineState) (r : Reg5) : BitVec 64 :=
  if r == reg31 then 0#64 else maskWidth w (s.xreg r)

def writeXzr (w : GpWidth) (s : MachineState) (r : Reg5) (v : BitVec 64) : MachineState :=
  if r == reg31 then s
  else
    let v' := maskWidth w v
    { s with xreg := fun r' => if r' == r then v' else s.xreg r' }

/-- `XREG_SP` / `WREG_SP` (`decode.ml:10-11`):
    register 31 accesses architectural `SP` / `WSP` (with 32-bit write zeroing
    `SP[63:32]`). -/
def readSp (w : GpWidth) (s : MachineState) (r : Reg5) : BitVec 64 :=
  if r == reg31 then maskWidth w s.sp else maskWidth w (s.xreg r)

def writeSp (w : GpWidth) (s : MachineState) (r : Reg5) (v : BitVec 64) : MachineState :=
  let v' := maskWidth w v
  if r == reg31 then { s with sp := v' }
  else { s with xreg := fun r' => if r' == r then v' else s.xreg r' }

/-- `QREG` / `DREG` (`instruction.ml:244-246`, `arm.ml:198-231`):
    64-bit NEON (`D`-register / `datasize = 64`) writes zero bits `[127:64]`. -/
def readVec (s : MachineState) (v : Vec5) : BitVec 128 :=
  s.vreg v

def writeVec (vw : VecWidth) (s : MachineState) (v : Vec5) (val : BitVec 128) : MachineState :=
  let val' := match vw with
    | .q128 => val
    | .d64  => (BitVec.extractLsb' 0 64 val).zeroExtend 128
  { s with vreg := fun v' => if v' == v then val' else s.vreg v' }

def readMem8 (m : ByteMem) (a : BitVec 64) : BitVec 8 := m a

def readMem16 (m : ByteMem) (a : BitVec 64) : BitVec 16 :=
  (m (a + 1#64)) ++ (m a)

def readMem32 (m : ByteMem) (a : BitVec 64) : BitVec 32 :=
  (readMem16 m (a + 2#64)) ++ (readMem16 m a)

def readMem64 (m : ByteMem) (a : BitVec 64) : BitVec 64 :=
  (readMem32 m (a + 4#64)) ++ (readMem32 m a)

def readMem128 (m : ByteMem) (a : BitVec 64) : BitVec 128 :=
  (readMem64 m (a + 8#64)) ++ (readMem64 m a)

def writeMem8 (m : ByteMem) (a : BitVec 64) (v : BitVec 8) : ByteMem :=
  fun addr => if addr == a then v else m addr

def writeMem16 (m : ByteMem) (a : BitVec 64) (v : BitVec 16) : ByteMem :=
  let m1 := writeMem8 m a (BitVec.extractLsb' 0 8 v)
  writeMem8 m1 (a + 1#64) (BitVec.extractLsb' 8 8 v)

def writeMem32 (m : ByteMem) (a : BitVec 64) (v : BitVec 32) : ByteMem :=
  let m1 := writeMem16 m a (BitVec.extractLsb' 0 16 v)
  writeMem16 m1 (a + 2#64) (BitVec.extractLsb' 16 16 v)

def writeMem64 (m : ByteMem) (a : BitVec 64) (v : BitVec 64) : ByteMem :=
  let m1 := writeMem32 m a (BitVec.extractLsb' 0 32 v)
  writeMem32 m1 (a + 4#64) (BitVec.extractLsb' 32 32 v)

def writeMem128 (m : ByteMem) (a : BitVec 64) (v : BitVec 128) : ByteMem :=
  let m1 := writeMem64 m a (BitVec.extractLsb' 0 64 v)
  writeMem64 m1 (a + 8#64) (BitVec.extractLsb' 64 64 v)

/-- 4-byte aligned little-endian instruction fetch (`arm.ml:18` `aligned_bytes_loaded`). -/
def fetchWord32 (code : CodeMap) (pc : BitVec 64) : Except ArmFault (BitVec 32) :=
  if (pc &&& 3#64) != 0#64 then
    .error .unalignedPc
  else
    match code pc, code (pc + 1#64), code (pc + 2#64), code (pc + 3#64) with
    | some b0, some b1, some b2, some b3 =>
      .ok (((b3 ++ b2) ++ (b1 ++ b0)))
    | _, _, _, _ => .error .unmappedFetch

end VendorArm64Ref
