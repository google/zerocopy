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
# `VendorArm64Ref.SemanticsScalar`

Pure, `Nat.rec`-total (`0` `isPartial`) AArch64 scalar GP ALU, NZCV flags,
bitfield, `ADRP` 4 KiB page-masking, branches, `SP` 16-byte alignment check,
`LDAR`/`STLR`/`LDAXR`/`STLXR`/`CLREX` alignment + `ExclusiveMonitor`, and
CRC32/CRC32C operational semantics.
-/

namespace VendorArm64Ref

def evalCond (f : PStateFlags) (cond : BitVec 4) : Bool :=
  let base := match (cond.toNat / 2) with
    | 0 => f.zf
    | 1 => f.cf
    | 2 => f.nf
    | 3 => f.vf
    | 4 => f.cf && !f.zf
    | 5 => f.nf == f.vf
    | 6 => (f.nf == f.vf) && !f.zf
    | _ => true
  if (cond.toNat % 2) == 1 && cond != 0b1111#4 then !base else base

def addWithCarry32 (x y : BitVec 32) (carryIn : Bool) : BitVec 32 × PStateFlags :=
  let cNat := if carryIn then 1 else 0
  let uSum := x.toNat + y.toNat + cNat
  let sSum := x.toInt + y.toInt + Int.ofNat cNat
  let res  := BitVec.ofNat 32 uSum
  let nf   := res.msb
  let zf   := res == 0#32
  let cf   := decide (uSum >= 2 ^ 32)
  let vf   := decide (res.toInt != sSum)
  (res, { nf := nf, zf := zf, cf := cf, vf := vf })

def addWithCarry64 (x y : BitVec 64) (carryIn : Bool) : BitVec 64 × PStateFlags :=
  let cNat := if carryIn then 1 else 0
  let uSum := x.toNat + y.toNat + cNat
  let sSum := x.toInt + y.toInt + Int.ofNat cNat
  let res  := BitVec.ofNat 64 uSum
  let nf   := res.msb
  let zf   := res == 0#64
  let cf   := decide (uSum >= 2 ^ 64)
  let vf   := decide (res.toInt != sSum)
  (res, { nf := nf, zf := zf, cf := cf, vf := vf })

def addWithCarryW (w : GpWidth) (x y : BitVec 64) (carryIn : Bool) : BitVec 64 × PStateFlags :=
  match w with
  | .x64 => addWithCarry64 x y carryIn
  | .w32 =>
    let (r32, fl) := addWithCarry32 (BitVec.extractLsb' 0 32 x) (BitVec.extractLsb' 0 32 y) carryIn
    (r32.zeroExtend 64, fl)

def shiftValW (w : GpWidth) (sh : ShiftKind) (v : BitVec 64) (amt : Nat) : BitVec 64 :=
  match w with
  | .x64 =>
    let a := amt % 64
    match sh with
    | .lsl => v <<< a
    | .lsr => v >>> a
    | .asr => BitVec.sshiftRight v a
    | .ror => if a == 0 then v else (v >>> a) ||| (v <<< (64 - a))
  | .w32 =>
    let v32 := BitVec.extractLsb' 0 32 v
    let a := amt % 32
    let r32 := match sh with
      | .lsl => v32 <<< a
      | .lsr => v32 >>> a
      | .asr => BitVec.sshiftRight v32 a
      | .ror => if a == 0 then v32 else (v32 >>> a) ||| (v32 <<< (32 - a))
    r32.zeroExtend 64

def extendVal64 (ext : ExtendKind) (v : BitVec 64) (shift : Nat) : BitVec 64 :=
  let base : BitVec 64 := match ext with
    | .uxtb => (BitVec.extractLsb' 0 8  v).zeroExtend 64
    | .uxth => (BitVec.extractLsb' 0 16 v).zeroExtend 64
    | .uxtw => (BitVec.extractLsb' 0 32 v).zeroExtend 64
    | .uxtx => v
    | .sxtb => (BitVec.extractLsb' 0 8  v).signExtend 64
    | .sxth => (BitVec.extractLsb' 0 16 v).signExtend 64
    | .sxtw => (BitVec.extractLsb' 0 32 v).signExtend 64
    | .sxtx => v
  base <<< shift

def clzWidth (width : Nat) (v : BitVec 64) : Nat :=
  Nat.rec (motive := fun _ => Nat × Bool)
    (0, false)
    (fun k (cnt, done) =>
      if done then (cnt, true)
      else
        let bitIdx := width - 1 - k
        if v.getLsbD bitIdx then (cnt, true) else (cnt + 1, false))
    width |>.1

def revBytes32 (v : BitVec 32) : BitVec 32 :=
  let b0 := BitVec.extractLsb' 0  8 v
  let b1 := BitVec.extractLsb' 8  8 v
  let b2 := BitVec.extractLsb' 16 8 v
  let b3 := BitVec.extractLsb' 24 8 v
  ((b0 ++ b1) ++ (b2 ++ b3))

def revBytes64 (v : BitVec 64) : BitVec 64 :=
  let lo := revBytes32 (BitVec.extractLsb' 0  32 v)
  let hi := revBytes32 (BitVec.extractLsb' 32 32 v)
  (lo ++ hi)

/-- `Nat.rec`-total reflected CRC-32 (`0xedb88320`) / CRC-32C (`0x82f63b78`)
    4-bit Sarwate nibble lookup tables (`0` `isPartial`, `O(nibs)` kernel WHNF). -/
def crcNibIeee (i : Nat) : Nat :=
  match i with
  | 0  => 0x00000000 | 1  => 0x1db71064 | 2  => 0x3b6e20c8 | 3  => 0x26d930ac
  | 4  => 0x76dc4190 | 5  => 0x6b6b51f4 | 6  => 0x4db26158 | 7  => 0x5005713c
  | 8  => 0xedb88320 | 9  => 0xf00f9344 | 10 => 0xd6d6a3e8 | 11 => 0xcb61b38c
  | 12 => 0x9b64c2b0 | 13 => 0x86d3d2d4 | 14 => 0xa00ae278 | _  => 0xbdbdf21c

def crcNibCast (i : Nat) : Nat :=
  match i with
  | 0  => 0x00000000 | 1  => 0x105ec76f | 2  => 0x20bd8ede | 3  => 0x30e349b1
  | 4  => 0x417b1dbc | 5  => 0x5125dad3 | 6  => 0x61c69362 | 7  => 0x7198540d
  | 8  => 0x82f63b78 | 9  => 0x92a8fc17 | 10 => 0xa24bb5a6 | 11 => 0xb21572c9
  | 12 => 0xc38d26c4 | 13 => 0xd3d3e1ab | 14 => 0xe330a81a | _  => 0xf36e6f75

def crc32StepNib (castagnoli : Bool) (nib : Nat) (c : Nat) : Nat :=
  let idx := Nat.land (Nat.xor c nib) 15
  let tbl := if castagnoli then crcNibCast idx else crcNibIeee idx
  Nat.xor (Nat.shiftRight c 4) tbl

def crc32Multi (castagnoli : Bool) (bytes : Nat) (crc : BitVec 32) (val : BitVec 64) : BitVec 32 :=
  let nibs := bytes * 2
  let vNat := val.toNat
  let res := Nat.rec (motive := fun _ => Nat)
    crc.toNat
    (fun k acc => crc32StepNib castagnoli (Nat.land (Nat.shiftRight vNat (k * 4)) 15) acc)
    nibs
  BitVec.ofNat 32 res

def execAluCore (w : GpWidth) (op : AluOp) (s : MachineState) (nextPc : BitVec 64)
    (useSpRd : Bool) (rd : Reg5) (lhs rhs : BitVec 64) : MachineState :=
  let (res, fl) := match op with
    | .add  => addWithCarryW w lhs rhs false
    | .adds => addWithCarryW w lhs rhs false
    | .sub  => addWithCarryW w lhs (~~~rhs) true
    | .subs => addWithCarryW w lhs (~~~rhs) true
  let setsFlags := (op == .adds) || (op == .subs)
  let s1 := if useSpRd && !setsFlags then writeSp w s rd res else writeXzr w s rd res
  let s2 := if setsFlags then { s1 with flags := fl } else s1
  { s2 with pc := nextPc }

def execBitfield (w : GpWidth) (op : BfmKind) (rd rn : Reg5) (immr imms : Nat)
    (s : MachineState) (nextPc : BitVec 64) : MachineState :=
  let width := match w with | .x64 => 64 | .w32 => 32
  let src := readXzr w s rn
  let dst := readXzr w s rd
  let res : BitVec 64 :=
    if imms >= immr then
      let len := imms - immr + 1
      let mask : BitVec 64 := (1#64 <<< len) - 1#64
      let extracted := (src >>> immr) &&& mask
      match op with
      | .ubfm => extracted
      | .bfm  => (dst &&& (~~~mask)) ||| extracted
      | .sbfm =>
        let signBit := src.getLsbD imms
        if signBit && len < 64 then extracted ||| ((~~~0#64) <<< len) else extracted
    else
      let pos := width - immr
      let len := imms + 1
      let maskLow : BitVec 64 := (1#64 <<< len) - 1#64
      let shifted := (src &&& maskLow) <<< pos
      let dstMask : BitVec 64 := maskLow <<< pos
      match op with
      | .ubfm => maskWidth w shifted
      | .bfm  => maskWidth w ((dst &&& (~~~dstMask)) ||| shifted)
      | .sbfm =>
        let signBit := src.getLsbD imms
        let topFill : BitVec 64 :=
          if signBit && (pos + len) < 64 then (~~~0#64) <<< (pos + len) else 0#64
        maskWidth w (shifted ||| topFill)
  let s1 := writeXzr w s rd res
  { s1 with pc := nextPc }

/-- Compute effective address + optional writeback value, enforcing Armv8-A
    `CheckSPAlignment()` (`SP % 16 == 0`) whenever `Rn == 31`. -/
def evalAddrMode (s : MachineState) (rn : Reg5) (mode : AddrMode)
    : Except ArmFault (BitVec 64 × Option (BitVec 64)) :=
  if rn == reg31 && ((s.sp &&& 15#64) != 0#64) then
    .error .spAlignmentFault
  else
    let base := readSp .x64 s rn
    match mode with
    | .unsignedOff off => .ok (base + off, none)
    | .unscaledOff off => .ok (base + off, none)
    | .preIndex off    => let ea := base + off; .ok (ea, some ea)
    | .postIndex off   => .ok (base, some (base + off))
    | .regOff rm ext sh =>
      let idx := extendVal64 ext (readXzr .x64 s rm) sh
      .ok (base + idx, none)

/-- Check `LDAR`/`STLR`/`LDAXR`/`STLXR` alignment (`AArch64.CheckAlignment` for
    `AccType_ORDERED` and `AccType_ATOMIC`):
    - Under baseline Armv8.0-A (`lse2Align16B == false`, e.g. `cortex-a53`), `ea`
      must be naturally aligned (`ea % szBytes == 0`), else `.alignmentFault` (`SIGBUS`).
    - Under Armv8.4-A `FEAT_LSE2` (`lse2Align16B == true`, e.g. `qemu-aarch64 -cpu max`),
      accesses whose bytes lie wholly within a single 16-byte aligned block
      (`(ea % 16) + szBytes <= 16`) succeed, while cross-16B accesses raise `.alignmentFault`. -/
def checkOrderedAlign (lse2Align16B : Bool) (_isExcl : Bool) (szBytes : Nat) (ea : BitVec 64) : Bool :=
  let mask := BitVec.ofNat 64 (szBytes - 1)
  if (ea &&& mask) == 0#64 then true
  else if lse2Align16B then
    ((ea.toNat % 16) + szBytes) <= 16
  else false

def execScalarInstr (exclSpuriousFail : Bool) (lse2Align16B : Bool) (ins : Instr)
    (s : MachineState) : Option MachineState :=
  let nextPc := s.pc + 4#64
  match ins with
  | .hintNop => some { s with pc := nextPc }
  | .clrex   => some { s with pc := nextPc, excl := none }
  | .ret rn  => some { s with pc := readXzr .x64 s rn }

  -- Reconciles `arm.ml:140` + `instruction.ml:750-758`: uses true `s.pc` (never `nextPc`)!
  | .adr page rd off =>
    let base := if page then (s.pc &&& 0xfffffffffffff000#64) else s.pc
    let s1 := writeXzr .x64 s rd (base + off)
    some { s1 with pc := nextPc }

  | .branchImm link off =>
    let s1 := if link then writeXzr .x64 s reg30 nextPc else s
    some { s1 with pc := s.pc + off }

  | .branchCond cond off =>
    let target := if evalCond s.flags cond then s.pc + off else nextPc
    some { s with pc := target }

  | .cbz w nz rt off =>
    let v := readXzr w s rt
    let isZero := v == 0#64
    let take := if nz then !isZero else isZero
    some { s with pc := if take then s.pc + off else nextPc }

  | .tbz nz rt bitIdx off =>
    let v := readXzr .x64 s rt
    let bSet := v.getLsbD bitIdx
    let take := if nz then bSet else !bSet
    some { s with pc := if take then s.pc + off else nextPc }

  | .aluImm w op rd rn imm =>
    some (execAluCore w op s nextPc true rd (readSp w s rn) imm)

  | .aluShift w op rd rn rm sh amt =>
    let rhs := shiftValW w sh (readXzr w s rm) amt
    some (execAluCore w op s nextPc false rd (readXzr w s rn) rhs)

  | .aluExt w op rd rn rm ext amt =>
    let rhs := maskWidth w (extendVal64 ext (readXzr .x64 s rm) amt)
    some (execAluCore w op s nextPc true rd (readSp w s rn) rhs)

  | .aluCarry w op rd rn rm =>
    let lhs := readXzr w s rn
    let rhs := readXzr w s rm
    let (res, fl) := match op with
      | .adc  => addWithCarryW w lhs rhs s.flags.cf
      | .adcs => addWithCarryW w lhs rhs s.flags.cf
      | .sbc  => addWithCarryW w lhs (~~~rhs) s.flags.cf
      | .sbcs => addWithCarryW w lhs (~~~rhs) s.flags.cf
    let setsFlags := (op == .adcs) || (op == .sbcs)
    let s1 := writeXzr w s rd res
    let s2 := if setsFlags then { s1 with flags := fl } else s1
    some { s2 with pc := nextPc }

  | .logImm w op rd rn mask =>
    let lhs := readXzr w s rn
    let res := maskWidth w (match op with
      | .and_ | .ands => lhs &&& mask
      | .orr          => lhs ||| mask
      | .eor          => lhs ^^^ mask
      | _             => lhs &&& mask)
    let setsFlags := op == .ands
    let s1 := if setsFlags then writeXzr w s rd res else writeSp w s rd res
    let nf := match w with | .x64 => res.msb | .w32 => res.getLsbD 31
    let s2 := if setsFlags then
      { s1 with flags := { nf := nf, zf := res == 0#64, cf := false, vf := false } }
    else s1
    some { s2 with pc := nextPc }

  | .logShift w op rd rn rm sh amt =>
    let lhs := readXzr w s rn
    let rhs := shiftValW w sh (readXzr w s rm) amt
    let res := maskWidth w (match op with
      | .and_ | .ands => lhs &&& rhs
      | .bic  | .bics => lhs &&& (~~~rhs)
      | .orr          => lhs ||| rhs
      | .orn          => lhs ||| (~~~rhs)
      | .eor          => lhs ^^^ rhs
      | .eon          => lhs ^^^ (~~~rhs))
    let setsFlags := (op == .ands) || (op == .bics)
    let s1 := writeXzr w s rd res
    let nf := match w with | .x64 => res.msb | .w32 => res.getLsbD 31
    let s2 := if setsFlags then
      { s1 with flags := { nf := nf, zf := res == 0#64, cf := false, vf := false } }
    else s1
    some { s2 with pc := nextPc }

  | .moveWide w op rd imm16 pos =>
    let shifted : BitVec 64 := (imm16.zeroExtend 64) <<< pos
    let res : BitVec 64 := match op with
      | .movz => shifted
      | .movn => maskWidth w (~~~shifted)
      | .movk =>
        let clrMask : BitVec 64 := ~~~((0xffff#64) <<< pos)
        (readXzr w s rd &&& clrMask) ||| shifted
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .bitfield w op rd rn immr imms =>
    some (execBitfield w op rd rn immr imms s nextPc)

  | .extr w rd rn rm lsb =>
    let hi := readXzr w s rn
    let lo := readXzr w s rm
    let res : BitVec 64 := match w with
      | .x64 =>
        let pair128 : BitVec 128 := hi ++ lo
        BitVec.extractLsb' lsb 64 pair128
      | .w32 =>
        let pair64 : BitVec 64 := (BitVec.extractLsb' 0 32 hi) ++ (BitVec.extractLsb' 0 32 lo)
        (BitVec.extractLsb' lsb 32 pair64).zeroExtend 64
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .shiftVar w sh rd rn rm =>
    let amt := (readXzr w s rm).toNat
    let res := shiftValW w sh (readXzr w s rn) amt
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .clz w rd rn =>
    let cnt := clzWidth (match w with | .x64 => 64 | .w32 => 32) (readXzr w s rn)
    let s1 := writeXzr w s rd (BitVec.ofNat 64 cnt)
    some { s1 with pc := nextPc }

  | .revBytes w rd rn =>
    let v := readXzr w s rn
    let res := match w with
      | .x64 => revBytes64 v
      | .w32 => (revBytes32 (BitVec.extractLsb' 0 32 v)).zeroExtend 64
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .madd w sub rd rn rm ra =>
    let n := readXzr w s rn
    let m := readXzr w s rm
    let a := readXzr w s ra
    let prod := n * m
    let res := maskWidth w (if sub then a - prod else a + prod)
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .mulHigh signed rd rn rm =>
    let n := readXzr .x64 s rn
    let m := readXzr .x64 s rm
    let res : BitVec 64 :=
      if signed then
        let prod128 : BitVec 128 := BitVec.ofInt 128 (n.toInt * m.toInt)
        BitVec.extractLsb' 64 64 prod128
      else
        let prod128 : BitVec 128 := BitVec.ofNat 128 (n.toNat * m.toNat)
        BitVec.extractLsb' 64 64 prod128
    let s1 := writeXzr .x64 s rd res
    some { s1 with pc := nextPc }

  | .umaddl sub rd rn rm ra =>
    let n := (BitVec.extractLsb' 0 32 (readXzr .w32 s rn)).toNat
    let m := (BitVec.extractLsb' 0 32 (readXzr .w32 s rm)).toNat
    let a := readXzr .x64 s ra
    let prod := BitVec.ofNat 64 (n * m)
    let res := if sub then a - prod else a + prod
    let s1 := writeXzr .x64 s rd res
    some { s1 with pc := nextPc }

  -- Armv8-A total integer division: division by `0` returns `0` (never traps!) and
  -- signed `INT_MIN / -1` wraps to `INT_MIN`.
  | .divInt w signed rd rn rm =>
    let lhs := readXzr w s rn
    let rhs := readXzr w s rm
    let res : BitVec 64 :=
      if rhs == 0#64 then 0#64
      else
        match w, signed with
        | .x64, false => BitVec.ofNat 64 (lhs.toNat / rhs.toNat)
        | .w32, false => BitVec.ofNat 64 ((BitVec.extractLsb' 0 32 lhs).toNat / (BitVec.extractLsb' 0 32 rhs).toNat)
        | .x64, true  => BitVec.ofInt 64 (Int.tdiv lhs.toInt rhs.toInt)
        | .w32, true  =>
          let q32 := BitVec.ofInt 32 (Int.tdiv (BitVec.extractLsb' 0 32 lhs).toInt (BitVec.extractLsb' 0 32 rhs).toInt)
          q32.zeroExtend 64
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .condSel w op rd rn rm cond =>
    let res : BitVec 64 :=
      if evalCond s.flags cond then readXzr w s rn
      else
        let m := readXzr w s rm
        match op with
        | .csel  => m
        | .csinc => maskWidth w (m + 1#64)
        | .csinv => maskWidth w (~~~m)
        | .csneg => maskWidth w (0#64 - m)
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .condCmp w sub rn rmOrImm nzcv cond =>
    let fl : PStateFlags :=
      if evalCond s.flags cond then
        let lhs := readXzr w s rn
        let rhs := match rmOrImm with
          | .inl rm   => readXzr w s rm
          | .inr imm5 => imm5.zeroExtend 64
        if sub then (addWithCarryW w lhs (~~~rhs) true).2
        else (addWithCarryW w lhs rhs false).2
      else
        { nf := nzcv.getLsbD 3, zf := nzcv.getLsbD 2, cf := nzcv.getLsbD 1, vf := nzcv.getLsbD 0 }
    some { s with pc := nextPc, flags := fl }

  | .crc32 castagnoli bytes rd rn rm =>
    let accIn := BitVec.extractLsb' 0 32 (readXzr .w32 s rn)
    let valIn := readXzr (if bytes == 8 then .x64 else .w32) s rm
    let out32 := crc32Multi castagnoli bytes accIn valIn
    let s1 := writeXzr .w32 s rd (out32.zeroExtend 64)
    some { s1 with pc := nextPc }

  | .ldstGp load msz rt rn mode =>
    match evalAddrMode s rn mode with
    | .error f => some { s with fault := some f }
    | .ok (ea, wbOpt) =>
      let sAfterMem : MachineState :=
        if load then
          match msz with
          | .b8      => writeXzr .w32 s rt ((readMem8  s.mem ea).zeroExtend 64)
          | .h16     => writeXzr .w32 s rt ((readMem16 s.mem ea).zeroExtend 64)
          | .w32     => writeXzr .w32 s rt ((readMem32 s.mem ea).zeroExtend 64)
          | .x64     => writeXzr .x64 s rt (readMem64  s.mem ea)
          | .sb8_32  => writeXzr .w32 s rt (((readMem8  s.mem ea).signExtend 32).zeroExtend 64)
          | .sb8_64  => writeXzr .x64 s rt ((readMem8  s.mem ea).signExtend 64)
          | .sh16_32 => writeXzr .w32 s rt (((readMem16 s.mem ea).signExtend 32).zeroExtend 64)
          | .sh16_64 => writeXzr .x64 s rt ((readMem16 s.mem ea).signExtend 64)
        else
          let v := readXzr .x64 s rt
          let m' := match msz with
            | .b8  => writeMem8  s.mem ea (BitVec.extractLsb' 0 8  v)
            | .h16 => writeMem16 s.mem ea (BitVec.extractLsb' 0 16 v)
            | .w32 => writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v)
            | _    => writeMem64 s.mem ea v
          { s with mem := m', excl := none }
      let sWb := match wbOpt with
        | some wbVal => writeSp .x64 sAfterMem rn wbVal
        | none       => sAfterMem
      some { sWb with pc := nextPc }

  | .ldstPairGp load w rt1 rt2 rn mode =>
    match evalAddrMode s rn mode with
    | .error f => some { s with fault := some f }
    | .ok (ea, wbOpt) =>
      let stepBytes : BitVec 64 := match w with | .x64 => 8#64 | .w32 => 4#64
      let sAfterMem : MachineState :=
        if load then
          let v1 := match w with
            | .x64 => readMem64 s.mem ea
            | .w32 => (readMem32 s.mem ea).zeroExtend 64
          let v2 := match w with
            | .x64 => readMem64 s.mem (ea + stepBytes)
            | .w32 => (readMem32 s.mem (ea + stepBytes)).zeroExtend 64
          let s1 := writeXzr w s rt1 v1
          writeXzr w s1 rt2 v2
        else
          let v1 := readXzr w s rt1
          let v2 := readXzr w s rt2
          let m' := match w with
            | .x64 => writeMem64 (writeMem64 s.mem ea v1) (ea + stepBytes) v2
            | .w32 => writeMem32 (writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v1))
                                 (ea + stepBytes) (BitVec.extractLsb' 0 32 v2)
          { s with mem := m', excl := none }
      let sWb := match wbOpt with
        | some wbVal => writeSp .x64 sAfterMem rn wbVal
        | none       => sAfterMem
      some { sWb with pc := nextPc }

  | .ldar w exclusive rt rn =>
    if rn == reg31 && ((s.sp &&& 15#64) != 0#64) then
      some { s with fault := some .spAlignmentFault }
    else
      let ea := readSp .x64 s rn
      let szBytes := match w with | .x64 => 8 | .w32 => 4
      if !checkOrderedAlign lse2Align16B exclusive szBytes ea then
        some { s with fault := some .alignmentFault }
      else
        let val := match w with
          | .x64 => readMem64 s.mem ea
          | .w32 => (readMem32 s.mem ea).zeroExtend 64
        let s1 := writeXzr w s rt val
        let ex' := if exclusive then some (ea, szBytes) else s1.excl
        some { s1 with pc := nextPc, excl := ex' }

  | .stlr w rt rn =>
    if rn == reg31 && ((s.sp &&& 15#64) != 0#64) then
      some { s with fault := some .spAlignmentFault }
    else
      let ea := readSp .x64 s rn
      let szBytes := match w with | .x64 => 8 | .w32 => 4
      if !checkOrderedAlign lse2Align16B false szBytes ea then
        some { s with fault := some .alignmentFault }
      else
        let v := readXzr w s rt
        let m' := match w with
          | .x64 => writeMem64 s.mem ea v
          | .w32 => writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v)
        some { s with pc := nextPc, mem := m', excl := none }

  | .stlxr w rs rt rn =>
    if rn == reg31 && ((s.sp &&& 15#64) != 0#64) then
      some { s with fault := some .spAlignmentFault }
    else
      let ea := readSp .x64 s rn
      let szBytes := match w with | .x64 => 8 | .w32 => 4
      if !checkOrderedAlign lse2Align16B true szBytes ea then
        some { s with fault := some .alignmentFault }
      else
        let monitorHit := match s.excl with
          | some (monAddr, monSz) => (monAddr == ea) && (monSz == szBytes)
          | none => false
        if monitorHit && !exclSpuriousFail then
          let v := readXzr w s rt
          let m' := match w with
            | .x64 => writeMem64 s.mem ea v
            | .w32 => writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v)
          let s1 := writeXzr .w32 { s with mem := m', excl := none } rs 0#64
          some { s1 with pc := nextPc }
        else
          let s1 := writeXzr .w32 { s with excl := none } rs 1#64
          some { s1 with pc := nextPc }

  | _ => none

end VendorArm64Ref
