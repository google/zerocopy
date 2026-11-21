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
import Init.Omega
import VendorX86GccRef
import ByteX86Gcc
import ByteX86GccDecodePass2

/-!
# `ByteX86GccPass2`

Kernel-checked Pass-2 operational state simulation (`0` `sorry`, `0` `isPartial`)
completing `ByteX86GccDecodePass2` (`decodeRef_commutes_of_len16`):

1. **Universal Single-Step & Multi-Step Forward Simulation
   (`vendorX86GccRef_step_sub_byteX86Gcc_step`,
   `vendorX86GccRef_stepsN_sub_byteX86Gcc_stepsN`):**
   `VendorX86GccRef.Step ⊆ ByteX86Gcc.Step` and `VendorX86GccRef.StepsN ⊆ ByteX86Gcc.StepsN`.
2. **Reverse Soundness Counterexamples:**
   - `misdecoded_rex_subreg8_refinement_counterexample` (`88 df` `mov bh, bl` vs `mov dil, bl`)
   - `collapsed_legacy_sse_vex_refinement_counterexample` (`66 0f ef c0` `pxor` vs VEX-128)
-/

namespace ByteX86GccPass2

/-! ## Section 3: Operational State Homomorphism & Universal Forward Simulation -/

def mapFlags (f : VendorX86GccRef.RFlags) : ByteX86Gcc.RFlags :=
  { cf := f.cf, pf := f.pf, af := f.af, zf := f.zf, sf := f.sf, of := f.of }

def mapOracle (o : VendorX86GccRef.UndefOracle) : ByteX86Gcc.UndefChoice :=
  { flags := mapFlags o.flags, undefGpr := o.gpr }

def mapState (s : VendorX86GccRef.MachineState) : ByteX86Gcc.X64State :=
  { rip    := s.rip
    regs   := fun r => s.gpr (unmapReg r)
    ymms   := s.ymm
    flags  := mapFlags s.flags
    mem    := s.mem
    halted := s.halted
    fault  := s.fault.isSome }

theorem gprUpd_commutes (gpr : VendorX86GccRef.Gpr → BitVec 64)
    (g : VendorX86GccRef.Gpr) (v : BitVec 64) :
    ByteX86Gcc.regUpd (fun r => gpr (unmapReg r)) (mapGpr g) v =
      (fun r => VendorX86GccRef.gprUpd gpr g v (unmapReg r)) := by
  funext r
  cases r <;> cases g <;> rfl

theorem readReg8_eq (gpr : VendorX86GccRef.Gpr → BitVec 64) (r8 : VendorX86GccRef.Reg8) :
    ByteX86Gcc.readSubReg8 (fun r => gpr (unmapReg r)) (mapReg8 r8) =
      VendorX86GccRef.readReg8 gpr r8 := by
  cases r8 <;> simp [mapReg8, ByteX86Gcc.readSubReg8, VendorX86GccRef.readReg8]

theorem writeReg8_commutes (gpr : VendorX86GccRef.Gpr → BitVec 64)
    (r8 : VendorX86GccRef.Reg8) (v : BitVec 8) :
    ByteX86Gcc.writeSubReg8 (fun r => gpr (unmapReg r)) (mapReg8 r8) v =
      (fun r => VendorX86GccRef.writeReg8 gpr r8 v (unmapReg r)) := by
  cases r8 with
  | lo8 g =>
    dsimp only [mapReg8, ByteX86Gcc.writeSubReg8, VendorX86GccRef.writeReg8]
    rw [unmapReg_mapGpr, gprUpd_commutes]
  | hi8 g =>
    dsimp only [mapReg8, ByteX86Gcc.writeSubReg8, VendorX86GccRef.writeReg8]
    rw [unmapReg_mapGpr, gprUpd_commutes]

theorem readGprSz_eq (sz : VendorX86GccRef.OpSize)
    (gpr : VendorX86GccRef.Gpr → BitVec 64) (g : VendorX86GccRef.Gpr) :
    ByteX86Gcc.readRegSz (mapOpSize sz) (fun r => gpr (unmapReg r)) (mapGpr g) =
      VendorX86GccRef.readGprSz sz gpr g := by
  cases sz <;> simp [mapOpSize, ByteX86Gcc.readRegSz, VendorX86GccRef.readGprSz]

theorem writeGprSz_commutes' (sz : VendorX86GccRef.OpSize)
    (gpr : VendorX86GccRef.Gpr → BitVec 64) (g : VendorX86GccRef.Gpr) (v : BitVec 64) :
    ByteX86Gcc.writeRegSz (mapOpSize sz) (fun r => gpr (unmapReg r)) (mapGpr g) v =
      (fun r => VendorX86GccRef.writeGprSz sz gpr g v (unmapReg r)) := by
  cases sz with
  | s64 => dsimp only [mapOpSize, ByteX86Gcc.writeRegSz, VendorX86GccRef.writeGprSz]; rw [gprUpd_commutes]
  | s32 => dsimp only [mapOpSize, ByteX86Gcc.writeRegSz, VendorX86GccRef.writeGprSz]; rw [gprUpd_commutes]
  | s16 => dsimp only [mapOpSize, ByteX86Gcc.writeRegSz, VendorX86GccRef.writeGprSz]; rw [unmapReg_mapGpr, gprUpd_commutes]

theorem evalAddr_eq (s : VendorX86GccRef.MachineState) (nextRip : BitVec 64)
    (a : VendorX86GccRef.MemAddr) :
    ByteX86Gcc.evalByteAddr (mapState s) nextRip (mapAddr a) =
      VendorX86GccRef.evalAddr s nextRip a := by
  rcases a with ⟨base, idx, disp, ripRel⟩
  unfold ByteX86Gcc.evalByteAddr VendorX86GccRef.evalAddr mapAddr mapState
  cases base with
  | none =>
    cases idx with
    | none => simp
    | some p => cases p; simp
  | some g =>
    cases idx with
    | none => simp
    | some p => cases p; simp

theorem readRm8_eq (s : VendorX86GccRef.MachineState) (nextRip : BitVec 64)
    (rm8 : VendorX86GccRef.Rm8Op) :
    ByteX86Gcc.readByteRm8 (mapState s) nextRip (mapRm8 rm8) =
      VendorX86GccRef.readRm8 s nextRip rm8 := by
  cases rm8 with
  | reg8 r => exact readReg8_eq s.gpr r
  | mem8 a => dsimp only [mapRm8, ByteX86Gcc.readByteRm8, VendorX86GccRef.readRm8]; rw [evalAddr_eq]; rfl

theorem writeRm8_commutes (s : VendorX86GccRef.MachineState) (nextRip : BitVec 64)
    (dst : VendorX86GccRef.Rm8Op) (v : BitVec 8) :
    ByteX86Gcc.writeByteRm8 (mapState s) nextRip (mapRm8 dst) v =
      mapState (VendorX86GccRef.writeRm8 s nextRip dst v) := by
  cases dst with
  | reg8 r =>
    dsimp only [mapRm8, ByteX86Gcc.writeByteRm8, VendorX86GccRef.writeRm8, mapState]
    rw [writeReg8_commutes]
  | mem8 a =>
    dsimp only [mapRm8, ByteX86Gcc.writeByteRm8, VendorX86GccRef.writeRm8]
    rw [evalAddr_eq]; rfl

theorem readRm_eq (sz : VendorX86GccRef.OpSize) (s : VendorX86GccRef.MachineState)
    (nextRip : BitVec 64) (rm : VendorX86GccRef.RmOp) :
    ByteX86Gcc.readByteRm (mapOpSize sz) (mapState s) nextRip (mapRm rm) =
      VendorX86GccRef.readRm sz s nextRip rm := by
  cases rm with
  | reg g => exact readGprSz_eq sz s.gpr g
  | mem a =>
    dsimp only [mapRm, ByteX86Gcc.readByteRm, VendorX86GccRef.readRm]
    rw [evalAddr_eq]
    cases sz <;> rfl

theorem writeRm_commutes (sz : VendorX86GccRef.OpSize) (s : VendorX86GccRef.MachineState)
    (nextRip : BitVec 64) (dst : VendorX86GccRef.RmOp) (v : BitVec 64) :
    ByteX86Gcc.writeByteRm (mapOpSize sz) (mapState s) nextRip (mapRm dst) v =
      mapState (VendorX86GccRef.writeRm sz s nextRip dst v) := by
  cases dst with
  | reg g =>
    dsimp only [mapRm, ByteX86Gcc.writeByteRm, VendorX86GccRef.writeRm, mapState]
    rw [writeGprSz_commutes']
  | mem a =>
    dsimp only [mapRm, ByteX86Gcc.writeByteRm, VendorX86GccRef.writeRm]
    rw [evalAddr_eq]
    cases sz <;> rfl

theorem evalCond_eq (cc : VendorX86GccRef.Cond) (f : VendorX86GccRef.RFlags) :
    ByteX86Gcc.evalCond (mapCond cc) (mapFlags f) = VendorX86GccRef.evalCond cc f := by
  cases cc <;> rfl

theorem evalAluN_eq {w : Nat} (hw : 0 < w) (op : VendorX86GccRef.AluOp)
    (a b : BitVec w) (oldF undefF : VendorX86GccRef.RFlags) :
    ByteX86Gcc.evalAluN hw (mapAluOp op) a b (mapFlags oldF) (mapFlags undefF) =
      let (r, fl) := VendorX86GccRef.evalAluN hw op a b oldF undefF
      (r, mapFlags fl) := by
  cases op <;> rfl

theorem evalAluSz_eq (sz : VendorX86GccRef.OpSize) (op : VendorX86GccRef.AluOp)
    (a b : BitVec 64) (oldF undefF : VendorX86GccRef.RFlags) :
    ByteX86Gcc.evalAluSz (mapOpSize sz) (mapAluOp op) a b (mapFlags oldF) (mapFlags undefF) =
      let (r, fl) := VendorX86GccRef.evalAluSz sz op a b oldF undefF
      (r, mapFlags fl) := by
  cases sz <;> cases op <;> rfl

theorem evalUnarySz_eq (sz : VendorX86GccRef.OpSize) (op : VendorX86GccRef.UnaryOp)
    (v : BitVec 64) (oldF : VendorX86GccRef.RFlags) :
    ByteX86Gcc.evalUnarySz (mapOpSize sz) (mapUnaryOp op) v (mapFlags oldF) =
      let (r, fl) := VendorX86GccRef.evalUnarySz sz op v oldF
      (r, mapFlags fl) := by
  cases sz <;> cases op <;> rfl

theorem parity8_eq (b : BitVec 8) :
    ByteX86Gcc.parity8 b = VendorX86GccRef.parity8 b := rfl

theorem evalShiftSz_eq (sz : VendorX86GccRef.OpSize) (op : VendorX86GccRef.ShiftOp)
    (v : BitVec 64) (cnt : BitVec 8) (oldF undefF : VendorX86GccRef.RFlags) :
    ByteX86Gcc.evalShiftSz (mapOpSize sz) (mapShiftOp op) v cnt (mapFlags oldF) (mapFlags undefF) =
      let (r, fl) := VendorX86GccRef.evalShiftSz sz op v cnt oldF undefF
      (r, mapFlags fl) := by
  cases sz with
  | s64 =>
    cases op <;> (by_cases hc : (cnt.toNat &&& 63) == 0 <;>
      simp [ByteX86Gcc.evalShiftSz, VendorX86GccRef.evalShiftSz, mapOpSize, mapShiftOp, hc, mapFlags, parity8_eq])
  | s32 =>
    cases op <;> (by_cases hc : (cnt.toNat &&& 31) == 0 <;>
      simp [ByteX86Gcc.evalShiftSz, VendorX86GccRef.evalShiftSz, mapOpSize, mapShiftOp, hc, mapFlags, parity8_eq])
  | s16 =>
    cases op <;> (by_cases hc : (cnt.toNat &&& 31) == 0 <;>
      (simp [ByteX86Gcc.evalShiftSz, VendorX86GccRef.evalShiftSz, mapOpSize, mapShiftOp, hc, mapFlags];
       try rfl))

theorem evalImulSz_eq (sz : VendorX86GccRef.OpSize) (a b : BitVec 64)
    (undefF : VendorX86GccRef.RFlags) :
    ByteX86Gcc.evalImulSz (mapOpSize sz) a b (mapFlags undefF) =
      let (r, fl) := VendorX86GccRef.evalImulSz sz a b undefF
      (r, mapFlags fl) := by
  cases sz <;> rfl

theorem writeXmmResult_eq (isVex : Bool) (ymms : VendorX86GccRef.YmmIdx → BitVec 256)
    (idx : VendorX86GccRef.YmmIdx) (v128 : BitVec 128) :
    ByteX86Gcc.writeXmm128 isVex ymms idx v128 =
      VendorX86GccRef.writeXmmResult isVex ymms idx v128 := by
  cases isVex <;> rfl

theorem readXmm128_eq (s : VendorX86GccRef.MachineState) (nextRip : BitVec 64)
    (xrm : VendorX86GccRef.XmmRmOp) :
    ByteX86Gcc.readByteXmm128 (mapState s) nextRip (mapXmmRm xrm) =
      VendorX86GccRef.readXmm128 s nextRip xrm := by
  cases xrm with
  | reg y => rfl
  | mem a => dsimp only [mapXmmRm, ByteX86Gcc.readByteXmm128, VendorX86GccRef.readXmm128]; rw [evalAddr_eq]; rfl

theorem readYmm256_eq (s : VendorX86GccRef.MachineState) (nextRip : BitVec 64)
    (xrm : VendorX86GccRef.XmmRmOp) :
    ByteX86Gcc.readByteYmm256 (mapState s) nextRip (mapXmmRm xrm) =
      VendorX86GccRef.readYmm256 s nextRip xrm := by
  cases xrm with
  | reg y => rfl
  | mem a => dsimp only [mapXmmRm, ByteX86Gcc.readByteYmm256, VendorX86GccRef.readYmm256]; rw [evalAddr_eq]; rfl

theorem readModeRhs_eq (m : VendorX86GccRef.SimdMode) (s : VendorX86GccRef.MachineState)
    (nextRip : BitVec 64) (xrm : VendorX86GccRef.XmmRmOp) :
    ByteX86Gcc.readByteModeRhs (mapSimdMode m) (mapState s) nextRip (mapXmmRm xrm) =
      VendorX86GccRef.readModeRhs m s nextRip xrm := by
  cases m with
  | legacy128 =>
    dsimp only [mapSimdMode, ByteX86Gcc.readByteModeRhs, VendorX86GccRef.readModeRhs]
    rw [readXmm128_eq]
  | vex128 =>
    dsimp only [mapSimdMode, ByteX86Gcc.readByteModeRhs, VendorX86GccRef.readModeRhs]
    rw [readXmm128_eq]
  | vex256 =>
    dsimp only [mapSimdMode, ByteX86Gcc.readByteModeRhs, VendorX86GccRef.readModeRhs]
    exact readYmm256_eq s nextRip xrm

theorem apply128Or256_eq (m : VendorX86GccRef.SimdMode)
    (ymms : VendorX86GccRef.YmmIdx → BitVec 256) (dst : VendorX86GccRef.YmmIdx)
    (f128 : BitVec 128 → BitVec 128 → BitVec 128) (a256 b256 : BitVec 256) :
    ByteX86Gcc.applyByte128Or256 (mapSimdMode m) ymms dst f128 a256 b256 =
      VendorX86GccRef.apply128Or256 m ymms dst f128 a256 b256 := by
  cases m <;> rfl

theorem unpack128_eq (op : VendorX86GccRef.VecUnpackOp) :
    ByteX86Gcc.unpack128 (mapVecUnpackOp op) = VendorX86GccRef.unpack128 op := by
  cases op <;> rfl

theorem extend128_eq (op : VendorX86GccRef.VecExtendOp) (s : VendorX86GccRef.MachineState)
    (nextRip : BitVec 64) (src : VendorX86GccRef.XmmRmOp) :
    ByteX86Gcc.extendByte128 (mapVecExtendOp op) (mapState s) nextRip (mapXmmRm src) =
      VendorX86GccRef.extend128 op s nextRip src := by
  cases op <;> cases src <;>
    (dsimp only [mapVecExtendOp, mapXmmRm, ByteX86Gcc.extendByte128, VendorX86GccRef.extend128];
     (try rw [evalAddr_eq]); rfl)

theorem extend256_eq (op : VendorX86GccRef.VecExtendOp) (s : VendorX86GccRef.MachineState)
    (nextRip : BitVec 64) (src : VendorX86GccRef.XmmRmOp) :
    ByteX86Gcc.extendByte256 (mapVecExtendOp op) (mapState s) nextRip (mapXmmRm src) =
      VendorX86GccRef.extend256 op s nextRip src := by
  unfold ByteX86Gcc.extendByte256 VendorX86GccRef.extend256
  rw [readXmm128_eq]
  cases op <;> rfl

theorem isCmpOrTest_eq (op : VendorX86GccRef.AluOp) :
    (mapAluOp op == ByteX86Gcc.AluOp.cmp || mapAluOp op == ByteX86Gcc.AluOp.test) =
      (op == VendorX86GccRef.AluOp.cmp || op == VendorX86GccRef.AluOp.test) := by
  cases op <;> rfl

theorem execInstr_commutes (ins : VendorX86GccRef.Instr) (nextRip : BitVec 64)
    (oracle : VendorX86GccRef.UndefOracle) (s : VendorX86GccRef.MachineState) :
    ByteX86Gcc.execByteInstr (mapInstr ins) nextRip (mapOracle oracle) (mapState s) =
      mapState (VendorX86GccRef.execInstr ins nextRip oracle s) := by
  have hsRip : ({ mapState s with rip := nextRip } : ByteX86Gcc.X64State) =
      mapState { s with rip := nextRip } := rfl
  have hregs : (mapState s).regs = (fun r => s.gpr (unmapReg r)) := rfl
  have hflags : (mapState s).flags = mapFlags s.flags := rfl
  cases ins with
  | nop | endbr64 | vzeroupper | ud2 | cli | ret64 | jmpRel _ => rfl
  | jccRel cc rel =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [hflags, evalCond_eq]; cases VendorX86GccRef.evalCond cc s.flags <;> rfl
  | mov8Load dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readRm8_eq, hregs, writeReg8_commutes]; try rfl
  | mov8Store dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [hsRip, hregs, readReg8_eq, writeRm8_commutes]
  | mov8Imm dst imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [hsRip, writeRm8_commutes]
  | alu8RmReg op dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [hsRip, readRm8_eq, hregs, readReg8_eq, hflags, evalAluN_eq, isCmpOrTest_eq]
    cases VendorX86GccRef.evalAluN (by decide) op (VendorX86GccRef.readRm8 s nextRip dst) (VendorX86GccRef.readReg8 s.gpr src) s.flags oracle.flags with
    | mk res fl =>
      dsimp only
      cases (op == .cmp || op == .test) <;> simp only [ite_true, Bool.false_eq_true, ite_false]
      · rw [writeRm8_commutes]; try rfl
      · rfl
  | alu8RegRm op dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [hregs, readReg8_eq, readRm8_eq, hflags, evalAluN_eq, isCmpOrTest_eq]
    cases VendorX86GccRef.evalAluN (by decide) op (VendorX86GccRef.readReg8 s.gpr dst) (VendorX86GccRef.readRm8 s nextRip src) s.flags oracle.flags with
    | mk res fl =>
      dsimp only
      cases (op == .cmp || op == .test) <;> simp only [ite_true, Bool.false_eq_true, ite_false]
      · rw [writeReg8_commutes]; try rfl
      · rfl
  | alu8Imm op dst imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [hsRip, readRm8_eq, hflags, evalAluN_eq, isCmpOrTest_eq]
    cases VendorX86GccRef.evalAluN (by decide) op (VendorX86GccRef.readRm8 s nextRip dst) imm s.flags oracle.flags with
    | mk res fl =>
      dsimp only
      cases (op == .cmp || op == .test) <;> simp only [ite_true, Bool.false_eq_true, ite_false]
      · rw [writeRm8_commutes]; try rfl
      · rfl
  | setcc8 cc dst =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [hsRip, hflags, evalCond_eq, writeRm8_commutes]
  | movzx8 sz dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readRm8_eq, hregs, writeGprSz_commutes']; try rfl
  | movzx16 sz dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    have hr := readRm_eq .s16 s nextRip src; dsimp only [mapOpSize] at hr
    rw [hr, hregs, writeGprSz_commutes']; try rfl
  | movsx8 sz dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readRm8_eq, hregs, writeGprSz_commutes']; try rfl
  | movsx16 sz dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    have hr := readRm_eq .s16 s nextRip src; dsimp only [mapOpSize] at hr
    rw [hr, hregs, writeGprSz_commutes']; try rfl
  | movsxd dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    have hr := readRm_eq .s32 s nextRip src; dsimp only [mapOpSize] at hr
    rw [hr, hregs, gprUpd_commutes]; try rfl
  | movLoad sz dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readRm_eq, hregs, writeGprSz_commutes']; try rfl
  | movStore sz dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [hsRip, hregs, readGprSz_eq, writeRm_commutes]
  | movImm sz dst imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [hregs, writeGprSz_commutes']; try rfl
  | movRmImm32 sz dst imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [hsRip, writeRm_commutes]
  | lea sz dst addr =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [evalAddr_eq, hregs, writeGprSz_commutes']; try rfl
  | xchg sz r1 rm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [hsRip, hregs, readGprSz_eq, readRm_eq, writeRm_commutes]
    dsimp only [mapState]; rw [writeGprSz_commutes']; try rfl
  | aluRmReg sz op dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [hsRip, readRm_eq, hregs, readGprSz_eq, hflags, evalAluSz_eq, isCmpOrTest_eq]
    cases VendorX86GccRef.evalAluSz sz op (VendorX86GccRef.readRm sz s nextRip dst) (VendorX86GccRef.readGprSz sz s.gpr src) s.flags oracle.flags with
    | mk res fl =>
      dsimp only
      cases (op == .cmp || op == .test) <;> simp only [ite_true, Bool.false_eq_true, ite_false]
      · rw [writeRm_commutes]; try rfl
      · rfl
  | aluRegRm sz op dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [hregs, readGprSz_eq, readRm_eq, hflags, evalAluSz_eq, isCmpOrTest_eq]
    cases VendorX86GccRef.evalAluSz sz op (VendorX86GccRef.readGprSz sz s.gpr dst) (VendorX86GccRef.readRm sz s nextRip src) s.flags oracle.flags with
    | mk res fl =>
      dsimp only
      cases (op == .cmp || op == .test) <;> simp only [ite_true, Bool.false_eq_true, ite_false]
      · rw [writeGprSz_commutes']; try rfl
      · rfl
  | aluImm sz op dst imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [hsRip, readRm_eq, hflags, evalAluSz_eq, isCmpOrTest_eq]
    cases VendorX86GccRef.evalAluSz sz op (VendorX86GccRef.readRm sz s nextRip dst) imm s.flags oracle.flags with
    | mk res fl =>
      dsimp only
      cases (op == .cmp || op == .test) <;> simp only [ite_true, Bool.false_eq_true, ite_false]
      · rw [writeRm_commutes]; try rfl
      · rfl
  | unaryRm sz op dst =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [hsRip, readRm_eq, hflags, evalUnarySz_eq]
    cases VendorX86GccRef.evalUnarySz sz op (VendorX86GccRef.readRm sz s nextRip dst) s.flags with
    | mk res fl => dsimp only; rw [writeRm_commutes]; try rfl
  | shiftImm sz op dst cnt =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [hsRip, readRm_eq, hflags, evalShiftSz_eq]
    cases VendorX86GccRef.evalShiftSz sz op (VendorX86GccRef.readRm sz s nextRip dst) cnt s.flags oracle.flags with
    | mk res fl => dsimp only; rw [writeRm_commutes]; try rfl
  | imul2 sz dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [hregs, readGprSz_eq, readRm_eq, evalImulSz_eq]
    cases VendorX86GccRef.evalImulSz sz (VendorX86GccRef.readGprSz sz s.gpr dst) (VendorX86GccRef.readRm sz s nextRip src) oracle.flags with
    | mk res fl => dsimp only; rw [writeGprSz_commutes']; try rfl
  | imul3 sz dst src imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [readRm_eq, evalImulSz_eq]
    cases VendorX86GccRef.evalImulSz sz (VendorX86GccRef.readRm sz s nextRip src) imm oracle.flags with
    | mk res fl => dsimp only; rw [hregs, writeGprSz_commutes']; try rfl
  | bsf sz dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapOracle]
    rw [readRm_eq, hregs]
    split <;> (rw [writeGprSz_commutes']; try rfl)
  | push64 src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapState]
    have hrsp : ByteX86Gcc.Reg.rsp = mapGpr .rsp := rfl
    rw [unmapReg_mapGpr, hrsp, gprUpd_commutes]; try rfl
  | pop64 dst =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapState]
    have hrsp : ByteX86Gcc.Reg.rsp = mapGpr .rsp := rfl
    rw [hrsp, gprUpd_commutes, gprUpd_commutes]; try rfl
  | leave64 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapState]
    have hrsp : ByteX86Gcc.Reg.rsp = mapGpr .rsp := rfl
    have hrbp : ByteX86Gcc.Reg.rbp = mapGpr .rbp := rfl
    rw [hrsp, hrbp, gprUpd_commutes, gprUpd_commutes]; try rfl
  | simdMovLoad m dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    cases m
    · dsimp only [mapSimdMode]; rw [readXmm128_eq]; dsimp only [mapState]; rw [writeXmmResult_eq]
    · dsimp only [mapSimdMode]; rw [readXmm128_eq]; dsimp only [mapState]; rw [writeXmmResult_eq]
    · dsimp only [mapSimdMode]; rw [readYmm256_eq]; try rfl
  | simdMovStore m dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    cases dst with
    | reg y =>
      cases m
      · dsimp only [mapXmmRm, mapSimdMode, mapState]; rw [writeXmmResult_eq]
      · dsimp only [mapXmmRm, mapSimdMode, mapState]; rw [writeXmmResult_eq]
      · rfl
    | mem a =>
      dsimp only [mapXmmRm]; rw [evalAddr_eq]; cases m <;> rfl
  | simdMovqLoad isVex dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    cases src
    · dsimp only [mapXmmRm, mapState]; rw [writeXmmResult_eq]; try rfl
    · dsimp only [mapXmmRm]; rw [evalAddr_eq]; dsimp only [mapState]; rw [writeXmmResult_eq]; try rfl
  | simdMovqStore isVex dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    cases dst
    · dsimp only [mapXmmRm, mapState]; rw [writeXmmResult_eq]; try rfl
    · dsimp only [mapXmmRm]; rw [evalAddr_eq]; try rfl
  | simdMovGprToX isVex is64 dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    have hsz : (if is64 then ByteX86Gcc.OpSize.s64 else .s32) =
        mapOpSize (if is64 then VendorX86GccRef.OpSize.s64 else .s32) := by cases is64 <;> rfl
    rw [hsz, readRm_eq]; dsimp only [mapState]; rw [writeXmmResult_eq]
  | simdMovXToGpr isVex is64 dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    have hsz : (if is64 then ByteX86Gcc.OpSize.s64 else .s32) =
        mapOpSize (if is64 then VendorX86GccRef.OpSize.s64 else .s32) := by cases is64 <;> rfl
    rw [hsRip, hsz, writeRm_commutes]; try rfl
  | simdBitwise m op d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; cases op <;> (dsimp only [mapAluOp, mapState]; rw [apply128Or256_eq]; try rfl)
  | simdAdd m ew d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; cases ew <;> (dsimp only [mapVecElem, mapState]; rw [apply128Or256_eq]; try rfl)
  | simdSub m ew d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; cases ew <;> (dsimp only [mapVecElem, mapState]; rw [apply128Or256_eq]; try rfl)
  | simdCmpeq m ew d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; cases ew <;> (dsimp only [mapVecElem, mapState]; rw [apply128Or256_eq]; try rfl)
  | simdCmpgt m ew d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; cases ew <;> (dsimp only [mapVecElem, mapState]; rw [apply128Or256_eq]; try rfl)
  | simdUnpack m op d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq, unpack128_eq]; dsimp only [mapState]; rw [apply128Or256_eq]
  | simdExtend m op dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    cases m
    · dsimp only [mapSimdMode]; rw [extend128_eq]; dsimp only [mapState]; rw [writeXmmResult_eq]
    · dsimp only [mapSimdMode]; rw [extend128_eq]; dsimp only [mapState]; rw [writeXmmResult_eq]
    · dsimp only [mapSimdMode]; rw [extend256_eq]; try rfl
  | simdBroadcastB m dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    cases src <;> cases m <;> dsimp only [mapXmmRm, mapSimdMode] <;>
      ((try rw [evalAddr_eq]); dsimp only [mapState]; (try rw [writeXmmResult_eq]); try rfl)
  | simdBroadcastQ m dst src =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    cases src <;> cases m <;> dsimp only [mapXmmRm, mapSimdMode] <;>
      ((try rw [evalAddr_eq]); dsimp only [mapState]; (try rw [writeXmmResult_eq]); try rfl)
  | simdPmullw m d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; dsimp only [mapState]; rw [apply128Or256_eq]; try rfl
  | simdPmulhuw m d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; dsimp only [mapState]; rw [apply128Or256_eq]; try rfl
  | simdPmulld m d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; dsimp only [mapState]; rw [apply128Or256_eq]; try rfl
  | simdPmaddwd m d s1 s2 =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; dsimp only [mapState]; rw [apply128Or256_eq]; try rfl
  | simdPsrldq m dst src imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapState]
    rw [apply128Or256_eq]; try rfl
  | simdPsrlqImm m dst src imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr, mapState]
    rw [apply128Or256_eq]; try rfl
  | simdPshufd m dst src imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; dsimp only [mapState]; rw [apply128Or256_eq]; try rfl
  | simdPshuflw m dst src imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readModeRhs_eq]; dsimp only [mapState]; rw [apply128Or256_eq]; try rfl
  | simdExtract128 dst src imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    cases dst
    · dsimp only [mapXmmRm, mapState]; rw [writeXmmResult_eq]
    · dsimp only [mapXmmRm]; rw [evalAddr_eq]; try rfl
  | simdPerm2i128 d s1 s2 imm =>
    dsimp only [mapInstr, ByteX86Gcc.execByteInstr, VendorX86GccRef.execInstr]
    rw [readYmm256_eq]; try rfl

/-- **Oracle-Level Single-Step Commutation (`stepWithOracle_commutes`):**
    `ByteX86Gcc.stepX64` commutes identically with `VendorX86GccRef.stepWithOracle`
    over every `CodeMap`, `UndefOracle`, and `MachineState`. -/
theorem stepWithOracle_commutes (code : ByteX86Gcc.CodeMap)
    (oracle : VendorX86GccRef.UndefOracle) (s : VendorX86GccRef.MachineState) :
    ByteX86Gcc.stepX64 code (mapOracle oracle) (mapState s) =
      mapState (VendorX86GccRef.stepWithOracle code oracle s) := by
  unfold ByteX86Gcc.stepX64 VendorX86GccRef.stepWithOracle
  have hhf : ((mapState s).halted || (mapState s).fault) = (s.halted || s.fault.isSome) := rfl
  rw [hhf]
  split
  · rfl
  · have hfw : ByteX86Gcc.fetchWindow16 code (mapState s).rip =
        VendorX86GccRef.fetchWindow16 code s.rip := rfl
    have hlen : (VendorX86GccRef.fetchWindow16 code s.rip).length = 16 := rfl
    rw [hfw, decodeRef_commutes_of_len16 _ hlen]
    cases VendorX86GccRef.decodeRef (VendorX86GccRef.fetchWindow16 code s.rip) with
    | fault fk => rfl
    | ok ins len =>
      dsimp only [mapOutcome]
      exact execInstr_commutes ins (s.rip + BitVec.ofNat 64 len) oracle s

/-- **Universal Single-Step Pass-2 Forward Simulation (`VendorX86GccRef.Step ⊆ ByteX86Gcc.Step`).** -/
theorem vendorX86GccRef_step_sub_byteX86Gcc_step (code : ByteX86Gcc.CodeMap)
    {s s' : VendorX86GccRef.MachineState}
    (hstep : VendorX86GccRef.Step code s s') :
    ByteX86Gcc.Step code (mapState s) (mapState s') := by
  rcases hstep with ⟨oracle, rfl⟩
  exact ⟨mapOracle oracle, stepWithOracle_commutes code oracle s⟩

/-- **Universal Multi-Step Pass-2 Trace Inclusion (`VendorX86GccRef.StepsN ⊆ ByteX86Gcc.StepsN`).** -/
theorem vendorX86GccRef_stepsN_sub_byteX86Gcc_stepsN (code : ByteX86Gcc.CodeMap)
    {n : Nat} {s s' : VendorX86GccRef.MachineState}
    (hsteps : VendorX86GccRef.StepsN code n s s') :
    ByteX86Gcc.StepsN code n (mapState s) (mapState s') := by
  induction hsteps with
  | zero s0 => exact .zero (mapState s0)
  | succ hs hrest ih =>
    exact .succ (vendorX86GccRef_step_sub_byteX86Gcc_step code hs) ih

/-! ## Section 4: Reverse Soundness Counterexamples -/

/-- **Counterexample 1 (`misdecoded_rex_subreg8_refinement_counterexample`):**
    In `gcc 15.2.0 -O3 -mavx2` (`c_xor_stream` offset `0x506`), GCC emits `88 df`
    (`mov bh, bl` without a REX prefix) to splat `key` into 16 bits. A buggy byte
    decoder that treats `rm = 7` without REX as `DIL` (`mov dil, bl`) produces a
    machine state that diverges from `mapState (stepWithOracle ...)`. -/
theorem misdecoded_rex_subreg8_refinement_counterexample :
    let code := ByteX86Gcc.codeFromBytes [0x88#8, 0xDF#8]
    let sRef : VendorX86GccRef.MachineState :=
      { rip := 0#64, gpr := fun g => if g == .rbx then 0x005A#64 else 0#64 }
    let sRef' := VendorX86GccRef.stepWithOracle code {} sRef
    let sBuggy := ByteX86Gcc.execByteInstr (.mov8Store (.reg8 (.lo8 .rdi)) (.lo8 .rbx)) 2#64 {} (mapState sRef)
    (mapState sRef').regs .rbx = 0x5A5A#64 ∧
    sBuggy.regs .rbx = 0x005A#64 ∧
    sBuggy.regs .rdi = 0x005A#64 ∧
    sBuggy ≠ mapState sRef' := by
  have h1 : (mapState (VendorX86GccRef.stepWithOracle (ByteX86Gcc.codeFromBytes [0x88#8, 0xDF#8]) {}
      { rip := 0#64, gpr := fun g => if g == .rbx then 0x005A#64 else 0#64 })).regs .rbx = 0x5A5A#64 := rfl
  have h2 : (ByteX86Gcc.execByteInstr (.mov8Store (.reg8 (.lo8 .rdi)) (.lo8 .rbx)) 2#64 {}
      (mapState { rip := 0#64, gpr := fun g => if g == .rbx then 0x005A#64 else 0#64 })).regs .rbx = 0x005A#64 := rfl
  refine ⟨h1, h2, rfl, ?_⟩
  intro heq
  have hrbx := congrArg (fun st => st.regs .rbx) heq
  rw [h2, h1] at hrbx
  nomatch hrbx

/-- **Counterexample 2 (`collapsed_legacy_sse_vex_refinement_counterexample`):**
    In `gcc 15.2.0 -O2` (`c_dot_u8_u16`, `c_xor_stream`, `c_bug4_asm_clobber_abi`),
    GCC emits Legacy Non-VEX SSE2 `66 0f ef c0` (`pxor xmm0, xmm0`). Collapsing
    Legacy SSE2 to VEX `L = 0` semantics (`SimdMode.vex128`, zeroing `YMM0[255:128]`)
    falsifies Pass-2 simulation whenever `YMM0[255:128] ≠ 0`. -/
theorem collapsed_legacy_sse_vex_refinement_counterexample :
    let code := ByteX86Gcc.codeFromBytes [0x66#8, 0x0F#8, 0xEF#8, 0xC0#8]
    let y0 : VendorX86GccRef.YmmIdx := ⟨0, by decide⟩
    let dirtyYmm0 : BitVec 256 := (1#128) ++ (0xAA#128)
    let sRef : VendorX86GccRef.MachineState :=
      { rip := 0#64, ymm := fun idx => if idx = y0 then dirtyYmm0 else 0#256 }
    let sRef' := VendorX86GccRef.stepWithOracle code {} sRef
    let sCollapsed := ByteX86Gcc.execByteInstr (.simdBitwise .vex128 .xor y0 y0 (.reg y0)) 4#64 {} (mapState sRef)
    BitVec.extractLsb' 128 128 ((mapState sRef').ymms y0) = 1#128 ∧
    BitVec.extractLsb' 128 128 (sCollapsed.ymms y0) = 0#128 ∧
    sCollapsed ≠ mapState sRef' := by
  have h1 : BitVec.extractLsb' 128 128
      ((mapState (VendorX86GccRef.stepWithOracle (ByteX86Gcc.codeFromBytes [0x66#8, 0x0F#8, 0xEF#8, 0xC0#8]) {}
        { rip := 0#64, ymm := fun idx => if idx = ⟨0, by decide⟩ then (1#128) ++ (0xAA#128) else 0#256 })).ymms ⟨0, by decide⟩) = 1#128 := rfl
  have h2 : BitVec.extractLsb' 128 128
      ((ByteX86Gcc.execByteInstr (.simdBitwise .vex128 .xor ⟨0, by decide⟩ ⟨0, by decide⟩ (.reg ⟨0, by decide⟩)) 4#64 {}
        (mapState { rip := 0#64, ymm := fun idx => if idx = ⟨0, by decide⟩ then (1#128) ++ (0xAA#128) else 0#256 })).ymms ⟨0, by decide⟩) = 0#128 := rfl
  refine ⟨h1, h2, ?_⟩
  intro heq
  have hy := congrArg (fun st => BitVec.extractLsb' 128 128 (st.ymms ⟨0, by decide⟩)) heq
  rw [h2, h1] at hy
  nomatch hy

end ByteX86GccPass2
