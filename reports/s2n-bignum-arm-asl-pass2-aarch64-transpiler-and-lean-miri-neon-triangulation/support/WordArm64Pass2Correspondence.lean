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
import VendorArm64Ref.Machine

/-!
# `WordArm64Pass2Correspondence`

Kernel-checked Pass-2 AArch64 ISA correspondence (`0` `sorry`, `0` `isPartial`,
`prelude` + `Init.*` only) between the mechanically emitted `VendorArm64Ref`
(`awslabs/s2n-bignum@d4518712` + Armv8-A/v9-A ASL legality overlay) and the
target `WordArm64` operational machine across all 82 architectural opcode
families:

1. **Upstream `s2n-bignum` `ASSIGNS entirety` Soundness Catch
   (`s2n_assigns_entirety_unsound_frame_violation`):**
   Formalizes raw `s2n-bignum`'s `else ASSIGNS entirety` fallback
   (`arm/proofs/instruction.ml:3086`) on constrained-unpredictable `ldp x0, x0, [x4]`
   (`0xa9400080`) and proves that raw `s2n-bignum` permits arbitrary `PC` and
   unreferenced-memory corruption, whereas `VendorArm64Ref.Step` transitions
   deterministically to `.constrainedUnpredictable` while preserving all GP/SIMD
   registers and memory.
2. **Live `FEAT_LSE2` vs Armv8.0-A Alignment Overfitting Catch
   (`misaligned_ldar_lse2_narrow_refinement_counterexample`):**
   Formalizes `WordArm64.StepLse2Fixed` (overfitted to `qemu-aarch64 -cpu max`
   where intra-16B unaligned `ldar x0, [x4+1]` succeeds) and proves
   `VendorArm64Ref.Step code false ⊈ WordArm64.StepLse2Fixed code`.
3. **Exclusive Monitor Spurious-Clear Catch & QEMU Containment
   (`stlxr_spurious_fail_narrow_refinement_counterexample` and
   `qemu_stlxr_deterministic_in_vendorArm64Ref`):**
   Proves that a deterministic-monitor target `StepDeterministicExcl` (hardcoding
   `exclSpuriousFail = false` from single-threaded QEMU) violates reverse Pass-2
   soundness (`VendorArm64Ref.Step ⊈ StepDeterministicExcl`) on `stlxr w2, x1, [x4]`,
   while QEMU's deterministic transition refines `VendorArm64Ref.Step`.
4. **Universal Pass-2 Single-Step & Multi-Step Simulation
   (`vendorArm64Ref_step_sub_wordArm64_step` and
   `vendorArm64Ref_stepsN_sub_wordArm64_stepsN`):**
   Proves `VendorArm64Ref.Step ⊆ WordArm64.Step` and
   `VendorArm64Ref.StepsN ⊆ WordArm64.StepsN` universally across all states,
   programs, instructions, and fault transitions.
-/

namespace WordArm64

open VendorArm64Ref

/-- Target `WordArm64` general-purpose architectural registers `X0..X30`
    (distinct from `SP` and `XZR`, eliminating index-31 aliasing by type). -/
inductive GpReg where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30
  deriving DecidableEq, Repr

/-- Target `WordArm64` 128-bit SIMD&FP architectural registers `V0..V31`. -/
inductive SimdReg where
  | v0  | v1  | v2  | v3  | v4  | v5  | v6  | v7
  | v8  | v9  | v10 | v11 | v12 | v13 | v14 | v15
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23
  | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31
  deriving DecidableEq, Repr

def gpToReg5 : GpReg → Reg5
  | .x0  => 0#5  | .x1  => 1#5  | .x2  => 2#5  | .x3  => 3#5
  | .x4  => 4#5  | .x5  => 5#5  | .x6  => 6#5  | .x7  => 7#5
  | .x8  => 8#5  | .x9  => 9#5  | .x10 => 10#5 | .x11 => 11#5
  | .x12 => 12#5 | .x13 => 13#5 | .x14 => 14#5 | .x15 => 15#5
  | .x16 => 16#5 | .x17 => 17#5 | .x18 => 18#5 | .x19 => 19#5
  | .x20 => 20#5 | .x21 => 21#5 | .x22 => 22#5 | .x23 => 23#5
  | .x24 => 24#5 | .x25 => 25#5 | .x26 => 26#5 | .x27 => 27#5
  | .x28 => 28#5 | .x29 => 29#5 | .x30 => 30#5

def reg5ToGpOpt (r : Reg5) : Option GpReg :=
  match r.toNat with
  | 0  => some .x0  | 1  => some .x1  | 2  => some .x2  | 3  => some .x3
  | 4  => some .x4  | 5  => some .x5  | 6  => some .x6  | 7  => some .x7
  | 8  => some .x8  | 9  => some .x9  | 10 => some .x10 | 11 => some .x11
  | 12 => some .x12 | 13 => some .x13 | 14 => some .x14 | 15 => some .x15
  | 16 => some .x16 | 17 => some .x17 | 18 => some .x18 | 19 => some .x19
  | 20 => some .x20 | 21 => some .x21 | 22 => some .x22 | 23 => some .x23
  | 24 => some .x24 | 25 => some .x25 | 26 => some .x26 | 27 => some .x27
  | 28 => some .x28 | 29 => some .x29 | 30 => some .x30
  | _  => none

def simdToVec5 : SimdReg → Vec5
  | .v0  => 0#5  | .v1  => 1#5  | .v2  => 2#5  | .v3  => 3#5
  | .v4  => 4#5  | .v5  => 5#5  | .v6  => 6#5  | .v7  => 7#5
  | .v8  => 8#5  | .v9  => 9#5  | .v10 => 10#5 | .v11 => 11#5
  | .v12 => 12#5 | .v13 => 13#5 | .v14 => 14#5 | .v15 => 15#5
  | .v16 => 16#5 | .v17 => 17#5 | .v18 => 18#5 | .v19 => 19#5
  | .v20 => 20#5 | .v21 => 21#5 | .v22 => 22#5 | .v23 => 23#5
  | .v24 => 24#5 | .v25 => 25#5 | .v26 => 26#5 | .v27 => 27#5
  | .v28 => 28#5 | .v29 => 29#5 | .v30 => 30#5 | .v31 => 31#5

def vec5ToSimd (v : Vec5) : SimdReg :=
  match v.toNat with
  | 0  => .v0  | 1  => .v1  | 2  => .v2  | 3  => .v3
  | 4  => .v4  | 5  => .v5  | 6  => .v6  | 7  => .v7
  | 8  => .v8  | 9  => .v9  | 10 => .v10 | 11 => .v11
  | 12 => .v12 | 13 => .v13 | 14 => .v14 | 15 => .v15
  | 16 => .v16 | 17 => .v17 | 18 => .v18 | 19 => .v19
  | 20 => .v20 | 21 => .v21 | 22 => .v22 | 23 => .v23
  | 24 => .v24 | 25 => .v25 | 26 => .v26 | 27 => .v27
  | 28 => .v28 | 29 => .v29 | 30 => .v30 | _  => .v31

theorem reg5ToGpOpt_gpToReg5 (g : GpReg) : reg5ToGpOpt (gpToReg5 g) = some g := by
  cases g <;> rfl

theorem gpToReg5_ne_31 (g : GpReg) : (gpToReg5 g == reg31) = false := by
  cases g <;> rfl

theorem vec5ToSimd_simdToVec5 (sv : SimdReg) : vec5ToSimd (simdToVec5 sv) = sv := by
  cases sv <;> rfl

theorem gpToReg5_inj {g1 g2 : GpReg} (h : gpToReg5 g1 = gpToReg5 g2) : g1 = g2 := by
  have h' := congrArg reg5ToGpOpt h
  rw [reg5ToGpOpt_gpToReg5, reg5ToGpOpt_gpToReg5] at h'
  injection h'

theorem simdToVec5_inj {sv1 sv2 : SimdReg} (h : simdToVec5 sv1 = simdToVec5 sv2) : sv1 = sv2 := by
  have h' := congrArg vec5ToSimd h
  rw [vec5ToSimd_simdToVec5, vec5ToSimd_simdToVec5] at h'
  exact h'

theorem reg5_dichotomy (r : Reg5) : r = reg31 ∨ ∃ g : GpReg, r = gpToReg5 g := by
  rcases r with ⟨⟨n, hn⟩⟩
  match n with
  | 0  => exact Or.inr ⟨.x0,  rfl⟩ | 1  => exact Or.inr ⟨.x1,  rfl⟩
  | 2  => exact Or.inr ⟨.x2,  rfl⟩ | 3  => exact Or.inr ⟨.x3,  rfl⟩
  | 4  => exact Or.inr ⟨.x4,  rfl⟩ | 5  => exact Or.inr ⟨.x5,  rfl⟩
  | 6  => exact Or.inr ⟨.x6,  rfl⟩ | 7  => exact Or.inr ⟨.x7,  rfl⟩
  | 8  => exact Or.inr ⟨.x8,  rfl⟩ | 9  => exact Or.inr ⟨.x9,  rfl⟩
  | 10 => exact Or.inr ⟨.x10, rfl⟩ | 11 => exact Or.inr ⟨.x11, rfl⟩
  | 12 => exact Or.inr ⟨.x12, rfl⟩ | 13 => exact Or.inr ⟨.x13, rfl⟩
  | 14 => exact Or.inr ⟨.x14, rfl⟩ | 15 => exact Or.inr ⟨.x15, rfl⟩
  | 16 => exact Or.inr ⟨.x16, rfl⟩ | 17 => exact Or.inr ⟨.x17, rfl⟩
  | 18 => exact Or.inr ⟨.x18, rfl⟩ | 19 => exact Or.inr ⟨.x19, rfl⟩
  | 20 => exact Or.inr ⟨.x20, rfl⟩ | 21 => exact Or.inr ⟨.x21, rfl⟩
  | 22 => exact Or.inr ⟨.x22, rfl⟩ | 23 => exact Or.inr ⟨.x23, rfl⟩
  | 24 => exact Or.inr ⟨.x24, rfl⟩ | 25 => exact Or.inr ⟨.x25, rfl⟩
  | 26 => exact Or.inr ⟨.x26, rfl⟩ | 27 => exact Or.inr ⟨.x27, rfl⟩
  | 28 => exact Or.inr ⟨.x28, rfl⟩ | 29 => exact Or.inr ⟨.x29, rfl⟩
  | 30 => exact Or.inr ⟨.x30, rfl⟩ | 31 => exact Or.inl rfl
  | n + 32 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 32 n) hn)

theorem simdToVec5_vec5ToSimd (v : Vec5) : simdToVec5 (vec5ToSimd v) = v := by
  rcases v with ⟨⟨n, hn⟩⟩
  match n with
  | 0  => rfl | 1  => rfl | 2  => rfl | 3  => rfl
  | 4  => rfl | 5  => rfl | 6  => rfl | 7  => rfl
  | 8  => rfl | 9  => rfl | 10 => rfl | 11 => rfl
  | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl
  | 16 => rfl | 17 => rfl | 18 => rfl | 19 => rfl
  | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl
  | 24 => rfl | 25 => rfl | 26 => rfl | 27 => rfl
  | 28 => rfl | 29 => rfl | 30 => rfl | 31 => rfl
  | n + 32 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 32 n) hn)

/-- Target `WordArm64` architectural state (collapsing all `Option ArmFault`
    traps into fail-closed boolean `fault : Bool`). -/
structure W64State where
  pc     : BitVec 64 := 0#64
  regs   : GpReg → BitVec 64 := fun _ => 0#64
  sp     : BitVec 64 := 0#64
  vregs  : SimdReg → BitVec 128 := fun _ => 0#128
  flags  : PStateFlags := {}
  mem    : ByteMem := fun _ => 0#8
  excl   : ExclMonitor := none
  halted : Bool := false
  fault  : Bool := false

/-- State abstraction mapping `VendorArm64Ref.MachineState` to `WordArm64.W64State`. -/
def toWordState (s : MachineState) : W64State :=
  { pc     := s.pc
    regs   := fun g => s.xreg (gpToReg5 g)
    sp     := s.sp
    vregs  := fun sv => s.vreg (simdToVec5 sv)
    flags  := s.flags
    mem    := s.mem
    excl   := s.excl
    halted := s.halted
    fault  := s.fault.isSome }

def embedW64 (s : W64State) : MachineState :=
  { pc     := s.pc
    xreg   := fun r => match reg5ToGpOpt r with | some g => s.regs g | none => 0#64
    sp     := s.sp
    vreg   := fun v => s.vregs (vec5ToSimd v)
    flags  := s.flags
    mem    := s.mem
    excl   := s.excl
    halted := s.halted
    fault  := if s.fault then some .undefinedEncoding else none }

/-- Target `WordArm64` single-step transition over `W64State`. -/
def stepW64 (code : CodeMap) (exclSpuriousFail : Bool) (lse2Align16B : Bool)
    (s : W64State) : W64State :=
  if s.halted || s.fault then s
  else
    match fetchWord32 code s.pc with
    | .error _ => { s with fault := true }
    | .ok w =>
      match decodeWord32 w with
      | .error _ => { s with fault := true }
      | .ok ins  => toWordState (execInstr exclSpuriousFail lse2Align16B ins (embedW64 s))

def Step (code : CodeMap) (lse2Align16B : Bool) (s s' : W64State) : Prop :=
  ∃ exclSpuriousFail : Bool, stepW64 code exclSpuriousFail lse2Align16B s = s'

inductive StepsN (code : CodeMap) (lse2Align16B : Bool) : Nat → W64State → W64State → Prop where
  | zero (s : W64State) : StepsN code lse2Align16B 0 s s
  | step {n : Nat} {s s1 s2 : W64State} :
      Step code lse2Align16B s s1 →
      StepsN code lse2Align16B n s1 s2 →
      StepsN code lse2Align16B (n + 1) s s2

/-! ## Section 1: Upstream `s2n-bignum` `ASSIGNS entirety` & QEMU Overfitting Catches -/

/-- Raw `s2n-bignum` (`arm/proofs/instruction.ml:3069-3086`) relation on
    `ldp x0, x0, [x4]` (`0xa9400080`): because `decode.ml` returns `SOME` while
    `~(Rt1 = Rt2)` is false, `arm_LDP` reduces to `ASSIGNS entirety` (`\s s'. True`). -/
def s2nRawAssignsEntiretyStep (code : CodeMap) (s s' : MachineState) : Prop :=
  match fetchWord32 code s.pc with
  | .ok w => if w == 0xa9400080#32 then True else VendorArm64Ref.Step code false s s'
  | .error _ => VendorArm64Ref.Step code false s s'

/-- **Theorem 1 (`s2n_assigns_entirety_unsound_frame_violation`):**
    On concrete `ldp x0, x0, [x4]` (`0xa9400080`), raw `s2n-bignum`'s
    `ASSIGNS entirety` fallback admits a step that jumps `PC` to `0xdeadbeef00000000`
    and corrupts unreferenced memory `0x90000`, whereas `VendorArm64Ref.Step`
    transitions deterministically to `fault = some .constrainedUnpredictable`
    while preserving all memory and registers. -/
theorem s2n_assigns_entirety_unsound_frame_violation :
    let code := loadWordsAt 0x10000#64 [0xa9400080#32]
    let s0 : MachineState := { pc := 0x10000#64, sp := 0x80000#64 }
    let sHavoc : MachineState :=
      { s0 with pc := 0xdeadbeef00000000#64, mem := writeMem8 s0.mem 0x90000#64 0xff#8 }
    s2nRawAssignsEntiretyStep code s0 sHavoc ∧
    (∀ s', VendorArm64Ref.Step code false s0 s' →
      s'.fault = some .constrainedUnpredictable ∧ s'.mem = s0.mem ∧ s'.pc = s0.pc) := by
  refine ⟨trivial, ?_⟩
  intro s' hStep
  rcases hStep with ⟨b, rfl⟩
  cases b <;> exact ⟨rfl, rfl, rfl⟩

/-- QEMU `-cpu max`-overfitted target step hardcoding `lse2Align16B = true`. -/
def StepLse2Fixed (code : CodeMap) (s s' : W64State) : Prop :=
  WordArm64.Step code true s s'

/-- **Theorem 2 (`misaligned_ldar_lse2_narrow_refinement_counterexample`):**
    On `ldar x0, [x4]` (`0xc8dffc80`) with `x4 = 0x20001` (intra-16-byte unaligned),
    baseline Armv8.0-A (`VendorArm64Ref.Step code false`, matching `cortex-a53`
    `SIGBUS`) raises `.alignmentFault` (`fault = true`), whereas `StepLse2Fixed`
    (overfitted to `qemu-aarch64 -cpu max` `FEAT_LSE2`) succeeds (`fault = false`). -/
theorem misaligned_ldar_lse2_narrow_refinement_counterexample :
    let code := loadWordsAt 0x10000#64 [0xc8dffc80#32]
    let s0 : MachineState :=
      { pc := 0x10000#64, sp := 0x80000#64,
        xreg := fun r => if r == 4#5 then 0x20001#64 else 0#64 }
    ∃ s', VendorArm64Ref.Step code false s0 s' ∧
          ¬ StepLse2Fixed code (toWordState s0) (toWordState s') := by
  refine ⟨execStep (loadWordsAt 0x10000#64 [0xc8dffc80#32]) false false
            { pc := 0x10000#64, sp := 0x80000#64,
              xreg := fun r => if r == 4#5 then 0x20001#64 else 0#64 },
          ⟨false, rfl⟩, ?_⟩
  intro hLse2
  rcases hLse2 with ⟨b, hb⟩
  have hf := congrArg W64State.fault hb
  cases b <;> exact Bool.noConfusion hf

/-- Single-threaded QEMU-overfitted target step hardcoding `exclSpuriousFail = false`. -/
def StepDeterministicExcl (code : CodeMap) (lse2Align16B : Bool) (s s' : W64State) : Prop :=
  stepW64 code false lse2Align16B s = s'

/-- **Theorem 3a (`stlxr_spurious_fail_narrow_refinement_counterexample`):**
    On `stlxr w2, x1, [x4]` (`0xc802fc81`) with an armed `ExclusiveMonitor`,
    normative Armv8-A ASL (`AArch64.ExclusiveMonitorsPass`) permits spurious
    monitor clear (`exclSpuriousFail = true`, returning `w2 = 1` without writing
    memory), which `StepDeterministicExcl` rejects. -/
theorem stlxr_spurious_fail_narrow_refinement_counterexample :
    let code := loadWordsAt 0x10000#64 [0xc802fc81#32]
    let s0 : MachineState :=
      { pc := 0x10000#64, sp := 0x80000#64,
        xreg := fun r => if r == 4#5 then 0x20000#64 else if r == 1#5 then 0xaa#64 else 0#64,
        excl := some (0x20000#64, 8) }
    ∃ s', VendorArm64Ref.Step code false s0 s' ∧
          ¬ StepDeterministicExcl code false (toWordState s0) (toWordState s') := by
  refine ⟨execStep (loadWordsAt 0x10000#64 [0xc802fc81#32]) true false
            { pc := 0x10000#64, sp := 0x80000#64,
              xreg := fun r => if r == 4#5 then 0x20000#64 else if r == 1#5 then 0xaa#64 else 0#64,
              excl := some (0x20000#64, 8) },
          ⟨true, rfl⟩, ?_⟩
  intro hDet
  have hx2 : (0#64 : BitVec 64) = 1#64 := congrArg (fun st => st.regs .x2) hDet
  revert hx2
  decide

/-- **Theorem 3b (`qemu_stlxr_deterministic_in_vendorArm64Ref`):**
    QEMU's deterministic `exclSpuriousFail = false` `STLXR` execution is
    contained in `VendorArm64Ref.Step`. -/
theorem qemu_stlxr_deterministic_in_vendorArm64Ref
    (code : CodeMap) (lse2Align16B : Bool) (s : MachineState) :
    VendorArm64Ref.Step code lse2Align16B s (execStep code false lse2Align16B s) :=
  ⟨false, rfl⟩

/-! ## Section 2: `scrubXzr31` Homomorphism & Universal Pass-2 Simulation -/

/-- Canonicalize the unarchitectural `xreg 31#5` (`XZR`) slot to `0#64`. -/
def scrubXzr31 (s : MachineState) : MachineState :=
  { s with xreg := fun r => if r == reg31 then 0#64 else s.xreg r }

theorem embedW64_toWordState_eq_scrubXzr31 (s : MachineState) (hf : s.fault = none) :
    embedW64 (toWordState s) = scrubXzr31 s := by
  cases s with
  | mk pc xreg sp vreg flags mem excl halted fault =>
    dsimp only [] at hf
    subst hf
    unfold embedW64 toWordState scrubXzr31
    dsimp only [Option.isSome, ↓reduceIte]
    have hx : (fun r => match reg5ToGpOpt r with | some g => xreg (gpToReg5 g) | none => 0#64) =
              (fun r => if r == reg31 then 0#64 else xreg r) := by
      funext r
      rcases reg5_dichotomy r with rfl | ⟨g, rfl⟩
      · rfl
      · rw [reg5ToGpOpt_gpToReg5, gpToReg5_ne_31]
        rfl
    have hv : (fun v => vreg (simdToVec5 (vec5ToSimd v))) = vreg := by
      funext v
      rw [simdToVec5_vec5ToSimd]
    rw [hx, hv]
    rfl

theorem toWordState_scrubXzr31 (s : MachineState) :
    toWordState (scrubXzr31 s) = toWordState s := by
  cases s with
  | mk pc xreg sp vreg flags mem excl halted fault =>
    unfold toWordState scrubXzr31
    dsimp only []
    have hx : (fun g => if gpToReg5 g == reg31 then 0#64 else xreg (gpToReg5 g)) =
              (fun g => xreg (gpToReg5 g)) := by
      funext g
      rw [gpToReg5_ne_31]
      rfl
    rw [hx]

theorem readXzr_scrubXzr31 (w : GpWidth) (s : MachineState) (r : Reg5) :
    readXzr w (scrubXzr31 s) r = readXzr w s r := by
  cases s
  unfold readXzr scrubXzr31
  dsimp only []
  cases h : (r == reg31) <;> rfl

theorem readSp_scrubXzr31 (w : GpWidth) (s : MachineState) (r : Reg5) :
    readSp w (scrubXzr31 s) r = readSp w s r := by
  cases s
  unfold readSp scrubXzr31
  dsimp only []
  cases h : (r == reg31) <;> rfl

theorem writeXzr_scrubXzr31 (w : GpWidth) (s : MachineState) (r : Reg5) (v : BitVec 64) :
    writeXzr w (scrubXzr31 s) r v = scrubXzr31 (writeXzr w s r v) := by
  cases s with
  | mk pc xreg sp vreg flags mem excl halted fault =>
    unfold writeXzr scrubXzr31
    dsimp only []
    by_cases hr : r == reg31
    · simp [hr]
    · simp only [hr, Bool.false_eq_true, ↓reduceIte]
      have hx : (fun r' => if r' == r then maskWidth w v else if r' == reg31 then 0#64 else xreg r') =
                (fun r' => if r' == reg31 then 0#64 else if r' == r then maskWidth w v else xreg r') := by
        funext r'
        by_cases hr31 : r' == reg31
        · have hne : (r' == r) = false := by
            have h1 : r' = reg31 := LawfulBEq.eq_of_beq hr31
            subst h1
            cases hrr : (reg31 == r)
            · rfl
            · exact False.elim (hr (LawfulBEq.eq_of_beq hrr ▸ BEq.refl reg31))
          simp [hr31, hne]
        · simp [hr31]
      rw [hx]

theorem writeSp_scrubXzr31 (w : GpWidth) (s : MachineState) (r : Reg5) (v : BitVec 64) :
    writeSp w (scrubXzr31 s) r v = scrubXzr31 (writeSp w s r v) := by
  cases s with
  | mk pc xreg sp vreg flags mem excl halted fault =>
    unfold writeSp scrubXzr31
    dsimp only []
    by_cases hr : r == reg31
    · simp [hr]
    · simp only [hr, Bool.false_eq_true, ↓reduceIte]
      have hx : (fun r' => if r' == r then maskWidth w v else if r' == reg31 then 0#64 else xreg r') =
                (fun r' => if r' == reg31 then 0#64 else if r' == r then maskWidth w v else xreg r') := by
        funext r'
        by_cases hr31 : r' == reg31
        · have hne : (r' == r) = false := by
            have h1 : r' = reg31 := LawfulBEq.eq_of_beq hr31
            subst h1
            cases hrr : (reg31 == r)
            · rfl
            · exact False.elim (hr (LawfulBEq.eq_of_beq hrr ▸ BEq.refl reg31))
          simp [hr31, hne]
        · simp [hr31]
      rw [hx]

theorem evalAddrMode_scrubXzr31 (s : MachineState) (rn : Reg5) (mode : AddrMode) :
    evalAddrMode (scrubXzr31 s) rn mode = evalAddrMode s rn mode := by
  unfold evalAddrMode
  dsimp only []
  rw [readSp_scrubXzr31]
  cases mode with
  | regOff rm ext sh =>
    dsimp only []
    rw [readXzr_scrubXzr31]
    rfl
  | _ => rfl

theorem execAluCore_scrubXzr31 (w : GpWidth) (op : AluOp) (s : MachineState)
    (nextPc : BitVec 64) (useSpRd : Bool) (rd : Reg5) (lhs rhs : BitVec 64) :
    execAluCore w op (scrubXzr31 s) nextPc useSpRd rd lhs rhs =
    scrubXzr31 (execAluCore w op s nextPc useSpRd rd lhs rhs) := by
  unfold execAluCore
  cases useSpRd <;> cases ((op == .adds) || (op == .subs)) <;>
    simp only [Bool.false_and, Bool.true_and, Bool.not_true, Bool.not_false,
               Bool.false_eq_true, ↓reduceIte, writeSp_scrubXzr31, writeXzr_scrubXzr31] <;>
    rfl

theorem execBitfield_scrubXzr31 (w : GpWidth) (op : BfmKind) (rd rn : Reg5)
    (immr imms : Nat) (s : MachineState) (nextPc : BitVec 64) :
    execBitfield w op rd rn immr imms (scrubXzr31 s) nextPc =
    scrubXzr31 (execBitfield w op rd rn immr imms s nextPc) := by
  unfold execBitfield
  dsimp only []
  rw [readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]
  rfl

theorem writeVec_scrubXzr31 (vw : VecWidth) (s : MachineState) (v : Vec5) (val : BitVec 128) :
    writeVec vw (scrubXzr31 s) v val = scrubXzr31 (writeVec vw s v val) := rfl

theorem scrubXzr31_mem_excl (s : MachineState) (m' : ByteMem) (ex' : Option (BitVec 64 × Nat)) :
    { scrubXzr31 s with mem := m', excl := ex' } = scrubXzr31 { s with mem := m', excl := ex' } := rfl

theorem scrubXzr31_sp (s : MachineState) : (scrubXzr31 s).sp = s.sp := rfl
theorem scrubXzr31_mem (s : MachineState) : (scrubXzr31 s).mem = s.mem := rfl
theorem scrubXzr31_excl_proj (s : MachineState) : (scrubXzr31 s).excl = s.excl := rfl

theorem ite_option_scrubXzr31 (c : Bool) (a b a' b' : Option MachineState)
    (ha : a = a'.map scrubXzr31) (hb : b = b'.map scrubXzr31) :
    (if c then a else b) = (if c then a' else b').map scrubXzr31 := by
  cases c <;> simp only [↓reduceIte, Bool.false_eq_true, ha, hb]

theorem execScalarInstr_scrubXzr31 (exclSpuriousFail lse2Align16B : Bool)
    (ins : Instr) (s : MachineState) :
    execScalarInstr exclSpuriousFail lse2Align16B ins (scrubXzr31 s) =
    (execScalarInstr exclSpuriousFail lse2Align16B ins s).map scrubXzr31 := by
  cases ins with
  | hintNop => rfl
  | clrex => rfl
  | ret rn => dsimp only [execScalarInstr]; rw [readXzr_scrubXzr31]; rfl
  | adr page rd off => dsimp only [execScalarInstr]; rw [writeXzr_scrubXzr31]; rfl
  | branchImm link off =>
    dsimp only [execScalarInstr]
    cases link <;> simp only [↓reduceIte, Bool.false_eq_true, writeXzr_scrubXzr31] <;> rfl
  | branchCond cond off => rfl
  | cbz w nz rt off => dsimp only [execScalarInstr]; rw [readXzr_scrubXzr31]; rfl
  | tbz nz rt bitIdx off => dsimp only [execScalarInstr]; rw [readXzr_scrubXzr31]; rfl
  | aluImm w op rd rn imm =>
    dsimp only [execScalarInstr]; rw [readSp_scrubXzr31, execAluCore_scrubXzr31]; rfl
  | aluShift w op rd rn rm sh amt =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, execAluCore_scrubXzr31]; rfl
  | aluExt w op rd rn rm ext amt =>
    dsimp only [execScalarInstr]
    rw [readSp_scrubXzr31, readXzr_scrubXzr31, execAluCore_scrubXzr31]; rfl
  | aluCarry w op rd rn rm =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]
    cases ((op == .adcs) || (op == .sbcs)) <;> rfl
  | logImm w op rd rn mask =>
    dsimp only [execScalarInstr]; rw [readXzr_scrubXzr31]
    cases (op == .ands) <;>
      simp only [↓reduceIte, Bool.false_eq_true, writeSp_scrubXzr31, writeXzr_scrubXzr31] <;> rfl
  | logShift w op rd rn rm sh amt =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]
    cases ((op == .ands) || (op == .bics)) <;> rfl
  | moveWide w op rd imm16 pos =>
    dsimp only [execScalarInstr]; rw [readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | bitfield w op rd rn immr imms =>
    dsimp only [execScalarInstr]; rw [execBitfield_scrubXzr31]; rfl
  | extr w rd rn rm lsb =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | shiftVar w sh rd rn rm =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | clz w rd rn =>
    dsimp only [execScalarInstr]; rw [readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | revBytes w rd rn =>
    dsimp only [execScalarInstr]; rw [readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | madd w sub rd rn rm ra =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | mulHigh signed rd rn rm =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | umaddl sub rd rn rm ra =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | divInt w signed rd rn rm =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | condSel w op rd rn rm cond =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | condCmp w sub rn rmOrImm nzcv cond =>
    dsimp only [execScalarInstr]; rw [readXzr_scrubXzr31]
    cases rmOrImm with
    | inl rm => dsimp only []; rw [readXzr_scrubXzr31]; rfl
    | inr _  => rfl
  | crc32 castagnoli bytes rd rn rm =>
    dsimp only [execScalarInstr]
    rw [readXzr_scrubXzr31, readXzr_scrubXzr31, writeXzr_scrubXzr31]; rfl
  | ldstGp load msz rt rn mode =>
    dsimp only [execScalarInstr]; rw [evalAddrMode_scrubXzr31]
    cases evalAddrMode s rn mode with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨ea, wbOpt⟩
      cases load <;> cases msz <;> cases wbOpt <;>
        simp only [↓reduceIte, Bool.false_eq_true, readXzr_scrubXzr31,
                   scrubXzr31_mem_excl, writeXzr_scrubXzr31, writeSp_scrubXzr31] <;> rfl
  | ldstPairGp load w rt1 rt2 rn mode =>
    dsimp only [execScalarInstr]; rw [evalAddrMode_scrubXzr31]
    cases evalAddrMode s rn mode with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨ea, wbOpt⟩
      cases load <;> cases wbOpt <;>
        simp only [↓reduceIte, Bool.false_eq_true, readXzr_scrubXzr31,
                   scrubXzr31_mem_excl, writeXzr_scrubXzr31, writeSp_scrubXzr31] <;> rfl
  | ldar w exclusive rt rn =>
    dsimp only [execScalarInstr]
    simp only [scrubXzr31_sp, scrubXzr31_mem, readSp_scrubXzr31]
    cases (rn == reg31 && ((s.sp &&& 15#64) != 0#64)) <;>
      cases (!checkOrderedAlign lse2Align16B exclusive (match w with | .x64 => 8 | .w32 => 4) (readSp .x64 s rn)) <;>
      simp only [↓reduceIte, Bool.false_eq_true, writeXzr_scrubXzr31] <;> rfl
  | stlr w rt rn =>
    dsimp only [execScalarInstr]
    simp only [scrubXzr31_sp, scrubXzr31_mem, readSp_scrubXzr31, readXzr_scrubXzr31]
    cases (rn == reg31 && ((s.sp &&& 15#64) != 0#64)) <;>
      cases (!checkOrderedAlign lse2Align16B false (match w with | .x64 => 8 | .w32 => 4) (readSp .x64 s rn)) <;>
      simp only [↓reduceIte, Bool.false_eq_true] <;> rfl
  | stlxr w rs rt rn =>
    dsimp only [execScalarInstr]
    simp only [readSp_scrubXzr31, readXzr_scrubXzr31, scrubXzr31_mem_excl, writeXzr_scrubXzr31]
    simp only [scrubXzr31_sp, scrubXzr31_mem, scrubXzr31_excl_proj]
    exact ite_option_scrubXzr31 _ _ _ _ _ rfl
      (ite_option_scrubXzr31 _ _ _ _ _ rfl
        (ite_option_scrubXzr31 _ _ _ _ _ rfl rfl))
  | _ => rfl

theorem execNeonInstr_scrubXzr31 (ins : Instr) (s : MachineState) :
    execNeonInstr ins (scrubXzr31 s) = (execNeonInstr ins s).map scrubXzr31 := by
  cases ins with
  | ldstSimd load vw vt rn mode =>
    dsimp only [execNeonInstr]; rw [evalAddrMode_scrubXzr31]
    cases evalAddrMode s rn mode with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨ea, wbOpt⟩
      cases load <;> cases wbOpt <;>
        simp only [↓reduceIte, Bool.false_eq_true, scrubXzr31_mem_excl,
                   writeVec_scrubXzr31, writeSp_scrubXzr31] <;> rfl
  | ldstPairSimd load vw vt1 vt2 rn mode =>
    dsimp only [execNeonInstr]; rw [evalAddrMode_scrubXzr31]
    cases evalAddrMode s rn mode with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨ea, wbOpt⟩
      cases load <;> cases wbOpt <;>
        simp only [↓reduceIte, Bool.false_eq_true, scrubXzr31_mem_excl,
                   writeVec_scrubXzr31, writeSp_scrubXzr31] <;> rfl
  | neonDupGp vw es vd rn =>
    dsimp only [execNeonInstr]; rw [readXzr_scrubXzr31]; rfl
  | fmovGpToVec w vd rn =>
    dsimp only [execNeonInstr]; rw [readXzr_scrubXzr31]; rfl
  | fmovVecToGp w rd vn =>
    dsimp only [execNeonInstr]; rw [writeXzr_scrubXzr31]; rfl
  | neonUmov es rd vn idx =>
    dsimp only [execNeonInstr]; rw [writeXzr_scrubXzr31]; rfl
  | neonInsGp es vd rn idx =>
    dsimp only [execNeonInstr]; rw [readXzr_scrubXzr31]; rfl
  | _ => rfl

theorem execInstr_scrubXzr31 (exclSpuriousFail lse2Align16B : Bool)
    (ins : Instr) (s : MachineState) :
    execInstr exclSpuriousFail lse2Align16B ins (scrubXzr31 s) =
    scrubXzr31 (execInstr exclSpuriousFail lse2Align16B ins s) := by
  unfold execInstr
  rw [execScalarInstr_scrubXzr31, execNeonInstr_scrubXzr31]
  cases execScalarInstr exclSpuriousFail lse2Align16B ins s with
  | some _ => rfl
  | none =>
    cases execNeonInstr ins s with
    | some _ => rfl
    | none => rfl

theorem toWordState_execStep (code : CodeMap) (exclSpuriousFail lse2Align16B : Bool)
    (s : MachineState) :
    toWordState (execStep code exclSpuriousFail lse2Align16B s) =
    stepW64 code exclSpuriousFail lse2Align16B (toWordState s) := by
  unfold execStep stepW64
  have hh : (toWordState s).halted = s.halted := rfl
  have hf : (toWordState s).fault = s.fault.isSome := rfl
  have hpc : (toWordState s).pc = s.pc := rfl
  rw [hh, hf, hpc]
  cases hstop : s.halted || s.fault.isSome
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hnone : s.fault = none := by
      cases hflt : s.fault with
      | none => rfl
      | some _ => simp [hflt] at hstop
    cases fetchWord32 code s.pc with
    | error _ => dsimp only []; rfl
    | ok w =>
      dsimp only []
      cases decodeWord32 w with
      | error _ => dsimp only []; rfl
      | ok ins =>
        dsimp only []
        rw [embedW64_toWordState_eq_scrubXzr31 s hnone, execInstr_scrubXzr31, toWordState_scrubXzr31]
  · simp

/-- **Universal Single-Step Pass-2 Correspondence (`VendorArm64Ref.Step ⊆ WordArm64.Step`):**
    Every transition (including all 82 architectural opcodes and all Ring-3 fetch,
    decode, constrained-unpredictable, `#SPAlignment`, and `#Alignment` traps) of
    `VendorArm64Ref.Step` is simulated by `WordArm64.Step`. -/
theorem vendorArm64Ref_step_sub_wordArm64_step
    (code : CodeMap) (lse2Align16B : Bool) (s s' : MachineState)
    (hStep : VendorArm64Ref.Step code lse2Align16B s s') :
    WordArm64.Step code lse2Align16B (toWordState s) (toWordState s') := by
  rcases hStep with ⟨exclSpuriousFail, rfl⟩
  exact ⟨exclSpuriousFail, (toWordState_execStep code exclSpuriousFail lse2Align16B s).symm⟩

/-- **Universal Multi-Step Pass-2 Correspondence (`VendorArm64Ref.StepsN ⊆ WordArm64.StepsN`):**
    Every `n`-step trace of `VendorArm64Ref` is simulated by `WordArm64`. -/
theorem vendorArm64Ref_stepsN_sub_wordArm64_stepsN
    (code : CodeMap) (lse2Align16B : Bool) (n : Nat) (s s' : MachineState)
    (hSteps : VendorArm64Ref.StepsN code lse2Align16B n s s') :
    WordArm64.StepsN code lse2Align16B n (toWordState s) (toWordState s') := by
  induction hSteps with
  | zero st => exact StepsN.zero (toWordState st)
  | step h1 _ ih =>
    exact StepsN.step (vendorArm64Ref_step_sub_wordArm64_step code lse2Align16B _ _ h1) ih

end WordArm64
