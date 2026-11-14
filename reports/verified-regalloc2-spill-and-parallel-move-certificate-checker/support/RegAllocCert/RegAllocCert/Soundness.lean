-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RegAllocCert.Certificate

namespace RegAllocCert

/-- Well-formedness of an allocation map `alloc : VReg → Loc` with respect to a reserved
scratch/caller-clobber physical register `reservedScratch`. -/
structure ValidAllocMap (alloc : VReg → Loc) (reservedScratch : PReg) : Prop where
  inj : ∀ v1 v2 : VReg, alloc v1 = alloc v2 → v1 = v2
  no_scratch_alias : ∀ v : VReg, alloc v ≠ .preg reservedScratch

/-- State simulation relation between `SSAState` and `MachState` under `alloc`. -/
def stateSim (alloc : VReg → Loc) (st : SSAState) (ms : MachState) : Prop :=
  ∀ v : VReg, ms.get (alloc v) = st.get v

theorem ssa_get_set_same (st : SSAState) (v : VReg) (val : Int) :
    (st.set v val).get v = val := by
  simp [SSAState.get, SSAState.set]

theorem ssa_get_set_ne (st : SSAState) {v1 v2 : VReg} (val : Int) (hne : v1 ≠ v2) :
    (st.set v2 val).get v1 = st.get v1 := by
  simp [SSAState.get, SSAState.set, hne]

theorem mach_get_set_same (ms : MachState) (l : Loc) (val : Int) :
    (ms.set l val).get l = val := by
  simp [MachState.get, MachState.set]

theorem mach_get_set_ne (ms : MachState) {l1 l2 : Loc} (val : Int) (hne : l1 ≠ l2) :
    (ms.set l2 val).get l1 = ms.get l1 := by
  simp [MachState.get, MachState.set, hne]

theorem stateSim_set
    {alloc : VReg → Loc} {reservedScratch : PReg}
    (h_wf : ValidAllocMap alloc reservedScratch)
    {st : SSAState} {ms : MachState}
    (h_sim : stateSim alloc st ms) (dst : VReg) (val : Int) :
    stateSim alloc (st.set dst val) (ms.set (alloc dst) val) := by
  intro v
  by_cases h_eq : v = dst
  · subst h_eq
    rw [mach_get_set_same, ssa_get_set_same]
  · have h_loc_ne : alloc v ≠ alloc dst := fun h_l => h_eq (h_wf.inj v dst h_l)
    rw [mach_get_set_ne _ _ h_loc_ne, ssa_get_set_ne _ _ h_eq, h_sim v]

theorem stateSim_set_scratch
    {alloc : VReg → Loc} {reservedScratch : PReg}
    (h_wf : ValidAllocMap alloc reservedScratch)
    {st : SSAState} {ms : MachState}
    (h_sim : stateSim alloc st ms) (val : Int) :
    stateSim alloc st (ms.set (.preg reservedScratch) val) := by
  intro v
  have h_ne : alloc v ≠ .preg reservedScratch := h_wf.no_scratch_alias v
  rw [mach_get_set_ne _ _ h_ne, h_sim v]

theorem stateSim_swap2
    {alloc : VReg → Loc} {reservedScratch : PReg}
    (h_wf : ValidAllocMap alloc reservedScratch)
    {st : SSAState} {ms : MachState}
    (h_sim : stateSim alloc st ms)
    (v1 v2 : VReg) (mode : CycleResolution)
    (h_side : (checkScratchDisjoint2 (alloc v1) (alloc v2) mode &&
               match mode with
               | .viaScratch s => decide (s = reservedScratch)
               | .viaXchg => true) = true) :
    stateSim alloc
      ((st.set v1 (st.get v2)).set v2 (st.get v1))
      (execSwap2Mach ms (alloc v1) (alloc v2) mode) := by
  cases mode with
  | viaXchg =>
    simp only [execSwap2Mach]
    rw [← h_sim v1, ← h_sim v2]
    exact stateSim_set h_wf (stateSim_set h_wf h_sim v1 (ms.get (alloc v2))) v2 (ms.get (alloc v1))
  | viaScratch s =>
    simp only [Bool.and_eq_true, checkScratchDisjoint2, decide_eq_true_eq] at h_side
    rcases h_side with ⟨⟨hs1, hs2, _⟩, rfl⟩
    simp only [execSwap2Mach]
    have h_sim1 : stateSim alloc st (ms.set (.preg s) (ms.get (alloc v1))) :=
      stateSim_set_scratch h_wf h_sim (ms.get (alloc v1))
    have h_v2 : (ms.set (.preg s) (ms.get (alloc v1))).get (alloc v2) = st.get v2 := h_sim1 v2
    have h_s :
        ((ms.set (.preg s) (ms.get (alloc v1))).set (alloc v1)
          ((ms.set (.preg s) (ms.get (alloc v1))).get (alloc v2))).get (.preg s) = st.get v1 := by
      rw [mach_get_set_ne _ _ hs1, mach_get_set_same, h_sim v1]
    rw [h_s, h_v2]
    exact stateSim_set h_wf (stateSim_set h_wf h_sim1 v1 (st.get v2)) v2 (st.get v1)

theorem stateSim_rotate3
    {alloc : VReg → Loc} {reservedScratch : PReg}
    (h_wf : ValidAllocMap alloc reservedScratch)
    {st : SSAState} {ms : MachState}
    (h_sim : stateSim alloc st ms)
    (v1 v2 v3 : VReg) (scratch : PReg)
    (h_side : (checkScratchDisjoint3 (alloc v1) (alloc v2) (alloc v3) scratch &&
               decide (scratch = reservedScratch)) = true) :
    stateSim alloc
      (((st.set v1 (st.get v2)).set v2 (st.get v3)).set v3 (st.get v1))
      (execRotate3Mach ms (alloc v1) (alloc v2) (alloc v3) scratch) := by
  simp only [Bool.and_eq_true, checkScratchDisjoint3, decide_eq_true_eq] at h_side
  rcases h_side with ⟨⟨hs1, hs2, _, _, h13, _⟩, rfl⟩
  simp only [execRotate3Mach]
  have h_sim1 : stateSim alloc st (ms.set (.preg scratch) (ms.get (alloc v1))) :=
    stateSim_set_scratch h_wf h_sim (ms.get (alloc v1))
  have h_v2 : (ms.set (.preg scratch) (ms.get (alloc v1))).get (alloc v2) = st.get v2 :=
    h_sim1 v2
  have h_v3 :
      ((ms.set (.preg scratch) (ms.get (alloc v1))).set (alloc v1)
        ((ms.set (.preg scratch) (ms.get (alloc v1))).get (alloc v2))).get (alloc v3) = st.get v3 := by
    rw [mach_get_set_ne _ _ (Ne.symm h13), h_sim1 v3]
  have h_s :
      (((ms.set (.preg scratch) (ms.get (alloc v1))).set (alloc v1)
          ((ms.set (.preg scratch) (ms.get (alloc v1))).get (alloc v2))).set (alloc v2)
        (((ms.set (.preg scratch) (ms.get (alloc v1))).set (alloc v1)
            ((ms.set (.preg scratch) (ms.get (alloc v1))).get (alloc v2))).get (alloc v3))).get
        (.preg scratch) = st.get v1 := by
    rw [mach_get_set_ne _ _ hs2, mach_get_set_ne _ _ hs1, mach_get_set_same, h_sim v1]
  rw [h_s, h_v3, h_v2]
  exact stateSim_set h_wf
    (stateSim_set h_wf (stateSim_set h_wf h_sim1 v1 (st.get v2)) v2 (st.get v3))
    v3 (st.get v1)

/-- Outcome-lifted simulation between `Outcome SSAState` and `Outcome MachState`. -/
def outcomeSim (alloc : VReg → Loc) (oS : Outcome SSAState) (oM : Outcome MachState) : Prop :=
  match oS with
  | .ub      => True
  | .panic   => oM = .panic
  | .val st' => ∃ ms', oM = .val ms' ∧ stateSim alloc st' ms'

/-- Instruction-level simulation soundness for `inferInstPair` + `checkCertSideConds`. -/
theorem inferInstPair_sound
    {alloc : VReg → Loc} {reservedScratch : PReg}
    (h_wf : ValidAllocMap alloc reservedScratch)
    (cert : InstCert)
    (h_side : checkCertSideConds alloc reservedScratch cert = true)
    {st : SSAState} {ms : MachState}
    (h_sim : stateSim alloc st ms) :
    outcomeSim alloc
      (evalSSAInst st (inferInstPair alloc cert).1)
      (evalMachInst ms (inferInstPair alloc cert).2) := by
  induction cert generalizing st ms with
  | constI dst val =>
    simp only [inferInstPair, evalSSAInst, evalMachInst, outcomeSim]
    exact ⟨_, rfl, stateSim_set h_wf h_sim dst val⟩
  | binOp op dst lhs rhs =>
    simp only [inferInstPair, evalSSAInst, evalMachInst, outcomeSim]
    rw [h_sim lhs, h_sim rhs]
    exact ⟨_, rfl, stateSim_set h_wf h_sim dst (evalBinOp op (st.get lhs) (st.get rhs))⟩
  | copyVReg dst src =>
    simp only [inferInstPair, evalSSAInst, evalMachInst, outcomeSim]
    rw [h_sim src]
    exact ⟨_, rfl, stateSim_set h_wf h_sim dst (st.get src)⟩
  | parSwap2 v1 v2 mode =>
    simp only [inferInstPair, evalSSAInst, evalMachInst, outcomeSim]
    simp only [checkCertSideConds] at h_side
    exact ⟨_, rfl, stateSim_swap2 h_wf h_sim v1 v2 mode h_side⟩
  | parRotate3 v1 v2 v3 scratch =>
    simp only [inferInstPair, evalSSAInst, evalMachInst, outcomeSim]
    simp only [checkCertSideConds] at h_side
    exact ⟨_, rfl, stateSim_rotate3 h_wf h_sim v1 v2 v3 scratch h_side⟩
  | callClobber dst arg delta clob =>
    simp only [inferInstPair, evalSSAInst, evalMachInst, outcomeSim]
    simp only [checkCertSideConds, decide_eq_true_eq] at h_side
    subst h_side
    rw [h_sim arg]
    have h_clob_sim : stateSim alloc st (ms.set (.preg clob) 0) :=
      stateSim_set_scratch h_wf h_sim 0
    exact ⟨_, rfl, stateSim_set h_wf h_clob_sim dst (st.get arg + delta)⟩
  | assertBoundsPanic v bound =>
    simp only [inferInstPair, evalSSAInst, evalMachInst]
    rw [h_sim v]
    by_cases h_b : 0 ≤ st.get v ∧ st.get v < bound
    · simp [h_b, outcomeSim, h_sim]
    · simp [h_b, outcomeSim]
  | assumeNonNegUB v =>
    simp only [inferInstPair, evalSSAInst, evalMachInst]
    rw [h_sim v]
    by_cases h_b : 0 ≤ st.get v
    · simp [h_b, outcomeSim, h_sim]
    · simp [h_b, outcomeSim]
  | seq c1 c2 ih1 ih2 =>
    simp only [checkCertSideConds, Bool.and_eq_true] at h_side
    simp only [inferInstPair, evalSSAInst, evalMachInst]
    have h1 := ih1 h_side.1 h_sim
    cases h_eval1 : evalSSAInst st (inferInstPair alloc c1).1 with
    | ub =>
      simp [outcomeSim]
    | panic =>
      rw [h_eval1] at h1
      simp only [outcomeSim] at h1
      rw [h1]
      simp [outcomeSim]
    | val st1 =>
      rw [h_eval1] at h1
      rcases h1 with ⟨ms1, h_m1, h_sim1⟩
      rw [h_m1]
      exact ih2 h_side.2 h_sim1

/-- Instruction-level certificate checker soundness (`checkInstCert_sound`). -/
theorem checkInstCert_sound
    {alloc : VReg → Loc} {reservedScratch : PReg}
    (h_wf : ValidAllocMap alloc reservedScratch)
    {ssa : SSAInst} {mach : MachInst} {cert : InstCert}
    (h_check : checkInstCert alloc reservedScratch ssa mach cert = true)
    {st : SSAState} {ms : MachState}
    (h_sim : stateSim alloc st ms) :
    outcomeSim alloc (evalSSAInst st ssa) (evalMachInst ms mach) := by
  simp only [checkInstCert, Bool.and_eq_true, decide_eq_true_eq] at h_check
  rcases h_check with ⟨⟨rfl, rfl⟩, h_side⟩
  exact inferInstPair_sound h_wf cert h_side h_sim

/-- Top-level `RegAllocCert` soundness theorem (`checkRegAllocCert_sound`). -/
theorem checkRegAllocCert_sound
    (ssaFn : SSAFunc) (machFn : MachFunc) (cert : RegAllocCertBundle)
    (h_wf : ValidAllocMap cert.alloc cert.reservedScratch)
    (h_check : checkRegAllocCert ssaFn machFn cert = true)
    (st : SSAState) (ms : MachState)
    (h_sim : stateSim cert.alloc st ms)
    (argVal : Int) :
    refines (evalSSAFunc ssaFn st argVal) (evalMachFunc machFn ms argVal) := by
  have h_inst : checkInstCert cert.alloc cert.reservedScratch ssaFn.body machFn.body cert.bodyCert = true := by
    simp only [checkRegAllocCert, Bool.and_eq_true] at h_check
    exact h_check.2
  have h_arg : cert.alloc ssaFn.argVReg = machFn.argLoc := by
    simp only [checkRegAllocCert, Bool.and_eq_true, decide_eq_true_eq] at h_check
    exact h_check.1.1.1.1
  have h_ret : cert.alloc ssaFn.retVReg = machFn.retLoc := by
    simp only [checkRegAllocCert, Bool.and_eq_true, decide_eq_true_eq] at h_check
    exact h_check.1.1.1.2
  have h_sim0 : stateSim cert.alloc (st.set ssaFn.argVReg argVal) (ms.set machFn.argLoc argVal) := by
    rw [← h_arg]
    exact stateSim_set h_wf h_sim ssaFn.argVReg argVal
  have h_body := checkInstCert_sound h_wf h_inst h_sim0
  intro h_no_ub
  simp only [evalSSAFunc, evalMachFunc] at h_no_ub ⊢
  cases h_s : evalSSAInst (st.set ssaFn.argVReg argVal) ssaFn.body with
  | ub =>
    simp [h_s] at h_no_ub
  | panic =>
    rw [h_s] at h_body
    simp only [outcomeSim] at h_body
    rw [h_body]
  | val stF =>
    rw [h_s] at h_body
    rcases h_body with ⟨msF, h_mF, h_simF⟩
    rw [h_mF]
    dsimp only
    rw [← h_ret, h_simF ssaFn.retVReg]

end RegAllocCert
