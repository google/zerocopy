-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RegAllocCert.Soundness

namespace RegAllocCert

/-- Declarative relational specification of valid instruction-level `RegAllocCert` certificates. -/
inductive ValidInstCert (alloc : VReg → Loc) (reservedScratch : PReg) :
    SSAInst → MachInst → InstCert → Prop where
  | constI (dst : VReg) (val : Int) :
      ValidInstCert alloc reservedScratch
        (.constI dst val) (.constLoc (alloc dst) val) (.constI dst val)
  | binOp (op : BinOp) (dst lhs rhs : VReg) :
      ValidInstCert alloc reservedScratch
        (.binOp op dst lhs rhs)
        (.binOpLoc op (alloc dst) (alloc lhs) (alloc rhs))
        (.binOp op dst lhs rhs)
  | copyVReg (dst src : VReg) :
      ValidInstCert alloc reservedScratch
        (.copyVReg dst src) (.moveLoc (alloc dst) (alloc src)) (.copyVReg dst src)
  | parSwap2 (v1 v2 : VReg) (mode : CycleResolution)
      (h_side : (checkScratchDisjoint2 (alloc v1) (alloc v2) mode &&
                 match mode with
                 | .viaScratch s => decide (s = reservedScratch)
                 | .viaXchg => true) = true) :
      ValidInstCert alloc reservedScratch
        (.parSwap2 v1 v2) (.swap2Loc (alloc v1) (alloc v2) mode) (.parSwap2 v1 v2 mode)
  | parRotate3 (v1 v2 v3 : VReg) (scratch : PReg)
      (h_side : (checkScratchDisjoint3 (alloc v1) (alloc v2) (alloc v3) scratch &&
                 decide (scratch = reservedScratch)) = true) :
      ValidInstCert alloc reservedScratch
        (.parRotate3 v1 v2 v3)
        (.rotate3Scratch (alloc v1) (alloc v2) (alloc v3) scratch)
        (.parRotate3 v1 v2 v3 scratch)
  | callClobber (dst arg : VReg) (delta : Int) (clob : PReg)
      (h_clob : clob = reservedScratch) :
      ValidInstCert alloc reservedScratch
        (.callClobber dst arg delta clob)
        (.callClobberLoc (alloc dst) (alloc arg) delta clob)
        (.callClobber dst arg delta clob)
  | assertBoundsPanic (v : VReg) (bound : Int) :
      ValidInstCert alloc reservedScratch
        (.assertBoundsPanic v bound)
        (.assertBoundsPanicLoc (alloc v) bound)
        (.assertBoundsPanic v bound)
  | assumeNonNegUB (v : VReg) :
      ValidInstCert alloc reservedScratch
        (.assumeNonNegUB v)
        (.assumeNonNegUBLoc (alloc v))
        (.assumeNonNegUB v)
  | seq {s1 s2 : SSAInst} {m1 m2 : MachInst} {c1 c2 : InstCert}
      (h1 : ValidInstCert alloc reservedScratch s1 m1 c1)
      (h2 : ValidInstCert alloc reservedScratch s2 m2 c2) :
      ValidInstCert alloc reservedScratch (.seq s1 s2) (.seq m1 m2) (.seq c1 c2)

/-- Declarative relational specification of a valid function-level `RegAllocCertBundle`. -/
structure ValidRegAlloc
    (ssaFn : SSAFunc) (machFn : MachFunc) (cert : RegAllocCertBundle) : Prop where
  arg_match   : cert.alloc ssaFn.argVReg = machFn.argLoc
  ret_match   : cert.alloc ssaFn.retVReg = machFn.retLoc
  spills_ok   : checkSpillListValid machFn.frameSize cert.spillSlots = true
  abi_ok      : checkABICalleeSaved machFn.frameSize machFn.calleeSaved machFn.epilogueRestores = true
  body_valid  : ValidInstCert cert.alloc cert.reservedScratch ssaFn.body machFn.body cert.bodyCert

theorem validInstCert_endpoints
    {alloc : VReg → Loc} {reservedScratch : PReg}
    {ssa : SSAInst} {mach : MachInst} {cert : InstCert}
    (h : ValidInstCert alloc reservedScratch ssa mach cert) :
    inferInstPair alloc cert = (ssa, mach) ∧
    checkCertSideConds alloc reservedScratch cert = true := by
  induction h with
  | constI _ _ => simp [inferInstPair, checkCertSideConds]
  | binOp _ _ _ _ => simp [inferInstPair, checkCertSideConds]
  | copyVReg _ _ => simp [inferInstPair, checkCertSideConds]
  | parSwap2 _ _ _ hs => exact ⟨rfl, hs⟩
  | parRotate3 _ _ _ _ hs => exact ⟨rfl, hs⟩
  | callClobber _ _ _ _ hc => simp [inferInstPair, checkCertSideConds, hc]
  | assertBoundsPanic _ _ => simp [inferInstPair, checkCertSideConds]
  | assumeNonNegUB _ => simp [inferInstPair, checkCertSideConds]
  | seq _ _ ih1 ih2 =>
    rcases ih1 with ⟨e1, s1⟩
    rcases ih2 with ⟨e2, s2⟩
    simp [inferInstPair, checkCertSideConds, e1, e2, s1, s2]

/-- Instruction-level checker completeness (`checkInstCert_complete`). -/
theorem checkInstCert_complete
    {alloc : VReg → Loc} {reservedScratch : PReg}
    {ssa : SSAInst} {mach : MachInst} {cert : InstCert}
    (h : ValidInstCert alloc reservedScratch ssa mach cert) :
    checkInstCert alloc reservedScratch ssa mach cert = true := by
  rcases validInstCert_endpoints h with ⟨h_ep, h_side⟩
  simp [checkInstCert, h_ep, h_side]

/-- Converse inversion: any certificate accepted by `checkInstCert` satisfies `ValidInstCert`. -/
theorem checkInstCert_to_valid
    {alloc : VReg → Loc} {reservedScratch : PReg}
    {ssa : SSAInst} {mach : MachInst} {cert : InstCert}
    (h : checkInstCert alloc reservedScratch ssa mach cert = true) :
    ValidInstCert alloc reservedScratch ssa mach cert := by
  simp only [checkInstCert, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨rfl, rfl⟩, h_side⟩
  induction cert with
  | constI dst val => exact .constI dst val
  | binOp op dst lhs rhs => exact .binOp op dst lhs rhs
  | copyVReg dst src => exact .copyVReg dst src
  | parSwap2 v1 v2 mode => exact .parSwap2 v1 v2 mode h_side
  | parRotate3 v1 v2 v3 scratch => exact .parRotate3 v1 v2 v3 scratch h_side
  | callClobber dst arg delta clob =>
    simp only [checkCertSideConds, decide_eq_true_eq] at h_side
    exact .callClobber dst arg delta clob h_side
  | assertBoundsPanic v bound => exact .assertBoundsPanic v bound
  | assumeNonNegUB v => exact .assumeNonNegUB v
  | seq c1 c2 ih1 ih2 =>
    simp only [checkCertSideConds, Bool.and_eq_true] at h_side
    exact .seq (ih1 h_side.1) (ih2 h_side.2)

/-- Bidirectional equivalence between `checkInstCert` and `ValidInstCert`. -/
theorem checkInstCert_iff_valid
    {alloc : VReg → Loc} {reservedScratch : PReg}
    {ssa : SSAInst} {mach : MachInst} {cert : InstCert} :
    checkInstCert alloc reservedScratch ssa mach cert = true ↔
    ValidInstCert alloc reservedScratch ssa mach cert :=
  ⟨checkInstCert_to_valid, checkInstCert_complete⟩

/-- Function-level checker completeness (`checkRegAllocCert_complete`). -/
theorem checkRegAllocCert_complete
    (ssaFn : SSAFunc) (machFn : MachFunc) (cert : RegAllocCertBundle)
    (h_valid : ValidRegAlloc ssaFn machFn cert) :
    checkRegAllocCert ssaFn machFn cert = true := by
  rcases h_valid with ⟨ha, hr, hs, habi, hb⟩
  simp [checkRegAllocCert, ha, hr, hs, habi, checkInstCert_complete hb]

/-- Bidirectional equivalence between `checkRegAllocCert` and `ValidRegAlloc`. -/
theorem checkRegAllocCert_iff_valid
    (ssaFn : SSAFunc) (machFn : MachFunc) (cert : RegAllocCertBundle) :
    checkRegAllocCert ssaFn machFn cert = true ↔ ValidRegAlloc ssaFn machFn cert := by
  constructor
  · intro h
    have ha : cert.alloc ssaFn.argVReg = machFn.argLoc := by
      simp only [checkRegAllocCert, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.1.1
    have hr : cert.alloc ssaFn.retVReg = machFn.retLoc := by
      simp only [checkRegAllocCert, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.1.2
    have hs : checkSpillListValid machFn.frameSize cert.spillSlots = true := by
      simp only [checkRegAllocCert, Bool.and_eq_true] at h
      exact h.1.1.2
    have habi : checkABICalleeSaved machFn.frameSize machFn.calleeSaved machFn.epilogueRestores = true := by
      simp only [checkRegAllocCert, Bool.and_eq_true] at h
      exact h.1.2
    have hb : checkInstCert cert.alloc cert.reservedScratch ssaFn.body machFn.body cert.bodyCert = true := by
      simp only [checkRegAllocCert, Bool.and_eq_true] at h
      exact h.2
    exact ⟨ha, hr, hs, habi, checkInstCert_to_valid hb⟩
  · exact checkRegAllocCert_complete ssaFn machFn cert

end RegAllocCert
