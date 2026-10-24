import AnnealResearch.TreeMemoryReleaseAgreement
import AnnealResearch.TreeMemoryPreservation

/-!
Ordered protector releases over an explicitly supplied finite registration list.
The reference and factored folds call their own actual release operations.
Every ordinary returned error retains its exact partial residual and skips the
remaining list. No runtime frame is inspected, cleared, detached or consumed.

The only operational correspondence/width admission is the existing WellSized
domain. Registrations need not be valid, distinct, live, protected, reachable or
safe. The exhaustive noChoice branch is not an actual release noChoice witness.
The owned equations do not formalize Rust/helper/generated-code adequacy,
panic/allocator/GC failure, a full Return/unwind/Drop operation or frame ownership.
-/

namespace AnnealResearch.TreeEndCall

/-- Selected supplied source-extra shape, independent of memory.currentFrame.
Passing this value does not prove linear consumption or source frame ownership. -/
structure SuppliedFrameExtra where
  protectors : List TreeMemory.Provenance

/-- Observe every reference outcome, including failure residuals. -/
def rResidual {A : Type} : TreeMemory.Result A → TreeMemory.State
  | .ok _ state => state
  | .ub _ state => state
  | .unsupported _ state => state
  | .noChoice state => state

/-- The existing factored all-outcome observer. -/
abbrev fResidual {A : Type} (answer : TreeFactoredMemory.Result A) :
    TreeFactoredMemory.State := answer.residual

def rReleaseList (memory : TreeMemory.State) :
    List TreeMemory.Provenance → TreeMemory.Result Unit
  | [] => .ok () memory
  | entry :: suffix =>
      match TreeMemory.release memory entry with
      | .ok () after => rReleaseList after suffix
      | .ub fault after => .ub fault after
      | .unsupported reason after => .unsupported reason after
      | .noChoice after => .noChoice after

/-- Independent recursion over actual factored release, without reference
execution, reification of an execution or reconstruction from its output. -/
def fReleaseList (memory : TreeFactoredMemory.State) :
    List TreeMemory.Provenance → TreeFactoredMemory.Result Unit
  | [] => .ok () memory
  | entry :: suffix =>
      match TreeFactoredMemory.release memory entry with
      | .ok () after => fReleaseList after suffix
      | .ub fault after => .ub fault after
      | .unsupported reason after => .unsupported reason after
      | .noChoice after => .noChoice after

def rEndCall (memory : TreeMemory.State) (extra : SuppliedFrameExtra) :
    TreeMemory.Result Unit := rReleaseList memory extra.protectors

def fEndCall (memory : TreeFactoredMemory.State) (extra : SuppliedFrameExtra) :
    TreeFactoredMemory.Result Unit := fReleaseList memory extra.protectors

theorem rReleaseList_nil (memory : TreeMemory.State) :
    rReleaseList memory [] = .ok () memory := rfl

theorem fReleaseList_nil (memory : TreeFactoredMemory.State) :
    fReleaseList memory [] = .ok () memory := rfl

theorem rReleaseList_cons (memory : TreeMemory.State)
    (entry : TreeMemory.Provenance) (suffix : List TreeMemory.Provenance) :
    rReleaseList memory (entry :: suffix) =
      (match TreeMemory.release memory entry with
      | .ok () after => rReleaseList after suffix
      | .ub fault after => .ub fault after
      | .unsupported reason after => .unsupported reason after
      | .noChoice after => .noChoice after) := rfl

theorem fReleaseList_cons (memory : TreeFactoredMemory.State)
    (entry : TreeMemory.Provenance) (suffix : List TreeMemory.Provenance) :
    fReleaseList memory (entry :: suffix) =
      (match TreeFactoredMemory.release memory entry with
      | .ok () after => fReleaseList after suffix
      | .ub fault after => .ub fault after
      | .unsupported reason after => .unsupported reason after
      | .noChoice after => .noChoice after) := rfl

theorem rEndCall_eq (memory : TreeMemory.State) (extra : SuppliedFrameExtra) :
    rEndCall memory extra = rReleaseList memory extra.protectors := rfl

theorem fEndCall_eq (memory : TreeFactoredMemory.State) (extra : SuppliedFrameExtra) :
    fEndCall memory extra = fReleaseList memory extra.protectors := rfl

/-- Carry the actual successful head's width into the tail; every failing head
is observed with its own actual residual, without a success or NoUB admission. -/
theorem fReleaseList_preserves (memory : TreeFactoredMemory.State)
    (registrations : List TreeMemory.Provenance)
    (sized : TreeFactoredMemory.WellSized memory) :
    TreeMemoryDomain.ResultWellSized (fReleaseList memory registrations) := by
  induction registrations generalizing memory with
  | nil => exact sized
  | cons entry suffix ih =>
      have nextSized := TreeMemoryPreservation.release_preserves memory entry sized
      cases released : TreeFactoredMemory.release memory entry with
      | ok value after =>
          cases value
          have afterSized : TreeFactoredMemory.WellSized after := by
            simpa only [TreeMemoryDomain.ResultWellSized, released,
              TreeFactoredMemory.Result.residual] using nextSized
          simpa only [fReleaseList, released] using ih after afterSized
      | ub fault after =>
          simpa only [fReleaseList, released] using nextSized
      | unsupported reason after =>
          simpa only [fReleaseList, released] using nextSized
      | noChoice after =>
          simpa only [fReleaseList, released] using nextSized

theorem fEndCall_preserves (memory : TreeFactoredMemory.State)
    (extra : SuppliedFrameExtra) (sized : TreeFactoredMemory.WellSized memory) :
    TreeMemoryDomain.ResultWellSized (fEndCall memory extra) :=
  fReleaseList_preserves memory extra.protectors sized

/-- Exact status, diagnostic and complete reified memory equality for every
finite supplied list. Width is the sole input condition. -/
theorem releaseList_agrees (memory : TreeFactoredMemory.State)
    (registrations : List TreeMemory.Provenance)
    (sized : TreeFactoredMemory.WellSized memory) :
    rReleaseList (TreeFactoredMemory.reify memory) registrations =
      TreeFactoredMemory.translate (fReleaseList memory registrations) := by
  induction registrations generalizing memory with
  | nil => rfl
  | cons entry suffix ih =>
      rw [rReleaseList_cons, fReleaseList_cons,
        TreeMemoryReleaseAgreement.release_agrees memory entry sized]
      have nextSized := TreeMemoryPreservation.release_preserves memory entry sized
      cases released : TreeFactoredMemory.release memory entry with
      | ok value after =>
          cases value
          have afterSized : TreeFactoredMemory.WellSized after := by
            simpa only [TreeMemoryDomain.ResultWellSized, released,
              TreeFactoredMemory.Result.residual] using nextSized
          change rReleaseList (TreeFactoredMemory.reify after) suffix =
            TreeFactoredMemory.translate (fReleaseList after suffix)
          exact ih after afterSized
      | ub fault after => rfl
      | unsupported reason after => rfl
      | noChoice after => rfl

theorem endCall_agrees (memory : TreeFactoredMemory.State)
    (extra : SuppliedFrameExtra) (sized : TreeFactoredMemory.WellSized memory) :
    rEndCall (TreeFactoredMemory.reify memory) extra =
      TreeFactoredMemory.translate (fEndCall memory extra) :=
  releaseList_agrees memory extra.protectors sized

/-- A primitive release changes only its tree map on every returned outcome.
This direct reference observation has no width or matching premise. -/
theorem rRelease_retains (memory : TreeMemory.State) (entry : TreeMemory.Provenance) :
    ((rResidual (TreeMemory.release memory entry)).raw,
      (rResidual (TreeMemory.release memory entry)).currentFrame) =
      (memory.raw, memory.currentFrame) := by
  rcases entry with ⟨id, path⟩
  cases allocationFound : memory.raw.allocations id <;>
    cases treeFound : memory.trees id
  all_goals simp only [TreeMemory.release, allocationFound, treeFound]
  all_goals try rfl
  rename_i allocation tree
  cases converted : TreeReference.unprotectAt tree path with
  | ub fault after => rfl
  | unsupported reason after => rfl
  | ok accesses convertedTree =>
      cases live : allocation.live <;> simp only [Bool.not_false, Bool.not_true,
        ite_true, Bool.false_eq_true, ite_false]
      · rfl
      · cases TreeReference.releaseTraverse convertedTree (some path) accesses with
        | ok value after => cases value; rfl
        | ub fault after => rfl
        | unsupported reason after => rfl

/-- Independent direct factored observation; no correspondence admission is
needed to observe unchanged raw memory and the recorded frame list. -/
theorem fRelease_retains (memory : TreeFactoredMemory.State)
    (entry : TreeMemory.Provenance) :
    ((fResidual (TreeFactoredMemory.release memory entry)).raw,
      (fResidual (TreeFactoredMemory.release memory entry)).currentFrame) =
      (memory.raw, memory.currentFrame) := by
  rcases entry with ⟨id, path⟩
  cases allocationFound : memory.raw.allocations id <;>
    cases treeFound : memory.trees id
  all_goals simp only [TreeFactoredMemory.release, allocationFound, treeFound]
  all_goals try rfl
  rename_i allocation tree
  cases converted : TreeFactored.unprotectAt tree path with
  | ub fault after => rfl
  | unsupported reason after => rfl
  | ok accesses convertedTree =>
      cases live : allocation.live <;> simp only [Bool.not_false, Bool.not_true,
        ite_true, Bool.false_eq_true, ite_false]
      · rfl
      · cases TreeFactored.releaseTraverse convertedTree path accesses with
        | ok value after => cases value; rfl
        | ub fault after => rfl
        | unsupported reason after => rfl

theorem rReleaseList_retains (memory : TreeMemory.State)
    (registrations : List TreeMemory.Provenance) :
    ((rResidual (rReleaseList memory registrations)).raw,
      (rResidual (rReleaseList memory registrations)).currentFrame) =
      (memory.raw, memory.currentFrame) := by
  induction registrations generalizing memory with
  | nil => rfl
  | cons entry suffix ih =>
      have retained := rRelease_retains memory entry
      cases released : TreeMemory.release memory entry with
      | ok value after =>
          cases value
          have headRetained : (after.raw, after.currentFrame) =
              (memory.raw, memory.currentFrame) := by
            simpa only [released, rResidual] using retained
          simpa only [rReleaseList, released] using (ih after).trans headRetained
      | ub fault after =>
          simpa only [rReleaseList, released, rResidual] using retained
      | unsupported reason after =>
          simpa only [rReleaseList, released, rResidual] using retained
      | noChoice after =>
          simpa only [rReleaseList, released, rResidual] using retained

theorem fReleaseList_retains (memory : TreeFactoredMemory.State)
    (registrations : List TreeMemory.Provenance) :
    ((fResidual (fReleaseList memory registrations)).raw,
      (fResidual (fReleaseList memory registrations)).currentFrame) =
      (memory.raw, memory.currentFrame) := by
  induction registrations generalizing memory with
  | nil => rfl
  | cons entry suffix ih =>
      have retained := fRelease_retains memory entry
      cases released : TreeFactoredMemory.release memory entry with
      | ok value after =>
          cases value
          have headRetained : (after.raw, after.currentFrame) =
              (memory.raw, memory.currentFrame) := by
            simpa only [released, fResidual, TreeFactoredMemory.Result.residual] using retained
          simpa only [fReleaseList, released] using (ih after).trans headRetained
      | ub fault after =>
          simpa only [fReleaseList, released, fResidual,
            TreeFactoredMemory.Result.residual] using retained
      | unsupported reason after =>
          simpa only [fReleaseList, released, fResidual,
            TreeFactoredMemory.Result.residual] using retained
      | noChoice after =>
          simpa only [fReleaseList, released, fResidual,
            TreeFactoredMemory.Result.residual] using retained

theorem rEndCall_retains (memory : TreeMemory.State) (extra : SuppliedFrameExtra) :
    ((rResidual (rEndCall memory extra)).raw,
      (rResidual (rEndCall memory extra)).currentFrame) =
      (memory.raw, memory.currentFrame) :=
  rReleaseList_retains memory extra.protectors

theorem fEndCall_retains (memory : TreeFactoredMemory.State) (extra : SuppliedFrameExtra) :
    ((fResidual (fEndCall memory extra)).raw,
      (fResidual (fEndCall memory extra)).currentFrame) =
      (memory.raw, memory.currentFrame) :=
  fReleaseList_retains memory extra.protectors

#print axioms rReleaseList_nil
#print axioms fReleaseList_nil
#print axioms rReleaseList_cons
#print axioms fReleaseList_cons
#print axioms rEndCall_eq
#print axioms fEndCall_eq
#print axioms fReleaseList_preserves
#print axioms fEndCall_preserves
#print axioms releaseList_agrees
#print axioms endCall_agrees
#print axioms rRelease_retains
#print axioms fRelease_retains
#print axioms rReleaseList_retains
#print axioms fReleaseList_retains
#print axioms rEndCall_retains
#print axioms fEndCall_retains

end AnnealResearch.TreeEndCall
