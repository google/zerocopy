import AnnealResearch.TreeEndCall
import AnnealResearch.TreeLiveRelease
import AnnealResearch.TreeLiveTransfer
import AnnealResearch.TreeAllocationDomain

/-!
Append/first-error laws for the actual finite ordered release folds, natural
reference-width transport, and separate successful stable matching. No public
agreement premise is strengthened. Terminal partial memories need not match.
These laws do not turn a propagated error into an operational continuation.
-/
namespace AnnealResearch.TreeEndCallProperties

open TreeEndCall

def rThen (answer : TreeMemory.Result Unit)
    (next : TreeMemory.State → TreeMemory.Result Unit) : TreeMemory.Result Unit :=
  match answer with
  | .ok () memory => next memory
  | .ub fault memory => .ub fault memory
  | .unsupported why memory => .unsupported why memory
  | .noChoice memory => .noChoice memory

def fThen (answer : TreeFactoredMemory.Result Unit)
    (next : TreeFactoredMemory.State → TreeFactoredMemory.Result Unit) :
    TreeFactoredMemory.Result Unit :=
  match answer with
  | .ok () memory => next memory
  | .ub fault memory => .ub fault memory
  | .unsupported why memory => .unsupported why memory
  | .noChoice memory => .noChoice memory

theorem rReleaseList_append (memory : TreeMemory.State)
    (front suffix : List TreeMemory.Provenance) :
    rReleaseList memory (front ++ suffix) =
      rThen (rReleaseList memory front) (fun after => rReleaseList after suffix) := by
  induction front generalizing memory with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.cons_append, rReleaseList]
    cases released : TreeMemory.release memory entry with
    | ok value after => cases value; exact ih after
    | ub fault after => rfl
    | unsupported why after => rfl
    | noChoice after => rfl

theorem fReleaseList_append (memory : TreeFactoredMemory.State)
    (front suffix : List TreeMemory.Provenance) :
    fReleaseList memory (front ++ suffix) =
      fThen (fReleaseList memory front) (fun after => fReleaseList after suffix) := by
  induction front generalizing memory with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.cons_append, fReleaseList]
    cases released : TreeFactoredMemory.release memory entry with
    | ok value after => cases value; exact ih after
    | ub fault after => rfl
    | unsupported why after => rfl
    | noChoice after => rfl

theorem r_ub_suffix (memory after : TreeMemory.State)
    (front suffix : List TreeMemory.Provenance) (fault : TreeMemory.Fault)
    (failed : rReleaseList memory front = .ub fault after) :
    rReleaseList memory (front ++ suffix) = .ub fault after := by
  rw [rReleaseList_append, failed]
  rfl

theorem r_unsupported_suffix (memory after : TreeMemory.State)
    (front suffix : List TreeMemory.Provenance) (why : TreeMemory.Unsupported)
    (failed : rReleaseList memory front = .unsupported why after) :
    rReleaseList memory (front ++ suffix) = .unsupported why after := by
  rw [rReleaseList_append, failed]
  rfl

theorem r_noChoice_suffix (memory after : TreeMemory.State)
    (front suffix : List TreeMemory.Provenance)
    (absent : rReleaseList memory front = .noChoice after) :
    rReleaseList memory (front ++ suffix) = .noChoice after := by
  rw [rReleaseList_append, absent]
  rfl

theorem f_ub_suffix (memory after : TreeFactoredMemory.State)
    (front suffix : List TreeMemory.Provenance) (fault : TreeMemory.Fault)
    (failed : fReleaseList memory front = .ub fault after) :
    fReleaseList memory (front ++ suffix) = .ub fault after := by
  rw [fReleaseList_append, failed]
  rfl

theorem f_unsupported_suffix (memory after : TreeFactoredMemory.State)
    (front suffix : List TreeMemory.Provenance) (why : TreeMemory.Unsupported)
    (failed : fReleaseList memory front = .unsupported why after) :
    fReleaseList memory (front ++ suffix) = .unsupported why after := by
  rw [fReleaseList_append, failed]
  rfl

theorem f_noChoice_suffix (memory after : TreeFactoredMemory.State)
    (front suffix : List TreeMemory.Provenance)
    (absent : fReleaseList memory front = .noChoice after) :
    fReleaseList memory (front ++ suffix) = .noChoice after := by
  rw [fReleaseList_append, absent]
  rfl

/-- Success/failure equations are actual execution observations, not stronger
admission for generic operation correspondence. Every suffix is skipped. -/
theorem r_success_then_UB (memory middle after : TreeMemory.State)
    (front suffix : List TreeMemory.Provenance) (entry : TreeMemory.Provenance)
    (fault : TreeMemory.Fault)
    (success : rReleaseList memory front = .ok () middle)
    (failed : TreeMemory.release middle entry = .ub fault after) :
    rReleaseList memory (front ++ entry :: suffix) = .ub fault after := by
  rw [rReleaseList_append, success]
  change rReleaseList middle (entry :: suffix) = .ub fault after
  simp only [rReleaseList, failed]

theorem f_success_then_UB (memory middle after : TreeFactoredMemory.State)
    (front suffix : List TreeMemory.Provenance) (entry : TreeMemory.Provenance)
    (fault : TreeMemory.Fault)
    (success : fReleaseList memory front = .ok () middle)
    (failed : TreeFactoredMemory.release middle entry = .ub fault after) :
    fReleaseList memory (front ++ entry :: suffix) = .ub fault after := by
  rw [fReleaseList_append, success]
  change fReleaseList middle (entry :: suffix) = .ub fault after
  simp only [fReleaseList, failed]

/-- Reference closure uses exact encoding and the checked F all-result domain.
Natural R width is the only input predicate; proof transport is explicit. -/
theorem rReleaseList_preserves (memory : TreeMemory.State)
    (registrations : List TreeMemory.Provenance)
    (sized : TreeMemoryEncoding.RWellSized memory) :
    TreeAllocationDomain.RResultWellSized (rReleaseList memory registrations) := by
  have encodedSized := (TreeMemoryEncoding.wellSized_encode_iff memory).1 sized
  have preserved := fReleaseList_preserves (TreeMemoryEncoding.encodeMemory memory)
    registrations encodedSized
  have translated := (TreeAllocationDomain.resultWellSized_translate _).2 preserved
  have agreement := releaseList_agrees (TreeMemoryEncoding.encodeMemory memory)
    registrations encodedSized
  rw [TreeMemoryEncoding.reify_encode_memory] at agreement
  rw [← agreement] at translated
  exact translated

theorem rEndCall_preserves (memory : TreeMemory.State) (extra : SuppliedFrameExtra)
    (sized : TreeMemoryEncoding.RWellSized memory) :
    TreeAllocationDomain.RResultWellSized (rEndCall memory extra) :=
  rReleaseList_preserves memory extra.protectors sized

/-- Successful running boundaries only. An ordinary failed release may leave
a live flag/permission mismatch in its exact terminal residual. -/
theorem rReleaseList_matching (memory : TreeMemory.State)
    (registrations : List TreeMemory.Provenance)
    (matching : TreeLiveKinds.LiveKinds memory) :
    TreeLiveRelease.RunningKinds (rReleaseList memory registrations) := by
  induction registrations generalizing memory with
  | nil => exact matching
  | cons entry rest ih =>
    have headMatching := TreeLiveRelease.release_preserves memory entry matching
    unfold rReleaseList
    cases released : TreeMemory.release memory entry with
    | ok value after =>
      cases value
      have afterMatching : TreeLiveKinds.LiveKinds after := by
        simpa only [released, TreeLiveRelease.RunningKinds] using headMatching
      exact ih after afterMatching
    | ub fault after => exact True.intro
    | unsupported why after => exact True.intro
    | noChoice after => exact True.intro

theorem rEndCall_matching (memory : TreeMemory.State) (extra : SuppliedFrameExtra)
    (matching : TreeLiveKinds.LiveKinds memory) :
    TreeLiveRelease.RunningKinds (rEndCall memory extra) :=
  rReleaseList_matching memory extra.protectors matching

/-- F executes its own fold. Matching proof investment is shared through the
only-width full-result correspondence, with matching a separate premise. -/
theorem fReleaseList_matching (memory : TreeFactoredMemory.State)
    (registrations : List TreeMemory.Provenance)
    (sized : TreeFactoredMemory.WellSized memory)
    (matching : TreeLiveTransfer.LiveKinds memory) :
    TreeLiveTransfer.RunningKinds (fReleaseList memory registrations) := by
  have reference := rReleaseList_matching (TreeFactoredMemory.reify memory)
    registrations matching
  rw [releaseList_agrees memory registrations sized] at reference
  exact (TreeLiveTransfer.runningKinds_translate _).1 reference

theorem fEndCall_matching (memory : TreeFactoredMemory.State) (extra : SuppliedFrameExtra)
    (sized : TreeFactoredMemory.WellSized memory)
    (matching : TreeLiveTransfer.LiveKinds memory) :
    TreeLiveTransfer.RunningKinds (fEndCall memory extra) :=
  fReleaseList_matching memory extra.protectors sized matching

#print axioms rReleaseList_append
#print axioms fReleaseList_append
#print axioms r_ub_suffix
#print axioms r_unsupported_suffix
#print axioms r_noChoice_suffix
#print axioms f_ub_suffix
#print axioms f_unsupported_suffix
#print axioms f_noChoice_suffix
#print axioms r_success_then_UB
#print axioms f_success_then_UB
#print axioms rReleaseList_preserves
#print axioms rEndCall_preserves
#print axioms rReleaseList_matching
#print axioms rEndCall_matching
#print axioms fReleaseList_matching
#print axioms fEndCall_matching

end AnnealResearch.TreeEndCallProperties
