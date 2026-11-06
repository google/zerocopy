import AnnealResearch.TreeReborrowKinds
import AnnealResearch.TreeReborrowAgreement
import AnnealResearch.TreeMemoryOperations
import AnnealResearch.TreeMemoryReleaseAgreement

/-!
Matching transfer to the unchanged actual factored-memory operations, using the
checked exact full-result correspondences. Only WellSized and live matching
are assumed publicly. The tree runners remain independently implemented; this
module introduces observers and proof transport, not another operation runner.

Load/store/deallocate/reborrow retain the stronger all-residual predicate.
Release has only stable-success RunningKinds: its terminal residuals remain
exactly the existing operation results without a matching obligation. No path,
settings compatibility, scalar success, reachability or NoUB premise is added.
-/

namespace AnnealResearch.TreeLiveTransfer

open TreeFactoredMemory (State Pointer Provenance)

/-- Matching concerns represented trees at actual live allocation records.
Reification imposes no condition on absent-path cells of the total store. -/
def LiveKinds (state : State) : Prop :=
  TreeLiveKinds.LiveKinds (TreeFactoredMemory.reify state)

/-- Every actual factored result retains its own residual, explicitly. -/
def residual : TreeFactoredMemory.Result A → State
  | .ok _ state => state
  | .ub _ state => state
  | .unsupported _ state => state
  | .noChoice state => state

def ResultLiveKinds (answer : TreeFactoredMemory.Result A) : Prop := LiveKinds (residual answer)

/-- Stable-running observer, with no matching obligation at terminal results.
It changes neither the original outcome nor any residual state or diagnostic. -/
def RunningKinds : TreeFactoredMemory.Result A → Prop
  | .ok _ state => LiveKinds state
  | .ub _ _ => True
  | .unsupported _ _ => True
  | .noChoice _ => True

theorem residual_translate (answer : TreeFactoredMemory.Result A) :
    TreeLiveMemory.residual (TreeFactoredMemory.translate answer) =
      TreeFactoredMemory.reify (residual answer) := by
  cases answer <;> rfl

theorem resultLiveKinds_translate (answer : TreeFactoredMemory.Result A) :
    TreeLiveMemory.ResultLiveKinds (TreeFactoredMemory.translate answer) ↔
      ResultLiveKinds answer := by
  cases answer <;> rfl

theorem runningKinds_translate (answer : TreeFactoredMemory.Result A) :
    TreeLiveRelease.RunningKinds (TreeFactoredMemory.translate answer) ↔
      RunningKinds answer := by
  cases answer <;> rfl

theorem resultLiveKinds_implies_runningKinds (answer : TreeFactoredMemory.Result A)
    (matching : ResultLiveKinds answer) : RunningKinds answer := by
  cases answer with
  | ok value state => exact matching
  | ub fault state => exact True.intro
  | unsupported reason state => exact True.intro
  | noChoice state => exact True.intro

/-- Existing exact load correspondence transports the stronger reference
all-residual property. All raw/tree failure categories remain present. -/
theorem load_preserves_all (state : State) (pointer : Pointer) (size align : Nat)
    (sized : TreeFactoredMemory.WellSized state) (matching : LiveKinds state) :
    ResultLiveKinds (TreeFactoredMemory.load state pointer size align) := by
  have reference := TreeLiveMemory.load_preserves
    (TreeFactoredMemory.reify state) pointer size align matching
  rw [TreeMemoryOperations.load_agrees state pointer size align sized] at reference
  exact (resultLiveKinds_translate _).mp reference

theorem store_preserves_all (state : State) (pointer : Pointer)
    (bytes : List MiniRustReference.Byte) (align : Nat)
    (sized : TreeFactoredMemory.WellSized state) (matching : LiveKinds state) :
    ResultLiveKinds (TreeFactoredMemory.store state pointer bytes align) := by
  have reference := TreeLiveMemory.store_preserves
    (TreeFactoredMemory.reify state) pointer bytes align matching
  rw [TreeMemoryOperations.store_agrees state pointer bytes align sized] at reference
  exact (resultLiveKinds_translate _).mp reference

theorem deallocate_preserves_all (state : State) (pointer : Pointer)
    (kind : MiniRustReference.Kind) (size align : Nat)
    (sized : TreeFactoredMemory.WellSized state) (matching : LiveKinds state) :
    ResultLiveKinds (TreeFactoredMemory.deallocate state pointer kind size align) := by
  have reference := TreeLiveMemory.deallocate_preserves
    (TreeFactoredMemory.reify state) pointer kind size align matching
  rw [TreeMemoryOperations.deallocate_agrees state pointer kind size align sized] at reference
  exact (resultLiveKinds_translate _).mp reference

/-- Actual independent insertion and initial-access correspondence includes
partial tree commits, unchanged raw state and successful frame registration. -/
theorem reborrow_preserves_all (state : State) (pointer : Pointer)
    (settings : TreeMemory.Settings)
    (sized : TreeFactoredMemory.WellSized state) (matching : LiveKinds state) :
    ResultLiveKinds (TreeFactoredMemory.reborrow state pointer settings) := by
  have reference := TreeReborrowKinds.reborrow_preserves_all
    (TreeFactoredMemory.reify state) pointer settings matching
  rw [TreeReborrowAgreement.reborrow_agrees state pointer settings sized] at reference
  exact (resultLiveKinds_translate _).mp reference

/-- Release deliberately uses only the stable-success observer. Actual live
conversion followed by terminal failure can leave a nonmatching residual. -/
theorem release_preserves (state : State) (provenance : Provenance)
    (sized : TreeFactoredMemory.WellSized state) (matching : LiveKinds state) :
    RunningKinds (TreeFactoredMemory.release state provenance) := by
  have reference := TreeLiveRelease.release_preserves
    (TreeFactoredMemory.reify state) provenance matching
  rw [TreeMemoryReleaseAgreement.release_agrees state provenance sized] at reference
  exact (runningKinds_translate _).mp reference

#print axioms residual_translate
#print axioms resultLiveKinds_translate
#print axioms runningKinds_translate
#print axioms resultLiveKinds_implies_runningKinds
#print axioms load_preserves_all
#print axioms store_preserves_all
#print axioms deallocate_preserves_all
#print axioms reborrow_preserves_all
#print axioms release_preserves

end AnnealResearch.TreeLiveTransfer
