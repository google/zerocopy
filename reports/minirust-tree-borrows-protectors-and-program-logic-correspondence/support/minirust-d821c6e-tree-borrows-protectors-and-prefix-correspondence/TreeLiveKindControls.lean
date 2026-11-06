import AnnealResearch.TreeLiveKinds
import AnnealResearch.TreeMemoryPairing

/-!
Constructed live witnesses and counterexamples separate matching from safety,
all-residual release invariants, and global matching of dead trees. The Frozen
release failure is explicitly shape-only. Earlier independent reference equations
supply the actual reborrow/store/release/free histories; no state is extracted
from an assumed success with a default.
-/
namespace AnnealResearch.TreeLiveKindControls

open TreePermissions
open TreeLiveKinds (LiveKinds)

/-- A fixture helper, stronger than needed by LiveKinds. It is not admission for
the general operation theorems. Actual live/nonempty records are witnessed below. -/
theorem single_tree_live (state : TreeMemory.State) (expected : TreeReference.Node)
    (trees : ∀ id, state.trees id = if id = 0 then some expected else none)
    (matching : TreeReference.kindsMatch expected = true) : LiveKinds state := by
  intro id allocation tree allocated alive found
  rw [trees id] at found
  by_cases zero : id = 0
  · subst id
    simp at found
    subst tree
    exact matching
  · simp [zero] at found

theorem read_live (protection : Protected) (yes : protection.yes = true) :
    LiveKinds (TreeMemoryControls.readState protection) := by
  apply single_tree_live _ (TreeMemoryControls.treeRead protection)
  · intro id
    by_cases zero : id = 0 <;>
      simp [TreeMemoryControls.readState, TreeMemoryControls.stateAB,
        TreeMemoryControls.stateA, TreeMemoryControls.initial, TreeMemory.setTree, zero]
  · rw [← TreePairing.read_reify protection, TreeQueries.kindsMatch_reify,
      TreePairing.read_kind_query]
    exact yes

theorem write_live (protection : Protected) (yes : protection.yes = true) :
    LiveKinds (TreeMemoryControls.writeState protection) := by
  apply single_tree_live _ (TreeMemoryControls.treeWrite protection)
  · intro id
    by_cases zero : id = 0 <;>
      simp [TreeMemoryControls.writeState, TreeMemoryControls.readState,
        TreeMemoryControls.stateAB, TreeMemoryControls.stateA,
        TreeMemoryControls.initial, TreeMemory.setTree, zero]
  · rw [← TreePairing.write_reify protection, TreeQueries.kindsMatch_reify,
      TreePairing.write_kind_query]
    exact yes

theorem released_live : LiveKinds TreeMemoryControls.releasedState := by
  apply TreeLiveKinds.liveKinds_setTree
    (TreeMemoryControls.writeState .strong) 0 TreeMemoryControls.treeReleased
    (write_live .strong rfl)
  intro allocation allocated alive
  simp [TreeMemoryControls.treeReleased, TreeReference.kindsMatch,
    TreeReference.childrenMatch, Permission.matchesProtector, Permission.isProt, Protected.yes]

/-- Matching has a present live size-one allocation and an actually constructed
protected tree here, rather than only vacuous missing/dead/empty obligations. -/
theorem constructed_nonempty_live :
    TreeMemoryControls.constructRead .strong =
      .ok TreeMemoryControls.t (TreeMemoryControls.readState .strong) ∧
    LiveKinds (TreeMemoryControls.readState .strong) ∧
    (TreeMemoryControls.readState .strong).raw.allocations 0 =
      some (TreeMemoryControls.block 1) ∧
    (TreeMemoryControls.block 1).live = true ∧
    (TreeMemoryControls.readState .strong).trees 0 =
      some (TreeMemoryControls.treeRead .strong) ∧
    (TreeMemoryControls.treeRead .strong).permissions.length = 1 := by
  refine ⟨TreeMemoryControls.full_strong_construction, read_live .strong rfl,
    rfl, rfl, ?_, rfl⟩
  simp [TreeMemoryControls.readState, TreeMemory.setTree]

theorem actual_successful_live_history :
    TreeMemory.store (TreeMemoryControls.readState .strong) TreeMemoryControls.t
      [TreeMemoryControls.seven] 1 = .ok () (TreeMemoryControls.writeState .strong) ∧
    LiveKinds (TreeMemoryControls.writeState .strong) ∧
    TreeMemory.release (TreeMemoryControls.writeState .strong) (0, [0, 0]) =
      .ok () TreeMemoryControls.releasedState ∧
    LiveKinds TreeMemoryControls.releasedState ∧
    TreeMemory.deallocate TreeMemoryControls.releasedState TreeMemoryControls.t .heap 1 1 =
      .ok () (TreeMemoryControls.freed TreeMemoryControls.releasedState
        TreeMemoryControls.treeReleased TreeMemoryControls.writtenBlock) :=
  ⟨TreeMemoryControls.actual_strong_write, write_live .strong rfl,
    TreeMemoryControls.successful_live_release, released_live,
    TreeMemoryControls.free_after_release⟩

theorem shape_failure_initially_liveKinds : LiveKinds TreeMemoryControls.liveFailure := by
  apply single_tree_live _ TreeMemoryControls.liveFailureTree
  · intro id
    by_cases zero : id = 0 <;>
      simp [TreeMemoryControls.liveFailure, TreeMemoryControls.initial, TreeMemory.setTree, zero]
  · exact TreeMemoryControls.live_failure_matching_scope.2.1

def failedState : TreeMemory.State :=
  TreeMemory.setTree TreeMemoryControls.liveFailure 0 TreeMemoryControls.liveFailureConverted

theorem failed_release_not_liveKinds : ¬ LiveKinds failedState := by
  intro matching
  have wrong := matching 0 (TreeMemoryControls.block 1)
    TreeMemoryControls.liveFailureConverted rfl rfl (by simp [failedState, TreeMemory.setTree])
  have mismatch : TreeReference.kindsMatch TreeMemoryControls.liveFailureConverted = false :=
    TreeMemoryControls.live_failure_matching_scope.2.2
  rw [mismatch] at wrong
  cases wrong

theorem actual_release_refutes_all_residual_matching :
    LiveKinds TreeMemoryControls.liveFailure ∧
    TreeMemory.release TreeMemoryControls.liveFailure (0, [0]) =
      .ub (.tree .unprotectedLocalWriteFrozen) failedState ∧
    ¬ LiveKinds failedState :=
  ⟨shape_failure_initially_liveKinds,
    TreeMemoryControls.live_failed_release_commits_conversion, failed_release_not_liveKinds⟩

theorem two_byte_liveKinds : LiveKinds TreeMemoryControls.twoRead := by
  apply single_tree_live _ TreeMemoryControls.twoTree
  · intro id
    by_cases zero : id = 0 <;>
      simp [TreeMemoryControls.twoRead, TreeMemoryControls.initial, TreeMemory.setTree, zero]
  · simp [TreeMemoryControls.twoTree, TreeReference.kindsMatch,
    TreeReference.childrenMatch, Permission.matchesProtector, Permission.isProt, Protected.yes]

/-- This failure has an actual successful reborrow history. Matching is not NoUB. -/
theorem constructed_store_UB_despite_matching :
    TreeMemory.reborrow (TreeMemoryControls.initial 2) TreeMemoryControls.twoPointer
      (TreeMemoryControls.protectedMutable .strong) =
      .ok TreeMemoryControls.twoChild TreeMemoryControls.twoRead ∧
    LiveKinds TreeMemoryControls.twoRead ∧
    TreeMemory.store TreeMemoryControls.twoRead TreeMemoryControls.root
      [TreeMemoryControls.seven, TreeMemoryControls.seven] 1 =
      .ub (.tree .protectedForeignWriteReservedAfterLocalRead) TreeMemoryControls.twoRead :=
  ⟨TreeMemoryControls.construct_two_byte_history, two_byte_liveKinds,
    TreeMemoryControls.two_byte_public_store_rolls_back⟩

#print axioms single_tree_live
#print axioms read_live
#print axioms write_live
#print axioms released_live
#print axioms constructed_nonempty_live
#print axioms actual_successful_live_history
#print axioms shape_failure_initially_liveKinds
#print axioms failed_release_not_liveKinds
#print axioms actual_release_refutes_all_residual_matching
#print axioms two_byte_liveKinds
#print axioms constructed_store_UB_despite_matching

end AnnealResearch.TreeLiveKindControls
