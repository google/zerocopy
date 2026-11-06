import AnnealResearch.TreeLiveKindControls
import AnnealResearch.TreeLiveMemory

/-!
Boundary controls for live-only matching. The dead Weak example follows actual
construction, store, free and release equations. A separate named mutant returns
success after actual unprotect conversion without running release traversal; it
is challenged by an actual nonempty protected construction/store history.
This mutant omits the traversal as a whole, not merely one implementation line.
-/
namespace AnnealResearch.TreeReleaseKindControls

open TreePermissions
open TreeLiveKinds (LiveKinds)

/-- The all-residual deallocation theorem transfers the established live witness
through the actual successful Weak free. -/
theorem dead_weak_liveKinds : LiveKinds TreeMemoryControls.deadWeak := by
  have preserved := TreeLiveMemory.deallocate_preserves
    (TreeMemoryControls.writeState .weak) TreeMemoryControls.t .heap 1 1
    (TreeLiveKindControls.write_live .weak rfl)
  simpa only [TreeMemoryControls.weak_used_grandchild_allows_free,
    TreeLiveMemory.ResultLiveKinds, TreeLiveMemory.residual,
    TreeMemoryControls.deadWeak] using preserved

/-- The target record is dead, so replacing its tree creates no live obligation.
Other actual live records would still have to retain their matching trees. -/
theorem dead_weak_released_liveKinds : LiveKinds TreeMemoryControls.deadWeakReleased := by
  apply TreeLiveKinds.liveKinds_setTree TreeMemoryControls.deadWeak 0
    TreeMemoryControls.treeDeadWeakReleased dead_weak_liveKinds
  intro allocation allocated alive
  have same : allocation = { TreeMemoryControls.writtenBlock with live := false } := by
    simpa [TreeMemoryControls.deadWeak, TreeMemoryControls.freed,
      MiniRustReference.replace] using allocated.symm
  subst allocation
  cases alive

theorem dead_release_keeps_live_scope :
    LiveKinds TreeMemoryControls.deadWeak ∧
    TreeMemory.release TreeMemoryControls.deadWeak (0, [0, 0]) =
      .ok () TreeMemoryControls.deadWeakReleased ∧
    LiveKinds TreeMemoryControls.deadWeakReleased ∧
    TreeReference.kindsMatch TreeMemoryControls.treeDeadWeakReleased = false :=
  ⟨dead_weak_liveKinds, TreeMemoryControls.successful_dead_weak_release,
    dead_weak_released_liveKinds,
    TreeMemoryControls.dead_weak_release_refutes_global_matching.2⟩

/-- Deliberate mutation: retain the real lookup and unprotect conversion, then
return success without release traversal. This is not an alternative semantics. -/
def releaseWithoutTraversal (state : TreeMemory.State) (provenance : TreeMemory.Provenance) :
    TreeMemory.Result Unit :=
  let (id, path) := provenance
  match state.raw.allocations id, state.trees id with
  | none, _ => .unsupported .basicRepresentation state
  | _, none => .unsupported .missingTree state
  | some _, some tree =>
    match TreeReference.unprotectAt tree path with
    | .ub fault changed => .ub (.tree fault) (TreeMemory.setTree state id changed)
    | .unsupported reason changed =>
        .unsupported (.tree reason) (TreeMemory.setTree state id changed)
    | .ok _ converted => .ok () (TreeMemory.setTree state id converted)

def omittedTree : TreeReference.Node :=
  .mk [.unprot .unique] .no
    [.mk [.unprot .unique] .no [.mk [.unprot .unique] .strong []],
      .mk [.unprot .disabled] .no []]

def omittedState : TreeMemory.State :=
  TreeMemory.setTree (TreeMemoryControls.writeState .strong) 0 omittedTree

theorem mutant_returns_mismatched_success :
    releaseWithoutTraversal (TreeMemoryControls.writeState .strong) (0, [0, 0]) =
      .ok () omittedState := by
  simp [releaseWithoutTraversal, TreeMemoryControls.writeState,
    TreeMemoryControls.readState, TreeMemoryControls.stateAB, TreeMemoryControls.stateA,
    TreeMemoryControls.initial, TreeMemoryControls.block, TreeMemoryControls.treeRead,
    TreeMemoryControls.treeAB, TreeMemoryControls.treeA, TreeMemoryControls.treeWrite,
    TreeMemory.setTree, TreeMemoryControls.writtenBlock, omittedState, omittedTree,
    MiniRustReference.replace, TreeReference.unprotectAt, TreeReference.modifyAt,
    TreeReference.unprotectPermissions, Permission.unprotect, PPermission.unprotect,
    TreeReference.Result.mapState, TreeReference.replaceNth, Protected.yes]

theorem mutant_result_not_liveKinds : ¬ LiveKinds omittedState := by
  intro matching
  have wrong := matching 0 TreeMemoryControls.writtenBlock omittedTree rfl rfl
    (by simp [omittedState, TreeMemory.setTree])
  have mismatch : TreeReference.kindsMatch omittedTree = false := by
    simp [omittedTree, TreeReference.kindsMatch, TreeReference.childrenMatch,
      Permission.matchesProtector, Permission.isProt, Protected.yes]
  rw [mismatch] at wrong
  cases wrong

/-- This witness starts from actual successful reborrow and store, with a live
size-one allocation. The real release succeeds and restores matching; the mutant
reports success while keeping a converted selected node's Strong flag. -/
theorem constructed_history_detects_omitted_traversal :
    TreeMemoryControls.constructRead .strong =
      .ok TreeMemoryControls.t (TreeMemoryControls.readState .strong) ∧
    TreeMemory.store (TreeMemoryControls.readState .strong) TreeMemoryControls.t
      [TreeMemoryControls.seven] 1 = .ok () (TreeMemoryControls.writeState .strong) ∧
    LiveKinds (TreeMemoryControls.writeState .strong) ∧
    TreeMemory.release (TreeMemoryControls.writeState .strong) (0, [0, 0]) =
      .ok () TreeMemoryControls.releasedState ∧
    LiveKinds TreeMemoryControls.releasedState ∧
    releaseWithoutTraversal (TreeMemoryControls.writeState .strong) (0, [0, 0]) =
      .ok () omittedState ∧ ¬ LiveKinds omittedState :=
  ⟨TreeMemoryControls.full_strong_construction, TreeMemoryControls.actual_strong_write,
    TreeLiveKindControls.write_live .strong rfl, TreeMemoryControls.successful_live_release,
    TreeLiveKindControls.released_live, mutant_returns_mismatched_success,
    mutant_result_not_liveKinds⟩

#print axioms dead_weak_liveKinds
#print axioms dead_weak_released_liveKinds
#print axioms dead_release_keeps_live_scope
#print axioms mutant_returns_mismatched_success
#print axioms mutant_result_not_liveKinds
#print axioms constructed_history_detects_omitted_traversal

end AnnealResearch.TreeReleaseKindControls
