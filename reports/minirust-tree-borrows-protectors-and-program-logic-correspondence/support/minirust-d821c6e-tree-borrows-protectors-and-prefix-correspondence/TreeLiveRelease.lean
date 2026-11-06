import AnnealResearch.TreeUnprotectKinds
import AnnealResearch.TreeLiveMemory

/-!
Stable-running matching for the actual recursive-reference memory release.
RunningKinds requires LiveKinds only for ok results. Terminal UB, unsupported,
and noChoice retain their exact original result/residual without a matching
obligation; the observer does not repair or erase any result.

Only input LiveKinds is assumed. Actual release branches determine whether the
selected allocation is dead or live. Dead-tree replacement has no selected live
obligation. A successful live release executes unprotectAt and releaseTraverse;
their checked query equality restores matching. No path, width, access-success,
NoUB, StateWF or liveness admission is imposed on the public theorem.
-/

namespace AnnealResearch.TreeLiveRelease

open TreeMemory (State Pointer Tree Provenance)
open TreeLiveKinds (LiveKinds)

/-- Matching at stable running boundaries; every terminal result is explicit.
This predicate imposes no safety, termination, progress or frame obligation. -/
def RunningKinds : TreeMemory.Result A → Prop
  | .ok _ state => LiveKinds state
  | .ub _ _ => True
  | .unsupported _ _ => True
  | .noChoice _ => True

/-- An arbitrary replacement at an actually dead allocation cannot violate the
live-only predicate. Other live IDs still use the original invariant. -/
theorem liveKinds_setTree_dead (state : State) (id : Nat)
    (allocation : MiniRustReference.Allocation) (tree : Tree)
    (matching : LiveKinds state) (found : state.raw.allocations id = some allocation)
    (dead : allocation.live = false) : LiveKinds (TreeMemory.setTree state id tree) := by
  apply TreeLiveKinds.liveKinds_setTree state id tree matching
  intro actual actualFound alive
  have sameAllocation : allocation = actual := Option.some.inj (found.symm.trans actualFound)
  have impossible : false = true := dead.symm.trans
    ((congrArg MiniRustReference.Allocation.live sameAllocation).trans alive)
  cases impossible

/-- The already checked all-residual property is stronger than RunningKinds. -/
theorem resultLiveKinds_implies_runningKinds (answer : TreeMemory.Result A)
    (matching : TreeLiveMemory.ResultLiveKinds answer) : RunningKinds answer := by
  cases answer with
  | ok value state => exact matching
  | ub fault state => exact True.intro
  | unsupported reason state => exact True.intro
  | noChoice state => exact True.intro

/-- Actual release, from input LiveKinds alone. The success equations below are
obtained by inspecting execution; they are not premises on the public caller. -/
theorem release_preserves (state : State) (provenance : Provenance)
    (matching : LiveKinds state) : RunningKinds (TreeMemory.release state provenance) := by
  rcases provenance with ⟨id, path⟩
  unfold TreeMemory.release
  dsimp only
  cases rawFound : state.raw.allocations id with
  | none => exact True.intro
  | some allocation =>
    cases present : state.trees id with
    | none => exact True.intro
    | some tree =>
      dsimp only
      cases converted : TreeReference.unprotectAt tree path with
      | ub fault changed => exact True.intro
      | unsupported reason changed => exact True.intro
      | ok accesses convertedTree =>
        dsimp only
        cases alive : allocation.live with
        | false =>
          exact liveKinds_setTree_dead state id allocation convertedTree matching rawFound alive
        | true =>
          cases traversed : TreeReference.releaseTraverse convertedTree (some path) accesses with
          | ub fault changed => exact True.intro
          | unsupported reason changed => exact True.intro
          | ok result changed =>
            cases result
            have preserved : TreeReference.kindsMatch changed = TreeReference.kindsMatch tree :=
              TreeUnprotectKinds.unprotect_release_success_matching
                tree path accesses convertedTree changed converted traversed
            exact TreeLiveKinds.liveKinds_replace_tree state id tree changed matching present preserved

theorem load_preserves (state : State) (pointer : Pointer) (size align : Nat)
    (matching : LiveKinds state) : RunningKinds (TreeMemory.load state pointer size align) :=
  resultLiveKinds_implies_runningKinds _ (TreeLiveMemory.load_preserves state pointer size align matching)

theorem store_preserves (state : State) (pointer : Pointer) (bytes : List MiniRustReference.Byte)
    (align : Nat) (matching : LiveKinds state) : RunningKinds (TreeMemory.store state pointer bytes align) :=
  resultLiveKinds_implies_runningKinds _ (TreeLiveMemory.store_preserves state pointer bytes align matching)

theorem deallocate_preserves (state : State) (pointer : Pointer) (kind : MiniRustReference.Kind)
    (size align : Nat) (matching : LiveKinds state) :
    RunningKinds (TreeMemory.deallocate state pointer kind size align) :=
  resultLiveKinds_implies_runningKinds _
    (TreeLiveMemory.deallocate_preserves state pointer kind size align matching)

#print axioms liveKinds_setTree_dead
#print axioms resultLiveKinds_implies_runningKinds
#print axioms release_preserves
#print axioms load_preserves
#print axioms store_preserves
#print axioms deallocate_preserves

end AnnealResearch.TreeLiveRelease
