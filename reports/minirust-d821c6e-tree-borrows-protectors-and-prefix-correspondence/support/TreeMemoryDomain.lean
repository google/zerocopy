import AnnealResearch.TreeRawGeometry
import AnnealResearch.TreeFactoredMemory
import AnnealResearch.TreeUnprotectWidths

/-!
Transport of the existing WellSized domain, before wrapper closure proofs.
Only raw option-size maps, actual per-ID tree widths, and tree topology/list
lengths are used. Permission values, flags, liveness and safety are absent from
the domain. No runner or existing admission definition is changed.
-/

namespace AnnealResearch.TreeFactoredMemory

/-- Observe every returned residual state, without filtering terminal outcomes. -/
def Result.residual : Result A → State
  | .ok _ state => state
  | .ub _ state => state
  | .unsupported _ state => state
  | .noChoice state => state

end AnnealResearch.TreeFactoredMemory

namespace AnnealResearch.TreeMemoryDomain

open TreeFactoredMemory (State Tree)

def ResultWellSized (answer : TreeFactoredMemory.Result A) : Prop :=
  TreeFactoredMemory.WellSized answer.residual

/-- This is a sufficient structural transport relation. Its all-query length
condition also constrains absent total-store cells; semantic representation
agreement still ignores those cells. Actual frozen workers preserve them too. -/
def SameTreeGeometry (before after : Tree) : Prop :=
  after.topology = before.topology ∧
    ∀ query, (after.store query).permissions.length = (before.store query).permissions.length

theorem uniform_of_same_geometry (before after : Tree) (width : Nat)
    (same : SameTreeGeometry before after)
    (uniform : TreeFactored.arrayLengthsTree before.topology [] before.store width = true) :
    TreeFactored.arrayLengthsTree after.topology [] after.store width = true := by
  rw [same.1]
  rw [TreeUnprotectWidths.arrayLengthsTree_congr_lengths before.topology []
    after.store before.store width same.2]
  exact uniform

/-- The option-size map includes both record presence and size, so each actual
new raw record has an old record whose width premise can be transported. -/
theorem wellSized_with_raw (state : State) (raw : MiniRustReference.State)
    (sized : TreeFactoredMemory.WellSized state)
    (same : TreeRawGeometry.SameSizeMap state.raw raw) :
    TreeFactoredMemory.WellSized { state with raw } := by
  intro id allocation tree rawFound treeFound
  obtain ⟨old, oldFound, sameSize⟩ := TreeRawGeometry.sameSizeMap_lookup
    (TreeRawGeometry.sameSizeMap_symm same) id allocation rawFound
  have width := sized id old tree oldFound treeFound
  simpa only [sameSize] using width

/-- A local replacement needs its width at the actual raw record only. If no
record exists at this ID the existing conditional domain adds no obligation. -/
theorem wellSized_setTree (state : State) (id : Nat) (tree : Tree)
    (sized : TreeFactoredMemory.WellSized state)
    (localWidth : ∀ allocation, state.raw.allocations id = some allocation →
      TreeFactored.arrayLengthsTree tree.topology [] tree.store allocation.size = true) :
    TreeFactoredMemory.WellSized (TreeFactoredMemory.setTree state id tree) := by
  intro selected allocation selectedTree rawFound treeFound
  by_cases sameId : selected = id
  · subst selected
    have sameTree : tree = selectedTree := by
      simpa [TreeFactoredMemory.setTree] using treeFound
    subst selectedTree
    exact localWidth allocation rawFound
  · have oldTree : state.trees selected = some selectedTree := by
      simpa only [TreeFactoredMemory.setTree, ite_eq_right sameId] using treeFound
    exact sized selected allocation selectedTree rawFound oldTree

/-- An actual existing tree can be replaced using only its structural geometry;
its permission values/protector flags may change, including on returned UB. -/
theorem wellSized_replace_tree (state : State) (id : Nat) (before after : Tree)
    (sized : TreeFactoredMemory.WellSized state)
    (present : state.trees id = some before) (same : SameTreeGeometry before after) :
    TreeFactoredMemory.WellSized (TreeFactoredMemory.setTree state id after) := by
  apply wellSized_setTree state id after sized
  intro allocation rawFound
  exact uniform_of_same_geometry before after allocation.size same
    (sized id allocation before rawFound present)

theorem wellSized_commit (state : State) (id : Nat) (before after : Tree)
    (raw : MiniRustReference.State) (sized : TreeFactoredMemory.WellSized state)
    (present : state.trees id = some before) (geometry : SameTreeGeometry before after)
    (rawSizes : TreeRawGeometry.SameSizeMap state.raw raw) :
    TreeFactoredMemory.WellSized { TreeFactoredMemory.setTree state id after with raw } := by
  exact wellSized_with_raw (TreeFactoredMemory.setTree state id after) raw
    (wellSized_replace_tree state id before after sized present geometry) rawSizes

theorem wellSized_with_frame (state : State) (frame : List TreeFactoredMemory.Provenance)
    (sized : TreeFactoredMemory.WellSized state) :
    TreeFactoredMemory.WellSized { state with currentFrame := frame } := sized

#print axioms TreeFactoredMemory.Result.residual
#print axioms uniform_of_same_geometry
#print axioms wellSized_with_raw
#print axioms wellSized_setTree
#print axioms wellSized_replace_tree
#print axioms wellSized_commit
#print axioms wellSized_with_frame

end AnnealResearch.TreeMemoryDomain
