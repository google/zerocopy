import AnnealResearch.TreeEncoding
import AnnealResearch.TreeFactoredMemory
import AnnealResearch.TreeQueries

/-!
Coverage of every owned recursive memory state by the existing factored memory
representation. Raw state and frame list are copied exactly; optional trees are
mapped at every allocation ID, independently of raw-record presence or liveness.
The representation theorem has no admission, reachability or NoUB premise.

RWellSized merely states the natural reference form of the existing paired
allocation/tree width domain. Its equivalence below neither adds a safety guard
nor removes the separate structural domain of operational correspondence.
No prefix-controller layer or source/helper adequacy theorem is imported.
-/

namespace AnnealResearch.TreeMemoryEncoding

def encodeMemory (state : TreeMemory.State) : TreeFactoredMemory.State :=
  { raw := state.raw
    trees := fun id => (state.trees id).map TreeEncoding.encode
    currentFrame := state.currentFrame }

theorem encodeMemory_raw (state : TreeMemory.State) :
    (encodeMemory state).raw = state.raw := rfl

theorem encodeMemory_frame (state : TreeMemory.State) :
    (encodeMemory state).currentFrame = state.currentFrame := rfl

theorem encodeMemory_tree (state : TreeMemory.State) (id : Nat) :
    (encodeMemory state).trees id = (state.trees id).map TreeEncoding.encode := rfl

/-- Every field and every ID reconstruct exactly, even with absent/mismatched
raw/tree records, dead records, arbitrary bytes, or arbitrary frame obligations. -/
theorem reify_encode_memory (state : TreeMemory.State) :
    TreeFactoredMemory.reify (encodeMemory state) = state := by
  cases state with
  | mk raw trees frame =>
    have treeRoundtrip :
        (fun id => ((trees id).map TreeEncoding.encode).map TreeCorrespondence.reify) = trees := by
      funext id
      cases trees id with
      | none => rfl
      | some node => exact congrArg Option.some (TreeEncoding.reify_encode node)
    change TreeMemory.State.mk raw
      (fun id => ((trees id).map TreeEncoding.encode).map TreeCorrespondence.reify) frame =
        TreeMemory.State.mk raw trees frame
    rw [treeRoundtrip]

theorem related_encode_memory (state : TreeMemory.State) :
    TreeFactoredMemory.Related state (encodeMemory state) := (reify_encode_memory state).symm

/-- Exact Boolean query equality for every width, including false queries on
nonuniform trees. No width premise is needed for encoding or this equality. -/
theorem arraysSized_encode (node : TreeReference.Node) (width : Nat) :
    TreeReference.arraysSized node width =
      TreeFactored.arrayLengthsTree (TreeEncoding.encode node).topology []
        (TreeEncoding.encode node).store width := by
  have query := TreeQueries.arraysSized_reify (TreeEncoding.encode node) width
  rw [TreeEncoding.reify_encode] at query
  exact query

/-- Paired records must have allocation-sized arrays at every represented node.
Missing raw/tree entries are allowed and dead allocations remain in the domain.
Permissions, flags, frames, valid paths, byte validity and safety are unrestricted. -/
def RWellSized (state : TreeMemory.State) : Prop :=
  ∀ id allocation node, state.raw.allocations id = some allocation →
    state.trees id = some node →
    TreeReference.arraysSized node allocation.size = true

theorem wellSized_encode_iff (state : TreeMemory.State) :
    RWellSized state ↔ TreeFactoredMemory.WellSized (encodeMemory state) := by
  constructor
  · intro sized id allocation tree rawFound encodedFound
    cases found : state.trees id with
    | none => simp [encodeMemory, found] at encodedFound
    | some node =>
      have same : TreeEncoding.encode node = tree := by
        simpa only [encodeMemory, found, Option.map_some, Option.some.injEq] using encodedFound
      subst tree
      rw [← arraysSized_encode node allocation.size]
      exact sized id allocation node rawFound found
  · intro sized id allocation node rawFound treeFound
    rw [arraysSized_encode node allocation.size]
    apply sized id allocation (TreeEncoding.encode node) rawFound
    simp only [encodeMemory, treeFound, Option.map_some]

#print axioms encodeMemory_raw
#print axioms encodeMemory_frame
#print axioms encodeMemory_tree
#print axioms reify_encode_memory
#print axioms related_encode_memory
#print axioms arraysSized_encode
#print axioms wellSized_encode_iff

end AnnealResearch.TreeMemoryEncoding
