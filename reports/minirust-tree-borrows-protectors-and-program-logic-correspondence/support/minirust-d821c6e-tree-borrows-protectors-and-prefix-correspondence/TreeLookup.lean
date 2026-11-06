import AnnealResearch.TreeReleaseAgreement

/-!
Generic lookup bridge for the frozen ordered recursive tree representations.
Absolute prefixes, child starting indices and missing paths are explicit.
No shape bound, array-size, scalar-success, NoUB or kind-matching premise is
needed for lookup. Validated operation agreement is a later layer.
-/

namespace AnnealResearch.TreeLookup

open TreeFactored (Path Topology Forest Store State)
open TreeCorrespondence (reifyTree reifyForest reify)

/-- relative is the position in this forest; start is its absolute child index.
The statement includes absence and preserves child order, not just membership. -/
theorem reifyForest_get? (children : Forest) (parent : Path) (start : Nat)
    (store : Store) (relative : Nat) :
    (reifyForest children parent start store)[relative]? =
      (children.get? relative).map
        (fun child => reifyTree child (parent ++ [start + relative]) store) := by
  induction relative generalizing children start with
  | zero =>
    cases children <;> simp [reifyForest, TreeFactored.Forest.get?]
  | succ relative ih =>
    cases children with
    | nil => simp [reifyForest, TreeFactored.Forest.get?]
    | cons child rest =>
      have increment : start + 1 + relative = start + (relative + 1) := by omega
      simpa [reifyForest, TreeFactored.Forest.get?, increment] using ih rest (start + 1)

theorem findNode_reifyTree (topology : Topology) (here : Path) (store : Store) (path : Path) :
    TreeReference.findNode (reifyTree topology here store) path =
      (TreeFactored.findTopology topology path).map
        (fun child => reifyTree child (here ++ path) store) := by
  induction path generalizing topology here with
  | nil => simp [TreeReference.findNode, TreeFactored.findTopology]
  | cons index rest ih =>
    cases topology with
    | node children =>
      change (match (reifyForest children here 0 store)[index]? with
          | none => none
          | some child => TreeReference.findNode child rest) =
        (match children.get? index with
          | none => none
          | some child => TreeFactored.findTopology child rest).map
          (fun child => reifyTree child (here ++ index :: rest) store)
      rw [reifyForest_get?]
      simp only [Nat.zero_add]
      cases selected : children.get? index with
      | none => rfl
      | some child =>
        change TreeReference.findNode (reifyTree child (here ++ [index]) store) rest =
          (TreeFactored.findTopology child rest).map
            (fun found => reifyTree found (here ++ index :: rest) store)
        simpa only [List.append_assoc, List.singleton_append] using ih child (here ++ [index])

mutual
  /-- Shifting the total store by base is exactly the absolute-base view of a
  recursively reified subtree; all represented descendants are included. -/
  theorem reifyTree_shift (topology : Topology) (here : Path) (store : Store) (base : Path) :
      reifyTree topology here (fun query => store (base ++ query)) =
        reifyTree topology (base ++ here) store := by
    cases topology with
    | node children =>
      simp only [reifyTree]
      rw [reifyForest_shift]
  termination_by structural topology

  theorem reifyForest_shift (children : Forest) (parent : Path) (index : Nat)
      (store : Store) (base : Path) :
      reifyForest children parent index (fun query => store (base ++ query)) =
        reifyForest children (base ++ parent) index store := by
    cases children with
    | nil => simp only [reifyForest]
    | cons child rest =>
      simp only [reifyForest]
      rw [reifyTree_shift, reifyForest_shift]
      simp only [List.append_assoc]
  termination_by structural children
end

/-- Both lookups return the complete selected subtree, with the factored
lookup's relative store view reified at its original absolute path. -/
theorem findNode_reify (state : State) (path : Path) :
    TreeReference.findNode (reify state) path =
      (TreeFactored.findNode state path).map reify := by
  change TreeReference.findNode (reifyTree state.topology [] state.store) path = _
  rw [findNode_reifyTree]
  simp only [List.nil_append, TreeFactored.findNode]
  cases selected : TreeFactored.findTopology state.topology path with
  | none => rfl
  | some child =>
    change some (reifyTree child path state.store) =
      some (reifyTree child [] (fun rest => state.store (path ++ rest)))
    rw [reifyTree_shift, List.append_nil]

theorem findNode_isSome_reifyTree (topology : Topology) (here : Path) (store : Store)
    (path : Path) :
    (TreeReference.findNode (reifyTree topology here store) path).isSome =
      (TreeFactored.findTopology topology path).isSome := by
  rw [findNode_reifyTree]
  cases TreeFactored.findTopology topology path <;> rfl

theorem pathPresent_reify (state : State) (path : Path) :
    TreeReference.pathPresent (reify state) (some path) =
      (TreeFactored.findTopology state.topology path).isSome :=
  findNode_isSome_reifyTree state.topology [] state.store path

theorem findNode_missing_iff (topology : Topology) (here : Path) (store : Store) (path : Path) :
    TreeReference.findNode (reifyTree topology here store) path = none ↔
      TreeFactored.findTopology topology path = none := by
  rw [findNode_reifyTree]
  cases TreeFactored.findTopology topology path <;> simp

theorem findNode_found (topology child : Topology) (here : Path) (store : Store) (path : Path)
    (found : TreeFactored.findTopology topology path = some child) :
    TreeReference.findNode (reifyTree topology here store) path =
      some (reifyTree child (here ++ path) store) := by
  rw [findNode_reifyTree, found]
  rfl

/-- Root and missing-path consequences for clients of the validated wrappers.
Neither premise below asserts that any permission transition succeeds. -/
theorem validPath_present (state : State) (path : Path) (child : Topology)
    (found : TreeFactored.findTopology state.topology path = some child) :
    TreeReference.pathPresent (reify state) (some path) = true := by
  rw [pathPresent_reify, found]
  rfl

#print axioms reifyForest_get?
#print axioms findNode_reifyTree
#print axioms reifyTree_shift
#print axioms reifyForest_shift
#print axioms findNode_reify
#print axioms findNode_isSome_reifyTree
#print axioms pathPresent_reify
#print axioms findNode_missing_iff
#print axioms findNode_found
#print axioms validPath_present

end AnnealResearch.TreeLookup
