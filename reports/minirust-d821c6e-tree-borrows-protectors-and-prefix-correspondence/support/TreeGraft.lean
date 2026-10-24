import AnnealResearch.TreeValidated

/-!
First insertion checkpoint: ordered root append and complete subtree-store
grafting. The actual independent F.addNode runner is unchanged. Every child
entry is installed from the child store, regardless of the previous values at
absent paths. The reference and factored validators differ outside the stated
uniform-width domain. No kind, operation-success, NoUB or reachability premise
is used. Nested parent paths and memory reborrow are separate later layers.
-/

namespace AnnealResearch.TreeGraft

open TreeFactored (Path Topology Forest Store State)
open TreeCorrespondence (reifyTree reifyForest reify)

/-- The exact store selection performed by frozen F.addNode. -/
def graft (old : Store) (fresh : Path) (child : Store) : Store :=
  fun query => match TreeFactored.stripPrefix fresh query with
    | none => old query
    | some rest => child rest

theorem stripPrefix_append (stem rest : Path) :
    TreeFactored.stripPrefix stem (stem ++ rest) = some rest := by
  induction stem with
  | nil => rfl
  | cons head tail ih =>
      change (if head = head then TreeFactored.stripPrefix tail (tail ++ rest) else none) = _
      rw [ite_eq_left rfl]
      exact ih

theorem graft_inside (old child : Store) (fresh rest : Path) :
    graft old fresh child (fresh ++ rest) = child rest := by
  simp only [graft, stripPrefix_append]

theorem graft_outside (old child : Store) (fresh query : Path)
    (outside : TreeFactored.stripPrefix fresh query = none) :
    graft old fresh child query = old query := by
  simp only [graft, outside]

/-- This installs the entire recursive child, rather than only its root entry. -/
theorem reifyTree_graft (topology : Topology) (fresh : Path) (old child : Store) :
    reifyTree topology fresh (graft old fresh child) = reifyTree topology [] child := by
  have shifted : (fun query => graft old fresh child (fresh ++ query)) = child := by
    funext query
    exact graft_inside old child fresh query
  have view := TreeLookup.reifyTree_shift topology [] (graft old fresh child) fresh
  simpa only [List.append_nil, shifted] using view.symm

/-- A fresh root child index cannot affect any earlier child's descendants. -/
theorem reifyTree_graft_other (topology : Topology) (index fresh : Nat)
    (old child : Store) (different : index ≠ fresh) :
    reifyTree topology [index] (graft old [fresh] child) =
      reifyTree topology [index] old := by
  apply TreeCorrespondence.reifyTree_congr
  intro query member
  obtain ⟨rest, shape⟩ := TreeTraversal.representedTree_suffix topology [index] query member
  subst query
  simp [graft, TreeFactored.stripPrefix, Ne.symm different]

theorem reifyForest_graft_after (children : Forest) (index fresh : Nat)
    (old child : Store) (later : index + children.length ≤ fresh) :
    reifyForest children [] index (graft old [fresh] child) =
      reifyForest children [] index old := by
  cases children with
  | nil => rfl
  | cons first rest =>
      have before : index ≠ fresh := by
        simp only [TreeFactored.Forest.length] at later
        omega
      have remaining : index + 1 + rest.length ≤ fresh := by
        simp only [TreeFactored.Forest.length] at later
        omega
      simp only [reifyForest, List.nil_append]
      rw [reifyTree_graft_other first index fresh old child before,
        reifyForest_graft_after rest (index + 1) fresh old child remaining]
termination_by structural children

theorem reifyForest_length (children : Forest) (parent : Path) (index : Nat) (store : Store) :
    (reifyForest children parent index store).length = children.length := by
  cases children with
  | nil => rfl
  | cons first rest =>
      simp only [reifyForest, List.length_cons, TreeFactored.Forest.length]
      rw [reifyForest_length rest parent (index + 1) store]
termination_by structural children

theorem reifyForest_snoc (children : Forest) (child : Topology) (parent : Path)
    (index : Nat) (store : Store) :
    reifyForest (children.snoc child) parent index store =
      reifyForest children parent index store ++
        [reifyTree child (parent ++ [index + children.length]) store] := by
  cases children with
  | nil => simp only [TreeFactored.Forest.snoc, TreeFactored.Forest.length,
      reifyForest, Nat.add_zero, List.nil_append]
  | cons first rest =>
      simp only [TreeFactored.Forest.snoc, reifyForest, TreeFactored.Forest.length]
      rw [reifyForest_snoc rest child parent (index + 1) store]
      have position : index + 1 + rest.length = index + (rest.length + 1) := by omega
      simp only [position, List.cons_append]
termination_by structural children

theorem get?_length (children : Forest) : children.get? children.length = none := by
  cases children with
  | nil => rfl
  | cons first rest =>
      simpa only [TreeFactored.Forest.length, TreeFactored.Forest.get?] using get?_length rest
termination_by structural children

theorem appended_path_was_absent (children : Forest) :
    TreeFactored.findTopology (.node children) [children.length] = none := by
  simp only [TreeFactored.findTopology, get?_length]

def graftRoot (children : Forest) (old : Store) (child : State) : State :=
  ⟨.node (children.snoc child.topology), graft old [children.length] child.store⟩

theorem addNode_root (children : Forest) (old : Store) (child : State) :
    TreeFactored.addNode ⟨.node children, old⟩ [] child =
      .ok [children.length] (graftRoot children old child) := rfl

theorem graftRoot_reify (children : Forest) (old : Store) (child : State) :
    reify (graftRoot children old child) =
      TreeReference.Node.mk (old []).permissions (old []).protection
        (reifyForest children [] 0 old ++ [reify child]) := by
  change TreeReference.Node.mk (old []).permissions (old []).protection
    (reifyForest (children.snoc child.topology) [] 0
      (graft old [children.length] child.store)) = _
  rw [reifyForest_snoc]
  simp only [List.nil_append, Nat.zero_add]
  rw [reifyForest_graft_after children 0 children.length old child.store (by omega),
    reifyTree_graft] <;> rfl

/-- Root insertion compares actual runner results under uniform parent/child
arrays. Old absent-store entries are unrestricted. The root is selected by the
operation argument itself; no valid-path or successful-result premise occurs. -/
theorem addNode_root_agrees (children : Forest) (old : Store) (child : State) (width : Nat)
    (parentUniform : TreeFactored.arrayLengthsTree (.node children) [] old width = true)
    (childUniform : TreeFactored.arrayLengthsTree child.topology [] child.store width = true) :
    TreeReference.addNode (reify ⟨.node children, old⟩) [] (reify child) =
      TreeAgreement.translate reify (TreeFactored.addNode ⟨.node children, old⟩ [] child) := by
  have rootWidth : (reify ⟨.node children, old⟩).permissions.length = width := by
    simpa only [reify, TreeQueries.reifyTree_permissions] using
      TreeValidated.uniform_root_width (.node children) [] old width parentUniform
  have parentArrays : TreeReference.arraysSized (reify ⟨.node children, old⟩) width = true := by
    rw [TreeQueries.arraysSized_reify]
    exact parentUniform
  have childArrays : TreeReference.arraysSized (reify child) width = true := by
    rw [TreeQueries.arraysSized_reify]
    exact childUniform
  rw [addNode_root]
  simp only [TreeAgreement.translate, graftRoot_reify]
  simp only [TreeReference.addNode, rootWidth, parentArrays, childArrays,
    Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  simp only [reify, reifyTree, TreeReference.modifyAt, List.nil_append]
  rw [reifyForest_length] <;> rfl

#print axioms stripPrefix_append
#print axioms graft_inside
#print axioms graft_outside
#print axioms reifyTree_graft
#print axioms reifyTree_graft_other
#print axioms reifyForest_graft_after
#print axioms reifyForest_length
#print axioms reifyForest_snoc
#print axioms get?_length
#print axioms appended_path_was_absent
#print axioms addNode_root
#print axioms graftRoot_reify
#print axioms addNode_root_agrees

end AnnealResearch.TreeGraft
