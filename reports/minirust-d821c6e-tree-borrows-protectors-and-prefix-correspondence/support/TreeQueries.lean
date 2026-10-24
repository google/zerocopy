import AnnealResearch.TreeCorrespondence

/-!
Generic recursive query agreement for the frozen recursive and independently
implemented topology/store encodings.  Reification visits every ordered node.
No access-success, NoUB, array-size, protector-kind, or frame-list premise is
needed for these queries.  They compare Boolean results even on mismatched
syntactic trees.  Operational access/release correspondence is separate work.

The parent alone compiles.  These owned proofs do not discharge manual source
import, helper/generated-code interpretation, or Rust adequacy assumptions.
-/
namespace AnnealResearch.TreeQueries

open TreeFactored (Path Topology Forest Store State)
open TreeCorrespondence (reifyTree reifyForest reify Related)

theorem nat_beq_decide (first second : Nat) :
    (first == second) = decide (first = second) := by
  by_cases same : first = second <;> simp [same]

theorem reifyTree_permissions (topology : Topology) (here : Path) (store : Store) :
    (reifyTree topology here store).permissions = (store here).permissions := by
  cases topology
  rfl

theorem reifyTree_protection (topology : Topology) (here : Path) (store : Store) :
    (reifyTree topology here store).protection = (store here).protection := by
  cases topology
  rfl

mutual
  theorem containsStrongTree_reify (topology : Topology) (here : Path) (store : Store) :
      TreeReference.containsStrong (reifyTree topology here store) =
        TreeFactored.containsStrongTree topology here store := by
    cases topology with
    | node children =>
      simp only [reifyTree, TreeReference.containsStrong, TreeFactored.containsStrongTree]
      rw [containsStrongForest_reify]
      cases (store here).protection <;> rfl
  termination_by structural topology

  theorem containsStrongForest_reify (children : Forest) (parent : Path) (index : Nat)
      (store : Store) :
      TreeReference.childrenContainStrong (reifyForest children parent index store) =
        TreeFactored.containsStrongForest children parent index store := by
    cases children with
    | nil => simp only [reifyForest, TreeReference.childrenContainStrong,
        TreeFactored.containsStrongForest]
    | cons child rest =>
      simp only [reifyForest, TreeReference.childrenContainStrong,
        TreeFactored.containsStrongForest]
      rw [containsStrongTree_reify, containsStrongForest_reify]
  termination_by structural children
end

mutual
  theorem arraysSizedTree_reify (topology : Topology) (here : Path) (store : Store)
      (width : Nat) :
      TreeReference.arraysSized (reifyTree topology here store) width =
        TreeFactored.arrayLengthsTree topology here store width := by
    cases topology with
    | node children =>
      simp only [reifyTree, TreeReference.arraysSized, TreeFactored.arrayLengthsTree]
      rw [nat_beq_decide, arraysSizedForest_reify]
  termination_by structural topology

  theorem arraysSizedForest_reify (children : Forest) (parent : Path) (index : Nat)
      (store : Store) (width : Nat) :
      TreeReference.childrenSized (reifyForest children parent index store) width =
        TreeFactored.arrayLengthsForest children parent index store width := by
    cases children with
    | nil => simp only [reifyForest, TreeReference.childrenSized,
        TreeFactored.arrayLengthsForest]
    | cons child rest =>
      simp only [reifyForest, TreeReference.childrenSized, TreeFactored.arrayLengthsForest]
      rw [arraysSizedTree_reify, arraysSizedForest_reify]
  termination_by structural children
end

mutual
  theorem kindsMatchTree_reify (topology : Topology) (here : Path) (store : Store) :
      TreeReference.kindsMatch (reifyTree topology here store) =
        TreeFactored.matchingTree topology here store := by
    cases topology with
    | node children =>
      simp only [reifyTree, TreeReference.kindsMatch, TreeFactored.matchingTree]
      rw [kindsMatchForest_reify]
  termination_by structural topology

  theorem kindsMatchForest_reify (children : Forest) (parent : Path) (index : Nat)
      (store : Store) :
      TreeReference.childrenMatch (reifyForest children parent index store) =
        TreeFactored.matchingForest children parent index store := by
    cases children with
    | nil => simp only [reifyForest, TreeReference.childrenMatch, TreeFactored.matchingForest]
    | cons child rest =>
      simp only [reifyForest, TreeReference.childrenMatch, TreeFactored.matchingForest]
      rw [kindsMatchTree_reify, kindsMatchForest_reify]
  termination_by structural children
end

theorem containsStrong_reify (state : State) :
    TreeReference.containsStrong (reify state) = TreeFactored.containsStrong state :=
  containsStrongTree_reify state.topology [] state.store

theorem arraysSized_reify (state : State) (width : Nat) :
    TreeReference.arraysSized (reify state) width =
      TreeFactored.arrayLengthsTree state.topology [] state.store width :=
  arraysSizedTree_reify state.topology [] state.store width

/-- The two public root-width validation queries use the same root array. -/
theorem arrayLengths_reify_root (state : State) :
    TreeReference.arraysSized (reify state) (reify state).permissions.length =
      TreeFactored.arrayLengths state := by
  change TreeReference.arraysSized (reifyTree state.topology [] state.store)
    (reifyTree state.topology [] state.store).permissions.length =
      TreeFactored.arrayLengthsTree state.topology [] state.store (state.store []).permissions.length
  rw [reifyTree_permissions]
  exact arraysSizedTree_reify state.topology [] state.store (state.store []).permissions.length

theorem kindsMatch_reify (state : State) :
    TreeReference.kindsMatch (reify state) = TreeFactored.matchesProtectors state :=
  kindsMatchTree_reify state.topology [] state.store

theorem related_containsStrong {node : TreeReference.Node} {state : State}
    (related : Related node state) :
    TreeReference.containsStrong node = TreeFactored.containsStrong state := by
  rw [related]
  exact containsStrong_reify state

theorem related_arraysSized {node : TreeReference.Node} {state : State}
    (related : Related node state) (width : Nat) :
    TreeReference.arraysSized node width =
      TreeFactored.arrayLengthsTree state.topology [] state.store width := by
  rw [related]
  exact arraysSized_reify state width

theorem related_arrayLengths_root {node : TreeReference.Node} {state : State}
    (related : Related node state) :
    TreeReference.arraysSized node node.permissions.length = TreeFactored.arrayLengths state := by
  rw [related]
  exact arrayLengths_reify_root state

theorem related_kindsMatch {node : TreeReference.Node} {state : State}
    (related : Related node state) :
    TreeReference.kindsMatch node = TreeFactored.matchesProtectors state := by
  rw [related]
  exact kindsMatch_reify state

#print axioms nat_beq_decide
#print axioms reifyTree_permissions
#print axioms reifyTree_protection
#print axioms containsStrongTree_reify
#print axioms containsStrongForest_reify
#print axioms arraysSizedTree_reify
#print axioms arraysSizedForest_reify
#print axioms kindsMatchTree_reify
#print axioms kindsMatchForest_reify
#print axioms containsStrong_reify
#print axioms arraysSized_reify
#print axioms arrayLengths_reify_root
#print axioms kindsMatch_reify
#print axioms related_containsStrong
#print axioms related_arraysSized
#print axioms related_arrayLengths_root
#print axioms related_kindsMatch

end AnnealResearch.TreeQueries
