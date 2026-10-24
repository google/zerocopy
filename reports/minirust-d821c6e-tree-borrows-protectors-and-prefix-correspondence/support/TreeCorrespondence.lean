import AnnealResearch.TreeReference
import AnnealResearch.TreeFactored

/-!
Bridge for the owned recursive and independently implemented topology/store
encodings. The operational implementations share only TreePermissions.

This module initially freezes representation helpers. Reification traverses
the full ordered topology and reads every represented node's entry. It ignores
only total-store cells at absent paths, never a node of the represented tree.
No access-success, NoUB, flag/kind compatibility or frame-list premise is hidden
in the relation. Operational agreement is a separate theorem obligation.
-/

namespace AnnealResearch.TreeCorrespondence

open TreeFactored (Path Topology Forest Entry Store State)

mutual
  def reifyTree (topology : Topology) (here : Path) (store : Store) : TreeReference.Node :=
    match topology with
    | .node children =>
      .mk (store here).permissions (store here).protection
        (reifyForest children here 0 store)
  termination_by structural topology

  def reifyForest (children : Forest) (parent : Path) (index : Nat) (store : Store) :
      List TreeReference.Node :=
    match children with
    | .nil => []
    | .cons child rest =>
      reifyTree child (parent ++ [index]) store ::
        reifyForest rest parent (index + 1) store
  termination_by structural children
end

def reify (state : State) : TreeReference.Node :=
  reifyTree state.topology [] state.store

/-- Exact represented-node payload and ordered-topology relation. No contents
of absent total-store cells are constrained. -/
def Related (node : TreeReference.Node) (state : State) : Prop := node = reify state

mutual
  /-- Absolute paths whose payload is read when reifying this subtree. -/
  def representedTree (topology : Topology) (here query : Path) : Prop :=
    match topology with
    | .node children => query = here ∨ representedForest children here 0 query
  termination_by structural topology

  def representedForest (children : Forest) (parent : Path) (index : Nat)
      (query : Path) : Prop :=
    match children with
    | .nil => False
    | .cons child rest =>
      representedTree child (parent ++ [index]) query ∨
        representedForest rest parent (index + 1) query
  termination_by structural children
end

def StoresAgree (topology : Topology) (here : Path) (first second : Store) : Prop :=
  ∀ query, representedTree topology here query → first query = second query

mutual
  theorem reifyTree_congr (topology : Topology) (here : Path) (first second : Store)
      (entries : StoresAgree topology here first second) :
      reifyTree topology here first = reifyTree topology here second := by
    cases topology with
    | node children =>
      simp only [StoresAgree, representedTree] at entries
      have rootEntry : first here = second here := entries here (Or.inl rfl)
      have childTrees := reifyForest_congr children here 0 first second
        (fun query member => entries query (Or.inr member))
      simp only [reifyTree]
      rw [rootEntry, childTrees]
  termination_by structural topology

  theorem reifyForest_congr (children : Forest) (parent : Path) (index : Nat)
      (first second : Store)
      (entries : ∀ query, representedForest children parent index query →
        first query = second query) :
      reifyForest children parent index first = reifyForest children parent index second := by
    cases children with
    | nil => simp only [reifyForest]
    | cons child rest =>
      simp only [representedForest] at entries
      have headTree := reifyTree_congr child (parent ++ [index]) first second
        (fun query member => entries query (Or.inl member))
      have restTrees := reifyForest_congr rest parent (index + 1) first second
        (fun query member => entries query (Or.inr member))
      simp only [reifyForest]
      rw [headTree, restTrees]
  termination_by structural children
end

theorem reify_congr (topology : Topology) (first second : Store)
    (entries : StoresAgree topology [] first second) :
    reify ⟨topology, first⟩ = reify ⟨topology, second⟩ :=
  reifyTree_congr topology [] first second entries

/-- This is an actual equality of reconstructed trees, not a declaration that
some represented node may be forgotten. -/
theorem overwrite_absent_preserves_reify (topology : Topology) (here absent : Path)
    (store : Store) (entry : Entry)
    (outside : ¬ representedTree topology here absent) :
    reifyTree topology here (TreeFactored.overwrite store absent entry) =
      reifyTree topology here store := by
  apply reifyTree_congr
  intro query member
  by_cases same : query = absent
  · subst query
    exact False.elim (outside member)
  · simp [TreeFactored.overwrite, same]

mutual
  theorem representedTree_length (topology : Topology) (here query : Path)
      (member : representedTree topology here query) : here.length ≤ query.length := by
    cases topology with
    | node children =>
      simp only [representedTree] at member
      rcases member with atRoot | belowRoot
      · subst query
        exact Nat.le_refl _
      · exact Nat.le_of_lt (representedForest_length children here 0 query belowRoot)
  termination_by structural topology

  theorem representedForest_length (children : Forest) (parent : Path) (index : Nat)
      (query : Path) (member : representedForest children parent index query) :
      parent.length < query.length := by
    cases children with
    | nil => simp only [representedForest] at member
    | cons child rest =>
      simp only [representedForest] at member
      rcases member with inChild | inRest
      · have longer := representedTree_length child (parent ++ [index]) query inChild
        simp only [List.length_append, List.length_singleton] at longer
        omega
      · exact representedForest_length rest parent (index + 1) query inRest
  termination_by structural children
end

theorem parent_absent_from_child_forest (children : Forest) (parent : Path) (index : Nat) :
    ¬ representedForest children parent index parent := by
  intro member
  have impossible := representedForest_length children parent index parent member
  omega

mutual
  def topologyOf (node : TreeReference.Node) : Topology :=
    match node with
    | .mk _ _ children => .node (forestOf children)
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  def forestOf (children : List TreeReference.Node) : Forest :=
    match children with
    | [] => .nil
    | child :: rest => .cons (topologyOf child) (forestOf rest)
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

mutual
  theorem topologyOf_reifyTree (topology : Topology) (here : Path) (store : Store) :
      topologyOf (reifyTree topology here store) = topology := by
    cases topology with
    | node children =>
      simp only [reifyTree, topologyOf]
      rw [forestOf_reifyForest]
  termination_by structural topology

  theorem forestOf_reifyForest (children : Forest) (parent : Path) (index : Nat)
      (store : Store) : forestOf (reifyForest children parent index store) = children := by
    cases children with
    | nil => simp only [reifyForest, forestOf]
    | cons child rest =>
      simp only [reifyForest, forestOf]
      rw [topologyOf_reifyTree, forestOf_reifyForest]
  termination_by structural children
end

theorem related_preserves_topology {node : TreeReference.Node} {state : State}
    (related : Related node state) : topologyOf node = state.topology := by
  rw [related]
  exact topologyOf_reifyTree state.topology [] state.store

theorem reified_is_related (state : State) : Related (reify state) state := rfl

def structuralToReference : TreeFactored.Structural → TreeReference.Structural
  | .invalidPath => .invalidPath
  | .arrayLength => .arrayLength
  | .range => .range
  | .missingProtector => .missingProtector
  | .unprotectUnprotected => .unprotectUnprotected

/-- Status, value and diagnostic agreement with a separately supplied residual
state relation. All ordinary UB residuals participate, not only successes. -/
def ResultRel (same : S → T → Prop) :
    TreeReference.Result A S → TreeFactored.Result A T → Prop
  | .ok value state, .ok other otherState => value = other ∧ same state otherState
  | .ub fault state, .ub other otherState => fault = other ∧ same state otherState
  | .unsupported reason state, .unsupported other otherState =>
      reason = structuralToReference other ∧ same state otherState
  | _, _ => False

theorem resultRel_bind {same : S → T → Prop}
    {left : TreeReference.Result A S} {right : TreeFactored.Result A T}
    (related : ResultRel same left right)
    (nextLeft : A → S → TreeReference.Result B S)
    (nextRight : A → T → TreeFactored.Result B T)
    (continued : ∀ value state otherState, same state otherState →
      ResultRel same (nextLeft value state) (nextRight value otherState)) :
    ResultRel same (left.bind nextLeft) (right.bind nextRight) := by
  cases left with
  | ok value state =>
    cases right with
    | ok other otherState =>
      rcases related with ⟨sameValue, residual⟩
      change ResultRel same (nextLeft value state) (nextRight other otherState)
      rw [sameValue]
      exact continued other state otherState residual
    | ub fault otherState => exact False.elim related
    | unsupported fault otherState => exact False.elim related
  | ub fault state =>
    cases right with
    | ok other otherState => exact False.elim related
    | ub other otherState => exact related
    | unsupported other otherState => exact False.elim related
  | unsupported fault state =>
    cases right with
    | ok other otherState => exact False.elim related
    | ub other otherState => exact False.elim related
    | unsupported other otherState => exact related

theorem resultRel_mapState {same : S → T → Prop} {nextSame : U → V → Prop}
    {left : TreeReference.Result A S} {right : TreeFactored.Result A T}
    (related : ResultRel same left right) (first : S → U) (second : T → V)
    (preserves : ∀ state otherState, same state otherState →
      nextSame (first state) (second otherState)) :
    ResultRel nextSame (left.mapState first) (right.mapState second) := by
  cases left with
  | ok value state =>
    cases right with
    | ok other otherState =>
      exact ⟨related.1, preserves state otherState related.2⟩
    | ub fault otherState => exact False.elim related
    | unsupported fault otherState => exact False.elim related
  | ub fault state =>
    cases right with
    | ok other otherState => exact False.elim related
    | ub other otherState => exact ⟨related.1, preserves state otherState related.2⟩
    | unsupported other otherState => exact False.elim related
  | unsupported fault state =>
    cases right with
    | ok other otherState => exact False.elim related
    | ub other otherState => exact False.elim related
    | unsupported other otherState => exact ⟨related.1, preserves state otherState related.2⟩

#print axioms reifyTree_congr
#print axioms reifyForest_congr
#print axioms reify_congr
#print axioms overwrite_absent_preserves_reify
#print axioms representedTree_length
#print axioms representedForest_length
#print axioms parent_absent_from_child_forest
#print axioms topologyOf_reifyTree
#print axioms forestOf_reifyForest
#print axioms related_preserves_topology
#print axioms reified_is_related
#print axioms resultRel_bind
#print axioms resultRel_mapState

end AnnealResearch.TreeCorrespondence
