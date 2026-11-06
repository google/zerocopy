import AnnealResearch.TreeKindPreservation

/-!
Exact matching-query preservation for the actual recursive reference access
traversal and public access validator. Every ordinary UB/unsupported residual
participates, including earlier byte and child updates. No width, valid path,
scalar-success, compatibility, reachability or NoUB premise is required.

The proofs observe only represented recursive nodes and impose no condition on
absent factored-store entries. Release changes a flag and needs its separate
pending-conversion relation; no release or full-memory LiveKinds claim is made.
-/

namespace AnnealResearch.TreeKindAccess

open TreePermissions
open TreeKindPreservation (mapState_state transitionRange_matching)

mutual
  theorem accessCore_matching (node : TreeReference.Node) (path : Option TreeReference.Path)
      (kind : AccessKind) (offset size : Nat) :
      TreeReference.kindsMatch (TreeReference.accessCore node path kind offset size).state =
        TreeReference.kindsMatch node :=
    match node with
    | .mk permissions protection children => by
      have byteMatching := transitionRange_matching permissions offset size kind
        (TreeReference.nodeRelation path) protection
      simp only [TreeReference.accessCore]
      cases acted : TreeReference.transitionRange permissions offset size kind
          (TreeReference.nodeRelation path) with
      | ok result changed =>
        cases result
        dsimp only
        have same : changed.all (fun entry => entry.matchesProtector protection) =
            permissions.all (fun entry => entry.matchesProtector protection) := by
          simpa only [acted, TreeReference.Result.state] using byteMatching
        rw [mapState_state]
        simp only [TreeReference.kindsMatch]
        rw [same, accessChildren_matching children path kind offset size 0]
      | ub fault changed =>
        have same : changed.all (fun entry => entry.matchesProtector protection) =
            permissions.all (fun entry => entry.matchesProtector protection) := by
          simpa only [acted, TreeReference.Result.state] using byteMatching
        simp only [TreeReference.Result.state, TreeReference.kindsMatch]
        rw [same]
      | unsupported reason changed =>
        have same : changed.all (fun entry => entry.matchesProtector protection) =
            permissions.all (fun entry => entry.matchesProtector protection) := by
          simpa only [acted, TreeReference.Result.state] using byteMatching
        simp only [TreeReference.Result.state, TreeReference.kindsMatch]
        rw [same]
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  theorem accessChildren_matching (children : List TreeReference.Node)
      (path : Option TreeReference.Path) (kind : AccessKind) (offset size index : Nat) :
      TreeReference.childrenMatch
          (TreeReference.accessChildren children path kind offset size index).state =
        TreeReference.childrenMatch children :=
    match children with
    | [] => by simp only [TreeReference.accessChildren, TreeReference.Result.state]
    | child :: rest => by
      have childMatching := accessCore_matching child (TreeReference.childPath path index)
        kind offset size
      simp only [TreeReference.accessChildren]
      cases acted : TreeReference.accessCore child (TreeReference.childPath path index)
          kind offset size with
      | ok result changed =>
        cases result
        dsimp only
        have same : TreeReference.kindsMatch changed = TreeReference.kindsMatch child := by
          simpa only [acted, TreeReference.Result.state] using childMatching
        rw [mapState_state]
        simp only [TreeReference.childrenMatch]
        rw [same, accessChildren_matching rest path kind offset size (index + 1)]
      | ub fault changed =>
        have same : TreeReference.kindsMatch changed = TreeReference.kindsMatch child := by
          simpa only [acted, TreeReference.Result.state] using childMatching
        simp only [TreeReference.Result.state, TreeReference.childrenMatch]
        rw [same]
      | unsupported reason changed =>
        have same : TreeReference.kindsMatch changed = TreeReference.kindsMatch child := by
          simpa only [acted, TreeReference.Result.state] using childMatching
        simp only [TreeReference.Result.state, TreeReference.childrenMatch]
        rw [same]
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

/-- Rejected arrays, missing paths and out-of-range requests keep the original
tree; the executed raw branch retains its exact matching Boolean as well. -/
theorem access_matching (node : TreeReference.Node) (path : Option TreeReference.Path)
    (kind : AccessKind) (offset size : Nat) :
    TreeReference.kindsMatch (TreeReference.access node path kind offset size).state =
      TreeReference.kindsMatch node := by
  unfold TreeReference.access
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · exact accessCore_matching node path kind offset size

theorem accessCore_preserves_matching (node : TreeReference.Node)
    (path : Option TreeReference.Path) (kind : AccessKind) (offset size : Nat)
    (matching : TreeReference.kindsMatch node = true) :
    TreeReference.kindsMatch (TreeReference.accessCore node path kind offset size).state = true :=
  (accessCore_matching node path kind offset size).trans matching

theorem access_preserves_matching (node : TreeReference.Node)
    (path : Option TreeReference.Path) (kind : AccessKind) (offset size : Nat)
    (matching : TreeReference.kindsMatch node = true) :
    TreeReference.kindsMatch (TreeReference.access node path kind offset size).state = true :=
  (access_matching node path kind offset size).trans matching

#print axioms accessCore_matching
#print axioms accessChildren_matching
#print axioms access_matching
#print axioms accessCore_preserves_matching
#print axioms access_preserves_matching

end AnnealResearch.TreeKindAccess
