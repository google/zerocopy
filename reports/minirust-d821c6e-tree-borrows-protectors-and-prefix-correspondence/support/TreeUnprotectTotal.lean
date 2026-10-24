import AnnealResearch.TreeUnprotectAgreement

/-!
Total owned unprotect agreement, including missing topology paths. An invalid
path never calls the entry callback and reconstructs the original recursive
tree. Its owned unsupported diagnostic is preserved. This removes path
admission from unprotect correspondence without adding a runtime guard or
permission-kind, scalar-success, or NoUB assumption.

This checkpoint establishes missing-path and total result agreement. Generic
array-width and returned-access-length preservation is the next explicit layer.
-/

namespace AnnealResearch.TreeUnprotectTotal

open TreePermissions
open TreeFactored (Path Topology Forest Entry Store State)

theorem replaceNth_get_self (nodes : List TreeReference.Node) (index : Nat)
    (node : TreeReference.Node) (found : nodes[index]? = some node) :
    TreeReference.replaceNth nodes index node = nodes := by
  induction index generalizing nodes with
  | zero =>
      cases nodes with
      | nil => simp at found
      | cons first rest =>
          change some first = some node at found
          have same := Option.some.inj found
          subst node
          rfl
  | succ index ih =>
      cases nodes with
      | nil => simp at found
      | cons first rest =>
          change rest[index]? = some node at found
          change first :: TreeReference.replaceNth rest index node = first :: rest
          rw [ih rest found]

/-- A missing path invokes no callback; ancestor reconstruction only replaces
each encountered child by itself, including the returned unsupported state. -/
theorem modifyAt_missing {A : Type} (node : TreeReference.Node) (path : Path)
    (callback : TreeReference.Node → TreeReference.Result A TreeReference.Node)
    (missing : TreeReference.findNode node path = none) :
    TreeReference.modifyAt node path callback = .unsupported .invalidPath node := by
  induction path generalizing node with
  | nil => simp only [TreeReference.findNode] at missing; cases missing
  | cons index rest ih =>
      cases node with
      | mk permissions protection children =>
          cases selected : children[index]? with
          | none => simp only [TreeReference.modifyAt, selected]
          | some child =>
              have below : TreeReference.findNode child rest = none := by
                simpa only [TreeReference.findNode, TreeReference.Node.children, selected]
                  using missing
              rw [TreeReference.modifyAt]
              simp only [selected]
              rw [ih child below]
              simp only [TreeReference.Result.mapState]
              rw [replaceNth_get_self children index child selected]

theorem unprotectAt_missing (state : State) (path : Path)
    (missing : TreeFactored.findTopology state.topology path = none) :
    TreeCorrespondence.ResultRel TreeCorrespondence.Related
      (TreeReference.unprotectAt (TreeCorrespondence.reify state) path)
      (TreeFactored.unprotectAt state path) := by
  have missingReference :
      TreeReference.findNode (TreeCorrespondence.reify state) path = none :=
    (TreeLookup.findNode_missing_iff state.topology [] state.store path).2 missing
  rw [TreeUnprotectAgreement.unprotectAt_reference_callback,
    modifyAt_missing _ _ _ missingReference]
  rw [TreeFactored.unprotectAt, missing]
  exact ⟨rfl, rfl⟩

/-- Arbitrary input states and paths: missing paths, missing flags, whole-map
failure and success all participate with exact full residual reification. -/
theorem unprotectAt_agreement (state : State) (path : Path) :
    TreeCorrespondence.ResultRel TreeCorrespondence.Related
      (TreeReference.unprotectAt (TreeCorrespondence.reify state) path)
      (TreeFactored.unprotectAt state path) := by
  cases found : TreeFactored.findTopology state.topology path with
  | none => exact unprotectAt_missing state path found
  | some selected =>
      exact TreeUnprotectAgreement.unprotectAt_agreement state path selected found

theorem unprotectAt_related (node : TreeReference.Node) (state : State) (path : Path)
    (related : TreeCorrespondence.Related node state) :
    TreeCorrespondence.ResultRel TreeCorrespondence.Related
      (TreeReference.unprotectAt node path) (TreeFactored.unprotectAt state path) := by
  rw [related]
  exact unprotectAt_agreement state path

/-- Equality adapter for memory-wrapper proofs that use the already frozen
TreeAgreement result translation instead of its equivalent ResultRel form. -/
theorem unprotectAt_eq_translate (state : State) (path : Path) :
    TreeReference.unprotectAt (TreeCorrespondence.reify state) path =
      TreeAgreement.translate TreeCorrespondence.reify (TreeFactored.unprotectAt state path) := by
  have related := unprotectAt_agreement state path
  cases reference : TreeReference.unprotectAt (TreeCorrespondence.reify state) path <;>
    cases factored : TreeFactored.unprotectAt state path <;>
    simp only [reference, factored, TreeCorrespondence.ResultRel,
      TreeCorrespondence.Related] at related
  all_goals try exact False.elim related
  all_goals
    rcases related with ⟨same, residual⟩
    simp only [TreeAgreement.translate]
    rw [same, residual]

#print axioms replaceNth_get_self
#print axioms modifyAt_missing
#print axioms unprotectAt_missing
#print axioms unprotectAt_agreement
#print axioms unprotectAt_related
#print axioms unprotectAt_eq_translate

end AnnealResearch.TreeUnprotectTotal
