import AnnealResearch.TreeUnprotect
import AnnealResearch.TreeNodePathUpdate

/-!
Generic Memory-stage selected-node unprotect agreement for the owned tree
equations. The only operation-agreement admission is a valid topology path.
Missing protector flags and failed whole-list conversion remain unsupported
outcomes, with exact unchanged residual states; they are not filtered away.
Successful conversion replaces the complete permission list and retains the
selected flag. No kind-matching, array-width, access-success or NoUB premise is
used. The later live/dead branch and release traversal are separate operations.
-/

namespace AnnealResearch.TreeUnprotectAgreement

open TreePermissions
open TreeFactored (Path Topology State)

/-- The complete source map is performed before the selected-node assignment.
The entry callback is only a result/representation adapter, not a runner. -/
theorem unprotectAt_reference_callback (node : TreeReference.Node) (path : Path) :
    TreeReference.unprotectAt node path =
      TreeReference.modifyAt node path
        (TreeNodeUpdate.entryCallback TreeUnprotect.unprotectEntry) := by
  unfold TreeReference.unprotectAt
  apply congrArg (TreeReference.modifyAt node path)
  funext selected
  cases selected with
  | mk permissions protection children =>
      cases protection with
      | no => rfl
      | weak =>
          simp only [TreeNodeUpdate.entryCallback, TreeNodeUpdate.entryOf,
            TreeReference.Node.permissions, TreeReference.Node.protection,
            TreeUnprotect.unprotectEntry, Protected.yes, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte]
          rw [TreeUnprotect.unprotectPermissions_eq]
          cases TreeFactored.unprotectPermissions permissions with
          | none => rfl
          | some pair => cases pair; rfl
      | strong =>
          simp only [TreeNodeUpdate.entryCallback, TreeNodeUpdate.entryOf,
            TreeReference.Node.permissions, TreeReference.Node.protection,
            TreeUnprotect.unprotectEntry, Protected.yes, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte]
          rw [TreeUnprotect.unprotectPermissions_eq]
          cases TreeFactored.unprotectPermissions permissions with
          | none => rfl
          | some pair => cases pair; rfl

/-- Failed callbacks overwrite their original Entry, which is exactly the
unchanged full factored state. No partially converted list is ever assigned. -/
theorem unprotectAt_factored_callback (state : State) (path : Path) :
    TreeFactored.unprotectAt state path =
      TreeNodeUpdate.updateEntryAt state path TreeUnprotect.unprotectEntry := by
  unfold TreeFactored.unprotectAt TreeNodeUpdate.updateEntryAt
  cases TreeFactored.findTopology state.topology path with
  | none => rfl
  | some selected =>
      simp only [TreeUnprotect.unprotectEntry]
      cases flag : (state.store path).protection.yes with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, TreeFactored.Result.mapState,
            TreeNodeUpdate.overwrite_current]
      | true =>
          simp only [↓reduceIte]
          cases TreeFactored.unprotectPermissions (state.store path).permissions with
          | none =>
              simp only [TreeFactored.Result.mapState, TreeNodeUpdate.overwrite_current]
          | some pair => cases pair; rfl

/-- Every returned category and its full residual representation are compared.
The path premise is structural, and does not assert scalar compatibility. -/
theorem unprotectAt_agreement (state : State) (path : Path) (selected : Topology)
    (found : TreeFactored.findTopology state.topology path = some selected) :
    TreeCorrespondence.ResultRel TreeCorrespondence.Related
      (TreeReference.unprotectAt (TreeCorrespondence.reify state) path)
      (TreeFactored.unprotectAt state path) := by
  rw [unprotectAt_reference_callback, unprotectAt_factored_callback]
  exact TreeNodePathUpdate.modifyAt_agreement state path selected
    TreeUnprotect.unprotectEntry found

theorem unprotectAt_related (node : TreeReference.Node) (state : State)
    (path : Path) (selected : Topology)
    (related : TreeCorrespondence.Related node state)
    (found : TreeFactored.findTopology state.topology path = some selected) :
    TreeCorrespondence.ResultRel TreeCorrespondence.Related
      (TreeReference.unprotectAt node path) (TreeFactored.unprotectAt state path) := by
  rw [related]
  exact unprotectAt_agreement state path selected found

/-- The selected flag survives success and both owned unsupported branches,
and also survives the missing-path outcome. Clearing it belongs to traversal. -/
theorem unprotectAt_preserves_flag (state : State) (path : Path) :
    ((TreeFactored.unprotectAt state path).residual.store path).protection =
      (state.store path).protection := by
  unfold TreeFactored.unprotectAt
  cases TreeFactored.findTopology state.topology path with
  | none => rfl
  | some selected =>
      cases flag : (state.store path).protection.yes with
      | false => rfl
      | true =>
          cases TreeFactored.unprotectPermissions (state.store path).permissions with
          | none => rfl
          | some pair =>
              rcases pair with ⟨permissions, accesses⟩
              exact (TreeOperations.setPermissions_here state.store path permissions).2

theorem unprotectAt_failed_conversion (state : State) (path : Path) (selected : Topology)
    (found : TreeFactored.findTopology state.topology path = some selected)
    (flag : (state.store path).protection.yes = true)
    (failed : TreeFactored.unprotectPermissions (state.store path).permissions = none) :
    TreeFactored.unprotectAt state path =
      .unsupported .unprotectUnprotected state := by
  simp only [TreeFactored.unprotectAt, found, flag, ↓reduceIte, failed]

theorem unprotectAt_missing_flag (state : State) (path : Path) (selected : Topology)
    (found : TreeFactored.findTopology state.topology path = some selected)
    (flag : (state.store path).protection.yes = false) :
    TreeFactored.unprotectAt state path = .unsupported .missingProtector state := by
  simp only [TreeFactored.unprotectAt, found, flag, Bool.false_eq_true, ↓reduceIte]

#print axioms unprotectAt_reference_callback
#print axioms unprotectAt_factored_callback
#print axioms unprotectAt_agreement
#print axioms unprotectAt_related
#print axioms unprotectAt_preserves_flag
#print axioms unprotectAt_failed_conversion
#print axioms unprotectAt_missing_flag

end AnnealResearch.TreeUnprotectAgreement
