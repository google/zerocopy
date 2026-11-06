import AnnealResearch.TreeInsertionWidths
import AnnealResearch.TreeTraversalGeometryPublic

/-!
Actual initial-access correspondence on the original supplied permission list.
R advances its offset; F retains the original offset and advances an index.
The helper equation aligns offset + index without recomputing settings from
mutated permissions. All partial UB/unsupported residuals participate.

Only uniform array width is operational admission. Paths, offsets and supplied
settings are arbitrary. Empty lists and permissions requesting no initial access
perform no path/range validation. Actual access preserves every width query,
which supplies the induction through successful steps and the error residuals.
This adds no memory wrapper, frame registration, kind or NoUB admission, or
source/helper/Rust adequacy claim.
-/

namespace AnnealResearch.TreeInitialAgreement

open TreePermissions
open TreeFactored (Path State)
open TreeCorrespondence (reify)

/-- Exact query preservation also includes initially malformed trees and every
returned category; it is a consequence of the unchanged actual access runner. -/
theorem initialAccessLoop_arrayLengths (state : State) (path : Path) (offset index : Nat)
    (permissions : List Permission) (width : Nat) :
    TreeFactored.arrayLengthsTree
        (TreeFactored.initialAccessLoop state path offset index permissions).residual.topology []
        (TreeFactored.initialAccessLoop state path offset index permissions).residual.store width =
      TreeFactored.arrayLengthsTree state.topology [] state.store width := by
  induction permissions generalizing state index with
  | nil => rfl
  | cons permission rest ih =>
      simp only [TreeFactored.initialAccessLoop]
      cases action : permission.initAccess with
      | none =>
          simp only
          exact ih state (index + 1)
      | some kind =>
          simp only
          have first := TreeTraversalGeometry.access_arrayLengths state path kind (offset + index) 1 width
          cases actual : TreeFactored.access state path kind (offset + index) 1 with
          | ok value changed =>
              cases value
              simp only [actual, TreeFactored.Result.residual] at first
              simp only [TreeFactored.Result.bind]
              exact (ih changed (index + 1)).trans first
          | ub fault changed =>
              simpa only [actual, TreeFactored.Result.residual, TreeFactored.Result.bind] using first
          | unsupported reason changed =>
              simpa only [actual, TreeFactored.Result.residual, TreeFactored.Result.bind] using first

theorem initialAccessLoop_preserves_uniform (state : State) (path : Path) (offset index : Nat)
    (permissions : List Permission) (width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true) :
    TreeFactored.arrayLengthsTree
      (TreeFactored.initialAccessLoop state path offset index permissions).residual.topology []
      (TreeFactored.initialAccessLoop state path offset index permissions).residual.store width = true :=
  (initialAccessLoop_arrayLengths state path offset index permissions width).trans uniform

theorem initialAccessLoop_agrees (state : State) (path : Path) (offset index : Nat)
    (permissions : List Permission) (width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true) :
    TreeReference.initialAccesses (reify state) path (offset + index) permissions =
      TreeAgreement.translate reify
        (TreeFactored.initialAccessLoop state path offset index permissions) := by
  induction permissions generalizing state index with
  | nil => rfl
  | cons permission rest ih =>
      simp only [TreeReference.initialAccesses, TreeFactored.initialAccessLoop]
      cases action : permission.initAccess with
      | none =>
          simp only
          simpa only [Nat.add_assoc] using ih state (index + 1) uniform
      | some kind =>
          simp only
          rw [TreeValidated.access_agrees state path kind (offset + index) 1 width uniform]
          cases actual : TreeFactored.access state path kind (offset + index) 1 with
          | ok value changed =>
              cases value
              simp only [TreeAgreement.translate, TreeReference.Result.bind, TreeFactored.Result.bind]
              have query := TreeTraversalGeometry.access_arrayLengths state path kind
                (offset + index) 1 width
              have changedUniform :
                  TreeFactored.arrayLengthsTree changed.topology [] changed.store width = true := by
                simpa only [actual, TreeFactored.Result.residual] using query.trans uniform
              simpa only [Nat.add_assoc, TreeAgreement.translate] using
                ih changed (index + 1) changedUniform
          | ub fault changed =>
              simp only [TreeAgreement.translate, TreeReference.Result.bind, TreeFactored.Result.bind]
          | unsupported reason changed =>
              simp only [TreeAgreement.translate, TreeReference.Result.bind, TreeFactored.Result.bind]

/-- Main actual-entry-point equation. No valid path, in-range offset, settings
compatibility, permission success or NoUB premise is assumed. -/
theorem initialAccesses_agrees (state : State) (path : Path) (offset : Nat)
    (permissions : List Permission) (width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true) :
    TreeReference.initialAccesses (reify state) path offset permissions =
      TreeAgreement.translate reify (TreeFactored.initialAccesses state path offset permissions) := by
  simpa only [Nat.add_zero, TreeFactored.initialAccesses] using
    initialAccessLoop_agrees state path offset 0 permissions width uniform

theorem initialAccesses_arrayLengths (state : State) (path : Path) (offset : Nat)
    (permissions : List Permission) (width : Nat) :
    TreeFactored.arrayLengthsTree
      (TreeFactored.initialAccesses state path offset permissions).residual.topology []
      (TreeFactored.initialAccesses state path offset permissions).residual.store width =
        TreeFactored.arrayLengthsTree state.topology [] state.store width :=
  initialAccessLoop_arrayLengths state path offset 0 permissions width

theorem initialAccesses_preserves_uniform (state : State) (path : Path) (offset : Nat)
    (permissions : List Permission) (width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true) :
    TreeFactored.arrayLengthsTree
      (TreeFactored.initialAccesses state path offset permissions).residual.topology []
      (TreeFactored.initialAccesses state path offset permissions).residual.store width = true :=
  (initialAccesses_arrayLengths state path offset permissions width).trans uniform

/-- Width-free controls: even malformed trees, invalid paths and large offsets
gain no validation when the original list requests no initial access. -/
theorem nil_no_validation (state : State) (path : Path) (offset : Nat) :
    TreeReference.initialAccesses (reify state) path offset [] = .ok () (reify state) ∧
      TreeFactored.initialAccesses state path offset [] = .ok () state := ⟨rfl, rfl⟩

theorem cell_no_validation (state : State) (path : Path) (offset : Nat) :
    TreeReference.initialAccesses (reify state) path offset [.prot .cell] = .ok () (reify state) ∧
      TreeFactored.initialAccesses state path offset [.prot .cell] = .ok () state := ⟨rfl, rfl⟩

#print axioms initialAccessLoop_arrayLengths
#print axioms initialAccessLoop_preserves_uniform
#print axioms initialAccessLoop_agrees
#print axioms initialAccesses_agrees
#print axioms initialAccesses_arrayLengths
#print axioms initialAccesses_preserves_uniform
#print axioms nil_no_validation
#print axioms cell_no_validation

end AnnealResearch.TreeInitialAgreement
