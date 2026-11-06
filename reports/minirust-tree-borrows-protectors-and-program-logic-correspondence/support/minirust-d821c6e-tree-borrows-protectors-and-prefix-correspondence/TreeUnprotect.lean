import AnnealResearch.TreeNodeUpdate

/-!
Complete-list unprotection equivalence for the owned d821c6e3 source equations.
Neither implementation mutates a permission prefix while converting the list:
one failed scalar conversion rejects the whole list. Unprot inputs are modeled
as unsupported, including when a protector flag is present; there is no added
kind-matching or success premise.

This checkpoint proves list conversion and its length accounting. Generic
selected-path operation agreement is pending the TreeNodeUpdate path theorem.
-/

namespace AnnealResearch.TreeUnprotect


open TreePermissions

/-- A failed Option conversion has the sole owned source diagnostic
unprotectUnprotected. In particular, failure is not an ordinary UB category. -/
theorem unprotectPermissions_eq (permissions : List Permission) :
    TreeReference.unprotectPermissions permissions =
      match TreeFactored.unprotectPermissions permissions with
      | none => .error .unprotectUnprotected
      | some value => .ok value := by
  induction permissions with
  | nil => rfl
  | cons permission rest ih =>
      cases scalar : permission.unprotect with
      | none => simp only [TreeReference.unprotectPermissions, TreeFactored.unprotectPermissions, scalar]
      | some pair =>
          rcases pair with ⟨changed, access⟩
          simp only [TreeReference.unprotectPermissions, TreeFactored.unprotectPermissions, scalar]
          rw [ih]
          cases TreeFactored.unprotectPermissions rest with
          | none => rfl
          | some value => cases value; rfl

theorem unprotectPermissions_lengths (permissions changed : List Permission)
    (accesses : List (Option AccessKind))
    (converted : TreeFactored.unprotectPermissions permissions = some (changed, accesses)) :
    changed.length = permissions.length ∧ accesses.length = permissions.length := by
  induction permissions generalizing changed accesses with
  | nil =>
      simp only [TreeFactored.unprotectPermissions, Option.some.injEq, Prod.mk.injEq] at converted
      rcases converted with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | cons permission rest ih =>
      cases scalar : permission.unprotect with
      | none =>
          simp only [TreeFactored.unprotectPermissions, scalar] at converted
          cases converted
      | some pair =>
          rcases pair with ⟨next, access⟩
          cases tail : TreeFactored.unprotectPermissions rest with
          | none =>
              simp only [TreeFactored.unprotectPermissions, scalar, tail] at converted
              cases converted
          | some pair =>
              rcases pair with ⟨changedRest, more⟩
              simp only [TreeFactored.unprotectPermissions, scalar, tail, Option.some.injEq,
                Prod.mk.injEq] at converted
              rcases converted with ⟨rfl, rfl⟩
              obtain ⟨permissionLength, accessLength⟩ := ih changedRest more tail
              constructor <;> simp only [List.length_cons, permissionLength, accessLength]

theorem unprotectPermissions_failure (permissions : List Permission)
    (failed : TreeFactored.unprotectPermissions permissions = none) :
    TreeReference.unprotectPermissions permissions = .error .unprotectUnprotected := by
  rw [unprotectPermissions_eq, failed]

theorem unprotectPermissions_success (permissions changed : List Permission)
    (accesses : List (Option AccessKind))
    (converted : TreeFactored.unprotectPermissions permissions = some (changed, accesses)) :
    TreeReference.unprotectPermissions permissions = .ok (changed, accesses) := by
  rw [unprotectPermissions_eq, converted]

/-- This callback converts the entire list before replacing its Entry. The
protector flag is intentionally retained for the later release traversal. -/
def unprotectEntry (entry : TreeFactored.Entry) : TreeFactored.Result (List (Option AccessKind)) TreeFactored.Entry :=
  if entry.protection.yes then
    match TreeFactored.unprotectPermissions entry.permissions with
    | none => .unsupported .unprotectUnprotected entry
    | some (permissions, accesses) =>
        .ok accesses { entry with permissions := permissions }
  else .unsupported .missingProtector entry

theorem unprotectEntry_protection (entry : TreeFactored.Entry) :
    (unprotectEntry entry).residual.protection = entry.protection := by
  unfold unprotectEntry
  cases flag : entry.protection with
  | no => simp only [flag, Protected.yes, Bool.false_eq_true, ↓reduceIte,
      TreeFactored.Result.residual]
  | weak =>
      simp only [Protected.yes, ↓reduceIte]
      cases TreeFactored.unprotectPermissions entry.permissions with
      | none => simpa only [TreeFactored.Result.residual] using flag
      | some pair => cases pair; rfl
  | strong =>
      simp only [Protected.yes, ↓reduceIte]
      cases TreeFactored.unprotectPermissions entry.permissions with
      | none => simpa only [TreeFactored.Result.residual] using flag
      | some pair => cases pair; rfl

#print axioms unprotectPermissions_eq
#print axioms unprotectPermissions_lengths
#print axioms unprotectPermissions_failure
#print axioms unprotectPermissions_success
#print axioms unprotectEntry_protection

end AnnealResearch.TreeUnprotect
