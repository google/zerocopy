import AnnealResearch.TreeCorrespondence

/-!
Staged operation bridge. This first layer relates independently implemented
per-offset store updates to recursive byte-list reconstruction. The result
adapter preserves ordinary UB, unsupported diagnostics and exact residual
stores. No access-success/NoUB or permission/protector matching premise is used.
The full recursive tree-operation theorem is a separate next proof obligation.
-/

namespace AnnealResearch.TreeOperations

open TreePermissions
open TreeFactored (Path Store)

def structuralToFactored : TreeReference.Structural → TreeFactored.Structural
  | .invalidPath => .invalidPath
  | .arrayLength => .arrayLength
  | .range => .range
  | .missingProtector => .missingProtector
  | .unprotectUnprotected => .unprotectUnprotected

theorem structural_roundtrip (reason : TreeReference.Structural) :
    TreeCorrespondence.structuralToReference (structuralToFactored reason) = reason := by
  cases reason <;> rfl

theorem setPermissions_current (store : Store) (here : Path) :
    TreeFactored.setPermissions store here (store here).permissions = store := by
  funext query
  by_cases same : query = here
  · subst query
    simp only [TreeFactored.setPermissions, TreeFactored.overwrite]
    cases store here
    rfl
  · simp [TreeFactored.setPermissions, TreeFactored.overwrite, same]

theorem setPermissions_setPermissions (store : Store) (here : Path)
    (first second : List Permission) :
    TreeFactored.setPermissions (TreeFactored.setPermissions store here first) here second =
      TreeFactored.setPermissions store here second := by
  funext query
  by_cases same : query = here
  · subst query
    simp [TreeFactored.setPermissions, TreeFactored.overwrite]
  · simp [TreeFactored.setPermissions, TreeFactored.overwrite, same]

theorem setPermissions_here (store : Store) (here : Path) (permissions : List Permission) :
    (TreeFactored.setPermissions store here permissions here).permissions = permissions ∧
    (TreeFactored.setPermissions store here permissions here).protection =
      (store here).protection := by
  simp [TreeFactored.setPermissions, TreeFactored.overwrite]

theorem setPermissions_other (store : Store) (here other : Path)
    (permissions : List Permission) (different : other ≠ here) :
    TreeFactored.setPermissions store here permissions other = store other := by
  simp [TreeFactored.setPermissions, TreeFactored.overwrite, different]

/-- Translate all result categories, keeping untouched leading bytes and every
other store cell. No successful-run restriction is part of the adapter. -/
def liftArray (store : Store) (here : Path) (lead : List Permission) :
    TreeReference.Result A (List Permission) → TreeFactored.Result A Store
  | .ok value permissions =>
      .ok value (TreeFactored.setPermissions store here (lead ++ permissions))
  | .ub fault permissions =>
      .ub fault (TreeFactored.setPermissions store here (lead ++ permissions))
  | .unsupported reason permissions =>
      .unsupported (structuralToFactored reason)
        (TreeFactored.setPermissions store here (lead ++ permissions))

theorem liftArray_mapState_append (store : Store) (here : Path)
    (outer inner : List Permission) (answer : TreeReference.Result A (List Permission)) :
    liftArray store here outer (answer.mapState (inner ++ ·)) =
      liftArray store here (outer ++ inner) answer := by
  cases answer <;> simp [liftArray, TreeReference.Result.mapState, List.append_assoc]

theorem liftArray_mapState_cons (store : Store) (here : Path) (lead : List Permission)
    (permission : Permission) (answer : TreeReference.Result A (List Permission)) :
    liftArray store here lead (answer.mapState (permission :: ·)) =
      liftArray store here (lead ++ [permission]) answer := by
  cases answer <;> simp [liftArray, TreeReference.Result.mapState, List.append_assoc]

theorem liftArray_rebase (store : Store) (here : Path) (initial lead : List Permission)
    (answer : TreeReference.Result A (List Permission)) :
    liftArray (TreeFactored.setPermissions store here initial) here lead answer =
      liftArray store here lead answer := by
  cases answer <;> simp only [liftArray, setPermissions_setPermissions]

theorem liftArray_resultRel (store : Store) (here : Path) (lead : List Permission)
    (answer : TreeReference.Result A (List Permission)) :
    TreeCorrespondence.ResultRel
      (fun permissions changed => changed =
        TreeFactored.setPermissions store here (lead ++ permissions))
      answer (liftArray store here lead answer) := by
  cases answer <;> simp [TreeCorrespondence.ResultRel, liftArray, structural_roundtrip]

private theorem permissionAt_after_lead (lead tail : List Permission) :
    TreeFactored.permissionAt (lead ++ tail) lead.length =
      TreeFactored.permissionAt tail 0 := by
  induction lead with
  | nil => rfl
  | cons permission rest ih =>
    simpa only [List.cons_append, List.length_cons, TreeFactored.permissionAt] using ih

private theorem replace_after_lead (lead tail : List Permission) (changed : Permission) :
    TreeFactored.replacePermission (lead ++ tail) lead.length changed =
      lead ++ TreeFactored.replacePermission tail 0 changed := by
  induction lead with
  | nil => rfl
  | cons permission rest ih =>
    simpa only [List.cons_append, List.length_cons, TreeFactored.replacePermission] using
      congrArg (permission :: ·) ih

private theorem transitionAt_after_lead (store : Store) (here : Path)
    (lead tail : List Permission) (kind : AccessKind) (relation : NodeRelation)
    (matching : (store here).permissions = lead ++ tail) :
    TreeFactored.transitionAt store here kind relation lead.length =
      match tail with
      | [] => .unsupported .range store
      | permission :: rest =>
        match permission.transition kind relation with
        | .error fault => .ub fault store
        | .ok changed =>
          .ok () (TreeFactored.setPermissions store here (lead ++ changed :: rest)) := by
  cases tail with
  | nil =>
    simp only [TreeFactored.transitionAt, matching, permissionAt_after_lead,
      TreeFactored.permissionAt]
  | cons permission rest =>
    simp only [TreeFactored.transitionAt, matching, permissionAt_after_lead,
      TreeFactored.permissionAt]
    cases permission.transition kind relation with
    | error fault => rfl
    | ok changed =>
      simp only [replace_after_lead, TreeFactored.replacePermission]

/-- Arbitrary leading bytes are fixed while the selected suffix is processed.
Counts exceeding that suffix are included: both sides retain all changes before
the matching structural range failure. -/
theorem transitionOffsets_prefix (store : Store) (here : Path) (kind : AccessKind)
    (relation : NodeRelation) (lead tail : List Permission) (count : Nat)
    (matching : (store here).permissions = lead ++ tail) :
    TreeFactored.transitionOffsets store here kind relation lead.length count =
      liftArray store here lead (TreeReference.transitionPrefix tail count kind relation) := by
  induction count generalizing store lead tail with
  | zero =>
    simp only [TreeFactored.transitionOffsets, TreeReference.transitionPrefix, liftArray]
    rw [← matching, setPermissions_current]
  | succ count ih =>
    rw [TreeFactored.transitionOffsets,
      transitionAt_after_lead store here lead tail kind relation matching]
    cases tail with
    | nil =>
      simp only [TreeFactored.Result.bind, TreeReference.transitionPrefix, liftArray,
        structuralToFactored]
      rw [← matching, setPermissions_current]
    | cons permission rest =>
      cases step : permission.transition kind relation with
      | error fault =>
        simp only [step, TreeFactored.Result.bind, TreeReference.transitionPrefix, liftArray]
        rw [← matching, setPermissions_current]
      | ok changed =>
        simp only [step, TreeFactored.Result.bind, TreeReference.transitionPrefix]
        have nextMatching :
            (TreeFactored.setPermissions store here (lead ++ changed :: rest) here).permissions =
              (lead ++ [changed]) ++ rest := by
          simp [TreeFactored.setPermissions, TreeFactored.overwrite, List.append_assoc]
        have next := ih (TreeFactored.setPermissions store here (lead ++ changed :: rest))
          (lead ++ [changed]) rest nextMatching
        simp only [List.length_append, List.length_singleton] at next
        rw [next, liftArray_rebase]
        exact (liftArray_mapState_cons store here lead changed
          (TreeReference.transitionPrefix rest count kind relation)).symm

private theorem transitionRange_after_lead (lead tail : List Permission) (count : Nat)
    (kind : AccessKind) (relation : NodeRelation) :
    TreeReference.transitionRange (lead ++ tail) lead.length count kind relation =
      (TreeReference.transitionPrefix tail count kind relation).mapState (lead ++ ·) := by
  induction lead with
  | nil =>
    simp only [List.nil_append, List.length_nil, TreeReference.transitionRange]
    cases TreeReference.transitionPrefix tail count kind relation <;> rfl
  | cons permission rest ih =>
    simp only [List.cons_append, List.length_cons, TreeReference.transitionRange]
    rw [ih]
    cases TreeReference.transitionPrefix tail count kind relation <;> rfl

private theorem split_at (permissions : List Permission) (offset : Nat)
    (within : offset ≤ permissions.length) :
    ∃ lead tail, permissions = lead ++ tail ∧ lead.length = offset := by
  induction offset generalizing permissions with
  | zero => exact ⟨[], permissions, rfl, rfl⟩
  | succ offset ih =>
    cases permissions with
    | nil => simp at within
    | cons permission rest =>
      have nextWithin : offset ≤ rest.length := by simpa using within
      obtain ⟨lead, tail, shape, lengthEq⟩ := ih rest nextWithin
      exact ⟨permission :: lead, tail, by simp [shape], by simp [lengthEq]⟩

/-- The declared byte-array domain requires offset inside or at array end.
No bound on count or scalar success is required by this stronger helper. -/
theorem transitionRange_agrees (store : Store) (here : Path) (kind : AccessKind)
    (relation : NodeRelation) (offset count : Nat)
    (within : offset ≤ (store here).permissions.length) :
    TreeFactored.transitionOffsets store here kind relation offset count =
      liftArray store here []
        (TreeReference.transitionRange (store here).permissions offset count kind relation) := by
  obtain ⟨lead, tail, matching, lengthEq⟩ := split_at (store here).permissions offset within
  rw [matching, ← lengthEq, transitionRange_after_lead, liftArray_mapState_append]
  simp only [List.nil_append]
  exact transitionOffsets_prefix store here kind relation lead tail count matching

/-- Protector-end accesses have the source's allocation-sized shape. None
entries skip scalar accesses, while every earlier real update is retained. -/
theorem releaseOffsets_prefix (store : Store) (here : Path) (relation : NodeRelation)
    (lead tail : List Permission) (accesses : List (Option AccessKind))
    (matching : (store here).permissions = lead ++ tail)
    (sameLength : tail.length = accesses.length) :
    TreeFactored.releaseOffsets store here relation lead.length accesses =
      liftArray store here lead (TreeReference.applyAccesses tail accesses relation) := by
  induction accesses generalizing store lead tail with
  | nil =>
    cases tail with
    | nil =>
      simp only [TreeFactored.releaseOffsets, TreeReference.applyAccesses, liftArray]
      rw [← matching, setPermissions_current]
    | cons permission rest => simp at sameLength
  | cons accessKind more ih =>
    cases tail with
    | nil => simp at sameLength
    | cons permission rest =>
      have restLength : rest.length = more.length := Nat.succ.inj sameLength
      cases accessKind with
      | none =>
        simp only [TreeFactored.releaseOffsets, TreeReference.applyAccesses]
        have nextMatching : (store here).permissions = (lead ++ [permission]) ++ rest := by
          simpa only [List.append_assoc, List.singleton_append] using matching
        have next := ih store (lead ++ [permission]) rest nextMatching restLength
        simp only [List.length_append, List.length_singleton] at next
        rw [next]
        exact (liftArray_mapState_cons store here lead permission
          (TreeReference.applyAccesses rest more relation)).symm
      | some kind =>
        rw [TreeFactored.releaseOffsets,
          transitionAt_after_lead store here lead (permission :: rest) kind relation matching]
        cases step : permission.transition kind relation with
        | error fault =>
          simp only [step, TreeFactored.Result.bind, TreeReference.applyAccesses, liftArray]
          rw [← matching, setPermissions_current]
        | ok changed =>
          simp only [step, TreeFactored.Result.bind, TreeReference.applyAccesses]
          have nextMatching :
              (TreeFactored.setPermissions store here (lead ++ changed :: rest) here).permissions =
                (lead ++ [changed]) ++ rest := by
            simp [TreeFactored.setPermissions, TreeFactored.overwrite, List.append_assoc]
          have next := ih (TreeFactored.setPermissions store here (lead ++ changed :: rest))
            (lead ++ [changed]) rest nextMatching restLength
          simp only [List.length_append, List.length_singleton] at next
          rw [next, liftArray_rebase]
          exact (liftArray_mapState_cons store here lead changed
            (TreeReference.applyAccesses rest more relation)).symm

theorem releaseArray_agrees (store : Store) (here : Path) (relation : NodeRelation)
    (accesses : List (Option AccessKind))
    (sameLength : (store here).permissions.length = accesses.length) :
    TreeFactored.releaseOffsets store here relation 0 accesses =
      liftArray store here []
        (TreeReference.applyAccesses (store here).permissions accesses relation) :=
  releaseOffsets_prefix store here relation [] (store here).permissions accesses rfl sameLength

/-- Every residual state of the translated array operation has the same
protector flag and every nonselected store entry, on success and on errors. -/
theorem liftArray_frame (store : Store) (here : Path) (lead : List Permission)
    (answer : TreeReference.Result A (List Permission)) :
    let changed := (liftArray store here lead answer).residual
    (changed here).protection = (store here).protection ∧
      ∀ other, other ≠ here → changed other = store other := by
  cases answer <;>
    simp only [liftArray, TreeFactored.Result.residual] <;>
    exact ⟨(setPermissions_here store here _).2,
      fun other different => setPermissions_other store here other _ different⟩

theorem transitionOffsets_frame (store : Store) (here : Path) (kind : AccessKind)
    (relation : NodeRelation) (offset count : Nat)
    (within : offset ≤ (store here).permissions.length) :
    let changed := (TreeFactored.transitionOffsets store here kind relation offset count).residual
    (changed here).protection = (store here).protection ∧
      ∀ other, other ≠ here → changed other = store other := by
  rw [transitionRange_agrees store here kind relation offset count within]
  exact liftArray_frame store here [] _

theorem releaseOffsets_frame (store : Store) (here : Path) (relation : NodeRelation)
    (accesses : List (Option AccessKind))
    (sameLength : (store here).permissions.length = accesses.length) :
    let changed := (TreeFactored.releaseOffsets store here relation 0 accesses).residual
    (changed here).protection = (store here).protection ∧
      ∀ other, other ≠ here → changed other = store other := by
  rw [releaseArray_agrees store here relation accesses sameLength]
  exact liftArray_frame store here [] _

#print axioms structural_roundtrip
#print axioms setPermissions_current
#print axioms setPermissions_setPermissions
#print axioms setPermissions_here
#print axioms setPermissions_other
#print axioms liftArray_resultRel
#print axioms transitionOffsets_prefix
#print axioms transitionRange_agrees
#print axioms releaseOffsets_prefix
#print axioms releaseArray_agrees
#print axioms liftArray_frame
#print axioms transitionOffsets_frame
#print axioms releaseOffsets_frame

end AnnealResearch.TreeOperations
