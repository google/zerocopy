import AnnealResearch.TreeReference

/-!
First positive-kind checkpoint: scalar and actual recursive-reference byte
loops preserve the complete Boolean permission/protector matching query on
every returned residual. Equality also retains initially false queries; there
is no width, valid-path, access-success, reachability, NoUB or compatibility
premise. No absent total-store cells are introduced by this reference proof.

These are observations of the unchanged runners. applyAccesses concerns only
permission transitions, not releaseCore's separate flag-clearing action. Full
recursive/public access and pending-conversion release are later checkpoints.
-/

namespace AnnealResearch.TreeKindPreservation

open TreePermissions

theorem mapState_state {A S T : Type} (answer : TreeReference.Result A S) (f : S → T) :
    (answer.mapState f).state = f answer.state := by
  cases answer <;> rfl

/-- Failure leaves the original permission; success uses the existing checked
scalar theorem. This is a result query, not another transition runner. -/
theorem scalar_matching (permission : Permission) (kind : AccessKind)
    (relation : NodeRelation) (protection : Protected) :
    (match permission.transition kind relation with
    | .ok changed => changed.matchesProtector protection
    | .error _ => permission.matchesProtector protection) =
      permission.matchesProtector protection := by
  cases acted : permission.transition kind relation with
  | error fault => rfl
  | ok changed => exact transition_preserves_matching kind relation protection acted

theorem transitionPrefix_matching (permissions : List Permission) (count : Nat)
    (kind : AccessKind) (relation : NodeRelation) (protection : Protected) :
    (TreeReference.transitionPrefix permissions count kind relation).state.all
        (fun permission => permission.matchesProtector protection) =
      permissions.all (fun permission => permission.matchesProtector protection) := by
  induction count generalizing permissions with
  | zero => cases permissions <;> rfl
  | succ count ih =>
    cases permissions with
    | nil => rfl
    | cons permission rest =>
      simp only [TreeReference.transitionPrefix]
      cases acted : permission.transition kind relation with
      | error fault => rfl
      | ok changed =>
        rw [mapState_state]
        change (changed.matchesProtector protection &&
            (TreeReference.transitionPrefix rest count kind relation).state.all
              (fun entry => entry.matchesProtector protection)) =
          (permission.matchesProtector protection &&
            rest.all (fun entry => entry.matchesProtector protection))
        rw [transition_preserves_matching kind relation protection acted, ih rest]

theorem transitionRange_matching (permissions : List Permission) (offset size : Nat)
    (kind : AccessKind) (relation : NodeRelation) (protection : Protected) :
    (TreeReference.transitionRange permissions offset size kind relation).state.all
        (fun permission => permission.matchesProtector protection) =
      permissions.all (fun permission => permission.matchesProtector protection) := by
  induction offset generalizing permissions with
  | zero =>
    cases permissions with
    | nil => exact transitionPrefix_matching [] size kind relation protection
    | cons permission rest =>
      exact transitionPrefix_matching (permission :: rest) size kind relation protection
  | succ offset ih =>
    cases permissions with
    | nil =>
      simp only [TreeReference.transitionRange]
      split <;> rfl
    | cons permission rest =>
      simp only [TreeReference.transitionRange]
      rw [mapState_state]
      change (permission.matchesProtector protection &&
          (TreeReference.transitionRange rest offset size kind relation).state.all
            (fun entry => entry.matchesProtector protection)) =
        (permission.matchesProtector protection &&
          rest.all (fun entry => entry.matchesProtector protection))
      rw [ih rest]

/-- Even unequal lists retain their exact residual query. None entries skip
the scalar access; this lemma does not clear any node's protector flag. -/
theorem applyAccesses_matching (permissions : List Permission)
    (accesses : List (Option AccessKind)) (relation : NodeRelation) (protection : Protected) :
    (TreeReference.applyAccesses permissions accesses relation).state.all
        (fun permission => permission.matchesProtector protection) =
      permissions.all (fun permission => permission.matchesProtector protection) := by
  induction accesses generalizing permissions with
  | nil => cases permissions <;> rfl
  | cons access more ih =>
    cases permissions with
    | nil => rfl
    | cons permission rest =>
      simp only [TreeReference.applyAccesses]
      cases access with
      | none =>
        rw [mapState_state]
        change (permission.matchesProtector protection &&
            (TreeReference.applyAccesses rest more relation).state.all
              (fun entry => entry.matchesProtector protection)) =
          (permission.matchesProtector protection &&
            rest.all (fun entry => entry.matchesProtector protection))
        rw [ih rest]
      | some kind =>
        dsimp only
        cases acted : permission.transition kind relation with
        | error fault => rfl
        | ok changed =>
          rw [mapState_state]
          change (changed.matchesProtector protection &&
              (TreeReference.applyAccesses rest more relation).state.all
                (fun entry => entry.matchesProtector protection)) =
            (permission.matchesProtector protection &&
              rest.all (fun entry => entry.matchesProtector protection))
          rw [transition_preserves_matching kind relation protection acted, ih rest]

#print axioms mapState_state
#print axioms scalar_matching
#print axioms transitionPrefix_matching
#print axioms transitionRange_matching
#print axioms applyAccesses_matching

end AnnealResearch.TreeKindPreservation
