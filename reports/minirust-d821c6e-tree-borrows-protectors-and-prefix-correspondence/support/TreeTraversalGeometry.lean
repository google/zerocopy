import AnnealResearch.TreeUnprotectWidths

/-!
Structural geometry of the unchanged independent factored tree operations.
SameLengths observes every total-store cell's permission-list length; Geometry
also preserves the complete ordered topology. Permission values and protector
flags are deliberately unrestricted. No operation-success, array-width, valid
path, NoUB or permission/protector compatibility premise is used.

This first checkpoint covers scalar updates and finite offset loops in every
result category. Mutual traversal and public access/release geometry remain
explicit pending obligations until this reusable layer is checked.
-/

namespace AnnealResearch.TreeTraversalGeometry

open TreePermissions
open TreeFactored (Path Topology Forest Entry Store State)

/-- Direction is input then residual, with equality oriented residual-to-input. -/
def SameLengths (before after : Store) : Prop :=
  ∀ query, (after query).permissions.length = (before query).permissions.length

def Geometry (before after : State) : Prop :=
  after.topology = before.topology ∧ SameLengths before.store after.store

theorem sameLengths_refl (store : Store) : SameLengths store store := fun _ => rfl

theorem sameLengths_trans (first second third : Store)
    (left : SameLengths first second) (right : SameLengths second third) :
    SameLengths first third := fun query => (right query).trans (left query)

theorem geometry_refl (state : State) : Geometry state state :=
  ⟨rfl, sameLengths_refl state.store⟩

theorem geometry_trans (first second third : State)
    (left : Geometry first second) (right : Geometry second third) :
    Geometry first third :=
  ⟨right.1.trans left.1, sameLengths_trans first.store second.store third.store left.2 right.2⟩

theorem replacePermission_length (permissions : List Permission) (offset : Nat)
    (replacement : Permission) :
    (TreeFactored.replacePermission permissions offset replacement).length = permissions.length := by
  induction permissions generalizing offset with
  | nil => rfl
  | cons first rest ih =>
      cases offset with
      | zero => rfl
      | succ offset =>
          change (TreeFactored.replacePermission rest offset replacement).length + 1 = rest.length + 1
          rw [ih offset]

theorem setPermissions_sameLengths (store : Store) (path : Path)
    (permissions : List Permission)
    (length : permissions.length = (store path).permissions.length) :
    SameLengths store (TreeFactored.setPermissions store path permissions) := by
  intro query
  by_cases same : query = path
  · subst query
    rw [(TreeOperations.setPermissions_here store path permissions).1]
    exact length
  · rw [TreeOperations.setPermissions_other store path query permissions same]

theorem setProtected_sameLengths (store : Store) (path : Path) (protection : Protected) :
    SameLengths store (TreeFactored.setProtected store path protection) := by
  intro query
  by_cases same : query = path
  · subst query
    simp [TreeFactored.setProtected, TreeFactored.overwrite]
  · simp [TreeFactored.setProtected, TreeFactored.overwrite, same]

/-- A failing bind retains its actual residual store. Only the success branch
runs its continuation; both branches preserve the same structural metric. -/
theorem bind_sameLengths {A B : Type} (before : Store)
    (answer : TreeFactored.Result A Store)
    (next : A → Store → TreeFactored.Result B Store)
    (first : SameLengths before answer.residual)
    (continued : ∀ value changed, SameLengths changed (next value changed).residual) :
    SameLengths before (answer.bind next).residual := by
  cases answer with
  | ok value changed =>
      exact sameLengths_trans before changed _ first (continued value changed)
  | ub fault changed => exact first
  | unsupported reason changed => exact first

theorem transitionAt_sameLengths (store : Store) (here : Path) (kind : AccessKind)
    (relation : NodeRelation) (offset : Nat) :
    SameLengths store (TreeFactored.transitionAt store here kind relation offset).residual := by
  unfold TreeFactored.transitionAt
  dsimp only
  cases TreeFactored.permissionAt (store here).permissions offset with
  | none => exact sameLengths_refl store
  | some permission =>
      dsimp only
      cases permission.transition kind relation with
      | error fault => exact sameLengths_refl store
      | ok changed =>
          exact setPermissions_sameLengths store here _
            (replacePermission_length (store here).permissions offset changed)

theorem transitionOffsets_sameLengths (store : Store) (here : Path) (kind : AccessKind)
    (relation : NodeRelation) (offset count : Nat) :
    SameLengths store
      (TreeFactored.transitionOffsets store here kind relation offset count).residual := by
  induction count generalizing store offset with
  | zero => exact sameLengths_refl store
  | succ count ih =>
      rw [TreeFactored.transitionOffsets]
      exact bind_sameLengths store _ _
        (transitionAt_sameLengths store here kind relation offset)
        (fun _ changed => ih changed (offset + 1))

theorem releaseOffsets_sameLengths (store : Store) (here : Path) (relation : NodeRelation)
    (offset : Nat) (accesses : List (Option AccessKind)) :
    SameLengths store (TreeFactored.releaseOffsets store here relation offset accesses).residual := by
  induction accesses generalizing store offset with
  | nil => exact sameLengths_refl store
  | cons access rest ih =>
      cases access with
      | none => exact ih store (offset + 1)
      | some kind =>
          rw [TreeFactored.releaseOffsets]
          exact bind_sameLengths store _ _
            (transitionAt_sameLengths store here kind relation offset)
            (fun _ changed => ih changed (offset + 1))

theorem mapStore_geometry {A : Type} (state : State) (answer : TreeFactored.Result A Store)
    (lengths : SameLengths state.store answer.residual) :
    Geometry state (answer.mapState (fun store => { state with store })).residual := by
  cases answer <;> exact ⟨rfl, lengths⟩

/-- Reuse the already checked complete-list conversion geometry. -/
theorem unprotectAt_geometry (state : State) (path : Path) :
    Geometry state (TreeFactored.unprotectAt state path).residual :=
  TreeUnprotectWidths.unprotectAt_geometry state path

theorem geometry_arrayLengths (before after : State) (width : Nat)
    (same : Geometry before after) :
    TreeFactored.arrayLengthsTree after.topology [] after.store width =
      TreeFactored.arrayLengthsTree before.topology [] before.store width := by
  rw [same.1]
  exact TreeUnprotectWidths.arrayLengthsTree_congr_lengths before.topology []
    after.store before.store width same.2

#print axioms sameLengths_refl
#print axioms sameLengths_trans
#print axioms geometry_refl
#print axioms geometry_trans
#print axioms replacePermission_length
#print axioms setPermissions_sameLengths
#print axioms setProtected_sameLengths
#print axioms bind_sameLengths
#print axioms transitionAt_sameLengths
#print axioms transitionOffsets_sameLengths
#print axioms releaseOffsets_sameLengths
#print axioms mapStore_geometry
#print axioms unprotectAt_geometry
#print axioms geometry_arrayLengths

end AnnealResearch.TreeTraversalGeometry
