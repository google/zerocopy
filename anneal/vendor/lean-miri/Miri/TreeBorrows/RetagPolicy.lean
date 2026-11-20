import Miri.TreeBorrows.Permissions
import Miri.TreeBorrows.GlobalState
import Miri.TreeBorrows.TreeState

/-!
The permission-selection policy in pinned Miri's `NewPermission::new`.
Rust type/layout facts and interpreter configuration are explicit inputs; this
module does not model rustc type queries, pointer checks, or the full retag
caller.
-/

namespace Miri.TreeBorrows.RetagPolicy

inductive RetagMode where
  | None
  | Default
  | TwoPhase
  | FnEntry
  | Raw
  deriving DecidableEq, Repr, Inhabited

inductive ReferenceKind where
  | Shared
  | Mutable
  | Box
  deriving DecidableEq, Repr, Inhabited

structure TypeFacts where
  isUnpin : Bool
  isUnsafeUnpin : Bool
  isFreeze : Bool
  deriving DecidableEq, Repr, Inhabited

structure PolicyConfig where
  implicitWrites : Bool
  rustcNoWritable : Bool
  deriving DecidableEq, Repr, Inhabited

structure NewPermission where
  freezePermission : Permission
  nonfreezePermission : Permission
  outsidePermission : Permission
  protector : Option ProtectorKind
  deriving DecidableEq, Repr

private inductive Part where
  | InsideFrozen
  | InsideUnsafeCell
  | Outside
  deriving DecidableEq, Repr

private def selectedPermission (kind : ReferenceKind) (part : Part)
    (frozen isProtected implicitWrites : Bool) : Permission :=
  match kind with
  | .Shared => if frozen then .Frozen else .Cell
  | .Mutable | .Box =>
      if implicitWrites && part != .Outside then .Unique
      else if isProtected || frozen then .ReservedFrz false
      else .ReservedIM

/-- Source `NewPermission::new` policy, with the rustc type queries and
`#[rustc_no_writable]` lookup supplied as finite inputs.

`None` covers both disabled retagging and the source's mutable/Box pinning
early return. Other interpreter operations around reborrowing remain outside
this policy function.
-/
def create (facts : TypeFacts) (kind : ReferenceKind) (mode : RetagMode)
    (config : PolicyConfig) : Option NewPermission := Id.run do
  if mode == .None then return none
  let tyIsUnpin := facts.isUnpin && facts.isUnsafeUnpin
  let isProtected := mode == .FnEntry
  let implicitWritesEnabled := isProtected && config.implicitWrites &&
    !config.rustcNoWritable
  if (kind == .Mutable || kind == .Box) && !tyIsUnpin then
    return none
  let choose (part : Part) :=
    let frozen := match part with
      | .InsideFrozen => true
      | .InsideUnsafeCell => false
      | .Outside => facts.isFreeze
    selectedPermission kind part frozen isProtected implicitWritesEnabled
  let protector :=
    if isProtected then
      some (if kind == .Box then .WeakProtector else .StrongProtector)
    else none
  return some {
    freezePermission := choose .InsideFrozen
    nonfreezePermission := choose .InsideUnsafeCell
    outsidePermission := choose .Outside
    protector
  }

/-- The source `tb_reborrow` closure selecting its permission for a frozen or
UnsafeCell byte and constructing the matching accessed/future location state.
The freeze-sensitive layout visitor that chooses `frozen` is a separate hook.
-/
inductive InitialStateError where
  | protectedReservedIM
  | invalidLazyPermission (permission : Permission)
  | lazyUnique
  deriving DecidableEq, Repr

def initialLocationState (policy : NewPermission) (frozen : Bool) :
    Except InitialStateError Tree.LocationState := do
  let permission := if frozen then policy.freezePermission else policy.nonfreezePermission
  let isProtected := policy.protector.isSome
  let sifa ← match permission.strongestIdempotentForeignAccess isProtected with
    | .Access sifa => pure sifa
    | .ImpossibleProtectedReservedIM => throw InitialStateError.protectedReservedIM
  if permission.associatedAccess.isSome then
    return Tree.LocationState.newAccessed permission sifa
  else
    match Tree.LocationState.newNonAccessed permission sifa with
    | .Constructed state => return state
    | .PermissionNotInitialOrDisabled => throw (.invalidLazyPermission permission)
    | .UniquePermissionNotAccessed => throw .lazyUnique

theorem none_mode_never_creates_permission (facts : TypeFacts)
    (kind : ReferenceKind) (config : PolicyConfig) :
    create facts kind .None config = none := by
  simp [create]

theorem pinned_mutable_reference_is_not_retagged (facts : TypeFacts)
    (config : PolicyConfig) (h : !(facts.isUnpin && facts.isUnsafeUnpin)) :
    create facts .Mutable .Default config = none := by
  simp [create, h]

theorem pinned_box_is_not_retagged (facts : TypeFacts)
    (config : PolicyConfig) (h : !(facts.isUnpin && facts.isUnsafeUnpin)) :
    create facts .Box .FnEntry config = none := by
  simp [create, h]

theorem shared_cell_starts_unaccessed :
    initialLocationState ⟨.Frozen, .Cell, .Cell, none⟩ false =
      .ok ⟨.Cell, false, .Write⟩ := by
  simp [initialLocationState, Permission.strongestIdempotentForeignAccess,
    Permission.associatedAccess, Tree.LocationState.newNonAccessed,
    Permission.isInitial, Permission.isDisabled, Permission.isUnique] <;> rfl

theorem unique_reborrow_starts_accessed :
    initialLocationState ⟨.Unique, .Unique, .ReservedFrz false, none⟩ true =
      .ok ⟨.Unique, true, .None⟩ := by
  simp [initialLocationState, Permission.strongestIdempotentForeignAccess,
    Permission.associatedAccess, Tree.LocationState.newAccessed] <;> rfl

end Miri.TreeBorrows.RetagPolicy
