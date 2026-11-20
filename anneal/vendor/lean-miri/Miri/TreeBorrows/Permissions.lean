/-!
Tree Borrows permission states and the per-node access transition function.

This is a port of `transition::{child_read, foreign_read, child_write,
foreign_write, perform_access}` in the pinned Miri source:
`upstream/miri-source/src/borrow_tracker/tree_borrows/perms.rs`.
The corresponding upstream revision is
`7fa591d7d4dd9af8154becbc8332f8096f8323b1` (blob
`0dd4712b85c7d660eb0a4395223335b2b766062b`).

This module models only one permission at one location. It does not model a
borrow tree, provenance, memory, initialization, protector lifetime, or
diagnostic transition history.
-/

namespace Miri.TreeBorrows

/-- The activation states of a Tree Borrows pointer. -/
inductive Permission where
  /-- A shared reference to interior mutable data. -/
  | Cell
  /-- A local mutable reference not yet written through. -/
  | ReservedFrz (conflicted : Bool)
  /-- A reservation to interior mutable data. -/
  | ReservedIM
  /-- A unique pointer. -/
  | Unique
  /-- A shared, read-only pointer. -/
  | Frozen
  /-- A disabled pointer. -/
  | Disabled
  deriving DecidableEq, Repr, Inhabited

/-- The access kind used by Miri's borrow tracker. -/
inductive AccessKind where
  | Read
  | Write
  deriving DecidableEq, Repr, Inhabited

/-- Whether an access is through this node or one of its children. -/
inductive AccessRelatedness where
  | LocalAccess
  | ForeignAccess
  deriving DecidableEq, Repr, Inhabited

/-- `true` exactly for an ancestor, sibling, cousin, or other non-child access. -/
def AccessRelatedness.isForeign : AccessRelatedness → Bool
  | .LocalAccess => false
  | .ForeignAccess => true

/-- Outcomes of Miri's `Option<PermissionPriv>` transition function.

`UndefinedBehavior` corresponds to upstream `None` for a forbidden child
access. `ImpossibleProtectedReservedIM` preserves the upstream `assert!(!protected)`
branches: those are invariant failures, not ordinary UB outcomes. -/
inductive AccessOutcome where
  | Transition (permission : Permission)
  | UndefinedBehavior
  | ImpossibleProtectedReservedIM
  deriving DecidableEq, Repr, Inhabited

private def childRead (state : Permission) : AccessOutcome :=
  match state with
  | .Disabled => .UndefinedBehavior
  | readable => .Transition readable

private def foreignRead (state : Permission) (isProtected : Bool) : AccessOutcome :=
  match state with
  | .Cell => .Transition .Cell
  | .Frozen => .Transition .Frozen
  | .Disabled => .Transition .Disabled
  | .ReservedFrz _ =>
      if isProtected then .Transition (.ReservedFrz true)
      else .Transition state
  | .ReservedIM =>
      if isProtected then .ImpossibleProtectedReservedIM
      else .Transition .ReservedIM
  | .Unique =>
      if isProtected then .Transition .Disabled
      else .Transition .Frozen

private def childWrite (state : Permission) (isProtected : Bool) : AccessOutcome :=
  match state with
  | .Cell => .Transition .Cell
  | .ReservedFrz true =>
      if isProtected then .UndefinedBehavior else .Transition .Unique
  | .ReservedFrz false => .Transition .Unique
  | .ReservedIM => .Transition .Unique
  | .Unique => .Transition .Unique
  | .Frozen => .UndefinedBehavior
  | .Disabled => .UndefinedBehavior

private def foreignWrite (state : Permission) (isProtected : Bool) : AccessOutcome :=
  match state with
  | .Cell => .Transition .Cell
  | .ReservedIM =>
      if isProtected then .ImpossibleProtectedReservedIM
      else .Transition .ReservedIM
  | _ => .Transition .Disabled

/-- Apply the pinned Miri transition rules to one permission.

The dispatcher is the same four-way match as upstream on `(kind,
rel_pos.is_foreign())`. -/
def performAccess (kind : AccessKind) (relPos : AccessRelatedness)
    (old : Permission) (isProtected : Bool) : AccessOutcome :=
  match kind, relPos.isForeign with
  | .Write, true => foreignWrite old isProtected
  | .Read, true => foreignRead old isProtected
  | .Write, false => childWrite old isProtected
  | .Read, false => childRead old

/-- Whether this permission is one of the upstream initial states. -/
def Permission.isInitial : Permission → Bool
  | .ReservedFrz false | .Frozen | .ReservedIM | .Cell | .Unique => true
  | .ReservedFrz true | .Disabled => false

/-- Source ordering by reachability of permission transitions.

This captures the `PartialOrd` relation from `PermissionPriv::partial_cmp`:
Cell is isolated; ReservedIM is incomparable with either ReservedFrz state;
all remaining reachable states form the Reserved → Unique → Frozen → Disabled
chain, with the conflicted Reserved state above the unconflicted one. -/
def permissionLE : Permission → Permission → Bool
  | .Cell, .Cell => true
  | .ReservedFrz false, .ReservedFrz _ => true
  | .ReservedFrz true, .ReservedFrz true => true
  | .ReservedFrz _, .Unique => true
  | .ReservedFrz _, .Frozen => true
  | .ReservedFrz _, .Disabled => true
  | .ReservedIM, .ReservedIM => true
  | .ReservedIM, .Unique => true
  | .ReservedIM, .Frozen => true
  | .ReservedIM, .Disabled => true
  | .Unique, .Unique => true
  | .Unique, .Frozen => true
  | .Unique, .Disabled => true
  | .Frozen, .Frozen => true
  | .Frozen, .Disabled => true
  | .Disabled, .Disabled => true
  | _, _ => false

/-- Result corresponding to Rust's `Option<Ordering>` for the source
`PermissionPriv::partial_cmp`. -/
inductive PermissionOrdering where
  | Incomparable
  | Less
  | Equal
  | Greater
  deriving DecidableEq, Repr, Inhabited

def permissionCompare (left right : Permission) : PermissionOrdering :=
  if permissionLE left right then
    if permissionLE right left then .Equal else .Less
  else if permissionLE right left then .Greater else .Incomparable

/-- Whether a local access to a permission is allowed by the wildcard cache. -/
inductive WildcardAccessLevel where
  | None
  | Read
  | Write
  deriving DecidableEq, Repr, Inhabited

/-- Whether a foreign access can be skipped after a recorded subtree access. -/
inductive IdempotentForeignAccess where
  | None
  | Read
  | Write
  deriving DecidableEq, Repr, Inhabited

namespace WildcardAccessLevel

def rank : WildcardAccessLevel → Nat
  | .None => 0
  | .Read => 1
  | .Write => 2

/-- Whether this cached access level allows the requested access kind. -/
def allows (level : WildcardAccessLevel) (kind : AccessKind) : Bool :=
  match level, kind with
  | .None, _ => false
  | .Read, .Read => true
  | .Read, .Write => false
  | .Write, _ => true

end WildcardAccessLevel

namespace IdempotentForeignAccess

def rank : IdempotentForeignAccess → Nat
  | .None => 0
  | .Read => 1
  | .Write => 2

def isLocal : IdempotentForeignAccess → Bool
  | .None => true
  | .Read | .Write => false

def isForeign (access : IdempotentForeignAccess) : Bool := !access.isLocal

/-- Source order used by Miri: `None < Read < Write`. -/
def le (left right : IdempotentForeignAccess) : Bool := left.rank ≤ right.rank

def max (left right : IdempotentForeignAccess) : IdempotentForeignAccess :=
  if left.rank ≤ right.rank then right else left

/-- Construct a foreign access from its access kind. -/
def fromForeign : AccessKind → IdempotentForeignAccess
  | .Read => .Read
  | .Write => .Write

/-- Convert an access and its relation to the cache's recorded-access value. -/
def fromAccessAndRelatedness (kind : AccessKind) (relatedness : AccessRelatedness) :
    IdempotentForeignAccess :=
  if relatedness.isForeign then fromForeign kind else .None

/-- Result of the source skip check, including its debug assertion. -/
inductive SkipCheckResult where
  | Decision (canSkip : Bool)
  | DebugAssertion
  deriving DecidableEq, Repr, Inhabited

/-- Whether the recorded access allows skipping the next foreign access.

The source's `debug_assert!(happeningNext.is_foreign())` is represented
explicitly for calls outside its documented domain. -/
def canSkipForeignAccess (recorded happeningNext : IdempotentForeignAccess) : SkipCheckResult :=
  if happeningNext.isLocal then .DebugAssertion
  else .Decision (le happeningNext recorded)

/-- Update a recorded access exactly as the source `record_new` method does. -/
def recordNew (recorded justHappened : IdempotentForeignAccess) : IdempotentForeignAccess :=
  if justHappened.isLocal then .None else max recorded justHappened

/-- Weaken a cache value when a newly inserted child has a weaker value. -/
def ensureNoStrongerThan (recorded strongestAllowed : IdempotentForeignAccess) :
    IdempotentForeignAccess × Bool :=
  if strongestAllowed.rank < recorded.rank then (strongestAllowed, true) else (recorded, false)

end IdempotentForeignAccess

namespace Permission

def isDisabled : Permission → Bool
  | .Disabled => true
  | _ => false

def isFrozen : Permission → Bool
  | .Frozen => true
  | _ => false

def isCell : Permission → Bool
  | .Cell => true
  | _ => false

def isUnique : Permission → Bool
  | .Unique => true
  | _ => false

def newUnique : Permission := .Unique
def newReservedFrz : Permission := .ReservedFrz false
def newReservedIM : Permission := .ReservedIM
def newFrozen : Permission := .Frozen
def newDisabled : Permission := .Disabled
def newCell : Permission := .Cell

/-- The access Miri associates with this permission when releasing protection or reborrowing. -/
def associatedAccess : Permission → Option AccessKind
  | .Cell => none
  | .Unique => some .Write
  | _ => some .Read

/-- Whether a parent permission can be soundly replaced by the given child
during the source's tree compaction. The caller must ensure the parent is not
protected, as the source documents. -/
def canBeReplacedByChild (parent child : Permission) : Bool :=
  match parent, child with
  | .Cell, _ => true
  | _, .Cell => false
  | .ReservedIM, _ => true
  | _, .ReservedIM => false
  | .ReservedFrz _, _ => true
  | _, .ReservedFrz _ => false
  | .Unique, .Unique | .Unique, .Frozen | .Unique, .Disabled => true
  | _, .Unique => false
  | .Frozen, .Frozen | .Frozen, .Disabled => true
  | _, .Frozen => false
  | .Disabled, .Disabled => true

/-- Strongest foreign action this node survives unchanged.

`ImpossibleProtectedReservedIM` preserves the upstream `unreachable!` branch
as an invariant failure instead of treating it as an ordinary result. -/
inductive IdempotentAccessResult where
  | Access (access : IdempotentForeignAccess)
  | ImpossibleProtectedReservedIM
  deriving DecidableEq, Repr, Inhabited

def strongestIdempotentForeignAccess (permission : Permission) (isProtected : Bool) :
    IdempotentAccessResult :=
  match permission with
  | .Cell => .Access .Write
  | .ReservedFrz false => if isProtected then .Access .None else .Access .Read
  | .ReservedFrz true => .Access .Read
  | .ReservedIM => if isProtected then .ImpossibleProtectedReservedIM else .Access .Write
  | .Unique => .Access .None
  | .Frozen => .Access .Read
  | .Disabled => .Access .Write

/-- Strongest local access that does not cause UB, used by wildcard tracking. -/
def strongestAllowedLocalAccess (permission : Permission) (isProtected : Bool) :
    WildcardAccessLevel :=
  match permission with
  | .Disabled => .None
  | .Frozen => .Read
  | .ReservedFrz true => if isProtected then .Read else .Write
  | _ => .Write

end Permission

/-- A transition reconstructed by the source diagnostics and permission API. -/
structure PermTransition where
  fromPermission : Permission
  toPermission : Permission
  deriving DecidableEq, Repr

namespace PermTransition

def isPossible (transition : PermTransition) : Bool :=
  permissionLE transition.fromPermission transition.toPermission

def isNoop (transition : PermTransition) : Bool :=
  transition.fromPermission == transition.toPermission

/-- Apply this transition only when the supplied starting permission matches. -/
def applied (transition : PermTransition) (startingPoint : Permission) : Option Permission :=
  if startingPoint == transition.fromPermission then some transition.toPermission else none

def producesDisabled (transition : PermTransition) : Bool :=
  transition.toPermission.isDisabled

def endpoint (transition : PermTransition) : Permission := transition.toPermission

end PermTransition

/-- Permission-level result of the public source `Permission::perform_access`
wrapper, retaining an explicit label for its invariant panic. -/
inductive PermTransitionOutcome where
  | Transition (transition : PermTransition)
  | UndefinedBehavior
  | ImpossibleProtectedReservedIM
  deriving DecidableEq, Repr, Inhabited

/-- Convert the per-node result to the source `PermTransition` wrapper form. -/
def performAccessTransition (kind : AccessKind) (relPos : AccessRelatedness)
    (old : Permission) (isProtected : Bool) : PermTransitionOutcome :=
  match performAccess kind relPos old isProtected with
  | .Transition next => .Transition ⟨old, next⟩
  | .UndefinedBehavior => .UndefinedBehavior
  | .ImpossibleProtectedReservedIM => .ImpossibleProtectedReservedIM

/-- A write activates an unconflicted two-phase reservation. -/
theorem reserved_local_write_activates :
    performAccessTransition .Write .LocalAccess (.ReservedFrz false) false =
      .Transition ⟨.ReservedFrz false, .Unique⟩ := rfl

theorem cell_is_unchanged (kind : AccessKind) (relPos : AccessRelatedness)
    (isProtected : Bool) :
    performAccess kind relPos .Cell isProtected = .Transition .Cell := by
  cases kind <;> cases relPos <;> cases isProtected <;> rfl

/-- If the protector invariant holds, the two upstream assertion branches are
unreachable. The invariant excludes only protected ReservedIM; Cell may be
protected, as in upstream behavior. -/
theorem valid_protector_avoids_invariant_failure (kind : AccessKind)
    (relPos : AccessRelatedness) (state : Permission) (isProtected : Bool)
    (h : isProtected = false ∨ state ≠ .ReservedIM) :
    performAccess kind relPos state isProtected ≠ .ImpossibleProtectedReservedIM := by
  cases kind <;> cases relPos <;> cases state with
  | Cell =>
      cases isProtected <;>
        simp_all [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite]
  | ReservedFrz conflicted =>
      cases conflicted <;> cases isProtected <;>
        simp_all [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite]
  | ReservedIM =>
      cases isProtected <;>
        simp_all [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite]
  | Unique =>
      cases isProtected <;>
        simp_all [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite]
  | Frozen =>
      cases isProtected <;>
        simp_all [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite]
  | Disabled =>
      cases isProtected <;>
        simp_all [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite]

/-- Every successful per-node transition is nondecreasing in Miri's source
permission ordering. -/
theorem successful_transition_is_monotone (kind : AccessKind)
    (relPos : AccessRelatedness) (state next : Permission) (isProtected : Bool)
    (h : performAccess kind relPos state isProtected = .Transition next) :
    permissionLE state next = true := by
  cases kind <;> cases relPos <;> cases state with
  | Cell =>
      cases isProtected <;>
        (simp [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite] at h <;>
          cases h <;> simp [permissionLE])
  | ReservedFrz conflicted =>
      cases conflicted <;> cases isProtected <;>
        (simp [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite] at h <;>
          cases h <;> simp [permissionLE])
  | ReservedIM =>
      cases isProtected <;>
        (simp [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite] at h <;>
          cases h <;> simp [permissionLE])
  | Unique =>
      cases isProtected <;>
        (simp [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite] at h <;>
          cases h <;> simp [permissionLE])
  | Frozen =>
      cases isProtected <;>
        (simp [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite] at h <;>
          cases h <;> simp [permissionLE])
  | Disabled =>
      cases isProtected <;>
        (simp [performAccess, AccessRelatedness.isForeign, foreignRead,
          foreignWrite, childRead, childWrite] at h <;>
          cases h <;> simp [permissionLE])

/-- Tree compaction always permits replacing a permission with itself. -/
theorem can_replace_permission_by_itself (state : Permission) :
    Permission.canBeReplacedByChild state state = true := by
  cases state with
  | Cell => rfl
  | ReservedFrz conflicted => cases conflicted <;> rfl
  | ReservedIM => rfl
  | Unique => rfl
  | Frozen => rfl
  | Disabled => rfl

/-- The strongest-local-access summary agrees with the local read/write
transition function: it allows exactly the accesses that are not UB. -/
theorem strongest_local_access_matches_transition (state : Permission)
    (isProtected : Bool) (kind : AccessKind) :
    WildcardAccessLevel.allows (Permission.strongestAllowedLocalAccess state isProtected) kind =
      match performAccess kind .LocalAccess state isProtected with
      | .Transition _ => true
      | .UndefinedBehavior | .ImpossibleProtectedReservedIM => false := by
  cases state with
  | Cell => cases kind <;> cases isProtected <;>
      simp [Permission.strongestAllowedLocalAccess, WildcardAccessLevel.allows,
        performAccess, AccessRelatedness.isForeign, childRead, childWrite]
  | ReservedFrz conflicted => cases conflicted <;> cases kind <;> cases isProtected <;>
      simp [Permission.strongestAllowedLocalAccess, WildcardAccessLevel.allows,
        performAccess, AccessRelatedness.isForeign, childRead, childWrite]
  | ReservedIM => cases kind <;> cases isProtected <;>
      simp [Permission.strongestAllowedLocalAccess, WildcardAccessLevel.allows,
        performAccess, AccessRelatedness.isForeign, childRead, childWrite]
  | Unique => cases kind <;> cases isProtected <;>
      simp [Permission.strongestAllowedLocalAccess, WildcardAccessLevel.allows,
        performAccess, AccessRelatedness.isForeign, childRead, childWrite]
  | Frozen => cases kind <;> cases isProtected <;>
      simp [Permission.strongestAllowedLocalAccess, WildcardAccessLevel.allows,
        performAccess, AccessRelatedness.isForeign, childRead, childWrite]
  | Disabled => cases kind <;> cases isProtected <;>
      simp [Permission.strongestAllowedLocalAccess, WildcardAccessLevel.allows,
        performAccess, AccessRelatedness.isForeign, childRead, childWrite]

/-- A recorded local access resets SIFA regardless of the previous value. -/
theorem record_local_access_resets_sifa (recorded : IdempotentForeignAccess) :
    IdempotentForeignAccess.recordNew recorded .None = .None := by
  cases recorded <;> rfl

/-- A successful source transition can be applied only at its recorded source
state, and then returns the recorded endpoint. -/
theorem transition_applied_at_source (transition : PermTransition) :
    transition.applied transition.fromPermission = some transition.toPermission := by
  simp [PermTransition.applied]

/-- A permission marked idempotent under foreign reads really is unchanged by
the source foreign-read transition. -/
theorem sifa_read_is_stable (state : Permission) (isProtected : Bool)
    (h : Permission.strongestIdempotentForeignAccess state isProtected =
      .Access .Read) :
    performAccess .Read .ForeignAccess state isProtected = .Transition state := by
  cases state with
  | Cell => cases isProtected <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead])
  | ReservedFrz conflicted => cases conflicted <;> cases isProtected <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead])
  | ReservedIM => cases isProtected <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead])
  | Unique => cases isProtected <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead])
  | Frozen => cases isProtected <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead])
  | Disabled => cases isProtected <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead])

/-- A permission marked idempotent under foreign writes is unchanged by both
foreign read and write transitions. -/
theorem sifa_write_is_stable (state : Permission) (isProtected : Bool)
    (h : Permission.strongestIdempotentForeignAccess state isProtected =
      .Access .Write) (kind : AccessKind) :
    performAccess kind .ForeignAccess state isProtected = .Transition state := by
  cases state with
  | Cell => cases isProtected <;> cases kind <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead, foreignWrite])
  | ReservedFrz conflicted => cases conflicted <;> cases isProtected <;> cases kind <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead, foreignWrite])
  | ReservedIM => cases isProtected <;> cases kind <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead, foreignWrite])
  | Unique => cases isProtected <;> cases kind <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead, foreignWrite])
  | Frozen => cases isProtected <;> cases kind <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead, foreignWrite])
  | Disabled => cases isProtected <;> cases kind <;>
      (simp_all [Permission.strongestIdempotentForeignAccess] <;>
        simp [performAccess, AccessRelatedness.isForeign, foreignRead, foreignWrite])

end Miri.TreeBorrows
