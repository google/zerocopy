import Std

/-!
Shared scalar tables for the selected MiniRust Tree Borrows source at
d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed. These definitions manually bind the
complete protected/unprotected permission cases in state_machine*.md.

The tables may be shared by later recursive reference and factored tree cores;
sharing them is not a proof of independently implemented scalar semantics.
No Rust, generated-interpreter, full Tree Borrows adequacy, access-success, or
NoUB theorem is asserted. Scalar faults below denote source UB branches only.
-/

namespace AnnealResearch.TreePermissions

inductive AccessKind where
  | read | write
  deriving DecidableEq, Repr

inductive NodeRelation where
  | localNode | foreignNode
  deriving DecidableEq, Repr

inductive Protected where
  | no | weak | strong
  deriving DecidableEq, Repr

def Protected.yes : Protected → Bool
  | .no => false | .weak | .strong => true

inductive UPermission where
  | cell | reserved | reservedIm | unique | frozen | disabled
  deriving DecidableEq, Repr

inductive PPermission where
  | cell
  | reserved (hadLocalRead hadForeignRead : Bool)
  | unique
  | frozen (hadLocalRead : Bool)
  | disabled
  deriving DecidableEq, Repr

/-- Categories distinguish the attempted operation even when two source
diagnostic strings coincide. sourceMessage retains the pinned spelling. -/
inductive Fault where
  | unprotectedLocalReadDisabled
  | unprotectedLocalWriteFrozen
  | unprotectedLocalWriteDisabled
  | protectedLocalReadDisabled
  | protectedLocalWriteReservedAfterForeignRead
  | protectedLocalWriteFrozen
  | protectedLocalWriteDisabled
  | protectedForeignReadUnique
  | protectedForeignWriteFrozenAfterLocalRead
  | protectedForeignWriteReservedAfterLocalRead
  | protectedForeignWriteUnique
  deriving DecidableEq, Repr

def Fault.sourceMessage : Fault → String
  | .unprotectedLocalReadDisabled => "Tree Borrows: local read of Disabled reference"
  | .unprotectedLocalWriteFrozen => "Tree Borrows: local write of Frozen reference"
  | .unprotectedLocalWriteDisabled => "Tree Borrows: local write of Disabled reference"
  | .protectedLocalReadDisabled => "Tree Borrows: local read of protected Disabled reference"
  | .protectedLocalWriteReservedAfterForeignRead =>
      "Tree Borrows: local write to protected Reserved reference that had a foreign read"
  | .protectedLocalWriteFrozen => "Tree Borrows: local write to protected Frozen reference"
  | .protectedLocalWriteDisabled => "Tree Borrows: local write to protected Disabled reference"
  | .protectedForeignReadUnique => "Tree Borrows: foreign read of protected Unique reference"
  | .protectedForeignWriteFrozenAfterLocalRead =>
      "Tree Borrows: foreign write of protected Frozen reference which had a local read"
  | .protectedForeignWriteReservedAfterLocalRead =>
      "Tree Borrows: foreign write of protected Reserved reference which had a local read"
  | .protectedForeignWriteUnique =>
      "Tree Borrows: foreign read of protected Unique reference"

namespace UPermission

def localRead : UPermission → Except Fault UPermission
  | .disabled => .error .unprotectedLocalReadDisabled
  | permission => .ok permission

def localWrite : UPermission → Except Fault UPermission
  | .frozen => .error .unprotectedLocalWriteFrozen
  | .disabled => .error .unprotectedLocalWriteDisabled
  | .cell => .ok .cell
  | _ => .ok .unique

def foreignRead : UPermission → Except Fault UPermission
  | .unique => .ok .frozen
  | permission => .ok permission

def foreignWrite : UPermission → Except Fault UPermission
  | .cell => .ok .cell
  | .reservedIm => .ok .reservedIm
  | _ => .ok .disabled

def transition (permission : UPermission) (kind : AccessKind) (relation : NodeRelation) :
    Except Fault UPermission :=
  match relation, kind with
  | .localNode, .read => localRead permission
  | .localNode, .write => localWrite permission
  | .foreignNode, .read => foreignRead permission
  | .foreignNode, .write => foreignWrite permission

def initAccess : UPermission → Option AccessKind
  | .cell => none
  | _ => some .read

def preventsDeallocation (_ : UPermission) : Bool := false

end UPermission

namespace PPermission

def localRead : PPermission → Except Fault PPermission
  | .cell => .ok .cell
  | .reserved _ hadForeign => .ok (.reserved true hadForeign)
  | .unique => .ok .unique
  | .frozen _ => .ok (.frozen true)
  | .disabled => .error .protectedLocalReadDisabled

def localWrite : PPermission → Except Fault PPermission
  | .cell => .ok .cell
  | .unique => .ok .unique
  | .reserved _ false => .ok .unique
  | .reserved _ true => .error .protectedLocalWriteReservedAfterForeignRead
  | .frozen _ => .error .protectedLocalWriteFrozen
  | .disabled => .error .protectedLocalWriteDisabled

def foreignRead : PPermission → Except Fault PPermission
  | .cell => .ok .cell
  | .unique => .error .protectedForeignReadUnique
  | .reserved hadLocal _ => .ok (.reserved hadLocal true)
  | .frozen hadLocal => .ok (.frozen hadLocal)
  | .disabled => .ok .disabled

def foreignWrite : PPermission → Except Fault PPermission
  | .cell => .ok .cell
  | .frozen true => .error .protectedForeignWriteFrozenAfterLocalRead
  | .reserved true _ => .error .protectedForeignWriteReservedAfterLocalRead
  | .unique => .error .protectedForeignWriteUnique
  | .frozen false => .ok .disabled
  | .reserved false _ => .ok .disabled
  | .disabled => .ok .disabled

def transition (permission : PPermission) (kind : AccessKind) (relation : NodeRelation) :
    Except Fault PPermission :=
  match relation, kind with
  | .localNode, .read => localRead permission
  | .localNode, .write => localWrite permission
  | .foreignNode, .read => foreignRead permission
  | .foreignNode, .write => foreignWrite permission

def initAccess : PPermission → Option AccessKind
  | .cell => none
  | .unique => some .write
  | _ => some .read

def unprotect : PPermission → UPermission × Option AccessKind
  | .unique => (.unique, some .write)
  | .reserved hadLocal _ => (.reserved, if hadLocal then some .read else none)
  | .frozen hadLocal => (.frozen, if hadLocal then some .read else none)
  | .disabled => (.disabled, none)
  | .cell => (.cell, none)

def preventsDeallocation : PPermission → Bool
  | .unique => true
  | .reserved hadLocal _ | .frozen hadLocal => hadLocal
  | .disabled | .cell => false

end PPermission

inductive Permission where
  | unprot (permission : UPermission)
  | prot (permission : PPermission)
  deriving DecidableEq, Repr

def Permission.isProt : Permission → Bool
  | .unprot _ => false | .prot _ => true

def Permission.transition (permission : Permission) (kind : AccessKind) (relation : NodeRelation) :
    Except Fault Permission :=
  match permission with
  | .unprot permission =>
      match permission.transition kind relation with
      | .ok result => .ok (.unprot result)
      | .error fault => .error fault
  | .prot permission =>
      match permission.transition kind relation with
      | .ok result => .ok (.prot result)
      | .error fault => .error fault

def Permission.initAccess : Permission → Option AccessKind
  | .unprot permission => permission.initAccess
  | .prot permission => permission.initAccess

/-- none denotes unsupported structural input (unprotecting an Unprot value),
corresponding to the source's unreachable branch, not object-language UB. -/
def Permission.unprotect : Permission → Option (Permission × Option AccessKind)
  | .unprot _ => none
  | .prot permission =>
      let result := permission.unprotect
      some (.unprot result.1, result.2)

def Permission.preventsDeallocation : Permission → Bool
  | .unprot permission => permission.preventsDeallocation
  | .prot permission => permission.preventsDeallocation

/-- Exact per-byte kind matching. For lists this is universally quantified;
an empty list satisfies it under every protector flag. -/
def Permission.matchesProtector (permission : Permission) (protection : Protected) : Bool :=
  permission.isProt == protection.yes

theorem transition_preserves_kind {permission result : Permission}
    (kind : AccessKind) (relation : NodeRelation)
    (success : permission.transition kind relation = .ok result) :
    result.isProt = permission.isProt := by
  cases permission with
  | unprot permission =>
    cases selected : permission.transition kind relation with
    | error fault => simp [Permission.transition, selected] at success
    | ok nextPermission =>
      simp only [Permission.transition, selected] at success
      cases success
      rfl
  | prot permission =>
    cases selected : permission.transition kind relation with
    | error fault => simp [Permission.transition, selected] at success
    | ok nextPermission =>
      simp only [Permission.transition, selected] at success
      cases success
      rfl

theorem transition_preserves_matching {permission result : Permission}
    (kind : AccessKind) (relation : NodeRelation) (protection : Protected)
    (success : permission.transition kind relation = .ok result) :
    result.matchesProtector protection = permission.matchesProtector protection := by
  unfold Permission.matchesProtector
  rw [transition_preserves_kind kind relation success]

theorem unprotected_foreign_never_UB (permission : UPermission) (kind : AccessKind) :
    ∃ result, permission.transition kind .foreignNode = .ok result := by
  cases permission <;> cases kind <;> exact ⟨_, rfl⟩

theorem prevention_iff_protected_foreign_write_UB (permission : PPermission) :
    permission.preventsDeallocation = true ↔ ∃ fault, permission.foreignWrite = .error fault := by
  cases permission with
  | cell => simp [PPermission.preventsDeallocation, PPermission.foreignWrite]
  | reserved hadLocal hadForeign =>
    cases hadLocal <;> cases hadForeign <;> simp [PPermission.preventsDeallocation, PPermission.foreignWrite]
  | unique => simp [PPermission.preventsDeallocation, PPermission.foreignWrite]
  | frozen hadLocal =>
    cases hadLocal <;> simp [PPermission.preventsDeallocation, PPermission.foreignWrite]
  | disabled => simp [PPermission.preventsDeallocation, PPermission.foreignWrite]

theorem protected_history_updates (hadLocal hadForeign : Bool) :
    PPermission.localRead (.reserved hadLocal hadForeign) = .ok (.reserved true hadForeign) ∧
    PPermission.foreignRead (.reserved hadLocal hadForeign) = .ok (.reserved hadLocal true) := ⟨rfl, rfl⟩

theorem reservation_foreign_read_blocks_activation :
    PPermission.foreignRead (.reserved false false) = .ok (.reserved false true) ∧
    PPermission.localWrite (.reserved false true) = .error .protectedLocalWriteReservedAfterForeignRead :=
  ⟨rfl, rfl⟩

theorem unaccessed_protected_foreign_write (hadForeign : Bool) :
    PPermission.foreignWrite (.reserved false hadForeign) = .ok .disabled ∧
    PPermission.foreignWrite (.frozen false) = .ok .disabled := ⟨rfl, rfl⟩

theorem initial_and_end_accesses :
    Permission.initAccess (.prot .unique) = some .write ∧
    Permission.initAccess (.unprot .unique) = some .read ∧
    Permission.unprotect (.prot .unique) = some (.unprot .unique, some .write) ∧
    Permission.unprotect (.prot (.reserved true false)) = some (.unprot .reserved, some .read) ∧
    Permission.unprotect (.prot (.reserved false true)) = some (.unprot .reserved, none) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cell_has_no_initial_end_or_block :
    Permission.initAccess (.prot .cell) = none ∧
    Permission.initAccess (.unprot .cell) = none ∧
    Permission.unprotect (.prot .cell) = some (.unprot .cell, none) ∧
    Permission.preventsDeallocation (.prot .cell) = false := ⟨rfl, rfl, rfl, rfl⟩

theorem unprotect_unprotected_is_structurally_unsupported (permission : UPermission) :
    Permission.unprotect (.unprot permission) = none := rfl

theorem weak_and_strong_have_same_kind_test (permission : Permission) :
    permission.matchesProtector .weak = permission.matchesProtector .strong := rfl

theorem source_unique_write_diagnostic_typo :
    Fault.sourceMessage .protectedForeignWriteUnique = Fault.sourceMessage .protectedForeignReadUnique ∧
    Fault.protectedForeignWriteUnique ≠ Fault.protectedForeignReadUnique := ⟨rfl, by decide⟩

#print axioms transition_preserves_kind
#print axioms transition_preserves_matching
#print axioms unprotected_foreign_never_UB
#print axioms prevention_iff_protected_foreign_write_UB
#print axioms protected_history_updates
#print axioms reservation_foreign_read_blocks_activation
#print axioms unaccessed_protected_foreign_write
#print axioms initial_and_end_accesses
#print axioms cell_has_no_initial_end_or_block
#print axioms unprotect_unprotected_is_structurally_unsupported
#print axioms weak_and_strong_have_same_kind_test
#print axioms source_unique_write_diagnostic_typo

end AnnealResearch.TreePermissions
