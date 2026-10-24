import AnnealResearch.Execution

/-!
Minimum borrowing/frame interaction probe, transcribed independently from the
pinned MiniRust files `state_machine_unprotected.md` and the `unprotect` function
in `state_machine_protected.md`. That transcription is an additional audited
assumption. This is a selected source-table probe, not Rust authority or a full
Tree Borrows graph, protector algorithm, or Iris integration.

An access updates every tag at its selected (allocation, byte offset). Distinct
tag names do not imply spatial separation. The frame theorem below separates
whole bytes; same-byte preservation requires a stable foreign permission.
-/

namespace AnnealResearch.BorrowFrame

open Execution

inductive Permission where
  | Cell | Reserved | ReservedIm | Unique | Frozen | Disabled
  deriving DecidableEq

inductive AccessKind where
  | read | write
  deriving DecidableEq

inductive NodeRelation where
  | local | foreign
  deriving DecidableEq

/-- Exactly the three error cases in the selected unprotected table. -/
inductive UB where
  | localReadDisabled | localWriteFrozen | localWriteDisabled
  deriving DecidableEq

def localRead : Permission → Except UB Permission
  | .Disabled => .error .localReadDisabled
  | p => .ok p

def localWrite : Permission → Except UB Permission
  | .Frozen => .error .localWriteFrozen
  | .Disabled => .error .localWriteDisabled
  | .Cell => .ok .Cell
  | _ => .ok .Unique

def foreignRead : Permission → Permission
  | .Unique => .Frozen
  | p => p

def foreignWrite : Permission → Permission
  | .Cell => .Cell
  | .ReservedIm => .ReservedIm
  | _ => .Disabled

def localTransition (kind : AccessKind) : Permission → Except UB Permission :=
  match kind with
  | .read => localRead
  | .write => localWrite

def foreignTransition (kind : AccessKind) : Permission → Permission :=
  match kind with
  | .read => foreignRead
  | .write => foreignWrite

def transition (relation : NodeRelation) (kind : AccessKind)
    (p : Permission) : Except UB Permission :=
  match relation with
  | .local => localTransition kind p
  | .foreign => .ok (foreignTransition kind p)

structure Byte where
  alloc : Nat
  offset : Nat
  deriving DecidableEq

abbrev Tag := Nat
abbrev Store := Byte → Tag → Permission

structure Access where
  byte : Byte
  tag : Tag
  kind : AccessKind

/-- The successful local permission is supplied after checking the table. All
other tags at the same byte receive the foreign transition. -/
def update (store : Store) (a : Access) (localAfter : Permission) : Store :=
  fun byte tag =>
    if byte = a.byte then
      if tag = a.tag then localAfter
      else foreignTransition a.kind (store byte tag)
    else store byte tag

def perform (store : Store) (a : Access) : Except UB Store :=
  match localTransition a.kind (store a.byte a.tag) with
  | .error reason => .error reason
  | .ok localAfter => .ok (update store a localAfter)

def AgreesOn (footprint : Byte → Prop) (before after : Store) : Prop :=
  ∀ byte, footprint byte → ∀ tag, before byte tag = after byte tag

/-- The allocation and byte offset both participate in this disjointness. -/
theorem update_spatial_frame {footprint : Byte → Prop} {store : Store}
    {a : Access} {p : Permission} (disjoint : ¬ footprint a.byte) :
    AgreesOn footprint store (update store a p) := by
  intro byte member tag
  have different : byte ≠ a.byte := by
    intro same
    exact disjoint (same ▸ member)
  simp [update, different]

theorem perform_spatial_frame {footprint : Byte → Prop} {store after : Store}
    {a : Access} (disjoint : ¬ footprint a.byte)
    (success : perform store a = .ok after) : AgreesOn footprint store after := by
  cases checked : localTransition a.kind (store a.byte a.tag) with
  | error reason => simp [perform, checked] at success
  | ok p =>
    have result : update store a p = after := by
      simpa [perform, checked] using success
    rw [← result]
    exact update_spatial_frame disjoint

abbrev Assertion := Store → Prop

def Supported (footprint : Byte → Prop) (assertion : Assertion) : Prop :=
  ∀ before after, AgreesOn footprint before after → assertion before → assertion after

def Triple (a : Access) (pre post : Assertion) : Prop :=
  ∀ store, pre store → ∃ after, perform store a = .ok after ∧ post after

theorem local_permission_triple (a : Access) (before after : Permission)
    (allowed : localTransition a.kind before = .ok after) :
    Triple a (fun store => store a.byte a.tag = before)
      (fun store => store a.byte a.tag = after) := by
  intro store owns
  refine ⟨update store a after, ?_, ?_⟩
  · simp [perform, owns, allowed]
  · simp [update]

theorem frame_triple {a : Access} {pre post frame : Assertion}
    {footprint : Byte → Prop} (triple : Triple a pre post)
    (supported : Supported footprint frame) (disjoint : ¬ footprint a.byte) :
    Triple a (fun store => pre store ∧ frame store)
      (fun store => post store ∧ frame store) := by
  intro store assumptions
  obtain ⟨after, success, postcondition⟩ := triple store assumptions.1
  exact ⟨after, success, postcondition,
    supported store after (perform_spatial_frame disjoint success) assumptions.2⟩

def ForeignStable (kind : AccessKind) (p : Permission) : Prop :=
  foreignTransition kind p = p

theorem same_byte_frame_of_stability {store : Store} {a : Access}
    {localAfter : Permission} {other : Tag} (different : other ≠ a.tag)
    (stable : ForeignStable a.kind (store a.byte other)) :
    update store a localAfter a.byte other = store a.byte other := by
  simpa [update, different, ForeignStable] using stable

theorem Cell_stable (kind : AccessKind) : ForeignStable kind .Cell := by
  cases kind <;> rfl

theorem Reserved_stable_under_read : ForeignStable .read .Reserved := rfl

-- These are actual transitions with explicit UB successors. No permission
-- checks are used to remove illegal operations from the execution subject.
inductive Config where
  | live (store : Store)
  | ub (reason : UB)

inductive Step (a : Access) : Config → Config → Prop where
  | success {store : Store} {p : Permission} :
      localTransition a.kind (store a.byte a.tag) = .ok p →
      Step a (.live store) (.live (update store a p))
  | failure {store : Store} {reason : UB} :
      localTransition a.kind (store a.byte a.tag) = .error reason →
      Step a (.live store) (.ub reason)

def Bad : Config → Prop
  | .live _ => False
  | .ub _ => True

theorem local_read_safe {p : Permission} (readable : p ≠ .Disabled) :
    localTransition .read p = .ok p := by
  cases p <;> simp_all [localTransition, localRead]

/-- Repeated reads are safe from an initial readable local permission. This
invariant handles every actual transition, including the potential UB case. -/
theorem read_forever_noUB (store : Store) (byte : Byte) (tag : Tag)
    (readable : store byte tag ≠ .Disabled) :
    NoUB (Step ⟨byte, tag, .read⟩) Bad (.live store) := by
  let invariant : Config → Prop
    | .live current => current byte tag ≠ .Disabled
    | .ub _ => False
  apply invariant_noUB (Invariant := invariant) readable
  · intro before after preserved edge
    cases edge with
    | @success current p checked =>
      change current byte tag ≠ .Disabled at preserved
      have accepted := local_read_safe preserved
      have same : p = current byte tag := Except.ok.inj (checked.symm.trans accepted)
      change update current ⟨byte, tag, .read⟩ p byte tag ≠ .Disabled
      simpa [update, same] using preserved
    | @failure current reason checked =>
      change current byte tag ≠ .Disabled at preserved
      have accepted := local_read_safe preserved
      have impossible := checked.symm.trans accepted
      cases impossible
  · intro state safe
    cases state with
    | live current => exact False.elim
    | ub reason => exact False.elim safe

/-- Adding arbitrary resources at disjoint bytes preserves the initial local
permission needed for the read invariant; each subsequent access also frames
those bytes by `update_spatial_frame`. -/
theorem read_forever_with_frame (store framed : Store) (byte : Byte) (tag : Tag)
    (sameOwn : framed byte tag = store byte tag)
    (readable : store byte tag ≠ .Disabled) :
    NoUB (Step ⟨byte, tag, .read⟩) Bad (.live framed) := by
  apply read_forever_noUB
  simpa [sameOwn] using readable

namespace TagCounterexample

def byte : Byte := ⟨0, 0⟩
def store (_ : Byte) (tag : Tag) : Permission := if tag = 0 then .Cell else .Unique
def readAccess : Access := ⟨byte, 0, .read⟩
def afterRead : Store := update store readAccess .Cell
def laterWrite : Access := ⟨byte, 1, .write⟩

theorem disjoint_tags_do_not_frame :
    readAccess.tag ≠ laterWrite.tag ∧
    perform store readAccess = .ok afterRead ∧
    store byte laterWrite.tag = .Unique ∧
    afterRead byte laterWrite.tag = .Frozen ∧
    perform afterRead laterWrite = .error .localWriteFrozen := by
  exact ⟨by decide, rfl, rfl, rfl, rfl⟩

theorem later_local_write_has_UB :
    Step laterWrite (.live afterRead) (.ub .localWriteFrozen) := by
  exact Step.failure rfl

end TagCounterexample

-- Only the protected-to-unprotected table is modeled here. In particular,
-- ending a protector may emit an access that must still be processed.
inductive ProtectedPermission where
  | Cell
  | Reserved (hadLocalRead hadForeignRead : Bool)
  | Unique
  | Frozen (hadLocalRead : Bool)
  | Disabled

def unprotect : ProtectedPermission → Permission × Option AccessKind
  | .Unique => (.Unique, some .write)
  | .Reserved true _ => (.Reserved, some .read)
  | .Reserved false _ => (.Reserved, none)
  | .Frozen true => (.Frozen, some .read)
  | .Frozen false => (.Frozen, none)
  | .Disabled => (.Disabled, none)
  | .Cell => (.Cell, none)

theorem protector_end_unique_implicit_write :
    unprotect .Unique = (.Unique, some .write) := rfl

theorem protector_end_frozen_read_implicit_read :
    unprotect (.Frozen true) = (.Frozen, some .read) := rfl

theorem protector_end_is_not_pure_erase : (unprotect .Unique).2 ≠ none := by
  intro impossible
  cases impossible

#print axioms perform_spatial_frame
#print axioms local_permission_triple
#print axioms frame_triple
#print axioms same_byte_frame_of_stability
#print axioms read_forever_noUB
#print axioms read_forever_with_frame
#print axioms TagCounterexample.disjoint_tags_do_not_frame
#print axioms TagCounterexample.later_local_write_has_UB
#print axioms protector_end_is_not_pure_erase

end AnnealResearch.BorrowFrame
