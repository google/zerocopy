import ToyPin.Core

/-!
# Structural pinning of the fields of a struct

A `Decl` describes one struct type `S` together with its author's choices:

* the field types (`fieldUnpin`: does field `i`'s type implement `Unpin`?);
* whether `S` implements `Unpin` (`unpin`, however obtained: auto trait, derive, or manual);
* the safe operations `S` offers on `Pin<&mut S>` (`api`): structural projection
  `Pin<&mut S> → Pin<&mut F_i>`, non-structural projection `Pin<&mut S> → &mut F_i`, a
  move-out (`Option::take`-like) `Pin<&mut S> → F_i`, and an in-place overwrite that does not
  drop the old value;
* what the destructor of `S` does with its `&mut self` argument (`dtor`): move out of a field
  (and drop the moved value), or overwrite a field without dropping its value;
* whether `S` is `#[repr(packed)]`: the drop glue then moves every field to a fresh
  (aligned) temporary and drops it there.

A program is a list of `Op`s (safe-code operations). `SafeOp` says when safe code may
perform an operation in a given state; `expand` gives its primitive actions.
-/

namespace Toy.Pin

/-- Operations `S` offers on `Pin<&mut S>`. In `SafeOp`, `take` and `overwrite` are callable
whether or not the object is pinned (an over-approximation: it only adds safe programs). -/
inductive ApiOp where
  /-- Structural projection `Pin<&mut S> → Pin<&mut F_i>`. -/
  | projPin (i : Nat)
  /-- Non-structural projection `Pin<&mut S> → &mut F_i`. -/
  | projMut (i : Nat)
  /-- A move-out `Pin<&mut S> → F_i` that leaves the field empty (e.g. `Option::take`). -/
  | take (i : Nat)
  /-- `Pin<&mut S> → ()` writing a fresh value into field `i` without dropping the old one. -/
  | overwrite (i : Nat)
  deriving DecidableEq, Repr

/-- What the destructor of `S` does through its `&mut self` argument. -/
inductive DtorOp where
  /-- Move the value out of field `i` (e.g. `mem::replace`), then drop the moved value. -/
  | moveOut (i : Nat)
  /-- Write a fresh value into field `i` without dropping the old one (e.g. `ptr::write`). -/
  | overwrite (i : Nat)
  deriving DecidableEq, Repr

/-- A struct type `S` and its author's pinning-related choices. -/
structure Decl where
  /-- One entry per field: does the field's type implement `Unpin`? -/
  fieldUnpin : List Bool
  /-- Does `S` implement `Unpin`? -/
  unpin : Bool
  /-- Safe operations offered on `Pin<&mut S>`. -/
  api : List ApiOp
  /-- Actions of the destructor of `S`, in order. -/
  dtor : List DtorOp
  /-- Is `S` `#[repr(packed)]`? -/
  packed : Bool
  deriving DecidableEq, Repr

namespace Decl

/-- Number of fields. -/
def nfields (d : Decl) : Nat := d.fieldUnpin.length

/-- `Unpin` flag of field `i`'s type; indices that are not fields count as `Unpin`. -/
def fieldTy (d : Decl) (i : Nat) : Bool := (d.fieldUnpin[i]?).getD true

/-- Field `i` is **structurally pinned** (a structural projection is offered) and its type is
**not `Unpin`**. Only such fields carry pinning obligations. -/
def PinnedNonUnpinField (d : Decl) (i : Nat) : Prop :=
  ApiOp.projPin i ∈ d.api ∧ d.fieldTy i = false

instance (d : Decl) (i : Nat) : Decidable (d.PinnedNonUnpinField i) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem fieldTy_eq_true_of_le {d : Decl} {i : Nat} (h : d.nfields ≤ i) : d.fieldTy i = true := by
  unfold fieldTy
  rw [List.getElem?_eq_none (by unfold nfields at h; omega)]
  rfl

theorem lt_of_pinnedNonUnpinField {d : Decl} {i : Nat} (h : d.PinnedNonUnpinField i) :
    i < d.nfields := by
  apply Nat.lt_of_not_le
  intro hle
  have := fieldTy_eq_true_of_le hle
  rw [h.2] at this
  cases this

/-- Bounded form of quantification over pinned non-`Unpin` fields (for decidability). -/
theorem forall_pnu_iff (d : Decl) (Q : Nat → Prop) :
    (∀ i, d.PinnedNonUnpinField i → Q i) ↔ (∀ i < d.nfields, d.PinnedNonUnpinField i → Q i) :=
  ⟨fun h i _ => h i, fun h i hi => h i (lt_of_pinnedNonUnpinField hi) hi⟩

end Decl

/-! ## The soundness conditions for structural pinning -/

/-- **(a) `Unpin` only if the pinned fields are `Unpin`.** If `S : Unpin`, every
structurally pinned field's type is `Unpin`. -/
def UnpinOnlyIfPinnedFieldsUnpin (d : Decl) : Prop :=
  d.unpin = true → ∀ i, ApiOp.projPin i ∈ d.api → d.fieldTy i = true

/-- **(b) Pinned destruction.** The destructor does not move out of a structurally pinned
non-`Unpin` field. -/
def DtorNoMoveOutOfPinned (d : Decl) : Prop :=
  ∀ i, d.PinnedNonUnpinField i → DtorOp.moveOut i ∉ d.dtor

/-- **(c) Drop guarantee for pinned fields.** Neither the API nor the destructor overwrites
a structurally pinned non-`Unpin` field without dropping its value. -/
def DropGuaranteeForPinned (d : Decl) : Prop :=
  ∀ i, d.PinnedNonUnpinField i → ApiOp.overwrite i ∉ d.api ∧ DtorOp.overwrite i ∉ d.dtor

/-- **(d) No move-out API for pinned fields.** No offered `Pin<&mut S> → F_i` move-out
(e.g. `Option::take`) for a structurally pinned non-`Unpin` field. -/
def NoPinnedTake (d : Decl) : Prop :=
  ∀ i, d.PinnedNonUnpinField i → ApiOp.take i ∉ d.api

/-- **(e) Not packed.** If `S` is `#[repr(packed)]` it has no structurally pinned
non-`Unpin` field. -/
def NotPackedIfPinned (d : Decl) : Prop :=
  d.packed = true → ∀ i, ¬ d.PinnedNonUnpinField i

/-- **(f) Consistent projection.** A structurally pinned non-`Unpin` field is not also
offered through a non-structural projection `Pin<&mut S> → &mut F_i`. -/
def ProjectionConsistent (d : Decl) : Prop :=
  ∀ i, d.PinnedNonUnpinField i → ApiOp.projMut i ∉ d.api

theorem unpinOnlyIf_iff (d : Decl) : UnpinOnlyIfPinnedFieldsUnpin d ↔
    (d.unpin = true → ∀ i < d.nfields, ApiOp.projPin i ∈ d.api → d.fieldTy i = true) :=
  ⟨fun h hu i _ => h hu i, fun h hu i hi => by
    by_cases hlt : i < d.nfields
    · exact h hu i hlt hi
    · exact Decl.fieldTy_eq_true_of_le (by omega)⟩

instance (d : Decl) : Decidable (UnpinOnlyIfPinnedFieldsUnpin d) :=
  decidable_of_iff _ (unpinOnlyIf_iff d).symm
instance (d : Decl) : Decidable (DtorNoMoveOutOfPinned d) :=
  decidable_of_iff _ (Decl.forall_pnu_iff d _).symm
instance (d : Decl) : Decidable (DropGuaranteeForPinned d) :=
  decidable_of_iff _ (Decl.forall_pnu_iff d _).symm
instance (d : Decl) : Decidable (NoPinnedTake d) :=
  decidable_of_iff _ (Decl.forall_pnu_iff d _).symm
instance (d : Decl) : Decidable (ProjectionConsistent d) :=
  decidable_of_iff _ (Decl.forall_pnu_iff d _).symm
instance (d : Decl) : Decidable (NotPackedIfPinned d) :=
  decidable_of_iff (d.packed = true → ∀ i < d.nfields, ¬ d.PinnedNonUnpinField i)
    ⟨fun h hp i hi => h hp i (Decl.lt_of_pinnedNonUnpinField hi) hi, fun h hp i _ => h hp i⟩

/-! ## Safe-code operations -/

/-- Operations of a program over objects of type `S` (addresses are heap indices). -/
inductive Op where
  /-- `S::new()`: allocate an object whose every field holds a fresh value. -/
  | new
  /-- Pin the owned object at `b` (`Box::pin`, `pin!`). -/
  | pin (b : Nat)
  /-- Call the structural projection of field `i` on `Pin<&mut S>`. -/
  | projPin (b i : Nat)
  /-- `F::init(self: Pin<&mut F>)`: the value at `l` stores its own address. -/
  | initSelf (l : Loc)
  /-- `F::link(self: Pin<&mut F>)`: the value at `l` links itself into the external list. -/
  | link (l : Loc)
  /-- `drop(mem::replace(&mut s.f_i, F_i::new()))` through some `&mut F_i`. -/
  | replaceField (b i : Nat)
  /-- `mem::swap(&mut s.f_i, &mut t.f_i)` for two distinct objects `s` at `b`, `t` at `c`. -/
  | swapField (b c i : Nat)
  /-- `s.f_i = F_i::new()` (drops the old value in place, then writes). -/
  | assignField (b i : Nat)
  /-- `let old = mem::replace(&mut *s, S::new())` through some `&mut S`; `old` is kept, as a
  live unpinned object, at the next free address. -/
  | replaceStruct (b : Nat)
  /-- `drop(s.as_mut().take_i())` using `S`'s own move-out operation. -/
  | take (b i : Nat)
  /-- `s.as_mut().overwrite_i()` using `S`'s own overwrite-without-drop operation. -/
  | overwrite (b i : Nat)
  /-- Drop the owner of the object at `b`. -/
  | drop (b : Nat)
  /-- Leak the object at `b`. Afterwards `SafeOp` forbids `drop b` and `forget b`; other
  operations on `b` stay available (references obtained earlier survive, as with
  `Box::leak`). A value-consuming `mem::forget` of the only owner corresponds to
  continuations that never mention `b` (see `unmentioned_object_unchanged`). -/
  | forget (b : Nat)
  deriving DecidableEq, Repr

/-- Safe code can obtain a `&mut F_i` to field `i` of the object at `b`: the object is
unpinned (the owner borrows it), or `S : Unpin` (`Pin::get_mut`), or `S` offers a
non-structural projection of field `i`, or field `i` was structurally projected and its type
is `Unpin` (`Pin::get_mut` on `Pin<&mut F_i>`). -/
def MutFieldAvail (d : Decl) (st : State) (b i : Nat) : Prop :=
  st.isLive b = true ∧
    (st.isPinned b = false ∨ d.unpin = true ∨ ApiOp.projMut i ∈ d.api ∨
      (st.isPinnedLoc (b, i) = true ∧ d.fieldTy i = true))

/-- Safe code can obtain a `&mut S` to the object at `b`: it is unpinned, or `S : Unpin`. -/
def MutStructAvail (d : Decl) (st : State) (b : Nat) : Prop :=
  st.isLive b = true ∧ (st.isPinned b = false ∨ d.unpin = true)

/-- When safe code may perform an operation. -/
def SafeOp (d : Decl) (st : State) : Op → Prop
  | .new => True
  | .pin b => st.isLive b = true ∧ st.isPinned b = false
  | .projPin b i => st.isLive b = true ∧ st.isPinned b = true ∧ ApiOp.projPin i ∈ d.api
  | .initSelf l => st.isLive l.1 = true ∧ st.isPinnedLoc l = true
  | .link l => st.isLive l.1 = true ∧ st.isPinnedLoc l = true
  | .replaceField b i => MutFieldAvail d st b i
  | .swapField b c i => b ≠ c ∧ MutFieldAvail d st b i ∧ MutFieldAvail d st c i
  | .assignField b i => MutFieldAvail d st b i
  | .replaceStruct b => MutStructAvail d st b
  | .take b i => st.isLive b = true ∧ ApiOp.take i ∈ d.api
  | .overwrite b i => st.isLive b = true ∧ ApiOp.overwrite i ∈ d.api
  | .drop b => st.isLive b = true ∧ st.isLeaked b = false
  | .forget b => st.isLive b = true ∧ st.isLeaked b = false

instance (d : Decl) (st : State) (b i : Nat) : Decidable (MutFieldAvail d st b i) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (d : Decl) (st : State) (b : Nat) : Decidable (MutStructAvail d st b) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (d : Decl) (st : State) (op : Op) : Decidable (SafeOp d st op) := by
  cases op <;> unfold SafeOp <;> infer_instance

/-- Move the value of `l` into a fresh temporary and drop it there. -/
def moveDrop (l : Loc) : List Act := [.moveOut l, .dropTemp l.2, .freeTemp]

/-- Primitive actions of one destructor action on the object at `b`. -/
def dtorActs (d : Decl) (b : Nat) : DtorOp → List Act
  | .moveOut i => moveDrop (b, i)
  | .overwrite i => [.write (b, i) (d.fieldTy i)]

/-- Drop glue for field `i` of the object at `b`: in place, or (packed) via an aligned
temporary. -/
def glueActs (d : Decl) (b i : Nat) : List Act :=
  if d.packed then moveDrop (b, i) else [.dropLeaf (b, i)]

/-- Dropping the object at `b`: the destructor of `S`, then the drop glue of every field,
then deallocation. -/
def dropActs (d : Decl) (b : Nat) : List Act :=
  d.dtor.flatMap (dtorActs d b) ++ (List.range d.nfields).flatMap (glueActs d b) ++
    [.dealloc b]

/-- Primitive actions of an operation. -/
def expand (d : Decl) : Op → List Act
  | .new => [.alloc (d.fieldUnpin.map some)]
  | .pin b => [.pinObj b]
  | .projPin b i => [.pinField (b, i)]
  | .initSelf l => [.setSelf l]
  | .link l => [.register l]
  | .replaceField b i => moveDrop (b, i) ++ [.write (b, i) (d.fieldTy i)]
  | .swapField b c i => [.swap (b, i) (c, i)]
  | .assignField b i => [.dropLeaf (b, i), .write (b, i) (d.fieldTy i)]
  | .replaceStruct b =>
    .moveObj b :: (List.range d.nfields).map fun i => .write (b, i) (d.fieldTy i)
  | .take b i => moveDrop (b, i)
  | .overwrite b i => [.write (b, i) (d.fieldTy i)]
  | .drop b => dropActs d b
  | .forget b => [.forget b]

/-- Primitive actions of a program. -/
def compile (d : Decl) (prog : List Op) : List Act := prog.flatMap (expand d)

/-- Every operation of the program is permitted to safe code in the state where it runs. -/
def SafeProgram (d : Decl) : State → List Op → Prop
  | _, [] => True
  | st, op :: ops => SafeOp d st op ∧ SafeProgram d (runActs st (expand d op)) ops

instance decSafeProgram (d : Decl) : ∀ st prog, Decidable (SafeProgram d st prog)
  | _, [] => isTrue trivial
  | st, op :: ops =>
    have := decSafeProgram d (runActs st (expand d op)) ops
    inferInstanceAs (Decidable (SafeOp d st op ∧ _))

/-- Every program accepted by `SafeProgram d` from `State.init` keeps both
address-sensitive invariants in every state visited by its compilation `compile d prog`. -/
def SafeProgramsKeepAddrInv (d : Decl) : Prop :=
  ∀ prog, SafeProgram d State.init prog → ∀ s ∈ states State.init (compile d prog), AddrInv s

end Toy.Pin
