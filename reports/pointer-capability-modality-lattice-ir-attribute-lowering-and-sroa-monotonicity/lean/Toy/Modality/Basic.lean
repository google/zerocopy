/-
Toy.Modality.Basic
==================

Core vocabulary of the toy model: pointee shapes, capability atoms,
modalities (sets of atoms), one-call traces, and the trace semantics `den` of
a modality.  Everything here is a definition or a small fully proved helper
lemma; the results of the package live in the other modules.

What the model is meant to capture: a Rust-like compiler that passes a pointer
argument to a function makes promises about the pointee *for the duration of
the call* (live at entry, live for the whole call, not written, not accessed
through unrelated pointers, accessed through the argument only inside the
pointee bytes) and about the pointer value (aligned, non-null).  A modality is
the set of such promises attached to one pointer.  `den s m` imposes exactly
the promises in `m` and nothing else; in particular `den s Mod.bot` is every
trace.
-/

namespace Toy.Modality

/-! ## Shapes -/

/-- Layout of a pointee: `size` bytes and alignment `2 ^ alignLog`.  The size is
positive by construction (`size_pos`): zero-sized pointees are outside the model.
The alignment is a power of two, hence never `0`. -/
structure Shape where
  size : Nat
  alignLog : Nat
  size_pos : 0 < size

/-- The alignment in bytes, `2 ^ alignLog` (always at least `1`). -/
def Shape.align (s : Shape) : Nat := 2 ^ s.alignLog

theorem Shape.align_pos (s : Shape) : 0 < s.align := Nat.two_pow_pos _

/-! ## Capability atoms and modalities -/

/-- Capability atoms: the individual promises a pointer argument can carry.
* `aligned`: the address is a multiple of the pointee alignment;
* `nonnull`: the address is not `0`;
* `derefEntry`: the pointee bytes are inside a live allocation at call entry;
* `derefWhole`: as `derefEntry`, and no allocation containing the address is
  freed during the call (live for the whole call);
* `frozen`: no write to the pointee bytes happens during the call;
* `unique`: no access to the pointee bytes happens during the call through a
  pointer not derived from this one;
* `bounded`: every access during the call through a pointer derived from this
  one stays inside the pointee bytes (bounded provenance). -/
inductive Atom
  | aligned
  | nonnull
  | derefEntry
  | derefWhole
  | frozen
  | unique
  | bounded
  deriving DecidableEq, Repr

/-- A modality: a set of atoms, represented by one membership bit per atom.
More atoms means a stronger promise.  The implication-closed modalities
(`Closed`) are the intended lattice elements; operations are defined on all
`2 ^ 7` sets. -/
structure Mod where
  aligned : Bool
  nonnull : Bool
  derefEntry : Bool
  derefWhole : Bool
  frozen : Bool
  unique : Bool
  bounded : Bool
  deriving DecidableEq, Repr

/-- Membership of an atom in a modality. -/
def Mod.has (m : Mod) : Atom → Bool
  | .aligned => m.aligned
  | .nonnull => m.nonnull
  | .derefEntry => m.derefEntry
  | .derefWhole => m.derefWhole
  | .frozen => m.frozen
  | .unique => m.unique
  | .bounded => m.bounded

/-- Inclusion of modalities: every atom of `m₁` is an atom of `m₂`
(`m₂` promises at least as much as `m₁`). -/
instance : LE Mod := ⟨fun m₁ m₂ => ∀ a, m₁.has a = true → m₂.has a = true⟩

theorem Mod.le_def (m₁ m₂ : Mod) : m₁ ≤ m₂ ↔ ∀ a, m₁.has a = true → m₂.has a = true :=
  Iff.rfl

/-- A universally quantified statement over the seven atoms is the conjunction
of its seven instances. -/
theorem Atom.forall_iff (P : Atom → Prop) :
    (∀ a, P a) ↔ P .aligned ∧ P .nonnull ∧ P .derefEntry ∧ P .derefWhole ∧ P .frozen ∧
      P .unique ∧ P .bounded := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _, h _, h _, h _⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩ a
    cases a
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7

instance (m₁ m₂ : Mod) : Decidable (m₁ ≤ m₂) :=
  decidable_of_iff _ (Atom.forall_iff (fun a => m₁.has a = true → m₂.has a = true)).symm

/-- Meet: atom-wise conjunction (intersection of atom sets). -/
def Mod.inf (m₁ m₂ : Mod) : Mod :=
  ⟨m₁.aligned && m₂.aligned, m₁.nonnull && m₂.nonnull, m₁.derefEntry && m₂.derefEntry,
   m₁.derefWhole && m₂.derefWhole, m₁.frozen && m₂.frozen, m₁.unique && m₂.unique,
   m₁.bounded && m₂.bounded⟩

/-- Join: atom-wise disjunction (union of atom sets). -/
def Mod.sup (m₁ m₂ : Mod) : Mod :=
  ⟨m₁.aligned || m₂.aligned, m₁.nonnull || m₂.nonnull, m₁.derefEntry || m₂.derefEntry,
   m₁.derefWhole || m₂.derefWhole, m₁.frozen || m₂.frozen, m₁.unique || m₂.unique,
   m₁.bounded || m₂.bounded⟩

/-- The empty modality: no promise (`den s Mod.bot` holds on every trace,
`den_bot`). -/
def Mod.bot : Mod := ⟨false, false, false, false, false, false, false⟩

/-- The full modality (every promise). -/
def Mod.top : Mod := ⟨true, true, true, true, true, true, true⟩

@[simp] theorem Mod.has_inf (m₁ m₂ : Mod) (a : Atom) :
    (m₁.inf m₂).has a = (m₁.has a && m₂.has a) := by cases a <;> rfl

@[simp] theorem Mod.has_sup (m₁ m₂ : Mod) (a : Atom) :
    (m₁.sup m₂).has a = (m₁.has a || m₂.has a) := by cases a <;> rfl

@[simp] theorem Mod.has_bot (a : Atom) : Mod.bot.has a = false := by cases a <;> rfl

@[simp] theorem Mod.has_top (a : Atom) : Mod.top.has a = true := by cases a <;> rfl

theorem Mod.ext_has {m₁ m₂ : Mod} (h : ∀ a, m₁.has a = m₂.has a) : m₁ = m₂ := by
  cases m₁; cases m₂
  have h1 := h .aligned; have h2 := h .nonnull; have h3 := h .derefEntry
  have h4 := h .derefWhole; have h5 := h .frozen; have h6 := h .unique
  have h7 := h .bounded
  simp only [Mod.has] at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7; rfl

/-! ## One-call traces -/

/-- Pointer provenance of an access: derived from the argument (`arg`) or not
(`other`). -/
inductive Tag
  | arg
  | other
  deriving DecidableEq, Repr

/-- Events of a call: reads and writes of one byte address, and frees of an
allocation (by id), each tagged with the provenance of the pointer used. -/
inductive Event
  | read (tg : Tag) (loc : Nat)
  | write (tg : Tag) (loc : Nat)
  | free (tg : Tag) (id : Nat)
  deriving DecidableEq, Repr

/-- An allocation: identifier, base address, and length in bytes. -/
structure Alloc where
  id : Nat
  base : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- A toy trace of one call for one pointer: the pointer's address `addr`, the
allocations live at call entry, the events during the call, and the events
after the call returns (read only by the return-position meaning of
`noalias`).  Events are an unordered record (a list read as a set).
Allocations created during the call are not represented. -/
structure Trace where
  addr : Nat
  live : List Alloc
  during : List Event
  after : List Event
  deriving Repr

/-- Address `x` is inside allocation `al`.  Address `0` is never inside an
allocation: an allocation with base `0` contains nothing. -/
def Alloc.contains (al : Alloc) (x : Nat) : Prop :=
  0 < al.base ∧ al.base ≤ x ∧ x < al.base + al.len

/-- The `n` bytes starting at `a` are inside allocation `al` (and `al` has a
positive base). -/
def Alloc.covers (al : Alloc) (a n : Nat) : Prop :=
  0 < al.base ∧ al.base ≤ a ∧ a + n ≤ al.base + al.len

/-- Address `x` is one of the pointee bytes `a, …, a + size - 1`. -/
def InRange (s : Shape) (a x : Nat) : Prop := a ≤ x ∧ x < a + s.size

/-- Address `x` is read or written in `es` through a pointer with tag `tg`. -/
def AccessedBy (es : List Event) (tg : Tag) (x : Nat) : Prop :=
  Event.read tg x ∈ es ∨ Event.write tg x ∈ es

/-- Address `x` is written in `es` (through any pointer). -/
def Written (es : List Event) (x : Nat) : Prop := ∃ tg, Event.write tg x ∈ es

/-- Bounded provenance (the meaning of the atom `bounded`): every address
read or written during the call through a pointer derived from the argument is
one of the pointee bytes. -/
def ArgInRange (s : Shape) (t : Trace) : Prop :=
  ∀ x, AccessedBy t.during .arg x → InRange s t.addr x

/-- The pointee bytes are inside one allocation live at call entry. -/
def Dereferenceable (s : Shape) (t : Trace) : Prop :=
  ∃ al ∈ t.live, al.covers t.addr s.size

/-- No allocation containing the address is freed during the call, through
any pointer. -/
def NotFreedDuring (t : Trace) : Prop :=
  ∀ al ∈ t.live, al.contains t.addr → ∀ tg, Event.free tg al.id ∉ t.during

/-- Trace meaning of each atom, for a pointee of shape `s`. -/
def atomSat (s : Shape) : Atom → Trace → Prop
  | .aligned, t => t.addr % s.align = 0
  | .nonnull, t => t.addr ≠ 0
  | .derefEntry, t => Dereferenceable s t
  | .derefWhole, t => Dereferenceable s t ∧ NotFreedDuring t
  | .frozen, t => ∀ x, InRange s t.addr x → ¬ Written t.during x
  | .unique, t => ∀ x, InRange s t.addr x → ¬ AccessedBy t.during .other x
  | .bounded, t => ArgInRange s t

/-- `⟦m⟧`: the traces that satisfy every atom of `m` (and no further
condition). -/
def den (s : Shape) (m : Mod) (t : Trace) : Prop :=
  ∀ a, m.has a = true → atomSat s a t

/-! ## Implication closure -/

/-- Implication closure for shape `s`: `derefWhole ⇒ derefEntry ⇒ nonnull`
(address `0` is never inside an allocation), and `aligned` holds outright when
the alignment is `1` (`alignLog = 0`).  `frozen`, `unique` and `bounded` are
unchanged. -/
def cl (s : Shape) (m : Mod) : Mod :=
  { m with
    aligned := m.aligned || s.alignLog == 0
    nonnull := m.nonnull || m.derefEntry || m.derefWhole
    derefEntry := m.derefEntry || m.derefWhole }

/-- `m` is implication-closed for shape `s`. -/
def Closed (s : Shape) (m : Mod) : Prop := cl s m = m

instance (s : Shape) (m : Mod) : Decidable (Closed s m) :=
  inferInstanceAs (Decidable (cl s m = m))

/-! ## Helper lemmas -/

theorem den_iff (s : Shape) (m : Mod) (t : Trace) :
    den s m t ↔
      (m.aligned = true → atomSat s .aligned t) ∧
      (m.nonnull = true → atomSat s .nonnull t) ∧
      (m.derefEntry = true → atomSat s .derefEntry t) ∧
      (m.derefWhole = true → atomSat s .derefWhole t) ∧
      (m.frozen = true → atomSat s .frozen t) ∧
      (m.unique = true → atomSat s .unique t) ∧
      (m.bounded = true → atomSat s .bounded t) := by
  constructor
  · intro h
    exact ⟨h .aligned, h .nonnull, h .derefEntry, h .derefWhole, h .frozen, h .unique,
      h .bounded⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩ a
    cases a
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7

/-- `⟦Mod.bot⟧` is every trace. -/
theorem den_bot (s : Shape) (t : Trace) : den s Mod.bot t := fun a h => by simp at h

theorem Alloc.contains_of_covers {al : Alloc} {a n : Nat} (h : al.covers a n) (hn : 0 < n) :
    al.contains a := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by omega⟩

theorem ne_zero_of_dereferenceable {s : Shape} {t : Trace} (h : Dereferenceable s t) :
    t.addr ≠ 0 := by
  obtain ⟨al, _, h1, h2, _⟩ := h
  omega

theorem zero_mod_align (s : Shape) : 0 % s.align = 0 := Nat.zero_mod _

theorem align_mod_align (s : Shape) : s.align % s.align = 0 := Nat.mod_self _

theorem one_mod_align_of_alignLog_ne_zero {s : Shape} (h : s.alignLog ≠ 0) :
    1 % s.align ≠ 0 := by
  have : 2 ≤ s.align := by
    unfold Shape.align
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.one_le_iff_ne_zero.mpr h)
    simpa using this
  rw [Nat.mod_eq_of_lt (by omega)]
  decide

theorem mod_align_of_alignLog_eq_zero {s : Shape} (h : s.alignLog = 0) (x : Nat) :
    x % s.align = 0 := by
  unfold Shape.align; rw [h, Nat.pow_zero, Nat.mod_one]

end Toy.Modality
