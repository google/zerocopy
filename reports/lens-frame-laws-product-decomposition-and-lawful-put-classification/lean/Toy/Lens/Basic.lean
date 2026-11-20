/-
Toy.Lens.Basic
==============

Total monomorphic lenses and the three classical lens laws, each as a
separate `Prop`, with a proved positive and a proved negative example for
every definition.

No Mathlib; core Lean only.
-/

namespace Toy

universe u v w

/--
A **total, monomorphic lens** from a state type `S` onto a view type `A`.

It is meant to capture the bare *interface* of a field of a record: a getter
`get` that reads the field out of a state and a setter `put` that writes a new
value of the field into a state.

* *total*: `get` and `put` are defined on every state (contrast `PLens`, where
  the field exists only on one variant of a sum type);
* *monomorphic*: writing cannot change the type of the state or of the field.

The structure carries **no laws**.  Every law is a separate `Prop` below, so
that theorems can state exactly which ones they use.
-/
structure Lens (S : Type u) (A : Type v) where
  /-- Read the view (the "field") out of a state. -/
  get : S → A
  /-- Write a new view into a state, producing the updated state. -/
  put : S → A → S

namespace Lens

variable {S : Type u} {A : Type v} {B : Type w}

/-! ## The three classical laws, as separate propositions -/

/--
**GetPut** — "writing back what you just read changes nothing".

Meant to capture: a setter has no side effect on the state beyond the field
itself *when the field value does not change*.  It rejects setters that touch
anything else unconditionally (see `resetSibling_not_getPut`).

Terminology note: the names follow Foster et al. (2007), where *GetPut* is
`put s (get s) = s`.  Several libraries (the Haskell `lens` package, some Lean
and Agda developments) use the opposite convention and call this law
`set-get`/`put_get`; only the equation, not the name, is authoritative.
-/
def GetPut (l : Lens S A) : Prop :=
  ∀ s, l.put s (l.get s) = s

/--
**PutGet** — "you read what you just wrote".

Meant to capture: the setter really stores the value.  It rejects read-only
or clamping "fields" whose setter drops (part of) the written value (see
`ignorePut_not_putGet`).

Terminology note: this is *PutGet* in the convention of Foster et al. (2007),
`get (put s a) = a`; some libraries call the same equation `get-set`/`get_put`.
-/
def PutGet (l : Lens S A) : Prop :=
  ∀ s a, l.get (l.put s a) = a

/--
**PutPut** — "the second write wins; the first leaves no trace".

Meant to capture: the setter keeps no history.  It rejects setters that
record that a write happened (see `dirtyFlag_not_putPut`).
-/
def PutPut (l : Lens S A) : Prop :=
  ∀ s a a', l.put (l.put s a) a' = l.put s a'

/--
**Well-behaved** = `GetPut ∧ PutGet` (Foster et al. 2007, "well-behaved lens").
Deliberately does *not* include `PutPut`.
-/
def WellBehaved (l : Lens S A) : Prop :=
  l.GetPut ∧ l.PutGet

/--
**Very well-behaved** = `GetPut ∧ PutGet ∧ PutPut` (Foster et al. 2007,
"very well-behaved lens").

Note what this is *not* meant to capture: it is a property of one lens in
isolation and says nothing about what `put` does to the *rest* of the state.
`twist_veryWellBehaved` is a very well-behaved lens whose setter flips a
sibling field.
-/
def VeryWellBehaved (l : Lens S A) : Prop :=
  l.GetPut ∧ l.PutGet ∧ l.PutPut

/-! ## Example lenses

The intended models (`fst`, `snd`) and four small "lawful-but-unintended" or
"almost lawful" setters on `Bool × Bool` used as negative examples.
-/

/-- The intended model: the first field of a pair. -/
def fst : Lens (A × B) A where
  get p := p.1
  put p a := (a, p.2)

/-- The intended model: the second field of a pair. -/
def snd : Lens (A × B) B where
  get p := p.2
  put p b := (p.1, b)

/-- A read-only "field": the setter silently ignores the written value. -/
def ignorePut : Lens (Bool × Bool) Bool where
  get p := p.1
  put p _ := p

/-- A setter with an unconditional side effect: it writes the first field and
resets the second field to `false`. -/
def resetSibling : Lens (Bool × Bool) Bool where
  get p := p.1
  put _ a := (a, false)

/-- A setter that keeps history: the second component is a *dirty flag* that
is raised whenever the first field is overwritten with a different value. -/
def dirtyFlag : Lens (Bool × Bool) Bool where
  get p := p.1
  put p a := if p.1 = a then p else (a, true)

/-- A **state-twisting** setter: it writes the first field and flips the
second field exactly when the written value differs from the old one.
It satisfies all three single-lens laws (`twist_veryWellBehaved`). -/
def twist : Lens (Bool × Bool) Bool where
  get p := p.1
  put p a := (a, xor p.2 (xor p.1 a))

/-- The **XOR view**: the view is `p.1 xor p.2`; writing it adjusts the second
component and keeps the first.  It satisfies all three single-lens laws
(`xorView_veryWellBehaved`), but is entangled with `fst`. -/
def xorView : Lens (Bool × Bool) Bool where
  get p := xor p.1 p.2
  put p v := (p.1, xor p.1 v)

/-! ## `Lens`: what the bare structure accepts and rejects

`Lens` carries no laws, so every pair of functions of the right types is a
lens; `fst` and `snd` above are the positive examples.  The one thing the
*type* rejects is a field that some state does not have: -/

/-- Negative example for `Lens`: there is no total lens from an inhabited
state type onto an empty view type — a total `get` would have to produce a
view.  (A *partial* lens with this shape does exist: `PLens.absent`.) -/
theorem not_lens_of_empty_view {S : Type u} (l : Lens S Empty) (s : S) : False :=
  (l.get s).elim

/-! ## `GetPut`: positive and negative examples -/

/-- Positive example for `GetPut`. -/
theorem fst_getPut : (fst : Lens (A × B) A).GetPut := fun _ => rfl

/-- Positive example for `GetPut`. -/
theorem snd_getPut : (snd : Lens (A × B) B).GetPut := fun _ => rfl

/-- Negative example for `GetPut`: a setter that always resets the sibling.
(It does satisfy `PutGet` and `PutPut`, so `GetPut` is independent of them.) -/
theorem resetSibling_not_getPut : ¬ resetSibling.GetPut :=
  fun h => absurd (h (false, true)) (by decide)

theorem resetSibling_putGet : resetSibling.PutGet := fun _ _ => rfl

theorem resetSibling_putPut : resetSibling.PutPut := fun _ _ _ => rfl

/-! ## `PutGet`: positive and negative examples -/

/-- Positive example for `PutGet`. -/
theorem fst_putGet : (fst : Lens (A × B) A).PutGet := fun _ _ => rfl

/-- Positive example for `PutGet`. -/
theorem snd_putGet : (snd : Lens (A × B) B).PutGet := fun _ _ => rfl

/-- Negative example for `PutGet`: a setter that ignores the written value.
(It does satisfy `GetPut` and `PutPut`, so `PutGet` is independent of them.) -/
theorem ignorePut_not_putGet : ¬ ignorePut.PutGet :=
  fun h => absurd (h (false, false) true) (by decide)

theorem ignorePut_getPut : ignorePut.GetPut := fun _ => rfl

theorem ignorePut_putPut : ignorePut.PutPut := fun _ _ _ => rfl

/-! ## `PutPut`: positive and negative examples -/

/-- Positive example for `PutPut`. -/
theorem fst_putPut : (fst : Lens (A × B) A).PutPut := fun _ _ _ => rfl

/-- Positive example for `PutPut`. -/
theorem snd_putPut : (snd : Lens (A × B) B).PutPut := fun _ _ _ => rfl

theorem dirtyFlag_getPut : dirtyFlag.GetPut := by
  intro ⟨a, d⟩
  cases a <;> cases d <;> rfl

theorem dirtyFlag_putGet : dirtyFlag.PutGet := by
  intro ⟨a, d⟩ a'
  cases a <;> cases d <;> cases a' <;> rfl

/-- Negative example for `PutPut`: a setter that raises a dirty flag.
(It does satisfy `GetPut` and `PutGet`, so `PutPut` is independent of them.) -/
theorem dirtyFlag_not_putPut : ¬ dirtyFlag.PutPut :=
  fun h => absurd (h (false, false) true false) (by decide)

/-! ## `WellBehaved`: positive and negative examples -/

/-- Positive example for `WellBehaved`. -/
theorem fst_wellBehaved : (fst : Lens (A × B) A).WellBehaved :=
  ⟨fst_getPut, fst_putGet⟩

/-- Positive example for `WellBehaved` that is *not* very well-behaved. -/
theorem dirtyFlag_wellBehaved : dirtyFlag.WellBehaved :=
  ⟨dirtyFlag_getPut, dirtyFlag_putGet⟩

/-- Negative example for `WellBehaved` (fails `PutGet`). -/
theorem ignorePut_not_wellBehaved : ¬ ignorePut.WellBehaved :=
  fun h => ignorePut_not_putGet h.2

/-- Negative example for `WellBehaved` (fails `GetPut`). -/
theorem resetSibling_not_wellBehaved : ¬ resetSibling.WellBehaved :=
  fun h => resetSibling_not_getPut h.1

/-! ## `VeryWellBehaved`: positive and negative examples -/

/-- Positive example for `VeryWellBehaved`. -/
theorem fst_veryWellBehaved : (fst : Lens (A × B) A).VeryWellBehaved :=
  ⟨fst_getPut, fst_putGet, fst_putPut⟩

/-- Positive example for `VeryWellBehaved`. -/
theorem snd_veryWellBehaved : (snd : Lens (A × B) B).VeryWellBehaved :=
  ⟨snd_getPut, snd_putGet, snd_putPut⟩

/-- Positive example for `VeryWellBehaved` that is nevertheless *unintended*:
the state-twisting setter. -/
theorem twist_veryWellBehaved : twist.VeryWellBehaved := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨a, b⟩
    cases a <;> cases b <;> rfl
  · intro ⟨a, b⟩ a'
    rfl
  · intro ⟨a, b⟩ a' a''
    cases a <;> cases b <;> cases a' <;> cases a'' <;> rfl

/-- Positive example for `VeryWellBehaved`: the XOR view. -/
theorem xorView_veryWellBehaved : xorView.VeryWellBehaved := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨a, b⟩
    cases a <;> cases b <;> rfl
  · intro ⟨a, b⟩ v
    cases a <;> cases b <;> cases v <;> rfl
  · intro ⟨a, b⟩ v v'
    cases a <;> cases b <;> cases v <;> cases v' <;> rfl

/-- Negative example for `VeryWellBehaved`: well-behaved but not `PutPut`. -/
theorem dirtyFlag_not_veryWellBehaved : ¬ dirtyFlag.VeryWellBehaved :=
  fun h => dirtyFlag_not_putPut h.2.2

end Lens

end Toy
