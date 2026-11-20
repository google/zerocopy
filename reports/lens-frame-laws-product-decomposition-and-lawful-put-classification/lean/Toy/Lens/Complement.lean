/-
Toy.Lens.Complement
===================

**F3 — constant-complement characterisation** of very well-behaved lenses.
Definitions, examples, supporting lemmas and the F3 main statements are all
proved.
-/
import Toy.Lens.Decomposition

namespace Toy

namespace Lens

universe u v w x

/-! ## Bundled bijections (core Lean has no `Equiv`) -/

/--
A bijection between two types, bundled with its inverse.

Meant to capture "`α` and `β` are the same type up to renaming of elements".
(Core Lean without Mathlib has no `Equiv`; this is the minimal local version.)
-/
structure Equiv (α : Type u) (β : Type v) where
  /-- The forward map. -/
  toFun : α → β
  /-- The inverse map. -/
  invFun : β → α
  /-- `invFun` undoes `toFun`. -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- `toFun` undoes `invFun`. -/
  right_inv : ∀ b, toFun (invFun b) = b

/-- Positive example for `Equiv`: the identity bijection. -/
def Equiv.refl (α : Type u) : Equiv α α where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl

/-- The forward map of an `Equiv` is injective. -/
theorem Equiv.injective {α : Type u} {β : Type v} (e : Equiv α β) : Function.Injective e.toFun :=
  fun a b h => (e.left_inv a).symm.trans ((congrArg e.invFun h).trans (e.left_inv b))

/-- Negative example for `Equiv`: there is no bijection between `Bool` and
`Unit`. -/
theorem not_equiv_bool_unit (e : Equiv Bool Unit) : False := by
  have h₀ : e.toFun true = e.toFun false := rfl
  have h : true = false :=
    (e.left_inv true).symm.trans ((congrArg e.invFun h₀).trans (e.left_inv false))
  exact absurd h (by decide)

variable {S : Type u} {A : Type v}

/-! ## Constant complements -/

/--
`HasConstantComplement l`: there is a *complement* type `C` and a bijection
`e : S ≃ A × C` under which `l` is the first-projection lens, i.e.

* `(e s).1 = l.get s`, and
* `e (l.put s a) = (a, (e s).2)`  — writing through `l` keeps the
  `C`-component constant.

Meant to capture Bancilhon–Spyratos "update translation under a constant
complement", in the form used for lenses: the state splits as *view × rest*
and `put` replaces the view and leaves the rest alone.

Terminology note: Bancilhon and Spyratos (1981) call a second view
`g : S → C` a complement when `s ↦ (get s, g s)` is merely *injective*; the
bijection `S ≃ A × C` required here is the specialisation to the case where
every view value may be written into every state (total `put`), as observed by
Foster et al. (2007, footnote 9).

The complement is required to live in the universe of `S`.  A complement
always exists there when the lens is very well-behaved: the quotient of `S`
by "`put s = put t`" is one, and it is used because, unlike the fibre of
`get`, it needs no base view.  For complements in other universes see
`veryWellBehaved_of_injective_intertwines_fst`.

Note what it does **not** capture: `C` is *some* complement, not a prescribed
sibling field.  `twist_hasConstantComplement` shows that the state-twisting
lens has a constant complement too.
-/
def HasConstantComplement (l : Lens S A) : Prop :=
  ∃ (C : Type u) (e : Equiv S (A × C)), Intertwines e.toFun l (fst : Lens (A × C) A)

/-- Positive example for `HasConstantComplement`: `fst` on a product, with
complement the second factor (lifted to the universe of the product). -/
theorem fst_hasConstantComplement {A : Type v} {B : Type w} :
    HasConstantComplement (fst : Lens (A × B) A) :=
  ⟨ULift.{v} B,
   { toFun := fun p => (p.1, ULift.up p.2)
     invFun := fun q => (q.1, q.2.down)
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl },
   ⟨fun _ => rfl, fun _ _ => rfl⟩⟩

/-- Positive example for `HasConstantComplement` that is *unintended*: the
state-twisting lens.  Its complement is not the second field `b` but the
"twisted" coordinate `a xor b`. -/
theorem twist_hasConstantComplement : HasConstantComplement twist := by
  refine ⟨Bool, ⟨fun p => (p.1, xor p.1 p.2), fun p => (p.1, xor p.1 p.2), ?_, ?_⟩, ?_, ?_⟩
  · intro ⟨a, b⟩
    cases a <;> cases b <;> rfl
  · intro ⟨a, c⟩
    cases a <;> cases c <;> rfl
  · intro _
    rfl
  · intro ⟨a, b⟩ a'
    cases a <;> cases b <;> cases a' <;> rfl

/-- Negative example for `HasConstantComplement`: the dirty-flag lens
(well-behaved, but not `PutPut`) has no constant complement. -/
theorem dirtyFlag_not_hasConstantComplement : ¬ HasConstantComplement dirtyFlag := by
  intro ⟨C, e, h⟩
  -- Under `e`, two successive writes look like one write ...
  have h₁ : e.toFun (dirtyFlag.put (dirtyFlag.put (false, false) true) false)
      = e.toFun (dirtyFlag.put (false, false) false) := by
    rw [h.put_eq, h.put_eq, h.put_eq]
    rfl
  -- ... so, `e` being injective, the two states would be equal.
  have h₂ := congrArg e.invFun h₁
  rw [e.left_inv, e.left_inv] at h₂
  exact absurd h₂ (by decide)

/-- Negative example for `HasConstantComplement`: the read-only field
(`GetPut` and `PutPut`, but not `PutGet`) has no constant complement. -/
theorem ignorePut_not_hasConstantComplement : ¬ HasConstantComplement ignorePut := by
  intro ⟨C, e, h⟩
  -- the write is ignored, so the first component of `e` would be both `true` and `false`
  have h₁ : (e.toFun (false, false)).1 = true :=
    congrArg Prod.fst (h.put_eq (false, false) true)
  have h₂ : (e.toFun (false, false)).1 = false := h.get_eq (false, false)
  rw [h₁] at h₂
  exact absurd h₂ (by decide)

/-- Negative example for `HasConstantComplement`: the sibling-resetting setter
(`PutGet` and `PutPut`, but not `GetPut`) has no constant complement. -/
theorem resetSibling_not_hasConstantComplement : ¬ HasConstantComplement resetSibling := by
  intro ⟨C, e, h⟩
  -- under `e`, writing back the current view is the identity ...
  have h₁ : e.toFun (resetSibling.put (false, true) (resetSibling.get (false, true)))
      = e.toFun (false, true) := by
    rw [h.put_eq, ← h.get_eq]
    rfl
  -- ... so, `e` being injective, `GetPut` would hold at `(false, true)`.
  have h₂ := congrArg e.invFun h₁
  rw [e.left_inv, e.left_inv] at h₂
  exact absurd h₂ (by decide)

/--
The fibre of `get` over a base view `a₀`: the states whose view is `a₀`.

Meant to capture the *canonical* complement of a very well-behaved lens when
a base view is available: "the rest of the state, with the field parked at
`a₀`".
-/
def Fiber (l : Lens S A) (a₀ : A) : Type u :=
  { s : S // l.get s = a₀ }

/-- The explicit inverse map of the fibre complement: `(a, c) ↦ l.put c a`.
(The forward map `s ↦ (l.get s, ⟨l.put s a₀, _⟩)` needs `PutGet` to land in
the fibre; it is pinned down by the equations in
`fiber_isConstantComplement_of_veryWellBehaved`, see
`fiberEquiv_eq_of_equations`.) -/
def fiberFrom (l : Lens S A) (a₀ : A) : A × Fiber l a₀ → S :=
  fun p => l.put p.2.1 p.1

/-- Positive example for `fiberFrom`: for `fst`, it writes the view into the
parked state. -/
theorem fiberFrom_fst {A : Type v} {B : Type w} (a₀ a : A) (b : B) :
    fiberFrom (fst : Lens (A × B) A) a₀ (a, ⟨(a₀, b), rfl⟩) = (a, b) :=
  rfl

/-- Negative example for `fiberFrom`: for the read-only field `ignorePut` it
does not write the view (it is not a right inverse of anything carrying
`get`). -/
theorem fiberFrom_ignorePut_ne :
    ignorePut.get (fiberFrom ignorePut false (true, ⟨(false, false), rfl⟩)) ≠ true := by
  decide

/-- **The equations of F3-fiber determine the bijection.**  Any two
bijections `S ≃ A × Fiber l a₀` satisfying the three conjuncts of the
conclusion of `fiber_isConstantComplement_of_veryWellBehaved` have the same
forward map and the same inverse map.  So the existential in that statement
names a unique, explicitly given bijection. -/
theorem fiberEquiv_eq_of_equations (l : Lens S A) (a₀ : A) (e e' : Equiv S (A × Fiber l a₀))
    (he : Intertwines e.toFun l (fst : Lens (A × Fiber l a₀) A) ∧
      (∀ s, ((e.toFun s).2).1 = l.put s a₀) ∧
      (∀ (a : A) (c : Fiber l a₀), e.invFun (a, c) = l.put c.1 a))
    (he' : Intertwines e'.toFun l (fst : Lens (A × Fiber l a₀) A) ∧
      (∀ s, ((e'.toFun s).2).1 = l.put s a₀) ∧
      (∀ (a : A) (c : Fiber l a₀), e'.invFun (a, c) = l.put c.1 a)) :
    e.toFun = e'.toFun ∧ e.invFun = e'.invFun := by
  refine ⟨funext fun s => ?_, funext fun p => ?_⟩
  · have h₁ : (e.toFun s).1 = (e'.toFun s).1 := (he.1.get_eq s).trans (he'.1.get_eq s).symm
    have h₂ : (e.toFun s).2 = (e'.toFun s).2 := Subtype.ext ((he.2.1 s).trans (he'.2.1 s).symm)
    exact Prod.ext h₁ h₂
  · exact (he.2.2 p.1 p.2).trans (he'.2.2 p.1 p.2).symm

/-- The fibre complement of the state-twisting lens is still twisted: with
base view `false`, the state `(true, b)` is parked at `(false, !b)`, not at
`(false, b)`. -/
theorem twist_put_park (b : Bool) : twist.put (true, b) false = (false, !b) := by
  cases b <;> rfl

/-- Positive example for `Fiber`: `(a₀, b)` lies in the fibre of `fst` over
`a₀`. -/
def fiberFstMk {A : Type v} {B : Type w} (a₀ : A) (b : B) :
    Fiber (fst : Lens (A × B) A) a₀ :=
  ⟨(a₀, b), rfl⟩

/-- Negative example for `Fiber`: the fibre of `fst` over `true` does not
contain a state whose first field is `false`. -/
theorem fiber_fst_true_val_ne (c : Fiber (fst : Lens (Bool × Bool) Bool) true) :
    c.1 ≠ (false, false) := by
  intro h
  have hc : (c.1).1 = true := c.2
  rw [h] at hc
  exact absurd hc (by decide)

/-! ## Ghost complements for a pair of lenses -/

section PairComplement

variable {B : Type w}

/--
`HasGhostComplement l₁ l₂`: there is a *ghost* type `G` and a bijection
`e : S ≃ A × B × G` under which `l₁` and `l₂` are the first and second field
lenses of a record whose third component is `G`, i.e.

* `(e s).1 = l₁.get s` and `e (l₁.put s a) = (a, (e s).2.1, (e s).2.2)`;
* `(e s).2.1 = l₂.get s` and `e (l₂.put s b) = ((e s).1, b, (e s).2.2)`.

Meant to capture "setting one field changes that field and nothing else"
**without** the claim that the two fields are all there is: the state may
carry further data `G`, which neither setter touches.  It is the two-lens
analogue of `HasConstantComplement`.  `IsProductDecomposition` corresponds to
a *one-point* ghost (`G` with exactly one element); an *empty* ghost is
possible only when `S` is empty, and then `IsProductDecomposition` can fail
while `HasGhostComplement` holds (when `A × B` is inhabited).
-/
def HasGhostComplement (l₁ : Lens S A) (l₂ : Lens S B) : Prop :=
  ∃ (G : Type u) (e : Equiv S (A × B × G)),
    Intertwines e.toFun l₁ (ghostFst : Lens (A × B × G) A) ∧
    Intertwines e.toFun l₂ (ghostSnd : Lens (A × B × G) B)

/-- Positive example for `HasGhostComplement`: the two visible fields of a
record with a ghost component, with the ghost itself (lifted to the universe of
the record) as complement. -/
theorem ghost_hasGhostComplement {A : Type v} {B : Type w} {G : Type x} :
    HasGhostComplement (ghostFst : Lens (A × B × G) A) (ghostSnd : Lens (A × B × G) B) :=
  ⟨ULift.{max v w} G,
   { toFun := fun s => (s.1, s.2.1, ULift.up s.2.2)
     invFun := fun q => (q.1, q.2.1, q.2.2.down)
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl },
   ⟨fun _ => rfl, fun _ _ => rfl⟩, ⟨fun _ => rfl, fun _ _ => rfl⟩⟩

/-- Positive example for `HasGhostComplement`: `fst` and `snd` on a product,
with a one-point type as ghost. -/
theorem fst_snd_hasGhostComplement {A : Type v} {B : Type w} :
    HasGhostComplement (fst : Lens (A × B) A) (snd : Lens (A × B) B) :=
  ⟨PUnit, ⟨fun p => (p.1, p.2, PUnit.unit), fun q => (q.1, q.2.1), fun _ => rfl, fun _ => rfl⟩,
    ⟨fun _ => rfl, fun _ _ => rfl⟩, ⟨fun _ => rfl, fun _ _ => rfl⟩⟩

/-- Reassociation: a ghost complement for `(l₁, l₂)` is in particular a
constant complement for `l₁` (with complement `B × G`).  Stated for view types
in the universe of `S`, where `B × G` is again in that universe. -/
theorem hasConstantComplement_left_of_hasGhostComplement {S A B : Type u}
    {l₁ : Lens S A} {l₂ : Lens S B} (h : HasGhostComplement l₁ l₂) : HasConstantComplement l₁ := by
  obtain ⟨G, e, h₁, _⟩ := h
  exact ⟨B × G, e, ⟨h₁.get_eq, h₁.put_eq⟩⟩

/-- Reassociation: a ghost complement for `(l₁, l₂)` is in particular a
constant complement for `l₂` (with complement `A × G`). -/
theorem hasConstantComplement_right_of_hasGhostComplement {S A B : Type u}
    {l₁ : Lens S A} {l₂ : Lens S B} (h : HasGhostComplement l₁ l₂) : HasConstantComplement l₂ := by
  obtain ⟨G, e, _, h₂⟩ := h
  refine ⟨A × G,
    ⟨fun s => ((e.toFun s).2.1, (e.toFun s).1, (e.toFun s).2.2),
     fun q => e.invFun (q.2.1, q.1, q.2.2),
     fun s => e.left_inv s,
     fun q => ?_⟩,
    ⟨h₂.get_eq, fun s b => ?_⟩⟩
  · show ((e.toFun (e.invFun (q.2.1, q.1, q.2.2))).2.1,
        (e.toFun (e.invFun (q.2.1, q.1, q.2.2))).1,
        (e.toFun (e.invFun (q.2.1, q.1, q.2.2))).2.2) = q
    rw [e.right_inv]
  · show ((e.toFun (l₂.put s b)).2.1, (e.toFun (l₂.put s b)).1, (e.toFun (l₂.put s b)).2.2) =
        (b, (e.toFun s).1, (e.toFun s).2.2)
    rw [h₂.put_eq]
    rfl

/-- Negative example for `HasGhostComplement`: two aliasing copies of `fst`.
Both are very well-behaved, but their puts do not commute. -/
theorem fstB_fstB_not_hasGhostComplement :
    ¬ HasGhostComplement (fst : Lens (Bool × Bool) Bool) (fst : Lens (Bool × Bool) Bool) := by
  intro ⟨G, e, h₁, h₂⟩
  have step₁ : e.toFun ((fst : Lens (Bool × Bool) Bool).put
        ((fst : Lens (Bool × Bool) Bool).put (false, false) true) false)
      = ghostSnd.put (ghostFst.put (e.toFun (false, false)) true) false :=
    (h₂.put_eq _ _).trans (congrArg (fun x => ghostSnd.put x false) (h₁.put_eq _ _))
  have step₂ : e.toFun ((fst : Lens (Bool × Bool) Bool).put
        ((fst : Lens (Bool × Bool) Bool).put (false, false) false) true)
      = ghostFst.put (ghostSnd.put (e.toFun (false, false)) false) true :=
    (h₁.put_eq _ _).trans (congrArg (fun x => ghostFst.put x true) (h₂.put_eq _ _))
  have h' := Equiv.injective e (step₁.trans step₂.symm)
  exact absurd h' (by decide)

/-- Negative example for `HasGhostComplement`: the state-twisting lens and
`snd`.  Both are very well-behaved, but their puts do not commute, so they are
not two fields of any record. -/
theorem twist_snd_not_hasGhostComplement :
    ¬ HasGhostComplement twist (snd : Lens (Bool × Bool) Bool) := by
  intro ⟨G, e, h₁, h₂⟩
  -- Under `e` the two puts are coordinate updates, hence commute ...
  have step₁ : e.toFun ((snd : Lens (Bool × Bool) Bool).put (twist.put (false, false) true) false)
      = ghostSnd.put (ghostFst.put (e.toFun (false, false)) true) false :=
    (h₂.put_eq _ _).trans (congrArg (fun x => ghostSnd.put x false) (h₁.put_eq _ _))
  have step₂ : e.toFun (twist.put ((snd : Lens (Bool × Bool) Bool).put (false, false) false) true)
      = ghostFst.put (ghostSnd.put (e.toFun (false, false)) false) true :=
    (h₁.put_eq _ _).trans (congrArg (fun x => ghostFst.put x true) (h₂.put_eq _ _))
  have h : e.toFun ((snd : Lens (Bool × Bool) Bool).put (twist.put (false, false) true) false)
      = e.toFun (twist.put ((snd : Lens (Bool × Bool) Bool).put (false, false) false) true) :=
    step₁.trans step₂.symm
  -- ... so, `e` being injective, the two original puts would commute too.
  have h' := congrArg e.invFun h
  rw [e.left_inv, e.left_inv] at h'
  exact absurd h' (by decide)

end PairComplement

/-- On the empty state type every lens is very well-behaved, and its getter
need not be surjective: very-well-behavedness alone does not make `get`
surjective. -/
theorem emptyState_veryWellBehaved_not_surjective (l : Lens Empty Bool) :
    l.VeryWellBehaved ∧ ¬ Function.Surjective l.get :=
  ⟨⟨fun s => s.elim, fun s => s.elim, fun s => s.elim⟩,
   fun h => (h true).elim fun s _ => s.elim⟩

/-! ## F3 — main statements -/

/--
**F3 (constant-complement characterisation).**  A lens is very well-behaved
if and only if it has a constant complement: a type `C` in the universe of `S`
and a bijection `S ≃ A × C` turning `get` into the first projection and `put`
into first-coordinate update.

No inhabitedness hypothesis appears in either direction: neither `S` nor `A`
is assumed nonempty.
-/
theorem veryWellBehaved_iff_hasConstantComplement (l : Lens S A) :
    l.VeryWellBehaved ↔ HasConstantComplement l := by
  constructor
  · -- laws ⇒ complement: the complement is `S` modulo "same put"
    rintro ⟨hgp, hpg, hpp⟩
    let r : S → S → Prop := fun s t => ∀ a, l.put s a = l.put t a
    refine ⟨Quot r,
      { toFun := fun s => (l.get s, Quot.mk r s)
        invFun := fun p => Quot.lift (fun s => l.put s p.1) (fun s t hst => hst p.1) p.2
        left_inv := fun s => hgp s
        right_inv := fun ⟨a, q⟩ =>
          @Quot.ind S r (fun q => (l.get (Quot.lift (fun s => l.put s a) (fun s t hst => hst a) q),
            Quot.mk r (Quot.lift (fun s => l.put s a) (fun s t hst => hst a) q)) = (a, q))
            (fun s => Prod.ext (hpg s a) (Quot.sound fun a' => hpp s a a')) q },
      ⟨fun _ => rfl, fun s a => Prod.ext (hpg s a) (Quot.sound fun a' => hpp s a a')⟩⟩
  · -- complement ⇒ laws: cancel the injective map `e.toFun`
    rintro ⟨C, e, h⟩
    have hf : Function.Injective e.toFun := e.injective
    refine ⟨fun s => hf ?_, fun s a => ?_, fun s a a' => hf ?_⟩
    · rw [h.put_eq, ← h.get_eq]
      rfl
    · exact (h.get_eq (l.put s a)).symm.trans (congrArg Prod.fst (h.put_eq s a))
    · rw [h.put_eq, h.put_eq, h.put_eq]
      rfl

/--
**F3, direction "complement ⇒ laws", sharp form.**  It is enough to have an
*injective* map `f : S → A × C` (into a product with a complement type `C` in
*any* universe) under which `l` is the first-projection lens; surjectivity of
`f` is not needed.
-/
theorem veryWellBehaved_of_injective_intertwines_fst {C : Type x}
    (l : Lens S A) (f : S → A × C) (hf : Function.Injective f)
    (h : Intertwines f l (fst : Lens (A × C) A)) :
    l.VeryWellBehaved := by
  refine ⟨fun s => hf ?_, fun s a => ?_, fun s a a' => hf ?_⟩
  · rw [h.put_eq, ← h.get_eq]
    rfl
  · exact (h.get_eq (l.put s a)).symm.trans (congrArg Prod.fst (h.put_eq s a))
  · rw [h.put_eq, h.put_eq, h.put_eq]
    rfl

/--
**F3, direction "laws ⇒ complement", explicit form with a base view.**  If `l`
is very well-behaved and a base view `a₀ : A` is given, then the fibre of
`get` over `a₀` is a constant complement, with the explicit bijection

* `s ↦ (l.get s, l.put s a₀)` and
* `(a, c) ↦ l.put c a` (this is `fiberFrom l a₀`).

The three conjuncts determine the bijection uniquely
(`fiberEquiv_eq_of_equations`).  The base view is what makes the complement a
*subtype of `S`*; without it (F3 proper) the complement is only known to exist
as some type.
-/
theorem fiber_isConstantComplement_of_veryWellBehaved
    (l : Lens S A) (hl : l.VeryWellBehaved) (a₀ : A) :
    ∃ e : Equiv S (A × Fiber l a₀),
      Intertwines e.toFun l (fst : Lens (A × Fiber l a₀) A) ∧
      (∀ s, ((e.toFun s).2).1 = l.put s a₀) ∧
      (∀ (a : A) (c : Fiber l a₀), e.invFun (a, c) = l.put c.1 a) := by
  rcases hl with ⟨hgp, hpg, hpp⟩
  refine ⟨{
    toFun := fun s => (l.get s, ⟨l.put s a₀, hpg s a₀⟩)
    invFun := fun p => l.put p.2.1 p.1
    left_inv := fun s => (hpp s a₀ (l.get s)).trans (hgp s)
    right_inv := fun ⟨a, ⟨c, hc⟩⟩ =>
      Prod.ext (hpg c a) (Subtype.ext ((hpp c a a₀).trans (hc ▸ hgp c)))
  }, ⟨fun _ => rfl, fun s a => Prod.ext (hpg s a) (Subtype.ext (hpp s a a₀))⟩,
  fun _ => rfl, fun _ _ => rfl⟩

/--
**F3, pair form (ghost-complement characterisation).**  Two lenses on the same
state are both very well-behaved and have commuting puts if and only if they
are, up to a bijection `S ≃ A × B × G` with `G` in the universe of `S`, the
first and second field lenses of a record with a third, untouched component
`G`.

This is the statement "setting one field changes that field and nothing else"
*without* joint extensionality: two very well-behaved lenses with commuting
puts are the two fields of a record with some further, untouched component.
No inhabitedness hypothesis appears.  It is the two-lens analogue of F3.
-/
theorem veryWellBehaved_and_putComm_iff_hasGhostComplement {B : Type w}
    (l₁ : Lens S A) (l₂ : Lens S B) :
    (l₁.VeryWellBehaved ∧ l₂.VeryWellBehaved ∧ PutComm l₁ l₂) ↔ HasGhostComplement l₁ l₂ := by
  constructor
  · rintro ⟨⟨gp₁, pg₁, pp₁⟩, ⟨gp₂, pg₂, pp₂⟩, hcomm⟩
    -- commuting puts give cross-independence of `l₂` from `l₁`
    have ind₂₁ : PutIndep l₂ l₁ := fun s b => by
      have h : l₂.put s b = l₁.put (l₂.put s b) (l₁.get s) := by
        rw [← hcomm, gp₁]
      exact (congrArg l₁.get h).trans (pg₁ _ _)
    -- the combined lens onto `A × B` is very well-behaved ...
    let lsum : Lens S (A × B) := {
      get := fun s => (l₁.get s, l₂.get s)
      put := fun s p => l₂.put (l₁.put s p.1) p.2
    }
    have hvwb : lsum.VeryWellBehaved := by
      refine ⟨fun s => ?_, fun s ⟨a, b⟩ => ?_, fun s ⟨a, b⟩ ⟨a', b'⟩ => ?_⟩
      · show l₂.put (l₁.put s (l₁.get s)) (l₂.get s) = s
        rw [gp₁, gp₂]
      · show (l₁.get (l₂.put (l₁.put s a) b), l₂.get (l₂.put (l₁.put s a) b)) = (a, b)
        rw [ind₂₁, pg₁, pg₂]
      · show l₂.put (l₁.put (l₂.put (l₁.put s a) b) a') b' = l₂.put (l₁.put s a') b'
        rw [← hcomm (l₁.put s a) a' b, pp₂, pp₁]
    -- ... so it has a constant complement `G` (F3), which is the ghost
    obtain ⟨G, e, he⟩ := (veryWellBehaved_iff_hasConstantComplement lsum).mp hvwb
    refine ⟨G, {
      toFun := fun s => let q := e.toFun s; (q.1.1, q.1.2, q.2)
      invFun := fun t => e.invFun ((t.1, t.2.1), t.2.2)
      left_inv := fun s => e.left_inv s
      right_inv := fun ⟨a, b, g⟩ => by
        show (let q := e.toFun (e.invFun ((a, b), g)); (q.1.1, q.1.2, q.2)) = (a, b, g)
        rw [e.right_inv]
    }, ⟨fun s => congrArg Prod.fst (he.get_eq s), fun s a => ?_⟩,
       ⟨fun s => congrArg Prod.snd (he.get_eq s), fun s b => ?_⟩⟩
    · have hp : l₁.put s a = lsum.put s (a, l₂.get s) := by
        show l₁.put s a = l₂.put (l₁.put s a) (l₂.get s)
        rw [hcomm, gp₂]
      rw [hp]
      have hq := he.put_eq s (a, l₂.get s)
      have hg₂ : (e.toFun s).1.2 = l₂.get s := congrArg Prod.snd (he.get_eq s)
      show ((e.toFun (lsum.put s (a, l₂.get s))).1.1,
            (e.toFun (lsum.put s (a, l₂.get s))).1.2,
            (e.toFun (lsum.put s (a, l₂.get s))).2) =
           (a, (e.toFun s).1.2, (e.toFun s).2)
      rw [hq, ← hg₂]
      rfl
    · have hp : l₂.put s b = lsum.put s (l₁.get s, b) := by
        show l₂.put s b = l₂.put (l₁.put s (l₁.get s)) b
        rw [gp₁]
      rw [hp]
      have hq := he.put_eq s (l₁.get s, b)
      have hg₁ : (e.toFun s).1.1 = l₁.get s := congrArg Prod.fst (he.get_eq s)
      show ((e.toFun (lsum.put s (l₁.get s, b))).1.1,
            (e.toFun (lsum.put s (l₁.get s, b))).1.2,
            (e.toFun (lsum.put s (l₁.get s, b))).2) =
           ((e.toFun s).1.1, b, (e.toFun s).2)
      rw [hq, ← hg₁]
      rfl
  · rintro ⟨G, e, h₁, h₂⟩
    have hinj : Function.Injective e.toFun := e.injective
    have vwb₁ : l₁.VeryWellBehaved :=
      veryWellBehaved_of_injective_intertwines_fst l₁
        (fun s => ((e.toFun s).1, ((e.toFun s).2.1, (e.toFun s).2.2)))
        (fun s t hst => hinj (Prod.ext (congrArg Prod.fst hst) (congrArg Prod.snd hst)))
        ⟨h₁.get_eq, fun s a => by rw [h₁.put_eq]; rfl⟩
    have vwb₂ : l₂.VeryWellBehaved :=
      veryWellBehaved_of_injective_intertwines_fst l₂
        (fun s => ((e.toFun s).2.1, ((e.toFun s).1, (e.toFun s).2.2)))
        (fun s t (hst : ((e.toFun s).2.1, ((e.toFun s).1, (e.toFun s).2.2)) =
                        ((e.toFun t).2.1, ((e.toFun t).1, (e.toFun t).2.2))) =>
          hinj (Prod.ext (congrArg (fun q => q.2.1) hst)
            (Prod.ext (congrArg (fun q : B × A × G => q.1) hst)
              (congrArg (fun q : B × A × G => q.2.2) hst))))
        ⟨h₂.get_eq, fun s b => by rw [h₂.put_eq]; rfl⟩
    refine ⟨vwb₁, vwb₂, fun s a b => hinj ?_⟩
    rw [h₂.put_eq, h₁.put_eq, h₁.put_eq, h₂.put_eq]
    rfl

end Lens

end Toy
