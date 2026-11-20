/-
Toy.Lens.Partial
================

**F5 — partial lenses on sum types.**

A field that exists only on one variant of a sum type is modelled by a
*partial* lens whose `get` and `put` return `Option`.  This file

* defines the variant-scoped laws and the variant-scoped conclusion, each with
  proved positive and negative examples;
* states and proves the variant-scoped version of F1 and its exact form;
* proves that **unscoped** joint extensionality is the wrong law for sum
  types: it identifies all states outside the variant, so it is violated by
  the intended model as soon as the type has two distinct states without the
  fields (e.g. two nullary tags);
* proves that variant-scoped laws, and even unscoped frame laws, do not
  prevent writes that switch the variant.
-/
import Toy.Lens.Tightness

namespace Toy

namespace Lens

universe u v w

/--
A **partial lens** from `S` onto `A`: a field that need not exist in every
state.  `get s = none` means "`s` has no such field"; `put s a = none` means
"the field cannot be written in `s`".

Meant to capture a field getter/setter pair of a value algebra whose values
form a sum type.  As with `Lens`, the structure carries no laws.

Modelling gap: the field type `A` is *typed*.  A unityped interface
`getField : Val → Option Val`, `setField : Val → Val → Option Val` (with
`A = Val`) usually rejects ill-typed written values by returning `none`; the
totality condition `TotalOn` below demands that *every* `a : A` can be written
on the variant, so such an interface fits only after restricting `A` to the
well-typed values (a subtype of `Val`).

Terminology note: this differs from the *affine traversals* ("optionals") of
profunctor optics, whose setter is total and a no-op where the field is
absent, from the `mwb_lens` class of the Isabelle AFP *Optics* entry (total
`put`, partial domain via `lens_source`), and from prisms (`wb_prism`), which
also fix the behaviour outside the variant.
-/
structure PLens (S : Type u) (A : Type v) where
  /-- Read the field, if the state has it. -/
  get : S → Option A
  /-- Write the field, if the state has it. -/
  put : S → A → Option S

namespace PLens

variable {S : Type u} {A : Type v} {B : Type w}

/-- Positive example for `PLens`: the field that no state has.  Unlike a total
lens (`Lens.not_lens_of_empty_view`), a partial lens may have an empty view
type on an inhabited state type.  (`PLens`, like `Lens`, carries no laws, so
there is nothing for the bare structure to reject.) -/
def absent : PLens S A where
  get _ := none
  put _ _ := none

/-! ## Variant-scoped laws

Throughout, `V : S → Prop` is the *variant*: the set of states on which the
fields are supposed to exist.
-/

/--
`TotalOn V l`: on the variant `V` the partial lens behaves like a total one —
`get` succeeds, `put` succeeds, and `put` stays inside the variant.

Meant to capture "the field exists on every state of the variant, and writing
it does not change the variant".  Its three components (`get` succeeds; `put`
succeeds; `put` stays in `V`) are independently needed for F5
(`totalOn_components_tight`).

Why `V` is an arbitrary predicate and not the domain of `get`: when two
variants of a sum type have fields of the same name, the domain of the field
getters spans both variants and joint extensionality fails there, while it
holds on each variant separately (`twin_jointExtOn_fails_on_union`).
-/
structure TotalOn (V : S → Prop) (l : PLens S A) : Prop where
  /-- On the variant, the field can be read. -/
  get_defined : ∀ s, V s → ∃ a, l.get s = some a
  /-- On the variant, the field can be written, and the result is again in
  the variant. -/
  put_defined : ∀ s a, V s → ∃ s', l.put s a = some s' ∧ V s'

/--
Variant-scoped **PutGet**: if a write succeeds on a state of the variant, the
written value is read back.
-/
def PutGetOn (V : S → Prop) (l : PLens S A) : Prop :=
  ∀ s a s', V s → l.put s a = some s' → l.get s' = some a

/--
Variant-scoped **cross-independence, one direction**: if a write through `l₁`
succeeds on a state of the variant, the `l₂`-field is unchanged.
-/
def PutIndepOn (V : S → Prop) (l₁ : PLens S A) (l₂ : PLens S B) : Prop :=
  ∀ s a s', V s → l₁.put s a = some s' → l₂.get s' = l₂.get s

/--
Variant-scoped **joint extensionality**: two states *of the variant* with
equal `l₁`-fields and equal `l₂`-fields are equal.

Meant to capture "the variant has no component other than these two fields".
The restriction to the variant is essential; compare `PLens.JointExt`.
-/
def JointExtOn (V : S → Prop) (l₁ : PLens S A) (l₂ : PLens S B) : Prop :=
  ∀ s t, V s → V t → l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t

/--
**Unscoped** joint extensionality: *any* two states with equal `l₁`-fields
and equal `l₂`-fields are equal — including states where both fields are
absent (`none = none`).

This is the naive transcription of `Lens.JointExt` to partial lenses.  It is
recorded here only to show that it is the **wrong law** for sum types: see
`eq_of_jointExt_of_get_eq_none` and
`pairFst_pairSnd_not_jointExt`.
-/
def JointExt (l₁ : PLens S A) (l₂ : PLens S B) : Prop :=
  ∀ s t, l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t

/--
`IsProductDecompositionOn V l₁ l₂` is the **conclusion of F5**: on the variant
`V`, the two partial lenses present the states as the product `A × B`.

* `get_defined` : every state of the variant has both fields;
* `injective`   : a state of the variant is determined by its two fields;
* `surjective`  : every pair of field values is realised by a state of the
                  variant;
* `put_fst`     : on the variant, `l₁.put` succeeds, stays in the variant, sets
                  the first field and leaves the second field unchanged;
* `put_snd`     : symmetrically for `l₂.put`.

It says **nothing** about states outside the variant.
-/
structure IsProductDecompositionOn (V : S → Prop) (l₁ : PLens S A) (l₂ : PLens S B) :
    Prop where
  /-- Every state of the variant has both fields. -/
  get_defined : ∀ s, V s → ∃ a b, l₁.get s = some a ∧ l₂.get s = some b
  /-- A state of the variant is determined by its two fields. -/
  injective : ∀ s t, V s → V t → l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t
  /-- Every pair of field values is realised by a state of the variant. -/
  surjective : ∀ a b, ∃ s, V s ∧ l₁.get s = some a ∧ l₂.get s = some b
  /-- On the variant, `l₁.put` is first-coordinate update. -/
  put_fst : ∀ s a, V s →
    ∃ s', l₁.put s a = some s' ∧ V s' ∧ l₁.get s' = some a ∧ l₂.get s' = l₂.get s
  /-- On the variant, `l₂.put` is second-coordinate update. -/
  put_snd : ∀ s b, V s →
    ∃ s', l₂.put s b = some s' ∧ V s' ∧ l₁.get s' = l₁.get s ∧ l₂.get s' = some b

/-! ## The intended model: a sum type with one binary variant and two nullary tags -/

/-- A small sum type: two nullary tags and one binary record variant. -/
inductive Shape where
  /-- A nullary tag. -/
  | nil
  /-- Another nullary tag. -/
  | unit
  /-- The record variant, with two Boolean fields. -/
  | pair (a b : Bool)
  deriving DecidableEq

/-- The variant of `Shape` on which the two fields exist. -/
def Shape.IsPair (s : Shape) : Prop :=
  ∃ a b, s = Shape.pair a b

/-- Positive example for `Shape.IsPair`. -/
theorem Shape.isPair_pair (a b : Bool) : (Shape.pair a b).IsPair :=
  ⟨a, b, rfl⟩

/-- Negative example for `Shape.IsPair`: a nullary tag is not a pair. -/
theorem Shape.not_isPair_nil : ¬ Shape.nil.IsPair := by
  intro ⟨a, b, h⟩
  cases h

/-- The first field of the `pair` variant of `Shape`. -/
def pairFst : PLens Shape Bool where
  get
    | .pair a _ => some a
    | _ => none
  put
    | .pair _ b, a' => some (.pair a' b)
    | _, _ => none

/-- The second field of the `pair` variant of `Shape`. -/
def pairSnd : PLens Shape Bool where
  get
    | .pair _ b => some b
    | _ => none
  put
    | .pair a _, b' => some (.pair a b')
    | _, _ => none

/-- A read-only first field of the `pair` variant: the write succeeds but is
ignored. -/
def pairIgnore : PLens Shape Bool where
  get
    | .pair a _ => some a
    | _ => none
  put
    | .pair a b, _ => some (.pair a b)
    | _, _ => none

/-- A **variant-switching** setter: like `pairFst` on the `pair` variant, but
on the tag `nil` the write *succeeds* and conjures a pair. -/
def pairFstSwitch : PLens Shape Bool where
  get
    | .pair a _ => some a
    | _ => none
  put
    | .pair _ b, a' => some (.pair a' b)
    | .nil, a' => some (.pair a' false)
    | .unit, _ => none

/-- First field of `Option (Bool × Bool)`: a sum type with exactly *one*
state outside the record variant. -/
def optFst : PLens (Option (Bool × Bool)) Bool where
  get
    | some p => some p.1
    | none => none
  put
    | some p, a' => some (some (a', p.2))
    | none, _ => none

/-- Second field of `Option (Bool × Bool)`. -/
def optSnd : PLens (Option (Bool × Bool)) Bool where
  get
    | some p => some p.2
    | none => none
  put
    | some p, b' => some (some (p.1, b'))
    | none, _ => none

/-! ## `TotalOn`: positive and negative examples -/

/-- Positive example for `TotalOn`. -/
theorem pairFst_totalOn : TotalOn Shape.IsPair pairFst where
  get_defined := by
    intro s ⟨a, b, hs⟩
    subst hs
    exact ⟨a, rfl⟩
  put_defined := by
    intro s a' ⟨a, b, hs⟩
    subst hs
    exact ⟨.pair a' b, rfl, a', b, rfl⟩

/-- Positive example for `TotalOn`. -/
theorem pairSnd_totalOn : TotalOn Shape.IsPair pairSnd where
  get_defined := by
    intro s ⟨a, b, hs⟩
    subst hs
    exact ⟨b, rfl⟩
  put_defined := by
    intro s b' ⟨a, b, hs⟩
    subst hs
    exact ⟨.pair a b', rfl, a, b', rfl⟩

/-- Negative example for `TotalOn`: `pairFst` is not total on the whole sum
type — the field does not exist on the tag `nil`. -/
theorem pairFst_not_totalOn_univ : ¬ TotalOn (fun _ => True) pairFst := by
  intro h
  obtain ⟨a, ha⟩ := h.get_defined Shape.nil trivial
  have ha' : (none : Option Bool) = some a := ha
  cases ha'

/-! ## `PutGetOn`: positive and negative examples -/

/-- Positive example for `PutGetOn`. -/
theorem pairFst_putGetOn : PutGetOn Shape.IsPair pairFst := by
  intro s a' s' ⟨a, b, hs⟩ hput
  subst hs
  cases hput
  rfl

/-- Positive example for `PutGetOn`. -/
theorem pairSnd_putGetOn : PutGetOn Shape.IsPair pairSnd := by
  intro s b' s' ⟨a, b, hs⟩ hput
  subst hs
  cases hput
  rfl

/-- Negative example for `PutGetOn`: the read-only field. -/
theorem pairIgnore_not_putGetOn : ¬ PutGetOn Shape.IsPair pairIgnore := by
  intro h
  have h' := h (.pair false false) true (.pair false false) ⟨false, false, rfl⟩ rfl
  exact absurd h' (by decide)

/-! ## `PutIndepOn`: positive and negative examples -/

/-- Positive example for `PutIndepOn`. -/
theorem pairFst_pairSnd_putIndepOn : PutIndepOn Shape.IsPair pairFst pairSnd := by
  intro s a' s' ⟨a, b, hs⟩ hput
  subst hs
  cases hput
  rfl

/-- Positive example for `PutIndepOn` (the other direction). -/
theorem pairSnd_pairFst_putIndepOn : PutIndepOn Shape.IsPair pairSnd pairFst := by
  intro s b' s' ⟨a, b, hs⟩ hput
  subst hs
  cases hput
  rfl

/-- Negative example for `PutIndepOn`: aliasing — a partial lens is not
independent of itself. -/
theorem pairFst_pairFst_not_putIndepOn : ¬ PutIndepOn Shape.IsPair pairFst pairFst := by
  intro h
  have h' := h (.pair false false) true (.pair true false) ⟨false, false, rfl⟩ rfl
  exact absurd h' (by decide)

/-! ## `JointExtOn`: positive and negative examples -/

/-- Positive example for `JointExtOn`. -/
theorem pairFst_pairSnd_jointExtOn : JointExtOn Shape.IsPair pairFst pairSnd := by
  intro s t ⟨a, b, hs⟩ ⟨a', b', ht⟩ h₁ h₂
  subst hs
  subst ht
  have ha : a = a' := Option.some.inj h₁
  have hb : b = b' := Option.some.inj h₂
  rw [ha, hb]

/-- Negative example for `JointExtOn`: two aliasing copies of the first field
do not see the second field. -/
theorem pairFst_pairFst_not_jointExtOn : ¬ JointExtOn Shape.IsPair pairFst pairFst := by
  intro h
  have h' := h (.pair false false) (.pair false true) ⟨false, false, rfl⟩ ⟨false, true, rfl⟩
    rfl rfl
  exact absurd h' (by decide)

/-! ## `IsProductDecompositionOn`: positive and negative examples -/

/-- Positive example for `IsProductDecompositionOn`, and the **non-vacuity
witness for F5**: the two fields of the `pair` variant of `Shape`. -/
theorem pairFst_pairSnd_isProductDecompositionOn :
    IsProductDecompositionOn Shape.IsPair pairFst pairSnd where
  get_defined := by
    intro s ⟨a, b, hs⟩
    subst hs
    exact ⟨a, b, rfl, rfl⟩
  injective := pairFst_pairSnd_jointExtOn
  surjective := fun a b => ⟨.pair a b, ⟨a, b, rfl⟩, rfl, rfl⟩
  put_fst := by
    intro s a' ⟨a, b, hs⟩
    subst hs
    exact ⟨.pair a' b, rfl, ⟨a', b, rfl⟩, rfl, rfl⟩
  put_snd := by
    intro s b' ⟨a, b, hs⟩
    subst hs
    exact ⟨.pair a b', rfl, ⟨a, b', rfl⟩, rfl, rfl⟩

/-- **Non-vacuity of F5.**  The two fields of the `pair` variant of `Shape`
satisfy every hypothesis of F5. -/
theorem pairFst_pairSnd_satisfy_f5_hypotheses :
    TotalOn Shape.IsPair pairFst ∧ TotalOn Shape.IsPair pairSnd ∧
    PutGetOn Shape.IsPair pairFst ∧ PutGetOn Shape.IsPair pairSnd ∧
    PutIndepOn Shape.IsPair pairFst pairSnd ∧ PutIndepOn Shape.IsPair pairSnd pairFst ∧
    JointExtOn Shape.IsPair pairFst pairSnd ∧ (Nonempty (Bool × Bool) → ∃ s, Shape.IsPair s) :=
  ⟨pairFst_totalOn, pairSnd_totalOn, pairFst_putGetOn, pairSnd_putGetOn,
    pairFst_pairSnd_putIndepOn, pairSnd_pairFst_putIndepOn, pairFst_pairSnd_jointExtOn,
    fun _ => ⟨Shape.pair false false, false, false, rfl⟩⟩

/-- Negative example for `IsProductDecompositionOn`: two aliasing copies of
the first field. -/
theorem pairFst_pairFst_not_isProductDecompositionOn :
    ¬ IsProductDecompositionOn Shape.IsPair pairFst pairFst :=
  fun h => pairFst_pairFst_not_jointExtOn h.injective

/-! ## F5 — main statements -/

/--
**F5 (variant-scoped pair decomposition).**  Let `V` be a variant.  If both
partial lenses are total on `V` (their `get` and `put` succeed there and `put`
stays in `V`), each satisfies `PutGet` on `V`, they are cross-independent on
`V` in both directions, they are jointly extensional *on `V`*, and `V` is
inhabited whenever `A × B` is, then on `V` the two lenses present the states
as the product `A × B`, with `l₁.put` and `l₂.put` acting as first- and
second-coordinate update.

Every hypothesis and the conclusion are relativised to `V`; nothing is
assumed or concluded about states outside `V`.  A caller holding
`hV : ∃ s, V s` passes `fun _ => hV`.
-/
theorem isProductDecompositionOn_of_totalOn_putGetOn_putIndepOn_jointExtOn_imp_nonempty
    {V : S → Prop} {l₁ : PLens S A} {l₂ : PLens S B}
    (ht₁ : TotalOn V l₁) (ht₂ : TotalOn V l₂)
    (h₁ : PutGetOn V l₁) (h₂ : PutGetOn V l₂)
    (h₁₂ : PutIndepOn V l₁ l₂) (h₂₁ : PutIndepOn V l₂ l₁)
    (hext : JointExtOn V l₁ l₂) (hV : Nonempty (A × B) → ∃ s, V s) :
    IsProductDecompositionOn V l₁ l₂ := by
  refine ⟨fun s hs => ?_, hext, fun a b => ?_, fun s a hs => ?_, fun s b hs => ?_⟩
  · obtain ⟨a, ha⟩ := ht₁.get_defined s hs
    obtain ⟨b, hb⟩ := ht₂.get_defined s hs
    exact ⟨a, b, ha, hb⟩
  · -- write `a` then `b` into a state of `V`
    obtain ⟨s₀, hv₀⟩ := hV ⟨(a, b)⟩
    obtain ⟨s₁, hp₁, hv₁⟩ := ht₁.put_defined s₀ a hv₀
    obtain ⟨s₂, hp₂, hv₂⟩ := ht₂.put_defined s₁ b hv₁
    exact ⟨s₂, hv₂, (h₂₁ s₁ b s₂ hv₁ hp₂).trans (h₁ s₀ a s₁ hv₀ hp₁), h₂ s₁ b s₂ hv₁ hp₂⟩
  · obtain ⟨s', hp, hv'⟩ := ht₁.put_defined s a hs
    exact ⟨s', hp, hv', h₁ s a s' hs hp, h₁₂ s a s' hs hp⟩
  · obtain ⟨s', hp, hv'⟩ := ht₂.put_defined s b hs
    exact ⟨s', hp, hv', h₂₁ s b s' hs hp, h₂ s b s' hs hp⟩

/--
**F5, exact form.**  The variant-scoped conclusion holds *if and only if* both
lenses are total on `V`, satisfy `PutGet` on `V`, are cross-independent on `V`
in both directions, are jointly extensional on `V`, and `V` is inhabited
whenever `A × B` is.
-/
theorem isProductDecompositionOn_iff_totalOn_putGetOn_putIndepOn_jointExtOn_imp_nonempty
    {V : S → Prop} {l₁ : PLens S A} {l₂ : PLens S B} :
    IsProductDecompositionOn V l₁ l₂ ↔
      TotalOn V l₁ ∧ TotalOn V l₂ ∧ PutGetOn V l₁ ∧ PutGetOn V l₂ ∧
        PutIndepOn V l₁ l₂ ∧ PutIndepOn V l₂ l₁ ∧ JointExtOn V l₁ l₂ ∧
        (Nonempty (A × B) → ∃ s, V s) := by
  constructor
  · intro h
    refine ⟨⟨fun s hv => let ⟨a, _, ha, _⟩ := h.get_defined s hv; ⟨a, ha⟩,
             fun s a hv => let ⟨s', hp, hv', _⟩ := h.put_fst s a hv; ⟨s', hp, hv'⟩⟩,
            ⟨fun s hv => let ⟨_, b, _, hb⟩ := h.get_defined s hv; ⟨b, hb⟩,
             fun s b hv => let ⟨s', hp, hv', _⟩ := h.put_snd s b hv; ⟨s', hp, hv'⟩⟩,
            fun s a s' hv hp => ?_, fun s b s' hv hp => ?_,
            fun s a s' hv hp => ?_, fun s b s' hv hp => ?_,
            h.injective,
            fun ⟨⟨a, b⟩⟩ => let ⟨s, hv, _, _⟩ := h.surjective a b; ⟨s, hv⟩⟩
    · obtain ⟨s'', hp', _, hg₁, _⟩ := h.put_fst s a hv
      cases hp.symm.trans hp'
      exact hg₁
    · obtain ⟨s'', hp', _, _, hg₂⟩ := h.put_snd s b hv
      cases hp.symm.trans hp'
      exact hg₂
    · obtain ⟨s'', hp', _, _, hg₂⟩ := h.put_fst s a hv
      cases hp.symm.trans hp'
      exact hg₂
    · obtain ⟨s'', hp', _, hg₁, _⟩ := h.put_snd s b hv
      cases hp.symm.trans hp'
      exact hg₁
  · rintro ⟨ht₁, ht₂, h₁, h₂, h₁₂, h₂₁, hext, hV⟩
    exact isProductDecompositionOn_of_totalOn_putGetOn_putIndepOn_jointExtOn_imp_nonempty
      ht₁ ht₂ h₁ h₂ h₁₂ h₂₁ hext hV

/-- On an empty variant with an empty first view the variant-scoped conclusion
holds although `V` is uninhabited: the nonemptiness condition of F5 must be
conditional on `Nonempty (A × B)`. -/
theorem emptyVariant_isProductDecompositionOn :
    IsProductDecompositionOn (fun _ : Shape => False) (absent : PLens Shape Empty) pairSnd ∧
    ¬ (∃ s : Shape, (fun _ => False) s) ∧
    (Nonempty (Empty × Bool) → ∃ s : Shape, (fun _ => False) s) :=
  ⟨{ get_defined := fun _ h => h.elim
     injective := fun _ _ h => h.elim
     surjective := fun a _ => a.elim
     put_fst := fun _ _ h => h.elim
     put_snd := fun _ _ h => h.elim },
   fun ⟨_, h⟩ => h, fun ⟨p⟩ => p.1.elim⟩

/-! ## Unscoped joint extensionality is the wrong law (proved) -/

/-- **Unscoped joint extensionality collapses the complement of the variant.**
If `JointExt l₁ l₂` holds, any two states in which *both* fields are absent
are equal. -/
theorem eq_of_jointExt_of_get_eq_none {l₁ : PLens S A} {l₂ : PLens S B}
    (h : JointExt l₁ l₂) {s t : S}
    (hs₁ : l₁.get s = none) (hs₂ : l₂.get s = none)
    (ht₁ : l₁.get t = none) (ht₂ : l₂.get t = none) :
    s = t :=
  h s t (hs₁.trans ht₁.symm) (hs₂.trans ht₂.symm)

/-- **Unscoped joint extensionality is unsatisfiable** as soon as two distinct
states lack both fields.  This is an impossibility result; its escape hatches
are `not_jointExt_of_two_states_without_fields_tight` (one per hypothesis),
`shape3_jointExt` (a sum type with only one state lacking both fields) and
`jointExtOn` scoped to the variant
(`scoped_decomposition_holds_but_unscoped_jointExt_fails`). -/
theorem not_jointExt_of_two_states_without_fields {l₁ : PLens S A} {l₂ : PLens S B}
    {s t : S} (hne : s ≠ t)
    (hs₁ : l₁.get s = none) (hs₂ : l₂.get s = none)
    (ht₁ : l₁.get t = none) (ht₂ : l₂.get t = none) :
    ¬ JointExt l₁ l₂ :=
  fun h => hne (eq_of_jointExt_of_get_eq_none h hs₁ hs₂ ht₁ ht₂)

/-- Negative example for `PLens.JointExt`, and the **F5 counterexample**: for
the intended model `Shape`, unscoped joint extensionality would equate the two
distinct nullary tags `nil` and `unit`. -/
theorem jointExt_pairFst_pairSnd_equates_tags :
    JointExt pairFst pairSnd → Shape.nil = Shape.unit :=
  fun h => eq_of_jointExt_of_get_eq_none h rfl rfl rfl rfl

/-- Negative example for `PLens.JointExt`: the intended model `Shape` violates
unscoped joint extensionality. -/
theorem pairFst_pairSnd_not_jointExt : ¬ JointExt pairFst pairSnd :=
  not_jointExt_of_two_states_without_fields (s := Shape.nil) (t := Shape.unit) (by decide)
    rfl rfl rfl rfl

/-- **F5 counterexample, bundled.**  The intended model satisfies the
variant-scoped conclusion (and hence every variant-scoped law) but violates
unscoped joint extensionality. -/
theorem scoped_decomposition_holds_but_unscoped_jointExt_fails :
    IsProductDecompositionOn Shape.IsPair pairFst pairSnd ∧ ¬ JointExt pairFst pairSnd :=
  ⟨pairFst_pairSnd_isProductDecompositionOn, pairFst_pairSnd_not_jointExt⟩

/-- Positive example for `PLens.JointExt`: on `Option (Bool × Bool)`, which
has only *one* state outside the record variant, unscoped joint extensionality
happens to hold.  The law is therefore not refuted by option-like test types;
it breaks only when the sum type has two or more field-less states. -/
theorem optFst_optSnd_jointExt : JointExt optFst optSnd := by
  intro s t h₁ h₂
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some q => exact absurd h₁ (by simp [optFst])
  | some p =>
    cases t with
    | none => exact absurd h₁ (by simp [optFst])
    | some q =>
      obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := q
      have ha : a = a' := Option.some.inj h₁
      have hb : b = b' := Option.some.inj h₂
      rw [ha, hb]

/-! ## Total lenses as partial lenses: F5 specialises to F1 (proved)

A total lens is a partial lens that never fails.  With the variant taken to be
the whole state type, every variant-scoped notion of this file reduces to the
corresponding total notion.  This checks that the scoped definitions are a
faithful generalisation, and it transports every F4 tightness witness to F5.
-/

/-- Regard a total lens as a partial lens that never fails. -/
def _root_.Toy.Lens.toPLens (l : Lens S A) : PLens S A where
  get s := some (l.get s)
  put s a := some (l.put s a)

/-- A total lens is total on the whole state type. -/
theorem totalOn_toPLens (l : Lens S A) : TotalOn (fun _ => True) l.toPLens :=
  ⟨fun s _ => ⟨l.get s, rfl⟩, fun s a _ => ⟨l.put s a, rfl, trivial⟩⟩

/-- Scoped `PutGet` on the whole type is `PutGet`. -/
theorem putGetOn_toPLens_iff (l : Lens S A) :
    PutGetOn (fun _ => True) l.toPLens ↔ l.PutGet := by
  constructor
  · intro h s a
    exact Option.some.inj (h s a (l.put s a) trivial rfl)
  · intro h s a s' _ hput
    have hs' : l.put s a = s' := Option.some.inj hput
    subst hs'
    exact congrArg some (h s a)

/-- Scoped cross-independence on the whole type is `PutIndep`. -/
theorem putIndepOn_toPLens_iff (l₁ : Lens S A) (l₂ : Lens S B) :
    PutIndepOn (fun _ => True) l₁.toPLens l₂.toPLens ↔ PutIndep l₁ l₂ := by
  constructor
  · intro h s a
    exact Option.some.inj (h s a (l₁.put s a) trivial rfl)
  · intro h s a s' _ hput
    have hs' : l₁.put s a = s' := Option.some.inj hput
    subst hs'
    exact congrArg some (h s a)

/-- Scoped joint extensionality on the whole type is `Lens.JointExt`. -/
theorem jointExtOn_toPLens_iff (l₁ : Lens S A) (l₂ : Lens S B) :
    JointExtOn (fun _ => True) l₁.toPLens l₂.toPLens ↔ Lens.JointExt l₁ l₂ := by
  constructor
  · intro h s t h₁ h₂
    exact h s t trivial trivial (congrArg some h₁) (congrArg some h₂)
  · intro h s t _ _ h₁ h₂
    exact h s t (Option.some.inj h₁) (Option.some.inj h₂)

/-- For total lenses, *unscoped* partial joint extensionality is also just
`Lens.JointExt`: the scoped and unscoped laws differ only where a field can be
absent. -/
theorem jointExt_toPLens_iff (l₁ : Lens S A) (l₂ : Lens S B) :
    JointExt l₁.toPLens l₂.toPLens ↔ Lens.JointExt l₁ l₂ := by
  constructor
  · intro h s t h₁ h₂
    exact h s t (congrArg some h₁) (congrArg some h₂)
  · intro h s t h₁ h₂
    exact h s t (Option.some.inj h₁) (Option.some.inj h₂)

/-- The scoped conclusion on the whole type is the conclusion of F1. -/
theorem isProductDecompositionOn_toPLens_iff (l₁ : Lens S A) (l₂ : Lens S B) :
    IsProductDecompositionOn (fun _ => True) l₁.toPLens l₂.toPLens ↔
      IsProductDecomposition l₁ l₂ := by
  constructor
  · intro h
    refine ⟨?_, ?_, ⟨fun _ => rfl, ?_⟩, ⟨fun _ => rfl, ?_⟩⟩
    · intro s t hst
      exact h.injective s t trivial trivial
        (congrArg (fun p : A × B => some p.1) hst) (congrArg (fun p : A × B => some p.2) hst)
    · intro p
      obtain ⟨s, _, hs₁, hs₂⟩ := h.surjective p.1 p.2
      have e₁ : l₁.get s = p.1 := Option.some.inj hs₁
      have e₂ : l₂.get s = p.2 := Option.some.inj hs₂
      refine ⟨s, ?_⟩
      show (l₁.get s, l₂.get s) = p
      rw [e₁, e₂]
    · intro s a
      obtain ⟨s', hput, _, hg₁, hg₂⟩ := h.put_fst s a trivial
      have hs' : l₁.put s a = s' := Option.some.inj hput
      subst hs'
      have e₁ : l₁.get (l₁.put s a) = a := Option.some.inj hg₁
      have e₂ : l₂.get (l₁.put s a) = l₂.get s := Option.some.inj hg₂
      show (l₁.get (l₁.put s a), l₂.get (l₁.put s a)) = (a, l₂.get s)
      rw [e₁, e₂]
    · intro s b
      obtain ⟨s', hput, _, hg₁, hg₂⟩ := h.put_snd s b trivial
      have hs' : l₂.put s b = s' := Option.some.inj hput
      subst hs'
      have e₁ : l₁.get (l₂.put s b) = l₁.get s := Option.some.inj hg₁
      have e₂ : l₂.get (l₂.put s b) = b := Option.some.inj hg₂
      show (l₁.get (l₂.put s b), l₂.get (l₂.put s b)) = (l₁.get s, b)
      rw [e₁, e₂]
  · intro h
    refine ⟨fun s _ => ⟨l₁.get s, l₂.get s, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro s t _ _ h₁ h₂
      apply h.injective
      have e₁ : l₁.get s = l₁.get t := Option.some.inj h₁
      have e₂ : l₂.get s = l₂.get t := Option.some.inj h₂
      show (l₁.get s, l₂.get s) = (l₁.get t, l₂.get t)
      rw [e₁, e₂]
    · intro a b
      obtain ⟨s, hs⟩ := h.surjective (a, b)
      exact ⟨s, trivial, congrArg (fun p : A × B => some p.1) hs,
        congrArg (fun p : A × B => some p.2) hs⟩
    · intro s a _
      have hp := h.intertwines_fst.put_eq s a
      exact ⟨l₁.put s a, rfl, trivial, congrArg (fun p : A × B => some p.1) hp,
        congrArg (fun p : A × B => some p.2) hp⟩
    · intro s b _
      have hp := h.intertwines_snd.put_eq s b
      exact ⟨l₂.put s b, rfl, trivial, congrArg (fun p : A × B => some p.1) hp,
        congrArg (fun p : A × B => some p.2) hp⟩

/-- **F5, `TotalOn V l₁`.**  On the one-point state type, the never-present
field `absent` next to the trivial total lens: every hypothesis of F5 holds
except `TotalOn V l₁`, and the conclusion fails.  (Everywhere-undefined puts
are the reason totality is needed, as in Foster et al. 2007, Section 3,
footnote 3.) -/
theorem absent_tight_totalOn :
    ¬ TotalOn (fun _ : Unit => True) (absent : PLens Unit Bool) ∧
    TotalOn (fun _ : Unit => True) (unitLens : Lens Unit Unit).toPLens ∧
    PutGetOn (fun _ : Unit => True) (absent : PLens Unit Bool) ∧
    PutGetOn (fun _ : Unit => True) (unitLens : Lens Unit Unit).toPLens ∧
    PutIndepOn (fun _ : Unit => True) (absent : PLens Unit Bool)
      (unitLens : Lens Unit Unit).toPLens ∧
    PutIndepOn (fun _ : Unit => True) (unitLens : Lens Unit Unit).toPLens
      (absent : PLens Unit Bool) ∧
    JointExtOn (fun _ : Unit => True) (absent : PLens Unit Bool)
      (unitLens : Lens Unit Unit).toPLens ∧
    (Nonempty (Bool × Unit) → ∃ _s : Unit, True) ∧
    ¬ IsProductDecompositionOn (fun _ : Unit => True) (absent : PLens Unit Bool)
      (unitLens : Lens Unit Unit).toPLens := by
  refine ⟨?_, totalOn_toPLens _, ?_, (putGetOn_toPLens_iff _).mpr (fun _ _ => rfl), ?_, ?_, ?_,
    fun _ => ⟨(), trivial⟩, ?_⟩
  · intro h
    obtain ⟨a, ha⟩ := h.get_defined () trivial
    have ha' : (none : Option Bool) = some a := ha
    cases ha'
  · intro s a s' _ h
    have h' : (none : Option Unit) = some s' := h
    cases h'
  · intro s a s' _ h
    have h' : (none : Option Unit) = some s' := h
    cases h'
  · intro s a s' _ _
    rfl
  · intro s t _ _ _ _
    rfl
  · intro h
    obtain ⟨a, b, ha, _⟩ := h.get_defined () trivial
    have ha' : (none : Option Bool) = some a := ha
    cases ha'

/-- **F5, `TotalOn V l₂`.**  The mirror image of `absent_tight_totalOn`. -/
theorem absent_tight_totalOn_right :
    TotalOn (fun _ : Unit => True) (unitLens : Lens Unit Unit).toPLens ∧
    ¬ TotalOn (fun _ : Unit => True) (absent : PLens Unit Bool) ∧
    PutGetOn (fun _ : Unit => True) (unitLens : Lens Unit Unit).toPLens ∧
    PutGetOn (fun _ : Unit => True) (absent : PLens Unit Bool) ∧
    PutIndepOn (fun _ : Unit => True) (unitLens : Lens Unit Unit).toPLens
      (absent : PLens Unit Bool) ∧
    PutIndepOn (fun _ : Unit => True) (absent : PLens Unit Bool)
      (unitLens : Lens Unit Unit).toPLens ∧
    JointExtOn (fun _ : Unit => True) (unitLens : Lens Unit Unit).toPLens
      (absent : PLens Unit Bool) ∧
    (Nonempty (Unit × Bool) → ∃ _s : Unit, True) ∧
    ¬ IsProductDecompositionOn (fun _ : Unit => True)
        (unitLens : Lens Unit Unit).toPLens (absent : PLens Unit Bool) := by
  obtain ⟨hnt, ht, hpgA, hpgU, hindAU, hindUA, _, _, _⟩ := absent_tight_totalOn
  refine ⟨ht, hnt, hpgU, hpgA, hindUA, hindAU, fun _ _ _ _ _ _ => rfl, fun _ => ⟨(), trivial⟩, ?_⟩
  intro h
  obtain ⟨_, b, _, hb⟩ := h.get_defined () trivial
  cases hb

/-- Transport of a total-lens witness of F1 to F5 (with the variant taken to be
the whole state type). -/
theorem f5_hyps_toPLens {S : Type u} {A : Type v} {B : Type w} (l₁ : Lens S A) (l₂ : Lens S B) :
    TotalOn (fun _ => True) l₁.toPLens ∧ TotalOn (fun _ => True) l₂.toPLens ∧
    (PutGetOn (fun _ => True) l₁.toPLens ↔ l₁.PutGet) ∧
    (PutGetOn (fun _ => True) l₂.toPLens ↔ l₂.PutGet) ∧
    (PutIndepOn (fun _ => True) l₁.toPLens l₂.toPLens ↔ Lens.PutIndep l₁ l₂) ∧
    (PutIndepOn (fun _ => True) l₂.toPLens l₁.toPLens ↔ Lens.PutIndep l₂ l₁) ∧
    (JointExtOn (fun _ => True) l₁.toPLens l₂.toPLens ↔ Lens.JointExt l₁ l₂) ∧
    ((Nonempty (A × B) → ∃ s : S, (fun _ => True) s) ↔ (Nonempty (A × B) → Nonempty S)) ∧
    (IsProductDecompositionOn (fun _ => True) l₁.toPLens l₂.toPLens ↔
      IsProductDecomposition l₁ l₂) :=
  ⟨totalOn_toPLens l₁, totalOn_toPLens l₂, putGetOn_toPLens_iff l₁, putGetOn_toPLens_iff l₂,
   putIndepOn_toPLens_iff l₁ l₂, putIndepOn_toPLens_iff l₂ l₁, jointExtOn_toPLens_iff l₁ l₂,
   ⟨fun h hn => let ⟨s, _⟩ := h hn; ⟨s⟩, fun h hn => let ⟨s⟩ := h hn; ⟨s, trivial⟩⟩,
   isProductDecompositionOn_toPLens_iff l₁ l₂⟩

/-- **F5, `PutGetOn V l₁`.**  The read-only first field next to `snd`,
regarded as partial lenses on the whole state type. -/
theorem f5_tight_putGetOn_left :
    TotalOn (fun _ => True) ignorePut.toPLens ∧ TotalOn (fun _ => True) sndB.toPLens ∧
    ¬ PutGetOn (fun _ => True) ignorePut.toPLens ∧ PutGetOn (fun _ => True) sndB.toPLens ∧
    PutIndepOn (fun _ => True) ignorePut.toPLens sndB.toPLens ∧
    PutIndepOn (fun _ => True) sndB.toPLens ignorePut.toPLens ∧
    JointExtOn (fun _ => True) ignorePut.toPLens sndB.toPLens ∧
    (Nonempty (Bool × Bool) → ∃ _s : Bool × Bool, True) ∧
    ¬ IsProductDecompositionOn (fun _ => True) ignorePut.toPLens sndB.toPLens := by
  obtain ⟨t1, t2, i1, i2, i3, i4, i5, i6, i7⟩ := f5_hyps_toPLens ignorePut sndB
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := ignorePut_tight_putGet_left
  exact ⟨t1, t2, fun h => p1 (i1.mp h), i2.mpr p2, i3.mpr p3, i4.mpr p4, i5.mpr p5, i6.mpr p6,
    fun h => p7 (i7.mp h)⟩

/-- **F5, `PutGetOn V l₂`.** -/
theorem f5_tight_putGetOn_right :
    TotalOn (fun _ => True) fstB.toPLens ∧ TotalOn (fun _ => True) ignorePutSnd.toPLens ∧
    PutGetOn (fun _ => True) fstB.toPLens ∧ ¬ PutGetOn (fun _ => True) ignorePutSnd.toPLens ∧
    PutIndepOn (fun _ => True) fstB.toPLens ignorePutSnd.toPLens ∧
    PutIndepOn (fun _ => True) ignorePutSnd.toPLens fstB.toPLens ∧
    JointExtOn (fun _ => True) fstB.toPLens ignorePutSnd.toPLens ∧
    (Nonempty (Bool × Bool) → ∃ _s : Bool × Bool, True) ∧
    ¬ IsProductDecompositionOn (fun _ => True) fstB.toPLens ignorePutSnd.toPLens := by
  obtain ⟨t1, t2, i1, i2, i3, i4, i5, i6, i7⟩ := f5_hyps_toPLens fstB ignorePutSnd
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := ignorePutSnd_tight_putGet_right
  exact ⟨t1, t2, i1.mpr p1, fun h => p2 (i2.mp h), i3.mpr p3, i4.mpr p4, i5.mpr p5, i6.mpr p6,
    fun h => p7 (i7.mp h)⟩

/-- **F5, `PutIndepOn V l₁ l₂`.**  The state-twisting setter next to `snd`. -/
theorem f5_tight_putIndepOn_left :
    TotalOn (fun _ => True) twist.toPLens ∧ TotalOn (fun _ => True) sndB.toPLens ∧
    PutGetOn (fun _ => True) twist.toPLens ∧ PutGetOn (fun _ => True) sndB.toPLens ∧
    ¬ PutIndepOn (fun _ => True) twist.toPLens sndB.toPLens ∧
    PutIndepOn (fun _ => True) sndB.toPLens twist.toPLens ∧
    JointExtOn (fun _ => True) twist.toPLens sndB.toPLens ∧
    (Nonempty (Bool × Bool) → ∃ _s : Bool × Bool, True) ∧
    ¬ IsProductDecompositionOn (fun _ => True) twist.toPLens sndB.toPLens := by
  obtain ⟨t1, t2, i1, i2, i3, i4, i5, i6, i7⟩ := f5_hyps_toPLens twist sndB
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := twist_tight_putIndep_left
  exact ⟨t1, t2, i1.mpr p1, i2.mpr p2, fun h => p3 (i3.mp h), i4.mpr p4, i5.mpr p5, i6.mpr p6,
    fun h => p7 (i7.mp h)⟩

/-- **F5, `PutIndepOn V l₂ l₁`.** -/
theorem f5_tight_putIndepOn_right :
    TotalOn (fun _ => True) sndB.toPLens ∧ TotalOn (fun _ => True) twist.toPLens ∧
    PutGetOn (fun _ => True) sndB.toPLens ∧ PutGetOn (fun _ => True) twist.toPLens ∧
    PutIndepOn (fun _ => True) sndB.toPLens twist.toPLens ∧
    ¬ PutIndepOn (fun _ => True) twist.toPLens sndB.toPLens ∧
    JointExtOn (fun _ => True) sndB.toPLens twist.toPLens ∧
    (Nonempty (Bool × Bool) → ∃ _s : Bool × Bool, True) ∧
    ¬ IsProductDecompositionOn (fun _ => True) sndB.toPLens twist.toPLens := by
  obtain ⟨t1, t2, i1, i2, i3, i4, i5, i6, i7⟩ := f5_hyps_toPLens sndB twist
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := twist_tight_putIndep_right
  exact ⟨t1, t2, i1.mpr p1, i2.mpr p2, i3.mpr p3, fun h => p4 (i4.mp h), i5.mpr p5, i6.mpr p6,
    fun h => p7 (i7.mp h)⟩

/-- **F5, `JointExtOn V l₁ l₂`.**  The two visible fields of a ghost record. -/
theorem f5_tight_jointExtOn :
    TotalOn (fun _ => True) ghostFstB.toPLens ∧ TotalOn (fun _ => True) ghostSndB.toPLens ∧
    PutGetOn (fun _ => True) ghostFstB.toPLens ∧ PutGetOn (fun _ => True) ghostSndB.toPLens ∧
    PutIndepOn (fun _ => True) ghostFstB.toPLens ghostSndB.toPLens ∧
    PutIndepOn (fun _ => True) ghostSndB.toPLens ghostFstB.toPLens ∧
    ¬ JointExtOn (fun _ => True) ghostFstB.toPLens ghostSndB.toPLens ∧
    (Nonempty (Bool × Bool) → ∃ _s : Bool × Bool × Bool, True) ∧
    ¬ IsProductDecompositionOn (fun _ => True) ghostFstB.toPLens ghostSndB.toPLens := by
  obtain ⟨t1, t2, i1, i2, i3, i4, i5, i6, i7⟩ := f5_hyps_toPLens ghostFstB ghostSndB
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := ghost_tight_jointExt
  exact ⟨t1, t2, i1.mpr p1, i2.mpr p2, i3.mpr p3, i4.mpr p4, fun h => p5 (i5.mp h), i6.mpr p6,
    fun h => p7 (i7.mp h)⟩

/-- **F5, the nonemptiness condition.**  The empty state type with one-point
views. -/
theorem f5_tight_nonempty :
    TotalOn (fun _ => True) emptyLens.toPLens ∧ TotalOn (fun _ => True) emptyLens.toPLens ∧
    PutGetOn (fun _ => True) emptyLens.toPLens ∧ PutGetOn (fun _ => True) emptyLens.toPLens ∧
    PutIndepOn (fun _ => True) emptyLens.toPLens emptyLens.toPLens ∧
    PutIndepOn (fun _ => True) emptyLens.toPLens emptyLens.toPLens ∧
    JointExtOn (fun _ => True) emptyLens.toPLens emptyLens.toPLens ∧
    ¬ (Nonempty (Unit × Unit) → ∃ _s : Empty, True) ∧
    ¬ IsProductDecompositionOn (fun _ => True) emptyLens.toPLens emptyLens.toPLens := by
  obtain ⟨t1, t2, i1, i2, i3, i4, i5, i6, i7⟩ := f5_hyps_toPLens emptyLens emptyLens
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := empty_tight_nonempty
  exact ⟨t1, t2, i1.mpr p1, i2.mpr p2, i3.mpr p3, i4.mpr p4, i5.mpr p5, fun h => p6 (i6.mp h),
    fun h => p7 (i7.mp h)⟩

/-- A field of `Option Bool` that is readable only on `some`, but writable
everywhere: `put _ a = some (some a)`. -/
def optWriteAll : PLens (Option Bool) Bool where
  get s := s
  put _ a := some (some a)

/-- A field on `Unit` that is readable but never writable. -/
def readOnlyUnit : PLens Unit Bool where
  get _ := some false
  put _ _ := none

/-- A field on `Bool` that is readable everywhere but whose put always leaves
the variant `{false}`. -/
def leaveVariant : PLens Bool Unit where
  get _ := some ()
  put _ _ := some true

/-- **The three components of `TotalOn` are independently needed for F5.**
Each instance violates exactly one component of `TotalOn V l₁` (the read
succeeds; the write succeeds; the write stays in `V`), satisfies every other
hypothesis of F5, and the conclusion fails. -/
theorem totalOn_components_tight :
    -- `get` fails on the variant
    (¬ (∀ s, (fun _ : Option Bool => True) s → ∃ a, optWriteAll.get s = some a) ∧
      (∀ s a, (fun _ : Option Bool => True) s →
        ∃ s', optWriteAll.put s a = some s' ∧ (fun _ => True) s') ∧
      TotalOn (fun _ => True) (unitLens : Lens (Option Bool) Unit).toPLens ∧
      PutGetOn (fun _ => True) optWriteAll ∧
      PutGetOn (fun _ => True) (unitLens : Lens (Option Bool) Unit).toPLens ∧
      PutIndepOn (fun _ => True) optWriteAll (unitLens : Lens (Option Bool) Unit).toPLens ∧
      PutIndepOn (fun _ => True) (unitLens : Lens (Option Bool) Unit).toPLens optWriteAll ∧
      JointExtOn (fun _ => True) optWriteAll (unitLens : Lens (Option Bool) Unit).toPLens ∧
      (Nonempty (Bool × Unit) → ∃ _s : Option Bool, True) ∧
      ¬ IsProductDecompositionOn (fun _ => True) optWriteAll
          (unitLens : Lens (Option Bool) Unit).toPLens) ∧
    -- `put` fails on the variant
    ((∀ s, (fun _ : Unit => True) s → ∃ a, readOnlyUnit.get s = some a) ∧
      (∀ s a, readOnlyUnit.put s a = none) ∧
      TotalOn (fun _ => True) (unitLens : Lens Unit Unit).toPLens ∧
      PutGetOn (fun _ => True) readOnlyUnit ∧
      PutGetOn (fun _ => True) (unitLens : Lens Unit Unit).toPLens ∧
      PutIndepOn (fun _ => True) readOnlyUnit (unitLens : Lens Unit Unit).toPLens ∧
      PutIndepOn (fun _ => True) (unitLens : Lens Unit Unit).toPLens readOnlyUnit ∧
      JointExtOn (fun _ => True) readOnlyUnit (unitLens : Lens Unit Unit).toPLens ∧
      (Nonempty (Bool × Unit) → ∃ _s : Unit, True) ∧
      ¬ IsProductDecompositionOn (fun _ => True) readOnlyUnit
          (unitLens : Lens Unit Unit).toPLens) ∧
    -- `put` leaves the variant
    ((∀ s, (fun b : Bool => b = false) s → ∃ a, leaveVariant.get s = some a) ∧
      (∀ s a, (fun b : Bool => b = false) s → ∃ s', leaveVariant.put s a = some s') ∧
      ¬ (∀ s a, (fun b : Bool => b = false) s →
          ∃ s', leaveVariant.put s a = some s' ∧ (fun b : Bool => b = false) s') ∧
      TotalOn (fun b : Bool => b = false) (unitLens : Lens Bool Unit).toPLens ∧
      PutGetOn (fun b : Bool => b = false) leaveVariant ∧
      PutGetOn (fun b : Bool => b = false) (unitLens : Lens Bool Unit).toPLens ∧
      PutIndepOn (fun b : Bool => b = false) leaveVariant (unitLens : Lens Bool Unit).toPLens ∧
      PutIndepOn (fun b : Bool => b = false) (unitLens : Lens Bool Unit).toPLens leaveVariant ∧
      JointExtOn (fun b : Bool => b = false) leaveVariant (unitLens : Lens Bool Unit).toPLens ∧
      (Nonempty (Unit × Unit) → ∃ s : Bool, (fun b : Bool => b = false) s) ∧
      ¬ IsProductDecompositionOn (fun b : Bool => b = false) leaveVariant
          (unitLens : Lens Bool Unit).toPLens) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, totalOn_toPLens _, ?_, (putGetOn_toPLens_iff _).mpr (fun _ _ => rfl),
      ?_, ?_, ?_, fun _ => ⟨none, trivial⟩, ?_⟩
    · intro h
      obtain ⟨a, ha⟩ := h none trivial
      cases ha
    · intro s a _
      exact ⟨some a, rfl, trivial⟩
    · intro s a s' _ h
      cases h
      rfl
    · intro s a s' _ _
      rfl
    · intro s a s' _ h
      cases h
      rfl
    · intro s t _ _ h₁ _
      exact h₁
    · intro h
      obtain ⟨a, b, ha, _⟩ := h.get_defined none trivial
      cases ha
  · refine ⟨fun _ _ => ⟨false, rfl⟩, fun _ _ => rfl, totalOn_toPLens _, ?_,
      (putGetOn_toPLens_iff _).mpr (fun _ _ => rfl), ?_, ?_, fun _ _ _ _ _ _ => rfl,
      fun _ => ⟨(), trivial⟩, ?_⟩
    · intro s a s' _ h
      cases h
    · intro s a s' _ h
      cases h
    · intro s a s' _ h
      cases h
      rfl
    · intro h
      obtain ⟨s, _, ha, _⟩ := h.surjective true ()
      cases ha
  · refine ⟨fun _ _ => ⟨(), rfl⟩, fun _ _ _ => ⟨true, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun _ => ⟨false, rfl⟩, ?_⟩
    · intro h
      obtain ⟨s', hs', hv⟩ := h false () rfl
      cases hs'
      cases hv
    · exact ⟨fun s _ => ⟨(), rfl⟩, fun s _ hs => ⟨s, rfl, hs⟩⟩
    · intro s a s' _ h
      cases h
      rfl
    · intro s a s' _ h
      cases h
      rfl
    · intro _ _ _ _ _
      rfl
    · intro s a s' _ h
      cases h
      rfl
    · intro s t hs ht _ _
      rw [hs, ht]
    · intro h
      obtain ⟨s', hput, hv, _⟩ := h.put_fst false () rfl
      cases hput
      cases hv
/-! ## A lawful-but-unintended partial instance (proved) -/

/-- **The variant-scoped laws do not constrain writes outside the variant.**
The variant-switching setter `pairFstSwitch` satisfies the variant-scoped
conclusion of F5 together with `pairSnd`, yet writing through it on the tag
`nil` succeeds and turns the tag into a pair. -/
theorem scoped_laws_admit_variant_switching_put :
    IsProductDecompositionOn Shape.IsPair pairFstSwitch pairSnd ∧
    pairFstSwitch.put Shape.nil true = some (Shape.pair true false) := by
  refine ⟨?_, rfl⟩
  constructor
  · intro s ⟨a, b, hs⟩
    subst hs
    exact ⟨a, b, rfl, rfl⟩
  · intro s t ⟨a, b, hs⟩ ⟨a', b', ht⟩ h₁ h₂
    subst hs
    subst ht
    have ha : a = a' := Option.some.inj h₁
    have hb : b = b' := Option.some.inj h₂
    rw [ha, hb]
  · exact fun a b => ⟨.pair a b, ⟨a, b, rfl⟩, rfl, rfl⟩
  · intro s a' ⟨a, b, hs⟩
    subst hs
    exact ⟨.pair a' b, rfl, ⟨a', b, rfl⟩, rfl, rfl⟩
  · intro s b' ⟨a, b, hs⟩
    subst hs
    exact ⟨.pair a b', rfl, ⟨a, b', rfl⟩, rfl, rfl⟩

/-- An unscoped frame law against `pairSnd` excludes *this particular*
variant-switching setter, because its write on `nil` produces a state that has
the `pairSnd` field.  It does **not** exclude variant switching in general:
see `unscoped_putIndep_admits_tag_switch` and
`unscoped_laws_admit_variant_switch`. -/
theorem pairFstSwitch_violates_unscoped_putIndep :
    ¬ PutIndepOn (fun _ => True) pairFstSwitch pairSnd := by
  intro h
  have h' := h Shape.nil true (Shape.pair true false) trivial rfl
  exact absurd h' (by decide)

/-! ## Unscoped laws still admit variant switching (proved) -/

/-- A setter like `pairFst` on the `pair` variant that turns the tag `nil`
into the tag `unit`. -/
def pairFstTagSwitch : PLens Shape Bool where
  get
    | .pair a _ => some a
    | _ => none
  put
    | .pair _ b, a' => some (.pair a' b)
    | .nil, _ => some .unit
    | .unit, _ => none

/-- **Unscoped `PutIndep` does not exclude switching between two field-less
tags.**  `pairFstTagSwitch` satisfies the variant-scoped conclusion together
with `pairSnd` and the unscoped frame law in both directions, yet its write on
`nil` succeeds and produces `unit`. -/
theorem unscoped_putIndep_admits_tag_switch :
    IsProductDecompositionOn Shape.IsPair pairFstTagSwitch pairSnd ∧
    PutIndepOn (fun _ => True) pairFstTagSwitch pairSnd ∧
    PutIndepOn (fun _ => True) pairSnd pairFstTagSwitch ∧
    pairFstTagSwitch.put Shape.nil true = some Shape.unit := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · refine ⟨?_, ?_, fun a b => ⟨.pair a b, ⟨a, b, rfl⟩, rfl, rfl⟩, ?_, ?_⟩
    · rintro s ⟨a, b, rfl⟩; exact ⟨a, b, rfl, rfl⟩
    · rintro s t ⟨a, b, rfl⟩ ⟨a', b', rfl⟩ h₁ h₂
      cases h₁; cases h₂; rfl
    · rintro s a' ⟨a, b, rfl⟩; exact ⟨.pair a' b, rfl, ⟨a', b, rfl⟩, rfl, rfl⟩
    · rintro s b' ⟨a, b, rfl⟩; exact ⟨.pair a b', rfl, ⟨a, b', rfl⟩, rfl, rfl⟩
  · intro s a' s' _ hput
    cases s <;> cases hput <;> rfl
  · intro s b' s' _ hput
    cases s <;> cases hput <;> rfl

/-- A sum type in which a one-field variant shares the field `b` with a
two-field variant. -/
inductive ShapeShared where
  /-- A variant with only the field `b`. -/
  | onlyB (b : Bool)
  /-- A variant with the fields `a` and `b`. -/
  | pair (a b : Bool)
  deriving DecidableEq

/-- The `pair` variant of `ShapeShared`. -/
def ShapeShared.IsPair (s : ShapeShared) : Prop :=
  ∃ a b, s = ShapeShared.pair a b

/-- The field `a`, whose write on `onlyB b` succeeds and produces `pair a b`. -/
def sharedFstSwitch : PLens ShapeShared Bool where
  get
    | .pair a _ => some a
    | .onlyB _ => none
  put
    | .pair _ b, a' => some (.pair a' b)
    | .onlyB b, a' => some (.pair a' b)

/-- The shared field `b`, present on both variants. -/
def sharedSnd : PLens ShapeShared Bool where
  get
    | .pair _ b => some b
    | .onlyB b => some b
  put
    | .pair a _, b' => some (.pair a b')
    | .onlyB _, b' => some (.onlyB b')

/-- **Unscoped `PutGet`, `GetPut`, `PutPut` and two-way unscoped `PutIndep`
still admit a variant-switching write.**  On `ShapeShared`, writing `a` on
`onlyB b` produces `pair a b`; all these unscoped laws and the variant-scoped
conclusion hold.  Excluding such writes needs a law that ties definedness of
`put` to the variant, such as `∀ s a, ¬ V s → l.put s a = none`. -/
theorem unscoped_laws_admit_variant_switch :
    IsProductDecompositionOn ShapeShared.IsPair sharedFstSwitch sharedSnd ∧
    PutGetOn (fun _ => True) sharedFstSwitch ∧
    PutGetOn (fun _ => True) sharedSnd ∧
    PutIndepOn (fun _ => True) sharedFstSwitch sharedSnd ∧
    PutIndepOn (fun _ => True) sharedSnd sharedFstSwitch ∧
    (∀ s a, sharedFstSwitch.get s = some a → sharedFstSwitch.put s a = some s) ∧
    (∀ s a a' s₁, sharedFstSwitch.put s a = some s₁ →
      sharedFstSwitch.put s₁ a' = sharedFstSwitch.put s a') ∧
    sharedFstSwitch.put (.onlyB false) true = some (.pair true false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · refine ⟨?_, ?_, fun a b => ⟨.pair a b, ⟨a, b, rfl⟩, rfl, rfl⟩, ?_, ?_⟩
    · rintro s ⟨a, b, rfl⟩; exact ⟨a, b, rfl, rfl⟩
    · rintro s t ⟨a, b, rfl⟩ ⟨a', b', rfl⟩ h₁ h₂
      cases h₁; cases h₂; rfl
    · rintro s a' ⟨a, b, rfl⟩; exact ⟨.pair a' b, rfl, ⟨a', b, rfl⟩, rfl, rfl⟩
    · rintro s b' ⟨a, b, rfl⟩; exact ⟨.pair a b', rfl, ⟨a, b', rfl⟩, rfl, rfl⟩
  · intro s a' s' _ hput; cases s <;> cases hput <;> rfl
  · intro s b' s' _ hput; cases s <;> cases hput <;> rfl
  · intro s a' s' _ hput; cases s <;> cases hput <;> rfl
  · intro s b' s' _ hput; cases s <;> cases hput <;> rfl
  · intro s a hget; cases s <;> cases hget; rfl
  · intro s a a' s₁ hput; cases s <;> cases hput <;> rfl

/-! ## Unscoped joint extensionality: escape hatches (proved) -/

/-- A field of `Bool` present exactly at the state `b`. -/
def presentAt (b : Bool) : PLens Bool Unit where
  get s := if s = b then some () else none
  put _ _ := none

/-- **Each hypothesis of `not_jointExt_of_two_states_without_fields` is
needed.**  Dropping `s ≠ t` (one-point state type, `s = t`), or any one of
the four absence equations (states `false` and `true` of `Bool`), leaves an
instance where unscoped `JointExt` holds. -/
theorem not_jointExt_of_two_states_without_fields_tight :
    -- dropping `s ≠ t` (on the one-point state type, `s = t = ()`)
    (¬ ((() : Unit) ≠ ()) ∧ (absent : PLens Unit Unit).get () = none ∧
      (absent : PLens Unit Unit).get () = none ∧ (absent : PLens Unit Unit).get () = none ∧
      (absent : PLens Unit Unit).get () = none ∧
      JointExt (absent : PLens Unit Unit) (absent : PLens Unit Unit)) ∧
    -- dropping `l₁.get s = none`
    ((false : Bool) ≠ true ∧ (presentAt false).get false ≠ none ∧
      (absent : PLens Bool Unit).get false = none ∧ (presentAt false).get true = none ∧
      (absent : PLens Bool Unit).get true = none ∧
      JointExt (presentAt false) (absent : PLens Bool Unit)) ∧
    -- dropping `l₂.get s = none`
    ((false : Bool) ≠ true ∧ (absent : PLens Bool Unit).get false = none ∧
      (presentAt false).get false ≠ none ∧ (absent : PLens Bool Unit).get true = none ∧
      (presentAt false).get true = none ∧
      JointExt (absent : PLens Bool Unit) (presentAt false)) ∧
    -- dropping `l₁.get t = none`
    ((false : Bool) ≠ true ∧ (presentAt true).get false = none ∧
      (absent : PLens Bool Unit).get false = none ∧ (presentAt true).get true ≠ none ∧
      (absent : PLens Bool Unit).get true = none ∧
      JointExt (presentAt true) (absent : PLens Bool Unit)) ∧
    -- dropping `l₂.get t = none`
    ((false : Bool) ≠ true ∧ (absent : PLens Bool Unit).get false = none ∧
      (presentAt true).get false = none ∧ (absent : PLens Bool Unit).get true = none ∧
      (presentAt true).get true ≠ none ∧
      JointExt (absent : PLens Bool Unit) (presentAt true)) := by
  refine ⟨⟨fun h => h rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩,
    ⟨by decide, by decide, rfl, by decide, rfl, ?_⟩,
    ⟨by decide, rfl, by decide, rfl, by decide, ?_⟩,
    ⟨by decide, by decide, rfl, by decide, rfl, ?_⟩,
    ⟨by decide, rfl, by decide, rfl, by decide, ?_⟩⟩
  all_goals
    intro s t h₁ h₂
    cases s <;> cases t <;> first | rfl | (exact absurd h₁ (by decide)) | (exact absurd h₂ (by decide))

/-- **Non-vacuity of the unscoped-extensionality impossibility (ground
instance).**  In the intended model `Shape`, the two nullary tags are distinct
states lacking both fields. -/
theorem f5_unscoped_nonvacuity :
    Shape.nil ≠ Shape.unit ∧ pairFst.get Shape.nil = none ∧ pairSnd.get Shape.nil = none ∧
    pairFst.get Shape.unit = none ∧ pairSnd.get Shape.unit = none :=
  ⟨by decide, rfl, rfl, rfl, rfl⟩

/-- A sum type with exactly one state lacking both fields. -/
inductive Shape3 where
  /-- A nullary tag. -/
  | nil
  /-- A variant with only the field `a`. -/
  | onlyA (a : Bool)
  /-- A variant with the fields `a` and `b`. -/
  | pair (a b : Bool)
  deriving DecidableEq

/-- The field `a` of `Shape3` (present on `onlyA` and `pair`). -/
def shape3A : PLens Shape3 Bool where
  get
    | .onlyA a => some a
    | .pair a _ => some a
    | .nil => none
  put
    | .onlyA _, a' => some (.onlyA a')
    | .pair _ b, a' => some (.pair a' b)
    | .nil, _ => none

/-- The field `b` of `Shape3` (present only on `pair`). -/
def shape3B : PLens Shape3 Bool where
  get
    | .pair _ b => some b
    | _ => none
  put
    | .pair a _, b' => some (.pair a b')
    | _, _ => none

/-- **Positive control for the unscoped-extensionality impossibility.**  On a
sum type with a single state lacking both fields, unscoped joint
extensionality holds. -/
theorem shape3_jointExt : JointExt shape3A shape3B := by
  intro s t h₁ h₂
  cases s <;> cases t <;> simp_all [shape3A, shape3B]

/-- A sum type whose non-record variant carries a payload. -/
inductive ShapeOther where
  /-- A variant with a payload that is not one of the two fields. -/
  | other (c : Bool)
  /-- The record variant. -/
  | pair (a b : Bool)
  deriving DecidableEq

/-- The first field of `ShapeOther`. -/
def otherFst : PLens ShapeOther Bool where
  get
    | .pair a _ => some a
    | _ => none
  put
    | .pair _ b, a' => some (.pair a' b)
    | _, _ => none

/-- The second field of `ShapeOther`. -/
def otherSnd : PLens ShapeOther Bool where
  get
    | .pair _ b => some b
    | _ => none
  put
    | .pair a _, b' => some (.pair a b')
    | _, _ => none

/-- **Failure does not need nullary tags:** a two-variant sum type whose other
variant carries a payload already violates unscoped joint extensionality. -/
theorem otherFst_otherSnd_not_jointExt : ¬ JointExt otherFst otherSnd :=
  not_jointExt_of_two_states_without_fields (s := ShapeOther.other false)
    (t := ShapeOther.other true) (by decide) rfl rfl rfl rfl

/-! ## Why the variant is an arbitrary predicate (proved) -/

/-- Two record variants with fields of the same names. -/
inductive ShapeTwin where
  /-- The first record variant. -/
  | pair1 (a b : Bool)
  /-- The second record variant, with the same field names. -/
  | pair2 (a b : Bool)
  deriving DecidableEq

/-- The field `a`, present on both variants. -/
def twinA : PLens ShapeTwin Bool where
  get
    | .pair1 a _ => some a
    | .pair2 a _ => some a
  put
    | .pair1 _ b, a' => some (.pair1 a' b)
    | .pair2 _ b, a' => some (.pair2 a' b)

/-- The field `b`, present on both variants. -/
def twinB : PLens ShapeTwin Bool where
  get
    | .pair1 _ b => some b
    | .pair2 _ b => some b
  put
    | .pair1 a _, b' => some (.pair1 a b')
    | .pair2 a _, b' => some (.pair2 a b')

/-- The first variant of `ShapeTwin`. -/
def ShapeTwin.IsPair1 (s : ShapeTwin) : Prop :=
  ∃ a b, s = ShapeTwin.pair1 a b

/-- **Shared field names.**  On `ShapeTwin` the domain of the getters is the
whole type, and joint extensionality fails there; on the variant `pair1` the
variant-scoped decomposition holds. -/
theorem twin_jointExtOn_fails_on_union :
    (∀ s, (∃ a, twinA.get s = some a) ∧ (∃ b, twinB.get s = some b)) ∧
    ¬ JointExtOn (fun _ => True) twinA twinB ∧
    IsProductDecompositionOn ShapeTwin.IsPair1 twinA twinB := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    cases s with
    | pair1 a b => exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    | pair2 a b => exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  · intro h
    exact absurd (h (.pair1 false false) (.pair2 false false) trivial trivial rfl rfl) (by decide)
  · refine ⟨?_, ?_, fun a b => ⟨.pair1 a b, ⟨a, b, rfl⟩, rfl, rfl⟩, ?_, ?_⟩
    · rintro s ⟨a, b, rfl⟩; exact ⟨a, b, rfl, rfl⟩
    · rintro s t ⟨a, b, rfl⟩ ⟨a', b', rfl⟩ h₁ h₂
      cases h₁; cases h₂; rfl
    · rintro s a' ⟨a, b, rfl⟩; exact ⟨.pair1 a' b, rfl, ⟨a', b, rfl⟩, rfl, rfl⟩
    · rintro s b' ⟨a, b, rfl⟩; exact ⟨.pair1 a b', rfl, ⟨a, b', rfl⟩, rfl, rfl⟩

/-! ## Variant-scoped derived laws (proved)

As for total lenses, `GetPut`, `PutPut` and commuting puts on the variant
follow from the hypotheses of F5 without the nonemptiness condition.
-/

/-- Variant-scoped **GetPut**: on the variant, writing back the current value
succeeds and changes nothing. -/
def GetPutOn (V : S → Prop) (l : PLens S A) : Prop :=
  ∀ s a, V s → l.get s = some a → l.put s a = some s

/-- Variant-scoped **PutPut**: on the variant, after a successful write, a
second write has the same outcome as writing the second value directly. -/
def PutPutOn (V : S → Prop) (l : PLens S A) : Prop :=
  ∀ s a a' s₁, V s → l.put s a = some s₁ → l.put s₁ a' = l.put s a'

/-- Variant-scoped **commuting puts**: on the variant, writing through `l₁` and
then `l₂` has the same outcome (state or failure) as the other order. -/
def PutCommOn (V : S → Prop) (l₁ : PLens S A) (l₂ : PLens S B) : Prop :=
  ∀ s a b, V s → ((l₁.put s a).bind fun t => l₂.put t b) = ((l₂.put s b).bind fun t => l₁.put t a)

/-- A first field of the `pair` variant whose write resets the second field. -/
def pairResetSnd : PLens Shape Bool where
  get
    | .pair a _ => some a
    | _ => none
  put
    | .pair _ _, a' => some (.pair a' false)
    | _, _ => none

/-- A first field of the `pair` variant whose second field is a dirty flag. -/
def pairDirty : PLens Shape Bool where
  get
    | .pair a _ => some a
    | _ => none
  put
    | .pair a b, a' => if a = a' then some (.pair a b) else some (.pair a' true)
    | _, _ => none

/-- Positive example for `GetPutOn`. -/
theorem pairFst_getPutOn : GetPutOn Shape.IsPair pairFst := by
  rintro s a ⟨x, y, rfl⟩ h
  cases h
  rfl

/-- Negative example for `GetPutOn`: the second field is reset. -/
theorem pairResetSnd_not_getPutOn : ¬ GetPutOn Shape.IsPair pairResetSnd := by
  intro h
  exact absurd (h (.pair false true) false ⟨false, true, rfl⟩ rfl) (by decide)

/-- Positive example for `PutPutOn`. -/
theorem pairFst_putPutOn : PutPutOn Shape.IsPair pairFst := by
  rintro s a a' s₁ ⟨x, y, rfl⟩ h
  cases h
  rfl

/-- Negative example for `PutPutOn`: the dirty flag remembers the first write. -/
theorem pairDirty_not_putPutOn : ¬ PutPutOn Shape.IsPair pairDirty := by
  intro h
  exact absurd (h (.pair false false) true false (.pair true true) ⟨false, false, rfl⟩ rfl)
    (by decide)

/-- Positive example for `PutCommOn`. -/
theorem pairFst_pairSnd_putCommOn : PutCommOn Shape.IsPair pairFst pairSnd := by
  rintro s a b ⟨x, y, rfl⟩
  rfl

/-- Negative example for `PutCommOn`: aliasing. -/
theorem pairFst_pairFst_not_putCommOn : ¬ PutCommOn Shape.IsPair pairFst pairFst := by
  intro h
  exact absurd (h (.pair false false) true false ⟨false, false, rfl⟩) (by decide)

/-- **Variant-scoped derived law 1.**  Totality of `l₁` on `V`, `PutGet` of `l₁`
on `V`, cross-independence of `l₁` from `l₂` on `V` and joint extensionality on
`V` imply `GetPut` of `l₁` on `V`. -/
theorem getPutOn_of_totalOn_putGetOn_putIndepOn_jointExtOn {V : S → Prop}
    {l₁ : PLens S A} {l₂ : PLens S B}
    (ht₁ : TotalOn V l₁) (h₁ : PutGetOn V l₁) (h₁₂ : PutIndepOn V l₁ l₂)
    (hext : JointExtOn V l₁ l₂) : GetPutOn V l₁ := by
  intro s a hs hget
  obtain ⟨s', hput, hs'⟩ := ht₁.put_defined s a hs
  rw [hput]
  exact congrArg some (hext s' s hs' hs ((h₁ s a s' hs hput).trans hget.symm) (h₁₂ s a s' hs hput))

/-- **Variant-scoped derived law 2.**  The same hypotheses imply `PutPut` of
`l₁` on `V`. -/
theorem putPutOn_of_totalOn_putGetOn_putIndepOn_jointExtOn {V : S → Prop}
    {l₁ : PLens S A} {l₂ : PLens S B}
    (ht₁ : TotalOn V l₁) (h₁ : PutGetOn V l₁) (h₁₂ : PutIndepOn V l₁ l₂)
    (hext : JointExtOn V l₁ l₂) : PutPutOn V l₁ := by
  intro s a a' s₁ hs hput
  obtain ⟨s₁', hput', hs₁⟩ := ht₁.put_defined s a hs
  have e : s₁' = s₁ := Option.some.inj (hput'.symm.trans hput)
  subst e
  obtain ⟨s₂, h₂p, hs₂⟩ := ht₁.put_defined s₁' a' hs₁
  obtain ⟨s₃, h₃p, hs₃⟩ := ht₁.put_defined s a' hs
  rw [h₂p, h₃p]
  congr 1
  apply hext s₂ s₃ hs₂ hs₃
  · exact (h₁ _ _ _ hs₁ h₂p).trans (h₁ _ _ _ hs h₃p).symm
  · exact (h₁₂ _ _ _ hs₁ h₂p).trans ((h₁₂ _ _ _ hs hput').trans (h₁₂ _ _ _ hs h₃p).symm)

/-- **Variant-scoped derived law 3.**  Totality, `PutGet` and
cross-independence on `V` for both lenses, and joint extensionality on `V`,
imply that the two puts commute on `V`. -/
theorem putCommOn_of_totalOn_putGetOn_putIndepOn_jointExtOn {V : S → Prop}
    {l₁ : PLens S A} {l₂ : PLens S B}
    (ht₁ : TotalOn V l₁) (ht₂ : TotalOn V l₂) (h₁ : PutGetOn V l₁) (h₂ : PutGetOn V l₂)
    (h₁₂ : PutIndepOn V l₁ l₂) (h₂₁ : PutIndepOn V l₂ l₁) (hext : JointExtOn V l₁ l₂) :
    PutCommOn V l₁ l₂ := by
  intro s a b hs
  obtain ⟨s₁, p₁, v₁⟩ := ht₁.put_defined s a hs
  obtain ⟨s₂, p₂, v₂⟩ := ht₂.put_defined s b hs
  obtain ⟨s₃, p₃, v₃⟩ := ht₂.put_defined s₁ b v₁
  obtain ⟨s₄, p₄, v₄⟩ := ht₁.put_defined s₂ a v₂
  rw [p₁, p₂]
  show l₂.put s₁ b = l₁.put s₂ a
  rw [p₃, p₄]
  congr 1
  apply hext s₃ s₄ v₃ v₄
  · exact (h₂₁ _ _ _ v₁ p₃).trans ((h₁ _ _ _ hs p₁).trans (h₁ _ _ _ v₂ p₄).symm)
  · exact (h₂ _ _ _ v₁ p₃).trans ((h₂ _ _ _ hs p₂).symm.trans (h₁₂ _ _ _ v₂ p₄).symm)

end PLens

end Lens

end Toy
