import Toy.Ledger.Witnesses

/-!
# Tight, necessary, and unweakenable; the weakest replacement premise

"Tight", "necessary", and "cannot be weakened" are three different properties: the only
implication among them valid in every sufficient, non-vacuous instance is
`NecessaryAt → UnweakenableAt`, and every combination compatible with it occurs. The weakest
premise that can replace a hypothesis is identified, and unweakenability is characterized
through it.
-/

namespace Toy.Ledger

universe u v

section General

variable {M : Type u} {ι : Type v}

/-! ## Necessity, unweakenability, tightness -/

/-- Global necessity implies necessity relative to the other hypotheses. -/
theorem unweakenableAt_of_necessaryAt {H : ι → M → Prop} {C : M → Prop} {i : ι}
    (h : NecessaryAt H C i) : UnweakenableAt H C i :=
  fun x _ hc => h x hc

/-- Under sufficiency, a hypothesis is unweakenable and not tight exactly when it is
entailed by the other hypotheses. -/
theorem unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient
    {H : ι → M → Prop} {C : M → Prop} (hs : Sufficient H C) (i : ι) :
    (UnweakenableAt H C i ∧ ¬ TightAt H C i) ↔ ∀ x, (∀ j, j ≠ i → H j x) → H i x :=
  ⟨fun ⟨hu, hnt⟩ x ho => hu x ho (Classical.byContradiction fun hnc => hnt ⟨x, ho, hnc⟩),
   fun hent => ⟨fun x ho _ => hent x ho,
     fun ⟨x, ho, hnc⟩ => hnc (hs x fun j =>
       (Classical.em (j = i)).elim (fun h => h ▸ hent x ho) (ho j))⟩⟩

/-! ## The weakest replacement premise -/

/-- `WeakestPremise H C i` is the weakest premise that can replace hypothesis `i`:
replacing `H i` by `H'` keeps sufficiency exactly when `H'` implies `WeakestPremise H C i`;
`WeakestPremise H C i` is itself a valid replacement; the original theorem holds exactly
when `H i` implies it; and hypothesis `i` is not tight exactly when its weakest replacement
is valid (i.e. `H i` can be replaced by `True`). -/
theorem weakestPremise_is_weakest_replacement
    (H : ι → M → Prop) (C : M → Prop) (i : ι) :
    (∀ H' : M → Prop,
      Sufficient (replaceAt H i H') C ↔ ∀ x, H' x → WeakestPremise H C i x) ∧
    Sufficient (replaceAt H i (WeakestPremise H C i)) C ∧
    (Sufficient H C ↔ ∀ x, H i x → WeakestPremise H C i x) ∧
    ((∀ x, WeakestPremise H C i x) ↔ ¬ TightAt H C i) := by
  have h1 : ∀ H' : M → Prop,
      Sufficient (replaceAt H i H') C ↔ ∀ x, H' x → WeakestPremise H C i x := fun H' =>
    ⟨fun hs x hx ho => hs x fun j =>
        ⟨fun _ => hx, fun hji => ho j hji⟩,
     fun hw x hall => hw x ((hall i).1 rfl) (fun j hj => (hall j).2 hj)⟩
  refine ⟨h1, (h1 _).mpr (fun _ h => h), ?_, ?_⟩
  · exact ⟨fun hs x hix ho =>
        hs x fun j => (Classical.em (j = i)).elim (fun h => h ▸ hix) (ho j),
      fun hw x hall => hw x (hall i) (fun j _ => hall j)⟩
  · exact ⟨fun hw ⟨x, ho, hnc⟩ => hnc (hw x ho),
      fun hnt x ho => Classical.byContradiction fun hnc => hnt ⟨x, ho, hnc⟩⟩

/-- Under sufficiency, three characterizations of unweakenability of hypothesis `i`:
(1) `H i` agrees with its weakest replacement premise wherever the other hypotheses hold;
(2) every weakening `H'` of `H i` that keeps the theorem true agrees with `H i` wherever the
other hypotheses hold (such weakenings may still differ from `H i` outside that region);
(3) `H i` agrees with the conclusion `C` wherever the other hypotheses hold. -/
theorem unweakenableAt_characterizations_of_sufficient
    {H : ι → M → Prop} {C : M → Prop} (hs : Sufficient H C) (i : ι) :
    (UnweakenableAt H C i ↔
      ∀ x, (∀ j, j ≠ i → H j x) → (H i x ↔ WeakestPremise H C i x)) ∧
    (UnweakenableAt H C i ↔
      ∀ H' : M → Prop, (∀ x, H i x → H' x) → Sufficient (replaceAt H i H') C →
        ∀ x, (∀ j, j ≠ i → H j x) → H' x → H i x) ∧
    (UnweakenableAt H C i ↔ ∀ x, (∀ j, j ≠ i → H j x) → (H i x ↔ C x)) := by
  obtain ⟨hrep, hW, hsW, _⟩ := weakestPremise_is_weakest_replacement H C i
  refine ⟨⟨fun hu x ho => ⟨fun hix => hsW.mp hs x hix, fun hw => hu x ho (hw ho)⟩,
      fun hiff x ho hc => (hiff x ho).mpr (fun _ => hc)⟩,
    ⟨fun hu H' _ hs' x ho hx' => hu x ho ((hrep H').mp hs' x hx' ho),
      fun hall x ho hc => hall (WeakestPremise H C i) (hsW.mp hs) hW x ho (fun _ => hc)⟩,
    ⟨fun hu x ho => ⟨fun hix => hsW.mp hs x hix ho, hu x ho⟩,
      fun hiff x ho hc => (hiff x ho).mpr hc⟩⟩

end General

/-! ## Witnesses: necessity, unweakenability, tightness -/

/-- Counterexample for `h` in `unweakenableAt_of_necessaryAt`: `x ≤ 1` in
`x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2` is not unweakenable (it can be weakened to `x + y ≤ 2`). -/
theorem unweakenableAt_of_necessaryAt_ce_not_necessary : ¬ UnweakenableAt sumH sumC .h1 :=
  not_unweakenableAt_sum_h1

/-- Non-vacuity for `unweakenableAt_of_necessaryAt`. -/
theorem unweakenableAt_of_necessaryAt_nonvacuity : NecessaryAt pinH pinC .h1 :=
  necessaryAt_pin_h1

/-- The six combinations of (tight, necessary, unweakenable) permitted by
`unweakenableAt_of_necessaryAt` all occur at hypothesis `h1` of a sufficient, non-vacuous
instance:
* `x ≥ 1, x ≤ 1 ⊢ x = 1`: tight, necessary, unweakenable;
* `x = 1, x = 1 ⊢ x = 1`: not tight, necessary, unweakenable;
* `x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2`: tight, not necessary, not unweakenable;
* `x ≥ 1, x ≤ 1 ⊢ x ≤ 1`: not tight, not necessary, not unweakenable;
* `x = 0, y = 0 ⊢ x = y`: tight, not necessary, unweakenable;
* `x = 0, (x = 0 ∧ y = 0) ⊢ x = y`: not tight, not necessary, unweakenable. -/
theorem tight_necessary_unweakenable_six_combinations :
    (Sufficient pinH pinC ∧ NonVacuous pinH ∧
      TightAt pinH pinC .h1 ∧ NecessaryAt pinH pinC .h1 ∧ UnweakenableAt pinH pinC .h1) ∧
    (Sufficient dupH pinC ∧ NonVacuous dupH ∧
      ¬ TightAt dupH pinC .h1 ∧ NecessaryAt dupH pinC .h1 ∧ UnweakenableAt dupH pinC .h1) ∧
    (Sufficient sumH sumC ∧ NonVacuous sumH ∧
      TightAt sumH sumC .h1 ∧ ¬ NecessaryAt sumH sumC .h1 ∧ ¬ UnweakenableAt sumH sumC .h1) ∧
    (Sufficient pinH pinWeakC ∧ NonVacuous pinH ∧
      ¬ TightAt pinH pinWeakC .h1 ∧ ¬ NecessaryAt pinH pinWeakC .h1 ∧
      ¬ UnweakenableAt pinH pinWeakC .h1) ∧
    (Sufficient eqH eqC ∧ NonVacuous eqH ∧
      TightAt eqH eqC .h1 ∧ ¬ NecessaryAt eqH eqC .h1 ∧ UnweakenableAt eqH eqC .h1) ∧
    (Sufficient entH eqC ∧ NonVacuous entH ∧
      ¬ TightAt entH eqC .h1 ∧ ¬ NecessaryAt entH eqC .h1 ∧ UnweakenableAt entH eqC .h1) := by
  refine ⟨⟨sufficient_pin, nonVacuous_pin, tightAt_pin_h1, necessaryAt_pin_h1,
      unweakenableAt_pin_h1⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, not_necessaryAt_sum_h1,
      not_unweakenableAt_sum_h1⟩, ⟨?_, nonVacuous_pin, not_tightAt_pinWeak_h1, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  -- duplicated hypotheses
  · intro x hx; simp [dupH] at hx; exact hx
  · exact ⟨1, by simp [dupH]⟩
  · rintro ⟨x, hx, hc⟩; simp [dupH] at hx; exact hc hx
  · intro x hx; exact hx
  · intro x _ hc; exact hc
  -- x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2
  · intro p hp; simp [sumH] at hp; simp [sumC]; omega
  · exact ⟨(0, 0), by simp [sumH]⟩
  · exact ⟨(5, 0), by simp [sumH], by simp [sumC]⟩
  -- x ≥ 1, x ≤ 1 ⊢ x ≤ 1
  · intro x hx; simp [pinH] at hx; exact hx.2
  · intro h; have := h 0 (by simp [pinWeakC]); simp [pinH] at this
  · intro h; have := h 0 (by simp [pinH]) (by simp [pinWeakC]); simp [pinH] at this
  -- x = 0, y = 0 ⊢ x = y
  · intro p hp; simp [eqH] at hp; simp [eqC]; omega
  · exact ⟨(0, 0), by simp [eqH]⟩
  · exact ⟨(1, 0), by simp [eqH], by simp [eqC]⟩
  · intro h; have := h (1, 1) (by simp [eqC]); simp [eqH] at this
  · intro p hp hc; simp [eqH] at hp; simp [eqC] at hc; simp [eqH]; omega
  -- x = 0, (x = 0 ∧ y = 0) ⊢ x = y
  · intro p hp; simp [entH] at hp; simp [eqC]; omega
  · exact ⟨(0, 0), by simp [entH]⟩
  · rintro ⟨p, hp, hc⟩; simp [entH] at hp; simp [eqC] at hc; omega
  · intro h; have := h (1, 1) (by simp [eqC]); simp [entH] at this
  · intro p hp _; simp [entH] at hp; simp [entH]; omega

/-- The three tight combinations of `tight_necessary_unweakenable_six_combinations` occur in
irredundant families: `x ≥ 1, x ≤ 1 ⊢ x = 1`, `x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2`, and
`x = 0, y = 0 ⊢ x = y` are irredundant. (The three non-tight combinations cannot occur in an
irredundant family, by the definition of `Irredundant`.) -/
theorem tight_combinations_in_irredundant_families :
    Irredundant pinH pinC ∧ Irredundant sumH sumC ∧ Irredundant eqH eqC := by
  refine ⟨irredundant_pin, fun i => ?_, fun i => ?_⟩
  · cases i
    · exact ⟨(5, 0), by simp [sumH], by simp [sumC]⟩
    · exact ⟨(0, 5), by simp [sumH], by simp [sumC]⟩
  · cases i
    · exact ⟨(1, 0), by simp [eqH], by simp [eqC]⟩
    · exact ⟨(0, 1), by simp [eqH], by simp [eqC]⟩

/-- Counterexample for `hs` in
`unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient`: for `True ⊢ False`
the left side fails (the hypothesis is tight) while the right side holds. -/
theorem unweakenableAt_and_not_tightAt_iff_entailed_ce_not_sufficient :
    ¬ ((UnweakenableAt topH falseC () ∧ ¬ TightAt topH falseC ()) ↔
        ∀ x, (∀ j, j ≠ () → topH j x) → topH () x) := by
  intro h
  exact (h.mpr (fun _ _ => trivial)).2 tightAt_topH_falseC

/-- Non-vacuity for `unweakenableAt_and_not_tightAt_iff_entailed_by_others_of_sufficient`,
with both sides true: in `x = 0, (x = 0 ∧ y = 0) ⊢ x = y`, hypothesis `x = 0` is entailed by
the other one. -/
theorem unweakenableAt_and_not_tightAt_iff_entailed_nonvacuity :
    Sufficient entH eqC ∧ (UnweakenableAt entH eqC .h1 ∧ ¬ TightAt entH eqC .h1) := by
  obtain ⟨-, -, -, -, -, ⟨hs, -, hnt, -, hu⟩⟩ := tight_necessary_unweakenable_six_combinations
  exact ⟨hs, hu, hnt⟩

/-- Non-tightness alone does not give entailment by the other hypotheses: in
`x ≥ 1, x ≤ 1 ⊢ x ≤ 1` the hypothesis `x ≥ 1` is not tight, but `x ≤ 1` does not entail
`x ≥ 1` (take `x = 0`). -/
theorem not_tightAt_not_entailed_by_others_pinWeak :
    Sufficient pinH pinWeakC ∧ ¬ TightAt pinH pinWeakC .h1 ∧
      ¬ ∀ x, (∀ j, j ≠ Two.h1 → pinH j x) → pinH .h1 x := by
  refine ⟨isolatingAt_sufficient_not_tightAt_pinWeak.1, not_tightAt_pinWeak_h1, fun h => ?_⟩
  have := h 0 (fun j hj => by cases j; exact absurd rfl hj; simp [pinH])
  simp [pinH] at this

/-! ## Witnesses: the weakest replacement premise -/

/-- Non-vacuity for `weakestPremise_is_weakest_replacement`: in `x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2`,
replacing `x ≤ 1` by `x + y ≤ 2` keeps sufficiency, the weakest replacement is not valid
(`h1` is tight), and it strictly weakens `x ≤ 1` (it holds at `(2, 0)`). -/
theorem weakestPremise_sum_nonvacuity :
    Sufficient (replaceAt sumH .h1 sumC) sumC ∧ TightAt sumH sumC .h1 ∧
      WeakestPremise sumH sumC .h1 (2, 0) ∧ ¬ sumH .h1 (2, 0) :=
  ⟨sufficient_replaceAt_sum_h1_by_sumC, ⟨(5, 0), by simp [sumH], by simp [sumC]⟩,
    weakestPremise_sum_h1_at_2_0⟩

/-- Weakenability allows premises that mention other variables: in
`x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2` the hypothesis `x ≤ 1` is not unweakenable (it can be replaced
by `x + y ≤ 2`), yet every premise `A x` on the first coordinate alone that is implied by
`x ≤ 1` and keeps the theorem true already implies `x ≤ 1`. -/
theorem sumH_h1_weakenable_but_not_within_first_coordinate :
    ¬ UnweakenableAt sumH sumC .h1 ∧
      ∀ A : Nat → Prop, (∀ x, x ≤ 1 → A x) →
        Sufficient (replaceAt sumH .h1 (fun p => A p.1)) sumC → ∀ x, A x → x ≤ 1 := by
  refine ⟨not_unweakenableAt_sum_h1, fun A _ hs x hA => ?_⟩
  have := hs (x, 1) (fun j => by
    cases j
    · exact (replaceAt_self _ _ _ _).mpr hA
    · exact (replaceAt_of_ne _ _ (by decide) _).mpr (by simp [sumH]))
  simp [sumC] at this
  omega

/-- For `True ⊢ False` the hypothesis is (vacuously) unweakenable, yet it disagrees with
its weakest replacement premise, which is `False`. -/
theorem unweakenableAt_true_false_disagrees :
    UnweakenableAt topH falseC () ∧
      ¬ ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ WeakestPremise topH falseC () x) := by
  refine ⟨fun _ _ hc => hc.elim, fun h => ?_⟩
  have := (h () (fun j hj => absurd (by cases j; rfl) hj)).mp trivial
  exact this (fun j hj => absurd (by cases j; rfl) hj)

/-- Counterexample for `hs` in `unweakenableAt_characterizations_of_sufficient`: for
`True ⊢ False` over `Unit` the conjunction fails because its first conjunct fails (`unweakenableAt_true_false_disagrees`); the third conjunct fails too (`unweakenableAt_third_characterization_fails_true_false`). -/
theorem unweakenableAt_characterizations_ce_not_sufficient :
    ¬ ((UnweakenableAt topH falseC () ↔
          ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ WeakestPremise topH falseC () x)) ∧
        (UnweakenableAt topH falseC () ↔
          ∀ H' : Unit → Prop, (∀ x, topH () x → H' x) → Sufficient (replaceAt topH () H') falseC →
            ∀ x, (∀ j, j ≠ () → topH j x) → H' x → topH () x) ∧
        (UnweakenableAt topH falseC () ↔
          ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ falseC x))) :=
  fun h => unweakenableAt_true_false_disagrees.2 (h.1.mp unweakenableAt_true_false_disagrees.1)

/-- Non-vacuity for `unweakenableAt_characterizations_of_sufficient`. -/
theorem unweakenableAt_characterizations_nonvacuity :
    Sufficient pinH pinC ∧ UnweakenableAt pinH pinC .h1 :=
  ⟨sufficient_pin, unweakenableAt_pin_h1⟩

/-- One hypothesis `b = true` with the conclusion `b = false`, over `Bool`. -/
def flipH : Unit → Bool → Prop := single fun b => b = true

/-- Conclusion `b = false`. -/
def flipC : Bool → Prop := fun b => b = false

/-- Second counterexample for `hs` in `unweakenableAt_characterizations_of_sufficient`: the
second characterization fails on its own for `b = true ⊢ b = false` over `Bool` (theorem
false). There no weakening keeps the theorem true, so the right side holds vacuously, while
unweakenability fails. (The first characterization holds on this instance, so the two
counterexamples are needed separately.) -/
theorem unweakenableAt_iff_weakenings_ce_not_sufficient :
    ¬ (UnweakenableAt flipH flipC () ↔
        ∀ H' : Bool → Prop, (∀ x, flipH () x → H' x) → Sufficient (replaceAt flipH () H') flipC →
          ∀ x, (∀ j, j ≠ () → flipH j x) → H' x → flipH () x) := by
  intro h
  have hnu : ¬ UnweakenableAt flipH flipC () := fun hu => by
    have := hu false (fun j hj => absurd (by cases j; rfl) hj) rfl
    simp [flipH] at this
  apply hnu
  refine h.mpr fun H' hw hsuff x _ _ => ?_
  exfalso
  have := hsuff true (fun j => by cases j; exact (replaceAt_self _ _ _ _).mpr (hw true rfl))
  simp [flipC] at this

/-- On `b = true ⊢ b = false` the first characterization of
`unweakenableAt_characterizations_of_sufficient` holds (both sides are false). -/
theorem unweakenableAt_first_characterization_holds_flip :
    UnweakenableAt flipH flipC () ↔
      ∀ x, (∀ j, j ≠ () → flipH j x) → (flipH () x ↔ WeakestPremise flipH flipC () x) := by
  constructor
  · intro hu
    have := hu false (fun j hj => absurd (by cases j; rfl) hj) rfl
    simp [flipH] at this
  · intro h
    have := (h true (fun j hj => absurd (by cases j; rfl) hj)).mp rfl
      (fun j hj => absurd (by cases j; rfl) hj)
    simp [flipC] at this

end Toy.Ledger
