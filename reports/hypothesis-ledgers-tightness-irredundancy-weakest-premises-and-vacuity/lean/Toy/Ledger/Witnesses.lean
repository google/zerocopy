import Toy.Ledger.Examples

/-!
# What tightness, irredundancy, and isolation witnesses establish

The exact meaning of a single `tight` label; the meaning of an all-`tight` ledger
(inclusion-minimality, and the minimal-unsatisfiable-family reading); and the separation of
irredundancy from the classical notions of axiom independence.
-/

namespace Toy.Ledger

universe u v

section General

variable {M : Type u} {ι : Type v}

/-! ## The exact meaning of `tight` -/

/-- Under sufficiency, every model that satisfies the hypotheses other than `i` and
violates the conclusion violates `H i` (so it violates `H i` and no other hypothesis); and
`TightAt H C i` holds exactly when some model satisfies every hypothesis other than `i` and
violates both `H i` and `C`. -/
theorem tightAt_iff_witness_violates_exactly_i_of_sufficient
    {H : ι → M → Prop} {C : M → Prop} (hs : Sufficient H C) (i : ι) :
    (∀ x, (∀ j, j ≠ i → H j x) → ¬ C x → ¬ H i x) ∧
    (TightAt H C i ↔ ∃ x, (∀ j, j ≠ i → H j x) ∧ ¬ H i x ∧ ¬ C x) := by
  have hpt : ∀ x, (∀ j, j ≠ i → H j x) → ¬ C x → ¬ H i x := fun x ho hnc hi =>
    hnc (hs x fun j => (Classical.em (j = i)).elim (fun h => h ▸ hi) (ho j))
  exact ⟨hpt, ⟨fun ⟨x, ho, hnc⟩ => ⟨x, ho, hpt x ho hnc, hnc⟩,
    fun ⟨x, ho, _, hnc⟩ => ⟨x, ho, hnc⟩⟩⟩

/-- `TightAt H C i` says exactly that the family with hypothesis `i` deleted is not
sufficient for `C`. No other assumption is needed. -/
theorem tightAt_iff_not_sufficient_without (H : ι → M → Prop) (C : M → Prop) (i : ι) :
    TightAt H C i ↔ ¬ Sufficient (restrict (fun j => j ≠ i) H) C :=
  ⟨fun ⟨x, ho, hnc⟩ hs => hnc (hs x fun ⟨j, hj⟩ => ho j hj),
   fun hns => Classical.byContradiction fun hnt =>
     hns fun x hs => Classical.byContradiction fun hnc =>
       hnt ⟨x, fun j hj => hs ⟨j, hj⟩, hnc⟩⟩

/-- When the theorem fails, every hypothesis is tight: any counterexample to `Sufficient H C`
is a tightness witness for every index. -/
theorem irredundant_of_not_sufficient {H : ι → M → Prop} {C : M → Prop}
    (hns : ¬ Sufficient H C) : Irredundant H C := fun _ =>
  Classical.byContradiction fun hnt => hns fun x hall =>
    Classical.byContradiction fun hnc => hnt ⟨x, fun j _ => hall j, hnc⟩

/-! ## An all-`tight` ledger is inclusion-minimality -/

/-- `Irredundant H C` holds exactly when no proper subfamily of `H` (one omitting at least
one hypothesis, possibly many) is sufficient for `C`. So the single-deletion witnesses
certify minimality against deleting any nonempty set of hypotheses. -/
theorem irredundant_iff_no_proper_subfamily_sufficient (H : ι → M → Prop) (C : M → Prop) :
    Irredundant H C ↔ ∀ S : ι → Prop, (∃ i, ¬ S i) → ¬ Sufficient (restrict S H) C :=
  ⟨fun hirr _ ⟨i, hni⟩ hs =>
     let ⟨x, ho, hnc⟩ := hirr i
     hnc (hs x fun ⟨j, hsj⟩ => ho j fun hji => hni (hji ▸ hsj)),
   fun h i => (tightAt_iff_not_sufficient_without H C i).mpr
     (h (fun j => j ≠ i) ⟨i, fun hne => hne rfl⟩)⟩

/-- A sufficient, irredundant, non-vacuous ledger is exactly a minimal unsatisfiable family
`{H i | i} ∪ {¬ C}`: the theorem is unsatisfiability of the family, `TightAt H C i` is
satisfiability after deleting `H i`, and `NonVacuous H` is satisfiability after deleting the
member `¬ C`. -/
theorem sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable
    (H : ι → M → Prop) (C : M → Prop) :
    (Sufficient H C ∧ Irredundant H C ∧ NonVacuous H) ↔
      MinimalUnsatisfiable (withNegatedConclusion H C) := by
  constructor
  · rintro ⟨hs, hirr, ⟨w, hw⟩⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx⟩
      exact hx none (hs x fun i => hx (some i))
    · rintro S ⟨k, hnk⟩
      cases k with
      | none =>
        refine ⟨w, fun ⟨j, hsj⟩ => ?_⟩
        cases j with
        | none => exact absurd hsj hnk
        | some i => exact hw i
      | some i =>
        obtain ⟨x, ho, hnc⟩ := hirr i
        refine ⟨x, fun ⟨j, hsj⟩ => ?_⟩
        cases j with
        | none => exact hnc
        | some j => exact ho j (fun hji => hnk (hji ▸ hsj))
  · rintro ⟨hunsat, hmin⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact Classical.byContradiction fun hnc =>
        hunsat ⟨x, fun k => match k with | none => hnc | some i => hx i⟩
    · intro i
      obtain ⟨x, hx⟩ := hmin (fun k => k ≠ some i) ⟨some i, fun h => h rfl⟩
      exact ⟨x, fun j hj => hx ⟨some j, fun h => hj (Option.some.inj h)⟩,
        hx ⟨none, by simp⟩⟩
    · obtain ⟨x, hx⟩ := hmin (fun k => k ≠ none) ⟨none, fun h => h rfl⟩
      exact ⟨x, fun i => hx ⟨some i, by simp⟩⟩

/-! ## Tightness versus isolation -/

/-- Under sufficiency, if hypothesis `i` is tight then it has an isolating model (one that
violates `H i` and satisfies every other hypothesis); by
`tightAt_iff_witness_violates_exactly_i_of_sufficient`, every tightness witness is one. -/
theorem isolatingAt_of_tightAt_of_sufficient {H : ι → M → Prop} {C : M → Prop} {i : ι}
    (hs : Sufficient H C) (ht : TightAt H C i) : IsolatingAt H i :=
  let ⟨x, ho, hnc⟩ := ht
  ⟨x, (tightAt_iff_witness_violates_exactly_i_of_sufficient hs i).1 x ho hnc, ho⟩

end General

/-! ## Witnesses: the meaning of `tight` -/

/-- The one-hypothesis family `True` over `Unit` (paired with the conclusion `False`, the
theorem fails). -/
def topH : Unit → Unit → Prop := single fun _ => True

theorem tightAt_topH_falseC : TightAt topH falseC () :=
  ⟨(), fun j hj => absurd (by cases j; rfl) hj, fun h => h⟩

/-- Counterexample for `hs` in `tightAt_iff_witness_violates_exactly_i_of_sufficient`:
for `True ⊢ False` over `Unit` (theorem false) the conclusion fails; the only model
satisfies the other (no) hypotheses and violates `False`, yet satisfies `H i = True`. -/
theorem tightAt_iff_witness_violates_exactly_i_ce_not_sufficient :
    ¬ ((∀ x, (∀ j, j ≠ () → topH j x) → ¬ falseC x → ¬ topH () x) ∧
        (TightAt topH falseC () ↔
          ∃ x, (∀ j, j ≠ () → topH j x) ∧ ¬ topH () x ∧ ¬ falseC x)) := by
  rintro ⟨hpt, _⟩
  exact hpt () (fun j hj => absurd (by cases j; rfl) hj) (fun h => h) trivial

/-- Non-vacuity for `tightAt_iff_witness_violates_exactly_i_of_sufficient`: the running
example `x ≥ 1, x ≤ 1 ⊢ x = 1` is sufficient, and `h1` is tight (witness `x = 0`, which
violates exactly `x ≥ 1`). -/
theorem tightAt_iff_witness_violates_exactly_i_nonvacuity :
    Sufficient pinH pinC ∧ TightAt pinH pinC .h1 ∧
      ((∀ j, j ≠ Two.h1 → pinH j 0) ∧ ¬ pinH .h1 0 ∧ ¬ pinC 0) :=
  ⟨sufficient_pin, tightAt_pin_h1, by simp [pinH], by simp [pinH], by simp [pinC]⟩

/-- Non-vacuity for `tightAt_iff_not_sufficient_without`: both sides hold for `h1` of the
running example. -/
theorem tightAt_iff_not_sufficient_without_nonvacuity :
    TightAt pinH pinC .h1 ∧ ¬ Sufficient (restrict (fun j => j ≠ Two.h1) pinH) pinC := by
  refine ⟨tightAt_pin_h1, fun h => ?_⟩
  have := h 0 (fun ⟨j, hj⟩ => by
    cases j
    · exact absurd rfl hj
    · simp [restrict, pinH])
  simp [pinC] at this

/-- Every false theorem is irredundant, even with duplicated trivial hypotheses:
`True, True ⊢ False` over `Unit` is not sufficient, yet irredundant and non-vacuous. -/
theorem irredundant_dup_true_false :
    ¬ Sufficient (pair (trueC (M := Unit)) trueC) falseC ∧
      Irredundant (pair (trueC (M := Unit)) trueC) falseC ∧
      NonVacuous (pair (trueC (M := Unit)) trueC) :=
  ⟨fun hs => hs () (fun j => by cases j <;> trivial),
   fun _ => ⟨(), fun j _ => by cases j <;> trivial, id⟩,
   ⟨(), fun j => by cases j <;> trivial⟩⟩

/-! ## Witnesses: all-`tight` ledgers -/

/-- Non-vacuity for `irredundant_iff_no_proper_subfamily_sufficient`: the running example
is irredundant, sufficient, and its empty subfamily is not sufficient. -/
theorem irredundant_iff_no_proper_subfamily_sufficient_nonvacuity :
    Sufficient pinH pinC ∧ Irredundant pinH pinC ∧
      ¬ Sufficient (restrict (fun _ => False) pinH) pinC := by
  refine ⟨sufficient_pin, irredundant_pin, fun h => ?_⟩
  have := h 0 (fun ⟨_, hj⟩ => hj.elim)
  simp [pinC] at this

/-- Single deletions do not compose: in `x = 1, x = 1 ⊢ x = 1` neither hypothesis is
tight (each can be deleted alone), yet deleting both leaves the empty family, which is not
sufficient. -/
theorem dup_each_not_tight_but_both_needed :
    Sufficient dupH pinC ∧ (∀ i, ¬ TightAt dupH pinC i) ∧
      ¬ Sufficient (restrict (fun _ => False) dupH) pinC := by
  refine ⟨fun x hx => by simpa [dupH, pinC] using hx .h1, fun i => ?_, fun h => ?_⟩
  · rintro ⟨x, ho, hc⟩
    cases i
    · exact hc (by simpa [dupH, pinC] using ho .h2 (by decide))
    · exact hc (by simpa [dupH, pinC] using ho .h1 (by decide))
  · have := h 0 (fun ⟨_, hj⟩ => hj.elim)
    simp [pinC] at this

/-- The infinite family `x ≥ 0, x ≥ 1, x ≥ 2, …` over `Nat` (hypothesis `i` is `i ≤ x`). -/
def geH : Nat → Nat → Prop := fun i x => i ≤ x

/-- An infinite sufficient family need not contain an irredundant sufficient subfamily:
`geH` is sufficient for `False` (no `x` is above every `i`), no single hypothesis is tight,
and no subfamily of `geH` is both sufficient for `False` and irredundant. -/
theorem geH_sufficient_no_irredundant_sufficient_subfamily :
    Sufficient geH falseC ∧ (∀ i, ¬ TightAt geH falseC i) ∧
      ∀ S : Nat → Prop,
        ¬ (Sufficient (restrict S geH) falseC ∧ Irredundant (restrict S geH) falseC) := by
  refine ⟨fun x hx => absurd (hx (x + 1)) (by simp [geH]), fun i => ?_, fun S => ?_⟩
  · rintro ⟨x, ho, _⟩
    have := ho (x + i + 1) (by omega)
    simp [geH] at this
    omega
  · rintro ⟨hs, hirr⟩
    by_cases hne : ∃ i, S i
    · obtain ⟨i, hi⟩ := hne
      obtain ⟨x, ho, _⟩ := hirr ⟨i, hi⟩
      apply hs (max x i)
      intro ⟨j, hj⟩
      show j ≤ max x i
      by_cases hji : j = i
      · omega
      · have := ho ⟨j, hj⟩ (fun h => hji (congrArg Subtype.val h))
        simp only [restrict, geH] at this
        omega
    · exact hs 0 (fun ⟨j, hj⟩ => absurd ⟨j, hj⟩ hne)

/-- Non-vacuity for `sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable`: both
sides hold for the running example. -/
theorem sufficient_irredundant_nonVacuous_iff_minimalUnsatisfiable_nonvacuity :
    (Sufficient pinH pinC ∧ Irredundant pinH pinC ∧ NonVacuous pinH) ∧
      MinimalUnsatisfiable (withNegatedConclusion pinH pinC) :=
  ⟨⟨sufficient_pin, irredundant_pin, nonVacuous_pin⟩, minimalUnsatisfiable_pin⟩

/-! ## Witnesses: tightness versus isolation -/

/-- The converse of `isolatingAt_of_tightAt_of_sufficient` fails: in `x ≥ 1, x ≤ 1 ⊢ x ≤ 1`
the hypothesis `x ≥ 1` has an isolating model (`x = 0`) but is not tight. -/
theorem isolatingAt_sufficient_not_tightAt_pinWeak :
    Sufficient pinH pinWeakC ∧ NonVacuous pinH ∧ IsolatingAt pinH .h1 ∧
      ¬ TightAt pinH pinWeakC .h1 := by
  refine ⟨fun x hx => ?_, nonVacuous_pin, isolatingAt_pin_h1, not_tightAt_pinWeak_h1⟩
  simp [pinH] at hx
  exact hx.2

/-- Irredundancy, full independence, and isolation are pairwise distinct in the ways a
reader might conflate them. (A) `x ≥ 1, x ≤ 1 ⊢ x = 1` is sufficient, irredundant, and
non-vacuous, yet not independent (no `x` makes both hypotheses false). (B) Two coordinate
bits are independent, yet with the valid conclusion `True` no hypothesis is tight.
(C) In `x ≥ 1, x ≤ 1 ⊢ x ≤ 1` the hypothesis `x ≥ 1` has an isolating model but is not
tight. -/
theorem irredundance_independence_isolation_countermodels :
    (Sufficient pinH pinC ∧ Irredundant pinH pinC ∧ NonVacuous pinH ∧ ¬ Independent pinH) ∧
    (Sufficient bitsH trueC ∧ NonVacuous bitsH ∧ Independent bitsH ∧
      ∀ i, ¬ TightAt bitsH trueC i) ∧
    (Sufficient pinH pinWeakC ∧ NonVacuous pinH ∧ IsolatingAt pinH .h1 ∧
      ¬ TightAt pinH pinWeakC .h1) := by
  refine ⟨⟨sufficient_pin, irredundant_pin, nonVacuous_pin, not_independent_pin⟩,
    ⟨fun _ _ => trivial, ⟨(true, true), by simp [bitsH]⟩, independent_bits, ?_⟩,
    isolatingAt_sufficient_not_tightAt_pinWeak⟩
  rintro i ⟨_, _, hc⟩
  exact hc trivial

/-- Isolation at every index does not give irredundancy: in `x ≥ 1, x ≤ 1 ⊢ x ≤ 1` both
hypotheses have isolating models (`x = 0` and `x = 2`), the theorem holds, and the family
is not irredundant (`x ≥ 1` is not tight). -/
theorem isolatingAt_every_index_not_irredundant_pinWeak :
    Sufficient pinH pinWeakC ∧ (∀ i, IsolatingAt pinH i) ∧ ¬ Irredundant pinH pinWeakC := by
  refine ⟨isolatingAt_sufficient_not_tightAt_pinWeak.1, fun i => ?_,
    fun h => not_tightAt_pinWeak_h1 (h .h1)⟩
  cases i
  · exact isolatingAt_pin_h1
  · exact ⟨2, by simp [pinH], by simp [pinH]⟩

/-- Counterexample for `hs` in `isolatingAt_of_tightAt_of_sufficient`: without sufficiency,
`True ⊢ False` has its only hypothesis tight but not isolatable. -/
theorem isolatingAt_of_tightAt_ce_not_sufficient :
    TightAt topH falseC () ∧ ¬ IsolatingAt topH () := by
  refine ⟨tightAt_topH_falseC, ?_⟩
  rintro ⟨_, hn, _⟩
  exact hn trivial

/-- Counterexample for `ht` in `isolatingAt_of_tightAt_of_sufficient`: the duplicated
hypotheses `x = 1, x = 1 ⊢ x = 1` are sufficient, yet `h1` has no isolating model. -/
theorem isolatingAt_of_tightAt_ce_not_tight :
    Sufficient dupH pinC ∧ ¬ IsolatingAt dupH .h1 := by
  refine ⟨fun x hx => ?_, not_isolatingAt_dup_h1⟩
  simp [dupH] at hx
  exact hx

/-- Non-vacuity for `isolatingAt_of_tightAt_of_sufficient`. -/
theorem isolatingAt_of_tightAt_of_sufficient_nonvacuity :
    Sufficient pinH pinC ∧ TightAt pinH pinC .h1 :=
  ⟨sufficient_pin, tightAt_pin_h1⟩

end Toy.Ledger
