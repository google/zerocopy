import Toy.Ledger.Strength

/-!
# Families of hypotheses: non-uniqueness, vacuity, depth, and restated conclusions

Irredundant sufficient hypothesis sets are neither unique nor of minimum size, although
inclusion-minimal sufficient subfamilies form an antichain. A complete tightness ledger does
not certify non-vacuity, and non-vacuity certifies no tightness. One tight hypothesis
certifies that the conclusion is not valid, and an irredundant, non-vacuous ledger does not
certify depth. No single hypothesis of an irredundant family with at least two hypotheses
entails the conclusion.
-/

namespace Toy.Ledger

universe u v

section General

variable {M : Type u} {ι : Type v}

/-! ## Inclusion-minimal sufficient subfamilies -/

/-- If a subfamily `S` of a vocabulary `H` is sufficient for `C`, every superfamily `T ⊇ S`
whose members are all tight (within `T`) equals `S`. In particular, of two sufficient,
irredundant subfamilies neither strictly contains the other. -/
theorem subfamily_eq_of_sufficient_of_irredundant_superfamily
    {H : ι → M → Prop} {C : M → Prop} {S T : ι → Prop}
    (hS : Sufficient (restrict S H) C) (hT : Irredundant (restrict T H) C)
    (hST : ∀ i, S i → T i) : S = T := by
  funext i
  apply propext
  refine ⟨hST i, fun hTi => Classical.byContradiction fun hnsi => ?_⟩
  obtain ⟨x, ho, hnc⟩ := hT ⟨i, hTi⟩
  exact hnc (hS x fun ⟨j, hSj⟩ => ho ⟨j, hST j hSj⟩ fun hjeq =>
    hnsi (Subtype.mk.inj hjeq ▸ hSj))

/-! ## What one tight hypothesis certifies -/

/-- A single tight hypothesis certifies that the conclusion is not valid over the model
type. Equivalently, if the conclusion is valid, no hypothesis is tight. -/
theorem not_valid_of_tightAt {H : ι → M → Prop} {C : M → Prop} {i : ι}
    (h : TightAt H C i) : ¬ ∀ x, C x :=
  let ⟨x, _, hnc⟩ := h
  fun hall => hnc (hall x)

/-! ## Hypotheses that restate the conclusion -/

/-- If hypothesis `i` alone entails the conclusion, no other hypothesis is tight. (No
assumption on the number of hypotheses is needed; with a single hypothesis the statement
is vacuous.) -/
theorem not_tightAt_of_ne_of_single_entails {H : ι → M → Prop} {C : M → Prop} {i j : ι}
    (hi : ∀ x, H i x → C x) (hj : j ≠ i) : ¬ TightAt H C j :=
  fun ⟨x, ho, hnc⟩ => hnc (hi x (ho i hj.symm))

/-- In an irredundant family with at least one hypothesis besides `i`, hypothesis `i` alone
does not entail the conclusion over the whole model type. (It may still agree with the
conclusion on the region where another hypothesis holds:
`irredundant_hypothesis_restates_conclusion_within_other`.) -/
theorem not_single_entails_of_irredundant_of_exists_other {H : ι → M → Prop} {C : M → Prop}
    {i : ι} (hirr : Irredundant H C) (hother : ∃ j, j ≠ i) : ¬ ∀ x, H i x → C x :=
  let ⟨j, hj⟩ := hother
  fun hi => not_tightAt_of_ne_of_single_entails hi hj (hirr j)

end General

/-! ## Witnesses: non-uniqueness and the antichain property -/

/-- Over the vocabulary `x ≤ 1, y ≤ 1, x + y ≤ 2` and the conclusion `x + y ≤ 2`, both the
two-member subfamily `{x ≤ 1, y ≤ 1}` and the one-member subfamily `{x + y ≤ 2}` are
sufficient, irredundant, and non-vacuous. So "every hypothesis is tight" singles out neither
a unique nor a minimum-size hypothesis set. -/
theorem irredundant_sufficient_subfamilies_of_sizes_two_and_one :
    (∀ j, j ≠ Three.h3 ↔ (j = .h1 ∨ j = .h2)) ∧
    Sufficient (restrict (fun j => j ≠ Three.h3) sumVocab) sumC ∧
    Irredundant (restrict (fun j => j ≠ Three.h3) sumVocab) sumC ∧
    NonVacuous (restrict (fun j => j ≠ Three.h3) sumVocab) ∧
    Sufficient (restrict (fun j => j = Three.h3) sumVocab) sumC ∧
    Irredundant (restrict (fun j => j = Three.h3) sumVocab) sumC ∧
    NonVacuous (restrict (fun j => j = Three.h3) sumVocab) := by
  refine ⟨fun j => by cases j <;> simp, sufficient_restrict_sumVocab_h1h2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    cases i
    · refine ⟨(5, 0), fun ⟨j, hj⟩ hne => ?_, by simp [sumC]⟩
      cases j
      · exact absurd rfl hne
      · simp [restrict, sumVocab]
      · exact absurd rfl hj
    · refine ⟨(0, 5), fun ⟨j, hj⟩ hne => ?_, by simp [sumC]⟩
      cases j
      · simp [restrict, sumVocab]
      · exact absurd rfl hne
      · exact absurd rfl hj
    · exact absurd rfl hi
  · exact ⟨(0, 0), fun ⟨j, _⟩ => by cases j <;> simp [restrict, sumVocab]⟩
  · intro p hp
    simpa [restrict, sumVocab, sumC] using hp ⟨.h3, rfl⟩
  · rintro ⟨i, hi⟩
    subst hi
    exact ⟨(5, 5), fun ⟨j, hj⟩ hne => absurd (Subtype.ext hj) hne, by simp [sumC]⟩
  · exact ⟨(0, 0), fun ⟨j, hj⟩ => by subst hj; simp [restrict, sumVocab]⟩

/-- The vocabulary `x = 0, y = 0, x = 0 ∧ y = 0` over `Int × Int`. -/
def intVocab : Three → Int × Int → Prop :=
  triple (fun p => p.1 = 0) (fun p => p.2 = 0) (fun p => p.1 = 0 ∧ p.2 = 0)

/-- Conclusion `x + y = 0` over `Int × Int`. -/
def intC : Int × Int → Prop := fun p => p.1 + p.2 = 0

/-- Irredundant sufficient subfamilies of different sizes also occur when no candidate
hypothesis is equivalent to the conclusion: over `Int × Int`, with candidates `x = 0`,
`y = 0`, `x = 0 ∧ y = 0` and conclusion `x + y = 0`, no candidate is equivalent to the
conclusion (take `(1, -1)`), and both `{x = 0, y = 0}` and `{x = 0 ∧ y = 0}` are sufficient,
irredundant, and non-vacuous. -/
theorem irredundant_sufficient_subfamilies_no_candidate_equals_conclusion :
    (∀ j, ¬ ∀ p, intVocab j p ↔ intC p) ∧
    Sufficient (restrict (fun j => j ≠ Three.h3) intVocab) intC ∧
    Irredundant (restrict (fun j => j ≠ Three.h3) intVocab) intC ∧
    NonVacuous (restrict (fun j => j ≠ Three.h3) intVocab) ∧
    Sufficient (restrict (fun j => j = Three.h3) intVocab) intC ∧
    Irredundant (restrict (fun j => j = Three.h3) intVocab) intC ∧
    NonVacuous (restrict (fun j => j = Three.h3) intVocab) := by
  refine ⟨fun j h => ?_, fun p hp => ?_, ?_, ?_, fun p hp => ?_, ?_, ?_⟩
  · have := (h (1, -1)).mpr (by simp [intC])
    cases j <;> simp [intVocab] at this
  · have h1 := hp ⟨.h1, by decide⟩
    have h2 := hp ⟨.h2, by decide⟩
    simp [restrict, intVocab] at h1 h2
    simp [intC]; omega
  · rintro ⟨i, hi⟩
    cases i
    · refine ⟨(1, 0), fun ⟨j, hj⟩ hne => ?_, by simp [intC]⟩
      cases j
      · exact absurd rfl hne
      · simp [restrict, intVocab]
      · exact absurd rfl hj
    · refine ⟨(0, 1), fun ⟨j, hj⟩ hne => ?_, by simp [intC]⟩
      cases j
      · simp [restrict, intVocab]
      · exact absurd rfl hne
      · exact absurd rfl hj
    · exact absurd rfl hi
  · exact ⟨(0, 0), fun ⟨j, _⟩ => by cases j <;> simp [restrict, intVocab]⟩
  · have h3 := hp ⟨.h3, rfl⟩
    simp [restrict, intVocab] at h3
    simp [intC]; omega
  · rintro ⟨i, hi⟩
    subst hi
    exact ⟨(1, 0), fun ⟨j, hj⟩ hne => absurd (Subtype.ext hj) hne, by simp [intC]⟩
  · exact ⟨(0, 0), fun ⟨j, hj⟩ => by subst hj; simp [restrict, intVocab]⟩

/-- Counterexample for `hS` in `subfamily_eq_of_sufficient_of_irredundant_superfamily`: in
`x ≥ 1, x ≤ 1 ⊢ x = 1`, the full family `T` is irredundant (and sufficient), the subfamily
`S = {x ≥ 1}` is contained in it (and is itself irredundant and non-vacuous, but not
sufficient), and `S ≠ T`. So an irredundant family can strictly contain an irredundant
family that is not sufficient. -/
theorem subfamily_eq_ce_not_sufficient :
    Irredundant (restrict (fun _ : Two => True) pinH) pinC ∧
      (∀ i : Two, (fun j => j = Two.h1) i → (fun _ => True) i) ∧
      (fun j : Two => j = Two.h1) ≠ (fun _ => True) ∧
      Sufficient (restrict (fun _ : Two => True) pinH) pinC ∧
      Irredundant (restrict (fun j : Two => j = Two.h1) pinH) pinC ∧
      NonVacuous (restrict (fun j : Two => j = Two.h1) pinH) ∧
      ¬ Sufficient (restrict (fun j : Two => j = Two.h1) pinH) pinC := by
  refine ⟨?_, fun _ _ => trivial, fun h => ?_, fun x hx => sufficient_pin x
    (fun j => hx ⟨j, trivial⟩), ?_, ?_, fun h => ?_⟩
  · rintro ⟨i, _⟩
    cases i
    · exact ⟨0, fun ⟨j, _⟩ hne => by
        cases j
        · exact absurd rfl hne
        · simp [restrict, pinH], by simp [pinC]⟩
    · exact ⟨2, fun ⟨j, _⟩ hne => by
        cases j
        · simp [restrict, pinH]
        · exact absurd rfl hne, by simp [pinC]⟩
  · have := congrFun h .h2
    simp at this
  · rintro ⟨i, rfl⟩
    exact ⟨0, fun ⟨j, hj⟩ hne => absurd (Subtype.ext hj) hne, by simp [pinC]⟩
  · exact ⟨1, fun ⟨j, hj⟩ => by subst hj; simp [restrict, pinH]⟩
  · have := h 2 (fun ⟨j, hj⟩ => by subst hj; simp [restrict, pinH])
    simp [pinC] at this

/-- Counterexample for `hT` in `subfamily_eq_of_sufficient_of_irredundant_superfamily`:
with the valid conclusion, the empty subfamily is sufficient and contained in the (not
irredundant) one-member family `{True}`, but differs from it. -/
theorem subfamily_eq_ce_not_irredundant :
    Sufficient (restrict (fun _ : Unit => False) (single (trueC (M := Nat)))) trueC ∧
      (∀ i : Unit, (fun _ => False) i → (fun _ => True) i) ∧
      (fun _ : Unit => False) ≠ (fun _ => True) :=
  ⟨fun _ _ => trivial, fun _ h => h.elim, fun h => (congrFun h ()).mpr trivial⟩

/-- Counterexample for `hST` in `subfamily_eq_of_sufficient_of_irredundant_superfamily`:
for the duplicated hypotheses `x = 1, x = 1 ⊢ x = 1`, `{h2}` is sufficient and `{h1}` is
irredundant, but they differ. -/
theorem subfamily_eq_ce_not_contained :
    Sufficient (restrict (fun j => j = Two.h2) dupH) pinC ∧
      Irredundant (restrict (fun j => j = Two.h1) dupH) pinC ∧
      (fun j => j = Two.h2) ≠ (fun j => j = Two.h1) := by
  refine ⟨fun x hx => by simpa [restrict, dupH, pinC] using hx ⟨.h2, rfl⟩, ?_, fun h => ?_⟩
  · rintro ⟨i, hi⟩
    subst hi
    exact ⟨0, fun ⟨j, hj⟩ hne => absurd (Subtype.ext hj) hne, by simp [pinC]⟩
  · have := (congrFun h .h1).mpr rfl
    simp at this

/-- Non-vacuity for `subfamily_eq_of_sufficient_of_irredundant_superfamily`: all three
hypotheses hold with `S = T = {x ≤ 1, y ≤ 1}` over the vocabulary `sumVocab`. -/
theorem subfamily_eq_nonvacuity :
    Sufficient (restrict (fun j => j ≠ Three.h3) sumVocab) sumC ∧
      Irredundant (restrict (fun j => j ≠ Three.h3) sumVocab) sumC ∧
      (∀ i, (fun j => j ≠ Three.h3) i → (fun j => j ≠ Three.h3) i) :=
  ⟨irredundant_sufficient_subfamilies_of_sizes_two_and_one.2.1,
    irredundant_sufficient_subfamilies_of_sizes_two_and_one.2.2.1, fun _ h => h⟩

/-! ## Witnesses: ledgers and vacuity -/

/-- A complete tightness ledger does not certify non-vacuity, and non-vacuity certifies no
tightness. On `Fin 3`, `x = 1, x = 2 ⊢ False` is sufficient and irredundant but vacuous (and
so its family with the negated conclusion is not minimally unsatisfiable). Over `Unit`,
`True ⊢ True` is sufficient and non-vacuous but its only hypothesis is not tight. -/
theorem irredundant_vacuous_and_nonvacuous_tightless :
    (Sufficient vacH falseC ∧ Irredundant vacH falseC ∧ ¬ NonVacuous vacH ∧
      ¬ MinimalUnsatisfiable (withNegatedConclusion vacH falseC)) ∧
    (Sufficient topH trueC ∧ NonVacuous topH ∧ ∀ i, ¬ TightAt topH trueC i) := by
  refine ⟨⟨fun x hx => not_nonVacuous_vac ⟨x, hx⟩, ?_, not_nonVacuous_vac,
    not_minimalUnsatisfiable_vac⟩, fun _ _ => trivial, ⟨(), fun _ => trivial⟩, ?_⟩
  · intro i
    cases i
    · exact ⟨2, by simp [vacH], fun h => h⟩
    · exact ⟨1, by simp [vacH], fun h => h⟩
  · rintro i ⟨_, _, hc⟩
    exact hc trivial

/-! ## Witnesses: what one tight hypothesis certifies -/

/-- Counterexample for `h` in `not_valid_of_tightAt`: with the valid conclusion `True`, the
conclusion `¬ ∀ x, C x` fails. -/
theorem not_valid_of_tightAt_ce_not_tight : ¬ ¬ ∀ x : Unit, trueC x :=
  fun h => h fun _ => trivial

/-- Non-vacuity for `not_valid_of_tightAt`. -/
theorem not_valid_of_tightAt_nonvacuity : TightAt pinH pinC .h1 :=
  tightAt_pin_h1

/-- Invalidity over the model type is compatible with validity on an intended class: in
`x ≥ 1, x ≤ 1 ⊢ x ≤ 1` over `Nat`, the hypothesis `x ≤ 1` is tight (witness `x = 2`), and
the conclusion holds throughout the class `x ≤ 1`. -/
theorem tightAt_pinWeak_h2_conclusion_valid_on_bounded :
    TightAt pinH pinWeakC .h2 ∧ ∀ x, bounded x → pinWeakC x :=
  ⟨⟨2, fun j hj => by cases j; simp [pinH]; exact absurd rfl hj, by simp [pinWeakC]⟩,
    fun _ h => h⟩

/-! ## Witnesses: depth is not certified -/

/-- A sufficient, irredundant, non-vacuous ledger does not certify depth: the schema
`P ∨ C, ¬ P ⊢ C` is sufficient for every instantiation of the predicates `P` and `C` over
every model type `N : Type u` (it is a propositional tautology), yet for `P x := x.1 = true`
and `C x := x.2 = true` over `Bool × Bool` both hypotheses are tight and the family is
non-vacuous. -/
theorem schematic_ledger_irredundant_nonvacuous :
    (∀ (N : Type u) (P C : N → Prop), Sufficient (schemaH P C) C) ∧
    Irredundant (schemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true))
      (fun p => p.2 = true) ∧
    NonVacuous (schemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true)) := by
  refine ⟨fun N P C x hx => ?_, ?_, ⟨(false, true), by simp [schemaH]⟩⟩
  · have h1 := hx .h1
    have h2 := hx .h2
    simp [schemaH] at h1 h2
    exact h1.resolve_left h2
  · intro i
    cases i
    · exact ⟨(false, false), by simp [schemaH], by simp⟩
    · exact ⟨(true, false), by simp [schemaH], by simp⟩

/-- The propositional schema `P ∨ C, ¬ P ∨ C ⊢ C`. -/
def orSchemaH {M : Type u} (P C : M → Prop) : Two → M → Prop :=
  pair (fun x => P x ∨ C x) (fun x => ¬ P x ∨ C x)

/-- Adding necessity and unweakenability of every hypothesis still does not certify depth:
the schema `P ∨ C, ¬ P ∨ C ⊢ C` is sufficient for every instantiation over every model type
`N : Type u`, and for `P x := x.1 = true`, `C x := x.2 = true` over `Bool × Bool` it is
irredundant and non-vacuous, and every hypothesis is necessary and unweakenable. -/
theorem or_schema_irredundant_nonvacuous_necessary_unweakenable :
    (∀ (N : Type u) (P C : N → Prop), Sufficient (orSchemaH P C) C) ∧
    Irredundant (orSchemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true))
      (fun p => p.2 = true) ∧
    NonVacuous (orSchemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true)) ∧
    (∀ i, NecessaryAt (orSchemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true))
      (fun p => p.2 = true) i) ∧
    (∀ i, UnweakenableAt (orSchemaH (fun p : Bool × Bool => p.1 = true) (fun p => p.2 = true))
      (fun p => p.2 = true) i) := by
  have hnec : ∀ i, NecessaryAt (orSchemaH (fun p : Bool × Bool => p.1 = true)
      (fun p => p.2 = true)) (fun p => p.2 = true) i := fun i x hc => by
    cases i
    · exact Or.inr hc
    · exact Or.inr hc
  refine ⟨fun N P C x hx => ?_, fun i => ?_, ⟨(true, true), fun i => by cases i <;> simp [orSchemaH]⟩,
    hnec, fun i => unweakenableAt_of_necessaryAt (hnec i)⟩
  · have h1 := hx .h1
    have h2 := hx .h2
    simp only [orSchemaH, pair] at h1 h2
    exact h1.elim (fun hp => h2.elim (fun hnp => absurd hp hnp) id) id
  · cases i
    · exact ⟨(false, false), fun j hj => by cases j; exact absurd rfl hj; simp [orSchemaH],
        by simp⟩
    · exact ⟨(true, false), fun j hj => by cases j; simp [orSchemaH]; exact absurd rfl hj,
        by simp⟩

/-! ## Witnesses: hypotheses that restate the conclusion -/

/-- Counterexample for `hi` in `not_tightAt_of_ne_of_single_entails`: in
`x ≥ 1, x ≤ 1 ⊢ x = 1`, `h2 ≠ h1` and `h2` is tight (here `x ≥ 1` alone does not entail
`x = 1`). -/
theorem not_tightAt_of_ne_ce_not_entails : Two.h2 ≠ Two.h1 ∧ TightAt pinH pinC .h2 :=
  ⟨by simp, tightAt_pin_h2⟩

/-- Counterexample for `hj` in `not_tightAt_of_ne_of_single_entails`: the one-hypothesis
family `x = 1 ⊢ x = 1` has its hypothesis entail the conclusion, and that same hypothesis
is tight. -/
theorem not_tightAt_of_ne_ce_same_index :
    (∀ x, single pinC () x → pinC x) ∧ TightAt (single pinC) pinC () :=
  ⟨fun _ h => h, ⟨0, fun j hj => absurd (by cases j; rfl) hj, by simp [pinC]⟩⟩

/-- Non-vacuity for `not_tightAt_of_ne_of_single_entails`. -/
theorem not_tightAt_of_ne_nonvacuity : (∀ x, dupH .h1 x → pinC x) ∧ Two.h2 ≠ Two.h1 :=
  ⟨fun _ h => h, by simp⟩

/-- Counterexample for `hirr` in `not_single_entails_of_irredundant_of_exists_other`: in
`x = 1, True ⊢ x = 1` there is a second hypothesis and the first entails the conclusion. -/
theorem not_single_entails_ce_not_irredundant :
    (∃ j, j ≠ Two.h1) ∧ ∀ x, pair pinC trueC .h1 x → pinC x :=
  ⟨⟨.h2, by simp⟩, fun _ h => h⟩

/-- Counterexample for `hother` in `not_single_entails_of_irredundant_of_exists_other`: the
one-hypothesis family `x = 1 ⊢ x = 1` is irredundant and its hypothesis entails the
conclusion. -/
theorem not_single_entails_ce_single_hypothesis :
    Irredundant (single pinC) pinC ∧ ∀ x, single pinC () x → pinC x :=
  ⟨fun _ => not_tightAt_of_ne_ce_same_index.2, fun _ h => h⟩

/-- Non-vacuity for `not_single_entails_of_irredundant_of_exists_other`. -/
theorem not_single_entails_nonvacuity : Irredundant pinH pinC ∧ ∃ j, j ≠ Two.h1 :=
  ⟨irredundant_pin, ⟨.h2, by simp⟩⟩

/-- Hypotheses `x ≠ 2` and `x = 1 ∨ x = 2` over `Fin 3`. -/
def hatchH : Two → Fin 3 → Prop := pair (fun x => x ≠ 2) (fun x => x = 1 ∨ x = 2)

/-- Conclusion `x = 1` over `Fin 3`. -/
def hatchC : Fin 3 → Prop := fun x => x = 1

/-- An irredundant two-hypothesis family can contain a hypothesis that agrees with the
conclusion wherever another hypothesis holds: `x ≠ 2, (x = 1 ∨ x = 2) ⊢ x = 1` over `Fin 3`
is sufficient, irredundant (witnesses `2` and `0`), and non-vacuous (witness `1`), and on
the region `x ≠ 2` the hypothesis `x = 1 ∨ x = 2` is equivalent to the conclusion. -/
theorem irredundant_hypothesis_restates_conclusion_within_other :
    Sufficient hatchH hatchC ∧ Irredundant hatchH hatchC ∧ NonVacuous hatchH ∧
      ∀ x, hatchH .h1 x → (hatchH .h2 x ↔ hatchC x) := by
  have key : ∀ x : Fin 3, x ≠ 2 → ((x = 1 ∨ x = 2) ↔ x = 1) := by decide
  refine ⟨fun x hx => ?_, fun i => ?_, ⟨1, fun i => by cases i <;> simp [hatchH] <;> decide⟩,
    fun x h1 => key x h1⟩
  · exact (key x (hx .h1)).mp (hx .h2)
  · cases i
    · exact ⟨2, fun j hj => by cases j; exact absurd rfl hj; simp [hatchH],
        by simp [hatchC]⟩
    · exact ⟨0, fun j hj => by cases j; simp [hatchH]; exact absurd rfl hj,
        by simp [hatchC]⟩

end Toy.Ledger
