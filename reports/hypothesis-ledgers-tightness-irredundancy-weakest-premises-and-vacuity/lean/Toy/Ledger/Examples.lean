import Toy.Ledger.Core

/-!
# Running examples and definition tests

Small natural instances used throughout, and, for every core definition, at least one
proved positive example (an intended instance it admits) and one proved negative example
(an instance it must reject).
-/

namespace Toy.Ledger

universe u

/-! ## Running example families -/

/-- Hypotheses of `x ≥ 1, x ≤ 1 ⊢ x = 1` over `Nat`. -/
def pinH : Two → Nat → Prop := pair (fun x => 1 ≤ x) (fun x => x ≤ 1)

/-- Conclusion `x = 1`. -/
def pinC : Nat → Prop := fun x => x = 1

/-- The weaker conclusion `x ≤ 1`, which merely restates hypothesis `h2` of `pinH`. -/
def pinWeakC : Nat → Prop := fun x => x ≤ 1

/-- Hypotheses of `x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2` over `Nat × Nat`. -/
def sumH : Two → Nat × Nat → Prop := pair (fun p => p.1 ≤ 1) (fun p => p.2 ≤ 1)

/-- Conclusion `x + y ≤ 2`. -/
def sumC : Nat × Nat → Prop := fun p => p.1 + p.2 ≤ 2

/-- A duplicated hypothesis: `x = 1, x = 1 ⊢ x = 1` (with conclusion `pinC`). -/
def dupH : Two → Nat → Prop := pair (fun x => x = 1) (fun x => x = 1)

/-- Hypotheses of `x = 0, y = 0 ⊢ x = y` over `Nat × Nat`. -/
def eqH : Two → Nat × Nat → Prop := pair (fun p => p.1 = 0) (fun p => p.2 = 0)

/-- Conclusion `x = y`. -/
def eqC : Nat × Nat → Prop := fun p => p.1 = p.2

/-- Hypotheses of `x = 0, (x = 0 ∧ y = 0) ⊢ x = y`: the first is entailed by the second. -/
def entH : Two → Nat × Nat → Prop := pair (fun p => p.1 = 0) (fun p => p.1 = 0 ∧ p.2 = 0)

/-- On `Fin 3`, the jointly unsatisfiable hypotheses `x = 1, x = 2`. -/
def vacH : Two → Fin 3 → Prop := pair (fun x => x = 1) (fun x => x = 2)

/-- The unsatisfiable conclusion. -/
def falseC {M : Type u} : M → Prop := fun _ => False

/-- The valid conclusion. -/
def trueC {M : Type u} : M → Prop := fun _ => True

/-- Two independent coordinate bits over `Bool × Bool`. -/
def bitsH : Two → Bool × Bool → Prop := pair (fun p => p.1 = true) (fun p => p.2 = true)

/-- The propositional schema `P ∨ C, ¬ P ⊢ C` instantiated with predicates `P` and `C`. -/
def schemaH {M : Type u} (P C : M → Prop) : Two → M → Prop :=
  pair (fun x => P x ∨ C x) (fun x => ¬ P x)

/-- A vocabulary of three candidate hypotheses over `Nat × Nat`:
`x ≤ 1`, `y ≤ 1`, `x + y ≤ 2`. -/
def sumVocab : Three → Nat × Nat → Prop :=
  triple (fun p => p.1 ≤ 1) (fun p => p.2 ≤ 1) (fun p => p.1 + p.2 ≤ 2)

/-- The reference class `x ≤ 1` of natural numbers. -/
def bounded : Nat → Prop := fun x => x ≤ 1

/-! ## `Sufficient` -/

theorem sufficient_pin : Sufficient pinH pinC := by
  intro x hx
  simp [pinH] at hx
  simp [pinC]; omega

theorem not_sufficient_single_le_one : ¬ Sufficient (single fun x : Nat => x ≤ 1) pinC := by
  intro h
  have := h 0 (by simp)
  simp [pinC] at this

/-! ## `TightAt` -/

theorem tightAt_pin_h1 : TightAt pinH pinC .h1 :=
  ⟨0, by simp [pinH], by simp [pinC]⟩

theorem tightAt_pin_h2 : TightAt pinH pinC .h2 :=
  ⟨2, by simp [pinH], by simp [pinC]⟩

theorem not_tightAt_pinWeak_h1 : ¬ TightAt pinH pinWeakC .h1 := by
  rintro ⟨x, hx, hc⟩
  simp [pinH] at hx
  exact hc hx

/-! ## `Irredundant` -/

theorem irredundant_pin : Irredundant pinH pinC := by
  intro i
  cases i
  · exact tightAt_pin_h1
  · exact tightAt_pin_h2

theorem not_irredundant_dup : ¬ Irredundant dupH pinC := by
  intro h
  obtain ⟨x, hx, hc⟩ := h .h1
  simp [dupH] at hx
  exact hc hx

/-! ## `NonVacuous` -/

theorem nonVacuous_pin : NonVacuous pinH :=
  ⟨1, by simp [pinH]⟩

theorem not_nonVacuous_vac : ¬ NonVacuous vacH := by
  rintro ⟨x, hx⟩
  simp [vacH] at hx
  rw [hx.1] at hx
  exact absurd hx.2 (by decide)

/-! ## `NecessaryAt` -/

theorem necessaryAt_pin_h1 : NecessaryAt pinH pinC .h1 := by
  intro x hx
  simp [pinC] at hx
  simp [pinH]; omega

theorem not_necessaryAt_sum_h1 : ¬ NecessaryAt sumH sumC .h1 := by
  intro h
  have := h (2, 0) (by simp [sumC])
  simp [sumH] at this

/-! ## `UnweakenableAt` -/

theorem unweakenableAt_pin_h1 : UnweakenableAt pinH pinC .h1 := by
  intro x _ hc
  simp [pinC] at hc
  simp [pinH]; omega

theorem not_unweakenableAt_sum_h1 : ¬ UnweakenableAt sumH sumC .h1 := by
  intro h
  have := h (2, 0) (by simp [sumH]) (by simp [sumC])
  simp [sumH] at this

/-! ## `Independent` -/

theorem independent_bits : Independent bitsH := by
  intro s
  exact ⟨(s .h1, s .h2), by simp [bitsH]⟩

theorem not_independent_pin : ¬ Independent pinH := by
  intro h
  obtain ⟨x, hx⟩ := h (fun _ => false)
  simp [pinH] at hx
  omega

/-! ## `IsolatingAt` -/

theorem isolatingAt_pin_h1 : IsolatingAt pinH .h1 :=
  ⟨0, by simp [pinH], by simp [pinH]⟩

theorem not_isolatingAt_dup_h1 : ¬ IsolatingAt dupH .h1 := by
  rintro ⟨x, hn, hx⟩
  simp [dupH] at hn hx
  exact hn hx

/-! ## `restrict` -/

theorem sufficient_restrict_sumVocab_h1h2 :
    Sufficient (restrict (fun j => j ≠ .h3) sumVocab) sumC := by
  intro p hp
  have h1 := hp ⟨.h1, by simp⟩
  have h2 := hp ⟨.h2, by simp⟩
  simp [restrict, sumVocab] at h1 h2
  simp [sumC]; omega

theorem not_sufficient_restrict_sumVocab_h1 :
    ¬ Sufficient (restrict (fun j => j = .h1) sumVocab) sumC := by
  intro h
  have := h (0, 5) (fun ⟨j, hj⟩ => by subst hj; simp [restrict, sumVocab])
  simp [sumC] at this

/-! ## `MinimalUnsatisfiable` and `withNegatedConclusion` -/

theorem minimalUnsatisfiable_pin : MinimalUnsatisfiable (withNegatedConclusion pinH pinC) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    have h0 := hx none
    have h1 := hx (some .h1)
    have h2 := hx (some .h2)
    simp [withNegatedConclusion, pinH, pinC] at h0 h1 h2
    omega
  · rintro S ⟨k, hk⟩
    rcases k with _ | k
    · refine ⟨1, fun ⟨j, hj⟩ => ?_⟩
      rcases j with _ | j
      · exact absurd hj hk
      · cases j <;> simp [restrict, withNegatedConclusion, pinH]
    · cases k
      · refine ⟨0, fun ⟨j, hj⟩ => ?_⟩
        rcases j with _ | j
        · simp [restrict, withNegatedConclusion, pinC]
        · cases j
          · exact absurd hj hk
          · simp [restrict, withNegatedConclusion, pinH]
      · refine ⟨2, fun ⟨j, hj⟩ => ?_⟩
        rcases j with _ | j
        · simp [restrict, withNegatedConclusion, pinC]
        · cases j
          · simp [restrict, withNegatedConclusion, pinH]
          · exact absurd hj hk

/-- Rejected: the family `{x = 1, x = 2, ¬ False}` is unsatisfiable, but deleting the
negated conclusion leaves the still-unsatisfiable `{x = 1, x = 2}`. -/
theorem not_minimalUnsatisfiable_vac : ¬ MinimalUnsatisfiable (withNegatedConclusion vacH falseC) := by
  rintro ⟨_, hmin⟩
  obtain ⟨x, hx⟩ := hmin (fun k => k ≠ none) ⟨none, fun h => h rfl⟩
  have h1 := hx ⟨some .h1, by simp⟩
  have h2 := hx ⟨some .h2, by simp⟩
  simp [restrict, withNegatedConclusion, vacH] at h1 h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ## Relativized notions -/

theorem sufficientIn_bounded_single : SufficientIn bounded (single fun x : Nat => 1 ≤ x) pinC := by
  intro x hb hx
  simp [bounded] at hb
  simp at hx
  simp [pinC]; omega

theorem not_sufficientIn_true_single : ¬ SufficientIn trueC (single fun x : Nat => 1 ≤ x) pinC := by
  intro h
  have := h 2 trivial (by simp)
  simp [pinC] at this

theorem tightIn_true_pin_h2 : TightIn trueC pinH pinC .h2 :=
  ⟨2, trivial, by simp [pinH], by simp [pinC]⟩

theorem not_tightIn_bounded_pin_h2 : ¬ TightIn bounded pinH pinC .h2 := by
  rintro ⟨x, hb, hx, hc⟩
  simp [bounded] at hb
  simp [pinH] at hx
  simp [pinC] at hc
  omega

theorem harmlessIn_bounded_pin_h2 : HarmlessIn bounded pinH .h2 := by
  intro x hb
  simpa [pinH, bounded] using hb

theorem not_harmlessIn_true_pin_h2 : ¬ HarmlessIn trueC pinH .h2 := by
  intro h
  have := h 2 trivial
  simp [pinH] at this

/-- The class `x = 0` contains no model of `pinH`. -/
def zeroClass : Nat → Prop := fun x => x = 0

theorem nonVacuousIn_bounded_pin : NonVacuousIn bounded pinH :=
  ⟨1, by simp [bounded], by simp [pinH]⟩

theorem not_nonVacuousIn_zeroClass_pin : ¬ NonVacuousIn zeroClass pinH := by
  rintro ⟨x, hx, hall⟩
  simp [zeroClass] at hx
  subst hx
  simp [pinH] at hall

/-! ## `replaceAt` and `WeakestPremise` -/

theorem sufficient_replaceAt_sum_h1_by_sumC : Sufficient (replaceAt sumH .h1 sumC) sumC :=
  fun _ hp => (replaceAt_self _ _ _ _).mp (hp .h1)

theorem not_sufficient_replaceAt_sum_h1_by_true : ¬ Sufficient (replaceAt sumH .h1 trueC) sumC := by
  intro h
  have := h (5, 0) (fun j => by
    cases j
    · exact (replaceAt_self _ _ _ _).mpr trivial
    · exact (replaceAt_of_ne _ _ (by decide) _).mpr (by simp [sumH]))
  simp [sumC] at this

/-- The weakest replacement for `x ≤ 1` in `x ≤ 1, y ≤ 1 ⊢ x + y ≤ 2` admits `(2, 0)`,
where `x ≤ 1` itself fails. -/
theorem weakestPremise_sum_h1_at_2_0 :
    WeakestPremise sumH sumC .h1 (2, 0) ∧ ¬ sumH .h1 (2, 0) := by
  refine ⟨fun _ => by simp [sumC], by simp [sumH]⟩

/-- ... and rejects `(5, 0)`. -/
theorem not_weakestPremise_sum_h1_at_5_0 : ¬ WeakestPremise sumH sumC .h1 (5, 0) := by
  intro h
  have := h (by simp [sumH])
  simp [sumC] at this

end Toy.Ledger
