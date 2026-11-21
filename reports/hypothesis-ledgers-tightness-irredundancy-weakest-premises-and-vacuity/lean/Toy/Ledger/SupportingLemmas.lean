import Toy.Ledger.Strength

/-!
# Supporting lemmas for two remarks in the cards

Two groups of small lemmas:

* On `True ⊢ False` over `Unit` (the counterexample instance `topH`, `falseC` for the
  sufficiency hypothesis of `unweakenableAt_characterizations_of_sufficient`), the first and
  the third characterizations fail separately, each as an equivalence on its own.
* "The antecedent holds at every model" and `NonVacuous` ("some model satisfies the
  antecedent") compare as follows: on a nonempty model type the first implies the second; the
  second does not imply the first; and over the empty model type the first holds (vacuously)
  for the family `True` while the second fails.
-/

namespace Toy.Ledger

universe u v

/-! ## Result 11: the first and third characterizations fail on `True ⊢ False` -/

/-- On `True ⊢ False` over `Unit` the first characterization of
`unweakenableAt_characterizations_of_sufficient` fails: its left side (unweakenability) holds
and its right side (agreement with the weakest premise) fails. -/
theorem unweakenableAt_first_characterization_fails_true_false :
    ¬ (UnweakenableAt topH falseC () ↔
        ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ WeakestPremise topH falseC () x)) :=
  fun h => unweakenableAt_true_false_disagrees.2 (h.mp unweakenableAt_true_false_disagrees.1)

/-- On `True ⊢ False` over `Unit` the third characterization of
`unweakenableAt_characterizations_of_sufficient` fails: its left side (unweakenability) holds
and its right side (agreement of the hypothesis `True` with the conclusion `False`) fails. -/
theorem unweakenableAt_third_characterization_fails_true_false :
    ¬ (UnweakenableAt topH falseC () ↔
        ∀ x, (∀ j, j ≠ () → topH j x) → (topH () x ↔ falseC x)) := by
  intro h
  have hagree := h.mp unweakenableAt_true_false_disagrees.1
  exact (hagree () (fun j hj => absurd (by cases j; rfl) hj)).mp trivial

/-! ## An antecedent that holds everywhere versus `NonVacuous` -/

/-- On a nonempty model type, a family whose members hold at every model is non-vacuous. -/
theorem nonVacuous_of_forall_of_nonempty {M : Type u} {ι : Type v} [hne : Nonempty M]
    {H : ι → M → Prop} (h : ∀ x, ∀ i, H i x) : NonVacuous H :=
  match hne with
  | ⟨x⟩ => ⟨x, h x⟩

/-- The converse fails: `x ≥ 1, x ≤ 1` over `Nat` is non-vacuous, but the antecedent fails at
`x = 0`. -/
theorem nonVacuous_pin_antecedent_not_everywhere :
    NonVacuous pinH ∧ ¬ ∀ x, ∀ i, pinH i x := by
  refine ⟨nonVacuous_pin, fun h => ?_⟩
  have := h 0 .h1
  simp [pinH, pair] at this

/-- Over the empty model type the antecedent `True` holds at every model (vacuously), and the
family is not non-vacuous. -/
theorem antecedent_everywhere_not_nonVacuous_empty :
    (∀ x : Empty, ∀ i, single (fun (_ : Empty) => True) i x) ∧
      ¬ NonVacuous (single (fun (_ : Empty) => True)) :=
  ⟨fun x => x.elim, fun ⟨x, _⟩ => x.elim⟩

end Toy.Ledger
