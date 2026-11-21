import ToyUnits.Syntax

/-!
# Plain reading = invariance among positive unit systems (framing result)

A *situation* is a pair `(s, ρ)` of a unit system `s` with positive factors and the readings `ρ`
of all variables in it. One unit-change step goes from `(s, ρ)` to
`(fun i => t i * s i, actEnv Γ t ρ)` for a positive `t`, provided the new system is positive.
A *physical situation* is a class of the quotient of situations by these steps. A formula has a
*plain reading* if its truth at a situation is a predicate of the physical situation alone.
-/

namespace Toy.Units

variable {m : Nat} {K : Type} [ScalarOps K]

/-- A situation: a unit system with positive factors, and the readings of all variables in it. -/
abbrev PosSituation (m : Nat) (K : Type) [ScalarOps K] : Type :=
  {p : (Fin m → K) × Env K // Positive p.1}

/-- One positive unit change, from situation `p` to situation `q`. -/
def unitChangeStep (Γ : Ctx m) (p q : PosSituation m K) : Prop :=
  ∃ t : Fin m → K, Positive t ∧ q.1 = ((fun i => t i * p.1.1 i), actEnv Γ t p.1.2)

/-- `φ` has a plain reading: some predicate `R` on physical situations (the quotient of
situations by unit-change steps) gives the truth value of `φ` at every situation. -/
def HasPlainReading (Γ : Ctx m) (φ : Formula m K) : Prop :=
  ∃ R : Quot (unitChangeStep (K := K) Γ) → Prop,
    ∀ p : PosSituation m K, Formula.holdsIn p.1.1 p.1.2 φ ↔ R (Quot.mk _ p)

/-- **Plain reading ⇔ invariance among positive unit systems.** For every context and formula,
and with no law assumed of the scalars, `φ` has a plain reading exactly when it keeps its truth
value under every positive unit change between positive unit systems. -/
theorem hasPlainReading_iff_posUnitInvariant (Γ : Ctx m) (φ : Formula m K) :
    HasPlainReading Γ φ ↔ PosUnitInvariant Γ φ := by
  constructor
  · rintro ⟨R, hR⟩ t s ρ ht hs hts
    have e : Quot.mk (unitChangeStep (K := K) Γ) ⟨(s, ρ), hs⟩ =
        Quot.mk _ ⟨((fun i => t i * s i), actEnv Γ t ρ), hts⟩ := Quot.sound ⟨t, ht, rfl⟩
    rw [hR ⟨((fun i => t i * s i), actEnv Γ t ρ), hts⟩, hR ⟨(s, ρ), hs⟩, e]
  · intro h
    refine ⟨Quot.lift (fun p : PosSituation m K => Formula.holdsIn p.1.1 p.1.2 φ) ?_,
      fun p => Iff.rfl⟩
    rintro ⟨⟨s, ρ⟩, hs⟩ ⟨q, hq⟩ ⟨t, ht, e⟩
    simp only at e
    subst e
    exact propext (h t s ρ ht hs hq).symm

end Toy.Units
