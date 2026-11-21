import ToyUpTo.LTS

/-!
# A toy process syntax: prefix, choice and inaction

Finite CCS-like terms `0`, `μ.P` (with `μ = none` the silent prefix τ) and
`P + Q`, with the usual structural operational semantics.  This is the only
concrete transition system used by the examples and counterexamples; it is
finite-state for every term (terms only shrink along transitions).
-/

namespace Toy.UpTo

universe v

/-- Process terms: inaction `0`, prefix `μ.P` and choice `P + Q`. -/
inductive Proc (L : Type v) where
  | nil : Proc L
  | pre : Option L → Proc L → Proc L
  | sum : Proc L → Proc L → Proc L
  deriving DecidableEq, Repr

namespace Proc

variable {L : Type v}

/-- The silent prefix `τ.P`. -/
abbrev tau (P : Proc L) : Proc L := .pre none P

/-- The visible prefix `a.P`. -/
abbrev act (a : L) (P : Proc L) : Proc L := .pre (some a) P

end Proc

open Proc

/-- Structural operational semantics: `μ.P -μ→ P`; `P + Q` moves as `P` or
as `Q`. -/
inductive PStep {L : Type v} : Proc L → Option L → Proc L → Prop
  | pre (μ : Option L) (P : Proc L) : PStep (.pre μ P) μ P
  | sumL {P Q P' : Proc L} {μ : Option L} : PStep P μ P' → PStep (.sum P Q) μ P'
  | sumR {P Q Q' : Proc L} {μ : Option L} : PStep Q μ Q' → PStep (.sum P Q) μ Q'

/-- Two visible labels, used by most concrete examples.  The weak failures do
not need two labels: they already occur over any non-empty label type
(`wbisim_not_sum_congruence_one_label`, `weak_upto_sum_context_unsound_one_label`,
and `weak_upto_expansion_commutes_counterexample` even over the empty one). -/
inductive Lbl where
  | a
  | b
  deriving DecidableEq, Repr

/-- Closure of a relation under `+`-contexts: the hole, closed terms, and
(nested) binary choice of such contexts.  Prefix contexts are *not*
included (with them the closure is no longer `sb`-compatible:
`prefix_context_not_compatible_sb`).  The closed-term constructor `refl` is
not needed for compatibility (`sumCloNoRefl_compatible_sb`); it is what lets
contexts such as `[·] + b.0` contain closed terms. -/
inductive SumClo {L : Type v} (R : Rel (Proc L)) : Rel (Proc L)
  | base {P Q : Proc L} : R P Q → SumClo R P Q
  | refl (P : Proc L) : SumClo R P P
  | sum {P₁ Q₁ P₂ Q₂ : Proc L} :
      SumClo R P₁ Q₁ → SumClo R P₂ Q₂ → SumClo R (.sum P₁ P₂) (.sum Q₁ Q₂)

/-! ### Inversion lemmas (fully proved) -/

section Inversion

variable {L : Type v}

theorem PStep.pre_inv {μ l : Option L} {P P' : Proc L} (h : PStep (.pre μ P) l P') :
    l = μ ∧ P' = P := by
  cases h
  exact ⟨rfl, rfl⟩

theorem PStep.sum_inv {l : Option L} {P Q X : Proc L} (h : PStep (.sum P Q) l X) :
    PStep P l X ∨ PStep Q l X := by
  cases h with
  | sumL h => exact Or.inl h
  | sumR h => exact Or.inr h

theorem PStep.nil_dead : ∀ (l : Option L) (P' : Proc L), ¬ PStep .nil l P' := by
  intro l P' h
  cases h

theorem PStep.act_noTau (a : L) (P : Proc L) : ∀ P', ¬ PStep (act a P) none P' := by
  intro P' h
  cases h

theorem PStep.sum_noTau {P Q : Proc L} (hP : ∀ P', ¬ PStep P none P')
    (hQ : ∀ Q', ¬ PStep Q none Q') : ∀ X, ¬ PStep (.sum P Q) none X := by
  intro X h
  rcases PStep.sum_inv h with h | h
  · exact hP _ h
  · exact hQ _ h

theorem PStep.sum_dead {P Q : Proc L} (hP : ∀ l P', ¬ PStep P l P')
    (hQ : ∀ l Q', ¬ PStep Q l Q') : ∀ l X, ¬ PStep (.sum P Q) l X := by
  intro l X h
  rcases PStep.sum_inv h with h | h
  · exact hP _ _ h
  · exact hQ _ _ h

end Inversion

end Toy.UpTo
