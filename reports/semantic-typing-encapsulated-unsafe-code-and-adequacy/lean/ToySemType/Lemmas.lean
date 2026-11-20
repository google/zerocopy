import ToySemType.Model

/-!
# Execution helper lemmas

Small lemmas for reasoning about all configurations reachable from a concrete
configuration, used by the fully proved examples and counterexamples.
-/

namespace Toy.SemType

open Expr

/-- One step of the per-heap body of `safeAndIn`. -/
theorem goodFrom_step {P : Nat → Expr → Prop} {e e₁ : Expr} {h h₁ : Heap}
    (hs : step e h = some (e₁, h₁))
    (k : ∀ e' h', Reaches (e₁, h₁) (e', h') →
      ¬ Stuck (e', h') ∧ (e'.isValue = true → P h'.length e')) :
    ∀ e' h', Reaches (e, h) (e', h') →
      ¬ Stuck (e', h') ∧ (e'.isValue = true → P h'.length e') := by
  intro e' h' hr
  rcases reaches_of_step (c := (e, h)) hs hr with heq | hr'
  · simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨not_stuck_of_step (c := (e', h')) hs, fun hv => ?_⟩
    simp [step_of_isValue hv] at hs
  · exact k e' h' hr'

/-- A value satisfies the per-heap body of `safeAndIn` iff it is in `P`. -/
theorem goodFrom_value {P : Nat → Expr → Prop} {e : Expr} {h : Heap}
    (hv : e.isValue = true) (hp : P h.length e) :
    ∀ e' h', Reaches (e, h) (e', h') →
      ¬ Stuck (e', h') ∧ (e'.isValue = true → P h'.length e') := by
  intro e' h' hr
  have := reaches_of_isValue hv hr
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  exact ⟨not_stuck_of_isValue hv, fun _ => hp⟩

/-- One step of the per-heap body of `valuesIn`. -/
theorem valFrom_step {P : Nat → Expr → Prop} {e e₁ : Expr} {h h₁ : Heap}
    (hs : step e h = some (e₁, h₁))
    (k : ∀ e' h', Reaches (e₁, h₁) (e', h') → e'.isValue = true → P h'.length e') :
    ∀ e' h', Reaches (e, h) (e', h') → e'.isValue = true → P h'.length e' := by
  intro e' h' hr hv
  rcases reaches_of_step (c := (e, h)) hs hr with heq | hr'
  · simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [step_of_isValue hv] at hs
  · exact k e' h' hr' hv

/-- A stuck configuration reaches no value. -/
theorem valFrom_stuck {P : Nat → Expr → Prop} {e : Expr} {h : Heap}
    (hst : Stuck (e, h)) :
    ∀ e' h', Reaches (e, h) (e', h') → e'.isValue = true → P h'.length e' := by
  intro e' h' hr hv
  cases hr with
  | refl => simp [Stuck] at hst; simp [hst] at hv
  | step hs _ => simp [Stuck] at hst; simp [hst.2] at hs

/-- A value is safe. -/
theorem safe_of_isValue {e : Expr} {h : Heap} (hv : e.isValue = true) : Safe (e, h) := by
  intro d hr
  rw [reaches_of_isValue hv hr]
  exact not_stuck_of_isValue hv

/-- Because `step` is deterministic, a configuration that reaches a value is
safe: no stuck configuration lies on (or beyond) its unique execution path. -/
theorem safe_of_reaches_value {c d : Config} (hr : Reaches c d) (hv : d.1.isValue = true) :
    Safe c := by
  induction hr with
  | refl c => exact safe_of_isValue (h := c.2) hv
  | step hs _ ih => exact safe_of_step hs (ih hv)

/-- Unfolding `safeAndIn`: reaching a stuck configuration from a heap with at
least `W` cells refutes `safeAndIn P W e`. -/
theorem not_safeAndIn_of_reaches_stuck {P : Nat → Expr → Prop} {W : Nat} {e : Expr}
    {h : Heap} {d : Config} (hW : W ≤ h.length) (hr : Reaches (e, h) d) (hs : Stuck d) :
    ¬ safeAndIn P W e := by
  intro hsafe
  exact (hsafe h hW d.1 d.2 hr).1 hs

/-- Unfolding `safeOnly`, likewise. -/
theorem not_safeOnly_of_reaches_stuck {P : Nat → Expr → Prop} {W : Nat} {e : Expr}
    {h : Heap} {d : Config} (hW : W ≤ h.length) (hr : Reaches (e, h) d) (hs : Stuck d) :
    ¬ safeOnly P W e := by
  intro hsafe
  exact hsafe h hW d hr hs

end Toy.SemType
