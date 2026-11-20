import ToySemType.Lemmas
import ToySemType.Programs

/-!
# Concrete semantic facts (fully proved)

Execution analyses of the concrete programs, used by the results, the
counterexamples, and the definition examples.
-/

namespace Toy.SemType

open Expr

/-- Every execution of `checkedBody n`, from any heap, is safe and ends (if at
all) in a word. -/
theorem checkedBody_good (n : Nat) (h : Heap) :
    ∀ e' h', Reaches (checkedBody n, h) (e', h') →
      ¬ Stuck (e', h') ∧ (e'.isValue = true → V Recipe.std .int h'.length e') := by
  apply goodFrom_step (e₁ := .ifz (.lt (.num n) (.num h.length)) (.num 0) (.read (.cast (.num n))))
    (h₁ := h) rfl
  apply goodFrom_step
    (e₁ := .ifz (.num (if n < h.length then 1 else 0)) (.num 0) (.read (.cast (.num n))))
    (h₁ := h) rfl
  by_cases hn : n < h.length
  · simp only [hn, ↓reduceIte]
    apply goodFrom_step (e₁ := .read (.cast (.num n))) (h₁ := h) rfl
    apply goodFrom_step (e₁ := .read (.loc n)) (h₁ := h) rfl
    apply goodFrom_step (e₁ := .num h[n]) (h₁ := h)
      (by simp [step, Expr.isValue, List.getElem?_eq_getElem hn])
    exact goodFrom_value rfl ⟨_, rfl⟩
  · simp only [hn, ↓reduceIte]
    apply goodFrom_step (e₁ := .num 0) (h₁ := h) rfl
    exact goodFrom_value rfl ⟨_, rfl⟩

/-- `checkedRead` is in the standard value interpretation of `int ⇒ int` at every world. -/
theorem checkedRead_V (W : Nat) : V Recipe.std (.arrow .int .int) W checkedRead := by
  refine ⟨_, rfl, rfl, fun W' _ v hv => ?_⟩
  obtain ⟨n, rfl⟩ := hv
  intro h _
  exact checkedBody_good n h

/-- **Encapsulation, concrete instance.** The bounds-checked raw read is
semantically well typed at `int ⇒ int`. -/
theorem checkedRead_semTyped : SemTyped Recipe.std [] checkedRead (.arrow .int .int) := by
  rw [semTyped_nil_iff]
  intro W h _
  exact goodFrom_value rfl (checkedRead_V h.length)

/-- A non-value use of the encapsulated library is semantically well typed. -/
theorem checkedRead_applied_semTyped (n : Nat) :
    SemTyped Recipe.std [] (.app checkedRead (.num n)) .int := by
  rw [semTyped_nil_iff]
  intro W h _
  exact goodFrom_step (e₁ := checkedBody n) (h₁ := h) rfl (checkedBody_good n h)

/-! ## The diverging term -/

theorem omega_step (h : Heap) : step omegaExpr h = some (omegaExpr, h) := rfl

/-- `omegaExpr` only ever reaches itself. -/
theorem omega_reaches_self {h : Heap} {d : Config} (hr : Reaches (omegaExpr, h) d) :
    d = (omegaExpr, h) := by
  suffices ∀ c d, Reaches c d → c = (omegaExpr, h) → d = (omegaExpr, h) from
    this _ _ hr rfl
  intro c d hrc hc
  induction hrc with
  | refl => exact hc
  | step hs _ ih =>
    subst hc
    rw [omega_step] at hs
    cases hs
    exact ih rfl

/-- Every execution of `omegaExpr` is safe and reaches no value. -/
theorem omega_good {P : Nat → Expr → Prop} (h : Heap) :
    ∀ e' h', Reaches (omegaExpr, h) (e', h') →
      ¬ Stuck (e', h') ∧ (e'.isValue = true → P h'.length e') := by
  intro e' h' hr
  have heq := omega_reaches_self hr
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨not_stuck_of_step (c := (omegaExpr, h')) (omega_step h'), fun hv => by cases hv⟩

/-- Every type is inhabited in the standard value interpretation at world 1
(at arrow types by `λ _. omegaExpr`). -/
theorem V_std_inhabited_one (τ : Ty) : ∃ v, V Recipe.std τ 1 v := by
  cases τ with
  | int => exact ⟨.num 0, 0, rfl⟩
  | ref => exact ⟨.loc 0, 0, rfl, Nat.zero_lt_one⟩
  | arrow σ ρ =>
    refine ⟨.lam omegaExpr, omegaExpr, rfl, rfl, fun W' _ v _ h _ => ?_⟩
    show ∀ e' h', Reaches (substAt 0 v omegaExpr, h) (e', h') → _
    have hsub : substAt 0 v omegaExpr = omegaExpr := rfl
    rw [hsub]
    exact omega_good h

end Toy.SemType
