/-
The easy half of an adequacy argument for the toy: every operational step is
reflected in the step-counting denotation (values agree, tick counts do not
increase and drop by at most one per step). The converse half — computational
adequacy, from denotations back to operational termination — is not mechanized.

Toy model.
-/
import Toy.Operational

namespace Toy

/-- How one operational step may change a denotation: at computation types the
result is unchanged and the tick count stays or drops by one; elsewhere nothing
changes. -/
def StepRel : (A : Ty) → A.den → A.den → Prop
  | Ty.comp _, r, r' => r.2 = r'.2 ∧ (r.1 = r'.1 ∨ r.1 = r'.1 + 1)
  | Ty.nat, x, y => x = y
  | Ty.arr _ _, f, g => f = g

theorem StepRel.of_eq {A : Ty} {x y : A.den} (h : x = y) : StepRel A x y := by
  subst h
  cases A with
  | nat => exact rfl
  | arr _ _ => exact rfl
  | comp _ => exact ⟨rfl, Or.inl rfl⟩

/-- Soundness of one step with respect to the denotation. -/
theorem Step.sound {A : Ty} {e e' : Tm [] A} (h : Step e e') (γ : Env []) :
    StepRel A (e.eval γ) (e'.eval γ) := by
  induction h with
  | beta b a => exact StepRel.of_eq ((Conv.beta b a).sound γ)
  | @appL A B f f' a _ ih =>
    have e : f.eval γ = f'.eval γ := ih
    apply StepRel.of_eq
    show f.eval γ (a.eval γ) = f'.eval γ (a.eval γ)
    rw [e]
  | bindRet a v => exact StepRel.of_eq ((Conv.bind_ret a v).sound γ)
  | @bindL A B u u' v _ ih =>
    have ih' : (u.eval γ).2 = (u'.eval γ).2 ∧
        ((u.eval γ).1 = (u'.eval γ).1 ∨ (u.eval γ).1 = (u'.eval γ).1 + 1) := ih
    obtain ⟨h₂, h₁⟩ := ih'
    show (bindSem (u.eval γ) fun a => v.eval (Env.cons a γ)).2
          = (bindSem (u'.eval γ) fun a => v.eval (Env.cons a γ)).2 ∧
        ((bindSem (u.eval γ) fun a => v.eval (Env.cons a γ)).1
            = (bindSem (u'.eval γ) fun a => v.eval (Env.cons a γ)).1 ∨
         (bindSem (u.eval γ) fun a => v.eval (Env.cons a γ)).1
            = (bindSem (u'.eval γ) fun a => v.eval (Env.cons a γ)).1 + 1)
    simp only [bindSem, h₂]
    refine ⟨trivial, ?_⟩
    cases h₁ with
    | inl h => left; omega
    | inr h => right; omega
  | tick e => exact ⟨rfl, Or.inr rfl⟩

/-- Reflexive–transitive closure of `Step`. -/
inductive Steps : {A : Ty} → Tm [] A → Tm [] A → Prop where
  | refl {A : Ty} (e : Tm [] A) : Steps e e
  | cons {A : Ty} {e e' e'' : Tm [] A} : Step e e' → Steps e' e'' → Steps e e''

/-- How an execution may change a denotation: at computation types the result is
unchanged and the tick count does not increase; elsewhere nothing changes. -/
def StepsRel : (A : Ty) → A.den → A.den → Prop
  | Ty.comp _, r, r' => r.2 = r'.2 ∧ r'.1 ≤ r.1
  | Ty.nat, x, y => x = y
  | Ty.arr _ _, f, g => f = g

theorem StepsRel.refl {A : Ty} (x : A.den) : StepsRel A x x := by
  cases A with
  | nat => exact rfl
  | arr _ _ => exact rfl
  | comp _ => exact ⟨rfl, Nat.le_refl _⟩

theorem StepsRel.cons {A : Ty} {x y z : A.den} (h₁ : StepRel A x y) (h₂ : StepsRel A y z) :
    StepsRel A x z := by
  cases A with
  | nat => exact Eq.trans h₁ h₂
  | arr _ _ => exact Eq.trans h₁ h₂
  | comp X =>
    have h₁' : x.2 = y.2 ∧ (x.1 = y.1 ∨ x.1 = y.1 + 1) := h₁
    have h₂' : y.2 = z.2 ∧ z.1 ≤ y.1 := h₂
    refine ⟨h₁'.1.trans h₂'.1, ?_⟩
    show z.1 ≤ x.1
    cases h₁'.2 with
    | inl h => omega
    | inr h => omega

/-- Soundness of executions with respect to the denotation, at every type. -/
theorem Steps.sound {A : Ty} {e e' : Tm [] A} (h : Steps e e') (γ : Env []) :
    StepsRel A (e.eval γ) (e'.eval γ) := by
  induction h with
  | refl e => exact StepsRel.refl _
  | cons hs _ ih => exact StepsRel.cons (hs.sound γ) ih

/-- Soundness of executions at computation type: if `e ⟶* e'` then both denote
the same result, and `e'` needs no more ticks than `e`. -/
theorem Steps.sound_comp {X : Ty} {e e' : Tm [] (Ty.comp X)} (h : Steps e e') (γ : Env []) :
    (e.eval γ).2 = (e'.eval γ).2 ∧ (e'.eval γ).1 ≤ (e.eval γ).1 :=
  h.sound γ

/-- If a closed computation reduces to `ret v`, the denotation's result component
is the denotation of `v` (operational result ⇒ denotational result). -/
theorem Steps.ret_sound {X : Ty} {e : Tm [] (Ty.comp X)} {v : Tm [] X}
    (h : Steps e (Tm.ret v)) (γ : Env []) : (e.eval γ).2 = v.eval γ :=
  (h.sound_comp γ).1

end Toy
