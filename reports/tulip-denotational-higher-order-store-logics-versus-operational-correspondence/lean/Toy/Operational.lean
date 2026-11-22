/-
(b) The operational contrast: a step-indexed weakest precondition over *raw
expressions* and a small-step relation. Its bind rule is a theorem only under
explicit context-lifting laws; a context whose hole is under a binder violates
those laws, and the bind rule's conclusion is then false.

Toy model. The operational semantics is a call-by-name small-step reduction on
the closed terms of `Toy.Syntax`.
-/
import Toy.Logic

namespace Toy

theorem ff_ne_tt {P : Prop} (h : false = true) : P := by cases h
theorem tt_ne_ff {P : Prop} (h : true = false) : P := by cases h

/-- An operational language: raw expressions, a value test, a small-step relation. -/
structure Lang where
  Expr : Type
  isVal : Expr → Bool
  step : Expr → Expr → Prop
  val_stuck : ∀ {e e' : Expr}, step e e' → isVal e = false

/-- Step-indexed operational weakest precondition (postcondition on termination,
plus progress). Every reduction step consumes one index; postconditions range over raw
expressions. -/
def wpo (L : Lang) : Nat → L.Expr → (L.Expr → Nat → Prop) → Prop
  | 0, e, Φ => (L.isVal e = true → Φ e 0) ∧ (L.isVal e = false → ∃ e', L.step e e')
  | n + 1, e, Φ =>
      (L.isVal e = true → Φ e (n + 1)) ∧
      (L.isVal e = false → (∃ e', L.step e e') ∧ ∀ e', L.step e e' → wpo L n e' Φ)

theorem wpo_zero (L : Lang) (e : L.Expr) (Φ : L.Expr → Nat → Prop) :
    wpo L 0 e Φ ↔ ((L.isVal e = true → Φ e 0) ∧ (L.isVal e = false → ∃ e', L.step e e')) :=
  Iff.rfl

theorem wpo_succ (L : Lang) (n : Nat) (e : L.Expr) (Φ : L.Expr → Nat → Prop) :
    wpo L (n + 1) e Φ ↔
      ((L.isVal e = true → Φ e (n + 1)) ∧
       (L.isVal e = false → (∃ e', L.step e e') ∧ ∀ e', L.step e e' → wpo L n e' Φ)) :=
  Iff.rfl

/-- The context-lifting laws an operational bind rule needs: the context must be
uniform with respect to reduction (it neither creates values, nor blocks steps of
its hole, nor steps on its own while the hole is a non-value). -/
structure CtxLaws (L₁ L₂ : Lang) (K : L₁.Expr → L₂.Expr) : Prop where
  fill_not_val : ∀ {e : L₁.Expr}, L₁.isVal e = false → L₂.isVal (K e) = false
  fill_step : ∀ {e e' : L₁.Expr}, L₁.step e e' → L₂.step (K e) (K e')
  fill_step_inv : ∀ {e : L₁.Expr} {e₂ : L₂.Expr}, L₁.isVal e = false → L₂.step (K e) e₂ →
    ∃ e', e₂ = K e' ∧ L₁.step e e'

/-- (b, positive half) The operational bind rule, *assuming* the context laws. -/
theorem wpo_bind {L₁ L₂ : Lang} {K : L₁.Expr → L₂.Expr} (hK : CtxLaws L₁ L₂ K)
    (Φ : L₂.Expr → Nat → Prop) :
    ∀ n e, wpo L₁ n e (fun v m => wpo L₂ m (K v) Φ) → wpo L₂ n (K e) Φ := by
  intro n
  induction n with
  | zero =>
    intro e H
    have H' := (wpo_zero _ _ _).1 H
    cases hv : L₁.isVal e with
    | true => exact H'.1 hv
    | false =>
      have hKv := hK.fill_not_val hv
      refine (wpo_zero _ _ _).2 ⟨fun h => ?_, fun _ => ?_⟩
      · rw [hKv] at h; exact ff_ne_tt h
      · obtain ⟨e', he'⟩ := H'.2 hv
        exact ⟨K e', hK.fill_step he'⟩
  | succ n ih =>
    intro e H
    have H' := (wpo_succ _ _ _ _).1 H
    cases hv : L₁.isVal e with
    | true => exact H'.1 hv
    | false =>
      have hKv := hK.fill_not_val hv
      obtain ⟨⟨e', he'⟩, Hall⟩ := H'.2 hv
      refine (wpo_succ _ _ _ _).2 ⟨fun h => ?_, fun _ => ⟨⟨K e', hK.fill_step he'⟩, ?_⟩⟩
      · rw [hKv] at h; exact ff_ne_tt h
      · intro e₂ h₂
        obtain ⟨e'', rfl, hs⟩ := hK.fill_step_inv hv h₂
        exact ih e'' (Hall e'' hs)

/-! ### The closed-term instance -/

def Tm.isVal : {Γ : Ctx} → {A : Ty} → Tm Γ A → Bool
  | _, _, Tm.lam _ => true
  | _, _, Tm.lit _ => true
  | _, _, Tm.ret _ => true
  | _, _, Tm.var _ => false
  | _, _, Tm.app _ _ => false
  | _, _, Tm.bind _ _ => false
  | _, _, Tm.tick _ => false

/-- Call-by-name small-step reduction on closed terms. Evaluation positions are
the head of an application and the first argument of `bind`; nothing reduces
under `lam` or in the body of `bind`. -/
inductive Step : {A : Ty} → Tm [] A → Tm [] A → Prop where
  | beta {A B : Ty} (b : Tm [A] B) (a : Tm [] A) : Step (Tm.app (Tm.lam b) a) (b.inst a)
  | appL {A B : Ty} {f f' : Tm [] (Ty.arr A B)} (a : Tm [] A) :
      Step f f' → Step (Tm.app f a) (Tm.app f' a)
  | bindRet {A B : Ty} (a : Tm [] A) (v : Tm [A] (Ty.comp B)) :
      Step (Tm.bind (Tm.ret a) v) (v.inst a)
  | bindL {A B : Ty} {u u' : Tm [] (Ty.comp A)} (v : Tm [A] (Ty.comp B)) :
      Step u u' → Step (Tm.bind u v) (Tm.bind u' v)
  | tick {A : Ty} (e : Tm [] (Ty.comp A)) : Step (Tm.tick e) e

theorem Step.not_val {A : Ty} {e e' : Tm [] A} (h : Step e e') : e.isVal = false := by
  cases h <;> rfl

/-- Closed terms of type `A` as an operational language. -/
def termLang (A : Ty) : Lang where
  Expr := Tm [] A
  isVal := Tm.isVal
  step := Step
  val_stuck := Step.not_val

/-- The application context `• a` is an evaluation context: it satisfies the laws. -/
theorem appCtx_laws {A B : Ty} (a : Tm [] A) :
    CtxLaws (termLang (Ty.arr A B)) (termLang B) (fun f => Tm.app f a) where
  fill_not_val := fun _ => rfl
  fill_step := fun h => Step.appL a h
  fill_step_inv := by
    intro f e₂ hv h
    have h' : Step (Tm.app f a) e₂ := h
    cases h' with
    | beta b _ => exact tt_ne_ff hv
    | appL _ hs => exact ⟨_, rfl, hs⟩

/-- The operational bind rule for the application context, as an instance. -/
theorem wpo_bind_app {A B : Ty} (a : Tm [] A) (Φ : Tm [] B → Nat → Prop) (n : Nat)
    (f : Tm [] (Ty.arr A B)) :
    wpo (termLang (Ty.arr A B)) n f (fun v m => wpo (termLang B) m (Tm.app v a) Φ) →
    wpo (termLang B) n (Tm.app f a) Φ :=
  wpo_bind (appCtx_laws a) Φ n f

/-! ### A context whose hole is under a binder -/

/-- `λ_. •`: the hole sits under a λ. -/
def lamCtx (A : Ty) {B : Ty} (e : Tm [] B) : Tm [] (Ty.arr A B) := Tm.lam e.wk

/-- The β-redex `(λx. x) 0`. -/
def redex : Tm [] Ty.nat := Tm.app (Tm.lam (Tm.var Var.z)) (Tm.lit 0)

theorem redex_step : Step redex (Tm.lit 0) := Step.beta (Tm.var Var.z) (Tm.lit 0)

theorem redex_step_inv {e' : Tm [] Ty.nat} (h : Step redex e') : e' = Tm.lit 0 := by
  have h' : Step (Tm.app (Tm.lam (Tm.var Var.z)) (Tm.lit 0)) e' := h
  cases h' with
  | beta _ _ => rfl
  | appL _ hs => cases hs

/-- (b) The binder context violates the lifting laws: `(λx.x) 0` steps, but
`λ_. (λx.x) 0` is a value and does not. -/
theorem lamCtx_not_ctxLaws (A : Ty) :
    ¬ CtxLaws (termLang Ty.nat) (termLang (Ty.arr A Ty.nat)) (lamCtx A) := by
  intro hK
  have h : Step (lamCtx A redex) (lamCtx A (Tm.lit 0)) := hK.fill_step redex_step
  have hv : (lamCtx A redex).isVal = false := h.not_val
  exact tt_ne_ff hv

/-- (b, negative half) The conclusion of the bind rule is *false* for the binder
context: the premise holds (the redex reduces to `0`, and `λ_. 0` satisfies the
postcondition), yet `λ_. (λx.x) 0` does not satisfy it. -/
theorem wpo_bind_fails_under_lam (A : Ty) :
    ∃ Φ : Tm [] (Ty.arr A Ty.nat) → Nat → Prop,
      wpo (termLang Ty.nat) 1 redex
        (fun v m => wpo (termLang (Ty.arr A Ty.nat)) m (lamCtx A v) Φ) ∧
      ¬ wpo (termLang (Ty.arr A Ty.nat)) 1 (lamCtx A redex) Φ := by
  refine ⟨fun t _ => t = lamCtx A (Tm.lit 0), ?_, ?_⟩
  · refine (wpo_succ _ 0 _ _).2 ⟨fun hv => ff_ne_tt hv, fun _ => ⟨⟨_, redex_step⟩, ?_⟩⟩
    intro e' he'
    have e : e' = Tm.lit 0 := redex_step_inv he'
    subst e
    refine (wpo_zero _ _ _).2 ⟨fun _ => ?_, fun hv => tt_ne_ff hv⟩
    exact (wpo_zero _ _ _).2 ⟨fun _ => rfl, fun hv => tt_ne_ff hv⟩
  · intro H
    have e : lamCtx A redex = lamCtx A (Tm.lit 0) := ((wpo_succ _ 0 _ _).1 H).1 rfl
    have e' : Tm.lam (A := A) (Tm.app (Tm.lam (Tm.var Var.z)) (Tm.lit 0))
        = Tm.lam (A := A) (Tm.lit 0 : Tm [A] Ty.nat) := e
    cases e'

/-- A predicate on raw closed terms separates `λ_. 0` from `λ_. (λx.x) 0`. -/
theorem operational_predicate_distinguishes (A : Ty) :
    ∃ Φ : Tm [] (Ty.arr A Ty.nat) → Prop, Φ (lamCtx A (Tm.lit 0)) ∧ ¬ Φ (lamCtx A redex) := by
  refine ⟨fun t => t = lamCtx A (Tm.lit 0), rfl, ?_⟩
  intro e
  have e' : Tm.lam (A := A) (Tm.app (Tm.lam (Tm.var Var.z)) (Tm.lit 0))
      = Tm.lam (A := A) (Tm.lit 0 : Tm [A] Ty.nat) := e
  cases e'

/-! ### The same two terms in the denotational logic -/

/-- The two terms are convertible: β under the binder (ξ-rule). -/
theorem lamCtx_conv (A : Ty) : Conv (lamCtx A redex) (lamCtx A (Tm.lit 0)) :=
  Conv.lam (Conv.beta (Tm.var Var.z) (Tm.lit 0))

/-- No predicate on denotations separates them. -/
theorem denotational_predicate_cannot_distinguish {S : SepAlg} (A : Ty)
    (P : (Ty.arr A Ty.nat).den → SProp S) (γ : Env []) :
    P ((lamCtx A redex).eval γ) = P ((lamCtx A (Tm.lit 0)).eval γ) := by
  rw [(lamCtx_conv A).sound γ]

/-- In particular the denotational `wp` of the two returned closures coincides for
every postcondition, where the operational bind rule's conclusion failed. -/
theorem wp_agrees_under_lam {S : SepAlg} (A : Ty)
    (Φ : PredC S [Ty.arr A Ty.nat]) :
    wp (Tm.ret (lamCtx A redex)) Φ = wp (Tm.ret (lamCtx A (Tm.lit 0))) Φ :=
  wp_congr (Conv.ret (lamCtx_conv A)) Φ

end Toy
