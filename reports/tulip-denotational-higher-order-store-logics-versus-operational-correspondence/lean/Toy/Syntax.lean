/-
A small typed object language with binders, its substitution calculus, a
step-counting denotational semantics and an equational theory that is a
congruence under binders.

Toy model. Simply typed monadic λ-calculus: `comp A` is a computation type whose
denotation counts abstract `tick`s (the finite elements `δᵏ(η a)` of a guarded
lift). There is no store, no recursion and no divergence.
-/
namespace Toy

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty
  | comp : Ty → Ty

abbrev Ctx := List Ty

/-- Typed de Bruijn variables. -/
inductive Var : Ctx → Ty → Type where
  | z {Γ : Ctx} {A : Ty} : Var (A :: Γ) A
  | s {Γ : Ctx} {A B : Ty} : Var Γ A → Var (B :: Γ) A

/-- Intrinsically typed terms. `lam` and the second argument of `bind` are binders. -/
inductive Tm : Ctx → Ty → Type where
  | var {Γ : Ctx} {A : Ty} : Var Γ A → Tm Γ A
  | lit {Γ : Ctx} : Nat → Tm Γ Ty.nat
  | lam {Γ : Ctx} {A B : Ty} : Tm (A :: Γ) B → Tm Γ (Ty.arr A B)
  | app {Γ : Ctx} {A B : Ty} : Tm Γ (Ty.arr A B) → Tm Γ A → Tm Γ B
  | ret {Γ : Ctx} {A : Ty} : Tm Γ A → Tm Γ (Ty.comp A)
  | bind {Γ : Ctx} {A B : Ty} : Tm Γ (Ty.comp A) → Tm (A :: Γ) (Ty.comp B) → Tm Γ (Ty.comp B)
  | tick {Γ : Ctx} {A : Ty} : Tm Γ (Ty.comp A) → Tm Γ (Ty.comp A)

/-! ### Renaming and substitution -/

def Ren (Γ Δ : Ctx) : Type := ∀ A, Var Γ A → Var Δ A

def Ren.ext {Γ Δ : Ctx} (ρ : Ren Γ Δ) (B : Ty) : Ren (B :: Γ) (B :: Δ)
  | _, Var.z => Var.z
  | _, Var.s x => Var.s (ρ _ x)

/-- The weakening renaming. -/
def Ren.shift {Γ : Ctx} (B : Ty) : Ren Γ (B :: Γ) := fun _ x => Var.s x

def Tm.ren : {Γ Δ : Ctx} → {A : Ty} → Tm Γ A → Ren Γ Δ → Tm Δ A
  | _, _, _, Tm.var x, ρ => Tm.var (ρ _ x)
  | _, _, _, Tm.lit n, _ => Tm.lit n
  | _, _, _, Tm.lam b, ρ => Tm.lam (b.ren (ρ.ext _))
  | _, _, _, Tm.app f a, ρ => Tm.app (f.ren ρ) (a.ren ρ)
  | _, _, _, Tm.ret a, ρ => Tm.ret (a.ren ρ)
  | _, _, _, Tm.bind u v, ρ => Tm.bind (u.ren ρ) (v.ren (ρ.ext _))
  | _, _, _, Tm.tick e, ρ => Tm.tick (e.ren ρ)

/-- Weakening by one variable. -/
def Tm.wk {Γ : Ctx} {A B : Ty} (t : Tm Γ A) : Tm (B :: Γ) A := t.ren (Ren.shift B)

/-- Typed simultaneous substitutions. -/
def Sub (Γ Δ : Ctx) : Type := ∀ A, Var Γ A → Tm Δ A

def Sub.ext {Γ Δ : Ctx} (σ : Sub Γ Δ) (B : Ty) : Sub (B :: Γ) (B :: Δ)
  | _, Var.z => Tm.var Var.z
  | _, Var.s x => (σ _ x).wk

def Tm.sub : {Γ Δ : Ctx} → {A : Ty} → Tm Γ A → Sub Γ Δ → Tm Δ A
  | _, _, _, Tm.var x, σ => σ _ x
  | _, _, _, Tm.lit n, _ => Tm.lit n
  | _, _, _, Tm.lam b, σ => Tm.lam (b.sub (σ.ext _))
  | _, _, _, Tm.app f a, σ => Tm.app (f.sub σ) (a.sub σ)
  | _, _, _, Tm.ret a, σ => Tm.ret (a.sub σ)
  | _, _, _, Tm.bind u v, σ => Tm.bind (u.sub σ) (v.sub (σ.ext _))
  | _, _, _, Tm.tick e, σ => Tm.tick (e.sub σ)

/-- The identity substitution. -/
def Sub.id (Γ : Ctx) : Sub Γ Γ := fun _ x => Tm.var x

/-- Composition of substitutions (apply `σ`, then `τ`). -/
def Sub.comp {Γ Δ Θ : Ctx} (σ : Sub Γ Δ) (τ : Sub Δ Θ) : Sub Γ Θ := fun _ x => (σ _ x).sub τ

/-- Single substitution for the most recently bound variable. -/
def Sub.one {Γ : Ctx} {A : Ty} (a : Tm Γ A) : Sub (A :: Γ) Γ
  | _, Var.z => a
  | _, Var.s x => Tm.var x

/-- `b.inst a` is `b[a/x]` for the bound variable `x` of `b`. -/
def Tm.inst {Γ : Ctx} {A B : Ty} (b : Tm (A :: Γ) B) (a : Tm Γ A) : Tm Γ B := b.sub (Sub.one a)

/-! ### Denotational semantics -/

/-- Denotation of types. A computation denotes a tick count and a result. -/
@[reducible] def Ty.den : Ty → Type
  | Ty.nat => Nat
  | Ty.arr A B => A.den → B.den
  | Ty.comp A => Nat × A.den

/-- Semantic environments: the object `⟦Γ⟧` of the base category. -/
def Env (Γ : Ctx) : Type := ∀ A, Var Γ A → A.den

def Env.cons {Γ : Ctx} {A : Ty} (a : A.den) (γ : Env Γ) : Env (A :: Γ)
  | _, Var.z => a
  | _, Var.s x => γ _ x

/-- Monadic bind on tick-counting computations. -/
def bindSem {X Y : Type} (r : Nat × X) (f : X → Nat × Y) : Nat × Y := (r.1 + (f r.2).1, (f r.2).2)

/-- One abstract step. -/
def tickSem {X : Type} (r : Nat × X) : Nat × X := (r.1 + 1, r.2)

/-- Denotation of terms: a base morphism `⟦Γ⟧ → ⟦A⟧`. -/
def Tm.eval : {Γ : Ctx} → {A : Ty} → Tm Γ A → Env Γ → A.den
  | _, _, Tm.var x, γ => γ _ x
  | _, _, Tm.lit n, _ => n
  | _, _, Tm.lam b, γ => fun a => b.eval (Env.cons a γ)
  | _, _, Tm.app f a, γ => (f.eval γ) (a.eval γ)
  | _, _, Tm.ret a, γ => (0, a.eval γ)
  | _, _, Tm.bind u v, γ => bindSem (u.eval γ) (fun a => v.eval (Env.cons a γ))
  | _, _, Tm.tick e, γ => tickSem (e.eval γ)

/-- Denotation of a substitution: a base morphism `⟦Δ⟧ → ⟦Γ⟧`. -/
def Sub.den {Γ Δ : Ctx} (σ : Sub Γ Δ) (δ : Env Δ) : Env Γ := fun _ x => (σ _ x).eval δ

/-! ### Semantic renaming and substitution lemmas -/

theorem Env.cons_ren_ext {Γ Δ : Ctx} {B : Ty} (ρ : Ren Γ Δ) (δ : Env Δ) (a : B.den) :
    (fun A x => Env.cons a δ A (ρ.ext B A x)) = Env.cons a (fun A x => δ A (ρ A x)) := by
  funext A x
  cases x <;> rfl

theorem Tm.eval_ren {Γ : Ctx} {A : Ty} (t : Tm Γ A) :
    ∀ {Δ : Ctx} (ρ : Ren Γ Δ) (δ : Env Δ), (t.ren ρ).eval δ = t.eval (fun A x => δ A (ρ A x)) := by
  induction t with
  | var x => intro Δ ρ δ; rfl
  | lit n => intro Δ ρ δ; rfl
  | lam b ih =>
    intro Δ ρ δ
    funext a
    show (b.ren (ρ.ext _)).eval (Env.cons a δ) = b.eval (Env.cons a fun A x => δ A (ρ A x))
    rw [ih, Env.cons_ren_ext]
  | app f a ihf iha =>
    intro Δ ρ δ
    show (f.ren ρ).eval δ ((a.ren ρ).eval δ) = _
    rw [ihf, iha]; rfl
  | ret a ih =>
    intro Δ ρ δ
    show (0, (a.ren ρ).eval δ) = _
    rw [ih]; rfl
  | bind u v ihu ihv =>
    intro Δ ρ δ
    show bindSem ((u.ren ρ).eval δ) (fun a => (v.ren (ρ.ext _)).eval (Env.cons a δ)) = _
    rw [ihu]
    have : (fun a => (v.ren (ρ.ext _)).eval (Env.cons a δ))
        = fun a => v.eval (Env.cons a fun A x => δ A (ρ A x)) := by
      funext a; rw [ihv, Env.cons_ren_ext]
    rw [this]; rfl
  | tick e ih =>
    intro Δ ρ δ
    show tickSem ((e.ren ρ).eval δ) = _
    rw [ih]; rfl

theorem Tm.eval_wk {Γ : Ctx} {A B : Ty} (t : Tm Γ A) (a : B.den) (γ : Env Γ) :
    (t.wk (B := B)).eval (Env.cons a γ) = t.eval γ := by
  unfold Tm.wk
  rw [Tm.eval_ren]
  rfl

theorem Sub.den_ext {Γ Δ : Ctx} {B : Ty} (σ : Sub Γ Δ) (a : B.den) (δ : Env Δ) :
    (σ.ext B).den (Env.cons a δ) = Env.cons a (σ.den δ) := by
  funext A x
  cases x with
  | z => rfl
  | s y => exact Tm.eval_wk (σ _ y) a δ

/-- The substitution lemma: syntactic substitution denotes reindexing. -/
theorem Tm.eval_sub {Γ : Ctx} {A : Ty} (t : Tm Γ A) :
    ∀ {Δ : Ctx} (σ : Sub Γ Δ) (δ : Env Δ), (t.sub σ).eval δ = t.eval (σ.den δ) := by
  induction t with
  | var x => intro Δ σ δ; rfl
  | lit n => intro Δ σ δ; rfl
  | lam b ih =>
    intro Δ σ δ
    funext a
    show (b.sub (σ.ext _)).eval (Env.cons a δ) = b.eval (Env.cons a (σ.den δ))
    rw [ih, Sub.den_ext]
  | app f a ihf iha =>
    intro Δ σ δ
    show (f.sub σ).eval δ ((a.sub σ).eval δ) = _
    rw [ihf, iha]; rfl
  | ret a ih =>
    intro Δ σ δ
    show (0, (a.sub σ).eval δ) = _
    rw [ih]; rfl
  | bind u v ihu ihv =>
    intro Δ σ δ
    show bindSem ((u.sub σ).eval δ) (fun a => (v.sub (σ.ext _)).eval (Env.cons a δ)) = _
    rw [ihu]
    have : (fun a => (v.sub (σ.ext _)).eval (Env.cons a δ))
        = fun a => v.eval (Env.cons a (σ.den δ)) := by
      funext a; rw [ihv, Sub.den_ext]
    rw [this]; rfl
  | tick e ih =>
    intro Δ σ δ
    show tickSem ((e.sub σ).eval δ) = _
    rw [ih]; rfl

theorem Sub.den_one {Γ : Ctx} {A : Ty} (a : Tm Γ A) (γ : Env Γ) :
    (Sub.one a).den γ = Env.cons (a.eval γ) γ := by
  funext B x
  cases x <;> rfl

theorem Tm.eval_inst {Γ : Ctx} {A B : Ty} (b : Tm (A :: Γ) B) (a : Tm Γ A) (γ : Env Γ) :
    (b.inst a).eval γ = b.eval (Env.cons (a.eval γ) γ) := by
  unfold Tm.inst
  rw [Tm.eval_sub, Sub.den_one]

theorem Sub.den_id (Γ : Ctx) (γ : Env Γ) : (Sub.id Γ).den γ = γ := rfl

/-- Substitution is functorial on denotations. -/
theorem Sub.den_comp {Γ Δ Θ : Ctx} (σ : Sub Γ Δ) (τ : Sub Δ Θ) (θ : Env Θ) :
    (σ.comp τ).den θ = σ.den (τ.den θ) := by
  funext A x
  exact Tm.eval_sub (σ A x) τ θ

/-! ### The equational theory -/

/-- Judgemental equality of the object language: β/η for functions, the monad
laws, commutation of `tick` with `bind`, closed under *every* term former —
including the two binders (`lam` and the body of `bind`). -/
inductive Conv : {Γ : Ctx} → {A : Ty} → Tm Γ A → Tm Γ A → Prop where
  | refl {Γ : Ctx} {A : Ty} (t : Tm Γ A) : Conv t t
  | symm {Γ : Ctx} {A : Ty} {t u : Tm Γ A} : Conv t u → Conv u t
  | trans {Γ : Ctx} {A : Ty} {t u v : Tm Γ A} : Conv t u → Conv u v → Conv t v
  | lam {Γ : Ctx} {A B : Ty} {b b' : Tm (A :: Γ) B} : Conv b b' → Conv (Tm.lam b) (Tm.lam b')
  | app {Γ : Ctx} {A B : Ty} {f f' : Tm Γ (Ty.arr A B)} {a a' : Tm Γ A} :
      Conv f f' → Conv a a' → Conv (Tm.app f a) (Tm.app f' a')
  | ret {Γ : Ctx} {A : Ty} {a a' : Tm Γ A} : Conv a a' → Conv (Tm.ret a) (Tm.ret a')
  | bind {Γ : Ctx} {A B : Ty} {u u' : Tm Γ (Ty.comp A)} {v v' : Tm (A :: Γ) (Ty.comp B)} :
      Conv u u' → Conv v v' → Conv (Tm.bind u v) (Tm.bind u' v')
  | tick {Γ : Ctx} {A : Ty} {e e' : Tm Γ (Ty.comp A)} : Conv e e' → Conv (Tm.tick e) (Tm.tick e')
  | beta {Γ : Ctx} {A B : Ty} (b : Tm (A :: Γ) B) (a : Tm Γ A) :
      Conv (Tm.app (Tm.lam b) a) (b.inst a)
  | eta {Γ : Ctx} {A B : Ty} (f : Tm Γ (Ty.arr A B)) :
      Conv f (Tm.lam (Tm.app f.wk (Tm.var Var.z)))
  | bind_ret {Γ : Ctx} {A B : Ty} (a : Tm Γ A) (v : Tm (A :: Γ) (Ty.comp B)) :
      Conv (Tm.bind (Tm.ret a) v) (v.inst a)
  | ret_bind {Γ : Ctx} {A : Ty} (u : Tm Γ (Ty.comp A)) :
      Conv (Tm.bind u (Tm.ret (Tm.var Var.z))) u
  | bind_assoc {Γ : Ctx} {A B C : Ty} (u : Tm Γ (Ty.comp A)) (v : Tm (A :: Γ) (Ty.comp B))
      (w : Tm (B :: Γ) (Ty.comp C)) :
      Conv (Tm.bind (Tm.bind u v) w)
        (Tm.bind u (Tm.bind v (w.ren ((Ren.shift A).ext B))))
  | tick_bind {Γ : Ctx} {A B : Ty} (u : Tm Γ (Ty.comp A)) (v : Tm (A :: Γ) (Ty.comp B)) :
      Conv (Tm.bind (Tm.tick u) v) (Tm.tick (Tm.bind u v))
  | bind_tick {Γ : Ctx} {A B : Ty} (u : Tm Γ (Ty.comp A)) (v : Tm (A :: Γ) (Ty.comp B)) :
      Conv (Tm.bind u (Tm.tick v)) (Tm.tick (Tm.bind u v))

/-- Soundness of the equational theory: convertible terms denote the *same*
base morphism. The `lam` and `bind` cases are congruence under a binder. -/
theorem Conv.sound {Γ : Ctx} {A : Ty} {t u : Tm Γ A} (h : Conv t u) :
    ∀ γ : Env Γ, t.eval γ = u.eval γ := by
  induction h with
  | refl t => intro γ; rfl
  | symm _ ih => intro γ; exact (ih γ).symm
  | trans _ _ ih₁ ih₂ => intro γ; exact (ih₁ γ).trans (ih₂ γ)
  | lam _ ih =>
    intro γ
    funext a
    exact ih (Env.cons a γ)
  | @app Γ A B f f' a a' _ _ ihf iha =>
    intro γ
    show f.eval γ (a.eval γ) = f'.eval γ (a'.eval γ)
    rw [ihf γ, iha γ]
  | @ret Γ A a a' _ ih =>
    intro γ
    show ((0 : Nat), a.eval γ) = ((0 : Nat), a'.eval γ)
    rw [ih γ]
  | @bind Γ A B u u' v v' _ _ ihu ihv =>
    intro γ
    show bindSem (u.eval γ) (fun a => v.eval (Env.cons a γ))
       = bindSem (u'.eval γ) (fun a => v'.eval (Env.cons a γ))
    rw [ihu γ]
    have : (fun a => v.eval (Env.cons a γ)) = fun a => v'.eval (Env.cons a γ) := by
      funext a; exact ihv (Env.cons a γ)
    rw [this]
  | @tick Γ A e e' _ ih =>
    intro γ
    show tickSem (e.eval γ) = tickSem (e'.eval γ)
    rw [ih γ]
  | beta b a =>
    intro γ
    show b.eval (Env.cons (a.eval γ) γ) = (b.inst a).eval γ
    rw [Tm.eval_inst]
  | eta f =>
    intro γ
    funext a
    show f.eval γ a = (f.wk.eval (Env.cons a γ)) a
    rw [Tm.eval_wk]
  | bind_ret a v =>
    intro γ
    show bindSem (0, a.eval γ) (fun x => v.eval (Env.cons x γ)) = (v.inst a).eval γ
    rw [Tm.eval_inst]
    simp [bindSem]
  | ret_bind u =>
    intro γ
    show bindSem (u.eval γ) (fun x => (0, x)) = u.eval γ
    simp [bindSem]
  | @bind_assoc Γ A B C u v w =>
    intro γ
    show bindSem (bindSem (u.eval γ) (fun a => v.eval (Env.cons a γ)))
          (fun b => w.eval (Env.cons b γ))
       = bindSem (u.eval γ) (fun a => bindSem (v.eval (Env.cons a γ))
          (fun b => (w.ren ((Ren.shift A).ext B)).eval (Env.cons b (Env.cons a γ))))
    have key : ∀ (a : A.den) (b : B.den),
        (w.ren ((Ren.shift A).ext B)).eval (Env.cons b (Env.cons a γ))
          = w.eval (Env.cons b γ) := by
      intro a b
      rw [Tm.eval_ren, Env.cons_ren_ext]
      rfl
    simp only [key]
    simp [bindSem, Nat.add_assoc]
  | tick_bind u v =>
    intro γ
    show bindSem (tickSem (u.eval γ)) (fun a => v.eval (Env.cons a γ))
       = tickSem (bindSem (u.eval γ) (fun a => v.eval (Env.cons a γ)))
    simp [bindSem, tickSem]
    omega
  | bind_tick u v =>
    intro γ
    show bindSem (u.eval γ) (fun a => tickSem (v.eval (Env.cons a γ)))
       = tickSem (bindSem (u.eval γ) (fun a => v.eval (Env.cons a γ)))
    simp [bindSem, tickSem]
    omega

/-- Convertible terms denote equal base morphisms (function-level statement). -/
theorem Conv.eval_eq {Γ : Ctx} {A : Ty} {t u : Tm Γ A} (h : Conv t u) : t.eval = u.eval :=
  funext h.sound

end Toy
