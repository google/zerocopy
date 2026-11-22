/-
A program logic over denotations: predicates are fibre elements over `⟦Γ⟧`,
syntactic substitution is reindexing, and the weakest precondition is a family of
maps on *denotations*. Congruence under binders is inherited from the equational
theory with no bind/lifting rule.

Toy model. Tick-counting computations only; no store.
-/
import Toy.Hyperdoctrine
import Toy.Syntax

namespace Toy

variable {S : SepAlg}

/-- Predicates in an object-language context: the fibre over `⟦Γ⟧`. -/
abbrev PredC (S : SepAlg) (Γ : Ctx) : Type := Pred S (Env Γ)

/-- Syntactic substitution on predicates is reindexing along `⟦σ⟧`. -/
def substP {Γ Δ : Ctx} (σ : Sub Γ Δ) (φ : PredC S Γ) : PredC S Δ := Pred.reidx σ.den φ

/-! ### Substitution is functorial -/

theorem substP_id {Γ : Ctx} (φ : PredC S Γ) : substP (Sub.id Γ) φ = φ := rfl

theorem substP_comp {Γ Δ Θ : Ctx} (σ : Sub Γ Δ) (τ : Sub Δ Θ) (φ : PredC S Γ) :
    substP (σ.comp τ) φ = substP τ (substP σ φ) := by
  funext θ
  show φ ((σ.comp τ).den θ) = φ (σ.den (τ.den θ))
  rw [Sub.den_comp]

/-! ### (a) Automatic substitution congruence -/

/-- Pointwise-convertible substitutions act identically on *every* predicate. -/
theorem substP_congr {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (h : ∀ A (x : Var Γ A), Conv (σ A x) (τ A x))
    (φ : PredC S Γ) : substP σ φ = substP τ φ := by
  have e : σ.den = τ.den := by
    funext δ A x
    exact (h A x).sound δ
  exact Pred.reidx_congr e φ

/-- `φ[u/x] = φ[v/x]` as fibre elements whenever `u ≡ v`. No hypothesis on `φ`. -/
theorem subst1_congr {Γ : Ctx} {A : Ty} {u v : Tm Γ A} (h : Conv u v) (φ : PredC S (A :: Γ)) :
    substP (Sub.one u) φ = substP (Sub.one v) φ := by
  apply substP_congr
  intro B x
  cases x with
  | z => exact h
  | s y => exact Conv.refl _

/-! ### Quantification over a program type, and Beck–Chevalley for substitution -/

def forallT {Γ : Ctx} {A : Ty} (φ : PredC S (A :: Γ)) : PredC S Γ :=
  fun γ => SProp.all fun a : A.den => φ (Env.cons a γ)

def existsT {Γ : Ctx} {A : Ty} (φ : PredC S (A :: Γ)) : PredC S Γ :=
  fun γ => SProp.ex fun a : A.den => φ (Env.cons a γ)

/-- `(∀x. φ)[σ] = ∀x. φ[σ↑]`: substitution commutes with the binder. -/
theorem substP_forallT {Γ Δ : Ctx} {A : Ty} (σ : Sub Γ Δ) (φ : PredC S (A :: Γ)) :
    substP σ (forallT φ) = forallT (substP (σ.ext A) φ) := by
  funext δ
  show SProp.all (fun a => φ (Env.cons a (σ.den δ)))
     = SProp.all (fun a => φ ((σ.ext A).den (Env.cons a δ)))
  have : (fun a : A.den => φ ((σ.ext A).den (Env.cons a δ)))
       = fun a => φ (Env.cons a (σ.den δ)) := by
    funext a; rw [Sub.den_ext]
  rw [this]

/-- `(∃x. φ)[σ] = ∃x. φ[σ↑]`. -/
theorem substP_existsT {Γ Δ : Ctx} {A : Ty} (σ : Sub Γ Δ) (φ : PredC S (A :: Γ)) :
    substP σ (existsT φ) = existsT (substP (σ.ext A) φ) := by
  funext δ
  show SProp.ex (fun a => φ (Env.cons a (σ.den δ)))
     = SProp.ex (fun a => φ ((σ.ext A).den (Env.cons a δ)))
  have : (fun a : A.den => φ ((σ.ext A).den (Env.cons a δ)))
       = fun a => φ (Env.cons a (σ.den δ)) := by
    funext a; rw [Sub.den_ext]
  rw [this]

/-! ### Weakest preconditions on denotations -/

/-- `wpSem (k, a) Φ = ▷ᵏ (Φ a)`: after `k` abstract steps the result satisfies `Φ`. -/
def wpSem {X : Type} (r : Nat × X) (Φ : X → SProp S) : SProp S :=
  ⟨fun n h => r.1 ≤ n → (Φ r.2).holds (n - r.1) h, by
    intro n m h le H hm
    exact (Φ r.2).down (Nat.sub_le_sub_right le r.1) (H (Nat.le_trans hm le))⟩

/-- The weakest precondition of a term depends on the term only through its denotation. -/
def wp {Γ : Ctx} {A : Ty} (e : Tm Γ (Ty.comp A)) (Φ : PredC S (A :: Γ)) : PredC S Γ :=
  fun γ => wpSem (e.eval γ) (fun a => Φ (Env.cons a γ))

/-- (a) `wp` is invariant under the whole equational theory. -/
theorem wp_congr {Γ : Ctx} {A : Ty} {e e' : Tm Γ (Ty.comp A)} (h : Conv e e')
    (Φ : PredC S (A :: Γ)) : wp e Φ = wp e' Φ := by
  funext γ
  show wpSem (e.eval γ) _ = wpSem (e'.eval γ) _
  rw [h.sound γ]

/-- β-reduction is not a proof rule: the two weakest preconditions are equal. -/
theorem wp_beta {Γ : Ctx} {A B : Ty} (b : Tm (A :: Γ) (Ty.comp B)) (a : Tm Γ A)
    (Φ : PredC S (B :: Γ)) : wp (Tm.app (Tm.lam b) a) Φ = wp (b.inst a) Φ :=
  wp_congr (Conv.beta b a) Φ

/-- (a) Congruence *under a λ*: rewriting the body of a returned closure does not
change the weakest precondition, for any postcondition. -/
theorem wp_ret_lam_congr {Γ : Ctx} {A B : Ty} {b b' : Tm (A :: Γ) B} (h : Conv b b')
    (Φ : PredC S (Ty.arr A B :: Γ)) : wp (Tm.ret (Tm.lam b)) Φ = wp (Tm.ret (Tm.lam b')) Φ :=
  wp_congr (Conv.ret (Conv.lam h)) Φ

/-- (a) Congruence under the `bind` binder (a let-binding). -/
theorem wp_bind_body_congr {Γ : Ctx} {A B : Ty} (u : Tm Γ (Ty.comp A))
    {v v' : Tm (A :: Γ) (Ty.comp B)} (h : Conv v v') (Φ : PredC S (B :: Γ)) :
    wp (Tm.bind u v) Φ = wp (Tm.bind u v') Φ :=
  wp_congr (Conv.bind (Conv.refl u) h) Φ

/-- Substitution commutes with `wp` and its postcondition binder (naturality). -/
theorem substP_wp {Γ Δ : Ctx} {A : Ty} (σ : Sub Γ Δ) (e : Tm Γ (Ty.comp A))
    (Φ : PredC S (A :: Γ)) : substP σ (wp e Φ) = wp (e.sub σ) (substP (σ.ext A) Φ) := by
  funext δ
  show wpSem (e.eval (σ.den δ)) (fun a => Φ (Env.cons a (σ.den δ)))
     = wpSem ((e.sub σ).eval δ) (fun a => Φ ((σ.ext A).den (Env.cons a δ)))
  rw [Tm.eval_sub]
  have : (fun a : A.den => Φ ((σ.ext A).den (Env.cons a δ)))
       = fun a => Φ (Env.cons a (σ.den δ)) := by
    funext a; rw [Sub.den_ext]
  rw [this]

/-! ### Proof rules for `wp` -/

theorem wpSem_mono {X : Type} (r : Nat × X) {Φ Ψ : X → SProp S} (h : ∀ x, Φ x ⊑ Ψ x) :
    wpSem r Φ ⊑ wpSem r Ψ :=
  fun n r' H hk => h _ (n - r.1) r' (H hk)

/-- `wp-val`, both directions. -/
theorem wpSem_ret {X : Type} (x : X) (Φ : X → SProp S) : wpSem (0, x) Φ = Φ x :=
  SProp.ext fun n _ => ⟨fun H => H (Nat.zero_le n), fun H _ => H⟩

/-- `wp-bind`, both directions: sequencing is composition of denotations. -/
theorem wpSem_bind {X Y : Type} (r : Nat × X) (f : X → Nat × Y) (Φ : Y → SProp S) :
    wpSem (bindSem r f) Φ = wpSem r (fun x => wpSem (f x) Φ) := by
  apply SProp.ext
  intro n h
  show (r.1 + (f r.2).1 ≤ n → (Φ (f r.2).2).holds (n - (r.1 + (f r.2).1)) h)
     ↔ (r.1 ≤ n → (f r.2).1 ≤ n - r.1 → (Φ (f r.2).2).holds (n - r.1 - (f r.2).1) h)
  rw [Nat.sub_sub]
  constructor
  · intro H _ h₂; exact H (by omega)
  · intro H h₁; exact H (by omega) (by omega)

/-- `wp-step`: one abstract step discharges one later. -/
theorem wpSem_tick {X : Type} (r : Nat × X) (Φ : X → SProp S) :
    SProp.later (wpSem r Φ) ⊑ wpSem (tickSem r) Φ := by
  intro n h H hk
  have hk' : r.1 + 1 ≤ n := hk
  have h₁ := H (n - 1) (by omega) (by omega)
  have e : n - 1 - r.1 = n - (r.1 + 1) := by omega
  show (Φ r.2).holds (n - (r.1 + 1)) h
  rw [← e]
  exact h₁

/-- Framing: resources not mentioned by the computation are preserved. -/
theorem wpSem_frame {X : Type} (r : Nat × X) (Φ : X → SProp S) (R : SProp S) :
    SProp.sep (wpSem r Φ) R ⊑ wpSem r (fun x => SProp.sep (Φ x) R) :=
  fun n _ ⟨h₁, h₂, j, a, b⟩ hk => ⟨h₁, h₂, j, a hk, R.down (Nat.sub_le n r.1) b⟩

/-- `wp-wand`. -/
theorem wpSem_wand {X : Type} (r : Nat × X) (Φ Ψ : X → SProp S) :
    SProp.sep (SProp.all fun x => SProp.wand (Φ x) (Ψ x)) (wpSem r Φ) ⊑ wpSem r Ψ :=
  fun n _ ⟨_, h₂, j, a, b⟩ hk => a r.2 (n - r.1) (Nat.sub_le n r.1) h₂ _ j (b hk)

/-- Syntactic `wp-val`. -/
theorem wp_ret {Γ : Ctx} {A : Ty} (a : Tm Γ A) (Φ : PredC S (A :: Γ)) :
    wp (Tm.ret a) Φ = substP (Sub.one a) Φ := by
  funext γ
  show wpSem (0, a.eval γ) (fun x => Φ (Env.cons x γ)) = Φ ((Sub.one a).den γ)
  rw [wpSem_ret, Sub.den_one]

/-- Syntactic `wp-bind`: no evaluation-context side condition is involved. -/
theorem wp_bind {Γ : Ctx} {A B : Ty} (u : Tm Γ (Ty.comp A)) (v : Tm (A :: Γ) (Ty.comp B))
    (Φ : PredC S (B :: Γ)) (γ : Env Γ) :
    wp (Tm.bind u v) Φ γ
      = wpSem (u.eval γ) (fun a => wpSem (v.eval (Env.cons a γ)) (fun b => Φ (Env.cons b γ))) :=
  wpSem_bind _ _ _

/-- Syntactic `wp-step`. -/
theorem wp_tick {Γ : Ctx} {A : Ty} (e : Tm Γ (Ty.comp A)) (Φ : PredC S (A :: Γ)) :
    Pred.later (wp e Φ) ⊩ wp (Tm.tick e) Φ :=
  fun γ => wpSem_tick (e.eval γ) _

end Toy
