/-
Toy.FloatTier.Determinism
=========================

Determinism of observations (value-level `isNaN`, `==`, `<` and bit-level
`signBit`, `toBits`) under every resolution of the nondeterminism of `S`, for
programs whose bit-level uses never receive the excluded values (`BitSafe`).

`DetCongr X R bad ok` (auxiliary) packages the facts used by one induction: the
relation `R` is reflexive, preserved by the allowed primitives (`ok`) and by the
bit-level operations on their magnitude argument, collapses to equality on
values with `bad = false`, and is respected by the value-level observations.
Two instances are proved:

* `R = ValEq`, `bad = isNaNOrZero`, all primitives;
* `R` = equality of NaN-collapsed views, `bad = isNaN`, arithmetic primitives
  only (no `min`/`max`).
-/
import Toy.FloatTier.Statements

namespace Toy.FloatTier

variable {f : Fmt}

/-- Auxiliary: the congruence facts used by `FExpr.evalS_rel_of_bitSafe`. -/
structure DetCongr (X : Extra f) (R : V f → V f → Prop) (bad : V f → Bool)
    (ok : Prim → Bool) : Prop where
  refl : ∀ x, R x x
  prim : ∀ p, ok p = true → ∀ {x₁ x₂ y₁ y₂ r₁ r₂ : V f}, R x₁ x₂ → R y₁ y₂ →
    primSet X p x₁ y₁ r₁ → primSet X p x₂ y₂ r₂ → R r₁ r₂
  neg : ∀ {x₁ x₂ : V f}, R x₁ x₂ → R x₁.neg x₂.neg
  abs : ∀ {x₁ x₂ : V f}, R x₁ x₂ → R x₁.abs x₂.abs
  copysign : ∀ {x₁ x₂ : V f} (y : V f), R x₁ x₂ → R (x₁.copysign y) (x₂.copysign y)
  good : ∀ {y₁ y₂ : V f}, R y₁ y₂ → bad y₁ = false → y₁ = y₂
  lt : ∀ {x₁ x₂ y₁ y₂ : V f}, R x₁ x₂ → R y₁ y₂ →
    lt x₁.toFP y₁.toFP = lt x₂.toFP y₂.toFP
  isNaN : ∀ {x₁ x₂ : V f}, R x₁ x₂ → x₁.isNaN = x₂.isNaN
  feq : ∀ {x₁ x₂ y₁ y₂ : V f}, R x₁ x₂ → R y₁ y₂ →
    feq x₁.toFP y₁.toFP = feq x₂.toFP y₂.toFP

theorem FExpr.evalS_rel_of_bitSafe {X : Extra f} {R : V f → V f → Prop} {bad : V f → Bool}
    {ok : Prim → Bool} (hC : DetCongr X R bad ok) (ρ : Nat → V f) :
    ∀ (e : FExpr f), e.PrimsOk ok = true → e.BitSafe X ρ bad →
      ∀ {r₁ r₂ : V f}, e.evalS X ρ r₁ → e.evalS X ρ r₂ → R r₁ r₂ := by
  intro e
  induction e with
  | lit v =>
    intro _ _ r₁ r₂ h₁ h₂; simp only [FExpr.evalS] at h₁ h₂; subst h₁ h₂; exact hC.refl _
  | var i =>
    intro _ _ r₁ r₂ h₁ h₂; simp only [FExpr.evalS] at h₁ h₂; subst h₁ h₂; exact hC.refl _
  | prim p a b iha ihb =>
    intro hok hs r₁ r₂ h₁ h₂
    simp only [FExpr.PrimsOk, Bool.and_eq_true] at hok
    obtain ⟨x₁, y₁, ha₁, hb₁, hp₁⟩ := h₁
    obtain ⟨x₂, y₂, ha₂, hb₂, hp₂⟩ := h₂
    exact hC.prim p hok.1.1 (iha hok.1.2 hs.1 ha₁ ha₂) (ihb hok.2 hs.2 hb₁ hb₂) hp₁ hp₂
  | neg a ih =>
    intro hok hs r₁ r₂ h₁ h₂
    obtain ⟨x₁, ha₁, rfl⟩ := h₁
    obtain ⟨x₂, ha₂, rfl⟩ := h₂
    exact hC.neg (ih hok hs ha₁ ha₂)
  | abs a ih =>
    intro hok hs r₁ r₂ h₁ h₂
    obtain ⟨x₁, ha₁, rfl⟩ := h₁
    obtain ⟨x₂, ha₂, rfl⟩ := h₂
    exact hC.abs (ih hok hs ha₁ ha₂)
  | copysign a b iha ihb =>
    intro hok hs r₁ r₂ h₁ h₂
    simp only [FExpr.PrimsOk, Bool.and_eq_true] at hok
    obtain ⟨x₁, y₁, ha₁, hb₁, rfl⟩ := h₁
    obtain ⟨x₂, y₂, ha₂, hb₂, rfl⟩ := h₂
    have hy : y₁ = y₂ := hC.good (ihb hok.2 hs.2.1 hb₁ hb₂) (hs.2.2 y₁ hb₁)
    subst hy
    exact hC.copysign y₁ (iha hok.1 hs.1 ha₁ ha₂)
  | selLt a b t e iha ihb iht ihe =>
    intro hok hs r₁ r₂ h₁ h₂
    simp only [FExpr.PrimsOk, Bool.and_eq_true] at hok
    obtain ⟨x₁, y₁, ha₁, hb₁, h₁⟩ := h₁
    obtain ⟨x₂, y₂, ha₂, hb₂, h₂⟩ := h₂
    have hl := hC.lt (iha hok.1.1.1 hs.1 ha₁ ha₂) (ihb hok.1.1.2 hs.2.1 hb₁ hb₂)
    rw [← hl] at h₂
    by_cases c : lt x₁.toFP y₁.toFP = true
    · simp only [c, ↓reduceIte] at h₁ h₂
      exact iht hok.1.2 (hs.2.2.1 ⟨x₁, y₁, ha₁, hb₁, c⟩) h₁ h₂
    · simp only [c, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
      exact ihe hok.2 (hs.2.2.2 ⟨x₁, y₁, ha₁, hb₁, Bool.eq_false_iff.mpr c⟩) h₁ h₂

theorem Prog.runS_unique_of_detCongr {X : Extra f} {R : V f → V f → Prop} {bad : V f → Bool}
    {ok : Prim → Bool} (hC : DetCongr X R bad ok) (ρ : Nat → V f) (P : Prog f)
    (hok : P.PrimsOk ok = true) (hs : P.BitSafe X ρ bad) {n₁ n₂ : Nat}
    (h₁ : P.runS X ρ n₁) (h₂ : P.runS X ρ n₂) : n₁ = n₂ := by
  cases P with
  | isNaN a =>
    obtain ⟨x₁, ha₁, rfl⟩ := h₁; obtain ⟨x₂, ha₂, rfl⟩ := h₂
    simp only [Prog.PrimsOk] at hok
    rw [hC.isNaN (FExpr.evalS_rel_of_bitSafe hC ρ a hok hs ha₁ ha₂)]
  | eq a b =>
    obtain ⟨x₁, y₁, ha₁, hb₁, rfl⟩ := h₁; obtain ⟨x₂, y₂, ha₂, hb₂, rfl⟩ := h₂
    simp only [Prog.PrimsOk, Bool.and_eq_true] at hok
    rw [hC.feq (FExpr.evalS_rel_of_bitSafe hC ρ a hok.1 hs.1 ha₁ ha₂)
      (FExpr.evalS_rel_of_bitSafe hC ρ b hok.2 hs.2 hb₁ hb₂)]
  | lt a b =>
    obtain ⟨x₁, y₁, ha₁, hb₁, rfl⟩ := h₁; obtain ⟨x₂, y₂, ha₂, hb₂, rfl⟩ := h₂
    simp only [Prog.PrimsOk, Bool.and_eq_true] at hok
    rw [hC.lt (FExpr.evalS_rel_of_bitSafe hC ρ a hok.1 hs.1 ha₁ ha₂)
      (FExpr.evalS_rel_of_bitSafe hC ρ b hok.2 hs.2 hb₁ hb₂)]
  | signBit a =>
    obtain ⟨x₁, ha₁, rfl⟩ := h₁; obtain ⟨x₂, ha₂, rfl⟩ := h₂
    simp only [Prog.PrimsOk] at hok
    rw [hC.good (FExpr.evalS_rel_of_bitSafe hC ρ a hok hs.1 ha₁ ha₂) (hs.2 x₁ ha₁)]
  | toBits a =>
    obtain ⟨x₁, ha₁, rfl⟩ := h₁; obtain ⟨x₂, ha₂, rfl⟩ := h₂
    simp only [Prog.PrimsOk] at hok
    rw [hC.good (FExpr.evalS_rel_of_bitSafe hC ρ a hok hs.1 ha₁ ha₂) (hs.2 x₁ ha₁)]

theorem detCongr_valEq (X : Extra f) : DetCongr X ValEq V.isNaNOrZero (fun _ => true) := by
  constructor
  · exact ValEq.refl
  · intro p _ x₁ x₂ y₁ y₂ r₁ r₂ hx hy h₁ h₂; exact primSet_valEq_congr p hx hy h₁ h₂
  · intro x₁ x₂ h; unfold ValEq; rw [V.toFP_neg, V.toFP_neg]; exact neg_eqNsz_congr h
  · intro x₁ x₂ h; unfold ValEq; rw [V.toFP_abs, V.toFP_abs]; exact setSign_eqNsz_congr h _
  · intro x₁ x₂ y h
    unfold ValEq; rw [V.toFP_copysign, V.toFP_copysign]; exact setSign_eqNsz_congr h _
  · intro y₁ y₂ h hb; exact V.eq_of_valEq_of_isNaNOrZero_false h hb
  · intro x₁ x₂ y₁ y₂ hx hy; exact lt_eqNsz_congr hx hy
  · intro x₁ x₂ h; exact h.isNaN_eq
  · intro x₁ x₂ y₁ y₂ hx hy; exact feq_eqNsz_congr hx hy

theorem detCongr_toFP (X : Extra f) :
    DetCongr X (fun x y => x.toFP = y.toFP) V.isNaN Prim.isArith := by
  constructor
  · intro _; rfl
  · intro p hp x₁ x₂ y₁ y₂ r₁ r₂ hx hy h₁ h₂; exact primSet_toFP_congr p hp hx hy h₁ h₂
  · intro x₁ x₂ h; simp only [V.toFP_neg, h]
  · intro x₁ x₂ h; simp only [V.toFP_abs, h]
  · intro x₁ x₂ y h; simp only [V.toFP_copysign, h]
  · intro y₁ y₂ h hb; exact V.eq_of_toFP_eq hb h
  · intro x₁ x₂ y₁ y₂ hx hy; simp only [hx, hy]
  · intro x₁ x₂ h; rw [← V.isNaN_toFP x₁, h, V.isNaN_toFP]
  · intro x₁ x₂ y₁ y₂ hx hy; simp only [hx, hy]

theorem FExpr.primsOk_true (e : FExpr f) : e.PrimsOk (fun _ => true) = true := by
  induction e <;> simp_all [FExpr.PrimsOk]

theorem Prog.primsOk_true (P : Prog f) : P.PrimsOk (fun _ => true) = true := by
  cases P <;> simp [Prog.PrimsOk, FExpr.primsOk_true]

/-- **Observation determinism (NaN-or-zero form).** For every extra-payload set
`X`, input `ρ` and program `P`: if in every execution of `S` from `ρ` every
bit-level use in `P` (the sign argument of `copysign`, the argument of
`signBit`/`toBits`) that the execution reaches receives a value that is neither
a NaN nor a zero (`BitSafe`, which constrains a `selLt` branch only if some
execution takes it), then any two observations `S` allows for `P` on `ρ`
(value-level or bit-level) are equal. -/
theorem Prog.runS_unique_of_bitSafe_nanOrZero (X : Extra f) (ρ : Nat → V f) (P : Prog f)
    (hsafe : P.BitSafe X ρ V.isNaNOrZero) :
    ∀ {n₁ n₂ : Nat}, P.runS X ρ n₁ → P.runS X ρ n₂ → n₁ = n₂ :=
  fun h₁ h₂ =>
    Prog.runS_unique_of_detCongr (detCongr_valEq X) ρ P (Prog.primsOk_true P) hsafe h₁ h₂

/-- Tier corollary of `Prog.runS_unique_of_bitSafe_nanOrZero`: two tiers that
are sound for `X` compute the same observation. -/
theorem Prog.runT_eq_of_tierSound_of_bitSafe_nanOrZero (X : Extra f) {τ₁ τ₂ : Tier f}
    (h₁ : TierSound X τ₁) (h₂ : TierSound X τ₂) (ρ : Nat → V f) (P : Prog f)
    (hsafe : P.BitSafe X ρ V.isNaNOrZero) : P.runT τ₁ ρ = P.runT τ₂ ρ :=
  Prog.runS_unique_of_bitSafe_nanOrZero X ρ P hsafe
    (Prog.runS_runT_of_tierSound h₁ P ρ) (Prog.runS_runT_of_tierSound h₂ P ρ)

/-- **Observation determinism (`min`/`max`-free form).** For every
extra-payload set `X`, input `ρ` and program `P` containing no `min`/`max`: if
in every execution of `S` from `ρ` every bit-level use in `P` that the
execution reaches receives a value that is not a NaN (`BitSafe`), then any two
observations `S` allows for `P` on `ρ` (value-level or bit-level) are equal. -/
theorem Prog.runS_unique_of_minMaxFree_of_bitSafe_nan (X : Extra f) (ρ : Nat → V f)
    (P : Prog f) (hmm : P.MinMaxFree = true) (hsafe : P.BitSafe X ρ V.isNaN) :
    ∀ {n₁ n₂ : Nat}, P.runS X ρ n₁ → P.runS X ρ n₂ → n₁ = n₂ :=
  fun h₁ h₂ => Prog.runS_unique_of_detCongr (detCongr_toFP X) ρ P hmm hsafe h₁ h₂

/-- Tier corollary of `Prog.runS_unique_of_minMaxFree_of_bitSafe_nan`. -/
theorem Prog.runT_eq_of_tierSound_of_minMaxFree_of_bitSafe_nan (X : Extra f)
    {τ₁ τ₂ : Tier f} (h₁ : TierSound X τ₁) (h₂ : TierSound X τ₂) (ρ : Nat → V f)
    (P : Prog f) (hmm : P.MinMaxFree = true) (hsafe : P.BitSafe X ρ V.isNaN) :
    P.runT τ₁ ρ = P.runT τ₂ ρ :=
  Prog.runS_unique_of_minMaxFree_of_bitSafe_nan X ρ P hmm hsafe
    (Prog.runS_runT_of_tierSound h₁ P ρ) (Prog.runS_runT_of_tierSound h₂ P ρ)

end Toy.FloatTier
