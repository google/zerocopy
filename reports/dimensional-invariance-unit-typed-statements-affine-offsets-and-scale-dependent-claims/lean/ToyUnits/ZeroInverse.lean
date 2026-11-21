import ToyUnits.Tightness

/-!
# The convention `0⁻¹ = 0` is exactly what homogeneity of typed expressions needs

With at least one base dimension, and over a field that has an element other than `0` and `1`,
every well-typed expression is homogeneous under every unit change with nonzero factors if and
only if the total division returns `0` at a zero denominator.
-/

namespace Toy.Units

variable {m : Nat} {K : Type} [ScalarOps K]

/-- Homogeneity of every well-typed expression: for every context `Γ`, expression `e` of
dimension `d`, unit change `t` with nonzero factors, unit system `s` and readings `ρ`, the reading
after the change is `scaleOf t d` times the reading before. -/
def AllHomogeneous (m : Nat) (K : Type) [ScalarOps K] : Prop :=
  ∀ (Γ : Ctx m) (e : Expr m K) (d : Dim m), HasDim Γ e d → ∀ t : Fin m → K, (∀ i, t i ≠ 0) →
    ∀ (s : Fin m → K) (ρ : Env K),
      Expr.evalIn (fun i => t i * s i) (actEnv Γ t ρ) e = scaleOf t d * Expr.evalIn s ρ e

/-- The dimension of the first base dimension: exponent `1` there, `0` elsewhere. -/
def unitDim (m : Nat) : Dim (m + 1) := fun i => if i = 0 then 1 else 0

theorem scaleOf_const_unitDim (h : CommRingLaws K) (a : K) :
    scaleOf (fun _ : Fin (m + 1) => a) (unitDim m) = a := by
  show zpow a (unitDim m 0) * finProd m (fun i => zpow a (unitDim m i.succ)) = a
  have h0 : unitDim m 0 = 1 := by simp [unitDim]
  have h1 : ∀ i : Fin m, zpow a (unitDim m i.succ) = 1 := by
    intro i
    have e : unitDim m i.succ = 0 := by simp [unitDim, Fin.succ_ne_zero]
    rw [e]
    rfl
  rw [h0, finProd_congr m _ _ h1, finProd_one h m, h.mul_one]
  exact npow_one h a

theorem scaleOf_one_units (h : FieldLaws K) (d : Dim m) : scaleOf (fun _ => (1 : K)) d = 1 := by
  unfold scaleOf
  rw [finProd_congr m _ _ (fun i => zpow_one_base h (d i))]
  exact finProd_one h.toCommRingLaws m

/-- **`0⁻¹ = 0` is exactly the convention under which typed expressions are homogeneous.** Under
the field laws, if the scalars contain an element other than `0` and `1`, then (with at least one
base dimension) every well-typed expression is homogeneous under every unit change with nonzero
factors if and only if `0⁻¹ = 0`. -/
theorem allHomogeneous_iff_invZero (h : FieldLaws K) (h2 : ∃ a : K, a ≠ 0 ∧ a ≠ 1) :
    AllHomogeneous (m + 1) K ↔ InvZeroLaw K := by
  have hR := h.toCommRingLaws
  constructor
  · intro H
    obtain ⟨a, ha0, ha1⟩ := h2
    have he : HasDim (fun _ => unitDim m) (Expr.div (K := K) (.var 0) (.var 1))
        (Dim.div (unitDim m) (unitDim m)) := .div (.var 0) (.var 1)
    have hdd : Dim.div (unitDim m) (unitDim m) = Dim.one := by
      funext i; simp [Dim.div, Dim.one]
    have hH := H _ _ _ he (fun _ => a) (fun _ => ha0) (fun _ => 1)
      (fun x => if x = 1 then 0 else 1)
    rw [hdd, scaleOf_one_dim h] at hH
    simp (config := { decide := true }) only [Expr.evalIn, actEnv, ite_true, ite_false] at hH
    rw [scaleOf_const_unitDim hR, h.mul_one, mul_zero' hR, one_mul' hR, one_mul' hR] at hH
    refine Classical.byContradiction fun hj => ha1 ?_
    have e : (0 : K)⁻¹ * a = (0 : K)⁻¹ * 1 := by rw [h.mul_one, h.mul_comm]; exact hH
    exact mul_left_cancel₀' h hj e
  · intro hz Γ e d he t ht s ρ
    exact evalIn_act_eq_scaleOf_mul h hz he ht s ρ

/-- `AllHomogeneous` (positive): `Rat`, with `0⁻¹ = 0`, has it for every number of base
dimensions. -/
theorem allHomogeneous_rat (m : Nat) : AllHomogeneous m Rat :=
  fun _ _ _ he _ ht s ρ => evalIn_act_eq_scaleOf_mul ratLaws.toFieldLaws ratInvZero he ht s ρ

/-- `AllHomogeneous` (negative): `RatJ`, with `0⁻¹ = 1`, does not have it (`divXY` at `y = 0`). -/
theorem not_allHomogeneous_ratJ : ¬ AllHomogeneous 1 RatJ := fun H =>
  divXY_not_homogeneous_ratJ.2.2.2.2
    (H ctxL divXY _ divXY_not_homogeneous_ratJ.2.2.1 _ divXY_not_homogeneous_ratJ.2.2.2.1 _ _)

/-- Hypotheses of `allHomogeneous_iff_invZero` hold together (`Rat`, with `a = 2`). -/
theorem nonvacuous_allHomogeneous_iff : FieldLaws Rat ∧ ∃ a : Rat, a ≠ 0 ∧ a ≠ 1 :=
  ⟨ratLaws.toFieldLaws, 2, by decide, by decide⟩

/-- **The element other than `0` and `1` is needed.** Over `GF2J` (the two-element field with
`0⁻¹ = 1`) the field laws hold and every element is `0` or `1`; with one base dimension every
nonzero unit change is the identity, so all typed expressions are homogeneous, yet `0⁻¹ ≠ 0`:
the equivalence fails. -/
theorem allHomogeneous_iff_fails_gf2J :
    FieldLaws GF2J ∧ ¬ (∃ a : GF2J, a ≠ 0 ∧ a ≠ 1) ∧
      ¬ (AllHomogeneous (0 + 1) GF2J ↔ InvZeroLaw GF2J) := by
  have hF := gf2J_fieldLaws
  have hR := hF.toCommRingLaws
  have hAll : AllHomogeneous (0 + 1) GF2J := by
    intro Γ e d _ t ht s ρ
    have htone : t = fun _ => 1 := by
      funext i
      rcases gf2J_eq_zero_or_one (t i) with h0 | h1
      · exact absurd h0 (ht i)
      · exact h1
    subst htone
    have hs : (fun i => (fun _ => (1 : GF2J)) i * s i) = s := by
      funext i; exact one_mul' hR (s i)
    have hρ : actEnv Γ (fun _ => (1 : GF2J)) ρ = ρ := by
      funext x; simp only [actEnv]; rw [scaleOf_one_units hF, one_mul' hR]
    rw [hs, hρ, scaleOf_one_units hF, one_mul' hR]
  refine ⟨hF, ?_, fun hiff => gf2J_not_invZero (hiff.1 hAll)⟩
  rintro ⟨a, h0, h1⟩
  rcases gf2J_eq_zero_or_one a with e | e
  · exact h0 e
  · exact h1 e

/-- **At least one base dimension is needed.** Over `RatJ` (field laws, `2 ∉ {0, 1}`) with no base
dimension, every scale factor is `1`, so all typed expressions are homogeneous, yet `0⁻¹ ≠ 0`:
the equivalence fails. -/
theorem allHomogeneous_iff_fails_zero_dims_ratJ :
    FieldLaws RatJ ∧ (∃ a : RatJ, a ≠ 0 ∧ a ≠ 1) ∧
      ¬ (AllHomogeneous 0 RatJ ↔ InvZeroLaw RatJ) := by
  have hR := ratJLaws.toCommRingLaws
  have hAll : AllHomogeneous 0 RatJ := by
    intro Γ e d _ t _ s ρ
    have hs : (fun i => t i * s i) = s := by funext i; exact i.elim0
    have hρ : actEnv Γ t ρ = ρ := by
      funext x; simp only [actEnv]; exact one_mul' hR (ρ x)
    rw [hs, hρ]
    exact (one_mul' hR _).symm
  refine ⟨ratJLaws.toFieldLaws, ⟨RatJ.ofRat 2, fun e => absurd (show (2 : Rat) = 0 from e)
    (by decide), fun e => absurd (show (2 : Rat) = 1 from e) (by decide)⟩,
    fun hiff => ratJ_not_invZero (hiff.1 hAll)⟩

end Toy.Units
