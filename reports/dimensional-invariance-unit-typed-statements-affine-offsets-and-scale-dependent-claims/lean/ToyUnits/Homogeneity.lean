import ToyUnits.Syntax

/-!
# Dimension typing gives invariance; positivity for order atoms

* `evalIn_act_eq_scaleOf_mul`: a well-typed expression is homogeneous under every unit change
  with nonzero factors (field laws and `0⁻¹ = 0`).
* `invariantAt_of_wellTypedAt`: a unit change `t` with nonzero factors preserves the truth of
  every formula whose `≤` atoms lie at dimensions `d` for which multiplication by
  `scaleOf t d` preserves and reflects `≤`.
* Corollaries: invariance under positive unit changes (`unitInvariant_of_wellTyped`),
  invariance of `≤`-free formulas under nonzero unit changes, and an exact characterization
  of the unit changes that preserve every formula with order atoms in a given set.
-/

namespace Toy.Units

variable {m : Nat} {K : Type} [ScalarOps K]

section ScaleOf
variable (h : FieldLaws K)
include h

theorem scaleOf_one_dim (s : Fin m → K) : scaleOf s Dim.one = 1 := by
  unfold scaleOf Dim.one
  exact finProd_one h.toCommRingLaws m

theorem scaleOf_mul_units (hz : InvZeroLaw K) (t s : Fin m → K) (d : Dim m) :
    scaleOf (fun i => t i * s i) d = scaleOf t d * scaleOf s d := by
  unfold scaleOf
  rw [← finProd_mul h.toCommRingLaws]
  exact finProd_congr m _ _ (fun i => zpow_mul_base h hz _ _ _)

theorem scaleOf_ne_zero {t : Fin m → K} (ht : ∀ i, t i ≠ 0) (d : Dim m) : scaleOf t d ≠ 0 :=
  finProd_ne_zero h m _ (fun i => zpow_ne_zero h (ht i) _)

theorem scaleOf_dim_mul {t : Fin m → K} (ht : ∀ i, t i ≠ 0) (d e : Dim m) :
    scaleOf t (Dim.mul d e) = scaleOf t d * scaleOf t e := by
  unfold scaleOf Dim.mul
  rw [← finProd_mul h.toCommRingLaws]
  exact finProd_congr m _ _ (fun i => zpow_add h (ht i) _ _)

theorem scaleOf_dim_div (hz : InvZeroLaw K) {t : Fin m → K} (ht : ∀ i, t i ≠ 0) (d e : Dim m) :
    scaleOf t (Dim.div d e) = scaleOf t d * (scaleOf t e)⁻¹ := by
  unfold scaleOf Dim.div
  rw [finProd_inv h hz, ← finProd_mul h.toCommRingLaws]
  refine finProd_congr m _ _ (fun i => ?_)
  rw [Int.sub_eq_add_neg, zpow_add h (ht i), zpow_neg h (ht i)]

theorem scaleOf_dim_pow (hz : InvZeroLaw K) {t : Fin m → K} (ht : ∀ i, t i ≠ 0) (d : Dim m)
    (k : Int) : scaleOf t (Dim.pow d k) = zpow (scaleOf t d) k := by
  unfold scaleOf Dim.pow
  rw [finProd_zpow h hz]
  exact finProd_congr m _ _ (fun i => (zpow_zpow h (ht i) _ _).symm)

end ScaleOf

theorem scaleOf_pos (h : OrderedFieldLaws K) {t : Fin m → K} (ht : Positive t) (d : Dim m) :
    0 < scaleOf t d :=
  finProd_pos h m _ (fun i => zpow_pos h (ht i) _)

/-- Under the ordered-field laws the premise `Positive (fun i => t i * s i)` of `PosUnitInvariant`
follows from the other two. -/
theorem posUnitInvariant_iff_of_orderedField (h : OrderedFieldLaws K) (Γ : Ctx m)
    (φ : Formula m K) :
    PosUnitInvariant Γ φ ↔ ∀ t : Fin m → K, Positive t → ∀ s : Fin m → K, Positive s →
      ∀ ρ : Env K, (Formula.holdsIn (fun i => t i * s i) (actEnv Γ t ρ) φ ↔
        Formula.holdsIn s ρ φ) :=
  ⟨fun H t ht s hs ρ => H t s ρ ht hs (fun i => mul_pos' h (ht i) (hs i)),
    fun H t s ρ ht hs _ => H t ht s hs ρ⟩

/-- **Homogeneity.** Under the field laws and `0⁻¹ = 0`, for every unit change `t` with nonzero
factors, a well-typed expression `e : d` read in the changed unit system with transformed readings
equals `scaleOf t d` times its reading before the change. -/
theorem evalIn_act_eq_scaleOf_mul (h : FieldLaws K) (hz : InvZeroLaw K) {Γ : Ctx m}
    {e : Expr m K} {d : Dim m} (he : HasDim Γ e d) {t : Fin m → K} (ht : ∀ i, t i ≠ 0)
    (s : Fin m → K) (ρ : Env K) :
    Expr.evalIn (fun i => t i * s i) (actEnv Γ t ρ) e = scaleOf t d * Expr.evalIn s ρ e := by
  have hR := h.toCommRingLaws
  induction he with
  | var x => rfl
  | lit c d =>
    simp only [Expr.evalIn]
    rw [scaleOf_mul_units h hz, h.mul_assoc]
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.evalIn]; rw [ih₁, ih₂, ← h.distrib]
  | sub _ _ ih₁ ih₂ =>
    simp only [Expr.evalIn]; rw [ih₁, ih₂, ← mul_neg' hR, ← h.distrib]
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.evalIn]; rw [ih₁, ih₂, scaleOf_dim_mul h ht, mul_mul_mul_comm' hR]
  | div _ _ ih₁ ih₂ =>
    simp only [Expr.evalIn]
    rw [ih₁, ih₂, scaleOf_dim_div h hz ht, mul_inv' h hz, mul_mul_mul_comm' hR]
  | zpow k _ ih =>
    simp only [Expr.evalIn]; rw [ih, zpow_mul_base h hz, scaleOf_dim_pow h hz ht]

theorem upd_actEnv (Γ : Ctx m) (t : Fin m → K) (ρ : Env K) (x : Nat) (d : Dim m) (v : K) :
    upd (actEnv Γ t ρ) x (scaleOf t d * v) = actEnv (upd Γ x d) t (upd ρ x v) := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [upd, actEnv]
  · simp [upd, actEnv, hy]

/-- **Invariance engine.** Under the field laws and `0⁻¹ = 0`, let `t` have nonzero factors and
let every dimension `d` with `O d` satisfy: multiplication by `scaleOf t d` preserves and
reflects `≤`. Then `t` leaves the truth value of every formula that is well typed with order
atoms at dimensions in `O` unchanged. -/
theorem invariantAt_of_wellTypedAt (h : FieldLaws K) (hz : InvZeroLaw K) {O : Dim m → Prop}
    {t : Fin m → K} (ht : ∀ i, t i ≠ 0)
    (hO : ∀ d, O d → ∀ a b : K, scaleOf t d * a ≤ scaleOf t d * b ↔ a ≤ b)
    {Γ : Ctx m} {φ : Formula m K} (hφ : WellTypedAt O Γ φ) : InvariantAt Γ t φ := by
  induction hφ with
  | le hd h₁ h₂ =>
    intro s ρ
    simp only [Formula.holdsIn]
    rw [evalIn_act_eq_scaleOf_mul h hz h₁ ht, evalIn_act_eq_scaleOf_mul h hz h₂ ht]
    exact hO _ hd _ _
  | eq h₁ h₂ =>
    intro s ρ
    simp only [Formula.holdsIn]
    rw [evalIn_act_eq_scaleOf_mul h hz h₁ ht, evalIn_act_eq_scaleOf_mul h hz h₂ ht]
    constructor
    · exact mul_left_cancel₀' h (scaleOf_ne_zero h ht _)
    · intro e; rw [e]
  | and _ _ ih₁ ih₂ =>
    intro s ρ; simp only [Formula.holdsIn]; rw [ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    intro s ρ; simp only [Formula.holdsIn]; rw [ih₁, ih₂]
  | not _ ih =>
    intro s ρ; simp only [Formula.holdsIn]; rw [ih]
  | @all Γ x d φ _ ih =>
    intro s ρ
    simp only [Formula.holdsIn]
    have hS := scaleOf_ne_zero h ht d
    constructor
    · intro H v
      have := H (scaleOf t d * v)
      rwa [upd_actEnv, ih] at this
    · intro H v
      have e : v = scaleOf t d * ((scaleOf t d)⁻¹ * v) := by
        rw [← h.mul_assoc, h.mul_inv _ hS, one_mul' h.toCommRingLaws]
      rw [e, upd_actEnv, ih]
      exact H _
  | @ex Γ x d φ _ ih =>
    intro s ρ
    simp only [Formula.holdsIn]
    have hS := scaleOf_ne_zero h ht d
    constructor
    · rintro ⟨v, hv⟩
      have e : v = scaleOf t d * ((scaleOf t d)⁻¹ * v) := by
        rw [← h.mul_assoc, h.mul_inv _ hS, one_mul' h.toCommRingLaws]
      rw [e, upd_actEnv, ih] at hv
      exact ⟨_, hv⟩
    · rintro ⟨v, hv⟩
      refine ⟨scaleOf t d * v, ?_⟩
      rwa [upd_actEnv, ih]

/-- **Dimension typing gives invariance.** Under the ordered-field laws and `0⁻¹ = 0`, every
well-typed formula (quantifiers included) is invariant under every positive unit change. -/
theorem unitInvariant_of_wellTyped (h : OrderedFieldLaws K) (hz : InvZeroLaw K) {Γ : Ctx m}
    {φ : Formula m K} (hφ : WellTyped Γ φ) : UnitInvariant Γ φ := by
  intro t ht
  refine invariantAt_of_wellTypedAt h.toFieldLaws hz
    (fun i => (ne_of_lt' h (ht i)).symm) ?_ hφ
  intro d _ a b
  exact mul_le_mul_left_iff' h (scaleOf_pos h ht d)

/-- **Equality-only formulas tolerate sign changes.** Under the field laws and `0⁻¹ = 0` (no order
law), every formula that is well typed with no `≤` atom is invariant under every unit change with
nonzero (possibly negative) factors. -/
theorem invariantAt_of_wellTypedAt_noOrder_of_ne_zero (h : FieldLaws K) (hz : InvZeroLaw K)
    {t : Fin m → K} (ht : ∀ i, t i ≠ 0) {Γ : Ctx m} {φ : Formula m K}
    (hφ : WellTypedAt (fun _ => False) Γ φ) : InvariantAt Γ t φ :=
  invariantAt_of_wellTypedAt h hz ht (fun _ hd => hd.elim) hφ

/-- **Which unit changes preserve order atoms (exact).** Under the ordered-field laws and
`0⁻¹ = 0`, a unit change `t` with nonzero factors preserves the truth value of every formula that
is well typed with order atoms at dimensions in `O` if and only if `scaleOf t d > 0` for every
dimension `d` with `O d`. -/
theorem invariantAt_all_wellTypedAt_iff (h : OrderedFieldLaws K) (hz : InvZeroLaw K)
    (O : Dim m → Prop) {t : Fin m → K} (ht : ∀ i, t i ≠ 0) :
    (∀ (Γ : Ctx m) (φ : Formula m K), WellTypedAt O Γ φ → InvariantAt Γ t φ) ↔
      (∀ d, O d → 0 < scaleOf t d) := by
  constructor
  · intro H d hd
    apply (mul_le_mul_left_iff_forall_iff_pos h _).1
    intro a b
    have hφ : WellTypedAt O (fun _ => d) (Formula.le (K := K) (.var 0) (.var 1)) :=
      .le hd (.var 0) (.var 1)
    have := H _ _ hφ (fun _ => 1) (fun x => if x = 0 then a else b)
    simpa [Formula.holdsIn, Expr.evalIn, actEnv] using this
  · intro H Γ φ hφ
    refine invariantAt_of_wellTypedAt h.toFieldLaws hz ht ?_ hφ
    intro d hd a b
    exact mul_le_mul_left_iff' h (H d hd)

end Toy.Units
