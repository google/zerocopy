import ToyUnits.FreeTheorem
import ToyUnits.AffineExamples

/-!
# Examples for the definitions and non-vacuity witnesses for the main results
-/

namespace Toy.Units

/-! ## Dimensions and scale factors -/

/-- `Dim.mul L L` has exponent `2`; `Dim.div L L` is dimensionless. -/
theorem dim_examples : Dim.mul L L 0 = 2 ∧ Dim.div L L = Dim.one := by
  refine ⟨rfl, ?_⟩; funext i; simp [Dim.div, Dim.one, L]

/-- Negative example: an area is not a length. -/
theorem dim_area_ne_length : Dim.mul L L ≠ L := by
  intro h; have := congrFun h 0; simp [Dim.mul, L] at this

/-- `scaleOf` (positive): switching from metres to millimetres (`t = 1000`) multiplies lengths by
`1000` and areas by `1000000`. -/
theorem scaleOf_mm_examples :
    scaleOf (fun _ => (1000 : Rat)) L = 1000 ∧
      scaleOf (fun _ => (1000 : Rat)) (Dim.mul L L) = 1000000 := by
  rw [scaleOf_L ratLaws.toCommRingLaws, scaleOf_mul_L_L ratLaws.toCommRingLaws]
  constructor <;> grind

/-- `scaleOf` (negative): areas do not scale like lengths. -/
theorem scaleOf_area_ne_length : scaleOf (fun _ => (1000 : Rat)) (Dim.mul L L) ≠ 1000 := by
  rw [scaleOf_mul_L_L ratLaws.toCommRingLaws]; grind

/-- `Positive`: `1000` is admitted, `-1` is rejected. -/
theorem positive_examples :
    Positive (m := 1) (fun _ => (1000 : Rat)) ∧ ¬ Positive (m := 1) (fun _ => (-1 : Rat)) := by
  refine ⟨fun _ => by grind, fun h => ?_⟩
  have := h 0; grind

/-- Laws (negative): `Int` with the inverse `fun _ => 0` violates `MulInvLaw`. -/
@[instance_reducible] def intOps : ScalarOps Int where
  inv _ := 0

theorem intOps_not_mulInv : ¬ @MulInvLaw Int intOps := by
  intro h
  have := h 2 (by decide)
  exact absurd this (by decide)

/-! ## Readings and unit changes -/

/-- `Expr.evalIn`: the literal "3 reference lengths" reads `3000` in a unit system with
`t = 1000`; a dimensionless literal `3` reads `3` in every unit system. -/
theorem evalIn_lit_examples (ρ : Env Rat) :
    (Expr.lit (3 : Rat) L).evalIn (fun _ => 1000) ρ = 3000 ∧
      (Expr.lit (3 : Rat) (Dim.one (m := 1))).evalIn (fun _ => 1000) ρ = 3 := by
  simp only [Expr.evalIn, scaleOf_L ratLaws.toCommRingLaws,
    scaleOf_dimOne_fin1 ratLaws.toCommRingLaws]
  constructor <;> grind

/-- `actEnv`: a length reading `3` becomes `3000` under `t = 1000`. -/
theorem actEnv_example : actEnv ctxL (fun _ => (1000 : Rat)) (fun _ => 3) 0 = 3000 := by
  simp only [actEnv, ctxL, scaleOf_L ratLaws.toCommRingLaws]; grind

/-- `unitChangeStep` (positive): from the reference units to `t = 1000`. -/
theorem unitChangeStep_example (ρ : Env Rat) :
    unitChangeStep ctxL ⟨((fun _ => 1), ρ), fun _ => (by decide : (0 : Rat) < 1)⟩
      ⟨((fun i => (fun _ => (1000 : Rat)) i * (fun _ => (1 : Rat)) i),
        actEnv ctxL (fun _ => 1000) ρ), fun _ => (by grind : (0 : Rat) < 1000 * 1)⟩ :=
  ⟨fun _ => 1000, positive_examples.1, rfl⟩

/-- `unitChangeStep` (negative): changing the unit system from `1` to `2` without transforming the
readings is not a unit-change step. -/
theorem unitChangeStep_readings_unchanged_not :
    ¬ unitChangeStep ctxL ⟨((fun _ => (1 : Rat)), fun _ => 1), fun _ => (by decide : (0 : Rat) < 1)⟩
      ⟨((fun _ => (2 : Rat)), fun _ => 1), fun _ => (by decide : (0 : Rat) < 2)⟩ := by
  rintro ⟨t, ht, h⟩
  have h1 := congrFun (congrArg Prod.fst h) 0
  have h2 := congrFun (congrArg Prod.snd h) 0
  simp only [actEnv, ctxL, scaleOf_L ratLaws.toCommRingLaws] at h1 h2
  grind

/-- `WellTypedAt` (negative): `0 ≤ x` is not well typed when no order atom is allowed. -/
theorem nonnegL_not_wellTypedAt_noOrder : ¬ WellTypedAt (fun _ => False) ctxL nonnegL := by
  intro h
  obtain ⟨d, hd, -, -⟩ := wellTypedAt_le_inv h
  exact hd

/-- `HasDim` (positive): `x * x` is an area. -/
theorem hasDim_area_example : HasDim ctxL (Expr.mul (K := Rat) (.var 0) (.var 0)) (Dim.mul L L) :=
  .mul (.var 0) (.var 0)

/-- `HasDim` (negative): `x + x * x` has no dimension. -/
theorem hasDim_sumMixed_none (d : Dim 1) :
    ¬ HasDim ctxL (Expr.add (K := Rat) (.var 0) (.mul (.var 0) (.var 0))) d := by
  intro h
  obtain ⟨ha, hb⟩ := hasDim_add_inv h
  obtain ⟨d₁, d₂, hc, hd, e2⟩ := hasDim_mul_inv hb
  rw [hasDim_var_inv hc, hasDim_var_inv hd] at e2
  have := congrFun ((hasDim_var_inv ha).symm.trans e2) 0
  simp [ctxL, L, Dim.mul] at this

/-! ## One-variable expressions -/

/-- `OneVarLength` (negative): `x + lit 1 L` has a dimensioned literal. -/
theorem addOneLength_not_oneVarLength : ¬ OneVarLength ctxL 0 addOneLength :=
  fun h => addOneLength_control.2.2.1 h.dimless

/-- `Expr.isPolynomial` (negative): `x * (1 / x)` uses division. -/
theorem xTimesInvX_not_polynomial : ¬ xTimesInvX.isPolynomial := fun h => h.2.elim

/-- `DefinableOnPos` (positive): `v ↦ 2 * v`. -/
theorem definableOnPos_two_mul : DefinableOnPos (fun v : Rat => 2 * v) :=
  (definableOnPos_iff ratLaws ratInvZero _).2 ⟨2, fun _ _ => rfl⟩

/-! ## Non-vacuity witnesses (every hypothesis of the named result holds) -/

/-- `∀ y : L, x ≤ y ∨ y ≤ x` with `x` a length: a well-typed quantified formula. -/
def quantL : Formula 1 Rat := .all 1 L (.or (.le (.var 0) (.var 1)) (.le (.var 1) (.var 0)))

theorem quantL_wellTyped : WellTyped ctxL quantL :=
  .all (.or (.le trivial (.var 0) (.var 1)) (.le trivial (.var 1) (.var 0)))

/-- Hypotheses of `evalIn_act_eq_scaleOf_mul` hold together. -/
theorem nonvacuous_homogeneity :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ HasDim ctxL xTimesInvX (Dim.mul L (Dim.div Dim.one L)) ∧
      (∀ i : Fin 1, (fun _ => (2 : Rat)) i ≠ 0) :=
  ⟨ratLaws.toFieldLaws, ratInvZero, xTimesInvX_hasDim, fun _ => (by decide : (2 : Rat) ≠ 0)⟩

/-- Hypotheses of `invariantAt_of_wellTypedAt` hold together (order atoms everywhere, `t = 2`). -/
theorem nonvacuous_engine :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (2 : Rat)) i ≠ 0) ∧
      (∀ d : Dim 1, (fun _ => True) d → ∀ a b : Rat,
        scaleOf (fun _ => (2 : Rat)) d * a ≤ scaleOf (fun _ => (2 : Rat)) d * b ↔ a ≤ b) ∧
      WellTypedAt (fun _ => True) ctxL quantL :=
  ⟨ratLaws.toFieldLaws, ratInvZero, fun _ => (by decide : (2 : Rat) ≠ 0),
    fun d _ _ _ => mul_le_mul_left_iff' ratLaws
      (scaleOf_pos ratLaws (fun _ => (by decide : (0 : Rat) < 2)) d),
    quantL_wellTyped⟩

/-- Hypotheses of `unitInvariant_of_wellTyped` hold together, for a quantified formula. -/
theorem nonvacuous_unitInvariant_of_wellTyped :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ WellTyped ctxL quantL :=
  ⟨ratLaws, ratInvZero, quantL_wellTyped⟩

/-- Hypotheses of `invariantAt_of_wellTypedAt_noOrder_of_ne_zero` hold together, at `t = -1`. -/
theorem nonvacuous_noOrder :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) ∧
      WellTypedAt (fun _ => False) ctxL eqXY :=
  ⟨ratLaws.toFieldLaws, ratInvZero, fun _ => (by decide : (-1 : Rat) ≠ 0), eqXY_wellTypedAt_noOrder⟩

/-- Hypotheses of `invariantAt_all_wellTypedAt_iff` hold together, at `t = -1`. -/
theorem nonvacuous_characterization :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) :=
  ⟨ratLaws, ratInvZero, fun _ => (by decide : (-1 : Rat) ≠ 0)⟩

/-- `∀ t₂ : pt, t₁ ≤ t₂ ∨ t₂ ≤ t₁` for a temperature reading `t₁`. -/
def quantPt : AFormula Rat := .all 1 .pt (.or (.le (.var 0) (.var 1)) (.le (.var 1) (.var 0)))

theorem quantPt_pointVectorTyped : PointVectorTyped WeightsSumOne sortsPt quantPt :=
  .all (.or (.le (.var 0) (.var 1)) (.le (.var 1) (.var 0)))

/-- Hypotheses of `affineInvariant_of_pointVectorTyped` hold together (an affine combination and a
quantified formula). -/
theorem nonvacuous_affine :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ PointVectorTyped WeightsSumOne sortsPt meanLe ∧
      PointVectorTyped WeightsSumOne sortsPt quantPt :=
  ⟨ratLaws, ratInvZero, meanLe_pointVectorTyped, quantPt_pointVectorTyped⟩

/-- `3 * (x ^ 3 / (x * x))`: a non-polynomial one-variable expression of dimension `L`. -/
def cubeOverSquare : Expr 1 Rat :=
  .mul (.lit 3 Dim.one) (.div (.zpow (.var 0) 3) (.mul (.var 0) (.var 0)))

theorem cubeOverSquare_oneVarLength : OneVarLength ctxL 0 cubeOverSquare where
  ctx_x := rfl
  typed := by
    have e : Dim.mul Dim.one (Dim.div (Dim.pow L 3) (Dim.mul L L)) = L := by
      funext i; simp [Dim.mul, Dim.div, Dim.pow, Dim.one, L]
    exact e ▸ HasDim.mul (HasDim.lit 3 Dim.one)
      (HasDim.div (HasDim.zpow 3 (HasDim.var 0)) (HasDim.mul (HasDim.var 0) (HasDim.var 0)))
  only_x := ⟨trivial, ⟨rfl, ⟨rfl, rfl⟩⟩⟩
  dimless := ⟨rfl, ⟨trivial, ⟨trivial, trivial⟩⟩⟩

/-- Hypotheses of `oneVarLength_eval_eq_mul` hold together (over `Rat`, a non-polynomial
expression). -/
theorem nonvacuous_oneVarLength :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ OneVarLength ctxL 0 cubeOverSquare :=
  ⟨ratLaws.toFieldLaws, ratInvZero, cubeOverSquare_oneVarLength⟩

/-- No ordered-field law can hold on `GF2`: `1 + 1 = 0` there. -/
theorem gf2_not_orderedFieldLaws : ¬ OrderedFieldLaws GF2 :=
  fun h => one_add_one_ne_zero' h gf2_one_add_one_eq_zero

/-- Hypotheses of `oneVarLength_eval_eq_mul` hold together over `GF2`, a field with `0⁻¹ = 0`
that admits no ordered-field laws. -/
theorem nonvacuous_oneVarLength_gf2 :
    FieldLaws GF2 ∧ InvZeroLaw GF2 ∧ ¬ OrderedFieldLaws GF2 ∧
      OneVarLength ctxL 0 (linearWitness (1 : GF2)) :=
  ⟨gf2_fieldLaws, gf2_invZero, gf2_not_orderedFieldLaws, linearWitness_oneVarLength 1⟩

/-- `2 * x + x - x` with `x` a length: a polynomial one-variable expression of dimension `L`. -/
def polyWitness : Expr 1 Rat := .sub (.add (.mul (.lit 2 Dim.one) (.var 0)) (.var 0)) (.var 0)

theorem polyWitness_oneVarLength : OneVarLength ctxL 0 polyWitness where
  ctx_x := rfl
  typed := .sub (.add (dim_one_mul_L ▸ HasDim.mul (HasDim.lit 2 Dim.one) (HasDim.var 0))
    (HasDim.var 0)) (HasDim.var 0)
  only_x := ⟨⟨⟨trivial, rfl⟩, rfl⟩, rfl⟩
  dimless := ⟨⟨⟨rfl, trivial⟩, trivial⟩, trivial⟩

/-- Hypotheses of `oneVarLength_poly_eval_eq_mul` hold together. -/
theorem nonvacuous_poly :
    CommRingLaws Rat ∧ HasDim ctxL polyWitness L ∧ polyWitness.onlyVar 0 ∧
      polyWitness.dimlessLits ∧ polyWitness.isPolynomial :=
  ⟨ratLaws.toCommRingLaws, polyWitness_oneVarLength.typed, polyWitness_oneVarLength.only_x,
    polyWitness_oneVarLength.dimless, ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩⟩

end Toy.Units
