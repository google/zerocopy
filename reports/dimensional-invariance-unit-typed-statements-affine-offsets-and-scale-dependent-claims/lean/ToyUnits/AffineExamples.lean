import ToyUnits.Affine

/-!
# Affine units: counterexamples, tightness witnesses and examples

The reference temperature scale is Celsius, `celsius = (1, 0)`; the change to Kelvin is
`celsiusToKelvin = (1, 5463/20)` (that is, `x ↦ x + 273.15`); the change to Fahrenheit is
`celsiusToFahrenheit = (9/5, 32)`.
-/

namespace Toy.Units

/-- The reference temperature scale (Celsius). -/
def celsius : Rat × Rat := (1, 0)
/-- The scale change from Celsius to Kelvin: `x ↦ x + 273.15`. -/
def celsiusToKelvin : Rat × Rat := (1, 5463 / 20)
/-- The scale change from Celsius to Fahrenheit: `x ↦ (9/5) * x + 32`. -/
def celsiusToFahrenheit : Rat × Rat := (9 / 5, 32)

/-- Every variable is a temperature reading (a point). -/
def sortsPt : Nat → ASort := fun _ => .pt

theorem hasSort_var_inv {K : Type} {W : K → K → Prop} {S : Nat → ASort} {x : Nat} {σ : ASort}
    (h : HasSort W S (.var x) σ) : σ = S x := by
  cases h; rfl

/-! ## Examples for the definitions -/

/-- `ASort.act`: 20 °C reads 293.15 K; a difference of 5 °C reads 5 K; 100 °C reads 212 °F. -/
theorem act_examples :
    ASort.pt.act celsiusToKelvin 20 = 5863 / 20 ∧ ASort.vec.act celsiusToKelvin 5 = 5 ∧
      ASort.pt.act celsiusToFahrenheit 100 = 212 := by
  simp only [ASort.act, celsiusToKelvin, celsiusToFahrenheit]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- `ASort.act` (negative): a temperature difference does not receive the offset. -/
theorem act_vec_no_offset : ASort.vec.act celsiusToKelvin 5 ≠ 5 + 5463 / 20 := by
  simp only [ASort.act, celsiusToKelvin]; grind

/-- `WeightsSumOne`: `(1/2, 1/2)` is admitted, `(1, 1)` is rejected. -/
theorem weightsSumOne_examples :
    WeightsSumOne (1 / 2 : Rat) (1 / 2) ∧ ¬ WeightsSumOne (1 : Rat) 1 := by
  unfold WeightsSumOne; constructor <;> grind

/-- `HasSort` (positive): the difference of two temperature readings is a temperature difference. -/
theorem hasSort_ptSubPt_example :
    HasSort (WeightsSumOne (K := Rat)) sortsPt (.sub (.var 0) (.var 1)) .vec :=
  .ptSubPt (.var 0) (.var 1)

/-- `HasSort` (negative): the sum of two temperature readings has no sort. -/
theorem hasSort_sum_none (σ : ASort) :
    ¬ HasSort (WeightsSumOne (K := Rat)) sortsPt (.add (.var 0) (.var 1)) σ := by
  intro h
  cases h with
  | ptAddVec _ h₂ => have := hasSort_var_inv h₂; cases this
  | vecAddPt h₁ _ => have := hasSort_var_inv h₁; cases this
  | vecAdd h₁ _ => have := hasSort_var_inv h₁; cases this
  | numAdd h₁ _ => have := hasSort_var_inv h₁; cases this

/-- `ADimChecked` (positive): the sum of two temperature readings has exponent `1`. -/
theorem aDimChecked_sum_example :
    ADimChecked (K := Rat) sortsPt (.add (.var 0) (.var 1)) 1 := .add (.var 0) (.var 1)

/-- `ADimChecked` (negative): a temperature plus a dimensionless literal has no exponent. -/
theorem aDimChecked_mixed_none (k : Int) :
    ¬ ADimChecked (K := Rat) sortsPt (.add (.var 0) (.lit 1 .num)) k := by
  intro h
  cases h with
  | add h₁ h₂ => cases h₁; cases h₂

/-! ## Dimension checking over-claims -/

/-- `t₁ + t₂ ≤ t₃` for three temperature readings. -/
def sumTemps : AFormula Rat := .le (.add (.var 0) (.var 1)) (.var 2)

theorem sumTemps_dimChecked : ADimCheckedF sortsPt sumTemps :=
  .le (.add (.var 0) (.var 1)) (.var 2)

theorem sumTemps_not_pointVectorTyped : ¬ PointVectorTyped WeightsSumOne sortsPt sumTemps := by
  intro h
  cases h with
  | le h₁ _ => exact hasSort_sum_none _ h₁

/-- Readings `t₁ = t₂ = -10`, `t₃ = 0` (in °C). -/
def sumTempsEnv : Env Rat := fun x => if x = 2 then 0 else -10

/-- **Counterexample (offset units).** The dimension-checked `t₁ + t₂ ≤ t₃` holds in °C at
`t₁ = t₂ = -10, t₃ = 0` (`-20 ≤ 0`) and fails for the same temperatures in K
(`263.15 + 263.15 ≤ 273.15`). -/
theorem sumTemps_celsius_kelvin :
    ADimCheckedF sortsPt sumTemps ∧
    AFormula.holdsIn celsius sumTempsEnv sumTemps ∧
    ¬ AFormula.holdsIn (celsiusToKelvin.1 * celsius.1, celsiusToKelvin.1 * celsius.2 + celsiusToKelvin.2)
        (actA sortsPt celsiusToKelvin sumTempsEnv) sumTemps := by
  refine ⟨sumTemps_dimChecked, ?_, ?_⟩
  · simp only [sumTemps, AFormula.holdsIn, AExpr.evalIn, sumTempsEnv]
    simp (config := { decide := true }) only [ite_true, ite_false]; grind
  · simp only [sumTemps, AFormula.holdsIn, AExpr.evalIn, actA, sortsPt, ASort.act,
      sumTempsEnv, celsiusToKelvin]
    simp (config := { decide := true }) only [ite_true, ite_false]; grind

/-- **Offset units: dimension checking over-claims.** The formula `t₁ + t₂ ≤ t₃` over temperature
readings passes plain dimension checking, is rejected by the point/vector discipline, and is not
invariant under positive affine scale changes between scales with positive factor: from °C to K
it flips (`sumTemps_celsius_kelvin`). -/
theorem sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant :
    ADimCheckedF sortsPt sumTemps ∧ ¬ PointVectorTyped WeightsSumOne sortsPt sumTemps ∧
      ¬ PosAffineInvariant sortsPt sumTemps := by
  refine ⟨sumTemps_dimChecked, sumTemps_not_pointVectorTyped, fun h => ?_⟩
  have hg : (0 : Rat) < celsiusToKelvin.1 := by simp only [celsiusToKelvin]; decide
  have hu : (0 : Rat) < celsius.1 := by simp only [celsius]; decide
  have hgu : (0 : Rat) < celsiusToKelvin.1 * celsius.1 := by
    simp only [celsiusToKelvin, celsius]; grind
  have := (h celsiusToKelvin celsius sumTempsEnv hg hu hgu).2 sumTemps_celsius_kelvin.2.1
  exact sumTemps_celsius_kelvin.2.2 this

/-- **Counterexample in canonical form (typing hypothesis of `affineInvariant_of_pointVectorTyped`).**
The ordered-field laws and `0⁻¹ = 0` hold for `Rat`; `t₁ + t₂ ≤ t₃` is not typed by the
point/vector discipline and is not `AffineInvariant`. -/
theorem sumTemps_affine_tight :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ ¬ PointVectorTyped WeightsSumOne sortsPt sumTemps ∧
      ¬ AffineInvariant sortsPt sumTemps :=
  ⟨ratLaws, ratInvZero, sumTemps_not_pointVectorTyped, fun h =>
    sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant.2.2
      (posAffineInvariant_of_affineInvariant h)⟩

/-! ## The mean of two temperatures -/

/-- `(1/2) t₁ + (1/2) t₂ ≤ t₃` for three temperature readings. -/
def meanLe : AFormula Rat := .le (.comb (1 / 2) (.var 0) (1 / 2) (.var 1)) (.var 2)

theorem meanLe_pointVectorTyped : PointVectorTyped WeightsSumOne sortsPt meanLe :=
  .le (.combPt (1 / 2) (1 / 2) weightsSumOne_examples.1 (.var 0) (.var 1)) (.var 2)

/-! ## Tightness witnesses for `affineInvariant_of_pointVectorTyped` -/

/-- `t₁ ≤ t₂` for two temperature readings. -/
def ptLe : AFormula Rat := .le (.var 0) (.var 1)

theorem ptLe_pointVectorTyped : PointVectorTyped WeightsSumOne sortsPt ptLe := .le (.var 0) (.var 1)

/-- **Counterexample (`a > 0` in `AffineInvariant` matters).** The scale change `x ↦ -x` reverses the
typed comparison `t₁ ≤ t₂` at `t₁ = 0, t₂ = 1`. -/
theorem ptLe_not_invariant_neg :
    PointVectorTyped WeightsSumOne sortsPt ptLe ∧
    ¬ (AFormula.holdsIn (((-1 : Rat), (0 : Rat)).1 * celsius.1,
          ((-1 : Rat), (0 : Rat)).1 * celsius.2 + ((-1 : Rat), (0 : Rat)).2)
        (actA sortsPt ((-1 : Rat), (0 : Rat)) (fun x => if x = 0 then 0 else 1)) ptLe ↔
      AFormula.holdsIn celsius (fun x => if x = 0 then 0 else 1) ptLe) := by
  refine ⟨ptLe_pointVectorTyped, ?_⟩
  simp only [ptLe, AFormula.holdsIn, AExpr.evalIn, actA, sortsPt, ASort.act]
  simp (config := { decide := true }) only [ite_true, ite_false]
  grind

/-- `t₁ + t₂ ≤ t₃` written as the affine combination with weights `(1, 1)`. -/
def combSumLe : AFormula Rat := .le (.comb 1 (.var 0) 1 (.var 1)) (.var 2)

/-- **Counterexample in canonical form (the weight condition is needed).** The ordered-field laws
and `0⁻¹ = 0` hold for `Rat`; with arbitrary weights allowed, `1 * t₁ + 1 * t₂ ≤ t₃` is typed, its
weights `(1, 1)` do not sum to one, and it is not `AffineInvariant` (°C to K at
`t₁ = t₂ = -10, t₃ = 0`). -/
theorem combSumLe_weights_tight :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ PointVectorTyped (fun _ _ => True) sortsPt combSumLe ∧
      ¬ WeightsSumOne (1 : Rat) 1 ∧ ¬ AffineInvariant sortsPt combSumLe := by
  refine ⟨ratLaws, ratInvZero, .le (.combPt 1 1 trivial (.var 0) (.var 1)) (.var 2),
    weightsSumOne_examples.2, fun h => ?_⟩
  have hg : (0 : Rat) < celsiusToKelvin.1 := by simp only [celsiusToKelvin]; decide
  have := (h celsiusToKelvin hg celsius sumTempsEnv).2
  simp only [combSumLe, AFormula.holdsIn, AExpr.evalIn, actA, sortsPt, ASort.act,
    sumTempsEnv, celsiusToKelvin] at this
  simp (config := { decide := true }) only [ite_true, ite_false] at this
  grind

/-- `(t₁ - t₂) / (t₃ - t₃) ≤ 1` over `RatJ` (a ratio of temperature differences). -/
def ratioLe : AFormula RatJ :=
  .le (.div (.sub (.var 0) (.var 1)) (.sub (.var 2) (.var 2))) (.lit 1 .num)

theorem ratioLe_pointVectorTyped : PointVectorTyped WeightsSumOne sortsPt ratioLe :=
  .le (.vecDivVec (.ptSubPt (.var 0) (.var 1)) (.ptSubPt (.var 2) (.var 2))) (.lit 1 .num)

/-- **Counterexample (`0⁻¹ = 0` is needed).** Over `RatJ` (`0⁻¹ = 1`, every ordered-field law),
the typed `(t₁ - t₂) / (t₃ - t₃) ≤ 1` is not invariant under `x ↦ 2 * x`: at
`t₁ = 1, t₂ = t₃ = 0` it reads `1 * 1 ≤ 1` before and `2 * 1 ≤ 1` after. -/
theorem ratioLe_not_affineInvariant_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ PointVectorTyped WeightsSumOne sortsPt ratioLe ∧
      ¬ AffineInvariant sortsPt ratioLe := by
  refine ⟨ratJLaws, ratJ_not_invZero, ratioLe_pointVectorTyped, fun h => ?_⟩
  have hg : (0 : RatJ) < (RatJ.ofRat 2, RatJ.ofRat 0).1 := (by decide : (0 : Rat) < 2)
  have := (h (RatJ.ofRat 2, RatJ.ofRat 0) hg (1, 0)
    (fun x => if x = 0 then RatJ.ofRat 1 else RatJ.ofRat 0)).2
  simp (config := { decide := true }) only [ratioLe, AFormula.holdsIn, AExpr.evalIn, actA,
    sortsPt, ASort.act, ite_true, ite_false] at this
  simp only [RatJ.one_def, RatJ.mul_def, RatJ.add_def, RatJ.neg_def,
    RatJ.inv_def, RatJ.le_def] at this
  grind

/-! ## Degenerate scales -/

/-- `1 + 1 * 1 ≤ 0` written with temperature-difference literals: `lit 1 vec + lit 1 vec * lit 1 vec
≤ lit 0 vec` (not typed by the point/vector discipline). -/
def affPosConst : AFormula Rat :=
  .le (.add (.lit 1 .vec) (.mul (.lit 1 .vec) (.lit 1 .vec))) (.lit 0 .vec)

/-- **`AffineInvariant` is strictly stronger than `PosAffineInvariant`.** `affPosConst` is false at
every scale with positive factor, hence `PosAffineInvariant`; it is not `AffineInvariant`, because
from the scale `u = (-1, 0)` the change `g = (2, 0)` flips it. -/
theorem affPosConst_posAffineInvariant_not_affineInvariant :
    PosAffineInvariant sortsPt affPosConst ∧ ¬ AffineInvariant sortsPt affPosConst := by
  have hfalse : ∀ (u : Rat × Rat), 0 < u.1 → ∀ ρ : Env Rat, ¬ AFormula.holdsIn u ρ affPosConst := by
    intro u hu ρ
    simp only [affPosConst, AFormula.holdsIn, AExpr.evalIn, ASort.act]
    have := Rat.mul_pos hu hu
    grind
  refine ⟨fun g u ρ _ hu hgu => ⟨fun h => (hfalse _ hgu _ h).elim, fun h => (hfalse _ hu _ h).elim⟩,
    fun h => ?_⟩
  have h2 := (h (2, 0) (by decide) (-1, 0) (fun _ => 0)).2
  simp only [affPosConst, AFormula.holdsIn, AExpr.evalIn, ASort.act] at h2
  have := h2 (by grind)
  grind

end Toy.Units
