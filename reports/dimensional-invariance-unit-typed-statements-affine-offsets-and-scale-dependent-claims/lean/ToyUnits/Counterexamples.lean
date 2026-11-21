import ToyUnits.Instances
import ToyUnits.PlainReading

/-!
# Counterexamples, tightness witnesses and controls for the dimension-typing results

All instances use one base dimension (`m = 1`), the length dimension `L`, and scalars `Rat`
(or `RatJ`, whose only difference from `Rat` is `0⁻¹ = 1`).
-/

namespace Toy.Units

section Compute
variable {K : Type} [ScalarOps K]

theorem scaleOf_L (h : CommRingLaws K) (t : Fin 1 → K) : scaleOf t L = t 0 := by
  show npow (t 0) 1 * 1 = t 0
  rw [h.mul_one]; exact npow_one h (t 0)

theorem scaleOf_dimOne_fin1 (h : CommRingLaws K) (t : Fin 1 → K) : scaleOf t Dim.one = 1 := by
  show (1 : K) * 1 = 1
  exact h.mul_one 1

theorem scaleOf_div_L_L (h : CommRingLaws K) (t : Fin 1 → K) : scaleOf t (Dim.div L L) = 1 := by
  show npow (t 0) 0 * 1 = 1
  exact h.mul_one 1

theorem scaleOf_mul_L_L (h : CommRingLaws K) (t : Fin 1 → K) :
    scaleOf t (Dim.mul L L) = t 0 * t 0 := by
  show npow (t 0) 2 * 1 = t 0 * t 0
  rw [h.mul_one]; show (1 * t 0) * t 0 = t 0 * t 0
  rw [one_mul' h]

end Compute

/-! ## The untyped reading is unit-dependent -/

/-- `x + x * x ≤ 2` with `x` (variable `0`) a length and the literal `2` dimensionless. -/
def sumMixed : Formula 1 Rat := .le (.add (.var 0) (.mul (.var 0) (.var 0))) (.lit 2 Dim.one)

theorem sumMixed_not_wellTyped : ¬ WellTyped ctxL sumMixed := by
  intro h
  obtain ⟨d, -, h₁, -⟩ := wellTypedAt_le_inv h
  obtain ⟨ha, hb⟩ := hasDim_add_inv h₁
  have e1 := hasDim_var_inv ha
  obtain ⟨d₁, d₂, hc, hd, e2⟩ := hasDim_mul_inv hb
  rw [hasDim_var_inv hc, hasDim_var_inv hd] at e2
  have := congrFun (e1.symm.trans e2) 0
  simp [ctxL, L, Dim.mul] at this

/-- Explicit flip: with `x = 1` in the reference units `sumMixed` holds (`1 + 1 ≤ 2`); after the
positive unit change `t = 2` it fails (`2 + 4 ≤ 2`). -/
theorem sumMixed_flips :
    Formula.holdsIn (fun _ => (1 : Rat)) (fun _ => 1) sumMixed ∧
    ¬ Formula.holdsIn (fun i => (fun _ => (2 : Rat)) i * (fun _ => (1 : Rat)) i)
        (actEnv ctxL (fun _ => 2) (fun _ => 1)) sumMixed := by
  simp only [sumMixed, Formula.holdsIn, Expr.evalIn, actEnv, ctxL,
    scaleOf_L ratLaws.toCommRingLaws, scaleOf_dimOne_fin1 ratLaws.toCommRingLaws]
  constructor <;> grind

/-- **Counterexample (untyped reading).** `sumMixed` is not well typed, and it is not invariant
under positive unit changes between positive unit systems: with `x = 1` in the reference units it
holds, after the unit change `t = 2` it fails (`sumMixed_flips`). -/
theorem sumMixed_not_wellTyped_not_posUnitInvariant :
    ¬ WellTyped ctxL sumMixed ∧ ¬ PosUnitInvariant ctxL sumMixed := by
  refine ⟨sumMixed_not_wellTyped, fun h => ?_⟩
  have := (h (fun _ => 2) (fun _ => 1) (fun _ => 1) (fun _ => (by decide : (0 : Rat) < 2))
    (fun _ => (by decide : (0 : Rat) < 1)) (fun _ => (by grind : (0 : Rat) < 2 * 1))).2
    sumMixed_flips.1
  exact sumMixed_flips.2 this

/-- **Counterexample in canonical form (typing hypothesis of `unitInvariant_of_wellTyped`).** The
ordered-field laws and `0⁻¹ = 0` hold for `Rat`, `sumMixed` is not well typed, and it is not
`UnitInvariant`. -/
theorem sumMixed_wellTyped_tight :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ ¬ WellTyped ctxL sumMixed ∧
      ¬ UnitInvariant ctxL sumMixed :=
  ⟨ratLaws, ratInvZero, sumMixed_not_wellTyped,
    fun h => sumMixed_not_wellTyped_not_posUnitInvariant.2 (posUnitInvariant_of_unitInvariant h)⟩

/-- `x ≤ 2` with `x` a length and the literal `2` written without a unit (annotated
dimensionless). -/
def dropUnitLe : Formula 1 Rat := .le (.var 0) (.lit 2 Dim.one)

/-- `x ≤ 2` with `x` a length and the literal `2` annotated as a length. -/
def unitLe : Formula 1 Rat := .le (.var 0) (.lit 2 L)

theorem unitLe_wellTyped : WellTyped ctxL unitLe := .le trivial (.var 0) (.lit 2 L)

/-- **A dropped unit on a literal.** `x ≤ 2` with a dimensionless `2` is not well typed, and it is
not invariant under positive unit changes between positive unit systems: with `x = 1` in the
reference units it holds (`1 ≤ 2`), after the unit change `t = 4` it fails (`4 ≤ 2`). -/
theorem dropUnitLe_not_wellTyped_not_posUnitInvariant :
    ¬ WellTyped ctxL dropUnitLe ∧ ¬ PosUnitInvariant ctxL dropUnitLe := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨d, -, h₁, h₂⟩ := wellTypedAt_le_inv h
    have := congrFun ((hasDim_var_inv h₁).symm.trans (hasDim_lit_inv h₂)) 0
    simp [ctxL, L, Dim.one] at this
  · have := (h (fun _ => 4) (fun _ => 1) (fun _ => 1) (fun _ => (by decide : (0 : Rat) < 4))
      (fun _ => (by decide : (0 : Rat) < 1)) (fun _ => (by grind : (0 : Rat) < 4 * 1))).2
    simp only [dropUnitLe, Formula.holdsIn, Expr.evalIn, actEnv, ctxL,
      scaleOf_L ratLaws.toCommRingLaws, scaleOf_dimOne_fin1 ratLaws.toCommRingLaws] at this
    have h' := this (by grind)
    grind

/-! ## Typing is sufficient, not necessary -/

/-- `x + x * x * x ≤ 0` with `x` a length and the literal `0` a length: a length is added to a
cubed length, so the formula is not well typed. -/
def cubeSum : Formula 1 Rat :=
  .le (.add (.var 0) (.mul (.mul (.var 0) (.var 0)) (.var 0))) (.lit 0 L)

theorem cubeSum_not_wellTyped : ¬ WellTyped ctxL cubeSum := by
  intro h
  obtain ⟨d, -, h₁, -⟩ := wellTypedAt_le_inv h
  obtain ⟨ha, hb⟩ := hasDim_add_inv h₁
  have e1 := hasDim_var_inv ha
  obtain ⟨d₁, d₂, hc, hd, e2⟩ := hasDim_mul_inv hb
  obtain ⟨d₃, d₄, he, hf, e3⟩ := hasDim_mul_inv hc
  rw [hasDim_var_inv hd] at e2
  rw [hasDim_var_inv he, hasDim_var_inv hf] at e3
  rw [e3] at e2
  have := congrFun (e1.symm.trans e2) 0
  simp [ctxL, L, Dim.mul] at this

theorem rat_add_cube_nonpos_iff (a : Rat) : a + a * a * a ≤ 0 ↔ a ≤ 0 := by
  constructor
  · intro h
    rcases @Rat.le_total a 0 with ha | ha
    · exact ha
    · by_cases h0 : a = 0
      · rw [h0]; exact Rat.le_refl
      · have hpos : 0 < a := Rat.lt_iff_le_and_ne.2 ⟨ha, fun e => h0 e.symm⟩
        have h3 : 0 < a * a * a := Rat.mul_pos (Rat.mul_pos hpos hpos) hpos
        grind
  · intro ha
    have hsq : 0 ≤ a * a := by
      have hn : 0 ≤ -a := by grind
      have := Rat.mul_nonneg hn hn
      grind
    have h3 : a * a * a ≤ a * a * 0 := Rat.mul_le_mul_of_nonneg_left ha hsq
    grind

theorem cubeSum_unitInvariant : UnitInvariant ctxL cubeSum := by
  intro t ht s ρ
  simp only [cubeSum, Formula.holdsIn, Expr.evalIn, actEnv, ctxL, Rat.mul_zero,
    rat_add_cube_nonpos_iff]
  have hS := scaleOf_pos ratLaws ht L
  have := mul_le_mul_left_iff' ratLaws (a := ρ 0) (b := 0) hS
  rwa [Rat.mul_zero] at this

/-- **Typing is not necessary.** `cubeSum` is not well typed, yet it is invariant under every
positive unit change. -/
theorem cubeSum_not_wellTyped_unitInvariant :
    ¬ WellTyped ctxL cubeSum ∧ UnitInvariant ctxL cubeSum :=
  ⟨cubeSum_not_wellTyped, cubeSum_unitInvariant⟩

/-- **Negative factor.** `cubeSum` is not invariant under the nonzero unit change `t = -1`: with
`x = 1` in the reference units it fails (`2 ≤ 0`); after the change it holds (`-2 ≤ 0`). -/
theorem cubeSum_not_invariantAt_neg_one : ¬ InvariantAt ctxL (fun _ => (-1 : Rat)) cubeSum := by
  intro h
  have := (h (fun _ => 1) (fun _ => 1)).1
  simp only [cubeSum, Formula.holdsIn, Expr.evalIn, actEnv, ctxL,
    scaleOf_L ratLaws.toCommRingLaws] at this
  have h' := this (by grind)
  grind

/-! ## Positivity and order atoms -/

/-- `0 ≤ x` with `x` a length and the literal `0` a length. -/
def nonnegL : Formula 1 Rat := .le (.lit 0 L) (.var 0)

theorem nonnegL_wellTyped : WellTyped ctxL nonnegL := .le trivial (.lit 0 L) (.var 0)

/-- **Counterexample (negative factor, odd exponent).** The well-typed `0 ≤ x` (exponent `1`) changes
truth value under the nonzero unit change `t = -1`. -/
theorem nonnegL_not_invariantAt_neg_one :
    (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) ∧ ¬ InvariantAt ctxL (fun _ => (-1 : Rat)) nonnegL := by
  refine ⟨fun _ => (by decide : (-1 : Rat) ≠ 0), fun h => ?_⟩
  have := (h (fun _ => 1) (fun _ => 1)).2
  simp only [nonnegL, Formula.holdsIn, Expr.evalIn, actEnv, ctxL,
    scaleOf_L ratLaws.toCommRingLaws, Rat.mul_zero] at this
  have h' := this (by decide)
  grind

/-- `0 ≤ x * x` with `x` a length (exponent `2` for the order atom). -/
def nonnegL2 : Formula 1 Rat := .le (.lit 0 (Dim.mul L L)) (.mul (.var 0) (.var 0))

/-- **Positive control (even exponent).** The order atom of `nonnegL2` sits at `L * L`; the unit
change `t = -1` multiplies that dimension by `1 > 0`, so the characterization theorem gives
invariance. -/
theorem nonnegL2_invariantAt_neg_one : InvariantAt ctxL (fun _ => (-1 : Rat)) nonnegL2 := by
  have hT : WellTypedAt (fun d => d = Dim.mul L L) ctxL nonnegL2 :=
    .le rfl (.lit 0 (Dim.mul L L)) (.mul (.var 0) (.var 0))
  refine (invariantAt_all_wellTypedAt_iff ratLaws ratInvZero (fun d => d = Dim.mul L L)
    (t := fun _ => (-1 : Rat)) (fun _ => by decide)).2 ?_ _ _ hT
  intro d hd; subst hd
  rw [scaleOf_mul_L_L ratLaws.toCommRingLaws]; grind

/-- `x = y` with `x` (variable `0`) and `y` (variable `1`) lengths. -/
def eqXY : Formula 1 Rat := .eq (.var 0) (.var 1)

theorem eqXY_wellTypedAt_noOrder : WellTypedAt (fun _ => False) ctxL eqXY := .eq (.var 0) (.var 1)

/-- **Counterexample (zero factor).** The `≤`-free well-typed `x = y` changes truth value under the
unit change `t = 0`: `1 = 2` fails, `0 * 1 = 0 * 2` holds. -/
theorem eqXY_not_invariantAt_zero : ¬ InvariantAt ctxL (fun _ => (0 : Rat)) eqXY := by
  intro h
  have := (h (fun _ => 1) (fun x => if x = 0 then 1 else 2)).1
  simp [eqXY, Formula.holdsIn, Expr.evalIn, actEnv, ctxL,
    scaleOf_L ratLaws.toCommRingLaws] at this

/-! ## Tightness of the hypotheses of homogeneity and invariance -/

/-- `x * (1 / x)` with `x` a length and `1` dimensionless; its dimension is `L * (1 / L)`. -/
def xTimesInvX : Expr 1 Rat := .mul (.var 0) (.div (.lit 1 Dim.one) (.var 0))

theorem xTimesInvX_hasDim : HasDim ctxL xTimesInvX (Dim.mul L (Dim.div Dim.one L)) :=
  .mul (.var 0) (.div (.lit 1 Dim.one) (.var 0))

/-- **Counterexample (zero factor, expressions), canonical form.** The field laws and `0⁻¹ = 0`
hold for `Rat` and `xTimesInvX` has its dimension, but the unit change `t = 0` has a zero factor,
and homogeneity fails: the left side is `0`, the right side is `1`. -/
theorem xTimesInvX_not_homogeneous_zero :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ HasDim ctxL xTimesInvX (Dim.mul L (Dim.div Dim.one L)) ∧
      ¬ (∀ i : Fin 1, (fun _ => (0 : Rat)) i ≠ 0) ∧
      Expr.evalIn (fun i => (fun _ => (0 : Rat)) i * (fun _ => (1 : Rat)) i)
          (actEnv ctxL (fun _ => 0) (fun _ => 1)) xTimesInvX ≠
        scaleOf (fun _ => (0 : Rat)) (Dim.mul L (Dim.div Dim.one L)) *
          Expr.evalIn (fun _ => 1) (fun _ => 1) xTimesInvX := by
  refine ⟨ratLaws.toFieldLaws, ratInvZero, xTimesInvX_hasDim, fun h => h 0 rfl, ?_⟩
  have hd : scaleOf (fun _ => (0 : Rat)) (Dim.mul L (Dim.div Dim.one L)) = 1 := by
    show npow (0 : Rat) 0 * 1 = 1
    exact Rat.mul_one 1
  rw [hd]
  simp only [xTimesInvX, Expr.evalIn, actEnv, ctxL, scaleOf_L ratLaws.toCommRingLaws,
    scaleOf_dimOne_fin1 ratLaws.toCommRingLaws]
  grind

/-- Context for `divLe`: `x` (variable `0`) and `y` (variable `1`) are lengths, `z` (variable `2`)
has dimension `L / L`. -/
def ctxDiv : Ctx 1 := fun x => if x = 2 then Dim.div L L else L

/-- `x / y ≤ z` over `RatJ`. -/
def divLe : Formula 1 RatJ := .le (.div (.var 0) (.var 1)) (.var 2)

theorem divLe_wellTyped : WellTyped ctxDiv divLe :=
  .le (d := Dim.div L L) trivial (.div (.var 0) (.var 1)) (.var 2)

/-- **Counterexample (`0⁻¹ = 0` is needed).** Over `RatJ`, which satisfies every ordered-field law
but has `0⁻¹ = 1`, the well-typed `x / y ≤ z` is not invariant under the positive unit change
`t = 2` from the positive reference system `s = 1`: at `x = 1, y = 0, z = 1` it reads `1 * 1 ≤ 1`
before and `2 * 1 ≤ 1` after. Hence it is neither `PosUnitInvariant` nor `UnitInvariant`. -/
theorem divLe_not_unitInvariant_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ WellTyped ctxDiv divLe ∧
      ¬ PosUnitInvariant ctxDiv divLe ∧ ¬ UnitInvariant ctxDiv divLe := by
  have hP : ¬ PosUnitInvariant ctxDiv divLe := by
    intro h
    have := (h (fun _ => RatJ.ofRat 2) (fun (_ : Fin 1) => (1 : RatJ))
      (fun x => if x = 1 then RatJ.ofRat 0 else RatJ.ofRat 1)
      (fun _ => (by decide : (0 : Rat) < 2)) (fun _ => (by decide : (0 : Rat) < 1))
      (fun _ => (by grind : (0 : Rat) < 2 * 1))).2
    simp (config := { decide := true }) only [divLe, Formula.holdsIn, Expr.evalIn, actEnv, ctxDiv,
      ite_true, ite_false] at this
    simp only [scaleOf_L ratJLaws.toCommRingLaws, scaleOf_div_L_L ratJLaws.toCommRingLaws,
      RatJ.one_def, RatJ.mul_def, RatJ.inv_def, RatJ.le_def] at this
    simp at this
    exact absurd this (by decide)
  exact ⟨ratJLaws, ratJ_not_invZero, divLe_wellTyped, hP,
    fun h => hP (posUnitInvariant_of_unitInvariant h)⟩

/-! ## Plain readings: positive and negative examples -/

theorem nonnegL_hasPlainReading : HasPlainReading ctxL nonnegL :=
  (hasPlainReading_iff_posUnitInvariant _ _).2
    (posUnitInvariant_of_unitInvariant (unitInvariant_of_wellTyped ratLaws ratInvZero nonnegL_wellTyped))

theorem sumMixed_no_plainReading : ¬ HasPlainReading ctxL sumMixed := fun h =>
  sumMixed_not_wellTyped_not_posUnitInvariant.2 ((hasPlainReading_iff_posUnitInvariant _ _).1 h)

/-! ## Degenerate base unit systems -/

/-- `lit 1 L + lit 1 (L * L) ≤ lit 0 L`: one reference length plus one reference area is at most
zero reference lengths (not well typed). -/
def posConstFormula : Formula 1 Rat := .le (.add (.lit 1 L) (.lit 1 (Dim.mul L L))) (.lit 0 L)

/-- **`UnitInvariant` is strictly stronger than `PosUnitInvariant`.** `posConstFormula` is false in
every positive unit system, hence `PosUnitInvariant`; it is not `UnitInvariant`, because from the
base system `s = -1` the positive unit change `t = 2` flips it (`-1 + 1 ≤ 0` holds,
`-2 + 4 ≤ 0` fails). -/
theorem posConstFormula_posUnitInvariant_not_unitInvariant :
    PosUnitInvariant ctxL posConstFormula ∧ ¬ UnitInvariant ctxL posConstFormula := by
  have hfalse : ∀ (s : Fin 1 → Rat), Positive s → ∀ ρ : Env Rat,
      ¬ Formula.holdsIn s ρ posConstFormula := by
    intro s hs ρ
    simp only [posConstFormula, Formula.holdsIn, Expr.evalIn,
      scaleOf_L ratLaws.toCommRingLaws, scaleOf_mul_L_L ratLaws.toCommRingLaws]
    have hpos : 0 < s 0 := hs 0
    have hsq : 0 < s 0 * s 0 := Rat.mul_pos hpos hpos
    grind
  refine ⟨fun t s ρ _ hs hts => ⟨fun h => (hfalse _ hts _ h).elim,
    fun h => (hfalse _ hs _ h).elim⟩, fun h => ?_⟩
  have h2 := (h (fun _ => 2) (fun _ => (by decide : (0 : Rat) < 2)) (fun _ => -1) (fun _ => 0)).2
  simp only [posConstFormula, Formula.holdsIn, Expr.evalIn,
    scaleOf_L ratLaws.toCommRingLaws, scaleOf_mul_L_L ratLaws.toCommRingLaws] at h2
  have := h2 (by grind)
  grind

end Toy.Units
