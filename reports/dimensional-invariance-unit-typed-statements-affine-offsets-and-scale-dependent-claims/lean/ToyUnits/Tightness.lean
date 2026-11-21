import ToyUnits.Examples

/-!
# Further tightness witnesses (canonical form: the other hypotheses hold, the conclusion fails)
-/

namespace Toy.Units

/-- The length variable `x` (variable `0`). -/
def xVar : Expr 1 Rat := .var 0

/-- **Counterexample (dimension hypothesis of homogeneity).** `x` (a length) is claimed at the wrong
dimension `1`: field laws, `0⁻¹ = 0` and a nonzero factor hold, yet under `t = 2` the reading `2` is
not `scaleOf t 1 * 1 = 1`. -/
theorem var_wrongDim_not_homogeneous :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (2 : Rat)) i ≠ 0) ∧
      ¬ HasDim ctxL xVar Dim.one ∧
      Expr.evalIn (fun i => (fun _ => (2 : Rat)) i * (fun _ => (1 : Rat)) i)
          (actEnv ctxL (fun _ => 2) (fun _ => 1)) xVar ≠
        scaleOf (fun (_ : Fin 1) => (2 : Rat)) Dim.one *
          Expr.evalIn (fun _ => 1) (fun _ => 1) xVar := by
  refine ⟨ratLaws.toFieldLaws, ratInvZero, fun _ => (by decide : (2 : Rat) ≠ 0), fun h => ?_, ?_⟩
  · have := congrFun (hasDim_var_inv h) 0; simp [ctxL, L, Dim.one] at this
  · simp only [xVar, Expr.evalIn, actEnv, ctxL, scaleOf_L ratLaws.toCommRingLaws,
      scaleOf_dimOne_fin1 ratLaws.toCommRingLaws]
    grind

/-- `x / y` over `RatJ`, with `x` (variable `0`) and `y` (variable `1`) lengths. -/
def divXY : Expr 1 RatJ := .div (.var 0) (.var 1)

/-- **Counterexample (`0⁻¹ = 0` for homogeneity).** Over `RatJ`, the well-typed `x / y` (lengths)
read at `x = 1, y = 0` is `1`; after `t = 2` it is `2`, not `scaleOf t (L / L) * 1 = 1`. -/
theorem divXY_not_homogeneous_ratJ :
    FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ HasDim ctxL divXY (Dim.div L L) ∧
      (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      Expr.evalIn (fun i => (fun _ => RatJ.ofRat 2) i * (fun (_ : Fin 1) => (1 : RatJ)) i)
          (actEnv ctxL (fun _ => RatJ.ofRat 2)
            (fun x => if x = 1 then RatJ.ofRat 0 else RatJ.ofRat 1)) divXY ≠
        scaleOf (fun _ => RatJ.ofRat 2) (Dim.div L L) *
          Expr.evalIn (fun _ => 1) (fun x => if x = 1 then RatJ.ofRat 0 else RatJ.ofRat 1)
            divXY := by
  refine ⟨ratJLaws.toFieldLaws, ratJ_not_invZero, .div (.var 0) (.var 1),
    fun _ => (by decide : (2 : Rat) ≠ 0), ?_⟩
  simp (config := { decide := true }) only [divXY, Expr.evalIn, actEnv, ctxL, ite_true, ite_false]
  simp only [scaleOf_L ratJLaws.toCommRingLaws, scaleOf_div_L_L ratJLaws.toCommRingLaws,
    RatJ.one_def, RatJ.mul_def, RatJ.inv_def, ne_eq, RatJ.ofRat_inj]
  grind

/-- `x / y = z` over `RatJ` (no order atom). -/
def divEq : Formula 1 RatJ := .eq (.div (.var 0) (.var 1)) (.var 2)

/-- **Counterexample (`0⁻¹ = 0` for the `≤`-free result).** Over `RatJ`, the `≤`-free well-typed
`x / y = z` changes truth value under the nonzero unit change `t = 2` at `x = 1, y = 0, z = 1`. -/
theorem divEq_not_invariant_ratJ :
    FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ WellTypedAt (fun _ => False) ctxDiv divEq ∧
      (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      ¬ InvariantAt ctxDiv (fun _ => RatJ.ofRat 2) divEq := by
  refine ⟨ratJLaws.toFieldLaws, ratJ_not_invZero,
    .eq (d := Dim.div L L) (.div (.var 0) (.var 1)) (.var 2),
    fun _ => (by decide : (2 : Rat) ≠ 0), fun h => ?_⟩
  have := (h (fun (_ : Fin 1) => (1 : RatJ))
    (fun x => if x = 1 then RatJ.ofRat 0 else RatJ.ofRat 1)).2
  simp (config := { decide := true }) only [divEq, Formula.holdsIn, Expr.evalIn, actEnv, ctxDiv,
    ite_true, ite_false] at this
  simp only [scaleOf_L ratJLaws.toCommRingLaws, scaleOf_div_L_L ratJLaws.toCommRingLaws,
    RatJ.one_def, RatJ.mul_def, RatJ.inv_def, RatJ.ofRat_inj] at this
  grind

/-- **Counterexample (dimensionless literals).** `x + lit 1 L` satisfies every other hypothesis of
`oneVarLength_poly_eval_eq_mul` and of `oneVarLength_eval_eq_mul`, yet its reading at `x = 2`
(reference units) is `3`, not `2` times its reading `2` at `x = 1`. -/
theorem addOneLength_not_linear :
    CommRingLaws Rat ∧ FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxL 0 = L ∧
      HasDim ctxL addOneLength L ∧ addOneLength.onlyVar 0 ∧ ¬ addOneLength.dimlessLits ∧
      addOneLength.isPolynomial ∧
      addOneLength.evalIn (fun _ => 1) (upd (fun _ => 0) 0 2) ≠
        addOneLength.evalIn (fun _ => 1) (upd (fun _ => 0) 0 1) * 2 := by
  obtain ⟨ht, ho, hnd, hv⟩ := addOneLength_control
  refine ⟨ratLaws.toCommRingLaws, ratLaws.toFieldLaws, ratInvZero, rfl, ht, ho, hnd,
    ⟨trivial, trivial⟩, ?_⟩
  rw [hv, hv]; grind

/-- **Counterexample (typing).** `x + lit 1 1` (no dimension) mentions only `x` and has
dimensionless literals, yet its reading at `x = 2` is `3`, not `2` times its reading `2` at
`x = 1`. Every other hypothesis of `oneVarLength_poly_eval_eq_mul` and of
`oneVarLength_eval_eq_mul` holds. -/
theorem addOneDimless_not_linear :
    CommRingLaws Rat ∧ FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxL 0 = L ∧
      (∀ d, ¬ HasDim ctxL addOneDimless d) ∧ addOneDimless.onlyVar 0 ∧
      addOneDimless.dimlessLits ∧ addOneDimless.isPolynomial ∧
      addOneDimless.evalIn (fun _ => 1) (upd (fun _ => 0) 0 2) ≠
        addOneDimless.evalIn (fun _ => 1) (upd (fun _ => 0) 0 1) * 2 := by
  obtain ⟨ht, ho, hd, hv⟩ := addOneDimless_control
  refine ⟨ratLaws.toCommRingLaws, ratLaws.toFieldLaws, ratInvZero, rfl, ht, ho, hd,
    ⟨trivial, trivial⟩, ?_⟩
  rw [hv, hv]; grind

/-- `x + y` with `x` (variable `0`) and `y` (variable `1`) lengths. -/
def twoVarSum : Expr 1 Rat := .add (.var 0) (.var 1)

/-- **Counterexample (one variable).** `x + y` is a polynomial of dimension `L` with no literal, but
it mentions `y`; with `y = 1` its reading at `x = 2` is `3`, not `2` times its reading `2` at
`x = 1`. Every other hypothesis of `oneVarLength_poly_eval_eq_mul` and of
`oneVarLength_eval_eq_mul` holds. -/
theorem twoVarSum_not_linear :
    CommRingLaws Rat ∧ FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxL 0 = L ∧
      HasDim ctxL twoVarSum L ∧ ¬ twoVarSum.onlyVar 0 ∧ twoVarSum.dimlessLits ∧
      twoVarSum.isPolynomial ∧
      twoVarSum.evalIn (fun _ => 1) (upd (fun _ => 1) 0 2) ≠
        twoVarSum.evalIn (fun _ => 1) (upd (fun _ => 1) 0 1) * 2 := by
  refine ⟨ratLaws.toCommRingLaws, ratLaws.toFieldLaws, ratInvZero, rfl, .add (.var 0) (.var 1),
    fun h => ?_, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ?_⟩
  · have h1 : (1 : Nat) = 0 := h.2
    exact absurd h1 (by decide)
  · simp (config := { decide := true }) only [twoVarSum, Expr.evalIn, upd, ite_true, ite_false]
    grind

/-- Context in which every variable has dimension `1 / L`. -/
def ctxInvL : Ctx 1 := fun _ => Dim.div Dim.one L

/-- `1 / x` with `x` of dimension `1 / L`; its dimension is `L`. -/
def invVar : Expr 1 Rat := .div (.lit 1 Dim.one) (.var 0)

/-- **Counterexample (`x` must be a length, rational fragment).** With `x` of dimension `1 / L`, the
one-variable expression `1 / x` has dimension `L` and dimensionless literals, yet its reading at
`x = 2` is `1/2`, not `2` times its reading `1` at `x = 1`. It uses division, so it is not a
counterexample for the polynomial fragment. -/
theorem invVar_not_linear :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxInvL 0 ≠ L ∧ HasDim ctxInvL invVar L ∧
      invVar.onlyVar 0 ∧ invVar.dimlessLits ∧ ¬ invVar.isPolynomial ∧
      invVar.evalIn (fun _ => 1) (upd (fun _ => 0) 0 2) ≠
        invVar.evalIn (fun _ => 1) (upd (fun _ => 0) 0 1) * 2 := by
  have hdim : Dim.div Dim.one (Dim.div Dim.one L) = L := by
    funext i; simp [Dim.div, Dim.one, L]
  refine ⟨ratLaws.toFieldLaws, ratInvZero, fun h => ?_,
    hdim ▸ HasDim.div (HasDim.lit 1 Dim.one) (HasDim.var 0),
    ⟨trivial, rfl⟩, ⟨rfl, trivial⟩, fun hp => hp, ?_⟩
  · have := congrFun h 0; simp [ctxInvL, Dim.div, Dim.one, L] at this
  · simp only [invVar, Expr.evalIn, upd_self, scaleOf_dimOne_fin1 ratLaws.toCommRingLaws]
    grind

/-- `lit 1 (1 / L)` over `RatJ`: one inverse reference length (no division, no power). -/
def invLLit : Expr 1 RatJ := .lit (RatJ.ofRat 1) (Dim.div Dim.one L)

/-- **`0⁻¹` also enters through literals of negative dimension in a base system with a zero
factor.** Over `RatJ` (field laws, `0⁻¹ = 1`), the polynomial literal `lit 1 (1 / L)` is not
homogeneous under the nonzero unit change `t = 2` applied to the degenerate base system `s = 0`. -/
theorem invLLit_not_homogeneous_zero_system_ratJ :
    FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ HasDim ctxL invLLit (Dim.div Dim.one L) ∧
      invLLit.isPolynomial ∧ (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      invLLit.evalIn (fun i => (fun _ => RatJ.ofRat 2) i * (fun _ => RatJ.ofRat 0) i)
          (actEnv ctxL (fun _ => RatJ.ofRat 2) (fun _ => RatJ.ofRat 1)) ≠
        scaleOf (fun _ => RatJ.ofRat 2) (Dim.div Dim.one L) *
          invLLit.evalIn (fun _ => RatJ.ofRat 0) (fun _ => RatJ.ofRat 1) := by
  refine ⟨ratJLaws.toFieldLaws, ratJ_not_invZero, .lit _ _, trivial,
    fun _ => (by decide : (2 : Rat) ≠ 0), ?_⟩
  have hscale0 : scaleOf (fun _ => RatJ.ofRat 0) (Dim.div Dim.one L) = RatJ.ofRat 1 := by
    show RatJ.ofRat ((1 * 0 : Rat) |> fun x => if x = 0 then 1 else x⁻¹) * RatJ.ofRat 1 =
      RatJ.ofRat 1
    simp [RatJ.mul_def]
  have hscale2 : scaleOf (fun _ => RatJ.ofRat 2) (Dim.div Dim.one L) = RatJ.ofRat (1 / 2) := by
    show RatJ.ofRat ((1 * 2 : Rat) |> fun x => if x = 0 then 1 else x⁻¹) * RatJ.ofRat 1 =
      RatJ.ofRat (1 / 2)
    simp [RatJ.mul_def]; grind
  have hmul0 : (fun i : Fin 1 => (fun _ => RatJ.ofRat 2) i * (fun _ => RatJ.ofRat 0) i) =
      (fun _ => RatJ.ofRat 0) := by
    funext i; show RatJ.ofRat (2 * 0) = RatJ.ofRat 0; simp
  rw [hmul0]
  simp only [invLLit, Expr.evalIn, hscale0, hscale2, RatJ.mul_def]
  intro heq
  have heq' : (1 : Rat) * 1 = (1 / 2) * (1 * 1) := heq
  grind

end Toy.Units

namespace Toy.Units

/-- `x + 1 / (1 / (x - x))` over `RatJ`: with `0⁻¹ = 1` the subterm `1 / (1 / (x - x))` is a constant
`1` of dimension `L`. -/
def addOneJunk : Expr 1 RatJ :=
  .add (.var 0) (.div (.lit 1 Dim.one) (.div (.lit 1 Dim.one) (.sub (.var 0) (.var 0))))

theorem addOneJunk_oneVarLength : OneVarLength ctxL 0 addOneJunk where
  ctx_x := rfl
  typed := by
    have e : Dim.div Dim.one (Dim.div Dim.one L) = L := by
      funext i; simp [Dim.div, Dim.one, L]
    exact HasDim.add (HasDim.var 0) (e ▸ HasDim.div (HasDim.lit 1 Dim.one)
      (HasDim.div (HasDim.lit 1 Dim.one) (HasDim.sub (HasDim.var 0) (HasDim.var 0))))
  only_x := ⟨rfl, ⟨trivial, ⟨trivial, ⟨rfl, rfl⟩⟩⟩⟩
  dimless := ⟨trivial, ⟨rfl, ⟨rfl, ⟨trivial, trivial⟩⟩⟩⟩

/-- **Counterexample (`0⁻¹ = 0` for non-definability).** Over `RatJ` (every ordered-field law,
`0⁻¹ = 1`), `v ↦ v + 1` is definable on positive readings: `x + 1 / (1 / (x - x))` has
dimension `L` and computes `v + 1` in every unit system. -/
theorem addOne_definableOnPos_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ DefinableOnPos (fun v : RatJ => v + 1) := by
  refine ⟨ratJLaws, ratJ_not_invZero, ctxL, 0, addOneJunk, rfl, addOneJunk_oneVarLength.typed,
    fun s ρ v _ => ?_⟩
  simp only [addOneJunk, Expr.evalIn, upd_self, scaleOf_dimOne_fin1 ratJLaws.toCommRingLaws]
  show v + RatJ.ofRat 1 * RatJ.ofRat 1 * (RatJ.ofRat 1 * RatJ.ofRat 1 * (v + -v)⁻¹)⁻¹ = v + RatJ.ofRat 1
  rw [ratJLaws.add_neg, RatJ.zero_def]
  simp only [RatJ.mul_def, RatJ.inv_def]
  congr 1
  simp
  exact congrArg RatJ.ofRat (inv_one' ratLaws.toFieldLaws)

/-! ## Canonical tightness witnesses: every other hypothesis holds and the conclusion fails -/

/-- **`definableOnPos_iff` needs `0⁻¹ = 0`.** Over `RatJ` the ordered-field laws hold, `0⁻¹ ≠ 0`,
and the equivalence fails for `f = fun v => v + 1`: the left side holds
(`addOne_definableOnPos_ratJ`), the right side does not (`1 + 1 = c * 1` and `2 + 1 = c * 2`). -/
theorem definableOnPos_iff_fails_without_invZero_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧
      ¬ (DefinableOnPos (fun v : RatJ => v + 1) ↔
        ∃ c : RatJ, ∀ v : RatJ, 0 < v → v + 1 = c * v) := by
  refine ⟨ratJLaws, ratJ_not_invZero, fun hiff => ?_⟩
  obtain ⟨c, hc⟩ := hiff.1 addOne_definableOnPos_ratJ.2.2
  have h1 := hc (RatJ.ofRat 1) (by decide : (0 : Rat) < 1)
  have h2 := hc (RatJ.ofRat 2) (by decide : (0 : Rat) < 2)
  change RatJ.ofRat (1 + 1) = RatJ.ofRat (RatJ.toRat c * 1) at h1
  change RatJ.ofRat (2 + 1) = RatJ.ofRat (RatJ.toRat c * 2) at h2
  have h1' : (1 : Rat) + 1 = RatJ.toRat c * 1 := h1
  have h2' : (2 : Rat) + 1 = RatJ.toRat c * 2 := h2
  grind

/-- **`invariantAt_all_wellTypedAt_iff` needs `0⁻¹ = 0`.** Over `RatJ`, with order atoms at every
dimension and `t = 2`: the ordered-field laws hold, `0⁻¹ ≠ 0`, `t` has nonzero factors, and the
equivalence fails (every `scaleOf t d` is positive, yet `divLe` is not invariant under `t`). -/
theorem orderIff_fails_without_invZero_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧
      (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      ¬ ((∀ (Γ : Ctx 1) (φ : Formula 1 RatJ),
            WellTypedAt (fun _ => True) Γ φ → InvariantAt Γ (fun _ => RatJ.ofRat 2) φ) ↔
          (∀ d : Dim 1, (fun _ => True) d → 0 < scaleOf (fun _ => RatJ.ofRat 2) d)) := by
  refine ⟨ratJLaws, ratJ_not_invZero, fun _ => (by decide : (2 : Rat) ≠ 0), fun hiff => ?_⟩
  have hrhs : ∀ d : Dim 1, (fun _ => True) d → 0 < scaleOf (fun _ => RatJ.ofRat 2) d :=
    fun d _ => scaleOf_pos ratJLaws (fun _ => (by decide : (0 : Rat) < 2)) d
  have hinv := hiff.2 hrhs ctxDiv divLe divLe_wellTyped
  have h := (hinv (fun _ => (1 : RatJ))
    (fun x => if x = 1 then RatJ.ofRat 0 else RatJ.ofRat 1)).2
  simp (config := { decide := true }) only [divLe, Formula.holdsIn, Expr.evalIn, actEnv, ctxDiv,
    ite_true, ite_false] at h
  simp only [scaleOf_L ratJLaws.toCommRingLaws, scaleOf_div_L_L ratJLaws.toCommRingLaws,
    RatJ.one_def, RatJ.mul_def, RatJ.inv_def, RatJ.le_def] at h
  simp at h
  exact absurd h (by decide)

/-- **`invariantAt_all_wellTypedAt_iff` needs nonzero factors.** Over `Rat`, with no order atom and
`t = 0`: the ordered-field laws and `0⁻¹ = 0` hold, `t` has a zero factor, and the equivalence
fails (the right side holds vacuously, yet `x = y` is not invariant under `t = 0`). -/
theorem orderIff_fails_at_zero_factor :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧
      ¬ (∀ i : Fin 1, (fun _ => (0 : Rat)) i ≠ 0) ∧
      ¬ ((∀ (Γ : Ctx 1) (φ : Formula 1 Rat),
            WellTypedAt (fun _ => False) Γ φ → InvariantAt Γ (fun _ => (0 : Rat)) φ) ↔
          (∀ d : Dim 1, (fun _ => False) d → 0 < scaleOf (fun _ => (0 : Rat)) d)) := by
  refine ⟨ratLaws, ratInvZero, fun h => h 0 rfl, fun hiff => ?_⟩
  have hinv := hiff.2 (fun _ hf => hf.elim) ctxL eqXY eqXY_wellTypedAt_noOrder
  exact eqXY_not_invariantAt_zero hinv

/-- **`invariantAt_of_wellTypedAt` needs `0⁻¹ = 0`.** Over `RatJ` with `t = 2` and order atoms at
every dimension: field laws, nonzero factors, the order condition and typing hold, `0⁻¹ ≠ 0`, and
`divLe` is not invariant under `t`. -/
theorem divLe_engine_tight_ratJ :
    FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧
      (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      (∀ d : Dim 1, (fun _ => True) d → ∀ a b : RatJ,
        scaleOf (fun _ => RatJ.ofRat 2) d * a ≤ scaleOf (fun _ => RatJ.ofRat 2) d * b ↔ a ≤ b) ∧
      WellTypedAt (fun _ => True) ctxDiv divLe ∧
      ¬ InvariantAt ctxDiv (fun _ => RatJ.ofRat 2) divLe := by
  refine ⟨ratJLaws.toFieldLaws, ratJ_not_invZero, fun _ => (by decide : (2 : Rat) ≠ 0),
    fun d _ _ _ => mul_le_mul_left_iff' ratJLaws
      (scaleOf_pos ratJLaws (fun _ => (by decide : (0 : Rat) < 2)) d),
    divLe_wellTyped, fun hinv => ?_⟩
  have h := (hinv (fun _ => (1 : RatJ))
    (fun x => if x = 1 then RatJ.ofRat 0 else RatJ.ofRat 1)).2
  simp (config := { decide := true }) only [divLe, Formula.holdsIn, Expr.evalIn, actEnv, ctxDiv,
    ite_true, ite_false] at h
  simp only [scaleOf_L ratJLaws.toCommRingLaws, scaleOf_div_L_L ratJLaws.toCommRingLaws,
    RatJ.one_def, RatJ.mul_def, RatJ.inv_def, RatJ.le_def] at h
  simp at h
  exact absurd h (by decide)

/-- **Nonzero factors are needed (`invariantAt_of_wellTypedAt` and
`invariantAt_of_wellTypedAt_noOrder_of_ne_zero`).** Over `Rat` with `t = 0` and no order atom:
field laws, `0⁻¹ = 0`, the (vacuous) order condition and typing hold, `t` has a zero factor, and
`x = y` is not invariant under `t`. -/
theorem eqXY_engine_tight_zero :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ ¬ (∀ i : Fin 1, (fun _ => (0 : Rat)) i ≠ 0) ∧
      (∀ d : Dim 1, (fun _ => False) d → ∀ a b : Rat,
        scaleOf (fun _ => (0 : Rat)) d * a ≤ scaleOf (fun _ => (0 : Rat)) d * b ↔ a ≤ b) ∧
      WellTypedAt (fun _ => False) ctxL eqXY ∧ ¬ InvariantAt ctxL (fun _ => (0 : Rat)) eqXY :=
  ⟨ratLaws.toFieldLaws, ratInvZero, fun h => h 0 rfl, fun _ hd => hd.elim,
    eqXY_wellTypedAt_noOrder, eqXY_not_invariantAt_zero⟩

/-- **The order condition of `invariantAt_of_wellTypedAt` is needed.** Over `Rat` with `t = -1`
and order atoms at every dimension: field laws, `0⁻¹ = 0`, nonzero factors and typing hold,
multiplication by `scaleOf t L = -1` does not preserve `≤`, and `0 ≤ x` is not invariant. -/
theorem nonnegL_engine_tight_neg_one :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) ∧
      ¬ (∀ d : Dim 1, (fun _ => True) d → ∀ a b : Rat,
        scaleOf (fun _ => (-1 : Rat)) d * a ≤ scaleOf (fun _ => (-1 : Rat)) d * b ↔ a ≤ b) ∧
      WellTypedAt (fun _ => True) ctxL nonnegL ∧
      ¬ InvariantAt ctxL (fun _ => (-1 : Rat)) nonnegL := by
  refine ⟨ratLaws.toFieldLaws, ratInvZero, nonnegL_not_invariantAt_neg_one.1, fun hO => ?_,
    nonnegL_wellTyped, nonnegL_not_invariantAt_neg_one.2⟩
  have h := (hO L trivial 0 1).2 (by decide)
  rw [scaleOf_L ratLaws.toCommRingLaws] at h
  grind

/-- **Typing is needed (`invariantAt_of_wellTypedAt`).** Over `Rat` with `t = 2` and order atoms at
every dimension: field laws, `0⁻¹ = 0`, nonzero factors and the order condition hold, `sumMixed` is
not well typed, and it is not invariant under `t`. -/
theorem sumMixed_engine_tight :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (2 : Rat)) i ≠ 0) ∧
      (∀ d : Dim 1, (fun _ => True) d → ∀ a b : Rat,
        scaleOf (fun _ => (2 : Rat)) d * a ≤ scaleOf (fun _ => (2 : Rat)) d * b ↔ a ≤ b) ∧
      ¬ WellTypedAt (fun _ => True) ctxL sumMixed ∧
      ¬ InvariantAt ctxL (fun _ => (2 : Rat)) sumMixed :=
  ⟨ratLaws.toFieldLaws, ratInvZero, fun _ => (by decide : (2 : Rat) ≠ 0),
    fun d _ _ _ => mul_le_mul_left_iff' ratLaws
      (scaleOf_pos ratLaws (fun _ => (by decide : (0 : Rat) < 2)) d),
    sumMixed_not_wellTyped, fun hinv => sumMixed_flips.2 ((hinv _ _).2 sumMixed_flips.1)⟩

/-- **The no-order-atom typing of `invariantAt_of_wellTypedAt_noOrder_of_ne_zero` is needed.** Over
`Rat` with `t = -1`: field laws, `0⁻¹ = 0` and nonzero factors hold, `0 ≤ x` is not well typed
without order atoms, and it is not invariant under `t`. -/
theorem nonnegL_noOrder_tight_neg_one :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) ∧
      ¬ WellTypedAt (fun _ => False) ctxL nonnegL ∧
      ¬ InvariantAt ctxL (fun _ => (-1 : Rat)) nonnegL := by
  refine ⟨ratLaws.toFieldLaws, ratInvZero, nonnegL_not_invariantAt_neg_one.1, fun h => ?_,
    nonnegL_not_invariantAt_neg_one.2⟩
  obtain ⟨d, hd, -, -⟩ := wellTypedAt_le_inv h
  exact hd

end Toy.Units
