/-
Toy.FloatTier.Counterexamples
=============================

Counterexamples (in canonical form: all other hypotheses hold and the
conclusion fails), positive controls and non-vacuity witnesses for the main
results, all fully proved.
-/
import Toy.FloatTier.Determinism
import Toy.FloatTier.Instances

namespace Toy.FloatTier

variable {f : Fmt}

/-! ### Evaluation helpers -/

theorem vzero_toFP (s : Bool) : (V.zero f s).toFP = zero f s := rfl

theorem vinf_toFP (s : Bool) : (V.inf s : V f).toFP = .inf s := rfl

theorem vzero_isNaN (s : Bool) : (V.zero f s).isNaN = false := rfl

theorem lt_zero_zero (s t : Bool) : lt (zero f s) (zero f t) = false := by
  simp [lt, zero, key, FP.isNaN, unitsOf_zero_zero, sval_zero]

theorem key_one (f : Fmt) : key (V.one f).toFP = ((2 ^ f.qneg : Nat) : Int) := by
  simp [V.one, V.toFP, key, sval, unitsOf_bias_zero]

theorem evalS_mulZeroInf (X : Extra f) (ρ : Nat → V f) (r : V f) :
    (FExpr.prim .mul (.lit (V.zero f false)) (.lit (.inf false))).evalS X ρ r ↔
      NaNChoice X (V.zero f false) (.inf false) r := by
  have hc : mul (V.zero f false).toFP (V.inf false : V f).toFP = .nan := by
    rw [vzero_toFP, vinf_toFP, mul_zero_inf]
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    simp only [FExpr.evalS] at hx hy
    subst hx hy
    simp only [primSet, arithSet, hc, FP.isNaN, ↓reduceIte] at h
    exact h
  · intro h
    refine ⟨_, _, rfl, rfl, ?_⟩
    simp only [primSet, arithSet, hc, FP.isNaN, ↓reduceIte]
    exact h

theorem evalS_minZero (X : Extra f) (ρ : Nat → V f) (r : V f) :
    (FExpr.prim .min (.lit (V.zero f false)) (.lit (V.zero f true))).evalS X ρ r ↔
      (r = V.zero f false ∨ r = V.zero f true) := by
  have hm : minSet X (V.zero f false) (V.zero f true) r ↔ (r = V.zero f false ∨ r = V.zero f true) := by
    simp only [minSet, vzero_isNaN, vzero_toFP, lt_zero_zero, Bool.and_self, Bool.false_eq_true,
      ↓reduceIte]
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    simp only [FExpr.evalS] at hx hy
    subst hx hy
    exact hm.1 h
  · intro h
    exact ⟨_, _, rfl, rfl, hm.2 h⟩

theorem nanChoice_isNaN_true {X : Extra f} {x y r : V f} (h : NaNChoice X x y r) :
    r.isNaN = true := h.1

theorem isZero_of_isNaN {r : V f} (h : r.isNaN = true) : r.isZero = false := by
  simp [V.isZero, V.toFP_eq_nan_of_isNaN h, FP.isZero]

theorem mul_zero_inf_V : mul (V.zero f false).toFP (V.inf false : V f).toFP = .nan := by
  rw [vzero_toFP, vinf_toFP, mul_zero_inf]

theorem tierCtfe_mul_zero_inf :
    tierCtfe .mul (V.zero f false) (.inf false) = V.prefNaN f false := by
  show ctfePolicy.arith (mul (V.zero f false).toFP (V.inf false : V f).toFP) (V.zero f false)
    (.inf false) = _
  rw [mul_zero_inf_V]
  rfl

theorem tierRunA_mul_zero_inf :
    tierRunA .mul (V.zero f false) (.inf false) = V.prefNaN f true := by
  show runPolicyA.arith (mul (V.zero f false).toFP (V.inf false : V f).toFP) (V.zero f false)
    (.inf false) = _
  rw [mul_zero_inf_V]
  rfl

theorem tierCtfe_min_zero : tierCtfe .min (V.zero f false) (V.zero f true) = V.zero f false := by
  simp only [tierCtfe, tierOf, vzero_isNaN, vzero_toFP, lt_zero_zero, ctfePolicy, Bool.and_self,
    Bool.false_eq_true, ↓reduceIte]

theorem tierRunA_min_zero : tierRunA .min (V.zero f false) (V.zero f true) = V.zero f true := by
  simp only [tierRunA, tierOf, vzero_isNaN, vzero_toFP, lt_zero_zero, runPolicyA, Bool.and_self,
    Bool.false_eq_true, ↓reduceIte]

theorem lt_zero_one : lt (zero f false) (V.one f).toFP = true := by
  have h1 : key (zero f false) = 0 := by simp [zero, key, unitsOf_zero_zero, sval]
  have h2 := key_one f
  have hq := Nat.two_pow_pos f.qneg
  have hn1 : (zero f false).isNaN = false := rfl
  have hn2 : (V.one f).toFP.isNaN = false := rfl
  unfold lt
  rw [hn1, hn2, h1, h2]
  simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq]
  omega

theorem lt_zero_negOne :
    lt (zero f false) (V.fin true ⟨f.bias, f.bias_lt_expCount⟩ ⟨0, f.fracCount_pos⟩).toFP = false := by
  have h1 : key (zero f false) = 0 := by simp [zero, key, unitsOf_zero_zero, sval]
  have h2 : key (V.fin true ⟨f.bias, f.bias_lt_expCount⟩ ⟨0, f.fracCount_pos⟩ : V f).toFP =
      -((2 ^ f.qneg : Nat) : Int) := by
    simp [V.toFP, key, sval, unitsOf_bias_zero]
  have hq := Nat.two_pow_pos f.qneg
  have hn1 : (zero f false).isNaN = false := rfl
  have hn2 : (V.fin true ⟨f.bias, f.bias_lt_expCount⟩ ⟨0, f.fracCount_pos⟩ : V f).toFP.isNaN =
      false := rfl
  unfold lt
  rw [hn1, hn2, h1, h2]
  simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not]
  omega

/-! ### Refinement tiers: positive controls and non-vacuity -/

/-- Non-vacuity for `refinesS_iff_tierSound`: a sound tier (both sides hold) and
an unsound tier (both sides fail). -/
theorem refinesS_iff_tierSound_nonvacuous :
    (RefinesS (noExtra (f := F23)) tierCtfe ∧ TierSound (noExtra (f := F23)) tierCtfe) ∧
    (¬ RefinesS (noExtra (f := F23)) tierBad ∧ ¬ TierSound (noExtra (f := F23)) tierBad) := by
  have hbad : ¬ TierSound (noExtra (f := F23)) tierBad := by
    intro h
    have := h .add (V.zero F23 false) (V.zero F23 false)
    revert this; decide
  exact ⟨⟨tierOf_refinesS _ _, tierOf_sound _ _⟩,
    ⟨fun h => hbad ((refinesS_iff_tierSound _ _).1 h), hbad⟩⟩

/-- Positive control for `sound_tiers_disagree_on_bits`: under the value-level
observation `isNaN (0.0 * +∞)`, the two tiers agree. -/
theorem tiers_agree_on_isNaN_zero_mul_inf (ρ : Nat → V f) :
    (progIsNaNZeroMulInf f).runT tierCtfe ρ = 1 ∧ (progIsNaNZeroMulInf f).runT tierRunA ρ = 1 := by
  simp [progIsNaNZeroMulInf, Prog.runT, FExpr.evalT, tierCtfe_mul_zero_inf,
    tierRunA_mul_zero_inf, V.prefNaN, V.isNaN]

/-- Non-vacuity for `Prog.runS_of_runS_fold`, and strictness of the inclusion:
`tierCtfe` is sound, the fold of `toBits (0.0 * +∞)` is a different program, it
has an `S`-observation, and `S` allows the original program an observation
(the bits of the negative preferred quiet NaN) that it does not allow the
folded program. -/
theorem runS_of_runS_fold_nonvacuous (ρ : Nat → V f) :
    TierSound (noExtra (f := f)) tierCtfe ∧
    (progBitsZeroMulInf f).fold tierCtfe = .toBits (.lit (V.prefNaN f false)) ∧
    ((progBitsZeroMulInf f).fold tierCtfe).runS noExtra ρ (V.prefNaN f false).bits ∧
    (progBitsZeroMulInf f).runS noExtra ρ (V.prefNaN f true).bits ∧
    ¬ ((progBitsZeroMulInf f).fold tierCtfe).runS noExtra ρ (V.prefNaN f true).bits := by
  have hfold : (progBitsZeroMulInf f).fold tierCtfe = .toBits (.lit (V.prefNaN f false)) := by
    simp [progBitsZeroMulInf, Prog.fold, FExpr.fold, FExpr.closed, FExpr.evalT,
      tierCtfe_mul_zero_inf]
  refine ⟨tierOf_sound _ _, hfold, ?_, ?_, ?_⟩
  · rw [hfold]; exact ⟨_, rfl, rfl⟩
  · exact ⟨V.prefNaN f true, (evalS_mulZeroInf noExtra ρ _).2 ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩
  · rw [hfold]
    rintro ⟨x, hx, h⟩
    simp only [FExpr.evalS] at hx
    subst hx
    exact prefNaN_bits_ne h.symm

/-- Positive control for `fold_tierCtfe_changes_tierRunA_bits`: folding the
NaN-free program `toBits (copysign (var 0) (+∞ * -∞))` with `tierCtfe` keeps the
variable, folds `+∞ * -∞` to `-∞`, and does not change the observation computed
by `tierRunA`, for every input. -/
theorem fold_tierCtfe_preserves_tierRunA_nan_free (ρ : Nat → V f) :
    (progBitsCopysignVarInfMulNegInf f).fold tierCtfe =
        .toBits (.copysign (.var 0) (.lit (.inf true))) ∧
      ((progBitsCopysignVarInfMulNegInf f).fold tierCtfe).runT tierRunA ρ =
        (progBitsCopysignVarInfMulNegInf f).runT tierRunA ρ := by
  constructor
  · simp [progBitsCopysignVarInfMulNegInf, Prog.fold, FExpr.fold, FExpr.closed, FExpr.evalT,
      tierCtfe, tierOf, ChoicePolicy.arith, V.toFP, mul, FP.isNaN, V.ofFP]
  · simp [progBitsCopysignVarInfMulNegInf, Prog.fold, FExpr.fold, FExpr.closed, Prog.runT,
      FExpr.evalT, tierCtfe, tierRunA, tierOf, ChoicePolicy.arith, V.toFP, mul, FP.isNaN, V.ofFP]

/-- **`S` allows observations that no tier produces.** In every format, for
every extra-payload set and input: `S` allows the observation `0` for
`copysign(1.0, 0.0 * +∞) == copysign(1.0, 0.0 * +∞)` (the two `*` nodes choose
NaNs of opposite sign), whereas every tier `τ` (sound or not) computes `1`,
because a tier makes the same choice at every occurrence of the same
operation on the same operands. -/
theorem exists_runS_not_realized_by_any_tier (X : Extra f) (ρ : Nat → V f) :
    (progSelfEqCopysignNaN f).runS X ρ 0 ∧
    ∀ τ : Tier f, (progSelfEqCopysignNaN f).runT τ ρ = 1 := by
  constructor
  · refine ⟨(V.one f).copysign (V.prefNaN f false), (V.one f).copysign (V.prefNaN f true),
      ⟨V.one f, V.prefNaN f false, rfl,
        (evalS_mulZeroInf X ρ _).2 ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩,
      ⟨V.one f, V.prefNaN f true, rfl,
        (evalS_mulZeroInf X ρ _).2 ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩, ?_⟩
    have h1 : key ((V.one f).copysign (V.prefNaN f false)).toFP = ((2 ^ f.qneg : Nat) : Int) :=
      key_one f
    have h2 : key ((V.one f).copysign (V.prefNaN f true)).toFP = -((2 ^ f.qneg : Nat) : Int) := by
      simp [V.one, V.copysign, V.withSign, V.prefNaN, V.signBit, V.toFP, key, sval,
        unitsOf_bias_zero]
    have hq := Nat.two_pow_pos f.qneg
    have hn1 : ((V.one f).copysign (V.prefNaN f false)).toFP.isNaN = false := rfl
    have hn2 : ((V.one f).copysign (V.prefNaN f true)).toFP.isNaN = false := rfl
    have hfeq : feq ((V.one f).copysign (V.prefNaN f false)).toFP
        ((V.one f).copysign (V.prefNaN f true)).toFP = false := by
      unfold feq
      rw [hn1, hn2, h1, h2]
      simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not]
      omega
    rw [hfeq]
    rfl
  · intro τ
    simp only [progSelfEqCopysignNaN, Prog.runT, FExpr.evalT]
    have hnn : ((V.one f).copysign (τ .mul (V.zero f false) (.inf false))).toFP.isNaN = false := by
      simp [V.one, V.copysign, V.withSign, V.toFP, FP.isNaN]
    have hfeq : feq ((V.one f).copysign (τ .mul (V.zero f false) (.inf false))).toFP
        ((V.one f).copysign (τ .mul (V.zero f false) (.inf false))).toFP = true := by
      unfold feq
      rw [hnn]
      simp
    rw [hfeq]
    rfl

/-! ### Value-level determinism: counterexamples and witnesses -/

theorem progCopysignNaN_runT_tierCtfe (ρ : Nat → V f) : (progCopysignNaN f).runT tierCtfe ρ = 1 := by
  show (lt (V.zero f false).toFP
    ((V.one f).copysign (tierCtfe .mul (V.zero f false) (.inf false))).toFP).toNat = 1
  rw [tierCtfe_mul_zero_inf, vzero_toFP]
  rw [show (V.one f).copysign (V.prefNaN f false) = V.one f from rfl, lt_zero_one]
  rfl

theorem progCopysignNaN_runT_tierRunA (ρ : Nat → V f) : (progCopysignNaN f).runT tierRunA ρ = 0 := by
  show (lt (V.zero f false).toFP
    ((V.one f).copysign (tierRunA .mul (V.zero f false) (.inf false))).toFP).toNat = 0
  rw [tierRunA_mul_zero_inf, vzero_toFP]
  rw [show (V.one f).copysign (V.prefNaN f true) =
    V.fin true ⟨f.bias, f.bias_lt_expCount⟩ ⟨0, f.fracCount_pos⟩ from rfl, lt_zero_negOne]
  rfl

/-- **Copysign on a NaN breaks determinism.** In every format, for every
extra-payload set and input: the program `0.0 < copysign(1.0, 0.0 * +∞)` has no
`min`/`max`, and every bit-level use in it receives a value that is not a zero;
yet the sound tiers `tierCtfe` and `tierRunA` compute `1` and `0`, so `S` allows
two different observations. (The NaN part of `isNaNOrZero`, and the hypothesis
of `Prog.runS_unique_of_minMaxFree_of_bitSafe_nan`, cannot be dropped.) -/
theorem copysignNaN_breaks_determinism (X : Extra f) (ρ : Nat → V f) :
    (progCopysignNaN f).BitSafe X ρ V.isZero ∧ (progCopysignNaN f).MinMaxFree = true ∧
    (progCopysignNaN f).runT tierCtfe ρ = 1 ∧ (progCopysignNaN f).runT tierRunA ρ = 0 ∧
    ¬ (∀ n₁ n₂, (progCopysignNaN f).runS X ρ n₁ → (progCopysignNaN f).runS X ρ n₂ → n₁ = n₂) := by
  refine ⟨?_, rfl, progCopysignNaN_runT_tierCtfe ρ, progCopysignNaN_runT_tierRunA ρ, ?_⟩
  · refine ⟨trivial, trivial, ⟨trivial, trivial⟩, ?_⟩
    intro y hy
    exact isZero_of_isNaN ((evalS_mulZeroInf X ρ y).1 hy).1
  · intro h
    have h1 := Prog.runS_runT_of_tierSound (tierOf_sound X ctfePolicy) (progCopysignNaN f) ρ
    have h2 := Prog.runS_runT_of_tierSound (tierOf_sound X runPolicyA) (progCopysignNaN f) ρ
    have := h _ _ h1 h2
    rw [show tierOf ctfePolicy = tierCtfe from rfl, show tierOf runPolicyA = tierRunA from rfl,
      progCopysignNaN_runT_tierCtfe, progCopysignNaN_runT_tierRunA] at this
    exact absurd this (by decide)

theorem progMinZeroSign_runT_tierCtfe (ρ : Nat → V f) : (progMinZeroSign f).runT tierCtfe ρ = 0 := by
  show (tierCtfe .min (V.zero f false) (V.zero f true)).signBit.toNat = 0
  rw [tierCtfe_min_zero]; rfl

theorem progMinZeroSign_runT_tierRunA (ρ : Nat → V f) : (progMinZeroSign f).runT tierRunA ρ = 1 := by
  show (tierRunA .min (V.zero f false) (V.zero f true)).signBit.toNat = 1
  rw [tierRunA_min_zero]; rfl

/-- **A sign test on `min(+0, -0)` breaks determinism.** In every format, for
every extra-payload set and input: in `signBit (min(+0.0, -0.0))` every
bit-level use receives a value that is not a NaN; yet the sound tiers
`tierCtfe` and `tierRunA` compute `0` and `1`, so `S` allows two different
observations. (The zero part of `isNaNOrZero`, and the `min`/`max`-freedom
hypothesis of `Prog.runS_unique_of_minMaxFree_of_bitSafe_nan`, cannot be
dropped.) -/
theorem minZeroSign_breaks_determinism (X : Extra f) (ρ : Nat → V f) :
    (progMinZeroSign f).BitSafe X ρ V.isNaN ∧ (progMinZeroSign f).MinMaxFree = false ∧
    (progMinZeroSign f).runT tierCtfe ρ = 0 ∧ (progMinZeroSign f).runT tierRunA ρ = 1 ∧
    ¬ (∀ n₁ n₂, (progMinZeroSign f).runS X ρ n₁ → (progMinZeroSign f).runS X ρ n₂ → n₁ = n₂) := by
  refine ⟨?_, rfl, progMinZeroSign_runT_tierCtfe ρ, progMinZeroSign_runT_tierRunA ρ, ?_⟩
  · refine ⟨⟨trivial, trivial⟩, ?_⟩
    intro y hy
    rcases (evalS_minZero X ρ y).1 hy with rfl | rfl <;> rfl
  · intro h
    have h1 := Prog.runS_runT_of_tierSound (tierOf_sound X ctfePolicy) (progMinZeroSign f) ρ
    have h2 := Prog.runS_runT_of_tierSound (tierOf_sound X runPolicyA) (progMinZeroSign f) ρ
    have := h _ _ h1 h2
    rw [show tierOf ctfePolicy = tierCtfe from rfl, show tierOf runPolicyA = tierRunA from rfl,
      progMinZeroSign_runT_tierCtfe, progMinZeroSign_runT_tierRunA] at this
    exact absurd this (by decide)

/-- **`min(+0, -0)` is deterministic up to `==`, not under a sign test.** In every
format, for every extra-payload set and input: `S` allows exactly the
observation `1` for `min(+0.0, -0.0) == +0.0`, and exactly the observations `0`
and `1` for `signBit (min(+0.0, -0.0))`. -/
theorem minZero_eq_and_signBit_runS (X : Extra f) (ρ : Nat → V f) (n : Nat) :
    ((progMinZeroEq f).runS X ρ n ↔ n = 1) ∧ ((progMinZeroSign f).runS X ρ n ↔ n = 0 ∨ n = 1) := by
  have hfeq : ∀ s t : Bool, feq (zero f s) (zero f t) = true := by
    intro s t; simp [feq, zero, key, FP.isNaN, unitsOf_zero_zero, sval_zero]
  constructor
  · simp only [progMinZeroEq, Prog.runS]
    constructor
    · rintro ⟨x, y, hx, hy, rfl⟩
      simp only [FExpr.evalS] at hy
      subst hy
      rcases (evalS_minZero X ρ x).1 hx with rfl | rfl <;> simp [vzero_toFP, hfeq]
    · rintro rfl
      exact ⟨V.zero f false, V.zero f false, (evalS_minZero X ρ _).2 (Or.inl rfl), rfl,
        by simp [vzero_toFP, hfeq]⟩
  · simp only [progMinZeroSign, Prog.runS]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases (evalS_minZero X ρ x).1 hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨V.zero f false, (evalS_minZero X ρ _).2 (Or.inl rfl), rfl⟩
      · exact ⟨V.zero f true, (evalS_minZero X ρ _).2 (Or.inr rfl), rfl⟩

theorem evalS_progNaNBranch_arg (X : Extra f) (ρ : Nat → V f) (y : V f) :
    (FExpr.selLt (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))) (.lit (V.zero f false))
      (.lit (V.one f)) (.prim .mul (.lit (.inf false)) (.lit (.inf true)))).evalS X ρ y ↔
      y = .inf true := by
  constructor
  · rintro ⟨x, z, hx, hz, h⟩
    rw [evalS_mulZeroInf] at hx
    simp only [FExpr.evalS] at hz
    subst hz
    rw [V.toFP_eq_nan_of_isNaN hx.1] at h
    simp only [lt, FP.isNaN, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨a, b, ha, hb, hab⟩ := h
    simp only [FExpr.evalS] at ha hb
    subst ha hb
    simpa [primSet, arithSet, V.toFP, mul, FP.isNaN, V.ofFP] using hab
  · rintro rfl
    refine ⟨V.prefNaN f false, V.zero f false,
      (evalS_mulZeroInf X ρ _).2 ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, rfl, ?_⟩
    rw [show (V.prefNaN f false).toFP = .nan from rfl]
    simp only [lt, FP.isNaN, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, _, rfl, rfl, by simp [primSet, arithSet, V.toFP, mul, FP.isNaN, V.ofFP]⟩

/-- **Non-vacuity of the determinism theorems.** In every format, for every
extra-payload set and input: `signBit (if 0.0 * +∞ < 0.0 then 1.0 else +∞ * -∞)`
produces a NaN, has no `min`/`max`, every bit-level use in it receives a value
that is neither a NaN nor a zero, and `S` allows exactly the observation `1`. -/
theorem progNaNBranchSign_nonvacuous (X : Extra f) (ρ : Nat → V f) :
    (progNaNBranchSign f).MinMaxFree = true ∧
    (progNaNBranchSign f).BitSafe X ρ V.isNaNOrZero ∧
    (progNaNBranchSign f).BitSafe X ρ V.isNaN ∧
    (∀ n, (progNaNBranchSign f).runS X ρ n ↔ n = 1) := by
  have harg := evalS_progNaNBranch_arg X ρ
  refine ⟨rfl, ⟨⟨⟨trivial, trivial⟩, trivial, fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩, ?_⟩,
    ⟨⟨⟨trivial, trivial⟩, trivial, fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩, ?_⟩, ?_⟩
  · intro y hy; rw [(harg y).1 hy]; rfl
  · intro y hy; rw [(harg y).1 hy]; rfl
  · intro n
    simp only [progNaNBranchSign, Prog.runS]
    constructor
    · rintro ⟨y, hy, rfl⟩; rw [(harg y).1 hy]; rfl
    · rintro rfl; exact ⟨_, (harg _).2 rfl, rfl⟩

/-- Non-vacuity of `Prog.runS_unique_of_bitSafe_nanOrZero` with internal
nondeterminism of `min` on zeros: `min(+0.0, -0.0) == +0.0` satisfies the
hypothesis (it has no bit-level use), its `min` node can return either zero,
and `S` allows exactly the observation `1`. -/
theorem progMinZeroEq_nonvacuous (X : Extra f) (ρ : Nat → V f) :
    (progMinZeroEq f).BitSafe X ρ V.isNaNOrZero ∧
    (FExpr.prim .min (.lit (V.zero f false)) (.lit (V.zero f true))).evalS X ρ (V.zero f false) ∧
    (FExpr.prim .min (.lit (V.zero f false)) (.lit (V.zero f true))).evalS X ρ (V.zero f true) ∧
    (∀ n, (progMinZeroEq f).runS X ρ n ↔ n = 1) :=
  ⟨⟨⟨trivial, trivial⟩, trivial⟩, (evalS_minZero X ρ _).2 (Or.inl rfl),
    (evalS_minZero X ρ _).2 (Or.inr rfl), fun n => (minZero_eq_and_signBit_runS X ρ n).1⟩

/-! ### Soundness hypotheses on tiers -/

theorem not_tierSound_tierBad (X : Extra f) : ¬ TierSound X tierBad := by
  intro h
  have h1 := h .mul (V.zero f false) (.inf false)
  simp only [primSet, arithSet, mul_zero_inf_V, FP.isNaN, ↓reduceIte] at h1
  exact absurd h1.1 (by simp [tierBad, V.isNaN])

/-- **Folding with an unsound tier need not refine `S`.** In every format, for
every extra-payload set and input: `tierBad` is not sound, and folding
`isNaN (0.0 * +∞)` with it yields a program with observation `0`, which `S` does
not allow for the original program. (The soundness hypothesis of
`Prog.runS_of_runS_fold` cannot be dropped.) -/
theorem fold_unsound_tier_not_refinement (X : Extra f) (ρ : Nat → V f) :
    ¬ TierSound X tierBad ∧ ((progIsNaNZeroMulInf f).fold tierBad).runS X ρ 0 ∧
      ¬ (progIsNaNZeroMulInf f).runS X ρ 0 := by
  refine ⟨not_tierSound_tierBad X, ?_, ?_⟩
  · exact ⟨.inf false, rfl, rfl⟩
  · rintro ⟨x, hx, h0⟩
    have hn := ((evalS_mulZeroInf X ρ x).1 hx).1
    rw [hn] at h0
    exact absurd h0 (by decide)

/-- **An unsound tier can disagree with a sound one on a value-level program.**
In every format, for every extra-payload set and input: `isNaN (0.0 * +∞)` has
no `min`/`max` and no bit-level use, `tierCtfe` is sound and `tierBad` is not, and
the two compute different observations. (The tier-soundness hypotheses of the
tier corollaries of the determinism theorems cannot be dropped.) -/
theorem unsound_tier_breaks_agreement (X : Extra f) (ρ : Nat → V f) :
    ¬ TierSound X tierBad ∧ TierSound X tierCtfe ∧
    (progIsNaNZeroMulInf f).BitSafe X ρ V.isNaNOrZero ∧
    (progIsNaNZeroMulInf f).BitSafe X ρ V.isNaN ∧
    (progIsNaNZeroMulInf f).MinMaxFree = true ∧
    (progIsNaNZeroMulInf f).runT tierBad ρ ≠ (progIsNaNZeroMulInf f).runT tierCtfe ρ := by
  refine ⟨not_tierSound_tierBad X, tierOf_sound X _, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, rfl, ?_⟩
  rw [(tiers_agree_on_isNaN_zero_mul_inf ρ).1]
  simp [progIsNaNZeroMulInf, Prog.runT, FExpr.evalT, tierBad, V.isNaN]

/-! ### Extra payloads -/

/-- If `S` allows a NaN result `r` for `p` on `x`, `y`, then for every
extra-payload set `X'` every element of `NaNChoice X' x y` is allowed. -/
theorem primSet_of_isNaN {X X' : Extra f} {p : Prim} {x y r r' : V f}
    (h : primSet X p x y r) (hr : r.isNaN = true) (h' : NaNChoice X' x y r') :
    primSet X' p x y r' := by
  have harith : ∀ c : FP f, arithSet X c x y r → arithSet X' c x y r' := by
    intro c hc
    unfold arithSet at hc ⊢
    split at hc
    · rename_i hcn; simp only [hcn, ↓reduceIte]; exact h'
    · rename_i hcn
      exfalso
      subst hc
      revert hr hcn
      cases c <;> simp [V.ofFP, V.isNaN, FP.isNaN]
  cases p with
  | add => exact harith _ h
  | sub => exact harith _ h
  | mul => exact harith _ h
  | min =>
    simp only [primSet, minSet] at h ⊢
    cases hx : x.isNaN <;> cases hy : y.isNaN <;>
      simp only [hx, hy, Bool.and_self, Bool.and_true, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte] at h ⊢
    · exfalso
      split at h
      · subst h; simp_all
      · split at h
        · subst h; simp_all
        · rcases h with rfl | rfl <;> simp_all
    · exfalso; subst h; simp_all
    · exfalso; subst h; simp_all
    · exact h'
  | max =>
    simp only [primSet, maxSet] at h ⊢
    cases hx : x.isNaN <;> cases hy : y.isNaN <;>
      simp only [hx, hy, Bool.and_self, Bool.and_true, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte] at h ⊢
    · exfalso
      split at h
      · subst h; simp_all
      · split at h
        · subst h; simp_all
        · rcases h with rfl | rfl <;> simp_all
    · exfalso; subst h; simp_all
    · exfalso; subst h; simp_all
    · exact h'

/-- **Extra payloads matter for soundness when `p ≥ 3`.** In `F23` (precision 3,
two NaN payloads), the tier `tierExtraPay1`, which returns payload `1` on every
NaN result, is sound for the extra-payload set `extraPay1` (payload `1` allowed)
and not sound for `noExtra`. -/
theorem tierExtraPay1_sound_extra_not_noExtra :
    TierSound extraPay1 tierExtraPay1 ∧ ¬ TierSound noExtra tierExtraPay1 := by
  constructor
  · intro p x y
    have hs := tierOf_sound extraPay1 ctfePolicy p x y
    unfold tierExtraPay1
    split
    · rename_i hn
      exact primSet_of_isNaN hs hn ⟨rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · exact hs
  · intro h
    have := h .mul (V.zero F23 false) (.inf false)
    revert this; decide

/-- **Extra payloads are irrelevant when `p = 2`.** In every format with
precision `p = 2` there is exactly one NaN payload (`0`), so for every
extra-payload set `X` and every tier `τ`, `τ` is sound for `X` iff it is sound
for `noExtra`. -/
theorem tierSound_extra_irrelevant_of_p_eq_two (hp2 : f.p = 2) (X : Extra f) (τ : Tier f) :
    TierSound X τ ↔ TierSound noExtra τ := by
  have hpc : f.payCount = 1 := by simp [Fmt.payCount, hp2]
  have hnan : ∀ x y r : V f, NaNChoice X x y r ↔ NaNChoice noExtra x y r := by
    intro x y r
    cases r with
    | snan s k => exact absurd k.isLt (by omega)
    | inf s => simp [NaNChoice, V.isNaN]
    | fin s E M => simp [NaNChoice, V.isNaN]
    | qnan s k =>
      have hk0 : k.val = 0 := by have := k.isLt; omega
      simp [NaNChoice, V.isNaN, V.isQuiet, V.payload, hk0]
  constructor <;> intro h p x y
  · have hpxy := h p x y
    cases p <;> simp only [primSet, arithSet, minSet, maxSet] at hpxy ⊢
    all_goals
      try (split at hpxy <;> simp_all)
  · have hpxy := h p x y
    cases p <;> simp only [primSet, arithSet, minSet, maxSet] at hpxy ⊢
    all_goals
      try (split at hpxy <;> simp_all)

/-! ### `BitSafe`: examples, guarded branches and non-necessity -/

/-- `BitSafe` constrains only branches that some `S`-execution takes. In every
format, for every extra-payload set and input: `progGuardedDeadCopysign`
satisfies `BitSafe` for `V.isNaNOrZero`, although the sign argument `0.0 * +∞`
of the `copysign` in its untaken branch has a NaN result; `S` allows exactly the
observation `1` for it; and `progGuardedInputCopysign` (a `copysign` on the
input, guarded by `0.0 < var 0`) satisfies `BitSafe` for `V.isNaNOrZero` for
every input, including NaN and zero inputs. -/
theorem ex_bitSafe_guarded (X : Extra f) (ρ : Nat → V f) :
    (progGuardedDeadCopysign f).BitSafe X ρ V.isNaNOrZero ∧
    (FExpr.prim .mul (.lit (V.zero f false)) (.lit (.inf false))).evalS X ρ (V.prefNaN f false) ∧
    (∀ n, (progGuardedDeadCopysign f).runS X ρ n ↔ n = 1) ∧
    (progGuardedInputCopysign f).BitSafe X ρ V.isNaNOrZero := by
  have hnan : (FExpr.prim .mul (.lit (V.zero f false)) (.lit (.inf false))).evalS X ρ
      (V.prefNaN f false) := (evalS_mulZeroInf X ρ _).2 ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨?_, hnan, ?_, ?_⟩
  · refine ⟨trivial, ⟨trivial, trivial⟩, trivial, ?_, fun _ => trivial⟩
    rintro ⟨x, y, hx, hy, hlt⟩
    have hn := ((evalS_mulZeroInf X ρ x).1 hx).1
    rw [V.toFP_eq_nan_of_isNaN hn] at hlt
    simp [lt, FP.isNaN] at hlt
  · intro n
    simp only [progGuardedDeadCopysign, Prog.runS]
    constructor
    · rintro ⟨x, y, hx, ⟨a, b, ha, hb, hy⟩, rfl⟩
      simp only [FExpr.evalS] at hx hb
      subst hx hb
      rw [V.toFP_eq_nan_of_isNaN ((evalS_mulZeroInf X ρ a).1 ha).1] at hy
      simp only [lt, FP.isNaN, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        FExpr.evalS] at hy
      subst hy
      rw [vzero_toFP, lt_zero_one]; rfl
    · rintro rfl
      refine ⟨V.zero f false, V.one f, rfl, ⟨V.prefNaN f false, V.zero f false, hnan, rfl, ?_⟩, ?_⟩
      · rw [show (V.prefNaN f false).toFP = .nan from rfl]
        simp only [lt, FP.isNaN, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          FExpr.evalS]
      · rw [vzero_toFP, lt_zero_one]; rfl
  · refine ⟨trivial, trivial, trivial, ?_, fun _ => trivial⟩
    rintro ⟨x, y, hx, hy, hlt⟩
    simp only [FExpr.evalS] at hx hy; subst hx hy
    refine ⟨trivial, trivial, ?_⟩
    intro z hz; simp only [FExpr.evalS] at hz; subst hz
    unfold V.isNaNOrZero
    cases hy0 : (ρ 0) with
    | qnan s k => rw [hy0] at hlt; simp [V.toFP, lt, FP.isNaN] at hlt
    | snan s k => rw [hy0] at hlt; simp [V.toFP, lt, FP.isNaN] at hlt
    | inf s => rfl
    | fin s E M =>
      rw [hy0] at hlt
      simp only [V.isNaN, Bool.false_or, V.isZero, V.toFP]
      cases hz0 : (FP.fin s E M).isZero
      · rfl
      · obtain ⟨t, ht⟩ := isZero_iff_eq_zero.1 hz0
        rw [vzero_toFP] at hlt
        simp only [V.toFP] at hlt
        rw [ht, lt_zero_zero] at hlt
        contradiction

/-- **`BitSafe` is sufficient, not necessary.** In every format, for every
extra-payload set and input: `signBit (abs (0.0 * +∞))` and
`toBits (lit (negative preferred quiet NaN))` are `min`/`max`-free, each applies
a bit-level observation to a NaN (so neither satisfies `BitSafe` for
`V.isNaN`), and yet `S` allows exactly one observation for each. -/
theorem bitSafe_not_necessary (X : Extra f) (ρ : Nat → V f) :
    ¬ (progSignBitAbsNaN f).BitSafe X ρ V.isNaN ∧ (progSignBitAbsNaN f).MinMaxFree = true ∧
    (∀ n, (progSignBitAbsNaN f).runS X ρ n ↔ n = 0) ∧
    ¬ (progBitsNaNLit f).BitSafe X ρ V.isNaN ∧ (progBitsNaNLit f).MinMaxFree = true ∧
    (∀ n, (progBitsNaNLit f).runS X ρ n ↔ n = (V.prefNaN f true).bits) := by
  have hnan : (FExpr.prim .mul (.lit (V.zero f false)) (.lit (.inf false))).evalS X ρ
      (V.prefNaN f false) := (evalS_mulZeroInf X ρ _).2 ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨?_, rfl, ?_, ?_, rfl, ?_⟩
  · rintro ⟨_, h⟩
    have := h ((V.prefNaN f false).abs) ⟨_, hnan, rfl⟩
    exact absurd this (by simp [V.prefNaN, V.abs, V.withSign, V.isNaN])
  · intro n
    simp only [progSignBitAbsNaN, Prog.runS]
    constructor
    · rintro ⟨x, ⟨y, _, rfl⟩, rfl⟩
      cases y <;> rfl
    · rintro rfl; exact ⟨_, ⟨_, hnan, rfl⟩, rfl⟩
  · rintro ⟨_, h⟩
    have := h (V.prefNaN f true) rfl
    exact absurd this (by simp [V.prefNaN, V.isNaN])
  · intro n
    simp only [progBitsNaNLit, Prog.runS, FExpr.evalS]
    constructor
    · rintro ⟨x, rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨_, rfl, rfl⟩

/-- Non-vacuity of `Prog.runS_unique_of_minMaxFree_of_bitSafe_nan` with a NaN
literal: in every format, for every extra-payload set and input,
`isNaN (lit (negative preferred quiet NaN) + 1.0)` is `min`/`max`-free,
satisfies `BitSafe` for `V.isNaN` and for `V.isNaNOrZero` (it has no bit-level
use), and `S` allows exactly the observation `1`. -/
theorem progIsNaNLitAdd_nonvacuous (X : Extra f) (ρ : Nat → V f) :
    (progIsNaNLitAdd f).MinMaxFree = true ∧ (progIsNaNLitAdd f).BitSafe X ρ V.isNaN ∧
    (progIsNaNLitAdd f).BitSafe X ρ V.isNaNOrZero ∧
    (∀ n, (progIsNaNLitAdd f).runS X ρ n ↔ n = 1) := by
  have hc : add (V.prefNaN f true).toFP (V.one f).toFP = .nan := rfl
  refine ⟨rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, fun n => ?_⟩
  simp only [progIsNaNLitAdd, Prog.runS]
  constructor
  · rintro ⟨x, ⟨a, b, ha, hb, h⟩, rfl⟩
    simp only [FExpr.evalS] at ha hb; subst ha hb
    simp only [primSet, arithSet, hc, FP.isNaN, ↓reduceIte] at h
    rw [h.1]; rfl
  · rintro rfl
    refine ⟨V.prefNaN f false, ⟨_, _, rfl, rfl, ?_⟩, rfl⟩
    simp only [primSet, arithSet, hc, FP.isNaN, ↓reduceIte]
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-! ### Refuted statements -/

/-- **Refuted: "value-level observations of the sound tiers `tierCtfe` and
`tierRunA` agree"** (without the hypothesis of
`Prog.runS_unique_of_bitSafe_nanOrZero`). In every format and for every input
there is a `<`-observation, `progCopysignNaN`, on which they differ. -/
theorem refuted_value_level_observations_of_sound_tiers_agree (ρ : Nat → V f) :
    ¬ (∀ (a b : FExpr f), (Prog.lt a b).runT tierCtfe ρ = (Prog.lt a b).runT tierRunA ρ) := by
  intro h
  have h1 := progCopysignNaN_runT_tierCtfe (f := f) ρ
  have h2 := progCopysignNaN_runT_tierRunA (f := f) ρ
  unfold progCopysignNaN at h1 h2
  have := h (.lit (V.zero f false))
    (.copysign (.lit (V.one f)) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))
  rw [h1, h2] at this
  exact absurd this (by decide)

/-- **Refuted: "a tier that uses extra payloads is sound for an extra-payload set
containing them and not for `noExtra`"**, as a statement about every format. In
`F32` (precision 2) there is no extra-payload set `X` and tier `τ` with `τ`
sound for `X` and not for `noExtra`. -/
theorem refuted_extra_payload_tier_separates_noExtra_p2 :
    ¬ ∃ (X : Extra F32) (τ : Tier F32), TierSound X τ ∧ ¬ TierSound noExtra τ := by
  rintro ⟨X, τ, h, hn⟩
  exact hn ((tierSound_extra_irrelevant_of_p_eq_two rfl X τ).1 h)

end Toy.FloatTier
