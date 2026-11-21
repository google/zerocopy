/-
Toy.FloatTier.CastExamples
==========================

Concrete, fully proved examples for the conversion definitions, the
counterexamples to the folklore `x <= (2^W - 1 as float)` guard, and
non-vacuity witnesses for the conversion results.
-/
import Toy.FloatTier.Instances

namespace Toy.FloatTier

/-! ### Definition examples -/

/-- `trunc` truncates toward zero: `trunc 3.5 = 3`, `trunc (-3.5) = -3` (not the
floor `-4`), `trunc (-0.5) = 0`. -/
theorem ex_trunc_F33 :
    trunc f33_3p5 = 3 ∧ trunc f33_m3p5 = -3 ∧ trunc f33_m0p5 = 0 := by decide

/-- `cvtU` (positive): `cvtU 2 3.5 = some 3` and `cvtU 2 (-0.5) = some 0` (a
negative input inside `(-1, 4)` is defined). -/
theorem ex_cvtU_defined_F33 : cvtU 2 f33_3p5 = some 3 ∧ cvtU 2 f33_m0p5 = some 0 := by decide

/-- `cvtU` (negative): `4.0`, `-1.0`, NaN and `+∞` are undefined for width 2. -/
theorem ex_cvtU_undefined_F33 :
    cvtU 2 f33_4 = none ∧ cvtU 2 (negOne F33) = none ∧ cvtU 2 (FP.nan : FP F33) = none ∧
      cvtU 2 (FP.inf false : FP F33) = none := by decide

/-- `cvtS` (signed width 3, range `[-4, 3]`): `-3.5 ↦ -3` and `3.5 ↦ 3` are
defined, `4.0` is not. -/
theorem ex_cvtS_F33 :
    cvtS 2 f33_m3p5 = some (-3) ∧ cvtS 2 f33_3p5 = some 3 ∧ cvtS 2 f33_4 = none := by decide

/-- `satU` (width 2, range `[0, 3]`): NaN ↦ 0, `+∞` ↦ 3, `-∞` ↦ 0, `-3.5` ↦ 0,
`3.5` ↦ 3, and `5.0` ↦ 3 (it saturates rather than wrapping to `5 mod 4 = 1`). -/
theorem ex_satU_F33 :
    satU 2 (FP.nan : FP F33) = 0 ∧ satU 2 (FP.inf false : FP F33) = 3 ∧
      satU 2 (FP.inf true : FP F33) = 0 ∧ satU 2 f33_m3p5 = 0 ∧ satU 2 f33_3p5 = 3 ∧
      satU 2 f33_5 = 3 := by decide

/-- `satS` (signed width 3, range `[-4, 3]`): NaN ↦ 0, `+∞` ↦ 3, `-∞` ↦ -4,
`-3.5` ↦ -3, `5.0` ↦ 3 and `-5.0` ↦ -4. -/
theorem ex_satS_F33 :
    satS 2 (FP.nan : FP F33) = 0 ∧ satS 2 (FP.inf false : FP F33) = 3 ∧
      satS 2 (FP.inf true : FP F33) = -4 ∧ satS 2 f33_m3p5 = -3 ∧ satS 2 f33_5 = 3 ∧
      satS 2 (FP.mk' F33 true 5 1) = -4 := by decide

/-- The degenerate unsigned width `W = 0` (range `[0, 0]`): in every format the
saturating conversion returns `0` on every input, including `+∞`. -/
theorem satU_width_zero {f : Fmt} (x : FP f) : satU 0 x = 0 := by
  have h := (satU_saturates_and_agrees 0 x).1
  simp at h
  omega

/-- `InOpenU` (positive and negative) in `F33` with `W = 2` (interval `(-1, 4)`):
`3.5` and `-0.5` lie in it; `4.0`, `-1.0`, NaN, `+∞` and `-∞` do not. -/
theorem ex_inOpenU_F33 :
    InOpenU 2 f33_3p5 ∧ InOpenU 2 f33_m0p5 ∧ ¬ InOpenU 2 f33_4 ∧ ¬ InOpenU 2 (negOne F33) ∧
      ¬ InOpenU 2 (FP.nan : FP F33) ∧ ¬ InOpenU 2 (FP.inf false : FP F33) ∧
      ¬ InOpenU 2 (FP.inf true : FP F33) := by decide

/-- `InOpenS` (positive and negative) in `F33`: with `k = 2` (interval `(-5, 4)`)
`-3.5` and `3.5` lie in it and `4.0`, NaN, `+∞`, `-∞` do not; with `k = 1`
(interval `(-3, 2)`) `-3.5` does not. -/
theorem ex_inOpenS_F33 :
    InOpenS 2 f33_m3p5 ∧ InOpenS 2 f33_3p5 ∧ ¬ InOpenS 1 f33_m3p5 ∧ ¬ InOpenS 2 f33_4 ∧
      ¬ InOpenS 2 (FP.nan : FP F33) ∧ ¬ InOpenS 2 (FP.inf false : FP F33) ∧
      ¬ InOpenS 2 (FP.inf true : FP F33) := by decide

/-- Tightness of `hx : x.isFinite = true` in `trunc_mem_unsigned_range_iff` and
`trunc_mem_signed_range_iff`. In every format and for every `W` and `k`: `+∞` is
not finite, `trunc (+∞)` is the junk value `0`, which lies in both target ranges,
but `+∞` lies in neither open interval, so both equivalences fail at `x = +∞`. -/
theorem trunc_mem_range_iff_fails_at_inf {f : Fmt} (W k : Nat) :
    (FP.inf false : FP f).isFinite = false ∧
    ¬ ((0 ≤ trunc (FP.inf false : FP f) ∧ trunc (FP.inf false : FP f) ≤ 2 ^ W - 1) ↔
        InOpenU W (FP.inf false : FP f)) ∧
    ¬ ((-(2 ^ k) ≤ trunc (FP.inf false : FP f) ∧ trunc (FP.inf false : FP f) ≤ 2 ^ k - 1) ↔
        InOpenS k (FP.inf false : FP f)) := by
  have ht : trunc (FP.inf false : FP f) = 0 := (trunc_uval_of_not_finite _ rfl).1
  have hn := not_inOpen_of_not_finite (f := f) W k (FP.inf false) rfl
  have hW : (1 : Int) ≤ 2 ^ W := by have := Nat.two_pow_pos W; rw [int_two_pow]; omega
  have hK : (1 : Int) ≤ 2 ^ k := by have := Nat.two_pow_pos k; rw [int_two_pow]; omega
  refine ⟨rfl, fun h => hn.1 (h.1 ⟨by omega, by omega⟩), fun h => hn.2 (h.1 ⟨by omega, by omega⟩)⟩

/-- `negOne` is `-1.0`: its key is `-2^qneg` (`-16` in `F33`). -/
theorem ex_negOne_F33 : key (negOne F33) = -16 := by decide

/-- `twoPowRound` and `TwoPowFits` (positive): `2^2 = 4.0` fits in `F33` and
rounds exactly. -/
theorem ex_twoPowRound_fits_F33 : TwoPowFits F33 2 ∧ twoPowRound F33 2 = f33_4 := by decide

/-- `twoPowRound` and `TwoPowFits` (negative): `2^4 = 16` exceeds the largest
finite value `14` of `F33` and rounds to `+∞`. -/
theorem ex_twoPowRound_overflow_F33 :
    ¬ TwoPowFits F33 4 ∧ twoPowRound F33 4 = .inf false := by decide

/-- `TwoPowFits` holds for `(W, format) = (32, binary32)`. -/
theorem ex_twoPowFits_binary32_32 : TwoPowFits Fbin32 32 := by decide

/-- `rangeCheckU` (positive and negative): with `c = 4.0` it accepts `3.5` and
`-0.5` and rejects `4.0`, `-1.0`, NaN and `+∞`. -/
theorem ex_rangeCheckU_F33 :
    rangeCheckU f33_4 f33_3p5 = true ∧ rangeCheckU f33_4 f33_m0p5 = true ∧
      rangeCheckU f33_4 f33_4 = false ∧ rangeCheckU f33_4 (negOne F33) = false ∧
      rangeCheckU f33_4 (FP.nan : FP F33) = false ∧
      rangeCheckU f33_4 (FP.inf false : FP F33) = false := by decide

/-! ### The folklore guard `x <= (2^W - 1 as float)` -/

/-- **The guard `x <= (2^W - 1 as float)` is not exact.**
(1) In `F32` (precision 2) with `W = 3`: `7 as float` rounds up to `8 = 2^3`, so
the guard accepts `x = 8.0`, for which the unchecked conversion is undefined;
the exact guard rejects it.
(2) In `F33` with `W = 2`: `3 as float` is exact (`roundNat_F33_three_exact`) and the guard rejects
`x = 3.5`, for which the unchecked conversion is defined (`trunc 3.5 = 3`);
the exact guard accepts it. -/
theorem naiveCheckU_not_exact_small :
    (roundNat F32 7 = twoPowRound F32 3 ∧ naiveCheckU 3 (twoPowRound F32 3) = true ∧
      cvtU 3 (twoPowRound F32 3) = none ∧ rangeCheckU (twoPowRound F32 3) (twoPowRound F32 3) = false) ∧
    (naiveCheckU 2 f33_3p5 = false ∧ cvtU 2 f33_3p5 = some 3 ∧
      rangeCheckU (twoPowRound F33 2) f33_3p5 = true) := by decide

/-- **The guard `x <= (2^W - 1 as float)` at `(W, format) = (32, binary32)`.**
`(2^32 - 1) as float` rounds to `2^32`, so the guard accepts `x = 2^32`, for
which the unchecked conversion to width 32 is undefined; the exact guard
`x > -1.0 && x < 2^32` rejects it. -/
theorem naiveCheckU_accepts_two_pow_32_binary32 :
    roundNat Fbin32 (2 ^ 32 - 1) = twoPowRound Fbin32 32 ∧
    naiveCheckU 32 (twoPowRound Fbin32 32) = true ∧ cvtU 32 (twoPowRound Fbin32 32) = none ∧
    rangeCheckU (twoPowRound Fbin32 32) (twoPowRound Fbin32 32) = false := by decide +kernel

/-- At `(W, format) = (128, binary32)`, `(2^128 - 1) as float` overflows to `+∞`, so
the guard `x <= (2^W - 1 as float)` accepts `x = +∞`, for which the unchecked
conversion to width 128 is undefined; the exact guard `x > -1.0 && x < +∞`
(here `twoPowRound Fbin32 128 = +∞`) rejects it. -/
theorem naiveCheckU_accepts_inf_binary32_128 :
    roundNat Fbin32 (2 ^ 128 - 1) = .inf false ∧ naiveCheckU 128 (FP.inf false : FP Fbin32) = true ∧
    cvtU 128 (FP.inf false : FP Fbin32) = none ∧
    rangeCheckU (twoPowRound Fbin32 128) (FP.inf false : FP Fbin32) = false := by decide +kernel

/-- At `(W, format) = (3, F23)`, where `W` equals the precision `p = 3`,
`(2^3 - 1) as float` overflows `F23` (largest finite value `3.5`) to `+∞`, so the
guard `x <= (2^W - 1 as float)` accepts `x = +∞`, for which `cvtU 3` is
undefined; the exact guard rejects it. -/
theorem naiveCheckU_accepts_inf_F23_3 :
    roundNat F23 (2 ^ 3 - 1) = .inf false ∧ naiveCheckU 3 (FP.inf false : FP F23) = true ∧
    cvtU 3 (FP.inf false : FP F23) = none ∧
    rangeCheckU (twoPowRound F23 3) (FP.inf false : FP F23) = false := by decide

/-- **In `F23` the guard `x <= (2^W - 1 as float)` is inexact at every width.**
For every width `W` there is a value `x` of `F23` on which the guard
`naiveCheckU W x` disagrees with definedness of `cvtU W x`. -/
theorem naiveCheckU_inexact_every_width_F23 (W : Nat) :
    ∃ x : FP F23, naiveCheckU W x ≠ (cvtU W x).isSome := by
  match W with
  | 0 => exact ⟨FP.mk' F23 false 0 2, by decide⟩
  | 1 => exact ⟨FP.mk' F23 false 1 2, by decide⟩
  | 2 => exact ⟨FP.mk' F23 false 2 3, by decide⟩
  | W' + 3 =>
    refine ⟨FP.inf false, ?_⟩
    have hge : 7 ≤ 2 ^ (W' + 3) - 1 := by
      have : 2 ^ 3 ≤ 2 ^ (W' + 3) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hmul : 28 ≤ (2 ^ (W' + 3) - 1) * 2 ^ F23.qneg := by
      have hq : 2 ^ F23.qneg = 4 := by decide
      rw [hq]; omega
    have hru : F23.maxUnits < roundUnits F23 ((2 ^ (W' + 3) - 1) * 2 ^ F23.qneg) 0 := by
      have hmax : F23.maxUnits = 14 := by decide
      have hr := rneDiv_ge ((2 ^ (W' + 3) - 1) * 2 ^ F23.qneg)
        (bitLen ((2 ^ (W' + 3) - 1) * 2 ^ F23.qneg) - F23.p)
      unfold roundUnits
      dsimp only
      simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add]
      generalize ht : bitLen ((2 ^ (W' + 3) - 1) * 2 ^ F23.qneg) - F23.p = t at hr ⊢
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · simp at hr; omega
      · have hpos : 0 < (2 ^ (W' + 3) - 1) * 2 ^ F23.qneg := by omega
        have hbs := (bitLen_spec hpos).1
        have hp3 : F23.p = 3 := rfl
        have hbge : 5 ≤ bitLen ((2 ^ (W' + 3) - 1) * 2 ^ F23.qneg) := by
          have := le_bitLen_of_le (k := 4)
            (show 2 ^ 4 ≤ (2 ^ (W' + 3) - 1) * 2 ^ F23.qneg by omega)
          omega
        have ht2 : 2 ≤ t := by omega
        have hqge : 4 ≤ (2 ^ (W' + 3) - 1) * 2 ^ F23.qneg / 2 ^ t := by
          rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos t)]
          have : 4 * 2 ^ t = 2 ^ (t + 2) := by rw [Nat.pow_add]; omega
          rw [this]
          exact Nat.le_trans (two_pow_le_two_pow (by omega)) hbs
        have hpow : 4 ≤ 2 ^ t :=
          calc 4 = 2 ^ 2 := rfl
            _ ≤ 2 ^ t := two_pow_le_two_pow ht2
        have hprod : 16 ≤ rneDiv ((2 ^ (W' + 3) - 1) * 2 ^ F23.qneg) t * 2 ^ t :=
          calc 16 = 4 * 4 := rfl
            _ ≤ _ := Nat.mul_le_mul (by omega) hpow
        omega
    have hrnd : roundNat F23 (2 ^ (W' + 3) - 1) = .inf false := by
      unfold roundNat round
      exact mkFin_overflow hru false
    have hnaive : naiveCheckU (W' + 3) (FP.inf false : FP F23) = true := by
      unfold naiveCheckU
      rw [hrnd]
      decide
    have hcvt : (cvtU (W' + 3) (FP.inf false : FP F23)).isSome = false := rfl
    rw [hnaive, hcvt]
    decide

/-- **Refuted: "the guard `x <= (2^W - 1 as float)` is exact when `W` equals the
precision `p`"**, as a statement about every format. In `F23` (`p = 3`) the
guard at `W = 3` disagrees with definedness of `cvtU 3` at `x = +∞`. -/
theorem refuted_naiveCheckU_exact_at_W_eq_p :
    F23.p = 3 ∧ ¬ (∀ x : FP F23, naiveCheckU 3 x = (cvtU 3 x).isSome) := by
  refine ⟨rfl, fun h => ?_⟩
  have := h (FP.inf false)
  rw [naiveCheckU_accepts_inf_F23_3.2.1, naiveCheckU_accepts_inf_F23_3.2.2.1] at this
  exact absurd this (by decide)

/-! ### Signed analogues of the guard -/

/-- **Two signed analogues of the two-comparison guard are not exact** (in
`F33`, precision 3; signed width `k + 1`).
(1) `k = 3` (so `k ≥ p`): `-2^3 - 1 = -9` rounds with ties-to-even to `-8.0`, so
the strict lower bound `x > (-2^k - 1 as float)` rejects `x = -8.0`, for which
`cvtS 3` is defined.
(2) `k = 1` (so `k < p`): the lower bound `x >= -2^k` rejects `x = -2.5`, for
which `cvtS 1` is defined (`trunc (-2.5) = -2`). -/
theorem signed_lower_guards_not_exact_F33 :
    (round F33 true (9 * 2 ^ F33.qneg) 0 = FP.mk' F33 true 6 0 ∧
      lt (round F33 true (9 * 2 ^ F33.qneg) 0) (FP.mk' F33 true 6 0) = false ∧
      cvtS 3 (FP.mk' F33 true 6 0) = some (-8)) ∧
    (le (FP.mk' F33 true 4 0) (FP.mk' F33 true 4 1) = false ∧
      cvtS 1 (FP.mk' F33 true 4 1) = some (-2)) := by decide

/-! ### Non-vacuity witnesses for the conversion results -/

/-- Non-vacuity for the truncation and unchecked-conversion results: finite
inputs of `F33` on both sides of the unsigned interval for `W = 2` and of the
signed interval for `k = 2` and `k = 1`, with the corresponding conversions. -/
theorem cast_results_nonvacuous :
    f33_3p5.isFinite = true ∧ f33_4.isFinite = true ∧ f33_m3p5.isFinite = true ∧
    InOpenU 2 f33_3p5 ∧ ¬ InOpenU 2 f33_4 ∧ InOpenS 2 f33_m3p5 ∧ ¬ InOpenS 1 f33_m3p5 ∧
    cvtU 2 f33_3p5 = some 3 ∧ cvtU 2 f33_4 = none ∧
    cvtS 2 f33_m3p5 = some (-3) ∧ cvtS 1 f33_m3p5 = none := by decide

/-- Non-vacuity for `rangeCheckU_twoPowRound_iff`, both cases. In `F33` with
`W = 2`, `2^2` fits and `c = 4.0`: the guard accepts `3.5` and rejects `4.0`. In
`F33` with `W = 4`, `2^4` does not fit and `c = +∞`: the guard accepts `4.0` and
rejects `+∞`. In binary32 with `W = 32`, `2^32` fits and the guard rejects
`x = 2^32`. In each instance the guard agrees with definedness of `cvtU W x`. -/
theorem rangeCheckU_twoPowRound_iff_nonvacuous :
    (TwoPowFits F33 2 ∧ twoPowRound F33 2 = f33_4 ∧
      rangeCheckU (twoPowRound F33 2) f33_3p5 = true ∧ (cvtU 2 f33_3p5).isSome = true ∧
      rangeCheckU (twoPowRound F33 2) f33_4 = false ∧ (cvtU 2 f33_4).isSome = false) ∧
    (¬ TwoPowFits F33 4 ∧ twoPowRound F33 4 = .inf false ∧
      rangeCheckU (twoPowRound F33 4) f33_4 = true ∧ (cvtU 4 f33_4).isSome = true ∧
      rangeCheckU (twoPowRound F33 4) (FP.inf false : FP F33) = false ∧
      (cvtU 4 (FP.inf false : FP F33)).isSome = false) ∧
    (TwoPowFits Fbin32 32 ∧
      rangeCheckU (twoPowRound Fbin32 32) (twoPowRound Fbin32 32) = false ∧
      (cvtU 32 (twoPowRound Fbin32 32)).isSome = false) := by decide +kernel

end Toy.FloatTier
