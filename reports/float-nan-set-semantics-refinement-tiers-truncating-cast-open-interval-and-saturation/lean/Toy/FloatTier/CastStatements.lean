/-
Toy.FloatTier.CastStatements
============================

Main results about float-to-integer conversion: the open-interval
characterization of truncation, undefined behaviour of the unchecked
conversion, exactness of the two-comparison range check, and the saturating
conversion.
-/
import Toy.FloatTier.Statements

namespace Toy.FloatTier

variable {f : Fmt}

/-! ### Auxiliary facts -/

theorem int_two_pow (n : Nat) : (2 : Int) ^ n = ((2 ^ n : Nat) : Int) := by
  simp

theorem unitsOf_bias_zero (f : Fmt) : unitsOf f f.bias 0 = 2 ^ f.qneg := by
  have hb := f.one_le_bias
  have hp := f.two_le_p
  rw [show f.bias = (f.bias - 1) + 1 by omega, unitsOf_succ, Nat.add_zero, Fmt.fracCount,
    ← Nat.pow_add]
  congr 1
  unfold Fmt.qneg
  omega

theorem key_negOne (f : Fmt) : key (negOne f) = -((2 ^ f.qneg : Nat) : Int) := by
  simp [negOne, key, sval, unitsOf_bias_zero]

theorem two_pow_qneg_le_maxUnits (f : Fmt) : 2 ^ f.qneg ≤ f.maxUnits := by
  have := unitsOf_le_maxUnits f f.bias_lt_expCount f.fracCount_pos
  rwa [unitsOf_bias_zero] at this

theorem twoPowRound_eq_mkFin (W : Nat) : twoPowRound f W = mkFin f false (2 ^ (W + f.qneg)) := by
  unfold twoPowRound round
  rw [roundUnits_repr0 (isRepr_two_pow f _)]

/-- If `2^W` fits, rounding it is exact: the result is finite with value
`2^W` (key `2^(W + qneg)`). -/
theorem twoPowRound_of_fits {W : Nat} (h : TwoPowFits f W) :
    (twoPowRound f W).isFinite = true ∧ key (twoPowRound f W) = ((2 ^ (W + f.qneg) : Nat) : Int) := by
  rw [twoPowRound_eq_mkFin]
  obtain ⟨E, M, hm, hu⟩ := mkFin_repr (isRepr_two_pow f _) h
  rw [hm false]
  simp [FP.isFinite, key, sval, hu]

/-- If `2^W` does not fit, rounding it overflows to `+∞`. -/
theorem twoPowRound_of_not_fits {W : Nat} (h : ¬ TwoPowFits f W) : twoPowRound f W = .inf false := by
  rw [twoPowRound_eq_mkFin]
  exact mkFin_overflow (Nat.lt_of_not_le h) false

/-! ### Truncation and the unchecked conversion -/

/-- On NaN and infinities, `trunc` and `uval` are both `0`. -/
theorem trunc_uval_of_not_finite (x : FP f) (hx : x.isFinite = false) :
    trunc x = 0 ∧ x.uval = 0 := by
  cases x with
  | nan => simp [trunc, FP.uval, FP.units, sval]
  | inf s => simp [trunc, FP.uval, FP.units, sval]
  | fin s E M => simp [FP.isFinite] at hx

/-- `InOpenU` and `InOpenS` are false on NaN and on `±∞`. -/
theorem not_inOpen_of_not_finite (W k : Nat) (x : FP f) (hx : x.isFinite = false) :
    ¬ InOpenU W x ∧ ¬ InOpenS k x := by
  constructor
  · intro h; have h1 := h.1; rw [hx] at h1; exact absurd h1 (by decide)
  · intro h; have h1 := h.1; rw [hx] at h1; exact absurd h1 (by decide)

/-- **Open-interval truncation, unsigned.** For every format, width `W` and
finite `x`: `trunc x` (truncation toward zero, computed by floor division of the
magnitude) lies in `[0, 2^W - 1]` iff `InOpenU W x`, i.e. iff `x` is finite and
`-1 < x < 2^W`. -/
theorem trunc_mem_unsigned_range_iff (W : Nat) (x : FP f) (hx : x.isFinite = true) :
    (0 ≤ trunc x ∧ trunc x ≤ 2 ^ W - 1) ↔ InOpenU W x := by
  have key : (0 ≤ trunc x ∧ trunc x ≤ 2 ^ W - 1) ↔
      (-((2 : Int) ^ f.qneg) < x.uval ∧ x.uval < (2 : Int) ^ W * 2 ^ f.qneg) := by
    unfold trunc FP.uval
    have hd : 0 < 2 ^ f.qneg := Nat.two_pow_pos _
    have k1 : x.units / 2 ^ f.qneg < 2 ^ W ↔ x.units < 2 ^ W * 2 ^ f.qneg :=
      Nat.div_lt_iff_lt_mul hd
    have k0 : x.units / 2 ^ f.qneg < 1 ↔ x.units < 1 * 2 ^ f.qneg := Nat.div_lt_iff_lt_mul hd
    have hP := Nat.two_pow_pos W
    have hPD : 0 < 2 ^ W * 2 ^ f.qneg := Nat.mul_pos hP hd
    rw [show (2 : Int) ^ W * 2 ^ f.qneg = ((2 ^ W * 2 ^ f.qneg : Nat) : Int) by simp,
      int_two_pow f.qneg, int_two_pow W]
    generalize x.units / 2 ^ f.qneg = k at *
    generalize 2 ^ W * 2 ^ f.qneg = PD at *
    generalize 2 ^ f.qneg = D at *
    generalize 2 ^ W = P at *
    cases x.signBit <;> simp only [sval, Bool.false_eq_true, ite_true, ite_false] <;> omega
  exact ⟨fun h => ⟨hx, key.1 h⟩, fun h => key.2 h.2⟩

/-- **Open-interval truncation, signed.** For every format, every `k` (signed
width `k + 1`) and every finite `x`: `trunc x` (truncation toward zero, computed
by floor division of the magnitude) lies in `[-2^k, 2^k - 1]` iff
`InOpenS k x`, i.e. iff `x` is finite and `-2^k - 1 < x < 2^k`. -/
theorem trunc_mem_signed_range_iff (k : Nat) (x : FP f) (hx : x.isFinite = true) :
    (-(2 ^ k) ≤ trunc x ∧ trunc x ≤ 2 ^ k - 1) ↔ InOpenS k x := by
  have key : (-(2 ^ k) ≤ trunc x ∧ trunc x ≤ 2 ^ k - 1) ↔
      (-(((2 : Int) ^ k + 1) * 2 ^ f.qneg) < x.uval ∧ x.uval < (2 : Int) ^ k * 2 ^ f.qneg) := by
    unfold trunc FP.uval
    have hd : 0 < 2 ^ f.qneg := Nat.two_pow_pos _
    have k1 : x.units / 2 ^ f.qneg < 2 ^ k ↔ x.units < 2 ^ k * 2 ^ f.qneg :=
      Nat.div_lt_iff_lt_mul hd
    have k2 : x.units / 2 ^ f.qneg < 2 ^ k + 1 ↔ x.units < (2 ^ k + 1) * 2 ^ f.qneg :=
      Nat.div_lt_iff_lt_mul hd
    have hK := Nat.two_pow_pos k
    have hKD : 0 < 2 ^ k * 2 ^ f.qneg := Nat.mul_pos hK hd
    have hK1D : 0 < (2 ^ k + 1) * 2 ^ f.qneg := Nat.mul_pos (by omega) hd
    rw [show ((2 : Int) ^ k + 1) * 2 ^ f.qneg = (((2 ^ k + 1) * 2 ^ f.qneg : Nat) : Int) by simp,
      show (2 : Int) ^ k * 2 ^ f.qneg = ((2 ^ k * 2 ^ f.qneg : Nat) : Int) by simp, int_two_pow k]
    generalize x.units / 2 ^ f.qneg = t at *
    generalize (2 ^ k + 1) * 2 ^ f.qneg = K1D at *
    generalize 2 ^ k * 2 ^ f.qneg = KD at *
    generalize 2 ^ k = K at *
    cases x.signBit <;> simp only [sval, Bool.false_eq_true, ite_true, ite_false] <;> omega
  exact ⟨fun h => ⟨hx, key.1 h⟩, fun h => key.2 h.2⟩

/-- **Undefined behaviour of the unchecked unsigned conversion.** `cvtU W x` is
undefined (`none`) iff `¬ InOpenU W x`, i.e. iff `x` is NaN or infinite, or `x`
lies outside the open interval `(-1, 2^W)`. -/
theorem cvtU_eq_none_iff (W : Nat) (x : FP f) :
    cvtU W x = none ↔ ¬ InOpenU W x := by
  unfold cvtU
  by_cases hx : x.isFinite = true
  · have := trunc_mem_unsigned_range_iff W x hx
    split
    · rename_i h; simp only [reduceCtorEq, false_iff, Classical.not_not]; exact this.1 h.2
    · rename_i h; simp only [true_iff]; intro h'; exact h ⟨hx, this.2 h'⟩
  · simp only [Bool.not_eq_true] at hx
    have hn := (not_inOpen_of_not_finite W 0 x hx).1
    simp [hx, hn]

/-- **Undefined behaviour of the unchecked signed conversion.** `cvtS k x` is
undefined (`none`) iff `¬ InOpenS k x`, i.e. iff `x` is NaN or infinite, or `x`
lies outside the open interval `(-2^k - 1, 2^k)`. -/
theorem cvtS_eq_none_iff (k : Nat) (x : FP f) :
    cvtS k x = none ↔ ¬ InOpenS k x := by
  unfold cvtS
  by_cases hx : x.isFinite = true
  · have := trunc_mem_signed_range_iff k x hx
    split
    · rename_i h; simp only [reduceCtorEq, false_iff, Classical.not_not]; exact this.1 h.2
    · rename_i h; simp only [true_iff]; intro h'; exact h ⟨hx, this.2 h'⟩
  · simp only [Bool.not_eq_true] at hx
    have hn := (not_inOpen_of_not_finite 0 k x hx).2
    simp [hx, hn]

theorem cvtU_isSome_iff (W : Nat) (x : FP f) :
    (cvtU W x).isSome = true ↔ InOpenU W x := by
  have := cvtU_eq_none_iff W x
  cases h : cvtU W x with
  | none =>
    simp only [h, true_iff, Option.isSome_none, Bool.false_eq_true, false_iff] at this ⊢
    exact this
  | some t =>
    simp only [h, reduceCtorEq, false_iff, Classical.not_not, Option.isSome_some, true_iff]
      at this ⊢
    exact this

/-- On `InOpenU W x`, the unchecked unsigned conversion returns `trunc x`. -/
theorem cvtU_eq_some_of_inOpenU {W : Nat} {x : FP f} (h : InOpenU W x) :
    cvtU W x = some (trunc x) := by
  have h2 := (trunc_mem_unsigned_range_iff W x h.1).2 h
  unfold cvtU
  simp [h.1, h2]

/-- On `InOpenS k x`, the unchecked signed conversion returns `trunc x`. -/
theorem cvtS_eq_some_of_inOpenS {k : Nat} {x : FP f} (h : InOpenS k x) :
    cvtS k x = some (trunc x) := by
  have h2 := (trunc_mem_signed_range_iff k x h.1).2 h
  unfold cvtS
  simp [h.1, h2]

/-! ### Range check -/

theorem key_fin (s : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) :
    key (FP.fin s E M) = (FP.fin s E M).uval := rfl

/-- **The two-comparison range check is exact.** For every format, width `W`
and value `x`, with `c = twoPowRound f W` (`2^W` rounded to the format, which
is `2^W` exactly when `TwoPowFits f W` and `+∞` otherwise), the guard
`x > -1.0 && x < c` holds iff the unchecked conversion `cvtU W x` is defined. -/
theorem rangeCheckU_twoPowRound_iff (W : Nat) (x : FP f) :
    rangeCheckU (twoPowRound f W) x = true ↔ (cvtU W x).isSome = true := by
  rw [cvtU_isSome_iff]
  unfold InOpenU
  have hq : (2 : Int) ^ f.qneg ≤ (f.maxUnits : Int) := by
    rw [int_two_pow]; exact Int.ofNat_le.2 (two_pow_qneg_le_maxUnits f)
  have hQ : (0 : Int) < 2 ^ f.qneg := by
    rw [int_two_pow]; have := Nat.two_pow_pos f.qneg; omega
  have hcast : ((2 ^ (W + f.qneg) : Nat) : Int) = (2 : Int) ^ W * 2 ^ f.qneg := by
    rw [Nat.pow_add]; simp
  have hneg1 : key (negOne f) = -((2 : Int) ^ f.qneg) := by rw [key_negOne, int_two_pow]
  have hnn : (negOne f).isNaN = false := rfl
  unfold rangeCheckU lt
  rw [hneg1, hnn]
  by_cases hfit : TwoPowFits f W
  · obtain ⟨hcf, hck⟩ := twoPowRound_of_fits hfit
    have hcn : (twoPowRound f W).isNaN = false := by
      revert hcf; cases twoPowRound f W <;> simp [FP.isFinite, FP.isNaN]
    have hfit' : (2 : Int) ^ W * 2 ^ f.qneg ≤ (f.maxUnits : Int) := by
      rw [← hcast]; exact Int.ofNat_le.2 hfit
    rw [hck, hcast, hcn]
    generalize (2 : Int) ^ W * 2 ^ f.qneg = PW at *
    generalize (2 : Int) ^ f.qneg = Q at *
    cases x with
    | nan => simp [FP.isNaN, FP.isFinite]
    | inf s =>
      cases s <;> simp only [FP.isNaN, FP.isFinite, key, sval, Bool.not_false, Bool.true_and,
        Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, false_and,
        iff_false, ite_true, ite_false] <;> push_cast <;> omega
    | fin s E M =>
      rw [key_fin]
      simp only [FP.isNaN, FP.isFinite, Bool.not_false, Bool.true_and, Bool.and_eq_true,
        decide_eq_true_eq, true_and]
  · have hnf : (f.maxUnits : Int) < (2 : Int) ^ W * 2 ^ f.qneg := by
      rw [← hcast]; exact Int.ofNat_lt.2 (Nat.lt_of_not_le hfit)
    rw [twoPowRound_of_not_fits hfit]
    generalize (2 : Int) ^ W * 2 ^ f.qneg = PW at *
    generalize (2 : Int) ^ f.qneg = Q at *
    cases x with
    | nan => simp [FP.isNaN, FP.isFinite]
    | inf s =>
      cases s <;> simp only [FP.isNaN, FP.isFinite, key, sval, Bool.not_false, Bool.true_and,
        Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, false_and,
        iff_false, ite_true, ite_false] <;> push_cast <;> omega
    | fin s E M =>
      have hu := Int.ofNat_le.2 (unitsOf_le_maxUnits f E.isLt M.isLt)
      have hb : (FP.fin s E M).uval ≤ f.maxUnits ∧ -(f.maxUnits : Int) ≤ (FP.fin s E M).uval := by
        simp only [FP.uval, FP.signBit, FP.units]
        cases s <;> simp only [sval, Bool.false_eq_true, ite_true, ite_false] <;> omega
      have hinf : key (FP.inf false : FP f) = (f.maxUnits : Int) + 1 := by
        simp [key, sval]
      rw [key_fin, hinf]
      simp only [FP.isNaN, FP.isFinite, Bool.not_false, Bool.true_and, Bool.and_eq_true,
        decide_eq_true_eq, true_and]
      omega

/-! ### Saturating conversion -/

/-- The clamping antecedents `x.uval ≤ -2^qneg` and `2^W * 2^qneg ≤ x.uval` imply
that `x` is finite, because `uval` is `0` on NaN and `±∞`. -/
theorem isFinite_of_uval_bounds (W : Nat) (x : FP f) :
    (x.uval ≤ -((2 : Int) ^ f.qneg) → x.isFinite = true) ∧
    ((2 : Int) ^ W * 2 ^ f.qneg ≤ x.uval → x.isFinite = true) := by
  have hQ : (0 : Int) < 2 ^ f.qneg := by
    rw [int_two_pow]; have := Nat.two_pow_pos f.qneg; omega
  have hW : (0 : Int) < 2 ^ W := by
    rw [int_two_pow]; have := Nat.two_pow_pos W; omega
  have hWQ : (0 : Int) < 2 ^ W * 2 ^ f.qneg := Int.mul_pos hW hQ
  constructor <;> intro h
  · cases hfin : x.isFinite
    · have hu := (trunc_uval_of_not_finite x hfin).2; omega
    · rfl
  · cases hfin : x.isFinite
    · have hu := (trunc_uval_of_not_finite x hfin).2; omega
    · rfl

/-- **Saturating unsigned conversion saturates and agrees with the unchecked
one.** For every format, width `W` and value `x`: `satU W x ∈ [0, 2^W - 1]`;
whenever `cvtU W x = some t`, `satU W x = t`; NaN gives `0`; `-∞` gives `0`;
`+∞` gives `2^W - 1`; `x ≤ -1` gives `0`; and `x ≥ 2^W` gives `2^W - 1` (the last
two antecedents hold for finite `x` only, `isFinite_of_uval_bounds`). -/
theorem satU_saturates_and_agrees (W : Nat) (x : FP f) :
    (0 ≤ satU W x ∧ satU W x ≤ 2 ^ W - 1) ∧
    (∀ t, cvtU W x = some t → satU W x = t) ∧
    (x = .nan → satU W x = 0) ∧
    (x = .inf true → satU W x = 0) ∧
    (x = .inf false → satU W x = 2 ^ W - 1) ∧
    (x.uval ≤ -((2 : Int) ^ f.qneg) → satU W x = 0) ∧
    ((2 : Int) ^ W * 2 ^ f.qneg ≤ x.uval → satU W x = 2 ^ W - 1) := by
  have hW : (1 : Int) ≤ 2 ^ W := by
    have := Nat.two_pow_pos W; rw [int_two_pow]; omega
  have hfinb := isFinite_of_uval_bounds W x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases x with
    | nan => simp [satU]; omega
    | inf s => cases s <;> simp [satU] <;> omega
    | fin s E M => simp only [satU]; omega
  · intro t ht
    unfold cvtU at ht
    split at ht
    · rename_i h
      simp only [Option.some.injEq] at ht
      subst ht
      cases x with
      | nan => simp [FP.isFinite] at h
      | inf s => simp [FP.isFinite] at h
      | fin s E M => simp only [satU]; omega
    · simp at ht
  · intro h; subst h; rfl
  · intro h; subst h; rfl
  · intro h; subst h; rfl
  · intro hle
    have hx := hfinb.1 hle
    cases x with
    | nan => simp [FP.isFinite] at hx
    | inf s => simp [FP.isFinite] at hx
    | fin s E M =>
      have hlt : ¬ (-((2 : Int) ^ f.qneg) < (FP.fin s E M).uval) := by omega
      have := (not_congr (trunc_mem_unsigned_range_iff W (.fin s E M) hx)).2
        (fun h => hlt h.2.1)
      have hle' : trunc (FP.fin s E M) ≤ 2 ^ W - 1 := by
        unfold trunc; simp only [FP.signBit, FP.units, FP.uval] at hle ⊢
        cases s
        · simp only [sval, Bool.false_eq_true, ite_false] at hle ⊢
          have : 0 ≤ ((unitsOf f E.val M.val : Nat) : Int) := Int.natCast_nonneg _
          have : (0 : Int) < 2 ^ f.qneg := by
            rw [int_two_pow]; have := Nat.two_pow_pos f.qneg; omega
          omega
        · simp only [sval, ite_true]
          have : (0 : Int) ≤ ((unitsOf f E.val M.val / 2 ^ f.qneg : Nat) : Int) :=
            Int.natCast_nonneg _
          omega
      simp only [satU]; omega
  · intro hge
    have hx := hfinb.2 hge
    cases x with
    | nan => simp [FP.isFinite] at hx
    | inf s => simp [FP.isFinite] at hx
    | fin s E M =>
      have hlt : ¬ ((FP.fin s E M).uval < (2 : Int) ^ W * 2 ^ f.qneg) := by omega
      have := (not_congr (trunc_mem_unsigned_range_iff W (.fin s E M) hx)).2
        (fun h => hlt h.2.2)
      have hge' : 0 ≤ trunc (FP.fin s E M) := by
        unfold trunc; simp only [FP.signBit, FP.units, FP.uval] at hge ⊢
        cases s
        · simp only [sval, Bool.false_eq_true, ite_false]; exact Int.natCast_nonneg _
        · simp only [sval, ite_true] at hge
          have : 0 ≤ ((unitsOf f E.val M.val : Nat) : Int) := Int.natCast_nonneg _
          have : (0 : Int) < 2 ^ W * 2 ^ f.qneg := by
            rw [int_two_pow, int_two_pow]; have := Nat.two_pow_pos f.qneg
            have := Nat.two_pow_pos W
            exact Int.mul_pos (by omega) (by omega)
          omega
      simp only [satU]; omega

/-- **Saturating signed conversion saturates and agrees with the unchecked
one.** For every format, every `k` (signed width `k + 1`) and value `x`:
`satS k x ∈ [-2^k, 2^k - 1]`; whenever `cvtS k x = some t`, `satS k x = t`; NaN
gives `0`; `-∞` gives `-2^k`; `+∞` gives `2^k - 1`; `x ≤ -2^k - 1` gives `-2^k`;
and `x ≥ 2^k` gives `2^k - 1`. -/
theorem satS_saturates_and_agrees (k : Nat) (x : FP f) :
    (-(2 ^ k) ≤ satS k x ∧ satS k x ≤ 2 ^ k - 1) ∧
    (∀ t, cvtS k x = some t → satS k x = t) ∧
    (x = .nan → satS k x = 0) ∧
    (x = .inf true → satS k x = -(2 ^ k)) ∧
    (x = .inf false → satS k x = 2 ^ k - 1) ∧
    (x.uval ≤ -(((2 : Int) ^ k + 1) * 2 ^ f.qneg) → satS k x = -(2 ^ k)) ∧
    ((2 : Int) ^ k * 2 ^ f.qneg ≤ x.uval → satS k x = 2 ^ k - 1) := by
  have hK : (1 : Int) ≤ 2 ^ k := by
    have := Nat.two_pow_pos k; rw [int_two_pow]; omega
  have hQ : (0 : Int) < 2 ^ f.qneg := by
    rw [int_two_pow]; have := Nat.two_pow_pos f.qneg; omega
  have hPos : (0 : Int) < (2 : Int) ^ k * 2 ^ f.qneg := Int.mul_pos (by omega) hQ
  have hNeg : (0 : Int) < ((2 : Int) ^ k + 1) * 2 ^ f.qneg := Int.mul_pos (by omega) hQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases x with
    | nan => simp [satS]; omega
    | inf s => cases s <;> simp [satS] <;> omega
    | fin s E M => simp only [satS]; omega
  · intro t ht
    unfold cvtS at ht
    split at ht
    · rename_i h
      simp only [Option.some.injEq] at ht
      subst ht
      cases x with
      | nan => simp [FP.isFinite] at h
      | inf s => simp [FP.isFinite] at h
      | fin s E M => simp only [satS]; omega
    · simp at ht
  · intro h; subst h; rfl
  · intro h; subst h; rfl
  · intro h; subst h; rfl
  · intro hle
    cases x with
    | nan => have hu := (trunc_uval_of_not_finite (FP.nan : FP f) rfl).2; omega
    | inf s => have hu := (trunc_uval_of_not_finite (FP.inf s : FP f) rfl).2; omega
    | fin s E M =>
      have hx : (FP.fin s E M).isFinite = true := rfl
      have hnot : ¬ InOpenS k (.fin s E M) := fun ho => by
        obtain ⟨_, h1, _⟩ := ho; omega
      have htr := (not_congr (trunc_mem_signed_range_iff k (.fin s E M) hx)).2 hnot
      have hle' : trunc (FP.fin s E M) ≤ 2 ^ k - 1 := by
        unfold trunc; simp only [FP.signBit, FP.units, FP.uval] at hle ⊢
        cases s
        · simp only [sval, Bool.false_eq_true, ite_false] at hle
          have : 0 ≤ ((unitsOf f E.val M.val : Nat) : Int) := Int.natCast_nonneg _
          omega
        · simp only [sval, ite_true]
          have : (0 : Int) ≤ ((unitsOf f E.val M.val / 2 ^ f.qneg : Nat) : Int) :=
            Int.natCast_nonneg _
          omega
      simp only [satS]; omega
  · intro hge
    cases x with
    | nan => have hu := (trunc_uval_of_not_finite (FP.nan : FP f) rfl).2; omega
    | inf s => have hu := (trunc_uval_of_not_finite (FP.inf s : FP f) rfl).2; omega
    | fin s E M =>
      have hx : (FP.fin s E M).isFinite = true := rfl
      have hnot : ¬ InOpenS k (.fin s E M) := fun ho => by
        obtain ⟨_, _, h2⟩ := ho; omega
      have htr := (not_congr (trunc_mem_signed_range_iff k (.fin s E M) hx)).2 hnot
      have hge' : -(2 ^ k) ≤ trunc (FP.fin s E M) := by
        unfold trunc; simp only [FP.signBit, FP.units, FP.uval] at hge ⊢
        cases s
        · simp only [sval, Bool.false_eq_true, ite_false]
          have : (0 : Int) ≤ ((unitsOf f E.val M.val / 2 ^ f.qneg : Nat) : Int) :=
            Int.natCast_nonneg _
          omega
        · simp only [sval, ite_true] at hge
          have : 0 ≤ ((unitsOf f E.val M.val : Nat) : Int) := Int.natCast_nonneg _
          omega
      simp only [satS]; omega

/-- **The saturation conjuncts characterize `satU`.** For every format, width
`W` and function `g : FP f → Int`: `g` satisfies, at every input, the seven
conjuncts of `satU_saturates_and_agrees` (with `g` in place of `satU W`) iff
`g` is `satU W`. -/
theorem satU_spec_iff (W : Nat) (g : FP f → Int) :
    (∀ x : FP f, (0 ≤ g x ∧ g x ≤ 2 ^ W - 1) ∧
      (∀ t, cvtU W x = some t → g x = t) ∧
      (x = .nan → g x = 0) ∧
      (x = .inf true → g x = 0) ∧
      (x = .inf false → g x = 2 ^ W - 1) ∧
      (x.uval ≤ -((2 : Int) ^ f.qneg) → g x = 0) ∧
      ((2 : Int) ^ W * 2 ^ f.qneg ≤ x.uval → g x = 2 ^ W - 1)) ↔
    ∀ x, g x = satU W x := by
  constructor
  · intro hg x
    obtain ⟨_, hagree, hnan, hninf, hpinf, hlo, hhi⟩ := hg x
    have hs := satU_saturates_and_agrees W x
    cases x with
    | nan => rw [hnan rfl, hs.2.2.1 rfl]
    | inf s =>
      cases s
      · rw [hpinf rfl, hs.2.2.2.2.1 rfl]
      · rw [hninf rfl, hs.2.2.2.1 rfl]
    | fin s E M =>
      by_cases hin : InOpenU W (FP.fin s E M)
      · have hc := cvtU_eq_some_of_inOpenU hin
        rw [hagree _ hc, hs.2.1 _ hc]
      · have hx : (FP.fin s E M).isFinite = true := rfl
        have hor : (FP.fin s E M).uval ≤ -((2 : Int) ^ f.qneg) ∨
            (2 : Int) ^ W * 2 ^ f.qneg ≤ (FP.fin s E M).uval := by
          by_cases h1 : (FP.fin s E M).uval ≤ -((2 : Int) ^ f.qneg)
          · exact Or.inl h1
          · right
            refine Classical.byContradiction fun h2 => hin ⟨hx, ?_, ?_⟩ <;> omega
        rcases hor with h | h
        · rw [hlo h, hs.2.2.2.2.2.1 h]
        · rw [hhi h, hs.2.2.2.2.2.2 h]
  · intro hg x
    simp only [hg]
    exact satU_saturates_and_agrees W x

/-- **The saturation conjuncts characterize `satS`.** For every format, every
`k` (signed width `k + 1`) and function `g : FP f → Int`: `g` satisfies, at every
input, the seven conjuncts of `satS_saturates_and_agrees` (with `g` in place of
`satS k`) iff `g` is `satS k`. -/
theorem satS_spec_iff (k : Nat) (g : FP f → Int) :
    (∀ x : FP f, (-(2 ^ k) ≤ g x ∧ g x ≤ 2 ^ k - 1) ∧
      (∀ t, cvtS k x = some t → g x = t) ∧
      (x = .nan → g x = 0) ∧
      (x = .inf true → g x = -(2 ^ k)) ∧
      (x = .inf false → g x = 2 ^ k - 1) ∧
      (x.uval ≤ -(((2 : Int) ^ k + 1) * 2 ^ f.qneg) → g x = -(2 ^ k)) ∧
      ((2 : Int) ^ k * 2 ^ f.qneg ≤ x.uval → g x = 2 ^ k - 1)) ↔
    ∀ x, g x = satS k x := by
  constructor
  · intro hg x
    obtain ⟨_, hagree, hnan, hninf, hpinf, hlo, hhi⟩ := hg x
    have hs := satS_saturates_and_agrees k x
    cases x with
    | nan => rw [hnan rfl, hs.2.2.1 rfl]
    | inf s =>
      cases s
      · rw [hpinf rfl, hs.2.2.2.2.1 rfl]
      · rw [hninf rfl, hs.2.2.2.1 rfl]
    | fin s E M =>
      by_cases hin : InOpenS k (FP.fin s E M)
      · have hc := cvtS_eq_some_of_inOpenS hin
        rw [hagree _ hc, hs.2.1 _ hc]
      · have hx : (FP.fin s E M).isFinite = true := rfl
        have hor : (FP.fin s E M).uval ≤ -(((2 : Int) ^ k + 1) * 2 ^ f.qneg) ∨
            (2 : Int) ^ k * 2 ^ f.qneg ≤ (FP.fin s E M).uval := by
          by_cases h1 : (FP.fin s E M).uval ≤ -(((2 : Int) ^ k + 1) * 2 ^ f.qneg)
          · exact Or.inl h1
          · right
            refine Classical.byContradiction fun h2 => hin ⟨hx, ?_, ?_⟩ <;> omega
        rcases hor with h | h
        · rw [hlo h, hs.2.2.2.2.2.1 h]
        · rw [hhi h, hs.2.2.2.2.2.2 h]
  · intro hg x
    simp only [hg]
    exact satS_saturates_and_agrees k x

end Toy.FloatTier
