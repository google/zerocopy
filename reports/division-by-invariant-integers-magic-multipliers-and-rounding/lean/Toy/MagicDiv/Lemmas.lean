/-
Toy.MagicDiv.Lemmas
===================

Supporting lemmas used by the proofs in `Toy.MagicDiv.Statements`: facts
about `clog2`, ceiling division, floor-division uniqueness, the signed range,
and the arithmetic shift on integers.
-/
import Toy.MagicDiv.Defs

namespace Toy.MagicDiv

/-! ### Unsigned helpers -/

/-- The lower bound `2^K ≤ m * d` already forces `d ≠ 0`; therefore no
separate nonzero-divisor hypothesis is needed next to it. -/
theorem pos_of_two_pow_le_mul {K m d : Nat} (h : 2 ^ K ≤ m * d) : 0 < d := by
  refine Nat.pos_of_ne_zero ?_
  rintro rfl
  rw [Nat.mul_zero] at h
  exact absurd h (Nat.not_le.mpr (Nat.two_pow_pos K))

/-- The ceiling multiplier satisfies the lower bound: `a ≤ ⌈a/d⌉ * d` for `d ≥ 1`. -/
theorem le_ceilDiv_mul (a d : Nat) (hd : 0 < d) : a ≤ ceilDiv a d * d := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (a + d - 1) d
  have h2 := Nat.mod_lt (a + d - 1) hd
  rw [Nat.mul_comm] at h1
  generalize (a + d - 1) / d * d = P at h1 ⊢
  generalize (a + d - 1) % d = r at h1 h2
  omega

/-- The ceiling multiplier overshoots by less than `d`: `⌈a/d⌉ * d < a + d`. -/
theorem ceilDiv_mul_lt (a d : Nat) (hd : 0 < d) : ceilDiv a d * d < a + d := by
  unfold ceilDiv
  have h1 := Nat.div_mul_le_self (a + d - 1) d
  omega

/-- `ceilDiv a d` is the least multiplier `c` with `a ≤ c * d`. -/
theorem ceilDiv_le_of_le_mul {a d c : Nat} (hd : 0 < d) (h : a ≤ c * d) : ceilDiv a d ≤ c := by
  unfold ceilDiv
  have : (a + d - 1) / d < c + 1 := by
    rw [Nat.div_lt_iff_lt_mul hd, Nat.add_mul, Nat.one_mul]
    omega
  omega

theorem le_two_pow_clog2 {d : Nat} (hd : 0 < d) : d ≤ 2 ^ clog2 d := by
  by_cases h1 : d ≤ 1
  · have : d = 1 := by omega
    subst this; simp [clog2]
  · unfold clog2
    simp only [h1, ↓reduceIte]
    have hlt : d - 1 < 2 ^ ((d - 1).log2 + 1) := Nat.lt_log2_self
    omega

theorem two_pow_pred_clog2_lt {d : Nat} (hd : 2 ≤ d) : 2 ^ (clog2 d - 1) < d := by
  unfold clog2
  have hle : ¬ d ≤ 1 := by omega
  simp only [hle, ↓reduceIte, Nat.add_sub_cancel]
  have hd1 : d - 1 ≠ 0 := by omega
  have hlog := Nat.log2_self_le hd1
  omega

theorem one_le_clog2 {d : Nat} (hd : 2 ≤ d) : 1 ≤ clog2 d := by
  unfold clog2
  have hnot : ¬ d ≤ 1 := by omega
  simp [hnot]

theorem clog2_le_of_le_two_pow {d N : Nat} (hd : d ≤ 2 ^ N) : clog2 d ≤ N := by
  by_cases h1 : d ≤ 1
  · simp [clog2, h1]
  · unfold clog2
    simp only [h1, ↓reduceIte]
    have hd1 : d - 1 ≠ 0 := by omega
    have : (d - 1).log2 < N := (Nat.log2_lt hd1).mpr (by omega)
    omega

theorem succ_le_clog2_of_two_pow_lt {N d : Nat} (hdN : 2 ^ N < d) : N + 1 ≤ clog2 d := by
  have hd2 : 2 ≤ d := by have := Nat.two_pow_pos N; omega
  unfold clog2
  have hle : ¬ d ≤ 1 := by omega
  simp only [hle, ↓reduceIte]
  suffices h : N ≤ (d - 1).log2 by omega
  rw [Nat.le_log2 (by omega)]
  omega

theorem clog2_two_pow (k : Nat) : clog2 (2 ^ k) = k := by
  apply Nat.le_antisymm (clog2_le_of_le_two_pow (Nat.le_refl _))
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    have := succ_le_clog2_of_two_pow_lt (N := k) (d := 2 ^ (k + 1))
      (Nat.pow_lt_pow_right (by decide) (by omega))
    exact this

/-- Floor quotient by a positive divisor via a two-sided bound. -/
theorem div_eq_of_bounds {a b q : Nat} (h1 : q * b ≤ a) (h2 : a < (q + 1) * b) : a / b = q :=
  Nat.div_eq_of_lt_le h1 h2

/-- `x < (x / d + 1) * d` for `d ≥ 1`. -/
theorem lt_succ_div_mul (x d : Nat) (hd : 0 < d) : x < (x / d + 1) * d := by
  have h1 := Nat.div_add_mod x d
  have h2 := Nat.mod_lt x hd
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  omega

/-- Monotonicity of the multiply-shift in the multiplier. -/
theorem mulShift_mono {x m m' s : Nat} (h : m ≤ m') : (x * m) >>> s ≤ (x * m') >>> s := by
  simp only [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_div_right (Nat.mul_le_mul_left x h)

/-! ### Signed helpers -/

theorem signedRange_iff_of_pos {N : Nat} (hN : 1 ≤ N) (x : Int) :
    SignedRange N x ↔ -(2 : Int) ^ (N - 1) ≤ x ∧ x < (2 : Int) ^ (N - 1) := by
  have h : (2 : Int) ^ N = 2 * 2 ^ (N - 1) := by
    rw [show N = (N - 1) + 1 by omega, Int.pow_succ]
    simp only [Nat.add_sub_cancel]
    exact Int.mul_comm _ _
  unfold SignedRange
  rw [h]
  omega

theorem signedRange_zero_iff (x : Int) : SignedRange 0 x ↔ x = 0 := by
  unfold SignedRange
  simp only [Int.pow_zero]
  omega

/-! ### Integer helpers -/

theorem intCast_two_pow (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by
  rw [Int.natCast_pow]; rfl

/-- Floor quotient of a negated natural number. -/
theorem neg_ediv_of_bounds {A B Q : Nat} (hB : 0 < B) (h1 : Q * B < A) (h2 : A ≤ (Q + 1) * B) :
    (-(A : Int)) / (B : Int) = -(Q : Int) - 1 := by
  have hB' : (0 : Int) < B := by omega
  rw [Int.ediv_eq_iff_of_pos hB']
  have c1 : ((Q * B : Nat) : Int) < (A : Int) := by omega
  have c2 : (A : Int) ≤ (((Q + 1) * B : Nat) : Int) := by omega
  rw [Int.natCast_mul] at c1
  rw [Int.natCast_mul, Int.natCast_add, Int.add_mul] at c2
  rw [Int.sub_mul, Int.neg_mul, Int.one_mul]
  simp only [Int.natCast_one, Int.one_mul] at c2
  omega

/-- Floor division of a nonnegative integer by a positive power of two: the
arithmetic shift of a natural number. -/
theorem natCast_mul_shiftRight (a b k : Nat) :
    ((a : Int) * (b : Int)) >>> k = (((a * b) / 2 ^ k : Nat) : Int) := by
  rw [Int.shiftRight_eq_div_pow, ← Int.natCast_mul, Int.ofNat_ediv_ofNat]

/-- The arithmetic shift of a signed `N`-bit value by `N - 1` is its sign mask. -/
theorem shiftRight_pred_of_signedRange {N : Nat} (hN : 1 ≤ N) {x : Int} (hx : SignedRange N x) :
    x >>> (N - 1) = if x < 0 then -1 else 0 := by
  rw [signedRange_iff_of_pos hN] at hx
  rw [Int.shiftRight_eq_div_pow, intCast_two_pow]
  have hP : (0 : Int) < 2 ^ (N - 1) := Int.pow_pos (by decide)
  split
  · rw [Int.ediv_eq_iff_of_pos hP]; omega
  · rw [Int.ediv_eq_iff_of_pos hP]; omega

/-- The logical shift of the all-ones `N`-bit pattern by `N - k` is `2^k - 1`
(for `k ≤ N`; at `k = 0` the shift count is `N` and the result is `0`). -/
theorem lsrN_neg_one {N k : Nat} (hk : k ≤ N) : lsrN N (-1) (N - k) = (2 : Int) ^ k - 1 := by
  unfold lsrN
  have hP : (0 : Int) < 2 ^ N := Int.pow_pos (by decide)
  have hmod : (-1 : Int) % 2 ^ N = 2 ^ N - 1 := by
    rw [Int.emod_def]
    have : (-1 : Int) / 2 ^ N = -1 := by rw [Int.ediv_eq_iff_of_pos hP]; omega
    rw [this]; omega
  rw [hmod, ← intCast_two_pow, ← intCast_two_pow]
  have h1 : ((2 ^ N : Nat) : Int) - 1 = ((2 ^ N - 1 : Nat) : Int) := by
    have := Nat.two_pow_pos N; omega
  rw [h1, Int.toNat_natCast, Nat.shiftRight_eq_div_pow]
  have hsplit : 2 ^ N = 2 ^ (N - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hdiv : (2 ^ N - 1) / 2 ^ (N - k) = 2 ^ k - 1 := by
    have hA := Nat.two_pow_pos (N - k)
    have hB := Nat.two_pow_pos k
    apply div_eq_of_bounds
    · rw [hsplit, Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
      have : 2 ^ (N - k) ≤ 2 ^ (N - k) * 2 ^ k := Nat.le_mul_of_pos_right _ hB
      omega
    · rw [Nat.sub_add_cancel hB, hsplit, Nat.mul_comm (2 ^ k)]
      have := Nat.mul_pos hA hB
      omega
  rw [hdiv]
  have := Nat.two_pow_pos k
  omega

theorem lsrN_zero (N s : Nat) : lsrN N 0 s = 0 := by
  simp [lsrN]



/-- Definition adequacy of `SignedRange`: `x` is in the signed `N`-bit range
exactly when it is the signed value of the `N`-bit two's-complement bit vector
`BitVec.ofInt N x`. -/
theorem signedRange_iff_toInt_ofInt (N : Nat) (x : Int) :
    SignedRange N x ↔ (BitVec.ofInt N x).toInt = x := by
  rw [BitVec.toInt_ofInt]
  have hM : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by rw [Int.natCast_pow]; rfl
  have hpos : 0 < 2 ^ N := Nat.two_pow_pos N
  unfold SignedRange
  constructor
  · rintro ⟨h1, h2⟩
    apply Int.bmod_eq_of_le_mul_two <;> omega
  · intro h
    have l := Int.le_bmod (x := x) hpos
    have u := Int.bmod_lt (x := x) hpos
    rw [h] at l u
    omega

end Toy.MagicDiv
