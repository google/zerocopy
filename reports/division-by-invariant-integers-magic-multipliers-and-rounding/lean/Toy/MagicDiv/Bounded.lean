/-
Toy.MagicDiv.Bounded
====================

Fully proved bounded results, established by kernel evaluation of Boolean
checkers (`decide +kernel`, no native code) together with small general
lemmas that reduce an unbounded quantifier (over all multipliers `m`, or all
shifts `s`) to finitely many evaluated cases.

* `mulShiftCorrect_iff_exactCriterion_u8`: the exact criterion for `N = 8`,
  every `1 ≤ d ≤ 255`, every `s ≤ 16`, and every multiplier `m`.
* `fixupQuot_unsignedMagic_u8`, `fixupQuot_unsignedMagic_u16_div7`: the
  add-and-shift fixup with the textbook multiplier, exhaustively.
* `no_single_word_multiplier_u8_div7`: no 8-bit multiplier with any shift
  divides 8-bit inputs by 7.
* `biasDivBV_u8`, `biasDivBVMasked_u8`: the bias-and-shift sequence on core
  `BitVec 8`, with total shifts and with shift counts reduced modulo 8.
* `robison_multiply_add_u8_div7`, `mulShift_u8_div7_below_209`: escape hatches
  for `no_single_word_multiplier_u8_div7`.
* `count_no_single_word_u8`, `count_single_word_u8`,
  `count_single_word_u8_directRem_fails`: counts over all 8-bit divisors.
-/
import Toy.MagicDiv.Statements

namespace Toy.MagicDiv

/-! ### Boolean bounded quantifier -/

/-- Boolean bounded universal quantifier `∀ x < n, f x`, by primitive recursion
(kernel-reducible). -/
def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec true (fun i acc => f i && acc) n

theorem allBelow_iff (n : Nat) (f : Nat → Bool) :
    allBelow n f = true ↔ ∀ x, x < n → f x = true := by
  induction n with
  | zero => exact iff_of_true rfl (fun x hx => absurd hx (Nat.not_lt_zero x))
  | succ n ih =>
    show (f n && allBelow n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h | h
      · exact h2 x h
      · subst h; exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun x hx => h x (Nat.lt_succ_of_lt hx)⟩

/-- Boolean version of `MulShiftCorrect`. -/
def correctB (N d m s : Nat) : Bool :=
  allBelow (2 ^ N) (fun x => (x * m) >>> s == x / d)

theorem correctB_iff (N d m s : Nat) : correctB N d m s = true ↔ MulShiftCorrect N d m s := by
  unfold correctB MulShiftCorrect
  rw [allBelow_iff]
  simp only [beq_iff_eq]

/-! ### General reduction lemmas (proved) -/

/-- Correctness is convex in the multiplier: if `m₁ ≤ m ≤ m₂` and both `m₁` and
`m₂` are correct at shift `s`, so is `m`. -/
theorem mulShiftCorrect_of_between {N d m₁ m₂ m s : Nat}
    (h₁ : MulShiftCorrect N d m₁ s) (h₂ : MulShiftCorrect N d m₂ s)
    (hm₁ : m₁ ≤ m) (hm₂ : m ≤ m₂) : MulShiftCorrect N d m s := by
  intro x hx
  have a := h₁ x hx
  have b := h₂ x hx
  have l : (x * m₁) >>> s ≤ (x * m) >>> s := by
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left x hm₁)
  have u : (x * m) >>> s ≤ (x * m₂) >>> s := by
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left x hm₂)
  omega

/-- A multiplier with `m * d < 2^s` is wrong at the input `x = d` (for
`1 ≤ d < 2^N`). -/
theorem not_mulShiftCorrect_of_mul_lt {N d m s : Nat} (hd : 0 < d) (hdN : d < 2 ^ N)
    (h : m * d < 2 ^ s) : ¬ MulShiftCorrect N d m s := by
  intro hc
  have e := hc d hdN
  rw [Nat.shiftRight_eq_div_pow, Nat.div_self hd, Nat.mul_comm,
    Nat.div_eq_of_lt h] at e
  exact absurd e (by decide)

/-- If the multiply-shift by `m` overshoots at some input `x < 2^N`, every
larger multiplier is wrong too. -/
theorem not_mulShiftCorrect_of_gt_at {N d m m' s x : Nat} (hx : x < 2 ^ N)
    (h : x / d < (x * m) >>> s) (hm : m ≤ m') : ¬ MulShiftCorrect N d m' s := by
  intro hc
  have e := hc x hx
  have : (x * m) >>> s ≤ (x * m') >>> s := by
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left x hm)
  omega

/-- The exact criterion is convex in the multiplier. -/
theorem exactCriterion_of_between {N d m₁ m₂ m s : Nat}
    (h₁ : ExactCriterion N d m₁ s) (h₂ : ExactCriterion N d m₂ s)
    (hm₁ : m₁ ≤ m) (hm₂ : m ≤ m₂) : ExactCriterion N d m s := by
  obtain ⟨l1, _⟩ := h₁
  obtain ⟨_, u2⟩ := h₂
  refine ⟨Nat.le_trans l1 (Nat.mul_le_mul_right d hm₁), ?_⟩
  exact Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.mul_le_mul_right d hm₂) _)) u2

/-- The upper half of the exact criterion fails for every multiplier above one
where it fails. -/
theorem not_exactCriterion_of_upper {N d M m s : Nat}
    (h : 2 ^ s ≤ lastFullBlockEnd N d * (M * d - 2 ^ s)) (hm : M ≤ m) :
    ¬ ExactCriterion N d m s := by
  rintro ⟨_, u⟩
  have := Nat.mul_le_mul_left (lastFullBlockEnd N d)
    (Nat.sub_le_sub_right (Nat.mul_le_mul_right d hm) (2 ^ s))
  omega

theorem not_exactCriterion_of_mul_lt {N d m s : Nat} (h : m * d < 2 ^ s) :
    ¬ ExactCriterion N d m s :=
  fun ⟨l, _⟩ => absurd l (Nat.not_le.mpr h)

theorem lastFullBlockEnd_lt (N d : Nat) : lastFullBlockEnd N d < 2 ^ N := by
  unfold lastFullBlockEnd
  have := Nat.two_pow_pos N
  omega

/-! ### Exact criterion for `N = 8` (bounded check) -/

/-- Boundary data for one `(N, d, s)`: `lo = ⌈2^s/d⌉`,
`hi = (2^s + (2^s - 1)/nc)/d`, `M = max lo (hi + 1)`. The check asserts:
(i) if `lo ≤ hi`, then `lo` and `hi` are both correct and both satisfy the
criterion; (ii) `lo - 1` (if any) violates the lower bound; (iii) `M`
overshoots at the input `nc` and violates the upper half of the criterion. -/
def boundaryCheck (N d s : Nat) : Bool :=
  let lo := ceilDiv (2 ^ s) d
  let nc := lastFullBlockEnd N d
  let hi := (2 ^ s + (2 ^ s - 1) / nc) / d
  let M := max lo (hi + 1)
  (!decide (lo ≤ hi) || (correctB N d lo s && correctB N d hi s &&
      decide (ExactCriterion N d lo s) && decide (ExactCriterion N d hi s))) &&
  (decide (lo = 0) || decide ((lo - 1) * d < 2 ^ s)) &&
  decide (nc / d < (nc * M) >>> s) &&
  decide (2 ^ s ≤ nc * (M * d - 2 ^ s))

theorem boundaryCheck_sound {N d s : Nat} (hd : 0 < d) (hdN : d < 2 ^ N)
    (h : boundaryCheck N d s = true) (m : Nat) :
    MulShiftCorrect N d m s ↔ ExactCriterion N d m s := by
  have hncN := lastFullBlockEnd_lt N d
  unfold boundaryCheck at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, correctB_iff] at h
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := h
  generalize ceilDiv (2 ^ s) d = lo at hA hB hC hD
  generalize (2 ^ s + (2 ^ s - 1) / lastFullBlockEnd N d) / d = hi at hA hB hC hD
  by_cases h1 : m < lo
  · have hm : m * d < 2 ^ s := by
      rcases hB with h0 | hB
      · omega
      · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right d (by omega : m ≤ lo - 1)) hB
    exact iff_of_false (not_mulShiftCorrect_of_mul_lt hd hdN hm)
      (not_exactCriterion_of_mul_lt hm)
  · by_cases h2 : m ≤ hi
    · rcases hA with hA | ⟨⟨⟨c1, c2⟩, e1⟩, e2⟩
      · exact absurd (by omega : lo ≤ hi) hA
      · exact iff_of_true (mulShiftCorrect_of_between c1 c2 (by omega) h2)
          (exactCriterion_of_between e1 e2 (by omega) h2)
    · have hM : max lo (hi + 1) ≤ m := Nat.max_le.mpr ⟨by omega, by omega⟩
      exact iff_of_false (not_mulShiftCorrect_of_gt_at hncN hC hM)
        (not_exactCriterion_of_upper hD hM)

/-- All boundary checks for `N = 8`, `d = 1, …, 255`, `s = 0, …, 16`. -/
def checkAll8 : Bool :=
  allBelow 255 (fun i => allBelow 17 (fun s => boundaryCheck 8 (i + 1) s))

theorem checkAll8_eq_true : checkAll8 = true := by decide +kernel

/-- **Exact criterion, bounded check (`N = 8`).** For every divisor
`1 ≤ d ≤ 255`, every shift `s ≤ 16`, and every multiplier `m` (unbounded),
`MulShiftCorrect 8 d m s ↔ ExactCriterion 8 d m s`. -/
theorem mulShiftCorrect_iff_exactCriterion_u8 :
    ∀ d, 0 < d → d < 2 ^ 8 → ∀ s, s ≤ 16 → ∀ m,
      MulShiftCorrect 8 d m s ↔ ExactCriterion 8 d m s := by
  intro d hd hdN s hs m
  have h := checkAll8_eq_true
  unfold checkAll8 at h
  rw [allBelow_iff] at h
  have hdN' : d < 256 := hdN
  have h2 := h (d - 1) (by omega)
  rw [allBelow_iff] at h2
  have h3 := h2 s (by omega)
  rw [show d - 1 + 1 = d by omega] at h3
  exact boundaryCheck_sound hd hdN h3 m

/-! ### Fixup sequence (bounded checks) -/

/-- Boolean check that the fixup with the textbook multiplier is correct for
all `x < 2^N`. -/
def fixupCheck (N d : Nat) : Bool :=
  allBelow (2 ^ N) (fun x => fixupQuot N (unsignedMagic N d - 2 ^ N) (clog2 d) x == x / d)

theorem fixupCheck_u8 : allBelow 254 (fun i => fixupCheck 8 (i + 2)) = true := by
  decide +kernel

theorem fixupCheck_u16_div7 : fixupCheck 16 7 = true := by decide +kernel

/-- **Fixup, bounded check (`N = 8`).** For every `2 ≤ d ≤ 255` and every
`x < 256`, the fixup with `m' = unsignedMagic 8 d - 2^8` and `ℓ = clog2 d`
computes `x / d`. -/
theorem fixupQuot_unsignedMagic_u8 :
    ∀ d, 2 ≤ d → d < 2 ^ 8 → ∀ x, x < 2 ^ 8 →
      fixupQuot 8 (unsignedMagic 8 d - 2 ^ 8) (clog2 d) x = x / d := by
  intro d hd hdN x hx
  have h := fixupCheck_u8
  rw [allBelow_iff] at h
  have hdN' : d < 256 := hdN
  have h2 := h (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at h2
  unfold fixupCheck at h2
  rw [allBelow_iff] at h2
  simpa using h2 x hx

/-- **Fixup, bounded check (`N = 16`, `d = 7`).** For every `x < 2^16`, the
fixup with `m' = unsignedMagic 16 7 - 2^16` and `ℓ = clog2 7 = 3` computes
`x / 7`. -/
theorem fixupQuot_unsignedMagic_u16_div7 :
    ∀ x, x < 2 ^ 16 → fixupQuot 16 (unsignedMagic 16 7 - 2 ^ 16) (clog2 7) x = x / 7 := by
  intro x hx
  have h := fixupCheck_u16_div7
  unfold fixupCheck at h
  rw [allBelow_iff] at h
  simpa using h x hx

/-! ### No single-word multiplier for 8-bit division by 7 -/

/-- **No 8-bit multiplier divides 8-bit inputs by 7.** For every `m < 2^8` and
every shift `s` (unbounded), `MulShiftCorrect 8 7 m s` fails. -/
theorem no_single_word_multiplier_u8_div7 :
    ∀ m, m < 2 ^ 8 → ∀ s, ¬ MulShiftCorrect 8 7 m s := by
  intro m hm s hc
  have hm' : m < 256 := hm
  by_cases hs : 16 ≤ s
  · have h16 : m * 7 < 2 ^ 16 := by
      have : (2 : Nat) ^ 16 = 65536 := by decide
      omega
    exact not_mulShiftCorrect_of_mul_lt (by decide) (by decide)
      (Nat.lt_of_lt_of_le h16 (Nat.pow_le_pow_right (by decide) hs)) hc
  · have hw : allBelow 256 (fun m => allBelow 16 (fun s =>
        ((7 * m) >>> s != 1) || ((251 * m) >>> s != 35))) = true := by decide +kernel
    rw [allBelow_iff] at hw
    have h1 := hw m hm'
    rw [allBelow_iff] at h1
    have h2 := h1 s (by omega)
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h2
    rcases h2 with h2 | h2
    · exact h2 (by simpa using hc 7 (by decide))
    · exact h2 (by simpa using hc 251 (by decide))

/-- **Minimal shift for 8-bit division by 7 is 11.** No multiplier works at
shift 10 or below, and `(m, s) = (293, 11)` works. -/
theorem minimal_shift_u8_div7 :
    (∀ s, s ≤ 10 → ∀ m, ¬ MulShiftCorrect 8 7 m s) ∧ MulShiftCorrect 8 7 293 11 := by
  refine ⟨?_, by decide +kernel⟩
  intro s hs m
  have hw : allBelow 11 (fun s =>
      decide ((ceilDiv (2 ^ s) 7 - 1) * 7 < 2 ^ s) &&
      decide (251 / 7 < (251 * ceilDiv (2 ^ s) 7) >>> s)) = true := by decide +kernel
  rw [allBelow_iff] at hw
  have h := hw s (by omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlo, hhi⟩ := h
  by_cases hm : ceilDiv (2 ^ s) 7 ≤ m
  · exact not_mulShiftCorrect_of_gt_at (by decide) hhi hm
  · exact not_mulShiftCorrect_of_mul_lt (by decide) (by decide)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 7 (by omega)) hlo)

/-! ### Bias-and-shift on core `BitVec 8` -/

/-- **Bias-and-shift on `BitVec 8` (bounded check).** For every `k < 8` and
every `x : BitVec 8`, the wrapping bit-vector sequence `biasDivBV k x` has
signed value `Int.tdiv x.toInt (2^k)`; for `k ≤ 6` (where `2^k` is a positive
signed 8-bit value) it equals core `BitVec.sdiv x (2^k)`. -/
theorem biasDivBV_u8 :
    (∀ k, k < 8 → ∀ x : BitVec 8, (biasDivBV k x).toInt = Int.tdiv x.toInt (2 ^ k)) ∧
    (∀ k, k ≤ 6 → ∀ x : BitVec 8, biasDivBV k x = x.sdiv (BitVec.ofNat 8 (2 ^ k))) := by
  have h1 : allBelow 8 (fun k => allBelow 256 (fun i =>
      (biasDivBV k (BitVec.ofNat 8 i)).toInt == Int.tdiv (BitVec.ofNat 8 i).toInt (2 ^ k))) = true := by
    decide +kernel
  have h2 : allBelow 7 (fun k => allBelow 256 (fun i =>
      biasDivBV k (BitVec.ofNat 8 i) == (BitVec.ofNat 8 i).sdiv (BitVec.ofNat 8 (2 ^ k)))) = true := by
    decide +kernel
  rw [allBelow_iff] at h1 h2
  refine ⟨fun k hk x => ?_, fun k hk x => ?_⟩
  · have h := h1 k hk
    rw [allBelow_iff] at h
    have e := h x.toNat x.isLt
    simpa using e
  · have h := h2 k (by omega)
    rw [allBelow_iff] at h
    have e := h x.toNat x.isLt
    simpa using e


/-- **Bias-and-shift on `BitVec 8` with shift counts reduced modulo 8
(bounded check).** For every `1 ≤ k < 8` and every `x : BitVec 8`, the wrapping
sequence whose three shift counts are taken modulo 8 has signed value
`Int.tdiv x.toInt (2^k)`. (At `k = 0` it fails: `ce_biasDivBVMasked_u8_k_zero`.) -/
theorem biasDivBVMasked_u8 :
    ∀ k, 1 ≤ k → k < 8 → ∀ x : BitVec 8,
      (biasDivBVMasked k x).toInt = Int.tdiv x.toInt (2 ^ k) := by
  have h : allBelow 8 (fun k => decide (k = 0) || allBelow 256 (fun i =>
      (biasDivBVMasked k (BitVec.ofNat 8 i)).toInt ==
        Int.tdiv (BitVec.ofNat 8 i).toInt (2 ^ k))) = true := by
    decide +kernel
  rw [allBelow_iff] at h
  intro k hk1 hk8 x
  have hk := h k hk8
  simp only [Bool.or_eq_true, decide_eq_true_eq, allBelow_iff, beq_iff_eq] at hk
  rcases hk with rfl | hk
  · omega
  · simpa using hk x.toNat x.isLt

/-! ### Escape hatches for 8-bit division by 7 -/

/-- **Multiply-add with an 8-bit constant.** `(x * 146 + 146) >>> 10 = x / 7`
for every `x < 2^8` (`146 = ⌊2^10/7⌋ < 2^8`). -/
theorem robison_multiply_add_u8_div7 :
    146 < 2 ^ 8 ∧ ∀ x, x < 2 ^ 8 → (x * 146 + 146) >>> 10 = x / 7 := by
  refine ⟨by decide, ?_⟩
  have h : allBelow 256 (fun x => (x * 146 + 146) >>> 10 == x / 7) = true := by decide +kernel
  rw [allBelow_iff] at h
  intro x hx
  simpa using h x hx

/-- **Narrower dividend range.** The 8-bit multiplier `147` with shift `10`
computes `x / 7` for every `x < 209`, and fails at `x = 209`. -/
theorem mulShift_u8_div7_below_209 :
    147 < 2 ^ 8 ∧ (∀ x, x < 209 → (x * 147) >>> 10 = x / 7) ∧ (209 * 147) >>> 10 ≠ 209 / 7 := by
  refine ⟨by decide, ?_, by decide⟩
  have h : allBelow 209 (fun x => (x * 147) >>> 10 == x / 7) = true := by decide +kernel
  rw [allBelow_iff] at h
  intro x hx
  simpa using h x hx

/-! ### Counts over all 8-bit divisors -/

/-- Boolean version of `∀ x < 2^N, directRem F d m x = x % d`. -/
def directRemB (N F d m : Nat) : Bool :=
  allBelow (2 ^ N) (fun x => directRem F d m x == x % d)

/-- For `N = 8`, the single-word candidate is incorrect for exactly `55` of the
divisors `1 ≤ d ≤ 255` (so, by `single_word_multiplier_exists_iff`, exactly
`55` of them admit no `8`-bit multiplier at any shift). -/
theorem count_no_single_word_u8 :
    (List.range 255).countP
      (fun i => !correctB 8 (i + 1) (singleWordMagic 8 (i + 1)) (singleWordShift 8 (i + 1))) = 55 := by
  decide +kernel

/-- For `N = 8`, the single-word candidate is correct for exactly `200` of the
divisors `1 ≤ d ≤ 255`. -/
theorem count_single_word_u8 :
    (List.range 255).countP
      (fun i => correctB 8 (i + 1) (singleWordMagic 8 (i + 1)) (singleWordShift 8 (i + 1))) = 200 := by
  decide +kernel

/-- Among those `200` divisors, the quotient-correct single-word pair
`(singleWordMagic 8 d, singleWordShift 8 d)` fails the direct remainder
computation `directRem` for exactly `42`. -/
theorem count_single_word_u8_directRem_fails :
    (List.range 255).countP
      (fun i => correctB 8 (i + 1) (singleWordMagic 8 (i + 1)) (singleWordShift 8 (i + 1)) &&
        !directRemB 8 (singleWordShift 8 (i + 1)) (i + 1) (singleWordMagic 8 (i + 1))) = 42 := by
  decide +kernel

end Toy.MagicDiv
