/-
Toy.MagicDiv.Statements
=======================

Main results, all fully proved. Bounded (evaluated) results live in
`Toy.MagicDiv.Bounded`; tightness counterexamples, positive controls and
further evaluated facts in `Toy.MagicDiv.Counterexamples`; non-vacuity
theorems in `Toy.MagicDiv.Witnesses`.

Conventions: `N` is the input width (unsigned inputs are `x < 2^N`, signed
inputs satisfy `SignedRange N x`), `d` the divisor, `m` the multiplier, `s`
(unsigned) or `k` (signed) the total right-shift amount, and `ℓ` the excess of
the shift over `N` (unsigned) or over `N - 1` (signed).
-/
import Toy.MagicDiv.Lemmas

namespace Toy.MagicDiv


/-! ### Multiply-shift correctness -/

/-- **Unsigned multiply-shift, sufficient criterion.** If
`2^(N+ℓ) ≤ m * d ≤ 2^(N+ℓ) + 2^ℓ`, then `(x * m) >>> (N + ℓ) = x / d` for every
`x < 2^N`. (`d ≥ 1` follows from the lower bound, see `pos_of_two_pow_le_mul`;
the ceiling multiplier `⌈2^(N+ℓ)/d⌉` meets the lower bound automatically, see
`le_ceilDiv_mul`.) -/
theorem mulShiftCorrect_of_sandwich (N ℓ d m : Nat)
    (hlo : 2 ^ (N + ℓ) ≤ m * d) (hhi : m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ) :
    MulShiftCorrect N d m (N + ℓ) := by
  have hd : 0 < d := pos_of_two_pow_le_mul hlo
  intro x hx
  rw [Nat.shiftRight_eq_div_pow]
  apply div_eq_of_bounds
  · calc x / d * 2 ^ (N + ℓ) ≤ x / d * (m * d) := Nat.mul_le_mul_left _ hlo
      _ = (x / d * d) * m := by rw [Nat.mul_comm m d, ← Nat.mul_assoc, Nat.mul_right_comm]
      _ ≤ x * m := Nat.mul_le_mul_right _ (Nat.div_mul_le_self x d)
  · have hq := lt_succ_div_mul x d hd
    have hxL : x * 2 ^ ℓ < 2 ^ (N + ℓ) := by
      rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos ℓ)
    apply Nat.lt_of_mul_lt_mul_right (a := d)
    calc x * m * d = x * (m * d) := Nat.mul_assoc _ _ _
      _ ≤ x * (2 ^ (N + ℓ) + 2 ^ ℓ) := Nat.mul_le_mul_left _ hhi
      _ = x * 2 ^ (N + ℓ) + x * 2 ^ ℓ := Nat.mul_add _ _ _
      _ < x * 2 ^ (N + ℓ) + 2 ^ (N + ℓ) := by omega
      _ = (x + 1) * 2 ^ (N + ℓ) := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ ((x / d + 1) * d) * 2 ^ (N + ℓ) := Nat.mul_le_mul_right _ hq
      _ = (x / d + 1) * 2 ^ (N + ℓ) * d := Nat.mul_right_comm _ _ _

/-! ### Multiplier size -/

/-- **Existence.** For every `d ≥ 1` and every `N`, the multiplier
`unsignedMagic N d = ⌈2^(N + clog2 d)/d⌉` satisfies the sandwich bounds of
`mulShiftCorrect_of_sandwich` with `ℓ = clog2 d`. -/
theorem unsignedMagic_sandwich (N d : Nat) (hd : 0 < d) :
    2 ^ (N + clog2 d) ≤ unsignedMagic N d * d ∧
      unsignedMagic N d * d ≤ 2 ^ (N + clog2 d) + 2 ^ clog2 d := by
  refine ⟨le_ceilDiv_mul _ d hd, ?_⟩
  have h1 := ceilDiv_mul_lt (2 ^ (N + clog2 d)) d hd
  have h2 := le_two_pow_clog2 hd
  unfold unsignedMagic
  omega

/-- **For `d ≥ 1` the textbook multiplier does not fit in `N` bits:** for every
`N` and every `d ≥ 1`, `2^N ≤ unsignedMagic N d` (`unsignedMagic N 0 = 0`). -/
theorem unsignedMagic_ge_two_pow_of_pos (N d : Nat) (hd : 0 < d) :
    2 ^ N ≤ unsignedMagic N d := by
  have hlo := (unsignedMagic_sandwich N d hd).1
  have hd_le := le_two_pow_clog2 hd
  have hmul : 2 ^ N * d ≤ unsignedMagic N d * d := by
    calc 2 ^ N * d
      _ ≤ 2 ^ N * 2 ^ clog2 d := Nat.mul_le_mul_left (2 ^ N) hd_le
      _ = 2 ^ (N + clog2 d) := (Nat.pow_add 2 N (clog2 d)).symm
      _ ≤ unsignedMagic N d * d := hlo
  exact Nat.le_of_mul_le_mul_right hmul hd

/-- `⌈a/d⌉ < B` as soon as `a + d ≤ B * d`. -/
theorem ceilDiv_lt_of {a d B : Nat} (hd : 0 < d) (h : a + d ≤ B * d) : ceilDiv a d < B := by
  unfold ceilDiv
  rw [Nat.div_lt_iff_lt_mul hd]
  omega

/-- **The textbook multiplier fits in `N + 1` bits for divisors up to
`2^(N+1)`.** If `d ≤ 2^(N+1)`, then `unsignedMagic N d < 2^(N+1)`. -/
theorem unsignedMagic_lt_two_pow_succ_of_le (N d : Nat) (hd : d ≤ 2 ^ (N + 1)) :
    unsignedMagic N d < 2 ^ (N + 1) := by
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · rcases Nat.lt_or_ge d 1 with hd1 | hd1
    · have : d = 0 := by omega
      subst this
      simp only [unsignedMagic, ceilDiv, Nat.div_zero]
      exact Nat.two_pow_pos _
    · have : d = 1 := by omega
      subst this
      have : 2 ^ N < 2 ^ (N + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
      simpa [unsignedMagic, ceilDiv, clog2] using this
  · have hc1 := one_le_clog2 hd2
    have hcle : clog2 d ≤ N + 1 := clog2_le_of_le_two_pow hd
    have hA := two_pow_pred_clog2_lt hd2
    have hAM : 2 ^ (clog2 d - 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) (by omega)
    apply ceilDiv_lt_of (by omega)
    have hsplit : 2 ^ (N + clog2 d) = 2 ^ (N + 1) * 2 ^ (clog2 d - 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hsplit]
    obtain ⟨e, he⟩ : ∃ e, d = 2 ^ (clog2 d - 1) + 1 + e := ⟨d - (2 ^ (clog2 d - 1) + 1), by omega⟩
    have hP : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [Nat.pow_succ, Nat.mul_comm]
    have hexp : 2 ^ (N + 1) * d = 2 ^ (N + 1) * 2 ^ (clog2 d - 1) + 2 ^ (N + 1) + 2 ^ (N + 1) * e := by
      conv => lhs; rw [he]
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have he' : e ≤ 2 ^ (N + 1) * e := Nat.le_mul_of_pos_left e (Nat.two_pow_pos _)
    omega

/-- For `d ≥ 2` the textbook multiplier is at most `2^(N+1)` (no upper bound
on `d` is needed for this weaker bound). -/
theorem unsignedMagic_le_two_pow_succ (N d : Nat) (hd : 2 ≤ d) :
    unsignedMagic N d ≤ 2 ^ (N + 1) := by
  apply ceilDiv_le_of_le_mul (by omega)
  have hc1 := one_le_clog2 hd
  have hA := two_pow_pred_clog2_lt hd
  have hsplit : 2 ^ (N + clog2 d) = 2 ^ (N + 1) * 2 ^ (clog2 d - 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hsplit]
  exact Nat.mul_le_mul_left _ (Nat.le_of_lt hA)


/-! ### Reduction lemmas on correctness -/

/-- A correct multiplier satisfies the lower bound `2^s ≤ m * d` (evaluate at
the input `x = d`, which needs `1 ≤ d < 2^N`). -/
theorem two_pow_le_mul_of_correct {N d m s : Nat} (hd : 0 < d) (hdN : d < 2 ^ N)
    (h : MulShiftCorrect N d m s) : 2 ^ s ≤ m * d := by
  have e := h d hdN
  rw [Nat.shiftRight_eq_div_pow, Nat.div_self hd, Nat.mul_comm] at e
  refine Nat.not_lt.mp fun hlt => ?_
  rw [Nat.div_eq_of_lt hlt] at e
  exact absurd e (by decide)

/-- If some multiplier `m` with `2^s ≤ m * d` is correct at shift `s`, the
ceiling multiplier `⌈2^s/d⌉` is correct at shift `s` too. -/
theorem mulShiftCorrect_ceilDiv_of_correct {N d m s : Nat} (hd : 0 < d)
    (h : MulShiftCorrect N d m s) (hm : 2 ^ s ≤ m * d) :
    MulShiftCorrect N d (ceilDiv (2 ^ s) d) s := by
  have hc : ceilDiv (2 ^ s) d ≤ m := ceilDiv_le_of_le_mul hd hm
  intro x hx
  have hup : (x * ceilDiv (2 ^ s) d) >>> s ≤ x / d := h x hx ▸ mulShift_mono hc
  have hlow : x / d ≤ (x * ceilDiv (2 ^ s) d) >>> s := by
    rw [Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (Nat.two_pow_pos s)]
    have hlo := le_ceilDiv_mul (2 ^ s) d hd
    calc x / d * 2 ^ s
      _ ≤ x / d * (ceilDiv (2 ^ s) d * d) := Nat.mul_le_mul_left _ hlo
      _ = (x / d * d) * ceilDiv (2 ^ s) d := by
          rw [Nat.mul_comm (ceilDiv (2 ^ s) d) d, ← Nat.mul_assoc]
      _ ≤ x * ceilDiv (2 ^ s) d := Nat.mul_le_mul_right _ (Nat.div_mul_le_self x d)
  omega

/-- **Correct shifts are upward closed for the ceiling multiplier.** If the
ceiling multiplier `⌈2^s/d⌉` is correct at shift `s`, the ceiling multiplier
`⌈2^(s+1)/d⌉` is correct at shift `s + 1` (any `N`, any `d`). -/
theorem mulShiftCorrect_ceilDiv_succ (N d s : Nat)
    (h : MulShiftCorrect N d (ceilDiv (2 ^ s) d) s) :
    MulShiftCorrect N d (ceilDiv (2 ^ (s + 1)) d) (s + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro x _; simp [ceilDiv]
  · intro x hx
    have h_prev := h x hx
    rw [Nat.shiftRight_eq_div_pow] at h_prev ⊢
    have hm_le : ceilDiv (2 ^ (s + 1)) d ≤ 2 * ceilDiv (2 ^ s) d := by
      apply ceilDiv_le_of_le_mul hd
      have h2s := le_ceilDiv_mul (2 ^ s) d hd
      rw [Nat.pow_succ, Nat.mul_assoc]
      omega
    have h_upper : (x * ceilDiv (2 ^ (s + 1)) d) / 2 ^ (s + 1) ≤ x / d := by
      have h1 : x * ceilDiv (2 ^ (s + 1)) d ≤ 2 * (x * ceilDiv (2 ^ s) d) := by
        calc x * ceilDiv (2 ^ (s + 1)) d
          _ ≤ x * (2 * ceilDiv (2 ^ s) d) := Nat.mul_le_mul_left x hm_le
          _ = 2 * (x * ceilDiv (2 ^ s) d) := by
              rw [← Nat.mul_assoc, Nat.mul_comm x 2, Nat.mul_assoc]
      have hp2 : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ, Nat.mul_comm]
      calc (x * ceilDiv (2 ^ (s + 1)) d) / 2 ^ (s + 1)
        _ = (x * ceilDiv (2 ^ (s + 1)) d) / (2 * 2 ^ s) := by rw [hp2]
        _ ≤ (2 * (x * ceilDiv (2 ^ s) d)) / (2 * 2 ^ s) := Nat.div_le_div_right h1
        _ = (x * ceilDiv (2 ^ s) d) / 2 ^ s := Nat.mul_div_mul_left _ _ (by decide : 0 < 2)
        _ = x / d := h_prev
    have h_lower : x / d ≤ (x * ceilDiv (2 ^ (s + 1)) d) / 2 ^ (s + 1) := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos (s + 1))]
      have hlo := le_ceilDiv_mul (2 ^ (s + 1)) d hd
      calc (x / d) * 2 ^ (s + 1)
        _ ≤ (x / d) * (ceilDiv (2 ^ (s + 1)) d * d) := Nat.mul_le_mul_left (x / d) hlo
        _ = ((x / d) * d) * ceilDiv (2 ^ (s + 1)) d := by
            rw [Nat.mul_comm (ceilDiv (2 ^ (s + 1)) d) d, ← Nat.mul_assoc]
        _ ≤ x * ceilDiv (2 ^ (s + 1)) d := Nat.mul_le_mul_right _ (Nat.div_mul_le_self x d)
    omega

/-- Iterated upward closure. -/
theorem mulShiftCorrect_ceilDiv_add (N d s j : Nat)
    (h : MulShiftCorrect N d (ceilDiv (2 ^ s) d) s) :
    MulShiftCorrect N d (ceilDiv (2 ^ (s + j)) d) (s + j) := by
  induction j with
  | zero => simpa using h
  | succ j ih => exact mulShiftCorrect_ceilDiv_succ N d (s + j) ih

/-- **The ceiling multiplier is optimal at each shift.** For `1 ≤ d < 2^N`
and every shift `s`, some multiplier is correct at shift `s` iff the ceiling
multiplier `⌈2^s/d⌉` is. -/
theorem exists_mulShiftCorrect_iff_ceilDiv (N d s : Nat) (hd : 0 < d)
    (hdN : d < 2 ^ N) :
    (∃ m, MulShiftCorrect N d m s) ↔ MulShiftCorrect N d (ceilDiv (2 ^ s) d) s := by
  refine ⟨fun ⟨m, hm⟩ => ?_, fun h => ⟨_, h⟩⟩
  exact mulShiftCorrect_ceilDiv_of_correct hd hm (two_pow_le_mul_of_correct hd hdN hm)

/-- **Exact criterion for divisors of at least `2^N`.** If `2^N ≤ d` (every
`N`-bit quotient is `0`), the multiply-shift is correct iff
`(2^N - 1) * m < 2^s`. -/
theorem mulShiftCorrect_iff_of_two_pow_le (N d m s : Nat) (hdN : 2 ^ N ≤ d) :
    MulShiftCorrect N d m s ↔ (2 ^ N - 1) * m < 2 ^ s := by
  unfold MulShiftCorrect
  constructor
  · intro h
    have hx : 2 ^ N - 1 < 2 ^ N := by have := Nat.two_pow_pos N; omega
    have heq := h (2 ^ N - 1) hx
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx hdN)] at heq
    refine Nat.not_le.mp fun hle => ?_
    have hpos : 0 < ((2 ^ N - 1) * m) / 2 ^ s := Nat.div_pos hle (Nat.two_pow_pos s)
    omega
  · intro hlt x hx
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx hdN)]
    apply Nat.div_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right m (by omega : x ≤ 2 ^ N - 1)) hlt

/-! ### Single-word multipliers -/

/-- **The single-word candidate fits in `N` bits.** For `N ≥ 1` and
`d ≤ 2^N`, `singleWordMagic N d < 2^N`. -/
theorem singleWordMagic_lt_two_pow (N d : Nat) (hN : 1 ≤ N) (hdN : d ≤ 2 ^ N) :
    singleWordMagic N d < 2 ^ N := by
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · rcases Nat.lt_or_ge d 1 with hd1 | hd1
    · have : d = 0 := by omega
      subst this
      simp only [singleWordMagic, ceilDiv, Nat.div_zero]
      exact Nat.two_pow_pos _
    · have : d = 1 := by omega
      subst this
      have : 2 ^ (N - 1) < 2 ^ N := Nat.pow_lt_pow_right (by decide) (by omega)
      simpa [singleWordMagic, singleWordShift, ceilDiv, clog2] using this
  · have hc1 := one_le_clog2 hd2
    have hcle : clog2 d ≤ N := clog2_le_of_le_two_pow hdN
    have hA := two_pow_pred_clog2_lt hd2
    have hAM : 2 ^ (clog2 d - 1) < 2 ^ N := Nat.pow_lt_pow_right (by decide) (by omega)
    unfold singleWordMagic singleWordShift
    apply ceilDiv_lt_of (by omega)
    have hsplit : 2 ^ (N + clog2 d - 1) = 2 ^ N * 2 ^ (clog2 d - 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hsplit]
    obtain ⟨e, he⟩ : ∃ e, d = 2 ^ (clog2 d - 1) + 1 + e := ⟨d - (2 ^ (clog2 d - 1) + 1), by omega⟩
    have hexp : 2 ^ N * d = 2 ^ N * 2 ^ (clog2 d - 1) + 2 ^ N + 2 ^ N * e := by
      conv => lhs; rw [he]
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have he' : e ≤ 2 ^ N * e := Nat.le_mul_of_pos_left e (Nat.two_pow_pos _)
    omega

/-- For `N ≥ 1` and `2^N ≤ d`, the single-word candidate is correct (every
`N`-bit quotient is `0`). -/
theorem singleWord_correct_of_two_pow_le (N d : Nat) (hN : 1 ≤ N) (hdN : 2 ^ N ≤ d) :
    MulShiftCorrect N d (singleWordMagic N d) (singleWordShift N d) := by
  have h2N : 2 ≤ 2 ^ N := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hN
    simpa using this
  have hd2 : 2 ≤ d := by omega
  have hc1 := one_le_clog2 hd2
  have hcN : N ≤ clog2 d := by
    have := le_two_pow_clog2 (by omega : 0 < d)
    exact (Nat.pow_le_pow_iff_right (by decide)).mp (Nat.le_trans hdN this)
  have hshift : singleWordShift N d = N + (clog2 d - 1) := by
    unfold singleWordShift; omega
  have hm : singleWordMagic N d ≤ 2 ^ (clog2 d - 1) := by
    unfold singleWordMagic
    rw [hshift]
    apply ceilDiv_le_of_le_mul (by omega)
    rw [Nat.pow_add, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hdN
  intro x hx
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx hdN), Nat.shiftRight_eq_div_pow]
  apply Nat.div_eq_of_lt
  rw [hshift, Nat.pow_add]
  calc x * singleWordMagic N d ≤ x * 2 ^ (clog2 d - 1) := Nat.mul_le_mul_left x hm
    _ < 2 ^ N * 2 ^ (clog2 d - 1) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)

/-- **Single-word multiplier characterization.** For every `N` and every `d`,
some multiplier `m < 2^N` with some shift `s` is correct for all `N`-bit inputs
if and only if the candidate `singleWordMagic N d = ⌈2^(N + clog2 d - 1)/d⌉`
is correct at shift `singleWordShift N d = N + clog2 d - 1`. (That the
candidate is itself below `2^N` when `N ≥ 1` and `d ≤ 2^N` is
`singleWordMagic_lt_two_pow`.) -/
theorem single_word_multiplier_exists_iff (N d : Nat) :
    (∃ m s, m < 2 ^ N ∧ MulShiftCorrect N d m s) ↔
      MulShiftCorrect N d (singleWordMagic N d) (singleWordShift N d) := by
  constructor
  · rintro ⟨m, s, hm, hc⟩
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · intro x _; simp [singleWordMagic, ceilDiv]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · intro x hx
      have : x = 0 := by simpa using hx
      subst this; simp
    rcases Nat.lt_or_ge d (2 ^ N) with hdN | hdN
    · -- main case: `1 ≤ d < 2^N`
      have hlo := two_pow_le_mul_of_correct hd hdN hc
      have hdc := le_two_pow_clog2 hd
      have hs : s ≤ singleWordShift N d := by
        have h1 : m * d < 2 ^ (N + clog2 d) := by
          rw [Nat.pow_add]
          exact Nat.mul_lt_mul_of_lt_of_le hm hdc (Nat.two_pow_pos _)
        have h2 : s < N + clog2 d :=
          (Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_le_of_lt hlo h1)
        unfold singleWordShift; omega
      have hceil := mulShiftCorrect_ceilDiv_of_correct hd hc hlo
      have := mulShiftCorrect_ceilDiv_add N d s (singleWordShift N d - s) hceil
      rw [Nat.add_sub_cancel' hs] at this
      exact this
    · exact singleWord_correct_of_two_pow_le N d hN hdN
  · intro h
    by_cases hc : 1 ≤ N ∧ d ≤ 2 ^ N
    · exact ⟨_, _, singleWordMagic_lt_two_pow N d hc.1 hc.2, h⟩
    · refine ⟨0, 0, Nat.two_pow_pos N, fun x hx => ?_⟩
      have hxd : x < d ∨ N = 0 := by omega
      rcases hxd with hxd | hN0
      · simp [Nat.div_eq_of_lt hxd]
      · subst hN0
        have : x = 0 := by simpa using hx
        subst this; simp


/-! ### Add-and-shift fixup -/

/-- **Fixup identity.** For `ℓ ≥ 1` and `m' ≤ 2^N`, the add-and-shift fixup
sequence equals the wide multiply-shift by `2^N + m'` for every natural
number `x` (no input-range hypothesis). -/
theorem fixupQuot_eq_wide (N m' ℓ x : Nat) (hℓ : 1 ≤ ℓ) (hm' : m' ≤ 2 ^ N) :
    fixupQuot N m' ℓ x = (x * (2 ^ N + m')) >>> (N + ℓ) := by
  unfold fixupQuot
  simp only [Nat.shiftRight_eq_div_pow]
  have hP := Nat.two_pow_pos N
  generalize ht : x * m' / 2 ^ N = t
  have htx : t ≤ x := by
    rw [← ht]
    apply Nat.div_le_of_le_mul
    rw [Nat.mul_comm (2 ^ N) x]
    exact Nat.mul_le_mul_left x hm'
  have havg : t + (x - t) / 2 ^ 1 = (x + t) / 2 := by
    have : (x - t + t * 2) / 2 = (x - t) / 2 + t := Nat.add_mul_div_right _ _ (by decide)
    rw [show x - t + t * 2 = x + t by omega] at this
    rw [this, Nat.pow_one]; omega
  have hwide : x * (2 ^ N + m') / 2 ^ (N + ℓ) = (x + t) / 2 ^ ℓ := by
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_add, Nat.mul_comm x (2 ^ N),
      Nat.add_comm, Nat.add_mul_div_left _ _ hP, ht, Nat.add_comm]
  rw [havg, hwide, Nat.div_div_eq_div_mul, ← Nat.pow_succ']
  congr 2
  omega

/-- **Fixup correctness.** If `ℓ ≥ 1`, `m' ≤ 2^N`, and the wide multiply-shift
by `2^N + m'` with shift `N + ℓ` is correct on `N`-bit inputs, then the fixup
sequence computes `x / d` for every `x < 2^N`. -/
theorem fixupQuot_correct (N d m' ℓ : Nat) (hℓ : 1 ≤ ℓ) (hm' : m' ≤ 2 ^ N)
    (h : MulShiftCorrect N d (2 ^ N + m') (N + ℓ)) :
    ∀ x, x < 2 ^ N → fixupQuot N m' ℓ x = x / d := by
  intro x hx
  rw [fixupQuot_eq_wide N m' ℓ x hℓ hm', h x hx]

/-- **Fixup with the textbook multiplier.** For every `d ≥ 2` and every `N`,
the fixup sequence with `m' = unsignedMagic N d - 2^N` and `ℓ = clog2 d`
computes `x / d` for every `x < 2^N`. -/
theorem fixupQuot_unsignedMagic_correct (N d : Nat) (hd : 2 ≤ d) :
    ∀ x, x < 2 ^ N → fixupQuot N (unsignedMagic N d - 2 ^ N) (clog2 d) x = x / d := by
  have hge := unsignedMagic_ge_two_pow_of_pos N d (by omega)
  have hle := unsignedMagic_le_two_pow_succ N d hd
  have hP : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by rw [Nat.pow_succ]; omega
  have hm' : unsignedMagic N d - 2 ^ N ≤ 2 ^ N := by omega
  have hsum : 2 ^ N + (unsignedMagic N d - 2 ^ N) = unsignedMagic N d := by omega
  have hsw := unsignedMagic_sandwich N d (by omega)
  have hc := mulShiftCorrect_of_sandwich N (clog2 d) d (unsignedMagic N d) hsw.1 hsw.2
  rw [← hsum] at hc
  exact fixupQuot_correct N d _ _ (one_le_clog2 hd) hm' hc

/-! ### Exact criterion -/

/-- **Exact criterion (unsigned).** For `1 ≤ d < 2^N`, the multiply-shift
`(x * m) >>> s` is correct on all `N`-bit inputs if and only if
`2^s ≤ m * d` and `lastFullBlockEnd N d * (m * d - 2^s) < 2^s`. -/
theorem mulShiftCorrect_iff_exactCriterion (N d m s : Nat) (hd : 0 < d)
    (hdN : d < 2 ^ N) :
    MulShiftCorrect N d m s ↔ ExactCriterion N d m s := by
  -- `2^N = d * Q + ρ` with `Q ≥ 1`, and `nc = d * Q - 1`.
  have hdiv := Nat.div_add_mod (2 ^ N) d
  have hρ := Nat.mod_lt (2 ^ N) hd
  generalize hQ : 2 ^ N / d = Q at hdiv
  generalize hR : 2 ^ N % d = ρ at hdiv hρ
  have hQ1 : 1 ≤ Q := by
    rw [← hQ]; exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
  have hdQ : d ≤ d * Q := Nat.le_mul_of_pos_right d hQ1
  have hnc : lastFullBlockEnd N d = d * Q - 1 := by
    unfold lastFullBlockEnd; omega
  have hncN : lastFullBlockEnd N d < 2 ^ N := by omega
  have hncd : lastFullBlockEnd N d / d = Q - 1 := by
    rw [hnc]
    apply div_eq_of_bounds
    · rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm Q d]; omega
    · rw [Nat.sub_add_cancel hQ1, Nat.mul_comm Q d]; omega
  generalize hn : lastFullBlockEnd N d = nc at hnc hncN hncd
  unfold ExactCriterion
  rw [hn]
  constructor
  · intro h
    have hlo := two_pow_le_mul_of_correct hd hdN h
    refine ⟨hlo, ?_⟩
    have e := h nc hncN
    rw [hncd, Nat.shiftRight_eq_div_pow] at e
    have h1 : nc * m < Q * 2 ^ s := by
      have : nc * m / 2 ^ s < Q := by omega
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).mp this
    have h2 : nc * m * d < Q * 2 ^ s * d := Nat.mul_lt_mul_of_pos_right h1 hd
    have h3 : Q * 2 ^ s * d = (nc + 1) * 2 ^ s := by
      rw [Nat.mul_right_comm, Nat.mul_comm Q d, show d * Q = nc + 1 by omega]
    have h4 : nc * m * d = nc * 2 ^ s + nc * (m * d - 2 ^ s) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hlo]
    have h5 : (nc + 1) * 2 ^ s = nc * 2 ^ s + 2 ^ s := by rw [Nat.add_mul, Nat.one_mul]
    omega
  · rintro ⟨hlo, hhi⟩ x hx
    rw [Nat.shiftRight_eq_div_pow]
    generalize hE : m * d - 2 ^ s = E at hhi
    have hmd : m * d = 2 ^ s + E := by omega
    apply div_eq_of_bounds
    · calc x / d * 2 ^ s ≤ x / d * (m * d) := Nat.mul_le_mul_left _ hlo
        _ = (x / d * d) * m := by rw [Nat.mul_comm m d, ← Nat.mul_assoc, Nat.mul_right_comm]
        _ ≤ x * m := Nat.mul_le_mul_right _ (Nat.div_mul_le_self x d)
    · apply Nat.lt_of_mul_lt_mul_right (a := d)
      have hxd := Nat.div_add_mod x d
      have hr := Nat.mod_lt x hd
      generalize hq : x / d = q at hxd
      generalize hrr : x % d = r at hxd hr
      -- `x * m * d = x * 2^s + x * E` and `(q + 1) * 2^s * d = x * 2^s + (d - r) * 2^s`.
      have hl : x * m * d = x * 2 ^ s + x * E := by rw [Nat.mul_assoc, hmd, Nat.mul_add]
      have hrgt : (q + 1) * 2 ^ s * d = x * 2 ^ s + (d - r) * 2 ^ s := by
        rw [Nat.mul_right_comm, ← Nat.add_mul]
        congr 1
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q d]; omega
      rw [hl, hrgt]
      suffices hk : x * E < (d - r) * 2 ^ s by omega
      by_cases hxnc : x ≤ nc
      · have h1 : x * E ≤ nc * E := Nat.mul_le_mul_right E hxnc
        have h2 : 2 ^ s ≤ (d - r) * 2 ^ s := Nat.le_mul_of_pos_left _ (by omega)
        omega
      · -- the last, incomplete block: `q = Q` and `r < ρ ≤ d - 1`
        have hqQ : q = Q := by
          rw [← hq]
          apply div_eq_of_bounds
          · rw [Nat.mul_comm]; omega
          · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
        subst hqQ
        have hr2 : 2 ≤ d - r := by omega
        have hx2 : x ≤ 2 * nc := by omega
        have h1 : x * E ≤ 2 * nc * E := Nat.mul_le_mul_right E hx2
        have h1' : 2 * nc * E = 2 * (nc * E) := Nat.mul_assoc 2 nc E
        have h2 : 2 * 2 ^ s ≤ (d - r) * 2 ^ s := Nat.mul_le_mul_right _ hr2
        omega

/-! ### Remainders -/

/-- **Unsigned remainder from any correct multiply-shift quotient.** If
`MulShiftCorrect N d m s`, then `x - d * ((x * m) >>> s) = x % d` for every
`x < 2^N`. -/
theorem mulShift_rem_eq_mod_of_correct (N d m s : Nat) (h : MulShiftCorrect N d m s) :
    ∀ x, x < 2 ^ N → x - d * ((x * m) >>> s) = x % d := by
  intro x hx
  rw [h x hx]
  have := Nat.div_add_mod x d
  omega

/-- **Direct remainder (no quotient).** Under the sandwich bounds,
`(((x * m) % 2^(N+ℓ)) * d) >>> (N + ℓ) = x % d` for every `x < 2^N`. A
multiplier that is merely correct for the quotient need not satisfy this
(`ce_directRem_quotient_valid_multiplier`). -/
theorem directRem_eq_mod_of_sandwich (N ℓ d m : Nat)
    (hlo : 2 ^ (N + ℓ) ≤ m * d) (hhi : m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ) :
    ∀ x, x < 2 ^ N → directRem (N + ℓ) d m x = x % d := by
  have hd : 0 < d := pos_of_two_pow_le_mul hlo
  intro x hx
  have hq := mulShiftCorrect_of_sandwich N ℓ d m hlo hhi x hx
  rw [Nat.shiftRight_eq_div_pow] at hq
  unfold directRem
  rw [Nat.shiftRight_eq_div_pow]
  have hP := Nat.two_pow_pos (N + ℓ)
  generalize hF : 2 ^ (N + ℓ) = F at hlo hhi hq hP
  generalize hE : m * d - F = E
  have hmd : m * d = F + E := by omega
  have hEl : E ≤ 2 ^ ℓ := by omega
  have hxE : x * E < F := by
    rw [← hF, Nat.pow_add]
    calc x * E ≤ x * 2 ^ ℓ := Nat.mul_le_mul_left x hEl
      _ < 2 ^ N * 2 ^ ℓ := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos ℓ)
  -- `x * m = F * (x / d) + (x * m) % F`, and `x / d = q`.
  have hdm := Nat.div_add_mod (x * m) F
  rw [hq] at hdm
  have hxd := Nat.div_add_mod x d
  generalize hq' : x / d = q at hdm hxd
  generalize hr : x % d = r at hxd
  generalize hlowp : x * m % F = L at hdm
  -- `L * d = r * F + x * E`
  have key : L * d = r * F + x * E := by
    have e1 : x * m * d = x * F + x * E := by rw [Nat.mul_assoc, hmd, Nat.mul_add]
    have e2 : x * m * d = F * q * d + L * d := by rw [← hdm, Nat.add_mul]
    have e3 : x * F = F * q * d + r * F := by
      rw [← hxd, Nat.add_mul]
      congr 1
      rw [Nat.mul_comm d q, Nat.mul_right_comm, Nat.mul_comm q F]
    omega
  rw [key, Nat.mul_comm r F, Nat.add_comm, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hxE]
  omega

/-- On power-of-two denominators `2^(N+ℓ)` with `ℓ < N`, the sandwich bound
coincides with the bound `(2^N - 1) * (m * d - 2^(N+ℓ)) < 2^(N+ℓ)` of
Lemire–Bartlett–Kaser (2021, Theorem 2) for `N`-bit inputs. -/
theorem sandwich_iff_directRem_bound (N ℓ d m : Nat) (hℓ : ℓ < N) :
    (2 ^ (N + ℓ) ≤ m * d ∧ m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ) ↔
      (2 ^ (N + ℓ) ≤ m * d ∧ (2 ^ N - 1) * (m * d - 2 ^ (N + ℓ)) < 2 ^ (N + ℓ)) := by
  have hLN : 2 ^ ℓ < 2 ^ N := Nat.pow_lt_pow_right (by decide) hℓ
  have hF : 2 ^ (N + ℓ) = 2 ^ N * 2 ^ ℓ := Nat.pow_add 2 N ℓ
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨hlo, ?_⟩
    have h1 : (2 ^ N - 1) * (m * d - 2 ^ (N + ℓ)) ≤ (2 ^ N - 1) * 2 ^ ℓ :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (2 ^ N - 1) * 2 ^ ℓ = 2 ^ N * 2 ^ ℓ - 2 ^ ℓ := by
      rw [Nat.sub_mul, Nat.one_mul]
    have h3 := Nat.two_pow_pos ℓ
    have h4 : 2 ^ ℓ ≤ 2 ^ N * 2 ^ ℓ := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos N)
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨hlo, Nat.not_lt.mp fun hgt => ?_⟩
    -- `E ≥ 2^ℓ + 1` gives `(2^N - 1) * E ≥ (2^N - 1) * (2^ℓ + 1) ≥ 2^(N+ℓ)`.
    have hE : 2 ^ ℓ + 1 ≤ m * d - 2 ^ (N + ℓ) := by omega
    have h1 : (2 ^ N - 1) * (2 ^ ℓ + 1) ≤ (2 ^ N - 1) * (m * d - 2 ^ (N + ℓ)) :=
      Nat.mul_le_mul_left _ hE
    have h2 : (2 ^ N - 1) * (2 ^ ℓ + 1) = 2 ^ N * 2 ^ ℓ + 2 ^ N - 2 ^ ℓ - 1 := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      have h4 : 2 ^ ℓ ≤ 2 ^ N * 2 ^ ℓ := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos N)
      omega
    omega



/-! ### Signed multiply-shift -/

/-- The negative branch of the signed criterion, over the naturals: for
`1 ≤ y ≤ 2^K` and `2^(K+ℓ) < m * d ≤ 2^(K+ℓ) + 2^ℓ`,
`(y / d) * 2^(K+ℓ) < y * m ≤ (y / d + 1) * 2^(K+ℓ)`. -/
theorem signed_neg_bounds {K ℓ d m y : Nat}
    (hlo : 2 ^ (K + ℓ) < m * d) (hhi : m * d ≤ 2 ^ (K + ℓ) + 2 ^ ℓ)
    (hy1 : 1 ≤ y) (hy : y ≤ 2 ^ K) :
    y / d * 2 ^ (K + ℓ) < y * m ∧ y * m ≤ (y / d + 1) * 2 ^ (K + ℓ) := by
  have hd : 0 < d := pos_of_two_pow_le_mul (Nat.le_of_lt hlo)
  have hm : 0 < m := by
    refine Nat.pos_of_ne_zero fun h => ?_
    subst h; simp at hlo
  have hxd := Nat.div_add_mod y d
  have hr := Nat.mod_lt y hd
  generalize hq : y / d = q at hxd ⊢
  generalize hrr : y % d = r at hxd hr
  generalize hF : 2 ^ (K + ℓ) = F at hlo hhi ⊢
  have hFpos : 0 < F := by rw [← hF]; exact Nat.two_pow_pos _
  generalize hE : m * d - F = E
  have hmd : m * d = F + E := by omega
  constructor
  · -- `y * m ≥ q * (m * d) = q * F + q * E` and `y * m ≥ 1`.
    have h1 : q * (m * d) ≤ y * m := by
      calc q * (m * d) = (d * q) * m := by
            rw [Nat.mul_comm m d, ← Nat.mul_assoc, Nat.mul_comm q d]
        _ ≤ y * m := Nat.mul_le_mul_right m (by omega)
    have h2 : q * (m * d) = q * F + q * E := by rw [hmd, Nat.mul_add]
    have h3 : q ≤ q * E := Nat.le_mul_of_pos_right q (by omega)
    have h4 : 1 ≤ y * m := Nat.mul_pos hy1 hm
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0; simp; omega
    · omega
  · refine Nat.le_of_mul_le_mul_right (?_ : y * m * d ≤ (q + 1) * F * d) hd
    have hl : y * m * d = y * F + y * E := by rw [Nat.mul_assoc, hmd, Nat.mul_add]
    have hrgt : (q + 1) * F * d = y * F + (d - r) * F := by
      rw [Nat.mul_right_comm, ← Nat.add_mul]
      congr 1
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q d]; omega
    rw [hl, hrgt]
    have hyE : y * E ≤ F := by
      rw [← hF, Nat.pow_add]
      calc y * E ≤ 2 ^ K * E := Nat.mul_le_mul_right E hy
        _ ≤ 2 ^ K * 2 ^ ℓ := Nat.mul_le_mul_left _ (by omega)
    have h2 : F ≤ (d - r) * F := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- **Signed multiply-shift with negative-dividend correction.** If
`2^((N-1)+ℓ) < m * d ≤ 2^((N-1)+ℓ) + 2^ℓ`, then for every signed `N`-bit `x`,
`((x * m) >>> ((N-1)+ℓ)) + (if x < 0 then 1 else 0) = Int.tdiv x d`
(exact products, flooring arithmetic shift). -/
theorem sdivMagic_eq_tdiv_of_sandwich (N ℓ d m : Nat)
    (hlo : 2 ^ (N - 1 + ℓ) < m * d) (hhi : m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ) :
    ∀ x, SignedRange N x → sdivMagic m (N - 1 + ℓ) x = Int.tdiv x d := by
  intro x hx
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    rw [(signedRange_zero_iff x).mp hx]
    simp [sdivMagic, Int.zero_shiftRight, Int.zero_tdiv]
  have hd : 0 < d := pos_of_two_pow_le_mul (Nat.le_of_lt hlo)
  have hx' := (signedRange_iff_of_pos hN x).mp hx
  rw [← intCast_two_pow] at hx'
  unfold sdivMagic
  by_cases hneg : x < 0
  · simp only [hneg, ↓reduceIte]
    obtain ⟨y, rfl⟩ : ∃ y : Nat, x = -(y : Int) := ⟨(-x).toNat, by omega⟩
    have hy1 : 1 ≤ y := by omega
    have hy : y ≤ 2 ^ (N - 1) := by omega
    obtain ⟨b1, b2⟩ := signed_neg_bounds hlo hhi hy1 hy
    have hq := neg_ediv_of_bounds (Nat.two_pow_pos _) b1 b2
    rw [Int.shiftRight_eq_div_pow, Int.neg_mul, ← Int.natCast_mul, hq, Int.neg_tdiv,
      ← Int.ofNat_tdiv]
    omega
  · simp only [hneg, ↓reduceIte]
    obtain ⟨n, rfl⟩ : ∃ n : Nat, x = (n : Int) := ⟨x.toNat, by omega⟩
    have hn : n < 2 ^ (N - 1) := by omega
    have hc := mulShiftCorrect_of_sandwich (N - 1) ℓ d m (Nat.le_of_lt hlo) hhi n hn
    rw [Nat.shiftRight_eq_div_pow] at hc
    rw [natCast_mul_shiftRight, hc, ← Int.ofNat_tdiv]
    omega

theorem sdivMagicUncorrected_eq_sdivMagic_sub_one (m k : Nat) (x : Int) (hx : x < 0) :
    sdivMagicUncorrected m k x = sdivMagic m k x - 1 := by
  unfold sdivMagicUncorrected sdivMagic
  simp only [hx, ↓reduceIte]
  omega

/-- **Omitting the correction is off by one on every negative dividend.**
Under the same bounds, for every negative signed `N`-bit `x`, the uncorrected
sequence gives `Int.tdiv x d - 1`. -/
theorem sdivMagicUncorrected_eq_tdiv_sub_one_of_neg (N ℓ d m : Nat)
    (hlo : 2 ^ (N - 1 + ℓ) < m * d) (hhi : m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ) :
    ∀ x, SignedRange N x → x < 0 →
      sdivMagicUncorrected m (N - 1 + ℓ) x = Int.tdiv x d - 1 := by
  intro x hx hneg
  rw [sdivMagicUncorrected_eq_sdivMagic_sub_one _ _ _ hneg,
    sdivMagic_eq_tdiv_of_sandwich N ℓ d m hlo hhi x hx]

/-- **Existence of a signed multiplier.** For every `d ≥ 1`,
`signedMagic N d = ⌊2^((N-1) + clog2 d)/d⌋ + 1` satisfies the bounds of
`sdivMagic_eq_tdiv_of_sandwich` with `ℓ = clog2 d`. -/
theorem signedMagic_sandwich (N d : Nat) (hd : 0 < d) :
    2 ^ (N - 1 + clog2 d) < signedMagic N d * d ∧
      signedMagic N d * d ≤ 2 ^ (N - 1 + clog2 d) + 2 ^ clog2 d := by
  unfold signedMagic
  have hd_le := le_two_pow_clog2 hd
  have hdiv := Nat.div_add_mod (2 ^ (N - 1 + clog2 d)) d
  have hrem := Nat.mod_lt (2 ^ (N - 1 + clog2 d)) hd
  have hexp : (2 ^ (N - 1 + clog2 d) / d + 1) * d =
      d * (2 ^ (N - 1 + clog2 d) / d) + d := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm _ d]
  generalize (2 ^ (N - 1 + clog2 d) / d + 1) * d = P at hexp ⊢
  generalize d * (2 ^ (N - 1 + clog2 d) / d) = Q at hdiv hexp
  generalize 2 ^ (N - 1 + clog2 d) % d = r at hdiv hrem
  omega

/-! ### Overflow -/

/-- **The only signed-division overflow.** For a signed `N`-bit dividend `x`
and any integer divisor `d`, `Int.tdiv x d` is again a signed `N`-bit value
unless `x = -2^(N-1)` and `d = -1`. -/
theorem tdiv_signedRange_iff (N : Nat) (x d : Int) (hx : SignedRange N x) :
    SignedRange N (Int.tdiv x d) ↔ ¬ (x = -(2 : Int) ^ (N - 1) ∧ d = -1) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    rw [(signedRange_zero_iff x).mp hx, Int.zero_tdiv]
    have : SignedRange 0 0 := by decide
    simp only [this, true_iff]
    simp
  rw [signedRange_iff_of_pos hN]
  rw [signedRange_iff_of_pos hN] at hx
  have hM : (1 : Int) ≤ 2 ^ (N - 1) := by
    have : (0 : Int) < 2 ^ (N - 1) := Int.pow_pos (by decide)
    omega
  generalize (2 : Int) ^ (N - 1) = M at hx hM ⊢
  by_cases hd1 : d = -1
  · subst hd1
    rw [Int.tdiv_neg, Int.tdiv_one]
    omega
  by_cases hd0 : d = 0
  · subst hd0; rw [Int.tdiv_zero]; omega
  by_cases hd1' : d = 1
  · subst hd1'; rw [Int.tdiv_one]; omega
  -- `|d| ≥ 2`: `|x.tdiv d| = |x| / |d| ≤ |x| / 2`
  have hab := Int.natAbs_tdiv x d
  have hdabs : 2 ≤ d.natAbs := by omega
  have h2 : (x.tdiv d).natAbs * 2 ≤ x.natAbs := by
    rw [hab]
    calc x.natAbs.div d.natAbs * 2 ≤ x.natAbs.div d.natAbs * d.natAbs :=
          Nat.mul_le_mul_left _ hdabs
      _ ≤ x.natAbs := Nat.div_mul_le_self _ _
  omega

/-! ### Power-of-two divisors -/

/-- **Arithmetic shift versus truncating division.** For every integer `x`
and every `k`, `x >>> k = Int.tdiv x (2^k)` iff `x ≥ 0` or `2^k ∣ x`. -/
theorem int_shiftRight_eq_tdiv_iff (x : Int) (k : Nat) :
    x >>> k = Int.tdiv x (2 ^ k) ↔ (0 ≤ x ∨ (2 : Int) ^ k ∣ x) := by
  rw [Int.shiftRight_eq_div_pow, intCast_two_pow, Int.tdiv_eq_ediv]
  have hs : ((2 : Int) ^ k).sign = 1 := Int.sign_eq_one_of_pos (Int.pow_pos (by decide))
  split
  · rename_i h
    exact iff_of_true (by omega) h
  · rename_i h
    rw [hs]
    constructor
    · intro e; omega
    · intro e
      exact absurd e h

theorem biasSum_eq {N k : Nat} (hk : k ≤ N) (hN : 1 ≤ N) {x : Int} (hx : SignedRange N x) :
    biasSum N k x = x + (if x < 0 then (2 : Int) ^ k - 1 else 0) := by
  unfold biasSum
  rw [shiftRight_pred_of_signedRange hN hx]
  split
  · rw [lsrN_neg_one hk]
  · rw [lsrN_zero]

/-- **Bias-and-shift power-of-two division (total shifts).** For `k < N` and
every signed `N`-bit `x`, the biased dividend stays in the signed `N`-bit range
(no overflow) and `biasDiv N k x = Int.tdiv x (2^k)`. Shifts are Lean's total
shifts; at `k = 0` the logical shift count is `N` and the bias is `0` only
because a logical shift by `N` gives `0` here. -/
theorem biasDiv_eq_tdiv_of_lt (N k : Nat) (hk : k < N) (x : Int) (hx : SignedRange N x) :
    SignedRange N (biasSum N k x) ∧ biasDiv N k x = Int.tdiv x (2 ^ k) := by
  have hN : 1 ≤ N := by omega
  have hb := biasSum_eq (Nat.le_of_lt hk) hN hx
  have hx' := (signedRange_iff_of_pos hN x).mp hx
  have hkN : (2 : Int) ^ k ≤ 2 ^ (N - 1) := by
    rw [← intCast_two_pow, ← intCast_two_pow]
    exact Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))
  have hk1 : (1 : Int) ≤ 2 ^ k := by
    have : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
    omega
  refine ⟨?_, ?_⟩
  · rw [signedRange_iff_of_pos hN, hb]
    split <;> omega
  · unfold biasDiv
    rw [hb, Int.shiftRight_eq_div_pow, intCast_two_pow]
    have hP : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
    split
    · rename_i hneg
      obtain ⟨y, rfl⟩ : ∃ y : Nat, x = -(y : Int) := ⟨(-x).toNat, by omega⟩
      rw [Int.neg_tdiv, ← intCast_two_pow, ← Int.ofNat_tdiv,
        Int.ediv_eq_iff_of_pos (by exact_mod_cast Nat.two_pow_pos k)]
      have hyd := Nat.div_add_mod y (2 ^ k)
      have hyr := Nat.mod_lt y (Nat.two_pow_pos k)
      generalize y / 2 ^ k = Y at hyd ⊢
      generalize y % 2 ^ k = R at hyd hyr
      generalize hB : 2 ^ k = B at hyd hyr ⊢
      have c : (B : Int) * (Y : Int) = (Y : Int) * (B : Int) := Int.mul_comm _ _
      rw [Int.neg_mul]
      omega
    · rw [Int.add_zero, Int.tdiv_eq_ediv_of_nonneg (by omega)]

/-- With every shift count reduced modulo `N`, the sequence agrees with the
total-shift sequence when `1 ≤ k < N` (all counts are already below `N`). -/
theorem biasMasked_eq_of_pos_of_lt {N k : Nat} (hk1 : 1 ≤ k) (hk : k < N) (x : Int) :
    biasSumMasked N k x = biasSum N k x ∧ biasDivMasked N k x = biasDiv N k x := by
  have h1 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (N - k) % N = N - k := Nat.mod_eq_of_lt (by omega)
  have h3 : k % N = k := Nat.mod_eq_of_lt hk
  have hs : biasSumMasked N k x = biasSum N k x := by
    unfold biasSumMasked biasSum; rw [h1, h2]
  refine ⟨hs, ?_⟩
  unfold biasDivMasked biasDiv; rw [hs, h3]

/-- **Bias-and-shift power-of-two division (shift counts reduced modulo
`N`).** For `1 ≤ k < N` and every signed `N`-bit `x`, the sequence whose shift
counts are reduced modulo `N` keeps the biased dividend in range and computes
`Int.tdiv x (2^k)`. The bound `1 ≤ k` is tight
(`ce_biasDivMasked_k_zero`). -/
theorem biasDivMasked_eq_tdiv_of_pos_of_lt (N k : Nat) (hk1 : 1 ≤ k) (hk : k < N) (x : Int)
    (hx : SignedRange N x) :
    SignedRange N (biasSumMasked N k x) ∧ biasDivMasked N k x = Int.tdiv x (2 ^ k) := by
  obtain ⟨e1, e2⟩ := biasMasked_eq_of_pos_of_lt hk1 hk x
  rw [e1, e2]
  exact biasDiv_eq_tdiv_of_lt N k hk x hx

/-! ### Signed remainder -/

/-- **Signed remainder from the corrected quotient.** Under the signed bounds,
for every signed `N`-bit `x`, `sremMagic d m ((N-1)+ℓ) x = Int.tmod x d`; it
lies in `[0, d)` when `x ≥ 0` and in `(-d, 0]` when `x < 0` (the sign of the
dividend, or zero). -/
theorem sremMagic_eq_tmod_and_sign (N ℓ d m : Nat)
    (hlo : 2 ^ (N - 1 + ℓ) < m * d) (hhi : m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ) :
    ∀ x, SignedRange N x →
      sremMagic d m (N - 1 + ℓ) x = Int.tmod x d ∧
      (0 ≤ x → 0 ≤ sremMagic d m (N - 1 + ℓ) x ∧ sremMagic d m (N - 1 + ℓ) x < d) ∧
      (x < 0 → -(d : Int) < sremMagic d m (N - 1 + ℓ) x ∧ sremMagic d m (N - 1 + ℓ) x ≤ 0) := by
  intro x hx
  have hd : 0 < d := pos_of_two_pow_le_mul (Nat.le_of_lt hlo)
  have hd' : (0 : Int) < d := by omega
  have he : sremMagic d m (N - 1 + ℓ) x = Int.tmod x d := by
    unfold sremMagic
    rw [sdivMagic_eq_tdiv_of_sandwich N ℓ d m hlo hhi x hx, Int.tmod_def]
  rw [he]
  refine ⟨rfl, fun h0 => ⟨Int.tmod_nonneg _ h0, Int.tmod_lt_of_pos _ hd'⟩,
    fun h0 => ⟨Int.lt_tmod_of_pos _ hd', ?_⟩⟩
  obtain ⟨y, rfl⟩ : ∃ y : Nat, x = -(y : Int) := ⟨(-x).toNat, by omega⟩
  rw [Int.neg_tmod]
  have := Int.tmod_nonneg (d : Int) (Int.natCast_nonneg y)
  omega


/-! ### Further facts used in the cards -/

/-- **The low part of the textbook multiplier fits in `N` bits.** For
`1 ≤ d ≤ 2^(N+1)`, `unsignedMagic N d = 2^N + m'` with
`m' = unsignedMagic N d - 2^N < 2^N`. -/
theorem unsignedMagic_eq_two_pow_add_low (N d : Nat) (hd0 : 0 < d) (hd : d ≤ 2 ^ (N + 1)) :
    unsignedMagic N d = 2 ^ N + (unsignedMagic N d - 2 ^ N) ∧
      unsignedMagic N d - 2 ^ N < 2 ^ N := by
  have h1 := unsignedMagic_ge_two_pow_of_pos N d hd0
  have h2 := unsignedMagic_lt_two_pow_succ_of_le N d hd
  have hP : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by rw [Nat.pow_succ]; omega
  omega

/-- The sandwich form of the unsigned remainder result (a corollary of
`mulShift_rem_eq_mod_of_correct` and `mulShiftCorrect_of_sandwich`). -/
theorem mulShift_rem_eq_mod_of_sandwich (N ℓ d m : Nat)
    (hlo : 2 ^ (N + ℓ) ≤ m * d) (hhi : m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ) :
    ∀ x, x < 2 ^ N → x - d * ((x * m) >>> (N + ℓ)) = x % d :=
  mulShift_rem_eq_mod_of_correct N d m (N + ℓ) (mulShiftCorrect_of_sandwich N ℓ d m hlo hhi)

/-- The final shift `clog2 d - 1` of the fixup is below the word width `N`
when `2 ≤ d ≤ 2^N`. -/
theorem fixupQuot_shift_lt_width (N d : Nat) (hd : 2 ≤ d) (hdN : d ≤ 2 ^ N) :
    clog2 d - 1 < N := by
  have h1 := one_le_clog2 hd
  have h2 := clog2_le_of_le_two_pow hdN
  omega

/-- For `2^N < d ≤ 2^(N+1)` the final shift `clog2 d - 1` of the fixup equals
the word width `N`. -/
theorem fixupQuot_shift_eq_width (N d : Nat) (hd : 2 ^ N < d) (hdN : d ≤ 2 ^ (N + 1)) :
    clog2 d - 1 = N := by
  have h1 := succ_le_clog2_of_two_pow_lt hd
  have h2 := clog2_le_of_le_two_pow hdN
  omega

/-- For `d = 1` and `N ≥ 1`, no multiplier below `2^N` is correct at a shift
`s ≥ N` (it fails at the input `2^N - 1`). -/
theorem not_mulShiftCorrect_div_one_of_width_le (N m s : Nat) (hN : 1 ≤ N) (hm : m < 2 ^ N)
    (hs : N ≤ s) : ¬ MulShiftCorrect N 1 m s := by
  intro h
  have hx : 2 ^ N - 1 < 2 ^ N := by have := Nat.two_pow_pos N; omega
  have e := h (2 ^ N - 1) hx
  rw [Nat.div_one, Nat.shiftRight_eq_div_pow] at e
  have h2N : 2 ≤ 2 ^ N := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hN
    simpa using this
  have hlt : (2 ^ N - 1) * m / 2 ^ s < 2 ^ N - 1 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)]
    have hs' : 2 ^ N ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
    calc (2 ^ N - 1) * m < (2 ^ N - 1) * 2 ^ N :=
          Nat.mul_lt_mul_of_pos_left hm (by omega)
      _ ≤ (2 ^ N - 1) * 2 ^ s := Nat.mul_le_mul_left _ hs'
  omega

/-- The signed multiplier always exceeds `2^(N-1)`: as an `N`-bit pattern it
is never a positive signed value. -/
theorem two_pow_pred_lt_signedMagic (N d : Nat) (hd : 0 < d) : 2 ^ (N - 1) < signedMagic N d := by
  unfold signedMagic
  have hdc := le_two_pow_clog2 hd
  have : 2 ^ (N - 1) ≤ 2 ^ (N - 1 + clog2 d) / d := by
    rw [Nat.le_div_iff_mul_le hd, Nat.pow_add]
    exact Nat.mul_le_mul_left _ hdc
  omega

/-! ### Width of the textbook multiplier outside the ranges of `unsignedMagic_bounds` -/

/-- At `d = 0` the textbook multiplier is `0`, for every `N`. -/
theorem unsignedMagic_zero_right (N : Nat) : unsignedMagic N 0 = 0 := by
  simp [unsignedMagic, ceilDiv]

/-- For every `N` and every power of two `d = 2^k` (every `k`, including
`k ≥ N + 2`), the textbook multiplier is exactly `2^N`. -/
theorem unsignedMagic_two_pow (N k : Nat) : unsignedMagic N (2 ^ k) = 2 ^ N := by
  unfold unsignedMagic ceilDiv
  rw [clog2_two_pow, Nat.pow_add]
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  apply div_eq_of_bounds
  · omega
  · rw [Nat.add_mul, Nat.one_mul]; omega

/-- The bound `d ≤ 2^(N+1)` of `unsignedMagic_lt_two_pow_succ_of_le` cannot be
raised by one at any width: for every `N`, `d = 2^(N+1) + 1` gives
`unsignedMagic N d = 2^(N+1)`. -/
theorem unsignedMagic_two_pow_succ_add_one (N : Nat) :
    unsignedMagic N (2 ^ (N + 1) + 1) = 2 ^ (N + 1) := by
  have hP : 2 ≤ 2 ^ (N + 1) := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ N + 1)
    simpa using this
  have hclog : clog2 (2 ^ (N + 1) + 1) = N + 2 := by
    apply Nat.le_antisymm
    · apply clog2_le_of_le_two_pow
      have : 2 ^ (N + 2) = 2 * 2 ^ (N + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      omega
    · exact succ_le_clog2_of_two_pow_lt (by omega)
  unfold unsignedMagic ceilDiv
  rw [hclog]
  have hexp : 2 ^ (N + (N + 2)) = 2 ^ (N + 1) * 2 ^ (N + 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  apply div_eq_of_bounds
  · rw [hexp, Nat.mul_add, Nat.mul_one]
    generalize 2 ^ (N + 1) * 2 ^ (N + 1) = Q
    omega
  · rw [hexp, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
    generalize 2 ^ (N + 1) * 2 ^ (N + 1) = Q
    omega

/-- The converse of `unsignedMagic_lt_two_pow_succ_of_le` fails at every width:
for every `N` and every `k ≥ N + 2`, the divisor `d = 2^k` exceeds `2^(N+1)`,
yet `unsignedMagic N d = 2^N < 2^(N+1)`. -/
theorem unsignedMagic_lt_two_pow_succ_converse_fails (N k : Nat) (hk : N + 2 ≤ k) :
    2 ^ (N + 1) < 2 ^ k ∧ unsignedMagic N (2 ^ k) < 2 ^ (N + 1) := by
  refine ⟨Nat.pow_lt_pow_right (by decide) (by omega), ?_⟩
  rw [unsignedMagic_two_pow]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- Divisors above `2^(N+1)` that are not powers of two can also give a
multiplier below `2^(N+1)`: `N = 1, d = 6`; `N = 8, d = 768 = 3 * 2^8`;
`N = 32, d = 3 * 2^32`. -/
theorem unsignedMagic_lt_two_pow_succ_above_examples :
    (2 ^ (1 + 1) < 6 ∧ unsignedMagic 1 6 < 2 ^ (1 + 1)) ∧
    (2 ^ (8 + 1) < 768 ∧ unsignedMagic 8 768 < 2 ^ (8 + 1)) ∧
    (2 ^ (32 + 1) < 3 * 2 ^ 32 ∧ unsignedMagic 32 (3 * 2 ^ 32) < 2 ^ (32 + 1)) := by
  decide

/-! ### Edge cases of the single-word candidate -/

/-- At `d = 0` the single-word candidate multiplier is `0`, for every `N`. -/
theorem singleWordMagic_zero_right (N : Nat) : singleWordMagic N 0 = 0 := by
  simp [singleWordMagic, ceilDiv]

/-- At `d = 1` the single-word candidate shift is `N - 1` (truncated: `0` at
`N = 0`). -/
theorem singleWordShift_one (N : Nat) : singleWordShift N 1 = N - 1 := by
  simp [singleWordShift, clog2]

/-- For every non-power-of-two `d` with `1 ≤ d < 2^N`, the single-word
candidate exceeds `2^(N-1)`. -/
theorem two_pow_pred_lt_singleWordMagic (N d : Nat)
    (hd : 1 ≤ d) (hdN : d < 2 ^ N) (hnpow : ∀ k : Nat, d ≠ 2 ^ k) :
    2 ^ (N - 1) < singleWordMagic N d := by
  have hd_ne1 : d ≠ 1 := fun h => hnpow 0 (by simpa using h)
  have hd2 : 2 ≤ d := by omega
  have hd_ne2 : d ≠ 2 := fun h => hnpow 1 (by simpa using h)
  have hd3 : 3 ≤ d := by omega
  have hN2 : 2 ≤ N :=
    Nat.not_lt.mp fun hlt => by
      have : 2 ^ N ≤ 2 := by
        rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl <;> decide
      omega
  have hc1 : 1 ≤ clog2 d := one_le_clog2 hd2
  have hd_lt_pow : d < 2 ^ clog2 d := by
    have hle := le_two_pow_clog2 (by omega : 0 < d)
    exact Nat.lt_of_le_of_ne hle (hnpow (clog2 d))
  unfold singleWordMagic singleWordShift ceilDiv
  have hshift : N + clog2 d - 1 = (N - 1) + clog2 d := by omega
  rw [hshift, Nat.pow_add]
  have hmul : 2 ^ (N - 1) * d < 2 ^ (N - 1) * 2 ^ clog2 d :=
    Nat.mul_lt_mul_of_pos_left hd_lt_pow (Nat.two_pow_pos (N - 1))
  have hdiv : 2 ^ (N - 1) + 1 ≤ (2 ^ (N - 1) * 2 ^ clog2 d + d - 1) / d := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < d), Nat.add_mul, Nat.one_mul]
    omega
  omega

/-! ### The fixup's final shift -/

/-- Among divisors `d ≥ 2`, the final shift `clog2 d - 1` of the fixup is below
the word width `N` exactly when `d ≤ 2^N`. -/
theorem fixupQuot_shift_lt_width_iff (N d : Nat) (hd : 2 ≤ d) :
    clog2 d - 1 < N ↔ d ≤ 2 ^ N := by
  refine ⟨fun hlt => Nat.not_lt.mp fun hgt => ?_, fixupQuot_shift_lt_width N d hd⟩
  have := succ_le_clog2_of_two_pow_lt hgt
  omega

end Toy.MagicDiv
