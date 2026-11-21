/-
Toy.FloatTier.Arith
===================

Fully proved arithmetic facts about the rounding machinery of
`Toy.FloatTier.Base` (`bitLen`, `rneDiv`, `roundUnits`, `mkFin`, `unitsOf`).

Provenance: verbatim copy, with the namespace renamed from `Toy.Float` to
`Toy.FloatTier` and the import adjusted, of lines 14-423 of
`lean/Toy/Float/Arith.lean` in the published package
`floating-point-algebraic-laws-reassociation-contraction-signed-zero-and-nan`
(sha256 of that file:
`251fabd61223d15ee0b72525c4f97e889a7fa1a6051981cfa7d91b02a040eec1`).
These are auxiliary lemmas; none of them is a main theorem of the package.
-/
import Toy.FloatTier.Base

namespace Toy.FloatTier

/-! ### Powers of two -/

theorem lt_two_pow_self' : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by have := lt_two_pow_self' n; rw [Nat.pow_succ]; omega

theorem one_le_two_pow (n : Nat) : 1 ≤ 2 ^ n := Nat.two_pow_pos n

theorem two_pow_le_two_pow {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

theorem two_pow_lt_two_pow {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b :=
  Nat.pow_lt_pow_right (by decide) h

/-! ### `bitLen` -/

theorem bitLenAux_zero : ∀ k : Nat, bitLenAux k 0 = 0
  | 0 => rfl
  | _ + 1 => by simp [bitLenAux]

theorem bitLenAux_eq (j : Nat) : ∀ (k n : Nat), 2 ^ j ≤ n → n < 2 ^ (j + 1) → j < k →
    bitLenAux k n = j + 1 := by
  induction j with
  | zero =>
    intro k n h1 h2 hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have : n = 1 := by simp at h1 h2; omega
    subst this; simp [bitLenAux, bitLenAux_zero]
  | succ j ih =>
    intro k n h1 h2 hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hp := Nat.two_pow_pos j
    rw [Nat.pow_succ] at h1
    rw [Nat.pow_succ, Nat.pow_succ] at h2
    have hn : n ≠ 0 := by omega
    simp only [bitLenAux, hn, ite_false]
    rw [ih k (n / 2) (by omega) (by rw [Nat.pow_succ]; omega) (by omega)]

/-- `bitLen n` is `j + 1` for `2^j ≤ n < 2^(j+1)`. -/
theorem bitLen_eq {j n : Nat} (h1 : 2 ^ j ≤ n) (h2 : n < 2 ^ (j + 1)) : bitLen n = j + 1 :=
  bitLenAux_eq j n n h1 h2 (Nat.lt_of_lt_of_le (lt_two_pow_self' j) h1)

theorem bitLen_zero : bitLen 0 = 0 := rfl

theorem bitLen_spec {n : Nat} (hn : 0 < n) :
    2 ^ (bitLen n - 1) ≤ n ∧ n < 2 ^ bitLen n := by
  rw [bitLen_eq (Nat.log2_self_le (by omega)) Nat.lt_log2_self]
  exact ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

theorem bitLen_pos {n : Nat} (hn : 0 < n) : 0 < bitLen n := by
  rw [bitLen_eq (Nat.log2_self_le (by omega)) Nat.lt_log2_self]; omega

theorem bitLen_le_of_lt {n k : Nat} (h : n < 2 ^ k) : bitLen n ≤ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bitLen_zero]
  · have := (bitLen_spec hn).1
    have h2 : 2 ^ (bitLen n - 1) < 2 ^ k := Nat.lt_of_le_of_lt this h
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
    omega

theorem le_bitLen_of_le {n k : Nat} (h : 2 ^ k ≤ n) : k + 1 ≤ bitLen n := by
  have hn : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos k) h
  have := (bitLen_spec hn).2
  have h2 : 2 ^ k < 2 ^ bitLen n := Nat.lt_of_le_of_lt h this
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
  omega

theorem bitLen_mul_two_pow {m : Nat} (hm : 0 < m) (t : Nat) :
    bitLen (m * 2 ^ t) = bitLen m + t := by
  obtain ⟨h1, h2⟩ := bitLen_spec hm
  have hb := bitLen_pos hm
  rw [show bitLen m + t = bitLen m - 1 + t + 1 by omega]
  apply bitLen_eq
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  · rw [show bitLen m - 1 + t + 1 = bitLen m + t by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos t)

/-! ### `rneDiv` -/

theorem rneDiv_mul_pow (q d : Nat) : rneDiv (q * 2 ^ d) d = q := by
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have hmod : (q * 2 ^ d) % 2 ^ d = 0 := Nat.mul_mod_left q (2 ^ d)
  have hdiv : (q * 2 ^ d) / 2 ^ d = q := Nat.mul_div_left q hpos
  unfold rneDiv
  simp only [hmod, hdiv, Nat.mul_zero]
  split
  · rename_i h; omega
  · rfl

theorem rneDiv_zero_right (m : Nat) : rneDiv m 0 = m := by
  simpa using rneDiv_mul_pow m 0

theorem rneDiv_mul_pow_add (m d t : Nat) : rneDiv (m * 2 ^ d) (d + t) = rneDiv m t := by
  have hd : 0 < 2 ^ d := Nat.two_pow_pos d
  have ht : 0 < 2 ^ t := Nat.two_pow_pos t
  have hsplit : 2 ^ (d + t) = 2 ^ t * 2 ^ d := by rw [Nat.pow_add, Nat.mul_comm]
  unfold rneDiv
  simp only [hsplit]
  rw [Nat.mul_div_mul_right _ _ hd, Nat.mul_mod_mul_right]
  have e1 : (2 * (m % 2 ^ t * 2 ^ d) > 2 ^ t * 2 ^ d) ↔ (2 * (m % 2 ^ t) > 2 ^ t) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_right hd
  have e2 : (2 * (m % 2 ^ t * 2 ^ d) = 2 ^ t * 2 ^ d) ↔ (2 * (m % 2 ^ t) = 2 ^ t) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_left_inj (by omega)
  simp only [e1, e2]

theorem rneDiv_ge (m d : Nat) : m / 2 ^ d ≤ rneDiv m d := by
  unfold rneDiv; dsimp only; split <;> omega

theorem rneDiv_le (m d : Nat) : rneDiv m d ≤ m / 2 ^ d + 1 := by
  unfold rneDiv; dsimp only; split <;> omega

/-! ### Representable magnitudes and `roundUnits` -/

/-- `n` units is a magnitude with at most `p` significant bits (no exponent
bound). -/
def IsRepr (f : Fmt) (n : Nat) : Prop := ∃ m t, m < 2 ^ f.p ∧ n = m * 2 ^ t

theorem IsRepr.mul_two_pow {f : Fmt} {n : Nat} (h : IsRepr f n) (k : Nat) :
    IsRepr f (n * 2 ^ k) := by
  obtain ⟨m, t, hm, rfl⟩ := h
  exact ⟨m, t + k, hm, by rw [Nat.pow_add, Nat.mul_assoc]⟩

theorem isRepr_of_lt {f : Fmt} {n : Nat} (h : n < 2 ^ f.p) : IsRepr f n :=
  ⟨n, 0, h, by simp⟩

theorem isRepr_two_pow (f : Fmt) (k : Nat) : IsRepr f (2 ^ k) :=
  ⟨1, k, Nat.one_lt_two_pow (by have := f.two_le_p; omega), by simp⟩

theorem roundUnits_zero (f : Fmt) (d : Nat) : roundUnits f 0 d = 0 := by
  unfold roundUnits rneDiv; simp [bitLen_zero]

/-- Rounding a representable magnitude (given exactly, at any scale `2^d`)
returns it. -/
theorem roundUnits_repr {f : Fmt} {n : Nat} (h : IsRepr f n) (d : Nat) :
    roundUnits f (n * 2 ^ d) d = n := by
  obtain ⟨m, t, hm, rfl⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp [roundUnits_zero]
  have hb : bitLen m ≤ f.p := bitLen_le_of_lt hm
  have hd : 0 < 2 ^ d := Nat.two_pow_pos d
  unfold roundUnits
  dsimp only
  rw [Nat.mul_div_cancel _ hd, bitLen_mul_two_pow hm0]
  obtain ⟨s, hs⟩ : ∃ s, t = (bitLen m + t - f.p) + s := ⟨t - (bitLen m + t - f.p), by omega⟩
  generalize bitLen m + t - f.p = u at hs ⊢
  subst hs
  have : m * 2 ^ (u + s) * 2 ^ d = (m * 2 ^ s) * 2 ^ (d + u) := by
    simp only [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [this, rneDiv_mul_pow, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm s u]

theorem roundUnits_repr0 {f : Fmt} {n : Nat} (h : IsRepr f n) : roundUnits f n 0 = n := by
  simpa using roundUnits_repr h 0

/-- Scaling the exact value by `2^d` and the denominator by `2^d` does not
change the rounded magnitude. -/
theorem roundUnits_mul_pow (f : Fmt) (m d : Nat) : roundUnits f (m * 2 ^ d) d = roundUnits f m 0 := by
  have hd : 0 < 2 ^ d := Nat.two_pow_pos d
  unfold roundUnits
  dsimp only
  rw [Nat.mul_div_cancel _ hd, Nat.pow_zero, Nat.div_one, Nat.zero_add, rneDiv_mul_pow_add]

theorem roundUnits_pos {f : Fmt} {m : Nat} (hm : 0 < m) : 0 < roundUnits f m 0 := by
  unfold roundUnits
  dsimp only
  simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add]
  have hge := rneDiv_ge m (bitLen m - f.p)
  have hs := (bitLen_spec hm).1
  have hp := f.two_le_p
  have : 1 ≤ m / 2 ^ (bitLen m - f.p) := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.one_mul]
    exact Nat.le_trans (two_pow_le_two_pow (by omega)) hs
  exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)

/-- The rounded magnitude is representable. -/
theorem roundUnits_isRepr (f : Fmt) (m d : Nat) : IsRepr f (roundUnits f m d) := by
  unfold roundUnits
  dsimp only
  generalize ht : bitLen (m / 2 ^ d) - f.p = t
  -- rneDiv m (d + t) ≤ m / 2^(d+t) + 1 and m / 2^(d+t) < 2^p (when t > 0) or ≤ 2^p - 1.
  have hq : m / 2 ^ (d + t) < 2 ^ f.p := by
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
    rcases Nat.eq_zero_or_pos (m / 2 ^ d) with h0 | hpos
    · rw [h0]; simp; exact Nat.two_pow_pos _
    · have := (bitLen_spec hpos).2
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      exact Nat.lt_of_lt_of_le this (two_pow_le_two_pow (by omega))
  have hle := rneDiv_le m (d + t)
  by_cases hlt : rneDiv m (d + t) < 2 ^ f.p
  · exact ⟨_, t, hlt, rfl⟩
  · have heq : rneDiv m (d + t) = 2 ^ f.p := by omega
    refine ⟨1, f.p + t, Nat.one_lt_two_pow (by have := f.two_le_p; omega), ?_⟩
    rw [heq, Nat.pow_add, Nat.one_mul]

/-! ### Formats -/

theorem Fmt.one_le_bias (f : Fmt) : 1 ≤ f.bias := by
  unfold Fmt.bias
  have : 2 ≤ 2 ^ (f.e - 1) :=
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (f.e - 1) := two_pow_le_two_pow (by have := f.two_le_e; omega)
  omega

theorem Fmt.two_pow_e_eq (f : Fmt) : 2 ^ f.e = 2 * f.bias + 2 := by
  unfold Fmt.bias
  have h : 2 ^ f.e = 2 * 2 ^ (f.e - 1) := by
    conv => lhs; rw [show f.e = (f.e - 1) + 1 by have := f.two_le_e; omega, Nat.pow_succ]
    omega
  have : 2 ≤ 2 ^ (f.e - 1) :=
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (f.e - 1) := two_pow_le_two_pow (by have := f.two_le_e; omega)
  omega

theorem Fmt.expCount_eq (f : Fmt) : f.expCount = 2 * f.bias + 1 := by
  unfold Fmt.expCount; have := f.two_pow_e_eq; omega

theorem Fmt.two_pow_p_eq (f : Fmt) : 2 ^ f.p = 2 * f.fracCount := by
  unfold Fmt.fracCount
  conv => lhs; rw [show f.p = (f.p - 1) + 1 by have := f.two_le_p; omega, Nat.pow_succ]
  omega

theorem Fmt.two_le_fracCount (f : Fmt) : 2 ≤ f.fracCount := by
  unfold Fmt.fracCount
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (f.p - 1) := two_pow_le_two_pow (by have := f.two_le_p; omega)

/-- `maxUnits = (2^p - 1) * 2^(2 * bias - 1)`. -/
theorem Fmt.maxUnits_eq (f : Fmt) : f.maxUnits = (2 ^ f.p - 1) * 2 ^ (2 * f.bias - 1) := by
  unfold Fmt.maxUnits; rw [f.two_pow_e_eq]; congr 2 <;> omega

theorem Fmt.maxUnits_isRepr (f : Fmt) : IsRepr f f.maxUnits :=
  ⟨2 ^ f.p - 1, 2 * f.bias - 1, by have := Nat.two_pow_pos f.p; omega, f.maxUnits_eq⟩

theorem Fmt.maxUnits_lt (f : Fmt) : f.maxUnits < 2 ^ (f.p + (2 * f.bias - 1)) := by
  rw [f.maxUnits_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right (by have := Nat.two_pow_pos f.p; omega) (Nat.two_pow_pos _)

theorem Fmt.fracCount_le_maxUnits (f : Fmt) : f.fracCount ≤ f.maxUnits := by
  rw [f.maxUnits_eq, f.two_pow_p_eq]
  have h1 := one_le_two_pow (2 * f.bias - 1)
  have h2 := f.two_le_fracCount
  calc f.fracCount ≤ (2 * f.fracCount - 1) * 1 := by omega
    _ ≤ _ := Nat.mul_le_mul_left _ h1

/-! ### `unitsOf` and field decoding -/

theorem unitsOf_zero_left (f : Fmt) (M : Nat) : unitsOf f 0 M = M := by simp [unitsOf]

theorem unitsOf_succ (f : Fmt) (E M : Nat) :
    unitsOf f (E + 1) M = (f.fracCount + M) * 2 ^ E := by simp [unitsOf]

theorem unitsOf_eq_zero_iff (f : Fmt) (E M : Nat) : unitsOf f E M = 0 ↔ E = 0 ∧ M = 0 := by
  rcases E with _ | E
  · simp [unitsOf]
  · rw [unitsOf_succ]
    have := f.fracCount_pos
    have := Nat.two_pow_pos E
    constructor
    · intro h; exfalso
      have : 0 < (f.fracCount + M) * 2 ^ E := Nat.mul_pos (by omega) (by omega)
      omega
    · intro h; omega

theorem unitsOf_isRepr (f : Fmt) {E M : Nat} (hM : M < f.fracCount) : IsRepr f (unitsOf f E M) := by
  rcases E with _ | E
  · rw [unitsOf_zero_left]; exact isRepr_of_lt (by have := f.two_pow_p_eq; omega)
  · rw [unitsOf_succ]
    exact ⟨_, E, by have := f.two_pow_p_eq; omega, rfl⟩

theorem unitsOf_le_maxUnits (f : Fmt) {E M : Nat} (hE : E < f.expCount) (hM : M < f.fracCount) :
    unitsOf f E M ≤ f.maxUnits := by
  rcases E with _ | E
  · rw [unitsOf_zero_left]; have := f.fracCount_le_maxUnits; omega
  · rw [unitsOf_succ, f.maxUnits_eq]
    have hE' : E ≤ 2 * f.bias - 1 := by have := f.expCount_eq; omega
    apply Nat.mul_le_mul
    · have := f.two_pow_p_eq; omega
    · exact two_pow_le_two_pow hE'

theorem isRepr_dvd {f : Fmt} {n : Nat} (hr : IsRepr f n) (hn : 0 < n) :
    2 ^ (bitLen n - f.p) ∣ n := by
  obtain ⟨m, t, hm, rfl⟩ := hr
  have hm0 : 0 < m := by rcases Nat.eq_zero_or_pos m with h | h <;> simp_all
  rw [bitLen_mul_two_pow hm0]
  have := bitLen_le_of_lt hm
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : bitLen m + t - f.p ≤ t)) (Nat.dvd_mul_left _ _)

/-- Decoding of a representable in-range magnitude. -/
theorem decode_spec {f : Fmt} {n : Nat} (hr : IsRepr f n) (hn : n ≤ f.maxUnits) :
    decodeE f n < f.expCount ∧ decodeM f n < f.fracCount ∧
      unitsOf f (decodeE f n) (decodeM f n) = n := by
  by_cases hlt : n < f.fracCount
  · have hE : decodeE f n = 0 := by simp [decodeE, hlt]
    have hM : decodeM f n = n := by simp [decodeM, hlt]
    rw [hE, hM, unitsOf_zero_left]; exact ⟨f.expCount_pos, hlt, rfl⟩
  · simp only [decodeE, decodeM, hlt, ite_false]
    have hF := f.two_pow_p_eq
    have hFpos := f.two_le_fracCount
    have hp2 := f.two_le_p
    have hn0 : 0 < n := by omega
    obtain ⟨hs1, hs2⟩ := bitLen_spec hn0
    have hbp : f.p ≤ bitLen n := by
      have h := le_bitLen_of_le (n := n) (k := f.p - 1) (by unfold Fmt.fracCount at hlt; omega)
      omega
    have hbmax : bitLen n ≤ f.p + (2 * f.bias - 1) :=
      bitLen_le_of_lt (Nat.lt_of_le_of_lt hn f.maxUnits_lt)
    obtain ⟨q, hq⟩ := isRepr_dvd hr hn0
    generalize bitLen n = b at *
    subst hq
    have hk : 2 ^ (b - 1) = 2 ^ (f.p - 1) * 2 ^ (b - f.p) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hk2 : 2 ^ b = 2 ^ f.p * 2 ^ (b - f.p) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    have hq1 : f.fracCount ≤ q := by
      rw [hk, Nat.mul_comm (2 ^ (b - f.p))] at hs1
      unfold Fmt.fracCount; exact Nat.le_of_mul_le_mul_right hs1 (Nat.two_pow_pos _)
    have hq2 : q < 2 ^ f.p := by
      rw [hk2, Nat.mul_comm (2 ^ (b - f.p))] at hs2
      exact Nat.lt_of_mul_lt_mul_right hs2
    refine ⟨?_, ?_, ?_⟩
    · have := f.expCount_eq; have := f.one_le_bias; omega
    · omega
    · rw [unitsOf_succ, show f.fracCount + (q - f.fracCount) = q by omega, Nat.mul_comm]

/-- `mkFin` of a representable in-range magnitude is a finite value with that
magnitude (and the requested sign; the fields do not depend on the sign). -/
theorem mkFin_repr {f : Fmt} {n : Nat} (hr : IsRepr f n) (hn : n ≤ f.maxUnits) :
    ∃ E : Fin f.expCount, ∃ M : Fin f.fracCount,
      (∀ s, mkFin f s n = .fin s E M) ∧ unitsOf f E.val M.val = n := by
  obtain ⟨hE, hM, hu⟩ := decode_spec hr hn
  refine ⟨⟨decodeE f n, hE⟩, ⟨decodeM f n, hM⟩, fun s => ?_, hu⟩
  unfold mkFin
  simp only [Nat.not_lt.mpr hn, ite_false, Nat.mod_eq_of_lt hE, Nat.mod_eq_of_lt hM]

theorem mkFin_overflow {f : Fmt} {n : Nat} (hn : f.maxUnits < n) (s : Bool) : mkFin f s n = .inf s := by
  unfold mkFin; simp [hn]

theorem decode_unitsOf (f : Fmt) (E : Fin f.expCount) (M : Fin f.fracCount) :
    decodeE f (unitsOf f E.val M.val) = E.val ∧ decodeM f (unitsOf f E.val M.val) = M.val := by
  rcases hEv : E.val with _ | E0
  · rw [unitsOf_zero_left]; simp [decodeE, decodeM, M.isLt]
  · rw [unitsOf_succ]
    have hF := f.two_pow_p_eq
    have hM2 := M.isLt
    have hFp := f.two_le_fracCount
    have hp2 := f.two_le_p
    have hge : f.fracCount ≤ (f.fracCount + M.val) * 2 ^ E0 :=
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    have hnlt : ¬ ((f.fracCount + M.val) * 2 ^ E0 < f.fracCount) := Nat.not_lt.mpr hge
    have hb : bitLen ((f.fracCount + M.val) * 2 ^ E0) = f.p + E0 := by
      rw [bitLen_mul_two_pow (by omega)]
      congr 1
      rw [show f.p = f.p - 1 + 1 by omega]
      apply bitLen_eq
      · unfold Fmt.fracCount; omega
      · rw [show f.p - 1 + 1 = f.p by omega]; omega
    simp only [decodeE, decodeM, hnlt, ite_false, hb]
    refine ⟨by omega, ?_⟩
    rw [show f.p + E0 - f.p = E0 by omega, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    omega

/-- Rebuilding a finite value from its sign and magnitude returns it. -/
theorem mkFin_fields (f : Fmt) (s : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) :
    mkFin f s (unitsOf f E.val M.val) = .fin s E M := by
  have key := decode_unitsOf f E M
  unfold mkFin
  simp only [Nat.not_lt.mpr (unitsOf_le_maxUnits f E.isLt M.isLt), ite_false, key.1, key.2,
    Nat.mod_eq_of_lt E.isLt, Nat.mod_eq_of_lt M.isLt]

theorem mkFin_units (x : FP f) (hx : x.isFinite = true) : mkFin f x.signBit x.units = x := by
  cases x with
  | nan => simp [FP.isFinite] at hx
  | inf s => simp [FP.isFinite] at hx
  | fin s E M => exact mkFin_fields f s E M

/-! ### `round` -/

theorem round_repr {f : Fmt} {n : Nat} (hr : IsRepr f n) (s : Bool) (d : Nat) :
    round f s (n * 2 ^ d) d = mkFin f s n := by
  unfold round; rw [roundUnits_repr hr]

theorem round_units (x : FP f) (hx : x.isFinite = true) (d : Nat) :
    round f x.signBit (x.units * 2 ^ d) d = x := by
  cases x with
  | nan => simp [FP.isFinite] at hx
  | inf s => simp [FP.isFinite] at hx
  | fin s E M =>
    simp only [FP.units, FP.signBit]
    rw [round_repr (unitsOf_isRepr f M.isLt), mkFin_fields]

/-- A nonzero exact value never rounds to a zero. -/
theorem round_ne_zero {f : Fmt} {m : Nat} (hm : 0 < m) (s s' : Bool) : round f s m 0 ≠ zero f s' := by
  unfold round
  have hpos := roundUnits_pos (f := f) hm
  by_cases hov : f.maxUnits < roundUnits f m 0
  · rw [mkFin_overflow hov]; simp [zero]
  · obtain ⟨E, M, h, hu⟩ := mkFin_repr (roundUnits_isRepr f m 0) (Nat.not_lt.mp hov)
    rw [h s]
    intro hz
    simp only [zero, FP.fin.injEq] at hz
    obtain ⟨_, hE, hM⟩ := hz
    subst hE hM
    simp [unitsOf] at hu
    omega

theorem neg_mkFin (f : Fmt) (s : Bool) (n : Nat) : (mkFin f s n).neg = mkFin f (!s) n := by
  unfold mkFin; split <;> rfl

theorem neg_round (f : Fmt) (s : Bool) (m d : Nat) : (round f s m d).neg = round f (!s) m d := by
  unfold round; exact neg_mkFin f s _

end Toy.FloatTier
