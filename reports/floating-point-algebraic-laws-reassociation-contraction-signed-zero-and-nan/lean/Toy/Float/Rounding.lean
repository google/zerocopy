/-
Toy.Float.Rounding
==================

Auxiliary facts about RNE rounding used to prove the accuracy and
double-rounding statements of `Toy.Float.Statements`: the nearest property of
`rneDiv` and `roundUnits`, a characterization of `rneDiv` by distance, the
"far from every midpoint" criterion for innocuous double rounding, and the
format-conversion facts behind `addVia` and `mulVia`. Nothing here is a result
card; these are auxiliary lemmas.
-/
import Toy.Float.Props

namespace Toy.Float

/-! ### Powers of two -/

theorem two_pow_split {a b : Nat} (h : a ≤ b) : 2 ^ b = 2 ^ (b - a) * 2 ^ a := by
  rw [← Nat.pow_add]; congr 1; omega

theorem add_one_mul' (a b : Nat) : (a + 1) * b = a * b + b := Nat.succ_mul a b

theorem two_pow_succ' (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- Two multiples of `D` closer than `D` are equal. -/
theorem eq_of_mul_close {u v D : Nat} (hD : 0 < D)
    (h : (((u * D : Nat) : Int) - ((v * D : Nat) : Int)).natAbs < D) : u = v := by
  rcases Nat.lt_trichotomy u v with huv | huv | huv
  · have : (u + 1) * D ≤ v * D := Nat.mul_le_mul_right _ huv
    rw [add_one_mul'] at this
    omega
  · exact huv
  · have : (v + 1) * D ≤ u * D := Nat.mul_le_mul_right _ huv
    rw [add_one_mul'] at this
    omega

/-! ### `rneDiv`: nearest property, error bound, characterization -/

/-- `rneDiv m e * 2^e` is at least as close to `m` as every multiple of `2^e`. -/
theorem rneDiv_nearest (m e k : Nat) :
    (((rneDiv m e * 2 ^ e : Nat) : Int) - (m : Int)).natAbs ≤
      (((k * 2 ^ e : Nat) : Int) - (m : Int)).natAbs := by
  unfold rneDiv
  dsimp only
  have hD : 0 < 2 ^ e := Nat.two_pow_pos e
  have hm := Nat.div_add_mod m (2 ^ e)
  have hr := Nat.mod_lt m hD
  generalize m / 2 ^ e = q at hm ⊢
  generalize m % 2 ^ e = r at hm hr ⊢
  generalize 2 ^ e = D at *
  subst hm
  have hqD : D * q = q * D := Nat.mul_comm _ _
  rcases Nat.lt_or_ge k (q + 1) with hk | hk
  · have h1 : k * D ≤ q * D := Nat.mul_le_mul_right _ (by omega)
    split
    · rw [add_one_mul']; omega
    · omega
  · have h1 : (q + 1) * D ≤ k * D := Nat.mul_le_mul_right _ hk
    rw [add_one_mul'] at h1
    split
    · rw [add_one_mul']; omega
    · omega

/-- Error bound: `rneDiv m e * 2^e` is within `2^e / 2` of `m`. -/
theorem rneDiv_err (m e : Nat) :
    2 * (((rneDiv m e * 2 ^ e : Nat) : Int) - (m : Int)).natAbs ≤ 2 ^ e := by
  unfold rneDiv
  dsimp only
  have hD : 0 < 2 ^ e := Nat.two_pow_pos e
  have hm := Nat.div_add_mod m (2 ^ e)
  have hr := Nat.mod_lt m hD
  generalize m / 2 ^ e = q at hm ⊢
  generalize m % 2 ^ e = r at hm hr ⊢
  generalize 2 ^ e = D at *
  subst hm
  have hqD : D * q = q * D := Nat.mul_comm _ _
  split
  · rw [add_one_mul' q D]; omega
  · omega

/-- A value strictly closer than `2^e / 2` to `m` is `rneDiv m e`. -/
theorem rneDiv_eq_of_close {m e n : Nat}
    (h : 2 * (((n * 2 ^ e : Nat) : Int) - (m : Int)).natAbs < 2 ^ e) : rneDiv m e = n := by
  unfold rneDiv
  dsimp only
  have hD : 0 < 2 ^ e := Nat.two_pow_pos e
  have hm := Nat.div_add_mod m (2 ^ e)
  have hr := Nat.mod_lt m hD
  generalize m / 2 ^ e = q at hm ⊢
  generalize m % 2 ^ e = r at hm hr ⊢
  generalize 2 ^ e = D at *
  subst hm
  have hqD : D * q = q * D := Nat.mul_comm _ _
  rcases Nat.lt_or_ge n q with hnq | hnq
  · have h1 : (n + 1) * D ≤ q * D := Nat.mul_le_mul_right _ hnq
    rw [add_one_mul'] at h1
    omega
  rcases Nat.lt_or_ge (q + 1) n with hnq2 | hnq2
  · have h1 : (q + 1 + 1) * D ≤ n * D := Nat.mul_le_mul_right _ hnq2
    rw [add_one_mul', add_one_mul'] at h1
    omega
  rcases Nat.eq_or_lt_of_le hnq with rfl | hnq
  · split
    · rename_i hc; omega
    · rfl
  · obtain rfl : n = q + 1 := by omega
    rw [add_one_mul' q D] at h
    split
    · rfl
    · rename_i hc; omega

/-! ### Nearest property of `roundUnits` -/

theorem isRepr_zero (f : Fmt) : IsRepr f 0 := ⟨0, 0, Nat.two_pow_pos _, by simp⟩

/-- `roundUnits f m d` is a representable magnitude nearest to `m / 2^d`: every
representable magnitude `n` (any exponent) is at least as far away. -/
theorem roundUnits_nearest (f : Fmt) (m d n : Nat) (hn : IsRepr f n) :
    (((roundUnits f m d * 2 ^ d : Nat) : Int) - (m : Int)).natAbs ≤
      (((n * 2 ^ d : Nat) : Int) - (m : Int)).natAbs := by
  unfold roundUnits
  dsimp only
  generalize hL : bitLen (m / 2 ^ d) = L
  obtain ⟨n0, s, hn0, rfl⟩ := hn
  generalize ht : L - f.p = t
  have key : rneDiv m (d + t) * 2 ^ t * 2 ^ d = rneDiv m (d + t) * 2 ^ (d + t) := by
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm t d]
  rw [key]
  by_cases hs : t ≤ s
  · have : n0 * 2 ^ s * 2 ^ d = (n0 * 2 ^ (s - t)) * 2 ^ (d + t) := by
      rw [show s = (s - t) + t by omega]
      simp only [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_sub_cancel]
    rw [this]
    exact rneDiv_nearest _ _ _
  · have hp := f.two_le_p
    have hq0 : 0 < m / 2 ^ d := by
      rcases Nat.eq_zero_or_pos (m / 2 ^ d) with h0 | h0
      · rw [h0, bitLen_zero] at hL; omega
      · exact h0
    have hspec := (bitLen_spec hq0).1
    rw [hL] at hspec
    have h2 : 2 ^ (L - 1) * 2 ^ d ≤ m := (Nat.le_div_iff_mul_le (Nat.two_pow_pos d)).mp hspec
    have h1 : n0 * 2 ^ s < 2 ^ (L - 1) := by
      have e1 : 2 ^ (L - 1) = 2 ^ f.p * 2 ^ (L - 1 - f.p) := by
        rw [← Nat.pow_add]; congr 1; omega
      have e2 : 2 ^ s ≤ 2 ^ (L - 1 - f.p) := two_pow_le_two_pow (by omega)
      rw [e1]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hn0 (Nat.two_pow_pos s))
        (Nat.mul_le_mul_left _ e2)
    have h4 : n0 * 2 ^ s * 2 ^ d ≤ 2 ^ (L - 1) * 2 ^ d := Nat.mul_le_mul_right _ (Nat.le_of_lt h1)
    have h3 := rneDiv_nearest m (d + t) (2 ^ (L - 1 - t))
    have e3 : 2 ^ (L - 1 - t) * 2 ^ (d + t) = 2 ^ (L - 1) * 2 ^ d := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [e3] at h3
    omega

/-! ### Innocuous double rounding -/

/-- Double rounding (first to multiples of `2^t'`, then to multiples of `2^t`,
`t' < t`) agrees with direct rounding to multiples of `2^t` when `A` is equal
to, or farther than `2^(t'-1)` from, every odd multiple of `2^(t-1)` (every
midpoint of the coarse grid). -/
theorem rneDiv_double {A t t' : Nat} (htt : t' < t) (ht' : 1 ≤ t')
    (hfar : ∀ n : Nat, A ≠ n * 2 ^ t + 2 ^ (t - 1) →
      2 ^ (t' - 1) < ((A : Int) - ((n * 2 ^ t + 2 ^ (t - 1) : Nat) : Int)).natAbs) :
    rneDiv (rneDiv A t' * 2 ^ t') t = rneDiv A t := by
  have eD : 2 ^ t = 2 * 2 ^ (t - 1) := by rw [← two_pow_succ']; congr 1; omega
  have eD' : 2 ^ t' = 2 * 2 ^ (t' - 1) := by rw [← two_pow_succ']; congr 1; omega
  have hh' : 2 ^ (t' - 1) < 2 ^ (t - 1) := two_pow_lt_two_pow (by omega)
  have hW := rneDiv_err A t'
  have hN := rneDiv_err A t
  by_cases hmid : 2 * (((rneDiv A t * 2 ^ t : Nat) : Int) - (A : Int)).natAbs = 2 ^ t
  · have hdvd : 2 ^ t' ∣ A := by
      generalize rneDiv A t = n0 at hmid
      have d1 : 2 ^ t' ∣ n0 * 2 ^ t :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_left _ _)
      have d2 : 2 ^ t' ∣ 2 ^ (t - 1) := Nat.pow_dvd_pow 2 (by omega)
      rcases (by omega : A = n0 * 2 ^ t + 2 ^ (t - 1) ∨ A + 2 ^ (t - 1) = n0 * 2 ^ t) with h | h
      · rw [h]; exact Nat.dvd_add d1 d2
      · have : A = n0 * 2 ^ t - 2 ^ (t - 1) := by omega
        rw [this]; exact Nat.dvd_sub d1 d2
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_comm (2 ^ t') c, rneDiv_mul_pow]
  · apply rneDiv_eq_of_close
    generalize hn0 : rneDiv A t = n0 at hN hmid ⊢
    generalize hWd : rneDiv A t' * 2 ^ t' = W at hW ⊢
    generalize hNd : n0 * 2 ^ t = N at hN hmid ⊢
    apply Nat.lt_of_not_le
    intro hcon
    rcases Nat.lt_or_ge W N with hWN | hWN
    · -- `W` is at or below the midpoint `N - 2^(t-1)`, `A` strictly above it.
      have hn1 : 1 ≤ n0 := by
        rcases Nat.eq_zero_or_pos n0 with h0 | h0
        · subst h0; omega
        · exact h0
      have e1 : (n0 - 1) * 2 ^ t + 2 ^ t = N := by
        rw [← add_one_mul', Nat.sub_add_cancel hn1, hNd]
      have := hfar (n0 - 1) (by omega)
      omega
    · -- `W` is at or above the midpoint `N + 2^(t-1)`, `A` strictly below it.
      have := hfar n0 (by omega)
      omega

/-- The sum or difference `A` of two magnitudes with `p` significant bits is
equal to, or farther than `2^(L-p'-1)` from, every odd multiple of `2^(L-p-1)`,
where `L` is the bit length of `A` and `2p + 1 ≤ p' < L`; this auxiliary form
assumes that the exponent `b` of `y` is below `L - p'`. -/
theorem sum_far_aux {p p' L A x y X Y a b : Nat} (hp2 : 2 ≤ p) (hpp : 2 * p + 1 ≤ p')
    (hL : p' < L) (hX : X < 2 ^ p) (hY : Y < 2 ^ p) (hx : x = X * 2 ^ a) (hy : y = Y * 2 ^ b)
    (hA : A = x + y ∨ A + y = x ∨ A + x = y) (hAL : 2 ^ (L - 1) ≤ A) (hb : b < L - p')
    (n : Nat) (hne : A ≠ n * 2 ^ (L - p) + 2 ^ (L - p - 1)) :
    2 ^ (L - p' - 1) < ((A : Int) - ((n * 2 ^ (L - p) + 2 ^ (L - p - 1) : Nat) : Int)).natAbs := by
  apply Nat.lt_of_not_le
  intro hle
  have eh : 2 ^ (L - p - 1) = 2 * 2 ^ (L - p - 2) := by rw [← two_pow_succ']; congr 1; omega
  have eD : 2 ^ (L - p) = 2 * 2 ^ (L - p - 1) := by rw [← two_pow_succ']; congr 1; omega
  have eL1 : 2 ^ (L - 1) = 2 ^ p * 2 ^ (L - p - 1) := by rw [← Nat.pow_add]; congr 1; omega
  have hh'q : 2 ^ (L - p' - 1) ≤ 2 ^ (L - p - 2) := two_pow_le_two_pow (by omega)
  -- `y` is below a quarter of the coarse spacing.
  have hyq : y < 2 ^ (L - p - 2) := by
    rw [hy]
    calc Y * 2 ^ b < 2 ^ p * 2 ^ b := Nat.mul_lt_mul_of_pos_right hY (Nat.two_pow_pos b)
      _ = 2 ^ (p + b) := (Nat.pow_add 2 p b).symm
      _ ≤ 2 ^ (L - p - 2) := two_pow_le_two_pow (by omega)
  have hpq : 2 ^ (L - p - 2) ≤ 2 ^ p * 2 ^ (L - p - 2) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos p)
  -- `x` is a multiple of the half spacing `2^(L-p-1)`.
  have ha : L - p - 1 ≤ a := by
    apply Nat.le_of_not_lt
    intro ha
    have hxq : x < 2 ^ p * 2 ^ (L - p - 2) := by
      rw [hx]
      calc X * 2 ^ a < 2 ^ p * 2 ^ a := Nat.mul_lt_mul_of_pos_right hX (Nat.two_pow_pos a)
        _ ≤ 2 ^ p * 2 ^ (L - p - 2) := Nat.mul_le_mul_left _ (two_pow_le_two_pow (by omega))
    have : 2 ^ p * 2 ^ (L - p - 1) = 2 * (2 ^ p * 2 ^ (L - p - 2)) := by
      rw [eh, Nat.mul_left_comm]
    omega
  have ex : x = (X * 2 ^ (a - (L - p - 1))) * 2 ^ (L - p - 1) := by
    rw [hx, Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  have emu : n * 2 ^ (L - p) + 2 ^ (L - p - 1) = (2 * n + 1) * 2 ^ (L - p - 1) := by
    rw [eD, add_one_mul' (2 * n), Nat.mul_assoc 2 n, Nat.mul_left_comm n 2]
  -- The two candidate multiples of `2^(L-p-1)` are closer than `2^(L-p-1)`, so equal.
  have hclose : X * 2 ^ (a - (L - p - 1)) = 2 * n + 1 := by
    apply eq_of_mul_close (Nat.two_pow_pos (L - p - 1))
    rw [← ex, ← emu]
    rcases hA with h | h | h <;> omega
  -- An odd multiple forces `a = L - p - 1`.
  have ha2 : a = L - p - 1 := by
    apply Nat.le_antisymm _ ha
    apply Nat.le_of_not_lt
    intro ha3
    have : 2 ^ (a - (L - p - 1)) = 2 * 2 ^ (a - (L - p - 1) - 1) := by
      rw [← two_pow_succ']; congr 1; omega
    rw [this, Nat.mul_left_comm] at hclose
    omega
  rw [ha2, Nat.sub_self, Nat.pow_zero, Nat.mul_one] at hclose
  -- So the midpoint is below `2^(L-1) ≤ A` by at least `2^(L-p-1)`.
  have hbig : (2 * n + 1 + 1) * 2 ^ (L - p - 1) ≤ 2 ^ p * 2 ^ (L - p - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [add_one_mul' (2 * n + 1)] at hbig
  rw [emu] at hle hne
  omega

theorem sum_far {p p' L A x y X Y a b : Nat} (hp2 : 2 ≤ p) (hpp : 2 * p + 1 ≤ p')
    (hL : p' < L) (hX : X < 2 ^ p) (hY : Y < 2 ^ p) (hx : x = X * 2 ^ a) (hy : y = Y * 2 ^ b)
    (hA : A = x + y ∨ A + y = x ∨ A + x = y) (hAL : 2 ^ (L - 1) ≤ A)
    (n : Nat) (hne : A ≠ n * 2 ^ (L - p) + 2 ^ (L - p - 1)) :
    2 ^ (L - p' - 1) < ((A : Int) - ((n * 2 ^ (L - p) + 2 ^ (L - p - 1) : Nat) : Int)).natAbs := by
  by_cases hb : b < L - p'
  · exact sum_far_aux hp2 hpp hL hX hY hx hy hA hAL hb n hne
  by_cases ha : a < L - p'
  · exact sum_far_aux hp2 hpp hL hY hX hy hx (by omega) hAL ha n hne
  -- Both exponents are at least `L - p'`: `A` and the midpoint are multiples of `2^(L-p')`.
  apply Nat.lt_of_not_le
  intro hle
  have dx : 2 ^ (L - p') ∣ x := hx ▸ Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_left _ _)
  have dy : 2 ^ (L - p') ∣ y := hy ▸ Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_left _ _)
  have dA : 2 ^ (L - p') ∣ A := by
    rcases hA with h | h | h
    · rw [h]; exact Nat.dvd_add dx dy
    · rw [show A = x - y by omega]; exact Nat.dvd_sub dx dy
    · rw [show A = y - x by omega]; exact Nat.dvd_sub dy dx
  have dmu : 2 ^ (L - p') ∣ n * 2 ^ (L - p) + 2 ^ (L - p - 1) :=
    Nat.dvd_add (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_left _ _))
      (Nat.pow_dvd_pow 2 (by omega))
  obtain ⟨c, hc⟩ := dA
  obtain ⟨c', hc'⟩ := dmu
  have eD' : 2 ^ (L - p') = 2 * 2 ^ (L - p' - 1) := by rw [← two_pow_succ']; congr 1; omega
  have : c = c' := by
    apply eq_of_mul_close (Nat.two_pow_pos (L - p'))
    rw [Nat.mul_comm c, Nat.mul_comm c', ← hc, ← hc']
    omega
  subst this
  exact hne (hc.trans hc'.symm)

/-- Rounding a magnitude in `[2^(L-1), 2^L]` to precision `p ≤ L`. -/
theorem roundUnits_of_range (f : Fmt) {W L : Nat} (hpL : f.p ≤ L) (h1 : 2 ^ (L - 1) ≤ W)
    (h2 : W ≤ 2 ^ L) : roundUnits f W 0 = rneDiv W (L - f.p) * 2 ^ (L - f.p) := by
  have hp := f.two_le_p
  rcases Nat.lt_or_ge W (2 ^ L) with hlt | hge
  · have hb : bitLen W = L := by
      rw [show L = L - 1 + 1 by omega] at hlt ⊢
      exact bitLen_eq h1 hlt
    unfold roundUnits
    simp [hb]
  · have hW : W = 2 ^ L := Nat.le_antisymm h2 hge
    subst hW
    rw [roundUnits_repr0 (isRepr_two_pow f L)]
    conv => rhs; rw [two_pow_split (Nat.sub_le L f.p), rneDiv_mul_pow]
    rw [← two_pow_split (Nat.sub_le L f.p)]

/-- Innocuous double rounding of a sum or difference: rounding a sum or
difference of two magnitudes with `p` significant bits first to `p' ≥ 2p + 1`
bits and then to `p` bits gives the same result as rounding it once to `p`
bits (unbounded exponent range). -/
theorem roundUnits_double_sum (f g : Fmt) (hp : 2 * f.p + 1 ≤ g.p) {x y A : Nat}
    (hx : IsRepr f x) (hy : IsRepr f y) (hA : A = x + y ∨ A + y = x ∨ A + x = y) :
    roundUnits f (roundUnits g A 0) 0 = roundUnits f A 0 := by
  rcases Nat.eq_zero_or_pos A with h0 | hA0
  · subst h0; simp [roundUnits_zero]
  obtain ⟨hL1, hL2⟩ := bitLen_spec hA0
  generalize hL : bitLen A = L at hL1 hL2
  by_cases hLg : L ≤ g.p
  · rw [roundUnits_repr0 (isRepr_of_lt (Nat.lt_of_lt_of_le hL2 (two_pow_le_two_pow hLg)))]
  have hp2 := f.two_le_p
  have eg : roundUnits g A 0 = rneDiv A (L - g.p) * 2 ^ (L - g.p) := by
    unfold roundUnits; simp [hL]
  have ef : roundUnits f A 0 = rneDiv A (L - f.p) * 2 ^ (L - f.p) := by
    unfold roundUnits; simp [hL]
  rw [eg, ef]
  -- The intermediate value lies in `[2^(L-1), 2^L]`.
  have e1 : 2 ^ (L - 1) = 2 ^ (L - 1 - (L - g.p)) * 2 ^ (L - g.p) := two_pow_split (by omega)
  have e2 : 2 ^ L = 2 ^ (L - (L - g.p)) * 2 ^ (L - g.p) := two_pow_split (by omega)
  have lo : 2 ^ (L - 1 - (L - g.p)) ≤ A / 2 ^ (L - g.p) :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (e1 ▸ hL1)
  have hi : A / 2 ^ (L - g.p) < 2 ^ (L - (L - g.p)) :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (e2 ▸ hL2)
  have r1 := rneDiv_ge A (L - g.p)
  have r2 := rneDiv_le A (L - g.p)
  have w1 : 2 ^ (L - 1) ≤ rneDiv A (L - g.p) * 2 ^ (L - g.p) := by
    rw [e1]; exact Nat.mul_le_mul_right _ (by omega)
  have w2 : rneDiv A (L - g.p) * 2 ^ (L - g.p) ≤ 2 ^ L := by
    rw [e2]; exact Nat.mul_le_mul_right _ (by omega)
  rw [roundUnits_of_range f (by omega) w1 w2]
  congr 1
  obtain ⟨X, a, hX, hxa⟩ := hx
  obtain ⟨Y, b, hY, hyb⟩ := hy
  apply rneDiv_double (by omega) (by omega)
  intro n hne
  have := sum_far (p := f.p) (p' := g.p) (L := L) hp2 hp (by omega) hX hY hxa hyb hA hL1 n hne
  rw [show L - f.p - 1 = L - f.p - 1 from rfl] at this
  exact this

/-! ### Scaling and range facts -/

theorem roundUnits_mul_pow_add (f : Fmt) (m d j : Nat) :
    roundUnits f (m * 2 ^ j) (d + j) = roundUnits f m d := by
  unfold roundUnits
  dsimp only
  have e1 : m * 2 ^ j / 2 ^ (d + j) = m / 2 ^ d := by
    rw [Nat.pow_add, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos j)]
  rw [e1, show d + j + (bitLen (m / 2 ^ d) - f.p) = j + (d + (bitLen (m / 2 ^ d) - f.p)) by omega,
    rneDiv_mul_pow_add]

theorem roundUnits_mul_pow_zero (f : Fmt) (A k : Nat) :
    roundUnits f (A * 2 ^ k) 0 = roundUnits f A 0 * 2 ^ k := by
  rcases Nat.eq_zero_or_pos A with h0 | hA
  · subst h0; simp [roundUnits_zero]
  by_cases hb : bitLen A ≤ f.p
  · have hr : IsRepr f A :=
      isRepr_of_lt (Nat.lt_of_lt_of_le (bitLen_spec hA).2 (two_pow_le_two_pow hb))
    rw [roundUnits_repr0 (hr.mul_two_pow k), roundUnits_repr0 hr]
  · unfold roundUnits
    simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add]
    rw [bitLen_mul_two_pow hA, show bitLen A + k - f.p = k + (bitLen A - f.p) by omega,
      rneDiv_mul_pow_add, Nat.pow_add, Nat.mul_comm (2 ^ k), Nat.mul_assoc]

/-- A lower bound on the rounded magnitude. -/
theorem two_pow_le_roundUnits (f : Fmt) {m d K : Nat} (h : 2 ^ K ≤ m / 2 ^ d) :
    2 ^ K ≤ roundUnits f m d := by
  unfold roundUnits
  dsimp only
  have hq0 : 0 < m / 2 ^ d := Nat.lt_of_lt_of_le (Nat.two_pow_pos K) h
  have hK := le_bitLen_of_le h
  have hs := (bitLen_spec hq0).1
  generalize bitLen (m / 2 ^ d) = L at hK hs
  have hp := f.two_le_p
  have hge := rneDiv_ge m (d + (L - f.p))
  have e : m / 2 ^ (d + (L - f.p)) = m / 2 ^ d / 2 ^ (L - f.p) := by
    rw [Nat.pow_add, Nat.div_div_eq_div_mul]
  have e2 : 2 ^ (L - 1) = 2 ^ (L - 1 - (L - f.p)) * 2 ^ (L - f.p) := two_pow_split (by omega)
  have h3 : 2 ^ (L - 1 - (L - f.p)) ≤ m / 2 ^ d / 2 ^ (L - f.p) := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← e2]; exact hs
  calc 2 ^ K ≤ 2 ^ (L - 1) := two_pow_le_two_pow (by omega)
    _ = 2 ^ (L - 1 - (L - f.p)) * 2 ^ (L - f.p) := e2
    _ ≤ rneDiv m (d + (L - f.p)) * 2 ^ (L - f.p) := Nat.mul_le_mul_right _ (by omega)

theorem IsRepr.mono {f g : Fmt} (hp : f.p ≤ g.p) {n : Nat} (h : IsRepr f n) : IsRepr g n := by
  obtain ⟨m, t, hm, rfl⟩ := h
  exact ⟨m, t, Nat.lt_of_lt_of_le hm (two_pow_le_two_pow hp), rfl⟩

theorem Fmt.qneg_add_two (f : Fmt) : f.qneg + 2 = f.bias + f.p := by
  unfold Fmt.qneg; have := f.two_le_p; omega

theorem qneg_sub_eq {f g : Fmt} (hp : f.p ≤ g.p) (hb : f.bias ≤ g.bias) :
    g.qneg - f.qneg = (g.bias - f.bias) + (g.p - f.p) := by
  have := f.qneg_add_two; have := g.qneg_add_two; omega

/-- The largest finite magnitude of `f`, rescaled to the units of a wider
format `g`, is at most the largest finite magnitude of `g`. -/
theorem maxUnits_mul_le {f g : Fmt} (hp : f.p ≤ g.p) (hb : f.bias ≤ g.bias) :
    f.maxUnits * 2 ^ (g.qneg - f.qneg) ≤ g.maxUnits := by
  have hb1 := f.one_le_bias
  have eL : 2 ^ (g.qneg - f.qneg) = 2 ^ (g.bias - f.bias) * 2 ^ (g.p - f.p) := by
    rw [qneg_sub_eq hp hb, Nat.pow_add]
  have eR : 2 ^ (2 * g.bias - 1) = 2 ^ (2 * f.bias - 1) * 2 ^ (g.bias - f.bias) * 2 ^ (g.bias - f.bias) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have eP : 2 ^ g.p = 2 ^ f.p * 2 ^ (g.p - f.p) := by rw [← Nat.pow_add]; congr 1; omega
  rw [f.maxUnits_eq, g.maxUnits_eq, eL, eR, eP]
  have hP := Nat.two_pow_pos f.p
  have hQ := Nat.two_pow_pos (g.p - f.p)
  have hB := Nat.two_pow_pos (g.bias - f.bias)
  generalize 2 ^ f.p = P at *
  generalize 2 ^ (g.p - f.p) = Q at *
  generalize 2 ^ (2 * f.bias - 1) = C
  generalize 2 ^ (g.bias - f.bias) = B at *
  have h1 : (P - 1) * Q ≤ P * Q - 1 := by
    rw [Nat.sub_mul, Nat.one_mul]; omega
  calc (P - 1) * C * (B * Q) = ((P - 1) * Q) * (C * B) := by
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (P * Q - 1) * (C * B) := Nat.mul_le_mul_right _ h1
    _ ≤ (P * Q - 1) * (C * B * B) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hB)

/-- A representable magnitude above the largest finite magnitude is at least
`2^emax` of the next binade. -/
theorem ge_of_gt_maxUnits {g : Fmt} {W : Nat} (hW : IsRepr g W) (h : g.maxUnits < W) :
    2 ^ (g.p + (2 * g.bias - 1)) ≤ W := by
  obtain ⟨m, s, hm, rfl⟩ := hW
  rw [g.maxUnits_eq] at h
  rcases Nat.lt_or_ge s (2 * g.bias - 1) with hs | hs
  · exfalso
    have : m * 2 ^ s ≤ (2 ^ g.p - 1) * 2 ^ (2 * g.bias - 1) :=
      Nat.mul_le_mul (by omega) (two_pow_le_two_pow (by omega))
    omega
  · have e : 2 ^ s = 2 ^ (s - (2 * g.bias - 1)) * 2 ^ (2 * g.bias - 1) := two_pow_split hs
    rw [e, ← Nat.mul_assoc] at h ⊢
    have h' : 2 ^ g.p - 1 < m * 2 ^ (s - (2 * g.bias - 1)) := Nat.lt_of_mul_lt_mul_right h
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ (by omega)

/-- Overflow in a wider format `g` implies overflow after rounding to `f`. -/
theorem overflow_transfer {f g : Fmt} (hp : f.p ≤ g.p) (hb : f.bias ≤ g.bias) {W : Nat}
    (hW : IsRepr g W) (h : g.maxUnits < W) : f.maxUnits < roundUnits f W (g.qneg - f.qneg) := by
  have hbig := ge_of_gt_maxUnits hW h
  have hb1 := f.one_le_bias
  have e : 2 ^ (g.p + (2 * g.bias - 1)) =
      2 ^ (f.p + (2 * f.bias - 1) + (g.bias - f.bias)) * 2 ^ (g.qneg - f.qneg) := by
    rw [qneg_sub_eq hp hb, ← Nat.pow_add]; congr 1; omega
  have h2 : 2 ^ (f.p + (2 * f.bias - 1)) ≤ W / 2 ^ (g.qneg - f.qneg) := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    calc 2 ^ (f.p + (2 * f.bias - 1)) * 2 ^ (g.qneg - f.qneg)
        ≤ 2 ^ (f.p + (2 * f.bias - 1) + (g.bias - f.bias)) * 2 ^ (g.qneg - f.qneg) :=
          Nat.mul_le_mul_right _ (two_pow_le_two_pow (by omega))
      _ = 2 ^ (g.p + (2 * g.bias - 1)) := e.symm
      _ ≤ W := hbig
  exact Nat.lt_of_lt_of_le f.maxUnits_lt (two_pow_le_roundUnits f h2)

/-! ### Format conversion -/

/-- Widening a finite value is exact. -/
theorem cvt_up_fin {f g : Fmt} (hp : f.p ≤ g.p) (hb : f.bias ≤ g.bias) (s : Bool)
    (E : Fin f.expCount) (M : Fin f.fracCount) :
    ∃ E' : Fin g.expCount, ∃ M' : Fin g.fracCount, cvt f g (.fin s E M) = .fin s E' M' ∧
      unitsOf g E'.val M'.val = unitsOf f E.val M.val * 2 ^ (g.qneg - f.qneg) := by
  have hq : f.qneg ≤ g.qneg := by unfold Fmt.qneg; omega
  have hr : IsRepr g (unitsOf f E.val M.val * 2 ^ (g.qneg - f.qneg)) :=
    ((unitsOf_isRepr f M.isLt).mono hp).mul_two_pow _
  have hle : unitsOf f E.val M.val * 2 ^ (g.qneg - f.qneg) ≤ g.maxUnits :=
    Nat.le_trans (Nat.mul_le_mul_right _ (unitsOf_le_maxUnits f E.isLt M.isLt)) (maxUnits_mul_le hp hb)
  obtain ⟨E', M', hEM, hu⟩ := mkFin_repr hr hle
  refine ⟨E', M', ?_, hu⟩
  simp only [cvt, hq, ite_true]
  unfold round
  rw [roundUnits_repr0 hr, hEM]

theorem cvt_down_fin {f g : Fmt} (hq : f.qneg < g.qneg) (s : Bool) (E : Fin g.expCount)
    (M : Fin g.fracCount) :
    cvt g f (.fin s E M) = round f s (unitsOf g E.val M.val) (g.qneg - f.qneg) := by
  simp only [cvt, Nat.not_le.mpr hq, ite_false]

theorem cvt_round {f g : Fmt} (hq : f.qneg < g.qneg) (s : Bool) (m : Nat) :
    cvt g f (round g s m 0) = if g.maxUnits < roundUnits g m 0 then .inf s
      else round f s (roundUnits g m 0) (g.qneg - f.qneg) := by
  show cvt g f (mkFin g s (roundUnits g m 0)) = _
  split
  · rename_i h; rw [mkFin_overflow h]; rfl
  · rename_i h
    obtain ⟨E, M, hEM, hu⟩ := mkFin_repr (roundUnits_isRepr g m 0) (Nat.le_of_not_lt h)
    rw [hEM, cvt_down_fin hq, hu]

theorem cvt_zero {f g : Fmt} (hq : f.qneg < g.qneg) (b : Bool) : cvt g f (zero g b) = zero f b := by
  show cvt g f (.fin b _ _) = _
  rw [cvt_down_fin hq]
  simp only [unitsOf_zero_left]
  show mkFin f b (roundUnits f 0 _) = _
  rw [roundUnits_zero, mkFin_zero]

end Toy.Float
