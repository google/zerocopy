/-
Toy.FloatTier.VLemmas
=====================

Auxiliary lemmas about payload-carrying values `V f` (including injectivity of
the bit encoding `V.bits`), the set-valued primitives and policy tiers.
-/
import Toy.FloatTier.Lemmas

namespace Toy.FloatTier

variable {f : Fmt}

namespace V

theorem isNaN_toFP (x : V f) : x.toFP.isNaN = x.isNaN := by
  cases x <;> rfl

theorem toFP_ofFP {c : FP f} (h : c.isNaN = false) : (V.ofFP c).toFP = c := by
  cases c with
  | nan => simp [FP.isNaN] at h
  | inf s => rfl
  | fin s E M => rfl

theorem toFP_neg (x : V f) : x.neg.toFP = x.toFP.neg := by
  cases x <;> rfl

theorem toFP_abs (x : V f) : x.abs.toFP = x.toFP.setSign false := by
  cases x <;> rfl

theorem toFP_copysign (x y : V f) : (x.copysign y).toFP = x.toFP.setSign y.signBit := by
  cases x <;> rfl

theorem eq_of_toFP_eq {x y : V f} (hx : x.isNaN = false) (h : x.toFP = y.toFP) : x = y := by
  cases x with
  | qnan => simp [isNaN] at hx
  | snan => simp [isNaN] at hx
  | inf s => cases y <;> simp_all [toFP]
  | fin s E M => cases y <;> simp_all [toFP]

theorem eq_of_valEq_of_isNaNOrZero_false {x y : V f} (h : ValEq x y)
    (hb : x.isNaNOrZero = false) : x = y := by
  simp only [isNaNOrZero, Bool.or_eq_false_iff] at hb
  rcases (eqNsz_iff _ _).1 h with h | ⟨hz, _⟩
  · exact eq_of_toFP_eq hb.1 h
  · simp [isZero] at hb; rw [hb.2] at hz; exact absurd hz (by decide)

theorem isNaN_of_NaNChoice {X : Extra f} {x y r : V f} (h : NaNChoice X x y r) :
    r.isNaN = true := h.1

theorem toFP_eq_nan_of_isNaN {r : V f} (h : r.isNaN = true) : r.toFP = .nan := by
  cases r <;> simp_all [isNaN, toFP]

end V

theorem setSign_eqNsz_congr {x x' : FP f} (hx : EqNsz x x') (b : Bool) :
    EqNsz (x.setSign b) (x'.setSign b) := by
  rcases (eqNsz_iff _ _).1 hx with rfl | ⟨hx1, hx2⟩
  · exact EqNsz.refl' _
  · obtain ⟨s, rfl⟩ := isZero_iff_eq_zero.1 hx1
    obtain ⟨s', rfl⟩ := isZero_iff_eq_zero.1 hx2
    exact eqNsz_zero_zero _ _

theorem ValEq.refl (x : V f) : ValEq x x := EqNsz.refl' _
theorem ValEq.symm {x y : V f} (h : ValEq x y) : ValEq y x := EqNsz.symm' h
theorem ValEq.trans {x y z : V f} (h₁ : ValEq x y) (h₂ : ValEq y z) : ValEq x z :=
  EqNsz.trans' h₁ h₂

theorem ValEq.isNaN_eq {x y : V f} (h : ValEq x y) : x.isNaN = y.isNaN := by
  rw [← V.isNaN_toFP, ← V.isNaN_toFP]; exact (isNaN_key_of_eqNsz h).1

theorem valEq_of_isNaN {x y : V f} (hx : x.isNaN = true) (hy : y.isNaN = true) : ValEq x y := by
  unfold ValEq; rw [V.toFP_eq_nan_of_isNaN hx, V.toFP_eq_nan_of_isNaN hy]; exact EqNsz.refl' _

/-- The NaN-collapsed view of any allowed arithmetic result is the IEEE result. -/
theorem arithSet_toFP {X : Extra f} {c : FP f} {x y r : V f} (h : arithSet X c x y r) :
    r.toFP = c := by
  unfold arithSet at h
  split at h
  · rename_i hc
    rw [V.toFP_eq_nan_of_isNaN h.1]
    cases c <;> simp_all [FP.isNaN]
  · rename_i hc; subst h; exact V.toFP_ofFP (by simpa using hc)

/-- Value-level congruence of `min`. -/
theorem minSet_valEq_congr {X : Extra f} {x₁ x₂ y₁ y₂ r₁ r₂ : V f}
    (hx : ValEq x₁ x₂) (hy : ValEq y₁ y₂)
    (h₁ : minSet X x₁ y₁ r₁) (h₂ : minSet X x₂ y₂ r₂) : ValEq r₁ r₂ := by
  have hnx := hx.isNaN_eq
  have hny := hy.isNaN_eq
  have hl1 : lt x₁.toFP y₁.toFP = lt x₂.toFP y₂.toFP := lt_eqNsz_congr hx hy
  have hl2 : lt y₁.toFP x₁.toFP = lt y₂.toFP x₂.toFP := lt_eqNsz_congr hy hx
  unfold minSet at h₁ h₂
  rw [← hnx, ← hny, ← hl1, ← hl2] at h₂
  by_cases a : x₁.isNaN = true <;> by_cases b : y₁.isNaN = true
  · simp only [a, b, Bool.and_self, ite_true] at h₁ h₂
    exact valEq_of_isNaN h₁.1 h₂.1
  · simp only [a, b, Bool.and_false, Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
    subst h₁ h₂; exact hy
  · simp only [a, b, Bool.and_true, Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
    subst h₁ h₂; exact hx
  · simp only [Bool.not_eq_true] at a b
    simp only [a, b, Bool.and_self, Bool.false_eq_true, ite_false] at h₁ h₂
    by_cases c1 : lt x₁.toFP y₁.toFP = true
    · simp only [c1, ite_true] at h₁ h₂; subst h₁ h₂; exact hx
    · by_cases c2 : lt y₁.toFP x₁.toFP = true
      · simp only [c1, c2, ite_true, Bool.false_eq_true, ite_false] at h₁ h₂; subst h₁ h₂; exact hy
      · simp only [c1, c2, Bool.false_eq_true, ite_false] at h₁ h₂
        simp only [Bool.not_eq_true] at c1 c2
        have hxy : ValEq x₁ y₁ :=
          eqNsz_of_not_lt_not_lt (by rw [V.isNaN_toFP]; exact a) (by rw [V.isNaN_toFP]; exact b)
            c1 c2
        have hx2y2 : ValEq x₂ y₂ := hx.symm.trans (hxy.trans hy)
        rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
        · exact hx
        · exact hxy.trans hy
        · exact hxy.symm.trans hx
        · exact hy

/-- Value-level congruence of `max`. -/
theorem maxSet_valEq_congr {X : Extra f} {x₁ x₂ y₁ y₂ r₁ r₂ : V f}
    (hx : ValEq x₁ x₂) (hy : ValEq y₁ y₂)
    (h₁ : maxSet X x₁ y₁ r₁) (h₂ : maxSet X x₂ y₂ r₂) : ValEq r₁ r₂ := by
  have hnx := hx.isNaN_eq
  have hny := hy.isNaN_eq
  have hl1 : lt x₁.toFP y₁.toFP = lt x₂.toFP y₂.toFP := lt_eqNsz_congr hx hy
  have hl2 : lt y₁.toFP x₁.toFP = lt y₂.toFP x₂.toFP := lt_eqNsz_congr hy hx
  unfold maxSet at h₁ h₂
  rw [← hnx, ← hny, ← hl1, ← hl2] at h₂
  by_cases a : x₁.isNaN = true <;> by_cases b : y₁.isNaN = true
  · simp only [a, b, Bool.and_self, ite_true] at h₁ h₂
    exact valEq_of_isNaN h₁.1 h₂.1
  · simp only [a, b, Bool.and_false, Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
    subst h₁ h₂; exact hy
  · simp only [a, b, Bool.and_true, Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
    subst h₁ h₂; exact hx
  · simp only [Bool.not_eq_true] at a b
    simp only [a, b, Bool.and_self, Bool.false_eq_true, ite_false] at h₁ h₂
    by_cases c1 : lt y₁.toFP x₁.toFP = true
    · simp only [c1, ite_true] at h₁ h₂; subst h₁ h₂; exact hx
    · by_cases c2 : lt x₁.toFP y₁.toFP = true
      · simp only [c1, c2, ite_true, Bool.false_eq_true, ite_false] at h₁ h₂; subst h₁ h₂; exact hy
      · simp only [c1, c2, Bool.false_eq_true, ite_false] at h₁ h₂
        simp only [Bool.not_eq_true] at c1 c2
        have hxy : ValEq x₁ y₁ :=
          eqNsz_of_not_lt_not_lt (by rw [V.isNaN_toFP]; exact a) (by rw [V.isNaN_toFP]; exact b)
            c2 c1
        rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
        · exact hx
        · exact hxy.trans hy
        · exact hxy.symm.trans hx
        · exact hy

/-- Value-level congruence of every primitive of `S`. -/
theorem primSet_valEq_congr {X : Extra f} (p : Prim) {x₁ x₂ y₁ y₂ r₁ r₂ : V f}
    (hx : ValEq x₁ x₂) (hy : ValEq y₁ y₂)
    (h₁ : primSet X p x₁ y₁ r₁) (h₂ : primSet X p x₂ y₂ r₂) : ValEq r₁ r₂ := by
  cases p with
  | add =>
    unfold ValEq; rw [arithSet_toFP h₁, arithSet_toFP h₂]; exact add_eqNsz_congr hx hy
  | sub =>
    unfold ValEq; rw [arithSet_toFP h₁, arithSet_toFP h₂]; exact sub_eqNsz_congr hx hy
  | mul =>
    unfold ValEq; rw [arithSet_toFP h₁, arithSet_toFP h₂]; exact mul_eqNsz_congr hx hy
  | min => exact minSet_valEq_congr hx hy h₁ h₂
  | max => exact maxSet_valEq_congr hx hy h₁ h₂

/-- NaN-collapse congruence of the arithmetic primitives. -/
theorem primSet_toFP_congr {X : Extra f} (p : Prim) (hp : p.isArith = true)
    {x₁ x₂ y₁ y₂ r₁ r₂ : V f} (hx : x₁.toFP = x₂.toFP) (hy : y₁.toFP = y₂.toFP)
    (h₁ : primSet X p x₁ y₁ r₁) (h₂ : primSet X p x₂ y₂ r₂) : r₁.toFP = r₂.toFP := by
  cases p with
  | add => simp only [primSet] at h₁ h₂; rw [arithSet_toFP h₁, arithSet_toFP h₂, hx, hy]
  | sub => simp only [primSet] at h₁ h₂; rw [arithSet_toFP h₁, arithSet_toFP h₂, hx, hy]
  | mul => simp only [primSet] at h₁ h₂; rw [arithSet_toFP h₁, arithSet_toFP h₂, hx, hy]
  | min => simp [Prim.isArith] at hp
  | max => simp [Prim.isArith] at hp

/-! ### Policy tiers -/

theorem nanResult_mem (X : Extra f) (pol : ChoicePolicy) (x y : V f) :
    NaNChoice X x y (pol.nanResult x y) := by
  unfold ChoicePolicy.nanResult
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    refine ⟨rfl, Or.inr (Or.inl ⟨x, by simp, h.2, rfl, rfl⟩)⟩
  · split
    · rename_i _ h
      simp only [Bool.and_eq_true] at h
      refine ⟨rfl, Or.inr (Or.inl ⟨y, by simp, h.2, rfl, rfl⟩)⟩
    · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem arith_mem (X : Extra f) (pol : ChoicePolicy) (c : FP f) (x y : V f) :
    arithSet X c x y (pol.arith c x y) := by
  unfold arithSet ChoicePolicy.arith
  split
  · exact nanResult_mem X pol x y
  · rfl

/-! ### The bit encoding -/

/-- Setting the sign bit adds `2^(e + p - 1)` to the bit pattern. -/
theorem V.bits_withSign_true (x : V f) :
    (x.withSign true).bits = (x.withSign false).bits + 2 ^ (f.e + f.p - 1) := by
  cases x <;> simp [V.withSign, V.bits] <;> omega

/-- `V.bits` is injective: every term of `V f` is a distinct bit pattern. -/
theorem V.bits_injective : Function.Injective (V.bits (f := f)) := by
  have he := f.two_le_e
  have hp := f.two_le_p
  have hP2pos : 0 < 2 ^ (f.p - 2) := Nat.two_pow_pos _
  have hP1 : 2 ^ (f.p - 1) = 2 * 2 ^ (f.p - 2) := by
    conv => lhs; rw [show f.p - 1 = (f.p - 2) + 1 by omega, Nat.pow_succ]
    omega
  have hHalf : (2 ^ f.e - 1) * 2 ^ (f.p - 1) + 2 ^ (f.p - 1) = 2 ^ (f.e + f.p - 1) := by
    have := Nat.two_pow_pos f.e
    calc (2 ^ f.e - 1) * 2 ^ (f.p - 1) + 2 ^ (f.p - 1)
        = (2 ^ f.e - 1 + 1) * 2 ^ (f.p - 1) := by rw [Nat.add_mul, Nat.one_mul]
      _ = 2 ^ f.e * 2 ^ (f.p - 1) := by rw [show 2 ^ f.e - 1 + 1 = 2 ^ f.e by omega]
      _ = 2 ^ (f.e + f.p - 1) := by
        rw [← Nat.pow_add, show f.e + (f.p - 1) = f.e + f.p - 1 by omega]
  have fin_lt : ∀ (E : Fin f.expCount) (M : Fin f.fracCount),
      E.val * 2 ^ (f.p - 1) + M.val < (2 ^ f.e - 1) * 2 ^ (f.p - 1) := by
    intro E M
    have hE : E.val ≤ 2 ^ f.e - 2 := by have := E.isLt; unfold Fmt.expCount at this; omega
    have hM : M.val < 2 ^ (f.p - 1) := M.isLt
    have hmul : E.val * 2 ^ (f.p - 1) ≤ (2 ^ f.e - 2) * 2 ^ (f.p - 1) :=
      Nat.mul_le_mul_right _ hE
    have := f.four_le_two_pow_e
    have hsplit : (2 ^ f.e - 2) * 2 ^ (f.p - 1) + 2 ^ (f.p - 1) =
        (2 ^ f.e - 1) * 2 ^ (f.p - 1) := by
      calc (2 ^ f.e - 2) * 2 ^ (f.p - 1) + 2 ^ (f.p - 1)
          = (2 ^ f.e - 2 + 1) * 2 ^ (f.p - 1) := by rw [Nat.add_mul, Nat.one_mul]
        _ = (2 ^ f.e - 1) * 2 ^ (f.p - 1) := by congr 1; omega
    omega
  let lowBits : V f → Nat
    | .qnan _ k => (2 ^ f.e - 1) * 2 ^ (f.p - 1) + 2 ^ (f.p - 2) + k.val
    | .snan _ k => (2 ^ f.e - 1) * 2 ^ (f.p - 1) + (k.val + 1)
    | .inf _ => (2 ^ f.e - 1) * 2 ^ (f.p - 1)
    | .fin _ E M => E.val * 2 ^ (f.p - 1) + M.val
  have bits_decomp : ∀ v : V f,
      v.bits = (if v.signBit then 2 ^ (f.e + f.p - 1) else 0) + lowBits v := by
    intro v; cases v <;> dsimp only [lowBits] <;> simp [V.bits, V.signBit, Nat.add_assoc] <;> rfl
  have low_lt : ∀ v : V f, lowBits v < 2 ^ (f.e + f.p - 1) := by
    intro v
    cases v with
    | qnan s k =>
      have hk : k.val < 2 ^ (f.p - 2) := k.isLt
      dsimp only [lowBits]; omega
    | snan s k =>
      have hk : k.val < 2 ^ (f.p - 2) - 1 := by
        have := k.isLt; unfold Fmt.payCount at this; omega
      dsimp only [lowBits]; omega
    | inf s =>
      dsimp only [lowBits]; omega
    | fin s E M =>
      have := fin_lt E M
      dsimp only [lowBits]; omega
  intro x y hxy
  have hbx := low_lt x
  have hby := low_lt y
  rw [bits_decomp x, bits_decomp y] at hxy
  have hs : x.signBit = y.signBit := by
    cases hx : x.signBit <;> cases hy : y.signBit <;>
      simp only [hx, hy, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hxy ⊢ <;> omega
  rw [hs] at hxy
  have hlow : lowBits x = lowBits y := by omega
  cases x with
  | qnan sx kx =>
    have hkx : kx.val < 2 ^ (f.p - 2) := kx.isLt
    cases y with
    | qnan sy ky =>
      simp only [V.signBit] at hs; subst hs
      dsimp only [lowBits] at hlow
      exact congrArg (V.qnan sx) (Fin.ext (by omega))
    | snan sy ky =>
      have hky : ky.val < 2 ^ (f.p - 2) - 1 := ky.isLt
      dsimp only [lowBits] at hlow; omega
    | inf sy =>
      dsimp only [lowBits] at hlow; omega
    | fin sy Ey My =>
      have := fin_lt Ey My
      dsimp only [lowBits] at hlow; omega
  | snan sx kx =>
    have hkx : kx.val < 2 ^ (f.p - 2) - 1 := kx.isLt
    cases y with
    | qnan sy ky =>
      dsimp only [lowBits] at hlow; omega
    | snan sy ky =>
      simp only [V.signBit] at hs; subst hs
      dsimp only [lowBits] at hlow
      exact congrArg (V.snan sx) (Fin.ext (by omega))
    | inf sy =>
      dsimp only [lowBits] at hlow; omega
    | fin sy Ey My =>
      have := fin_lt Ey My
      dsimp only [lowBits] at hlow; omega
  | inf sx =>
    cases y with
    | qnan sy ky =>
      dsimp only [lowBits] at hlow; omega
    | snan sy ky =>
      dsimp only [lowBits] at hlow; omega
    | inf sy =>
      simp only [V.signBit] at hs; subst hs; rfl
    | fin sy Ey My =>
      have := fin_lt Ey My
      dsimp only [lowBits] at hlow; omega
  | fin sx Ex Mx =>
    have hfx := fin_lt Ex Mx
    cases y with
    | qnan sy ky =>
      dsimp only [lowBits] at hlow; omega
    | snan sy ky =>
      dsimp only [lowBits] at hlow; omega
    | inf sy =>
      dsimp only [lowBits] at hlow; omega
    | fin sy Ey My =>
      simp only [V.signBit] at hs; subst hs
      dsimp only [lowBits] at hlow
      have hMx : Mx.val < 2 ^ (f.p - 1) := Mx.isLt
      have hMy : My.val < 2 ^ (f.p - 1) := My.isLt
      have hdiv1 : (Ex.val * 2 ^ (f.p - 1) + Mx.val) / 2 ^ (f.p - 1) = Ex.val := by
        rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hMx, Nat.add_zero]
      have hdiv2 : (Ey.val * 2 ^ (f.p - 1) + My.val) / 2 ^ (f.p - 1) = Ey.val := by
        rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hMy, Nat.add_zero]
      have hEeq : Ex.val = Ey.val := by
        have hd := congrArg (· / 2 ^ (f.p - 1)) hlow
        simpa only [hdiv1, hdiv2] using hd
      have hMeq : Mx.val = My.val := by rw [hEeq] at hlow; omega
      have hEf : Ex = Ey := Fin.ext hEeq
      have hMf : Mx = My := Fin.ext hMeq
      rw [hEf, hMf]

end Toy.FloatTier
