/-
Toy.FloatTier.Lemmas
====================

Auxiliary lemmas: value-level congruence of the IEEE
operations of `Toy.FloatTier.Base` with respect to `EqNsz` (equality up to the
sign of zero), injectivity of the comparison key up to the sign of zero, and
the corresponding facts for the payload-carrying values `V f`.
-/
import Toy.FloatTier.Lang

namespace Toy.FloatTier

variable {f : Fmt}

/-! ### `EqNsz` on `FP f` -/

theorem EqNsz.refl' (x : FP f) : EqNsz x x := rfl

theorem EqNsz.symm' {x y : FP f} (h : EqNsz x y) : EqNsz y x := Eq.symm h

theorem EqNsz.trans' {x y z : FP f} (h₁ : EqNsz x y) (h₂ : EqNsz y z) : EqNsz x z :=
  Eq.trans h₁ h₂

theorem zero_isZero (s : Bool) : (zero f s).isZero = true := by
  simp [zero, FP.isZero]

theorem isZero_iff_eq_zero {x : FP f} : x.isZero = true ↔ ∃ s, x = zero f s := by
  constructor
  · intro h
    cases x with
    | nan => simp [FP.isZero] at h
    | inf s => simp [FP.isZero] at h
    | fin s E M =>
      simp only [FP.isZero, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨s, by simp only [zero, FP.fin.injEq, true_and]; exact ⟨Fin.ext h.1, Fin.ext h.2⟩⟩
  · rintro ⟨s, rfl⟩; exact zero_isZero s

theorem eqNsz_iff (x y : FP f) : EqNsz x y ↔ x = y ∨ (x.isZero = true ∧ y.isZero = true) := by
  unfold EqNsz zeroBlind
  by_cases hx : x.isZero = true <;> by_cases hy : y.isZero = true <;> simp only [hx, hy,
    ite_true, ite_false, Bool.false_eq_true, and_false, false_and, or_false, and_self, or_true]
  · constructor
    · intro h; rw [← h] at hy; exact absurd (zero_isZero false) hy
    · intro h; rw [h] at hx; exact absurd hx hy
  · constructor
    · intro h; rw [h] at hx; exact absurd (zero_isZero false) hx
    · intro h; rw [h] at hx; exact absurd hy hx

theorem eqNsz_zero_zero (s t : Bool) : EqNsz (zero f s) (zero f t) :=
  (eqNsz_iff _ _).2 (Or.inr ⟨zero_isZero s, zero_isZero t⟩)

theorem unitsOf_zero_zero (f : Fmt) : unitsOf f 0 0 = 0 := by simp [unitsOf]

theorem sval_zero (s : Bool) : sval s 0 = 0 := by cases s <;> simp [sval]

/-! ### Congruence of `add`, `sub`, `mul` -/

theorem add_zero_left_eqNsz (s s' : Bool) (y : FP f) :
    EqNsz (add (zero f s) y) (add (zero f s') y) := by
  cases y with
  | nan => rfl
  | inf t => rfl
  | fin t E M =>
    simp only [zero, add, unitsOf_zero_zero, sval_zero, Int.zero_add]
    split
    · exact eqNsz_zero_zero _ _
    · exact EqNsz.refl' _

theorem add_zero_right_eqNsz (x : FP f) (t t' : Bool) :
    EqNsz (add x (zero f t)) (add x (zero f t')) := by
  cases x with
  | nan => rfl
  | inf s => rfl
  | fin s E M =>
    simp only [zero, add, unitsOf_zero_zero, sval_zero, Int.add_zero]
    split
    · exact eqNsz_zero_zero _ _
    · exact EqNsz.refl' _

theorem add_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    EqNsz (add x y) (add x' y') := by
  have h1 : EqNsz (add x y) (add x' y) := by
    rcases (eqNsz_iff _ _).1 hx with rfl | ⟨hx1, hx2⟩
    · exact EqNsz.refl' _
    · obtain ⟨s, rfl⟩ := isZero_iff_eq_zero.1 hx1
      obtain ⟨s', rfl⟩ := isZero_iff_eq_zero.1 hx2
      exact add_zero_left_eqNsz s s' y
  have h2 : EqNsz (add x' y) (add x' y') := by
    rcases (eqNsz_iff _ _).1 hy with rfl | ⟨hy1, hy2⟩
    · exact EqNsz.refl' _
    · obtain ⟨t, rfl⟩ := isZero_iff_eq_zero.1 hy1
      obtain ⟨t', rfl⟩ := isZero_iff_eq_zero.1 hy2
      exact add_zero_right_eqNsz x' t t'
  exact EqNsz.trans' h1 h2

theorem neg_eqNsz_congr {x x' : FP f} (hx : EqNsz x x') : EqNsz x.neg x'.neg := by
  rcases (eqNsz_iff _ _).1 hx with rfl | ⟨hx1, hx2⟩
  · exact EqNsz.refl' _
  · obtain ⟨s, rfl⟩ := isZero_iff_eq_zero.1 hx1
    obtain ⟨s', rfl⟩ := isZero_iff_eq_zero.1 hx2
    exact eqNsz_zero_zero _ _

theorem sub_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    EqNsz (sub x y) (sub x' y') :=
  add_eqNsz_congr hx (neg_eqNsz_congr hy)

theorem round_zero_units (b : Bool) (d : Nat) : round f b 0 d = zero f b := by
  unfold round
  rw [roundUnits_zero]
  have := mkFin_fields f b ⟨0, f.expCount_pos⟩ ⟨0, f.fracCount_pos⟩
  simpa [unitsOf_zero_zero, zero] using this

theorem mul_zero_left_eqNsz (s s' : Bool) (y : FP f) :
    EqNsz (mul (zero f s) y) (mul (zero f s') y) := by
  cases y with
  | nan => rfl
  | inf t => simp only [zero, mul, unitsOf_zero_zero, ite_true]; rfl
  | fin t E M =>
    simp only [zero, mul, unitsOf_zero_zero, Nat.zero_mul, round_zero_units]
    exact eqNsz_zero_zero _ _

theorem mul_zero_right_eqNsz (x : FP f) (t t' : Bool) :
    EqNsz (mul x (zero f t)) (mul x (zero f t')) := by
  cases x with
  | nan => rfl
  | inf s => simp only [zero, mul, unitsOf_zero_zero, ite_true]; rfl
  | fin s E M =>
    simp only [zero, mul, unitsOf_zero_zero, Nat.mul_zero, round_zero_units]
    exact eqNsz_zero_zero _ _

theorem mul_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    EqNsz (mul x y) (mul x' y') := by
  have h1 : EqNsz (mul x y) (mul x' y) := by
    rcases (eqNsz_iff _ _).1 hx with rfl | ⟨hx1, hx2⟩
    · exact EqNsz.refl' _
    · obtain ⟨s, rfl⟩ := isZero_iff_eq_zero.1 hx1
      obtain ⟨s', rfl⟩ := isZero_iff_eq_zero.1 hx2
      exact mul_zero_left_eqNsz s s' y
  have h2 : EqNsz (mul x' y) (mul x' y') := by
    rcases (eqNsz_iff _ _).1 hy with rfl | ⟨hy1, hy2⟩
    · exact EqNsz.refl' _
    · obtain ⟨t, rfl⟩ := isZero_iff_eq_zero.1 hy1
      obtain ⟨t', rfl⟩ := isZero_iff_eq_zero.1 hy2
      exact mul_zero_right_eqNsz x' t t'
  exact EqNsz.trans' h1 h2

/-! ### Comparisons -/

theorem isNaN_key_of_eqNsz {x x' : FP f} (hx : EqNsz x x') :
    x.isNaN = x'.isNaN ∧ key x = key x' := by
  rcases (eqNsz_iff _ _).1 hx with rfl | ⟨hx1, hx2⟩
  · exact ⟨rfl, rfl⟩
  · obtain ⟨s, rfl⟩ := isZero_iff_eq_zero.1 hx1
    obtain ⟨s', rfl⟩ := isZero_iff_eq_zero.1 hx2
    simp [zero, FP.isNaN, key, unitsOf_zero_zero, sval_zero]

theorem lt_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    lt x y = lt x' y' := by
  obtain ⟨h1, h2⟩ := isNaN_key_of_eqNsz hx
  obtain ⟨h3, h4⟩ := isNaN_key_of_eqNsz hy
  simp only [lt, h1, h2, h3, h4]

theorem feq_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    feq x y = feq x' y' := by
  obtain ⟨h1, h2⟩ := isNaN_key_of_eqNsz hx
  obtain ⟨h3, h4⟩ := isNaN_key_of_eqNsz hy
  simp only [feq, h1, h2, h3, h4]

theorem sval_eq_sval_iff (s t : Bool) (n m : Nat) :
    sval s n = sval t m ↔ n = m ∧ (s = t ∨ n = 0) := by
  cases s <;> cases t <;> simp [sval] <;> omega

/-- Equal comparison keys of non-NaN values: identical, or both zeros. -/
theorem eqNsz_of_key_eq {x y : FP f} (hx : x.isNaN = false) (hy : y.isNaN = false)
    (h : key x = key y) : EqNsz x y := by
  rw [eqNsz_iff]
  cases x with
  | nan => simp [FP.isNaN] at hx
  | inf s =>
    cases y with
    | nan => simp [FP.isNaN] at hy
    | inf t =>
      simp only [key, sval_eq_sval_iff] at h
      left; rcases h with ⟨_, h | h⟩
      · rw [h]
      · omega
    | fin t E M =>
      exfalso
      simp only [key, sval_eq_sval_iff] at h
      have := unitsOf_le_maxUnits f E.isLt M.isLt
      omega
  | fin s E M =>
    cases y with
    | nan => simp [FP.isNaN] at hy
    | inf t =>
      exfalso
      simp only [key, sval_eq_sval_iff] at h
      have := unitsOf_le_maxUnits f E.isLt M.isLt
      omega
    | fin t E' M' =>
      simp only [key, sval_eq_sval_iff] at h
      obtain ⟨hu, hs | h0⟩ := h
      · left
        subst hs
        rw [← mkFin_fields f s E M, ← mkFin_fields f s E' M', hu]
      · right
        have h0' : unitsOf f E'.val M'.val = 0 := by omega
        rw [unitsOf_eq_zero_iff] at h0 h0'
        simp [FP.isZero, h0, h0']

/-- Non-NaN values that are neither `<` nor `>` each other are equal up to the
sign of zero. -/
theorem eqNsz_of_not_lt_not_lt {x y : FP f} (hx : x.isNaN = false) (hy : y.isNaN = false)
    (h1 : lt x y = false) (h2 : lt y x = false) : EqNsz x y := by
  apply eqNsz_of_key_eq hx hy
  simp only [lt, hx, hy, Bool.not_false, Bool.true_and, decide_eq_false_iff_not] at h1 h2
  omega

end Toy.FloatTier
