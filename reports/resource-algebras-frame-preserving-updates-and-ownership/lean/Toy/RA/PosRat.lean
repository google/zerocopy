/-!
# Positive Rational Numbers (`PosRat`)

A self-contained, Mathlib-free construction of the positive rationals `ℚ_{>0}`
as a quotient of positive numerator/denominator pairs, supporting addition,
ordering, and subtraction of strictly smaller fractions. Used to construct the
fractional permission algebra `fracRA` matching Iris's `Qp`.
-/

namespace Toy.RA

/-- Raw pair `(num, den)` representing the positive fraction `num / den`. -/
structure RawPosRat where
  num : Nat
  den : Nat
  num_pos : 0 < num
  den_pos : 0 < den

/-- Cross-multiplication equivalence on raw positive fractions. -/
def RawPosRat.equiv (a b : RawPosRat) : Prop :=
  a.num * b.den = b.num * a.den

theorem RawPosRat.equiv_refl (a : RawPosRat) : RawPosRat.equiv a a := rfl

theorem RawPosRat.equiv_symm {a b : RawPosRat} (h : RawPosRat.equiv a b) :
    RawPosRat.equiv b a := h.symm

theorem RawPosRat.equiv_trans {a b c : RawPosRat}
    (hab : RawPosRat.equiv a b) (hbc : RawPosRat.equiv b c) :
    RawPosRat.equiv a c := by
  unfold RawPosRat.equiv at *
  have h1 : (a.num * c.den) * b.den = (c.num * a.den) * b.den := by
    calc (a.num * c.den) * b.den
        = (a.num * b.den) * c.den := by rw [Nat.mul_right_comm]
      _ = (b.num * a.den) * c.den := by rw [hab]
      _ = (b.num * c.den) * a.den := by rw [Nat.mul_right_comm]
      _ = (c.num * b.den) * a.den := by rw [hbc]
      _ = (c.num * a.den) * b.den := by rw [Nat.mul_right_comm]
  exact Nat.eq_of_mul_eq_mul_right b.den_pos h1

instance RawPosRat.setoid : Setoid RawPosRat where
  r := RawPosRat.equiv
  iseqv := ⟨RawPosRat.equiv_refl, RawPosRat.equiv_symm, RawPosRat.equiv_trans⟩

/-- The positive rational numbers `ℚ_{>0}`, defined as the quotient of
`RawPosRat` by cross-multiplication equivalence. Captures Iris's `Qp` carrier
for fractional permissions without external dependencies. -/
def PosRat : Type := Quotient RawPosRat.setoid

namespace PosRat

/-- Construct a positive rational from positive natural numbers `n` and `d`. -/
def mk (n d : Nat) (hn : 0 < n) (hd : 0 < d) : PosRat :=
  Quotient.mk RawPosRat.setoid ⟨n, d, hn, hd⟩

/-- Full fraction `1 = 1/1`. -/
def one : PosRat := mk 1 1 (by omega) (by omega)

/-- Half fraction `1/2`. -/
def half : PosRat := mk 1 2 (by omega) (by omega)

/-- Over-full fraction `2 = 2/1` (useful for invalid-fraction tests). -/
def two : PosRat := mk 2 1 (by omega) (by omega)

/-- Raw addition on pairs. -/
private def rawAdd (a b : RawPosRat) : RawPosRat where
  num := a.num * b.den + b.num * a.den
  den := a.den * b.den
  num_pos := Nat.add_pos_left (Nat.mul_pos a.num_pos b.den_pos) _
  den_pos := Nat.mul_pos a.den_pos b.den_pos

private theorem rawAdd_equiv {a₁ a₂ b₁ b₂ : RawPosRat}
    (ha : RawPosRat.equiv a₁ a₂) (hb : RawPosRat.equiv b₁ b₂) :
    RawPosRat.equiv (rawAdd a₁ b₁) (rawAdd a₂ b₂) := by
  unfold RawPosRat.equiv rawAdd at *
  dsimp only
  rw [Nat.add_mul, Nat.add_mul]
  have h1 : a₁.num * b₁.den * (a₂.den * b₂.den) = a₂.num * b₂.den * (a₁.den * b₁.den) := by
    calc a₁.num * b₁.den * (a₂.den * b₂.den)
        = (a₁.num * a₂.den) * (b₁.den * b₂.den) := by ac_rfl
      _ = (a₂.num * a₁.den) * (b₁.den * b₂.den) := by rw [ha]
      _ = a₂.num * b₂.den * (a₁.den * b₁.den) := by ac_rfl
  have h2 : b₁.num * a₁.den * (a₂.den * b₂.den) = b₂.num * a₂.den * (a₁.den * b₁.den) := by
    calc b₁.num * a₁.den * (a₂.den * b₂.den)
        = (b₁.num * b₂.den) * (a₁.den * a₂.den) := by ac_rfl
      _ = (b₂.num * b₁.den) * (a₁.den * a₂.den) := by rw [hb]
      _ = b₂.num * a₂.den * (a₁.den * b₁.den) := by ac_rfl
  rw [h1, h2]

/-- Addition of positive rationals. -/
def add : PosRat → PosRat → PosRat :=
  Quotient.lift₂ (fun a b => Quotient.mk RawPosRat.setoid (rawAdd a b))
    (fun _ _ _ _ ha hb => Quotient.sound (rawAdd_equiv ha hb))

private theorem rawLe_iff {a₁ a₂ b₁ b₂ : RawPosRat}
    (ha : RawPosRat.equiv a₁ a₂) (hb : RawPosRat.equiv b₁ b₂) :
    (a₁.num * b₁.den ≤ b₁.num * a₁.den) ↔ (a₂.num * b₂.den ≤ b₂.num * a₂.den) := by
  unfold RawPosRat.equiv at *
  have hpos1 : 0 < a₂.den * b₂.den := Nat.mul_pos a₂.den_pos b₂.den_pos
  have hpos2 : 0 < a₁.den * b₁.den := Nat.mul_pos a₁.den_pos b₁.den_pos
  constructor
  · intro h
    have hm : (a₁.num * b₁.den) * (a₂.den * b₂.den) ≤ (b₁.num * a₁.den) * (a₂.den * b₂.den) :=
      Nat.mul_le_mul_right _ h
    have hl : (a₁.num * b₁.den) * (a₂.den * b₂.den) = (a₂.num * b₂.den) * (a₁.den * b₁.den) := by
      calc (a₁.num * b₁.den) * (a₂.den * b₂.den)
          = (a₁.num * a₂.den) * (b₁.den * b₂.den) := by ac_rfl
        _ = (a₂.num * a₁.den) * (b₁.den * b₂.den) := by rw [ha]
        _ = (a₂.num * b₂.den) * (a₁.den * b₁.den) := by ac_rfl
    have hr : (b₁.num * a₁.den) * (a₂.den * b₂.den) = (b₂.num * a₂.den) * (a₁.den * b₁.den) := by
      calc (b₁.num * a₁.den) * (a₂.den * b₂.den)
          = (b₁.num * b₂.den) * (a₁.den * a₂.den) := by ac_rfl
        _ = (b₂.num * b₁.den) * (a₁.den * a₂.den) := by rw [hb]
        _ = (b₂.num * a₂.den) * (a₁.den * b₁.den) := by ac_rfl
    rw [hl, hr] at hm
    exact Nat.le_of_mul_le_mul_right hm hpos2
  · intro h
    have hm : (a₂.num * b₂.den) * (a₁.den * b₁.den) ≤ (b₂.num * a₂.den) * (a₁.den * b₁.den) :=
      Nat.mul_le_mul_right _ h
    have hl : (a₂.num * b₂.den) * (a₁.den * b₁.den) = (a₁.num * b₁.den) * (a₂.den * b₂.den) := by
      calc (a₂.num * b₂.den) * (a₁.den * b₁.den)
          = (a₂.num * a₁.den) * (b₂.den * b₁.den) := by ac_rfl
        _ = (a₁.num * a₂.den) * (b₂.den * b₁.den) := by rw [← ha]
        _ = (a₁.num * b₁.den) * (a₂.den * b₂.den) := by ac_rfl
    have hr : (b₂.num * a₂.den) * (a₁.den * b₁.den) = (b₁.num * a₁.den) * (a₂.den * b₂.den) := by
      calc (b₂.num * a₂.den) * (a₁.den * b₁.den)
          = (b₂.num * b₁.den) * (a₂.den * a₁.den) := by ac_rfl
        _ = (b₁.num * b₂.den) * (a₂.den * a₁.den) := by rw [← hb]
        _ = (b₁.num * a₁.den) * (a₂.den * b₂.den) := by ac_rfl
    rw [hl, hr] at hm
    exact Nat.le_of_mul_le_mul_right hm hpos1

/-- Non-strict order `q₁ ≤ q₂` on positive rationals. -/
def le : PosRat → PosRat → Prop :=
  Quotient.lift₂ (fun a b => a.num * b.den ≤ b.num * a.den)
    (fun _ _ _ _ ha hb => propext (rawLe_iff ha hb))

private theorem rawLt_iff {a₁ a₂ b₁ b₂ : RawPosRat}
    (ha : RawPosRat.equiv a₁ a₂) (hb : RawPosRat.equiv b₁ b₂) :
    (a₁.num * b₁.den < b₁.num * a₁.den) ↔ (a₂.num * b₂.den < b₂.num * a₂.den) := by
  have h := rawLe_iff hb ha
  constructor <;> intro hlt
  · exact Nat.lt_of_not_le (fun hle => Nat.not_le_of_lt hlt (h.mpr hle))
  · exact Nat.lt_of_not_le (fun hle => Nat.not_le_of_lt hlt (h.mp hle))

/-- Strict order `q₁ < q₂` on positive rationals. -/
def lt : PosRat → PosRat → Prop :=
  Quotient.lift₂ (fun a b => a.num * b.den < b.num * a.den)
    (fun _ _ _ _ ha hb => propext (rawLt_iff ha hb))

theorem add_assoc (a b c : PosRat) : add (add a b) c = add a (add b c) := by
  refine Quotient.inductionOn₃ a b c fun x y z => Quotient.sound ?_
  change RawPosRat.equiv (rawAdd (rawAdd x y) z) (rawAdd x (rawAdd y z))
  unfold RawPosRat.equiv rawAdd
  dsimp only
  simp only [Nat.add_mul]
  have h1 : x.num * y.den * z.den * (x.den * (y.den * z.den)) =
            x.num * (y.den * z.den) * (x.den * y.den * z.den) := by ac_rfl
  have h2 : y.num * x.den * z.den * (x.den * (y.den * z.den)) =
            y.num * z.den * x.den * (x.den * y.den * z.den) := by ac_rfl
  have h3 : z.num * (x.den * y.den) * (x.den * (y.den * z.den)) =
            z.num * y.den * x.den * (x.den * y.den * z.den) := by ac_rfl
  rw [h1, h2, h3, Nat.add_assoc]

theorem add_comm (a b : PosRat) : add a b = add b a := by
  refine Quotient.inductionOn₂ a b fun x y => Quotient.sound ?_
  change RawPosRat.equiv (rawAdd x y) (rawAdd y x)
  unfold RawPosRat.equiv rawAdd
  dsimp only
  have hden : x.den * y.den = y.den * x.den := Nat.mul_comm _ _
  have hnum : x.num * y.den + y.num * x.den = y.num * x.den + x.num * y.den := Nat.add_comm _ _
  rw [hden, hnum]

theorem le_refl (a : PosRat) : le a a :=
  Quotient.inductionOn a fun _ => Nat.le_refl _

theorem le_of_lt {a b : PosRat} (h : lt a b) : le a b :=
  Quotient.inductionOn₂ a b (fun _ _ hlt => Nat.le_of_lt hlt) h

theorem le_trans {a b c : PosRat} (hab : le a b) (hbc : le b c) : le a c := by
  revert hab hbc
  refine Quotient.inductionOn₃ a b c fun x y z hxy hyz => ?_
  change x.num * y.den ≤ y.num * x.den at hxy
  change y.num * z.den ≤ z.num * y.den at hyz
  change x.num * z.den ≤ z.num * x.den
  have h1 : (x.num * z.den) * (y.num * y.den) ≤ (z.num * x.den) * (y.num * y.den) := by
    calc (x.num * z.den) * (y.num * y.den)
        = (x.num * y.den) * (y.num * z.den) := by ac_rfl
      _ ≤ (y.num * x.den) * (z.num * y.den) := Nat.mul_le_mul hxy hyz
      _ = (z.num * x.den) * (y.num * y.den) := by ac_rfl
  exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos y.num_pos y.den_pos)

theorem le_of_add_le {a b c : PosRat} (h : le (add a b) c) : le a c := by
  revert h
  refine Quotient.inductionOn₃ a b c fun x y z hxyz => ?_
  change (x.num * y.den + y.num * x.den) * z.den ≤ z.num * (x.den * y.den) at hxyz
  change x.num * z.den ≤ z.num * x.den
  have h1 : (x.num * z.den) * y.den ≤ (z.num * x.den) * y.den := by
    calc (x.num * z.den) * y.den
        = (x.num * y.den) * z.den := by ac_rfl
      _ ≤ (x.num * y.den + y.num * x.den) * z.den :=
          Nat.mul_le_mul_right z.den (Nat.le_add_right _ _)
      _ ≤ z.num * (x.den * y.den) := hxyz
      _ = (z.num * x.den) * y.den := by ac_rfl
  exact Nat.le_of_mul_le_mul_right h1 y.den_pos

theorem add_le_add_right {a b : PosRat} (c : PosRat) (h : le a b) :
    le (add a c) (add b c) := by
  revert h
  refine Quotient.inductionOn₃ a b c fun x y z hxy => ?_
  change x.num * y.den ≤ y.num * x.den at hxy
  change (x.num * z.den + z.num * x.den) * (y.den * z.den) ≤
         (y.num * z.den + z.num * y.den) * (x.den * z.den)
  rw [Nat.add_mul, Nat.add_mul]
  have h1 : x.num * z.den * (y.den * z.den) ≤ y.num * z.den * (x.den * z.den) := by
    calc x.num * z.den * (y.den * z.den)
        = (x.num * y.den) * (z.den * z.den) := by ac_rfl
      _ ≤ (y.num * x.den) * (z.den * z.den) := Nat.mul_le_mul_right _ hxy
      _ = y.num * z.den * (x.den * z.den) := by ac_rfl
  have h2 : z.num * x.den * (y.den * z.den) = z.num * y.den * (x.den * z.den) := by ac_rfl
  rw [h2]
  exact Nat.add_le_add_right h1 _

theorem le_of_add_le_add_right {a b c : PosRat} (h : le (add a c) (add b c)) :
    le a b := by
  revert h
  refine Quotient.inductionOn₃ a b c fun x y z hxyz => ?_
  change (x.num * z.den + z.num * x.den) * (y.den * z.den) ≤
         (y.num * z.den + z.num * y.den) * (x.den * z.den) at hxyz
  change x.num * y.den ≤ y.num * x.den
  rw [Nat.add_mul, Nat.add_mul] at hxyz
  have h2 : z.num * x.den * (y.den * z.den) = z.num * y.den * (x.den * z.den) := by ac_rfl
  rw [h2] at hxyz
  have h1 := Nat.le_of_add_le_add_right hxyz
  have hl : x.num * z.den * (y.den * z.den) = (x.num * y.den) * (z.den * z.den) := by ac_rfl
  have hr : y.num * z.den * (x.den * z.den) = (y.num * x.den) * (z.den * z.den) := by ac_rfl
  rw [hl, hr] at h1
  exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos z.den_pos z.den_pos)

theorem not_add_le_self (a b : PosRat) : ¬ le (add a b) a := by
  refine Quotient.inductionOn₂ a b fun x y h => ?_
  change (x.num * y.den + y.num * x.den) * x.den ≤ x.num * (x.den * y.den) at h
  rw [Nat.add_mul] at h
  have heq : x.num * y.den * x.den = x.num * (x.den * y.den) := by ac_rfl
  rw [heq] at h
  have hpos : 0 < y.num * x.den * x.den :=
    Nat.mul_pos (Nat.mul_pos y.num_pos x.den_pos) x.den_pos
  omega

/-- Raw guarded subtraction, defaulting to `1/1` when `b ≥ a`. -/
private def rawSubOrOne (x y : RawPosRat) : RawPosRat :=
  if hxy : y.num * x.den < x.num * y.den then
    ⟨x.num * y.den - y.num * x.den, x.den * y.den,
     Nat.sub_pos_of_lt hxy, Nat.mul_pos x.den_pos y.den_pos⟩
  else
    ⟨1, 1, by omega, by omega⟩

private theorem rawSubOrOne_equiv {x₁ y₁ x₂ y₂ : RawPosRat}
    (hx : RawPosRat.equiv x₁ x₂) (hy : RawPosRat.equiv y₁ y₂) :
    RawPosRat.equiv (rawSubOrOne x₁ y₁) (rawSubOrOne x₂ y₂) := by
  unfold rawSubOrOne
  have hiff := rawLt_iff hy hx
  by_cases h1 : y₁.num * x₁.den < x₁.num * y₁.den
  · have h2 : y₂.num * x₂.den < x₂.num * y₂.den := hiff.mp h1
    rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2)]
    unfold RawPosRat.equiv at *
    dsimp only
    rw [Nat.sub_mul, Nat.sub_mul]
    have ha : x₁.num * y₁.den * (x₂.den * y₂.den) = x₂.num * y₂.den * (x₁.den * y₁.den) := by
      calc x₁.num * y₁.den * (x₂.den * y₂.den)
          = (x₁.num * x₂.den) * (y₁.den * y₂.den) := by ac_rfl
        _ = (x₂.num * x₁.den) * (y₁.den * y₂.den) := by rw [hx]
        _ = x₂.num * y₂.den * (x₁.den * y₁.den) := by ac_rfl
    have hb : y₁.num * x₁.den * (x₂.den * y₂.den) = y₂.num * x₂.den * (x₁.den * y₁.den) := by
      calc y₁.num * x₁.den * (x₂.den * y₂.den)
          = (y₁.num * y₂.den) * (x₁.den * x₂.den) := by ac_rfl
        _ = (y₂.num * y₁.den) * (x₁.den * x₂.den) := by rw [hy]
        _ = y₂.num * x₂.den * (x₁.den * y₁.den) := by ac_rfl
    rw [ha, hb]
  · have h2 : ¬ (y₂.num * x₂.den < x₂.num * y₂.den) := fun h2 => h1 (hiff.mpr h2)
    rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_right_of_eq_false (eq_false h2)]
    rfl

/-- Positive difference `a - b` when `b < a`. Used to construct the exact
complementary fraction `1 - q` of any partial fraction `q < 1`. -/
def sub (a b : PosRat) (_h : lt b a) : PosRat :=
  Quotient.liftOn₂ a b (fun x y => Quotient.mk RawPosRat.setoid (rawSubOrOne x y))
    (fun _ _ _ _ hx hy => Quotient.sound (rawSubOrOne_equiv hx hy))

theorem add_sub_cancel (a b : PosRat) (h : lt b a) : add b (sub a b h) = a := by
  revert h
  refine Quotient.inductionOn₂ a b fun x y hlt => ?_
  change y.num * x.den < x.num * y.den at hlt
  have hsub : rawSubOrOne x y =
      ⟨x.num * y.den - y.num * x.den, x.den * y.den,
       Nat.sub_pos_of_lt hlt, Nat.mul_pos x.den_pos y.den_pos⟩ := by
    unfold rawSubOrOne
    rw [dite_eq_left_of_eq_true (eq_true hlt)]
  apply Quotient.sound
  change RawPosRat.equiv (rawAdd y (rawSubOrOne x y)) x
  rw [hsub]
  unfold RawPosRat.equiv rawAdd
  dsimp only
  have hle : y.num * x.den ≤ x.num * y.den := Nat.le_of_lt hlt
  have hsum : y.num * (x.den * y.den) + (x.num * y.den - y.num * x.den) * y.den =
              x.num * y.den * y.den := by
    calc y.num * (x.den * y.den) + (x.num * y.den - y.num * x.den) * y.den
        = (y.num * x.den) * y.den + (x.num * y.den - y.num * x.den) * y.den := by ac_rfl
      _ = (y.num * x.den + (x.num * y.den - y.num * x.den)) * y.den := by rw [Nat.add_mul]
      _ = (x.num * y.den) * y.den := by rw [Nat.add_sub_of_le hle]
  rw [hsum]
  ac_rfl

theorem half_add_half : add half half = one := by
  apply Quotient.sound
  change RawPosRat.equiv (rawAdd ⟨1, 2, _, _⟩ ⟨1, 2, _, _⟩) ⟨1, 1, _, _⟩
  rfl

theorem half_lt_one : lt half one := by
  change 1 * 1 < 1 * 2
  omega

theorem not_two_le_one : ¬ le two one := by
  change ¬ (2 * 1 ≤ 1 * 1)
  omega

theorem lt_iff_exists_add (a b : PosRat) : lt a b ↔ ∃ c : PosRat, add a c = b := by
  constructor
  · intro h
    exact ⟨sub b a h, add_sub_cancel b a h⟩
  · rintro ⟨c, rfl⟩
    refine Quotient.inductionOn₂ a c fun x y => ?_
    change x.num * (x.den * y.den) < (x.num * y.den + y.num * x.den) * x.den
    rw [Nat.add_mul]
    have heq : x.num * (x.den * y.den) = x.num * y.den * x.den := by ac_rfl
    rw [heq]
    exact Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.mul_pos y.num_pos x.den_pos) x.den_pos)

/-! ## Positive and Negative Examples for `PosRat` -/

theorem posRat_le_pos_example : le half one := le_of_lt half_lt_one

theorem posRat_le_neg_example : ¬ le two one := not_two_le_one

theorem posRat_lt_pos_example : lt half one := half_lt_one

theorem posRat_lt_neg_example : ¬ lt one one := by
  change ¬ (1 * 1 < 1 * 1)
  omega

end PosRat

end Toy.RA
