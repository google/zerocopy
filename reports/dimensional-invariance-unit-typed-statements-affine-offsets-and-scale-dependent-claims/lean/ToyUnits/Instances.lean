import ToyUnits.Homogeneity
import ToyUnits.Inversion

/-!
# Concrete scalar domains and the length dimension

* `Rat` (Lean core rationals) satisfies `OrderedFieldLaws` and `InvZeroLaw` (`ratLaws`,
  `ratInvZero`).
* `RatJ` is `Rat` with the one change `0⁻¹ := 1`: it satisfies `OrderedFieldLaws` but not
  `InvZeroLaw` (`ratJLaws`, `ratJ_not_invZero`). It is used to test whether a result needs `0⁻¹ = 0`.
* `L` is the length dimension of the one-base-dimension setting, and `ctxL` declares every
  variable a length.
-/

namespace Toy.Units

/-- `Rat` satisfies every ordered-field law. -/
theorem ratLaws : OrderedFieldLaws Rat where
  add_assoc := Rat.add_assoc
  add_comm := Rat.add_comm
  add_zero := Rat.add_zero
  add_neg := Rat.add_neg_cancel
  mul_assoc := Rat.mul_assoc
  mul_comm := Rat.mul_comm
  mul_one := Rat.mul_one
  distrib := Rat.mul_add
  mul_inv := Rat.mul_inv_cancel
  zero_ne_one := by unfold ZeroNeOneLaw; decide
  le_refl := fun _ => Rat.le_refl
  le_trans := fun _ _ _ => Rat.le_trans
  le_antisymm := fun _ _ => Rat.le_antisymm
  le_total := fun _ _ => Rat.le_total
  lt_iff := fun a b => by
    constructor
    · intro h; exact ⟨Rat.le_of_lt h, Rat.not_le.2 h⟩
    · intro h; exact Rat.not_le.1 h.2
  add_le_mono := fun _ _ _ h => Rat.add_le_add_right.2 h
  mul_nonneg := fun _ _ => Rat.mul_nonneg

/-- In `Rat`, `0⁻¹ = 0`. -/
theorem ratInvZero : InvZeroLaw Rat := Rat.inv_zero

/-- `Rat` with the inverse changed at a single point: `0⁻¹ := 1`. -/
def RatJ : Type := Rat

/-- Embedding of rationals into `RatJ` (the identity). -/
def RatJ.ofRat (q : Rat) : RatJ := q

/-- The underlying rational of an element of `RatJ` (the identity). -/
def RatJ.toRat (a : RatJ) : Rat := a

instance instScalarOpsRatJ : ScalarOps RatJ where
  zero := RatJ.ofRat 0
  one := RatJ.ofRat 1
  add a b := RatJ.ofRat (RatJ.toRat a + RatJ.toRat b)
  mul a b := RatJ.ofRat (RatJ.toRat a * RatJ.toRat b)
  neg a := RatJ.ofRat (-(RatJ.toRat a))
  inv a := RatJ.ofRat (if RatJ.toRat a = 0 then 1 else (RatJ.toRat a)⁻¹)
  le a b := RatJ.toRat a ≤ RatJ.toRat b
  lt a b := RatJ.toRat a < RatJ.toRat b

namespace RatJ
theorem zero_def : (0 : RatJ) = ofRat 0 := rfl
theorem one_def : (1 : RatJ) = ofRat 1 := rfl
theorem add_def (a b : Rat) : ofRat a + ofRat b = ofRat (a + b) := rfl
theorem mul_def (a b : Rat) : ofRat a * ofRat b = ofRat (a * b) := rfl
theorem neg_def (a : Rat) : -(ofRat a) = ofRat (-a) := rfl
theorem inv_def (a : Rat) : (ofRat a)⁻¹ = ofRat (if a = 0 then 1 else a⁻¹) := rfl
theorem le_def (a b : Rat) : ofRat a ≤ ofRat b ↔ a ≤ b := Iff.rfl
theorem lt_def (a b : Rat) : ofRat a < ofRat b ↔ a < b := Iff.rfl
theorem ofRat_inj (a b : Rat) : ofRat a = ofRat b ↔ a = b := Iff.rfl
end RatJ

/-- `RatJ` satisfies every ordered-field law (the field axioms say nothing about `0⁻¹`). -/
theorem ratJLaws : OrderedFieldLaws RatJ where
  add_assoc := ratLaws.add_assoc
  add_comm := ratLaws.add_comm
  add_zero := ratLaws.add_zero
  add_neg := ratLaws.add_neg
  mul_assoc := ratLaws.mul_assoc
  mul_comm := ratLaws.mul_comm
  mul_one := ratLaws.mul_one
  distrib := ratLaws.distrib
  mul_inv := fun (a : Rat) (h : RatJ.ofRat a ≠ RatJ.ofRat 0) => by
    have h' : a ≠ 0 := h
    show RatJ.ofRat (a * (if a = 0 then 1 else a⁻¹)) = RatJ.ofRat 1
    simp only [h', ↓reduceIte]; exact congrArg RatJ.ofRat (Rat.mul_inv_cancel a h')
  zero_ne_one := ratLaws.zero_ne_one
  le_refl := ratLaws.le_refl
  le_trans := ratLaws.le_trans
  le_antisymm := ratLaws.le_antisymm
  le_total := ratLaws.le_total
  lt_iff := ratLaws.lt_iff
  add_le_mono := ratLaws.add_le_mono
  mul_nonneg := ratLaws.mul_nonneg

/-- In `RatJ`, `0⁻¹ = 1 ≠ 0`. -/
theorem ratJ_not_invZero : ¬ InvZeroLaw RatJ := by
  intro h
  have h1 : RatJ.ofRat (if (0 : Rat) = 0 then 1 else (0 : Rat)⁻¹) = RatJ.ofRat 0 := h
  have h2 : (if (0 : Rat) = 0 then (1 : Rat) else (0 : Rat)⁻¹) = 0 := h1
  simp at h2

/-- The two-element field `GF(2)` (`false` is `0`, `true` is `1`), with `0⁻¹ = 0`. Its order
relations are placeholders: no ordered-field law is intended. -/
def GF2 : Type := Bool

instance instScalarOpsGF2 : ScalarOps GF2 where
  zero := false
  one := true
  add a b := xor a b
  mul a b := a && b
  neg a := a
  inv a := a
  le _ _ := True
  lt _ _ := False

/-- `GF2` satisfies the field laws. -/
theorem gf2_fieldLaws : FieldLaws GF2 where
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_neg := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  mul_one := by intro a; cases a <;> rfl
  distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_inv := by
    intro a ha
    cases a with
    | false => exact (ha rfl).elim
    | true => rfl
  zero_ne_one := by intro h; cases h

/-- In `GF2`, `0⁻¹ = 0`. -/
theorem gf2_invZero : InvZeroLaw GF2 := rfl

/-- In `GF2`, `1 + 1 = 0`. -/
theorem gf2_one_add_one_eq_zero : (1 : GF2) + 1 = 0 := rfl

/-- `GF2` with the inverse changed at a single point: `0⁻¹ := 1`. -/
def GF2J : Type := Bool

instance instScalarOpsGF2J : ScalarOps GF2J where
  zero := false
  one := true
  add a b := xor a b
  mul a b := a && b
  neg a := a
  inv _ := true
  le _ _ := True
  lt _ _ := False

/-- `GF2J` satisfies the field laws (they say nothing about `0⁻¹`). -/
theorem gf2J_fieldLaws : FieldLaws GF2J where
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_neg := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  mul_one := by intro a; cases a <;> rfl
  distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_inv := by
    intro a ha
    cases a with
    | false => exact (ha rfl).elim
    | true => rfl
  zero_ne_one := by intro h; cases h

/-- In `GF2J`, `0⁻¹ = 1 ≠ 0`. -/
theorem gf2J_not_invZero : ¬ InvZeroLaw GF2J := by
  intro h; cases h

/-- Every element of `GF2J` is `0` or `1`. -/
theorem gf2J_eq_zero_or_one (a : GF2J) : a = 0 ∨ a = 1 := by
  cases a with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

/-- The length dimension in the setting with one base dimension. -/
def L : Dim 1 := fun _ => 1

/-- Every variable is a length. -/
def ctxL : Ctx 1 := fun _ => L

end Toy.Units
