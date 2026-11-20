import ToyFarkas.Sparse

/-!
# Linear constraints and their integer and rational semantics

A constraint is `lhs · x ⋈ rhs` with integer coefficients, integer right-hand side, and
`⋈ ∈ {≤, <}`. Two semantics are given:

* **integer points** `x : Nat → Int` (`Constraint.HoldsInt`);
* **rational points by scaling**: a rational point with common denominator `d`
  is written `x = p / d` with numerators `p : Nat → Int`; multiplying through by `d`
  gives `lhs · p ⋈ rhs * d` (`Constraint.HoldsScaled`). This is the rational
  semantics only when `d > 0`; every theorem that speaks about rational points
  carries `0 < d` as an explicit hypothesis.

Modeling bridge (prose, not a Lean theorem; no rational number type is used): a finite
system `S : List Constraint` mentions only finitely many variables, so the restriction of any
rational point to those variables has a positive common denominator `d`, and variables not
mentioned in `S` do not affect satisfaction. Hence, for a finite system, "no `(d, p)` with
`d > 0` satisfies `S` scaled" corresponds to "no rational point satisfies `S`". For an
arbitrary point `q : Nat → ℚ` (for example `q i = 1 / (i + 1)`) no single common denominator
exists; the bridge relies on the finiteness of `S`.
-/

namespace Toy.Farkas

/-- The relation symbol of a constraint: non-strict `≤` or strict `<`. -/
inductive Rel where
  | le
  | lt
  deriving DecidableEq, Repr

/-- Interpretation of a relation symbol on integers. -/
def Rel.Sat : Rel → Int → Int → Prop
  | .le, a, b => a ≤ b
  | .lt, a, b => a < b

instance Rel.decSat : (r : Rel) → (a b : Int) → Decidable (r.Sat a b)
  | .le, a, b => inferInstanceAs (Decidable (a ≤ b))
  | .lt, a, b => inferInstanceAs (Decidable (a < b))

/-- A linear constraint `lhs · x ⋈ rhs` with integer data. -/
structure Constraint where
  lhs : SparseVec
  rel : Rel
  rhs : Int
  deriving DecidableEq, Repr

namespace Constraint

/-- Whether the constraint is strict. -/
def isStrict (c : Constraint) : Bool :=
  match c.rel with
  | .le => false
  | .lt => true

/-- Satisfaction at an integer point `x`. -/
def HoldsInt (c : Constraint) (x : Nat → Int) : Prop :=
  c.rel.Sat (SparseVec.eval c.lhs x) c.rhs

instance (c : Constraint) (x : Nat → Int) : Decidable (c.HoldsInt x) :=
  inferInstanceAs (Decidable (c.rel.Sat _ _))

/-- Satisfaction at the scaled point `(d, p)`: `lhs · p ⋈ rhs * d`. For `d > 0` this is
satisfaction at the rational point `p / d`. -/
def HoldsScaled (c : Constraint) (d : Int) (p : Nat → Int) : Prop :=
  c.rel.Sat (SparseVec.eval c.lhs p) (c.rhs * d)

instance (c : Constraint) (d : Int) (p : Nat → Int) : Decidable (c.HoldsScaled d p) :=
  inferInstanceAs (Decidable (c.rel.Sat _ _))

end Constraint

/-- A constraint system (finite conjunction) holds at an integer point. -/
def SatInt (S : List Constraint) (x : Nat → Int) : Prop :=
  ∀ c ∈ S, c.HoldsInt x

instance (S : List Constraint) (x : Nat → Int) : Decidable (SatInt S x) :=
  inferInstanceAs (Decidable (∀ c ∈ S, c.HoldsInt x))

/-- A constraint system holds at the scaled point `(d, p)` (rational point `p / d` when `d > 0`). -/
def SatScaled (S : List Constraint) (d : Int) (p : Nat → Int) : Prop :=
  ∀ c ∈ S, c.HoldsScaled d p

instance (S : List Constraint) (d : Int) (p : Nat → Int) : Decidable (SatScaled S d p) :=
  inferInstanceAs (Decidable (∀ c ∈ S, c.HoldsScaled d p))

/-- Integer satisfaction is scaled satisfaction with denominator `1`. -/
theorem Constraint.holdsInt_iff_holdsScaled_one (c : Constraint) (x : Nat → Int) :
    c.HoldsInt x ↔ c.HoldsScaled 1 x := by
  simp [Constraint.HoldsInt, Constraint.HoldsScaled]

theorem satInt_iff_satScaled_one (S : List Constraint) (x : Nat → Int) :
    SatInt S x ↔ SatScaled S 1 x := by
  simp [SatInt, SatScaled, Constraint.holdsInt_iff_holdsScaled_one]

/-! ## Definition examples -/

/-- The point `x₀ = v` (all other variables `0`). -/
def pt1 (v : Int) : Nat → Int := fun i => if i = 0 then v else 0

/-- The point `(x₀, x₁) = (a, b)` (all other variables `0`). -/
def pt2 (a b : Int) : Nat → Int := fun i => if i = 0 then a else if i = 1 then b else 0

/-- Positive example: `2·x₀ - x₁ ≤ 3` holds at `(2, 1)`. -/
theorem ex_holdsInt_pos : Constraint.HoldsInt ⟨[(0, 2), (1, -1)], .le, 3⟩ (pt2 2 1) := by decide

/-- Negative example: `2·x₀ - x₁ ≤ 3` fails at `(3, 1)`. -/
theorem ex_holdsInt_neg : ¬ Constraint.HoldsInt ⟨[(0, 2), (1, -1)], .le, 3⟩ (pt2 3 1) := by decide

/-- Negative example: strictness is respected (`x₀ < 2` fails at `x₀ = 2`). -/
theorem ex_holdsInt_strict_neg : ¬ Constraint.HoldsInt ⟨[(0, 1)], .lt, 2⟩ (pt1 2) := by decide

/-- Positive example: `2·x₀ ≤ 1` holds at the rational point `x₀ = 1/2`, i.e. `(d, p) = (2, 1)`. -/
theorem ex_holdsScaled_pos : Constraint.HoldsScaled ⟨[(0, 2)], .le, 1⟩ 2 (pt1 1) := by decide

/-- Negative example: `2·x₀ ≤ 1` fails at the rational point `x₀ = 3/2`. -/
theorem ex_holdsScaled_neg : ¬ Constraint.HoldsScaled ⟨[(0, 2)], .le, 1⟩ 2 (pt1 3) := by decide

/-- Positive example: the system `{2x₀ ≤ 1, -2x₀ ≤ -1}` (i.e. `x₀ = 1/2`) holds at `(2, 1)`. -/
theorem ex_satScaled_pos :
    SatScaled [⟨[(0, 2)], .le, 1⟩, ⟨[(0, -2)], .le, -1⟩] 2 (pt1 1) := by decide

/-- Negative example: the same system has no solution among small integers. -/
theorem ex_satInt_neg :
    ∀ v : Fin 7, ¬ SatInt [⟨[(0, 2)], .le, 1⟩, ⟨[(0, -2)], .le, -1⟩] (pt1 ((v : Int) - 3)) := by
  decide

/-- Positive example: `{x₀ ≤ 1, -x₀ ≤ 0}` holds at the integer point `x₀ = 1`. -/
theorem ex_satInt_pos : SatInt [⟨[(0, 1)], .le, 1⟩, ⟨[(0, -1)], .le, 0⟩] (pt1 1) := by decide

/-- Negative example: the system `{2x₀ ≤ 1, -2x₀ ≤ -1}` (i.e. `x₀ = 1/2`) fails at the scaled
point `(d, p) = (2, 3)`, i.e. at the rational point `x₀ = 3/2`. -/
theorem ex_satScaled_neg :
    ¬ SatScaled [⟨[(0, 2)], .le, 1⟩, ⟨[(0, -2)], .le, -1⟩] 2 (pt1 3) := by decide

/-- Degenerate instance: `SatScaled` with `d = 0` is not a rational semantics: the infeasible
system `{0 ≤ -1}` is "satisfied" at `d = 0`. Theorems about rational points therefore
assume `0 < d`. -/
theorem ex_satScaled_denominator_zero_degenerate :
    SatScaled [⟨[], .le, -1⟩] 0 (fun _ => 0) := by decide

/-- Positive example: a `<` constraint is strict. -/
theorem ex_isStrict_pos : Constraint.isStrict ⟨[(0, 1)], .lt, 1⟩ = true := by decide

/-- Negative example: a `≤` constraint is not strict. -/
theorem ex_isStrict_neg : Constraint.isStrict ⟨[(0, 1)], .le, 1⟩ = false := by decide

end Toy.Farkas
