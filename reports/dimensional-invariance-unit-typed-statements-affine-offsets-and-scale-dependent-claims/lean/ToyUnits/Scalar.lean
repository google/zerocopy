/-!
# Scalars: operations as data, every law a separate named proposition

A scalar domain is a type `K` with the operations of an ordered field
(`0`, `1`, `+`, `*`, unary `-`, `⁻¹`, `≤`, `<`). No law is assumed by the class:
each law is a separate `Prop`, and theorems name the laws they use. The bundles
`CommRingLaws`, `FieldLaws` and `OrderedFieldLaws` collect the usual axioms.
The convention `0⁻¹ = 0` (`InvZeroLaw`) is deliberately kept outside every bundle.
-/

namespace Toy.Units

/-- The operations of a scalar domain (data only; no laws). -/
class ScalarOps (K : Type) extends Zero K, One K, Add K, Mul K, Neg K, Inv K, LE K, LT K

instance instScalarOpsRat : ScalarOps Rat where

section Laws
variable (K : Type) [ScalarOps K]

/-- Associativity of `+`. -/
def AddAssocLaw : Prop := ∀ a b c : K, a + b + c = a + (b + c)
/-- Commutativity of `+`. -/
def AddCommLaw : Prop := ∀ a b : K, a + b = b + a
/-- `0` is a right identity for `+`. -/
def AddZeroLaw : Prop := ∀ a : K, a + 0 = a
/-- `-a` is a right additive inverse of `a`. -/
def AddNegLaw : Prop := ∀ a : K, a + -a = 0
/-- Associativity of `*`. -/
def MulAssocLaw : Prop := ∀ a b c : K, a * b * c = a * (b * c)
/-- Commutativity of `*`. -/
def MulCommLaw : Prop := ∀ a b : K, a * b = b * a
/-- `1` is a right identity for `*`. -/
def MulOneLaw : Prop := ∀ a : K, a * 1 = a
/-- Left distributivity of `*` over `+`. -/
def DistribLaw : Prop := ∀ a b c : K, a * (b + c) = a * b + a * c
/-- Every nonzero element has `a⁻¹` as a right multiplicative inverse. -/
def MulInvLaw : Prop := ∀ a : K, a ≠ 0 → a * a⁻¹ = 1
/-- The domain is nontrivial. -/
def ZeroNeOneLaw : Prop := (0 : K) ≠ 1
/-- The total-division convention `0⁻¹ = 0`. This is a choice of junk value, not a field axiom. -/
def InvZeroLaw : Prop := (0 : K)⁻¹ = 0
/-- Reflexivity of `≤`. -/
def LeReflLaw : Prop := ∀ a : K, a ≤ a
/-- Transitivity of `≤`. -/
def LeTransLaw : Prop := ∀ a b c : K, a ≤ b → b ≤ c → a ≤ c
/-- Antisymmetry of `≤`. -/
def LeAntisymmLaw : Prop := ∀ a b : K, a ≤ b → b ≤ a → a = b
/-- Totality of `≤`. -/
def LeTotalLaw : Prop := ∀ a b : K, a ≤ b ∨ b ≤ a
/-- `<` is the strict part of `≤`. -/
def LtIffLaw : Prop := ∀ a b : K, a < b ↔ a ≤ b ∧ ¬ b ≤ a
/-- Translation preserves `≤`. -/
def AddLeMonoLaw : Prop := ∀ a b c : K, a ≤ b → a + c ≤ b + c
/-- The product of nonnegative elements is nonnegative. -/
def MulNonnegLaw : Prop := ∀ a b : K, 0 ≤ a → 0 ≤ b → 0 ≤ a * b

/-- The commutative-ring axioms, each a separate field. -/
structure CommRingLaws : Prop where
  add_assoc : AddAssocLaw K
  add_comm : AddCommLaw K
  add_zero : AddZeroLaw K
  add_neg : AddNegLaw K
  mul_assoc : MulAssocLaw K
  mul_comm : MulCommLaw K
  mul_one : MulOneLaw K
  distrib : DistribLaw K

/-- The field axioms (without any convention for `0⁻¹`). -/
structure FieldLaws : Prop extends CommRingLaws K where
  mul_inv : MulInvLaw K
  zero_ne_one : ZeroNeOneLaw K

/-- The ordered-field axioms (without any convention for `0⁻¹`). -/
structure OrderedFieldLaws : Prop extends FieldLaws K where
  le_refl : LeReflLaw K
  le_trans : LeTransLaw K
  le_antisymm : LeAntisymmLaw K
  le_total : LeTotalLaw K
  lt_iff : LtIffLaw K
  add_le_mono : AddLeMonoLaw K
  mul_nonneg : MulNonnegLaw K

end Laws

end Toy.Units
