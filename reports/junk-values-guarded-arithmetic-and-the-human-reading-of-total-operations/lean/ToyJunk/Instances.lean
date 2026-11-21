import ToyJunk.Lemmas

/-!
# Named variables, environments, and formulas used throughout the package
-/

namespace Toy.Junk

/-- Natural variable `a` (index 0). -/
abbrev vA : Term .nat := .natVar 0
/-- Natural variable `b` (index 1). -/
abbrev vB : Term .nat := .natVar 1
/-- Integer variable `x` (index 0). -/
abbrev vX : Term .int := .intVar 0

/-- The environment with `a = x`, `b = y` (natural variables 0 and 1) and every other
variable `0`. -/
def envAB (x y : Nat) : Env := ⟨fun i => if i = 0 then x else if i = 1 then y else 0, fun _ => 0⟩

/-- `(a - b) * 0 = 0` at `Nat`. -/
def fMulZero : Formula := .eq (.mul (.sub vA vB) (.natLit 0)) (.natLit 0)

/-- `a - b ≤ a` at `Nat`. -/
def fSubLeSelf : Formula := .le (.sub vA vB) vA

/-- `a - b + b = a` at `Nat`. -/
def fSubAddCancel : Formula := .eq (.add (.sub vA vB) vB) vA

/-- `b ≤ a → a - b + b = a` at `Nat` (the guarded restatement of `fSubAddCancel`). -/
def fSubAddCancelGuarded : Formula := .imp (.le vB vA) fSubAddCancel

/-- `0 - 1 = 0` at `Nat`. -/
def fZeroSubOne : Formula := .eq (.sub (.natLit 0) (.natLit 1)) (.natLit 0)

/-- `5 - 3 = 2` at `Nat` (a partial operation used inside its domain). -/
def fFiveSubThree : Formula := .eq (.sub (.natLit 5) (.natLit 3)) (.natLit 2)

/-- `x / 0 = 0` at `Int`. -/
def fDivZero : Formula := .eq (.div vX (.intLit 0)) (.intLit 0)

/-- `2 - 3 < 0` with every literal at `Nat`. -/
def fNumeralNat : Formula := .lt (.sub (.natLit 2) (.natLit 3)) (.natLit 0)

/-- `2 - 3 < 0` with every literal at `Int`. -/
def fNumeralInt : Formula := .lt (.sub (.intLit 2) (.intLit 3)) (.intLit 0)

/-- `x / 0 = x / 0` at `Int` (reflexivity of a junk term; no multiplication). -/
def fDivZeroRefl : Formula := .eq (.div vX (.intLit 0)) (.div vX (.intLit 0))

/-- `x / 0 = 0 ∨ ¬ (x / 0 = 0)` at `Int` (excluded middle over a junk term). -/
def fDivZeroEM : Formula := .or fDivZero (.not fDivZero)

end Toy.Junk
