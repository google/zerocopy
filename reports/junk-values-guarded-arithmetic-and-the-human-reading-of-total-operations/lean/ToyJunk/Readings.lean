import ToyJunk.Examples

/-!
# Lean readings of the named formulas, with explicit types

For each named formula of the package, its truth value in Lean's reading
(`evalJ leanJ`, equivalently `leanEvalF` by `evalJ_leanJ_iff`) is stated as an ordinary Lean
proposition in which every numeral and every variable has a visible type. The variables of a
formula are supplied by `envAB a b` (natural variables `vA = a` and `vB = b`), by `envX x`
(integer variable `vX = x`) or by an arbitrary environment `ρ` (`ρ.int 0` for `vX`,
`ρ.int 1` for `vY`). These theorems add no assumption: each is a definitional unfolding
of `leanEvalF`.
-/

namespace Toy.Junk

/-! ## Formulas over the natural variables `a` and `b` -/

theorem leanReading_fMulZero (a b : Nat) :
    evalJ leanJ fMulZero (envAB a b) = true ↔ (a - b) * 0 = (0 : Nat) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fSubLeSelf (a b : Nat) :
    evalJ leanJ fSubLeSelf (envAB a b) = true ↔ a - b ≤ a :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fSubAddCancel (a b : Nat) :
    evalJ leanJ fSubAddCancel (envAB a b) = true ↔ a - b + b = a :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fSubAddCancelGuarded (a b : Nat) :
    evalJ leanJ fSubAddCancelGuarded (envAB a b) = true ↔ (b ≤ a → a - b + b = a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fCastPlacement (a b : Nat) :
    evalJ leanJ fCastPlacement (envAB a b) = true ↔ ((a - b : Nat) : Int) = (a : Int) - (b : Int) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fSubAddCancelCast (a b : Nat) :
    evalJ leanJ fSubAddCancelCast (envAB a b) = true ↔
      (a : Int) - (b : Int) + (b : Int) = (a : Int) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fDvdDiv (a b : Nat) :
    evalJ leanJ fDvdDiv (envAB a b) = true ↔ (b ∣ a → a / b * b = a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fDvdDivGuarded (a b : Nat) :
    evalJ leanJ fDvdDivGuarded (envAB a b) = true ↔ (¬ b = 0 → b ∣ a → a / b * b = a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fDvdDivDividendGuard (a b : Nat) :
    evalJ leanJ fDvdDivDividendGuard (envAB a b) = true ↔ (¬ a = 0 → b ∣ a → a / b * b = a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fTrivOr (a b : Nat) :
    evalJ leanJ fTrivOr (envAB a b) = true ↔ ((0 : Nat) ≤ 0 ∨ a - b = 0) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fOrNegGuardSubCancel (a b : Nat) :
    evalJ leanJ fOrNegGuardSubCancel (envAB a b) = true ↔ (¬ b ≤ a ∨ a - b + b = a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fModDisjGuard (a b : Nat) :
    evalJ leanJ fModDisjGuard (envAB a b) = true ↔ (b = 0 ∨ a % b < b) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fContradictoryGuard (a b : Nat) :
    evalJ leanJ fContradictoryGuard (envAB a b) = true ↔ (b ≤ a ∧ a < b → a - b = 1) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fExImpGuard (a b : Nat) :
    evalJ leanJ fExImpGuard (envAB a b) = true ↔ ∃ v : Nat, v ≤ a → a - v = 1 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fExAndGuard (a b : Nat) :
    evalJ leanJ fExAndGuard (envAB a b) = true ↔ ∃ v : Nat, v ≤ a ∧ a - v = 1 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fNatDivModId (a b : Nat) :
    evalJ leanJ fNatDivModId (envAB a b) = true ↔ (¬ b = 0 → a / b * b + a % b = a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fGuardFirst (a b : Nat) :
    evalJ leanJ fGuardFirst (envAB a b) = true ↔ (b ≤ a ∧ a - b + b = a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fGuardSecond (a b : Nat) :
    evalJ leanJ fGuardSecond (envAB a b) = true ↔ (a - b + b = a ∧ b ≤ a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fContrapositive (a b : Nat) :
    evalJ leanJ fContrapositive (envAB a b) = true ↔ (¬ a - b + b = a → ¬ b ≤ a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fGuardedNatMod (a b : Nat) :
    evalJ leanJ fGuardedNatMod (envAB a b) = true ↔ (¬ b = 0 → a % b < b) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fStaleGuard (a b : Nat) :
    evalJ leanJ fStaleGuard (envAB a b) = true ↔ (b ≤ a ∧ ∀ v : Nat, a - v + v = a) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

/-! ## Formulas over the integer variable `x` (and `y`) -/

theorem leanReading_fDivZero (x : Int) :
    evalJ leanJ fDivZero (envX x) = true ↔ x / 0 = (0 : Int) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fDivZeroRefl (x : Int) :
    evalJ leanJ fDivZeroRefl (envX x) = true ↔ x / (0 : Int) = x / (0 : Int) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fDivZeroEM (x : Int) :
    evalJ leanJ fDivZeroEM (envX x) = true ↔ (x / 0 = (0 : Int) ∨ ¬ x / 0 = (0 : Int)) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fToNatGuardFirst (x : Int) :
    evalJ leanJ fToNatGuardFirst (envX x) = true ↔ (0 ≤ x ∧ x.toNat = x.toNat) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fToNatGuardSecond (x : Int) :
    evalJ leanJ fToNatGuardSecond (envX x) = true ↔ (x.toNat = x.toNat ∧ 0 ≤ x) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fToNatImp (x : Int) :
    evalJ leanJ fToNatImp (envX x) = true ↔ (0 ≤ x → x.toNat = x.toNat) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fToNatContrapose (x : Int) :
    evalJ leanJ fToNatContrapose (envX x) = true ↔ (¬ x.toNat = x.toNat → ¬ 0 ≤ x) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fGuardedToNat (x : Int) :
    evalJ leanJ fGuardedToNat (envX x) = true ↔ (0 ≤ x → ((x.toNat : Nat) : Int) = x) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fGuardedIntMod (ρ : Env) :
    evalJ leanJ fGuardedIntMod ρ = true ↔
      (0 < ρ.int 1 ∧ 0 ≤ ρ.int 0 → ρ.int 0 % ρ.int 1 < ρ.int 1) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fGuardedIntDiv (ρ : Env) :
    evalJ leanJ fGuardedIntDiv ρ = true ↔
      (¬ ρ.int 1 = 0 ∧ ρ.int 1 ∣ ρ.int 0 → ρ.int 0 / ρ.int 1 * ρ.int 1 = ρ.int 0) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

/-! ## Closed formulas (the environment is irrelevant) -/

theorem leanReading_fZeroSubOne (ρ : Env) :
    evalJ leanJ fZeroSubOne ρ = true ↔ (0 : Nat) - 1 = 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fFiveSubThree (ρ : Env) :
    evalJ leanJ fFiveSubThree ρ = true ↔ (5 : Nat) - 3 = 2 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fNumeralNat (ρ : Env) :
    evalJ leanJ fNumeralNat ρ = true ↔ (2 : Nat) - 3 < 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fNumeralInt (ρ : Env) :
    evalJ leanJ fNumeralInt ρ = true ↔ (2 : Int) - 3 < 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fTruncSubCancel01 (ρ : Env) :
    evalJ leanJ fTruncSubCancel01 ρ = true ↔ (0 : Nat) - 1 + 1 = 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fTruncSubLe01 (ρ : Env) :
    evalJ leanJ fTruncSubLe01 ρ = true ↔ (0 : Nat) - 1 ≤ 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fFiveDivZero (ρ : Env) :
    evalJ leanJ fFiveDivZero ρ = true ↔ (5 : Int) / 0 = 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fFiveModZero (ρ : Env) :
    evalJ leanJ fFiveModZero ρ = true ↔ (5 : Nat) % 0 = 5 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fFloorDiv (ρ : Env) :
    evalJ leanJ fFloorDiv ρ = true ↔ (7 : Nat) / 2 * 2 = 7 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fNegSevenDivTwo (ρ : Env) :
    evalJ leanJ fNegSevenDivTwo ρ = true ↔ (-7 : Int) / 2 = -4 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fSevenDivNegTwo (ρ : Env) :
    evalJ leanJ fSevenDivNegTwo ρ = true ↔ (7 : Int) / (-2) = -3 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fNegSevenModTwo (ρ : Env) :
    evalJ leanJ fNegSevenModTwo ρ = true ↔ (-7 : Int) % 2 = 1 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fSevenModNegTwo (ρ : Env) :
    evalJ leanJ fSevenModNegTwo ρ = true ↔ (7 : Int) % (-2) = 1 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fCastPlacement01 (ρ : Env) :
    evalJ leanJ fCastPlacement01 ρ = true ↔
      (((0 : Nat) - 1 : Nat) : Int) = ((0 : Nat) : Int) - ((1 : Nat) : Int) :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fToNatNeg (ρ : Env) :
    evalJ leanJ fToNatNeg ρ = true ↔ (-3 : Int).toNat = 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fSevenDivTwo (ρ : Env) :
    evalJ leanJ fSevenDivTwo ρ = true ↔ (7 : Nat) / 2 = 3 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fSevenModTwo (ρ : Env) :
    evalJ leanJ fSevenModTwo ρ = true ↔ (7 : Nat) % 2 = 1 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fOneDivTwo (ρ : Env) :
    evalJ leanJ fOneDivTwo ρ = true ↔ (1 : Nat) / 2 = 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

/-! ## Closed quantified formulas -/

theorem leanReading_fBoundedCancel (ρ : Env) :
    evalJ leanJ fBoundedCancel ρ = true ↔ ∀ a b : Nat, b ≤ a → a - b + b = a :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fUnboundedCancel (ρ : Env) :
    evalJ leanJ fUnboundedCancel ρ = true ↔ ∀ a b : Nat, a - b + b = a :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fAllZeroLeSubOne (ρ : Env) :
    evalJ leanJ fAllZeroLeSubOne ρ = true ↔ ∀ a : Nat, 0 ≤ a - 1 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fAllSubSucc (ρ : Env) :
    evalJ leanJ fAllSubSucc ρ = true ↔ ∀ a : Nat, a - (a + 1) = 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fExSubSuccNe (ρ : Env) :
    evalJ leanJ fExSubSuccNe ρ = true ↔ ∃ a : Nat, ¬ a - (a + 1) = 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

theorem leanReading_fAllOneDivZero (ρ : Env) :
    evalJ leanJ fAllOneDivZero ρ = true ↔ ∀ n : Nat, 2 < n → 1 / n = 0 :=
  (evalJ_leanJ_iff _ _).trans Iff.rfl

end Toy.Junk
