import ToyFarkas.Checker

/-!
# Necessity of the checker's side conditions

Each counterexample below is in canonical form: a concrete system and certificate for
which every *other* condition of `farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts`
holds, yet the system is satisfiable (the conclusion fails). Further counterexamples show
that common variants of the strictness bookkeeping and of the zero test are unsound.
-/

namespace Toy.Farkas

/-! ## Dropping one condition of the structured soundness theorem -/

/-- `{x₀ ≤ 1, x₀ ≤ 2}`: satisfiable (e.g. at `x₀ = 0`). -/
def sysTwoUpper : List Constraint := [⟨[(0, 1)], .le, 1⟩, ⟨[(0, 1)], .le, 2⟩]

/-- **A negative multiplier "certifies" a satisfiable system.** With multipliers `(1, -1)`
the combination of `{x₀ ≤ 1, x₀ ≤ 2}` is `0 ≤ -1`: the left-hand side vanishes and the
right-hand side contradicts, `d = 1 > 0`, yet `x₀ = 0` satisfies the system (as an integer
point and as the rational point `(d, p) = (1, 0)`). Only `multipliersNonneg` fails. -/
theorem ce_farkas_negative_multiplier :
    multipliersNonneg [1, -1] = false ∧
    lhsVanishes sysTwoUpper [1, -1] = true ∧
    rhsContradicts sysTwoUpper [1, -1] = true ∧
    (0 : Int) < 1 ∧
    SatScaled sysTwoUpper 1 (pt1 0) ∧ SatInt sysTwoUpper (pt1 0) := by decide

/-- **Dropping `lhsVanishes`.** `{x₀ ≤ -1}` with multiplier `1`: non-negative, right-hand side
`-1 < 0` contradicts, but the left-hand side `x₀` does not vanish and `x₀ = -1` is a solution. -/
theorem ce_farkas_lhs_not_vanishing :
    multipliersNonneg [1] = true ∧
    lhsVanishes [⟨[(0, 1)], .le, -1⟩] [1] = false ∧
    rhsContradicts [⟨[(0, 1)], .le, -1⟩] [1] = true ∧
    (0 : Int) < 1 ∧
    SatScaled [⟨[(0, 1)], .le, -1⟩] 1 (pt1 (-1)) := by decide

/-- **Dropping `rhsContradicts`.** `{x₀ ≤ 1, -x₀ ≤ -1}` with `(1, 1)`: non-negative, the
left-hand side vanishes, but the conclusion `0 ≤ 0` is not contradictory and `x₀ = 1` is a
solution. -/
theorem ce_farkas_rhs_not_contradicting :
    multipliersNonneg [1, 1] = true ∧
    lhsVanishes sysEq [1, 1] = true ∧
    rhsContradicts sysEq [1, 1] = false ∧
    (0 : Int) < 1 ∧
    SatScaled sysEq 1 (pt1 1) := by decide

/-- **Dropping `0 < d`.** For `{0 ≤ -1}` (empty left-hand side) the certificate `(1)` passes
all three checks, yet the scaled point with `d = 0` satisfies the scaled system, because
`0 ≤ -1 * 0`. So `0 < d` is needed for the scaled reading to mean "rational point". -/
theorem ce_farkas_denominator_zero :
    checkFarkas [⟨[], .le, -1⟩] [1] = true ∧
    multipliersNonneg [1] = true ∧
    lhsVanishes [⟨[], .le, -1⟩] [1] = true ∧
    rhsContradicts [⟨[], .le, -1⟩] [1] = true ∧
    ¬ ((0 : Int) < 0) ∧
    SatScaled [⟨[], .le, -1⟩] 0 (fun _ => 0) := by decide

/-! ## Strict versus non-strict bookkeeping -/

/-- A buggy contradiction test that treats every combination as strict (accepts `0 ≤ 0`). -/
def rhsContradictsIgnoringStrictness (S : List Constraint) (cert : List Int) : Bool :=
  decide (combineRhs S cert ≤ 0)

/-- A buggy strictness flag: the combination is declared strict when *any* premise is strict,
even one whose multiplier is `0`. -/
def combineStrictAnyPremise (S : List Constraint) (_cert : List Int) : Bool :=
  S.any Constraint.isStrict

/-- The contradiction test using the buggy strictness flag. -/
def rhsContradictsAnyPremise (S : List Constraint) (cert : List Int) : Bool :=
  if combineStrictAnyPremise S cert then decide (combineRhs S cert ≤ 0)
  else decide (combineRhs S cert < 0)

theorem ex_rhsContradictsIgnoringStrictness_pos :
    rhsContradictsIgnoringStrictness sysEq [1, 1] = true := by decide
theorem ex_rhsContradictsIgnoringStrictness_neg :
    rhsContradictsIgnoringStrictness sysTwoUpper [1, 0] = false := by decide

/-- `{x₀ ≤ 1, -x₀ ≤ -1, x₁ < 5}`: satisfiable at `(x₀, x₁) = (1, 0)`. -/
def sysEqPlusStrict : List Constraint :=
  [⟨[(0, 1)], .le, 1⟩, ⟨[(0, -1)], .le, -1⟩, ⟨[(1, 1)], .lt, 5⟩]

theorem ex_combineStrictAnyPremise_pos : combineStrictAnyPremise sysEqPlusStrict [1, 1, 0] = true := by
  decide
theorem ex_combineStrictAnyPremise_neg : combineStrictAnyPremise sysEq [1, 1] = false := by decide

/-- Positive example: with the buggy flag, the derived `0 ≤ 0` of `sysEqPlusStrict` is misread as
`0 < 0`, which is contradictory. -/
theorem ex_rhsContradictsAnyPremise_pos :
    rhsContradictsAnyPremise sysEqPlusStrict [1, 1, 0] = true := by decide

/-- Negative example: without any strict premise the buggy test agrees with `rhsContradicts` and
rejects `0 ≤ 0`; it is not the constant `true`. -/
theorem ex_rhsContradictsAnyPremise_neg : rhsContradictsAnyPremise sysEq [1, 1] = false := by decide

/-- **Non-strict conclusion read as strict.** If `0 ≤ 0` is treated as contradictory (as when
strictness is ignored), the satisfiable `{x₀ ≤ 1, -x₀ ≤ -1}` is "certified" by `(1, 1)`. -/
theorem ce_farkas_strictness_ignored :
    multipliersNonneg [1, 1] = true ∧
    lhsVanishes sysEq [1, 1] = true ∧
    rhsContradictsIgnoringStrictness sysEq [1, 1] = true ∧
    rhsContradicts sysEq [1, 1] = false ∧ checkFarkas sysEq [1, 1] = false ∧
    (0 : Int) < 1 ∧ SatInt sysEq (pt1 1) ∧ SatScaled sysEq 1 (pt1 1) := by decide

/-- **Strictness taken from a zero-weighted premise.** If the combination is declared strict
because *some* premise is strict, then `(1, 1, 0)` "certifies" the satisfiable
`{x₀ ≤ 1, -x₀ ≤ -1, x₁ < 5}`: the derived `0 ≤ 0` is misread as `0 < 0`. -/
theorem ce_farkas_strict_flag_from_zero_weight :
    multipliersNonneg [1, 1, 0] = true ∧
    lhsVanishes sysEqPlusStrict [1, 1, 0] = true ∧
    rhsContradictsAnyPremise sysEqPlusStrict [1, 1, 0] = true ∧
    rhsContradicts sysEqPlusStrict [1, 1, 0] = false ∧
    SatInt sysEqPlusStrict (pt2 1 0) := by decide

/-! ## Integer tightening of strict constraints -/

/-- Integer tightening: `lhs · x < b` becomes `lhs · x ≤ b - 1` (equivalent over integers). -/
def Constraint.tighten (c : Constraint) : Constraint :=
  match c.rel with
  | .le => c
  | .lt => ⟨c.lhs, .le, c.rhs - 1⟩

/-- The Farkas checker run on the integer-tightened system. -/
def checkFarkasTightened (S : List Constraint) (cert : List Int) : Bool :=
  checkFarkas (S.map Constraint.tighten) cert

theorem ex_tighten_pos : Constraint.tighten ⟨[(0, 1)], .lt, 1⟩ = ⟨[(0, 1)], .le, 0⟩ := by decide
theorem ex_tighten_neg : Constraint.tighten ⟨[(0, 1)], .le, 1⟩ ≠ ⟨[(0, 1)], .le, 0⟩ := by decide

theorem Constraint.holdsInt_tighten_iff (c : Constraint) (x : Nat → Int) :
    c.tighten.HoldsInt x ↔ c.HoldsInt x := by
  obtain ⟨lhs, rel, rhs⟩ := c
  cases rel <;> simp [Constraint.tighten, Constraint.HoldsInt, Rel.Sat] <;> omega

/-- **Integer tightening is sound over integers.** If the checker accepts the tightened system,
the original system has no integer solution. -/
theorem checkFarkasTightened_sound_int (S : List Constraint) (cert : List Int)
    (h : checkFarkasTightened S cert = true) (x : Nat → Int) : ¬ SatInt S x := by
  intro hx
  apply checkFarkas_sound_int _ cert h x
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  exact (Constraint.holdsInt_tighten_iff c' x).mpr (hx c' hc')

/-- The acceptance hypothesis of `checkFarkasTightened_sound_int` cannot be dropped: the
satisfiable `sysEq` is rejected with `(1, 1)` and has the integer solution `x₀ = 1`. -/
theorem ce_checkFarkasTightened_rejects_satisfiable :
    checkFarkasTightened sysEq [1, 1] = false ∧ SatInt sysEq (pt1 1) := by decide

/-- `{x₀ < 1, -x₀ < 0}`, i.e. `0 < x₀ < 1`: no integer solution, rational solution `1/2`. -/
def sysOpenUnit : List Constraint := [⟨[(0, 1)], .lt, 1⟩, ⟨[(0, -1)], .lt, 0⟩]

/-- Non-vacuity of `checkFarkasTightened_sound_int`. -/
theorem nv_checkFarkasTightened : checkFarkasTightened sysOpenUnit [1, 1] = true := by decide

/-- **Integer tightening is unsound over the rationals.** The tightened checker accepts
`{x₀ < 1, -x₀ < 0}`, which the rational point `x₀ = 1/2` (`(d, p) = (2, 1)`) satisfies; the
untightened checker rejects the same certificate. -/
theorem ce_tightening_unsound_over_rat :
    checkFarkasTightened sysOpenUnit [1, 1] = true ∧
    checkFarkas sysOpenUnit [1, 1] = false ∧
    (0 : Int) < 2 ∧ SatScaled sysOpenUnit 2 (pt1 1) := by decide

/-! ## Zero tests that ignore the dense semantics -/

/-- A buggy zero test that ignores indices: the coefficients sum to zero. -/
def isZeroIndexBlind (v : SparseVec) : Bool := (v.map Prod.snd).sum == 0

/-- A buggy zero test that reads only the first entry recorded for each index. -/
def coeffFirstMatch (v : SparseVec) (i : Nat) : Int :=
  match v.find? (fun p => p.1 == i) with
  | some p => p.2
  | none => 0

def isZeroFirstMatch (v : SparseVec) : Bool := v.all (fun p => coeffFirstMatch v p.1 == 0)

theorem ex_isZeroIndexBlind_pos : isZeroIndexBlind [(0, 1), (0, -1)] = true := by decide
theorem ex_isZeroIndexBlind_neg : isZeroIndexBlind [(0, 1), (1, 1)] = false := by decide
theorem ex_isZeroFirstMatch_pos : isZeroFirstMatch [(0, 0), (1, 0)] = true := by decide
theorem ex_isZeroFirstMatch_neg : isZeroFirstMatch [(0, 0), (1, 2)] = false := by decide
/-- Positive example: `coeffFirstMatch` returns the first entry recorded for the index. -/
theorem ex_coeffFirstMatch_pos : coeffFirstMatch [(0, 0), (0, 1)] 0 = 0 := by decide
/-- Negative example: it is not the dense coefficient (`coeff [(0, 0), (0, 1)] 0 = 1`). -/
theorem ex_coeffFirstMatch_neg :
    coeffFirstMatch [(0, 0), (0, 1)] 0 ≠ SparseVec.coeff [(0, 0), (0, 1)] 0 := by decide

/-- **An index-blind zero test is unsound.** `{x₀ - x₁ ≤ -1}` with multiplier `1`: the
coefficients sum to `0` and `-1 < 0`, yet `(x₀, x₁) = (0, 1)` is a solution. -/
theorem ce_zero_test_index_blind :
    multipliersNonneg [1] = true ∧
    checkFarkas [⟨[(0, 1), (1, -1)], .le, -1⟩] [1] = false ∧
    isZeroIndexBlind (combineLhs [⟨[(0, 1), (1, -1)], .le, -1⟩] [1]) = true ∧
    lhsVanishes [⟨[(0, 1), (1, -1)], .le, -1⟩] [1] = false ∧
    rhsContradicts [⟨[(0, 1), (1, -1)], .le, -1⟩] [1] = true ∧
    SatInt [⟨[(0, 1), (1, -1)], .le, -1⟩] (pt2 0 1) := by decide

/-- **A first-match zero test is unsound in the presence of duplicate indices.**
`{0·x₀ + 1·x₀ ≤ -1}` (written with a duplicate entry) with multiplier `1`: the first entry
for index `0` is `0`, so a first-match test declares the form zero, yet `x₀ = -1` is a
solution. -/
theorem ce_zero_test_first_match :
    multipliersNonneg [1] = true ∧
    checkFarkas [⟨[(0, 0), (0, 1)], .le, -1⟩] [1] = false ∧
    isZeroFirstMatch (combineLhs [⟨[(0, 0), (0, 1)], .le, -1⟩] [1]) = true ∧
    lhsVanishes [⟨[(0, 0), (0, 1)], .le, -1⟩] [1] = false ∧
    rhsContradicts [⟨[(0, 0), (0, 1)], .le, -1⟩] [1] = true ∧
    SatInt [⟨[(0, 0), (0, 1)], .le, -1⟩] (pt1 (-1)) := by decide

/-- **Duplicate-free inputs do not make first-match lookup safe.** Each premise of
`{x₀ ≤ 0, x₀ ≤ -1}` has a single entry, but the combination with multipliers `(0, 1)` is
`[(0, 0), (0, 1)]`: the zero multiplier inserts the entry `(0, 0)` ahead of `(0, 1)`. A first-match
test declares it zero, `-1 < 0` contradicts, yet `x₀ = -1` is a solution. -/
theorem ce_zero_test_first_match_dupfree_inputs :
    combineLhs [⟨[(0, 1)], .le, 0⟩, ⟨[(0, 1)], .le, -1⟩] [0, 1] = [(0, 0), (0, 1)] ∧
    multipliersNonneg [0, 1] = true ∧
    checkFarkas [⟨[(0, 1)], .le, 0⟩, ⟨[(0, 1)], .le, -1⟩] [0, 1] = false ∧
    isZeroFirstMatch (combineLhs [⟨[(0, 1)], .le, 0⟩, ⟨[(0, 1)], .le, -1⟩] [0, 1]) = true ∧
    rhsContradicts [⟨[(0, 1)], .le, 0⟩, ⟨[(0, 1)], .le, -1⟩] [0, 1] = true ∧
    SatInt [⟨[(0, 1)], .le, 0⟩, ⟨[(0, 1)], .le, -1⟩] (pt1 (-1)) := by decide

end Toy.Farkas
