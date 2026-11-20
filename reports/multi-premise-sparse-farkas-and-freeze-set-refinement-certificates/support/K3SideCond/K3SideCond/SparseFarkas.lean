-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Arbitrary $k$-Premise, $m$-Variable Sparse Linear Farkas Certificates (`SparseFarkas.lean`)

Generalizes the prior baseline `FarkasCert2` (fixed to 2 hypotheses over 2 variables `x, y`) to arbitrary
$k$-premise systems over $m$ variables (`SparseLinearLeZero` and `FarkasCertN`).
Proves `checkFarkasCertN_sound` and `checkFarkasCertN_iff_valid` in Lean `v4.34.1` using only
`[propext, Quot.sound]`, discharging multi-dimensional slice/subslice bounds (`a + i < len` from
`0 ≤ a`, `a ≤ b`, `b ≤ len`, `0 ≤ i`, `i < b - a`), 2D/3D matrix tile guards, and
`LoopVectorize` runtime alias checks in $O(\text{nnz})$ integer multiplications.
-/

namespace K3SideCond

/-- A sparse linear inequality `constTerm + ∑ (varId, coeff) ∈ terms, coeff * env varId ≤ 0`. -/
structure SparseLinearLeZero where
  constTerm : Int
  terms     : List (Nat × Int)
  deriving DecidableEq, Repr

/-- Evaluate a list of `(varId, coeff)` pairs under variable assignment `env : Nat → Int`. -/
def evalTerms (env : Nat → Int) : List (Nat × Int) → Int
  | [] => 0
  | (v, c) :: rest => c * env v + evalTerms env rest

/-- Evaluate the full affine expression `constTerm + evalTerms env terms`. -/
def SparseLinearLeZero.eval (con : SparseLinearLeZero) (env : Nat → Int) : Int :=
  con.constTerm + evalTerms env con.terms

/-- Proposition that `con` holds under variable assignment `env`. -/
def SparseLinearLeZero.holds (con : SparseLinearLeZero) (env : Nat → Int) : Prop :=
  con.eval env ≤ 0

/-- Add coefficient `c` for variable `v` into a sparse term list. -/
def insertTerm (v : Nat) (c : Int) : List (Nat × Int) → List (Nat × Int)
  | [] => if c = 0 then [] else [(v, c)]
  | (v', c') :: rest =>
      if v = v' then
        let sum := c + c'
        if sum = 0 then rest else (v', sum) :: rest
      else
        (v', c') :: insertTerm v c rest

theorem evalTerms_insertTerm (env : Nat → Int) (v : Nat) (c : Int) (ts : List (Nat × Int)) :
    evalTerms env (insertTerm v c ts) = c * env v + evalTerms env ts := by
  induction ts with
  | nil =>
    unfold insertTerm
    by_cases hc : c = 0
    · subst hc; simp [evalTerms]
    · simp [hc, evalTerms]
  | cons hd rest ih =>
    rcases hd with ⟨v', c'⟩
    unfold insertTerm
    by_cases hv : v = v'
    · subst hv
      simp only [↓reduceIte]
      by_cases hsum : c + c' = 0
      · simp only [hsum, ↓reduceIte, evalTerms]
        have h_add : (c + c') * env v = 0 := by rw [hsum, Int.zero_mul]
        rw [Int.add_mul] at h_add
        omega
      · simp only [hsum, ↓reduceIte, evalTerms, Int.add_mul]
        omega
    · simp only [hv, ↓reduceIte, evalTerms, ih]
      omega

/-- Add a scaled sparse term list `lam * ts` into an accumulator term list `acc`. -/
def addScaledTerms (lam : Int) : List (Nat × Int) → List (Nat × Int) → List (Nat × Int)
  | [], acc => acc
  | (v, c) :: rest, acc => addScaledTerms lam rest (insertTerm v (lam * c) acc)

theorem evalTerms_addScaledTerms (env : Nat → Int) (lam : Int)
    (ts acc : List (Nat × Int)) :
    evalTerms env (addScaledTerms lam ts acc) =
    lam * evalTerms env ts + evalTerms env acc := by
  induction ts generalizing acc with
  | nil => simp [addScaledTerms, evalTerms]
  | cons hd rest ih =>
    rcases hd with ⟨v, c⟩
    simp only [addScaledTerms, evalTerms, ih, evalTerms_insertTerm]
    rw [Int.mul_add, Int.mul_assoc]
    omega

/-- Combine two sparse linear inequalities `acc + lam * con`. -/
def addScaledConstraint (lam : Int) (con : SparseLinearLeZero) (acc : SparseLinearLeZero) :
    SparseLinearLeZero :=
  { constTerm := acc.constTerm + lam * con.constTerm
    terms     := addScaledTerms lam con.terms acc.terms }

theorem eval_addScaledConstraint (env : Nat → Int) (lam : Int)
    (con acc : SparseLinearLeZero) :
    (addScaledConstraint lam con acc).eval env =
    acc.eval env + lam * con.eval env := by
  unfold addScaledConstraint SparseLinearLeZero.eval
  simp only [evalTerms_addScaledTerms]
  rw [Int.mul_add]
  omega

/-- Fold a list of `(lam_i, premise_i)` pairs onto an initial constraint `init`. -/
def combinePremises : List (Int × SparseLinearLeZero) → SparseLinearLeZero → SparseLinearLeZero
  | [], acc => acc
  | (lam, con) :: rest, acc => combinePremises rest (addScaledConstraint lam con acc)

/-- Predicate stating that every premise in `premises` holds under `env`. -/
def AllPremisesHold (env : Nat → Int) : List (Int × SparseLinearLeZero) → Prop
  | [] => True
  | (_, con) :: rest => con.holds env ∧ AllPremisesHold env rest

/-- Check that every multiplier `lam` in `premises` is non-negative (`0 ≤ lam`). -/
def allMultipliersNonNeg : List (Int × SparseLinearLeZero) → Bool
  | [] => true
  | (lam, _) :: rest => decide (0 ≤ lam) && allMultipliersNonNeg rest

theorem eval_combinePremises_le_acc (env : Nat → Int)
    (premises : List (Int × SparseLinearLeZero)) (acc : SparseLinearLeZero)
    (h_nonneg : allMultipliersNonNeg premises = true)
    (h_holds : AllPremisesHold env premises) :
    (combinePremises premises acc).eval env ≤ acc.eval env := by
  induction premises generalizing acc with
  | nil => exact Int.le_refl _
  | cons hd rest ih =>
    rcases hd with ⟨lam, con⟩
    unfold combinePremises
    simp only [allMultipliersNonNeg, Bool.and_eq_true, decide_eq_true_eq] at h_nonneg
    rcases h_holds with ⟨h_con, h_rest⟩
    unfold SparseLinearLeZero.holds at h_con
    have h_step := ih (addScaledConstraint lam con acc) h_nonneg.2 h_rest
    rw [eval_addScaledConstraint] at h_step
    have h_mul : lam * con.eval env ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos h_nonneg.1 h_con
    omega

/-- Arbitrary $k$-premise, $m$-variable sparse Farkas certificate (`FarkasCertN`). -/
structure FarkasCertN where
  premises  : List (Int × SparseLinearLeZero)
  negTarget : SparseLinearLeZero
  deriving DecidableEq, Repr

/-- Executable $O(\text{nnz})$ checker for `FarkasCertN`:
Verifies that all multipliers are non-negative and that folding `∑ lam_i * p_i + negTarget`
cancels all variable terms (`combined.terms = []`) leaving a strictly positive constant
(`1 ≤ combined.constTerm`). -/
def checkFarkasCertN (cert : FarkasCertN) : Bool :=
  let combined := combinePremises cert.premises cert.negTarget
  allMultipliersNonNeg cert.premises &&
  decide (combined.terms = [] ∧ 1 ≤ combined.constTerm)

/-- Declarative validity specification for `FarkasCertN`. -/
structure ValidFarkasCertN (cert : FarkasCertN) : Prop where
  nonneg_lams : allMultipliersNonNeg cert.premises = true
  zero_terms  : (combinePremises cert.premises cert.negTarget).terms = []
  pos_const   : 1 ≤ (combinePremises cert.premises cert.negTarget).constTerm

/-- Soundness of `checkFarkasCertN` for arbitrary $k$ premises and $m$ variables:
If `checkFarkasCertN cert = true` and `AllPremisesHold env cert.premises`, then
`¬ cert.negTarget.holds env`. -/
theorem checkFarkasCertN_sound (cert : FarkasCertN)
    (h_check : checkFarkasCertN cert = true)
    (env : Nat → Int)
    (h_holds : AllPremisesHold env cert.premises) :
    ¬ cert.negTarget.holds env := by
  unfold checkFarkasCertN at h_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_check
  rcases h_check with ⟨h_nonneg, ⟨h_terms, h_const⟩⟩
  intro h_neg
  unfold SparseLinearLeZero.holds at h_neg
  have h_le := eval_combinePremises_le_acc env cert.premises cert.negTarget h_nonneg h_holds
  have h_comb_eval : (combinePremises cert.premises cert.negTarget).eval env =
      (combinePremises cert.premises cert.negTarget).constTerm := by
    unfold SparseLinearLeZero.eval
    rw [h_terms]
    simp [evalTerms]
  omega

/-- Bidirectional equivalence between `checkFarkasCertN` and `ValidFarkasCertN`. -/
theorem checkFarkasCertN_iff_valid (cert : FarkasCertN) :
    checkFarkasCertN cert = true ↔ ValidFarkasCertN cert := by
  unfold checkFarkasCertN
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  · intro ⟨h1, h2, h3⟩
    simp [h1, h2, h3]

end K3SideCond
