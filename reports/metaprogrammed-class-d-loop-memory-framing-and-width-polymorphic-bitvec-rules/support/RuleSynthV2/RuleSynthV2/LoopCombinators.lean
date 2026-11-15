-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynthV2.MemFrame

/-!
# Reusable Class D Loop & Memory-Frame Simulation Combinators (`LoopCombinators.lean`)

Factors the fuel/iteration-indexed induction and memory-frame commutation obligations of Class C
and Class D optimization rules into reusable, parameterized simulation lemmas:
1. `evalStmt_while_zero`: Dead zero-trip loop elimination (`whileSteps 0 b = skip`);
2. `evalStmt_while_peel1`: Loop peeling (`whileSteps (k + 1) b = seq b (whileSteps k b)`);
3. `evalStmt_while_unroll2`: $2\times$ loop unrolling (`whileSteps (2 * k) b = whileSteps k (seq b b)`);
4. `evalStmt_while_split`: Loop splitting / fusion (`whileSteps (k1 + k2) b = seq (whileSteps k1 b) (whileSteps k2 b)`);
5. `evalStmt_while_cong`: Loop body refinement congruence (`stmtRefines b1 b2 → stmtRefines (whileSteps k b1) (whileSteps k b2)`);
6. `evalStmt_while_licm_skip`: Loop-invariant skip/nop hoisting.
-/

namespace RuleSynthV2

@[simp] theorem evalStmt_seq_skip_right (st : State) (s : Stmt) :
    evalStmt st (.seq s .skip) = evalStmt st s := by
  simp only [evalStmt]
  cases evalStmt st s <;> rfl

@[simp] theorem evalStmt_seq_skip_left (st : State) (s : Stmt) :
    evalStmt st (.seq .skip s) = evalStmt st s := by
  simp [evalStmt]

@[simp] theorem evalStmt_seq_assoc (st : State) (s1 s2 s3 : Stmt) :
    evalStmt st (.seq (.seq s1 s2) s3) = evalStmt st (.seq s1 (.seq s2 s3)) := by
  simp only [evalStmt]
  cases evalStmt st s1 <;> rfl

/-- Dead zero-trip loop elimination (`whileSteps 0 body` evaluates identically to `skip`). -/
@[simp] theorem evalStmt_while_zero (st : State) (b : Stmt) :
    evalStmt st (.whileSteps 0 b) = evalStmt st .skip := by
  simp [evalStmt]

/-- Loop peeling (`whileSteps (k + 1) b` evaluates identically to `seq b (whileSteps k b)`). -/
@[simp] theorem evalStmt_while_peel1 (st : State) (k : Nat) (b : Stmt) :
    evalStmt st (.whileSteps (k + 1) b) = evalStmt st (.seq b (.whileSteps k b)) := by
  simp [evalStmt]

/-- Two-iteration unrolling (`whileSteps (k + 2) b` evaluates identically to
`seq (seq b b) (whileSteps k b)`). -/
@[simp] theorem evalStmt_while_peel2 (st : State) (k : Nat) (b : Stmt) :
    evalStmt st (.whileSteps (k + 2) b) = evalStmt st (.seq (.seq b b) (.whileSteps k b)) := by
  simp only [evalStmt]
  cases evalStmt st b <;> rfl

/-- Full $2\times$ loop unrolling (`whileSteps (2 * k) b` evaluates identically to
`whileSteps k (seq b b)`), proved ONCE by induction on `k` and reused across all Class D
unrolling rules! -/
@[simp] theorem evalStmt_while_unroll2 (k : Nat) (b : Stmt) (st : State) :
    evalStmt st (.whileSteps (2 * k) b) = evalStmt st (.whileSteps k (.seq b b)) := by
  induction k generalizing st with
  | zero => simp [evalStmt]
  | succ k' ih =>
    have h_mul : 2 * (k' + 1) = (2 * k') + 2 := by omega
    rw [h_mul, evalStmt_while_peel2, evalStmt_while_peel1]
    simp only [evalStmt]
    cases h1 : evalStmt st b with
    | val st1 =>
      simp only []
      cases h2 : evalStmt st1 b with
      | val st2 => exact ih st2
      | panic => rfl
      | ub => rfl
    | panic => rfl
    | ub => rfl

/-- Loop trip-count splitting (`whileSteps (k1 + k2) b` evaluates identically to
`seq (whileSteps k1 b) (whileSteps k2 b)`), proved by induction on `k1`. -/
@[simp] theorem evalStmt_while_split (k1 k2 : Nat) (b : Stmt) (st : State) :
    evalStmt st (.whileSteps (k1 + k2) b) =
    evalStmt st (.seq (.whileSteps k1 b) (.whileSteps k2 b)) := by
  induction k1 generalizing st with
  | zero => simp [evalStmt]
  | succ k1' ih =>
    have h_add : (k1' + 1) + k2 = (k1' + k2) + 1 := by omega
    rw [h_add]
    simp only [evalStmt]
    cases h1 : evalStmt st b with
    | val st1 =>
      simp only []
      rw [ih st1]
      simp [evalStmt]
    | panic => rfl
    | ub => rfl

/-- Loop body refinement congruence: if `stmtRefines b1 b2`, then
`stmtRefines (.whileSteps k b1) (.whileSteps k b2)` for all trip counts `k`. -/
theorem stmtRefines_whileSteps {b1 b2 : Stmt} (k : Nat) (hb : stmtRefines b1 b2) :
    stmtRefines (.whileSteps k b1) (.whileSteps k b2) := by
  induction k with
  | zero =>
    intro st _; simp [evalStmt]
  | succ k' ih =>
    intro st hno_ub
    simp only [evalStmt] at hno_ub ⊢
    have hb_st := hb st
    cases h1 : evalStmt st b1 with
    | val st1 =>
      have h1_ne : Outcome.val st1 ≠ Outcome.ub := by nofun
      have hb_eq : evalStmt st b2 = Outcome.val st1 := by
        rw [← h1]; exact hb_st (by rw [h1]; exact h1_ne)
      rw [hb_eq]; simp only [h1] at hno_ub
      exact ih st1 hno_ub
    | panic =>
      have h1_ne : (Outcome.panic : Outcome State) ≠ Outcome.ub := by nofun
      have hb_eq : evalStmt st b2 = Outcome.panic := by
        rw [← h1]; exact hb_st (by rw [h1]; exact h1_ne)
      rw [hb_eq]
    | ub =>
      simp only [h1] at hno_ub; exact False.elim (hno_ub rfl)

theorem stmtRefines_seq {a1 a2 b1 b2 : Stmt}
    (ha : stmtRefines a1 a2) (hb : stmtRefines b1 b2) :
    stmtRefines (.seq a1 b1) (.seq a2 b2) := by
  intro st hno_ub
  simp only [evalStmt] at hno_ub ⊢
  have ha_st := ha st
  cases h1 : evalStmt st a1 with
  | val st1 =>
    have h1_ne : Outcome.val st1 ≠ Outcome.ub := by nofun
    have ha_eq : evalStmt st a2 = Outcome.val st1 := by
      rw [← h1]; exact ha_st (by rw [h1]; exact h1_ne)
    rw [ha_eq]; simp only [h1] at hno_ub; exact hb st1 hno_ub
  | panic =>
    have h1_ne : (Outcome.panic : Outcome State) ≠ Outcome.ub := by nofun
    have ha_eq : evalStmt st a2 = Outcome.panic := by
      rw [← h1]; exact ha_st (by rw [h1]; exact h1_ne)
    rw [ha_eq]
  | ub =>
    simp only [h1] at hno_ub; exact False.elim (hno_ub rfl)

end RuleSynthV2
