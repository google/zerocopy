-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import W6Proto.Syntax

namespace W6Proto

/-- Machine state mapping SSA/local registers and stack/memory slots to integer values. -/
structure State where
  regs : RegId → Int
  slots : SlotId → Int

def State.setReg (st : State) (r : RegId) (v : Int) : State :=
  { st with regs := fun r' => if r' = r then v else st.regs r' }

def State.setSlot (st : State) (s : SlotId) (v : Int) : State :=
  { st with slots := fun s' => if s' = s then v else st.slots s' }

/-- Observable evaluation outcomes with explicit `UB` and `Panic` states. -/
inductive Outcome (α : Type) where
  | val (v : α)
  | panic
  | ub
  deriving DecidableEq, Repr

/-- Standard compiler refinement relation: if the source program does not trigger
undefined behavior (`Outcome.ub`), the target program produces the exact same
observable outcome (`val` or `panic`). When the source executes `ub`, any target
outcome refines it. -/
def refines {α : Type} (oSrc oTgt : Outcome α) : Prop :=
  oSrc ≠ Outcome.ub → oTgt = oSrc

theorem refines_refl {α : Type} (o : Outcome α) : refines o o := by
  intro _
  rfl

theorem refines_trans {α : Type} {o1 o2 o3 : Outcome α}
    (h12 : refines o1 o2) (h23 : refines o2 o3) : refines o1 o3 := by
  intro h1
  have Eq2 : o2 = o1 := h12 h1
  have h2 : o2 ≠ Outcome.ub := by rw [Eq2]; exact h1
  have Eq3 : o3 = o2 := h23 h2
  rw [Eq3, Eq2]

/-- Evaluate pure expressions over a register environment. -/
def evalExpr (st : State) : Expr → Int
  | .const v => v
  | .var r => st.regs r
  | .add a b => evalExpr st a + evalExpr st b
  | .sub a b => evalExpr st a - evalExpr st b
  | .mul a b => evalExpr st a * evalExpr st b

/-- Evaluate a statement, returning `Outcome State`. -/
def evalStmt (st : State) : Stmt → Outcome State
  | .skip => .val st
  | .assign dst e => .val (st.setReg dst (evalExpr st e))
  | .storeSlot slot _tag e => .val (st.setSlot slot (evalExpr st e))
  | .loadSlot dst slot _tag => .val (st.setReg dst (st.slots slot))
  | .checkBoundsPanic r bound =>
      if 0 ≤ st.regs r ∧ st.regs r < bound then .val st else .panic
  | .assumeNoOverflowUB r limit =>
      if st.regs r ≤ limit then .val st else .ub
  | .seq s1 s2 =>
      match evalStmt st s1 with
      | .val st' => evalStmt st' s2
      | .panic => .panic
      | .ub => .ub

/-- Evaluate a program and project the final return register value. -/
def evalProg (st : State) (p : Prog) : Outcome Int :=
  match evalStmt st p.body with
  | .val st' => .val (st'.regs p.retReg)
  | .panic => .panic
  | .ub => .ub

/-- Statement-level refinement lifting to program-level refinement. -/
def stmtRefines (sSrc sTgt : Stmt) : Prop :=
  ∀ st : State, refines (evalStmt st sSrc) (evalStmt st sTgt)

theorem stmtRefines_refl (s : Stmt) : stmtRefines s s := by
  intro st
  exact refines_refl _

theorem stmtRefines_trans {s1 s2 s3 : Stmt}
    (h12 : stmtRefines s1 s2) (h23 : stmtRefines s2 s3) : stmtRefines s1 s3 := by
  intro st
  exact refines_trans (h12 st) (h23 st)

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
      rw [← h1]
      exact ha_st (by rw [h1]; exact h1_ne)
    rw [ha_eq]
    simp only [h1] at hno_ub
    exact hb st1 hno_ub
  | panic =>
    have h1_ne : (Outcome.panic : Outcome State) ≠ Outcome.ub := by nofun
    have ha_eq : evalStmt st a2 = Outcome.panic := by
      rw [← h1]
      exact ha_st (by rw [h1]; exact h1_ne)
    rw [ha_eq]
  | ub =>
    simp only [h1] at hno_ub
    exact False.elim (hno_ub rfl)

end W6Proto
