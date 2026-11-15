-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Fuel-Indexed Loop & Memory-Frame Operational Semantics (`MemFrame.lean`)

Defines the statement IR (`Stmt`) with bounded/fuel-indexed loops (`.whilePos countReg body`),
memory loads/stores (`.loadSlot`, `.storeSlot`), pure register expressions (`Expr`), and
algebraic memory-frame lens lemmas (`setSlot_get_same`, `setSlot_get_ne`, `setSlot_overwrite`,
`setSlot_comm`, `evalExpr_setSlot`, `evalExpr_setReg_ne`) used by `RuleSynthV2` to discharge
Class C memory-frame and Class D loop transformation proofs automatically.
-/

namespace RuleSynthV2

abbrev RegId := Nat
abbrev SlotId := Nat

/-- Pure register expressions. -/
inductive Expr where
  | const (v : Int)
  | var (r : RegId)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  deriving DecidableEq, Repr

/-- Check that `Expr` does not read register `r`. -/
def exprNotReadsReg (r : RegId) : Expr → Bool
  | .const _ => true
  | .var r' => decide (r' ≠ r)
  | .add a b => exprNotReadsReg r a && exprNotReadsReg r b
  | .sub a b => exprNotReadsReg r a && exprNotReadsReg r b
  | .mul a b => exprNotReadsReg r a && exprNotReadsReg r b

/-- Machine state mapping virtual registers and memory slots to integers. -/
structure State where
  regs  : RegId → Int
  slots : SlotId → Int

def State.setReg (st : State) (r : RegId) (v : Int) : State :=
  { st with regs := fun r' => if r' = r then v else st.regs r' }

def State.setSlot (st : State) (s : SlotId) (v : Int) : State :=
  { st with slots := fun s' => if s' = s then v else st.slots s' }

/-- Observable evaluation outcomes (`val`, `panic`, `ub`). -/
inductive Outcome (α : Type) where
  | val (v : α)
  | panic
  | ub
  deriving DecidableEq, Repr

/-- Standard forward refinement: if the source does not trigger `ub`, the target produces
the exact same outcome (`val` or `panic`). -/
def refines {α : Type} (oSrc oTgt : Outcome α) : Prop :=
  oSrc ≠ Outcome.ub → oTgt = oSrc

theorem refines_refl {α : Type} (o : Outcome α) : refines o o := by
  intro _; rfl

theorem refines_trans {α : Type} {o1 o2 o3 : Outcome α}
    (h12 : refines o1 o2) (h23 : refines o2 o3) : refines o1 o3 := by
  intro h1
  have eq2 : o2 = o1 := h12 h1
  have h2 : o2 ≠ Outcome.ub := by rw [eq2]; exact h1
  rw [h23 h2, eq2]

/-- Evaluate pure register expressions. -/
def evalExpr (st : State) : Expr → Int
  | .const v => v
  | .var r => st.regs r
  | .add a b => evalExpr st a + evalExpr st b
  | .sub a b => evalExpr st a - evalExpr st b
  | .mul a b => evalExpr st a * evalExpr st b

/-- Statement IR including Class C memory operations and Class D fuel-indexed loops (`whileSteps`). -/
inductive Stmt where
  | skip
  | assign (dst : RegId) (e : Expr)
  | storeSlot (slot : SlotId) (e : Expr)
  | loadSlot (dst : RegId) (slot : SlotId)
  | callPure (dst : RegId) (arg : Expr)
  | tailCallRet (dst : RegId) (arg : Expr)
  | checkBoundsPanic (r : RegId) (bound : Int)
  | assumeNonNegUB (r : RegId)
  | ifZeroCond (cond : Int) (thenBr elseBr : Stmt)
  | whileSteps (iters : Nat) (body : Stmt)
  | seq (s1 s2 : Stmt)
  deriving DecidableEq, Repr

/-- Operational semantics for `Stmt` including bounded/counted loop execution (`whileSteps`). -/
def evalStmt (st : State) : Stmt → Outcome State
  | .skip => .val st
  | .assign dst e => .val (st.setReg dst (evalExpr st e))
  | .storeSlot slot e => .val (st.setSlot slot (evalExpr st e))
  | .loadSlot dst slot => .val (st.setReg dst (st.slots slot))
  | .callPure dst arg => .val (st.setReg dst (evalExpr st arg))
  | .tailCallRet dst arg => .val (st.setReg dst (evalExpr st arg))
  | .checkBoundsPanic r bound =>
      if 0 ≤ st.regs r ∧ st.regs r < bound then .val st else .panic
  | .assumeNonNegUB r =>
      if 0 ≤ st.regs r then .val st else .ub
  | .ifZeroCond cond thenBr elseBr =>
      if cond = 0 then evalStmt st thenBr else evalStmt st elseBr
  | .whileSteps 0 _ => .val st
  | .whileSteps (k + 1) body =>
      match evalStmt st body with
      | .val st' => evalStmt st' (.whileSteps k body)
      | .panic => .panic
      | .ub => .ub
  | .seq s1 s2 =>
      match evalStmt st s1 with
      | .val st' => evalStmt st' s2
      | .panic => .panic
      | .ub => .ub

/-- Statement refinement across all machine states `st : State`. -/
def stmtRefines (sSrc sTgt : Stmt) : Prop :=
  ∀ st : State, refines (evalStmt st sSrc) (evalStmt st sTgt)

theorem stmtRefines_refl (s : Stmt) : stmtRefines s s := by
  intro st; exact refines_refl _

theorem stmtRefines_trans {s1 s2 s3 : Stmt}
    (h12 : stmtRefines s1 s2) (h23 : stmtRefines s2 s3) : stmtRefines s1 s3 := by
  intro st; exact refines_trans (h12 st) (h23 st)

-- ============================================================================
-- Algebraic Memory-Frame & Register Lens Lemmas (`@[simp]`)
-- ============================================================================

@[simp] theorem evalExpr_setSlot (st : State) (s : SlotId) (v : Int) (e : Expr) :
    evalExpr (st.setSlot s v) e = evalExpr st e := by
  induction e <;> simp_all [evalExpr, State.setSlot]

@[simp] theorem evalExpr_setReg_of_notReads (st : State) (r : RegId) (v : Int) (e : Expr)
    (h_nr : exprNotReadsReg r e = true) :
    evalExpr (st.setReg r v) e = evalExpr st e := by
  induction e with
  | const c => rfl
  | var r' =>
    simp only [exprNotReadsReg, decide_eq_true_eq] at h_nr
    simp [evalExpr, State.setReg, h_nr]
  | add a b iha ihb =>
    simp only [exprNotReadsReg, Bool.and_eq_true] at h_nr
    simp [evalExpr, iha h_nr.1, ihb h_nr.2]
  | sub a b iha ihb =>
    simp only [exprNotReadsReg, Bool.and_eq_true] at h_nr
    simp [evalExpr, iha h_nr.1, ihb h_nr.2]
  | mul a b iha ihb =>
    simp only [exprNotReadsReg, Bool.and_eq_true] at h_nr
    simp [evalExpr, iha h_nr.1, ihb h_nr.2]

@[simp] theorem setSlot_get_same (st : State) (s : SlotId) (v : Int) :
    (st.setSlot s v).slots s = v := by
  simp [State.setSlot]

@[simp] theorem setSlot_get_ne (st : State) {s1 s2 : SlotId} (v : Int) (hne : s1 ≠ s2) :
    (st.setSlot s2 v).slots s1 = st.slots s1 := by
  simp [State.setSlot, hne]

@[simp] theorem setReg_get_same (st : State) (r : RegId) (v : Int) :
    (st.setReg r v).regs r = v := by
  simp [State.setReg]

@[simp] theorem setReg_get_ne (st : State) {r1 r2 : RegId} (v : Int) (hne : r1 ≠ r2) :
    (st.setReg r2 v).regs r1 = st.regs r1 := by
  simp [State.setReg, hne]

@[simp] theorem setSlot_overwrite (st : State) (s : SlotId) (v1 v2 : Int) :
    (st.setSlot s v1).setSlot s v2 = st.setSlot s v2 := by
  cases st; simp only [State.setSlot, State.mk.injEq, true_and]; funext s'; split <;> rfl

@[simp] theorem setReg_overwrite (st : State) (r : RegId) (v1 v2 : Int) :
    (st.setReg r v1).setReg r v2 = st.setReg r v2 := by
  cases st; simp only [State.setReg, State.mk.injEq, and_true]; funext r'; split <;> rfl

theorem setSlot_comm (st : State) {s1 s2 : SlotId} (v1 v2 : Int) (hne : s1 ≠ s2) :
    (st.setSlot s1 v1).setSlot s2 v2 = (st.setSlot s2 v2).setSlot s1 v1 := by
  cases st; simp only [State.setSlot, State.mk.injEq, true_and]
  funext s'
  by_cases h1 : s' = s1
  · subst h1; simp [hne]
  · by_cases h2 : s' = s2
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem setReg_comm (st : State) {r1 r2 : RegId} (v1 v2 : Int) (hne : r1 ≠ r2) :
    (st.setReg r1 v1).setReg r2 v2 = (st.setReg r2 v2).setReg r1 v1 := by
  cases st; simp only [State.setReg, State.mk.injEq, and_true]
  funext r'
  by_cases h1 : r' = r1
  · subst h1; simp [hne]
  · by_cases h2 : r' = r2
    · subst h2; simp [h1]
    · simp [h1, h2]

@[simp] theorem setReg_setSlot_comm (st : State) (r : RegId) (vr : Int) (s : SlotId) (vs : Int) :
    (st.setReg r vr).setSlot s vs = (st.setSlot s vs).setReg r vr := by
  cases st; rfl

@[simp] theorem setSlot_regs (st : State) (s : SlotId) (v : Int) :
    (st.setSlot s v).regs = st.regs := rfl

@[simp] theorem setReg_slots (st : State) (r : RegId) (v : Int) :
    (st.setReg r v).slots = st.slots := rfl

end RuleSynthV2
