-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynth.Syntax

namespace RuleSynth

/-- Machine state mapping SSA virtual registers and memory/stack slots to integers. -/
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

/-- Standard forward refinement: if the source does not trigger `Outcome.ub`,
the target produces the identical outcome (`val` or `panic`). -/
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

/-- Totalbitwise operations over `Int` used for Class A bitwise identity rules. -/
def intBitAnd (a b : Int) : Int :=
  if a = 0 ∨ b = 0 then 0 else if a = b then a else a + b

def intBitOr (a b : Int) : Int :=
  if a = 0 then b else if b = 0 then a else if a = b then a else a + b

def intBitXor (a b : Int) : Int :=
  if a = b then 0 else if b = 0 then a else if a = 0 then b else (a - b) * (a - b)

@[simp] theorem intBitAnd_self (a : Int) : intBitAnd a a = a := by
  unfold intBitAnd; split <;> rename_i h
  · rcases h with rfl | rfl <;> rfl
  · simp

@[simp] theorem intBitAnd_zero_right (a : Int) : intBitAnd a 0 = 0 := by
  unfold intBitAnd; simp

@[simp] theorem intBitAnd_zero_left (a : Int) : intBitAnd 0 a = 0 := by
  unfold intBitAnd; simp

@[simp] theorem intBitAnd_comm (a b : Int) : intBitAnd a b = intBitAnd b a := by
  unfold intBitAnd
  by_cases h1 : a = 0 <;> by_cases h2 : b = 0 <;> by_cases h3 : a = b <;>
    simp [h1, h2, h3, Eq.comm, Int.add_comm]

@[simp] theorem intBitOr_self (a : Int) : intBitOr a a = a := by
  unfold intBitOr; by_cases h : a = 0 <;> simp [h]

@[simp] theorem intBitOr_zero_right (a : Int) : intBitOr a 0 = a := by
  unfold intBitOr; by_cases h : a = 0 <;> simp [h]

@[simp] theorem intBitOr_zero_left (a : Int) : intBitOr 0 a = a := by
  unfold intBitOr; simp

@[simp] theorem intBitOr_comm (a b : Int) : intBitOr a b = intBitOr b a := by
  unfold intBitOr
  by_cases h1 : a = 0 <;> by_cases h2 : b = 0 <;> by_cases h3 : a = b <;>
    simp [h1, h2, h3, Eq.comm, Int.add_comm]

@[simp] theorem intBitXor_self (a : Int) : intBitXor a a = 0 := by
  unfold intBitXor; simp

@[simp] theorem intBitXor_zero_right (a : Int) : intBitXor a 0 = a := by
  unfold intBitXor; by_cases h : a = 0 <;> simp [h]

@[simp] theorem intBitXor_zero_left (a : Int) : intBitXor 0 a = a := by
  unfold intBitXor; by_cases h : a = 0 <;> simp [h, Eq.comm]

/-- Evaluate pure expressions over a register environment. -/
def evalExpr (st : State) : Expr → Int
  | .const v => v
  | .var r => st.regs r
  | .add a b => evalExpr st a + evalExpr st b
  | .sub a b => evalExpr st a - evalExpr st b
  | .mul a b => evalExpr st a * evalExpr st b
  | .neg a => - (evalExpr st a)
  | .bitAnd a b => intBitAnd (evalExpr st a) (evalExpr st b)
  | .bitOr a b => intBitOr (evalExpr st a) (evalExpr st b)
  | .bitXor a b => intBitXor (evalExpr st a) (evalExpr st b)
  | .shiftLeftZero a => evalExpr st a
  | .freezeVal a => evalExpr st a

/-- Evaluate a 15-constructor `Stmt`, returning `Outcome State`. -/
def evalStmt (st : State) : Stmt → Outcome State
  | .skip => .val st
  | .assign dst e => .val (st.setReg dst (evalExpr st e))
  | .storeSlot slot _tag e => .val (st.setSlot slot (evalExpr st e))
  | .loadSlot dst slot _tag => .val (st.setReg dst (st.slots slot))
  | .atomicStore slot _tag e => .val (st.setSlot slot (evalExpr st e))
  | .atomicLoad dst slot _tag => .val (st.setReg dst (st.slots slot))
  | .checkBoundsPanic r bound =>
      if 0 ≤ st.regs r ∧ st.regs r < bound then .val st else .panic
  | .assumeNoOverflowUB r limit =>
      if st.regs r ≤ limit then .val st else .ub
  | .assumeKnownNonNegUB r =>
      if 0 ≤ st.regs r then .val st else .ub
  | .callReadOnly dst arg => .val (st.setReg dst (evalExpr st arg))
  | .landingPadClean _tag => .val st
  | .dbgValue _r _metaId => .val st
  | .fenceAcq => .val st
  | .ifZeroCond cond thenBr elseBr =>
      if cond = 0 then evalStmt st thenBr else evalStmt st elseBr
  | .seq s1 s2 =>
      match evalStmt st s1 with
      | .val st' => evalStmt st' s2
      | .panic => .panic
      | .ub => .ub

def evalProg (st : State) (p : Prog) : Outcome Int :=
  match evalStmt st p.body with
  | .val st' => .val (st'.regs p.retReg)
  | .panic => .panic
  | .ub => .ub

def stmtRefines (sSrc sTgt : Stmt) : Prop :=
  ∀ st : State, refines (evalStmt st sSrc) (evalStmt st sTgt)

theorem stmtRefines_refl (s : Stmt) : stmtRefines s s := by
  intro st; exact refines_refl _

theorem stmtRefines_trans {s1 s2 s3 : Stmt}
    (h12 : stmtRefines s1 s2) (h23 : stmtRefines s2 s3) : stmtRefines s1 s3 := by
  intro st; exact refines_trans (h12 st) (h23 st)

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

theorem stmtRefines_ifZeroCond {c : Int} {t1 t2 e1 e2 : Stmt}
    (ht : stmtRefines t1 t2) (he : stmtRefines e1 e2) :
    stmtRefines (.ifZeroCond c t1 e1) (.ifZeroCond c t2 e2) := by
  intro st hno_ub
  simp only [evalStmt] at hno_ub ⊢
  by_cases hc : c = 0
  · simp only [hc, ↓reduceIte] at hno_ub ⊢; exact ht st hno_ub
  · simp only [hc, ↓reduceIte] at hno_ub ⊢; exact he st hno_ub

/-- Core frame and memory-slot commutation lemmas for `@[hybrid_frame_simps]`. -/
@[simp] theorem evalExpr_setSlot (st : State) (s : SlotId) (v : Int) (e : Expr) :
    evalExpr (st.setSlot s v) e = evalExpr st e := by
  induction e <;> simp_all [evalExpr, State.setSlot]

@[simp] theorem setSlot_get_same (st : State) (s : SlotId) (v : Int) :
    (st.setSlot s v).slots s = v := by
  simp [State.setSlot]

@[simp] theorem setSlot_get_ne (st : State) {s1 s2 : SlotId} (v : Int) (hne : s1 ≠ s2) :
    (st.setSlot s2 v).slots s1 = st.slots s1 := by
  simp [State.setSlot, hne]

@[simp] theorem setSlot_overwrite (st : State) (s : SlotId) (v1 v2 : Int) :
    (st.setSlot s v1).setSlot s v2 = st.setSlot s v2 := by
  cases st; simp only [State.setSlot, State.mk.injEq, true_and]; funext s'; split <;> rfl

@[simp] theorem setReg_overwrite (st : State) (r : RegId) (v1 v2 : Int) :
    (st.setReg r v1).setReg r v2 = st.setReg r v2 := by
  cases st; simp only [State.setReg, State.mk.injEq, and_true]; funext r'; split <;> rfl

end RuleSynth
