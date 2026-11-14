-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RegAllocCert.Syntax

namespace RegAllocCert

/-- Observable outcomes for `MiniSSA` and `MiniMach` executions. -/
inductive Outcome (α : Type) where
  | val (v : α)
  | panic
  | ub
  deriving DecidableEq, Repr

/-- Standard compiler refinement: whenever `src` does not trigger UB (`Outcome.ub`),
`tgt` produces the exact same observable outcome (`val` or `panic`). -/
def refines {α : Type} (src tgt : Outcome α) : Prop :=
  src ≠ Outcome.ub → tgt = src

theorem refines_refl {α : Type} (o : Outcome α) : refines o o := by
  intro _
  rfl

theorem refines_trans {α : Type} {o1 o2 o3 : Outcome α}
    (h12 : refines o1 o2) (h23 : refines o2 o3) : refines o1 o3 := by
  intro h1
  have eq2 : o2 = o1 := h12 h1
  have h2 : o2 ≠ Outcome.ub := by rw [eq2]; exact h1
  have eq3 : o3 = o2 := h23 h2
  rw [eq3, eq2]

/-- Pure ALU semantics over `Int`. -/
def evalBinOp (op : BinOp) (a b : Int) : Int :=
  match op with
  | .add    => a + b
  | .sub    => a - b
  | .mul    => a * b
  | .bitAnd => Int.ofNat (a.toNat &&& b.toNat)
  | .bitXor => Int.ofNat (a.toNat ^^^ b.toNat)

/-- `MiniSSA` virtual register state. -/
structure SSAState where
  vregs : VReg → Int

def SSAState.get (st : SSAState) (v : VReg) : Int :=
  st.vregs v

def SSAState.set (st : SSAState) (v : VReg) (val : Int) : SSAState :=
  { vregs := fun v' => if v' = v then val else st.vregs v' }

/-- Operational semantics of `MiniSSA` instructions, including simultaneous
parallel edge swaps (`parSwap2` and `parRotate3`). -/
def evalSSAInst (st : SSAState) : SSAInst → Outcome SSAState
  | .constI dst val =>
      .val (st.set dst val)
  | .binOp op dst lhs rhs =>
      .val (st.set dst (evalBinOp op (st.get lhs) (st.get rhs)))
  | .copyVReg dst src =>
      .val (st.set dst (st.get src))
  | .parSwap2 v1 v2 =>
      let val1 := st.get v1
      let val2 := st.get v2
      .val ((st.set v1 val2).set v2 val1)
  | .parRotate3 v1 v2 v3 =>
      let val1 := st.get v1
      let val2 := st.get v2
      let val3 := st.get v3
      .val (((st.set v1 val2).set v2 val3).set v3 val1)
  | .callClobber dst arg delta _clob =>
      .val (st.set dst (st.get arg + delta))
  | .assertBoundsPanic v bound =>
      if 0 ≤ st.get v ∧ st.get v < bound then .val st else .panic
  | .assumeNonNegUB v =>
      if 0 ≤ st.get v then .val st else .ub
  | .seq i1 i2 =>
      match evalSSAInst st i1 with
      | .val st' => evalSSAInst st' i2
      | .panic   => .panic
      | .ub      => .ub

/-- Evaluate a `MiniSSA` function given initial state `st` and argument `argVal`. -/
def evalSSAFunc (fn : SSAFunc) (st : SSAState) (argVal : Int) : Outcome Int :=
  let st0 := st.set fn.argVReg argVal
  match evalSSAInst st0 fn.body with
  | .val stF => .val (stF.get fn.retVReg)
  | .panic   => .panic
  | .ub      => .ub

/-- `MiniMach` machine state over `Loc` (`PReg ⊎ SpillSlot`). -/
structure MachState where
  locs : Loc → Int

def MachState.get (ms : MachState) (l : Loc) : Int :=
  ms.locs l

def MachState.set (ms : MachState) (l : Loc) (val : Int) : MachState :=
  { locs := fun l' => if l' = l then val else ms.locs l' }

/-- Sequential decomposition of a 2-way parallel swap in `MiniMach`:
- `viaScratch s`: `s := l1; l1 := l2; l2 := s` (3 sequential moves);
- `viaXchg`: atomic exchange `l1 ↔ l2`. -/
def execSwap2Mach (ms : MachState) (l1 l2 : Loc) (mode : CycleResolution) : MachState :=
  match mode with
  | .viaScratch scratch =>
      let sLoc := Loc.preg scratch
      let ms1 := ms.set sLoc (ms.get l1)
      let ms2 := ms1.set l1 (ms1.get l2)
      ms2.set l2 (ms2.get sLoc)
  | .viaXchg =>
      let val1 := ms.get l1
      let val2 := ms.get l2
      (ms.set l1 val2).set l2 val1

/-- Sequential decomposition of a 3-way parallel rotation `(l1, l2, l3) := (l2, l3, l1)`
using scratch register `scratch`: `s := l1; l1 := l2; l2 := l3; l3 := s` (4 sequential moves). -/
def execRotate3Mach (ms : MachState) (l1 l2 l3 : Loc) (scratch : PReg) : MachState :=
  let sLoc := Loc.preg scratch
  let ms1 := ms.set sLoc (ms.get l1)
  let ms2 := ms1.set l1 (ms1.get l2)
  let ms3 := ms2.set l2 (ms2.get l3)
  ms3.set l3 (ms3.get sLoc)

/-- Operational semantics of `MiniMach` instructions. Notice that `callClobberLoc`
first reads `arg`, then clobbers `Loc.preg clobberedPReg` to `0`, and finally writes `dst`. -/
def evalMachInst (ms : MachState) : MachInst → Outcome MachState
  | .constLoc dst val =>
      .val (ms.set dst val)
  | .binOpLoc op dst lhs rhs =>
      .val (ms.set dst (evalBinOp op (ms.get lhs) (ms.get rhs)))
  | .moveLoc dst src =>
      .val (ms.set dst (ms.get src))
  | .swap2Loc l1 l2 mode =>
      .val (execSwap2Mach ms l1 l2 mode)
  | .rotate3Scratch l1 l2 l3 scratch =>
      .val (execRotate3Mach ms l1 l2 l3 scratch)
  | .callClobberLoc dst arg delta clob =>
      let argVal := ms.get arg
      let msClob := ms.set (.preg clob) 0
      .val (msClob.set dst (argVal + delta))
  | .assertBoundsPanicLoc l bound =>
      if 0 ≤ ms.get l ∧ ms.get l < bound then .val ms else .panic
  | .assumeNonNegUBLoc l =>
      if 0 ≤ ms.get l then .val ms else .ub
  | .seq m1 m2 =>
      match evalMachInst ms m1 with
      | .val ms' => evalMachInst ms' m2
      | .panic   => .panic
      | .ub      => .ub

/-- Save callee-saved physical registers to their designated prologue spill slots. -/
def saveCalleeRegs (ms : MachState) : List (PReg × SpillSlot) → MachState
  | [] => ms
  | (r, s) :: rest => saveCalleeRegs (ms.set (.spill s) (ms.get (.preg r))) rest

/-- Restore callee-saved physical registers from their epilogue spill slots. -/
def restoreCalleeRegs (ms : MachState) : List (PReg × SpillSlot) → MachState
  | [] => ms
  | (r, s) :: rest => restoreCalleeRegs (ms.set (.preg r) (ms.get (.spill s))) rest

/-- Evaluate a `MiniMach` function given initial machine state `ms` and argument `argVal`. -/
def evalMachFunc (fn : MachFunc) (ms : MachState) (argVal : Int) : Outcome Int :=
  let ms0 := ms.set fn.argLoc argVal
  match evalMachInst ms0 fn.body with
  | .val msF => .val (msF.get fn.retLoc)
  | .panic   => .panic
  | .ub      => .ub

end RegAllocCert
