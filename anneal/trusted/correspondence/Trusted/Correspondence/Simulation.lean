-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics
import Trusted.Correspondence.Codec
import Trusted.Correspondence.State
import Trusted.Correspondence.Config
import Trusted.Correspondence.Eval

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Simulation Invariant (`Trusted.Correspondence.Simulation`)

Relates $M_{\text{anneal}}$ states (`Trusted.MirSemantics.State`) to real
`ExecutionMachine`-backed $M_{\text{ref}}$ states (`RefState`).
-/

/-! ## One-to-One Simulation Invariant (`SimulationInv`) -/

/-- Well-typedness of a single $M_{\text{anneal}}$ `LocalSlot` against its
declared `MirTy`:
- `.dead`: always valid;
- `.live none`: valid only for non-ZST types (0-byte ZSTs `.unit` and admitted
  1-variant `.zeroSized` enums are always inhabited as `.live (some _)` in
  reachable $M_{\text{anneal}}$ states);
- `.live (some v)`: `checkVal v ty = true`. -/
def SlotMatchesTy (ty : MirTy) : LocalSlot → Prop
  | .dead => True
  | .live none =>
    ty ≠ .unit ∧
    (∀ ety : EnumTy, ty = .enum ety → isZstEnumTy ety = false)
  | .live (some v) => checkVal v ty = true

/-- Pointwise well-typedness of a frame's local slots against `body.locals`. -/
inductive SlotsMatchTys : List MirTy → List LocalSlot → Prop where
  | nil : SlotsMatchTys [] []
  | cons {ty : MirTy} {tys : List MirTy}
      {slot : LocalSlot} {slots : List LocalSlot} :
      SlotMatchesTy ty slot →
      SlotsMatchTys tys slots →
      SlotsMatchTys (ty :: tys) (slot :: slots)

/-- Lift a frame's `LocalSlot` list into pre-cached
`Miri.Interpreter.LocalState` entries against type table `types` and declared
local types `bodyLocals`. -/
noncomputable def liftLocals (types : List MirTy) :
    List MirTy → List LocalSlot →
      List (Miri.Interpreter.LocalState Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout)
  | ty :: tys, slot :: slots =>
    refLocalStateOfSlot types ty slot :: liftLocals types tys slots
  | _, _ => []

/-- Statement-index bound invariant: whenever `f.blockIdx` names an in-bounds
basic block `bb`, `f.stmtIdx ≤ bb.statements.length` (matching `Step.step`,
which dispatches the terminator when `statementIndex ≥ statements.size`). -/
def FramePcInBounds (body : Body) (f : FrameState) : Prop :=
  ∀ bb : BasicBlock,
    MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb →
    f.stmtIdx ≤ bb.statements.length

/-- Deterministic update of `TerminatorMachine.Control Unit` across a single
step from `(body, f)`: unchanged on statements, advanced via
`advanceRefControl` on terminators (`stmtIdx == bb.statements.length`). -/
noncomputable def nextRefControlForStep (body : Body) (f : FrameState)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) :
    Miri.Interpreter.TerminatorMachine.Control Unit :=
  match MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none => ctrl
  | some bb =>
    match MirSemantics.getElem? bb.statements f.stmtIdx with
    | some _ => ctrl
    | none =>
      if Nat.beq f.stmtIdx bb.statements.length then
        advanceRefControl ctrl
      else
        ctrl

/-- Lift an $M_{\text{anneal}}$ single-frame `StepResult` to $M_{\text{ref}}$,
preserving `retTy`, `retPlace`, `memory`, `maxSteps`, advancing `control` on
terminators, and incrementing `stepsExecuted`. -/
noncomputable def mapStepRes (rp : RefProg) (body : Body)
    (rbody : RefBody) (f : FrameState) (rs : RefState) :
    StepResult State TerminalOut → StepResult RefState TerminalOut
  | .step { frames := [f'], callerMem := cm } =>
    let rf' := mkRefMiriFrame rp.types f'.defId rbody f'.blockIdx f'.stmtIdx
      (liftLocals rp.types body.locals f'.locals) rs.retPlace
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    .step {
      rs with
      miri := mkRefMiriState rf' rs.miri.machine.memory ctrl' cm
      stepsExecuted := rs.stepsExecuted + 1
    }
  | .step _ => .fault .unsupported
  | .done out => .done out
  | .fault k => .fault k

/-- Convert a lifted `StepResult RefState TerminalOut` into a `RefOutcome`. -/
noncomputable def stepResultToRefOutcome :
    StepResult RefState TerminalOut → RefOutcome
  | .step rs' => .running rs'
  | .done out => .returned out
  | .fault k => faultToRefOutcome k

/-- Frame-level one-to-one simulation invariant relating $M_{\text{anneal}}$
frame `f` to its real `Miri.Interpreter.Frame` `rf`. -/
def FrameSimInv (rp : RefProg) (p : Program) (f : FrameState)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (rf : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra) : Prop :=
  ∃ (body : Body) (rbody : RefBody),
    MirSemantics.getElem? p.bodies f.defId = some body ∧
    MirSemantics.getElem? rp.bodies f.defId = some rbody ∧
    decodeBody rp.types rbody = some body ∧
    Nat.blt body.argumentCount body.locals.length = true ∧
    storageAnnotationsInBounds body = true ∧
    discriminantTypesValid body = true ∧
    body.locals.all isSupportedScalarOrUnitTy = true ∧
    SlotsMatchTys body.locals f.locals ∧
    FramePcInBounds body f ∧
    rf = mkRefMiriFrame rp.types f.defId rbody f.blockIdx f.stmtIdx
      (liftLocals rp.types body.locals f.locals) retPlace

/-- Type of the entry function's return place `_0`, which types the caller-owned
return allocation `retPlace`. -/
noncomputable def entryRetTy? (p : Program) : Option MirTy :=
  match MirSemantics.getElem? p.bodies p.entryDefId with
  | some body => MirSemantics.getElem? body.locals 0
  | none => none

/-- Whole-state one-to-one simulation invariant between $M_{\text{anneal}}$ and
the real `ExecutionMachine`-backed $M_{\text{ref}}$: constrains every semantic
field of `s` and `rs` (including the single active `Miri.Interpreter.Frame`,
fresh caller-owned return allocation `retPlace` in `miri.machine.memory`,
disabled borrow/race trackers, `pendingMoveDeinit = false`, `callerMem`, and
`RefControlValid`), unique in both directions up to `(stepsExecuted, maxSteps,
miri.machine.user.control)`. -/
def SimulationInv (rp : RefProg) (p : Program) (s : State) (rs : RefState) :
    Prop :=
  ∃ (f : FrameState)
    (rf : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (retTy : MirTy)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit),
    decodeProg rp = some p ∧
    s.frames = [f] ∧
    f.defId = p.entryDefId ∧
    entryRetTy? p = some retTy ∧
    rs.retTy = retTy ∧
    refInitMemoryAndRetPlace rp.types retTy = .ok (mem, rs.retPlace) ∧
    RefControlValid ctrl ∧
    rs.miri = mkRefMiriState rf mem ctrl s.callerMem ∧
    FrameSimInv rp p f rs.retPlace rf

end Trusted.Correspondence
