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
- `.immediate none`: valid only for non-ZST types (0-byte ZSTs `.unit` and
  admitted 1-variant `.zeroSized` enums are always inhabited as
  `.immediate (some _)` in reachable $M_{\text{anneal}}$ states);
- `.immediate (some v)`: `checkVal v ty = true`;
- `.indirect _`: excluded. Profile version 1 has no statement that moves a
  local into memory (projections, address-of, and calls are `.unsupported`),
  so neither $M_{\text{anneal}}$ (`forceAllocation`) nor `lean-miri`
  (`Place.forceAllocation`) creates an indirect local on any execution from
  `initState` / `initRefState`. `slotToMiriLocalValue` still lifts
  `.indirect place` one-to-one to `.live (.indirect (memPlaceToMiri place))`;
  the lockstep proof for indirect locals belongs to the profile that makes
  them reachable. -/
def SlotMatchesTy (ty : MirTy) : LocalSlot → Prop
  | .dead => True
  | .immediate none =>
    ty ≠ .unit ∧
    (∀ ety : EnumTy, ty = .enum ety → isZstEnumTy ety = false)
  | .immediate (some v) => checkVal v ty = true
  | .indirect _ => False
  | .partialTuple _ => False

/-- Pointwise well-typedness of a frame's local slots against `body.locals`. -/
inductive SlotsMatchTys : List MirTy → List LocalSlot → Prop where
  | nil : SlotsMatchTys [] []
  | cons {ty : MirTy} {tys : List MirTy}
      {slot : LocalSlot} {slots : List LocalSlot} :
      SlotMatchesTy ty slot →
      SlotsMatchTys tys slots →
      SlotsMatchTys (ty :: tys) (slot :: slots)

/-- Lift a frame's `LocalSlot` list into `Miri.Interpreter.LocalState`
entries with explicit layout cache bits `cache` (`true` = `some layout`,
`false` = `none`). -/
noncomputable def liftLocalsCached (types : List MirTy) :
    List MirTy → List LocalSlot → List Bool →
      List (Miri.Interpreter.LocalState Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout)
  | ty :: tys, slot :: slots, cached :: restCache =>
    refLocalStateOfSlotWithCache types ty slot cached ::
      liftLocalsCached types tys slots restCache
  | _, _, _ => []

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

/-- Whether operand `opnd` reads local `idx` via `localToOp`/`evalPlace`
(triggering `layoutLocal` caching). -/
noncomputable def operandTouchesLocal (opnd : Operand) (idx : Nat) : Bool :=
  match opnd with
  | .copy p | .move p => Nat.beq p.localId idx
  | .constant _ => false

/-- Whether rvalue `rv` reads local `idx` via `localToOp`/`evalPlace`. -/
noncomputable def rvalueTouchesLocal (rv : Rvalue) (idx : Nat) : Bool :=
  match rv with
  | .use opnd => operandTouchesLocal opnd idx
  | .binaryOp _ lhs rhs =>
    operandTouchesLocal lhs idx || operandTouchesLocal rhs idx
  | .unaryOp _ opnd => operandTouchesLocal opnd idx
  | .cast .intToInt opnd _ => operandTouchesLocal opnd idx
  | .discriminant p => Nat.beq p.localId idx
  | _ => false

/-- Whether executing one non-pushing step from `(body, f)` touches local
`idx` (caching its `LocalLayout` in `Miri.Interpreter.Frame.locals`). -/
noncomputable def stepTouchesLocal (body : Body) (f : FrameState) (idx : Nat) :
    Bool :=
  match MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none => false
  | some bb =>
    match MirSemantics.getElem? bb.statements f.stmtIdx with
    | some stmt =>
      match stmt with
      | .assign dst rv => Nat.beq dst.localId idx || rvalueTouchesLocal rv idx
      | _ => false
    | none =>
      if Nat.beq f.stmtIdx bb.statements.length then
        match bb.terminator with
        | .switchInt discr _ => operandTouchesLocal discr idx
        | _ => false
      else
        false

/-- Update `Miri.Interpreter.LocalState` entries for a same-frame transition
given `f'`'s `LocalSlot`s and the predicate `touched : Nat → Bool` marking
slots accessed during the step. -/
noncomputable def updateMiriLocalsLoop (types : List MirTy)
    (touched : Nat → Bool) (idx : Nat) :
    List MirTy → List LocalSlot →
      List (Miri.Interpreter.LocalState Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout) →
      List (Miri.Interpreter.LocalState Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout)
  | ty :: tys, slot :: slots, oldLs :: oldRest =>
    let cached := oldLs.layout.isSome || touched idx
    refLocalStateOfSlotWithCache types ty slot cached ::
      updateMiriLocalsLoop types touched (idx + 1) tys slots oldRest
  | _, _, _ => []

/-- Initial layout-cache bits of a freshly pushed callee frame: parameter slots
`1 .. argumentCount` are cached by `passArgument` (`true`), while `_0` and
temporaries `> argumentCount` begin uncached (`false`) until accessed. -/
noncomputable def calleeInitCacheLoop (argCount idx : Nat) :
    List MirTy → List Bool
  | [] => []
  | _ :: rest =>
    (!Nat.beq idx 0 && Nat.ble idx argCount) ::
      calleeInitCacheLoop argCount (idx + 1) rest

/-- Whether executing a call terminator from `(body, f)` touches caller local
`idx` (via `evalPlace` on `dst` and `evalOperand`/`placeToOp` on `args`). -/
noncomputable def callTouchesCallerLocal (body : Body) (f : FrameState)
    (idx : Nat) : Bool :=
  match MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none => false
  | some bb =>
    match bb.terminator with
    | .call _ args dst _ _ | .sysrootCall _ args dst _ _ =>
      Nat.beq dst.localId idx || args.any (fun a => operandTouchesLocal a idx)
    | _ => false

/-- Lift a post-step $M_{\text{anneal}}$ `frames'` stack onto $M_{\text{ref}}$'s
bottom-to-top `oldFrames` array and active `prevTopRel?`. -/
noncomputable def liftStackStep (rp : RefProg) (body : Body) (f : FrameState)
    (oldFrames : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (prevTopRel? : Option Nat) (frames' : List FrameState) :
    Option (Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra) ×
      Option Nat) :=
  match frames' with
  | [] => none
  | [f'] =>
    if Nat.beq oldFrames.size 1 then
      match oldFrames[0]? with
      | none => none
      | some rf =>
        let newLocals :=
          updateMiriLocalsLoop rp.types (stepTouchesLocal body f) 0
            body.locals f'.locals rf.locals.toList
        let rf' := {
          rf with
          locals := Array.mk newLocals
          location := .mir ⟨f'.blockIdx, f'.stmtIdx⟩
        }
        some (Array.mk [rf'], prevTopRel?)
    else if Nat.beq oldFrames.size 2 then
      -- Non-root return to root frame (`f'` is updated root caller).
      match oldFrames[0]?, f.retDst? with
      | some rfCaller, some dst =>
        let dstTy := body.locals[0]?.getD .unit
        let _ := dstTy
        let callerLocals :=
          updateMiriLocalsLoop rp.types (fun idx => Nat.beq idx dst.localId) 0
            (rfCaller.body.locals.toList.filterMap (resolveTy rp.types))
            f'.locals rfCaller.locals.toList
        let rfCaller' := {
          rfCaller with
          locals := Array.mk callerLocals
          location := .mir ⟨f'.blockIdx, f'.stmtIdx⟩
        }
        some (Array.mk [rfCaller'], some 0)
      | _, _ => none
    else
      none
  | fTop :: fNext :: rest =>
    let newLen := rest.length + 2
    if Nat.beq newLen oldFrames.size then
      -- Same-depth step on non-root top frame `fTop`.
      match oldFrames.back? with
      | none => none
      | some rf =>
        let newLocals :=
          updateMiriLocalsLoop rp.types (stepTouchesLocal body f) 0
            body.locals fTop.locals rf.locals.toList
        let rf' := {
          rf with
          locals := Array.mk newLocals
          location := .mir ⟨fTop.blockIdx, fTop.stmtIdx⟩
        }
        some (oldFrames.pop.push rf', prevTopRel?)
    else if Nat.beq newLen (oldFrames.size + 1) then
      -- Call push onto `oldFrames` (`fTop` is new callee, `fNext` is updated
      -- caller).
      match oldFrames.back?, fTop.retDst? with
      | some rfCaller, some dst =>
        let callerLocals :=
          updateMiriLocalsLoop rp.types (callTouchesCallerLocal body f) 0
            body.locals fNext.locals rfCaller.locals.toList
        let rfCaller' := {
          rfCaller with
          locals := Array.mk callerLocals
        }
        let fnTag :=
          match fTop.sysrootOp? with
          | some op => fnTagForSysroot op
          | none => fnTagForCrate fTop.defId
        match refResolveCalleeBody rp fnTag with
        | none => none
        | some (calleeRbody, calleeTys) =>
          let dstTy := calleeTys[0]?.getD .unit
          let calleeCache :=
            calleeInitCacheLoop calleeRbody.argumentCount 0 calleeTys
          let calleeLocals :=
            liftLocalsCached rp.types calleeTys fTop.locals calleeCache
          let rfCallee :=
            mkRefMiriCallFrame rp.types fnTag calleeRbody fTop.blockIdx
              fTop.stmtIdx calleeLocals (oldFrames.size - 1) dst.localId dstTy
              fTop.retTarget?
          some ((oldFrames.pop.push rfCaller').push rfCallee,
            some oldFrames.size)
      | _, _ => none
    else if Nat.beq (newLen + 1) oldFrames.size then
      -- Non-root return to non-root caller `fTop`.
      let popped := oldFrames.pop
      match popped.back?, f.retDst? with
      | some rfCaller, some dst =>
        let callerTys :=
          match rfCaller.functionInstance.kind with
          | .Item fnTag =>
            match refResolveCalleeBody rp fnTag with
            | some (_, tys) => tys
            | none => []
          | _ => []
        let callerLocals :=
          updateMiriLocalsLoop rp.types (fun idx => Nat.beq idx dst.localId) 0
            callerTys fTop.locals rfCaller.locals.toList
        let rfCaller' := {
          rfCaller with
          locals := Array.mk callerLocals
          location := .mir ⟨fTop.blockIdx, fTop.stmtIdx⟩
        }
        some (popped.pop.push rfCaller', some (popped.size - 1))
      | _, _ => none
    else
      none

/-- Lift an $M_{\text{anneal}}$ `StepResult` to $M_{\text{ref}}$, preserving
return-place metadata, memory, and `maxSteps`, advancing `control` on
terminators, updating frame stack and `topUserRelevantFrame` on calls/returns,
and incrementing `stepsExecuted`. -/
noncomputable def mapStepRes (rp : RefProg) (body : Body)
    (_rbody : RefBody) (f : FrameState) (rs : RefState) :
    StepResult State TerminalOut → StepResult RefState TerminalOut
  | .step { frames := frames', callerMem := cm, mem := _ } =>
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    let prevTopRel? :=
      match rs.miri.machine.threads.activeThread? with
      | some th => th.topUserRelevantFrame
      | none => none
    match liftStackStep rp body f rs.miri.stack.frames prevTopRel? frames' with
    | none => .fault .unsupported
    | some (newFrames, newTopRel?) =>
      .step {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory ctrl' cm
        stepsExecuted := rs.stepsExecuted + 1
      }
  | .done out => .done out
  | .fault k => .fault k

/-- Convert a lifted `StepResult RefState TerminalOut` into a `RefOutcome`. -/
noncomputable def stepResultToRefOutcome :
    StepResult RefState TerminalOut → RefOutcome
  | .step rs' => .running rs'
  | .done out => .returned out
  | .fault k => faultToRefOutcome k

/-- Resolve the `RefBody` executing in `f` (`sysrootNumRefBody` when
`f.sysrootOp? = some op`, otherwise `rp.bodies[f.defId]`). -/
noncomputable def activeRefFrameBody (rp : RefProg) (f : FrameState) :
    Option RefBody :=
  match f.sysrootOp? with
  | some op => some (sysrootNumRefBody rp.types op)
  | none => MirSemantics.getElem? rp.bodies f.defId

/-- Root-frame simulation invariant relating $M_{\text{anneal}}$ root frame
`f` to its real `Miri.Interpreter.Frame` `rf`. -/
def FrameSimInv (rp : RefProg) (p : Program) (f : FrameState)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (rf : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra) : Prop :=
  ∃ (body : Body) (rbody : RefBody) (cache : List Bool),
    MirSemantics.getElem? p.bodies f.defId = some body ∧
    MirSemantics.getElem? rp.bodies f.defId = some rbody ∧
    decodeBody rp.types rbody = some body ∧
    Nat.blt body.argumentCount body.locals.length = true ∧
    storageAnnotationsInBounds body = true ∧
    discriminantTypesValid body = true ∧
    castTypesValid body = true ∧
    callsAdmitted p body = true ∧
    allCallBodiesStaticAdmitted p body = true ∧
    body.locals.all isSupportedScalarOrUnitTy = true ∧
    SlotsMatchTys body.locals f.locals ∧
    FramePcInBounds body f ∧
    cache = List.replicate body.locals.length true ∧
    rf = mkRefMiriFrame rp.types f.defId rbody f.blockIdx f.stmtIdx
      (liftLocalsCached rp.types body.locals f.locals cache) retPlace

/-- Non-root callee frame simulation invariant relating callee frame `f` at
caller depth `callerIdx` (returning `dstTy` into `dstLocalId`) to its real
`Miri.Interpreter.Frame` `rf`. -/
def CallFrameSimInv (rp : RefProg) (p : Program) (f : FrameState)
    (callerIdx : Nat) (dstLocalId : LocalId) (dstTy : MirTy)
    (rf : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra) : Prop :=
  ∃ (body : Body) (rbody : RefBody) (cache : List Bool) (fnTag : Nat),
    activeFrameBody p f = some body ∧
    activeRefFrameBody rp f = some rbody ∧
    decodeBody rp.types rbody = some body ∧
    fnTag = (match f.sysrootOp? with
      | some op => fnTagForSysroot op
      | none => fnTagForCrate f.defId) ∧
    (f.sysrootOp? = none → MirSemantics.getElem? p.bodies f.defId = some body) ∧
    (∀ op, f.sysrootOp? = some op → f.defId = 0) ∧
    Nat.blt body.argumentCount body.locals.length = true ∧
    storageAnnotationsInBounds body = true ∧
    discriminantTypesValid body = true ∧
    castTypesValid body = true ∧
    assignTypesValid body = true ∧
    callsAdmitted p body = true ∧
    allCallBodiesStaticAdmitted p body = true ∧
    body.locals.all isSupportedScalarOrUnitTy = true ∧
    SlotsMatchTys body.locals f.locals ∧
    FramePcInBounds body f ∧
    cache.length = body.locals.length ∧
    rf = mkRefMiriCallFrame rp.types fnTag rbody f.blockIdx f.stmtIdx
      (liftLocalsCached rp.types body.locals f.locals cache) callerIdx
      dstLocalId dstTy f.retTarget?

/-- Inductive stack-frame correspondence relating a top-first
$M_{\text{anneal}}$ frame stack to its top-first list of real
`Miri.Interpreter.Frame`s. -/
inductive FramesSimInv (rp : RefProg) (p : Program)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance) :
    List FrameState →
      List (Miri.Interpreter.Frame Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout
        Miri.Interpreter.MachineHooks.FrameExtra) → Prop where
  | root {f : FrameState}
      {rf : Miri.Interpreter.Frame Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout
        Miri.Interpreter.MachineHooks.FrameExtra} :
      f.defId = p.entryDefId →
      f.sysrootOp? = none →
      f.retDst? = none →
      f.retTarget? = none →
      FrameSimInv rp p f retPlace rf →
      FramesSimInv rp p retPlace [f] [rf]
  | push {callee caller : FrameState} {rest : List FrameState}
      {rcallee rcaller : Miri.Interpreter.Frame Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout
        Miri.Interpreter.MachineHooks.FrameExtra}
      {rrest : List (Miri.Interpreter.Frame Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout
        Miri.Interpreter.MachineHooks.FrameExtra)}
      {callerBody calleeBody : Body} {dst : Place} {dstTy retTy : MirTy} :
      FramesSimInv rp p retPlace (caller :: rest) (rcaller :: rrest) →
      activeFrameBody p caller = some callerBody →
      activeFrameBody p callee = some calleeBody →
      callee.retDst? = some dst →
      dst.projection.isEmpty = true →
      MirSemantics.getElem? callerBody.locals dst.localId = some dstTy →
      isSupportedScalarOrUnitTy dstTy = true →
      MirSemantics.getElem? calleeBody.locals 0 = some retTy →
      MirTy.beq dstTy retTy = true →
      (match callee.retTarget? with
       | none => True
       | some tgt => Nat.blt tgt callerBody.basicBlocks.length = true) →
      (∃ ls, rcaller.locals[dst.localId]? = some ls ∧ ls.layout.isSome = true) →
      CallFrameSimInv rp p callee rest.length dst.localId dstTy rcallee →
      FramesSimInv rp p retPlace (callee :: caller :: rest)
        (rcallee :: rcaller :: rrest)

/-- Admissible `topUserRelevantFrame` thread cache values for a non-empty stack
of depth `numFrames`: `none` only on the initial 1-frame stack, or `some
(numFrames - 1)` when all stack frames have user relevance `255`. -/
def refTopRelevanceValid (numFrames : Nat) : Option Nat → Prop
  | none => numFrames = 1
  | some idx => 0 < numFrames ∧ idx = numFrames - 1

/-- Type of the entry function's return place `_0`, which types the caller-owned
return allocation `retPlace`. -/
noncomputable def entryRetTy? (p : Program) : Option MirTy :=
  match MirSemantics.getElem? p.bodies p.entryDefId with
  | some body => MirSemantics.getElem? body.locals 0
  | none => none

/-- Whole-state one-to-one simulation invariant between $M_{\text{anneal}}$ and
the real `ExecutionMachine`-backed $M_{\text{ref}}$ across single- and
multi-frame call stacks: constrains every semantic field of `s` and `rs`
(including bottom-to-top `Miri.Interpreter.Frame`s, fresh caller-owned return
allocation `retPlace` in `miri.machine.memory`, disabled borrow/race trackers,
`pendingMoveDeinit = false`, `callerMem`, `RefControlValid`, and
`refTopRelevanceValid`), unique in both directions up to `(stepsExecuted,
maxSteps, miri.machine.user.control, miri.machine.threads, local layout cache
bits)`. -/
def SimulationInv (rp : RefProg) (p : Program) (s : State) (rs : RefState) :
    Prop :=
  ∃ (rframes : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra))
    (retTy : MirTy)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (topRel? : Option Nat),
    decodeProg rp = some p ∧
    !s.frames.isEmpty = true ∧
    s.mem = entryMemory ∧
    entryRetTy? p = some retTy ∧
    rs.retTy = retTy ∧
    refInitMemoryAndRetPlace rp.types retTy = .ok (mem, rs.retPlace) ∧
    RefControlValid ctrl ∧
    refTopRelevanceValid rframes.size topRel? ∧
    rs.miri = mkRefMiriStackState rframes topRel? mem ctrl s.callerMem ∧
    FramesSimInv rp p rs.retPlace s.frames rframes.toList.reverse

end Trusted.Correspondence
