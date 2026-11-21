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
import Trusted.Correspondence.Eval

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Simulation Invariant (`Trusted.Correspondence.Simulation`)

Relates $M_{\text{anneal}}$ states (`Trusted.MirSemantics.State`) to
$M_{\text{ref}}$ states (`RefState`).
-/

/-! ## One-to-One Simulation Invariant (`SimulationInv`) -/

/-- Pair each runtime `LocalSlot` with its pre-cached `some ty` layout. -/
noncomputable def zipRefLocals :
    List MirTy → List LocalSlot → List RefLocalState
  | ty :: tys, slot :: slots => ⟨slot, some ty⟩ :: zipRefLocals tys slots
  | _, _ => []

/-- Lift an $M_{\text{anneal}}$ `FrameState` to its unique $M_{\text{ref}}$
`RefFrameState` with `cachedLayout` populated from `bodyLocals`. -/
noncomputable def liftFrame (bodyLocals : List MirTy)
    (f : FrameState) : RefFrameState :=
  { defId := f.defId
    blockIdx := f.blockIdx
    stmtIdx := f.stmtIdx
    locals := zipRefLocals bodyLocals f.locals
    isCallerSentinel := false }

/-- Lift an $M_{\text{anneal}}$ single-frame `StepResult` to
$M_{\text{ref}}$. -/
noncomputable def mapStepRes (bodyLocals : List MirTy) :
    StepResult State TerminalOut → StepResult RefState TerminalOut
  | .step { frames := [f'], callerMem := cm } =>
    .step { frames := [liftFrame bodyLocals f'], callerMem := cm }
  | .step { frames := _, callerMem := cm } =>
    .step { frames := [], callerMem := cm }
  | .done out => .done out
  | .fault k => .fault k

/-- Frame-level one-to-one simulation invariant: relates $M_{\text{anneal}}$
frame `f` to $M_{\text{ref}}$ frame `rf` via exact equality
`rf = liftFrame body.locals f`. -/
def FrameSimInv (p : Program) (f : FrameState)
    (rf : RefFrameState) : Prop :=
  ∃ body : Body,
    MirSemantics.getElem? p.bodies f.defId = some body ∧
    f.locals.length = body.locals.length ∧
    rf = liftFrame body.locals f

/-- Type of the entry function's return place `_0`, which types the caller
sentinel's destination slot (`callerSentinelFrame`). -/
noncomputable def entryRetTy? (p : Program) : Option MirTy :=
  match MirSemantics.getElem? p.bodies p.entryDefId with
  | some body => MirSemantics.getElem? body.locals 0
  | none => none

/-- Whole-state one-to-one simulation invariant between $M_{\text{anneal}}$ and
$M_{\text{ref}}$: constrains every field of `s` and `rs` (up to the explicit
step counters `rs.stepsExecuted` and `rs.maxSteps`), placing the fixed caller
sentinel for the entry function's return type beneath the lifted image of the
single $M_{\text{anneal}}$ frame executing `p.entryDefId`. -/
def SimulationInv (p : Program) (s : State) (rs : RefState) :
    Prop :=
  ∃ f : FrameState, ∃ rf : RefFrameState, ∃ retTy : MirTy,
    s.frames = [f] ∧
    rs.frames = [callerSentinelFrame retTy, rf] ∧
    rs.callerMem = s.callerMem ∧
    entryRetTy? p = some retTy ∧
    f.defId = p.entryDefId ∧
    FrameSimInv p f rf

end Trusted.Correspondence
