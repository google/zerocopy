-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.ByteCodec
import Anneal.MirCorrespondence.LayoutAndAlign
import Anneal.MirCorrespondence.MiriMemoryBridge
import Anneal.MirCorrespondence.ProfileV2RefMachine
import Anneal.MirCorrespondence.ProfileV2Correspondence
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.SimHelpers

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# Profile v2 Symbolic Stepping Toolkit (`ProfileV2Witnesses`)

Companion module to `Anneal.MirCorrespondence.ProfileV2Correspondence` providing
a reusable symbolic stepping toolkit for
`Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)`, including
zero-TCB `Init.Internal.Order.While` (`Lean.Loop.forIn_eq_of_monadTail`)
unfolding for `ValidityVisitor.validatePlace` (`recursive := true`).

Concrete conservative-edge separations (`Edge 1`–`Edge 3`,
`not_biFaultEquivV2_encodeProg`) live in
`Anneal.MirCorrespondence.ProfileV2EdgeWitnesses`; canary definitions and
negative locksteps (`V2_C4a`–`V2_C6`) live in `ProfileV2Canaries`; positive
locksteps (`V2_C2`, `V2_C1`, `V2_C3`) and domain `SafetyRefinementV2On` /
`BiFaultEquivV2On` bundles live in `ProfileV2PosCanaries`,
`ProfileV2PosCanariesC1`, and `ProfileV2C3AndBundles`.
-/

/-! ## Section 1: Profile v2 Witness Program Helpers -/

/-- Helper constructing a Profile v2 single-body `Program`. -/
noncomputable def mkV2Prog (body : Body) : Program := {
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [body]
}

/-! ## Section 2: Symbolic Stepping Toolkit for `ExecutionMachine.step` -/

noncomputable abbrev refExecCfgV2 (rp : RefProg) :=
  Miri.Interpreter.ExecutionMachine.withValidation
    (refExecutionConfigV2 rp) refLimitsV2

theorem refStepCfgV2_eq (rp : RefProg) :
    Miri.Interpreter.ExecutionMachine.withValidation (refExecCfgV2 rp)
      refLimitsV2 = refExecCfgV2 rp := rfl

noncomputable def refValHooksV2 (types : List MirTy) :=
  Miri.Interpreter.TypedMachineBindings.bindValidity
    (refValidityHooksV2 types) refRetagHooks 16

theorem refTryNew_spec_v2 (sz : Miri.ABI.Size) (al : Miri.ABI.Align)
    (ab : UInt64) (hab : al.bytes = .ok ab)
    (hna : Miri.ABI.Align.fromBytes ab = .ok al) :
    ∃ a : Miri.Memory.Allocation Miri.Memory.Provenance Unit,
      Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance) sz al
        .Uninit (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok a ∧
      a.byteSize = sz ∧
      a.len = sz.bytes.toNat ∧
      a.mutability = .Mut ∧
      a.align = al ∧
      a.extra = () ∧
      a.nativeBuffer = none ∧
      a.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      a.initializationMask = Miri.Memory.InitMask.new sz false ∧
      Miri.Memory.InitMask.WriteProof.WellFormed a.initializationMask ∧
      (∀ (range : Miri.Memory.AllocRange) (finish : Miri.ABI.Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ sz.bytes.toNat →
        a.getBytesUnchecked range =
          .ok (Array.replicate (finish.bytes.toNat - range.start.bytes.toNat) 0)) := by
  let ⟨a, h_ok, h_al⟩ :=
    Miri.Memory.Allocation.tryNew_exists (P := Miri.Memory.Provenance)
      sz al ab .Uninit hab hna
  let ⟨h_sz, h_len, h_mut, h_ext, h_nb, h_pm, h_im, _, h_wf, h_gb⟩ :=
    Miri.Memory.Allocation.tryNew_spec sz al .Uninit a h_ok
  exact ⟨a, h_ok, h_sz, h_len, h_mut, h_al, h_ext, h_nb, h_pm, h_im rfl, h_wf,
    h_gb⟩

theorem refState_with_pmd_false (st : RefMiriState)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    ({ st with machine := { st.machine with pendingMoveDeinit := false } } :
      RefMiriState) = st := by
  cases st with
  | mk s m =>
    cases m with
    | mk m1 b1 d1 t1 r1 a1 u1 pmd =>
      dsimp only at h_pmd
      subst h_pmd
      rfl

theorem eStateM_bind_pure_fn {ε σ α β : Type} (a : α)
    (f : α → EStateM ε σ β) :
    EStateM.bind (EStateM.pure a) f = f a := rfl

theorem eStateM_apply_bind {ε σ α β : Type} (x : EStateM ε σ α)
    (f : α → EStateM ε σ β) (a : α) (s s₁ : σ)
    (h : x s = .ok a s₁) {out : EStateM.Result ε σ β}
    (hf : f a s₁ = out) :
    EStateM.bind x f s = out := by
  dsimp only [EStateM.bind]; rw [h]; exact hf

theorem eStateM_loop_forIn_eq {ε σ β : Type} (s0 : σ)
    {l : Lean.Loop} {b : β}
    {f : Unit → β → EStateM ε σ (ForInStep β)} :
    ForIn.forIn l b f =
      Bind.bind (f () b) (fun step =>
        match step with
        | .done val => pure val
        | .yield val => ForIn.forIn l val f) :=
  let mt : Lean.Order.MonadTail (EStateM ε σ) := {
    instCCPO α instA :=
      @Lean.Order.instCCPOPi σ
        (fun _ => EStateM.Result ε σ α)
        (fun _ =>
          @Lean.Order.FlatOrder.instCCPO (EStateM.Result ε σ α)
            (.ok (@Classical.choice α instA) s0))
    bind_mono_right {α γ a f₁ f₂} instG h s := by
      dsimp only [Bind.bind, EStateM.bind]
      cases a s with
      | error e s' =>
        exact @Lean.Order.FlatOrder.rel.refl (EStateM.Result ε σ γ)
          (.ok (@Classical.choice γ instG) s0) (.error e s')
      | ok x s' => dsimp only; exact h x s'
  }
  @Lean.Loop.forIn_eq_of_monadTail (EStateM ε σ) _ _ _ mt l b f

theorem beforeTerminator_initCtrl_v2 (rp : RefProg) (st : RefMiriState)
    (h_ctrl : st.machine.user.control = refInitControl)
    (h_threads : st.machine.threads =
      Miri.Concurrency.ThreadManager.initial true) :
    (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
        refLimitsV2).beforeTerminator 0 st =
      ({ st with
          machine := { st.machine with
            user := { st.machine.user with
              control := advanceRefControl refInitControl } } }, .ok ()) := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      cases user with
      | mk control callerMem =>
        dsimp only at h_ctrl h_threads
        subst h_ctrl h_threads
        rfl

theorem stack_currentFrame_single_v2 (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (h_fr : st.stack.frames = Array.mk [frame]) :
    st.stack.currentFrame? = some frame := by
  dsimp only [Miri.Interpreter.Stack.currentFrame?]
  rw [h_fr]
  rfl

private theorem evalStatement_assign_v2 {P L E M C V : Type}
    (hooks : Miri.Interpreter.StepHooks P L E M C V) (c : C)
    (stmt : Miri.MIR.Statement) (mirDst : Miri.MIR.Place)
    (mirRv : Miri.MIR.Rvalue) (st : Miri.Interpreter.StepState P L E M)
    (h_kind : stmt.kind = .Assign mirDst mirRv) :
    Miri.Interpreter.Step.evalStatement hooks c stmt st =
      hooks.assign c mirDst mirRv st := by
  cases stmt with
  | mk _ kind =>
    dsimp only at h_kind
    subst h_kind
    rfl

theorem execStep_assign_ok (rp : RefProg) (st st' : RefMiriState)
    (frame frame' : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (bbId : BasicBlockId) (sIdx : Nat)
    (block : Miri.MIR.BasicBlock) (stmt : Miri.MIR.Statement)
    (mirDst : Miri.MIR.Place) (mirRv : Miri.MIR.Rvalue)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_loc : frame.location = .mir ⟨bbId, sIdx⟩)
    (h_bb : frame.body.basicBlocks[bbId]? = some block)
    (h_st : block.statements[sIdx]? = some stmt)
    (h_kind : stmt.kind = .Assign mirDst mirRv)
    (h_assign : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).assign 0 mirDst mirRv st =
      (st', .ok ()))
    (h_fr' : st'.stack.frames = Array.mk [frame'])
    (h_loc' : frame'.location = .mir ⟨bbId, sIdx⟩) :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
        refLimitsV2 0 st =
      ({ st' with
          stack :=
            ⟨Array.mk [{ frame' with location := .mir ⟨bbId, sIdx + 1⟩ }]⟩
          machine := { st'.machine with pendingMoveDeinit := false } },
        .ok true) := by
  have h_cf := stack_currentFrame_single_v2 st frame h_fr
  have h_cf' := stack_currentFrame_single_v2 st' frame' h_fr'
  have h_ev := evalStatement_assign_v2
    (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
      refLimitsV2) 0 stmt mirDst mirRv st h_kind
  dsimp only [Miri.Interpreter.ExecutionMachine.step]
  rw [refState_with_pmd_false st h_pmd]
  dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure,
    Pure.pure]
  rw [h_cf]
  dsimp only
  rw [h_loc]
  dsimp only
  rw [h_bb]
  dsimp only
  rw [h_st]
  dsimp only
  rw [h_ev, h_assign]
  dsimp only
  rw [h_cf']
  dsimp only
  rw [h_loc', h_fr, h_fr']
  rfl

theorem execStep_assign_err (rp : RefProg) (st st' : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (bbId : BasicBlockId) (sIdx : Nat)
    (block : Miri.MIR.BasicBlock) (stmt : Miri.MIR.Statement)
    (mirDst : Miri.MIR.Place) (mirRv : Miri.MIR.Rvalue)
    (err : Miri.Interpreter.StepError)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_loc : frame.location = .mir ⟨bbId, sIdx⟩)
    (h_bb : frame.body.basicBlocks[bbId]? = some block)
    (h_st : block.statements[sIdx]? = some stmt)
    (h_kind : stmt.kind = .Assign mirDst mirRv)
    (h_assign : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).assign 0 mirDst mirRv st =
      (st', .error err)) :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
        refLimitsV2 0 st =
      ({ st' with machine := { st'.machine with pendingMoveDeinit := false } },
        .error err) := by
  have h_cf := stack_currentFrame_single_v2 st frame h_fr
  have h_ev := evalStatement_assign_v2
    (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
      refLimitsV2) 0 stmt mirDst mirRv st h_kind
  dsimp only [Miri.Interpreter.ExecutionMachine.step]
  rw [refState_with_pmd_false st h_pmd]
  dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure,
    Pure.pure]
  rw [h_cf]
  dsimp only
  rw [h_loc]
  dsimp only
  rw [h_bb]
  dsimp only
  rw [h_st]
  dsimp only
  rw [h_ev, h_assign]

private theorem step_term_hooks_v2 {P L E M C V : Type}
    (hooks : Miri.Interpreter.StepHooks P L E M C V) (c : C)
    (st stMid st' : Miri.Interpreter.StepState P L E M)
    (frame : Miri.Interpreter.Frame P L E)
    (bbId : BasicBlockId) (sIdx : Nat) (block : Miri.MIR.BasicBlock)
    (out : Except Miri.Interpreter.StepError Unit)
    (h_cf : st.stack.currentFrame? = some frame)
    (h_loc : frame.location = .mir ⟨bbId, sIdx⟩)
    (h_bb : frame.body.basicBlocks[bbId]? = some block)
    (h_st : block.statements[sIdx]? = none)
    (h_bt : hooks.beforeTerminator c st = (stMid, .ok ()))
    (h_term : hooks.terminator c block.terminator stMid = (st', out)) :
    Miri.Interpreter.Step.step hooks c st = (st', out.map fun _ => true) := by
  cases hooks with
  | mk f1 f2 f3 f4 f5 f6 f7 f8 beforeTerminator terminator =>
    dsimp only at h_bt h_term
    dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure,
      Pure.pure]
    rw [h_cf]; dsimp only; rw [h_loc]; dsimp only; rw [h_bb]; dsimp only
    rw [h_st]; dsimp only; rw [h_bt]; dsimp only; rw [h_term]
    rfl

theorem execStep_term_ok (rp : RefProg) (st stMid st' : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (bbId : BasicBlockId) (sIdx : Nat) (block : Miri.MIR.BasicBlock)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_loc : frame.location = .mir ⟨bbId, sIdx⟩)
    (h_bb : frame.body.basicBlocks[bbId]? = some block)
    (h_st : block.statements[sIdx]? = none)
    (h_bt : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).beforeTerminator 0 st =
      (stMid, .ok ()))
    (h_term : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).terminator 0 block.terminator
      stMid = (st', .ok ())) :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
        refLimitsV2 0 st =
      ({ st' with machine := { st'.machine with pendingMoveDeinit := false } },
        .ok true) := by
  have h_cf := stack_currentFrame_single_v2 st frame h_fr
  dsimp only [Miri.Interpreter.ExecutionMachine.step]
  rw [refState_with_pmd_false st h_pmd]
  rw [step_term_hooks_v2 _ 0 st stMid st' frame bbId sIdx block (.ok ())
    h_cf h_loc h_bb h_st h_bt h_term]
  rfl

theorem currentFrame_single_v2 (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (h_fr : st.stack.frames = Array.mk [frame]) :
    Miri.Interpreter.MachineHooks.currentFrame st = .ok frame st := by
  dsimp only [Miri.Interpreter.MachineHooks.currentFrame, get, getThe,
    MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure,
    Pure.pure, EStateM.pure, Miri.Interpreter.Stack.currentFrame?]
  rw [h_fr]
  rfl

theorem frameIndex_single_v2 (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (h_fr : st.stack.frames = Array.mk [frame]) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.frameIndex st = .ok 0 st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.projectionHooks, refExecCfgV2,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfigV2,
    refExecutionConfig, refPlaceProjectionHooksV2,
    refBasePlaceProjectionHooksV2, refBasePlaceProjectionHooks,
    Miri.Interpreter.PlaceMachine.placeHooks, bind, Bind.bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, Pure.pure, EStateM.pure,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    Miri.Interpreter.Stack.frameIndex]
  rw [h_fr]
  rfl

theorem projPlace_getFrame_eq_v2 (rp : RefProg) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.getFrame =
      Miri.Interpreter.MachineHooks.currentFrame := rfl

theorem projPlace_checkPlaceType_eq_v2 (rp : RefProg) (c : Choice)
    (mp : Miri.MIR.Place) (vp : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (st : RefMiriState) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.checkPlaceType c mp vp st = .ok () st := rfl

theorem opHooks_deinitMovedPlace_v2 (rp : RefProg) :
    (Miri.Interpreter.ExecutionMachine.operandHooks
      (refExecCfgV2 rp)).deinitMovedPlace = true := rfl

theorem opHooks_validationInProgress_v2 (rp : RefProg) (st : RefMiriState) :
    (Miri.Interpreter.ExecutionMachine.operandHooks
      (refExecCfgV2 rp)).compiler.validationInProgress st = .ok false st := rfl

theorem opHooks_checkPlaceType_v2 (rp : RefProg) (c : Choice)
    (mp : Miri.MIR.Place) (op : Miri.Interpreter.OpTy Miri.Memory.Provenance)
    (st : RefMiriState) :
    (Miri.Interpreter.ExecutionMachine.operandHooks
      (refExecCfgV2 rp)).checkPlaceType c mp op st = .ok () st := rfl

theorem opHooks_constantAt_v2 (rp : RefProg) (c : Choice)
    (path : Miri.Interpreter.OperandPath) (co : Miri.MIR.ConstOperand)
    (known : Option Miri.Interpreter.LocalLayout) :
    (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp)).constantAt
      c path co known = refEvalConstOperandV2 rp.types co := rfl

theorem array_forIn_empty_v2 {ε σ α β : Type}
    (init : β) (f : α → β → EStateM ε σ (ForInStep β)) (st : σ) :
    forIn (Array.empty : Array α) init f st = .ok init st := rfl

theorem projPlace_evalPlace_local_v2 (rp : RefProg) (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (localId : LocalId) (lay : Miri.Interpreter.LocalLayout)
    (v : Miri.Interpreter.LocalValue Miri.Memory.Provenance) (skip : Bool)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_get : frame.getLocal localId = .ok ⟨v, some lay⟩)
    (h_sized : lay.layout.isSized = true) :
    Miri.Interpreter.PlaceDynamic.evalPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp))
        0 ⟨localId, Array.empty⟩ skip st =
      .ok ⟨.local 0 localId none frame.localsIdentity, lay⟩ st := by
  have h_cf := currentFrame_single_v2 st frame h_fr
  have h_fi := frameIndex_single_v2 (rp := rp) st frame h_fr
  have h_lay :
      Miri.Interpreter.placeLayoutOfLocal
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place 0 localId st = .ok lay st := by
    dsimp only [Miri.Interpreter.placeLayoutOfLocal, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [projPlace_getFrame_eq_v2, h_cf]
    dsimp only
    rw [h_get]
    rfl
  have h_ltp :
      Miri.Interpreter.localToPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place 0 localId st =
        .ok ⟨.local 0 localId none frame.localsIdentity, lay⟩ st := by
    dsimp only [Miri.Interpreter.localToPlace, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rw [h_lay]
    dsimp only
    rw [h_sized, ite_true_eq, eStateM_bind_ok h_fi, projPlace_getFrame_eq_v2,
      eStateM_bind_ok h_cf]
    rfl
  have h_skip_f :
      (skip && (Array.empty == Array.mk [Miri.MIR.ProjectionElem.Deref])) =
      false := by
    cases skip <;> rfl
  dsimp only [Miri.Interpreter.PlaceDynamic.evalPlace, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ltp]
  dsimp only
  rw [h_skip_f, ite_false_eq]
  rw [eStateM_bind_ok (array_forIn_empty_v2 _ _ st)]
  rw [eStateM_bind_ok (projPlace_checkPlaceType_eq_v2 rp 0
    ⟨localId, Array.empty⟩
    ⟨.local 0 localId none frame.localsIdentity, lay⟩ st)]
  rfl

theorem evalOperand_local_imm_v2 (rp : RefProg) (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (localId : LocalId) (lay : Miri.Interpreter.LocalLayout)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (known : Option Miri.Interpreter.LocalLayout)
    (path : Miri.Interpreter.OperandPath)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId = .ok ⟨.live (.immediate imm), some lay⟩)
    (h_uns : lay.layout.backendRepr.isUnsized = false) :
    let opHooks := Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp)
    Miri.Interpreter.OperandMachine.evalOperandAt opHooks 0 path
        (.Copy ⟨localId, Array.empty⟩) known st =
      .ok ⟨.immediate imm, lay⟩
        { st with machine := { st.machine with pendingMoveDeinit := false } } := by
  intro opHooks
  let st1 : RefMiriState :=
    { st with machine := { st.machine with pendingMoveDeinit := false } }
  have h_s1 : st1.stack.frames = Array.mk [frame] := h_fr
  have h_cf := currentFrame_single_v2 st1 frame h_s1
  have h_op : frame.getLocalOperand localId = .ok (.immediate imm) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]
    rw [h_get]; rfl
  have h_after : Miri.Interpreter.MachineHooks.afterLocalRead localId st1 =
      .ok () st1 := by
    dsimp only [Miri.Interpreter.MachineHooks.afterLocalRead, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_cf]
    dsimp only
    rw [h_dr]
    rfl
  have h_mod :
      (modify (fun s : RefMiriState =>
          { s with machine := { s.machine with pendingMoveDeinit := false } }) :
        EStateM Miri.Interpreter.StepError RefMiriState Unit) st = .ok () st1 := rfl
  have h_lto :
      Miri.Interpreter.OperandMachine.localToOp opHooks 0 localId
          (if (Array.empty : Array Miri.MIR.ProjectionElem).isEmpty then known
           else none) st1 =
        .ok ⟨.immediate imm, lay⟩ st1 := by
    dsimp only [Miri.Interpreter.OperandMachine.localToOp, bind, Bind.bind,
      pure, Pure.pure]
    rw [eStateM_bind_ok h_cf]
    rw [eStateM_bind_ok (show _ = EStateM.Result.ok
        ⟨.live (.immediate imm), some lay⟩ st1 from by rw [h_get]; rfl)]
    dsimp only
    rw [eStateM_bind_pure]
    rw [eStateM_bind_ok h_cf]
    rw [eStateM_bind_ok (show _ = EStateM.Result.ok
        (Miri.Interpreter.Operand.immediate imm) st1 from by rw [h_op]; rfl)]
    dsimp only
    rw [h_uns, ite_false_eq, eStateM_bind_ok (opHooks_validationInProgress_v2 rp st1),
      ite_false_eq, eStateM_bind_ok h_after]
    rfl
  dsimp only [opHooks, Miri.Interpreter.OperandMachine.evalOperandAt,
    Miri.Interpreter.OperandMachine.evalOperand,
    Miri.Interpreter.OperandMachine.evalPlaceToOp,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [opHooks_deinitMovedPlace_v2, ite_true_eq, eStateM_bind_ok h_mod]
  rw [eStateM_bind_ok h_lto]
  rw [eStateM_bind_ok (array_forIn_empty_v2 _ _ st1)]
  rw [eStateM_bind_ok (opHooks_checkPlaceType_v2 rp 0
    ⟨localId, Array.empty⟩ ⟨.immediate imm, lay⟩ st1)]
  rfl

theorem refEvalConst_int_v2 (types : List MirTy) (st : RefMiriState)
    (w : IntWidth) (s : Bool) (n : Nat) (tid : TyId)
    (sc : Miri.Memory.ScalarInt)
    (h_mem : MirSemantics.getElem? types tid = some (.int w s))
    (h_try : Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 n)
      (toMiriSize w) = .ok (some sc)) :
    refEvalConstOperandV2 types
        ⟨⟨0⟩, none, .Val (.Scalar (.Int n 16)) (canonicalTyId types tid)⟩ st =
      .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar w sc.data))),
          refLocalLayoutForTyV2 types (.int w s)⟩ st := by
  let ⟨_, h_g, _⟩ := canonicalTyId_of_some h_mem
  dsimp only [refEvalConstOperandV2]
  rw [h_g]
  dsimp only [refCheckedLocalLayoutForTyV2, refCheckedLayoutDataForTyV2,
    refTyLayoutFitsU64V2, ite_true, evalRefConstLit]
  rw [h_try]
  rfl

theorem refValHooksV2_typeName (types : List MirTy) (c : Choice)
    (tyId : TyId) (st : RefMiriState) :
    (refValHooksV2 types).typeName c tyId st = .ok "" st := rfl

theorem refValHooksV2_withGhostValidation (types : List MirTy)
    {A : Type} (act : Miri.Interpreter.ValidityVisitor.M RefMiriState A) :
    (refValHooksV2 types).withGhostValidation act = act := rfl

theorem refValHooksV2_toOp (types : List MirTy) :
    (refValHooksV2 types).toOp =
      Miri.Interpreter.placeToOp (refBasePlaceProjectionHooksV2 types).place := rfl

theorem refValHooksV2_debugAssertions (types : List MirTy) :
    (refValHooksV2 types).debugAssertions = false := rfl

noncomputable def refInitSessV2 (isIndirect : Bool) :
    Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
  path := ⟨"", Array.mk []⟩, flags := ⟨true, false⟩, ctfeMode := none,
  refTracking := some .empty,
  dataBytes := if isIndirect then some .empty else none
}

theorem validatePlace_empty_noRanges_v2 (types : List MirTy)
    (st st1 : RefMiriState)
    (place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (op : Miri.Interpreter.OpTy Miri.Memory.Provenance)
    (sess₀ sess₁ : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (h_toOp : Miri.Interpreter.placeToOp
      (refBasePlaceProjectionHooksV2 types).place 0 place st = .ok op st)
    (h_sess₀ : sess₀ =
      refInitSessV2 (match op.op with | .indirect _ => true | .immediate _ => false))
    (h_visit : Miri.Interpreter.ValidityVisitor.visit
      (refValHooksV2 types) 0 16 sess₀ place st = .ok sess₁ st1)
    (h_noRanges : sess₁.dataBytes = none)
    (h_next : sess₁.refTracking.bind Miri.Memory.Validity.RefTracking.next = none) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 types)
        0 16 place true true st = .ok () st1 := by
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok (refValHooksV2_typeName types 0 place.layout.ty st)]
  rw [refValHooksV2_withGhostValidation, ite_true_eq]
  refine eStateM_apply_bind _ _ sess₁ st st1 ?_ ?_
  · rw [refValHooksV2_toOp, eStateM_bind_ok h_toOp]
    cases h_op : op.op with
    | indirect mp =>
      dsimp only
      rw [ite_true_eq]
      have hs :
          (⟨⟨"", Array.mk []⟩, ⟨true, false⟩, none, some .empty,
            some .empty⟩ :
            Miri.Interpreter.ValidityVisitor.Session
              Miri.Memory.Provenance) = sess₀ := by
        rw [h_sess₀, h_op]; rfl
      rw [hs, eStateM_bind_ok h_visit]
      rw [Miri.Interpreter.ValidityVisitor.resetPadding_no_ranges
        (refValHooksV2 types) 0 sess₁ place h_noRanges]
      dsimp only [pure, Pure.pure]
      rw [eStateM_bind_pure]
      rfl
    | immediate imm =>
      dsimp only
      rw [ite_true_eq]
      have hs :
          (⟨⟨"", Array.mk []⟩, ⟨true, false⟩, none, some .empty, none⟩ :
            Miri.Interpreter.ValidityVisitor.Session
              Miri.Memory.Provenance) = sess₀ := by
        rw [h_sess₀, h_op]; rfl
      rw [hs, eStateM_bind_ok h_visit]
      rw [Miri.Interpreter.ValidityVisitor.resetPadding_no_ranges
        (refValHooksV2 types) 0 sess₁ place h_noRanges]
      dsimp only [pure, Pure.pure]
      rw [eStateM_bind_pure]
      rfl
  rw [ite_true_eq, eStateM_loop_forIn_eq st1]
  dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]
  rw [h_next]
  dsimp only
  rw [eStateM_bind_pure_fn]
  dsimp only
  rw [eStateM_loop_forIn_eq st1, ite_false_eq]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_pure_fn]
  dsimp only
  rw [eStateM_bind_pure]
  rfl

theorem afterLocalRead_no_race_v2 (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (localId : LocalId)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none) :
    Miri.Interpreter.MachineHooks.afterLocalRead localId st = .ok () st := by
  have h_cf := currentFrame_single_v2 st frame h_fr
  dsimp only [Miri.Interpreter.MachineHooks.afterLocalRead, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_cf]
  dsimp only
  rw [h_dr]
  rfl

theorem afterLocalWrite_no_race_v2 (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (localId : LocalId) (initOnly : Bool)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none) :
    Miri.Interpreter.MachineHooks.afterLocalWrite localId initOnly st =
      .ok () st := by
  have h_cf := currentFrame_single_v2 st frame h_fr
  dsimp only [Miri.Interpreter.MachineHooks.afterLocalWrite, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_cf]
  dsimp only
  rw [h_dr]
  rfl

theorem refLocalLayoutForTyV2_rawPtr_sized (types : List MirTy)
    (mut_ : Trusted.MirAst.Mutability) (pt : MirTy)
    (h_uns : refIsUnsizedTyV2 pt = false) :
    (refLocalLayoutForTyV2 types (.rawPtr mut_ pt)).layout =
      refThinPtrLayoutDataV2 := by
  cases pt with
  | slice _ => cases h_uns
  | _ => rfl

theorem refLayoutDataForTyV2_isSized (ty : MirTy)
    (h_uns : refIsUnsizedTyV2 ty = false) :
    (refLayoutDataForTyV2 ty).isSized = true := by
  cases ty with
  | slice _ => cases h_uns
  | ref _ pt => cases pt <;> rfl
  | rawPtr _ pt => cases pt <;> rfl
  | rangeTo t =>
    cases t with
    | int w s => cases w <;> cases s <;> rfl
    | _ => rfl
  | rangeFrom t =>
    cases t with
    | int w s => cases w <;> cases s <;> rfl
    | _ => rfl
  | enum ety =>
    dsimp only [refLayoutDataForTyV2, refAsEnumTy?, refEnumLayoutDataV2]
    cases ety.tagRepr <;> rfl
  | tuple fs =>
    cases fs with
    | nil => rfl
    | cons a as =>
      cases as with
      | nil =>
        cases h_t : refTupleFieldsLayoutV2 0 0 [a] with
        | mk offs rest =>
          cases rest with
          | mk endOff maxPow2 =>
            cases a <;> simp only [refLayoutDataForTyV2, h_t] <;> rfl
      | cons b bs =>
        cases bs with
        | nil =>
          cases a with
          | int w s =>
            cases b with
            | bool => rfl
            | _ =>
              unfold refLayoutDataForTyV2
              dsimp only
              cases h_t : refTupleFieldsLayoutV2 0 0 [.int w s, _] with
              | mk offs rest => cases rest with | mk endOff maxPow2 => rfl
          | _ =>
            unfold refLayoutDataForTyV2
            dsimp only
            cases h_t : refTupleFieldsLayoutV2 0 0 [_, b] with
            | mk offs rest => cases rest with | mk endOff maxPow2 => rfl
        | cons c cs =>
          cases h_t : refTupleFieldsLayoutV2 0 0 (a :: b :: c :: cs) with
          | mk offs rest =>
            cases rest with
            | mk endOff maxPow2 =>
              cases a with
              | int w s =>
                cases b <;> simp only [refLayoutDataForTyV2, h_t] <;> rfl
              | _ =>
                simp only [refLayoutDataForTyV2, h_t] <;> rfl
  | _ => rfl

theorem frame_setLocalOperand_spec_v2
    (frame frame' : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (localId : LocalId) (v : Miri.Interpreter.Operand Miri.Memory.Provenance)
    (h_set : frame.setLocalOperand localId v = .ok frame') :
    frame'.extra = frame.extra ∧
    frame'.localsIdentity = frame.localsIdentity ∧
    frame'.body = frame.body := by
  cases frame with
  | mk b bi fi ext rc rp li ls vl tc loc =>
    dsimp only [Miri.Interpreter.Frame.setLocalOperand] at h_set
    cases h_g : Miri.Interpreter.Frame.getLocalOperand
        ⟨b, bi, fi, ext, rc, rp, li, ls, vl, tc, loc⟩ localId with
    | error e => rw [h_g] at h_set; cases h_set
    | ok ov =>
      rw [h_g] at h_set
      dsimp only [Miri.Interpreter.Frame.replaceLocalValue, bind, Bind.bind,
        Except.bind, pure, Pure.pure, Except.pure] at h_set
      cases h_dec : decide (localId < ls.size) with
      | false =>
        have h_f : ¬ (localId < ls.size) := by
          intro h_t; rw [decide_eq_true h_t] at h_dec; cases h_dec
        simp [h_f] at h_set
      | true =>
        have h_t : localId < ls.size := of_decide_eq_true h_dec
        simp [h_t] at h_set
        rw [← h_set]
        exact ⟨rfl, rfl, rfl⟩

theorem refBaseProj_debugOff_v2 (types : List MirTy) :
    (refBasePlaceProjectionHooksV2 types).place.debugAssertions = false := rfl

theorem refProjPlace_debugOff_v2 (rp : RefProg) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.debugAssertions = false := rfl

theorem refProjPlace_localToOp_v2 (rp : RefProg) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.localToOp =
      Miri.Interpreter.PlaceMachine.localToOp
        (refCompilerHooksV2 rp.types) := rfl

theorem refProjPlace_getFrame_v2 (rp : RefProg) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.getFrame =
      Miri.Interpreter.MachineHooks.currentFrame := rfl

theorem refProjPlace_writeLocalImm_v2 (rp : RefProg) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.writeLocalImmediate =
      fun _ => Miri.Interpreter.placeWriteLocalImmediate
        Miri.Interpreter.MachineHooks.currentFrame
        Miri.Interpreter.MachineHooks.setCurrentFrame
        (refCompilerHooksV2 rp.types).validationInProgress
        Miri.Interpreter.MachineHooks.afterLocalWrite
        (refCompilerHooksV2 rp.types).debugAbiCheck := rfl

theorem refProjPlace_enforceValidity_v2 (rp : RefProg) (c : Choice)
    (lay : Miri.Interpreter.LocalLayout) (st : RefMiriState) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.enforceValidity c lay st = .ok true st := rfl

theorem refProjPlace_validate_v2 (rp : RefProg) (c : Choice)
    (place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks
      (refExecCfgV2 rp)).place.validate c place =
      Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 rp.types)
        c 16 place true true := rfl

private theorem placeToOp_val_local_imm_v2 (types : List MirTy)
    (localId : LocalId) (ty : MirTy)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (st : RefMiriState)
    (h_uns : refIsUnsizedTyV2 ty = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate imm), some (refLocalLayoutForTyV2 types ty)⟩) :
    Miri.Interpreter.placeToOp (refBasePlaceProjectionHooksV2 types).place 0
        ⟨.local 0 localId none frame.localsIdentity,
          refLocalLayoutForTyV2 types ty⟩ st =
      .ok ⟨.immediate imm, refLocalLayoutForTyV2 types ty⟩ st := by
  have h_cf := currentFrame_single_v2 st frame h_fr
  have h_fi : (refBasePlaceProjectionHooksV2 types).place.frameIndex st =
      .ok 0 st := by
    dsimp only [refBasePlaceProjectionHooksV2, refBasePlaceProjectionHooks,
      Miri.Interpreter.PlaceMachine.placeHooks, bind, Bind.bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw,
      Miri.Interpreter.Stack.frameIndex]
    rw [h_fr]
    rfl
  have h_op : frame.getLocalOperand localId = .ok (.immediate imm) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]; rw [h_get]; rfl
  have h_sz : (refLocalLayoutForTyV2 types ty).layout.isSized = true :=
    refLayoutDataForTyV2_isSized ty h_uns
  have h_dbg : (refBasePlaceProjectionHooksV2 types).place.debugAssertions =
      false := rfl
  have h_vip : (refBaseCompilerHooksV2 types).validationInProgress =
      (fun st => .ok false st) := rfl
  have h_ar := afterLocalRead_no_race_v2 st frame localId h_fr h_dr
  have h_lto :
      (refBasePlaceProjectionHooksV2 types).place.localToOp 0 localId st =
        .ok ⟨.immediate imm, refLocalLayoutForTyV2 types ty⟩ st := by
    dsimp only [refBasePlaceProjectionHooksV2, refBasePlaceProjectionHooks,
      Miri.Interpreter.PlaceMachine.placeHooks,
      Miri.Interpreter.PlaceMachine.localToOp,
      Miri.Interpreter.PlaceMachine.localToOpCore,
      Miri.Interpreter.PlaceMachine.layoutLocal]
    simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      h_cf, h_get, h_op, h_sz, h_vip, h_ar,
      Bool.not_true, Bool.false_eq_true, ite_false]
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore]
  simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    h_fi, h_dbg, h_lto, bne_self_eq_false, Bool.false_eq_true, ite_false]

private theorem valMem_readImm_ptr_v2 (types : List MirTy) (tyId : TyId)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance) (st : RefMiriState) :
    Miri.Interpreter.ValidityMemory.readImmediate (refValidityMemoryEnvV2 types)
        ⟨.immediate (.scalar sc), ⟨tyId, refThinPtrLayoutDataV2⟩⟩
        .rawPointer st =
      .ok ⟨.scalar sc, ⟨tyId, refThinPtrLayoutDataV2⟩⟩ st := by
  cases st with
  | mk stack machine => rfl

theorem writeLocalImmediate_direct_v2 (rp : RefProg) (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (localId : LocalId) (oldImm newImm : Miri.Interpreter.Immediate
      Miri.Memory.Provenance)
    (lay : Miri.Interpreter.LocalLayout)
    (frame' : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_sz : lay.layout.isSized = true)
    (h_get : frame.getLocal localId = .ok ⟨.live (.immediate oldImm), some lay⟩)
    (h_set : frame.setLocalOperand localId (.immediate newImm) = .ok frame')
    (h_val : Miri.Interpreter.ValidityVisitor.validatePlace
      (refValHooksV2 rp.types) 0 16
      ⟨.local 0 localId none frame.localsIdentity, lay⟩ true true
      { st with stack := ⟨Array.mk [frame']⟩ } =
      .ok () { st with stack := ⟨Array.mk [frame']⟩ }) :
    (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecutionConfigV2 rp)
      refLimitsV2).writeImmediate 0 newImm
      ⟨.local 0 localId none frame.localsIdentity, lay⟩ st =
      .ok () { st with stack := ⟨Array.mk [frame']⟩ } := by
  have h_cf := currentFrame_single_v2 st frame h_fr
  have h_fi := frameIndex_single_v2 (rp := rp) st frame h_fr
  have h_fr' : ({ st with stack := ⟨Array.mk [frame']⟩ } : RefMiriState).stack.frames =
      Array.mk [frame'] := rfl
  let ⟨h_dr_eq, _⟩ :=
    frame_setLocalOperand_spec_v2 frame frame' localId (.immediate newImm) h_set
  have h_dr' : frame'.extra.dataRace = none := by rw [h_dr_eq, h_dr]
  have h_g_op : frame.getLocalOperand localId = .ok (.immediate oldImm) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]; rw [h_get]; rfl
  have h_dbg := refProjPlace_debugOff_v2 rp
  have h_vip : (refCompilerHooksV2 rp.types).validationInProgress
      { st with stack := ⟨Array.mk [frame']⟩ } =
      .ok false { st with stack := ⟨Array.mk [frame']⟩ } := rfl
  have h_abid : (refCompilerHooksV2 rp.types).debugAbiCheck newImm lay
      { st with stack := ⟨Array.mk [frame']⟩ } =
      .ok () { st with stack := ⟨Array.mk [frame']⟩ } := rfl
  have h_sf :
      Miri.Interpreter.MachineHooks.setCurrentFrame frame' st =
        .ok () { st with stack := ⟨Array.mk [frame']⟩ } := by
    dsimp only [Miri.Interpreter.MachineHooks.setCurrentFrame,
      get, getThe, MonadStateOf.get, EStateM.get, set,
      MonadStateOf.set, EStateM.set, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_fr]
    rfl
  have h_aw := afterLocalWrite_no_race_v2
    { st with stack := ⟨Array.mk [frame']⟩ } frame' localId false h_fr' h_dr'
  have h_wl :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.writeLocalImmediate 0 localId lay newImm st =
        .ok () { st with stack := ⟨Array.mk [frame']⟩ } := by
    rw [refProjPlace_writeLocalImm_v2]
    dsimp only [Miri.Interpreter.placeWriteLocalImmediate,
      bind, Bind.bind, pure, Pure.pure]
    simp only [h_sz, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [eStateM_bind_ok h_cf, h_g_op, Miri.Interpreter.stackLift_ok]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure_fn]
    dsimp only
    rw [h_set, Miri.Interpreter.stackLift_ok]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure_fn, eStateM_bind_ok h_sf, eStateM_bind_ok h_vip]
    simp only [Bool.false_eq_true, ite_false]
    rw [eStateM_bind_ok h_aw]
    exact h_abid
  have h_ev := refProjPlace_enforceValidity_v2 rp 0 lay
    { st with stack := ⟨Array.mk [frame']⟩ }
  dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
    Miri.Interpreter.writePlaceImmediate,
    Miri.Interpreter.writePlaceImmediateNoValidate,
    Miri.Interpreter.asMplaceOrMutableLocal]
  simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff _ _ h_dbg,
    Miri.Interpreter.stackLift_ok, refProjPlace_getFrame_v2,
    h_sz, h_dbg, h_fi, h_cf, h_g_op, h_wl, h_ev, Option.isSome,
    bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  rw [refProjPlace_validate_v2]
  exact h_val

/-! ## Section 3: Validity Visitor & Reference-Return Stepping Lemmas -/

theorem refValHooksV2_classify (types : List MirTy) (c : Choice)
    (tyId : TyId) (st : RefMiriState) :
    (refValHooksV2 types).classify c tyId st =
      match resolveTy types tyId with
      | some .bool => .ok .boolean st
      | some (.int _ _) => .ok .integer st
      | some .char => .ok .character st
      | some .unit => .ok (.aggregate false false false) st
      | some .never => .ok .never st
      | some (.rawPtr _ pt) =>
        .ok (.rawPointer (tyIdFor types pt) (!refIsUnsizedTyV2 pt)) st
      | some (.ref .shared _) => .ok (.reference false) st
      | some (.ref .mut _) => .ok (.reference true) st
      | some (.slice elem) => .ok (.sequence (tyIdFor types elem)) st
      | some (.rangeTo (.int .isize false))
      | some (.rangeFrom (.int .isize false))
      | some (.tuple _) => .ok (.aggregate false false false) st
      | some ty =>
        match refAsEnumTy? ty with
        | some _ => .ok (.aggregate false false true) st
        | none => .error (.invalidProgram "unsupported validity type") st
      | none => .error (.invalidProgram "unsupported validity type") st := rfl

theorem refValHooksV2_readImmediate (types : List MirTy) (c : Choice)
    (place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (exp : Miri.Memory.ExpectedValue) :
    (refValHooksV2 types).readImmediate c place exp =
      Bind.bind
        (Miri.Interpreter.placeToOp
          (refBasePlaceProjectionHooksV2 types).place c place)
        (fun op =>
          Miri.Interpreter.ValidityMemory.readImmediate
            (refValidityMemoryEnvV2 types) op exp) := rfl

theorem rawPtr_validate_v2 (types : List MirTy)
    (st : RefMiriState) (localId : LocalId) (pt : MirTy)
    (mut_ : Trusted.MirAst.Mutability)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_tid : resolveTy types (tyIdFor types (.rawPtr mut_ pt)) =
      some (.rawPtr mut_ pt))
    (h_uns : refIsUnsizedTyV2 pt = false)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate (.scalar (.fromPointer
        Miri.ABI.RuntimeTargetDataLayout.default.base ptr))),
        some (refLocalLayoutForTyV2 types (.rawPtr mut_ pt))⟩) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 types) 0 16
        ⟨.local 0 localId none frame.localsIdentity,
          refLocalLayoutForTyV2 types (.rawPtr mut_ pt)⟩
        true true st = .ok () st := by
  let lay := refLocalLayoutForTyV2 types (.rawPtr mut_ pt)
  let imm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromPointer Miri.ABI.RuntimeTargetDataLayout.default.base ptr)
  let place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
    ⟨.local 0 localId none frame.localsIdentity, lay⟩
  have h_toOp := placeToOp_val_local_imm_v2 types localId (.rawPtr mut_ pt)
    imm frame st rfl h_fr h_dr h_get
  have h_lay : lay.layout = refThinPtrLayoutDataV2 :=
    refLocalLayoutForTyV2_rawPtr_sized types mut_ pt h_uns
  have h_lay_eq : lay = ⟨tyIdFor types (.rawPtr mut_ pt), refThinPtrLayoutDataV2⟩ := by
    dsimp only [lay, refLocalLayoutForTyV2] at h_lay
    dsimp only [lay, refLocalLayoutForTyV2]
    rw [h_lay]
  have h_ri_vm :
      Miri.Interpreter.ValidityMemory.readImmediate (refValidityMemoryEnvV2 types)
        ⟨.immediate imm, lay⟩ .rawPointer st =
      .ok ⟨.scalar (.fromPointer
        Miri.ABI.RuntimeTargetDataLayout.default.base ptr),
        ⟨tyIdFor types (.rawPtr mut_ pt), refThinPtrLayoutDataV2⟩⟩ st := by
    rw [h_lay_eq]
    exact valMem_readImm_ptr_v2 types (tyIdFor types (.rawPtr mut_ pt)) _ st
  have h_ri : (refValHooksV2 types).readImmediate 0 place .rawPointer st =
      .ok ⟨.scalar (.fromPointer
        Miri.ABI.RuntimeTargetDataLayout.default.base ptr),
        ⟨tyIdFor types (.rawPtr mut_ pt), refThinPtrLayoutDataV2⟩⟩ st := by
    rw [refValHooksV2_readImmediate]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_toOp]
    exact h_ri_vm
  have h_cls : (refValHooksV2 types).classify 0 lay.ty st =
      .ok (.rawPointer (tyIdFor types pt) true) st := by
    rw [refValHooksV2_classify]
    dsimp only [lay, refLocalLayoutForTyV2]
    rw [h_tid]
    dsimp only
    rw [h_uns]
    rfl
  have h_vis :
      Miri.Interpreter.ValidityVisitor.visit (refValHooksV2 types) 0 16
          (refInitSessV2 false) place st =
        .ok (refInitSessV2 false) st := by
    rw [Miri.Interpreter.ValidityVisitor.visit.eq_2]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_cls]
    change (EStateM.bind (EStateM.bind
      ((refValHooksV2 types).readImmediate 0 place .rawPointer) _) _ st) = _
    dsimp only [EStateM.bind]
    rw [h_ri]
    rfl
  exact validatePlace_empty_noRanges_v2 types st st place
    ⟨.immediate imm, lay⟩ (refInitSessV2 false) (refInitSessV2 false)
    h_toOp rfl h_vis rfl rfl

theorem alloc_writePtr_readScalar_v2 {E : Type}
    (a : Miri.Memory.Allocation Miri.Memory.Provenance E)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (h_sz : a.byteSize = Miri.ABI.Size.ofBytes 8)
    (h_len : a.len = 8)
    (h_mut : a.mutability = .Mut)
    (h_im : a.initializationMask.len = a.byteSize)
    (h_wf : Miri.Memory.InitMask.WriteProof.WellFormed a.initializationMask)
    (h_pm : a.provenanceMap = Miri.Memory.ProvenanceMap.new) :
    ∃ a',
      a.writeScalar refRuntimeLayoutV2.base
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
        (.fromPointer refRuntimeLayoutV2.base ptr) = .ok () a' ∧
      a'.byteSize = Miri.ABI.Size.ofBytes 8 ∧
      a'.readScalar refRuntimeLayoutV2.base
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
        true =
        .ok (.fromPointer refRuntimeLayoutV2.base ptr) := by
  let rng := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
  let sc := Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base ptr
  let ⟨pm1, h_ins, _, h_rp⟩ :=
    provenanceMap_new_insertPtr_roundTrip (Prov := Miri.Memory.Provenance)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) ptr.provenance
      (by decide) (by decide)
  have h_sto : a.len = a.byteSize.bytes.toNat := by
    rw [h_len, h_sz]; rfl
  have h_bd : rng.start.bytes.toNat + rng.size.bytes.toNat ≤
      a.byteSize.bytes.toNat := by
    rw [h_sz]; decide
  have h_conv : sc.toBitsOrPtrInternal rng.size = .ok (.pointer ptr) := by
    dsimp only [sc, rng, Miri.Memory.Scalar.fromPointer,
      Miri.Memory.Scalar.toBitsOrPtrInternal, refRuntimeLayoutV2,
      Miri.Memory.allocRange]
    rfl
  have h_clr : ∀ fullBytes : Array UInt8,
      a.getBytesUnchecked
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO a.byteSize) =
        .ok fullBytes →
      a.provenanceMap.clear rng fullBytes
        (Miri.ABI.Size.fromBits refRuntimeLayoutV2.base.pointerWidth.bits) =
        .ok () Miri.Memory.ProvenanceMap.new := by
    intro fullBytes _
    rw [h_pm]
    exact provenanceMap_new_clear rng fullBytes
      (Miri.ABI.Size.fromBits refRuntimeLayoutV2.base.pointerWidth.bits)
      (by decide) (by decide)
  let ⟨a', h_ws, h_bsz, _, _, _, _, _, _, _, _, h_init, h_pm', _, h_gb, _⟩ :=
    Miri.Memory.Allocation.writeScalar_spec refRuntimeLayoutV2.base a rng sc
      (.pointer ptr) Miri.Memory.ProvenanceMap.new pm1 h_sto h_mut h_im h_wf
      (by decide) (by decide) h_bd h_conv h_clr ⟨rfl, h_ins⟩
  have h_rp' : a'.provenanceMap.readPtr rng.start
      (Miri.ABI.Size.fromBits refRuntimeLayoutV2.base.pointerWidth.bits) =
      .ok (some ptr.provenance) := by
    rw [h_pm']; exact h_rp
  have h_bv : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat =
      ptr.offset.bytes.toNat := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt
      (Nat.lt_trans (UInt64.toNat_lt ptr.offset.bytes) (by decide))
  have h_slice : a'.getBytesUnchecked rng =
      .ok (Array.ofFn (fun i : Fin rng.size.bytes.toNat =>
        UInt8.ofNat (Nat.mod (Nat.div ptr.offset.bytes.toNat
          (Nat.pow 2 (8 *
            (if refRuntimeLayoutV2.base.endian == .little then i.1
             else rng.size.bytes.toNat - i.1 - 1)))) 256))) := by
    have h_g := h_gb ptr rfl
    rw [h_bv] at h_g
    exact h_g
  have h_off_bd :
      ptr.offset.bytes.toNat < Nat.pow 2 (8 * rng.size.bytes.toNat) := by
    exact Nat.lt_of_lt_of_le (UInt64.toNat_lt ptr.offset.bytes) (by decide)
  have h_rd := Miri.Memory.Allocation.readScalar_ptr_roundtrip a'
    refRuntimeLayoutV2.base rng ptr h_init rfl (by decide) h_off_bd h_rp' h_slice
  exact ⟨a', h_ws, by rw [h_bsz, h_sz], h_rd⟩

private theorem frameRelevance_beforeStackPop_single_v2 (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_thr : st.machine.threads = Miri.Concurrency.ThreadManager.initial true) :
    Miri.Interpreter.FrameRelevance.beforeStackPop st = .ok () st := by
  cases st with
  | mk stack machine =>
    cases stack with
    | mk frames =>
      cases machine with
      | mk m b d threads ra as u p =>
        dsimp only at h_fr h_thr
        subst h_fr h_thr
        rfl

theorem returnFromCurrentFrame_op_single_v2 (rp : RefProg)
    (st : RefMiriState) (retOp : Miri.Interpreter.Operand Miri.Memory.Provenance)
    (retTy : MirTy) (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (stmts0 : Array Miri.MIR.Statement) (memMid memOut : RefMiriMem)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_rc : frame.returnContinuation = .stop true)
    (h_rp : frame.returnPlace = .memory retPlace)
    (h_loc : frame.location = .mir ⟨0, 1⟩)
    (h_bt : st.machine.borrowTracker = none)
    (h_thr : st.machine.threads = Miri.Concurrency.ThreadManager.initial true)
    (h_bb0 : frame.body.basicBlocks[0]? = some {
      statements := stmts0
      terminator := { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
      cleanup := false })
    (h_retOp :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.localToOp 0 0 st =
        .ok ⟨retOp, refLocalLayoutForTyV2 rp.types retTy⟩ st)
    (h_clean : Miri.Interpreter.CallMachine.cleanup
      { refLifecycle rp.types with storage := refStorageHooksV2 rp.types }
      0 false frame
      { st with stack := ⟨Array.empty⟩,
                machine := { st.machine with memory := memMid } } =
      .ok .normal
      { st with stack := ⟨Array.empty⟩,
                machine := { st.machine with memory := memOut } })
    (h_copy : Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0
      ⟨retOp, refLocalLayoutForTyV2 rp.types retTy⟩
      ⟨.memory retPlace.mplace, retPlace.layout⟩ true
      { st with stack := ⟨Array.empty⟩ } =
      .ok ()
      { st with stack := ⟨Array.empty⟩,
                machine := { st.machine with memory := memMid } }) :
    (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
      refLimitsV2).terminator 0
      { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return } st =
      ({ st with stack := ⟨Array.empty⟩,
                 machine := { st.machine with memory := memOut } }, .ok ()) := by
  have h_scf := stack_currentFrame_single_v2 st frame h_fr
  have h_rel := frameRelevance_beforeStackPop_single_v2 st frame h_fr h_thr
  have h_pop :
      Miri.Interpreter.TypedMachineBindings.popRaw
        (Miri.Interpreter.TypedMachineBindings.retagHooks
          (refExecCfgV2 rp).access (refExecCfgV2 rp).retag) st =
        .ok frame { st with stack := ⟨Array.empty⟩ } := by
    dsimp only [Miri.Interpreter.TypedMachineBindings.popRaw,
      Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure,
      get, getThe, MonadStateOf.get, EStateM.get, set,
      MonadStateOf.set, EStateM.set, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rw [h_bt]
    simp only [Option.isSome, Bool.false_eq_true, ite_false, EStateM.pure]
    rw [h_rel]
    dsimp only [Miri.Interpreter.Stack.popFrame]
    rw [h_fr]
    rfl
  have h_lc : (refExecCfgV2 rp).lifecycle =
      { refLifecycle rp.types with storage := refStorageHooksV2 rp.types } := rfl
  dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
    Miri.Interpreter.ControlFlow.evalTerminator,
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
    Miri.Interpreter.ExecutionControl.hooks,
    Miri.Interpreter.Call.run, Miri.Interpreter.MachineHooks.run,
    Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [h_scf]
  dsimp only
  rw [h_loc]
  dsimp only
  rw [h_bb0]
  dsimp only
  rw [bne_self_eq_false, ite_false_eq, Bool.false_and, ite_false_eq]
  rw [h_retOp]
  dsimp only
  rw [h_pop]
  dsimp only
  rw [Bool.not_false, ite_true_eq, h_rp]
  dsimp only [Miri.Interpreter.RuntimeStackPlace.toRuntimePlace]
  simp only [h_copy, h_lc, h_clean, h_rc]
  rfl

theorem returnFromCurrentFrame_imm_single_v2 (rp : RefProg)
    (st : RefMiriState) (retVal : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (retTy : MirTy) (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (stmts0 : Array Miri.MIR.Statement) (mem' : RefMiriMem)
    (h_uns : refIsUnsizedTyV2 retTy = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_rc : frame.returnContinuation = .stop true)
    (h_rp : frame.returnPlace = .memory retPlace)
    (h_loc : frame.location = .mir ⟨0, 1⟩)
    (h_bt : st.machine.borrowTracker = none)
    (h_thr : st.machine.threads = Miri.Concurrency.ThreadManager.initial true)
    (h_fdr : frame.extra.dataRace = none)
    (h_bb0 : frame.body.basicBlocks[0]? = some {
      statements := stmts0
      terminator := { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
      cleanup := false })
    (h_get0 : frame.getLocal 0 =
      .ok ⟨.live (.immediate retVal), some (refLocalLayoutForTyV2 rp.types retTy)⟩)
    (h_clean : Miri.Interpreter.CallMachine.cleanup
      { refLifecycle rp.types with storage := refStorageHooksV2 rp.types }
      0 false frame
      { st with stack := ⟨Array.empty⟩,
                machine := { st.machine with memory := mem' } } =
      .ok .normal
      { st with stack := ⟨Array.empty⟩,
                machine := { st.machine with memory := mem' } })
    (h_copy : Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0
      ⟨.immediate retVal, refLocalLayoutForTyV2 rp.types retTy⟩
      ⟨.memory retPlace.mplace, retPlace.layout⟩ true
      { st with stack := ⟨Array.empty⟩ } =
      .ok ()
      { st with stack := ⟨Array.empty⟩,
                machine := { st.machine with memory := mem' } }) :
    (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
      refLimitsV2).terminator 0
      { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return } st =
      ({ st with stack := ⟨Array.empty⟩,
                 machine := { st.machine with memory := mem' } }, .ok ()) := by
  have h_cf := currentFrame_single_v2 st frame h_fr
  have h_op0 : frame.getLocalOperand 0 = .ok (.immediate retVal) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]; rw [h_get0]; rfl
  have h_sz : (refLocalLayoutForTyV2 rp.types retTy).layout.isSized = true :=
    refLayoutDataForTyV2_isSized retTy h_uns
  have h_vip : (refCompilerHooksV2 rp.types).validationInProgress st =
      .ok false st := rfl
  have h_ar := afterLocalRead_no_race_v2 st frame 0 h_fr h_fdr
  have h_retOp :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.localToOp 0 0 st =
        .ok ⟨.immediate retVal, refLocalLayoutForTyV2 rp.types retTy⟩ st := by
    rw [refProjPlace_localToOp_v2]
    dsimp only [Miri.Interpreter.PlaceMachine.localToOp,
      Miri.Interpreter.PlaceMachine.localToOpCore,
      Miri.Interpreter.PlaceMachine.layoutLocal]
    simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      h_cf, h_get0, h_op0, h_sz, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [h_vip]
    dsimp only
    simp only [Bool.false_eq_true, ite_false]
    rw [eStateM_bind_ok h_ar]
    rfl
  exact returnFromCurrentFrame_op_single_v2 rp st (.immediate retVal) retTy
    retPlace frame stmts0 mem' mem' h_fr h_rc h_rp h_loc h_bt h_thr h_bb0
    h_retOp h_clean h_copy

noncomputable def retAllocIdV2 : Miri.Memory.AllocId :=
  ⟨1, by decide⟩

noncomputable def retPtrV2 :
    Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
  ⟨Miri.ABI.Size.ZERO, some (.concrete retAllocIdV2 Miri.Memory.BorTag.one)⟩

noncomputable def retMemPlaceV2 :
    Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
  ⟨retPtrV2, .none, none⟩

noncomputable def singleDataRange64V2 :
    Miri.Memory.Validity.DataRangeSet :=
  match Miri.Memory.Validity.DataRangeSet.empty.addRange
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) with
  | .ok rs => rs
  | .error _ => .empty

private theorem getPtrAlloc_retPlace_8_ghost_aux_v2
    (sz : Miri.ABI.Size) (signedSize : Int)
    (mem : RefMiriMem) (alloc : RefMiriAlloc)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (globalHooks : Miri.Memory.GlobalAllocationHooks Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit
      (Miri.Interpreter.PlaceMachine.AccessState Unit RefUser))
    (accessHooks : Miri.Memory.AllocationAccessHooks Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit
      (Miri.Interpreter.PlaceMachine.AccessState Unit RefUser)
      Miri.Memory.ProvenanceExtra)
    (h_gh : globalHooks = refGlobalAllocationHooks)
    (h_find : mem.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, alloc⟩))
    (h_sz : alloc.byteSize = sz)
    (h_sa : Miri.Memory.sizeAsI64 sz = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_cb : Miri.Memory.checkedBounds ⟨Miri.ABI.Size.ofBytes 8⟩ retAllocIdV2
      sz Miri.ABI.Size.ZERO signedSize .memoryAccess = .ok ())
    (h_rp : accessHooks.resolvePointer mem ⟨machine, none⟩ retPtrV2 signedSize =
      ⟨⟨machine, none⟩,
        .ok (.ok ⟨retAllocIdV2, Miri.ABI.Size.ZERO,
          .concrete Miri.Memory.BorTag.one⟩)⟩) :
    Miri.Memory.AllocationAccess.getPtrAlloc mem ⟨machine, none⟩
        ⟨Miri.ABI.Size.ofBytes 8⟩ retPtrV2 sz true none
        globalHooks accessHooks =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocIdV2, Miri.Memory.allocRange Miri.ABI.Size.ZERO sz, alloc⟩,
        .ok (some ⟨retAllocIdV2, Miri.Memory.allocRange Miri.ABI.Size.ZERO sz,
          alloc⟩)⟩ := by
  have h_raw : Miri.Memory.MemoryLifecycle.getAllocRaw mem ⟨machine, none⟩
      retAllocIdV2 none globalHooks =
      ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRaw]
    rw [h_gh]
    dsimp only [refGlobalAllocationHooks, Id.run, bind, Bind.bind,
      pure, Pure.pure]
    rw [h_find]
  dsimp only [Miri.Memory.AllocationAccess.getPtrAlloc]
  change (match Miri.Memory.sizeAsI64 sz with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sa]
  change (if (signedSize != 0) = true then _ else _) = _
  rw [h_nz, ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_rp]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [ite_false_eq, h_raw]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_sz, h_cb]
  rfl

private theorem getPtrAlloc_retPlace_8_ghost_cfg_v2
    (mem : RefMiriMem) (alloc : RefMiriAlloc)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_find : mem.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, alloc⟩))
    (h_sz : alloc.byteSize = Miri.ABI.Size.ofBytes 8) :
    Miri.Memory.AllocationAccess.getPtrAlloc mem ⟨machine, none⟩
        ⟨Miri.ABI.Size.ofBytes 8⟩ retPtrV2 (Miri.ABI.Size.ofBytes 8) true none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocIdV2, Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (Miri.ABI.Size.ofBytes 8), alloc⟩,
        .ok (some ⟨retAllocIdV2, Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (Miri.ABI.Size.ofBytes 8), alloc⟩)⟩ :=
  getPtrAlloc_retPlace_8_ghost_aux_v2 (Miri.ABI.Size.ofBytes 8) 8
    mem alloc machine cfg.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks cfg)
    h_gh h_find h_sz rfl rfl (by decide)
    (by
      dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
      rw [h_res]
      rfl)

/-- Sized place access composed from a pointer access that may reorder live
rows (`memory'`). -/
theorem getPlaceAlloc_sized_of_access_v2' {P E K H X : Type}
    [DecidableEq K]
    (memory memory' : Miri.Memory.MemoryState P E K) (hooks : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (reference : Miri.Memory.AllocationAccessRef P E)
    (sized : place.layout.backendRepr.isUnsized = false)
    (aligned : place.mplace.misaligned = none)
    (actual : Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
      ⟨Miri.ABI.Size.ofBytes 8⟩ place.mplace.ptr place.layout.size
      ghost kind global access =
      ⟨memory', hooks, some reference, .ok (some reference)⟩) :
    Miri.Interpreter.getPlaceAlloc memory hooks place
        refRuntimeLayoutV2 ghost kind global access dynamic =
      ⟨memory', hooks, some reference, .ok (some reference)⟩ := by
  cases place with
  | mk mplace layout =>
    cases mplace with
    | mk ptr metaVal misaligned =>
      dsimp only at aligned
      subst aligned
      cases layout with
      | mk sz al repr cty =>
        dsimp only at sized actual
        cases repr with
        | Scalar _ | ScalarPair | SimdVector | SimdScalableVector =>
          change (match (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
              ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
            | Except.error error =>
              Miri.Interpreter.MemoryOperandResult.mk
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                (Except.error (Miri.Interpreter.MemoryOperandError.pointerAccess error))
            | Except.ok reference? =>
              Miri.Interpreter.MemoryOperandResult.mk
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                (Except.ok reference?)) = _
          rw [actual]
        | @Memory isSized =>
          cases isSized with
          | false => cases sized
          | true =>
            change (match (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
              | Except.error error =>
                Miri.Interpreter.MemoryOperandResult.mk
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                  (Except.error (Miri.Interpreter.MemoryOperandError.pointerAccess error))
              | Except.ok reference? =>
                Miri.Interpreter.MemoryOperandResult.mk
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                  (Miri.Memory.AllocationAccess.getPtrAlloc memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                  (Except.ok reference?)) = _
            rw [actual]

/-- Mutable sized place access composed from a pointer access that may
reorder the live rows (`memory'`). -/
theorem getPlaceAllocMut_sized_of_access_v2' {P E K H X : Type}
    [DecidableEq K]
    (memory memory' : Miri.Memory.MemoryState P E K) (hooks : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (reference : Miri.Memory.AllocationAccessRef P E)
    (sized : place.layout.backendRepr.isUnsized = false)
    (aligned : place.mplace.misaligned = none)
    (actual : Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
      ⟨Miri.ABI.Size.ofBytes 8⟩ place.mplace.ptr place.layout.size
      ghost kind global access =
      ⟨memory', hooks, some reference, .ok (some reference)⟩) :
    Miri.Interpreter.getPlaceAllocMut memory hooks place
        refRuntimeLayoutV2 ghost kind global access dynamic =
      ⟨memory', hooks, some reference, .ok (some reference)⟩ := by
  cases place with
  | mk mplace layout =>
    cases mplace with
    | mk ptr metaVal misaligned =>
      dsimp only at aligned
      subst aligned
      cases layout with
      | mk sz al repr cty =>
        dsimp only at sized actual
        cases repr with
        | Scalar _ | ScalarPair | SimdVector | SimdScalableVector =>
          change (match (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
              ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
            | Except.error error =>
              Miri.Interpreter.MemoryOperandResult.mk
                (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                (Except.error (Miri.Interpreter.MemoryOperandError.pointerAccess error))
            | Except.ok reference? =>
              Miri.Interpreter.MemoryOperandResult.mk
                (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                  ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                (Except.ok reference?)) = _
          rw [actual]
        | @Memory isSized =>
          cases isSized with
          | false => cases sized
          | true =>
            change (match (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).outcome with
              | Except.error error =>
                Miri.Interpreter.MemoryOperandResult.mk
                  (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                  (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                  (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                  (Except.error (Miri.Interpreter.MemoryOperandError.pointerAccess error))
              | Except.ok reference? =>
                Miri.Interpreter.MemoryOperandResult.mk
                  (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).memory
                  (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).hooks
                  (Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
                    ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access).touched
                  (Except.ok reference?)) = _
            rw [actual]

private theorem getPtrAllocMut_retPlace_8_v2 (types : List MirTy)
    (mem : RefMiriMem) (alloc : RefMiriAlloc)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
    (h_find : mem.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, alloc⟩))
    (h_last : (mem.live.filter (fun row => row.1 != retAllocIdV2)).push
      (retAllocIdV2, ⟨.stack, alloc⟩) = mem.live)
    (h_sz : alloc.byteSize = Miri.ABI.Size.ofBytes 8)
    (h_mut : alloc.mutability = .Mut)
    (h_extra : alloc.extra =
      Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
        (Miri.ABI.Size.ofBytes 8))
    (h_dr : machine.dataRace = none) :
    Miri.Memory.AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩
        ⟨Miri.ABI.Size.ofBytes 8⟩ retPtrV2 (Miri.ABI.Size.ofBytes 8) false none
        (refAccessConfigV2 types).globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 types)) =
      ⟨mem, ⟨machine, none⟩,
        some ⟨retAllocIdV2, Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (Miri.ABI.Size.ofBytes 8), alloc⟩,
        .ok (some ⟨retAllocIdV2, Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (Miri.ABI.Size.ofBytes 8), alloc⟩)⟩ := by
  exact Miri.Memory.AllocationAccess.live_mut_of_edges mem ⟨machine, none⟩
    ⟨Miri.ABI.Size.ofBytes 8⟩ retPtrV2 (Miri.ABI.Size.ofBytes 8) none
    (refAccessConfigV2 types).globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 types))
    retAllocIdV2 ⟨.stack, alloc⟩ (.concrete Miri.Memory.BorTag.one) 8
    rfl (by decide)
    (by
      dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
      exact Miri.Interpreter.PlaceMachine.resolvePointer_ok
        (refAccessConfigV2 types) mem machine retPtrV2 8 _ rfl)
    h_find h_mut rfl
    (by rw [h_sz]; decide)
    rfl
    (by
      dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
      rw [h_extra]
      exact Miri.Interpreter.PlaceMachine.memoryAccess_fresh_write
        (refAccessConfigV2 types) machine retAllocIdV2 Miri.Memory.BorTag.one
        (Miri.ABI.Size.ofBytes 8) h_dr rfl rfl rfl)
    h_last

private theorem writeMemory_thinPtr_ret_v2 (types : List MirTy)
    (mut_ : Trusted.MirAst.Mutability) (pt : MirTy)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (st : RefMiriState)
    (rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
    (h_uns : refIsUnsizedTyV2 pt = false)
    (h_raw : Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawRet)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩))
    (h_last : (st.machine.memory.live.filter
        (fun row => row.1 != retAllocIdV2)).push
      (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) = st.machine.memory.live)
    (h_dr : st.machine.dataRace = none) :
    let lay := refLocalLayoutForTyV2 types (.rawPtr mut_ pt)
    let rng := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
    ∃ after mem',
      mem' = { st.machine.memory with
        live := (st.machine.memory.live.filter
          (fun row => row.1 != retAllocIdV2)).push
            (retAllocIdV2, ⟨.stack, after⟩) } ∧
      Miri.Interpreter.PlaceMachine.writeMemory (refAccessConfigV2 types)
          (fun _ => true)
          (.scalar (.fromPointer refRuntimeLayoutV2.base ptr))
          ⟨retMemPlaceV2, lay⟩ st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      after.byteSize = Miri.ABI.Size.ofBytes 8 ∧
      after.readScalar refRuntimeLayoutV2.base rng true =
        .ok (.fromPointer refRuntimeLayoutV2.base ptr) := by
  intro lay rng
  let ⟨rawRet', h_ok, h_rsz, h_rlen, h_rmut, _, _, _, h_rpm, h_rim, h_rwf, _⟩ :=
    refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT 8 rfl rfl
  rw [h_raw] at h_ok
  injection h_ok with h_req
  subst h_req
  let alloc := rawRet.withExtra
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
      (Miri.ABI.Size.ofBytes 8))
  have h_im_len : alloc.initializationMask.len = alloc.byteSize := by
    change rawRet.initializationMask.len = rawRet.byteSize
    rw [h_rim, h_rsz]; rfl
  let ⟨after, h_ws, h_asz, h_rd⟩ := alloc_writePtr_readScalar_v2 alloc ptr
    h_rsz h_rlen h_rmut h_im_len h_rwf h_rpm
  have h_lay_d : lay.layout = refThinPtrLayoutDataV2 :=
    refLocalLayoutForTyV2_rawPtr_sized types mut_ pt h_uns
  have h_lml : Miri.Interpreter.localMemoryLayout lay =
      ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
        .Scalar (.Initialized (value := .Pointer Miri.ABI.AddressSpace.ZERO)
          (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 8))),
        some lay.ty⟩ := by
    dsimp only [Miri.Interpreter.localMemoryLayout]
    rw [h_lay_d]; rfl
  have h_ptr_acc := getPtrAllocMut_retPlace_8_v2 types st.machine.memory alloc
    st.machine h_find h_last h_rsz h_rmut rfl h_dr
  have h_place_acc :
      Miri.Interpreter.getPlaceAllocMut st.machine.memory ⟨st.machine, none⟩
          ⟨retMemPlaceV2, Miri.Interpreter.localMemoryLayout lay⟩
          (refAccessConfigV2 types).runtime false none
          (refAccessConfigV2 types).globalHooks
          (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 types))
          (refAccessConfigV2 types).dynamicLayout =
        ⟨st.machine.memory, ⟨st.machine, none⟩,
          some ⟨retAllocIdV2, rng, alloc⟩, .ok (some ⟨retAllocIdV2, rng, alloc⟩)⟩ := by
    refine Miri.Interpreter.getPlaceAllocMut_sized_of_access st.machine.memory
      ⟨st.machine, none⟩ ⟨retMemPlaceV2, Miri.Interpreter.localMemoryLayout lay⟩
      (refAccessConfigV2 types).runtime (Miri.ABI.Size.ofBytes 8) none
      (refAccessConfigV2 types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 types))
      (refAccessConfigV2 types).dynamicLayout ⟨retAllocIdV2, rng, alloc⟩
      (by rw [h_lml]; rfl) rfl rfl ?_
    rw [h_lml]
    exact h_ptr_acc
  have h_commit := Miri.Memory.MemoryState.setLiveAllocation_of_find
    st.machine.memory retAllocIdV2 ⟨.stack, alloc⟩ after h_find
  have h_sz8 : (Miri.Interpreter.localMemoryLayout lay).size =
      Miri.ABI.Size.ofBytes 8 := by
    rw [h_lml]
  have h_wm := Miri.Interpreter.writeImmediate_scalar_of_access
    st.machine.memory
    { st.machine.memory with
      live := (st.machine.memory.live.filter
        (fun row => row.1 != retAllocIdV2)).push
          (retAllocIdV2, ⟨.stack, after⟩) }
    ⟨st.machine, none⟩ ⟨retMemPlaceV2, Miri.Interpreter.localMemoryLayout lay⟩
    (refAccessConfigV2 types).runtime none
    (refAccessConfigV2 types).globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 types))
    (refAccessConfigV2 types).dynamicLayout (fun _ => true)
    (.fromPointer refRuntimeLayoutV2.base ptr)
    (.Initialized (value := .Pointer Miri.ABI.AddressSpace.ZERO)
      (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 8)))
    retAllocIdV2 alloc after
    (by rw [h_lml]) rfl trivial (by rw [h_lml]; exact Nat.le_refl _)
    (by dsimp only; rw [h_sz8]; exact h_place_acc) h_ws h_commit
  refine ⟨after, _, rfl, ?_, h_asz, h_rd⟩
  exact Miri.Interpreter.PlaceMachine.writeMemory_of_result
    (refAccessConfigV2 types) (fun _ => true)
    (.scalar (.fromPointer refRuntimeLayoutV2.base ptr))
    ⟨retMemPlaceV2, lay⟩ st _ _ rfl h_wm

private theorem readImmediate_retPlace_8_cfg_v2 (types : List MirTy)
    (mut_ : Trusted.MirAst.Mutability) (pt : MirTy)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (st : RefMiriState) (after : RefMiriAlloc)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_res : cfg.resolvePointer = refResolvePointer)
    (h_gh : cfg.globalHooks = refGlobalAllocationHooks)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, after⟩))
    (h_sz : after.byteSize = Miri.ABI.Size.ofBytes 8)
    (h_rd : after.readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
      true = .ok (.fromPointer refRuntimeLayoutV2.base ptr)) :
    let lay : Miri.Interpreter.LocalLayout :=
      ⟨tyIdFor types (.rawPtr mut_ pt), refThinPtrLayoutDataV2⟩
    let imm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base ptr)
    Miri.Interpreter.readImmediate st.machine.memory ⟨st.machine, none⟩
        (.indirect retMemPlaceV2) (Miri.Interpreter.localMemoryLayout lay)
        refRuntimeLayoutV2 true none cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
      ⟨st.machine.memory, ⟨st.machine, none⟩,
        some ⟨retAllocIdV2,
          Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8),
          after⟩,
        .ok ⟨imm, Miri.Interpreter.localMemoryLayout lay⟩⟩ := by
  intro lay imm
  let mplace : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨retMemPlaceV2,
      ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
        .Scalar (.Initialized (value := .Pointer Miri.ABI.AddressSpace.ZERO)
          (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 8))),
        some (tyIdFor types (.rawPtr mut_ pt))⟩⟩
  have h_lml : Miri.Interpreter.localMemoryLayout lay = mplace.layout := rfl
  have h_pt : mplace.mplace.ptr = retPtrV2 := rfl
  have h_lsz : mplace.layout.size = Miri.ABI.Size.ofBytes 8 := rfl
  have h_uns : mplace.layout.backendRepr.isUnsized = false := rfl
  have h_aln : mplace.mplace.misaligned = none := rfl
  have h_ptr_acc := getPtrAlloc_retPlace_8_ghost_cfg_v2 st.machine.memory
    after st.machine cfg h_res h_gh h_find h_sz
  have h_act :
      Miri.Memory.AllocationAccess.getPtrAlloc st.machine.memory
        ⟨st.machine, none⟩ ⟨Miri.ABI.Size.ofBytes 8⟩
        mplace.mplace.ptr mplace.layout.size true none cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
      ⟨st.machine.memory, ⟨st.machine, none⟩,
        some ⟨retAllocIdV2,
          Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8),
          after⟩,
        .ok (some ⟨retAllocIdV2,
          Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8),
          after⟩)⟩ := by
    rw [h_pt, h_lsz]
    exact h_ptr_acc
  have h_g_acc :
      Miri.Interpreter.getPlaceAlloc st.machine.memory ⟨st.machine, none⟩
          mplace refRuntimeLayoutV2 true none cfg.globalHooks
          (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
        ⟨st.machine.memory, ⟨st.machine, none⟩,
          some ⟨retAllocIdV2,
            Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8),
            after⟩,
          .ok (some ⟨retAllocIdV2,
            Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8),
            after⟩)⟩ := by
    exact getPlaceAlloc_sized_of_access_v2' _ _ _ mplace _ _ _ _ _ _
      h_uns h_aln h_act
  rw [h_lml]
  have h_raw_m :
      Miri.Interpreter.readImmediateFromMplaceRaw st.machine.memory
          ⟨st.machine, none⟩ mplace refRuntimeLayoutV2 true none cfg.globalHooks
          (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
        ⟨st.machine.memory, ⟨st.machine, none⟩,
          some ⟨retAllocIdV2,
            Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (Miri.ABI.Size.ofBytes 8),
            after⟩,
          .ok (some ⟨imm, mplace.layout⟩)⟩ := by
    dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run,
      bind, Bind.bind, pure, Pure.pure]
    rw [h_g_acc]
    dsimp only [mplace, Miri.ABI.BackendRepr.isUnsized]
    simp only [Bool.false_eq_true, ite_false]
    change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
      (Except.mapError Miri.Interpreter.MemoryOperandError.allocation
        (after.readScalar refRuntimeLayoutV2.base
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
          true)) _ _ = _
    rw [h_rd]
    rfl
  dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
    Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [show ({ mplace := retMemPlaceV2, layout := mplace.layout } :
      Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance) = mplace from rfl]
  rw [h_raw_m]
  dsimp only [mplace]
  rfl

private theorem rawPtr_validate_mem_8_v2 (types : List MirTy)
    (mut_ : Trusted.MirAst.Mutability) (pt : MirTy)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (st : RefMiriState) (after : RefMiriAlloc)
    (h_uns : refIsUnsizedTyV2 pt = false)
    (h_tid : resolveTy types (tyIdFor types (.rawPtr mut_ pt)) =
      some (.rawPtr mut_ pt))
    (h_find : st.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, after⟩))
    (h_sz : after.byteSize = Miri.ABI.Size.ofBytes 8)
    (h_rd : after.readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
      true = .ok (.fromPointer refRuntimeLayoutV2.base ptr)) :
    let lay := refLocalLayoutForTyV2 types (.rawPtr mut_ pt)
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 types) 0 16
        ⟨.memory retMemPlaceV2, lay⟩ true true st = .ok () st := by
  let lay : Miri.Interpreter.LocalLayout :=
    ⟨tyIdFor types (.rawPtr mut_ pt), refThinPtrLayoutDataV2⟩
  have h_lay_d : (refLocalLayoutForTyV2 types (.rawPtr mut_ pt)).layout =
      refThinPtrLayoutDataV2 :=
    refLocalLayoutForTyV2_rawPtr_sized types mut_ pt h_uns
  have h_lay_eq :
      refLocalLayoutForTyV2 types (.rawPtr mut_ pt) = lay := by
    dsimp only [lay, refLocalLayoutForTyV2] at h_lay_d
    dsimp only [lay, refLocalLayoutForTyV2]
    rw [h_lay_d]
  rw [h_lay_eq]
  let place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
    ⟨.memory retMemPlaceV2, lay⟩
  let sc := Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base ptr
  let imm : Miri.Interpreter.Immediate Miri.Memory.Provenance := .scalar sc
  have h_toOp : Miri.Interpreter.placeToOp
      (refBasePlaceProjectionHooksV2 types).place 0 place st =
      .ok ⟨.indirect retMemPlaceV2, lay⟩ st := rfl
  have h_ri_raw := readImmediate_retPlace_8_cfg_v2 types mut_ pt ptr st after
    (refAccessConfigV2 types) rfl rfl h_find h_sz h_rd
  have h_rt_acc : (refAccessConfigV2 types).runtime = refRuntimeLayoutV2 := rfl
  have h_ri : (refValHooksV2 types).readImmediate 0 place .rawPointer st =
      .ok ⟨imm, lay⟩ st := by
    rw [refValHooksV2_readImmediate]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_toOp]
    dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
      refValidityMemoryEnvV2,
      get, getThe, MonadStateOf.get, EStateM.get,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [show refValidityMemoryEnv.memory st = st.machine.memory from rfl,
      show refValidityMemoryEnv.hooks st = ⟨st.machine, none⟩ from rfl,
      h_rt_acc, h_ri_raw]
    cases st with | mk sk mc => cases mc with | mk _ _ _ _ _ _ _ _ => rfl
  have h_cls : (refValHooksV2 types).classify 0 lay.ty st =
      .ok (.rawPointer (tyIdFor types pt) true) st := by
    rw [refValHooksV2_classify]
    dsimp only [lay]
    rw [h_tid]
    dsimp only
    rw [h_uns]
    rfl
  have h_vis :
      Miri.Interpreter.ValidityVisitor.visit (refValHooksV2 types) 0 16
          (refInitSessV2 true) place st =
        .ok { refInitSessV2 true with dataBytes := some singleDataRange64V2 }
          st := by
    rw [Miri.Interpreter.ValidityVisitor.visit.eq_2]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_cls]
    change (EStateM.bind (EStateM.bind
      ((refValHooksV2 types).readImmediate 0 place .rawPointer) _) _ st) = _
    dsimp only [EStateM.bind]
    rw [h_ri]
    rfl
  have h_next :
      ({ refInitSessV2 true with dataBytes := some singleDataRange64V2 } :
          Miri.Interpreter.ValidityVisitor.Session
            Miri.Memory.Provenance).refTracking.bind
          Miri.Memory.Validity.RefTracking.next = none := rfl
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok (refValHooksV2_typeName types 0 lay.ty st)]
  rw [refValHooksV2_withGhostValidation, ite_true_eq]
  refine eStateM_apply_bind _ _
    { refInitSessV2 true with dataBytes := some singleDataRange64V2 } st st ?_ ?_
  · rw [refValHooksV2_toOp, eStateM_bind_ok h_toOp]
    dsimp only
    rw [ite_true_eq]
    have hs :
        (⟨⟨"", Array.mk []⟩, ⟨true, false⟩, none, some .empty, some .empty⟩ :
          Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance) =
          refInitSessV2 true := rfl
    rw [hs, eStateM_bind_ok h_vis]
    rfl
  rw [ite_true_eq, eStateM_loop_forIn_eq st]
  dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]
  rw [h_next]
  dsimp only
  rw [eStateM_bind_pure_fn]
  dsimp only
  rw [eStateM_loop_forIn_eq st, ite_false_eq]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_pure_fn]
  dsimp only
  rw [eStateM_bind_pure]
  rfl

private theorem allocId_beq_refl_v2 (a : Miri.Memory.AllocId) :
    (a == a) = true :=
  beq_self_eq_true a

theorem allocId_find_filter_push_v2 {V : Type}
    (xs : Array (Miri.Memory.AllocId × V)) (k : Miri.Memory.AllocId) (v : V) :
    ((xs.filter (fun row => row.1 != k)).push (k, v)).find?
        (fun row => row.1 == k) =
      some (k, v) := by
  rw [← Array.find?_toList, Array.toList_push, Array.toList_filter]
  induction xs.toList with
  | nil =>
    dsimp only [List.filter, List.nil_append, List.find?]
    rw [allocId_beq_refl_v2 k]
  | cons r rs ih =>
    dsimp only [List.filter]
    cases h_neq : (r.1 != k) with
    | false =>
      simp only
      exact ih
    | true =>
      have h_eq : (r.1 == k) = false := by
        cases h_b : (r.1 == k) with
        | false => rfl
        | true =>
          dsimp only [bne] at h_neq
          rw [h_b] at h_neq
          cases h_neq
      simp only [List.cons_append, List.find?, h_eq]
      exact ih

theorem copyRuntimePlace_thinPtr_ret_v2 (rp : RefProg)
    (mut_ : Trusted.MirAst.Mutability) (pt : MirTy)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance) (st : RefMiriState)
    (rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
    (h_uns : refIsUnsizedTyV2 pt = false)
    (h_tid : resolveTy rp.types (tyIdFor rp.types (.rawPtr mut_ pt)) =
      some (.rawPtr mut_ pt))
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_raw : Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawRet)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩))
    (h_last : (st.machine.memory.live.filter
        (fun row => row.1 != retAllocIdV2)).push
      (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) = st.machine.memory.live)
    (h_dr : st.machine.dataRace = none) :
    let lay := refLocalLayoutForTyV2 rp.types (.rawPtr mut_ pt)
    let imm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base ptr)
    ∃ after mem',
      mem' = { st.machine.memory with
        live := (st.machine.memory.live.filter
          (fun row => row.1 != retAllocIdV2)).push
            (retAllocIdV2, ⟨.stack, after⟩) } ∧
      Miri.Interpreter.copyRuntimePlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place
        (refExecCfgV2 rp).copy 0 ⟨.immediate imm, lay⟩
        ⟨.memory retMemPlaceV2, lay⟩ true st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      after.byteSize = Miri.ABI.Size.ofBytes 8 ∧
      after.readScalar refRuntimeLayoutV2.base
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
        true = .ok (.fromPointer refRuntimeLayoutV2.base ptr) := by
  intro lay imm
  let ⟨after, mem', h_mem', h_wm, h_asz, h_rd⟩ :=
    writeMemory_thinPtr_ret_v2 rp.types mut_ pt ptr st rawRet
      h_uns h_raw h_find h_last h_dr
  let st' : RefMiriState :=
    { st with machine := { st.machine with memory := mem' } }
  have h_find' : st'.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, after⟩) := by
    dsimp only [st']
    rw [h_mem']
    exact allocId_find_filter_push_v2 st.machine.memory.live
      retAllocIdV2 ⟨.stack, after⟩
  have h_val := rawPtr_validate_mem_8_v2 rp.types mut_ pt ptr st' after
    h_uns h_tid h_find' h_asz h_rd
  have h_pad : (refExecCfgV2 rp).copy.hasPadding lay = .ok false := by
    dsimp only [refExecCfgV2, Miri.Interpreter.ExecutionMachine.withValidation,
      Miri.Interpreter.TypedMachineBindings.bindValidation,
      refExecutionConfigV2, refPlaceCopyHooksV2, refHasPaddingV2, lay]
    rw [refLocalLayoutForTyV2_rawPtr_sized rp.types mut_ pt h_uns]
    rfl
  have h_tpd :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.takePendingMoveDeinit st = .ok false st := by
    dsimp only [Miri.Interpreter.ExecutionMachine.projectionHooks,
      Miri.Interpreter.PlaceMachine.takePendingMoveDeinit]
    cases st with
    | mk sk mc =>
      cases mc with
      | mk m b d t r a u pmd =>
        dsimp only at h_pmd; subst h_pmd; rfl
  have h_rr : (refExecCfgV2 rp).copy.readRaw 0 ⟨.immediate imm, lay⟩ st =
      .ok (.immediate ⟨imm, Miri.Interpreter.localMemoryLayout lay⟩) st := by
    cases st with
    | mk sk mc => cases mc with | mk _ _ _ _ _ _ _ _ => rfl
  have h_sz : lay.layout.isSized = true := by
    dsimp only [lay]
    rw [refLocalLayoutForTyV2_rawPtr_sized rp.types mut_ pt h_uns]
    rfl
  have h_sz_eq : (lay.layout.size != lay.layout.size) = false := bne_self_eq_false _
  have h_ty_eq : (lay.ty != lay.ty) = false := bne_self_eq_false _
  have h_compat : (refExecCfgV2 rp).copy.compatible lay lay = .ok true := by
    dsimp only [refExecCfgV2, Miri.Interpreter.ExecutionMachine.withValidation,
      Miri.Interpreter.TypedMachineBindings.bindValidation,
      refExecutionConfigV2, refPlaceCopyHooksV2]
    rw [beq_self_eq_true]
  have h_wpv :
      Miri.Interpreter.writePlaceImmediateNoValidate
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place 0 imm ⟨.memory retMemPlaceV2, lay⟩ st =
        .ok () st' := by
    dsimp only [Miri.Interpreter.writePlaceImmediateNoValidate,
      Miri.Interpreter.asMplaceOrMutableLocal,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_sz]
    exact h_wm
  have h_cpnv :
      Miri.Interpreter.copyRuntimePlaceNoValidate
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place
          (refExecCfgV2 rp).copy 0 ⟨.immediate imm, lay⟩
          ⟨.memory retMemPlaceV2, lay⟩ true st = .ok () st' := by
    dsimp only [Miri.Interpreter.copyRuntimePlaceNoValidate,
      bind, Bind.bind, pure, Pure.pure]
    rw [h_compat, Miri.Interpreter.placeLift_ok]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure_fn]
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    rw [h_pad, Miri.Interpreter.placeLift_ok]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure_fn]
    rw [eStateM_bind_ok h_tpd, ite_false_eq, eStateM_bind_ok h_rr]
    simp only [h_sz, h_sz_eq, Bool.not_true, Bool.false_or,
      Bool.false_eq_true, ite_false]
    simp only [ite_true]
    exact h_wpv
  refine ⟨after, mem', h_mem', ?_, h_asz, h_rd⟩
  dsimp only [Miri.Interpreter.copyRuntimePlace, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_cpnv,
    eStateM_bind_ok (refProjPlace_enforceValidity_v2 rp 0 lay st')]
  simp only [h_ty_eq, Bool.false_eq_true, ite_false, ite_true]
  rw [refProjPlace_validate_v2]
  exact h_val

noncomputable def alloc2IdV2 : Miri.Memory.AllocId :=
  ⟨2, by decide⟩

noncomputable def alloc3IdV2 : Miri.Memory.AllocId :=
  ⟨3, by decide⟩

theorem m_bind_ok {ε σ α β : Type} {x : EStateM ε σ α}
    {f : α → EStateM ε σ β} {a : α} {s s₁ : σ} (h : x s = .ok a s₁) :
    (Bind.bind x f) s = f a s₁ := by
  dsimp only [Bind.bind, EStateM.bind]; rw [h]

theorem mh_apply_bind {K U α β : Type}
    (x : Miri.Interpreter.MachineHooks.M K U α)
    (f : α → Miri.Interpreter.MachineHooks.M K U β)
    (a : α) (s s₁ : Miri.Interpreter.MachineHooks.State K U)
    (h : x s = .ok a s₁)
    {out : EStateM.Result Miri.Interpreter.StepError
      (Miri.Interpreter.MachineHooks.State K U) β}
    (hf : f a s₁ = out) :
    (Bind.bind x f) s = out := by
  dsimp only [Bind.bind, EStateM.bind]; rw [h]; exact hf

theorem mh_if_false_apply {K U α : Type} {c : Bool}
    (h_c : c = false) (t e : Miri.Interpreter.MachineHooks.M K U α)
    (st : Miri.Interpreter.MachineHooks.State K U)
    {out : EStateM.Result Miri.Interpreter.StepError
      (Miri.Interpreter.MachineHooks.State K U) α}
    (he : e st = out) :
    (if c = true then t else e) st = out := by
  rw [h_c]; simp only [Bool.false_eq_true, ite_false]; exact he

theorem eStateM_if_false_apply {ε σ α : Type} {c : Bool}
    (h_c : c = false) (t e : EStateM ε σ α) (s : σ)
    {out : EStateM.Result ε σ α} (he : e s = out) :
    (if c = true then t else e) s = out := by
  rw [h_c]; simp only [Bool.false_eq_true, ite_false]; exact he

theorem ite_pair_error_eq_ok {α β γ : Type} (c : Bool) (a : α) (e : β)
    (x : α × Except β γ) (a' : α) (g : γ)
    (h : (if c = true then (a, Except.error e) else x) = (a', Except.ok g)) :
    x = (a', Except.ok g) := by
  cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h
  · exact h
  · injection h with _ h2; cases h2

theorem reserveAllocId_live_dead_v2 (mem0 mem1 : RefMiriMem)
    (aid : Miri.Memory.AllocId)
    (h_res : mem0.reserveAllocId = (mem1, .ok aid)) :
    mem1.live = mem0.live ∧ mem1.dead = mem0.dead := by
  dsimp only [Miri.Memory.MemoryState.reserveAllocId, Id.run,
    bind, Bind.bind, pure, Pure.pure] at h_res
  have h1 := ite_pair_error_eq_ok _ _ _ _ _ _ h_res
  have h2 := ite_pair_error_eq_ok _ _ _ _ _ _ h1
  cases h_al : Miri.Memory.AllocId.ofUInt64 mem0.nextAllocId with
  | none => rw [h_al] at h2; cases h2
  | some id =>
    rw [h_al] at h2
    have h3 := ite_pair_error_eq_ok _ _ _ _ _ _ h2
    cases h_sw : mem0.sourceAllocIdWorldActive <;>
      rw [h_sw] at h3 <;>
      simp only [Bool.false_eq_true, ite_false, ite_true] at h3 <;>
      injection h3 with h_m1 _ <;>
      rw [← h_m1] <;> exact ⟨rfl, rfl⟩

theorem ite_not_eq_false {α : Sort u} {P : Prop} [Decidable P] (t e : α)
    (h : ¬ P) : (if P then t else e) = e := by
  simp only [h, ite_false]

theorem list_forIn_noIndirect_cleanup_v2 (xs : List RefLocalState)
    (st : RefMiriState)
    (dealloc : Miri.Memory.Pointer (Option Miri.Memory.Provenance) →
      Miri.Interpreter.MachineHooks.M Unit RefUser Unit)
    (h_no : ∀ s, s ∈ xs →
      match s.value with | .live (.indirect _) => False | _ => True) :
    forIn (m := Miri.Interpreter.MachineHooks.M Unit RefUser) xs PUnit.unit
        (fun slot (_ : PUnit) =>
          match slot.value with
          | .live (.indirect place) =>
            Bind.bind (dealloc place.ptr)
              (fun _ => pure (ForInStep.yield PUnit.unit))
          | _ => pure (ForInStep.yield PUnit.unit)) st =
      .ok PUnit.unit st := by
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    have hs : match s.value with | .live (.indirect _) => False | _ => True :=
      h_no s (List.Mem.head rest)
    have hrest : ∀ r, r ∈ rest →
        match r.value with | .live (.indirect _) => False | _ => True :=
      fun r hr => h_no r (List.Mem.tail s hr)
    rw [List.forIn_cons]
    cases h_v : s.value with
    | dead =>
      dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
      exact ih hrest
    | live op =>
      cases op with
      | immediate _ =>
        dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
        exact ih hrest
      | indirect p =>
        rw [h_v] at hs
        exact False.elim hs

theorem cleanup_noIndirect_v2 (types : List MirTy)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (st : RefMiriState)
    (h_rc : frame.returnContinuation = .stop true)
    (h_va : frame.vaList = Array.empty)
    (h_no : ∀ s, s ∈ frame.locals.toList →
      match s.value with | .live (.indirect _) => False | _ => True) :
    Miri.Interpreter.CallMachine.cleanup
        { refLifecycle types with storage := refStorageHooksV2 types }
        0 false frame st = .ok .normal st := by
  have h_va_for :
      forIn (m := Miri.Interpreter.MachineHooks.M Unit RefUser) frame.vaList
          PUnit.unit (fun arg (_ : PUnit) =>
            Bind.bind
              ((refStorageHooksV2 types).deallocateStack arg.mplace.ptr)
              (fun _ => pure (ForInStep.yield PUnit.unit))) st =
        .ok PUnit.unit st := by
    rw [h_va]; rfl
  have h_loc_for := list_forIn_noIndirect_cleanup_v2 frame.locals.toList st
    (refStorageHooksV2 types).deallocateStack h_no
  dsimp only [Miri.Interpreter.CallMachine.cleanup]
  rw [h_rc]
  dsimp only
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [← Array.forIn_toList]
  refine mh_apply_bind _ _ _ _ _ h_loc_for ?_
  refine mh_apply_bind _ _ _ _ _ h_va_for ?_
  rfl

theorem return_thinPtr_2local_v2 (rp : RefProg) (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (stmts0 : Array Miri.MIR.Statement) (mut_ : Trusted.MirAst.Mutability)
    (pt : MirTy) (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
    (retSlot : RefLocalState) (argSlot : RefLocalState)
    (h_uns : refIsUnsizedTyV2 pt = false)
    (h_tid : resolveTy rp.types (tyIdFor rp.types (.rawPtr mut_ pt)) =
      some (.rawPtr mut_ pt))
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_rc : frame.returnContinuation = .stop true)
    (h_va : frame.vaList = Array.empty)
    (h_locs : frame.locals = Array.mk [retSlot, argSlot])
    (h_s0 : retSlot =
      ⟨.live (.immediate (.scalar (.fromPointer refRuntimeLayoutV2.base ptr))),
       some (refLocalLayoutForTyV2 rp.types (.rawPtr mut_ pt))⟩)
    (h_s1 : match argSlot.value with | .live (.indirect _) => False | _ => True)
    (h_rp : frame.returnPlace = .memory ⟨retMemPlaceV2,
      refLocalLayoutForTyV2 rp.types (.rawPtr mut_ pt)⟩)
    (h_loc : frame.location = .mir ⟨0, 1⟩)
    (h_bt : st.machine.borrowTracker = none)
    (h_thr : st.machine.threads = Miri.Concurrency.ThreadManager.initial true)
    (h_fdr : frame.extra.dataRace = none)
    (h_ctrl : st.machine.user.control = refInitControl)
    (h_dr : st.machine.dataRace = none)
    (h_bb0 : frame.body.basicBlocks[0]? = some {
      statements := stmts0
      terminator := { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
      cleanup := false })
    (h_st1 : stmts0[1]? = none)
    (h_raw : Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawRet)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩))
    (h_last : (st.machine.memory.live.filter
        (fun row => row.1 != retAllocIdV2)).push
      (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) = st.machine.memory.live) :
    ∃ after mem',
      mem' = { st.machine.memory with
        live := (st.machine.memory.live.filter
          (fun row => row.1 != retAllocIdV2)).push
            (retAllocIdV2, ⟨.stack, after⟩) } ∧
      Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
          refLimitsV2 0 st =
        ({ st with
            stack := ⟨Array.empty⟩
            machine := { st.machine with
              memory := mem'
              user := { st.machine.user with
                control := advanceRefControl refInitControl } } }, .ok true) ∧
      after.byteSize = Miri.ABI.Size.ofBytes 8 ∧
      after.readScalar refRuntimeLayoutV2.base
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
        true = .ok (.fromPointer refRuntimeLayoutV2.base ptr) := by
  let stMid : RefMiriState := { st with
    machine := { st.machine with
      user := { st.machine.user with
        control := advanceRefControl refInitControl } } }
  have h_bt_ok := beforeTerminator_initCtrl_v2 rp st h_ctrl h_thr
  have h_stMid_find : stMid.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) := h_find
  have h_stMid_last : (stMid.machine.memory.live.filter
      (fun row => row.1 != retAllocIdV2)).push
      (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) = stMid.machine.memory.live := h_last
  let stMidE : RefMiriState := { stMid with stack := ⟨Array.empty⟩ }
  have h_empty_find : stMidE.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) := h_stMid_find
  have h_empty_last : (stMidE.machine.memory.live.filter
      (fun row => row.1 != retAllocIdV2)).push
      (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) = stMidE.machine.memory.live := h_stMid_last
  let ⟨after, mem', h_mem', h_copy, h_asz, h_rd⟩ :=
    copyRuntimePlace_thinPtr_ret_v2 rp mut_ pt ptr stMidE rawRet
      h_uns h_tid h_pmd h_raw h_empty_find h_empty_last h_dr
  have h_get0 : frame.getLocal 0 =
      .ok ⟨.live (.immediate (.scalar (.fromPointer refRuntimeLayoutV2.base ptr))),
        some (refLocalLayoutForTyV2 rp.types (.rawPtr mut_ pt))⟩ := by
    dsimp only [Miri.Interpreter.Frame.getLocal]
    rw [h_locs, h_s0]
    rfl
  have h_no : ∀ s, s ∈ frame.locals.toList →
      match s.value with | .live (.indirect _) => False | _ => True := by
    intro s hs
    rw [h_locs] at hs
    cases hs with
    | head => rw [h_s0]; exact True.intro
    | tail _ hs1 =>
      cases hs1 with
      | head => exact h_s1
      | tail _ hnil => cases hnil
  have h_clean := cleanup_noIndirect_v2 rp.types frame
    { stMid with stack := ⟨Array.empty⟩,
                 machine := { stMid.machine with memory := mem' } }
    h_rc h_va h_no
  have h_term := returnFromCurrentFrame_imm_single_v2 rp stMid
    (.scalar (.fromPointer refRuntimeLayoutV2.base ptr)) (.rawPtr mut_ pt)
    ⟨retMemPlaceV2, refLocalLayoutForTyV2 rp.types (.rawPtr mut_ pt)⟩
    frame stmts0 mem' rfl h_fr h_rc h_rp h_loc h_bt h_thr h_fdr h_bb0
    h_get0 h_clean h_copy
  have h_step := execStep_term_ok rp st stMid
    { stMid with stack := ⟨Array.empty⟩,
                 machine := { stMid.machine with memory := mem' } }
    frame 0 1 {
      statements := stmts0
      terminator := { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
      cleanup := false }
    h_pmd h_fr h_loc h_bb0 h_st1 h_bt_ok h_term
  let stEnd : RefMiriState :=
    { stMid with stack := ⟨Array.empty⟩,
                 machine := { stMid.machine with memory := mem' } }
  have h_res :
      ({ stEnd with
          machine := { stEnd.machine with pendingMoveDeinit := false } } :
        RefMiriState) =
        { st with
            stack := ⟨Array.empty⟩
            machine := { st.machine with
              memory := mem'
              user := { st.machine.user with
                control := advanceRefControl refInitControl } } } := by
    cases st with
    | mk sk mc =>
      cases mc with
      | mk m b d t r a u pmd =>
        dsimp only at h_pmd
        subst h_pmd
        rfl
  rw [h_res] at h_step
  exact ⟨after, mem', h_mem', h_step, h_asz, h_rd⟩

private theorem refMaxByteProvAllocIdV2_map_none (raw : List UInt8) :
    refMaxByteProvAllocIdV2
      (raw.map (fun b => Trusted.MirSemantics.AllocByte.init b none)) = 0 := by
  induction raw with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem refByteProvHasIdV2_map_none (id : Trusted.MirAst.AllocId)
    (raw : List UInt8) :
    refByteProvHasIdV2 id
      (raw.map (fun b => Trusted.MirSemantics.AllocByte.init b none)) =
      false := by
  induction raw with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem refInit_1alloc_thinPtr_2local_v2 (types : List MirTy)
    (retMut argMut : Trusted.MirAst.Mutability) (retPt argPt : MirTy)
    (alloc2 : Trusted.MirSemantics.Allocation) (raw : List UInt8)
    (off : UInt64)
    (h_live : alloc2.live = true)
    (h_id : alloc2.allocId = 2)
    (h_al : alloc2.alignLog2 ≤ 29)
    (h_bytes : alloc2.bytes = raw.map (fun b => Trusted.MirSemantics.AllocByte.init b none))
    (h_sz : raw.length < Nat.pow 2 64)
    (h_uns_ret : refIsUnsizedTyV2 retPt = false) :
    let cm : CallerMemory := ⟨[alloc2]⟩
    ∃ ma2 rawRet,
      AllocByteSliceRel raw alloc2 ma2 ∧
      Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
        (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawRet ∧
      refInitCallerMemoryV2 types cm (.rawPtr retMut retPt) =
        .ok (
          ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
              nextAllocId := 3
              live := (Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩),
                (retAllocIdV2, ⟨.stack, rawRet.withExtra
                  (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                    (Miri.ABI.Size.ofBytes 8))⟩)]) }
            ).setIssuedIds (Array.mk [alloc2IdV2, retAllocIdV2]),
          ⟨retMemPlaceV2, refLocalLayoutForTyV2 types (.rawPtr retMut retPt)⟩) ∧
      refRefsValidInMiriListV2
        (({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
            nextAllocId := 3
            live := (Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩),
              (retAllocIdV2, ⟨.stack, rawRet.withExtra
                (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                  (Miri.ABI.Size.ofBytes 8))⟩)]) }
          ).setIssuedIds (Array.mk [alloc2IdV2, retAllocIdV2]))
        [.rawPtr argMut argPt] [.ptr ⟨some 2, off, .isize⟩] = true := by
  intro cm
  let ⟨ma2, h_ma2, h_rel⟩ :=
    refAllocToMiriV2_plainInit_spec alloc2 raw h_live h_bytes h_al h_sz
  let ⟨rawRet, h_raw, _, _, _, _, _, _, _, _, _, _⟩ :=
    refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT 8 rfl rfl
  have h_lay_d : (refLocalLayoutForTyV2 types (.rawPtr retMut retPt)).layout =
      refThinPtrLayoutDataV2 :=
    refLocalLayoutForTyV2_rawPtr_sized types retMut retPt h_uns_ret
  have h_sz8 : (refLocalLayoutForTyV2 types (.rawPtr retMut retPt)).layout.size =
      Miri.ABI.Size.ofBytes 8 := by rw [h_lay_d]; rfl
  have h_al8 : (refLocalLayoutForTyV2 types (.rawPtr retMut retPt)).layout.align.abi =
      Miri.ABI.Align.EIGHT := by rw [h_lay_d]; rfl
  have h_ins :
      refInsertCallerAllocsV2 (Miri.Memory.MemoryState.empty : RefMiriMem)
          Array.empty [alloc2] =
        .ok ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
          live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩)] },
          Array.mk [alloc2IdV2]) := by
    dsimp only [refInsertCallerAllocsV2]
    rw [h_id, h_live]
    have h_a2 : refExactAllocIdV2 2 = some alloc2IdV2 := rfl
    rw [h_a2]
    dsimp only
    rw [h_ma2]
    rfl
  refine ⟨ma2, rawRet, h_rel, h_raw, ?_, ?_⟩
  · dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2, Bool.not_true,
      ite_false]
    rw [h_sz8, h_al8, h_raw]
    dsimp only
    rw [h_ins]
    dsimp only [cm, refAllocBytesHaveProvIdV2, refMaxAllocBytesProvIdV2,
      refHasAllocIdV2, refMaxAllocIdV2]
    have h_bp1 : refByteProvHasIdV2 1 alloc2.bytes = false := by
      rw [h_bytes]; exact refByteProvHasIdV2_map_none 1 raw
    have h_bm : refMaxByteProvAllocIdV2 alloc2.bytes = 0 := by
      rw [h_bytes]; exact refMaxByteProvAllocIdV2_map_none raw
    simp only [h_id, h_bp1, h_bm]
    rfl
  · rfl

private theorem refInitCallerMemoryV2_withArgs_eq
    (types : List MirTy) (cm : CallerMemory) (retTy : MirTy)
    (paramTys : List MirTy) (args : List Val) (mem0 : RefMiriMem)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (h_icm : refInitCallerMemoryV2 types cm retTy = .ok (mem0, retPlace))
    (h_refs : refRefsValidInMiriListV2 mem0 paramTys args = true)
    (h_disj : refSpansPairwiseDisjointV2
      (refAccessSpansListV2 paramTys args) = true)
    (h_extra_max : Nat.ble (refMaxValListAllocIdV2 args)
      (Nat.max (refMaxAllocIdV2 cm.allocations)
        (refMaxAllocBytesProvIdV2 cm.allocations)) = true)
    (h_extra_one : refValListHasAllocIdV2 1 args = false) :
    refInitCallerMemoryV2 types cm retTy
      (fun memCaller =>
        refRefsValidInMiriListV2 memCaller paramTys args &&
          refSpansPairwiseDisjointV2 (refAccessSpansListV2 paramTys args))
      (refMaxValListAllocIdV2 args) (refValListHasAllocIdV2 1 args) =
      .ok (mem0, retPlace) := by
  dsimp only [refInitCallerMemoryV2] at h_icm
  dsimp only [refInitCallerMemoryV2]
  cases h_fit : refOwnLayoutFitsU64V2 retTy with
  | false =>
    rw [h_fit] at h_icm
    simp only [Bool.not_false, ite_true] at h_icm
    cases h_icm
  | true =>
    simp only [h_fit, Bool.not_true, Bool.false_eq_true, ite_false] at h_icm
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases h_try : Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
        (refLocalLayoutForTyV2 types retTy).layout.size
        (refLocalLayoutForTyV2 types retTy).layout.align.abi .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) with
    | error _ => rw [h_try] at h_icm; cases h_icm
    | ok rawRet =>
      rw [h_try] at h_icm
      dsimp only at h_icm; dsimp only
      cases h_ins : refInsertCallerAllocsV2 Miri.Memory.MemoryState.empty
          Array.empty cm.allocations with
      | error _ => rw [h_ins] at h_icm; cases h_icm
      | ok p1 =>
        rw [h_ins] at h_icm
        dsimp only at h_icm; dsimp only
        have h_max_le : refMaxValListAllocIdV2 args ≤
            Nat.max (refMaxAllocIdV2 cm.allocations)
              (refMaxAllocBytesProvIdV2 cm.allocations) :=
          Nat.le_of_ble_eq_true h_extra_max
        have h_max_eq : Nat.max (Nat.max (refMaxAllocIdV2 cm.allocations)
              (refMaxAllocBytesProvIdV2 cm.allocations))
              (refMaxValListAllocIdV2 args) =
            Nat.max (refMaxAllocIdV2 cm.allocations)
              (refMaxAllocBytesProvIdV2 cm.allocations) :=
          Nat.max_eq_left h_max_le
        have h_max0 : Nat.max (Nat.max (refMaxAllocIdV2 cm.allocations)
              (refMaxAllocBytesProvIdV2 cm.allocations)) 0 =
            Nat.max (refMaxAllocIdV2 cm.allocations)
              (refMaxAllocBytesProvIdV2 cm.allocations) := Nat.max_zero _
        have h_one_eq : (refHasAllocIdV2 1 cm.allocations ||
              refAllocBytesHaveProvIdV2 1 cm.allocations ||
              refValListHasAllocIdV2 1 args) =
            (refHasAllocIdV2 1 cm.allocations ||
              refAllocBytesHaveProvIdV2 1 cm.allocations) := by
          rw [h_extra_one]; exact Bool.or_false _
        have h_one0 : (refHasAllocIdV2 1 cm.allocations ||
              refAllocBytesHaveProvIdV2 1 cm.allocations || false) =
            (refHasAllocIdV2 1 cm.allocations ||
              refAllocBytesHaveProvIdV2 1 cm.allocations) := Bool.or_false _
        rw [h_max0, h_one0] at h_icm
        rw [h_max_eq, h_one_eq]
        cases h_b1 : (refHasAllocIdV2 1 cm.allocations ||
            refAllocBytesHaveProvIdV2 1 cm.allocations) with
        | false =>
          rw [h_b1] at h_icm
          simp only [Bool.false_eq_true, ite_false] at h_icm
          simp only [Bool.false_eq_true, ite_false]
          have h_ex1 : refExactAllocIdV2 1 =
              some ⟨1, by decide⟩ := rfl
          rw [h_ex1] at h_icm; rw [h_ex1]
          dsimp only at h_icm; dsimp only
          cases h_nx : !Nat.beq (UInt64.ofNat (Nat.max 2
                (Nat.max (refMaxAllocIdV2 cm.allocations)
                  (refMaxAllocBytesProvIdV2 cm.allocations) + 1))).toNat
              (Nat.max 2 (Nat.max (refMaxAllocIdV2 cm.allocations)
                (refMaxAllocBytesProvIdV2 cm.allocations) + 1)) with
          | true =>
            rw [h_nx] at h_icm; simp only [ite_true] at h_icm; cases h_icm
          | false =>
            rw [h_nx] at h_icm
            simp only [Bool.false_eq_true, ite_false] at h_icm
            simp only [Bool.false_eq_true, ite_false]
            injection h_icm with h_pair
            have h_m0 : ({ p1.1 with
                nextAllocId := UInt64.ofNat (Nat.max 2
                  (Nat.max (refMaxAllocIdV2 cm.allocations)
                    (refMaxAllocBytesProvIdV2 cm.allocations) + 1))
                live := p1.1.live.push (⟨1, by decide⟩, ⟨.stack,
                  rawRet.withExtra (Miri.TreeBorrows.BorrowTree.new
                    Miri.Memory.BorTag.one
                    (refLocalLayoutForTyV2 types retTy).layout.size)⟩)
              }).setIssuedIds (p1.2.push ⟨1, by decide⟩) = mem0 :=
              congrArg Prod.fst h_pair
            have h_live : mem0.live = p1.1.live.push (⟨1, by decide⟩,
                ⟨.stack, rawRet.withExtra (Miri.TreeBorrows.BorrowTree.new
                  Miri.Memory.BorTag.one
                  (refLocalLayoutForTyV2 types retTy).layout.size)⟩) := by
              rw [← h_m0]; rfl
            have h_eq_c := (refRefsValidInMiriListV2_push_spec p1.1 mem0
              (⟨1, by decide⟩, ⟨.stack, rawRet.withExtra
                (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                  (refLocalLayoutForTyV2 types retTy).layout.size)⟩)
              h_live paramTys args).1 h_extra_one
            have h_c_true :
                refRefsValidInMiriListV2 p1.1 paramTys args = true := by
              rw [← h_eq_c]; exact h_refs
            simp only [h_c_true, h_disj, Bool.and_self, Bool.not_true,
              Bool.false_eq_true, ite_false]
            exact congrArg Except.ok h_pair
        | true =>
          rw [h_b1] at h_icm
          simp only [ite_true] at h_icm
          simp only [ite_true]
          cases h_ex : refExactAllocIdV2 (Nat.max (refMaxAllocIdV2 cm.allocations)
              (refMaxAllocBytesProvIdV2 cm.allocations) + 1) with
          | none => rw [h_ex] at h_icm; cases h_icm
          | some retId =>
            rw [h_ex] at h_icm
            dsimp only at h_icm; dsimp only
            cases h_nx : !Nat.beq (UInt64.ofNat
                  (Nat.max (refMaxAllocIdV2 cm.allocations)
                    (refMaxAllocBytesProvIdV2 cm.allocations) + 2)).toNat
                (Nat.max (refMaxAllocIdV2 cm.allocations)
                  (refMaxAllocBytesProvIdV2 cm.allocations) + 2) with
            | true =>
              rw [h_nx] at h_icm; simp only [ite_true] at h_icm; cases h_icm
            | false =>
              rw [h_nx] at h_icm
              simp only [Bool.false_eq_true, ite_false] at h_icm
              simp only [Bool.false_eq_true, ite_false]
              injection h_icm with h_pair
              have h_m0 : ({ p1.1 with
                  nextAllocId := UInt64.ofNat
                    (Nat.max (refMaxAllocIdV2 cm.allocations)
                      (refMaxAllocBytesProvIdV2 cm.allocations) + 2)
                  live := p1.1.live.push (retId, ⟨.stack, rawRet.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      (refLocalLayoutForTyV2 types retTy).layout.size)⟩)
                }).setIssuedIds (p1.2.push retId) = mem0 :=
                congrArg Prod.fst h_pair
              have h_live : mem0.live = p1.1.live.push (retId, ⟨.stack,
                  rawRet.withExtra (Miri.TreeBorrows.BorrowTree.new
                    Miri.Memory.BorTag.one
                    (refLocalLayoutForTyV2 types retTy).layout.size)⟩) := by
                rw [← h_m0]; rfl
              have h_ret_val := refExactAllocIdV2_toNat h_ex
              have h_fr_args :
                  refValListHasAllocIdV2 retId.value.toNat args = false := by
                rw [h_ret_val]
                exact refValListHasAllocIdV2_false_of_gt _ args
                  (Nat.lt_succ_of_le h_max_le)
              have h_eq_c := (refRefsValidInMiriListV2_push_spec p1.1 mem0
                (retId, ⟨.stack, rawRet.withExtra
                  (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                    (refLocalLayoutForTyV2 types retTy).layout.size)⟩)
                h_live paramTys args).1 h_fr_args
              have h_c_true :
                  refRefsValidInMiriListV2 p1.1 paramTys args = true := by
                rw [← h_eq_c]; exact h_refs
              simp only [h_c_true, h_disj, Bool.and_self, Bool.not_true,
                Bool.false_eq_true, ite_false]
              exact congrArg Except.ok h_pair

theorem initRefStateV2_ok_v2 (rp : RefProg) (q : Query) (ms : Nat)
    (rbody : RefBody) (localTys : List MirTy) (retTy : MirTy)
    (mem0 mem1 : RefMiriMem)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (rlocals : List RefLocalState)
    (h_w : rp.pointerWidthBits = 64) (h_v : rp.mirProfileVersion = 2)
    (h_cm : refValidCallerMemoryV2 q.callerMem = true)
    (h_b : Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId = some rbody)
    (h_lt : decodeLocalTys rp.types rbody.locals = some localTys)
    (h_chk :
      (rbody.basicBlocks.isEmpty ||
        !Nat.blt rbody.argumentCount localTys.length ||
        !refStorageAnnotationsInBounds rbody ||
        !refDiscriminantTypesValid localTys rbody ||
        !refCastTypesValid rp.types localTys rbody ||
        !localTys.all refIsSupportedLocalTyV2 ||
        !localTys.all refTyLayoutFitsU64V2) = false)
    (h_arg :
      checkRefArgsMatchV2 q.args ((localTys.drop 1).take rbody.argumentCount) =
        true)
    (h_r0 : Trusted.MirSemantics.getElem? localTys 0 = some retTy)
    (h_icm : refInitCallerMemoryV2 rp.types q.callerMem retTy = .ok (mem0, retPlace))
    (h_refs :
      refRefsValidInMiriListV2 mem0 ((localTys.drop 1).take rbody.argumentCount)
        q.args = true)
    (h_disj :
      refSpansPairwiseDisjointV2
        (refAccessSpansListV2 ((localTys.drop 1).take rbody.argumentCount) q.args) =
        true)
    (h_locs :
      initRefLocalsLoopV2 rp.types rbody q.args mem0 0 localTys =
        .ok (rlocals, mem1))
    (h_args_u64 : refValListAllocIdsFitU64V2 q.args = true := by rfl)
    (h_extra_max : Nat.ble (refMaxValListAllocIdV2 q.args)
      (Nat.max (refMaxAllocIdV2 q.callerMem.allocations)
        (refMaxAllocBytesProvIdV2 q.callerMem.allocations)) = true := by rfl)
    (h_extra_one : refValListHasAllocIdV2 1 q.args = false := by rfl) :
    initRefStateV2 rp q ms =
      .ok {
        miri := mkRefMiriState
          (mkRefMiriFrameV2 rp.types rp.entryDefId rbody 0 0 rlocals retPlace)
          mem1 refInitControl q.callerMem
        retTy := retTy, retPlace := retPlace
        stepsExecuted := 0, maxSteps := ms } := by
  dsimp only [initRefStateV2]
  simp only [h_w, h_v, Nat.beq, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ite_false]
  simp only [h_cm, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [h_b]
  dsimp only
  rw [h_lt]
  dsimp only
  simp only [h_chk, Bool.false_eq_true, ite_false]
  simp only [h_arg, h_args_u64, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, ite_false]
  rw [h_r0]
  dsimp only
  rw [refInitCallerMemoryV2_withArgs_eq rp.types q.callerMem retTy
    ((localTys.drop 1).take rbody.argumentCount) q.args mem0 retPlace
    h_icm h_refs h_disj h_extra_max h_extra_one]
  dsimp only
  rw [h_locs]

theorem mulWithOverflow_isize_0_1_v2 :
    Miri.Interpreter.IntegerOps.binary .MulWithOverflow
        ⟨miriScalar .isize 0,
          ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩
        ⟨miriScalar .isize 1,
          ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩ =
      .ok (.withOverflow (miriScalar .isize 0) false) := by
  have h_tf0 : Miri.Memory.ScalarInt.truncateFromInt (BitVec.ofInt 128 0).toInt
      (toMiriSize .isize) =
      match Miri.Memory.ScalarInt.truncateFromUInt
          (BitVec.ofInt 128 (BitVec.ofInt 128 0).toInt)
          (toMiriSize .isize) with
      | .ok (sc, _) =>
        match (toMiriSize .isize).signExtend sc.data with
        | .ok decoded => .ok (sc, decoded != (BitVec.ofInt 128 0).toInt)
        | .error e => .error (.sizeError e)
      | .error e => .error e := by
    let x := (BitVec.ofInt 128 0).toInt
    have h_rng : (decide (x < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (x ≥ HPow.hPow (2 : Int) 127)) = false := by
      dsimp only [x]; simp only [bitVec_ofInt_eq]; decide
    dsimp only [Miri.Memory.ScalarInt.truncateFromInt, bind, Bind.bind,
      Except.bind, pure, Pure.pure, Except.pure]
    change (if (decide (x < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (x ≥ HPow.hPow (2 : Int) 127)) = true then _ else _) = _
    rw [h_rng]; simp only [Bool.false_eq_true, ite_false]; rfl
  have h_d0 : Miri.Interpreter.IntegerOps.decode ⟨miriScalar .isize 0,
      ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩ = .ok 0 := by
    change Miri.Interpreter.IntegerOps.decode
      (miriIntValue ⟨.isize, true, 0⟩) = _
    rw [integerOps_decode_eq]; rfl
  have h_d1 : Miri.Interpreter.IntegerOps.decode ⟨miriScalar .isize 1,
      ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩ = .ok 1 := by
    change Miri.Interpreter.IntegerOps.decode
      (miriIntValue ⟨.isize, true, 1⟩) = _
    rw [integerOps_decode_eq]; rfl
  have h_ib : Miri.Interpreter.IntegerOps.binary .MulWithOverflow
      ⟨miriScalar .isize 0,
        ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩
      ⟨miriScalar .isize 1,
        ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩ =
      match Miri.Memory.ScalarInt.truncateFromInt (BitVec.ofInt 128 0).toInt
          (toMiriSize .isize) with
      | .ok (value, lossy) =>
        .ok (.withOverflow value
          ((decide ((0 : Int) < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide ((0 : Int) ≥ HPow.hPow (2 : Int) 127)) || lossy))
      | .error e => .error (.scalar e) := by
    dsimp only [Miri.Interpreter.IntegerOps.binary, bind, Bind.bind,
      Except.bind, pure, Pure.pure, Except.pure]
    rw [h_d0, h_d1]; rfl
  rw [h_ib, h_tf0, bitVec_ofInt_eq, bitVec_ofInt_eq,
    truncateFromUInt_eq_miriScalar .isize (bvOfInt 128 (bvOfInt 128 0).toInt)]
  dsimp only
  rw [miriScalar_data, size_signExtend_eq]
  dsimp only
  rw [show miriScalar .isize (bvOfInt 128 (bvOfInt 128 0).toInt) =
      miriScalar .isize 0 from by decide]
  rw [show ((decide ((0 : Int) < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide ((0 : Int) ≥ HPow.hPow (2 : Int) 127)) ||
      (signExtendBits .isize (truncateBits .isize
        (bvOfInt 128 (bvOfInt 128 0).toInt)) != (bvOfInt 128 0).toInt)) =
      false from by decide]

theorem pointer_wrappingSignedOffset_zero_v2
    (p : Miri.Memory.Pointer (Option Miri.Memory.Provenance)) :
    p.wrappingSignedOffset 0 refPointerArithmetic = .ok p := by
  cases p with | mk off prov => cases off with | mk b =>
    dsimp only [Miri.Memory.Pointer.wrappingSignedOffset,
      Miri.Memory.Pointer.wrappingOffset, Miri.ABI.Size.ofBytes]
    rw [show (0 : Int64).toUInt64 = 0 from rfl, UInt64.add_zero]
    have h_lt : b.toNat < Nat.pow 2 64 := UInt64.toNat_lt b
    have h_ext :
        (BitVec.zeroExtend 128
          (BitVec.extractLsb 63 0 (BitVec.ofNat 128 b.toNat))).toNat =
          b.toNat := by
      have h_e :
          BitVec.extractLsb 63 0 (BitVec.ofNat 128 b.toNat) =
            BitVec.ofNat 64 b.toNat := by
        simp only [BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide)),
          Nat.shiftRight_zero]
      rw [h_e, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt,
        Nat.mod_eq_of_lt (Nat.lt_trans h_lt (by decide))]
    have h_tr : refPointerArithmetic.truncateToTargetUsize b = .ok b := by
      change (if (BitVec.zeroExtend 128
          (BitVec.extractLsb 63 0 (BitVec.ofNat 128 b.toNat))).toNat <
            Nat.pow 2 64
        then Except.ok (UInt64.ofNat (BitVec.zeroExtend 128
          (BitVec.extractLsb 63 0 (BitVec.ofNat 128 b.toNat))).toNat)
        else Except.error Miri.Memory.PointerError.unsignedConversionOverflow) =
        .ok b
      rw [h_ext]; simp only [h_lt, ite_true]; rw [UInt64.ofNat_toNat]
    change Except.bind (refPointerArithmetic.truncateToTargetUsize b) _ = _
    rw [h_tr]; rfl

theorem binOp_offset_zero_u8_v2 (rp : RefProg) (mut_ : Trusted.MirAst.Mutability)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance) (m0 : RefMiriState)
    (h_pt1 : resolveTy rp.types (tyIdFor rp.types (.rawPtr mut_ u8Ty)) =
      some (.rawPtr mut_ u8Ty))
    (h_isize : resolveTy rp.types (tyIdFor rp.types (.int .isize true)) =
      some (.int .isize true)) :
    let ptrLay := refLocalLayoutForTyV2 rp.types (.rawPtr mut_ u8Ty)
    let isizeLay := refLocalLayoutForTyV2 rp.types (.int .isize true)
    let ptrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base ptr)
    (Miri.Interpreter.ExecutionMachine.rvalueHooks
        (refExecCfgV2 rp) refLimitsV2).binaryOp 0 .Offset
      ⟨ptrImm, ptrLay⟩
      ⟨.scalar (.fromScalarInt (miriScalar .isize 0)), isizeLay⟩ m0 =
      .ok ⟨ptrImm, ptrLay⟩ m0 := by
  intro ptrLay isizeLay ptrImm
  have h_cls_ptr : (refScalarLeavesV2 rp.types).classify 0 ptrLay.ty m0 =
      .ok .pointer m0 := by
    dsimp only [refScalarLeavesV2, ptrLay, refLocalLayoutForTyV2]; rw [h_pt1]
  have h_cls_is : (refScalarLeavesV2 rp.types).classify 0 isizeLay.ty m0 =
      .ok (.integer (toMiriIntKind .isize true)) m0 := by
    dsimp only [refScalarLeavesV2, isizeLay, refLocalLayoutForTyV2]; rw [h_isize]
  have h_ovl : (refScalarLeavesV2 rp.types).overflowLayout 0 isizeLay m0 =
      .ok (refLocalLayoutForTyV2 rp.types
        (.tuple [.int .isize true, .bool])) m0 := by
    dsimp only [refScalarLeavesV2, isizeLay, refLocalLayoutForTyV2]
    rw [h_isize]
  have h_mul : Miri.Interpreter.ExecutionScalar.integerBinary
      (refScalarLeavesV2 rp.types) 0 .MulWithOverflow
      (⟨.scalar (.fromScalarInt (miriScalar .isize 0)), isizeLay⟩ :
        Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance)
      (⟨.scalar (.fromScalarInt (miriScalar .isize 1)), isizeLay⟩ :
        Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance) m0 =
      .ok ⟨.scalarPair (.fromScalarInt (miriScalar .isize 0))
        (.fromBool false),
        refLocalLayoutForTyV2 rp.types (.tuple [.int .isize true, .bool])⟩
        m0 := by
    dsimp only [Miri.Interpreter.ExecutionScalar.integerBinary,
      Miri.Interpreter.RvalueM, bind, Bind.bind, pure, Pure.pure]
    refine eStateM_apply_bind _ _ _ _ _ h_cls_is ?_
    dsimp only
    refine eStateM_apply_bind _ _ _ _ _ h_cls_is ?_
    dsimp only
    refine eStateM_apply_bind _ _
      ({ scalar := miriScalar .isize 0,
         type := ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩ } :
        Miri.Interpreter.IntegerValue)
      _ _ rfl ?_
    refine eStateM_apply_bind _ _
      ({ scalar := miriScalar .isize 1,
         type := ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩ } :
        Miri.Interpreter.IntegerValue)
      _ _ rfl ?_
    rw [show (Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.Shl ||
        Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.ShlUnchecked ||
        Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.Shr ||
        Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.ShrUnchecked) =
        false from rfl,
      show (isizeLay.ty == isizeLay.ty) = true from beq_self_eq_true _]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    refine eStateM_apply_bind _ _ (.withOverflow (miriScalar .isize 0) false)
      _ _ (by dsimp only [Except.mapError]; rw [mulWithOverflow_isize_0_1_v2]; rfl) ?_
    dsimp only [Miri.Interpreter.ExecutionScalar.finish,
      Miri.Interpreter.RvalueM, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rw [h_ovl]
  have h_ptlay : (refExecCfgV2 rp).pointeeLayout 0 ptrLay.ty m0 =
      .ok (refLocalLayoutForTyV2 rp.types u8Ty) m0 := by
    change (match resolveTy rp.types (tyIdFor rp.types (.rawPtr mut_ u8Ty)) with
      | some (.rawPtr _ pt) | some (.ref _ pt) =>
        match refCheckedLocalLayoutForTyV2 rp.types pt with
        | some lay => EStateM.Result.ok lay m0
        | none =>
          EStateM.Result.error
            (Miri.Interpreter.StepError.unsupported
              "pointee layout exceeds UInt64") m0
      | _ =>
        EStateM.Result.error
          (Miri.Interpreter.StepError.invalidProgram
            "pointeeLayout on non-pointer type") m0) = _
    rw [h_pt1]
    rfl
  have h_wrp : ptr.withOptionalProvenance.wrappingSignedOffset 0
      (refExecCfgV2 rp).arithmetic = .ok ptr.withOptionalProvenance :=
    pointer_wrappingSignedOffset_zero_v2 ptr.withOptionalProvenance
  have h_fmp : Miri.Memory.Scalar.fromMaybePointer
      (refExecCfgV2 rp).access.runtime.base ptr.withOptionalProvenance =
      .ok (.fromPointer refRuntimeLayoutV2.base ptr) := by
    cases ptr; rfl
  dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks]
  rw [refStepCfgV2_eq]
  dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
    Miri.Interpreter.ExecutionScalar.hooks,
    Miri.Interpreter.ScalarOps.binary, Miri.Interpreter.MachineHooks.M,
    bind, Bind.bind, pure, Pure.pure]
  rw [show (refExecCfgV2 rp).scalar = refScalarLeavesV2 rp.types from rfl]
  refine eStateM_apply_bind _ _ _ _ _ h_cls_ptr ?_; dsimp only
  refine eStateM_apply_bind _ _ _ _ _ h_cls_is ?_; dsimp only
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
  refine eStateM_apply_bind _ _
    (Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base ptr) _ _ rfl ?_
  refine eStateM_apply_bind _ _ ptr.withOptionalProvenance _ _ (by
    dsimp only [Except.mapError]
    have h_base : (refExecCfgV2 rp).access.runtime.base =
        refRuntimeLayoutV2.base := rfl
    rw [h_base, show Miri.Memory.Scalar.toPointer
        (Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base ptr)
        refRuntimeLayoutV2.base =
        .ok ptr.withOptionalProvenance from by cases ptr; rfl]
    rfl) ?_
  refine eStateM_apply_bind _ _ (refLocalLayoutForTyV2 rp.types u8Ty)
    _ _ h_ptlay ?_
  rw [show ((refLocalLayoutForTyV2 rp.types u8Ty).layout.isSized &&
      decide ((refLocalLayoutForTyV2 rp.types u8Ty).layout.size.bytes.toNat <
        Nat.pow 2 63)) = true from rfl]
  simp only [ite_true]
  rw [show (refLocalLayoutForTyV2 rp.types u8Ty).layout.size.bytes.toNat =
      1 from rfl,
    show Int.ofNat 1 = (1 : Int) from rfl,
    show isizeLay.layout.size = Miri.ABI.Size.ofBytes 8 from rfl]
  rw [show Miri.Memory.Scalar.fromInt (Prov := Miri.Memory.Provenance)
      1 (Miri.ABI.Size.ofBytes 8) =
    .ok (.fromScalarInt (miriScalar .isize 1)) from by decide]
  dsimp only [Except.mapError]
  refine eStateM_apply_bind _ _
    (Miri.Memory.Scalar.fromScalarInt (miriScalar .isize 1)) _ _ rfl ?_
  rw [show ({ ty := isizeLay.ty, layout := isizeLay.layout } :
      Miri.Interpreter.LocalLayout) = isizeLay from rfl]
  refine eStateM_apply_bind _ _ _ _ _ h_mul ?_
  dsimp only [Miri.Interpreter.Immediate.toScalarPair]
  refine eStateM_apply_bind _ _
    (Miri.Memory.Scalar.fromScalarInt (miriScalar .isize 0),
     Miri.Memory.Scalar.fromBool false) _ _ rfl ?_
  rw [show (Miri.Memory.Scalar.fromBool false :
      Miri.Memory.Scalar Miri.Memory.Provenance).toBool = .ok false from rfl]
  dsimp only [Except.mapError]
  refine eStateM_apply_bind _ _ false _ _ rfl ?_
  simp only [Bool.false_eq_true, ite_false]
  rw [show (refExecCfgV2 rp).arithmetic.pointerSize =
    Miri.ABI.Size.ofBytes 8 from rfl]
  rw [show (Miri.Memory.Scalar.fromScalarInt (miriScalar .isize 0) :
      Miri.Memory.Scalar Miri.Memory.Provenance).toTargetIsize
      (Miri.ABI.Size.ofBytes 8) = .ok 0 from rfl,
    show isizeLay.layout.backendRepr.isSigned = .ok true from rfl]
  dsimp only [Except.mapError]
  refine eStateM_apply_bind _ _ (0 : Int64) _ _ rfl ?_
  refine eStateM_apply_bind _ _ true _ _ rfl ?_
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false,
    bne_self_eq_false]
  refine eStateM_apply_bind _ _ ptr.withOptionalProvenance m0 m0
    (by simp only [h_wrp]; rfl) ?_
  refine eStateM_apply_bind _ _
    (Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base ptr) m0 m0
    (by simp only [h_fmp]; rfl) ?_
  rfl

theorem genericCopy_zero_v2 (types : List MirTy) (deinit : Bool)
    (st : RefMiriState)
    (src dst : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (h_src : src.provenance = none ∨
      ∃ id t, src.provenance = some (.concrete id t)) :
    Miri.Interpreter.GlobalMemoryCopyMachine.genericCopy
      { refAccessConfigV2 types with deinitMovedPlace := deinit }
      (fun _ => refEmptyAddressState)
      refPointerArithmetic src dst Miri.ABI.Size.ZERO 1 true st =
      .ok () st := by
  cases h_src with
  | inl h =>
    cases src with | mk off p =>
      dsimp only at h; subst h
      cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd =>
        cases deinit <;> rfl
  | inr h =>
    let ⟨id, t, h_p⟩ := h
    cases src with | mk off p =>
      dsimp only at h_p; subst h_p
      cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd =>
        cases deinit <;> rfl

theorem typedCopy_zero_v2 (rp : RefProg) (st : RefMiriState)
    (src dst : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (h_src_sz : src.layout.layout.size = Miri.ABI.Size.ZERO)
    (h_dst_sz : dst.layout.layout.size = Miri.ABI.Size.ZERO)
    (h_dst_sized : dst.layout.layout.isSized = true)
    (h_src_mis : src.mplace.misaligned = none)
    (h_dst_mis : dst.mplace.misaligned = none)
    (h_src_prov : src.mplace.ptr.provenance = none ∨
      ∃ id t, src.mplace.ptr.provenance = some (.concrete id t)) :
    (refExecCfgV2 rp).copy.memoryCopy 0 src dst st = .ok () st := by
  dsimp only [refExecCfgV2, Miri.Interpreter.ExecutionMachine.withValidation,
    Miri.Interpreter.TypedMachineBindings.bindValidation,
    Miri.Interpreter.GlobalMemoryCopyMachine.typedCopy]
  rw [show (refExecutionConfigV2 rp).compiler.debugAssertions = false from rfl]
  rw [m_bind_ok (by
    rw [Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta.eq_def]
    rw [h_dst_sized]
    rfl)]
  dsimp only
  simp only [Bool.false_eq_true, ite_false]
  rw [h_src_sz, h_dst_sz]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
  refine mh_apply_bind _ _ () st st
    (genericCopy_zero_v2 rp.types true st src.mplace.ptr
      dst.mplace.ptr h_src_prov) ?_
  rw [h_src_mis, h_dst_mis]
  rfl

theorem refValHooksV2_opsemInhabited_unit (types : List MirTy) (c : Choice)
    (tyId : TyId) (st : RefMiriState)
    (h_ty : resolveTy types tyId = some .unit) :
    (refValHooksV2 types).opsemInhabited c tyId st = .ok true st := by
  have h_eq : (refValHooksV2 types).opsemInhabited c tyId st =
      match resolveTy types tyId with
      | some ty => .ok (!(refLayoutDataForTyV2 ty).uninhabited) st
      | none => .error (.invalidProgram "unknown TyId in opsemInhabited") st :=
    rfl
  rw [h_eq, h_ty]
  rfl

theorem refValHooksV2_sizeAndAlign_unit (types : List MirTy)
    (mp : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (st : RefMiriState) (h_sz : mp.layout.layout.size = Miri.ABI.Size.ZERO)
    (h_sized : mp.layout.layout.isSized = true) :
    (refValHooksV2 types).sizeAndAlign 0 mp st =
      .ok (some (Miri.ABI.Size.ZERO, mp.layout.layout.align.abi)) st := by
  have h_sa : (refValHooksV2 types).sizeAndAlign 0 mp st =
      Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta
        (refDynamicLayoutHooksV2 types) 0 8 mp.mplace.metadata mp.layout st :=
    rfl
  rw [h_sa, Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta]
  dsimp only [pure, Pure.pure]
  rw [h_sized, h_sz]; rfl

theorem refValHooksV2_beginPadding_zero (types : List MirTy)
    (mp : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (st : RefMiriState) :
    (refValHooksV2 types).beginPadding 0 mp Miri.ABI.Size.ZERO st =
      .ok none st :=
  Miri.Interpreter.ValidityMemory.beginPadding_zero
    (refValidityMemoryEnvV2 types) mp st rfl

theorem validatePlace_unit_forced_v2 (types : List MirTy) (st : RefMiriState)
    (place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (mp : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (h_toOp : Miri.Interpreter.placeToOp
      (refBasePlaceProjectionHooksV2 types).place 0 place st =
      .ok ⟨.indirect mp.mplace, mp.layout⟩ st)
    (h_force : Miri.Interpreter.forceAllocation
      (refBasePlaceProjectionHooksV2 types).place 0 place st = .ok mp st)
    (h_ty : resolveTy types place.layout.ty = some .unit)
    (h_fld : place.layout.layout.fields =
      .Arbitrary (Array.mk []) (Array.mk []))
    (h_var : place.layout.layout.variants = .Single 0)
    (h_sz : mp.layout.layout.size = Miri.ABI.Size.ZERO)
    (h_sized : mp.layout.layout.isSized = true) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 types)
        0 16 place true true st = .ok () st := by
  have h_cls : (refValHooksV2 types).classify 0 place.layout.ty st =
      .ok (.aggregate false false false) st := by
    rw [refValHooksV2_classify, h_ty]
  have h_vis :
      Miri.Interpreter.ValidityVisitor.visit (refValHooksV2 types) 0 16
        (refInitSessV2 true) place st = .ok (refInitSessV2 true) st :=
    Miri.Interpreter.ValidityVisitor.visit_fieldless
      (refValHooksV2 types) 0 15 (refInitSessV2 true) place st 0 h_cls
      (refValHooksV2_opsemInhabited_unit types 0 place.layout.ty st h_ty)
      h_fld h_var rfl (refValHooksV2_debugAssertions types)
  have h_rst := Miri.Interpreter.ValidityVisitor.resetPadding_forced_zero
    (refValHooksV2 types) 0 (refInitSessV2 true) place mp st rfl h_force h_sz
    (refValHooksV2_sizeAndAlign_unit types mp st h_sz h_sized)
    (refValHooksV2_beginPadding_zero types mp st)
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok (refValHooksV2_typeName types 0 place.layout.ty st),
    refValHooksV2_withGhostValidation, ite_true_eq]
  have hs :
      (⟨⟨"", Array.mk []⟩, ⟨true, false⟩, none, some .empty, some .empty⟩ :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance) =
        refInitSessV2 true := rfl
  refine eStateM_apply_bind _ _ (refInitSessV2 true) st st ?_ ?_
  · rw [refValHooksV2_toOp, eStateM_bind_ok h_toOp]
    dsimp only
    rw [ite_true_eq, hs, eStateM_bind_ok h_vis, eStateM_bind_ok h_rst]
    rfl
  rw [ite_true_eq, eStateM_loop_forIn_eq st]
  dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]
  rw [show (refInitSessV2 true).refTracking.bind
      Miri.Memory.Validity.RefTracking.next = none from rfl]
  dsimp only
  rw [eStateM_bind_pure_fn]
  dsimp only
  rw [eStateM_loop_forIn_eq st, ite_false_eq]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_pure_fn]
  dsimp only
  rw [eStateM_bind_pure]
  rfl

theorem copyRuntimePlace_unit_v2 (rp : RefProg) (st st' : RefMiriState)
    (src : Miri.Interpreter.OpTy Miri.Memory.Provenance)
    (srcMp dstMp : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (dest : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (allowTrans : Bool)
    (h_src_op : src.op = .indirect srcMp.mplace)
    (h_src_lay : src.layout = refLocalLayoutForTyV2 rp.types .unit)
    (h_dst_lay : dest.layout = refLocalLayoutForTyV2 rp.types .unit)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_src_mis : srcMp.mplace.misaligned = none)
    (h_dst_mis : dstMp.mplace.misaligned = none)
    (h_dst_sz : dstMp.layout.layout.size = Miri.ABI.Size.ZERO)
    (h_src_prov : srcMp.mplace.ptr.provenance = none ∨
      ∃ id t, srcMp.mplace.ptr.provenance = some (.concrete id t))
    (h_force : Miri.Interpreter.forceAllocation
      (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place 0 dest st = .ok dstMp st')
    (h_toOp' : Miri.Interpreter.placeToOp
      (refBasePlaceProjectionHooksV2 rp.types).place 0 dest st' =
      .ok ⟨.indirect dstMp.mplace, dstMp.layout⟩ st')
    (h_force' : Miri.Interpreter.forceAllocation
      (refBasePlaceProjectionHooksV2 rp.types).place 0 dest st' =
      .ok dstMp st')
    (h_ty_u : resolveTy rp.types (tyIdFor rp.types .unit) = some .unit)
    (h_dst_sized : dstMp.layout.layout.isSized = true) :
    Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0 src dest allowTrans st = .ok () st' := by
  let unitLay := refLocalLayoutForTyV2 rp.types .unit
  have h_val := validatePlace_unit_forced_v2 rp.types st' dest dstMp
    h_toOp' h_force' (by rw [h_dst_lay]; exact h_ty_u)
    (by rw [h_dst_lay]; rfl) (by rw [h_dst_lay]; rfl) h_dst_sz h_dst_sized
  have h_compat : (refExecCfgV2 rp).copy.compatible unitLay unitLay = .ok true := by
    change Except.ok (unitLay.ty == unitLay.ty) = Except.ok true
    rw [beq_self_eq_true]
  dsimp only [Miri.Interpreter.copyRuntimePlace,
    Miri.Interpreter.copyRuntimePlaceNoValidate,
    Miri.Interpreter.MachineHooks.M, Miri.Interpreter.PlaceM]
  rw [h_src_lay, h_dst_lay]
  rw [show (refExecCfgV2 rp).copy.compatible unitLay unitLay = .ok true from
    h_compat, Miri.Interpreter.placeLift_ok]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_pure_fn]
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
  rw [show (refExecCfgV2 rp).copy.hasPadding unitLay = .ok true from rfl,
    Miri.Interpreter.placeLift_ok]
  dsimp only [pure, Pure.pure]
  rw [eStateM_bind_pure_fn]
  have h_tpd :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.takePendingMoveDeinit st = .ok false st := by
    cases st with | mk sk mc => cases mc with | mk _ _ _ _ _ _ _ pmd =>
      dsimp only at h_pmd; subst h_pmd; rfl
  dsimp only [EStateM.bind, EStateM.pure]
  rw [h_tpd]
  dsimp only [EStateM.bind, EStateM.pure]
  simp only [ite_true]
  cases src with | mk s_op s_lay =>
    dsimp only at h_src_op h_src_lay; subst h_src_op
    dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_force]
    dsimp only
    rw [typedCopy_zero_v2 rp st'
      ⟨srcMp.mplace, refLocalLayoutForTyV2 rp.types .unit⟩ dstMp
      rfl h_dst_sz h_dst_sized h_src_mis h_dst_mis h_src_prov]
    dsimp only [EStateM.pure]
    simp only [Bool.false_eq_true, ite_false]
    dsimp only [EStateM.pure]
    rw [refProjPlace_enforceValidity_v2 rp 0 unitLay st']
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
    rw [refProjPlace_validate_v2]
    exact h_val

theorem allocateStack_unit_v2 (rp : RefProg) (st : RefMiriState)
    (aid : Miri.Memory.AllocId)
    (rawZst : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
    (h_try : Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
      Miri.ABI.Size.ZERO Miri.ABI.Align.ONE .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawZst)
    (h_bt : st.machine.borrowTracker = none)
    (h_dr : st.machine.dataRace = none)
    (h_avail : st.machine.memory.idSupplyExhausted = false)
    (h_nz : st.machine.memory.nextAllocId ≠ 0)
    (h_src_av : st.machine.memory.sourceAllocIdWorldActive = true →
      st.machine.memory.sourceAllocIdExhausted = false)
    (h_src_nz : st.machine.memory.sourceAllocIdWorldActive = true →
      st.machine.memory.sourceAllocIdNext ≠ 0)
    (h_iss : ∀ id, id ∈ st.machine.memory.issuedIds →
      id.value.toNat < st.machine.memory.nextAllocId.toNat)
    (h_lv : ∀ row, row ∈ st.machine.memory.live →
      row.1.value.toNat < st.machine.memory.nextAllocId.toNat)
    (h_gl : ∀ row, row ∈ st.machine.memory.globals →
      row.allocId.value.toNat < st.machine.memory.nextAllocId.toNat)
    (h_dd : ∀ row, row ∈ st.machine.memory.dead →
      row.allocId.value.toNat < st.machine.memory.nextAllocId.toNat)
    (h_aid : (⟨st.machine.memory.nextAllocId, h_nz⟩ : Miri.Memory.AllocId) =
      aid) :
    let unitLay := refLocalLayoutForTyV2 rp.types .unit
    ∃ mem1,
      st.machine.memory.reserveAllocId = (mem1, .ok aid) ∧
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.allocateStack 0 unitLay st =
        .ok ⟨⟨⟨Miri.ABI.Size.ZERO, some (.concrete aid Miri.Memory.BorTag.one)⟩,
            .none, none⟩, unitLay⟩
          { st with
            machine := { st.machine with
              memory := { mem1 with
                live := mem1.live.push
                  (aid, ⟨.stack, rawZst.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      Miri.ABI.Size.ZERO)⟩) } } } := by
  intro unitLay
  let ⟨mem1, h_res_raw⟩ :=
    Miri.Memory.MemoryState.reserve_of_highWater st.machine.memory
      h_avail h_nz h_src_av h_src_nz h_iss h_lv h_gl h_dd
  have h_res : st.machine.memory.reserveAllocId = (mem1, .ok aid) := by
    rw [h_aid] at h_res_raw; exact h_res_raw
  refine ⟨mem1, h_res, ?_⟩
  let ⟨rawZst', h_ok, h_sz, _⟩ := refTryNew_spec_v2 Miri.ABI.Size.ZERO
    Miri.ABI.Align.ONE 1 rfl rfl
  rw [h_try] at h_ok; injection h_ok with h_eq; subst h_eq
  cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd =>
    dsimp only at h_bt h_dr h_res; subst h_bt h_dr
    have h_raw :
        Miri.Interpreter.PlaceMachine.allocateStackRaw refAllocationConfig
            Miri.ABI.Size.ZERO Miri.ABI.Align.ONE
            ⟨sk, { memory := m, borrowTracker := none, dataRace := none,
                   threads := t, raceAllocations := r, allocationSpans := a,
                   user := u, pendingMoveDeinit := pmd }⟩ =
          .ok ⟨Miri.ABI.Size.ZERO, some (.concrete aid Miri.Memory.BorTag.one)⟩
            ⟨sk, { memory := { mem1 with
                      live := mem1.live.push (aid, ⟨.stack, rawZst.withExtra
                        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                          Miri.ABI.Size.ZERO)⟩) },
                   borrowTracker := none, dataRace := none, threads := t,
                   raceAllocations := r, allocationSpans := a, user := u,
                   pendingMoveDeinit := pmd }⟩ := by
      dsimp only [Miri.Interpreter.PlaceMachine.allocateStackRaw]
      rw [show refAllocationConfig.nativeStorage = none from rfl,
        show refAllocationConfig.zeroedStorage =
          (fun n _ => some (Array.replicate n.bytes.toNat 0)) from rfl]
      dsimp only [bind, Bind.bind, pure, Pure.pure]
      rw [show Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
          Miri.ABI.Size.ZERO Miri.ABI.Align.ONE .Uninit
          (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawZst
        from h_try, eStateM_bind_pure_fn]
      dsimp only; rw [eStateM_bind_pure_fn]
      dsimp only [tryCatch, tryCatchThe, MonadExcept.tryCatch,
        MonadExceptOf.tryCatch, EStateM.tryCatch, EarlyReturn.runK,
        ExceptT.run, ExceptT.bind, ExceptT.pure, get, getThe,
        MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
        EStateM.bind, EStateM.pure]
      rw [h_sz, show refAllocationConfig.maximumObjectSize = refMaxSizeOfVal
        from rfl]
      simp only [show ¬ (Miri.ABI.Size.ZERO.bytes > refMaxSizeOfVal.bytes) from
        by decide, ite_false]
      dsimp only [bind, Bind.bind, pure, Pure.pure,
        EStateM.bind, EStateM.pure, EStateM.get, EStateM.set,
        EStateM.modifyGet]
      rw [h_res]; rfl
    rw [show (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place.allocateStack 0 unitLay =
        Miri.Interpreter.PlaceMachine.allocateStack refAllocationConfig unitLay
      from rfl]
    dsimp only [Miri.Interpreter.PlaceMachine.allocateStack, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [show unitLay.layout.isSized = true from rfl]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [show unitLay.layout.size = Miri.ABI.Size.ZERO from rfl,
      show unitLay.layout.align.abi = Miri.ABI.Align.ONE from rfl,
      eStateM_bind_ok h_raw]
    rfl

theorem forceAllocation_unit_local_v2 (rp : RefProg) (st : RefMiriState)
    (frame frame' : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (localId : LocalId) (aid : Miri.Memory.AllocId) (mem1 : RefMiriMem)
    (rawZst : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate .uninit), some (refLocalLayoutForTyV2 rp.types .unit)⟩)
    (h_set : frame.setLocalOperand localId
      (.indirect ⟨⟨Miri.ABI.Size.ZERO, some (.concrete aid Miri.Memory.BorTag.one)⟩,
        .none, none⟩) = .ok frame')
    (h_alloc :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.allocateStack 0
          (refLocalLayoutForTyV2 rp.types .unit) st =
        .ok ⟨⟨⟨Miri.ABI.Size.ZERO, some (.concrete aid Miri.Memory.BorTag.one)⟩,
            .none, none⟩, refLocalLayoutForTyV2 rp.types .unit⟩
          { st with
            machine := { st.machine with
              memory := { mem1 with
                live := mem1.live.push
                  (aid, ⟨.stack, rawZst.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      Miri.ABI.Size.ZERO)⟩) } } }) :
    let unitLay := refLocalLayoutForTyV2 rp.types .unit
    let mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
      ⟨⟨Miri.ABI.Size.ZERO, some (.concrete aid Miri.Memory.BorTag.one)⟩,
        .none, none⟩
    let mem2 : RefMiriMem := { mem1 with
      live := mem1.live.push (aid, ⟨.stack, rawZst.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          Miri.ABI.Size.ZERO)⟩) }
    Miri.Interpreter.forceAllocation
        (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place 0
        ⟨.local 0 localId none frame.localsIdentity, unitLay⟩ st =
      .ok ⟨mp, unitLay⟩
        { st with
          stack := ⟨Array.mk [frame']⟩
          machine := { st.machine with
            memory := mem2
            allocationSpans :=
              (st.machine.allocationSpans.filter fun e => e.1 != aid).push
                (aid, ⟨0⟩, none) } } := by
  intro unitLay mp mem2
  let st1 : RefMiriState := { st with machine := { st.machine with memory := mem2 } }
  let st2 : RefMiriState :=
    { st1 with machine := { st1.machine with
      allocationSpans :=
        (st.machine.allocationSpans.filter fun e => e.1 != aid).push
          (aid, ⟨0⟩, none) } }
  have h_cf := currentFrame_single_v2 st frame h_fr
  have h_fi := frameIndex_single_v2 (rp := rp) st frame h_fr
  have h_g_op : frame.getLocalOperand localId = .ok (.immediate .uninit) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]; rw [h_get]; rfl
  have h_dbg := refProjPlace_debugOff_v2 rp
  have h_in : (mem2.live.any fun e => e.1 == aid) = true := by
    dsimp only [mem2]; rw [Array.any_push, beq_self_eq_true, Bool.or_true]
  have h_alm :
      Miri.Interpreter.MachineHooks.afterLocalMovedToMemory localId
          ⟨mp, unitLay⟩ (refCompilerHooksV2 rp.types).localSpan st1 =
        .ok () st2 := by
    dsimp only [Miri.Interpreter.MachineHooks.afterLocalMovedToMemory, mp,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [currentFrame_single_v2 st1 frame h_fr]
    dsimp only
    rw [show (refCompilerHooksV2 rp.types).localSpan frame.body localId st1 =
        .ok ⟨0⟩ st1 from rfl]
    dsimp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      get, getThe, MonadStateOf.get, EStateM.get]
    rw [show st2.machine.memory.live.any (fun e => e.1 == aid) = true from h_in]
    simp only [h_dr]
    rfl
  have h_sf2 : Miri.Interpreter.MachineHooks.setCurrentFrame frame' st2 =
      .ok () { st2 with stack := ⟨Array.mk [frame']⟩ } := by
    dsimp only [Miri.Interpreter.MachineHooks.setCurrentFrame,
      get, getThe, MonadStateOf.get, EStateM.get, set,
      MonadStateOf.set, EStateM.set, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rw [h_fr]; rfl
  have h_pol : Miri.Interpreter.placeLayoutOfLocal
      (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place 0 localId st = .ok unitLay st := by
    dsimp only [Miri.Interpreter.placeLayoutOfLocal, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [projPlace_getFrame_eq_v2, h_cf]
    dsimp only
    rw [h_get, Miri.Interpreter.stackLift_ok]
    rfl
  have h_alm' :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.afterLocalMovedToMemory 0 localId ⟨mp, unitLay⟩
        st1 = .ok () st2 := h_alm
  have h_sf2' :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.setFrame frame' st2 =
        .ok () { st2 with stack := ⟨Array.mk [frame']⟩ } := h_sf2
  simp only [Miri.Interpreter.forceAllocation, Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff _ _ h_dbg,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    h_fi, bne_self_eq_false, Bool.false_eq_true, ite_false,
    projPlace_getFrame_eq_v2, h_cf, h_g_op, Miri.Interpreter.stackLift_ok, h_pol,
    show unitLay.layout.isSized = true from rfl, Bool.not_true]
  dsimp only [unitLay]
  rw [h_alloc]
  dsimp only
  rw [h_alm']
  dsimp only
  rw [currentFrame_single_v2 st2 frame h_fr]
  dsimp only
  rw [h_set, Miri.Interpreter.stackLift_ok]
  rw [show (pure frame' : Miri.Interpreter.MachineHooks.M Unit RefUser _) st2 =
    .ok frame' st2 from rfl]
  dsimp only
  rw [h_sf2']

theorem refCastHooks_ptrToPtr_v2 (rp : RefProg)
    (mutSrc mutDst : Trusted.MirAst.Mutability) (ptSrc ptDst : MirTy)
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (frame frame' : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (st : RefMiriState) (localId : LocalId)
    (h_uns_src : refIsUnsizedTyV2 ptSrc = false)
    (h_uns_dst : refIsUnsizedTyV2 ptDst = false)
    (h_src_tid : resolveTy rp.types (tyIdFor rp.types (.rawPtr mutSrc ptSrc)) =
      some (.rawPtr mutSrc ptSrc))
    (h_dst_tid : resolveTy rp.types (tyIdFor rp.types (.rawPtr mutDst ptDst)) =
      some (.rawPtr mutDst ptDst))
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate .uninit),
        some (refLocalLayoutForTyV2 rp.types (.rawPtr mutDst ptDst))⟩)
    (h_set : frame.setLocalOperand localId
      (.immediate (.scalar (.fromPointer refRuntimeLayoutV2.base ptr))) =
      .ok frame')
    (h_val : Miri.Interpreter.ValidityVisitor.validatePlace
      (refValHooksV2 rp.types) 0 16
      ⟨.local 0 localId none frame.localsIdentity,
        refLocalLayoutForTyV2 rp.types (.rawPtr mutDst ptDst)⟩ true true
      { st with stack := ⟨Array.mk [frame']⟩ } =
      .ok () { st with stack := ⟨Array.mk [frame']⟩ }) :
    let srcLay := refLocalLayoutForTyV2 rp.types (.rawPtr mutSrc ptSrc)
    let dstLay := refLocalLayoutForTyV2 rp.types (.rawPtr mutDst ptDst)
    let ptrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base ptr)
    (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecutionConfigV2 rp)
      refLimitsV2).cast 0 ⟨.immediate ptrImm, srcLay⟩ .PtrToPtr dstLay.ty
      ⟨.local 0 localId none frame.localsIdentity, dstLay⟩ st =
      .ok () { st with stack := ⟨Array.mk [frame']⟩ } := by
  intro srcLay dstLay ptrImm
  have h_src_d : srcLay.layout = refThinPtrLayoutDataV2 :=
    refLocalLayoutForTyV2_rawPtr_sized rp.types mutSrc ptSrc h_uns_src
  have h_dst_d : dstLay.layout = refThinPtrLayoutDataV2 :=
    refLocalLayoutForTyV2_rawPtr_sized rp.types mutDst ptDst h_uns_dst
  have h_src_eq : srcLay = ⟨srcLay.ty, refThinPtrLayoutDataV2⟩ := by
    dsimp only [srcLay, refLocalLayoutForTyV2] at h_src_d
    dsimp only [srcLay, refLocalLayoutForTyV2]
    rw [h_src_d]
  have h_tpd :
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
          refLimitsV2).takePendingMoveDeinit st = .ok false st := by
    dsimp only [Miri.Interpreter.ExecutionMachine.castHooks]
    rw [refStepCfgV2_eq]
    dsimp only [Miri.Interpreter.ExecutionCast.hooks,
      Miri.Interpreter.ExecutionMachine.projectionHooks,
      Miri.Interpreter.PlaceMachine.takePendingMoveDeinit]
    cases st with | mk sk mc => cases mc with | mk _ _ _ _ _ _ _ pmd =>
      dsimp only at h_pmd; subst h_pmd; rfl
  have h_ti_src :
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
          refLimitsV2).typeInfo 0 srcLay.ty st =
        .ok (.rawPointer (tyIdFor rp.types ptSrc)) st := by
    change (refCastLeavesV2 rp.types).typeInfo 0 srcLay.ty st = _
    dsimp only [refCastLeavesV2, srcLay, refLocalLayoutForTyV2]
    rw [h_src_tid]
  have h_ti_dst :
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
          refLimitsV2).typeInfo 0 dstLay.ty st =
        .ok (.rawPointer (tyIdFor rp.types ptDst)) st := by
    change (refCastLeavesV2 rp.types).typeInfo 0 dstLay.ty st = _
    dsimp only [refCastLeavesV2, dstLay, refLocalLayoutForTyV2]
    rw [h_dst_tid]
  have h_ev :
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
          refLimitsV2).enforceValidity 0 srcLay st = .ok true st := rfl
  have h_ri :
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
          refLimitsV2).readImmediate 0 ⟨.immediate ptrImm, srcLay⟩ st =
        .ok ⟨ptrImm, srcLay⟩ st := by
    rw [h_src_eq]
    cases st with | mk sk mc => cases mc with | mk _ _ _ _ _ _ _ pmd =>
      dsimp only at h_pmd; subst h_pmd; rfl
  have h_wr_cast :
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
          refLimitsV2).writeImmediate 0 ptrImm
          ⟨.local 0 localId none frame.localsIdentity, dstLay⟩ st =
        .ok () { st with stack := ⟨Array.mk [frame']⟩ } :=
    writeLocalImmediate_direct_v2 rp st frame localId .uninit ptrImm
      dstLay frame' h_fr h_dr (by rw [h_dst_d]; rfl) h_get h_set h_val
  dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
    Miri.Interpreter.Cast.cast, Miri.Interpreter.MachineHooks.M,
    bind, Bind.bind, pure, Pure.pure]
  rw [show Miri.Interpreter.ExecutionMachine.withValidation
      (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl]
  rw [eStateM_bind_ok h_tpd]
  rw [show ((Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
      refLimitsV2).destLayout
        ⟨Miri.Interpreter.RuntimePlaceRef.local 0 localId none
          frame.localsIdentity, dstLay⟩).ty = dstLay.ty from rfl,
    beq_self_eq_true]
  simp only [ite_true]
  rw [eStateM_bind_pure_fn]
  rw [show (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
      refLimitsV2).destLayout
        ⟨Miri.Interpreter.RuntimePlaceRef.local 0 localId none
          frame.localsIdentity, dstLay⟩ = dstLay from rfl]
  simp only [Bool.false_eq_true, ite_false]
  rw [eStateM_bind_ok h_ev, ite_true_eq, eStateM_bind_ok h_ti_src]
  dsimp only
  rw [show srcLay.layout.backendRepr = refThinPtrLayoutDataV2.backendRepr
    from congrArg Miri.ABI.LayoutData.backendRepr h_src_d]
  refine mh_if_false_apply (by decide) _ _ st ?_
  rw [eStateM_bind_ok h_ri]
  refine eStateM_apply_bind
    (Miri.Interpreter.Cast.ptrToPtr
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
        refLimitsV2) 0 ⟨ptrImm, srcLay⟩ dstLay)
    (fun result =>
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfgV2 rp)
        refLimitsV2).writeImmediate 0 result.imm
        ⟨.local 0 localId none frame.localsIdentity, dstLay⟩)
    { imm := ptrImm, layout := dstLay } st st ?_ h_wr_cast
  dsimp only [Miri.Interpreter.Cast.ptrToPtr, Miri.Interpreter.MachineHooks.M,
    bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_ti_src]
  dsimp only
  refine eStateM_if_false_apply rfl _ _ st ?_
  rw [eStateM_bind_ok h_ti_dst]
  dsimp only
  have h_sz_eq : (srcLay.layout.size == dstLay.layout.size) = true := by
    rw [h_src_d, h_dst_d]; rfl
  rw [h_sz_eq]
  simp only [ite_true]
  rfl

end Anneal.MirCorrespondence
