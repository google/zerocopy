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
import Anneal.MirCorrespondence.Codec
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.EnumEquiv
import Anneal.MirCorrespondence.MemRoundTrip
import Anneal.MirCorrespondence.RvalueStep

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

/-!
# Statement, Terminator, and `ExecutionMachine.step` Simulation
(`Anneal.MirCorrespondence.StmtTermStep`)

Proves per-statement (`Step.evalStatement`), per-terminator
(`ControlFlow.evalTerminator`), and single-step (`ExecutionMachine.step` ->
`evalRefStep_eq_base : EvalRefStepEqClaim`) equivalence between
$M_{\text{anneal}}$ (`Trusted.MirSemantics`) and real
`Miri.Interpreter.ExecutionMachine` (`Trusted.Correspondence`), together with
invariant preservation (`evalStep_step_inv`).
-/

/-! ## Section 1: List, Codec, and Step-Invariant Helpers -/

theorem getElem?_none_of_setElem?_none {α : Type} {xs : List α} {i : Nat}
    {v : α}
    (h : MirSemantics.setElem? xs i v = none) :
    MirSemantics.getElem? xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero => cases h
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_r : MirSemantics.setElem? rest j v with
      | some _ => rw [h_r] at h; cases h
      | none => exact ih h_r

theorem getElem?_some_of_setElem?_some {α : Type} {xs xs' : List α} {i : Nat}
    {v : α}
    (h : MirSemantics.setElem? xs i v = some xs') :
    ∃ x : α, MirSemantics.getElem? xs i = some x := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons x rest ih =>
    cases i with
    | zero => exact ⟨x, rfl⟩
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_r : MirSemantics.setElem? rest j v with
      | none => rw [h_r] at h; cases h
      | some _ => exact ih h_r

theorem decodeBasicBlock_inv {ts : List MirTy} {rbb : RefBasicBlock}
    {bb : BasicBlock}
    (h : decodeBasicBlock ts rbb = some bb) :
    mapOption (decodeStmt ts) rbb.statements = some bb.statements ∧
    decodeTerminator ts rbb.terminator = some bb.terminator ∧
    rbb.cleanup = bb.cleanup := by
  dsimp only [decodeBasicBlock, optMap2] at h
  cases h₁ : mapOption (decodeStmt ts) rbb.statements with
  | none => rw [h₁] at h; cases h
  | some stmts =>
    cases h₂ : decodeTerminator ts rbb.terminator with
    | none => rw [h₁, h₂] at h; cases h
    | some term =>
      rw [h₁, h₂] at h
      injection h with h_eq
      rw [← h_eq]
      exact ⟨rfl, rfl, rfl⟩

theorem decodeBody_inv {ts : List MirTy} {rbody : RefBody} {body : Body}
    (h : decodeBody ts rbody = some body) :
    rbody.argumentCount = body.argumentCount ∧
    decodeLocalTys ts rbody.locals = some body.locals ∧
    mapOption (decodeBasicBlock ts) rbody.basicBlocks = some body.basicBlocks ∧
    rbody.isUnsafe = body.isUnsafe ∧
    rbody.identity = body.identity := by
  dsimp only [decodeBody, optMap2] at h
  cases h₁ : decodeLocalTys ts rbody.locals with
  | none => rw [h₁] at h; cases h
  | some locals =>
    cases h₂ : mapOption (decodeBasicBlock ts) rbody.basicBlocks with
    | none => rw [h₁, h₂] at h; cases h
    | some bbs =>
      rw [h₁, h₂] at h
      injection h with h_eq
      rw [← h_eq]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem decodeProg_inv {rp : RefProg} {p : Program}
    (h : decodeProg rp = some p) :
    rp.entryDefId = p.entryDefId ∧
    rp.pointerWidthBits = p.pointerWidthBits ∧
    rp.mirProfileVersion = p.mirProfileVersion ∧
    rp.scope = p.scope ∧
    mapOption (decodeBody rp.types) rp.bodies = some p.bodies := by
  dsimp only [decodeProg, optMap] at h
  cases h_b : mapOption (decodeBody rp.types) rp.bodies with
  | none => rw [h_b] at h; cases h
  | some b' =>
    rw [h_b] at h
    injection h with h_eq
    rw [← h_eq]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem decodeProg_panicStrategy {rp : RefProg} {p : Program}
    (h : decodeProg rp = some p) :
    rp.panicStrategy = p.panicStrategy ∧
    rp.hasLocalPanicHandler = p.hasLocalPanicHandler := by
  dsimp only [decodeProg, optMap] at h
  cases h_b : mapOption (decodeBody rp.types) rp.bodies with
  | none => rw [h_b] at h; cases h
  | some b' =>
    rw [h_b] at h
    injection h with h_eq
    rw [← h_eq]
    exact ⟨rfl, rfl⟩

private theorem discriminantTypesValid_stmt {body : Body} {bb : BasicBlock}
    {blockIdx : BasicBlockId} {stmtIdx : Nat} {dst : Place} {rv : Rvalue}
    (h_dv : discriminantTypesValid body = true)
    (h_bb : MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (h_st : MirSemantics.getElem? bb.statements stmtIdx = some (.assign dst rv)) :
    ∀ (src : Place) (srcTy : MirTy) (ety : EnumTy) (dstTy : MirTy),
      rv = .discriminant src →
      dst.projection.isEmpty = true →
      src.projection.isEmpty = true →
      MirSemantics.getElem? body.locals src.localId = some srcTy →
      refAsEnumTy? srcTy = some ety →
      MirSemantics.getElem? body.locals dst.localId = some dstTy →
      enumAdmitted ety = true →
      dstTy = .int ety.discrWidth ety.discrSigned := by
  intro src srcTy ety dstTy h_rv h_dpe h_spe h_sty h_as h_dty h_adm
  subst h_rv
  have h_bb_ok := list_all_mirGetElem? h_dv h_bb
  have h_st_ok := list_all_mirGetElem? h_bb_ok h_st
  change
    (if (dst.projection.isEmpty && src.projection.isEmpty) = true then
      match MirSemantics.getElem? body.locals src.localId with
      | some srcTy =>
        match srcTy with
        | .enum ety =>
          match MirSemantics.getElem? body.locals dst.localId with
          | some dstTy =>
            if enumAdmitted ety then
              MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
            else true
          | none => true
        | .ordering =>
          match MirSemantics.getElem? body.locals dst.localId with
          | some dstTy => MirTy.beq dstTy (.int .i8 true)
          | none => true
        | _ => true
      | none => true
    else true) = true at h_st_ok
  rw [h_dpe, h_spe, Bool.and_self, ite_true_eq, h_sty] at h_st_ok
  cases srcTy with
  | enum _ =>
    cases h_as
    dsimp only at h_st_ok
    rw [h_dty] at h_st_ok
    change
      (if enumAdmitted ety = true then
        MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
      else true) = true at h_st_ok
    rw [h_adm, ite_true_eq] at h_st_ok
    exact MirTy.eq_of_beq h_st_ok
  | ordering =>
    cases h_as
    dsimp only at h_st_ok
    rw [h_dty] at h_st_ok
    exact MirTy.eq_of_beq h_st_ok
  | _ => cases h_as

private theorem castTypesValid_stmt {body : Body} {bb : BasicBlock}
    {blockIdx : BasicBlockId} {stmtIdx : Nat} {dst : Place} {rv : Rvalue}
    (h_cv : castTypesValid body = true)
    (h_bb : MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (h_st :
      MirSemantics.getElem? bb.statements stmtIdx = some (.assign dst rv)) :
    ∀ (opnd : Operand) (castTy dstTy : MirTy),
      rv = .cast .intToInt opnd castTy →
      dst.projection.isEmpty = true →
      MirSemantics.getElem? body.locals dst.localId = some dstTy →
      dstTy = castTy := by
  intro opnd castTy dstTy h_rv h_dpe h_dty
  subst h_rv
  have h_bb_ok := list_all_mirGetElem? h_cv h_bb
  have h_st_ok := list_all_mirGetElem? h_bb_ok h_st
  change
    (if dst.projection.isEmpty = true then
      match MirSemantics.getElem? body.locals dst.localId with
      | some dstTy => MirTy.beq dstTy castTy
      | none => true
    else true) = true at h_st_ok
  rw [h_dpe, ite_true_eq] at h_st_ok
  change
    (match MirSemantics.getElem? body.locals dst.localId with
     | some dstTy => MirTy.beq dstTy castTy
     | none => true) = true at h_st_ok
  rw [h_dty] at h_st_ok
  exact MirTy.eq_of_beq h_st_ok

theorem assignTypesValid_stmt {body : Body} {bb : BasicBlock}
    {blockIdx : BasicBlockId} {stmtIdx : Nat} {stmt : StatementKind}
    (h_av : assignTypesValid body = true)
    (h_bb : MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (h_st : MirSemantics.getElem? bb.statements stmtIdx = some stmt) :
    mirAssignStmtOk body.locals stmt = true := by
  dsimp only [assignTypesValid] at h_av
  have h_bb_ok := list_all_mirGetElem? h_av h_bb
  exact list_all_mirGetElem? h_bb_ok h_st

/-- Under `SlotsMatchTys`, replacing a local's value never deallocates:
`deallocateLocal` only acts on `.indirect` slots. -/
theorem deallocateLocal_eq_ok_of_slotsMatchTys {tys : List MirTy}
    {slots : List LocalSlot} {i : Nat} {slot : LocalSlot} {ty : MirTy}
    (amem : MemoryState)
    (h_inv : SlotsMatchTys tys slots)
    (h_ty : MirSemantics.getElem? tys i = some ty)
    (h_sl : MirSemantics.getElem? slots i = some slot) :
    deallocateLocal amem slot = .ok amem := by
  cases slot with
  | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
  | partialTuple _ =>
    exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)
  | dead => rfl
  | immediate _ => rfl

theorem evalStatement_step_inv {body : Body} {bb : BasicBlock}
    {f : FrameState} {amem : MemoryState} {callerMem : CallerMemory}
    {stmt : StatementKind} {s' : State}
    (h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (h_st : MirSemantics.getElem? bb.statements f.stmtIdx = some stmt)
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_step : evalStatement body f amem callerMem stmt = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := callerMem, mem := amem } ∧
      f'.defId = f.defId ∧
      SlotsMatchTys body.locals f'.locals ∧
      FramePcInBounds body f' := by
  have h_pc' : ∀ (locs : List LocalSlot),
      FramePcInBounds body { f with stmtIdx := f.stmtIdx + 1, locals := locs } := by
    intro locs bb' h_bb'
    rw [h_bb] at h_bb'
    injection h_bb' with h_eq
    subst h_eq
    exact mirGetElem?_lt_of_some h_st
  cases stmt with
  | nop =>
    injection h_step with h_eq
    refine ⟨{ f with stmtIdx := f.stmtIdx + 1 }, h_eq.symm, rfl, h_inv,
      h_pc' f.locals⟩
  | storageLive localId =>
    dsimp only [evalStatement] at h_step
    cases h_ty : MirSemantics.getElem? body.locals localId with
    | none => rw [h_ty] at h_step; cases h_step
    | some localTy =>
      rw [h_ty] at h_step
      dsimp only at h_step
      cases h_old : MirSemantics.getElem? f.locals localId with
      | none => rw [h_old] at h_step; cases h_step
      | some old =>
      rw [h_old] at h_step
      dsimp only at h_step
      cases h_set :
          MirSemantics.setElem? f.locals localId (liveUninitSlot localTy) with
      | none => rw [h_set] at h_step; cases h_step
      | some locals' =>
        rw [h_set] at h_step
        dsimp only at h_step
        rw [deallocateLocal_eq_ok_of_slotsMatchTys amem h_inv h_ty h_old]
          at h_step
        injection h_step with h_eq
        refine ⟨{ f with stmtIdx := f.stmtIdx + 1, locals := locals' },
          h_eq.symm, rfl,
          SlotsMatchTys.setElem? h_inv h_ty
            (slotMatchesTy_liveUninitSlot localTy) h_set,
          h_pc' locals'⟩
  | storageDead localId =>
    dsimp only [evalStatement] at h_step
    cases h0 : Nat.beq localId 0 <;> rw [h0] at h_step
    · cases h_old : MirSemantics.getElem? f.locals localId with
      | none => rw [h_old] at h_step; cases h_step
      | some old =>
      rw [h_old] at h_step
      dsimp only at h_step
      cases h_set : MirSemantics.setElem? f.locals localId .dead with
      | none => rw [h_set] at h_step; cases h_step
      | some locals' =>
        rw [h_set] at h_step
        let ⟨localTy, h_ty⟩ := getElem?_some_of_length_eq
          (SlotsMatchTys.length_eq h_inv) h_old
        dsimp only at h_step
        rw [deallocateLocal_eq_ok_of_slotsMatchTys amem h_inv h_ty h_old]
          at h_step
        injection h_step with h_eq
        refine ⟨{ f with stmtIdx := f.stmtIdx + 1, locals := locals' },
          h_eq.symm, rfl,
          SlotsMatchTys.setElem? h_inv h_ty (slot' := .dead) True.intro h_set,
          h_pc' locals'⟩
    · cases h_step
  | assign dst rvalue =>
    dsimp only [evalStatement] at h_step
    cases h_emp : dst.projection.isEmpty <;> rw [h_emp] at h_step
    · cases h_step
    · cases h_ty : MirSemantics.getElem? body.locals dst.localId with
      | none => rw [h_ty] at h_step; cases h_step
      | some dstTy =>
        rw [h_ty] at h_step
        dsimp only at h_step
        cases h_rv : evalRvalue body.locals f.locals amem dstTy rvalue with
        | error _ => rw [h_rv] at h_step; cases h_step
        | ok res =>
          rw [h_rv] at h_step
          cases res with | mk val rest =>
          cases rest with | mk localsAfterRval memAfterRval =>
          dsimp only at h_step
          cases h_wr : writePlace localsAfterRval memAfterRval dst.localId dstTy
              val with
          | error _ => rw [h_wr] at h_step; cases h_step
          | ok pair =>
            cases pair with | mk localsAfterWrite memAfterWrite =>
            rw [h_wr] at h_step
            injection h_step with h_eq
            let ⟨h_inv₁, h_m₁⟩ := evalRvalue_slotsMatchTys h_inv h_rv
            let ⟨h_inv₂, h_m₂⟩ := writePlace_slotsMatchTys h_inv₁ h_ty h_wr
            rw [h_m₂, h_m₁] at h_eq
            refine ⟨{ f with
                stmtIdx := f.stmtIdx + 1, locals := localsAfterWrite },
              h_eq.symm, rfl, h_inv₂, h_pc' localsAfterWrite⟩
  | unsupported => cases h_step

theorem evalTerminator_step_inv {body : Body} {bb : BasicBlock}
    {f : FrameState} {amem : MemoryState} {callerMem : CallerMemory}
    {ps : PanicStrategy} {lh : Bool} {s' : State}
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_step : evalTerminator body bb f amem callerMem ps lh = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := callerMem, mem := amem } ∧
      f'.defId = f.defId ∧
      SlotsMatchTys body.locals f'.locals ∧
      FramePcInBounds body f' := by
  have h_pc0 : ∀ (tgt : BasicBlockId) (locs : List LocalSlot),
      FramePcInBounds body { f with blockIdx := tgt, stmtIdx := 0, locals := locs } :=
    fun _ _ _ _ => Nat.zero_le _
  cases bb with | mk stmts term cleanup =>
  cases term with
  | goto target =>
    injection h_step with h_eq
    refine ⟨{ f with blockIdx := target, stmtIdx := 0 }, h_eq.symm, rfl, h_inv,
      h_pc0 target f.locals⟩
  | return_ =>
    dsimp only [evalTerminator] at h_step
    cases cleanup
    · cases h_sl : MirSemantics.getElem? f.locals 0 with
      | none => rw [h_sl] at h_step; cases h_step
      | some s =>
        rw [h_sl] at h_step
        cases s with
        | dead => cases h_step
        | immediate o => cases o <;> cases h_step
        | indirect _ =>
          let ⟨_, h_ty⟩ := getElem?_some_of_length_eq
            (SlotsMatchTys.length_eq h_inv) h_sl
          exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
        | partialTuple _ =>
          let ⟨_, h_ty⟩ := getElem?_some_of_length_eq
            (SlotsMatchTys.length_eq h_inv) h_sl
          exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)
    · cases h_step
  | unreachable | unwindResume | call _ _ _ _ _
  | coreCall _ _ _ _ _ | sysrootCall _ _ _ _ _ | unsupported =>
    cases h_step
  | assert cond expected msg target unwind =>
    dsimp only [evalTerminator] at h_step
    cases h_c : evalPrimitiveOperand body.locals f.locals amem cond with
    | error _ => rw [h_c] at h_step; cases h_step
    | ok res =>
      rw [h_c] at h_step
      cases res with | mk condVal rest =>
      cases rest with | mk localsAfterCond amemAfterCond =>
      let ⟨h_inv₁, h_m₁⟩ := evalPrimitiveOperand_slotsMatchTys h_inv h_c
      rw [h_m₁] at h_step
      dsimp only at h_step
      cases condVal with
      | bool b =>
        dsimp only at h_step
        cases h_b : (b == expected) with
        | true =>
          rw [h_b] at h_step
          injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_inv₁, h_pc0 target localsAfterCond⟩
        | false =>
          rw [h_b] at h_step
          dsimp only [evalAssertFailure] at h_step
          cases msg with
          | misalignedPtrDeref | nullPtrDeref | unsupported => cases h_step
          | boundsCheck | overflowNeg | divByZero | remByZero =>
            cases lh <;> cases ps <;> cases unwind <;> cases h_step
          | overflow op =>
            cases op <;>
              (first
                | (cases lh <;> cases ps <;> cases unwind <;> cases h_step)
                | cases h_step)
      | scalar _ | char _ | unit | enumVal _ _ | tuple _ | ptr _ | slicePtr _ _
      | rangeTo _ | rangeFrom _ | bytes _ | array _ | ordering _ | optionVal _ | range _ _
      | boxPtr _ _ | vec _ _ _ =>
        cases h_step
  | switchInt discr targets =>
    dsimp only [evalTerminator] at h_step
    cases h_d : evalPrimitiveOperand body.locals f.locals amem discr with
    | error _ => rw [h_d] at h_step; cases h_step
    | ok res =>
      rw [h_d] at h_step
      cases res with | mk discrVal rest =>
      cases rest with | mk localsAfterDiscr memAfterDiscr =>
      let ⟨h_inv₁, h_m₁⟩ := evalPrimitiveOperand_slotsMatchTys h_inv h_d
      rw [h_m₁] at h_step
      dsimp only at h_step
      cases discrVal with
      | scalar sv =>
        dsimp only at h_step
        cases h_sw : evalSwitchBranches sv.width sv.bits targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_inv₁, h_pc0 _ localsAfterDiscr⟩
      | bool b =>
        dsimp only at h_step
        cases h_sw : evalBoolSwitchBranches b targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_inv₁, h_pc0 _ localsAfterDiscr⟩
      | char ch =>
        dsimp only at h_step
        cases h_sw : evalCharSwitchBranches ch targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_inv₁, h_pc0 _ localsAfterDiscr⟩
      | unit | enumVal _ _ | tuple _ | array _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _
      | rangeFrom _ | range _ _ | optionVal _ | bytes _ | ordering _ =>
        dsimp only at h_step
        cases h_br : targets.branches with
        | cons _ _ => rw [h_br] at h_step; cases h_step
        | nil =>
          rw [h_br] at h_step
          injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_inv₁, h_pc0 _ localsAfterDiscr⟩

theorem evalStep_step_inv {p : Program} {c : Choice} {s s' : State}
    {f : FrameState} {body : Body}
    (hs : s.frames = [f])
    (h_body : activeFrameBody p f = some body)
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_nc : ∀ bb, MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb →
      (∀ callee args dst tgt uw, bb.terminator ≠ .call callee args dst tgt uw) ∧
      (∀ op args dst tgt uw, bb.terminator ≠ .sysrootCall op args dst tgt uw))
    (h_step : evalStep p c s = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := s.callerMem, mem := s.mem } ∧
      f'.defId = f.defId ∧
      SlotsMatchTys body.locals f'.locals ∧
      FramePcInBounds body f' := by
  unfold evalStep at h_step
  rw [hs] at h_step
  dsimp only at h_step
  rw [h_body] at h_step
  dsimp only at h_step
  cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none => rw [h_bb] at h_step; cases h_step
  | some bb =>
    rw [h_bb] at h_step
    dsimp only at h_step
    cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx with
    | none =>
      rw [h_st] at h_step
      dsimp only at h_step
      cases h_end : Nat.beq f.stmtIdx bb.statements.length with
      | false => rw [h_end] at h_step; cases h_step
      | true =>
        rw [h_end] at h_step
        cases h_bt : bb.terminator with
        | call callee args dst tgt uw =>
          exact False.elim ((h_nc bb h_bb).1 callee args dst tgt uw h_bt)
        | sysrootCall op args dst tgt uw =>
          exact False.elim ((h_nc bb h_bb).2 op args dst tgt uw h_bt)
        | return_ =>
          rw [h_bt] at h_step
          cases h_cl : bb.cleanup <;> dsimp only [evalTerminator] at h_step
          · rw [h_bt, h_cl] at h_step
            cases h0 : MirSemantics.getElem? f.locals 0 with
            | none => rw [h0] at h_step; cases h_step
            | some sl =>
              rw [h0] at h_step
              cases sl with
              | dead => cases h_step
              | immediate o => cases o <;> cases h_step
              | partialTuple _ =>
                let ⟨_, h_ty⟩ := getElem?_some_of_length_eq
                  (SlotsMatchTys.length_eq h_inv) h0
                exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h0)
              | indirect _ =>
                let ⟨_, h_ty⟩ := getElem?_some_of_length_eq
                  (SlotsMatchTys.length_eq h_inv) h0
                exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h0)
          · rw [h_bt, h_cl] at h_step; cases h_step
        | goto _ | unreachable | unwindResume | switchInt _ _
        | assert _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported =>
          rw [h_bt] at h_step
          dsimp only at h_step
          cases h_ev : evalTerminator body bb f s.mem s.callerMem
              p.panicStrategy p.hasLocalPanicHandler with
          | fault _ => rw [h_ev] at h_step; cases h_step
          | done _ => rw [h_ev] at h_step; cases h_step
          | step s₁ =>
            rw [h_ev] at h_step
            dsimp only [attachCallers] at h_step
            injection h_step with h_eq
            subst h_eq
            have h_ev' : evalTerminator body bb f s.mem s.callerMem
                p.panicStrategy p.hasLocalPanicHandler = .step s₁ := h_ev
            let ⟨f', hs₁, hdef, hinv', hpc'⟩ := evalTerminator_step_inv h_inv h_ev'
            rw [hs₁]
            exact ⟨f', rfl, hdef, hinv', hpc'⟩
    | some stmt =>
      rw [h_st] at h_step
      dsimp only at h_step
      cases h_ev : evalStatement body f s.mem s.callerMem stmt with
      | fault _ => rw [h_ev] at h_step; cases h_step
      | done _ => rw [h_ev] at h_step; cases h_step
      | step s₁ =>
        rw [h_ev] at h_step
        dsimp only [attachCallers] at h_step
        injection h_step with h_eq
        subst h_eq
        let ⟨f', hs₁, hdef, hinv', hpc'⟩ := evalStatement_step_inv h_bb h_st h_inv h_ev
        rw [hs₁]
        exact ⟨f', rfl, hdef, hinv', hpc'⟩

theorem refControlValid_nextRefControlForStep {body : Body} {f : FrameState}
    {ctrl : Miri.Interpreter.TerminatorMachine.Control Unit}
    (h : RefControlValid ctrl) :
    RefControlValid (nextRefControlForStep body f ctrl) := by
  dsimp only [nextRefControlForStep]
  cases MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none => exact h
  | some bb =>
    dsimp only
    cases MirSemantics.getElem? bb.statements f.stmtIdx with
    | some _ => exact h
    | none =>
      dsimp only
      cases Nat.beq f.stmtIdx bb.statements.length with
      | false => exact h
      | true => exact refControlValid_advance h

noncomputable def updateCacheLoop (touched : Nat → Bool) (idx : Nat) :
    List Bool → List Bool
  | [] => []
  | b :: bs => (b || touched idx) :: updateCacheLoop touched (idx + 1) bs

theorem updateCacheLoop_length (touched : Nat → Bool) (idx : Nat) :
    ∀ cache : List Bool, (updateCacheLoop touched idx cache).length = cache.length
  | [] => rfl
  | _ :: bs => congrArg Nat.succ (updateCacheLoop_length touched (idx + 1) bs)

theorem getElem?_updateCacheLoop (touched : Nat → Bool) (idx : Nat) :
    ∀ (cache : List Bool) (i : Nat),
      MirSemantics.getElem? (updateCacheLoop touched idx cache) i =
        (MirSemantics.getElem? cache i).map (fun b => b || touched (idx + i))
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: bs, i + 1 => by
    have ih := getElem?_updateCacheLoop touched (idx + 1) bs i
    have h_add : idx + 1 + i = idx + (i + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [h_add] at ih
    exact ih

theorem list_eq_of_getElem?_eq {α : Type} :
    ∀ {xs ys : List α},
      xs.length = ys.length →
      (∀ i : Nat, MirSemantics.getElem? xs i = MirSemantics.getElem? ys i) →
      xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, hget => by
    have h0 : some x = some y := hget 0
    injection h0 with hxy
    subst hxy
    have htl := list_eq_of_getElem?_eq (Nat.succ.inj hlen) (fun i => hget (i + 1))
    rw [htl]

theorem updateMiriLocalsLoop_liftLocalsCached (types : List MirTy)
    (touched : Nat → Bool) (idx : Nat) :
    ∀ (tys : List MirTy) (newSlots oldSlots : List LocalSlot)
      (cache : List Bool),
      tys.length = newSlots.length →
      newSlots.length = oldSlots.length →
      oldSlots.length = cache.length →
      updateMiriLocalsLoop types touched idx tys newSlots
        (liftLocalsCached types tys oldSlots cache) =
      liftLocalsCached types tys newSlots
        (updateCacheLoop touched idx cache)
  | [], [], [], [], _, _, _ => rfl
  | ty :: tys, newSlot :: newSlots, oldSlot :: oldSlots, cached :: cache,
      h1, h2, h3 => by
    dsimp only [liftLocalsCached, updateMiriLocalsLoop, updateCacheLoop]
    have h_ls :
        ((refLocalStateOfSlotWithCache types ty oldSlot cached).layout.isSome ||
          touched idx) = (cached || touched idx) := by
      cases cached <;> rfl
    rw [h_ls]
    have h_tail := updateMiriLocalsLoop_liftLocalsCached types touched (idx + 1)
      tys newSlots oldSlots cache (Nat.succ.inj h1) (Nat.succ.inj h2)
      (Nat.succ.inj h3)
    rw [h_tail]

theorem updateCacheLoop_false (touched : Nat → Bool) (idx : Nat)
    (cache : List Bool) (h_false : ∀ i, idx ≤ i → touched i = false) :
    updateCacheLoop touched idx cache = cache := by
  apply list_eq_of_getElem?_eq (updateCacheLoop_length touched idx cache)
  intro i
  rw [getElem?_updateCacheLoop]
  cases hc : MirSemantics.getElem? cache i with
  | none => rfl
  | some b =>
    dsimp only [Option.map]
    rw [h_false (idx + i) (Nat.le_add_right idx i), Bool.or_false]

theorem updateCacheLoop_comp (t₁ t₂ : Nat → Bool) (idx : Nat)
    (cache : List Bool) :
    updateCacheLoop t₂ idx (updateCacheLoop t₁ idx cache) =
      updateCacheLoop (fun i => t₁ i || t₂ i) idx cache := by
  apply list_eq_of_getElem?_eq
  · rw [updateCacheLoop_length, updateCacheLoop_length, updateCacheLoop_length]
  · intro i
    rw [getElem?_updateCacheLoop, getElem?_updateCacheLoop, getElem?_updateCacheLoop]
    cases MirSemantics.getElem? cache i with
    | none => rfl
    | some b =>
      dsimp only [Option.map]
      rw [Bool.or_assoc]

private theorem getElem?_cacheTouch_ne :
    ∀ {cache : List Bool} {i id : Nat},
      id ≠ i →
      MirSemantics.getElem? (cacheTouch cache id) i =
        MirSemantics.getElem? cache i
  | [], _, _, _ => rfl
  | _ :: _, 0, 0, h => False.elim (h rfl)
  | _ :: _, 0, _ + 1, _ => rfl
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: rest, i + 1, j + 1, h =>
    @getElem?_cacheTouch_ne rest i j (fun h_eq => h (congrArg Nat.succ h_eq))

theorem updateCacheLoop_cacheTouch (cache : List Bool) (id : Nat) :
    updateCacheLoop (fun i => Nat.beq id i) 0 cache = cacheTouch cache id := by
  apply list_eq_of_getElem?_eq
  · rw [updateCacheLoop_length, cacheTouch_length]
  · intro i
    rw [getElem?_updateCacheLoop]
    rw [Nat.zero_add]
    cases hc : MirSemantics.getElem? cache i with
    | none =>
      have h_ge := mirGetElem?_ge_of_none hc
      have h_ge' : (cacheTouch cache id).length ≤ i := by
        rw [cacheTouch_length]; exact h_ge
      rw [mirGetElem?_none_of_ge h_ge']
      rfl
    | some b =>
      dsimp only [Option.map]
      cases h_b : Nat.beq id i with
      | true =>
        rw [Bool.or_true]
        have h_eq : id = i := Nat.eq_of_beq_eq_true h_b
        subst h_eq
        rw [getElem?_cacheTouch_self hc]
      | false =>
        have h_ne : id ≠ i := fun h_eq => by
          subst h_eq; rw [Nat.beq_refl] at h_b; cases h_b
        rw [Bool.or_false, getElem?_cacheTouch_ne h_ne, hc]

theorem updateCacheLoop_operandCacheTouch (cache : List Bool)
    (opnd : Operand) :
    updateCacheLoop (fun i => operandTouchesLocal opnd i) 0 cache =
      operandCacheTouch cache opnd := by
  cases opnd with
  | copy p | move p =>
    exact updateCacheLoop_cacheTouch cache p.localId
  | constant _ =>
    exact updateCacheLoop_false _ 0 cache (fun _ _ => rfl)

theorem updateCacheLoop_rvalueCacheTouch (dstId : LocalId) (rv : Rvalue)
    (cache : List Bool) :
    updateCacheLoop (fun i => Nat.beq dstId i || rvalueTouchesLocal rv i) 0
        cache =
      rvalueCacheTouch dstId rv cache := by
  rw [← updateCacheLoop_comp (fun i => Nat.beq dstId i)
    (rvalueTouchesLocal rv) 0 cache, updateCacheLoop_cacheTouch]
  cases rv with
  | use op =>
    have h_f : rvalueTouchesLocal (.use op) = operandTouchesLocal op := rfl
    dsimp only [rvalueCacheTouch]
    rw [h_f]
    exact updateCacheLoop_operandCacheTouch (cacheTouch cache dstId) op
  | binaryOp op lhs rhs =>
    have h_f : rvalueTouchesLocal (.binaryOp op lhs rhs) =
        fun i => operandTouchesLocal lhs i || operandTouchesLocal rhs i := rfl
    dsimp only [rvalueCacheTouch]
    rw [h_f, ← updateCacheLoop_comp (operandTouchesLocal lhs)
      (operandTouchesLocal rhs) 0 (cacheTouch cache dstId),
      updateCacheLoop_operandCacheTouch, updateCacheLoop_operandCacheTouch]
  | unaryOp op opnd =>
    have h_f : rvalueTouchesLocal (.unaryOp op opnd) = operandTouchesLocal opnd := rfl
    dsimp only [rvalueCacheTouch]
    rw [h_f]
    exact updateCacheLoop_operandCacheTouch (cacheTouch cache dstId) opnd
  | cast kind op ty =>
    cases kind with
    | intToInt =>
      have h_f : rvalueTouchesLocal (.cast .intToInt op ty) = operandTouchesLocal op := rfl
      dsimp only [rvalueCacheTouch]
      rw [h_f]
      exact updateCacheLoop_operandCacheTouch (cacheTouch cache dstId) op
    | unsupported | ptrToPtr | intToPtr | unsize | boxAsRef =>
      change updateCacheLoop (fun _ => false) 0 (cacheTouch cache dstId) =
        cacheTouch cache dstId
      exact updateCacheLoop_false _ 0 _ (fun _ _ => rfl)
  | discriminant p =>
    have h_f : rvalueTouchesLocal (.discriminant p) = fun i => Nat.beq p.localId i := rfl
    dsimp only [rvalueCacheTouch]
    rw [h_f]
    exact updateCacheLoop_cacheTouch (cacheTouch cache dstId) p.localId
  | ref _ _ =>
    change updateCacheLoop (fun _ => false) 0 (cacheTouch cache dstId) =
      cacheTouch cache dstId
    exact updateCacheLoop_false _ 0 _ (fun _ _ => rfl)
  | addressOf _ _ | fakeAddressOf _ =>
    change updateCacheLoop (fun _ => false) 0 (cacheTouch cache dstId) =
      cacheTouch cache dstId
    exact updateCacheLoop_false _ 0 _ (fun _ _ => rfl)
  | aggregateTuple _ | useRetag _ | aggregateRangeTo _ _
  | aggregateRangeFrom _ _ | aggregateArray _ _ | repeat_ _ _ _
  | aggregateRange _ _ _ | aggregateOption _ _ _ =>
    change updateCacheLoop (fun _ => false) 0 (cacheTouch cache dstId) =
      cacheTouch cache dstId
    exact updateCacheLoop_false _ 0 _ (fun _ _ => rfl)
  | unsupported =>
    change updateCacheLoop (fun _ => false) 0 (cacheTouch cache dstId) =
      cacheTouch cache dstId
    exact updateCacheLoop_false _ 0 _ (fun _ _ => rfl)

noncomputable def stmtCacheTouch (stmt : StatementKind) (cache : List Bool) :
    List Bool :=
  match stmt with
  | .assign dst rv => rvalueCacheTouch dst.localId rv cache
  | _ => cache

theorem stmtCacheTouch_length (stmt : StatementKind) (cache : List Bool) :
    (stmtCacheTouch stmt cache).length = cache.length := by
  cases stmt with
  | assign dst rv => exact rvalueCacheTouch_length dst.localId rv cache
  | _ => rfl

private theorem mapOption_resolveTy_map_canonical (ts : List MirTy) :
    ∀ (tids : List TyId) (locs : List MirTy),
      decodeLocalTys ts tids = some locs →
      (tids.map (canonicalTyId ts)).filterMap (resolveTy ts) = locs
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | tid :: tids, locs, h => by
    dsimp only [decodeLocalTys, mapOption, optMap2] at h
    cases h_g : MirSemantics.getElem? ts tid with
    | none => rw [h_g] at h; cases h
    | some ty =>
      cases h_rest : mapOption (MirSemantics.getElem? ts) tids with
      | none => rw [h_g, h_rest] at h; cases h
      | some rest =>
        rw [h_g, h_rest] at h
        injection h with h_eq
        have h_rest' : decodeLocalTys ts tids = some rest := h_rest
        let ⟨_, _, h_res_can⟩ := canonicalTyId_of_some h_g
        dsimp only [List.map, List.filterMap]
        rw [h_res_can]
        dsimp only [List.filterMap]
        rw [← h_eq, mapOption_resolveTy_map_canonical ts tids rest h_rest']

theorem toMiriBody_locals_filterMap_resolveTy {ts : List MirTy}
    {rbody : RefBody} {body : Body}
    (h_dec : decodeBody ts rbody = some body) :
    (toMiriBody ts rbody).locals.toList.filterMap (resolveTy ts) =
      body.locals := by
  let ⟨_, h_locs, _, _, _⟩ := decodeBody_inv h_dec
  exact mapOption_resolveTy_map_canonical ts rbody.locals body.locals h_locs

/-! ## Section 2: `StorageLive`, `StorageDead`, and `Step.evalStatement` -/

private theorem deallocateLocal_slot_pure (rp : RefProg) (ty : MirTy)
    (slot : LocalSlot) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_sm : SlotMatchesTy ty slot) :
    (match slotToMiriLocalValue ty slot with
     | .live (.indirect place) =>
       (refStorageHooks rp.types).deallocateStack place.ptr st
     | _ => EStateM.Result.ok () st) = .ok () st := by
  cases slot with
  | dead => rfl
  | immediate optVal => cases optVal <;> rfl
  | indirect _ | partialTuple _ => exact False.elim h_sm

private theorem storageLiveDyn_ref_eq (rp : RefProg)
    (ctx : SimFrameCtx) (rbody : RefBody) (body : Body)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (slots : List LocalSlot)
    (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (localId : LocalId)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_c_len : cache.length = body.locals.length)
    (h_inv : SlotsMatchTys body.locals slots) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots
      cache mem ctrl cm
    let res := Miri.Interpreter.MachineHooks.storageLiveDyn
      (refStorageHooks rp.types) localId .none st
    match MirSemantics.getElem? body.locals localId with
    | none => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .unsupported
    | some localTy =>
      match MirSemantics.setElem? slots localId (liveUninitSlot localTy) with
      | none => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .unsupported
      | some slots' =>
        res = .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals
          slots' cache mem ctrl cm) := by
  intro st res
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    body.locals slots cache mem ctrl cm
  have h_len := SlotsMatchTys.length_eq h_inv
  cases h_ty : MirSemantics.getElem? body.locals localId with
  | none =>
    have h_gl := mkGenSimFrame_getLocal_none_left rp ctx rbody blockIdx stmtIdx
      body.locals slots cache localId h_ty
    have h_err :
        res = .error (.stack (.invalidLocal localId
          (liftLocalsCached rp.types body.locals slots cache).length)) st := by
      dsimp only [res, Miri.Interpreter.MachineHooks.storageLiveDyn, bind, Bind.bind,
        pure, Pure.pure]
      rw [eStateM_bind_ok h_cf, h_gl]
      rfl
    exact ⟨_, _, h_err, rfl⟩
  | some localTy =>
    dsimp only
    let ⟨slot, h_sl⟩ := getElem?_some_of_length_eq h_len.symm h_ty
    let ⟨b, h_c⟩ := getElem?_some_of_length_eq h_c_len.symm h_ty
    let ⟨slots', h_set⟩ := mirSetElem?_some_of_lt slots localId
      (liveUninitSlot localTy) (mirGetElem?_lt_of_some h_sl)
    rw [h_set]
    dsimp only
    let ⟨tid, h_rty, _⟩ := decodeBody_local_mem_types h_bdec h_ty
    have h_bl :
        (mkGenSimFrame rp ctx rbody blockIdx stmtIdx body.locals slots cache).body.locals[localId]? =
          some (canonicalTyId rp.types tid) := by
      dsimp only [mkGenSimFrame, toMiriBody]
      rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map, h_rty]
      rfl
    have h_gl := mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx
      body.locals slots cache localId localTy slot b h_ty h_sl h_c
    have h_rep := mkGenSimFrame_replaceLocalValue_some rp ctx rbody blockIdx
      stmtIdx body.locals slots slots' cache localId localTy slot
      (liveUninitSlot localTy) b h_ty h_sl h_c h_set
    rw [slotToMiriLocalValue_liveUninit localTy] at h_rep
    dsimp only [res, Miri.Interpreter.MachineHooks.storageLiveDyn, bind, Bind.bind,
      pure, Pure.pure]
    rw [eStateM_bind_ok h_cf, h_gl]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure, h_bl]
    dsimp only [refStorageHooks]
    rw [eStateM_bind_pure, eStateM_bind_pure]
    dsimp only [ite_true_eq]
    rw [eStateM_bind_pure]
    dsimp only
    have h_hm : (Miri.Interpreter.MemPlaceMeta.none : Miri.Interpreter.MemPlaceMeta Miri.Memory.Provenance).hasMeta = false := rfl
    rw [h_hm, ite_false_eq]
    have h_alw := afterLocalWrite_mkGenSimState rp ctx rbody blockIdx stmtIdx
      body.locals slots cache mem ctrl cm localId true
    rw [eStateM_bind_ok h_alw, eStateM_bind_pure, eStateM_bind_ok h_cf, h_gl]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure, h_rep]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure]
    have h_scf := setCurrentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
      body.locals slots slots' cache cache mem ctrl cm
    rw [eStateM_bind_ok h_scf]
    cases slot with
    | dead => rfl
    | immediate optVal => cases optVal <;> rfl
    | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
    | partialTuple _ =>
      exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)

private theorem storageDead_ref_eq (rp : RefProg)
    (ctx : SimFrameCtx) (rbody : RefBody) (body : Body)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (slots : List LocalSlot)
    (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (localId : LocalId)
    (h_c_len : cache.length = body.locals.length)
    (h_inv : SlotsMatchTys body.locals slots) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots
      cache mem ctrl cm
    let res := Miri.Interpreter.MachineHooks.storageDead
      (refStorageHooks rp.types) localId st
    if Nat.beq localId 0 then
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .unsupported
    else
      match MirSemantics.setElem? slots localId .dead with
      | none => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .unsupported
      | some slots' =>
        res = .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals
          slots' cache mem ctrl cm) := by
  intro st res
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    body.locals slots cache mem ctrl cm
  have h_len := SlotsMatchTys.length_eq h_inv
  cases localId with
  | zero =>
    have h_err : res = .error (.stack .cannotMakeReturnPlaceDead) st := rfl
    exact ⟨_, _, h_err, rfl⟩
  | succ n =>
    simp only [Nat.beq, Bool.false_eq_true, ite_false]
    have h_ne0 : ((n + 1) == 0) = false := rfl
    cases h_set : MirSemantics.setElem? slots (n + 1) .dead with
    | none =>
      have h_sl_none := getElem?_none_of_setElem?_none h_set
      have h_gl := mkGenSimFrame_getLocal_none_right rp ctx rbody blockIdx stmtIdx
        body.locals slots cache (n + 1) h_sl_none
      have h_err :
          res = .error (.stack (.invalidLocal (n + 1)
            (liftLocalsCached rp.types body.locals slots cache).length)) st := by
        dsimp only [res, Miri.Interpreter.MachineHooks.storageDead, bind, Bind.bind,
          pure, Pure.pure]
        rw [h_ne0, ite_false_eq, eStateM_bind_ok h_cf, h_gl]
        rfl
      exact ⟨_, _, h_err, rfl⟩
    | some slots' =>
      let ⟨slot, h_sl⟩ := getElem?_some_of_setElem?_some h_set
      let ⟨localTy, h_ty⟩ := getElem?_some_of_length_eq h_len h_sl
      let ⟨b, h_c⟩ := getElem?_some_of_length_eq h_c_len.symm h_ty
      have h_gl := mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx
        body.locals slots cache (n + 1) localTy slot b h_ty h_sl h_c
      have h_rep := mkGenSimFrame_replaceLocalValue_some rp ctx rbody blockIdx
        stmtIdx body.locals slots slots' cache (n + 1) localTy slot .dead b
        h_ty h_sl h_c h_set
      dsimp only [res, Miri.Interpreter.MachineHooks.storageDead, bind, Bind.bind,
        pure, Pure.pure]
      rw [h_ne0, ite_false_eq, eStateM_bind_ok h_cf, h_gl]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      dsimp only [slotToMiriLocalValue] at h_rep
      rw [eStateM_bind_pure, h_rep]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      have h_scf := setCurrentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
        body.locals slots slots' cache cache mem ctrl cm
      rw [eStateM_bind_ok h_scf]
      cases slot with
      | dead => rfl
      | immediate optVal => cases optVal <;> rfl
      | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
      | partialTuple _ =>
        exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)

private theorem step_evalStatement_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (body : Body) (f : FrameState)
    (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (amem : MemoryState) (rstmt : RefStatementKind)
    (stmt : StatementKind)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_c_len : cache.length = body.locals.length)
    (h_assign_ok :
      cache = List.replicate body.locals.length true ∨
      mirAssignStmtOk body.locals stmt = true)
    (h_arg : Nat.blt body.argumentCount body.locals.length = true)
    (h_supp : body.locals.all isSupportedScalarOrUnitTy = true)
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_st_dec : decodeStmt rp.types rstmt = some stmt)
    (h_discr_ty :
      ∀ (dst src : Place) (srcTy : MirTy) (ety : EnumTy) (dstTy : MirTy),
        stmt = .assign dst (.discriminant src) →
        dst.projection.isEmpty = true →
        src.projection.isEmpty = true →
        MirSemantics.getElem? body.locals src.localId = some srcTy →
        refAsEnumTy? srcTy = some ety →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        enumAdmitted ety = true →
        dstTy = .int ety.discrWidth ety.discrSigned)
    (h_cast_ty :
      ∀ (dst : Place) (opnd : Operand) (castTy dstTy : MirTy),
        stmt = .assign dst (.cast .intToInt opnd castTy) →
        dst.projection.isEmpty = true →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        dstTy = castTy) :
    let st := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
      f.locals cache mem ctrl cm
    let res := Miri.Interpreter.Step.evalStatement
      (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
      c (toMiriStatement rp.types rstmt) st
    match evalStatement body f amem cm stmt with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = some k
    | .done _ => False
    | .step s' =>
      ∃ slots',
        s' = { frames := [{ f with stmtIdx := f.stmtIdx + 1, locals := slots' }],
               callerMem := cm, mem := amem } ∧
        res = (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
          slots' (stmtCacheTouch stmt cache) mem ctrl cm, .ok ()) := by
  intro st res
  cases rstmt with
  | nop =>
    injection h_st_dec with h_eq; subst h_eq
    exact ⟨f.locals, rfl, rfl⟩
  | storageLive localId =>
    injection h_st_dec with h_eq; subst h_eq
    have h_sl := storageLiveDyn_ref_eq rp ctx rbody body f.blockIdx f.stmtIdx
      f.locals cache mem ctrl cm localId h_bdec h_c_len h_inv
    have h_res :
        res = Miri.Interpreter.MachineHooks.run
          (Miri.Interpreter.MachineHooks.storageLiveDyn (refStorageHooks rp.types)
            localId .none) st := rfl
    rw [h_res]
    dsimp only [evalStatement, Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    cases h_ty : MirSemantics.getElem? body.locals localId with
    | none =>
      rw [h_ty] at h_sl
      let ⟨err, st', h_err, h_fk⟩ := h_sl
      rw [h_err]
      exact ⟨err, st', rfl, h_fk⟩
    | some localTy =>
      dsimp only
      rw [h_ty] at h_sl
      dsimp only at h_sl
      let ⟨old, h_old⟩ := getElem?_some_of_length_eq
        (SlotsMatchTys.length_eq h_inv).symm h_ty
      rw [h_old]
      dsimp only
      cases h_set : MirSemantics.setElem? f.locals localId (liveUninitSlot localTy) with
      | none =>
        rw [h_set] at h_sl
        let ⟨err, st', h_err, h_fk⟩ := h_sl
        rw [h_err]
        exact ⟨err, st', rfl, h_fk⟩
      | some slots' =>
        rw [h_set] at h_sl
        dsimp only
        rw [deallocateLocal_eq_ok_of_slotsMatchTys amem h_inv h_ty h_old]
        rw [h_sl]
        exact ⟨slots', rfl, rfl⟩
  | storageDead localId =>
    injection h_st_dec with h_eq; subst h_eq
    have h_sd := storageDead_ref_eq rp ctx rbody body f.blockIdx f.stmtIdx
      f.locals cache mem ctrl cm localId h_c_len h_inv
    have h_res :
        res = Miri.Interpreter.MachineHooks.run
          (Miri.Interpreter.MachineHooks.storageDead (refStorageHooks rp.types)
            localId) st := rfl
    rw [h_res]
    dsimp only [evalStatement, Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    cases h0 : Nat.beq localId 0 with
    | true =>
      rw [h0] at h_sd
      dsimp only [ite_true_eq] at h_sd
      let ⟨err, st', h_err, h_fk⟩ := h_sd
      rw [h_err]
      exact ⟨err, st', rfl, h_fk⟩
    | false =>
      rw [h0] at h_sd
      dsimp only [ite_false_eq] at h_sd
      cases h_old : MirSemantics.getElem? f.locals localId with
      | none =>
        have h_set : MirSemantics.setElem? f.locals localId .dead = none := by
          cases h_s : MirSemantics.setElem? f.locals localId .dead with
          | none => rfl
          | some _ =>
            let ⟨_, h_g⟩ := getElem?_some_of_setElem?_some h_s
            rw [h_old] at h_g; cases h_g
        rw [h_set] at h_sd
        let ⟨err, st', h_err, h_fk⟩ := h_sd
        rw [h_err]
        exact ⟨err, st', rfl, h_fk⟩
      | some old =>
        dsimp only
        let ⟨oldTy, h_oty⟩ := getElem?_some_of_length_eq
          (SlotsMatchTys.length_eq h_inv) h_old
        cases h_set : MirSemantics.setElem? f.locals localId .dead with
        | none =>
          rw [h_set] at h_sd
          let ⟨err, st', h_err, h_fk⟩ := h_sd
          rw [h_err]
          exact ⟨err, st', rfl, h_fk⟩
        | some slots' =>
          rw [h_set] at h_sd
          dsimp only
          rw [deallocateLocal_eq_ok_of_slotsMatchTys amem h_inv h_oty h_old]
          rw [h_sd]
          exact ⟨slots', rfl, rfl⟩
  | assign rdst rrv =>
    dsimp only [decodeStmt, optMap2] at h_st_dec
    cases h_pl : decodePlace rp.types rdst with
    | none => rw [h_pl] at h_st_dec; cases h_st_dec
    | some dst =>
      cases h_rv : decodeRvalue rp.types rrv with
      | none => rw [h_pl, h_rv] at h_st_dec; cases h_st_dec
      | some rv =>
        rw [h_pl, h_rv] at h_st_dec
        injection h_st_dec with h_eq; subst h_eq
        have h_ev := evalRvalueIntoPlace_ref_eq rp c ctx rbody body f.blockIdx
          f.stmtIdx f.locals cache amem mem ctrl cm rdst dst rrv rv h_bdec
          h_c_len h_assign_ok h_supp h_inv h_pl h_rv
          (fun src srcTy ety dstTy h_eq_rv =>
            h_discr_ty dst src srcTy ety dstTy (by rw [h_eq_rv]))
          (fun opnd castTy dstTy h_eq_rv =>
            h_cast_ty dst opnd castTy dstTy (by rw [h_eq_rv]))
        have h_res :
            res = Miri.Interpreter.MachineHooks.run
              (Miri.Interpreter.evalRvalueIntoPlace
                (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfg rp) refLimits)
                c (toMiriRvalue rp.types rrv) (toMiriPlace rdst)) st := rfl
        rw [h_res]
        dsimp only [evalStatement, Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
        cases h_dpe : dst.projection.isEmpty with
        | false =>
          rw [h_dpe] at h_ev
          dsimp only [Bool.not, ite_true_eq] at h_ev
          dsimp only [Bool.not, ite_true_eq]
          let ⟨err, st', h_err, h_fk⟩ := h_ev
          rw [h_err]
          exact ⟨err, st', rfl, h_fk⟩
        | true =>
          rw [h_dpe] at h_ev
          dsimp only [Bool.not, ite_false_eq] at h_ev
          dsimp only [Bool.not, ite_false_eq]
          cases h_dty : MirSemantics.getElem? body.locals dst.localId with
          | none =>
            rw [h_dty] at h_ev
            let ⟨err, st', h_err, h_fk⟩ := h_ev
            rw [h_err]
            exact ⟨err, st', rfl, h_fk⟩
          | some dstTy =>
            dsimp only
            rw [h_dty] at h_ev
            dsimp only at h_ev
            cases h_er : evalRvalue body.locals f.locals amem dstTy rv with
            | error k =>
              rw [h_er] at h_ev
              let ⟨err, st', h_err, h_fk⟩ := h_ev
              rw [h_err]
              exact ⟨err, st', rfl, h_fk⟩
            | ok triple =>
              cases triple with
              | mk val rest =>
              cases rest with
              | mk localsAfterRval memAfterRval =>
                dsimp only
                rw [h_er] at h_ev
                dsimp only at h_ev
                cases h_wp : writePlace localsAfterRval memAfterRval dst.localId
                    dstTy val with
                | error k =>
                  rw [h_wp] at h_ev
                  let ⟨err, st', h_err, h_fk⟩ := h_ev
                  rw [h_err]
                  exact ⟨err, st', rfl, h_fk⟩
                | ok pair =>
                  cases pair with
                  | mk slots' amem' =>
                  rw [h_wp] at h_ev
                  rw [h_ev]
                  let ⟨h_inv₁, h_m₁⟩ := evalRvalue_slotsMatchTys h_inv h_er
                  let ⟨_, h_m₂⟩ := writePlace_slotsMatchTys h_inv₁ h_dty h_wp
                  refine ⟨slots', ?_, rfl⟩
                  rw [h_m₂, h_m₁]
  | unsupported =>
    injection h_st_dec with h_eq; subst h_eq
    have h_ev := evalRvalueIntoPlace_ref_eq rp c ctx rbody body f.blockIdx
      f.stmtIdx f.locals cache amem mem ctrl cm ⟨0, []⟩ ⟨0, []⟩ .unsupported
      .unsupported h_bdec h_c_len
      (Or.inr (by dsimp only [mirAssignStmtOk]; cases MirSemantics.getElem? body.locals 0 <;> rfl))
      h_supp h_inv rfl rfl
      (fun _ _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
    have h_res :
        res = Miri.Interpreter.MachineHooks.run
          (Miri.Interpreter.evalRvalueIntoPlace
            (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfg rp) refLimits)
            c (toMiriRvalue rp.types .unsupported) (toMiriPlace ⟨0, []⟩)) st := rfl
    rw [h_res]
    dsimp only [evalStatement, Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    have h_pos : 0 < body.locals.length :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.blt_eq.mp h_arg)
    let ⟨ty₀, h_ty₀⟩ := mirGetElem?_some_of_lt h_pos
    rw [h_ty₀] at h_ev
    dsimp only [evalRvalue] at h_ev
    let ⟨err, st', h_err, h_fk⟩ := h_ev
    rw [h_err]
    exact ⟨err, st', rfl, h_fk⟩

/-! ## Section 3: `Return`, `SwitchInt`, and `ControlFlow.evalTerminator` -/

private theorem placeMachine_localToOp_live (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (optVal : Option Val)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal)) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
      cache mem ctrl cm
    Miri.Interpreter.PlaceMachine.localToOp (refExecCfg rp).compiler c id st =
      .ok ⟨.immediate (optValToMiriImm ty optVal),
        refLocalLayoutForTy rp.types ty⟩
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
          (cacheTouch cache id) mem ctrl cm) := by
  intro st
  let ⟨b, h_c⟩ := getElem?_some_of_length_eq h_c_len.symm h_ty
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
  have h_gl := mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache id ty (.immediate optVal) b h_ty h_sl h_c
  have h_c' := getElem?_cacheTouch_self h_c
  have h_cf' := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots (cacheTouch cache id) mem ctrl cm
  have h_go' := mkGenSimFrame_getLocalOperand_live rp ctx rbody blockIdx stmtIdx
    bodyLocals slots (cacheTouch cache id) id ty optVal true h_ty h_sl h_c'
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  cases b with
  | true =>
    rw [cacheTouch_eq_self_of_true h_c] at h_cf'
    rw [cacheTouch_eq_self_of_true h_c] at h_go'
    rw [cacheTouch_eq_self_of_true h_c]
    have h_ll :
        Miri.Interpreter.PlaceMachine.layoutLocal (refExecCfg rp).compiler c id st =
          .ok (refLocalLayoutForTy rp.types ty) st := by
      dsimp only [Miri.Interpreter.PlaceMachine.layoutLocal, bind, Bind.bind,
        pure, Pure.pure]
      rw [eStateM_bind_ok h_cf, h_gl]
      rfl
    dsimp only [Miri.Interpreter.PlaceMachine.localToOp,
      Miri.Interpreter.PlaceMachine.localToOpCore, bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_ll, eStateM_bind_ok h_cf, h_go']
    dsimp only
    change EStateM.bind (EStateM.pure _) _ _ = _
    rw [eStateM_bind_pure]
    simp only [h_sz, Bool.not_true, Bool.false_eq_true, ite_false]
    have h_vip : (refExecCfg rp).compiler.validationInProgress st = .ok false st := rfl
    rw [eStateM_bind_ok h_vip]
    rw [ite_false_eq, eStateM_bind_ok (afterLocalRead_mkGenSimState rp ctx rbody
      blockIdx stmtIdx bodyLocals slots cache mem ctrl cm id)]
    rfl
  | false =>
    have h_st_cf : st.stack.currentFrame? =
        some (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache) :=
      stack_currentFrame?_push _ _
    have h_rl : (refExecCfg rp).compiler.layout c id st =
        .ok (refLocalLayoutForTy rp.types ty) st := by
      dsimp only [refExecCfg, Miri.Interpreter.ExecutionMachine.withValidation,
        refExecutionConfig, refCompilerHooks,
        Miri.Interpreter.TypedMachineBindings.bindValidation,
        refBaseCompilerHooks]
      rw [h_st_cf]
      dsimp only
      let ⟨tid, h_rloc, h_ts⟩ := decodeLocalTys_mirGetElem? h_locs h_ty
      let ⟨h_can, _, h_res⟩ := canonicalTyId_of_some h_ts
      have h_m : MirSemantics.getElem? (rbody.locals.map (canonicalTyId rp.types)) id =
          some (canonicalTyId rp.types tid) := by
        rw [mirGetElem?_map, h_rloc]; rfl
      dsimp only [mkGenSimFrame, toMiriBody]
      rw [array_getElem?_eq_mirGetElem?, h_m, h_can]
      dsimp only
      rw [h_can] at h_res
      rw [refLayoutOfTyId_tyIdFor_of_resolve h_res]
    have h_gc := mkGenSimFrame_getOrCacheLocalLayout_some rp ctx rbody blockIdx
      stmtIdx bodyLocals slots cache id ty (.immediate optVal) false
      (refLocalLayoutForTy rp.types ty) h_ty h_sl h_c (fun _ => rfl)
    have h_set := setCurrentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
      bodyLocals slots slots cache (cacheTouch cache id) mem ctrl cm
    let st' := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
      (cacheTouch cache id) mem ctrl cm
    have h_ll :
        Miri.Interpreter.PlaceMachine.layoutLocal (refExecCfg rp).compiler c id st =
          .ok (refLocalLayoutForTy rp.types ty) st' := by
      dsimp only [Miri.Interpreter.PlaceMachine.layoutLocal, bind, Bind.bind,
        pure, Pure.pure]
      rw [eStateM_bind_ok h_cf, h_gl]
      dsimp only [refLocalStateOfSlotWithCache]
      rw [ite_false_eq]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      rw [eStateM_bind_ok h_rl, eStateM_bind_ok h_cf, h_gc]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure, eStateM_bind_ok h_set]
      rfl
    dsimp only [Miri.Interpreter.PlaceMachine.localToOp,
      Miri.Interpreter.PlaceMachine.localToOpCore, bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_ll, eStateM_bind_ok h_cf', h_go']
    dsimp only
    change EStateM.bind (EStateM.pure _) _ _ = _
    rw [eStateM_bind_pure]
    simp only [h_sz, Bool.not_true, Bool.false_eq_true, ite_false]
    have h_vip : (refExecCfg rp).compiler.validationInProgress st' = .ok false st' := rfl
    rw [eStateM_bind_ok h_vip]
    rw [ite_false_eq, eStateM_bind_ok (afterLocalRead_mkGenSimState rp ctx rbody
      blockIdx stmtIdx bodyLocals slots (cacheTouch cache id) mem ctrl cm id)]
    rfl

private theorem placeMachine_localToOp_dead (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
      cache mem ctrl cm
    ∃ st',
      Miri.Interpreter.PlaceMachine.localToOp (refExecCfg rp).compiler c id st =
        .error (.stack (.localExpectedLive id)) st' := by
  intro st
  let ⟨b, h_c⟩ := getElem?_some_of_length_eq h_c_len.symm h_ty
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
  have h_gl := mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache id ty .dead b h_ty h_sl h_c
  cases b with
  | true =>
    have h_go := mkGenSimFrame_getLocalOperand_dead rp ctx rbody blockIdx stmtIdx
      bodyLocals slots cache id ty true h_ty h_sl h_c
    have h_ll :
        Miri.Interpreter.PlaceMachine.layoutLocal (refExecCfg rp).compiler c id st =
          .ok (refLocalLayoutForTy rp.types ty) st := by
      dsimp only [Miri.Interpreter.PlaceMachine.layoutLocal, bind, Bind.bind,
        pure, Pure.pure]
      rw [eStateM_bind_ok h_cf, h_gl]
      rfl
    refine ⟨st, ?_⟩
    dsimp only [Miri.Interpreter.PlaceMachine.localToOp,
      Miri.Interpreter.PlaceMachine.localToOpCore, bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_ll, eStateM_bind_ok h_cf, h_go]
    rfl
  | false =>
    have h_st_cf : st.stack.currentFrame? =
        some (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache) :=
      stack_currentFrame?_push _ _
    have h_rl : (refExecCfg rp).compiler.layout c id st =
        .ok (refLocalLayoutForTy rp.types ty) st := by
      dsimp only [refExecCfg, Miri.Interpreter.ExecutionMachine.withValidation,
        refExecutionConfig, refCompilerHooks,
        Miri.Interpreter.TypedMachineBindings.bindValidation,
        refBaseCompilerHooks]
      rw [h_st_cf]
      dsimp only
      let ⟨tid, h_rloc, h_ts⟩ := decodeLocalTys_mirGetElem? h_locs h_ty
      let ⟨h_can, _, h_res⟩ := canonicalTyId_of_some h_ts
      have h_m : MirSemantics.getElem? (rbody.locals.map (canonicalTyId rp.types)) id =
          some (canonicalTyId rp.types tid) := by
        rw [mirGetElem?_map, h_rloc]; rfl
      dsimp only [mkGenSimFrame, toMiriBody]
      rw [array_getElem?_eq_mirGetElem?, h_m, h_can]
      dsimp only
      rw [h_can] at h_res
      rw [refLayoutOfTyId_tyIdFor_of_resolve h_res]
    let ⟨fr', h_gc, h_go'⟩ := mkGenSimFrame_getOrCacheLocalLayout_dead rp ctx rbody
      blockIdx stmtIdx bodyLocals slots cache id ty false
      (refLocalLayoutForTy rp.types ty) h_ty h_sl h_c
    let st' := mkRefMiriStackState (ctx.below.push fr') ctx.topRel? mem ctrl cm
    have h_set' : Miri.Interpreter.MachineHooks.setCurrentFrame fr' st = .ok () st' := by
      dsimp only [Miri.Interpreter.MachineHooks.setCurrentFrame, get, getThe,
        MonadStateOf.get, set, MonadStateOf.set, EStateM.get, EStateM.set,
        st, st', mkGenSimState, mkRefMiriStackState, bind, Bind.bind, pure, Pure.pure,
        EStateM.bind, EStateM.pure]
      rw [array_isEmpty_push_false]
      simp only [Bool.false_eq_true, ite_false]
      rw [array_pop_push_eq]
      rfl
    have h_cf' : Miri.Interpreter.MachineHooks.currentFrame st' = .ok fr' st' := by
      dsimp only [Miri.Interpreter.MachineHooks.currentFrame, st', mkRefMiriStackState,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
        get, getThe, MonadStateOf.get, EStateM.get]
      rw [stack_currentFrame?_push]
      rfl
    have h_ll :
        Miri.Interpreter.PlaceMachine.layoutLocal (refExecCfg rp).compiler c id st =
          .ok (refLocalLayoutForTy rp.types ty) st' := by
      dsimp only [Miri.Interpreter.PlaceMachine.layoutLocal, bind, Bind.bind,
        pure, Pure.pure]
      rw [eStateM_bind_ok h_cf, h_gl]
      dsimp only [refLocalStateOfSlotWithCache]
      rw [ite_false_eq]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      rw [eStateM_bind_ok h_rl, eStateM_bind_ok h_cf, h_gc]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure, eStateM_bind_ok h_set']
      rfl
    refine ⟨st', ?_⟩
    dsimp only [Miri.Interpreter.PlaceMachine.localToOp,
      Miri.Interpreter.PlaceMachine.localToOpCore, bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_ll, eStateM_bind_ok h_cf', h_go']
    rfl

private theorem computeTop_push_of_back {below : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    {fr bfr : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra}
    (h_back : below.back? = some bfr)
    (h_rel : bfr.extra.userRelevance = 255) :
    Miri.Interpreter.FrameRelevance.computeTop ⟨below.push fr⟩ 1 =
      some (below.size - 1) := by
  have h_pos : 0 < below.size := by
    cases h_sz : below.size with
    | zero =>
      have h_b : below.back? = none := by
        dsimp only [Array.back?]
        rw [Array.getElem?_eq_none (by rw [h_sz]; exact Nat.zero_le _)]
      rw [h_b] at h_back; cases h_back
    | succ n => exact Nat.zero_lt_succ n
  have h_idx : below[below.size - 1]? = some bfr := by
    dsimp only [Array.back?] at h_back
    exact h_back
  have h_lt : below.size - 1 < below.size := Nat.sub_lt h_pos (Nat.zero_lt_succ 0)
  have h_frame_idx : (below.push fr)[below.size - 1]? = some bfr := by
    rw [Array.getElem?_push_lt h_lt, ← Array.getElem?_eq_getElem h_lt]
    exact h_idx
  have h_drop : ((List.range (below.push fr).size).reverse.drop 1) =
      (below.size - 1) :: (List.range (below.size - 1)).reverse := by
    rw [Array.size_push]
    have h_sz_eq : below.size = (below.size - 1) + 1 := (Nat.sub_add_cancel h_pos).symm
    rw [h_sz_eq, List.range_succ, List.range_succ, List.reverse_append,
      List.reverse_append]
    rfl
  dsimp only [Miri.Interpreter.FrameRelevance.computeTop, Id.run]
  rw [h_drop, List.forIn_cons]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [h_frame_idx]
  dsimp only
  rw [h_rel]
  rfl

private theorem popRaw_mkGenSimState (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory)
    (h_tr : refTopRelevanceValid (ctx.below.size + 1) ctx.topRel?)
    (h_back : ctx.below.isEmpty = false →
      ∃ bfr, ctx.below.back? = some bfr ∧ bfr.extra.userRelevance = 255) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
      cache mem ctrl cm
    let fr := mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
    let topRel' : Option Nat :=
      if ctx.below.isEmpty then none else some (ctx.below.size - 1)
    ∃ stPop : Miri.Interpreter.MachineHooks.State Unit RefUser,
      Miri.Interpreter.TypedMachineBindings.popRaw
          (Miri.Interpreter.TypedMachineBindings.retagHooks
            (refExecCfg rp).access (refExecCfg rp).retag) st =
        .ok fr stPop ∧
      stPop.stack.frames = ctx.below ∧
      stPop.machine.memory = mem ∧
      stPop.machine.dataRace = none ∧
      stPop.machine.pendingMoveDeinit = false ∧
      stPop.machine.user.callerMem = cm ∧
      stPop.machine.threads =
        { Miri.Concurrency.ThreadManager.initial true with
          threads := (Miri.Concurrency.ThreadManager.initial true).threads.mapIdx
            fun index thread =>
              if index == (Miri.Concurrency.ThreadManager.initial true).activeThread.toNat then
                { thread with topUserRelevantFrame := topRel' }
              else thread } ∧
      stPop = mkRefMiriStackState ctx.below topRel' mem ctrl cm := by
  intro st fr topRel'
  refine ⟨mkRefMiriStackState ctx.below topRel' mem ctrl cm, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have h_bp :
      Miri.Interpreter.FrameRelevance.beforeStackPop st =
        .ok () (mkRefMiriStackState (ctx.below.push fr) topRel' mem ctrl cm) := by
    cases h_emp : ctx.below.isEmpty with
    | true =>
      have h_e : ctx.below = Array.empty := Array.isEmpty_iff.mp h_emp
      have h_z : ctx.below.size = 0 := by rw [h_e]; rfl
      cases h_rel : ctx.topRel? with
      | none =>
        dsimp only [st, mkGenSimState, topRel']
        rw [h_emp, ite_true_eq, h_e, h_rel]
        rfl
      | some idx =>
        rw [h_rel, h_z] at h_tr
        have h_eq : idx = 0 := by
          dsimp only [refTopRelevanceValid] at h_tr; exact h_tr.2
        subst h_eq
        dsimp only [st, mkGenSimState, topRel']
        rw [h_emp, ite_true_eq, h_e, h_rel]
        rfl
    | false =>
      cases h_rel : ctx.topRel? with
      | none =>
        rw [h_rel] at h_tr
        dsimp only [refTopRelevanceValid] at h_tr
        have h_z : ctx.below.size = 0 := Nat.succ_inj.mp h_tr
        have h_emp_t : ctx.below.isEmpty = true := Array.isEmpty_iff.mpr (Array.eq_empty_iff_size_eq_zero.mpr h_z)
        rw [h_emp_t] at h_emp; cases h_emp
      | some idx =>
        rw [h_rel] at h_tr
        have h_eq : idx = ctx.below.size := by
          dsimp only [refTopRelevanceValid] at h_tr
          rw [Nat.add_sub_cancel] at h_tr
          exact h_tr.2
        subst h_eq
        let ⟨bfr, h_b, h_r⟩ := h_back h_emp
        have h_comp := computeTop_push_of_back (fr := fr) h_b h_r
        have h_comp_eq : Miri.Interpreter.FrameRelevance.computeTop ⟨ctx.below.push fr⟩ 1 = topRel' := by
          dsimp only [topRel']; rw [h_emp, ite_false_eq]; exact h_comp
        have h_bp_ex : ∃ (act noop : Miri.Interpreter.MachineHooks.M Unit RefUser Unit),
            Miri.Interpreter.FrameRelevance.beforeStackPop
                (mkRefMiriStackState (ctx.below.push fr) (some ctx.below.size) mem ctrl cm) =
              (if (ctx.below.size == (ctx.below.push fr).size - 1) = true then
                act else noop)
                (mkRefMiriStackState (ctx.below.push fr) (some ctx.below.size) mem ctrl cm) ∧
            act (mkRefMiriStackState (ctx.below.push fr) (some ctx.below.size) mem ctrl cm) =
              .ok () (mkRefMiriStackState (ctx.below.push fr)
                (Miri.Interpreter.FrameRelevance.computeTop ⟨ctx.below.push fr⟩ 1) mem ctrl cm) :=
          ⟨_, _, rfl, rfl⟩
        let ⟨act, noop, h_bp1, h_bp2⟩ := h_bp_ex
        rw [Array.size_push, Nat.add_sub_cancel, beq_self_eq_true, ite_true_eq] at h_bp1
        dsimp only [st, mkGenSimState]
        rw [h_rel, h_bp1, h_bp2, h_comp_eq]
  have h_bt : Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure
      (Miri.Interpreter.TypedMachineBindings.retagHooks (refExecCfg rp).access (refExecCfg rp).retag).ensureTreeExtra st =
      .ok () st := rfl
  have h_pop :
      st.stack.popFrame = .ok (⟨ctx.below⟩, fr) := by
    dsimp only [st, mkGenSimState, mkRefMiriStackState, Miri.Interpreter.Stack.popFrame]
    have h_back_push : (ctx.below.push fr).back? = some fr := by
      dsimp only [Array.back?]
      rw [Array.size_push, Nat.add_sub_cancel, Array.getElem?_push_size]
    rw [h_back_push]
    dsimp only [pure, Pure.pure, Except.pure]
    rw [array_pop_push_eq]
  dsimp only [Miri.Interpreter.TypedMachineBindings.popRaw, bind, Bind.bind,
    pure, Pure.pure]
  rw [eStateM_bind_ok h_bt, eStateM_bind_ok h_bp]
  have h_get : (get : Miri.Interpreter.MachineHooks.M Unit RefUser
        (Miri.Interpreter.MachineHooks.State Unit RefUser))
        (mkRefMiriStackState (ctx.below.push fr) topRel' mem ctrl cm) =
      .ok (mkRefMiriStackState (ctx.below.push fr) topRel' mem ctrl cm)
        (mkRefMiriStackState (ctx.below.push fr) topRel' mem ctrl cm) := rfl
  rw [eStateM_bind_ok h_get]
  have h_pop2 :
      (mkRefMiriStackState (ctx.below.push fr) topRel' mem ctrl cm).stack.popFrame =
        .ok (⟨ctx.below⟩, fr) := h_pop
  rw [h_pop2]
  dsimp only [Except.pure]
  change EStateM.bind (EStateM.pure _) _ _ = _
  rw [eStateM_bind_pure]
  have h_set : (set (mkRefMiriStackState ctx.below topRel' mem ctrl cm) :
        Miri.Interpreter.MachineHooks.M Unit RefUser Unit)
        (mkRefMiriStackState (ctx.below.push fr) topRel' mem ctrl cm) =
      .ok () (mkRefMiriStackState ctx.below topRel' mem ctrl cm) := rfl
  dsimp only
  have h_mach_eq :
      ({ stack := ({ frames := ctx.below } : Miri.Interpreter.Stack _ _ _),
         machine := (mkRefMiriStackState (ctx.below.push fr) topRel' mem ctrl cm).machine } :
          Miri.Interpreter.MachineHooks.State Unit RefUser) =
        mkRefMiriStackState ctx.below topRel' mem ctrl cm := rfl
  rw [h_mach_eq, eStateM_bind_ok h_set]
  rfl

private theorem returnFromCurrentFrame_ref_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (body : Body) (rbb : RefBasicBlock)
    (bb : BasicBlock) (f : FrameState) (retTy : MirTy) (cache : List Bool)
    (topRel? : Option Nat) (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (amem : MemoryState)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_c_len : cache.length = body.locals.length)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = some rbb)
    (h_rbb_dec : decodeBasicBlock rp.types rbb = some bb)
    (h_rterm : rbb.terminator = .return_)
    (h_ret_ty : MirSemantics.getElem? body.locals 0 = some retTy)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, retPlace))
    (h_tr : refTopRelevanceValid 1 topRel?)
    (h_supp : body.locals.all isSupportedScalarOrUnitTy = true)
    (h_inv : SlotsMatchTys body.locals f.locals)
    (ps : PanicStrategy := .unwind) (lh : Bool := true) :
    let ctx : SimFrameCtx :=
      { below := Array.empty
        topRel? := topRel?
        fnTag := defId
        retCont := .stop false
        retPlace := .memory retPlace }
    let st := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals
      cache mem ctrl cm
    let res := (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfig rp) refLimits).terminator c
      (toMiriTerminator rp.types .return_) st
    match evalTerminator body bb f amem cm ps lh with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = some k
    | .done (.returned ⟨v, cm'⟩) =>
      ∃ st',
        res = (st', .ok ()) ∧
        st'.stack.frames.isEmpty = true ∧
        refReadReturnVal st'.machine.memory retTy retPlace = .ok v ∧
        st'.machine.user.callerMem = cm'
    | .done (.aborted cm') =>
      ∃ st',
        res = (st', .error (.termination (.abort "panic abort"))) ∧
        st'.machine.user.callerMem = cm'
    | .done (.unwound _) => False
    | .step s' =>
      ∃ tgt slots',
        s' = { frames := [{ f with blockIdx := tgt, stmtIdx := 0, locals := slots' }],
               callerMem := cm, mem := amem } ∧
        res = (mkGenSimState rp ctx rbody tgt 0 body.locals slots' cache
          mem ctrl cm, .ok ()) := by
  intro ctx st res
  let ⟨_, h_term_dec, h_cl_eq⟩ := decodeBasicBlock_inv h_rbb_dec
  rw [h_rterm] at h_term_dec
  injection h_term_dec with h_bb_term
  have h_st_cf :
      st.stack.currentFrame? =
        some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) :=
    rfl
  have h_mf_loc :
      (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).location =
        .mir ⟨f.blockIdx, f.stmtIdx⟩ := rfl
  have h_mb :
      (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).body.basicBlocks[f.blockIdx]? =
        some (toMiriBasicBlock rp.types rbb) := by
    dsimp only [mkGenSimFrame, toMiriBody]
    rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map, h_rbb]
    rfl
  have h_len := SlotsMatchTys.length_eq h_inv
  have h_locs := (decodeBody_inv h_bdec).2.1
  have h_ret_supp : isSupportedScalarOrUnitTy retTy = true :=
    list_all_mirGetElem? (p := isSupportedScalarOrUnitTy) h_supp h_ret_ty
  have h_ret_res : resolveTy rp.types (tyIdFor rp.types retTy) = some retTy := by
    let ⟨_, _, h_ts⟩ := decodeBody_local_mem_types h_bdec h_ret_ty
    exact (resolveTy_tyIdFor_of_mem h_ts).2
  cases h_cl : bb.cleanup with
  | true =>
    have h_rcl : rbb.cleanup = true := h_cl_eq.trans h_cl
    have h_ev_t : evalTerminator body bb f amem cm ps lh = .fault .unsupported := by
      dsimp only [evalTerminator]; rw [← h_bb_term, h_cl]; rfl
    rw [h_ev_t]
    have h_err :
        res = (st, .error (.invalidProgram "return/unwind cleanup assertion failed")) := by
      dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.ControlFlow.evalTerminator,
        Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
        toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure]
      rw [h_st_cf]
      dsimp only
      rw [h_mf_loc]
      dsimp only
      rw [h_mb]
      dsimp only [toMiriBasicBlock]
      rw [h_rcl]
      rfl
    exact ⟨_, _, h_err, rfl⟩
  | false =>
    have h_rcl : rbb.cleanup = false := h_cl_eq.trans h_cl
    let ⟨slot₀, h_sl₀⟩ := getElem?_some_of_length_eq h_len.symm h_ret_ty
    cases slot₀ with
    | indirect _ =>
      exact False.elim (SlotsMatchTys.not_indirect h_inv h_ret_ty h_sl₀)
    | partialTuple _ =>
      exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ret_ty h_sl₀)
    | dead =>
      have h_ev_t : evalTerminator body bb f amem cm ps lh = .fault .undefined := by
        dsimp only [evalTerminator]
        rw [← h_bb_term]
        dsimp only
        rw [h_cl, ite_false_eq, h_sl₀]
      rw [h_ev_t]
      let ⟨st', h_ro⟩ := placeMachine_localToOp_dead rp c ctx rbody f.blockIdx f.stmtIdx
        body.locals f.locals cache mem ctrl cm 0 retTy h_locs h_c_len h_ret_ty h_sl₀
      have h_ro' :
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits)).place.localToOp
            c 0 st = .error (.stack (.localExpectedLive 0)) st' := h_ro
      have h_err : res = (st', .error (.stack (.localExpectedLive 0))) := by
        dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
          Miri.Interpreter.ControlFlow.evalTerminator,
          Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
          Miri.Interpreter.ExecutionControl.hooks,
          Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
          toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [h_st_cf]
        dsimp only
        rw [h_mf_loc]
        dsimp only
        rw [h_mb]
        dsimp only [toMiriBasicBlock]
        rw [h_rcl, h_ro']
        rfl
      exact ⟨_, _, h_err, rfl⟩
    | immediate optVal =>
      have h_ro := placeMachine_localToOp_live rp c ctx rbody f.blockIdx f.stmtIdx
        body.locals f.locals cache mem ctrl cm 0 retTy optVal h_locs h_c_len
        h_ret_ty h_sl₀
      let ⟨stPop, h_pop, h_pop_fr, h_pop_mem, h_pop_dr, h_pop_pmd, h_pop_cm, _, _⟩ :=
        popRaw_mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals
          (cacheTouch cache 0) mem ctrl cm h_tr (fun h => by cases h)
      have h_ro' :
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits)).place.localToOp
            c 0 st =
          .ok ⟨.immediate (optValToMiriImm retTy optVal),
            refLocalLayoutForTy rp.types retTy⟩
            (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals
              (cacheTouch cache 0) mem ctrl cm) := h_ro
      have h_pop' :
          Miri.Interpreter.TypedMachineBindings.popRaw
            (Miri.Interpreter.TypedMachineBindings.retagHooks
              (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).access
              (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).retag)
            (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals
              (cacheTouch cache 0) mem ctrl cm) =
          .ok (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals
            (cacheTouch cache 0)) stPop := h_pop
      have h_step_copy_err :
          ∀ (e : Miri.Interpreter.StepError) (st₁ : Miri.Interpreter.MachineHooks.State Unit RefUser),
            Miri.Interpreter.copyRuntimePlace
                (Miri.Interpreter.ExecutionMachine.projectionHooks
                  (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits)).place
                (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).copy c
                ⟨.immediate (optValToMiriImm retTy optVal),
                  refLocalLayoutForTy rp.types retTy⟩
                ⟨.memory retPlace.mplace, retPlace.layout⟩ true stPop = .error e st₁ →
            res = (st₁, Except.error e) := by
        intro e st₁ h_cp
        dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
          Miri.Interpreter.ControlFlow.evalTerminator,
          Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
          Miri.Interpreter.ExecutionControl.hooks,
          Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
          toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [h_st_cf]
        dsimp only
        rw [h_mf_loc]
        dsimp only
        rw [h_mb]
        dsimp only [toMiriBasicBlock]
        rw [h_rcl, h_ro']
        dsimp only
        rw [h_pop']
        dsimp only [mkGenSimFrame, ctx,
          Miri.Interpreter.RuntimeStackPlace.toRuntimePlace]
        simp only [h_cp]
        rfl
      have h_step_copy_ok :
          ∀ (st₁ : Miri.Interpreter.MachineHooks.State Unit RefUser),
            Miri.Interpreter.copyRuntimePlace
                (Miri.Interpreter.ExecutionMachine.projectionHooks
                  (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits)).place
                (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).copy c
                ⟨.immediate (optValToMiriImm retTy optVal),
                  refLocalLayoutForTy rp.types retTy⟩
                ⟨.memory retPlace.mplace, retPlace.layout⟩ true stPop = .ok () st₁ →
            res =
              if (!st₁.stack.frames.isEmpty) = true then
                (st₁, Except.error (.invalidProgram "NoCleanup requires empty stack and normal return"))
              else (st₁, Except.ok ()) := by
        intro st₁ h_cp
        dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
          Miri.Interpreter.ControlFlow.evalTerminator,
          Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
          Miri.Interpreter.ExecutionControl.hooks,
          Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
          toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [h_st_cf]
        dsimp only
        rw [h_mf_loc]
        dsimp only
        rw [h_mb]
        dsimp only [toMiriBasicBlock]
        rw [h_rcl, h_ro']
        dsimp only
        rw [h_pop']
        dsimp only [mkGenSimFrame, ctx,
          Miri.Interpreter.RuntimeStackPlace.toRuntimePlace]
        simp only [h_cp, Bool.or_false]
        rfl
      have h_sm := SlotsMatchTys.getElem? h_inv h_ret_ty h_sl₀
      cases optVal with
      | none =>
        have h_ev_t : evalTerminator body bb f amem cm ps lh = .fault .undefined := by
          dsimp only [evalTerminator]
          rw [← h_bb_term]
          dsimp only
          rw [h_cl, ite_false_eq, h_sl₀]
        rw [h_ev_t]
        let ⟨msg, st', h_ub⟩ := copyReturn_uninit_ub rp c retTy mem retPlace stPop
          h_init h_pop_mem h_pop_dr h_pop_pmd h_sm h_ret_supp h_ret_res
        exact ⟨_, _, h_step_copy_err _ _ h_ub, rfl⟩
      | some v =>
        have h_ev_t : evalTerminator body bb f amem cm ps lh = .done (.returned ⟨v, cm⟩) := by
          dsimp only [evalTerminator]
          rw [← h_bb_term]
          dsimp only
          rw [h_cl, ite_false_eq, h_sl₀]
        rw [h_ev_t]
        let ⟨mem', h_ok, h_rd⟩ := copyReturn_ok rp c retTy v mem retPlace stPop
          h_init h_pop_mem h_pop_dr h_pop_pmd h_sm h_ret_res
        rw [h_step_copy_ok _ h_ok]
        dsimp only
        rw [h_pop_fr]
        exact ⟨_, rfl, by dsimp only; rw [h_pop_fr]; rfl, h_rd, h_pop_cm⟩

private theorem bvToInt_eq_toInt {n : Nat} (x : BitVec n) :
    bvToInt x = x.toInt := rfl

private theorem bitVec_ofNat_toNat_128 (x : BitVec 128) :
    BitVec.ofNat 128 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

private theorem compareSwitchCase_scalar_ref_eq (rp : RefProg) (c : Choice)
    (w : IntWidth) (s : Bool) (bits caseBits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : truncateBits w bits = bits) :
    let h := refExecCfg rp
    let val : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromScalarInt (miriScalar w bits)),
        refLocalLayoutForTy rp.types (.int w s)⟩
    let res : Miri.Interpreter.StepResult
        (Miri.Interpreter.MachineHooks.State Unit RefUser) Bool :=
      Miri.Interpreter.MachineHooks.run
        (EStateM.bind
          (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              (BitVec.ofNat 128 caseBits.toNat) val.layout.layout.size).mapError
              Miri.Interpreter.ScalarOps.scalarError with
           | .ok v => EStateM.pure v | .error e => EStateM.throw e)
          (fun caseScalar =>
            EStateM.bind
              (Miri.Interpreter.ScalarOps.binary
                (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
                val ⟨.scalar caseScalar, val.layout⟩)
              (fun result =>
                EStateM.bind
                  (match result.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError with
                   | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                  (fun sc =>
                    match sc.toBool.mapError Miri.Interpreter.ScalarOps.scalarError with
                    | .ok v => EStateM.pure v | .error e => EStateM.throw e))))
        st
    if truncateBits w caseBits != caseBits then
      ∃ err, res = (st, .error err) ∧ stepErrorFaultKind err = some .unsupported
    else
      res = (st, .ok (truncateBits w bits == truncateBits w caseBits)) := by
  intro h val res
  have h_sz : val.layout.layout.size = toMiriSize w := by
    cases w <;> cases s <;> rfl
  have h_from :
      Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
        (BitVec.ofNat 128 caseBits.toNat) val.layout.layout.size =
      if truncateBits w caseBits != caseBits then
        .error (.scalarInt (.integerConversionOverflow caseBits.toNat))
      else
        .ok (.fromScalarInt (miriScalar w caseBits)) := by
    rw [bitVec_ofNat_toNat_128, h_sz]
    dsimp only [Miri.Memory.Scalar.fromUInt]
    rw [tryFromUInt_eq_truncateFromUInt, truncateFromUInt_eq_miriScalar w caseBits]
    cases h_ne : (truncateBits w caseBits != caseBits) with
    | true => rfl
    | false => rfl
  cases h_ne : (truncateBits w caseBits != caseBits) with
  | true =>
    rw [h_ne] at h_from
    dsimp only [ite_true_eq] at h_from
    dsimp only [ite_true_eq]
    refine ⟨Miri.Interpreter.ScalarOps.scalarError (.scalarInt (.integerConversionOverflow caseBits.toNat)), ?_, rfl⟩
    dsimp only [res, Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    rw [h_from]
    rfl
  | false =>
    rw [h_ne] at h_from
    dsimp only [ite_false_eq] at h_from
    dsimp only [ite_false_eq]
    have h_ceq := truncateBits_eq_of_beq_false h_ne
    have h_lwf : ({ width := w, signed := s, bits := bits } : ScalarVal).wf = true := by
      dsimp only [ScalarVal.wf]; rw [h_tr, beq_self_eq_true]
    have h_lcv : checkVal (.scalar ⟨w, s, bits⟩) (.int w s) = true := by
      dsimp only [checkVal, Val.ty?]
      rw [h_lwf, ite_true_eq]
      dsimp only [MirTy.beq]
      rw [IntWidth.beq_refl]; cases s <;> rfl
    have h_rwf : ({ width := w, signed := s, bits := caseBits } : ScalarVal).wf = true := by
      dsimp only [ScalarVal.wf]; rw [h_ceq, beq_self_eq_true]
    have h_rcv : checkVal (.scalar ⟨w, s, caseBits⟩) (.int w s) = true := by
      dsimp only [checkVal, Val.ty?]
      rw [h_rwf, ite_true_eq]
      dsimp only [MirTy.beq]
      rw [IntWidth.beq_refl]; cases s <;> rfl
    have h_bin := scalarOps_binary_ref_eq rp c .eq (.int w s) (.int w s)
      (.scalar ⟨w, s, bits⟩) (.scalar ⟨w, s, caseBits⟩) st h_lcv rfl h_rcv rfl
      (resolveTy_tyIdFor_int rp.types w s)
    have h_ev : evalBinOp .eq (.scalar ⟨w, s, bits⟩) (.scalar ⟨w, s, caseBits⟩) =
        .ok (.bool (truncateBits w bits == truncateBits w caseBits)) := by
      dsimp only [evalBinOp]
      rw [IntWidth.beq_refl, beq_self_eq_true, Bool.and_self]
      change Except.ok (Val.bool
        (decodeScalar { width := w, signed := s, bits := bits } ==
         decodeScalar { width := w, signed := s, bits := caseBits })) = _
      rw [decodeScalar_beq_eq]
    rw [h_ev] at h_bin
    let ⟨resTy, h_res_cv, _, h_ok_bin⟩ := h_bin
    have h_rty : resTy = .bool := by
      dsimp only [checkVal, Val.ty?] at h_res_cv
      exact (MirTy.eq_of_beq h_res_cv).symm
    subst h_rty
    dsimp only [res, h, val, Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    rw [h_from]
    dsimp only [Except.mapError]
    rw [eStateM_bind_pure]
    dsimp only [toMiriBinOp, valToMiriImmediate] at h_ok_bin
    rw [eStateM_bind_ok h_ok_bin]
    cases (truncateBits w bits == truncateBits w caseBits) <;> rfl

private theorem scalarOps_classify_bool' (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).classify c
        (tyIdFor rp.types .bool) st = .ok .boolean st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
    Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refScalarLeaves]
  rw [resolveTy_tyIdFor_of_aux (code := 0) rfl]

private theorem eStateM_bind_congr {ε σ α β : Type}
    {x y : EStateM ε σ α} {f g : α → EStateM ε σ β} {s : σ}
    (hx : x s = y s) (hf : ∀ a s', f a s' = g a s') :
    EStateM.bind x f s = EStateM.bind y g s := by
  dsimp only [EStateM.bind]
  rw [hx]
  cases y s with
  | error _ _ => rfl
  | ok a s' => exact hf a s'

private theorem compareSwitchCase_bool_ref_eq (rp : RefProg) (c : Choice)
    (b : Bool) (caseBits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    let h := refExecCfg rp
    let val : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromBool b), refLocalLayoutForTy rp.types .bool⟩
    let res : Miri.Interpreter.StepResult
        (Miri.Interpreter.MachineHooks.State Unit RefUser) Bool :=
      Miri.Interpreter.MachineHooks.run
        (EStateM.bind
          (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              (BitVec.ofNat 128 caseBits.toNat) val.layout.layout.size).mapError
              Miri.Interpreter.ScalarOps.scalarError with
           | .ok v => EStateM.pure v | .error e => EStateM.throw e)
          (fun caseScalar =>
            EStateM.bind
              (Miri.Interpreter.ScalarOps.binary
                (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
                val ⟨.scalar caseScalar, val.layout⟩)
              (fun result =>
                EStateM.bind
                  (match result.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError with
                   | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                  (fun sc =>
                    match sc.toBool.mapError Miri.Interpreter.ScalarOps.scalarError with
                    | .ok v => EStateM.pure v | .error e => EStateM.throw e))))
        st
    match evalConstLit .bool (.scalar caseBits) with
    | .error k =>
      ∃ err, res = (st, .error err) ∧ stepErrorFaultKind err = some k
    | .ok (.bool cb) =>
      res = (st, .ok (b == cb))
    | .ok _ => False := by
  intro h val res
  have h_from :
      Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
        (BitVec.ofNat 128 caseBits.toNat) val.layout.layout.size =
      if truncateBits .i8 caseBits != caseBits then
        .error (.scalarInt (.integerConversionOverflow caseBits.toNat))
      else
        .ok (.fromScalarInt (miriScalar .i8 caseBits)) := by
    rw [bitVec_ofNat_toNat_128]
    have h_sz : val.layout.layout.size = toMiriSize .i8 := rfl
    rw [h_sz]
    dsimp only [Miri.Memory.Scalar.fromUInt]
    rw [tryFromUInt_eq_truncateFromUInt, truncateFromUInt_eq_miriScalar .i8 caseBits]
    cases h_ne : (truncateBits .i8 caseBits != caseBits) with
    | true => rfl
    | false => rfl
  dsimp only [evalConstLit]
  cases h_ne : (truncateBits .i8 caseBits != caseBits) with
  | true =>
    rw [h_ne] at h_from
    dsimp only [ite_true_eq] at h_from
    dsimp only [ite_true_eq]
    refine ⟨Miri.Interpreter.ScalarOps.scalarError (.scalarInt (.integerConversionOverflow caseBits.toNat)), ?_, rfl⟩
    dsimp only [res, Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    rw [h_from]
    rfl
  | false =>
    rw [h_ne] at h_from
    dsimp only [ite_false_eq] at h_from
    dsimp only [ite_false_eq]
    have h_step_bin :
        Miri.Interpreter.ScalarOps.binary
          (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
          val ⟨.scalar (.fromScalarInt (miriScalar .i8 caseBits)), val.layout⟩ st =
        let v := UInt8.ofNat (truncateBits .i8 caseBits).toNat
        if v == 0 then
          .ok ⟨.scalar (.fromBool (b == false)), refLocalLayoutForTy rp.types .bool⟩ st
        else if v == 1 then
          .ok ⟨.scalar (.fromBool (b == true)), refLocalLayoutForTy rp.types .bool⟩ st
        else
          .error (Miri.Interpreter.ScalarOps.scalarError (.scalarInt (.invalidBool v))) st := by
      dsimp only [Miri.Interpreter.ScalarOps.binary, bind, Bind.bind, val]
      change (EStateM.bind
        ((Miri.Interpreter.ExecutionMachine.scalarHooks h).classify c (tyIdFor rp.types .bool))
        _ st) = _
      rw [eStateM_bind_ok (scalarOps_classify_bool' rp c st)]
      dsimp only
      change (EStateM.bind
        (if (tyIdFor rp.types .bool == tyIdFor rp.types .bool) = true then
          EStateM.pure ()
        else EStateM.throw (StepError.invalidProgram "asymmetric scalar operand types")) _ st) = _
      rw [beq_self_eq_true, ite_true_eq, eStateM_bind_pure]
      have h_r_tobool :
          (Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
            (miriScalar .i8 caseBits)).toBool =
          let v := UInt8.ofNat (truncateBits .i8 caseBits).toNat
          if v == 0 then .ok false
          else if v == 1 then .ok true
          else .error (.scalarInt (.invalidBool v)) := by
        dsimp only [Miri.Memory.Scalar.toBool, Miri.Memory.Scalar.toUInt8,
          Miri.Memory.Scalar.toUInt, Miri.Memory.Scalar.toBits,
          Miri.Memory.Scalar.toScalarInt, Miri.Memory.Scalar.tryToScalarInt,
          Miri.Memory.Scalar.fromScalarInt, Miri.Memory.ScalarInt.tryToBool,
          Miri.Memory.ScalarInt.toUInt8, bind, Bind.bind, Except.bind,
          pure, Pure.pure, Except.pure]
        have h_u8 :
            (miriScalar .i8 caseBits).toBits (Miri.ABI.Size.ofBytes 1) =
              .ok (truncateBits .i8 caseBits) :=
          miriScalar_toUInt .i8 caseBits
        rw [h_u8]
        have h10 : ((Miri.ABI.Size.ofBytes 1).bytes == 0) = false := rfl
        rw [h10, ite_false_eq]
        dsimp only [Except.mapError]
        cases h0 : (UInt8.ofNat (truncateBits .i8 caseBits).toNat == 0) with
        | true => simp only [ite_true]
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          cases h1 : (UInt8.ofNat (truncateBits .i8 caseBits).toNat == 1) with
          | true => simp only [ite_true]
          | false => simp only [Bool.false_eq_true, ite_false]; rfl
      cases b with
      | false =>
        change (EStateM.bind (EStateM.pure _) _ st) = _
        rw [eStateM_bind_pure]
        change (EStateM.bind (EStateM.pure _) _ st) = _
        rw [eStateM_bind_pure]
        change (EStateM.bind (EStateM.pure false) _ st) = _
        rw [eStateM_bind_pure]
        rw [h_r_tobool]
        dsimp only
        cases h0 : (UInt8.ofNat (truncateBits .i8 caseBits).toNat == 0) with
        | true => simp only [ite_true]; rfl
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          cases h1 : (UInt8.ofNat (truncateBits .i8 caseBits).toNat == 1) with
          | true => simp only [ite_true]; rfl
          | false => simp only [Bool.false_eq_true, ite_false]; rfl
      | true =>
        change (EStateM.bind (EStateM.pure _) _ st) = _
        rw [eStateM_bind_pure]
        change (EStateM.bind (EStateM.pure _) _ st) = _
        rw [eStateM_bind_pure]
        change (EStateM.bind (EStateM.pure true) _ st) = _
        rw [eStateM_bind_pure]
        rw [h_r_tobool]
        dsimp only
        cases h0 : (UInt8.ofNat (truncateBits .i8 caseBits).toNat == 0) with
        | true => simp only [ite_true]; rfl
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          cases h1 : (UInt8.ofNat (truncateBits .i8 caseBits).toNat == 1) with
          | true => simp only [ite_true]; rfl
          | false => simp only [Bool.false_eq_true, ite_false]; rfl
    dsimp only [res, Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    rw [h_from]
    dsimp only [Except.mapError]
    rw [eStateM_bind_pure]
    cases h0 : (UInt8.ofNat (truncateBits .i8 caseBits).toNat == 0) with
    | true =>
      dsimp only at h_step_bin
      rw [h0, ite_true_eq] at h_step_bin
      dsimp only [ite_true_eq]
      rw [eStateM_bind_ok h_step_bin]
      cases b <;> rfl
    | false =>
      dsimp only at h_step_bin
      rw [h0, ite_false_eq] at h_step_bin
      dsimp only [ite_false_eq]
      cases h1 : (UInt8.ofNat (truncateBits .i8 caseBits).toNat == 1) with
      | true =>
        rw [h1, ite_true_eq] at h_step_bin
        dsimp only [ite_true_eq]
        rw [eStateM_bind_ok h_step_bin]
        cases b <;> rfl
      | false =>
        rw [h1, ite_false_eq] at h_step_bin
        dsimp only [ite_false_eq]
        rw [eStateM_bind_err h_step_bin]
        exact ⟨_, rfl, rfl⟩

private theorem forIn_list_map_congr {α β σ : Type} (l : List α) (init : σ)
    (m : α → β) (f g : β → σ → Id (ForInStep σ))
    (h : ∀ x s, f (m x) s = g (m x) s) :
    forIn (m := Id) (l.map m) init f = forIn (m := Id) (l.map m) init g := by
  induction l generalizing init with
  | nil => rfl
  | cons a tl ih =>
    rw [List.map_cons, List.forIn_cons, List.forIn_cons, h]
    cases g (m a) init with
    | done s => rfl
    | yield s => exact ih s

private theorem evalConstLit_bool_scalar_is_bool (bits : BitVec 128) (v : Val)
    (h : evalConstLit .bool (.scalar bits) = .ok v) :
    ∃ cb : Bool, v = .bool cb := by
  dsimp only [evalConstLit] at h
  cases h1 : (truncateBits .i8 bits != bits) with
  | true => simp [h1] at h
  | false =>
    simp only [h1, Bool.false_eq_true, ite_false] at h
    cases h2 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 0) with
    | true =>
      simp only [h2, ite_true] at h
      injection h with hv
      exact ⟨false, hv.symm⟩
    | false =>
      simp only [h2, Bool.false_eq_true, ite_false] at h
      cases h3 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 1) with
      | true =>
        simp only [h3, ite_true] at h
        injection h with hv
        exact ⟨true, hv.symm⟩
      | false => simp [h3] at h

private theorem evalSwitchBranches_error_eq_unsupported (w : IntWidth)
    (bits : BitVec 128) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) (k : FaultKind)
    (h : evalSwitchBranches w bits otherwise branches = .error k) :
    k = .unsupported := by
  induction branches with
  | nil => dsimp only [evalSwitchBranches] at h; cases h
  | cons hd rest ih =>
    cases hd with
    | mk cb tgt =>
      dsimp only [evalSwitchBranches] at h
      cases h1 : (truncateBits w cb != cb) with
      | true => simp [h1] at h; exact h.symm
      | false =>
        simp only [h1, Bool.false_eq_true, ite_false] at h
        cases h2 : (truncateBits w bits == truncateBits w cb) with
        | true => simp [h2] at h
        | false =>
          simp only [h2, Bool.false_eq_true, ite_false] at h
          exact ih h

private abbrev MiriStepState :=
  Miri.Interpreter.MachineHooks.State Unit RefUser

private theorem switchInt_forIn_cons {st : MiriStepState}
    (cmp : Nat → MiriStepState → Miri.Interpreter.StepResult MiriStepState Bool)
    (caseBits : BitVec 128) (target otherwise : BasicBlockId)
    (rest : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (((caseBits, target) :: rest).map
        (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult MiriStepState Unit)),
        st, otherwise)
      (fun case __s =>
        have __s := __s.snd
        have state := __s.fst
        have target := __s.snd
        match case with
        | Miri.MIR.SwitchTarget.Case bits block =>
          match cmp bits state with
          | (next, comparison) =>
            have state := next
            match comparison with
            | Except.error error =>
              pure (ForInStep.done
                (some (state, Except.error error), state, target))
            | Except.ok true =>
              have target := block
              pure (ForInStep.done (none, state, target))
            | Except.ok false =>
              pure (ForInStep.yield (none, state, target))) =
    match cmp caseBits.toNat st with
    | (next, Except.error error) =>
      (some (next, Except.error error), next, otherwise)
    | (next, Except.ok true) => (none, next, target)
    | (next, Except.ok false) =>
      forIn (m := Id)
        (rest.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
        ((none : Option (Miri.Interpreter.StepResult MiriStepState Unit)),
          next, otherwise)
        (fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match cmp bits state with
            | (next, comparison) =>
              have state := next
              match comparison with
              | Except.error error =>
                pure (ForInStep.done
                  (some (state, Except.error error), state, target))
              | Except.ok true =>
                have target := block
                pure (ForInStep.done (none, state, target))
              | Except.ok false =>
                pure (ForInStep.yield (none, state, target))) := by
  rw [List.map_cons, List.forIn_cons]
  dsimp only [Bind.bind, Pure.pure, Id.run]
  cases cmp caseBits.toNat st with
  | mk next comparison =>
    cases comparison with
    | error _ => rfl
    | ok flag => cases flag <;> rfl

private theorem switchInt_forIn_scalar (rp : RefProg) (c : Choice)
    (st : MiriStepState) (w : IntWidth) (s : Bool) (bits : BitVec 128)
    (otherwise : BasicBlockId) (branches : List (BitVec 128 × BasicBlockId))
    (h_tr : truncateBits w bits = bits) :
    let h := refExecCfg rp
    let val : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromScalarInt (miriScalar w bits)),
        refLocalLayoutForTy rp.types (.int w s)⟩
    let cmp : Nat → MiriStepState → Miri.Interpreter.StepResult MiriStepState Bool :=
      fun caseNat state =>
        Miri.Interpreter.MachineHooks.run
          (EStateM.bind
            (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                (BitVec.ofNat 128 caseNat) val.layout.layout.size).mapError
                Miri.Interpreter.ScalarOps.scalarError with
             | .ok v => EStateM.pure v | .error e => EStateM.throw e)
            (fun caseScalar =>
              EStateM.bind
                (Miri.Interpreter.ScalarOps.binary
                  (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
                  val ⟨.scalar caseScalar, val.layout⟩)
                (fun result =>
                  EStateM.bind
                    (match result.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError with
                     | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                    (fun sc =>
                      match sc.toBool.mapError Miri.Interpreter.ScalarOps.scalarError with
                      | .ok v => EStateM.pure v | .error e => EStateM.throw e))))
          state
    let loopRes :=
      forIn (m := Id)
        (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
        ((none : Option (Miri.Interpreter.StepResult MiriStepState Unit)),
          st, otherwise)
        (fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match cmp bits state with
            | (next, comparison) =>
              have state := next
              match comparison with
              | Except.error error =>
                pure (ForInStep.done
                  (some (state, Except.error error), state, target))
              | Except.ok true =>
                have target := block
                pure (ForInStep.done (none, state, target))
              | Except.ok false =>
                pure (ForInStep.yield (none, state, target)))
    match evalSwitchBranches w bits otherwise branches with
    | .error k =>
      ∃ err, loopRes = (some (st, .error err), st, otherwise) ∧
        stepErrorFaultKind err = some k
    | .ok target =>
      loopRes = (none, st, target) := by
  intro h val cmp
  induction branches with
  | nil =>
    dsimp only [evalSwitchBranches]
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest ih =>
    cases hd with
    | mk caseBits target =>
      dsimp only
      rw [switchInt_forIn_cons (cmp := cmp)]
      have h_cmp := compareSwitchCase_scalar_ref_eq rp c w s bits caseBits st h_tr
      dsimp only [evalSwitchBranches]
      cases h_ne : (truncateBits w caseBits != caseBits) with
      | true =>
        rw [h_ne] at h_cmp
        dsimp only [ite_true_eq] at h_cmp
        dsimp only [ite_true_eq]
        let ⟨err, h_err, h_fk⟩ := h_cmp
        dsimp only [cmp]
        rw [h_err]
        exact ⟨err, rfl, h_fk⟩
      | false =>
        rw [h_ne] at h_cmp
        dsimp only [ite_false_eq] at h_cmp
        dsimp only [ite_false_eq]
        dsimp only [cmp]
        rw [h_cmp]
        cases (truncateBits w bits == truncateBits w caseBits) with
        | true => rfl
        | false => exact ih

private theorem switchInt_forIn_bool (rp : RefProg) (c : Choice)
    (st : MiriStepState) (b : Bool) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    let h := refExecCfg rp
    let val : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromBool b), refLocalLayoutForTy rp.types .bool⟩
    let cmp : Nat → MiriStepState → Miri.Interpreter.StepResult MiriStepState Bool :=
      fun caseNat state =>
        Miri.Interpreter.MachineHooks.run
          (EStateM.bind
            (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                (BitVec.ofNat 128 caseNat) val.layout.layout.size).mapError
                Miri.Interpreter.ScalarOps.scalarError with
             | .ok v => EStateM.pure v | .error e => EStateM.throw e)
            (fun caseScalar =>
              EStateM.bind
                (Miri.Interpreter.ScalarOps.binary
                  (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
                  val ⟨.scalar caseScalar, val.layout⟩)
                (fun result =>
                  EStateM.bind
                    (match result.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError with
                     | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                    (fun sc =>
                      match sc.toBool.mapError Miri.Interpreter.ScalarOps.scalarError with
                      | .ok v => EStateM.pure v | .error e => EStateM.throw e))))
          state
    let loopRes :=
      forIn (m := Id)
        (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
        ((none : Option (Miri.Interpreter.StepResult MiriStepState Unit)),
          st, otherwise)
        (fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match cmp bits state with
            | (next, comparison) =>
              have state := next
              match comparison with
              | Except.error error =>
                pure (ForInStep.done
                  (some (state, Except.error error), state, target))
              | Except.ok true =>
                have target := block
                pure (ForInStep.done (none, state, target))
              | Except.ok false =>
                pure (ForInStep.yield (none, state, target)))
    match evalBoolSwitchBranches b otherwise branches with
    | .error k =>
      ∃ err, loopRes = (some (st, .error err), st, otherwise) ∧
        stepErrorFaultKind err = some k
    | .ok target =>
      loopRes = (none, st, target) := by
  intro h val cmp
  induction branches with
  | nil =>
    dsimp only [evalBoolSwitchBranches]
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest ih =>
    cases hd with
    | mk caseBits target =>
      dsimp only
      rw [switchInt_forIn_cons (cmp := cmp)]
      have h_cmp := compareSwitchCase_bool_ref_eq rp c b caseBits st
      dsimp only [evalBoolSwitchBranches]
      cases h_cl : evalConstLit .bool (.scalar caseBits) with
      | error k =>
        rw [h_cl] at h_cmp
        let ⟨err, h_err, h_fk⟩ := h_cmp
        dsimp only [cmp]
        rw [h_err]
        exact ⟨err, rfl, h_fk⟩
      | ok v =>
        let ⟨cb, h_cb⟩ := evalConstLit_bool_scalar_is_bool caseBits v h_cl
        subst h_cb
        rw [h_cl] at h_cmp
        dsimp only [cmp]
        rw [h_cmp]
        cases cb <;> cases b
        · rfl
        · exact ih
        · exact ih
        · rfl

private theorem scalar_toChar_miriScalar_i32 (bits : BitVec 128)
    (h_tr : truncateBits .i32 bits = bits) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar .i32 bits)).toChar =
    if isUnicodeScalar bits.toNat then .ok (Char.ofNat bits.toNat)
    else .error (.scalarInt (.invalidChar (UInt32.ofNat bits.toNat))) := by
  dsimp only [Miri.Memory.Scalar.toChar, Miri.Memory.Scalar.toScalarInt,
    Miri.Memory.Scalar.tryToScalarInt, Miri.Memory.Scalar.fromScalarInt,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [miriScalar_i32_toChar h_tr]
  cases isUnicodeScalar bits.toNat <;> rfl

private theorem char_beq_eq_nat_beq (a b : Char) :
    (a == b) = Nat.beq a.toNat b.toNat := by
  cases h : Nat.beq a.toNat b.toNat with
  | true =>
    have h_eq : a = b :=
      Char.ext (UInt32.toNat_inj.mp (Nat.eq_of_beq_eq_true h))
    rw [h_eq]; exact beq_self_eq_true b
  | false =>
    apply beq_false_of_ne
    intro h_eq
    rw [h_eq, Nat.beq_refl] at h
    cases h

private theorem scalarOps_classify_char' (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .char) = some .char) :
    (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).classify c
        (tyIdFor rp.types .char) st = .ok .character st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
    Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refScalarLeaves]
  rw [h_res]

private theorem compareSwitchCase_char_ref_eq (rp : RefProg) (c : Choice)
    (ch : Char) (caseBits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .char) = some .char) :
    let h := refExecCfg rp
    let val : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromChar ch), refLocalLayoutForTy rp.types .char⟩
    let res : Miri.Interpreter.StepResult
        (Miri.Interpreter.MachineHooks.State Unit RefUser) Bool :=
      Miri.Interpreter.MachineHooks.run
        (EStateM.bind
          (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              (BitVec.ofNat 128 caseBits.toNat) val.layout.layout.size).mapError
              Miri.Interpreter.ScalarOps.scalarError with
           | .ok v => EStateM.pure v | .error e => EStateM.throw e)
          (fun caseScalar =>
            EStateM.bind
              (Miri.Interpreter.ScalarOps.binary
                (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
                val ⟨.scalar caseScalar, val.layout⟩)
              (fun result =>
                EStateM.bind
                  (match result.imm.toScalar.mapError
                      Miri.Interpreter.ScalarOps.immediateError with
                   | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                  (fun sc =>
                    match sc.toBool.mapError
                        Miri.Interpreter.ScalarOps.scalarError with
                    | .ok v => EStateM.pure v | .error e => EStateM.throw e))))
        st
    match evalConstLit .char (.scalar caseBits) with
    | .error k =>
      ∃ err, res = (st, .error err) ∧ stepErrorFaultKind err = some k
    | .ok (.char cc) =>
      res = (st, .ok (Nat.beq ch.toNat cc.toNat))
    | .ok _ => False := by
  intro h val res
  have h_from :
      Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
        (BitVec.ofNat 128 caseBits.toNat) val.layout.layout.size =
      if truncateBits .i32 caseBits != caseBits then
        .error (.scalarInt (.integerConversionOverflow caseBits.toNat))
      else
        .ok (.fromScalarInt (miriScalar .i32 caseBits)) := by
    rw [bitVec_ofNat_toNat_128]
    have h_sz : val.layout.layout.size = toMiriSize .i32 := rfl
    rw [h_sz]
    dsimp only [Miri.Memory.Scalar.fromUInt]
    rw [tryFromUInt_eq_truncateFromUInt,
      truncateFromUInt_eq_miriScalar .i32 caseBits]
    cases (truncateBits .i32 caseBits != caseBits) <;> rfl
  dsimp only [evalConstLit]
  cases h_ne : (truncateBits .i32 caseBits != caseBits) with
  | true =>
    rw [h_ne] at h_from
    dsimp only [ite_true_eq] at h_from
    dsimp only [ite_true_eq]
    refine ⟨Miri.Interpreter.ScalarOps.scalarError
      (.scalarInt (.integerConversionOverflow caseBits.toNat)), ?_, rfl⟩
    dsimp only [res, Miri.Interpreter.MachineHooks.run,
      Miri.Interpreter.Call.run]
    rw [h_from]
    rfl
  | false =>
    rw [h_ne] at h_from
    dsimp only [ite_false_eq] at h_from
    dsimp only [ite_false_eq]
    have h_tr := truncateBits_eq_of_beq_false h_ne
    have h_rc := scalar_toChar_miriScalar_i32 caseBits h_tr
    have h_step_bin :
        Miri.Interpreter.ScalarOps.binary
          (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
          val ⟨.scalar (.fromScalarInt (miriScalar .i32 caseBits)),
            val.layout⟩ st =
        if isUnicodeScalar caseBits.toNat then
          .ok ⟨.scalar (.fromBool (ch == Char.ofNat caseBits.toNat)),
            refLocalLayoutForTy rp.types .bool⟩ st
        else
          .error (Miri.Interpreter.ScalarOps.scalarError
            (.scalarInt (.invalidChar (UInt32.ofNat caseBits.toNat)))) st := by
      dsimp only [Miri.Interpreter.ScalarOps.binary, bind, Bind.bind, val]
      change (EStateM.bind
        ((Miri.Interpreter.ExecutionMachine.scalarHooks h).classify c
          (tyIdFor rp.types .char))
        _ st) = _
      rw [eStateM_bind_ok (scalarOps_classify_char' rp c st h_res)]
      dsimp only
      change (EStateM.bind
        (if (tyIdFor rp.types .char == tyIdFor rp.types .char) = true then
          EStateM.pure ()
        else EStateM.throw
          (StepError.invalidProgram "asymmetric scalar operand types"))
        _ st) = _
      rw [beq_self_eq_true, ite_true_eq, eStateM_bind_pure]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      rw [scalar_toChar_fromChar, h_rc]
      cases isUnicodeScalar caseBits.toNat <;> rfl
    dsimp only [res, Miri.Interpreter.MachineHooks.run,
      Miri.Interpreter.Call.run]
    rw [h_from]
    dsimp only [Except.mapError]
    rw [eStateM_bind_pure]
    cases h_u : isUnicodeScalar caseBits.toNat with
    | false =>
      rw [h_u, ite_false_eq] at h_step_bin
      dsimp only [ite_false_eq]
      rw [eStateM_bind_err h_step_bin]
      exact ⟨_, rfl, rfl⟩
    | true =>
      rw [h_u, ite_true_eq] at h_step_bin
      dsimp only [ite_true_eq]
      rw [eStateM_bind_ok h_step_bin, char_beq_eq_nat_beq]
      cases Nat.beq ch.toNat (Char.ofNat caseBits.toNat).toNat <;> rfl

private theorem scalar_fromUInt_toMiriSize (w : IntWidth) (v : BitVec 128) :
    Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance) v
        (toMiriSize w) =
      if truncateBits w v != v then
        .error (.scalarInt (.integerConversionOverflow v.toNat))
      else
        .ok (.fromScalarInt (miriScalar w v)) := by
  dsimp only [Miri.Memory.Scalar.fromUInt]
  rw [tryFromUInt_eq_truncateFromUInt, truncateFromUInt_eq_miriScalar w v]
  cases (truncateBits w v != v) <;> rfl

private theorem scalar_fromUInt_pair_err_unsupported (rp : RefProg)
    (w : IntWidth) (s : Bool) (v : BitVec 128) (e : ScalarError)
    (h : Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance) v
        (refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])).layout.size =
      .error e) :
    stepErrorFaultKind (Miri.Interpreter.ScalarOps.scalarError e) =
      some .unsupported := by
  have h_gen : ∀ w' : IntWidth,
      Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance) v
          (toMiriSize w') = .error e →
      stepErrorFaultKind (Miri.Interpreter.ScalarOps.scalarError e) =
        some .unsupported := by
    intro w' h'
    rw [scalar_fromUInt_toMiriSize] at h'
    cases h_ne : (truncateBits w' v != v) with
    | true =>
      rw [h_ne, ite_true_eq] at h'
      injection h' with h_e
      rw [← h_e]
      rfl
    | false =>
      rw [h_ne, ite_false_eq] at h'
      cases h'
  cases w with
  | i8 => exact h_gen .i16 h
  | i16 => exact h_gen .i32 h
  | i32 => exact h_gen .i64 h
  | i64 => exact h_gen .i128 h
  | isize => exact h_gen .i128 h
  | i128 =>
    have h32 : Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance) v
        (Miri.ABI.Size.ofBytes 32) =
        .error (.scalarInt (.sizeTooLarge (Miri.ABI.Size.ofBytes 32))) := rfl
    have h_sz : (refLocalLayoutForTy rp.types
        (.tuple [.int .i128 s, .bool])).layout.size =
        Miri.ABI.Size.ofBytes 32 := rfl
    rw [h_sz, h32] at h
    injection h with h_e
    rw [← h_e]
    rfl

private theorem scalarOps_classify_pair' (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (w : IntWidth) (s : Bool)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).classify c
        (tyIdFor rp.types (.tuple [.int w s, .bool])) st =
      .error (.invalidProgram "non-scalar operand type") st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
    Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refScalarLeaves]
  rw [h_res]

private theorem compareSwitchCase_pair_ref_eq (rp : RefProg) (c : Choice)
    (w : IntWidth) (s : Bool) (bits : BitVec 128) (b : Bool) (caseNat : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    let h := refExecCfg rp
    let val : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalarPair (.fromScalarInt (miriScalar w bits)) (.fromBool b),
        refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])⟩
    let res : Miri.Interpreter.StepResult
        (Miri.Interpreter.MachineHooks.State Unit RefUser) Bool :=
      Miri.Interpreter.MachineHooks.run
        (EStateM.bind
          (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
              (BitVec.ofNat 128 caseNat) val.layout.layout.size).mapError
              Miri.Interpreter.ScalarOps.scalarError with
           | .ok v => EStateM.pure v | .error e => EStateM.throw e)
          (fun caseScalar =>
            EStateM.bind
              (Miri.Interpreter.ScalarOps.binary
                (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
                val ⟨.scalar caseScalar, val.layout⟩)
              (fun result =>
                EStateM.bind
                  (match result.imm.toScalar.mapError
                      Miri.Interpreter.ScalarOps.immediateError with
                   | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                  (fun sc =>
                    match sc.toBool.mapError
                        Miri.Interpreter.ScalarOps.scalarError with
                    | .ok v => EStateM.pure v | .error e => EStateM.throw e))))
        st
    ∃ err, res = (st, .error err) ∧ stepErrorFaultKind err = some .unsupported := by
  intro h val res
  dsimp only [res, Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
  cases h_fu : Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
      (BitVec.ofNat 128 caseNat) val.layout.layout.size with
  | error e =>
    refine ⟨Miri.Interpreter.ScalarOps.scalarError e, rfl,
      scalar_fromUInt_pair_err_unsupported rp w s _ e h_fu⟩
  | ok caseScalar =>
    dsimp only [Except.mapError]
    rw [eStateM_bind_pure]
    have h_bin :
        Miri.Interpreter.ScalarOps.binary
          (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
          val ⟨.scalar caseScalar, val.layout⟩ st =
        .error (.invalidProgram "non-scalar operand type") st := by
      dsimp only [Miri.Interpreter.ScalarOps.binary, bind, Bind.bind, val]
      change (EStateM.bind
        ((Miri.Interpreter.ExecutionMachine.scalarHooks h).classify c
          (tyIdFor rp.types (.tuple [.int w s, .bool])))
        _ st) = _
      rw [eStateM_bind_err (scalarOps_classify_pair' rp c st w s h_res)]
    rw [eStateM_bind_err h_bin]
    exact ⟨_, rfl, rfl⟩


private theorem switchInt_forIn_char (rp : RefProg) (c : Choice)
    (st : MiriStepState) (ch : Char) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId))
    (h_res : resolveTy rp.types (tyIdFor rp.types .char) = some .char) :
    let h := refExecCfg rp
    let val : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromChar ch), refLocalLayoutForTy rp.types .char⟩
    let cmp : Nat → MiriStepState →
        Miri.Interpreter.StepResult MiriStepState Bool :=
      fun caseNat state =>
        Miri.Interpreter.MachineHooks.run
          (EStateM.bind
            (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                (BitVec.ofNat 128 caseNat) val.layout.layout.size).mapError
                Miri.Interpreter.ScalarOps.scalarError with
             | .ok v => EStateM.pure v | .error e => EStateM.throw e)
            (fun caseScalar =>
              EStateM.bind
                (Miri.Interpreter.ScalarOps.binary
                  (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
                  val ⟨.scalar caseScalar, val.layout⟩)
                (fun result =>
                  EStateM.bind
                    (match result.imm.toScalar.mapError
                        Miri.Interpreter.ScalarOps.immediateError with
                     | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                    (fun sc =>
                      match sc.toBool.mapError
                          Miri.Interpreter.ScalarOps.scalarError with
                      | .ok v => EStateM.pure v
                      | .error e => EStateM.throw e))))
          state
    let loopRes :=
      forIn (m := Id)
        (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
        ((none : Option (Miri.Interpreter.StepResult MiriStepState Unit)),
          st, otherwise)
        (fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match cmp bits state with
            | (next, comparison) =>
              have state := next
              match comparison with
              | Except.error error =>
                pure (ForInStep.done
                  (some (state, Except.error error), state, target))
              | Except.ok true =>
                have target := block
                pure (ForInStep.done (none, state, target))
              | Except.ok false =>
                pure (ForInStep.yield (none, state, target)))
    match evalCharSwitchBranches ch otherwise branches with
    | .error k =>
      ∃ err, loopRes = (some (st, .error err), st, otherwise) ∧
        stepErrorFaultKind err = some k
    | .ok target =>
      loopRes = (none, st, target) := by
  intro h val cmp
  induction branches with
  | nil =>
    dsimp only [evalCharSwitchBranches]
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest ih =>
    cases hd with
    | mk caseBits target =>
      dsimp only
      rw [switchInt_forIn_cons (cmp := cmp)]
      have h_cmp := compareSwitchCase_char_ref_eq rp c ch caseBits st h_res
      dsimp only [evalCharSwitchBranches]
      cases h_cl : evalConstLit .char (.scalar caseBits) with
      | error k =>
        rw [h_cl] at h_cmp
        let ⟨err, h_err, h_fk⟩ := h_cmp
        dsimp only [cmp]
        rw [h_err]
        exact ⟨err, rfl, h_fk⟩
      | ok v =>
        rw [h_cl] at h_cmp
        cases v with
        | char cc =>
          dsimp only [cmp]
          rw [h_cmp]
          cases Nat.beq ch.toNat cc.toNat
          · exact ih
          · rfl
        | scalar _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _ | range _ _
        | optionVal _ | bool _
        | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ =>
          exact False.elim h_cmp

private theorem switchInt_forIn_pair (rp : RefProg) (c : Choice)
    (st : MiriStepState) (w : IntWidth) (s : Bool) (bits : BitVec 128)
    (b : Bool) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId))
    (h_res : resolveTy rp.types (tyIdFor rp.types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    let h := refExecCfg rp
    let val : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalarPair (.fromScalarInt (miriScalar w bits)) (.fromBool b),
        refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])⟩
    let cmp : Nat → MiriStepState →
        Miri.Interpreter.StepResult MiriStepState Bool :=
      fun caseNat state =>
        Miri.Interpreter.MachineHooks.run
          (EStateM.bind
            (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                (BitVec.ofNat 128 caseNat) val.layout.layout.size).mapError
                Miri.Interpreter.ScalarOps.scalarError with
             | .ok v => EStateM.pure v | .error e => EStateM.throw e)
            (fun caseScalar =>
              EStateM.bind
                (Miri.Interpreter.ScalarOps.binary
                  (Miri.Interpreter.ExecutionMachine.scalarHooks h) c .Eq
                  val ⟨.scalar caseScalar, val.layout⟩)
                (fun result =>
                  EStateM.bind
                    (match result.imm.toScalar.mapError
                        Miri.Interpreter.ScalarOps.immediateError with
                     | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                    (fun sc =>
                      match sc.toBool.mapError
                          Miri.Interpreter.ScalarOps.scalarError with
                      | .ok v => EStateM.pure v
                      | .error e => EStateM.throw e))))
          state
    let loopRes :=
      forIn (m := Id)
        (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
        ((none : Option (Miri.Interpreter.StepResult MiriStepState Unit)),
          st, otherwise)
        (fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match cmp bits state with
            | (next, comparison) =>
              have state := next
              match comparison with
              | Except.error error =>
                pure (ForInStep.done
                  (some (state, Except.error error), state, target))
              | Except.ok true =>
                have target := block
                pure (ForInStep.done (none, state, target))
              | Except.ok false =>
                pure (ForInStep.yield (none, state, target)))
    match branches with
    | [] => loopRes = (none, st, otherwise)
    | _ :: _ =>
      ∃ err, loopRes = (some (st, .error err), st, otherwise) ∧
        stepErrorFaultKind err = some .unsupported := by
  intro h val cmp
  cases branches with
  | nil =>
    dsimp only
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest =>
    cases hd with
    | mk caseBits target =>
      dsimp only
      rw [switchInt_forIn_cons (cmp := cmp)]
      let ⟨err, h_err, h_fk⟩ :=
        compareSwitchCase_pair_ref_eq rp c w s bits b caseBits.toNat st h_res
      dsimp only [cmp]
      rw [h_err]
      exact ⟨err, rfl, h_fk⟩

noncomputable def termCacheTouch : TerminatorKind → List Bool → List Bool
  | .switchInt discr _, cache => operandCacheTouch cache discr
  | .assert cond _ _ _ _, cache => operandCacheTouch cache cond
  | _, cache => cache

private theorem goToBlock_mkGenSimState (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx tgt : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (h_loc : ctx.locOverride = none) :
    Miri.Interpreter.ControlFlow.goToBlock tgt
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) =
      (mkGenSimState rp ctx rbody tgt 0 bodyLocals slots cache mem ctrl cm, .ok ()) := by
  dsimp only [Miri.Interpreter.ControlFlow.goToBlock,
    Miri.Interpreter.ControlFlow.setLocation, mkGenSimState, mkRefMiriStackState]
  rw [stack_currentFrame?_push]
  dsimp only
  rw [array_pop_push_eq]
  dsimp only [mkGenSimFrame]
  rw [h_loc]

private theorem assertConditionTypesValid_cond_bool {body : Body}
    {bb : BasicBlock} {blockIdx : BasicBlockId} {slots slots1 : List LocalSlot}
    {amem amem1 : MemoryState} {cond : Operand} {expected : Bool}
    {msg : AssertKind} {target : BasicBlockId} {unwind : UnwindAction}
    {condVal : Val}
    (h_act : assertConditionTypesValid body = true)
    (h_bb : MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (h_term : bb.terminator = .assert cond expected msg target unwind)
    (h_inv : SlotsMatchTys body.locals slots)
    (h_p : evalPrimitiveOperand body.locals slots amem cond =
      .ok (condVal, slots1, amem1)) :
    ∃ b : Bool, condVal = .bool b := by
  have h_bb_ok := list_all_mirGetElem? h_act h_bb
  rw [h_term] at h_bb_ok
  dsimp only [evalPrimitiveOperand] at h_p
  cases h_eos : evalOperandToSlot body.locals slots amem
      isPrimitiveReadableTy cond with
  | error _ => rw [h_eos] at h_p; cases h_p
  | ok tup =>
    cases tup with | mk ty rest =>
    cases rest with | mk optVal rest₂ =>
    cases rest₂ with | mk slots' mem' =>
    rw [h_eos] at h_p
    dsimp only at h_p
    cases h_pr : isPrimitiveReadableTy ty with
    | false => rw [h_pr] at h_p; cases h_p
    | true =>
      rw [h_pr] at h_p
      dsimp only [Bool.not, ite_false_eq] at h_p
      cases optVal with
      | none => cases h_p
      | some v =>
        injection h_p with htup
        injection htup with hv_eq _
        subst hv_eq
        let ⟨_, h_sm, _⟩ := evalOperandToSlot_slotsMatchTys h_inv h_eos
        have h_cv : checkVal v ty = true := h_sm
        have h_ty_bool : ty = .bool := by
          cases cond with
          | copy p =>
            dsimp only [evalOperandToSlot] at h_eos
            cases h_l : MirSemantics.getElem? body.locals p.localId with
            | none => rw [h_l] at h_eos; cases h_eos
            | some lt =>
              rw [h_l] at h_eos
              cases h_s : MirSemantics.getElem? slots p.localId with
              | none => rw [h_s] at h_eos; cases h_eos
              | some sl =>
                rw [h_s] at h_eos
                cases sl with
                | dead => cases h_eos
                | immediate _ =>
                  cases h_pe : p.projection.isEmpty with
                  | false => rw [h_pe] at h_eos; cases h_eos
                  | true =>
                    rw [h_pe] at h_eos
                    injection h_eos with h_e
                    injection h_e with h_teq _
                    dsimp only at h_bb_ok
                    rw [h_pe, h_l] at h_bb_ok
                    dsimp only at h_bb_ok
                    exact (MirTy.eq_of_beq h_bb_ok) ▸ h_teq.symm
                | indirect _ =>
                  cases h_pe : p.projection.isEmpty with
                  | false => rw [h_pe] at h_eos; cases h_eos
                  | true =>
                    rw [h_pe] at h_eos
                    dsimp only [Bool.not, ite_false_eq] at h_eos
                    cases h_ok : isPrimitiveReadableTy lt with
                    | false => rw [h_ok] at h_eos; cases h_eos
                    | true =>
                      rw [h_ok] at h_eos
                      dsimp only [Bool.not, ite_false_eq] at h_eos
                      cases h_ld : loadIndirect amem lt _ with
                      | error _ => rw [h_ld] at h_eos; cases h_eos
                      | ok _ =>
                        rw [h_ld] at h_eos
                        injection h_eos with h_e
                        injection h_e with h_teq _
                        dsimp only at h_bb_ok
                        rw [h_pe, h_l] at h_bb_ok
                        dsimp only at h_bb_ok
                        exact (MirTy.eq_of_beq h_bb_ok) ▸ h_teq.symm
                | partialTuple _ => cases h_eos
          | move p =>
            dsimp only [evalOperandToSlot] at h_eos
            cases h_l : MirSemantics.getElem? body.locals p.localId with
            | none => rw [h_l] at h_eos; cases h_eos
            | some lt =>
              rw [h_l] at h_eos
              cases h_s : MirSemantics.getElem? slots p.localId with
              | none => rw [h_s] at h_eos; cases h_eos
              | some sl =>
                rw [h_s] at h_eos
                cases sl with
                | dead => cases h_eos
                | immediate _ =>
                  cases h_pe : p.projection.isEmpty with
                  | false => rw [h_pe] at h_eos; cases h_eos
                  | true =>
                    rw [h_pe] at h_eos
                    dsimp only [Bool.not, ite_false_eq] at h_eos
                    cases h_st : MirSemantics.setElem? slots p.localId
                        (liveUninitSlot lt) with
                    | none => rw [h_st] at h_eos; cases h_eos
                    | some _ =>
                      rw [h_st] at h_eos
                      injection h_eos with h_e
                      injection h_e with h_teq _
                      dsimp only at h_bb_ok
                      rw [h_pe, h_l] at h_bb_ok
                      dsimp only at h_bb_ok
                      exact (MirTy.eq_of_beq h_bb_ok) ▸ h_teq.symm
                | indirect _ =>
                  cases h_pe : p.projection.isEmpty with
                  | false => rw [h_pe] at h_eos; cases h_eos
                  | true =>
                    rw [h_pe] at h_eos
                    dsimp only [Bool.not, ite_false_eq] at h_eos
                    cases h_ok : isPrimitiveReadableTy lt with
                    | false => rw [h_ok] at h_eos; cases h_eos
                    | true =>
                      rw [h_ok] at h_eos
                      dsimp only [Bool.not, ite_false_eq] at h_eos
                      cases h_ld : loadIndirect amem lt _ with
                      | error _ => rw [h_ld] at h_eos; cases h_eos
                      | ok _ =>
                        rw [h_ld] at h_eos
                        dsimp only at h_eos
                        cases h_di : deinitIndirect amem lt _ with
                        | error _ => rw [h_di] at h_eos; cases h_eos
                        | ok _ =>
                          rw [h_di] at h_eos
                          injection h_eos with h_e
                          injection h_e with h_teq _
                          dsimp only at h_bb_ok
                          rw [h_pe, h_l] at h_bb_ok
                          dsimp only at h_bb_ok
                          exact (MirTy.eq_of_beq h_bb_ok) ▸ h_teq.symm
                | partialTuple _ => cases h_eos
          | constant c =>
            dsimp only [evalOperandToSlot] at h_eos
            cases h_ec : evalConstLit c.ty c.lit with
            | error _ => rw [h_ec] at h_eos; cases h_eos
            | ok _ =>
              rw [h_ec] at h_eos
              injection h_eos with h_e
              injection h_e with h_teq _
              dsimp only at h_bb_ok
              exact (MirTy.eq_of_beq h_bb_ok) ▸ h_teq.symm
        rw [h_ty_bool] at h_cv
        exact checkVal_bool_inv h_cv

private noncomputable def refAssertPanicHooks (rp : RefProg) :
    Miri.Interpreter.Panic.Hooks Unit RefUser Choice Unit := {
  driver := Miri.Interpreter.FunctionCalls.bindUnwind
    (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).panic.driver
    (Miri.Interpreter.ExecutionCalls.helpers
      (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).helpers
      (Miri.Interpreter.ExecutionMachine.callHooks (refExecutionConfig rp) refLimits))
  allocateStringDedup :=
    (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).panic.allocateStringDedup
  toImmediatePointer :=
    (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).panic.toImmediatePointer
  langItem :=
    (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).panic.langItem
  genericParameters :=
    (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).panic.genericParameters
  evalOperand := fun c op => Miri.Interpreter.OperandMachine.evalOperand
    (Miri.Interpreter.ExecutionMachine.operandHooks
      (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits)) c op none
  evalOperandAt := fun c path op => Miri.Interpreter.OperandMachine.evalOperandAt
    (Miri.Interpreter.ExecutionMachine.operandHooks
      (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits)) c path op none
}

private noncomputable def safePanicMono (rp : RefProg) (c : Choice)
    (item : Miri.Interpreter.Panic.LangItem) :
    Miri.Interpreter.MachineHooks.M Unit RefUser
      Miri.Interpreter.CallInstance :=
  Bind.bind ((refAssertPanicHooks rp).langItem c item) fun __x =>
    match __x with
    | some definition =>
      have args : Array Miri.MIR.GenericArg := List.toArray List.nil
      Bind.bind ((refAssertPanicHooks rp).genericParameters c definition)
        fun (__do_lift : Array Miri.Interpreter.MainGenericParameter) =>
          Bind.bind
            (ForIn.forIn __do_lift args
              fun (parameter : Miri.Interpreter.MainGenericParameter)
                  (__s : Array Miri.MIR.GenericArg) =>
                have args : Array Miri.MIR.GenericArg := __s
                match parameter with
                | .lifetime =>
                  have args : Array Miri.MIR.GenericArg :=
                    args.push (.Lifetime .Erased)
                  Pure.pure (ForInStep.yield args)
                | .typeParameter =>
                  Bind.bind
                    (MonadExcept.throw
                      (.invalidProgram
                        "Instance::mono called on type/const generic panic item") :
                      Miri.Interpreter.MachineHooks.M Unit RefUser Unit)
                    fun (_ : Unit) => Pure.pure (ForInStep.yield args)
                | .constParameter =>
                  Bind.bind
                    (MonadExcept.throw
                      (.invalidProgram
                        "Instance::mono called on type/const generic panic item") :
                      Miri.Interpreter.MachineHooks.M Unit RefUser Unit)
                    fun (_ : Unit) => Pure.pure (ForInStep.yield args))
            fun (__s : Array Miri.MIR.GenericArg) =>
              have args : Array Miri.MIR.GenericArg := __s
              Pure.pure ⟨.Item definition, args⟩
    | _ => MonadExcept.throw (.invalidProgram "missing panic language item")

private noncomputable def safePanicCall (rp : RefProg) (c : Choice)
    (item : Miri.Interpreter.Panic.LangItem)
    (args : Array (Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance))
    (unwind : Miri.MIR.UnwindAction)
    (st₁ : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    Miri.Interpreter.MachineHooks.State Unit RefUser ×
      Except Miri.Interpreter.StepError Unit :=
  Miri.Interpreter.MachineHooks.run
    (Bind.bind (safePanicMono rp c item) fun fnInstance =>
      (refAssertPanicHooks rp).driver.callFunction c fnInstance args
        (.goto none unwind))
    st₁

private theorem evalOperandAt_dummy_isize (rp : RefProg) (c : Choice)
    (pathField : String)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    (refAssertPanicHooks rp).evalOperandAt c
        (Miri.Interpreter.OperandPath.assertion pathField)
        (refAssertDummyOperand rp.types) st =
      .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar .isize 0))),
            refLocalLayoutForTy rp.types (.int .isize false)⟩ st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd; rfl

private theorem readImmediate_dummy_isize (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    (refAssertPanicHooks rp).driver.readImmediate c
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar .isize 0))),
          refLocalLayoutForTy rp.types (.int .isize false)⟩ st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar .isize 0)),
            refLocalLayoutForTy rp.types (.int .isize false)⟩ st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd; rfl

private theorem safePanicCall_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (rbb : RefBasicBlock)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (bodyLocals : List MirTy)
    (slots1 : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (cond : RefOperand) (expected : Bool)
    (msg : AssertKind) (target : BasicBlockId) (unwind : UnwindAction)
    (item : Miri.Interpreter.Panic.LangItem)
    (args : Array (Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance))
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks blockIdx = some rbb)
    (h_rt : rbb.terminator = .assert cond expected msg target unwind)
    (h_loc_none : ctx.locOverride = none)
    (h_item : match item with
      | .PanicBoundsCheck | .PanicDivOverflow | .PanicRemOverflow
      | .PanicDivZero | .PanicRemZero => True
      | _ => False) :
    let st₁ := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots1
      cache mem ctrl cm
    match evalAssertFailure .boundsCheck rp.panicStrategy unwind cm
        rp.hasLocalPanicHandler with
    | .fault k =>
      ∃ err st',
        safePanicCall rp c item args (toMiriUnwindAction unwind) st₁ =
          (st', .error err) ∧
        stepErrorFaultKind err = some k
    | .done (.aborted cm') =>
      ∃ st',
        safePanicCall rp c item args (toMiriUnwindAction unwind) st₁ =
          (st', .error (.termination (.abort "panic abort"))) ∧
        st'.machine.user.callerMem = cm'
    | .done (.returned _) | .done (.unwound _) | .step _ => False := by
  intro st₁
  have h_cf : st₁.stack.currentFrame? =
      some (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots1
        cache) := by
    dsimp only [st₁, mkGenSimState, mkRefMiriStackState]
    rw [stack_currentFrame?_push]
  have h_loc : (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots1
      cache).location = .mir ⟨blockIdx, stmtIdx⟩ := by
    dsimp only [mkGenSimFrame]
    rw [h_loc_none]
  have h_bb : (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots1
      cache).body.basicBlocks[blockIdx]? =
      some (toMiriBasicBlock rp.types rbb) := by
    dsimp only [mkGenSimFrame, toMiriBody]
    rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map, h_rbb]
    rfl
  have h_tkind : (toMiriBasicBlock rp.types rbb).terminator.kind =
      .Assert (toMiriOperand rp.types cond) expected
        (toMiriAssertKind rp.types msg) target (toMiriUnwindAction unwind) := by
    dsimp only [toMiriBasicBlock]
    rw [h_rt]
    rfl
  cases item <;>
  first
  | exact False.elim h_item
  | (cases h_lh : rp.hasLocalPanicHandler <;>
     cases h_ps : rp.panicStrategy <;> cases unwind <;>
     dsimp only [safePanicCall, safePanicMono, refAssertPanicHooks,
       Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
       Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
       refPanicLangItem, evalAssertFailure, toMiriUnwindAction,
       bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure] <;>
     rw [h_lh, h_ps] <;>
     first
     | exact ⟨.unsupported "crate-local panic_handler unsupported", st₁, rfl, rfl⟩
     | exact ⟨.unsupported "panic unwind unsupported", st₁, rfl, rfl⟩
     | (dsimp only
        rw [h_cf]; dsimp only
        rw [h_loc]; dsimp only
        rw [h_bb]; dsimp only
        rw [h_tkind]
        first
        | exact ⟨st₁, rfl, rfl⟩
        | exact ⟨.unsupported "panic assert cleanup unsupported", st₁, rfl, rfl⟩))

private theorem assertPanic_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (rbb : RefBasicBlock)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (bodyLocals : List MirTy)
    (slots1 : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (cond : RefOperand) (expected : Bool)
    (msg : AssertKind) (target : BasicBlockId) (unwind : UnwindAction)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks blockIdx = some rbb)
    (h_rt : rbb.terminator = .assert cond expected msg target unwind)
    (h_loc_none : ctx.locOverride = none) :
    let st₁ := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots1
      cache mem ctrl cm
    let res := Miri.Interpreter.MachineHooks.run
      (Miri.Interpreter.Panic.assertPanic (refAssertPanicHooks rp) c
        (toMiriAssertKind rp.types msg) (toMiriUnwindAction unwind)) st₁
    match evalAssertFailure msg rp.panicStrategy unwind cm
        rp.hasLocalPanicHandler with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = some k
    | .done (.aborted cm') =>
      ∃ st',
        res = (st', .error (.termination (.abort "panic abort"))) ∧
        st'.machine.user.callerMem = cm'
    | .done (.returned _) | .done (.unwound _) | .step _ => False := by
  intro st₁ res
  cases msg with
  | misalignedPtrDeref | nullPtrDeref | unsupported =>
    exact ⟨_, st₁, rfl, rfl⟩
  | boundsCheck =>
    have h_eq :
        res =
          safePanicCall rp c .PanicBoundsCheck
            ([⟨.scalar (.fromScalarInt (miriScalar .isize 0)),
                refLocalLayoutForTy rp.types (.int .isize false)⟩,
              ⟨.scalar (.fromScalarInt (miriScalar .isize 0)),
                refLocalLayoutForTy rp.types (.int .isize false)⟩].toArray)
            (toMiriUnwindAction unwind) st₁ := by
      dsimp only [res, Miri.Interpreter.MachineHooks.run,
        Miri.Interpreter.Call.run, Miri.Interpreter.Panic.assertPanic,
        toMiriAssertKind, bind, Bind.bind, EStateM.bind]
      rw [evalOperandAt_dummy_isize rp c "index" st₁ rfl]
      dsimp only
      rw [readImmediate_dummy_isize rp c st₁ rfl]
      dsimp only
      rw [evalOperandAt_dummy_isize rp c "length" st₁ rfl]
      dsimp only
      rw [readImmediate_dummy_isize rp c st₁ rfl]
      rfl
    rw [h_eq]
    exact safePanicCall_eq rp c ctx rbody rbb blockIdx stmtIdx bodyLocals
      slots1 cache mem ctrl cm cond expected .boundsCheck target unwind
      .PanicBoundsCheck _ h_rbb h_rt h_loc_none True.intro
  | overflowNeg =>
    exact ⟨_, st₁, rfl, rfl⟩
  | divByZero =>
    have h_eq :
        res = safePanicCall rp c .PanicDivZero [].toArray
          (toMiriUnwindAction unwind) st₁ := rfl
    rw [h_eq]
    exact safePanicCall_eq rp c ctx rbody rbb blockIdx stmtIdx bodyLocals
      slots1 cache mem ctrl cm cond expected .divByZero target unwind
      .PanicDivZero [].toArray h_rbb h_rt h_loc_none True.intro
  | remByZero =>
    have h_eq :
        res = safePanicCall rp c .PanicRemZero [].toArray
          (toMiriUnwindAction unwind) st₁ := rfl
    rw [h_eq]
    exact safePanicCall_eq rp c ctx rbody rbb blockIdx stmtIdx bodyLocals
      slots1 cache mem ctrl cm cond expected .remByZero target unwind
      .PanicRemZero [].toArray h_rbb h_rt h_loc_none True.intro
  | overflow op =>
    cases op with
    | div =>
      have h_eq :
          res = safePanicCall rp c .PanicDivOverflow [].toArray
            (toMiriUnwindAction unwind) st₁ := rfl
      rw [h_eq]
      exact safePanicCall_eq rp c ctx rbody rbb blockIdx stmtIdx bodyLocals
        slots1 cache mem ctrl cm cond expected (.overflow .div) target unwind
        .PanicDivOverflow [].toArray h_rbb h_rt h_loc_none True.intro
    | rem =>
      have h_eq :
          res = safePanicCall rp c .PanicRemOverflow [].toArray
            (toMiriUnwindAction unwind) st₁ := rfl
      rw [h_eq]
      exact safePanicCall_eq rp c ctx rbody rbb blockIdx stmtIdx bodyLocals
        slots1 cache mem ctrl cm cond expected (.overflow .rem) target unwind
        .PanicRemOverflow [].toArray h_rbb h_rt h_loc_none True.intro
    | add | sub | mul | shr | shl
    | addUnchecked | addWithOverflow | subUnchecked | subWithOverflow
    | mulUnchecked | mulWithOverflow | bitXor | bitAnd | bitOr | eq | lt | le
    | ne | ge | gt | cmp | offset | shlUnchecked | shrUnchecked =>
      exact ⟨_, st₁, rfl, rfl⟩

private theorem evalTerminator_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (body : Body) (rbb : RefBasicBlock)
    (bb : BasicBlock) (f : FrameState) (retTy : MirTy) (cache : List Bool)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (amem : MemoryState)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_c_len : cache.length = body.locals.length)
    (h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = some rbb)
    (h_rbb_dec : decodeBasicBlock rp.types rbb = some bb)
    (h_loc : ctx.locOverride = none)
    (h_root : rbb.terminator = .return_ →
      ∃ defId,
        ctx = { below := Array.empty
                topRel? := ctx.topRel?
                fnTag := defId
                retCont := .stop false
                retPlace := .memory retPlace } ∧
        refTopRelevanceValid 1 ctx.topRel? ∧
        MirSemantics.getElem? body.locals 0 = some retTy ∧
        refInitMemoryAndRetPlace rp.types retTy = .ok (mem, retPlace))
    (h_noncall :
      (∀ callee args dst tgt uw, rbb.terminator ≠ .call callee args dst tgt uw) ∧
      (∀ op args dst tgt uw, rbb.terminator ≠ .sysrootCall op args dst tgt uw))
    (h_act : assertConditionTypesValid body = true)
    (h_supp : body.locals.all isSupportedScalarOrUnitTy = true)
    (h_inv : SlotsMatchTys body.locals f.locals) :
    let st := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
      f.locals cache mem ctrl cm
    let res := (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfig rp) refLimits).terminator c
      (toMiriTerminator rp.types rbb.terminator) st
    match evalTerminator body bb f amem cm rp.panicStrategy
        rp.hasLocalPanicHandler with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = some k
    | .done (.returned ⟨v, cm'⟩) =>
      ∃ st',
        res = (st', .ok ()) ∧
        st'.stack.frames.isEmpty = true ∧
        refReadReturnVal st'.machine.memory retTy retPlace = .ok v ∧
        st'.machine.user.callerMem = cm'
    | .done (.aborted cm') =>
      ∃ st',
        res = (st', .error (.termination (.abort "panic abort"))) ∧
        st'.machine.user.callerMem = cm'
    | .done (.unwound _) => False
    | .step s' =>
      ∃ tgt slots',
        s' = { frames := [{ f with blockIdx := tgt, stmtIdx := 0, locals := slots' }],
               callerMem := cm, mem := amem } ∧
        res = (mkGenSimState rp ctx rbody tgt 0 body.locals slots'
          (termCacheTouch bb.terminator cache) mem ctrl cm, .ok ()) := by
  intro st
  let ⟨_, h_term_dec, _⟩ := decodeBasicBlock_inv h_rbb_dec
  cases h_rt : rbb.terminator with
  | goto target =>
    intro res
    rw [h_rt] at h_term_dec
    injection h_term_dec with h_eq
    dsimp only [evalTerminator]
    rw [← h_eq]
    dsimp only [termCacheTouch]
    exact ⟨target, f.locals, rfl, by
      dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.ControlFlow.evalTerminator,
        toMiriTerminator, Id.run]
      exact goToBlock_mkGenSimState rp ctx rbody f.blockIdx target f.stmtIdx
        body.locals f.locals cache mem ctrl cm h_loc⟩
  | return_ =>
    intro res
    rw [h_rt] at h_term_dec
    injection h_term_dec with h_eq
    let ⟨defId, h_ctx_eq, h_tr, h_ret_ty, h_init⟩ := h_root h_rt
    have h_ret := returnFromCurrentFrame_ref_eq rp c defId rbody body rbb bb f
      retTy cache ctx.topRel? retPlace mem ctrl cm amem h_bdec h_c_len h_rbb
      h_rbb_dec h_rt h_ret_ty h_init h_tr h_supp h_inv rp.panicStrategy
      rp.hasLocalPanicHandler
    rw [← h_eq]
    dsimp only [evalTerminator, termCacheTouch] at h_ret
    dsimp only [evalTerminator, termCacheTouch]
    dsimp only [res, st]
    rw [h_ctx_eq]
    exact h_ret
  | unreachable =>
    intro res
    rw [h_rt] at h_term_dec
    injection h_term_dec with h_eq
    dsimp only [evalTerminator]
    rw [← h_eq]
    exact ⟨_, _, rfl, rfl⟩
  | unwindResume =>
    intro res
    rw [h_rt] at h_term_dec
    injection h_term_dec with h_eq
    dsimp only [evalTerminator]
    rw [← h_eq]
    exact ⟨_, _, rfl, rfl⟩
  | assert rcond expected rmsg target runwind =>
    intro res
    rw [h_rt] at h_term_dec
    dsimp only [decodeTerminator, optMap] at h_term_dec
    cases h_c : decodeOperand rp.types rcond with
    | none => rw [h_c] at h_term_dec; cases h_term_dec
    | some cond =>
      rw [h_c] at h_term_dec
      injection h_term_dec with h_eq
      dsimp only [evalTerminator]
      rw [← h_eq]
      dsimp only [termCacheTouch]
      have h_locs := (decodeBody_inv h_bdec).2.1
      have h_evC := evalPrimitiveOperand_ref_eq rp c ctx rbody f.blockIdx
        f.stmtIdx body.locals f.locals cache amem mem ctrl cm
        (Miri.Interpreter.OperandPath.instruction "condition")
        rcond cond none h_locs h_c_len
        (refConstantAt_eq_of_ne_fn rp c _ (by decide) (fun _ _ _ => rfl))
        h_inv h_c
        (operandKnownOk_none _ _ _ _)
        (fun _ _ h_ty =>
          let ⟨_, _, h_ts⟩ := decodeBody_local_mem_types h_bdec h_ty
          (resolveTy_tyIdFor_of_mem h_ts).2)
      cases h_pC : evalPrimitiveOperand body.locals f.locals amem cond with
      | error k =>
        rw [h_pC] at h_evC
        dsimp only
        let ⟨err, st', h_err, h_fk⟩ := h_evC
        refine ⟨err, st', ?_, h_fk⟩
        have h_err' :
            EStateM.bind
              (Miri.Interpreter.OperandMachine.evalOperandAt
                (Miri.Interpreter.ExecutionMachine.operandHooks
                  (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits))
                c (Miri.Interpreter.OperandPath.instruction "condition")
                (toMiriOperand rp.types rcond) none)
              (fun __do_lift =>
                Miri.Interpreter.PlaceMachine.readImmediate
                  (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).access
                  __do_lift)
              st = .error err st' := h_err
        dsimp only [EStateM.bind] at h_err'
        dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
          Miri.Interpreter.ControlFlow.evalTerminator,
          Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
          toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure,
          EStateM.bind]
        rw [h_err']
      | ok triple =>
        cases triple with | mk condVal rest =>
        cases rest with | mk slots1 amem1 =>
        have h_amem : amem1 = amem :=
          (evalPrimitiveOperand_slotsMatchTys h_inv h_pC).2
        rw [h_pC] at h_evC
        dsimp only
        let ⟨condTy, h_ccv, _, _, _, h_okC⟩ := h_evC
        let ⟨b, h_cv_b⟩ := assertConditionTypesValid_cond_bool
          h_act h_bb h_eq.symm h_inv h_pC
        subst h_cv_b
        have h_cty : condTy = .bool := by
          dsimp only [checkVal] at h_ccv
          cases condTy <;> cases h_ccv
          rfl
        subst h_cty
        dsimp only [valToMiriImmediate] at h_okC
        have h_okC' :
            EStateM.bind
              (Miri.Interpreter.OperandMachine.evalOperandAt
                (Miri.Interpreter.ExecutionMachine.operandHooks
                  (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits))
                c (Miri.Interpreter.OperandPath.instruction "condition")
                (toMiriOperand rp.types rcond) none)
              (fun __do_lift =>
                Miri.Interpreter.PlaceMachine.readImmediate
                  (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).access
                  __do_lift)
              st =
            .ok ⟨.scalar (.fromBool b),
                  refLocalLayoutForTy rp.types .bool⟩
              (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
                slots1 (operandCacheTouch cache cond) mem ctrl cm) := h_okC
        dsimp only [EStateM.bind] at h_okC'
        have h_res_bool :
            res =
              if (expected == b) = true then
                Miri.Interpreter.ControlFlow.goToBlock target
                  (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
                    slots1 (operandCacheTouch cache cond) mem ctrl cm)
              else
                Miri.Interpreter.MachineHooks.run
                  (Miri.Interpreter.Panic.assertPanic (refAssertPanicHooks rp)
                    c (toMiriAssertKind rp.types rmsg)
                    (toMiriUnwindAction runwind))
                  (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
                    slots1 (operandCacheTouch cache cond) mem ctrl cm) := by
          dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
            Miri.Interpreter.ControlFlow.evalTerminator,
            Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
            toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure,
            EStateM.bind]
          rw [h_okC']
          cases b <;> cases expected <;> rfl
        have h_bcomm : (expected == b) = (b == expected) := by
          cases b <;> cases expected <;> rfl
        rw [h_res_bool, h_bcomm]
        dsimp only
        cases h_eqb : (b == expected) with
        | true =>
          dsimp only [ite_true_eq, jumpToBlock]
          exact ⟨target, slots1, by rw [h_amem],
            goToBlock_mkGenSimState rp ctx rbody f.blockIdx target f.stmtIdx
              body.locals slots1 (operandCacheTouch cache cond) mem ctrl cm h_loc⟩
        | false =>
          dsimp only [ite_false_eq]
          have h_ap := assertPanic_ref_eq rp c ctx rbody rbb f.blockIdx f.stmtIdx
            body.locals slots1 (operandCacheTouch cache cond) mem ctrl cm rcond
            expected rmsg target runwind h_rbb h_rt h_loc
          cases h_af : evalAssertFailure rmsg rp.panicStrategy runwind cm
              rp.hasLocalPanicHandler with
          | fault k =>
            rw [h_af] at h_ap
            exact h_ap
          | done out =>
            rw [h_af] at h_ap
            cases out with
            | aborted cm' => exact h_ap
            | returned _ => exact False.elim h_ap
            | unwound _ => exact False.elim h_ap
          | step _ =>
            rw [h_af] at h_ap
            exact False.elim h_ap
  | call callee rargs rdst tgt uw =>
    exact False.elim (h_noncall.1 callee rargs rdst tgt uw h_rt)
  | sysrootCall op rargs rdst tgt uw =>
    exact False.elim (h_noncall.2 op rargs rdst tgt uw h_rt)
  | coreCall _ rargs rdst _ _ =>
    intro res
    rw [h_rt] at h_term_dec
    dsimp only [decodeTerminator, optMap2] at h_term_dec
    cases h_a : mapOption (decodeOperand rp.types) rargs with
    | none => rw [h_a] at h_term_dec; cases h_term_dec
    | some _ =>
      cases h_d : decodePlace rp.types rdst with
      | none => rw [h_a, h_d] at h_term_dec; cases h_term_dec
      | some _ =>
        rw [h_a, h_d] at h_term_dec
        injection h_term_dec with h_eq
        dsimp only [evalTerminator]
        rw [← h_eq]
        exact ⟨_, _, rfl, rfl⟩
  | unsupported =>
    intro res
    rw [h_rt] at h_term_dec
    injection h_term_dec with h_eq
    dsimp only [evalTerminator]
    rw [← h_eq]
    exact ⟨_, _, rfl, rfl⟩
  | switchInt rdiscr targets =>
    intro res
    rw [h_rt] at h_term_dec
    dsimp only [decodeTerminator, optMap] at h_term_dec
    cases h_d : decodeOperand rp.types rdiscr with
    | none => rw [h_d] at h_term_dec; cases h_term_dec
    | some discr =>
      rw [h_d] at h_term_dec
      injection h_term_dec with h_eq
      dsimp only [evalTerminator]
      rw [← h_eq]
      dsimp only [termCacheTouch]
      have h_locs := (decodeBody_inv h_bdec).2.1
      have h_evD := evalPrimitiveOperand_ref_eq rp c ctx rbody f.blockIdx
        f.stmtIdx body.locals f.locals cache amem mem ctrl cm
        (Miri.Interpreter.OperandPath.instruction "discriminant")
        rdiscr discr none h_locs h_c_len
        (refConstantAt_eq_of_ne_fn rp c _ (by decide) (fun _ _ _ => rfl))
        h_inv h_d
        (operandKnownOk_none _ _ _ _)
        (fun _ _ h_ty =>
          let ⟨_, _, h_ts⟩ := decodeBody_local_mem_types h_bdec h_ty
          (resolveTy_tyIdFor_of_mem h_ts).2)
      cases h_pD : evalPrimitiveOperand body.locals f.locals amem discr with
      | error k =>
        rw [h_pD] at h_evD
        dsimp only
        let ⟨err, st', h_err, h_fk⟩ := h_evD
        refine ⟨err, st', ?_, h_fk⟩
        have h_err' :
            EStateM.bind
              (Miri.Interpreter.OperandMachine.evalOperandAt
                (Miri.Interpreter.ExecutionMachine.operandHooks
                  (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits))
                c (Miri.Interpreter.OperandPath.instruction "discriminant")
                (toMiriOperand rp.types rdiscr) none)
              (fun __do_lift =>
                Miri.Interpreter.PlaceMachine.readImmediate
                  (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).access
                  __do_lift)
              st = .error err st' := h_err
        dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
          Miri.Interpreter.ControlFlow.evalTerminator,
          Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
          toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [h_err']
      | ok pair =>
        cases pair with
        | mk discrVal rest =>
        cases rest with
        | mk slotsAfterDiscr amemAfterDiscr =>
          have h_amem : amemAfterDiscr = amem :=
            (evalPrimitiveOperand_slotsMatchTys h_inv h_pD).2
          rw [h_pD] at h_evD
          dsimp only
          let ⟨discrTy, h_dcv, h_dpr, h_dres, _, h_okD⟩ := h_evD
          let st₁ := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
            slotsAfterDiscr (operandCacheTouch cache discr) mem ctrl cm
          have h_after_discr :
              res =
                match forIn (m := Id)
                    (targets.branches.map (fun b : BitVec 128 × BasicBlockId =>
                      Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
                    ((none : Option (Miri.Interpreter.StepResult MiriStepState Unit)),
                      st₁, targets.otherwise)
                    (fun case __s =>
                      have __s := __s.snd
                      have state := __s.fst
                      have target := __s.snd
                      match case with
                      | Miri.MIR.SwitchTarget.Case bits block =>
                        match Miri.Interpreter.MachineHooks.run
                            (EStateM.bind
                              (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                                  (BitVec.ofNat 128 bits)
                                  (refLocalLayoutForTy rp.types discrTy).layout.size).mapError
                                  Miri.Interpreter.ScalarOps.scalarError with
                               | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                              (fun caseScalar =>
                                EStateM.bind
                                  (Miri.Interpreter.ScalarOps.binary
                                    (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)) c .Eq
                                    ⟨valToMiriImmediate discrTy discrVal, refLocalLayoutForTy rp.types discrTy⟩
                                    ⟨.scalar caseScalar, refLocalLayoutForTy rp.types discrTy⟩)
                                  (fun result =>
                                    EStateM.bind
                                      (match result.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError with
                                       | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                                      (fun sc =>
                                        match sc.toBool.mapError Miri.Interpreter.ScalarOps.scalarError with
                                        | .ok v => EStateM.pure v | .error e => EStateM.throw e))))
                            state with
                        | (next, comparison) =>
                          have state := next
                          match comparison with
                          | Except.error error =>
                            pure (ForInStep.done
                              (some (state, Except.error error), state, target))
                          | Except.ok true =>
                            have target := block
                            pure (ForInStep.done (none, state, target))
                          | Except.ok false =>
                            pure (ForInStep.yield (none, state, target))) with
                | (some early, _, _) => early
                | (none, state, target) =>
                  Miri.Interpreter.ControlFlow.goToBlock target state := by
            have h_okD_raw :
                EStateM.bind
                  (Miri.Interpreter.OperandMachine.evalOperandAt
                    (Miri.Interpreter.ExecutionMachine.operandHooks
                      (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits))
                    c (Miri.Interpreter.OperandPath.instruction "discriminant")
                    (toMiriOperand rp.types rdiscr) none)
                  (fun __do_lift =>
                    Miri.Interpreter.PlaceMachine.readImmediate
                      (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).access
                      __do_lift)
                  st =
                .ok ⟨valToMiriImmediate discrTy discrVal, refLocalLayoutForTy rp.types discrTy⟩ st₁ := h_okD
            have h_okD' :
                Miri.Interpreter.MachineHooks.run
                  (EStateM.bind
                    (Miri.Interpreter.OperandMachine.evalOperandAt
                      (Miri.Interpreter.ExecutionMachine.operandHooks
                        (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits))
                      c (Miri.Interpreter.OperandPath.instruction "discriminant")
                      (toMiriOperand rp.types rdiscr) none)
                    (fun __do_lift =>
                      Miri.Interpreter.PlaceMachine.readImmediate
                        (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).access
                        __do_lift))
                  st =
                (st₁, .ok ⟨valToMiriImmediate discrTy discrVal, refLocalLayoutForTy rp.types discrTy⟩) := by
              dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
              rw [h_okD_raw]
            dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
              Miri.Interpreter.ControlFlow.evalTerminator,
              toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure]
            rw [h_okD']
            dsimp only
            rw [← Array.forIn_toList]
            have h_al :
                ({ toList := targets.branches.map (fun b : BitVec 128 × BasicBlockId =>
                    Miri.MIR.SwitchTarget.Case b.1.toNat b.2) } :
                  Array Miri.MIR.SwitchTarget).toList =
                targets.branches.map (fun b : BitVec 128 × BasicBlockId =>
                  Miri.MIR.SwitchTarget.Case b.1.toNat b.2) := rfl
            rw [h_al]
            rw [forIn_list_map_congr (g :=
              fun case __s =>
                have __s := __s.snd
                have state := __s.fst
                have target := __s.snd
                match case with
                | Miri.MIR.SwitchTarget.Case bits block =>
                  match Miri.Interpreter.MachineHooks.run
                      (EStateM.bind
                        (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                            (BitVec.ofNat 128 bits)
                            (refLocalLayoutForTy rp.types discrTy).layout.size).mapError
                            Miri.Interpreter.ScalarOps.scalarError with
                         | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                        (fun caseScalar =>
                          EStateM.bind
                            (Miri.Interpreter.ScalarOps.binary
                              (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)) c .Eq
                              ⟨valToMiriImmediate discrTy discrVal, refLocalLayoutForTy rp.types discrTy⟩
                              ⟨.scalar caseScalar, refLocalLayoutForTy rp.types discrTy⟩)
                            (fun result =>
                              EStateM.bind
                                (match result.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError with
                                 | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                                (fun sc =>
                                  match sc.toBool.mapError Miri.Interpreter.ScalarOps.scalarError with
                                  | .ok v => EStateM.pure v | .error e => EStateM.throw e))))
                      state with
                  | (next, comparison) =>
                    have state := next
                    match comparison with
                    | Except.error error =>
                      pure (ForInStep.done
                        (some (state, Except.error error), state, target))
                    | Except.ok true =>
                      have target := block
                      pure (ForInStep.done (none, state, target))
                    | Except.ok false =>
                      pure (ForInStep.yield (none, state, target)))]
            · cases forIn (m := Id)
                  (targets.branches.map (fun b : BitVec 128 × BasicBlockId =>
                    Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
                  ((none : Option (Miri.Interpreter.StepResult MiriStepState Unit)),
                    st₁, targets.otherwise)
                  (fun case __s =>
                    have __s := __s.snd
                    have state := __s.fst
                    have target := __s.snd
                    match case with
                    | Miri.MIR.SwitchTarget.Case bits block =>
                      match Miri.Interpreter.MachineHooks.run
                          (EStateM.bind
                            (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                                (BitVec.ofNat 128 bits)
                                (refLocalLayoutForTy rp.types discrTy).layout.size).mapError
                                Miri.Interpreter.ScalarOps.scalarError with
                             | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                            (fun caseScalar =>
                              EStateM.bind
                                (Miri.Interpreter.ScalarOps.binary
                                  (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)) c .Eq
                                  ⟨valToMiriImmediate discrTy discrVal, refLocalLayoutForTy rp.types discrTy⟩
                                  ⟨.scalar caseScalar, refLocalLayoutForTy rp.types discrTy⟩)
                                (fun result =>
                                  EStateM.bind
                                    (match result.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError with
                                     | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                                    (fun sc =>
                                      match sc.toBool.mapError Miri.Interpreter.ScalarOps.scalarError with
                                      | .ok v => EStateM.pure v | .error e => EStateM.throw e))))
                          state with
                      | (next, comparison) =>
                        have state := next
                        match comparison with
                        | Except.error error =>
                          pure (ForInStep.done
                            (some (state, Except.error error), state, target))
                        | Except.ok true =>
                          have target := block
                          pure (ForInStep.done (none, state, target))
                        | Except.ok false =>
                          pure (ForInStep.yield (none, state, target))) with
              | mk o p =>
                cases o with
                | some _ => rfl
                | none => cases p; rfl
            · intro b s
              cases s with | mk r p => cases p with | mk state target =>
              dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run, refExecCfg]
              rw [eStateM_bind_congr
                (y := match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                    (BitVec.ofNat 128 b.1.toNat)
                    (refLocalLayoutForTy rp.types discrTy).layout.size).mapError
                    Miri.Interpreter.ScalarOps.scalarError with
                  | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                (g := fun caseScalar =>
                  EStateM.bind
                    (Miri.Interpreter.ScalarOps.binary
                      (Miri.Interpreter.ExecutionMachine.scalarHooks
                        (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits))
                      c .Eq
                      ⟨valToMiriImmediate discrTy discrVal, refLocalLayoutForTy rp.types discrTy⟩
                      ⟨.scalar caseScalar, refLocalLayoutForTy rp.types discrTy⟩)
                    (fun result =>
                      EStateM.bind
                        (match result.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError with
                         | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                        (fun sc =>
                          match sc.toBool.mapError Miri.Interpreter.ScalarOps.scalarError with
                          | .ok v => EStateM.pure v | .error e => EStateM.throw e)))]
              · cases EStateM.bind
                    (match (Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                        (BitVec.ofNat 128 b.1.toNat)
                        (refLocalLayoutForTy rp.types discrTy).layout.size).mapError
                        Miri.Interpreter.ScalarOps.scalarError with
                     | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                    (fun caseScalar =>
                      EStateM.bind
                        (Miri.Interpreter.ScalarOps.binary
                          (Miri.Interpreter.ExecutionMachine.scalarHooks
                            (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits))
                          c .Eq
                          ⟨valToMiriImmediate discrTy discrVal, refLocalLayoutForTy rp.types discrTy⟩
                          ⟨.scalar caseScalar, refLocalLayoutForTy rp.types discrTy⟩)
                        (fun result =>
                          EStateM.bind
                            (match result.imm.toScalar.mapError Miri.Interpreter.ScalarOps.immediateError with
                             | .ok v => EStateM.pure v | .error e => EStateM.throw e)
                            (fun sc =>
                              match sc.toBool.mapError Miri.Interpreter.ScalarOps.scalarError with
                              | .ok v => EStateM.pure v | .error e => EStateM.throw e)))
                    state with
                | error _ _ => rfl
                | ok v _ => cases v <;> rfl
              · cases Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
                    (BitVec.ofNat 128 b.1.toNat)
                    (refLocalLayoutForTy rp.types discrTy).layout.size <;> rfl
              · intro caseScalar s₁
                apply eStateM_bind_congr rfl
                intro result s₂
                apply eStateM_bind_congr
                · cases result with | mk imm _ => cases imm <;> rfl
                · intro sc s₃
                  cases sc.toBool <;> rfl
          rw [h_after_discr]
          cases checkVal_eq_true_inv h_dcv with
          | inl h_i =>
            let ⟨w, s, bits, h_ty_eq, h_val_eq, h_tr⟩ := h_i
            subst h_ty_eq h_val_eq
            have h_loop := switchInt_forIn_scalar rp c st₁ w s bits
              targets.otherwise targets.branches h_tr
            dsimp only [valToMiriImmediate]
            cases h_sw : evalSwitchBranches w bits targets.otherwise targets.branches with
            | error k =>
              rw [h_sw] at h_loop
              dsimp only
              let ⟨err, h_lr, h_fk⟩ := h_loop
              rw [h_lr]
              exact ⟨err, st₁, rfl, h_fk⟩
            | ok tgt =>
              rw [h_sw] at h_loop
              dsimp only
              rw [h_loop]
              exact ⟨tgt, slotsAfterDiscr, by rw [h_amem],
                goToBlock_mkGenSimState rp ctx rbody f.blockIdx tgt f.stmtIdx
                  body.locals slotsAfterDiscr
                  (operandCacheTouch cache discr) mem ctrl cm h_loc⟩
          | inr h_rest =>
            cases h_rest with
            | inl h_b =>
              let ⟨b, h_ty_eq, h_val_eq⟩ := h_b
              subst h_ty_eq h_val_eq
              have h_loop := switchInt_forIn_bool rp c st₁ b
                targets.otherwise targets.branches
              dsimp only [valToMiriImmediate]
              cases h_sw : evalBoolSwitchBranches b targets.otherwise targets.branches with
              | error k =>
                rw [h_sw] at h_loop
                dsimp only
                let ⟨err, h_lr, h_fk⟩ := h_loop
                rw [h_lr]
                exact ⟨err, st₁, rfl, h_fk⟩
              | ok tgt =>
                rw [h_sw] at h_loop
                dsimp only
                rw [h_loop]
                exact ⟨tgt, slotsAfterDiscr, by rw [h_amem],
                  goToBlock_mkGenSimState rp ctx rbody f.blockIdx tgt f.stmtIdx
                    body.locals slotsAfterDiscr
                    (operandCacheTouch cache discr) mem ctrl cm h_loc⟩
            | inr h_rest2 =>
              cases h_rest2 with
              | inl h_u => rw [h_u.1] at h_dpr; cases h_dpr
              | inr h_rest3 =>
              cases h_rest3 with
              | inl h_e =>
                let ⟨_, _, h_ty_eq, _, _, _⟩ := h_e
                rw [h_ty_eq] at h_dpr; cases h_dpr
              | inr h_rest4 =>
              cases h_rest4 with
              | inl h_c =>
                let ⟨ch, h_ty_eq, h_val_eq⟩ := h_c
                subst h_ty_eq h_val_eq
                have h_loop := switchInt_forIn_char rp c st₁ ch
                  targets.otherwise targets.branches h_dres
                dsimp only [valToMiriImmediate]
                cases h_sw : evalCharSwitchBranches ch targets.otherwise
                    targets.branches with
                | error k =>
                  rw [h_sw] at h_loop
                  dsimp only
                  let ⟨err, h_lr, h_fk⟩ := h_loop
                  rw [h_lr]
                  exact ⟨err, st₁, rfl, h_fk⟩
                | ok tgt =>
                  rw [h_sw] at h_loop
                  dsimp only
                  rw [h_loop]
                  exact ⟨tgt, slotsAfterDiscr, by rw [h_amem],
                    goToBlock_mkGenSimState rp ctx rbody f.blockIdx tgt f.stmtIdx
                      body.locals slotsAfterDiscr
                      (operandCacheTouch cache discr) mem ctrl cm h_loc⟩
              | inr h_rest5 =>
              cases h_rest5 with
              | inl h_o =>
                let ⟨_, h_ty_eq, _⟩ := h_o
                rw [h_ty_eq] at h_dpr; cases h_dpr
              | inr h_p =>
                let ⟨w, s, bits, b, h_ty_eq, h_val_eq, _⟩ := h_p
                subst h_ty_eq h_val_eq
                have h_loop := switchInt_forIn_pair rp c st₁ w s bits b
                  targets.otherwise targets.branches h_dres
                dsimp only [valToMiriImmediate]
                cases h_br : targets.branches with
                | nil =>
                  rw [h_br] at h_loop
                  dsimp only at h_loop
                  dsimp only
                  rw [h_loop]
                  exact ⟨targets.otherwise, slotsAfterDiscr, by rw [h_amem],
                    goToBlock_mkGenSimState rp ctx rbody f.blockIdx targets.otherwise f.stmtIdx
                      body.locals slotsAfterDiscr
                      (operandCacheTouch cache discr) mem ctrl cm h_loc⟩
                | cons hd tl =>
                  rw [h_br] at h_loop
                  dsimp only at h_loop
                  let ⟨err, h_lr, h_fk⟩ := h_loop
                  dsimp only
                  rw [h_lr]
                  exact ⟨err, st₁, rfl, h_fk⟩

/-! ## Section 4: `ExecutionMachine.step` Simulation (`EvalRefStepEqClaim`) -/

private theorem evalRefStep_of_err (rp : RefProg) (c : Choice) (rs : RefState)
    (st' : MiriStepState) (err : Miri.Interpreter.StepError) (k : FaultKind)
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true)
    (h_fk : stepErrorFaultKind err = some k)
    (h_step : Miri.Interpreter.ExecutionMachine.step
        (refExecutionConfig rp) refLimits c rs.miri = (st', .error err)) :
    evalRefStep rp c rs = faultToRefOutcome k := by
  dsimp only [evalRefStep]
  rw [h_lt, ite_not_true_eq, h_step]
  cases err with
  | undefinedBehavior _ => cases h_fk; rfl
  | stack se => cases se <;> cases h_fk <;> rfl
  | termination te => cases te <;> cases h_fk <;> rfl
  | _ => cases h_fk; rfl

private theorem forIn_list_yield_noop {ε σ α : Type}
    (f : α → Unit → EStateM ε σ (ForInStep Unit))
    (h_f : ∀ a st, f a () st = .ok (.yield ()) st) :
    ∀ (xs : List α) (st : σ),
      forIn xs () f st = .ok () st
  | [], _ => rfl
  | a :: rest, st => by
    rw [List.forIn_cons]
    dsimp only [bind, Bind.bind]
    rw [eStateM_bind_ok (h_f a st)]
    exact forIn_list_yield_noop f h_f rest st

private theorem forIn_array_yield_noop {ε σ α : Type} (xs : Array α)
    (f : α → Unit → EStateM ε σ (ForInStep Unit))
    (h_f : ∀ a st, f a () st = .ok (.yield ()) st) (st : σ) :
    forIn xs () f st = .ok () st := by
  rw [← Array.forIn_toList]
  exact forIn_list_yield_noop f h_f xs.toList st

private theorem cleanup_goto_noop (rp : RefProg) (c : Choice)
    (retTarget? : Option BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (fr : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (st : MiriStepState)
    (h_cont : fr.returnContinuation = .goto retTarget? unwind) :
    Miri.Interpreter.CallMachine.cleanup (refLifecycle rp.types) c false fr st =
      .ok .normal st := by
  dsimp only [Miri.Interpreter.CallMachine.cleanup, bind, Bind.bind,
    pure, Pure.pure, EStateM.pure]
  rw [h_cont]
  dsimp only
  rw [ite_not_true_eq]
  rw [eStateM_bind_ok (forIn_array_yield_noop fr.locals _
    (fun (slot : Miri.Interpreter.LocalState Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout) st0 => by
      cases hv : slot.value with
      | dead => rfl
      | live lv => cases lv <;> rfl) st)]
  rw [eStateM_bind_ok (forIn_array_yield_noop fr.vaList _ (fun _ _ => rfl) st)]
  rfl

private theorem writePlace_ok_mem_eq_of_slotsMatchTys {tys : List MirTy}
    {slots slots' : List LocalSlot} {amem amem' : MemoryState}
    {dstId : LocalId} {dstTy : MirTy} {v : Val}
    (h_inv : SlotsMatchTys tys slots)
    (h_ty : MirSemantics.getElem? tys dstId = some dstTy)
    (h_wp : writePlace slots amem dstId dstTy v = .ok (slots', amem')) :
    amem' = amem := by
  dsimp only [writePlace] at h_wp
  cases h_cv : checkVal v dstTy with
  | false =>
    have h_nt : (!false) = true := rfl
    rw [h_cv, h_nt, ite_true_eq] at h_wp
    cases h_wp
  | true =>
    have h_nf : (!true) = false := rfl
    rw [h_cv, h_nf, ite_false_eq] at h_wp
    cases h_sl : MirSemantics.getElem? slots dstId with
    | none => rw [h_sl] at h_wp; cases h_wp
    | some sl =>
      rw [h_sl] at h_wp
      cases sl with
      | dead => cases h_wp
      | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
      | partialTuple _ =>
        exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)
      | immediate _ =>
        cases h_set : MirSemantics.setElem? slots dstId (.immediate (some v)) with
        | none => rw [h_set] at h_wp; cases h_wp
        | some _ =>
          rw [h_set] at h_wp
          cases h_wp
          rfl

private theorem machineHooks_run_ok {K U A : Type}
    {m : Miri.Interpreter.MachineHooks.M K U A}
    {s s' : Miri.Interpreter.MachineHooks.State K U} {a : A}
    (h : m s = .ok a s') :
    Miri.Interpreter.MachineHooks.run m s = (s', .ok a) := by
  dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
  rw [h]

private theorem machineHooks_run_error {K U A : Type}
    {m : Miri.Interpreter.MachineHooks.M K U A}
    {s s' : Miri.Interpreter.MachineHooks.State K U} {e : Miri.Interpreter.StepError}
    (h : m s = .error e s') :
    Miri.Interpreter.MachineHooks.run m s = (s', .error e) := by
  dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
  rw [h]

private theorem returnFromCurrentFrame_copy_err
    {P L E M C Op : Type}
    (hooks : Miri.Interpreter.ControlHooks P L E M C Op)
    (c : C) (st st₁ st₂ st' : Miri.Interpreter.StepState P L E M)
    (frame frame' : Miri.Interpreter.Frame P L E)
    (blk si : Nat) (bb : Miri.MIR.BasicBlock) (val : Op)
    (e : Miri.Interpreter.StepError)
    (h_cf : st.stack.currentFrame? = some frame)
    (h_loc : frame.location = .mir ⟨blk, si⟩)
    (h_bb : frame.body.basicBlocks[blk]? = some bb)
    (h_clean : bb.cleanup = false)
    (h_ro : hooks.returnOperand c st = (st₁, .ok val))
    (h_pop : hooks.popFrame c st₁ = (st₂, .ok frame'))
    (h_cp : hooks.copyReturn c val frame'.returnPlace st₂ = (st', .error e)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks c false st =
      (st', .error e) := by
  simp only [Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
    Id.run, bind, Bind.bind, pure, Pure.pure,
    h_cf, h_loc, h_bb, h_clean, h_ro, h_pop, h_cp]
  rfl

private theorem returnFromCurrentFrame_goto_ok
    {P L E M C Op : Type}
    (hooks : Miri.Interpreter.ControlHooks P L E M C Op)
    (c : C) (st st₁ st₂ st₃ st₄ : Miri.Interpreter.StepState P L E M)
    (frame frame' : Miri.Interpreter.Frame P L E)
    (blk si : Nat) (bb : Miri.MIR.BasicBlock) (val : Op)
    (ret : Option Nat) (unwind : Miri.MIR.UnwindAction)
    (h_cf : st.stack.currentFrame? = some frame)
    (h_loc : frame.location = .mir ⟨blk, si⟩)
    (h_bb : frame.body.basicBlocks[blk]? = some bb)
    (h_clean : bb.cleanup = false)
    (h_ro : hooks.returnOperand c st = (st₁, .ok val))
    (h_pop : hooks.popFrame c st₁ = (st₂, .ok frame'))
    (h_cp : hooks.copyReturn c val frame'.returnPlace st₂ = (st₃, .ok ()))
    (h_cleanup : hooks.cleanupFrame c false frame' st₃ = (st₄, .ok .normal))
    (h_rc : frame'.returnContinuation = .goto ret unwind) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks c false st =
      Miri.Interpreter.ControlFlow.returnToBlock ret st₄ := by
  simp only [Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
    Id.run, bind, Bind.bind, pure, Pure.pure,
    h_cf, h_loc, h_bb, h_clean, h_ro, h_pop, h_cp, h_cleanup, h_rc]
  rfl

private theorem nonRootReturn_ref_eq (rp : RefProg) (p : Program) (c : Choice)
    (ctx callerCtx : SimFrameCtx) (rbody callerRbody : RefBody)
    (body callerBody : Body) (rbb : RefBasicBlock) (bb : BasicBlock)
    (f caller : FrameState) (retTy dstTy : MirTy)
    (cache callerCache : List Bool)
    (rcaller : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (restCallers : List FrameState)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (amem : MemoryState) (dst : Place)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_cbdec : decodeBody rp.types callerRbody = some callerBody)
    (h_c_len : cache.length = body.locals.length)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = some rbb)
    (h_rbb_dec : decodeBasicBlock rp.types rbb = some bb)
    (h_rterm : rbb.terminator = .return_)
    (h_ret_ty : MirSemantics.getElem? body.locals 0 = some retTy)
    (h_dst_ty : MirSemantics.getElem? callerBody.locals dst.localId = some dstTy)
    (h_eq_ty : MirTy.beq retTy dstTy = true)
    (h_dst_c : MirSemantics.getElem? callerCache dst.localId = some true)
    (h_ret_dst : f.retDst? = some dst)
    (h_dst_proj : dst.projection.isEmpty = true)
    (h_caller_body : activeFrameBody p caller = some callerBody)
    (h_supp : body.locals.all isSupportedScalarOrUnitTy = true)
    (h_csupp : callerBody.locals.all isSupportedScalarOrUnitTy = true)
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_cinv : SlotsMatchTys callerBody.locals caller.locals)
    (h_rcaller_eq : rcaller = mkGenSimFrame rp callerCtx callerRbody
      caller.blockIdx caller.stmtIdx callerBody.locals caller.locals callerCache)
    (h_ctx_below : ctx.below = callerCtx.below.push rcaller)
    (h_ctx_tr : ctx.topRel? = some ctx.below.size)
    (h_ctx_rc : ctx.retCont = .goto f.retTarget? .Unreachable)
    (h_ctx_rp : ctx.retPlace = .frameLocal callerCtx.below.size dst.localId none
      (refLocalLayoutForTy rp.types dstTy)
      (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0))
    (h_ctx_loc : ctx.locOverride = none)
    (h_caller_loc : callerCtx.locOverride = none) :
    let st := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
      f.locals cache mem ctrl cm
    let res := (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfig rp) refLimits).terminator c
      (toMiriTerminator rp.types .return_) st
    match evalNonRootReturn p body bb f caller restCallers amem cm with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = some k
    | .done _ => False
    | .step s' =>
      ∃ tgt callerLocals',
        s' = { frames := { caller with blockIdx := tgt, stmtIdx := 0, locals := callerLocals' } :: restCallers,
               callerMem := cm, mem := amem } ∧
        res = (mkGenSimState rp { callerCtx with topRel? := some callerCtx.below.size }
          callerRbody tgt 0 callerBody.locals callerLocals' callerCache mem ctrl cm,
          .ok ()) := by
  intro st res
  have h_b_inv := decodeBody_inv h_bdec
  have h_cb_inv := decodeBody_inv h_cbdec
  let ⟨_, h_rbb_term, h_rbb_clean⟩ := decodeBasicBlock_inv h_rbb_dec
  rw [h_rterm] at h_rbb_term
  injection h_rbb_term with h_term_eq
  have h_st_cf :
      st.stack.currentFrame? =
        some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals
          f.locals cache) := by
    dsimp only [st, mkGenSimState, mkRefMiriStackState]
    exact stack_currentFrame?_push _ _
  have h_mf_loc :
      (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).location =
        .mir ⟨f.blockIdx, f.stmtIdx⟩ := by
    dsimp only [mkGenSimFrame]; rw [h_ctx_loc]
  have h_mf_bb :
      (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals
          cache).body.basicBlocks[f.blockIdx]? =
        some (toMiriBasicBlock rp.types rbb) := by
    dsimp only [mkGenSimFrame, toMiriBody]
    rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map, h_rbb]
    rfl
  cases h_cl : bb.cleanup with
  | true =>
    have h_rcl : rbb.cleanup = true := h_rbb_clean.trans h_cl
    dsimp only [evalNonRootReturn]
    rw [h_cl, Bool.true_or, ite_true_eq]
    have h_err :
        res = (st, .error (.invalidProgram "return/unwind cleanup assertion failed")) := by
      dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.ControlFlow.evalTerminator,
        Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
        toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure]
      rw [h_st_cf]
      dsimp only
      rw [h_mf_loc]
      dsimp only
      rw [h_mf_bb]
      dsimp only [toMiriBasicBlock]
      rw [h_rcl]
      rfl
    exact ⟨_, _, h_err, rfl⟩
  | false =>
    have h_rcl : rbb.cleanup = false := h_rbb_clean.trans h_cl
    have h_len := SlotsMatchTys.length_eq h_inv
    cases getElem?_some_of_length_eq h_len.symm h_ret_ty with
    | intro sl0 h_sl0 =>
    dsimp only [evalNonRootReturn]
    rw [h_cl, SlotsMatchTys.localsHaveIndirect_false h_inv, Bool.false_or,
      ite_false_eq, h_sl0]
    cases sl0 with
    | partialTuple _ =>
      exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ret_ty h_sl0)
    | indirect _ =>
      exact False.elim (SlotsMatchTys.not_indirect h_inv h_ret_ty h_sl0)
    | dead =>
      cases placeMachine_localToOp_dead rp c ctx rbody
        f.blockIdx f.stmtIdx body.locals f.locals cache mem ctrl cm 0 retTy
        h_b_inv.2.1 h_c_len h_ret_ty h_sl0 with
      | intro st₁ h_dead =>
      have h_ro' :
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (Miri.Interpreter.ExecutionMachine.withValidation
              (refExecutionConfig rp) refLimits)).place.localToOp c 0 st =
            .error (.stack (.localExpectedLive 0)) st₁ := h_dead
      have h_ro_run :
          Miri.Interpreter.MachineHooks.run
            ((Miri.Interpreter.ExecutionMachine.projectionHooks
              (Miri.Interpreter.ExecutionMachine.withValidation
                (refExecutionConfig rp) refLimits)).place.localToOp c 0) st =
            (st₁, .error (.stack (.localExpectedLive 0))) :=
        machineHooks_run_error h_ro'
      have h_err : res = (st₁, .error (.stack (.localExpectedLive 0))) := by
        dsimp only [res, Miri.Interpreter.ExecutionMachine.stepHooks,
          Miri.Interpreter.ControlFlow.evalTerminator,
          Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
          Miri.Interpreter.ExecutionControl.hooks,
          toMiriTerminator, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [h_st_cf]
        dsimp only
        rw [h_mf_loc]
        dsimp only
        rw [h_mf_bb]
        dsimp only [toMiriBasicBlock]
        rw [h_rcl, h_ro_run]
        rfl
      exact ⟨_, _, h_err, rfl⟩
    | immediate optRet =>
      have h_ro := placeMachine_localToOp_live rp c ctx rbody
        f.blockIdx f.stmtIdx body.locals f.locals cache mem ctrl cm 0 retTy optRet
        h_b_inv.2.1 h_c_len h_ret_ty h_sl0
      let cache₁ := cacheTouch cache 0
      let st₁ := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
        f.locals cache₁ mem ctrl cm
      have h_ro' :
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (Miri.Interpreter.ExecutionMachine.withValidation
              (refExecutionConfig rp) refLimits)).place.localToOp c 0 st =
            .ok ⟨.immediate (optValToMiriImm retTy optRet),
              refLocalLayoutForTy rp.types retTy⟩ st₁ := h_ro
      have h_tr_ctx : refTopRelevanceValid (ctx.below.size + 1) ctx.topRel? := by
        rw [h_ctx_tr]; dsimp only [refTopRelevanceValid]
        exact ⟨Nat.succ_pos _, Nat.add_sub_cancel _ 1⟩
      have h_back_ctx : ctx.below.isEmpty = false →
          ∃ bfr, ctx.below.back? = some bfr ∧ bfr.extra.userRelevance = 255 := by
        intro _
        refine ⟨rcaller, ?_, ?_⟩
        · rw [h_ctx_below]
          dsimp only [Array.back?]
          rw [Array.size_push, Nat.add_sub_cancel, Array.getElem?_push_size]
        · rw [h_rcaller_eq]; rfl
      cases popRaw_mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals
          f.locals cache₁ mem ctrl cm h_tr_ctx h_back_ctx with
      | intro stPop h_pop_rest =>
      have h_pop_raw := h_pop_rest.1
      have h_stPop_eq := h_pop_rest.2.2.2.2.2.2.2
      have h_topRel_pop :
          (if ctx.below.isEmpty then none else some (ctx.below.size - 1)) =
            some callerCtx.below.size := by
        rw [h_ctx_below, array_isEmpty_push_false, ite_false_eq,
          Array.size_push, Nat.add_sub_cancel]
      let callerCtx' := { callerCtx with topRel? := some callerCtx.below.size }
      have h_stPop_caller :
          stPop = mkGenSimState rp callerCtx'
            callerRbody caller.blockIdx caller.stmtIdx callerBody.locals
            caller.locals callerCache mem ctrl cm := by
        rw [h_stPop_eq, h_topRel_pop, h_ctx_below, h_rcaller_eq]
        rfl
      have h_pop' :
          Miri.Interpreter.TypedMachineBindings.popRaw
            (Miri.Interpreter.TypedMachineBindings.retagHooks
              (Miri.Interpreter.ExecutionMachine.withValidation
                (refExecutionConfig rp) refLimits).access
              (Miri.Interpreter.ExecutionMachine.withValidation
                (refExecutionConfig rp) refLimits).retag) st₁ =
            .ok (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals
              f.locals cache₁) stPop := h_pop_raw
      have h_ro_run :
          Miri.Interpreter.MachineHooks.run
            ((Miri.Interpreter.ExecutionMachine.projectionHooks
              (Miri.Interpreter.ExecutionMachine.withValidation
                (refExecutionConfig rp) refLimits)).place.localToOp c 0) st =
            (st₁, .ok ⟨.immediate (optValToMiriImm retTy optRet),
              refLocalLayoutForTy rp.types retTy⟩) :=
        machineHooks_run_ok h_ro'
      have h_pop_run :
          Miri.Interpreter.MachineHooks.run
            (Miri.Interpreter.TypedMachineBindings.popRaw
              (Miri.Interpreter.TypedMachineBindings.retagHooks
                (Miri.Interpreter.ExecutionMachine.withValidation
                  (refExecutionConfig rp) refLimits).access
                (Miri.Interpreter.ExecutionMachine.withValidation
                  (refExecutionConfig rp) refLimits).retag)) st₁ =
            (stPop, .ok (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals
              f.locals cache₁)) :=
        machineHooks_run_ok h_pop'
      let vh := Miri.Interpreter.ExecutionMachine.withValidation
        (refExecutionConfig rp) refLimits
      let ctrlHooks := Miri.Interpreter.ExecutionControl.hooks
        vh.control.bodySpan vh.lifecycle vh.access
        (Miri.Interpreter.ExecutionMachine.projectionHooks vh).place vh.copy vh.retag
        (Miri.Interpreter.ExecutionCalls.helpers vh.helpers
          (Miri.Interpreter.ExecutionMachine.callHooks vh refLimits))
        vh.unwindTerminateFunction
      have h_res_ctrl :
          res = Miri.Interpreter.ControlFlow.returnFromCurrentFrame ctrlHooks c false st := rfl
      have h_step_copy_err :
          ∀ (e : Miri.Interpreter.StepError) (st' : MiriStepState),
            Miri.Interpreter.copyRuntimePlace
                (Miri.Interpreter.ExecutionMachine.projectionHooks
                  (Miri.Interpreter.ExecutionMachine.withValidation
                    (refExecutionConfig rp) refLimits)).place
                (Miri.Interpreter.ExecutionMachine.withValidation
                  (refExecutionConfig rp) refLimits).copy c
                ⟨.immediate (optValToMiriImm retTy optRet),
                  refLocalLayoutForTy rp.types retTy⟩
                ⟨.local callerCtx.below.size dst.localId none
                  (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0),
                  refLocalLayoutForTy rp.types dstTy⟩ true stPop = .error e st' →
            res = (st', Except.error e) := by
        intro e st' h_cp
        have h_cp_run :
            ctrlHooks.copyReturn c
              ⟨.immediate (optValToMiriImm retTy optRet),
                refLocalLayoutForTy rp.types retTy⟩
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals
                f.locals cache₁).returnPlace stPop = (st', .error e) := by
          dsimp only [ctrlHooks, vh, Miri.Interpreter.ExecutionControl.hooks, mkGenSimFrame]
          rw [h_ctx_rp]
          dsimp only [Miri.Interpreter.RuntimeStackPlace.toRuntimePlace]
          exact machineHooks_run_error h_cp
        rw [h_res_ctrl]
        exact returnFromCurrentFrame_copy_err ctrlHooks c st st₁ stPop st' _ _
          f.blockIdx f.stmtIdx (toMiriBasicBlock rp.types rbb) _ e
          h_st_cf h_mf_loc h_mf_bb (by dsimp only [toMiriBasicBlock]; exact h_rcl)
          h_ro_run h_pop_run h_cp_run
      have h_step_copy_ok :
          ∀ (stCopied : MiriStepState),
            Miri.Interpreter.copyRuntimePlace
                (Miri.Interpreter.ExecutionMachine.projectionHooks
                  (Miri.Interpreter.ExecutionMachine.withValidation
                    (refExecutionConfig rp) refLimits)).place
                (Miri.Interpreter.ExecutionMachine.withValidation
                  (refExecutionConfig rp) refLimits).copy c
                ⟨.immediate (optValToMiriImm retTy optRet),
                  refLocalLayoutForTy rp.types retTy⟩
                ⟨.local callerCtx.below.size dst.localId none
                  (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0),
                  refLocalLayoutForTy rp.types dstTy⟩ true stPop = .ok () stCopied →
            res =
              Miri.Interpreter.ControlFlow.returnToBlock f.retTarget? stCopied := by
        intro stCopied h_cp
        have h_cp_run :
            ctrlHooks.copyReturn c
              ⟨.immediate (optValToMiriImm retTy optRet),
                refLocalLayoutForTy rp.types retTy⟩
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals
                f.locals cache₁).returnPlace stPop = (stCopied, .ok ()) := by
          dsimp only [ctrlHooks, vh, Miri.Interpreter.ExecutionControl.hooks, mkGenSimFrame]
          rw [h_ctx_rp]
          dsimp only [Miri.Interpreter.RuntimeStackPlace.toRuntimePlace]
          exact machineHooks_run_ok h_cp
        have h_clean := cleanup_goto_noop rp c f.retTarget? .Unreachable
          (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals
            f.locals cache₁) stCopied (by dsimp only [mkGenSimFrame]; exact h_ctx_rc)
        have h_clean' :
            Miri.Interpreter.CallMachine.cleanup
              (Miri.Interpreter.ExecutionMachine.withValidation
                (refExecutionConfig rp) refLimits).lifecycle c false
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals
                f.locals cache₁) stCopied = .ok .normal stCopied := h_clean
        have h_clean_run := machineHooks_run_ok h_clean'
        rw [h_res_ctrl]
        exact returnFromCurrentFrame_goto_ok ctrlHooks c st st₁ stPop stCopied stCopied _ _
          f.blockIdx f.stmtIdx (toMiriBasicBlock rp.types rbb) _ f.retTarget? .Unreachable
          h_st_cf h_mf_loc h_mf_bb (by dsimp only [toMiriBasicBlock]; exact h_rcl)
          h_ro_run h_pop_run h_cp_run h_clean_run (by dsimp only [mkGenSimFrame]; exact h_ctx_rc)
      cases decodeBody_local_mem_types h_bdec h_ret_ty with
      | intro _ h_ret_tid =>
      cases decodeBody_local_mem_types h_cbdec h_dst_ty with
      | intro _ h_dst_tid =>
      have h_ret_res := resolveTy_tyIdFor_of_mem h_ret_tid.2
      have h_dst_res := resolveTy_tyIdFor_of_mem h_dst_tid.2
      have h_clen := SlotsMatchTys.length_eq h_cinv
      cases getElem?_some_of_length_eq h_clen.symm h_dst_ty with
      | intro dstSlot h_dst_sl =>
      have h_ret_supp : isSupportedScalarOrUnitTy retTy = true :=
        list_all_mirGetElem? h_supp h_ret_ty
      have h_dst_supp : isSupportedScalarOrUnitTy dstTy = true :=
        list_all_mirGetElem? h_csupp h_dst_ty
      have h_sm_ret : SlotMatchesTy retTy (.immediate optRet) :=
        SlotsMatchTys.getElem? h_inv h_ret_ty h_sl0
      have h_copy := copyRuntimePlace_imm_to_local_transmute rp c
        callerCtx'
        callerRbody caller.blockIdx caller.stmtIdx callerBody.locals
        caller.locals callerCache amem mem ctrl cm dst.localId retTy dstTy
        optRet dstSlot h_dst_ty h_dst_sl h_dst_c h_ret_res.2 h_dst_res.2
        h_dst_supp h_cinv h_sm_ret h_eq_ty
      dsimp only [callerCtx'] at h_copy
      rw [← h_stPop_caller] at h_copy
      cases optRet with
      | none =>
        cases h_copy with
        | intro err h_rest =>
          cases h_rest with
          | intro st' h_pair =>
            exact ⟨err, st', h_step_copy_err err st' h_pair.1, h_pair.2⟩
      | some retVal =>
        dsimp only
        rw [h_ret_dst]
        dsimp only
        rw [h_dst_proj]
        dsimp only [Bool.not, ite_false_eq]
        rw [h_caller_body]
        dsimp only
        rw [h_dst_ty]
        dsimp only
        dsimp only at h_copy
        cases h_wp : writePlace caller.locals amem dst.localId dstTy retVal with
        | error k =>
          rw [h_wp] at h_copy
          cases h_copy with
          | intro err h_rest =>
            cases h_rest with
            | intro st' h_pair =>
              exact ⟨err, st', h_step_copy_err err st' h_pair.1, h_pair.2⟩
        | ok pair =>
          cases pair with
          | mk callerLocals' amem' =>
            have h_amem' : amem' = amem :=
              writePlace_ok_mem_eq_of_slotsMatchTys h_cinv h_dst_ty h_wp
            rw [h_amem'] at h_wp
            rw [h_wp] at h_copy
            dsimp only at h_copy
            let stCopied := mkGenSimState rp callerCtx'
              callerRbody caller.blockIdx caller.stmtIdx callerBody.locals
              callerLocals' callerCache mem ctrl cm
            have h_res_ret := h_step_copy_ok stCopied h_copy
            cases h_rtgt : f.retTarget? with
            | none =>
              rw [h_rtgt] at h_res_ret
              exact ⟨_, _, h_res_ret, rfl⟩
            | some tgt =>
              refine ⟨tgt, callerLocals', ?_, ?_⟩
              · rw [h_amem']
              rw [h_rtgt] at h_res_ret
              rw [h_res_ret]
              exact goToBlock_mkGenSimState rp callerCtx'
                callerRbody caller.blockIdx tgt caller.stmtIdx callerBody.locals
                callerLocals' callerCache mem ctrl cm h_caller_loc

/-! ## Section 5: Multi-frame Call & Sysroot Call Semantics -/

private theorem sysrootNumOpOfCode_code (op : SysrootNumOp) :
    sysrootNumOpOfCode (sysrootNumOpCode op) = some op := by
  cases op with
  | mk k w s => cases k <;> cases w <;> cases s <;> rfl

private theorem fnTagForCrate_mod_div (defId : DefId) :
    ((fnTagForCrate defId).mod 2 == 0) = true ∧
      (fnTagForCrate defId).div 2 = defId := by
  dsimp only [fnTagForCrate]
  constructor
  · have h_m : (2 * defId).mod 2 = 0 := by
      change HMod.hMod (2 * defId) 2 = 0
      exact Nat.mul_mod_right 2 defId
    rw [h_m]; rfl
  · change HDiv.hDiv (2 * defId) 2 = defId
    exact Nat.mul_div_right defId (by decide)

private theorem fnTagForSysroot_mod_div (op : SysrootNumOp) :
    ((fnTagForSysroot op).mod 2 == 0) = false ∧
      (fnTagForSysroot op).div 2 = sysrootNumOpCode op := by
  dsimp only [fnTagForSysroot]
  constructor
  · have h_m : (2 * sysrootNumOpCode op + 1).mod 2 = 1 := by
      change HMod.hMod (2 * sysrootNumOpCode op + 1) 2 = 1
      rw [Nat.mul_add_mod]
    rw [h_m]; rfl
  · change HDiv.hDiv (2 * sysrootNumOpCode op + 1) 2 = sysrootNumOpCode op
    rw [Nat.mul_add_div (by decide : 0 < 2)]
    exact Nat.add_zero _

private theorem refResolveCalleeBody_crate (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (localTys : List MirTy)
    (h_get : MirSemantics.getElem? rp.bodies defId = some rbody)
    (h_locs : decodeLocalTys rp.types rbody.locals = some localTys) :
    refResolveCalleeBody rp (fnTagForCrate defId) = some (rbody, localTys) := by
  let ⟨h_mod, h_div⟩ := fnTagForCrate_mod_div defId
  dsimp only [refResolveCalleeBody]
  rw [h_mod, ite_true_eq, h_div, h_get]
  dsimp only
  rw [h_locs]

private theorem sysrootNumRefBody_decode_of_types (types : List MirTy)
    (op : SysrootNumOp) {tid : TyId}
    (h_mem : MirSemantics.getElem? types tid = some (.int op.width op.signed)) :
    decodeLocalTys types (sysrootNumRefBody types op).locals =
        some [.int op.width op.signed, .int op.width op.signed,
          .int op.width op.signed] ∧
      decodeBody types (sysrootNumRefBody types op) = some (sysrootNumBody op) := by
  have h_res : MirSemantics.getElem? types (tyIdFor types (.int op.width op.signed)) =
      some (.int op.width op.signed) := (resolveTy_tyIdFor_of_mem h_mem).1
  have h_locs :
      decodeLocalTys types (sysrootNumRefBody types op).locals =
        some [.int op.width op.signed, .int op.width op.signed,
          .int op.width op.signed] := by
    dsimp only [sysrootNumRefBody, decodeLocalTys, mapOption, optMap, optMap2]
    rw [h_res]
  refine ⟨h_locs, ?_⟩
  dsimp only [decodeBody]
  rw [h_locs]
  dsimp only [sysrootNumRefBody, mapOption, decodeBasicBlock, decodeStmt,
    decodePlace, decodeRvalue, decodeOperand, decodeTerminator, optMap, optMap2,
    sysrootNumBody]
  cases op.kind <;> rfl

private theorem refResolveCalleeBody_sysroot (rp : RefProg) (op : SysrootNumOp) :
    refResolveCalleeBody rp (fnTagForSysroot op) =
      some (sysrootNumRefBody rp.types op,
        [.int op.width op.signed, .int op.width op.signed, .int op.width op.signed]) := by
  let ⟨h_mod, h_div⟩ := fnTagForSysroot_mod_div op
  dsimp only [refResolveCalleeBody]
  rw [h_mod, ite_false_eq, h_div, sysrootNumOpOfCode_code]

private theorem sysrootNumBody_static_ok (op : SysrootNumOp) :
    (sysrootNumBody op).argumentCount.blt (sysrootNumBody op).locals.length = true ∧
      storageAnnotationsInBounds (sysrootNumBody op) = true ∧
      discriminantTypesValid (sysrootNumBody op) = true ∧
      castTypesValid (sysrootNumBody op) = true ∧
      assignTypesValid (sysrootNumBody op) = true ∧
      (sysrootNumBody op).locals.all isSupportedScalarOrUnitTy = true ∧
      (sysrootNumBody op).basicBlocks.isEmpty = false := by
  cases op with
  | mk k w s => cases k <;> cases w <;> cases s <;> decide

private theorem all_getElem?_eq_true {α : Type} {xs : List α} {p : α → Bool} {i : Nat}
    {x : α} (h_all : xs.all p = true) (h_get : MirSemantics.getElem? xs i = some x) :
    p x = true := list_all_mirGetElem? h_all h_get

private theorem mem_of_mirGetElem? {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α},
      MirSemantics.getElem? xs i = some x → x ∈ xs
  | _ :: _, 0, _, h => by cases h; exact List.mem_cons_self
  | _ :: _, i + 1, _, h => List.mem_cons_of_mem _ (mem_of_mirGetElem? h)

private theorem bodyHasAnyCall_of_call (body : Body) (idx : BasicBlockId) (bb : BasicBlock)
    (h_bb : MirSemantics.getElem? body.basicBlocks idx = some bb)
    (callee : DefId) (args : List Operand) (dst : Place)
    (tgt : Option BasicBlockId) (unwind : UnwindAction)
    (h_term : bb.terminator = .call callee args dst tgt unwind) :
    bodyHasAnyCall body = true := by
  dsimp only [bodyHasAnyCall]
  exact List.any_eq_true.mpr ⟨bb, mem_of_mirGetElem? h_bb, (by rw [h_term])⟩

private theorem bodyHasAnyCall_of_sysrootCall (body : Body) (idx : BasicBlockId) (bb : BasicBlock)
    (h_bb : MirSemantics.getElem? body.basicBlocks idx = some bb)
    (op : SysrootNumOp) (args : List Operand) (dst : Place)
    (tgt : Option BasicBlockId) (unwind : UnwindAction)
    (h_term : bb.terminator = .sysrootCall op args dst tgt unwind) :
    bodyHasAnyCall body = true := by
  dsimp only [bodyHasAnyCall]
  exact List.any_eq_true.mpr ⟨bb, mem_of_mirGetElem? h_bb, (by rw [h_term])⟩

private theorem allCallBodiesStaticAdmitted_callee (p : Program) (callerBody : Body)
    (f : FrameState) (bb : BasicBlock) (callee : DefId) (args : List Operand)
    (dst : Place) (tgt : Option BasicBlockId) (unwind : UnwindAction)
    (calleeBody : Body)
    (h_bb : MirSemantics.getElem? callerBody.basicBlocks f.blockIdx = some bb)
    (h_term : bb.terminator = .call callee args dst tgt unwind)
    (h_all_static : allCallBodiesStaticAdmitted p callerBody = true)
    (h_callee : MirSemantics.getElem? p.bodies callee = some calleeBody) :
    calleeBody.argumentCount.blt calleeBody.locals.length = true ∧
      storageAnnotationsInBounds calleeBody = true ∧
      discriminantTypesValid calleeBody = true ∧
      castTypesValid calleeBody = true ∧
      assignTypesValid calleeBody = true ∧
      callsAdmitted p calleeBody = true ∧
      allCallBodiesStaticAdmitted p calleeBody = true ∧
      calleeBody.locals.all isSupportedScalarOrUnitTy = true ∧
      calleeBody.basicBlocks.isEmpty = false := by
  have h_any : bodyHasAnyCall callerBody = true :=
    bodyHasAnyCall_of_call callerBody f.blockIdx bb h_bb callee args dst tgt unwind h_term
  dsimp only [allCallBodiesStaticAdmitted] at h_all_static
  rw [h_any, ite_true_eq, Bool.and_eq_true] at h_all_static
  have h_cs := all_getElem?_eq_true h_all_static.2 h_callee
  dsimp only [callBodyStaticAdmitted, singleBodyStaticAdmitted] at h_cs
  rw [Bool.and_eq_true] at h_cs
  let ⟨h_single, h_assign⟩ := h_cs
  simp only [Bool.and_eq_true] at h_single
  let ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h_nb⟩, h_arg⟩, h_sa⟩, h_dv⟩, h_cv⟩, _⟩, h_supp⟩, h_calls⟩ :=
    h_single
  have h_ne : calleeBody.basicBlocks.isEmpty = false := by
    cases h_e : calleeBody.basicBlocks.isEmpty with
    | false => rfl
    | true => rw [h_e] at h_nb; cases h_nb
  have h_callee_all : allCallBodiesStaticAdmitted p calleeBody = true := by
    dsimp only [allCallBodiesStaticAdmitted]
    cases h_ca : bodyHasAnyCall calleeBody with
    | false => rfl
    | true =>
      rw [ite_true_eq, Bool.and_eq_true]
      exact ⟨h_assign, h_all_static.2⟩
  exact ⟨h_arg, h_sa, h_dv, h_cv, h_assign, h_calls, h_callee_all, h_supp, h_ne⟩

private theorem refCallsAdmitted_call_elim (rp : RefProg) (localTys : List MirTy)
    (rbody : RefBody) (rbb : RefBasicBlock) (blockIdx : BasicBlockId)
    (callee : DefId) (rargs : List RefOperand) (rdst : RefPlace)
    (tgt : Option BasicBlockId) (unwind : UnwindAction)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks blockIdx = some rbb)
    (h_rterm : rbb.terminator = .call callee rargs rdst tgt unwind)
    (h_rcalls : refCallsAdmitted rp localTys rbody = true) :
    ∃ calleeRbody calleeLocalTys,
      MirSemantics.getElem? rp.bodies callee = some calleeRbody ∧
      decodeLocalTys rp.types calleeRbody.locals = some calleeLocalTys ∧
      refCallTargetAdmitted rp.types localTys rbody rbb calleeRbody.argumentCount
        calleeLocalTys rargs rdst tgt unwind = true := by
  dsimp only [refCallsAdmitted] at h_rcalls
  have h_check := list_all_mirGetElem? h_rcalls h_rbb
  rw [h_rterm] at h_check
  dsimp only at h_check
  cases h_cb : MirSemantics.getElem? rp.bodies callee with
  | none => rw [h_cb] at h_check; cases h_check
  | some calleeRbody =>
    rw [h_cb] at h_check
    dsimp only at h_check
    cases h_cl : decodeLocalTys rp.types calleeRbody.locals with
    | none => rw [h_cl] at h_check; dsimp only at h_check; cases h_check
    | some calleeLocalTys =>
      rw [h_cl] at h_check
      dsimp only at h_check
      exact ⟨calleeRbody, calleeLocalTys, rfl, h_cl, (bool_and_split h_check).2⟩

private theorem refCallsAdmitted_sysrootCall_elim (rp : RefProg) (localTys : List MirTy)
    (rbody : RefBody) (rbb : RefBasicBlock) (blockIdx : BasicBlockId)
    (op : SysrootNumOp) (rargs : List RefOperand) (rdst : RefPlace)
    (tgt : Option BasicBlockId) (unwind : UnwindAction)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks blockIdx = some rbb)
    (h_rterm : rbb.terminator = .sysrootCall op rargs rdst tgt unwind)
    (h_rcalls : refCallsAdmitted rp localTys rbody = true) :
    let ty := MirTy.int op.width op.signed
    refCallTargetAdmitted rp.types localTys rbody rbb 2 [ty, ty, ty]
      rargs rdst tgt unwind = true := by
  dsimp only [refCallsAdmitted] at h_rcalls
  have h_check := list_all_mirGetElem? h_rcalls h_rbb
  rw [h_rterm] at h_check
  exact h_check

private theorem cacheTouch_idem (cache : List Bool) (id : Nat) :
    cacheTouch (cacheTouch cache id) id = cacheTouch cache id := by
  cases h_g : MirSemantics.getElem? (cacheTouch cache id) id with
  | none =>
    apply list_eq_of_getElem?_eq
    · rw [cacheTouch_length]
    · intro i
      have h_ge : cache.length ≤ id := by
        rw [← cacheTouch_length cache id]
        exact mirGetElem?_ge_of_none h_g
      have h_ge' : (cacheTouch cache id).length ≤ id := by
        rw [cacheTouch_length]; exact h_ge
      cases h_ci : MirSemantics.getElem? (cacheTouch cache id) i with
      | none =>
        rw [mirGetElem?_none_of_ge (by rw [cacheTouch_length]; exact mirGetElem?_ge_of_none h_ci)]
      | some b =>
        have h_lt : i < (cacheTouch cache id).length := mirGetElem?_lt_of_some h_ci
        have h_ne : id ≠ i := fun h_eq => by
          subst h_eq
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_lt h_ge')
        rw [getElem?_cacheTouch_ne h_ne, h_ci]
  | some b =>
    cases b with
    | true => exact cacheTouch_eq_self_of_true h_g
    | false =>
      cases h_orig : MirSemantics.getElem? cache id with
      | none =>
        have h_lt : id < (cacheTouch cache id).length := mirGetElem?_lt_of_some h_g
        rw [cacheTouch_length] at h_lt
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_lt (mirGetElem?_ge_of_none h_orig)))
      | some b₀ =>
        rw [getElem?_cacheTouch_self h_orig] at h_g
        cases h_g

private theorem calleeInitCacheLoop_length (argCount idx : Nat) :
    ∀ (tys : List MirTy), (calleeInitCacheLoop argCount idx tys).length = tys.length
  | [] => rfl
  | _ :: rest => by
    dsimp only [calleeInitCacheLoop, List.length]
    rw [calleeInitCacheLoop_length argCount (idx + 1) rest]

private theorem getElem?_calleeInitCacheLoop (argCount : Nat) :
    ∀ (idx : Nat) (tys : List MirTy) (i : Nat) (ty : MirTy),
      MirSemantics.getElem? tys i = some ty →
      MirSemantics.getElem? (calleeInitCacheLoop argCount idx tys) i =
        some (!Nat.beq (idx + i) 0 && Nat.ble (idx + i) argCount)
  | _, [], _, _, h => by cases h
  | idx, _ :: rest, 0, _, _ => by
    dsimp only [calleeInitCacheLoop, MirSemantics.getElem?]
    rw [Nat.add_zero]
  | idx, _ :: rest, i + 1, ty, h => by
    have h_ih := getElem?_calleeInitCacheLoop argCount (idx + 1) rest i ty h
    rw [Nat.add_right_comm idx 1 i] at h_ih
    exact h_ih

private theorem liftLocalsCached_dead_false (types : List MirTy) :
    ∀ (tys : List MirTy),
      liftLocalsCached types tys (List.replicate tys.length .dead)
          (List.replicate tys.length false) =
        List.replicate tys.length { value := .dead, layout := none }
  | [] => rfl
  | _ :: rest => by
    dsimp only [List.length, List.replicate, liftLocalsCached,
      refLocalStateOfSlotWithCache, slotToMiriLocalValue]
    rw [ite_false_eq, liftLocalsCached_dead_false types rest]

private theorem array_contains_eq_refNatListContains (seen : List LocalId) (x : LocalId) :
    seen.toArray.contains x = refNatListContains x seen := by
  induction seen with
  | nil => simp [Array.contains, refNatListContains]
  | cons a rest ih =>
    have h_eq :
        ((a :: rest).toArray.contains x = true) ↔
          (refNatListContains x (a :: rest) = true) := by
      simp only [Array.contains_iff_mem, List.mem_toArray, List.mem_cons]
      dsimp only [refNatListContains]
      rw [Bool.or_eq_true, Nat.beq_eq]
      constructor
      · intro h
        cases h with
        | inl h_eq => subst h_eq; exact Or.inl rfl
        | inr h_in =>
          right
          rw [← ih]
          simp [h_in]
      · intro h
        cases h with
        | inl h_eq => subst h_eq; exact Or.inl rfl
        | inr h_r =>
          right
          rw [← ih] at h_r
          simp only [Array.contains_iff_mem, List.mem_toArray] at h_r
          exact h_r
    cases h_lhs : (a :: rest).toArray.contains x with
    | true => exact (h_eq.mp h_lhs).symm
    | false =>
      cases h_rhs : refNatListContains x (a :: rest) with
      | false => rfl
      | true => rw [h_eq.mpr h_rhs] at h_lhs; cases h_lhs

private theorem moveDefinitelyDisjoint_loop1_gen (rp : RefProg)
    (f : Miri.MIR.SpannedOperand → Array Miri.MIR.Place → ForInStep (Array Miri.MIR.Place))
    (hf : ∀ (arg : Miri.MIR.SpannedOperand) (places : Array Miri.MIR.Place),
      f arg places = match arg.operand with
        | .Move place => ForInStep.yield (places.push place)
        | _ => ForInStep.yield places) :
    ∀ (xs : List RefOperand) (acc : List Miri.MIR.Place),
      (forIn (m := Id) (xs.map (toMiriSpannedOperand rp.types)) (Array.mk acc) f).toList =
        acc ++ (refMovePlaceList xs).map toMiriPlace
  | [], acc => by
    rw [show (forIn (m := Id) ([].map (toMiriSpannedOperand rp.types)) (Array.mk acc) f) =
      Array.mk acc from rfl]
    simp [refMovePlaceList]
  | x :: xs, acc => by
    rw [List.map_cons, List.forIn_cons]
    dsimp only [toMiriSpannedOperand, bind, Bind.bind, pure, Pure.pure, Id.run]
    rw [hf]
    cases x with
    | copy pl => exact moveDefinitelyDisjoint_loop1_gen rp f hf xs acc
    | constant c => exact moveDefinitelyDisjoint_loop1_gen rp f hf xs acc
    | move pl =>
      dsimp only [toMiriOperand, refMovePlaceList, List.map]
      have h_ps : (Array.mk acc).push (toMiriPlace pl) = Array.mk (acc ++ [toMiriPlace pl]) :=
        congrArg Array.mk (by simp)
      rw [h_ps, moveDefinitelyDisjoint_loop1_gen rp f hf xs (acc ++ [toMiriPlace pl]), List.append_assoc]
      rfl

private theorem moveDefinitelyDisjoint_loop2 :
    ∀ (places : List RefPlace) (seen : List LocalId),
      refPlacesDisjointAux seen places = true →
      (forIn (m := Id) (places.map toMiriPlace) ((none : Option Bool), Array.mk seen)
          (fun place (__s : Option Bool × Array LocalId) =>
            if (place.projection[0]? == some Miri.MIR.ProjectionElem.Deref ||
                __s.snd.contains place.localId) = true then
              ForInStep.done (some false, __s.snd)
            else
              ForInStep.yield (none, __s.snd.push place.localId))).1 = none
  | [], _, _ => rfl
  | p :: rest, seen, h => by
    dsimp only [refPlacesDisjointAux] at h
    cases h_pe : p.projection.isEmpty with
    | false =>
      rw [h_pe] at h
      cases h
    | true =>
      cases h_c : refNatListContains p.localId seen with
      | true =>
        rw [h_pe, h_c] at h
        cases h
      | false =>
        rw [h_pe, h_c] at h
        have h_cont : (Array.mk seen).contains p.localId = false := by
          rw [array_contains_eq_refNatListContains seen p.localId]
          exact h_c
        rw [List.map_cons, List.forIn_cons]
        dsimp only [bind, Bind.bind, pure, Pure.pure, Id.run]
        have h_proj_emp : (toMiriPlace p).projection = Array.empty := by
          dsimp only [toMiriPlace]; rw [h_pe]; rfl
        have h_get0 : (toMiriPlace p).projection[0]? = none := by
          rw [h_proj_emp]; rfl
        have h_lid : (toMiriPlace p).localId = p.localId := rfl
        rw [h_get0, h_lid, h_cont]
        rw [show (none == some Miri.MIR.ProjectionElem.Deref) = false from rfl, Bool.false_or, ite_false_eq]
        have h_ps : (Array.mk seen).push p.localId = Array.mk (seen ++ [p.localId]) :=
          congrArg Array.mk (by simp)
        rw [h_ps]
        exact moveDefinitelyDisjoint_loop2 rest (seen ++ [p.localId])
          (by
            have h_mem : ∀ (xs : List RefPlace) (s₁ s₂ : List LocalId),
                (∀ k, refNatListContains k s₁ = refNatListContains k s₂) →
                refPlacesDisjointAux s₁ xs = refPlacesDisjointAux s₂ xs := by
              intro xs
              induction xs with
              | nil => intro _ _ _; rfl
              | cons q qs ih =>
                intro s₁ s₂ hs
                dsimp only [refPlacesDisjointAux]
                rw [hs q.localId]
                cases (!q.projection.isEmpty || refNatListContains q.localId s₂) with
                | true => rfl
                | false =>
                  apply ih
                  intro k
                  dsimp only [refNatListContains]
                  rw [hs k]
            rw [← h_mem rest (p.localId :: seen) (seen ++ [p.localId])]
            · exact h
            · intro k
              rw [← array_contains_eq_refNatListContains, ← array_contains_eq_refNatListContains]
              simp [List.mem_cons, Bool.or_comm])

private theorem moveDefinitelyDisjoint_toMiri_of_ref (rp : RefProg)
    (rargs : List RefOperand) (rdst : RefPlace)
    (h : refMoveDefinitelyDisjoint rargs rdst = true) :
    Miri.Interpreter.Call.moveDefinitelyDisjoint
      ⟨rargs.map (toMiriSpannedOperand rp.types)⟩ (toMiriPlace rdst) = true := by
  dsimp only [Miri.Interpreter.Call.moveDefinitelyDisjoint, Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [← Array.forIn_toList, Array.toList_push, ← Array.forIn_toList]
  dsimp only
  rw [show (List.toArray ([] : List Miri.MIR.Place)) = Array.mk [] from rfl]
  rw [moveDefinitelyDisjoint_loop1_gen rp _ (fun opnd places => by cases opnd.operand <;> rfl) rargs []]
  dsimp only [List.nil_append]
  have h_l2 := moveDefinitelyDisjoint_loop2 (refMovePlaceList rargs ++ [rdst]) [] h
  rw [List.map_append] at h_l2
  dsimp only [List.map] at h_l2
  rw [h_l2]

private def mirStmtStorageMarker? (s : Miri.MIR.Statement) : Option Nat :=
  match s.kind with
  | .StorageLive id => some id
  | .StorageDead id => some id
  | _ => none

private def astStmtStorageMarker? (s : StatementKind) : Option Nat :=
  match s with
  | .storageLive id => some id
  | .storageDead id => some id
  | _ => none

private theorem stmtHasStorageMarker_toMiriStatement (types : List MirTy)
    (rstmt : RefStatementKind) (stmt : StatementKind)
    (h_dec : decodeStmt types rstmt = some stmt) :
    mirStmtStorageMarker? (toMiriStatement types rstmt) = astStmtStorageMarker? stmt := by
  cases rstmt with
  | assign dst rv =>
    dsimp only [decodeStmt, optMap2] at h_dec
    cases h_d : decodePlace types dst with
    | none => rw [h_d] at h_dec; cases h_dec
    | some _ =>
      cases h_r : decodeRvalue types rv with
      | none => rw [h_d, h_r] at h_dec; cases h_dec
      | some _ =>
        rw [h_d, h_r] at h_dec; cases h_dec; rfl
  | storageLive id => cases h_dec; rfl
  | storageDead id => cases h_dec; rfl
  | nop => cases h_dec; rfl
  | unsupported => cases h_dec; rfl

private theorem alwaysLive_stmts_loop (types : List MirTy) (n : Nat) :
    ∀ (rstmts : List RefStatementKind) (stmts : List StatementKind)
      (acc : Array Nat),
      mapOption (decodeStmt types) rstmts = some stmts →
      stmts.all (fun s =>
        match s with
        | .storageLive id | .storageDead id => Nat.blt id n
        | _ => true) = true →
      ∃ acc' : Array Nat,
        forIn (rstmts.map (toMiriStatement types)) acc
            (fun statement (annotated : Array Nat) =>
              match mirStmtStorageMarker? statement with
              | some id =>
                if id ≥ n then
                  Except.error (Miri.Interpreter.StepError.invalidProgram "storage annotation local out of bounds")
                else pure (ForInStep.yield (annotated.push id))
              | _ => pure (ForInStep.yield annotated)) = Except.ok acc' ∧
          ∀ id, acc'.contains id =
            (acc.contains id || stmts.any (MirSemantics.stmtHasStorageMarker id))
  | [], [], acc, _, _ => ⟨acc, rfl, fun _ => by simp⟩
  | [], _ :: _, _, h_dec, _ => by cases h_dec
  | rs :: rrest, [], _, h_dec, _ => by
    dsimp only [mapOption, optMap2] at h_dec
    cases h_s0 : decodeStmt types rs with
    | none => rw [h_s0] at h_dec; cases h_dec
    | some _ =>
      rw [h_s0] at h_dec
      cases h_r0 : mapOption (decodeStmt types) rrest with
      | none => rw [h_r0] at h_dec; cases h_dec
      | some _ => rw [h_r0] at h_dec; cases h_dec
  | rs :: rrest, s :: srest, acc, h_dec, h_all => by
    dsimp only [mapOption, optMap2] at h_dec
    cases h_s : decodeStmt types rs with
    | none => rw [h_s] at h_dec; cases h_dec
    | some s' =>
      cases h_r : mapOption (decodeStmt types) rrest with
      | none => rw [h_s, h_r] at h_dec; cases h_dec
      | some srest' =>
        rw [h_s, h_r] at h_dec
        injection h_dec with h_eq
        injection h_eq with hs_eq hrest_eq
        cases hs_eq; cases hrest_eq
        dsimp only [List.all] at h_all
        rw [Bool.and_eq_true] at h_all
        have h_marker := stmtHasStorageMarker_toMiriStatement types rs s h_s
        cases h_m : astStmtStorageMarker? s with
        | none =>
          have h_m' : mirStmtStorageMarker? (toMiriStatement types rs) = none :=
            h_marker.trans h_m
          have h_not : ∀ id, MirSemantics.stmtHasStorageMarker id s = false := by
            intro id
            cases s <;> first | rfl | cases h_m
          let ⟨acc', h_loop, h_cont⟩ := alwaysLive_stmts_loop types n rrest srest acc h_r h_all.2
          refine ⟨acc', ?_, fun id => ?_⟩
          · rw [List.map_cons, List.forIn_cons]
            dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
            rw [h_m']
            exact h_loop
          · rw [h_cont id]
            dsimp only [List.any]
            rw [h_not id, Bool.false_or]
        | some mkId =>
          have h_m' : mirStmtStorageMarker? (toMiriStatement types rs) = some mkId :=
            h_marker.trans h_m
          have h_lt : mkId < n := by
            cases s with
            | storageLive id => cases h_m; exact Nat.blt_eq.mp h_all.1
            | storageDead id => cases h_m; exact Nat.blt_eq.mp h_all.1
            | assign _ _ | nop | unsupported => cases h_m
          have h_nge : ¬ (mkId ≥ n) := Nat.not_le_of_lt h_lt
          let ⟨acc', h_loop, h_cont⟩ :=
            alwaysLive_stmts_loop types n rrest srest (acc.push mkId) h_r h_all.2
          refine ⟨acc', ?_, fun id => ?_⟩
          · rw [List.map_cons, List.forIn_cons]
            dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
            rw [h_m']
            dsimp only
            rw [ite_eq_right h_nge]
            exact h_loop
          · rw [h_cont id]
            have h_sm_eq : MirSemantics.stmtHasStorageMarker id s = (mkId == id) := by
              cases s with
              | storageLive id' =>
                dsimp only [astStmtStorageMarker?] at h_m; injection h_m with h_id; subst h_id
                dsimp only [MirSemantics.stmtHasStorageMarker]
                exact Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq, beq_iff_eq])
              | storageDead id' =>
                dsimp only [astStmtStorageMarker?] at h_m; injection h_m with h_id; subst h_id
                dsimp only [MirSemantics.stmtHasStorageMarker]
                exact Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq, beq_iff_eq])
              | assign _ _ | nop | unsupported => cases h_m
            have h_push_c : (acc.push mkId).contains id = (acc.contains id || (mkId == id)) := by
              have h_iff : ((acc.push mkId).contains id = true) ↔
                  ((acc.contains id || (mkId == id)) = true) := by
                simp only [Array.contains_iff_mem, Array.mem_push, Bool.or_eq_true, beq_iff_eq]
                constructor
                · intro h
                  cases h with
                  | inl h => exact Or.inl h
                  | inr h => exact Or.inr h.symm
                · intro h
                  cases h with
                  | inl h => exact Or.inl h
                  | inr h => exact Or.inr h.symm
              cases h_lhs : (acc.push mkId).contains id with
              | true => exact (h_iff.mp h_lhs).symm
              | false =>
                cases h_rhs : (acc.contains id || (mkId == id)) with
                | false => rfl
                | true => rw [h_iff.mpr h_rhs] at h_lhs; cases h_lhs
            rw [h_push_c]
            dsimp only [List.any]
            rw [h_sm_eq, Bool.or_assoc]

private theorem alwaysLive_blocks_loop (types : List MirTy) (n : Nat) :
    ∀ (rbbs : List RefBasicBlock) (bbs : List BasicBlock) (acc : Array Nat),
      mapOption (decodeBasicBlock types) rbbs = some bbs →
      bbs.all (fun bb =>
        bb.statements.all (fun s =>
          match s with
          | .storageLive id | .storageDead id => Nat.blt id n
          | _ => true)) = true →
      ∃ acc' : Array Nat,
        forIn (rbbs.map (toMiriBasicBlock types)) acc
            (fun (block : Miri.MIR.BasicBlock) (annotated : Array Nat) =>
              Bind.bind
                (forIn block.statements annotated fun (statement : Miri.MIR.Statement) (annotated : Array Nat) =>
                  match mirStmtStorageMarker? statement with
                  | some id =>
                    if id ≥ n then
                      Except.error (Miri.Interpreter.StepError.invalidProgram "storage annotation local out of bounds")
                    else pure (ForInStep.yield (annotated.push id))
                  | _ => pure (ForInStep.yield annotated))
                (fun __s => pure (ForInStep.yield __s))) = Except.ok acc' ∧
          ∀ id, acc'.contains id =
            (acc.contains id || bbs.any (fun bb => bb.statements.any (MirSemantics.stmtHasStorageMarker id)))
  | [], [], acc, _, _ => ⟨acc, rfl, fun _ => by simp⟩
  | [], _ :: _, _, h_dec, _ => by cases h_dec
  | _ :: _, [], _, h_dec, _ => by
    dsimp only [mapOption, optMap2] at h_dec
    cases h_b0 : decodeBasicBlock types _ with
    | none => rw [h_b0] at h_dec; cases h_dec
    | some _ =>
      rw [h_b0] at h_dec
      cases h_r0 : mapOption (decodeBasicBlock types) _ with
      | none => rw [h_r0] at h_dec; cases h_dec
      | some _ => rw [h_r0] at h_dec; cases h_dec
  | rbb :: rrest, bb :: brest, acc, h_dec, h_all => by
    dsimp only [mapOption, optMap2] at h_dec
    cases h_b : decodeBasicBlock types rbb with
    | none => rw [h_b] at h_dec; cases h_dec
    | some bb' =>
      cases h_r : mapOption (decodeBasicBlock types) rrest with
      | none => rw [h_b, h_r] at h_dec; cases h_dec
      | some brest' =>
        rw [h_b, h_r] at h_dec
        injection h_dec with h_eq
        injection h_eq with hb_eq hrest_eq
        cases hb_eq; cases hrest_eq
        dsimp only [List.all] at h_all
        rw [Bool.and_eq_true] at h_all
        let ⟨h_stmts, _, _⟩ := decodeBasicBlock_inv h_b
        let ⟨acc₁, h_inner, h_c1⟩ :=
          alwaysLive_stmts_loop types n rbb.statements bb.statements acc h_stmts h_all.1
        let ⟨acc₂, h_outer, h_c2⟩ :=
          alwaysLive_blocks_loop types n rrest brest acc₁ h_r h_all.2
        refine ⟨acc₂, ?_, fun id => ?_⟩
        · rw [List.map_cons, List.forIn_cons]
          dsimp only [toMiriBasicBlock, bind, Bind.bind]
          rw [← Array.forIn_toList, h_inner]
          have h_eb : ∀ {α β : Type} (a : α) (f : α → Except Miri.Interpreter.StepError β),
              (Except.ok a).bind f = f a := fun _ _ => rfl
          rw [h_eb]
          rw [show (pure (ForInStep.yield acc₁) : Except Miri.Interpreter.StepError (ForInStep (Array Nat))) =
            Except.ok (ForInStep.yield acc₁) from rfl, h_eb]
          exact h_outer
        · rw [h_c2 id, h_c1 id]
          dsimp only [List.any]
          rw [Bool.or_assoc]

private theorem alwaysLiveVarsAndTemps_eq_clean (b : Miri.MIR.Body) :
    Miri.Interpreter.CallMachine.alwaysLiveVarsAndTemps b =
      Bind.bind
        (forIn b.basicBlocks.toList Array.empty fun (block : Miri.MIR.BasicBlock) (annotated : Array Nat) =>
          Bind.bind
            (forIn block.statements annotated fun (statement : Miri.MIR.Statement) (annotated : Array Nat) =>
              match mirStmtStorageMarker? statement with
              | some id =>
                if id ≥ b.locals.size then
                  Except.error (Miri.Interpreter.StepError.invalidProgram "storage annotation local out of bounds")
                else pure (ForInStep.yield (annotated.push id))
              | _ => pure (ForInStep.yield annotated))
            (fun __s => pure (ForInStep.yield __s)))
        (fun __s =>
          pure (List.filter (fun id => decide (id > b.argumentCount) && !__s.contains id)
            (List.range b.locals.size)).toArray) := by
  dsimp only [Miri.Interpreter.CallMachine.alwaysLiveVarsAndTemps]
  rw [← Array.forIn_toList]
  apply congrArg (fun x => Bind.bind x _)
  apply congrArg (fun f => forIn b.basicBlocks.toList Array.empty f)
  funext block annotated
  apply congrArg (fun x => Bind.bind x _)
  apply congrArg (fun f => forIn block.statements annotated f)
  funext statement annotated
  dsimp only [mirStmtStorageMarker?]
  cases statement.kind with
  | StorageLive id =>
    dsimp only
    cases Classical.em (id ≥ b.locals.size) with
    | inl h_ge => rw [ite_eq_left h_ge, ite_eq_left h_ge]; rfl
    | inr h_ge => rw [ite_eq_right h_ge, ite_eq_right h_ge]
  | StorageDead id =>
    dsimp only
    cases Classical.em (id ≥ b.locals.size) with
    | inl h_ge => rw [ite_eq_left h_ge, ite_eq_left h_ge]; rfl
    | inr h_ge => rw [ite_eq_right h_ge, ite_eq_right h_ge]
  | _ => rfl

private theorem alwaysLiveVarsAndTemps_toMiriBody (rp : RefProg)
    (rbody : RefBody) (body : Body)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_sa : storageAnnotationsInBounds body = true) :
    ∃ locals : Array Nat,
      Miri.Interpreter.CallMachine.alwaysLiveVarsAndTemps (toMiriBody rp.types rbody) =
        Except.ok locals ∧
      locals.toList =
        (List.range body.locals.length).filter
          (fun id => decide (id > body.argumentCount) && !hasStorageAnnotation body id) := by
  let ⟨h_arg_eq, h_locs, h_bbs, _, _⟩ := decodeBody_inv h_bdec
  have h_len : rbody.locals.length = body.locals.length := mapOption_length h_locs
  have h_bounds :
      body.basicBlocks.all (fun bb =>
        bb.statements.all (fun s =>
          match s with
          | .storageLive id | .storageDead id => Nat.blt id body.locals.length
          | _ => true)) = true := by
    dsimp only [storageAnnotationsInBounds] at h_sa
    exact h_sa
  let ⟨annotated, h_loop, h_cont⟩ :=
    alwaysLive_blocks_loop rp.types body.locals.length rbody.basicBlocks body.basicBlocks Array.empty h_bbs h_bounds
  refine ⟨(List.filter (fun id => decide (id > body.argumentCount) && !annotated.contains id)
      (List.range body.locals.length)).toArray, ?_, ?_⟩
  · rw [alwaysLiveVarsAndTemps_eq_clean]
    have h_sz_eq : (toMiriBody rp.types rbody).locals.size = body.locals.length := by
      dsimp only [toMiriBody]
      change (rbody.locals.map (canonicalTyId rp.types)).length = body.locals.length
      rw [List.length_map, h_len]
    simp only [h_sz_eq]
    dsimp only [toMiriBody]
    change (Bind.bind (forIn (rbody.basicBlocks.map (toMiriBasicBlock rp.types)) Array.empty _) _) = _
    rw [h_loop]
    dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    simp only [h_arg_eq]
  · apply List.filter_congr
    intro id _
    rw [h_cont id]
    have h_emp : (Array.empty : Array Nat).contains id = false := by simp [Array.empty]
    rw [h_emp, Bool.false_or]
    rfl

private theorem initLocalsLoop_length (body : Body) (args : List Val) :
    ∀ (idx : Nat) (tys : List MirTy),
      (initLocalsLoop body args idx tys).length = tys.length
  | _, [] => rfl
  | idx, _ :: rest => by
    dsimp only [initLocalsLoop, List.length]
    rw [initLocalsLoop_length body args (idx + 1) rest]

private theorem getElem?_initLocalsLoop (body : Body) (args : List Val) :
    ∀ (idx : Nat) (tys : List MirTy) (i : Nat) (ty : MirTy),
      MirSemantics.getElem? tys i = some ty →
      MirSemantics.getElem? (initLocalsLoop body args idx tys) i =
        some (if (idx + i).beq 0 then liveUninitSlot ty
              else if (idx + i).ble body.argumentCount then
                match MirSemantics.getElem? args (idx + i - 1) with
                | some v => .immediate (some v)
                | none => .dead
              else if hasStorageAnnotation body (idx + i) then .dead
              else liveUninitSlot ty)
  | _, [], _, _, h => by cases h
  | idx, ty :: _, 0, ty', h => by
    cases h
    dsimp only [initLocalsLoop, MirSemantics.getElem?]
    rw [Nat.add_zero]
    rfl
  | idx, _ :: rest, i + 1, ty, h => by
    dsimp only [initLocalsLoop, MirSemantics.getElem?]
    have h_ih := getElem?_initLocalsLoop body args (idx + 1) rest i ty h
    rw [Nat.add_right_comm idx 1 i] at h_ih
    exact h_ih

private theorem mirGetElem?_mirSetElem?_eq {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α},
      MirSemantics.setElem? xs i v = some xs' →
      MirSemantics.getElem? xs' i = some v
  | [], _, _, _, h => by cases h
  | _ :: rest, _, 0, v, h => by injection h with h_eq; cases h_eq; rfl
  | x :: rest, _, j + 1, v, h => by
    dsimp only [MirSemantics.setElem?] at h
    cases h_r : MirSemantics.setElem? rest j v with
    | none => rw [h_r] at h; cases h
    | some rest' =>
      rw [h_r] at h; injection h with h_eq; cases h_eq
      dsimp only [MirSemantics.getElem?]
      exact mirGetElem?_mirSetElem?_eq h_r

private theorem mirGetElem?_mirSetElem?_ne {α : Type} :
    ∀ {xs xs' : List α} {i j : Nat} {v : α},
      MirSemantics.setElem? xs i v = some xs' →
      j ≠ i →
      MirSemantics.getElem? xs' j = MirSemantics.getElem? xs j
  | [], _, _, _, _, h, _ => by cases h
  | _ :: rest, _, 0, 0, _, _, hne => False.elim (hne rfl)
  | _ :: rest, _, 0, k + 1, _, h, _ => by injection h with h_eq; cases h_eq; rfl
  | x :: rest, _, i + 1, 0, v, h, _ => by
    dsimp only [MirSemantics.setElem?] at h
    cases h_r : MirSemantics.setElem? rest i v with
    | none => rw [h_r] at h; cases h
    | some rest' => rw [h_r] at h; injection h with h_eq; cases h_eq; rfl
  | x :: rest, _, i + 1, k + 1, v, h, hne => by
    dsimp only [MirSemantics.setElem?] at h
    cases h_r : MirSemantics.setElem? rest i v with
    | none => rw [h_r] at h; cases h
    | some rest' =>
      rw [h_r] at h; injection h with h_eq; cases h_eq
      dsimp only [MirSemantics.getElem?]
      exact mirGetElem?_mirSetElem?_ne h_r (fun h_eq => hne (congrArg Nat.succ h_eq))

private theorem eStateM_bind_assoc {ε σ α β γ : Type}
    (x : EStateM ε σ α) (f : α → EStateM ε σ β) (g : β → EStateM ε σ γ) (s : σ) :
    ((EStateM.bind x f).bind g) s = EStateM.bind x (fun a => (f a).bind g) s := by
  dsimp only [EStateM.bind]
  cases x s <;> rfl

private theorem storageLiveDyn_loop_slots (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (body : Body)
    (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_c_len : cache.length = body.locals.length) :
    ∀ (ids : List Nat) (slots : List LocalSlot),
      (∀ id, id ∈ ids → id < body.locals.length) →
      SlotsMatchTys body.locals slots →
      ∃ slots' : List LocalSlot,
        SlotsMatchTys body.locals slots' ∧
        slots'.length = body.locals.length ∧
        (∀ k ty, MirSemantics.getElem? body.locals k = some ty →
          MirSemantics.getElem? slots' k =
            if k ∈ ids then some (liveUninitSlot ty) else MirSemantics.getElem? slots k) ∧
        forIn (m := EStateM Miri.Interpreter.StepError MiriStepState) ids PUnit.unit
          (fun localId (_ : PUnit) =>
            EStateM.bind (Miri.Interpreter.MachineHooks.storageLiveDyn (refStorageHooks rp.types) localId MemPlaceMeta.none)
              fun __r => EStateM.pure (ForInStep.yield PUnit.unit))
          (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots cache mem ctrl cm) =
          .ok PUnit.unit (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots' cache mem ctrl cm)
  | [], slots, _, h_inv =>
    ⟨slots, h_inv, SlotsMatchTys.length_eq h_inv, fun _ _ _ => rfl, rfl⟩
  | id :: rest, slots, h_in, h_inv => by
    have h_id_lt : id < body.locals.length := h_in id (by simp)
    cases h_ty : MirSemantics.getElem? body.locals id with
    | none => exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_id_lt (mirGetElem?_ge_of_none h_ty)))
    | some ty =>
      have h_sl_len : slots.length = body.locals.length := SlotsMatchTys.length_eq h_inv
      cases h_set : MirSemantics.setElem? slots id (liveUninitSlot ty) with
      | none =>
        have h_lt_slots : id < slots.length := by rw [h_sl_len]; exact h_id_lt
        cases mirSetElem?_some_of_lt slots id (liveUninitSlot ty) h_lt_slots with
        | intro _ h_some => rw [h_some] at h_set; cases h_set
      | some slots₁ =>
        have h_sld := storageLiveDyn_ref_eq rp ctx rbody body blockIdx stmtIdx slots cache mem ctrl cm
          id h_bdec h_c_len h_inv
        dsimp only at h_sld
        rw [h_ty] at h_sld
        dsimp only at h_sld
        rw [h_set] at h_sld
        dsimp only at h_sld
        have h_inv₁ : SlotsMatchTys body.locals slots₁ :=
          SlotsMatchTys.setElem? h_inv h_ty (slotMatchesTy_liveUninitSlot ty) h_set
        let ⟨slots', h_inv', h_len', h_get', h_rest⟩ :=
          storageLiveDyn_loop_slots rp c ctx rbody body blockIdx stmtIdx cache mem ctrl cm
            h_bdec h_c_len rest slots₁ (fun x hx => h_in x (by simp [hx])) h_inv₁
        refine ⟨slots', h_inv', h_len', ?_, ?_⟩
        · intro k tyk h_tyk
          rw [h_get' k tyk h_tyk]
          cases Classical.em (k ∈ rest) with
          | inl hk_rest =>
            have hk_all : k ∈ id :: rest := by simp [hk_rest]
            rw [ite_eq_left hk_rest, ite_eq_left hk_all]
          | inr hk_rest =>
            rw [ite_eq_right hk_rest]
            cases Classical.em (k = id) with
            | inl hk_id =>
              subst hk_id
              rw [h_ty] at h_tyk; injection h_tyk with h_teq; subst h_teq
              have hk_all : k ∈ k :: rest := by simp
              rw [ite_eq_left hk_all]
              exact mirGetElem?_mirSetElem?_eq h_set
            | inr hk_id =>
              have hk_all : ¬ (k ∈ id :: rest) := by simp [hk_id, hk_rest]
              rw [ite_eq_right hk_all]
              exact mirGetElem?_mirSetElem?_ne h_set hk_id
        · rw [List.forIn_cons]
          dsimp only [bind, Bind.bind]
          rw [eStateM_bind_assoc, eStateM_bind_ok h_sld]
          exact h_rest

private theorem stack_updateCurrentLocation_push
    (below : Array (Miri.Interpreter.Frame Miri.Memory.Provenance Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra))
    (fr : Miri.Interpreter.Frame Miri.Memory.Provenance Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (h_nz : 0 < fr.body.basicBlocks.size) :
    (Miri.Interpreter.Stack.mk (below.push fr)).updateCurrentLocation (.mir .start) =
      .ok (Miri.Interpreter.Stack.mk (below.push { fr with location := .mir .start })) := by
  dsimp only [Miri.Interpreter.Stack.updateCurrentLocation]
  have h_back : (below.push fr).back? = some fr := by
    dsimp only [Array.back?]
    rw [Array.size_push, Nat.add_sub_cancel, Array.getElem?_push_size]
  rw [h_back]
  dsimp only [Miri.Interpreter.Frame.setLocation, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure, Miri.MIR.Location.start]
  rw [dite_eq_left h_nz, ite_eq_left (Nat.zero_le _)]
  dsimp only
  have h_lt : (below.push fr).size - 1 < (below.push fr).size := by
    rw [Array.size_push, Nat.add_sub_cancel]
    exact Nat.lt_succ_self _
  rw [dite_eq_left h_lt]
  apply congrArg Except.ok
  apply congrArg Miri.Interpreter.Stack.mk
  apply Array.toList_inj.mp
  simp

private theorem pushDone_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (body : Body)
    (slots : List LocalSlot) (cache : List Bool) (argVals : List Val)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_nb : body.basicBlocks.isEmpty = false)
    (h_arg : Nat.blt body.argumentCount body.locals.length = true)
    (h_sa : storageAnnotationsInBounds body = true)
    (h_c_len : cache.length = body.locals.length)
    (h_inv : SlotsMatchTys body.locals slots)
    (_h_ctx_loc : ctx.locOverride = some (.unwinding ⟨0⟩))
    (h_slots_pre :
      ∀ (k : Nat) (ty : MirTy), MirSemantics.getElem? body.locals k = some ty →
        if 1 ≤ k ∧ k ≤ body.argumentCount then
          MirSemantics.getElem? slots k =
            some (match MirSemantics.getElem? argVals (k - 1) with
              | some v => .immediate (some v)
              | none => .dead)
        else
          MirSemantics.getElem? slots k = some .dead) :
    let st := mkGenSimState rp ctx rbody 0 0 body.locals slots cache mem ctrl cm
    Miri.Interpreter.CallMachine.pushDone (refLifecycle rp.types) st =
      .ok () (mkGenSimState rp { ctx with locOverride := none } rbody 0 0
        body.locals (initLocalsLoop body argVals 0 body.locals) cache mem ctrl cm) := by
  intro st
  have h_lt0 : 0 < body.locals.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.blt_eq.mp h_arg)
  cases h_ty0 : MirSemantics.getElem? body.locals 0 with
  | none => exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_lt0 (mirGetElem?_ge_of_none h_ty0)))
  | some retTy =>
    have h_sl_len : slots.length = body.locals.length := SlotsMatchTys.length_eq h_inv
    cases h_set0 : MirSemantics.setElem? slots 0 (liveUninitSlot retTy) with
    | none =>
      let ⟨_, h_some⟩ := mirSetElem?_some_of_lt slots 0 (liveUninitSlot retTy) (by rw [h_sl_len]; exact h_lt0)
      rw [h_some] at h_set0; cases h_set0
    | some slots₁ =>
      have h_sld0 := storageLiveDyn_ref_eq rp ctx rbody body 0 0 slots cache mem ctrl cm
        0 h_bdec h_c_len h_inv
      dsimp only at h_sld0
      rw [h_ty0] at h_sld0
      dsimp only at h_sld0
      rw [h_set0] at h_sld0
      dsimp only at h_sld0
      have h_inv₁ : SlotsMatchTys body.locals slots₁ :=
        SlotsMatchTys.setElem? h_inv h_ty0 (slotMatchesTy_liveUninitSlot retTy) h_set0
      let ⟨localsArr, h_al_ok, h_al_list⟩ :=
        alwaysLiveVarsAndTemps_toMiriBody rp rbody body h_bdec h_sa
      have h_in_range : ∀ x, x ∈ localsArr.toList → x < body.locals.length := by
        intro x hx
        rw [h_al_list, List.mem_filter, List.mem_range] at hx
        exact hx.1
      let ⟨slots₂, _, h_len2, h_get2, h_loop⟩ :=
        storageLiveDyn_loop_slots rp c ctx rbody body 0 0 cache mem ctrl cm
          h_bdec h_c_len localsArr.toList slots₁ h_in_range h_inv₁
      have h_slots2_eq : slots₂ = initLocalsLoop body argVals 0 body.locals := by
        apply list_eq_of_getElem?_eq
        · rw [h_len2, initLocalsLoop_length]
        · intro k
          cases h_tyk : MirSemantics.getElem? body.locals k with
          | none =>
            have h_ge : body.locals.length ≤ k := mirGetElem?_ge_of_none h_tyk
            rw [mirGetElem?_none_of_ge (by rw [h_len2]; exact h_ge)]
            rw [mirGetElem?_none_of_ge (by rw [initLocalsLoop_length]; exact h_ge)]
          | some ty =>
            rw [h_get2 k ty h_tyk]
            rw [getElem?_initLocalsLoop body argVals 0 body.locals k ty h_tyk]
            rw [Nat.zero_add]
            have h_k_lt : k < body.locals.length := mirGetElem?_lt_of_some h_tyk
            have h_mem_iff :
                (k ∈ localsArr.toList) ↔
                  (k > body.argumentCount ∧ hasStorageAnnotation body k = false) := by
              rw [h_al_list, List.mem_filter, List.mem_range]
              constructor
              · intro ⟨_, h_cond⟩
                rw [Bool.and_eq_true, decide_eq_true_eq] at h_cond
                exact ⟨h_cond.1, by
                  cases ha : hasStorageAnnotation body k with
                  | false => rfl
                  | true => rw [ha] at h_cond; cases h_cond.2⟩
              · intro ⟨h_gt, h_nh⟩
                exact ⟨h_k_lt, by simp [decide_eq_true h_gt, h_nh]⟩
            cases k with
            | zero =>
              have h_nmem : ¬ ((0 : Nat) ∈ localsArr.toList) := fun h => by
                exact Nat.not_lt_zero _ (h_mem_iff.mp h).1
              rw [ite_eq_right h_nmem]
              rw [h_ty0] at h_tyk; injection h_tyk with h_teq; subst h_teq
              exact mirGetElem?_mirSetElem?_eq h_set0
            | succ k' =>
              have h_ne0 : Nat.beq (k' + 1) 0 = false := rfl
              rw [h_ne0, ite_false_eq]
              cases Classical.em (k' + 1 ≤ body.argumentCount) with
              | inl h_le =>
                have h_ble : Nat.ble (k' + 1) body.argumentCount = true := Nat.ble_eq.mpr h_le
                have h_nmem : ¬ ((k' + 1) ∈ localsArr.toList) := fun h => by
                  exact Nat.not_le_of_gt (h_mem_iff.mp h).1 h_le
                rw [ite_eq_right h_nmem, h_ble, ite_true_eq]
                rw [mirGetElem?_mirSetElem?_ne h_set0 (Nat.succ_ne_zero k')]
                have h_pre := h_slots_pre (k' + 1) ty h_tyk
                rw [ite_eq_left ⟨Nat.succ_pos _, h_le⟩] at h_pre
                exact h_pre
              | inr h_le =>
                have h_gt : k' + 1 > body.argumentCount := Nat.lt_of_not_le h_le
                have h_ble : Nat.ble (k' + 1) body.argumentCount = false := by
                  cases hb : Nat.ble (k' + 1) body.argumentCount with
                  | false => rfl
                  | true => exact False.elim (h_le (Nat.ble_eq.mp hb))
                rw [h_ble, ite_false_eq]
                cases h_ann : hasStorageAnnotation body (k' + 1) with
                | true =>
                  have h_nmem : ¬ ((k' + 1) ∈ localsArr.toList) := fun h => by
                    rw [(h_mem_iff.mp h).2] at h_ann; cases h_ann
                  rw [ite_eq_right h_nmem, ite_true_eq]
                  rw [mirGetElem?_mirSetElem?_ne h_set0 (Nat.succ_ne_zero k')]
                  have h_pre := h_slots_pre (k' + 1) ty h_tyk
                  rw [ite_eq_right (fun ⟨_, h_le'⟩ => h_le h_le')] at h_pre
                  exact h_pre
                | false =>
                  have h_mem : (k' + 1) ∈ localsArr.toList := h_mem_iff.mpr ⟨h_gt, h_ann⟩
                  rw [ite_eq_left h_mem, ite_false_eq]
      have h_cf_mid :
          Miri.Interpreter.MachineHooks.currentFrame
              (mkGenSimState rp ctx rbody 0 0 body.locals slots₁ cache mem ctrl cm) =
            .ok (mkGenSimFrame rp ctx rbody 0 0 body.locals slots₁ cache)
              (mkGenSimState rp ctx rbody 0 0 body.locals slots₁ cache mem ctrl cm) :=
        currentFrame_mkGenSimState rp ctx rbody 0 0 body.locals slots₁ cache mem ctrl cm
      have h_upd_loc :
          (mkGenSimState rp ctx rbody 0 0 body.locals slots₂ cache mem ctrl cm).stack.updateCurrentLocation
              (.mir .start) =
            .ok (mkGenSimState rp { ctx with locOverride := none } rbody 0 0 body.locals
              slots₂ cache mem ctrl cm).stack := by
        dsimp only [mkGenSimState, mkRefMiriStackState]
        have h_sz_bbs : 0 < (mkGenSimFrame rp ctx rbody 0 0 body.locals slots₂ cache).body.basicBlocks.size := by
          dsimp only [mkGenSimFrame, toMiriBody]
          change 0 < (rbody.basicBlocks.map (toMiriBasicBlock rp.types)).length
          rw [List.length_map]
          let ⟨_, _, h_bbs, _, _⟩ := decodeBody_inv h_bdec
          have h_len_bbs := mapOption_length h_bbs
          rw [h_len_bbs]
          cases h_bb0 : body.basicBlocks with
          | nil => rw [h_bb0] at h_nb; cases h_nb
          | cons _ _ => exact Nat.succ_pos _
        have h_s := stack_updateCurrentLocation_push ctx.below
          (mkGenSimFrame rp ctx rbody 0 0 body.locals slots₂ cache) h_sz_bbs
        exact h_s
      dsimp only [st, Miri.Interpreter.CallMachine.pushDone, refLifecycle, bind, Bind.bind,
        pure, Pure.pure, get, getThe, MonadStateOf.get, set, MonadStateOf.set]
      rw [eStateM_bind_ok h_sld0]
      rw [eStateM_bind_ok h_cf_mid]
      dsimp only [mkGenSimFrame]
      rw [h_al_ok]
      dsimp only
      rw [show ∀ {ε σ α β : Type} (a : α) (f : α → EStateM ε σ β) (s : σ),
          ((EStateM.pure a).bind f) s = f a s from fun _ _ _ => rfl]
      rw [← Array.forIn_toList]
      rw [eStateM_bind_ok h_loop]
      dsimp only [EStateM.bind, EStateM.get, EStateM.set]
      rw [h_upd_loc, h_slots2_eq]
      rfl

private theorem pushRaw_ref_eq (rp : RefProg)
    (ctx : SimFrameCtx) (rbody calleeRbody : RefBody)
    (bodyLocals calleeLocals : List MirTy)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (slots : List LocalSlot)
    (cache : List Bool) (calleeBody : Body) (fnTag : DefId)
    (dstLocalId : LocalId) (dstTy : MirTy) (retTarget? : Option BasicBlockId)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory)
    (h_cbdec : decodeBody rp.types calleeRbody = some calleeBody)
    (h_clocs : calleeLocals = calleeBody.locals)
    (h_tr : refTopRelevanceValid (ctx.below.size + 1) ctx.topRel?) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    let oldFr := mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
    let calleeCtx : SimFrameCtx :=
      { (SimFrameCtx.call rp.types (ctx.below.push oldFr) (some (ctx.below.size + 1))
          fnTag ctx.below.size dstLocalId dstTy retTarget?) with
        locOverride := some (.unwinding ⟨0⟩) }
    Miri.Interpreter.CallMachine.pushRaw (refLifecycle rp.types) false
        { kind := .Item fnTag, args := List.toArray [] }
        { identity := .ofCanonicalIndex fnTag, body := toMiriBody rp.types calleeRbody }
        (.frameLocal ctx.below.size dstLocalId none (refLocalLayoutForTy rp.types dstTy)
          (.ofAllocationToken 0))
        (.goto retTarget? .Unreachable) st =
      .ok () (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeLocals
        (List.replicate calleeLocals.length .dead)
        (List.replicate calleeLocals.length false) mem ctrl cm) := by
  intro st oldFr calleeCtx
  subst h_clocs
  let ⟨_, h_locs, _, _, _⟩ := decodeBody_inv h_cbdec
  have h_cb_len : calleeRbody.locals.length = calleeBody.locals.length := mapOption_length h_locs
  have h_frame_locals :
      Array.replicate (toMiriBody rp.types calleeRbody).locals.size
          ({ value := .dead, layout := none } :
            Miri.Interpreter.LocalState Miri.Memory.Provenance Miri.Interpreter.LocalLayout) =
        ⟨liftLocalsCached rp.types calleeBody.locals
          (List.replicate calleeBody.locals.length .dead)
          (List.replicate calleeBody.locals.length false)⟩ := by
    rw [liftLocalsCached_dead_false]
    dsimp only [toMiriBody]
    change Array.replicate (calleeRbody.locals.map (canonicalTyId rp.types)).length _ = _
    rw [List.length_map, h_cb_len]
    rfl
  let newFr := mkGenSimFrame rp calleeCtx calleeRbody 0 0 calleeBody.locals
    (List.replicate calleeBody.locals.length .dead)
    (List.replicate calleeBody.locals.length false)
  let stMid :=
    mkGenSimState rp { calleeCtx with topRel? := ctx.topRel? } calleeRbody 0 0 calleeBody.locals
      (List.replicate calleeBody.locals.length .dead)
      (List.replicate calleeBody.locals.length false) mem ctrl cm
  have h_afterStackPush :
      Miri.Interpreter.FrameRelevance.afterStackPush false stMid =
        .ok () (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals
          (List.replicate calleeBody.locals.length .dead)
          (List.replicate calleeBody.locals.length false) mem ctrl cm) := by
    cases h_tr_case : ctx.topRel? with
    | none =>
      rw [h_tr_case] at h_tr
      dsimp only [refTopRelevanceValid] at h_tr
      have h_sz0 : ctx.below.size = 0 := Nat.succ_inj.mp h_tr
      have h_e : ctx.below = Array.empty := Array.eq_empty_iff_size_eq_zero.mpr h_sz0
      dsimp only [stMid, calleeCtx, mkGenSimState, mkRefMiriStackState]
      rw [h_e, h_tr_case]
      rfl
    | some k =>
      rw [h_tr_case] at h_tr
      have h_k : k = ctx.below.size := h_tr.2
      subst h_k
      have h_stack_eq : stMid.stack.frames = (ctx.below.push oldFr).push newFr := rfl
      have h_get : stMid.stack.frames[ctx.below.size]? = some oldFr := by
        rw [h_stack_eq, Array.getElem?_push_lt (by rw [Array.size_push]; exact Nat.lt_succ_self _),
          Array.getElem_push_eq]
      have h_sz_sub : stMid.stack.frames.size - 1 = ctx.below.size + 1 := by
        rw [h_stack_eq, Array.size_push, Array.size_push, Nat.add_sub_cancel]
      have h_cf := currentFrame_mkGenSimState rp { calleeCtx with topRel? := some ctx.below.size }
        calleeRbody 0 0 calleeBody.locals (List.replicate calleeBody.locals.length .dead)
        (List.replicate calleeBody.locals.length false) mem ctrl cm
      have h_stMid_eq :
          stMid = mkGenSimState rp { calleeCtx with topRel? := some ctx.below.size }
            calleeRbody 0 0 calleeBody.locals (List.replicate calleeBody.locals.length .dead)
            (List.replicate calleeBody.locals.length false) mem ctrl cm := by
        dsimp only [stMid]; rw [h_tr_case]
      rw [h_stMid_eq]
      let stMid' := mkGenSimState rp { calleeCtx with topRel? := some ctx.below.size }
        calleeRbody 0 0 calleeBody.locals (List.replicate calleeBody.locals.length .dead)
        (List.replicate calleeBody.locals.length false) mem ctrl cm
      let activeFn : Miri.Interpreter.MachineHooks.M Unit RefUser Miri.Concurrency.ThreadRecord :=
        bind get fun __do_lift =>
          match __do_lift.machine.threads.activeThread? with
          | some thread => pure thread
          | _ => throw (.invalidProgram "active relevance thread missing")
      let setFn : Option Nat → Miri.Interpreter.MachineHooks.M Unit RefUser Unit := fun value =>
        Bind.bind activeFn fun _ =>
          modify fun state => { state with machine := { state.machine with threads := {
            state.machine.threads with threads := state.machine.threads.threads.mapIdx fun index thread =>
              if index == state.machine.threads.activeThread.toNat then
                { thread with topUserRelevantFrame := value } else thread } } }
      have h_after_cf :
          Miri.Interpreter.FrameRelevance.afterStackPush false stMid' =
            (match stMid'.stack.frames[ctx.below.size]? with
             | none =>
               Bind.bind (throw (Miri.Interpreter.StepError.invalidProgram "user relevance cache index out of bounds"))
                 fun current =>
                   if (255 : UInt8) ≥ current then setFn (some (stMid'.stack.frames.size - 1)) else pure ()
             | some frame =>
               Bind.bind (pure frame.extra.userRelevance)
                 fun current =>
                   if (255 : UInt8) ≥ current then setFn (some (stMid'.stack.frames.size - 1)) else pure ()) stMid' := by
        dsimp only [Miri.Interpreter.FrameRelevance.afterStackPush, bind, Bind.bind]
        rw [eStateM_bind_ok h_cf]
        rfl
      have h_get' : stMid'.stack.frames[ctx.below.size]? = some oldFr := by
        change stMid.stack.frames[ctx.below.size]? = some oldFr
        exact h_get
      have h_sz_sub' : stMid'.stack.frames.size - 1 = ctx.below.size + 1 := by
        change stMid.stack.frames.size - 1 = ctx.below.size + 1
        exact h_sz_sub
      change Miri.Interpreter.FrameRelevance.afterStackPush false stMid' = _
      rw [h_after_cf, h_get']
      dsimp only [oldFr, mkGenSimFrame, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
      rw [ite_eq_left (by decide), h_sz_sub']
      rfl
  dsimp only [Miri.Interpreter.CallMachine.pushRaw, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, Miri.Interpreter.Frame.create, Miri.Interpreter.MachineHooks.initFrame,
    Miri.Interpreter.FrameMetadata.userRelevance, refLifecycle]
  dsimp only [st, mkGenSimState, mkRefMiriStackState]
  rw [h_frame_locals]
  exact h_afterStackPush

/-! ### Section 5C: Call Terminator Correspondence (`evalCallTerminator`) -/

private theorem withValidation_refExecCfg_idem (rp : RefProg) :
    Miri.Interpreter.ExecutionMachine.withValidation (refExecCfg rp) refLimits =
      refExecCfg rp := rfl

private theorem cacheTouch_preserves_true {cache : List Bool} {i j : Nat}
    (h_i : MirSemantics.getElem? cache i = some true) :
    MirSemantics.getElem? (cacheTouch cache j) i = some true := by
  cases Classical.em (i = j) with
  | inl hij => subst hij; exact getElem?_cacheTouch_self h_i
  | inr hij => rw [getElem?_cacheTouch_ne (Ne.symm hij)]; exact h_i

private theorem operandCacheTouch_preserves_true {cache : List Bool} {i : Nat}
    (op : Operand) (h_i : MirSemantics.getElem? cache i = some true) :
    MirSemantics.getElem? (operandCacheTouch cache op) i = some true := by
  cases op with
  | copy p | move p => exact cacheTouch_preserves_true h_i
  | constant _ => exact h_i

private noncomputable def callCacheTouch (dstId : LocalId)
    (args : List Operand) (cache : List Bool) : List Bool :=
  args.foldl operandCacheTouch (cacheTouch cache dstId)

private theorem callCacheTouch_length (dstId : LocalId) (args : List Operand)
    (cache : List Bool) :
    (callCacheTouch dstId args cache).length = cache.length := by
  dsimp only [callCacheTouch]
  have h_fold : ∀ (xs : List Operand) (c : List Bool),
      (xs.foldl operandCacheTouch c).length = c.length := by
    intro xs
    induction xs with
    | nil => intro c; rfl
    | cons x rest ih =>
      intro c
      dsimp only [List.foldl]
      rw [ih, operandCacheTouch_length]
  rw [h_fold, cacheTouch_length]

private theorem updateCacheLoop_args_foldl :
    ∀ (args : List Operand) (cache : List Bool),
      updateCacheLoop (fun idx => args.any fun a => operandTouchesLocal a idx) 0 cache =
        args.foldl operandCacheTouch cache
  | [], cache => updateCacheLoop_false _ 0 cache (fun _ _ => rfl)
  | op :: rest, cache => by
    have h_fn :
        (fun idx => (op :: rest).any fun a => operandTouchesLocal a idx) =
          (fun idx => operandTouchesLocal op idx ||
            rest.any fun a => operandTouchesLocal a idx) := rfl
    rw [h_fn, ← updateCacheLoop_comp (operandTouchesLocal op) _ 0 cache,
      updateCacheLoop_operandCacheTouch]
    exact updateCacheLoop_args_foldl rest (operandCacheTouch cache op)

private theorem updateCacheLoop_callCacheTouch (dstId : LocalId)
    (args : List Operand) (cache : List Bool) :
    updateCacheLoop
        (fun idx => Nat.beq dstId idx || args.any fun a => operandTouchesLocal a idx)
        0 cache =
      callCacheTouch dstId args cache := by
  rw [← updateCacheLoop_comp (fun idx => Nat.beq dstId idx) _ 0 cache,
    updateCacheLoop_cacheTouch]
  exact updateCacheLoop_args_foldl args (cacheTouch cache dstId)

private theorem mkGenSimState_frameIndex (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory) :
    (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm).stack.frameIndex =
      .ok ctx.below.size := by
  dsimp only [mkGenSimState, mkRefMiriStackState]
  rw [stack_frameIndex_push]

private theorem evalOperand_function_tag_ok (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (fnTag : Nat) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
    let funcOp : Miri.MIR.Operand :=
      .Constant { span := { id := 0 }, userType := none, value := .Val .ZeroSized (fnTyBase rp.types + fnTag) }
    calls.evalOperandAt c (.instruction "function") funcOp st =
      .ok { op := .immediate .uninit, layout := { ty := fnTyBase rp.types + fnTag, layout := refUnitLayoutData } } st := by
  intro st calls funcOp
  have h_deinit : (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).deinitMovedPlace = true := rfl
  have h_constAt :
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).constantAt =
        (refOperandLeaves rp.types).constantAt := rfl
  dsimp only [calls, Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  dsimp only [Miri.Interpreter.ExecutionCalls.make, Miri.Interpreter.OperandMachine.evalOperandAt, funcOp,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [h_constAt, h_deinit]
  dsimp only [refOperandLeaves, ite_true_eq]
  rw [show (Array.push (Miri.Interpreter.OperandPath.instruction "function")
      (Miri.Interpreter.OperandPathElement.field "constant") ==
      Array.push (Miri.Interpreter.OperandPath.instruction "function")
      (Miri.Interpreter.OperandPathElement.field "constant")) = true from by decide]
  dsimp only [ite_true_eq]
  rw [Nat.ble_eq.mpr (Nat.le_add_right _ _)]
  rfl

private theorem placeToOp_local_live (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (optVal : Option Val)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal)) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
    let rsp : Miri.Interpreter.RuntimeStackPlace Miri.Memory.Provenance :=
      .frameLocal ctx.below.size id none (refLocalLayoutForTy rp.types ty) (.ofAllocationToken 0)
    calls.placeToOp c rsp st =
      .ok ⟨.immediate (optValToMiriImm ty optVal), refLocalLayoutForTy rp.types ty⟩
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
          (cacheTouch cache id) mem ctrl cm) := by
  intro st calls rsp
  have h_fi := placeHooks_frameIndex_ok rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
  have h_dbg : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.debugAssertions = false := rfl
  have h_lo := placeMachine_localToOp_live rp c ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    id ty optVal h_locs h_c_len h_ty h_sl
  dsimp only [calls, Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  dsimp only [Miri.Interpreter.ExecutionCalls.make, rsp, Miri.Interpreter.RuntimeStackPlace.toRuntimePlace,
    Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    bind, Bind.bind, pure, Pure.pure]
  change EStateM.bind ((Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.frameIndex) _ st = _
  rw [eStateM_bind_ok h_fi]
  rw [show (ctx.below.size != ctx.below.size) = false from by simp, ite_false_eq]
  rw [h_dbg, ite_false_eq]
  have h_lo' :
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.localToOp c id st =
        .ok ⟨.immediate (optValToMiriImm ty optVal), refLocalLayoutForTy rp.types ty⟩
          (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots (cacheTouch cache id) mem ctrl cm) := h_lo
  change EStateM.bind
    ((Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.localToOp c id) _ st = _
  rw [eStateM_bind_ok h_lo']
  rw [ite_false_eq]
  rfl

private theorem placeToOp_local_dead (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
    let rsp : Miri.Interpreter.RuntimeStackPlace Miri.Memory.Provenance :=
      .frameLocal ctx.below.size id none (refLocalLayoutForTy rp.types ty) (.ofAllocationToken 0)
    ∃ st', calls.placeToOp c rsp st = .error (.stack (.localExpectedLive id)) st' := by
  intro st calls rsp
  have h_fi := placeHooks_frameIndex_ok rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
  have h_dbg : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.debugAssertions = false := rfl
  let ⟨st', h_lo⟩ := placeMachine_localToOp_dead rp c ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    id ty h_locs h_c_len h_ty h_sl
  refine ⟨st', ?_⟩
  dsimp only [calls, Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  dsimp only [Miri.Interpreter.ExecutionCalls.make, rsp, Miri.Interpreter.RuntimeStackPlace.toRuntimePlace,
    Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    bind, Bind.bind, pure, Pure.pure]
  change EStateM.bind ((Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.frameIndex) _ st = _
  rw [eStateM_bind_ok h_fi]
  rw [show (ctx.below.size != ctx.below.size) = false from by simp, ite_false_eq]
  rw [h_dbg, ite_false_eq]
  have h_lo' :
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.localToOp c id st =
        .error (.stack (.localExpectedLive id)) st' := h_lo
  change EStateM.bind
    ((Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.localToOp c id) _ st = _
  dsimp only [EStateM.bind]
  rw [h_lo']

private theorem placeMachine_layoutLocal_ok (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (slot : LocalSlot)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
    calls.localLayout c id st =
      .ok (refLocalLayoutForTy rp.types ty)
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
          (cacheTouch cache id) mem ctrl cm) := by
  intro st calls
  let ⟨b, h_c⟩ := getElem?_some_of_length_eq h_c_len.symm h_ty
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
  have h_gl := mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache id ty slot b h_ty h_sl h_c
  dsimp only [calls, Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  dsimp only [Miri.Interpreter.ExecutionCalls.make, Miri.Interpreter.PlaceMachine.layoutLocal,
    bind, Bind.bind]
  rw [eStateM_bind_ok h_cf]
  rw [h_gl]
  dsimp only [pure, Pure.pure]
  rw [eStateM_bind_pure]
  cases b with
  | true =>
    dsimp only [refLocalStateOfSlotWithCache, pure, Pure.pure, EStateM.pure, ite_true_eq]
    rw [cacheTouch_eq_self_of_true h_c]
  | false =>
    dsimp only [refLocalStateOfSlotWithCache, bind, Bind.bind, pure, Pure.pure]
    rw [ite_false_eq]
    dsimp only
    have h_cl : (refExecCfg rp).compiler.layout c id st = .ok (refLocalLayoutForTy rp.types ty) st :=
      operandHooks_compiler_layout_ok rp ctx c rbody blockIdx stmtIdx
        bodyLocals slots cache mem ctrl cm id ty h_locs h_ty
    have h_gc := mkGenSimFrame_getOrCacheLocalLayout_some rp ctx rbody blockIdx stmtIdx
      bodyLocals slots cache id ty slot false (refLocalLayoutForTy rp.types ty)
      h_ty h_sl h_c (fun _ => rfl)
    rw [eStateM_bind_ok h_cl, eStateM_bind_ok h_cf, h_gc]
    change (EStateM.bind (EStateM.pure _) _) st = _
    rw [eStateM_bind_pure]
    dsimp only
    rw [eStateM_bind_ok (setCurrentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
      bodyLocals slots slots cache (cacheTouch cache id) mem ctrl cm)]
    rfl

private noncomputable def evalCallArgOpt (callerLocalsTys : List MirTy) (locals : List LocalSlot)
    (opnd : Operand) (paramTy : MirTy) :
    Except FaultKind (Option Val × List LocalSlot) :=
  match opnd with
  | .copy place =>
    if !place.projection.isEmpty then .error .unsupported
    else
      match MirSemantics.getElem? callerLocalsTys place.localId, MirSemantics.getElem? locals place.localId with
      | some _ty, some .dead => .error .undefined
      | some ty, some (.immediate optVal) =>
        if !ty.beq paramTy then .error .unsupported
        else .ok (optVal, locals)
      | _, _ => .error .unsupported
  | .move place =>
    if !place.projection.isEmpty then .error .unsupported
    else
      match MirSemantics.getElem? callerLocalsTys place.localId, MirSemantics.getElem? locals place.localId with
      | some _ty, some .dead => .error .undefined
      | some ty, some (.immediate optVal) =>
        if !ty.beq paramTy then .error .unsupported
        else
          match MirSemantics.setElem? locals place.localId (liveUninitSlot ty) with
          | some locals' => .ok (optVal, locals')
          | none => .error .unsupported
      | _, _ => .error .unsupported
  | .constant c =>
    if !c.ty.beq paramTy then .error .unsupported
    else
      match evalConstLit c.ty c.lit with
      | .ok v => .ok (some v, locals)
      | .error k => .error k

private noncomputable def evalCallArgsOpt (callerLocalsTys : List MirTy) :
    List LocalSlot → List Operand → List MirTy →
      Except FaultKind (List (MirTy × Option Val) × List LocalSlot)
  | locals, [], [] => .ok ([], locals)
  | locals, opnd :: restArgs, paramTy :: restParams =>
    match evalCallArgOpt callerLocalsTys locals opnd paramTy with
    | .error k => .error k
    | .ok (optVal, locals₁) =>
      match evalCallArgsOpt callerLocalsTys locals₁ restArgs restParams with
      | .error k => .error k
      | .ok (restVals, locals₂) => .ok ((paramTy, optVal) :: restVals, locals₂)
  | _, _, _ => .error .unsupported

private def allSomeVals (xs : List (MirTy × Option Val)) : Option (List Val) :=
  xs.foldr (fun p acc => match p.2 with | none => none | some v => acc.map (v :: ·)) (some [])

private theorem allSomeVals_nil : allSomeVals [] = some [] := rfl

private theorem allSomeVals_cons_none (t : MirTy) (rest : List (MirTy × Option Val)) :
    allSomeVals ((t, none) :: rest) = none := rfl

private theorem allSomeVals_cons_some (t : MirTy) (v : Val) (rest : List (MirTy × Option Val)) :
    allSomeVals ((t, some v) :: rest) = (allSomeVals rest).map (v :: ·) := rfl

private theorem evalCallArgOpt_preserves_slots_match {tys : List MirTy} {slots slots' : List LocalSlot}
    {opnd : Operand} {paramTy : MirTy} {optVal : Option Val}
    (h_inv : SlotsMatchTys tys slots)
    (h_ok : evalCallArgOpt tys slots opnd paramTy = .ok (optVal, slots')) :
    SlotsMatchTys tys slots' ∧
    (match opnd with
     | .constant c => ∃ v, optVal = some v ∧ checkVal v c.ty = true ∧ c.ty = paramTy
     | _ => SlotMatchesTy paramTy (.immediate optVal)) := by
  cases opnd with
  | copy place =>
    dsimp only [evalCallArgOpt] at h_ok
    cases h_pe : place.projection.isEmpty with
    | false => rw [h_pe] at h_ok; cases h_ok
    | true =>
      rw [h_pe, Bool.not_true, ite_false_eq] at h_ok
      cases h_ty : MirSemantics.getElem? tys place.localId with
      | none => rw [h_ty] at h_ok; cases h_ok
      | some ty =>
        rw [h_ty] at h_ok
        cases h_sl : MirSemantics.getElem? slots place.localId with
        | none => rw [h_sl] at h_ok; cases h_ok
        | some sl =>
          rw [h_sl] at h_ok
          cases sl with
          | dead | indirect _ | partialTuple _ => cases h_ok
          | immediate ov =>
            dsimp only at h_ok
            cases h_beq : ty.beq paramTy with
            | false => rw [h_beq] at h_ok; cases h_ok
            | true =>
              rw [h_beq, Bool.not_true, ite_false_eq] at h_ok
              injection h_ok with h_tup
              injection h_tup with h_ov h_sl_eq
              cases h_ov; cases h_sl_eq
              have h_teq : ty = paramTy := MirTy.eq_of_beq h_beq
              cases h_teq
              exact ⟨h_inv, SlotsMatchTys.getElem? h_inv h_ty h_sl⟩
  | move place =>
    dsimp only [evalCallArgOpt] at h_ok
    cases h_pe : place.projection.isEmpty with
    | false => rw [h_pe] at h_ok; cases h_ok
    | true =>
      rw [h_pe, Bool.not_true, ite_false_eq] at h_ok
      cases h_ty : MirSemantics.getElem? tys place.localId with
      | none => rw [h_ty] at h_ok; cases h_ok
      | some ty =>
        rw [h_ty] at h_ok
        cases h_sl : MirSemantics.getElem? slots place.localId with
        | none => rw [h_sl] at h_ok; cases h_ok
        | some sl =>
          rw [h_sl] at h_ok
          cases sl with
          | dead | indirect _ | partialTuple _ => cases h_ok
          | immediate ov =>
            dsimp only at h_ok
            cases h_beq : ty.beq paramTy with
            | false => rw [h_beq] at h_ok; cases h_ok
            | true =>
              rw [h_beq, Bool.not_true, ite_false_eq] at h_ok
              cases h_set : MirSemantics.setElem? slots place.localId (liveUninitSlot ty) with
              | none => rw [h_set] at h_ok; cases h_ok
              | some slots₁ =>
                rw [h_set] at h_ok
                injection h_ok with h_tup
                injection h_tup with h_ov h_sl_eq
                cases h_ov; cases h_sl_eq
                have h_teq : ty = paramTy := MirTy.eq_of_beq h_beq
                cases h_teq
                exact ⟨SlotsMatchTys.setElem? h_inv h_ty (slotMatchesTy_liveUninitSlot paramTy) h_set,
                  SlotsMatchTys.getElem? h_inv h_ty h_sl⟩
  | constant c =>
    dsimp only [evalCallArgOpt] at h_ok
    cases h_beq : c.ty.beq paramTy with
    | false => rw [h_beq] at h_ok; cases h_ok
    | true =>
      rw [h_beq, Bool.not_true, ite_false_eq] at h_ok
      cases h_lit : evalConstLit c.ty c.lit with
      | error _ => rw [h_lit] at h_ok; cases h_ok
      | ok v =>
        rw [h_lit] at h_ok
        injection h_ok with h_tup
        injection h_tup with h_ov h_sl_eq
        cases h_ov; cases h_sl_eq
        exact ⟨h_inv, ⟨v, rfl, evalConstLit_checkVal h_lit, MirTy.eq_of_beq h_beq⟩⟩

private def callArgOpMatch (tys : List MirTy) (paramTy : MirTy) : Operand → Prop
  | .copy place | .move place =>
    place.projection.isEmpty = true ∧
    ∃ argTy, MirSemantics.getElem? tys place.localId = some argTy ∧ argTy.beq paramTy = true
  | .constant c =>
    c.ty.beq paramTy = true ∧ ∃ v, evalConstLit c.ty c.lit = .ok v

private theorem evalCallArgOpt_vs_evalCallArg {tys : List MirTy} {slots : List LocalSlot}
    (mem : MemoryState) (hasMove : Bool) (opnd : Operand) (paramTy : MirTy)
    (h_inv : SlotsMatchTys tys slots)
    (h_match : callArgOpMatch tys paramTy opnd) :
    match evalCallArgOpt tys slots opnd paramTy with
    | .error k => k = .undefined ∧ evalCallArg tys slots mem hasMove opnd paramTy = .error .undefined
    | .ok (none, _) => evalCallArg tys slots mem hasMove opnd paramTy = .error .undefined
    | .ok (some v, slots') => evalCallArg tys slots mem hasMove opnd paramTy = .ok (v, slots', mem) := by
  cases opnd with
  | copy place =>
    let ⟨h_pe, argTy, h_ty, h_beq⟩ := h_match
    let ⟨sl, h_sl⟩ := getElem?_some_of_length_eq (SlotsMatchTys.length_eq h_inv).symm h_ty
    have h_sm := SlotsMatchTys.getElem? h_inv h_ty h_sl
    cases sl with
    | indirect _ => cases h_sm
    | partialTuple _ => cases h_sm
    | dead =>
      have h_ib : (hasMove && false) = false := by cases hasMove <;> rfl
      simp [evalCallArgOpt, evalCallArg, evalOperandToSlot, h_pe, h_ty, h_sl, h_ib]
    | immediate optVal =>
      have h_ib : (hasMove && false) = false := by cases hasMove <;> rfl
      simp only [evalCallArgOpt, evalCallArg, evalOperandToSlot, h_pe, h_ty, h_sl,
        Bool.not_true, ite_false_eq, h_ib, h_beq]
      cases optVal <;> rfl
  | move place =>
    let ⟨h_pe, argTy, h_ty, h_beq⟩ := h_match
    let ⟨sl, h_sl⟩ := getElem?_some_of_length_eq (SlotsMatchTys.length_eq h_inv).symm h_ty
    have h_sm := SlotsMatchTys.getElem? h_inv h_ty h_sl
    cases sl with
    | indirect _ => cases h_sm
    | partialTuple _ => cases h_sm
    | dead =>
      simp [evalCallArgOpt, evalCallArg, evalOperandToSlot, h_pe, h_ty, h_sl]
    | immediate optVal =>
      have h_lt := mirGetElem?_lt_of_some h_ty
      rw [← SlotsMatchTys.length_eq h_inv] at h_lt
      let ⟨slots', h_set⟩ := mirSetElem?_some_of_lt slots place.localId (liveUninitSlot argTy) h_lt
      simp only [evalCallArgOpt, evalCallArg, evalOperandToSlot, h_pe, h_ty, h_sl,
        Bool.not_true, ite_false_eq, h_beq, h_set]
      cases optVal <;> rfl
  | constant c =>
    let ⟨h_beq, v, h_lit⟩ := h_match
    simp only [evalCallArgOpt, evalCallArg, evalOperandToSlot, h_beq, Bool.not_true, ite_false_eq, h_lit]

private theorem evalCallArgsOpt_vs_evalCallArgs (tys : List MirTy)
    (mem : MemoryState) (hasMove : Bool) :
    ∀ (slots : List LocalSlot) (args : List Operand) (paramTys : List MirTy),
      SlotsMatchTys tys slots →
      callArgsMatchBody tys args paramTys = true →
      match evalCallArgsOpt tys slots args paramTys with
      | .error k => k = .undefined ∧ evalCallArgs tys slots mem hasMove args paramTys = .error .undefined
      | .ok (pairs, slots') =>
        match allSomeVals pairs with
        | none => evalCallArgs tys slots mem hasMove args paramTys = .error .undefined
        | some vals => evalCallArgs tys slots mem hasMove args paramTys = .ok (vals, slots', mem)
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, _, h_match => by cases h_match
  | _, _ :: _, [], _, h_match => by cases h_match
  | slots, opnd :: restArgs, paramTy :: restParams, h_inv, h_match => by
    dsimp only [callArgsMatchBody] at h_match
    rw [Bool.and_eq_true] at h_match
    have h_m1 : callArgOpMatch tys paramTy opnd := by
      cases opnd with
      | copy place | move place =>
        dsimp only [callArgOpMatch] at h_match
        dsimp only [callArgOpMatch]
        cases h_pe : place.projection.isEmpty with
        | false => rw [h_pe] at h_match; cases h_match.1
        | true =>
          cases h_ty : MirSemantics.getElem? tys place.localId with
          | none => rw [h_pe, h_ty] at h_match; cases h_match.1
          | some argTy =>
            rw [h_pe, h_ty] at h_match
            exact ⟨rfl, argTy, rfl, h_match.1⟩
      | constant c =>
        dsimp only [callArgOpMatch] at h_match
        dsimp only [callArgOpMatch]
        have h_c1 := h_match.1
        rw [Bool.and_eq_true] at h_c1
        cases h_lit : evalConstLit c.ty c.lit with
        | error _ => rw [h_lit] at h_c1; cases h_c1.2
        | ok v => exact ⟨h_c1.1, v, rfl⟩
    have h1 := evalCallArgOpt_vs_evalCallArg mem hasMove opnd paramTy h_inv h_m1
    dsimp only [evalCallArgsOpt, evalCallArgs]
    cases h_opt1 : evalCallArgOpt tys slots opnd paramTy with
    | error k =>
      rw [h_opt1] at h1
      rw [h1.2]
      exact ⟨h1.1, rfl⟩
    | ok pair1 =>
      cases pair1 with
      | mk optVal slots₁ =>
        rw [h_opt1] at h1
        let ⟨h_inv₁, _⟩ := evalCallArgOpt_preserves_slots_match h_inv h_opt1
        have h_rest := evalCallArgsOpt_vs_evalCallArgs tys mem hasMove slots₁ restArgs restParams h_inv₁ h_match.2
        dsimp only
        cases optVal with
        | none =>
          cases h_opt2 : evalCallArgsOpt tys slots₁ restArgs restParams with
          | error k =>
            rw [h_opt2] at h_rest
            exact ⟨h_rest.1, by rw [h1]⟩
          | ok pair2 =>
            cases pair2 with
            | mk pairs₂ slots₂ =>
              dsimp only
              rw [allSomeVals_cons_none]
              rw [h1]
        | some v =>
          rw [h1]
          dsimp only
          cases h_opt2 : evalCallArgsOpt tys slots₁ restArgs restParams with
          | error k =>
            rw [h_opt2] at h_rest
            rw [h_rest.2]
            exact ⟨h_rest.1, rfl⟩
          | ok pair2 =>
            cases pair2 with
            | mk pairs₂ slots₂ =>
              rw [h_opt2] at h_rest
              dsimp only at h_rest
              dsimp only
              rw [allSomeVals_cons_some]
              cases h_as : allSomeVals pairs₂ with
              | none =>
                rw [h_as] at h_rest
                dsimp only at h_rest
                rw [h_rest]
                rfl
              | some vs =>
                rw [h_as] at h_rest
                dsimp only at h_rest
                rw [h_rest]
                rfl

private theorem evalCallArgsOpt_length (tys : List MirTy) :
    ∀ (slots slots' : List LocalSlot) (args : List Operand) (paramTys : List MirTy)
      (pairs : List (MirTy × Option Val)),
      evalCallArgsOpt tys slots args paramTys = .ok (pairs, slots') →
      pairs.length = args.length
  | _, _, [], [], _, h => by cases h; rfl
  | _, _, [], _ :: _, _, h => by cases h
  | _, _, _ :: _, [], _, h => by cases h
  | slots, slots', op :: restArgs, pTy :: restParams, pairs, h => by
    dsimp only [evalCallArgsOpt] at h
    cases h1 : evalCallArgOpt tys slots op pTy with
    | error _ => rw [h1] at h; cases h
    | ok p1 =>
      cases p1 with
      | mk ov s1 =>
        rw [h1] at h; dsimp only at h
        cases h2 : evalCallArgsOpt tys s1 restArgs restParams with
        | error _ => rw [h2] at h; cases h
        | ok p2 =>
          cases p2 with
          | mk pairs₂ s2 =>
            rw [h2] at h; dsimp only at h
            injection h with ht; injection ht with hp _
            cases hp
            exact congrArg Nat.succ (evalCallArgsOpt_length tys s1 s2 restArgs restParams pairs₂ h2)

private theorem evalCallArgOpt_dst_preserved {tys : List MirTy} {slots slots' : List LocalSlot}
    {opnd : Operand} {paramTy : MirTy} {optVal : Option Val} {dstId : LocalId}
    (h_nmove : ∀ p, opnd = .move p → p.localId ≠ dstId)
    (h_ok : evalCallArgOpt tys slots opnd paramTy = .ok (optVal, slots')) :
    MirSemantics.getElem? slots' dstId = MirSemantics.getElem? slots dstId := by
  cases opnd with
  | copy place =>
    dsimp only [evalCallArgOpt] at h_ok
    cases h_pe : place.projection.isEmpty <;> rw [h_pe] at h_ok
    · cases h_ok
    · cases h_ty : MirSemantics.getElem? tys place.localId with
      | none => rw [h_ty] at h_ok; cases h_ok
      | some ty =>
        rw [h_ty] at h_ok
        cases h_sl : MirSemantics.getElem? slots place.localId with
        | none => rw [h_sl] at h_ok; cases h_ok
        | some sl =>
          rw [h_sl] at h_ok
          cases sl with
          | dead | indirect _ | partialTuple _ => cases h_ok
          | immediate ov =>
            dsimp only at h_ok
            cases h_beq : ty.beq paramTy <;> rw [h_beq] at h_ok
            · cases h_ok
            · injection h_ok with h_t; injection h_t with _ h_s; cases h_s; rfl
  | constant c =>
    dsimp only [evalCallArgOpt] at h_ok
    cases h_beq : c.ty.beq paramTy <;> rw [h_beq] at h_ok
    · cases h_ok
    · cases h_lit : evalConstLit c.ty c.lit <;> rw [h_lit] at h_ok
      · cases h_ok
      · dsimp only at h_ok; injection h_ok with h_t; injection h_t with _ h_s; cases h_s; rfl
  | move place =>
    have h_ne : place.localId ≠ dstId := h_nmove place rfl
    dsimp only [evalCallArgOpt] at h_ok
    cases h_pe : place.projection.isEmpty <;> rw [h_pe] at h_ok
    · cases h_ok
    · cases h_ty : MirSemantics.getElem? tys place.localId with
      | none => rw [h_ty] at h_ok; cases h_ok
      | some ty =>
        rw [h_ty] at h_ok
        cases h_sl : MirSemantics.getElem? slots place.localId with
        | none => rw [h_sl] at h_ok; cases h_ok
        | some sl =>
          rw [h_sl] at h_ok
          cases sl with
          | dead | indirect _ | partialTuple _ => cases h_ok
          | immediate ov =>
            dsimp only at h_ok
            cases h_beq : ty.beq paramTy <;> rw [h_beq] at h_ok
            · cases h_ok
            · cases h_set : MirSemantics.setElem? slots place.localId (liveUninitSlot ty) <;> rw [h_set] at h_ok
              · cases h_ok
              · dsimp only at h_ok
                injection h_ok with h_t; injection h_t with _ h_s; cases h_s
                exact mirGetElem?_mirSetElem?_ne h_set h_ne.symm

private theorem evalCallArgsOpt_dst_preserved (tys : List MirTy) (dstId : LocalId) :
    ∀ (slots slots' : List LocalSlot) (args : List Operand) (paramTys : List MirTy)
      (pairs : List (MirTy × Option Val)),
      (∀ p, p ∈ MirSemantics.movePlaceList args → p.localId ≠ dstId) →
      evalCallArgsOpt tys slots args paramTys = .ok (pairs, slots') →
      MirSemantics.getElem? slots' dstId = MirSemantics.getElem? slots dstId
  | slots, _, [], [], _, _, h_ok => by cases h_ok; rfl
  | _, _, [], _ :: _, _, _, h_ok => by cases h_ok
  | _, _, _ :: _, [], _, _, h_ok => by cases h_ok
  | slots, slots', op :: restArgs, pTy :: restParams, pairs, h_disj, h_ok => by
    dsimp only [evalCallArgsOpt] at h_ok
    cases h_1 : evalCallArgOpt tys slots op pTy with
    | error _ => rw [h_1] at h_ok; cases h_ok
    | ok pair1 =>
      cases pair1 with
      | mk ov slots₁ =>
        rw [h_1] at h_ok
        dsimp only at h_ok
        cases h_2 : evalCallArgsOpt tys slots₁ restArgs restParams with
        | error _ => rw [h_2] at h_ok; cases h_ok
        | ok pair2 =>
          cases pair2 with
          | mk pairs₂ slots₂ =>
            rw [h_2] at h_ok
            dsimp only at h_ok
            injection h_ok with h_t; injection h_t with _ h_s; cases h_s
            have h_n1 : ∀ p, op = .move p → p.localId ≠ dstId := by
              intro p hp
              apply h_disj
              cases hp
              dsimp only [MirSemantics.movePlaceList]
              exact List.mem_cons_self
            have h_n2 : ∀ p, p ∈ MirSemantics.movePlaceList restArgs → p.localId ≠ dstId := by
              intro p hp
              apply h_disj
              cases op <;> simp only [MirSemantics.movePlaceList] <;>
                first | exact hp | exact List.mem_cons_of_mem _ hp
            have h_p1 := evalCallArgOpt_dst_preserved h_n1 h_1
            have h_p2 := evalCallArgsOpt_dst_preserved tys dstId slots₁ slots' restArgs restParams pairs₂ h_n2 h_2
            exact h_p2.trans h_p1

private theorem refPlacesDisjointAux_not_mem_end :
    ∀ (places : List RefPlace) (seen : List LocalId) (dst : RefPlace),
      refPlacesDisjointAux seen (places ++ [dst]) = true →
      ∀ p, p ∈ places → p.localId ≠ dst.localId
  | [], _, _, _, _, hp => by cases hp
  | p :: rest, seen, dst, h_disj, q, hq => by
    rw [List.cons_append] at h_disj
    dsimp only [refPlacesDisjointAux] at h_disj
    cases h_pe : p.projection.isEmpty with
    | false => rw [h_pe] at h_disj; cases h_disj
    | true =>
      rw [h_pe, Bool.not_true, Bool.false_or] at h_disj
      cases h_c : refNatListContains p.localId seen with
      | true => rw [h_c] at h_disj; cases h_disj
      | false =>
        rw [h_c, ite_false_eq] at h_disj
        simp only [List.mem_cons] at hq
        cases hq with
        | inl hqp =>
          cases hqp
          intro h_eq
          have h_fail : ∀ (xs : List RefPlace) (s : List LocalId),
              refNatListContains dst.localId s = true →
              refPlacesDisjointAux s (xs ++ [dst]) = false := by
            intro xs
            induction xs with
            | nil =>
              intro s hs
              rw [List.nil_append]
              dsimp only [refPlacesDisjointAux]
              rw [hs, Bool.or_true, ite_true_eq]
            | cons r rs ih =>
              intro s hs
              rw [List.cons_append]
              dsimp only [refPlacesDisjointAux]
              cases h_bad : (!r.projection.isEmpty || refNatListContains r.localId s) with
              | true => rw [ite_true_eq]
              | false =>
                rw [ite_false_eq]
                apply ih
                dsimp only [refNatListContains]
                rw [hs, Bool.or_true]
          have h_in : refNatListContains dst.localId (p.localId :: seen) = true := by
            dsimp only [refNatListContains]; rw [h_eq, Nat.beq_refl]; rfl
          rw [h_fail rest (p.localId :: seen) h_in] at h_disj
          cases h_disj
        | inr hqr => exact refPlacesDisjointAux_not_mem_end rest (p.localId :: seen) dst h_disj q hqr

private theorem movePlaceList_decode_eq (types : List MirTy) :
    ∀ (rargs : List RefOperand) (args : List Operand),
      mapOption (decodeOperand types) rargs = some args →
      ∀ p, p ∈ MirSemantics.movePlaceList args →
        ∃ rp, rp ∈ refMovePlaceList rargs ∧ p.localId = rp.localId
  | [], [], _, _, hp => by cases hp
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by
    dsimp only [mapOption, optMap2] at h
    cases h1 : decodeOperand types _ <;> cases h2 : mapOption (decodeOperand types) _ <;>
      rw [h1, h2] at h <;> cases h
  | ro :: rrest, op :: rest, h_dec, p, hp => by
    dsimp only [mapOption, optMap2] at h_dec
    cases h1 : decodeOperand types ro with
    | none => rw [h1] at h_dec; cases h_dec
    | some op' =>
      cases h2 : mapOption (decodeOperand types) rrest with
      | none => rw [h1, h2] at h_dec; cases h_dec
      | some rest' =>
        rw [h1, h2] at h_dec
        injection h_dec with h_eq; injection h_eq with ho hr
        cases ho; cases hr
        cases ro with
        | copy rp =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_p : decodePlace types rp <;> rw [h_p] at h1
          · cases h1
          · injection h1 with h_o; cases h_o
            dsimp only [MirSemantics.movePlaceList] at hp
            dsimp only [refMovePlaceList]
            exact movePlaceList_decode_eq types rrest rest h2 p hp
        | constant rc =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_t : MirSemantics.getElem? types rc.ty <;> rw [h_t] at h1
          · cases h1
          · injection h1 with h_o; cases h_o
            dsimp only [MirSemantics.movePlaceList] at hp
            dsimp only [refMovePlaceList]
            exact movePlaceList_decode_eq types rrest rest h2 p hp
        | move rp =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_p : decodePlace types rp <;> rw [h_p] at h1
          · cases h1
          · injection h1 with h_o; cases h_o
            dsimp only [MirSemantics.movePlaceList] at hp
            dsimp only [refMovePlaceList]
            cases hp with
            | head => exact ⟨rp, List.mem_cons_self, (decodePlace_inv h_p).1.symm⟩
            | tail _ h_mem =>
              let ⟨rp', h_m', h_id⟩ := movePlaceList_decode_eq types rrest rest h2 p h_mem
              exact ⟨rp', List.mem_cons_of_mem _ h_m', h_id⟩

private theorem callHooks_evalOperandAt_eq (rp : RefProg) (c : Choice) (path : Miri.Interpreter.OperandPath)
    (op : Miri.MIR.Operand) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).evalOperandAt c path op st =
      match Miri.Interpreter.OperandMachine.evalOperandAt
          (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)) c path op none st with
      | .error e s' => .error e s'
      | .ok v s' => .ok v { s' with machine := { s'.machine with pendingMoveDeinit := false } } := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  dsimp only [Miri.Interpreter.ExecutionCalls.make, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  cases Miri.Interpreter.OperandMachine.evalOperandAt
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)) c path op none st with
  | error _ _ => rfl
  | ok _ s' =>
    cases s' with
    | mk stk mach =>
      cases mach
      have h_de : (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).deinitMovedPlace = true := rfl
      dsimp only
      rw [h_de, ite_true_eq]
      dsimp only [EStateM.bind, EStateM.modifyGet, EStateM.pure]

private theorem callHooks_evalPlace_eq (rp : RefProg) (c : Choice) (pl : Miri.MIR.Place) (skip : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).evalPlace c pl skip st =
      match Miri.Interpreter.PlaceDynamic.evalPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)) c pl skip st with
      | .ok r s' => .ok r.stackView s'
      | .error e s' => .error e s' := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  dsimp only [Miri.Interpreter.ExecutionCalls.make, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases Miri.Interpreter.PlaceDynamic.evalPlace
    (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)) c pl skip st <;> rfl

private theorem callHooks_evalPlace_local_ok (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (skip : Bool) (ty : MirTy) (slot : LocalSlot)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).evalPlace c
      { localId := id, projection := Array.empty } skip
      (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm) =
      .ok (⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance).stackView
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots (cacheTouch cache id) mem ctrl cm) := by
  rw [callHooks_evalPlace_eq]
  change (match Miri.Interpreter.PlaceDynamic.evalPlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)) c
      ⟨id, Array.empty⟩ skip
      (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm) with
    | EStateM.Result.ok r s' => EStateM.Result.ok r.stackView s'
    | EStateM.Result.error e s' => EStateM.Result.error e s') = _
  rw [placeDynamic_evalPlace_local_ok rp c ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    id skip ty slot h_locs h_c_len h_ty h_sl]

private theorem callHooks_functionSignature_eq (rp : RefProg) (c : Choice)
    (layout : Miri.Interpreter.LocalLayout) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).functionSignature c layout st =
      if Nat.blt layout.ty (fnTyBase rp.types) = true then
        .error (.unsupported "invalid callee TyId") st
      else
        match refResolveCalleeBody rp (layout.ty - fnTyBase rp.types) with
        | none => .error (.unsupported "missing callee signature") st
        | some (rbody, _) => .ok (rbody.argumentCount, ()) st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  rfl

private theorem callHooks_functionKind_eq (rp : RefProg)
    (tyId : Miri.MIR.TyId) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).functionKind tyId st =
      if Nat.blt tyId (fnTyBase rp.types) = true then
        .error (.unsupported "invalid callee TyId") st
      else .ok (.FnDef (tyId - fnTyBase rp.types) Array.empty) st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  rfl

private theorem callHooks_resolve_eq (rp : RefProg) (c : Choice)
    (defId : Miri.MIR.DefId) (gargs : Array Miri.MIR.GenericArg)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).resolve c defId gargs st =
      .ok { kind := .Item defId, args := Array.empty } st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  rfl

private theorem callHooks_fnAbiOfInstance_eq (rp : RefProg) (c : Choice)
    (fnInst : Miri.Interpreter.CallInstance) (extra : Array Miri.MIR.TyId)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).fnAbiOfInstance c fnInst extra st =
      if (!extra.isEmpty) = true then
        .error (.unsupported "variadic calls unsupported") st
      else
        match fnInst.kind with
        | .Item fnTag =>
          match refResolveCalleeBody rp fnTag with
          | none => .error (.unsupported "missing callee ABI") st
          | some (rbody, localTys) =>
            match refFnAbiOfBody rp.types rbody localTys with
            | .ok abi => .ok abi st
            | .error e => .error e st
        | _ => .error (.unsupported "non-Item call unsupported") st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  rfl

private theorem callHooks_requiresCallerLocation_eq (rp : RefProg)
    (fnInst : Miri.Interpreter.CallInstance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).requiresCallerLocation fnInst st =
      .ok false st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks]
  rw [withValidation_refExecCfg_idem]
  rfl

private theorem evalFnCallArgumentAt_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (rop : RefOperand) (op : Operand) (paramTy : MirTy) (argIdx : Nat)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_dec : decodeOperand rp.types rop = some op)
    (h_match : callArgOpMatch bodyLocals paramTy op) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
    match evalCallArgOpt bodyLocals slots op paramTy with
    | .error k =>
      k = .undefined ∧
      ∃ err st',
        Miri.Interpreter.Call.evalFnCallArgumentAt calls c (toMiriOperand rp.types rop) true
          (.argument argIdx) st = .error err st' ∧
        stepErrorFaultKind err = some .undefined
    | .ok (optVal, slots') =>
      Miri.Interpreter.Call.evalFnCallArgumentAt calls c (toMiriOperand rp.types rop) true
        (.argument argIdx) st =
        .ok (.Copy ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩)
          (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots'
            (operandCacheTouch cache op) mem ctrl cm) := by
  intro st calls
  dsimp only [st]
  cases rop with
  | copy rplace =>
    dsimp only [decodeOperand, optMap] at h_dec
    cases h_pdec : decodePlace rp.types rplace with
    | none => rw [h_pdec] at h_dec; cases h_dec
    | some place =>
      rw [h_pdec] at h_dec
      injection h_dec with hop_eq; cases hop_eq
      let ⟨h_pe, argTy, h_ty, h_beq⟩ := h_match
      have h_eq_ty : argTy = paramTy := MirTy.eq_of_beq h_beq
      cases h_eq_ty
      have h_ev := operandMachine_evalOperandAt_eq rp c ctx rbody blockIdx stmtIdx bodyLocals slots cache
        entryMemory mem ctrl cm (.argument argIdx) (.copy rplace) (.copy place) (fun _ => true) none
        h_locs h_c_len (refConstantAt_eq_of_ne_fn rp c _
          (by simp [Miri.Interpreter.OperandPath.argument, Miri.Interpreter.OperandPath.instruction])
          (fun _ _ _ => rfl))
        h_inv (by dsimp only [decodeOperand, optMap]; rw [h_pdec]) (fun _ _ => True.intro)
      dsimp only [evalOperandToSlot] at h_ev
      rw [h_ty] at h_ev
      cases h_sl : MirSemantics.getElem? slots place.localId with
      | none =>
        let ⟨_, h_some⟩ := getElem?_some_of_length_eq (SlotsMatchTys.length_eq h_inv).symm h_ty
        rw [h_some] at h_sl; cases h_sl
      | some sl =>
        have h_sm := SlotsMatchTys.getElem? h_inv h_ty h_sl
        dsimp only [evalCallArgOpt]
        rw [h_pe, h_ty, h_sl]
        have h_rp_inv := decodePlace_inv h_pdec
        have h_rpe : rplace.projection.isEmpty = true := h_rp_inv.2.trans h_pe
        have h_rid : rplace.localId = place.localId := h_rp_inv.1
        have h_miri_pl : toMiriPlace rplace = { localId := place.localId, projection := Array.empty } := by
          dsimp only [toMiriPlace]; rw [h_rpe, h_rid]; rfl
        cases sl with
        | indirect _ => cases h_sm
        | partialTuple _ => cases h_sm
        | dead =>
          rw [h_sl] at h_ev
          let ⟨err, st', h_err, h_fk⟩ := h_ev
          refine ⟨rfl, err, st', ?_, h_fk⟩
          dsimp only [calls, Miri.Interpreter.Call.evalFnCallArgumentAt, toMiriOperand,
            bind, Bind.bind, pure, Pure.pure]
          rw [h_miri_pl]
          have h_err' :
              (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).evalOperandAt c
                (.argument argIdx) (Miri.MIR.Operand.Copy { localId := place.localId, projection := Array.empty }) st =
                .error err st' := by
            rw [callHooks_evalOperandAt_eq]; dsimp only [toMiriOperand] at h_err; rw [h_miri_pl] at h_err; rw [h_err]
          rw [eStateM_bind_err h_err']
        | immediate optVal =>
          rw [h_sl, h_pe] at h_ev
          dsimp only at h_ev
          dsimp only
          rw [Bool.not_true, ite_false_eq, h_beq, Bool.not_true, ite_false_eq]
          dsimp only [calls, Miri.Interpreter.Call.evalFnCallArgumentAt, toMiriOperand,
            bind, Bind.bind, pure, Pure.pure]
          rw [h_miri_pl]
          have h_ev' :
              (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).evalOperandAt c
                (.argument argIdx) (Miri.MIR.Operand.Copy { localId := place.localId, projection := Array.empty }) st =
                .ok ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩
                  (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
                    (cacheTouch cache place.localId) mem ctrl cm) := by
            rw [callHooks_evalOperandAt_eq]; dsimp only [toMiriOperand] at h_ev; rw [h_miri_pl] at h_ev; rw [h_ev]; rfl
          rw [eStateM_bind_ok h_ev']
          rfl
  | constant rc =>
    dsimp only [decodeOperand, optMap] at h_dec
    cases h_t : MirSemantics.getElem? rp.types rc.ty with
    | none => rw [h_t] at h_dec; cases h_dec
    | some cTy =>
      rw [h_t] at h_dec
      injection h_dec with hop_eq; cases hop_eq
      let ⟨h_beq, v, h_lit⟩ := h_match
      have h_eq_ty : cTy = paramTy := MirTy.eq_of_beq h_beq
      cases h_eq_ty
      have h_ev := operandMachine_evalOperandAt_eq rp c ctx rbody blockIdx stmtIdx bodyLocals slots cache
        entryMemory mem ctrl cm (.argument argIdx) (.constant rc) (.constant { ty := paramTy, lit := rc.lit })
        (fun _ => true) none h_locs h_c_len
        (refConstantAt_eq_of_ne_fn rp c _
          (by simp [Miri.Interpreter.OperandPath.argument, Miri.Interpreter.OperandPath.instruction])
          (fun _ _ _ => rfl)) h_inv
        (by dsimp only [decodeOperand, optMap]; rw [h_t]) True.intro
      dsimp only [evalOperandToSlot] at h_ev
      rw [h_lit] at h_ev
      dsimp only [evalCallArgOpt]
      rw [h_beq, Bool.not_true, ite_false_eq, h_lit]
      dsimp only [calls, Miri.Interpreter.Call.evalFnCallArgumentAt, toMiriOperand,
        bind, Bind.bind, pure, Pure.pure]
      have h_ev' :
          (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).evalOperandAt c
            (.argument argIdx) (toMiriOperand rp.types (.constant rc)) st =
            .ok ⟨.immediate (optValToMiriImm paramTy v), refLocalLayoutForTy rp.types paramTy⟩ st := by
        rw [callHooks_evalOperandAt_eq]; rw [h_ev]; rfl
      dsimp only [toMiriOperand] at h_ev'
      rw [eStateM_bind_ok h_ev']
      rfl
  | move rplace =>
    dsimp only [decodeOperand, optMap] at h_dec
    cases h_pdec : decodePlace rp.types rplace with
    | none => rw [h_pdec] at h_dec; cases h_dec
    | some place =>
      rw [h_pdec] at h_dec
      injection h_dec with hop_eq; cases hop_eq
      let ⟨h_pe, argTy, h_ty, h_beq⟩ := h_match
      have h_eq_ty : argTy = paramTy := MirTy.eq_of_beq h_beq
      cases h_eq_ty
      have h_rp_inv := decodePlace_inv h_pdec
      have h_rpe : rplace.projection.isEmpty = true := h_rp_inv.2.trans h_pe
      have h_rid : rplace.localId = place.localId := h_rp_inv.1
      have h_miri_pl : toMiriPlace rplace = { localId := place.localId, projection := Array.empty } := by
        dsimp only [toMiriPlace]; rw [h_rpe, h_rid]; rfl
      have h_miri_pe : (toMiriPlace rplace).projection.isEmpty = true := by rw [h_miri_pl]; rfl
      cases h_sl : MirSemantics.getElem? slots place.localId with
      | none =>
        let ⟨_, h_some⟩ := getElem?_some_of_length_eq (SlotsMatchTys.length_eq h_inv).symm h_ty
        rw [h_some] at h_sl; cases h_sl
      | some sl =>
        have h_sm := SlotsMatchTys.getElem? h_inv h_ty h_sl
        have h_ep_call := callHooks_evalPlace_local_ok rp c ctx rbody blockIdx stmtIdx
          bodyLocals slots cache mem ctrl cm place.localId true paramTy sl h_locs h_c_len h_ty h_sl
        dsimp only [evalCallArgOpt]
        rw [h_pe, h_ty, h_sl]
        cases sl with
        | indirect _ => cases h_sm
        | partialTuple _ => cases h_sm
        | dead =>
          have h_c1 : (cacheTouch cache place.localId).length = bodyLocals.length := by
            rw [cacheTouch_length, h_c_len]
          let ⟨st', h_pto⟩ := placeToOp_local_dead rp c ctx rbody blockIdx stmtIdx
            bodyLocals slots (cacheTouch cache place.localId) mem ctrl cm place.localId paramTy
            h_locs h_c1 h_ty h_sl
          refine ⟨rfl, .stack (.localExpectedLive place.localId), st', ?_, rfl⟩
          dsimp only [calls, Miri.Interpreter.Call.evalFnCallArgumentAt, toMiriOperand,
            bind, Bind.bind, pure, Pure.pure]
          rw [h_miri_pl]
          rw [eStateM_bind_ok h_ep_call]
          dsimp only [Miri.Interpreter.RuntimePlace.stackView]
          have h_de : (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).deinitMovedPlace = true := rfl
          rw [h_de, show (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false from rfl]
          rw [ite_true_eq, Bool.true_and, ite_false_eq]
          rw [eStateM_bind_err h_pto]
        | immediate optVal =>
          dsimp only
          rw [Bool.not_true, ite_false_eq, h_beq, Bool.not_true, ite_false_eq]
          have h_lt := mirGetElem?_lt_of_some h_ty
          rw [← SlotsMatchTys.length_eq h_inv] at h_lt
          cases h_set : MirSemantics.setElem? slots place.localId (liveUninitSlot paramTy) with
          | none =>
            let ⟨_, h_some⟩ := mirSetElem?_some_of_lt slots place.localId (liveUninitSlot paramTy) h_lt
            rw [h_some] at h_set; cases h_set
          | some slots' =>
            dsimp only
            have h_c1 : (cacheTouch cache place.localId).length = bodyLocals.length := by
              rw [cacheTouch_length, h_c_len]
            have h_pto := placeToOp_local_live rp c ctx rbody blockIdx stmtIdx
              bodyLocals slots (cacheTouch cache place.localId) mem ctrl cm place.localId paramTy optVal
              h_locs h_c1 h_ty h_sl
            rw [cacheTouch_idem] at h_pto
            let ⟨b₁, h_c₁⟩ := getElem?_some_of_length_eq h_c1.symm h_ty
            have h_cf1 := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
              bodyLocals slots (cacheTouch cache place.localId) mem ctrl cm
            have h_rep := mkGenSimFrame_replaceLocalValue_some rp ctx rbody blockIdx stmtIdx
              bodyLocals slots slots' (cacheTouch cache place.localId) place.localId paramTy
              (.immediate optVal) (liveUninitSlot paramTy) b₁ h_ty h_sl h_c₁ h_set
            have h_deinit_eq :
                (if (refLocalLayoutForTy rp.types paramTy).layout.isZst = true then
                    Miri.Interpreter.Operand.immediate (optValToMiriImm paramTy optVal)
                  else Miri.Interpreter.Operand.immediate .uninit) =
                  Miri.Interpreter.Operand.immediate .uninit :=
              refLayoutDataForTy_isZst_move_deinit paramTy optVal h_sm
            dsimp only [calls, Miri.Interpreter.Call.evalFnCallArgumentAt, toMiriOperand,
              bind, Bind.bind, pure, Pure.pure]
            rw [h_miri_pl]
            rw [eStateM_bind_ok h_ep_call]
            dsimp only [Miri.Interpreter.RuntimePlace.stackView]
            have h_de : (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).deinitMovedPlace = true := rfl
            rw [h_de, show (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false from rfl]
            rw [ite_true_eq, Bool.true_and, ite_false_eq]
            rw [eStateM_bind_ok h_pto]
            dsimp only
            rw [ite_true_eq, h_deinit_eq, ← slotToMiriLocalValue_liveUninit paramTy]
            have h_gf : (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).getFrame =
                Miri.Interpreter.MachineHooks.currentFrame := rfl
            have h_sf : (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).setFrame =
                Miri.Interpreter.MachineHooks.setCurrentFrame := rfl
            rw [h_gf, h_sf, eStateM_bind_ok h_cf1]
            rw [h_rep]
            dsimp only
            rw [eStateM_bind_ok (setCurrentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
              bodyLocals slots slots' (cacheTouch cache place.localId)
              (cacheTouch cache place.localId) mem ctrl cm)]
            rfl

private theorem deallocateTempArgs_empty
    {P S C E Other Extern FnABI ArgABI : Type}
    (calls : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI) (c : C) (s : S) :
    Miri.Interpreter.Call.deallocateTempArgs calls c (List.toArray []) s = .ok () s := by
  dsimp only [Miri.Interpreter.Call.deallocateTempArgs]
  rw [← Array.forIn_toList]
  rfl

private noncomputable def miriCleanupMirror
    {P S C E Other Extern FnABI ArgABI A : Type}
    (calls : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI) (c : C)
    (tempAllocs : Array (Miri.Memory.Pointer (Option P)))
    (action : Miri.Interpreter.CallM S A) : Miri.Interpreter.CallM S A := fun s =>
  match action s with
  | .ok val s' => .ok val s'
  | .error err s' =>
    match Miri.Interpreter.Call.deallocateTempArgs calls c tempAllocs s' with
    | .ok () s'' => .error err s''
    | .error _ s'' => .error err s''

private theorem miriCleanupMirror_empty
    {P S C E Other Extern FnABI ArgABI A : Type}
    (calls : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI) (c : C)
    (action : Miri.Interpreter.CallM S A) (s : S) :
    miriCleanupMirror calls c (List.toArray []) action s = action s := by
  dsimp only [miriCleanupMirror]
  cases action s with
  | ok _ _ => rfl
  | error _ _ => dsimp only; rw [deallocateTempArgs_empty]

private theorem miriCleanupMirror_empty_fn
    {P S C E Other Extern FnABI ArgABI A : Type}
    (calls : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI) (c : C)
    (action : Miri.Interpreter.CallM S A) :
    miriCleanupMirror calls c (List.toArray []) action = action :=
  funext (miriCleanupMirror_empty calls c action)

private def miriRequireMirror {S : Type} (condition : Bool) (message : String) :
    Miri.Interpreter.CallM S Unit :=
  if condition then pure () else throw (.invalidProgram message)

private noncomputable def evalCalleeAndArgsLoop
    (calls : Miri.Interpreter.CallHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      Miri.Interpreter.MachineHooks.FrameExtra Unit Unit
      (Miri.ABI.FnAbi Miri.MIR.TyId) (Miri.ABI.ArgAbi Miri.MIR.TyId))
    (c : Choice) (argsArr : Array Miri.MIR.SpannedOperand)
    (disjoint hasMove : Bool)
    (range : List Nat)
    (acc : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance)) :
    Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser)
      (Array (Miri.Memory.Pointer (Option Miri.Memory.Provenance)) ×
        Array (Miri.Interpreter.FnArg Miri.Memory.Provenance)) :=
  forIn range ((List.toArray [] : Array (Miri.Memory.Pointer (Option Miri.Memory.Provenance))), acc)
    (fun index __s =>
      match argsArr[index]? with
      | some arg =>
        EStateM.bind
          (miriCleanupMirror calls c __s.fst
            (Miri.Interpreter.Call.evalFnCallArgumentAt calls c arg.operand disjoint
              (Miri.Interpreter.OperandPath.argument index)))
          fun fnArg =>
          match fnArg with
          | .InPlace _ (some { op := .indirect tmpMplace, layout := _ }) =>
            pure (ForInStep.yield (__s.fst.push tmpMplace.ptr, __s.snd.push fnArg))
          | .InPlace _ _ =>
            pure (ForInStep.yield (__s.fst, __s.snd.push fnArg))
          | .Copy op =>
            if hasMove = true then
              match op.op with
              | .immediate _ =>
                pure (ForInStep.yield (__s.fst, __s.snd.push fnArg))
              | .indirect _ =>
                if (!op.layout.layout.isSized) = true then
                  EStateM.bind
                    (miriCleanupMirror calls c __s.fst
                      (throw (Miri.Interpreter.StepError.unsupported
                        "unsized indirect copy argument materialization unsupported") :
                        Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit))
                    fun _ =>
                  EStateM.bind (miriCleanupMirror calls c __s.fst (calls.allocateStack c op.layout)) fun tmpCopy =>
                  EStateM.bind
                    (miriCleanupMirror calls c (__s.fst.push tmpCopy.mplace.ptr) (calls.copyToMemory c op tmpCopy))
                    fun _ =>
                  pure (ForInStep.yield (__s.fst.push tmpCopy.mplace.ptr,
                    __s.snd.push (.Copy ⟨.indirect tmpCopy.mplace, tmpCopy.layout⟩)))
                else
                  EStateM.bind (miriCleanupMirror calls c __s.fst (calls.allocateStack c op.layout)) fun tmpCopy =>
                  EStateM.bind
                    (miriCleanupMirror calls c (__s.fst.push tmpCopy.mplace.ptr) (calls.copyToMemory c op tmpCopy))
                    fun _ =>
                  pure (ForInStep.yield (__s.fst.push tmpCopy.mplace.ptr,
                    __s.snd.push (.Copy ⟨.indirect tmpCopy.mplace, tmpCopy.layout⟩)))
            else
              pure (ForInStep.yield (__s.fst, __s.snd.push fnArg))
      | none =>
        EStateM.bind
          (miriCleanupMirror calls c __s.fst
            (throw (Miri.Interpreter.StepError.invalidProgram "missing source call argument") :
              Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit))
          fun _ =>
        pure (ForInStep.yield (__s.fst, __s.snd)))

private noncomputable def evalCalleePostMirror
    {P S C E Other Extern FnABI ArgABI : Type}
    (calls : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI) (c : C)
    (func : Miri.Interpreter.OpTy P)
    (tempAllocs : Array (Miri.Memory.Pointer (Option P)))
    (evaluated : Array (Miri.Interpreter.FnArg P)) :
    Miri.Interpreter.CallM S (Miri.Interpreter.EvaluatedCall P Other Extern FnABI) :=
  miriCleanupMirror calls c tempAllocs
    (EStateM.bind (calls.functionSignature c func.layout) fun __x =>
      match __x with
      | (inputCount, externAbi) =>
        EStateM.bind (miriRequireMirror (decide (inputCount ≤ evaluated.size))
            "call has fewer args than normalized signature") fun _ =>
          have extra : Array Miri.MIR.TyId := Array.map (fun arg => arg.layout.ty) (evaluated.extract inputCount)
          EStateM.bind (calls.functionKind func.layout.ty) fun fk =>
            match fk with
            | .FnPtr =>
              EStateM.bind (calls.readPointer c func) fun fnPtr =>
                EStateM.bind (calls.getPtrFn c fnPtr) fun fnVal =>
                  EStateM.bind (calls.fnAbiOfFnPtr c func.layout extra) fun abi =>
                    EStateM.pure ⟨fnVal, evaluated, externAbi, some abi, false, tempAllocs⟩
            | .FnDef definition args =>
              EStateM.bind (calls.resolve c definition args) fun fnInstance =>
                have __do_jp : Option FnABI → Miri.Interpreter.CallM S (Miri.Interpreter.EvaluatedCall P Other Extern FnABI) :=
                  fun abi =>
                    EStateM.bind (calls.requiresCallerLocation fnInstance) fun __do_lift =>
                      EStateM.pure ⟨.Instance fnInstance, evaluated, externAbi, abi, __do_lift, tempAllocs⟩
                match fnInstance.kind with
                | .LlvmIntrinsic _ =>
                  EStateM.bind (EStateM.pure none) __do_jp
                | .Intrinsic definition =>
                  EStateM.bind (calls.fnAbiOfInstance c ⟨.Item definition, fnInstance.args⟩ extra) fun __do_lift =>
                    EStateM.bind (EStateM.pure (some __do_lift)) __do_jp
                | _ =>
                  EStateM.bind (calls.fnAbiOfInstance c fnInstance extra) fun __do_lift =>
                    EStateM.bind (EStateM.pure (some __do_lift)) __do_jp
            | .invalid => throw (.invalidProgram "invalid callee type"))

private theorem list_drop_eq_getElem?_cons {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : xs.drop i = x :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => cases h
  | cons a rest ih =>
    cases i with
    | zero => simp at h; subst h; rfl
    | succ k =>
      rw [List.getElem?_cons_succ] at h
      rw [List.drop_succ_cons]
      exact ih h

private theorem evalCalleeAndArgs_loop_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (allRargs : List RefOperand) (hasMove : Bool)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals) :
    ∀ (count idx : Nat) (rargs : List RefOperand) (opnds : List Operand)
      (paramTys : List MirTy) (slots : List LocalSlot) (cache : List Bool)
      (acc : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance)),
      idx + count = allRargs.length →
      allRargs.drop idx = rargs →
      mapOption (decodeOperand rp.types) rargs = some opnds →
      callArgsMatchBody bodyLocals opnds paramTys = true →
      SlotsMatchTys bodyLocals slots →
      cache.length = bodyLocals.length →
      let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
      let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
      let argsArr : Array Miri.MIR.SpannedOperand := ⟨allRargs.map (toMiriSpannedOperand rp.types)⟩
      let loop := evalCalleeAndArgsLoop calls c argsArr true hasMove (List.range' idx count 1) acc st
      match evalCallArgsOpt bodyLocals slots opnds paramTys with
      | .error k =>
        k = .undefined ∧ ∃ err st', loop = .error err st' ∧ stepErrorFaultKind err = some .undefined
      | .ok (pairs, slots') =>
        ∃ cache',
          cache' = opnds.foldl operandCacheTouch cache ∧
          cache'.length = bodyLocals.length ∧
          (∀ k, MirSemantics.getElem? cache k = some true → MirSemantics.getElem? cache' k = some true) ∧
          SlotsMatchTys bodyLocals slots' ∧
          loop =
            .ok (List.toArray [], ⟨acc.toList ++ pairs.map (fun (ty, ov) =>
                Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩)
              (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache' mem ctrl cm)
  | 0, idx, rargs, opnds, paramTys, slots, cache, acc, h_sum, h_drop, h_dec, h_match, h_inv, h_c_len => by
    rw [Nat.add_zero] at h_sum
    have h_ge : allRargs.length ≤ idx := Nat.le_of_eq h_sum.symm
    have h_nil : rargs = [] := by rw [← h_drop]; exact List.drop_of_length_le h_ge
    cases h_nil
    cases h_dec
    cases paramTys with
    | cons _ _ => cases h_match
    | nil =>
      refine ⟨cache, rfl, h_c_len, fun _ h => h, h_inv, ?_⟩
      dsimp only [evalCalleeAndArgsLoop, List.range', evalCallArgsOpt]
      rw [List.forIn_nil (m := Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser))]
      simp [pure, Pure.pure, EStateM.pure]
  | count + 1, idx, rargs, opnds, paramTys, slots, cache, acc, h_sum, h_drop, h_dec, h_match, h_inv, h_c_len => by
    have h_lt : idx < allRargs.length := by
      rw [← h_sum, ← Nat.add_assoc]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos count)
    let ⟨ro, h_get_ro⟩ : ∃ ro, allRargs[idx]? = some ro := by
      cases h : allRargs[idx]? with
      | none => exact absurd (List.getElem?_eq_none_iff.mp h) (Nat.not_le.mpr h_lt)
      | some ro => exact ⟨ro, rfl⟩
    have h_drop_cons : allRargs.drop idx = ro :: allRargs.drop (idx + 1) :=
      list_drop_eq_getElem?_cons h_get_ro
    have h_rargs : rargs = ro :: allRargs.drop (idx + 1) := h_drop.symm.trans h_drop_cons
    cases h_rargs
    dsimp only [mapOption, optMap2] at h_dec
    cases h_d1 : decodeOperand rp.types ro with
    | none => rw [h_d1] at h_dec; cases h_dec
    | some op =>
      cases h_d2 : mapOption (decodeOperand rp.types) (allRargs.drop (idx + 1)) with
      | none => rw [h_d1, h_d2] at h_dec; cases h_dec
      | some restOpnds =>
        rw [h_d1, h_d2] at h_dec
        injection h_dec with h_opnds
        cases h_opnds
        cases paramTys with
        | nil => cases h_match
        | cons paramTy restParams =>
          dsimp only [callArgsMatchBody] at h_match
          rw [Bool.and_eq_true] at h_match
          have h_m1 : callArgOpMatch bodyLocals paramTy op := by
            cases op with
            | copy place | move place =>
              dsimp only [callArgOpMatch] at h_match
              dsimp only [callArgOpMatch]
              cases h_pe : place.projection.isEmpty with
              | false => rw [h_pe] at h_match; cases h_match.1
              | true =>
                cases h_ty : MirSemantics.getElem? bodyLocals place.localId with
                | none => rw [h_pe, h_ty] at h_match; cases h_match.1
                | some argTy => rw [h_pe, h_ty] at h_match; exact ⟨rfl, argTy, rfl, h_match.1⟩
            | constant c =>
              dsimp only [callArgOpMatch] at h_match
              dsimp only [callArgOpMatch]
              have h_c1 := h_match.1
              rw [Bool.and_eq_true] at h_c1
              cases h_lit : evalConstLit c.ty c.lit with
              | error _ => rw [h_lit] at h_c1; cases h_c1.2
              | ok v => exact ⟨h_c1.1, v, rfl⟩
          have h_arg := evalFnCallArgumentAt_ref_eq rp c ctx rbody blockIdx stmtIdx
            bodyLocals slots cache mem ctrl cm ro op paramTy idx h_locs h_c_len h_inv h_d1 h_m1
          have h_arr_get :
              (⟨allRargs.map (toMiriSpannedOperand rp.types)⟩ : Array Miri.MIR.SpannedOperand)[idx]? =
                some (toMiriSpannedOperand rp.types ro) := by
            simp [List.getElem?_map, h_get_ro]
          dsimp only [evalCalleeAndArgsLoop, List.range']
          rw [List.forIn_cons]
          dsimp only [evalCallArgsOpt, bind, Bind.bind]
          rw [h_arr_get]
          dsimp only [toMiriSpannedOperand]
          rw [miriCleanupMirror_empty_fn, eStateM_bind_assoc]
          cases h_opt1 : evalCallArgOpt bodyLocals slots op paramTy with
          | error k =>
            rw [h_opt1] at h_arg
            let ⟨hk, err, st', h_err, h_fk⟩ := h_arg
            rw [eStateM_bind_err h_err]
            exact ⟨hk, err, st', rfl, h_fk⟩
          | ok pair1 =>
            cases pair1 with
            | mk optVal slots₁ =>
              rw [h_opt1] at h_arg
              rw [eStateM_bind_ok h_arg]
              dsimp only
              have h_hm :
                  (if hasMove = true then
                      (pure (ForInStep.yield ((List.toArray [] : Array (Miri.Memory.Pointer (Option Miri.Memory.Provenance))),
                        acc.push (Miri.Interpreter.FnArg.Copy
                          ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩))) :
                        Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) _)
                    else
                      pure (ForInStep.yield ((List.toArray [] : Array (Miri.Memory.Pointer (Option Miri.Memory.Provenance))),
                        acc.push (Miri.Interpreter.FnArg.Copy
                          ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩)))) =
                    pure (ForInStep.yield ((List.toArray [] : Array (Miri.Memory.Pointer (Option Miri.Memory.Provenance))),
                      acc.push (Miri.Interpreter.FnArg.Copy
                        ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩))) := by
                cases hasMove <;> rfl
              rw [h_hm]
              dsimp only [pure, Pure.pure]
              rw [eStateM_bind_pure]
              dsimp only
              let ⟨h_inv₁, _⟩ := evalCallArgOpt_preserves_slots_match h_inv h_opt1
              have h_c1 : (operandCacheTouch cache op).length = bodyLocals.length := by
                rw [operandCacheTouch_length, h_c_len]
              have h_ih := evalCalleeAndArgs_loop_ref_eq rp c ctx rbody blockIdx stmtIdx bodyLocals mem ctrl cm
                allRargs hasMove h_locs count (idx + 1) (allRargs.drop (idx + 1)) restOpnds restParams
                slots₁ (operandCacheTouch cache op)
                (acc.push (Miri.Interpreter.FnArg.Copy
                  ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩))
                (by rw [Nat.add_assoc, Nat.add_comm 1 count, ← Nat.add_assoc]; exact h_sum) rfl h_d2 h_match.2 h_inv₁ h_c1
              cases h_opt2 : evalCallArgsOpt bodyLocals slots₁ restOpnds restParams with
              | error k =>
                rw [h_opt2] at h_ih
                exact h_ih
              | ok pair2 =>
                cases pair2 with
                | mk pairs₂ slots₂ =>
                  rw [h_opt2] at h_ih
                  let ⟨cache', h_c'_eq, h_c'_len, h_c'_pres, h_inv₂, h_eq⟩ := h_ih
                  refine ⟨cache', h_c'_eq, h_c'_len, ?_, h_inv₂, ?_⟩
                  · intro k hk
                    exact h_c'_pres k (operandCacheTouch_preserves_true op hk)
                  · change evalCalleeAndArgsLoop (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits) c
                        (⟨allRargs.map (toMiriSpannedOperand rp.types)⟩ : Array Miri.MIR.SpannedOperand)
                        true hasMove (List.range' (idx + 1) count 1)
                        (acc.push (Miri.Interpreter.FnArg.Copy
                          ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩))
                        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots₁
                          (operandCacheTouch cache op) mem ctrl cm) = _
                    rw [h_eq]
                    simp only [Array.toList_push, List.map_cons, List.append_assoc, List.singleton_append]

private theorem forIn_congr_body {m : Type u → Type v} [Monad m] {α β : Type u}
    {f g : α → β → m (ForInStep β)} (h : ∀ a b, f a b = g a b) :
    ∀ (xs : List α) (init : β), forIn xs init f = forIn xs init g
  | [], _ => rfl
  | x :: xs, init => by
    rw [List.forIn_cons, List.forIn_cons, h x init]
    apply congrArg (Bind.bind (g x init))
    funext step
    cases step with
    | done _ => rfl
    | yield _ => exact forIn_congr_body h xs _

private theorem evalCalleeAndArgs_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (calleeFnTag : Nat) (calleeRbody : RefBody) (calleeLocalTys : List MirTy)
    (rargs : List RefOperand) (opnds : List Operand) (rdst : RefPlace)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_callee : refResolveCalleeBody rp calleeFnTag = some (calleeRbody, calleeLocalTys))
    (h_disj : refMoveDefinitelyDisjoint rargs rdst = true)
    (h_dec_args : mapOption (decodeOperand rp.types) rargs = some opnds)
    (h_argc : opnds.length = calleeRbody.argumentCount)
    (h_blt : calleeRbody.argumentCount < calleeLocalTys.length)
    (h_match : callArgsMatchBody bodyLocals opnds (List.take calleeRbody.argumentCount (List.drop 1 calleeLocalTys)) = true) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm
    let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
    let funcOp : Miri.MIR.Operand :=
      .Constant { span := { id := 0 }, userType := none, value := .Val .ZeroSized (fnTyBase rp.types + calleeFnTag) }
    let miriArgs : Array Miri.MIR.SpannedOperand := ⟨rargs.map (toMiriSpannedOperand rp.types)⟩
    let paramTys := List.take calleeRbody.argumentCount (List.drop 1 calleeLocalTys)
    match evalCallArgsOpt bodyLocals slots opnds paramTys with
    | .error k =>
      k = .undefined ∧
      ∃ err st',
        Miri.Interpreter.Call.evalCalleeAndArgs calls c funcOp miriArgs (toMiriPlace rdst) st = .error err st' ∧
        stepErrorFaultKind err = some .undefined
    | .ok (pairs, slots') =>
      ∃ cache' calleeAbi,
        refFnAbiOfBody rp.types calleeRbody calleeLocalTys = .ok calleeAbi ∧
        cache' = opnds.foldl operandCacheTouch cache ∧
        cache'.length = bodyLocals.length ∧
        (∀ k, MirSemantics.getElem? cache k = some true → MirSemantics.getElem? cache' k = some true) ∧
        SlotsMatchTys bodyLocals slots' ∧
        Miri.Interpreter.Call.evalCalleeAndArgs calls c funcOp miriArgs (toMiriPlace rdst) st =
          .ok {
            callee := .Instance { kind := .Item calleeFnTag, args := List.toArray [] }
            args := ⟨pairs.map (fun (ty, ov) =>
              Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩
            callerAbi := ()
            fnAbi := some calleeAbi
            withCallerLocation := false
            tempAllocs := List.toArray []
          }
          (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache' mem ctrl cm) := by
  intro st calls funcOp miriArgs paramTys
  have h_fn_op := evalOperand_function_tag_ok rp c ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm calleeFnTag
  have h_md : Miri.Interpreter.Call.moveDefinitelyDisjoint miriArgs (toMiriPlace rdst) = true :=
    moveDefinitelyDisjoint_toMiri_of_ref rp rargs rdst h_disj
  have h_abi : ∃ calleeAbi, refFnAbiOfBody rp.types calleeRbody calleeLocalTys = .ok calleeAbi := by
    dsimp only [refFnAbiOfBody]
    have h_plen : (List.take calleeRbody.argumentCount (List.drop 1 calleeLocalTys)).length = calleeRbody.argumentCount := by
      rw [List.length_take, List.length_drop]
      exact Nat.min_eq_left (Nat.le_sub_one_of_lt h_blt)
    rw [show ((List.take calleeRbody.argumentCount (List.drop 1 calleeLocalTys)).length != calleeRbody.argumentCount) = false from by
      rw [h_plen]; simp]
    dsimp only [Bool.false_eq_true, ite_false_eq]
    have h_0_lt : 0 < calleeLocalTys.length := Nat.lt_of_le_of_lt (Nat.zero_le _) h_blt
    cases h_g0 : calleeLocalTys with
    | nil =>
      rw [h_g0] at h_blt
      cases h_blt
    | cons _ _ => exact ⟨_, rfl⟩
  let ⟨calleeAbi, h_abi_ok⟩ := h_abi
  have h_rargs_len : rargs.length = calleeRbody.argumentCount := by
    have h1 : rargs.length = opnds.length := mapOption_length h_dec_args
    exact h1.trans h_argc
  let hasMove := calls.deinitMovedPlace &&
    ((match funcOp with | .Move _ => calls.deinitMovedPlace | _ => false) ||
      miriArgs.any fun a => match a.operand with | .Move _ => true | _ => false)
  have h_ite_false :
      ∀ {α : Type} {b : Bool} (_hb : b = false) (t e : α),
        (if b = true then t else e) = e := fun hb _t e => by rw [hb]; rfl
  have h_ite_true :
      ∀ {α : Type} {b : Bool} (_hb : b = true) (t e : α),
        (if b = true then t else e) = t := fun hb t _e => by rw [hb]; rfl
  have h_eval_steps :
      Miri.Interpreter.Call.evalCalleeAndArgs calls c funcOp miriArgs (toMiriPlace rdst) st =
        EStateM.bind
          (evalCalleeAndArgsLoop calls c miriArgs true hasMove (List.range' 0 rargs.length 1) (List.toArray []))
          (fun p => evalCalleePostMirror calls c
            { op := .immediate .uninit, layout := { ty := fnTyBase rp.types + calleeFnTag, layout := refUnitLayoutData } }
            p.fst p.snd) st := by
    have h_gen : ∀ (mv : Bool), hasMove = mv →
        Miri.Interpreter.Call.evalCalleeAndArgs calls c funcOp miriArgs (toMiriPlace rdst) st =
          EStateM.bind
            (evalCalleeAndArgsLoop calls c miriArgs true mv (List.range' 0 rargs.length 1) (List.toArray []))
            (fun p => evalCalleePostMirror calls c
              { op := .immediate .uninit, layout := { ty := fnTyBase rp.types + calleeFnTag, layout := refUnitLayoutData } }
              p.fst p.snd) st := by
      intro mv h_mv_eq
      dsimp only [hasMove] at h_mv_eq
      dsimp only [Miri.Interpreter.Call.evalCalleeAndArgs, bind, Bind.bind]
      change EStateM.bind (calls.evalOperandAt c (.instruction "function") funcOp) _ st = _
      rw [eStateM_bind_ok h_fn_op]
      dsimp only
      cases mv with
      | false =>
        change (EStateM.bind (EStateM.pure ()) (fun _ =>
          if (calls.deinitMovedPlace &&
            ((match funcOp with | .Move _ => calls.deinitMovedPlace | _ => false) ||
              miriArgs.any fun a => match a.operand with | .Move _ => true | _ => false)) = true
          then _ else _) st) = _
        rw [h_mv_eq]
        rw [ite_false_eq]
        rw [h_md]
        rw [eStateM_bind_pure]
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        dsimp only [Std.Legacy.Range.start, Std.Legacy.Range.size, Std.Legacy.Range.step]
        have h_sz : miriArgs.size = rargs.length := by simp [miriArgs]
        rw [h_sz, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
        apply congrFun (congr (congrArg EStateM.bind _) (by rfl))
        dsimp only [evalCalleeAndArgsLoop]
        apply forIn_congr_body
        intro index __s
        cases miriArgs[index]? with
        | none => rfl
        | some arg =>
          exact congr (congrArg EStateM.bind rfl) (funext fun fnArg => by
            cases fnArg with
            | InPlace _ snap =>
              cases snap with
              | none => rfl
              | some op => cases op with | mk o l => cases o <;> rfl
            | Copy op =>
              dsimp only
              exact (h_ite_false (by rw [← h_sz]; exact h_mv_eq) _ _).trans rfl)
      | true =>
        change (EStateM.bind (EStateM.pure ()) (fun _ =>
          if (calls.deinitMovedPlace &&
            ((match funcOp with | .Move _ => calls.deinitMovedPlace | _ => false) ||
              miriArgs.any fun a => match a.operand with | .Move _ => true | _ => false)) = true
          then _ else _) st) = _
        rw [h_mv_eq]
        rw [ite_true_eq]
        rw [h_md]
        rw [eStateM_bind_pure]
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        dsimp only [Std.Legacy.Range.start, Std.Legacy.Range.size, Std.Legacy.Range.step]
        have h_sz : miriArgs.size = rargs.length := by simp [miriArgs]
        rw [h_sz, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
        apply congrFun (congr (congrArg EStateM.bind _) (by rfl))
        dsimp only [evalCalleeAndArgsLoop]
        apply forIn_congr_body
        intro index __s
        cases miriArgs[index]? with
        | none => rfl
        | some arg =>
          exact congr (congrArg EStateM.bind rfl) (funext fun fnArg => by
            cases fnArg with
            | InPlace _ snap =>
              cases snap with
              | none => rfl
              | some op => cases op with | mk o l => cases o <;> rfl
            | Copy op =>
              dsimp only
              apply (h_ite_true (by rw [← h_sz]; exact h_mv_eq) _ _).trans
              cases op.op
              · rfl
              · cases (!op.layout.layout.isSized) <;> rfl)
    exact h_gen hasMove rfl
  have h_loop := evalCalleeAndArgs_loop_ref_eq rp c ctx rbody blockIdx stmtIdx bodyLocals mem ctrl cm
    rargs hasMove h_locs rargs.length 0 rargs opnds paramTys slots cache (List.toArray [])
    (Nat.zero_add _) rfl h_dec_args h_match h_inv h_c_len
  cases h_eval : evalCallArgsOpt bodyLocals slots opnds paramTys with
  | error k =>
    rw [h_eval] at h_loop
    let ⟨hk, err, st', h_err, h_fk⟩ := h_loop
    rw [h_eval_steps, eStateM_bind_err h_err]
    exact ⟨hk, err, st', rfl, h_fk⟩
  | ok pair =>
    cases pair with
    | mk pairs slots' =>
      rw [h_eval] at h_loop
      let ⟨cache', h_c'_eq, h_c'_len, h_c'_pres, h_inv', h_loop_ok⟩ := h_loop
      rw [h_eval_steps, eStateM_bind_ok h_loop_ok]
      dsimp only
      refine ⟨cache', calleeAbi, h_abi_ok, h_c'_eq, h_c'_len, h_c'_pres, h_inv', ?_⟩
      let st' := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache' mem ctrl cm
      change evalCalleePostMirror calls c _ (List.toArray [])
        ⟨pairs.map (fun (ty, ov) =>
          Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩
        st' = _
      dsimp only [evalCalleePostMirror]
      rw [miriCleanupMirror_empty]
      dsimp only [bind, Bind.bind, pure, Pure.pure, miriRequireMirror]
      have h_blt_fn : Nat.blt (fnTyBase rp.types + calleeFnTag) (fnTyBase rp.types) = false := by
        cases h_b : Nat.blt (fnTyBase rp.types + calleeFnTag) (fnTyBase rp.types) with
        | false => rfl
        | true => exact False.elim (Nat.not_le_of_gt (Nat.blt_eq.mp h_b) (Nat.le_add_right _ _))
      have h_sig : calls.functionSignature c { ty := fnTyBase rp.types + calleeFnTag, layout := refUnitLayoutData } st' =
          .ok (calleeRbody.argumentCount, ()) st' := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
        rw [callHooks_functionSignature_eq]
        dsimp only
        rw [h_blt_fn, ite_false_eq, Nat.add_sub_cancel_left, h_callee]
      rw [eStateM_bind_ok h_sig]
      have h_ev_sz :
          (⟨pairs.map (fun (ty, ov) =>
              Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩ :
              Array (Miri.Interpreter.FnArg Miri.Memory.Provenance)).size = calleeRbody.argumentCount := by
        have h_plen := evalCallArgsOpt_length bodyLocals slots slots' opnds paramTys pairs h_eval
        simp [h_plen, h_argc]
      have h_req : decide (calleeRbody.argumentCount ≤
          (⟨pairs.map (fun (ty, ov) =>
              Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩ :
              Array (Miri.Interpreter.FnArg Miri.Memory.Provenance)).size) = true := by
        rw [h_ev_sz]; exact decide_eq_true (Nat.le_refl _)
      rw [h_req, ite_true_eq]
      dsimp only [pure, Pure.pure]
      rw [eStateM_bind_pure]
      have h_fk : calls.functionKind (fnTyBase rp.types + calleeFnTag) st' = .ok (.FnDef calleeFnTag (List.toArray [])) st' := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
        rw [callHooks_functionKind_eq]
        rw [h_blt_fn, ite_false_eq, Nat.add_sub_cancel_left]
        rfl
      rw [eStateM_bind_ok h_fk]
      dsimp only
      have h_res : calls.resolve c calleeFnTag (List.toArray []) st' = .ok { kind := .Item calleeFnTag, args := List.toArray [] } st' := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
        rw [callHooks_resolve_eq rp c calleeFnTag (List.toArray []) st']
        rfl
      rw [eStateM_bind_ok h_res]
      dsimp only
      have h_ext_empty :
          Array.map (fun (arg : Miri.Interpreter.FnArg Miri.Memory.Provenance) => arg.layout.ty)
            ((⟨pairs.map (fun (ty, ov) =>
                Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩ :
                Array (Miri.Interpreter.FnArg Miri.Memory.Provenance)).extract calleeRbody.argumentCount) = List.toArray [] := by
        apply Array.ext_getElem?
        simp [h_ev_sz]
      rw [h_ext_empty]
      have h_fabi :
          calls.fnAbiOfInstance c { kind := .Item calleeFnTag, args := List.toArray [] } (List.toArray []) st' = .ok calleeAbi st' := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
        rw [callHooks_fnAbiOfInstance_eq]
        rw [show ((!(List.toArray [] : Array Miri.MIR.TyId).isEmpty) = false) from rfl, ite_false_eq]
        dsimp only
        rw [h_callee]
        dsimp only
        rw [h_abi_ok]
      rw [eStateM_bind_ok h_fabi]
      rw [eStateM_bind_pure]
      have h_rcl : calls.requiresCallerLocation { kind := .Item calleeFnTag, args := List.toArray [] } st' = .ok false st' := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
        exact callHooks_requiresCallerLocation_eq rp { kind := .Item calleeFnTag, args := List.toArray [] } st'
      rw [eStateM_bind_ok h_rcl]
      rfl

/-! ### Section 5C.3: `initStackFrame`, `initFnCall`, and Call Terminators -/

private theorem callHooks_abiCanUnwind_eq (rp : RefProg) (abi : Miri.ABI.FnAbi Miri.MIR.TyId) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).abiCanUnwind abi =
      abi.canUnwind := rfl

private theorem callHooks_abiVariadic_eq (rp : RefProg) (abi : Miri.ABI.FnAbi Miri.MIR.TyId) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).abiVariadic abi =
      abi.cVariadic := rfl

private theorem callHooks_abiArgs_eq (rp : RefProg) (abi : Miri.ABI.FnAbi Miri.MIR.TyId) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).abiArgs abi =
      abi.args := rfl

private theorem callHooks_abiReturn_eq (rp : RefProg) (abi : Miri.ABI.FnAbi Miri.MIR.TyId) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).abiReturn abi =
      abi.ret := rfl

private theorem callHooks_argLayout_eq (rp : RefProg) (a : Miri.ABI.ArgAbi Miri.MIR.TyId) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).argLayout a =
      a.layout := rfl

private theorem callHooks_argIsIgnore_eq (rp : RefProg) (a : Miri.ABI.ArgAbi Miri.MIR.TyId) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).argIsIgnore a =
      a.isIgnore := rfl

private theorem callHooks_isOneZst_eq (rp : RefProg) (l : Miri.Interpreter.LocalLayout) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).isOneZst l =
      l.layout.is1zst := rfl

private theorem callHooks_sameConvention_eq (rp : RefProg)
    (a b : Miri.ABI.FnAbi Miri.MIR.TyId) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).sameConvention a b =
      (a.conv == b.conv) := rfl

private theorem callHooks_isRustCall_eq (rp : RefProg) (u : Unit) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).isRustCall u = false := rfl

private theorem callHooks_checkArgumentCompat_eq (rp : RefProg) (c : Choice)
    (a b : Miri.ABI.ArgAbi Miri.MIR.TyId)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).checkArgumentCompat c a b st =
      .ok (decide ((a == b) = true)) st := rfl

private theorem callHooks_checkTargetFeatures_eq (rp : RefProg) (c : Choice)
    (fnInst : Miri.Interpreter.CallInstance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).checkTargetFeatures c fnInst st =
      .ok () st := rfl

private theorem callHooks_afterFrameInit_eq (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).afterFrameInit c st =
      .ok () st := rfl

private theorem callHooks_isForeignItem_eq (rp : RefProg)
    (fnInst : Miri.Interpreter.CallInstance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).isForeignItem fnInst st =
      .ok false st := rfl

private theorem callHooks_deinitMovedPlace_eq (rp : RefProg) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).deinitMovedPlace = true := rfl

private theorem callHooks_localSpan_eq (rp : RefProg) (b : Miri.MIR.Body) (id : Miri.MIR.LocalId)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).localSpan b id st =
      .ok { id := 0 } st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, Miri.Interpreter.ExecutionCalls.make,
    Miri.Interpreter.TypedMachineBindings.bindValidation, refExecutionConfig, refCompilerHooks,
    refBaseCompilerHooks]

private theorem callHooks_nonCapturingClosure_item (rp : RefProg) (c : Choice) (fnTag : Nat)
    (gargs : Array Miri.MIR.GenericArg) (abi : Miri.ABI.FnAbi Miri.MIR.TyId)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).nonCapturingClosure
        c { kind := .Item fnTag, args := gargs } abi st =
      .ok false st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, Miri.Interpreter.ExecutionCalls.make,
    Miri.Interpreter.TypedMachineBindings.bindValidation, refExecutionConfig,
    Miri.Interpreter.ExecutionCallLeaves.nonCapturingClosure, bind, Bind.bind,
    pure, Pure.pure, EStateM.bind, EStateM.pure]
  rfl

private theorem callHooks_findMirOrEvalFn_item (rp : RefProg) (c : Choice) (fnTag : Nat)
    (abi : Miri.ABI.FnAbi Miri.MIR.TyId)
    (args : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance))
    (dest : Miri.Interpreter.RuntimeStackPlace Miri.Memory.Provenance)
    (ret : Option Miri.MIR.BasicBlockId) (uw : Miri.MIR.UnwindAction)
    (rbody : RefBody) (localTys : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_callee : refResolveCalleeBody rp fnTag = some (rbody, localTys)) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).findMirOrEvalFn
        c { kind := .Item fnTag, args := Array.empty } abi args dest ret uw st =
      .ok (some ({ identity := .ofCanonicalIndex fnTag, body := toMiriBody rp.types rbody },
        { kind := .Item fnTag, args := Array.empty })) st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, Miri.Interpreter.ExecutionCalls.make,
    Miri.Interpreter.CallDispatchMachine.findMirOrEvalFn, refExecutionConfig]
  change (EStateM.bind (fun st => EStateM.Result.ok false st) fun isForeign =>
    if isForeign = true then _ else _) st = _
  dsimp only [EStateM.bind, ite_false]
  change (EStateM.bind get fun st0 => _) st = _
  dsimp only [EStateM.bind, get, MonadStateOf.get]
  rw [h_callee]
  rfl

private theorem callHooks_frameIndex_ok (rp : RefProg) (ctx : SimFrameCtx) (rbody : RefBody)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (bodyLocals : List MirTy)
    (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory) :
    (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).frameIndex
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm) =
      .ok ctx.below.size
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm) := by
  dsimp only [Miri.Interpreter.ExecutionMachine.callHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, Miri.Interpreter.ExecutionCalls.make]
  change (EStateM.bind EStateM.get _) _ = _
  dsimp only [EStateM.bind, EStateM.get]
  have h_fi :
      (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem ctrl cm).stack.frameIndex =
        Except.ok ctx.below.size := by
    dsimp only [Miri.Interpreter.Stack.frameIndex, mkGenSimState, mkRefMiriStackState]
    have h_ne : (ctx.below.push (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache)).isEmpty = false := by
      simp [Array.isEmpty]
    rw [h_ne]
    dsimp only [ite_false, Pure.pure, Except.pure]
    simp [Array.size_push]
  rw [h_fi]
  rfl

private theorem layoutData_beq_refl (l : Miri.ABI.LayoutData) : (l == l) = true := by
  cases l; simp [BEq.beq]

private theorem argAbi_beq_refl (a : Miri.ABI.ArgAbi Miri.MIR.TyId) : (a == a) = true := by
  cases a with | mk l m =>
  cases l with | mk t d =>
  cases m <;> simp [BEq.beq]

private theorem sysrootNumOpOfCode_eq (op : SysrootNumOp) :
    sysrootNumOpOfCode (sysrootNumOpCode op) = some op := by
  cases op with | mk k w s =>
  cases k <;> cases w <;> cases s <;> rfl

private theorem decodeBody_sysrootNumRefBody (rp : RefProg) (op : SysrootNumOp) {i : Nat}
    (h_in : MirSemantics.getElem? rp.types i = some (.int op.width op.signed)) :
    decodeBody rp.types (sysrootNumRefBody rp.types op) = some (sysrootNumBody op) := by
  have h_get : MirSemantics.getElem? rp.types
      (tyIdFor rp.types (.int op.width op.signed)) = some (.int op.width op.signed) :=
    (resolveTy_tyIdFor_of_mem h_in).1
  dsimp only [sysrootNumRefBody, sysrootNumBody, decodeBody, decodeLocalTys, mapOption, optMap2]
  rw [h_get]
  cases op.kind <;> rfl

private theorem resolveTy_tyIdFor_of_decode (ts : List MirTy)
    {rlocs : List Miri.MIR.TyId} {locals : List MirTy}
    (h_dec : decodeLocalTys ts rlocs = some locals) {i : Nat} {ty : MirTy}
    (h_get : MirSemantics.getElem? locals i = some ty) :
    resolveTy ts (tyIdFor ts ty) = some ty :=
  let ⟨_, _, h_t⟩ := decodeLocalTys_mirGetElem? h_dec h_get
  (resolveTy_tyIdFor_of_mem h_t).2

private theorem setElem?_some_of_getElem? {α : Type} :
    ∀ (xs : List α) (i : Nat) (x v : α),
      MirSemantics.getElem? xs i = some x →
      ∃ ys, MirSemantics.setElem? xs i v = some ys
  | [], _, _, _, h => by cases h
  | _ :: rest, 0, _, v, _ => ⟨v :: rest, rfl⟩
  | hd :: rest, i + 1, x, v, h => by
    let ⟨ys, h_ys⟩ := setElem?_some_of_getElem? rest i x v h
    exact ⟨hd :: ys, by dsimp only [MirSemantics.setElem?]; rw [h_ys]⟩

private theorem setElem?_setElem?_same {α : Type} :
    ∀ (xs : List α) (i : Nat) (v₁ v₂ : α) (ys : List α),
      MirSemantics.setElem? xs i v₁ = some ys →
      MirSemantics.setElem? ys i v₂ = MirSemantics.setElem? xs i v₂
  | [], _, _, _, _, h => by cases h
  | _ :: rest, 0, _, v₂, ys, h => by injection h with h_eq; subst h_eq; rfl
  | hd :: rest, i + 1, v₁, v₂, ys, h => by
    dsimp only [MirSemantics.setElem?] at h
    cases h_r : MirSemantics.setElem? rest i v₁ with
    | none => rw [h_r] at h; cases h
    | some rs =>
      rw [h_r] at h; injection h with h_eq; subst h_eq
      dsimp only [MirSemantics.setElem?]
      rw [setElem?_setElem?_same rest i v₁ v₂ rs h_r]

private theorem setElem?_getElem?_eq {α : Type} :
    ∀ (xs : List α) (i j : Nat) (v : α) (ys : List α),
      MirSemantics.setElem? xs i v = some ys →
      MirSemantics.getElem? ys j =
        if j == i then some v else MirSemantics.getElem? xs j
  | [], _, _, _, _, h => by cases h
  | _ :: _, 0, 0, v, ys, h => by injection h with h_eq; subst h_eq; rfl
  | _ :: _, 0, _ + 1, v, ys, h => by injection h with h_eq; subst h_eq; rfl
  | hd :: rest, i + 1, 0, v, ys, h => by
    dsimp only [MirSemantics.setElem?] at h
    cases h_r : MirSemantics.setElem? rest i v with
    | none => rw [h_r] at h; cases h
    | some rs => rw [h_r] at h; injection h with h_eq; subst h_eq; rfl
  | hd :: rest, i + 1, j + 1, v, ys, h => by
    dsimp only [MirSemantics.setElem?] at h
    cases h_r : MirSemantics.setElem? rest i v with
    | none => rw [h_r] at h; cases h
    | some rs =>
      rw [h_r] at h; injection h with h_eq; subst h_eq
      dsimp only [MirSemantics.getElem?]
      rw [setElem?_getElem?_eq rest i j v rs h_r]
      have h_beq : (j + 1 == i + 1) = (j == i) := by
        cases h_ji : (j == i)
        · have hjne : j ≠ i := fun heq => by subst heq; simp at h_ji
          exact beq_false_of_ne (fun h => hjne (Nat.succ.inj h))
        · have hjeq : j = i := eq_of_beq h_ji
          subst hjeq; exact beq_self_eq_true _
      rw [h_beq]

private theorem writePlace_liveUninitSlot_ok (slots : List LocalSlot) (amem : MemoryState)
    (id : LocalId) (ty : MirTy) (v : Val)
    (h_sl : MirSemantics.getElem? slots id = some (liveUninitSlot ty))
    (h_cv : checkVal v ty = true) :
    writePlace slots amem id ty v =
      match MirSemantics.setElem? slots id (.immediate (some v)) with
      | some slots' => .ok (slots', amem)
      | none => .error .unsupported := by
  dsimp only [writePlace]
  have h_not : (!checkVal v ty) = false := by rw [h_cv]; rfl
  rw [h_not, ite_false_eq, h_sl]
  cases ty <;> dsimp only [liveUninitSlot] <;>
    first
    | rfl
    | (cases h_z : isZstEnumTy _ <;>
        first
        | (rw [ite_false_eq]; rfl)
        | (rw [ite_true_eq]; rfl))

private theorem getElem?_cacheTouch_eq :
    ∀ (cache : List Bool) (id k : Nat) (b0 b1 : Bool),
      MirSemantics.getElem? cache k = some b0 →
      MirSemantics.getElem? (cacheTouch cache id) k = some b1 →
      b1 = (b0 || Nat.beq id k)
  | [], _, _, _, _, h0, _ => by cases h0
  | _ :: _, 0, 0, _, _, h0, h1 => by
    dsimp only [cacheTouch, MirSemantics.getElem?] at h0 h1
    injection h0 with hb0; injection h1 with hb1; subst hb0; subst hb1
    simp [Nat.beq]
  | _ :: _, 0, _ + 1, _, _, h0, h1 => by
    dsimp only [cacheTouch, MirSemantics.getElem?] at h0 h1
    rw [h0] at h1; injection h1 with heq; subst heq; simp [Nat.beq]
  | _ :: _, _ + 1, 0, _, _, h0, h1 => by
    dsimp only [cacheTouch, MirSemantics.getElem?] at h0 h1
    rw [h0] at h1; injection h1 with heq; subst heq; simp [Nat.beq]
  | _ :: rest, id + 1, k + 1, b0, b1, h0, h1 =>
    getElem?_cacheTouch_eq rest id k b0 b1 h0 h1

private theorem getElem?_foldl_operandCacheTouch :
    ∀ (opnds : List Operand) (cache : List Bool) (k : Nat) (b0 b1 : Bool),
      MirSemantics.getElem? cache k = some b0 →
      MirSemantics.getElem? (opnds.foldl operandCacheTouch cache) k = some b1 →
      b1 = (b0 || opnds.any (fun op => operandTouchesLocal op k))
  | [], _, _, _, _, h0, h1 => by
    dsimp only [List.foldl] at h1
    rw [h0] at h1; injection h1 with heq; subst heq; simp
  | op :: rest, cache, k, b0, b1, h0, h1 => by
    dsimp only [List.foldl] at h1
    have h_len_eq : (operandCacheTouch cache op).length = cache.length := operandCacheTouch_length _ _
    have hk_lt : k < cache.length := mirGetElem?_lt_of_some h0
    let ⟨bm, hbm⟩ := mirGetElem?_some_of_lt (Nat.lt_of_lt_of_eq hk_lt h_len_eq.symm)
    have h_ih := getElem?_foldl_operandCacheTouch rest (operandCacheTouch cache op) k bm b1 hbm h1
    have h_step : bm = (b0 || operandTouchesLocal op k) := by
      cases op with
      | copy p | move p => exact getElem?_cacheTouch_eq cache p.localId k b0 bm h0 hbm
      | constant _ =>
        dsimp only [operandCacheTouch] at hbm
        rw [h0] at hbm; injection hbm with heq; subst heq; simp [operandTouchesLocal]
    rw [h_ih, h_step]
    simp [List.any_cons, Bool.or_assoc]

private theorem operandCacheTouch_length_foldl :
    ∀ (opnds : List Operand) (cache : List Bool),
      (opnds.foldl operandCacheTouch cache).length = cache.length
  | [], _ => rfl
  | op :: rest, cache => by
    dsimp only [List.foldl]
    rw [operandCacheTouch_length_foldl rest _, operandCacheTouch_length]

private theorem updateMiriLocalsLoop_eq_liftLocalsCached (types : List MirTy) (touched : Nat → Bool) :
    ∀ (idx : Nat) (tys : List MirTy) (oldSlots newSlots : List LocalSlot)
      (oldCache newCache : List Bool),
      oldSlots.length = tys.length →
      oldCache.length = tys.length →
      newCache.length = tys.length →
      (∀ (j : Nat) (b0 b1 : Bool),
        MirSemantics.getElem? oldCache j = some b0 →
        MirSemantics.getElem? newCache j = some b1 →
        b1 = (b0 || touched (idx + j))) →
      updateMiriLocalsLoop types touched idx tys newSlots
          (liftLocalsCached types tys oldSlots oldCache) =
        liftLocalsCached types tys newSlots newCache
  | _, [], [], _, [], [], _, _, _, _ => rfl
  | _, [], _ :: _, _, _, _, h, _, _, _ => by cases h
  | _, [], [], _, _ :: _, _, _, h, _, _ => by cases h
  | _, [], [], _, [], _ :: _, _, _, h, _ => by cases h
  | _, _ :: _, [], _, _, _, h, _, _, _ => by cases h
  | _, _ :: _, _ :: _, _, [], _, _, h, _, _ => by cases h
  | _, _ :: _, _ :: _, _, _ :: _, [], _, _, h, _ => by cases h
  | idx, ty :: tys, oldS :: oldSs, [], oldB :: oldBs, newB :: newBs, _, _, _, _ => rfl
  | idx, ty :: tys, oldS :: oldSs, newS :: newSs, oldB :: oldBs, newB :: newBs,
      h1, h2, h3, h_pt => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2 h3
    dsimp only [liftLocalsCached, updateMiriLocalsLoop]
    have h_is : (refLocalStateOfSlotWithCache types ty oldS oldB).layout.isSome = oldB := by
      cases oldB <;> rfl
    have h_b0 : newB = (oldB || touched (idx + 0)) := h_pt 0 oldB newB rfl rfl
    rw [Nat.add_zero] at h_b0
    rw [h_is, ← h_b0]
    apply congrArg (List.cons _)
    apply updateMiriLocalsLoop_eq_liftLocalsCached types touched (idx + 1) tys oldSs newSs oldBs newBs h1 h2 h3
    intro j b0 b1 hb0 hb1
    have this := h_pt (j + 1) b0 b1 hb0 hb1
    rw [Nat.add_comm j 1, ← Nat.add_assoc] at this
    exact this

private theorem decodePlace_id_empty {ts : List MirTy} {rp : RefPlace} {p : Place}
    (h : decodePlace ts rp = some p) :
    p.localId = rp.localId ∧ p.projection.isEmpty = rp.projection.isEmpty := by
  dsimp only [decodePlace] at h
  cases h_m : mapOption (decodeProjElem ts) rp.projection with
  | none => rw [h_m] at h; cases h
  | some xs =>
    rw [h_m] at h
    injection h with h_eq
    subst h_eq
    refine ⟨rfl, ?_⟩
    cases h_rp : rp.projection with
    | nil =>
      rw [h_rp] at h_m
      injection h_m with hx
      subst hx
      rfl
    | cons pe rest =>
      rw [h_rp] at h_m
      dsimp only [mapOption, optMap2] at h_m
      cases h1 : decodeProjElem ts pe with
      | none => rw [h1] at h_m; cases h_m
      | some y =>
        rw [h1] at h_m
        cases h2 : mapOption (decodeProjElem ts) rest with
        | none => rw [h2] at h_m; cases h_m
        | some ys => rw [h2] at h_m; injection h_m with hx; subst hx; rfl

private theorem mapOption_decodePlace_refMovePlaceList {ts : List MirTy} :
    ∀ {rargs : List RefOperand} {args : List Operand},
      mapOption (decodeOperand ts) rargs = some args →
      mapOption (decodePlace ts) (refMovePlaceList rargs) = some (movePlaceList args)
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by
    dsimp only [mapOption, optMap2] at h
    cases h_op : decodeOperand ts _ with
    | none => rw [h_op] at h; cases h
    | some _ =>
      rw [h_op] at h
      cases h_rest : mapOption (decodeOperand ts) _ <;> rw [h_rest] at h <;> cases h
  | ro :: rrest, op :: rest, h => by
    dsimp only [mapOption, optMap2] at h
    cases h1 : decodeOperand ts ro with
    | none => rw [h1] at h; cases h
    | some op' =>
      rw [h1] at h
      cases h2 : mapOption (decodeOperand ts) rrest with
      | none => rw [h2] at h; cases h
      | some rest' =>
        rw [h2] at h
        injection h with h_eq
        injection h_eq with h_o h_r
        subst h_o; subst h_r
        have ih := mapOption_decodePlace_refMovePlaceList h2
        cases ro with
        | copy rp =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h1; cases h1
          | some p => rw [h_p] at h1; injection h1 with hop; subst hop; exact ih
        | move rp =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h1; cases h1
          | some p =>
            rw [h_p] at h1; injection h1 with hop; subst hop
            dsimp only [refMovePlaceList, movePlaceList, mapOption, optMap2]
            rw [h_p, ih]
        | constant rc =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_t : MirSemantics.getElem? ts rc.ty with
          | none => rw [h_t] at h1; cases h1
          | some ty => rw [h_t] at h1; injection h1 with hop; subst hop; exact ih

private theorem refNatListContains_eq_natListContains (x : Nat) :
    ∀ (ys : List Nat), refNatListContains x ys = natListContains x ys
  | [] => rfl
  | y :: ys => by
    dsimp only [refNatListContains, natListContains]
    rw [refNatListContains_eq_natListContains x ys]

private theorem refPlacesDisjointAux_eq_placesDisjointAux {ts : List MirTy} :
    ∀ (seen : List LocalId) (rps : List RefPlace) (ps : List Place),
      mapOption (decodePlace ts) rps = some ps →
      refPlacesDisjointAux seen rps = placesDisjointAux seen ps
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by cases h
  | _, _ :: _, [], h => by
    dsimp only [mapOption, optMap2] at h
    cases h1 : decodePlace ts _ with
    | none => rw [h1] at h; cases h
    | some _ => rw [h1] at h; cases h2 : mapOption (decodePlace ts) _ <;> rw [h2] at h <;> cases h
  | seen, rp :: rrest, p :: prest, h => by
    dsimp only [mapOption, optMap2] at h
    cases h1 : decodePlace ts rp with
    | none => rw [h1] at h; cases h
    | some p' =>
      rw [h1] at h
      cases h2 : mapOption (decodePlace ts) rrest with
      | none => rw [h2] at h; cases h
      | some prest' =>
        rw [h2] at h; injection h with h_eq; injection h_eq with hp hpr
        subst hp; subst hpr
        let ⟨h_id, h_emp⟩ := decodePlace_id_empty h1
        dsimp only [refPlacesDisjointAux, placesDisjointAux]
        rw [h_id, h_emp, refNatListContains_eq_natListContains,
          refPlacesDisjointAux_eq_placesDisjointAux (rp.localId :: seen) rrest prest' h2]

private theorem mapOption_append {α β : Type} (f : α → Option β) :
    ∀ {xs₁ xs₂ : List α} {ys₁ ys₂ : List β},
      mapOption f xs₁ = some ys₁ →
      mapOption f xs₂ = some ys₂ →
      mapOption f (xs₁ ++ xs₂) = some (ys₁ ++ ys₂)
  | [], _, [], _, _, h2 => h2
  | [], _, _ :: _, _, h1, _ => by cases h1
  | x :: xs, xs₂, ys₁, ys₂, h1, h2 => by
    dsimp only [mapOption, optMap2] at h1
    cases h_fx : f x with
    | none => rw [h_fx] at h1; cases h1
    | some y =>
      rw [h_fx] at h1
      cases h_rest : mapOption f xs with
      | none => rw [h_rest] at h1; cases h1
      | some ys =>
        rw [h_rest] at h1; injection h1 with h_eq; subst h_eq
        dsimp only [List.cons_append, mapOption, optMap2]
        rw [h_fx, mapOption_append f h_rest h2]

private theorem refMoveDefinitelyDisjoint_eq_moveDefinitelyDisjoint {ts : List MirTy}
    {rargs : List RefOperand} {args : List Operand} {rdst : RefPlace} {dst : Place}
    (h_args : mapOption (decodeOperand ts) rargs = some args)
    (h_dst : decodePlace ts rdst = some dst) :
    refMoveDefinitelyDisjoint rargs rdst = moveDefinitelyDisjoint args dst := by
  dsimp only [refMoveDefinitelyDisjoint, moveDefinitelyDisjoint]
  have h_mp := mapOption_decodePlace_refMovePlaceList h_args
  have h_one : mapOption (decodePlace ts) [rdst] = some [dst] := by
    dsimp only [mapOption, optMap2]; rw [h_dst]
  exact refPlacesDisjointAux_eq_placesDisjointAux [] (refMovePlaceList rargs ++ [rdst])
    (movePlaceList args ++ [dst]) (mapOption_append (decodePlace ts) h_mp h_one)

private def miriAtMirror {S A : Type} (values : Array A) (index : Nat) (message : String) :
    Miri.Interpreter.CallM S A :=
  match values[index]? with
  | none => throw (.invalidProgram message)
  | some value => pure value

private def miriSetSpanMirror
    {P S C E Other Extern FnABI ArgABI : Type}
    (calls : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI)
    (span : Miri.MIR.SpanRef) : Miri.Interpreter.CallM S Unit :=
  EStateM.bind calls.getFrame fun frame =>
    calls.setFrame { frame with location := .unwinding span }

private noncomputable def initFrameSimpleLoop
    {P S C E Other Extern FnABI ArgABI : Type}
    (calls : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI) (c : C)
    (loadedBody : Miri.MIR.Body) (args : Array (Miri.Interpreter.FnArg P))
    (callerAbis calleeAbis : Array ArgABI)
    (range : List Nat) (acc : Nat × Nat) : Miri.Interpreter.CallM S (Nat × Nat) :=
  forIn range acc fun zeroIndex __s =>
    let localId := zeroIndex + 1
    EStateM.bind (calls.localSpan loadedBody localId) fun span =>
    EStateM.bind (miriSetSpanMirror calls span) fun _ =>
    EStateM.bind (calls.localLayout c localId) fun layout =>
    EStateM.bind (miriAtMirror calleeAbis __s.snd "missing callee ABI") fun calleeAbi =>
    EStateM.bind (match args[__s.fst]? with
      | none => throw (.undefinedBehavior "calling a function with fewer arguments than it requires")
      | some arg => pure arg) fun caller =>
    EStateM.bind (miriAtMirror callerAbis __s.fst "missing caller ABI") fun callerAbi =>
    EStateM.bind (Miri.Interpreter.Call.passArgument calls c caller callerAbi calleeAbi __s.snd ⟨localId, Array.empty⟩ layout.ty false) fun _ =>
    pure (ForInStep.yield (__s.fst + 1, __s.snd + 1))

private theorem passArgument_single_ref_eq (rp : RefProg) (c : Choice)
    (calleeCtx : SimFrameCtx) (calleeRbody : RefBody) (calleeBody : Body)
    (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (zeroIndex : Nat) (paramTy : MirTy) (optVal : Option Val) (calleeIndex : Nat)
    (h_cbdec : decodeBody rp.types calleeRbody = some calleeBody)
    (h_c_len : cache.length = calleeBody.locals.length)
    (h_inv : SlotsMatchTys calleeBody.locals slots)
    (h_supp : calleeBody.locals.all isSupportedScalarOrUnitTy = true)
    (h_loc_ty : MirSemantics.getElem? calleeBody.locals (zeroIndex + 1) = some paramTy)
    (h_sm : SlotMatchesTy paramTy (.immediate optVal)) :
    let st := mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm
    let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
    let caller : Miri.Interpreter.FnArg Miri.Memory.Provenance :=
      .Copy ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩
    let abi : Miri.ABI.ArgAbi Miri.MIR.TyId :=
      { layout := refLocalLayoutForTy rp.types paramTy, mode := .Direct Miri.ABI.ArgAttributes.new }
    match optVal with
    | none =>
      ∃ err st',
        Miri.Interpreter.Call.passArgument calls c caller abi abi calleeIndex
          ⟨zeroIndex + 1, Array.empty⟩ (tyIdFor rp.types paramTy) false st = .error err st' ∧
        stepErrorFaultKind err = some .undefined
    | some v =>
      ∃ slots',
        MirSemantics.setElem? slots (zeroIndex + 1) (.immediate (some v)) = some slots' ∧
        SlotsMatchTys calleeBody.locals slots' ∧
        Miri.Interpreter.Call.passArgument calls c caller abi abi calleeIndex
          ⟨zeroIndex + 1, Array.empty⟩ (tyIdFor rp.types paramTy) false st =
          .ok () (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots'
            (cacheTouch cache (zeroIndex + 1)) mem ctrl cm) := by
  intro st calls caller abi
  have h_locs : decodeLocalTys rp.types calleeRbody.locals = some calleeBody.locals := by
    dsimp only [decodeBody] at h_cbdec
    cases h_l : decodeLocalTys rp.types calleeRbody.locals with
    | none => rw [h_l] at h_cbdec; cases h_cbdec
    | some ls =>
      rw [h_l] at h_cbdec
      cases h_b : mapOption (decodeBasicBlock rp.types) calleeRbody.basicBlocks with
      | none => rw [h_b] at h_cbdec; cases h_cbdec
      | some bs => rw [h_b] at h_cbdec; injection h_cbdec with hb; subst hb; rfl
  have h_res : resolveTy rp.types (tyIdFor rp.types paramTy) = some paramTy :=
    resolveTy_tyIdFor_of_decode rp.types h_locs h_loc_ty
  have h_pt_supp : isSupportedScalarOrUnitTy paramTy = true :=
    list_all_mirGetElem? h_supp h_loc_ty
  have h_c_lt : zeroIndex + 1 < cache.length := by
    rw [h_c_len]; exact mirGetElem?_lt_of_some h_loc_ty
  let ⟨b_old, h_cb⟩ := mirGetElem?_some_of_lt h_c_lt
  have h_s_lt : zeroIndex + 1 < slots.length := by
    rw [SlotsMatchTys.length_eq h_inv]; exact mirGetElem?_lt_of_some h_loc_ty
  let ⟨slot_old, h_sl⟩ := mirGetElem?_some_of_lt h_s_lt
  let ⟨slots1, h_set1⟩ := setElem?_some_of_getElem? slots (zeroIndex + 1) slot_old
    (liveUninitSlot paramTy) h_sl
  have h_inv1 : SlotsMatchTys calleeBody.locals slots1 :=
    SlotsMatchTys.setElem? h_inv h_loc_ty (slotMatchesTy_liveUninitSlot paramTy) h_set1
  have h_sl1 : MirSemantics.getElem? slots1 (zeroIndex + 1) = some (liveUninitSlot paramTy) := by
    have := setElem?_getElem?_eq slots (zeroIndex + 1) (zeroIndex + 1) (liveUninitSlot paramTy) slots1 h_set1
    simp at this
    exact this
  have h_sd := storageLiveDyn_ref_eq rp calleeCtx calleeRbody calleeBody 0 0 slots cache mem ctrl cm
    (zeroIndex + 1) h_cbdec h_c_len h_inv
  rw [h_loc_ty] at h_sd; dsimp only at h_sd
  rw [h_set1] at h_sd; dsimp only at h_sd
  have h_ep := callHooks_evalPlace_local_ok rp c calleeCtx calleeRbody 0 0 calleeBody.locals
    slots1 cache mem ctrl cm (zeroIndex + 1) false paramTy (liveUninitSlot paramTy)
    h_locs h_c_len h_loc_ty h_sl1
  have h_c1_len : (cacheTouch cache (zeroIndex + 1)).length = calleeBody.locals.length := by
    rw [cacheTouch_length, h_c_len]
  have h_c1_self : MirSemantics.getElem? (cacheTouch cache (zeroIndex + 1)) (zeroIndex + 1) = some true :=
    getElem?_cacheTouch_self h_cb
  have h_cp := copyRuntimePlace_imm_to_local_transmute rp c calleeCtx calleeRbody 0 0
    calleeBody.locals slots1 (cacheTouch cache (zeroIndex + 1)) entryMemory mem ctrl cm
    (zeroIndex + 1) paramTy paramTy optVal (liveUninitSlot paramTy)
    h_loc_ty h_sl1 h_c1_self h_res h_res h_pt_supp h_inv1 h_sm (MirTy.beq_refl paramTy)
  have h_pa_pre :
      Miri.Interpreter.Call.passArgument calls c caller abi abi calleeIndex
          ⟨zeroIndex + 1, Array.empty⟩ (tyIdFor rp.types paramTy) false st =
        EStateM.bind
          (calls.copyAllowTransmute c
            ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩
            (⟨.local calleeCtx.below.size (zeroIndex + 1) none (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0),
              refLocalLayoutForTy rp.types paramTy⟩ : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance).stackView)
          (fun _ => EStateM.pure ())
          (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots1
            (cacheTouch cache (zeroIndex + 1)) mem ctrl cm) := by
    dsimp only [caller, Miri.Interpreter.Call.passArgument, bind, Bind.bind, pure, Pure.pure]
    have h_ty_eq : (tyIdFor rp.types paramTy == (calls.argLayout abi).ty) = true := by
      rw [callHooks_argLayout_eq]
      exact beq_self_eq_true _
    have h_lay_eq : (caller.layout.layout == (calls.argLayout abi).layout) = true := by
      rw [callHooks_argLayout_eq]
      exact layoutData_beq_refl _
    have h_cmp : calls.checkArgumentCompat c abi abi st = .ok true st := by
      rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
        callHooks_checkArgumentCompat_eq, argAbi_beq_refl]
      rfl
    rw [h_ty_eq]
    change EStateM.bind (miriRequireMirror true "callee type does not match ABI") _ st = _
    rw [show (miriRequireMirror true "callee type does not match ABI" :
        Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit) = EStateM.pure () from rfl,
      eStateM_bind_pure]
    rw [h_lay_eq]
    change EStateM.bind (miriRequireMirror true "caller layout does not match ABI") _ st = _
    rw [show (miriRequireMirror true "caller layout does not match ABI" :
        Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit) = EStateM.pure () from rfl,
      eStateM_bind_pure, eStateM_bind_ok h_cmp, ite_true_eq]
    rw [show (!false) = true from rfl, ite_true_eq]
    change EStateM.bind (miriRequireMirror true "nonlocal destination in storage_live_dyn") _ st = _
    rw [show (miriRequireMirror true "nonlocal destination in storage_live_dyn" :
        Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit) = EStateM.pure () from rfl,
      eStateM_bind_pure]
    rw [show (!(Miri.Interpreter.OpTy.metadata ⟨.immediate (optValToMiriImm paramTy optVal),
        refLocalLayoutForTy rp.types paramTy⟩).hasMeta ||
        (refLocalLayoutForTy rp.types paramTy).ty == tyIdFor rp.types paramTy) = true from rfl]
    change EStateM.bind (miriRequireMirror true "argument metadata type mismatch") _ st = _
    rw [show (miriRequireMirror true "argument metadata type mismatch" :
        Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit) = EStateM.pure () from rfl,
      eStateM_bind_pure]
    have h_sd_call : calls.storageLiveDyn c (zeroIndex + 1) .none st =
        .ok () (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots1 cache mem ctrl cm) :=
      h_sd
    rw [show (Miri.Interpreter.OpTy.metadata ⟨.immediate (optValToMiriImm paramTy optVal),
        refLocalLayoutForTy rp.types paramTy⟩) = .none from rfl]
    rw [eStateM_bind_ok h_sd_call]
    change EStateM.bind ((Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).evalPlace c
        ⟨zeroIndex + 1, Array.empty⟩ false) _ _ = _
    rw [eStateM_bind_ok h_ep]
  rw [h_pa_pre]
  have h_cat_eq : (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).copyAllowTransmute c
      ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩
      (⟨.local calleeCtx.below.size (zeroIndex + 1) none (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types paramTy⟩ : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance).stackView =
      Miri.Interpreter.copyRuntimePlace (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        (refExecCfg rp).copy c
        ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩
        ⟨.local calleeCtx.below.size (zeroIndex + 1) none (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types paramTy⟩ true := rfl
  rw [h_cat_eq]
  cases optVal with
  | none =>
    rw [eStateM_bind_err h_cp.choose_spec.choose_spec.1]
    exact ⟨h_cp.choose, h_cp.choose_spec.choose, rfl, h_cp.choose_spec.choose_spec.2⟩
  | some v =>
    have h_cv : checkVal v paramTy = true := h_sm
    have h_wp := writePlace_liveUninitSlot_ok slots1 entryMemory (zeroIndex + 1) paramTy v h_sl1 h_cv
    let ⟨slots2, h_set2⟩ := setElem?_some_of_getElem? slots1 (zeroIndex + 1)
      (liveUninitSlot paramTy) (.immediate (some v)) h_sl1
    have h_set2_eq : MirSemantics.setElem? slots (zeroIndex + 1) (.immediate (some v)) = some slots2 := by
      rw [← setElem?_setElem?_same slots (zeroIndex + 1) (liveUninitSlot paramTy) (.immediate (some v)) slots1 h_set1]
      exact h_set2
    have h_inv2 : SlotsMatchTys calleeBody.locals slots2 :=
      SlotsMatchTys.setElem? h_inv1 h_loc_ty h_sm h_set2
    rw [h_set2] at h_wp
    dsimp only at h_cp
    rw [h_wp] at h_cp
    dsimp only at h_cp
    rw [eStateM_bind_ok h_cp]
    refine ⟨slots2, h_set2_eq, h_inv2, rfl⟩

private theorem mirGetElem?_eq_list_getElem? {α : Type} :
    ∀ (xs : List α) (i : Nat), MirSemantics.getElem? xs i = xs[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, i + 1 => mirGetElem?_eq_list_getElem? rest i

private theorem getElem?_take_drop_param {α : Type} :
    ∀ (xs : List α) (n i : Nat),
      i < n → n < xs.length →
      MirSemantics.getElem? (List.take n (List.drop 1 xs)) i =
        MirSemantics.getElem? xs (i + 1)
  | [], _, _, _, hn => by simp at hn
  | _ :: xs, n + 1, 0, _, hn => by
    cases xs with
    | nil => simp at hn
    | cons _ _ => rfl
  | _ :: xs, n + 1, i + 1, hi, hn => by
    cases xs with
    | nil => simp at hn
    | cons y rest =>
      dsimp only [List.drop, List.take, MirSemantics.getElem?]
      exact getElem?_take_drop_param (y :: rest) n i (Nat.lt_of_succ_lt_succ hi)
        (by dsimp only [List.length] at hn; exact Nat.lt_of_succ_lt_succ hn)

private theorem initFrameSimpleLoop_ref_eq (rp : RefProg) (c : Choice)
    (calleeCtx : SimFrameCtx) (calleeRbody : RefBody) (calleeBody : Body)
    (calleeAbi : Miri.ABI.FnAbi Miri.MIR.TyId)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (allPairs : List (MirTy × Option Val))
    (h_cbdec : decodeBody rp.types calleeRbody = some calleeBody)
    (h_supp : calleeBody.locals.all isSupportedScalarOrUnitTy = true)
    (h_c_argc : Nat.blt calleeBody.argumentCount calleeBody.locals.length = true)
    (h_loc_ovr : calleeCtx.locOverride = some (.unwinding ⟨0⟩))
    (h_abi : refFnAbiOfBody rp.types calleeRbody calleeBody.locals = .ok calleeAbi)
    (h_pairs_len : allPairs.length = calleeBody.argumentCount)
    (h_pairs_match : ∀ (j : Nat) (ty : MirTy) (ov : Option Val),
      MirSemantics.getElem? allPairs j = some (ty, ov) →
      MirSemantics.getElem? calleeBody.locals (j + 1) = some ty ∧ SlotMatchesTy ty (.immediate ov)) :
    ∀ (count idx : Nat) (remPairs : List (MirTy × Option Val))
      (slots : List LocalSlot) (cache : List Bool),
      idx + count = calleeBody.argumentCount →
      allPairs.drop idx = remPairs →
      SlotsMatchTys calleeBody.locals slots →
      cache.length = calleeBody.locals.length →
      let st := mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm
      let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
      let argsArr : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance) :=
        ⟨allPairs.map (fun (ty, ov) =>
          Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩
      let loop := initFrameSimpleLoop calls c (toMiriBody rp.types calleeRbody) argsArr
        calleeAbi.args calleeAbi.args (List.range' idx count 1) (idx, idx) st
      match allSomeVals remPairs with
      | none =>
        ∃ err st', loop = .error err st' ∧ stepErrorFaultKind err = some .undefined
      | some remVals =>
        ∃ slots' cache',
          SlotsMatchTys calleeBody.locals slots' ∧
          cache'.length = calleeBody.locals.length ∧
          (∀ (k : Nat),
            (idx + 1 ≤ k ∧ k < idx + 1 + count →
              ∃ v, MirSemantics.getElem? remVals (k - (idx + 1)) = some v ∧
                MirSemantics.getElem? slots' k = some (.immediate (some v)) ∧
                MirSemantics.getElem? cache' k = some true) ∧
            (¬ (idx + 1 ≤ k ∧ k < idx + 1 + count) →
              MirSemantics.getElem? slots' k = MirSemantics.getElem? slots k ∧
              MirSemantics.getElem? cache' k = MirSemantics.getElem? cache k)) ∧
          loop = .ok (calleeBody.argumentCount, calleeBody.argumentCount)
            (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots' cache' mem ctrl cm)
  | 0, idx, remPairs, slots, cache, h_sum, h_drop, h_inv, h_c_len => by
    rw [Nat.add_zero] at h_sum
    have h_ge : allPairs.length ≤ idx := Nat.le_of_eq (h_pairs_len.trans h_sum.symm)
    have h_nil : remPairs = [] := by rw [← h_drop]; exact List.drop_of_length_le h_ge
    subst h_nil
    dsimp only
    rw [allSomeVals_nil]
    refine ⟨slots, cache, h_inv, h_c_len,
      fun _ => ⟨fun h => False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h.1 h.2)), fun _ => ⟨rfl, rfl⟩⟩, ?_⟩
    dsimp only [initFrameSimpleLoop, List.range']
    rw [List.forIn_nil]
    rw [h_sum]
    rfl
  | count + 1, idx, remPairs, slots, cache, h_sum, h_drop, h_inv, h_c_len => by
    have h_idx_lt : idx < allPairs.length := by
      rw [h_pairs_len, ← h_sum, ← Nat.add_assoc]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos count)
    let ⟨p0, hp0⟩ := mirGetElem?_some_of_lt h_idx_lt
    cases p0 with
    | mk paramTy optVal =>
      have h_drop_cons : allPairs.drop idx = (paramTy, optVal) :: allPairs.drop (idx + 1) :=
        list_drop_eq_getElem?_cons ((mirGetElem?_eq_list_getElem? allPairs idx).symm.trans hp0)
      have h_rem : remPairs = (paramTy, optVal) :: allPairs.drop (idx + 1) :=
        h_drop.symm.trans h_drop_cons
      subst h_rem
      let ⟨h_loc_ty, h_sm⟩ := h_pairs_match idx paramTy optVal hp0
      have h_c_lt : idx + 1 < cache.length := by rw [h_c_len]; exact mirGetElem?_lt_of_some h_loc_ty
      let ⟨b_old, h_cb⟩ := mirGetElem?_some_of_lt h_c_lt
      have h_s_lt : idx + 1 < slots.length := by
        rw [SlotsMatchTys.length_eq h_inv]; exact mirGetElem?_lt_of_some h_loc_ty
      let ⟨slot_old, h_sl⟩ := mirGetElem?_some_of_lt h_s_lt
      have h_locs : decodeLocalTys rp.types calleeRbody.locals = some calleeBody.locals := by
        dsimp only [decodeBody] at h_cbdec
        cases h_l : decodeLocalTys rp.types calleeRbody.locals with
        | none => rw [h_l] at h_cbdec; cases h_cbdec
        | some ls =>
          rw [h_l] at h_cbdec
          cases h_b : mapOption (decodeBasicBlock rp.types) calleeRbody.basicBlocks with
          | none => rw [h_b] at h_cbdec; cases h_cbdec
          | some bs => rw [h_b] at h_cbdec; injection h_cbdec with hb; subst hb; rfl
      have h_st_span :
          (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).localSpan
              (toMiriBody rp.types calleeRbody) (idx + 1)
              (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm) =
            .ok { id := 0 }
              (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm) :=
        callHooks_localSpan_eq rp _ _ _
      have h_set_span :
          miriSetSpanMirror (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits)
              { id := 0 }
              (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm) =
            .ok () (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm) := by
        dsimp only [miriSetSpanMirror, bind, Bind.bind]
        have h_gf :
            (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).getFrame
                (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm) =
              .ok (mkGenSimFrame rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache)
                (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm) :=
          currentFrame_mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm
        rw [eStateM_bind_ok h_gf]
        have h_fr_eq :
            let fr := mkGenSimFrame rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache
            ({ fr with location := .unwinding { id := 0 } } :
              Miri.Interpreter.Frame Miri.Memory.Provenance Miri.Interpreter.LocalLayout
                Miri.Interpreter.MachineHooks.FrameExtra) = fr := by
          dsimp only [mkGenSimFrame]
          rw [h_loc_ovr]
        rw [h_fr_eq]
        exact setCurrentFrame_mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots slots cache cache mem ctrl cm
      have h_lay := placeMachine_layoutLocal_ok rp c calleeCtx calleeRbody 0 0 calleeBody.locals
        slots cache mem ctrl cm (idx + 1) paramTy slot_old h_locs h_c_len h_loc_ty h_sl
      have h_c1_len : (cacheTouch cache (idx + 1)).length = calleeBody.locals.length := by
        rw [cacheTouch_length, h_c_len]
      have h_abi_get :
          calleeAbi.args[idx]? =
            some ({
              layout := refLocalLayoutForTy rp.types paramTy
              mode := .Direct Miri.ABI.ArgAttributes.new } : Miri.ABI.ArgAbi Miri.MIR.TyId) := by
        dsimp only [refFnAbiOfBody] at h_abi
        have h_arg_lt : calleeBody.argumentCount < calleeBody.locals.length := nat_lt_of_blt_eq_true h_c_argc
        have h_rarg_eq : calleeRbody.argumentCount = calleeBody.argumentCount := by
          dsimp only [decodeBody] at h_cbdec
          cases h_l : decodeLocalTys rp.types calleeRbody.locals with
          | none => rw [h_l] at h_cbdec; cases h_cbdec
          | some ls =>
            rw [h_l] at h_cbdec
            cases h_b : mapOption (decodeBasicBlock rp.types) calleeRbody.basicBlocks with
            | none => rw [h_b] at h_cbdec; cases h_cbdec
            | some bs => rw [h_b] at h_cbdec; injection h_cbdec with hb; subst hb; rfl
        have h_td_len : ((calleeBody.locals.drop 1).take calleeRbody.argumentCount).length =
            calleeRbody.argumentCount := by
          rw [h_rarg_eq, List.length_take, List.length_drop]
          exact Nat.min_eq_left (Nat.le_sub_one_of_lt h_arg_lt)
        have h_td_ne : (((calleeBody.locals.drop 1).take calleeRbody.argumentCount).length !=
            calleeRbody.argumentCount) = false := by
          rw [h_td_len]; simp
        rw [h_td_ne] at h_abi
        rw [ite_false_eq] at h_abi
        cases h_g0 : MirSemantics.getElem? calleeBody.locals 0 with
        | none =>
          exact False.elim (Nat.not_le_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) h_arg_lt)
            (mirGetElem?_ge_of_none h_g0))
        | some retTy =>
          rw [h_g0] at h_abi
          dsimp only at h_abi
          injection h_abi with h_fa
          rw [← h_fa]
          have h_idx_argc : idx < calleeBody.argumentCount := by
            rw [← h_sum, ← Nat.add_assoc]
            exact Nat.lt_add_of_pos_right (Nat.succ_pos count)
          have h_p_get : MirSemantics.getElem?
              ((calleeBody.locals.drop 1).take calleeRbody.argumentCount) idx = some paramTy := by
            rw [h_rarg_eq, getElem?_take_drop_param calleeBody.locals calleeBody.argumentCount idx
              h_idx_argc h_arg_lt]
            exact h_loc_ty
          rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map, h_p_get]
          rfl
      have h_arr_get :
          (⟨allPairs.map (fun (ty, ov) =>
              Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩ :
              Array (Miri.Interpreter.FnArg Miri.Memory.Provenance))[idx]? =
            some (.Copy ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩) := by
        simp [List.getElem?_map, (mirGetElem?_eq_list_getElem? allPairs idx).symm.trans hp0]
      let st := mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots cache mem ctrl cm
      let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
      let argsArr : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance) :=
        ⟨allPairs.map (fun (ty, ov) =>
          Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩
      have h_step_pre :
          initFrameSimpleLoop calls c (toMiriBody rp.types calleeRbody) argsArr
              calleeAbi.args calleeAbi.args (List.range' idx (count + 1) 1) (idx, idx) st =
            EStateM.bind
              (Miri.Interpreter.Call.passArgument calls c
                (.Copy ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩)
                ({ layout := refLocalLayoutForTy rp.types paramTy,
                   mode := .Direct Miri.ABI.ArgAttributes.new } : Miri.ABI.ArgAbi Miri.MIR.TyId)
                ({ layout := refLocalLayoutForTy rp.types paramTy,
                   mode := .Direct Miri.ABI.ArgAttributes.new } : Miri.ABI.ArgAbi Miri.MIR.TyId)
                idx ⟨idx + 1, Array.empty⟩ (tyIdFor rp.types paramTy) false)
              (fun _ =>
                initFrameSimpleLoop calls c (toMiriBody rp.types calleeRbody) argsArr
                  calleeAbi.args calleeAbi.args (List.range' (idx + 1) count 1) (idx + 1, idx + 1))
              (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals slots
                (cacheTouch cache (idx + 1)) mem ctrl cm) := by
        dsimp only [initFrameSimpleLoop, List.range']
        rw [List.forIn_cons]
        dsimp only [bind, Bind.bind, pure, Pure.pure]
        rw [eStateM_bind_assoc, eStateM_bind_ok h_st_span, eStateM_bind_assoc,
          eStateM_bind_ok h_set_span, eStateM_bind_assoc, eStateM_bind_ok h_lay]
        rw [eStateM_bind_assoc]
        rw [show miriAtMirror calleeAbi.args idx "missing callee ABI" =
            EStateM.pure ({
              layout := refLocalLayoutForTy rp.types paramTy
              mode := .Direct Miri.ABI.ArgAttributes.new } : Miri.ABI.ArgAbi Miri.MIR.TyId) from by
          dsimp only [miriAtMirror]; rw [h_abi_get]; rfl]
        rw [eStateM_bind_pure, h_arr_get]
        dsimp only
        rw [eStateM_bind_assoc, eStateM_bind_pure, eStateM_bind_assoc]
        rw [show miriAtMirror calleeAbi.args idx "missing caller ABI" =
            EStateM.pure ({
              layout := refLocalLayoutForTy rp.types paramTy
              mode := .Direct Miri.ABI.ArgAttributes.new } : Miri.ABI.ArgAbi Miri.MIR.TyId) from by
          dsimp only [miriAtMirror]; rw [h_abi_get]; rfl]
        rw [eStateM_bind_pure, eStateM_bind_assoc]
        apply congrFun (congrArg (fun fn => EStateM.bind fn _) _)
        apply congrArg (fun ty => Miri.Interpreter.Call.passArgument calls c
          (.Copy ⟨.immediate (optValToMiriImm paramTy optVal), refLocalLayoutForTy rp.types paramTy⟩)
          { layout := refLocalLayoutForTy rp.types paramTy, mode := .Direct Miri.ABI.ArgAttributes.new }
          { layout := refLocalLayoutForTy rp.types paramTy, mode := .Direct Miri.ABI.ArgAttributes.new }
          idx { localId := idx + 1, projection := Array.empty } ty false)
        rfl
      have h_pa := passArgument_single_ref_eq rp c calleeCtx calleeRbody calleeBody slots
        (cacheTouch cache (idx + 1)) mem ctrl cm idx paramTy optVal idx
        h_cbdec h_c1_len h_inv h_supp h_loc_ty h_sm
      dsimp only [calls] at h_step_pre
      dsimp only
      rw [h_step_pre]
      cases optVal with
      | none =>
        rw [allSomeVals_cons_none]
        let ⟨err, st', h_pa_err, h_fk⟩ := h_pa
        rw [eStateM_bind_err h_pa_err]
        exact ⟨err, st', rfl, h_fk⟩
      | some v =>
        let ⟨slots₁, h_set1, h_inv1, h_pa_ok⟩ := h_pa
        rw [eStateM_bind_ok h_pa_ok]
        have h_c2_len : (cacheTouch (cacheTouch cache (idx + 1)) (idx + 1)).length =
            calleeBody.locals.length := by
          rw [cacheTouch_length, h_c1_len]
        have h_ih := initFrameSimpleLoop_ref_eq rp c calleeCtx calleeRbody calleeBody calleeAbi
          mem ctrl cm allPairs h_cbdec h_supp h_c_argc h_loc_ovr h_abi h_pairs_len h_pairs_match
          count (idx + 1) (allPairs.drop (idx + 1)) slots₁
          (cacheTouch (cacheTouch cache (idx + 1)) (idx + 1))
          (by rw [Nat.add_assoc, Nat.add_comm 1 count, ← Nat.add_assoc]; exact h_sum) rfl h_inv1 h_c2_len
        rw [allSomeVals_cons_some]
        cases h_asv : allSomeVals (allPairs.drop (idx + 1)) with
        | none =>
          rw [h_asv] at h_ih
          exact h_ih
        | some restVals =>
          rw [h_asv] at h_ih
          dsimp only [Option.map]
          let ⟨slots', cache', h_inv', h_c'_len, h_pt', h_ih_ok⟩ := h_ih
          refine ⟨slots', cache', h_inv', h_c'_len, ?_, h_ih_ok⟩
          intro k
          constructor
          · intro hk
            have hk_split : k = idx + 1 ∨ (idx + 2 ≤ k ∧ k < idx + 2 + count) :=
              match Nat.eq_or_lt_of_le hk.1 with
              | Or.inl h => Or.inl h.symm
              | Or.inr h =>
                Or.inr ⟨h, by
                  rw [Nat.add_comm count 1, ← Nat.add_assoc] at hk
                  exact hk.2⟩
            cases hk_split with
            | inl hkeq =>
              subst hkeq
              have h_not : ¬ (idx + 2 ≤ idx + 1 ∧ idx + 1 < idx + 2 + count) :=
                fun h => Nat.not_succ_le_self _ h.1
              have h_pres := (h_pt' (idx + 1)).2 h_not
              refine ⟨v, by rw [Nat.sub_self]; rfl, ?_, ?_⟩
              · rw [h_pres.1]
                have h_s1 := setElem?_getElem?_eq slots (idx + 1) (idx + 1) (.immediate (some v)) slots₁ h_set1
                simp at h_s1
                exact h_s1
              · rw [h_pres.2]
                exact getElem?_cacheTouch_self (getElem?_cacheTouch_self h_cb)
            | inr hkr =>
              have h_in := (h_pt' k).1 hkr
              let ⟨w, hw, hsw, hcw⟩ := h_in
              have h_sub : k - (idx + 1) = (k - (idx + 2)) + 1 := by
                apply Nat.sub_eq_of_eq_add
                rw [Nat.add_assoc (k - (idx + 2)) 1 (idx + 1), Nat.add_comm 1 (idx + 1)]
                exact (Nat.sub_add_cancel hkr.1).symm
              rw [h_sub]
              exact ⟨w, hw, hsw, hcw⟩
          · intro h_out
            have h_not : ¬ (idx + 2 ≤ k ∧ k < idx + 2 + count) := by
              intro h
              apply h_out
              refine ⟨Nat.le_trans (Nat.le_succ _) h.1, ?_⟩
              cases h with
              | intro _ h2 =>
                change k < idx + 1 + 1 + count at h2
                rw [Nat.add_assoc (idx + 1) 1 count, Nat.add_comm 1 count] at h2
                exact h2
            have h_ne : k ≠ idx + 1 := by
              intro h_eq
              subst h_eq
              exact h_out ⟨Nat.le_refl _, Nat.lt_add_of_pos_right (Nat.succ_pos count)⟩
            have h_pres := (h_pt' k).2 h_not
            refine ⟨?_, ?_⟩
            · rw [h_pres.1]
              have h_s1 := setElem?_getElem?_eq slots (idx + 1) k (.immediate (some v)) slots₁ h_set1
              rw [beq_false_of_ne h_ne] at h_s1
              exact h_s1
            · rw [h_pres.2]
              have h_c1 : MirSemantics.getElem? (cacheTouch (cacheTouch cache (idx + 1)) (idx + 1)) k =
                  MirSemantics.getElem? cache k := by
                cases h_ck : MirSemantics.getElem? cache k with
                | none =>
                  have hk_ge : cache.length ≤ k := mirGetElem?_ge_of_none h_ck
                  rw [mirGetElem?_none_of_ge (by rw [cacheTouch_length, cacheTouch_length]; exact hk_ge)]
                | some bk =>
                  have h_lt1 : k < (cacheTouch cache (idx + 1)).length := by
                    rw [cacheTouch_length]; exact mirGetElem?_lt_of_some h_ck
                  have h_lt2 : k < (cacheTouch (cacheTouch cache (idx + 1)) (idx + 1)).length := by
                    rw [cacheTouch_length, cacheTouch_length]; exact mirGetElem?_lt_of_some h_ck
                  let ⟨bm, hbm⟩ := mirGetElem?_some_of_lt h_lt1
                  let ⟨b2, hb2⟩ := mirGetElem?_some_of_lt h_lt2
                  have he1 := getElem?_cacheTouch_eq cache (idx + 1) k bk bm h_ck hbm
                  have he2 := getElem?_cacheTouch_eq (cacheTouch cache (idx + 1)) (idx + 1) k bm b2 hbm hb2
                  have hb_ne : Nat.beq (idx + 1) k = false := by
                    cases h : Nat.beq (idx + 1) k with
                    | false => rfl
                    | true => exact absurd (Nat.eq_of_beq_eq_true h) (Ne.symm h_ne)
                  rw [hb_ne, Bool.or_false] at he1 he2
                  subst he2; subst he1; exact hb2
              exact h_c1

private theorem getElem?_calleeInitCacheLoop_ext (argCount : Nat) (tys : List MirTy)
    (cache : List Bool) (h_len : cache.length = tys.length)
    (h_pt : ∀ (k : Nat) (ty : MirTy), MirSemantics.getElem? tys k = some ty →
      MirSemantics.getElem? cache k = some (!Nat.beq k 0 && Nat.ble k argCount)) :
    cache = calleeInitCacheLoop argCount 0 tys := by
  apply List.ext_getElem?
  intro k
  cases h_ty : MirSemantics.getElem? tys k with
  | none =>
    have h_ge : tys.length ≤ k := mirGetElem?_ge_of_none h_ty
    have h_l1 : cache.length ≤ k := by rw [h_len]; exact h_ge
    have h_l2 : (calleeInitCacheLoop argCount 0 tys).length ≤ k := by
      have : ∀ (idx : Nat) (ts : List MirTy), (calleeInitCacheLoop argCount idx ts).length = ts.length := by
        intro idx ts; induction ts generalizing idx with | nil => rfl | cons _ _ ih => simp [calleeInitCacheLoop, ih]
      rw [this 0 tys]; exact h_ge
    rw [List.getElem?_eq_none h_l1, List.getElem?_eq_none h_l2]
  | some ty =>
    have h1 := h_pt k ty h_ty
    have h2 := getElem?_calleeInitCacheLoop argCount 0 tys k ty h_ty
    rw [Nat.zero_add] at h2
    rw [← mirGetElem?_eq_list_getElem?, ← mirGetElem?_eq_list_getElem?, h1, h2]

private theorem initStackFrame_argLoop_eq (rp : RefProg) (c : Choice)
    (calleeRbody : RefBody) (calleeBody : Body)
    (calleeAbi : Miri.ABI.FnAbi Miri.MIR.TyId)
    (argsArr : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance))
    (mbody : Miri.MIR.Body)
    (h_mbody : mbody = toMiriBody rp.types calleeRbody)
    (h_argc : mbody.argumentCount = calleeBody.argumentCount)
    (f : Nat → Nat × Nat →
      Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) (ForInStep (Nat × Nat)))
    (h_body : ∀ (zeroIndex : Nat) (__s : Nat × Nat),
      f zeroIndex __s =
        EStateM.bind ((Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).localSpan mbody (zeroIndex + 1)) fun span =>
        EStateM.bind (miriSetSpanMirror (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits) span) fun _ =>
        EStateM.bind ((Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).localLayout c (zeroIndex + 1)) fun layout =>
        EStateM.bind (miriAtMirror calleeAbi.args __s.snd "missing callee ABI") fun calleeAbi1 =>
        EStateM.bind (match argsArr[__s.fst]? with
          | none => throw (.undefinedBehavior "calling a function with fewer arguments than it requires")
          | some arg => EStateM.pure arg) fun caller =>
        EStateM.bind (miriAtMirror calleeAbi.args __s.fst "missing caller ABI") fun callerAbi =>
        EStateM.bind (Miri.Interpreter.Call.passArgument
            (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits) c caller callerAbi calleeAbi1 __s.snd
            ⟨zeroIndex + 1, Array.empty⟩ layout.ty false) fun _ =>
        EStateM.pure (ForInStep.yield (__s.fst + 1, __s.snd + 1))) :
    forIn ({ stop := mbody.argumentCount, step_pos := Nat.zero_lt_one } : Std.Legacy.Range) (0, 0) f =
      initFrameSimpleLoop (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits)
        c (toMiriBody rp.types calleeRbody) argsArr calleeAbi.args calleeAbi.args
        (List.range' 0 calleeBody.argumentCount 1) (0, 0) := by
  subst h_mbody
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only [Std.Legacy.Range.start, Std.Legacy.Range.size, Std.Legacy.Range.step]
  rw [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, h_argc]
  dsimp only [initFrameSimpleLoop, bind, Bind.bind, pure, Pure.pure]
  apply forIn_congr_body
  intro zeroIndex __s
  rw [h_body zeroIndex __s]
  cases argsArr[__s.fst]? <;> rfl

private theorem eStateM_bind_forIn_congr_err
    {ε σ α β γ : Type}
    {r : List α} {init : β}
    {body1 body2 : α → β → EStateM ε σ (ForInStep β)}
    (h_body : ∀ x b, body1 x b = body2 x b)
    (cont : β → EStateM ε σ γ) (s : σ) {err : ε} {s' : σ}
    (h_err : (forIn r init body2) s = .error err s') :
    EStateM.bind (forIn r init body1) cont s = .error err s' := by
  have hb : body1 = body2 := funext fun x => funext fun b => h_body x b
  subst hb
  exact eStateM_bind_err h_err

private theorem eStateM_bind_forIn_congr_ok
    {ε σ α β γ : Type}
    {r : List α} {init : β}
    {body1 body2 : α → β → EStateM ε σ (ForInStep β)}
    (h_body : ∀ x b, body1 x b = body2 x b)
    (cont : β → EStateM ε σ γ) (s : σ) {res : β} {s1 : σ}
    (h_ok : (forIn r init body2) s = .ok res s1) :
    EStateM.bind (forIn r init body1) cont s = cont res s1 := by
  have hb : body1 = body2 := funext fun x => funext fun b => h_body x b
  subst hb
  exact eStateM_bind_ok h_ok

/-- `EvalRefStepEqClaim` bridge for `Call.initStackFrame`. -/
private theorem initStackFrame_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody calleeRbody : RefBody) (body calleeBody : Body)
    (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (callerSlots : List LocalSlot) (callerCache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (fnTag : Nat) (dst : Place) (dstTy : MirTy) (target : Option BasicBlockId) (unwind : UnwindAction)
    (calleeAbi : Miri.ABI.FnAbi Miri.MIR.TyId)
    (allPairs : List (MirTy × Option Val)) (optDstVal : Option Val) (bDead : Bool)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_cbdec : decodeBody rp.types calleeRbody = some calleeBody)
    (h_callee_res : refResolveCalleeBody rp fnTag = some (calleeRbody, calleeBody.locals))
    (h_abi : refFnAbiOfBody rp.types calleeRbody calleeBody.locals = .ok calleeAbi)
    (h_c_len : callerCache.length = body.locals.length)
    (h_tr : refTopRelevanceValid (ctx.below.size + 1) ctx.topRel?)
    (h_csupp : calleeBody.locals.all isSupportedScalarOrUnitTy = true)
    (h_c_argc : Nat.blt calleeBody.argumentCount calleeBody.locals.length = true)
    (h_c_sa : storageAnnotationsInBounds calleeBody = true)
    (h_c_nb : calleeBody.basicBlocks.isEmpty = false)
    (h_dst_ty : MirSemantics.getElem? body.locals dst.localId = some dstTy)
    (h_dst_ret : match MirSemantics.getElem? calleeBody.locals 0 with
      | some rty => dstTy.beq rty = true | none => False)
    (h_dst_slot : if bDead then MirSemantics.getElem? callerSlots dst.localId = some .dead
      else MirSemantics.getElem? callerSlots dst.localId = some (.immediate optDstVal))
    (h_pairs_len : allPairs.length = calleeBody.argumentCount)
    (h_pairs_match : ∀ (j : Nat) (ty : MirTy) (ov : Option Val),
      MirSemantics.getElem? allPairs j = some (ty, ov) →
      MirSemantics.getElem? calleeBody.locals (j + 1) = some ty ∧ SlotMatchesTy ty (.immediate ov)) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals callerSlots callerCache mem ctrl cm
    let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
    let argsArr : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance) :=
      ⟨allPairs.map (fun (ty, ov) =>
        Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩
    let loadedBody : Miri.Interpreter.LoadedBody :=
      { identity := .ofCanonicalIndex fnTag, body := toMiriBody rp.types calleeRbody }
    let destRsp : Miri.Interpreter.RuntimeStackPlace Miri.Memory.Provenance :=
      .frameLocal ctx.below.size dst.localId none (refLocalLayoutForTy rp.types dstTy)
        (.ofAllocationToken 0)
    let act := Miri.Interpreter.Call.initStackFrame calls c
      { kind := .Item fnTag, args := List.toArray [] } loadedBody calleeAbi argsArr false destRsp
      (.goto target (toMiriUnwindAction unwind)) st
    match bDead, allSomeVals allPairs with
    | true, _ =>
      ∃ err st', act = .error err st' ∧ stepErrorFaultKind err = some .undefined
    | false, none =>
      ∃ err st', act = .error err st' ∧ stepErrorFaultKind err = some .undefined
    | false, some argVals =>
      let callerCache' := cacheTouch callerCache dst.localId
      let oldFr := mkGenSimFrame rp ctx rbody blockIdx stmtIdx body.locals callerSlots callerCache'
      let calleeCtx := SimFrameCtx.call rp.types (ctx.below.push oldFr) (some (ctx.below.size + 1))
        fnTag ctx.below.size dst.localId dstTy target
      let calleeSlots := initLocalsLoop calleeBody argVals 0 calleeBody.locals
      let calleeCache := calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals
      act = .ok () (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals
        calleeSlots calleeCache mem ctrl cm) := by
  intro st calls argsArr loadedBody destRsp act
  have h_locs : decodeLocalTys rp.types rbody.locals = some body.locals := by
    dsimp only [decodeBody] at h_bdec
    cases h_l : decodeLocalTys rp.types rbody.locals with
    | none => rw [h_l] at h_bdec; cases h_bdec
    | some ls =>
      rw [h_l] at h_bdec
      cases h_b : mapOption (decodeBasicBlock rp.types) rbody.basicBlocks with
      | none => rw [h_b] at h_bdec; cases h_bdec
      | some bs => rw [h_b] at h_bdec; injection h_bdec with hb; subst hb; rfl
  have h_ret_ty_eq : MirSemantics.getElem? calleeBody.locals 0 = some dstTy := by
    cases h_r0 : MirSemantics.getElem? calleeBody.locals 0 with
    | none => rw [h_r0] at h_dst_ret; cases h_dst_ret
    | some rty =>
      rw [h_r0] at h_dst_ret
      rw [MirTy.eq_of_beq h_dst_ret]
  have h_rarg_eq : calleeRbody.argumentCount = calleeBody.argumentCount := by
    dsimp only [decodeBody] at h_cbdec
    cases h_l : decodeLocalTys rp.types calleeRbody.locals with
    | none => rw [h_l] at h_cbdec; cases h_cbdec
    | some ls =>
      rw [h_l] at h_cbdec
      cases h_b : mapOption (decodeBasicBlock rp.types) calleeRbody.basicBlocks with
      | none => rw [h_b] at h_cbdec; cases h_cbdec
      | some bs => rw [h_b] at h_cbdec; injection h_cbdec with hb; subst hb; rfl
  have h_abi_fields :
      calleeAbi =
        { args := (List.map (fun ty =>
            ({ layout := refLocalLayoutForTy rp.types ty, mode := Miri.ABI.PassMode.Direct Miri.ABI.ArgAttributes.new } :
              Miri.ABI.ArgAbi Miri.MIR.TyId)) (List.take calleeRbody.argumentCount (List.drop 1 calleeBody.locals))).toArray
          ret := { layout := refLocalLayoutForTy rp.types dstTy, mode := Miri.ABI.PassMode.Direct Miri.ABI.ArgAttributes.new }
          cVariadic := false
          fixedCount := 0
          conv := Miri.ABI.CanonAbi.Rust
          canUnwind := false } := by
    dsimp only [refFnAbiOfBody] at h_abi
    cases h_ne : (List.take calleeRbody.argumentCount (List.drop 1 calleeBody.locals)).length !=
        calleeRbody.argumentCount <;> rw [h_ne] at h_abi
    · rw [h_ret_ty_eq] at h_abi
      injection h_abi with h_fa
      exact h_fa.symm
    · cases h_abi
  have h_var : calls.abiVariadic calleeAbi = false := by
    rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
      callHooks_abiVariadic_eq, h_abi_fields]
  have h_canu : calls.abiCanUnwind calleeAbi = false := by
    rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
      callHooks_abiCanUnwind_eq, h_abi_fields]
  have h_rcl : calls.requiresCallerLocation { kind := .Item fnTag, args := List.toArray [] } st = .ok false st := by
    rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
    exact callHooks_requiresCallerLocation_eq rp _ st
  have h_fn_abi : calls.fnAbiOfInstance c { kind := .Item fnTag, args := List.toArray [] } (List.toArray []) st = .ok calleeAbi st := by
    rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
      callHooks_fnAbiOfInstance_eq]
    rw [show ((!(List.toArray [] : Array Miri.MIR.TyId).isEmpty) = false) from rfl, ite_false_eq]
    dsimp only
    rw [h_callee_res]
    dsimp only
    rw [h_abi]
  have h_conv : calls.sameConvention calleeAbi calleeAbi = true := by
    rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
      callHooks_sameConvention_eq, h_abi_fields]
    rfl
  have h_feat : calls.checkTargetFeatures c { kind := .Item fnTag, args := List.toArray [] } st = .ok () st := by
    rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
    exact callHooks_checkTargetFeatures_eq rp c _ st
  cases bDead with
  | true =>
    dsimp only [act, Miri.Interpreter.Call.initStackFrame, bind, Bind.bind]
    rw [eStateM_bind_ok h_rcl, show (false != false) = false from rfl, ite_false_eq, ite_false_eq]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure, h_var, ite_false_eq, ite_false_eq, eStateM_bind_pure]
    rw [eStateM_bind_ok h_fn_abi, h_conv, ite_true_eq]
    rw [h_var, show (false == false) = true from rfl, ite_true_eq]
    rw [show (false && _) = false from rfl, ite_false_eq]
    rw [eStateM_bind_ok h_feat, h_canu, ite_false_eq]
    let ⟨st_err, h_pto_err⟩ := placeToOp_local_dead rp c ctx rbody blockIdx stmtIdx
      body.locals callerSlots callerCache mem ctrl cm dst.localId dstTy
      h_locs h_c_len h_dst_ty h_dst_slot
    rw [eStateM_bind_err h_pto_err]
    exact ⟨_, st_err, rfl, rfl⟩
  | false =>
    have h_pto := placeToOp_local_live rp c ctx rbody blockIdx stmtIdx body.locals callerSlots
      callerCache mem ctrl cm dst.localId dstTy optDstVal h_locs h_c_len h_dst_ty h_dst_slot
    have h_act_step : ∀ (actRest : Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit),
        EStateM.bind (calls.placeToOp c destRsp) (fun _ => actRest) st =
          actRest (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals callerSlots
            (cacheTouch callerCache dst.localId) mem ctrl cm) := by
      intro actRest; rw [eStateM_bind_ok h_pto]
    cases h_asv : allSomeVals allPairs with
    | none =>
      let calleeCtxRaw : SimFrameCtx :=
        { (SimFrameCtx.call rp.types (ctx.below.push
            (mkGenSimFrame rp ctx rbody blockIdx stmtIdx body.locals callerSlots (cacheTouch callerCache dst.localId)))
            (some (ctx.below.size + 1)) fnTag ctx.below.size dst.localId dstTy target) with
          locOverride := some (.unwinding ⟨0⟩) }
      have h_init_inv : SlotsMatchTys calleeBody.locals (List.replicate calleeBody.locals.length .dead) := by
        induction calleeBody.locals with
        | nil => exact SlotsMatchTys.nil
        | cons ty rest ih => rw [List.length_cons, List.replicate_succ]; exact SlotsMatchTys.cons True.intro ih
      have h_loop := initFrameSimpleLoop_ref_eq rp c calleeCtxRaw calleeRbody calleeBody calleeAbi
        mem ctrl cm allPairs h_cbdec h_csupp h_c_argc rfl h_abi h_pairs_len h_pairs_match
        calleeBody.argumentCount 0 allPairs
        (List.replicate calleeBody.locals.length .dead)
        (List.replicate calleeBody.locals.length false)
        (Nat.zero_add _) rfl h_init_inv (List.length_replicate)
      rw [h_asv] at h_loop
      let ⟨err, st', h_l_err, h_fk⟩ := h_loop
      refine ⟨err, st', ?_, h_fk⟩
      dsimp only [act, Miri.Interpreter.Call.initStackFrame, bind, Bind.bind]
      rw [eStateM_bind_ok h_rcl, show (false != false) = false from rfl, ite_false_eq, ite_false_eq]
      dsimp only [pure, Pure.pure]
      rw [eStateM_bind_pure, h_var, ite_false_eq, ite_false_eq, eStateM_bind_pure]
      rw [eStateM_bind_ok h_fn_abi, h_conv, ite_true_eq]
      rw [h_var, show (false == false) = true from rfl, ite_true_eq]
      rw [show (false && _) = false from rfl, ite_false_eq]
      rw [eStateM_bind_ok h_feat, h_canu, ite_false_eq]
      rw [eStateM_bind_ok h_pto]
      dsimp only
      let callerCache' := cacheTouch callerCache dst.localId
      have h_c'_len : callerCache'.length = body.locals.length := by rw [cacheTouch_length, h_c_len]
      have h_push := pushRaw_ref_eq rp ctx rbody calleeRbody body.locals calleeBody.locals
        blockIdx stmtIdx callerSlots callerCache' calleeBody fnTag dst.localId dstTy target mem ctrl cm
        h_cbdec rfl h_tr
      have h_push_c :
          calls.pushRaw c { kind := .Item fnTag, args := List.toArray [] } loadedBody destRsp
              (.goto target .Unreachable)
              (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals callerSlots callerCache' mem ctrl cm) =
            .ok () (mkGenSimState rp
              { (SimFrameCtx.call rp.types (ctx.below.push
                  (mkGenSimFrame rp ctx rbody blockIdx stmtIdx body.locals callerSlots callerCache'))
                  (some (ctx.below.size + 1)) fnTag ctx.below.size dst.localId dstTy target) with
                locOverride := some (.unwinding ⟨0⟩) }
              calleeRbody 0 0 calleeBody.locals
              (List.replicate calleeBody.locals.length .dead)
              (List.replicate calleeBody.locals.length false) mem ctrl cm) := h_push
      rw [eStateM_bind_ok h_push_c]
      let st2 := mkGenSimState rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
        (List.replicate calleeBody.locals.length .dead)
        (List.replicate calleeBody.locals.length false) mem ctrl cm
      have h_gf :
          calls.getFrame st2 =
            .ok (mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
              (List.replicate calleeBody.locals.length .dead)
              (List.replicate calleeBody.locals.length false)) st2 :=
        currentFrame_mkGenSimState rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
          (List.replicate calleeBody.locals.length .dead)
          (List.replicate calleeBody.locals.length false) mem ctrl cm
      rw [eStateM_bind_ok h_gf]
      have h_loc_eq :
          (mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
            (List.replicate calleeBody.locals.length .dead)
            (List.replicate calleeBody.locals.length false)).location = .unwinding ⟨0⟩ := rfl
      rw [h_loc_eq]
      dsimp only
      rw [eStateM_bind_pure]
      have h_sf : calls.setFrame
          (mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
            (List.replicate calleeBody.locals.length .dead)
            (List.replicate calleeBody.locals.length false)) st2 = .ok () st2 :=
        setCurrentFrame_mkGenSimState rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
          (List.replicate calleeBody.locals.length .dead)
          (List.replicate calleeBody.locals.length .dead)
          (List.replicate calleeBody.locals.length false)
          (List.replicate calleeBody.locals.length false) mem ctrl cm
      let fr2 := mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
        (List.replicate calleeBody.locals.length .dead)
        (List.replicate calleeBody.locals.length false)
      have h_sf_eta :
          calls.setFrame
            { body := fr2.body, bodyIdentity := fr2.bodyIdentity,
              functionInstance := fr2.functionInstance, extra := fr2.extra,
              returnContinuation := fr2.returnContinuation, returnPlace := fr2.returnPlace,
              localsIdentity := fr2.localsIdentity, locals := fr2.locals,
              vaList := fr2.vaList, trackCallerArg := none,
              location := Miri.Interpreter.FrameLocation.unwinding ⟨0⟩ } st2 = .ok () st2 :=
        h_sf
      rw [eStateM_bind_ok h_sf_eta]
      have h_nc : calls.nonCapturingClosure c { kind := .Item fnTag, args := List.toArray [] } calleeAbi st2 = .ok false st2 := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
        exact callHooks_nonCapturingClosure_item rp c fnTag (List.toArray []) calleeAbi st2
      rw [eStateM_bind_ok h_nc, ite_false_eq]
      have h_abi_sz : calleeAbi.args.size = calleeBody.argumentCount := by
        rw [h_abi_fields]
        have h_arg_lt := nat_lt_of_blt_eq_true h_c_argc
        simp only [List.size_toArray, List.length_map, List.length_take, List.length_drop, h_rarg_eq]
        exact Nat.min_eq_left (Nat.le_sub_one_of_lt h_arg_lt)
      have h_args_sz : argsArr.size = calleeBody.argumentCount := by simp [argsArr, h_pairs_len]
      have h_arg_cmp :
          ((argsArr.size + 0) == (calls.abiArgs calleeAbi).size) = true := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
          callHooks_abiArgs_eq, Nat.add_zero, h_args_sz, h_abi_sz]
        exact beq_self_eq_true _
      rw [h_arg_cmp]
      change EStateM.bind (miriRequireMirror _ "mismatch between caller ABI and arguments") _ _ = _
      rw [eStateM_bind_ok (show miriRequireMirror true "mismatch between caller ABI and arguments" st2 = .ok () st2 from rfl)]
      have h_b_argc : loadedBody.body.argumentCount = calleeBody.argumentCount := h_rarg_eq
      have h_spread_none : loadedBody.body.spreadArgument = none := rfl
      have h_bind_retag :
          ∀ (bodyFn : Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) (Nat × Nat))
            (cont : Nat × Nat → Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit),
            EStateM.bind (calls.withRetagMode c .FnEntry bodyFn) cont st2 =
              EStateM.bind bodyFn cont st2 := fun _ _ => rfl
      rw [h_bind_retag]
      simp only [h_spread_none, Bool.false_and,
        show (∀ n : Nat, (none == some n) = false) from fun _ => rfl, ite_false_eq]
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      dsimp only [Std.Legacy.Range.start, Std.Legacy.Range.size, Std.Legacy.Range.step]
      rw [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, h_b_argc, eStateM_bind_assoc]
      dsimp only [initFrameSimpleLoop] at h_l_err
      exact eStateM_bind_forIn_congr_err
        (fun zeroIndex __s => by
          dsimp only [calls, loadedBody]
          rw [show (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).abiArgs calleeAbi = calleeAbi.args from
            callHooks_abiArgs_eq rp calleeAbi]
          cases argsArr[__s.fst]? <;> rfl)
        _ st2 h_l_err
    | some argVals =>
      dsimp only [act, Miri.Interpreter.Call.initStackFrame, bind, Bind.bind]
      rw [eStateM_bind_ok h_rcl, show (false != false) = false from rfl, ite_false_eq, ite_false_eq]
      dsimp only [pure, Pure.pure]
      rw [eStateM_bind_pure, h_var, ite_false_eq, ite_false_eq, eStateM_bind_pure]
      rw [eStateM_bind_ok h_fn_abi, h_conv, ite_true_eq]
      rw [h_var, show (false == false) = true from rfl, ite_true_eq]
      rw [show (false && _) = false from rfl, ite_false_eq]
      rw [eStateM_bind_ok h_feat, h_canu, ite_false_eq]
      rw [eStateM_bind_ok h_pto]
      let callerCache' := cacheTouch callerCache dst.localId
      have h_c'_len : callerCache'.length = body.locals.length := by
        rw [cacheTouch_length, h_c_len]
      have h_push := pushRaw_ref_eq rp ctx rbody calleeRbody body.locals calleeBody.locals
        blockIdx stmtIdx callerSlots callerCache' calleeBody fnTag dst.localId dstTy target mem ctrl cm
        h_cbdec rfl h_tr
      have h_push_c :
          calls.pushRaw c { kind := .Item fnTag, args := List.toArray [] } loadedBody destRsp
              (.goto target .Unreachable)
              (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals callerSlots callerCache' mem ctrl cm) =
            .ok () (mkGenSimState rp
              { (SimFrameCtx.call rp.types (ctx.below.push
                  (mkGenSimFrame rp ctx rbody blockIdx stmtIdx body.locals callerSlots callerCache'))
                  (some (ctx.below.size + 1)) fnTag ctx.below.size dst.localId dstTy target) with
                locOverride := some (.unwinding ⟨0⟩) }
              calleeRbody 0 0 calleeBody.locals
              (List.replicate calleeBody.locals.length .dead)
              (List.replicate calleeBody.locals.length false) mem ctrl cm) :=
        h_push
      rw [eStateM_bind_ok h_push_c]
      let calleeCtxRaw : SimFrameCtx :=
        { (SimFrameCtx.call rp.types (ctx.below.push
            (mkGenSimFrame rp ctx rbody blockIdx stmtIdx body.locals callerSlots callerCache'))
            (some (ctx.below.size + 1)) fnTag ctx.below.size dst.localId dstTy target) with
          locOverride := some (.unwinding ⟨0⟩) }
      let st2 := mkGenSimState rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
        (List.replicate calleeBody.locals.length .dead)
        (List.replicate calleeBody.locals.length false) mem ctrl cm
      have h_gf :
          calls.getFrame st2 =
            .ok (mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
              (List.replicate calleeBody.locals.length .dead)
              (List.replicate calleeBody.locals.length false)) st2 :=
        currentFrame_mkGenSimState rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
          (List.replicate calleeBody.locals.length .dead)
          (List.replicate calleeBody.locals.length false) mem ctrl cm
      rw [eStateM_bind_ok h_gf]
      have h_loc_eq :
          (mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
            (List.replicate calleeBody.locals.length .dead)
            (List.replicate calleeBody.locals.length false)).location = .unwinding ⟨0⟩ := rfl
      rw [h_loc_eq]
      dsimp only
      rw [eStateM_bind_pure]
      have h_sf : calls.setFrame
          (mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
            (List.replicate calleeBody.locals.length .dead)
            (List.replicate calleeBody.locals.length false)) st2 = .ok () st2 :=
        setCurrentFrame_mkGenSimState rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
          (List.replicate calleeBody.locals.length .dead)
          (List.replicate calleeBody.locals.length .dead)
          (List.replicate calleeBody.locals.length false)
          (List.replicate calleeBody.locals.length false) mem ctrl cm
      let fr2 := mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
        (List.replicate calleeBody.locals.length .dead)
        (List.replicate calleeBody.locals.length false)
      have h_sf_eta :
          calls.setFrame
            { body := fr2.body, bodyIdentity := fr2.bodyIdentity,
              functionInstance := fr2.functionInstance, extra := fr2.extra,
              returnContinuation := fr2.returnContinuation, returnPlace := fr2.returnPlace,
              localsIdentity := fr2.localsIdentity, locals := fr2.locals,
              vaList := fr2.vaList, trackCallerArg := none,
              location := Miri.Interpreter.FrameLocation.unwinding ⟨0⟩ } st2 = .ok () st2 :=
        h_sf
      rw [eStateM_bind_ok h_sf_eta]
      have h_nc : calls.nonCapturingClosure c { kind := .Item fnTag, args := List.toArray [] } calleeAbi st2 = .ok false st2 := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
        exact callHooks_nonCapturingClosure_item rp c fnTag (List.toArray []) calleeAbi st2
      rw [eStateM_bind_ok h_nc, ite_false_eq]
      have h_abi_sz : calleeAbi.args.size = calleeBody.argumentCount := by
        rw [h_abi_fields]
        have h_arg_lt := nat_lt_of_blt_eq_true h_c_argc
        simp only [List.size_toArray, List.length_map, List.length_take, List.length_drop, h_rarg_eq]
        exact Nat.min_eq_left (Nat.le_sub_one_of_lt h_arg_lt)
      have h_args_sz : argsArr.size = calleeBody.argumentCount := by
        simp [argsArr, h_pairs_len]
      have h_arg_cmp :
          ((argsArr.size + 0) == (calls.abiArgs calleeAbi).size) = true := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
          callHooks_abiArgs_eq, Nat.add_zero, h_args_sz, h_abi_sz]
        exact beq_self_eq_true _
      rw [h_arg_cmp]
      change EStateM.bind (miriRequireMirror _ "mismatch between caller ABI and arguments") _ _ = _
      rw [eStateM_bind_ok (show miriRequireMirror true "mismatch between caller ABI and arguments" st2 = .ok () st2 from rfl)]
      have h_init_inv : SlotsMatchTys calleeBody.locals (List.replicate calleeBody.locals.length .dead) := by
        induction calleeBody.locals with
        | nil => exact SlotsMatchTys.nil
        | cons ty rest ih =>
          rw [List.length_cons, List.replicate_succ]
          exact SlotsMatchTys.cons True.intro ih
      have h_loop := initFrameSimpleLoop_ref_eq rp c calleeCtxRaw calleeRbody calleeBody calleeAbi
        mem ctrl cm allPairs h_cbdec h_csupp h_c_argc rfl h_abi h_pairs_len h_pairs_match
        calleeBody.argumentCount 0 allPairs
        (List.replicate calleeBody.locals.length .dead)
        (List.replicate calleeBody.locals.length false)
        (Nat.zero_add _) rfl h_init_inv (List.length_replicate)
      have h_b_argc : loadedBody.body.argumentCount = calleeBody.argumentCount := by
        dsimp only [loadedBody, toMiriBody]; exact h_rarg_eq
      have h_retag_simp : ∀ (act : Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) (Nat × Nat)),
          calls.withRetagMode c .FnEntry act st2 = act st2 := fun _ => rfl
      have h_spread_none : loadedBody.body.spreadArgument = none := rfl
      have h_bind_retag :
          ∀ (bodyFn : Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) (Nat × Nat))
            (cont : Nat × Nat → Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit),
            EStateM.bind (calls.withRetagMode c .FnEntry bodyFn) cont st2 =
              EStateM.bind bodyFn cont st2 := fun _ _ => rfl
      rw [h_bind_retag]
      simp only [h_spread_none, Bool.false_and,
        show (∀ n : Nat, (none == some n) = false) from fun _ => rfl, ite_false_eq]
      rw [h_asv] at h_loop
      let ⟨slots', cache', h_inv', h_c'_len, h_pt', h_loop_ok⟩ := h_loop
      dsimp only [initFrameSimpleLoop] at h_loop_ok
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      dsimp only [Std.Legacy.Range.start, Std.Legacy.Range.size, Std.Legacy.Range.step]
      rw [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, h_b_argc, eStateM_bind_assoc]
      rw [eStateM_bind_forIn_congr_ok
        (fun zeroIndex __s => by
          dsimp only [calls, loadedBody]
          rw [show (Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits).abiArgs calleeAbi = calleeAbi.args from
            callHooks_abiArgs_eq rp calleeAbi]
          cases argsArr[__s.fst]? <;> rfl)
        _ st2 h_loop_ok]
      dsimp only
      rw [eStateM_bind_pure]
      dsimp only
      let st3 := mkGenSimState rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals slots' cache' mem ctrl cm
      have h_sp0 : calls.localSpan loadedBody.body 0 st3 = .ok { id := 0 } st3 :=
        callHooks_localSpan_eq rp _ _ _
      have h_set_sp : ∀ (sp : Miri.MIR.SpanRef),
          miriSetSpanMirror calls { id := 0 } st3 = .ok () st3 := by
        intro _
        dsimp only [miriSetSpanMirror, bind, Bind.bind]
        have h_gf3 : calls.getFrame st3 =
            .ok (mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals slots' cache') st3 := by
          dsimp only [calls, st3]
          exact currentFrame_mkGenSimState rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals slots' cache' mem ctrl cm
        rw [eStateM_bind_ok h_gf3]
        have h_fr3 :
            ({ mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals slots' cache' with
                location := .unwinding { id := 0 } } :
              Miri.Interpreter.Frame Miri.Memory.Provenance Miri.Interpreter.LocalLayout
                Miri.Interpreter.MachineHooks.FrameExtra) =
              mkGenSimFrame rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals slots' cache' := rfl
        rw [h_fr3]
        exact setCurrentFrame_mkGenSimState rp calleeCtxRaw calleeRbody 0 0 calleeBody.locals
          slots' slots' cache' cache' mem ctrl cm
      have h_ret_cmp : calls.checkArgumentCompat c (calls.abiReturn calleeAbi) (calls.abiReturn calleeAbi) st3 =
          .ok true st3 := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
          callHooks_checkArgumentCompat_eq, argAbi_beq_refl]
        rfl
      have h_req_cnt :
          ((calleeBody.argumentCount == (calls.abiArgs calleeAbi).size)) = true := by
        rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
          callHooks_abiArgs_eq, h_abi_sz]
        exact beq_self_eq_true _
      have h_nlt : ¬ (calleeBody.argumentCount < argsArr.size) := by
        rw [h_args_sz]; exact Nat.lt_irrefl _
      have h_afi : calls.afterFrameInit c st3 = .ok () st3 :=
        callHooks_afterFrameInit_eq rp c st3
      have h_slots_pre :
          ∀ (k : Nat) (ty : MirTy), MirSemantics.getElem? calleeBody.locals k = some ty →
            if 1 ≤ k ∧ k ≤ calleeBody.argumentCount then
              MirSemantics.getElem? slots' k =
                some (match MirSemantics.getElem? argVals (k - 1) with
                  | some v => .immediate (some v) | none => .dead)
            else
              MirSemantics.getElem? slots' k = some .dead := by
        intro k ty h_tyk
        cases Classical.em (1 ≤ k ∧ k ≤ calleeBody.argumentCount) with
        | inl hk =>
          rw [ite_eq_left hk]
          have hk' : 0 + 1 ≤ k ∧ k < 0 + 1 + calleeBody.argumentCount := by
            rw [Nat.zero_add, Nat.add_comm 1 calleeBody.argumentCount]; exact ⟨hk.1, Nat.lt_succ_of_le hk.2⟩
          let ⟨v, hv, hsk, _⟩ := (h_pt' k).1 hk'
          have h_sub : k - (0 + 1) = k - 1 := by rw [Nat.zero_add]
          rw [h_sub] at hv
          rw [hv, hsk]
        | inr hk =>
          rw [ite_eq_right hk]
          have h_not' : ¬ (0 + 1 ≤ k ∧ k < 0 + 1 + calleeBody.argumentCount) := by
            intro h; rw [Nat.zero_add, Nat.add_comm 1 calleeBody.argumentCount] at h; exact hk ⟨h.1, Nat.le_of_lt_succ h.2⟩
          have h_pres := (h_pt' k).2 h_not'
          rw [h_pres.1, mirGetElem?_eq_list_getElem?, List.getElem?_replicate,
            ite_eq_left (mirGetElem?_lt_of_some h_tyk)]
      have h_pd := pushDone_ref_eq rp c calleeCtxRaw calleeRbody calleeBody slots' cache' argVals mem ctrl cm
        h_cbdec h_c_nb h_c_argc h_c_sa h_c'_len h_inv' rfl h_slots_pre
      have h_pd_c : calls.pushDone c st3 =
          .ok () (mkGenSimState rp { calleeCtxRaw with locOverride := none } calleeRbody 0 0
            calleeBody.locals (initLocalsLoop calleeBody argVals 0 calleeBody.locals) cache' mem ctrl cm) :=
        h_pd
      have h_cache'_eq : cache' = calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals := by
        apply getElem?_calleeInitCacheLoop_ext calleeBody.argumentCount calleeBody.locals cache' h_c'_len
        intro k ty h_tyk
        cases Classical.em (1 ≤ k ∧ k ≤ calleeBody.argumentCount) with
        | inl hk =>
          have hk' : 0 + 1 ≤ k ∧ k < 0 + 1 + calleeBody.argumentCount := by
            rw [Nat.zero_add, Nat.add_comm 1 calleeBody.argumentCount]; exact ⟨hk.1, Nat.lt_succ_of_le hk.2⟩
          let ⟨_, _, _, hck⟩ := (h_pt' k).1 hk'
          have h_ne0 : Nat.beq k 0 = false := by
            cases k with
            | zero => exact absurd hk.1 (by decide)
            | succ _ => rfl
          have h_ble : Nat.ble k calleeBody.argumentCount = true := Nat.ble_eq.mpr hk.2
          rw [h_ne0, h_ble]; exact hck
        | inr hk =>
          have h_not' : ¬ (0 + 1 ≤ k ∧ k < 0 + 1 + calleeBody.argumentCount) := by
            intro h; rw [Nat.zero_add, Nat.add_comm 1 calleeBody.argumentCount] at h; exact hk ⟨h.1, Nat.le_of_lt_succ h.2⟩
          have h_pres := (h_pt' k).2 h_not'
          have h_cf : MirSemantics.getElem? cache' k = some false := by
            rw [h_pres.2, mirGetElem?_eq_list_getElem?, List.getElem?_replicate,
              ite_eq_left (mirGetElem?_lt_of_some h_tyk)]
          have h_cond : (!Nat.beq k 0 && Nat.ble k calleeBody.argumentCount) = false := by
            cases Nat.eq_zero_or_pos k with
            | inl h0 => subst h0; rfl
            | inr hp =>
              have h_gt : calleeBody.argumentCount < k :=
                Nat.lt_of_not_le (fun hle => hk ⟨hp, hle⟩)
              have h_ble : Nat.ble k calleeBody.argumentCount = false := by
                cases hb : Nat.ble k calleeBody.argumentCount with
                | false => rfl
                | true => exact absurd (Nat.ble_eq.mp hb) (Nat.not_le_of_gt h_gt)
              rw [h_ble, Bool.and_false]
          rw [h_cond]; exact h_cf
      rw [eStateM_bind_ok h_sp0]
      change EStateM.bind (miriSetSpanMirror calls { id := 0 }) _ st3 = _
      rw [eStateM_bind_ok (h_set_sp { id := 0 }), eStateM_bind_ok h_ret_cmp, ite_true_eq]
      change EStateM.bind (miriSetSpanMirror calls { id := 0 }) _ st3 = _
      rw [eStateM_bind_ok (h_set_sp { id := 0 }), eStateM_bind_pure]
      rw [h_req_cnt]
      change EStateM.bind (miriRequireMirror true "mismatch between callee ABI and callee body arguments") _ st3 = _
      rw [show (miriRequireMirror true "mismatch between callee ABI and callee body arguments" :
          Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit) = EStateM.pure () from rfl,
        eStateM_bind_pure, ite_eq_right h_nlt, eStateM_bind_ok h_afi]
      rw [h_pd_c, h_cache'_eq]
      rfl

private theorem initFnCall_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody calleeRbody : RefBody) (body calleeBody : Body)
    (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (callerSlots : List LocalSlot) (callerCache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (fnTag : Nat) (dst : Place) (dstTy : MirTy) (target : Option BasicBlockId)
    (calleeAbi : Miri.ABI.FnAbi Miri.MIR.TyId)
    (allPairs : List (MirTy × Option Val)) (optDstVal : Option Val) (bDead : Bool)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_cbdec : decodeBody rp.types calleeRbody = some calleeBody)
    (h_callee_res : refResolveCalleeBody rp fnTag = some (calleeRbody, calleeBody.locals))
    (h_abi : refFnAbiOfBody rp.types calleeRbody calleeBody.locals = .ok calleeAbi)
    (h_c_len : callerCache.length = body.locals.length)
    (h_tr : refTopRelevanceValid (ctx.below.size + 1) ctx.topRel?)
    (h_csupp : calleeBody.locals.all isSupportedScalarOrUnitTy = true)
    (h_c_argc : Nat.blt calleeBody.argumentCount calleeBody.locals.length = true)
    (h_c_sa : storageAnnotationsInBounds calleeBody = true)
    (h_c_nb : calleeBody.basicBlocks.isEmpty = false)
    (h_dst_ty : MirSemantics.getElem? body.locals dst.localId = some dstTy)
    (h_dst_ret : match MirSemantics.getElem? calleeBody.locals 0 with
      | some rty => dstTy.beq rty = true | none => False)
    (h_dst_slot : if bDead then MirSemantics.getElem? callerSlots dst.localId = some .dead
      else MirSemantics.getElem? callerSlots dst.localId = some (.immediate optDstVal))
    (h_pairs_len : allPairs.length = calleeBody.argumentCount)
    (h_pairs_match : ∀ (j : Nat) (ty : MirTy) (ov : Option Val),
      MirSemantics.getElem? allPairs j = some (ty, ov) →
      MirSemantics.getElem? calleeBody.locals (j + 1) = some ty ∧ SlotMatchesTy ty (.immediate ov)) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals callerSlots callerCache mem ctrl cm
    let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
    let argsArr : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance) :=
      ⟨allPairs.map (fun (ty, ov) =>
        Miri.Interpreter.FnArg.Copy ⟨.immediate (optValToMiriImm ty ov), refLocalLayoutForTy rp.types ty⟩)⟩
    let destRsp : Miri.Interpreter.RuntimeStackPlace Miri.Memory.Provenance :=
      .frameLocal ctx.below.size dst.localId none (refLocalLayoutForTy rp.types dstTy)
        (.ofAllocationToken 0)
    let req : Miri.Interpreter.CallRequest Miri.Memory.Provenance Unit Unit (Miri.ABI.FnAbi Miri.MIR.TyId) := {
      callee := .Instance { kind := .Item fnTag, args := List.toArray [] }
      callerAbi := ()
      callerFnAbi := some calleeAbi
      args := argsArr
      withCallerLocation := false
      destination := destRsp
      target := target
      unwind := .Unreachable
      tempAllocs := List.toArray []
    }
    let act := Miri.Interpreter.Call.initFnCall calls c 8 req st
    match bDead, allSomeVals allPairs with
    | true, _ =>
      ∃ err st', act = .error err st' ∧ stepErrorFaultKind err = some .undefined
    | false, none =>
      ∃ err st', act = .error err st' ∧ stepErrorFaultKind err = some .undefined
    | false, some argVals =>
      let callerCache' := cacheTouch callerCache dst.localId
      let oldFr := mkGenSimFrame rp ctx rbody blockIdx stmtIdx body.locals callerSlots callerCache'
      let calleeCtx := SimFrameCtx.call rp.types (ctx.below.push oldFr) (some (ctx.below.size + 1))
        fnTag ctx.below.size dst.localId dstTy target
      let calleeSlots := initLocalsLoop calleeBody argVals 0 calleeBody.locals
      let calleeCache := calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals
      act = .ok () (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals
        calleeSlots calleeCache mem ctrl cm) := by
  intro st calls argsArr destRsp req act
  have h_r0 : ∃ rty, MirSemantics.getElem? calleeBody.locals 0 = some rty ∧ dstTy.beq rty = true := by
    cases h_g : MirSemantics.getElem? calleeBody.locals 0 with
    | none => rw [h_g] at h_dst_ret; cases h_dst_ret
    | some rty => rw [h_g] at h_dst_ret; exact ⟨rty, rfl, h_dst_ret⟩
  let ⟨rty, h_c0, h_dreq⟩ := h_r0
  have h_rarg_eq : calleeRbody.argumentCount = calleeBody.argumentCount := by
    dsimp only [decodeBody] at h_cbdec
    cases h_l : decodeLocalTys rp.types calleeRbody.locals with
    | none => rw [h_l] at h_cbdec; cases h_cbdec
    | some ls =>
      rw [h_l] at h_cbdec
      cases h_b : mapOption (decodeBasicBlock rp.types) calleeRbody.basicBlocks with
      | none => rw [h_b] at h_cbdec; cases h_cbdec
      | some bs => rw [h_b] at h_cbdec; injection h_cbdec with hb; subst hb; rfl
  have h_abi_canu : calleeAbi.canUnwind = false := by
    dsimp only [refFnAbiOfBody] at h_abi
    cases h_ne : (List.take calleeRbody.argumentCount (List.drop 1 calleeBody.locals)).length !=
        calleeRbody.argumentCount <;> rw [h_ne] at h_abi
    · rw [h_c0] at h_abi; injection h_abi with h_fa; rw [← h_fa]
    · cases h_abi
  have h_canu : calls.abiCanUnwind calleeAbi = false := by
    rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl,
      callHooks_abiCanUnwind_eq, h_abi_canu]
  have h_is_for : calls.isForeignItem { kind := .Item fnTag, args := List.toArray [] } st = .ok false st :=
    callHooks_isForeignItem_eq rp _ st
  have h_found : calls.findMirOrEvalFn c { kind := .Item fnTag, args := List.toArray [] } calleeAbi argsArr destRsp target .Unreachable st =
      .ok (some ({ identity := .ofCanonicalIndex fnTag, body := toMiriBody rp.types calleeRbody },
        { kind := .Item fnTag, args := List.toArray [] })) st := by
    rw [show calls = Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits from rfl]
    exact callHooks_findMirOrEvalFn_item rp c fnTag calleeAbi argsArr destRsp target .Unreachable
      calleeRbody calleeBody.locals st h_callee_res
  have h_rc : calls.isRustCall () = false := callHooks_isRustCall_eq rp ()
  have h_isf := initStackFrame_ref_eq rp c ctx rbody calleeRbody body calleeBody blockIdx stmtIdx
    callerSlots callerCache mem ctrl cm fnTag dst dstTy target .unreachable calleeAbi allPairs optDstVal bDead
    h_bdec h_cbdec h_callee_res h_abi h_c_len h_tr h_csupp h_c_argc h_c_sa h_c_nb
    h_dst_ty h_dst_ret h_dst_slot h_pairs_len h_pairs_match
  have h_cleanup_bind_found :
      ∀ {γ : Type}
        (k : Option (Miri.Interpreter.LoadedBody × Miri.Interpreter.CallInstance) →
          Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) Unit)
        (cont : Unit → Miri.Interpreter.CallM (Miri.Interpreter.MachineHooks.State Unit RefUser) γ),
        EStateM.bind
            (miriCleanupMirror calls c (List.toArray [])
              (EStateM.bind
                (calls.findMirOrEvalFn c { kind := .Item fnTag, args := List.toArray [] } calleeAbi argsArr destRsp target
                  .Unreachable)
                k))
            cont st =
          EStateM.bind
            (k (some ({ identity := .ofCanonicalIndex fnTag, body := toMiriBody rp.types calleeRbody },
              { kind := .Item fnTag, args := List.toArray [] })))
            cont st := by
    intro γ k cont
    have h_inner :
        miriCleanupMirror calls c (List.toArray [])
          (EStateM.bind
            (calls.findMirOrEvalFn c { kind := .Item fnTag, args := List.toArray [] } calleeAbi argsArr destRsp target
              .Unreachable)
            k) st =
          k (some ({ identity := .ofCanonicalIndex fnTag, body := toMiriBody rp.types calleeRbody },
            { kind := .Item fnTag, args := List.toArray [] })) st := by
      rw [miriCleanupMirror_empty, eStateM_bind_ok h_found]
    dsimp only [EStateM.bind]
    rw [h_inner]
  have h_de_true : calls.deinitMovedPlace = true := rfl
  have h_ct1 :
      (miriCleanupMirror calls c (List.toArray [])
        (if calls.deinitMovedPlace then
          EStateM.bind (calls.isForeignItem { kind := .Item fnTag, args := List.toArray [] }) fun b =>
            if b then Miri.Interpreter.Call.materializeAndDeinitArgs calls c argsArr
            else pure (argsArr, List.toArray [])
        else pure (argsArr, List.toArray []))) st = .ok (argsArr, List.toArray []) st := by
    rw [miriCleanupMirror_empty]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [h_de_true, ite_true_eq, eStateM_bind_ok h_is_for, ite_false_eq]
    rfl
  cases bDead with
  | true =>
    dsimp only at h_isf
    let ⟨err, st', h_isf_err, h_fk⟩ := h_isf
    refine ⟨err, st', ?_, h_fk⟩
    dsimp only [act, req, Miri.Interpreter.Call.initFnCall, Miri.Interpreter.Call.initFnCall._f,
      Nat.brecOn, Miri.Interpreter.Call.initFnCallStep, bind, Bind.bind, pure, Pure.pure]
    rw [show ((some calleeAbi).any fun abi => !calls.abiCanUnwind abi) = true from by
      dsimp only [Option.any]; rw [h_canu]; rfl, ite_true_eq]
    rw [eStateM_bind_assoc, eStateM_bind_pure, eStateM_bind_assoc]
    change EStateM.bind (miriCleanupMirror calls c (List.toArray [])
      (if calls.deinitMovedPlace then
        EStateM.bind (calls.isForeignItem { kind := .Item fnTag, args := List.toArray [] }) fun b =>
          if b then Miri.Interpreter.Call.materializeAndDeinitArgs calls c argsArr
          else pure (argsArr, List.toArray [])
      else pure (argsArr, List.toArray []))) _ _ = _
    rw [eStateM_bind_ok h_ct1]
    rw [show ((List.toArray [] : Array (Miri.Memory.Pointer (Option Miri.Memory.Provenance))) ++ List.toArray []) = List.toArray [] from rfl]
    dsimp only
    rw [eStateM_bind_assoc]
    change EStateM.bind (miriCleanupMirror calls c (List.toArray [])
      (EStateM.bind (calls.findMirOrEvalFn c { kind := .Item fnTag, args := List.toArray [] }
        calleeAbi argsArr destRsp target .Unreachable) _)) _ _ = _
    rw [h_cleanup_bind_found]
    dsimp only
    rw [h_rc, show (false && !argsArr.isEmpty) = false from rfl, ite_false_eq]
    change EStateM.bind (Miri.Interpreter.Call.initStackFrame calls c { kind := .Item fnTag, args := List.toArray [] }
      ({ identity := .ofCanonicalIndex fnTag, body := toMiriBody rp.types calleeRbody } : Miri.Interpreter.LoadedBody)
      calleeAbi argsArr false destRsp (.goto target (toMiriUnwindAction .unreachable))) _ _ = _
    rw [eStateM_bind_err h_isf_err]
  | false =>
    cases h_asv : allSomeVals allPairs with
    | none =>
      rw [h_asv] at h_isf
      dsimp only at h_isf
      let ⟨err, st', h_isf_err, h_fk⟩ := h_isf
      refine ⟨err, st', ?_, h_fk⟩
      dsimp only [act, req, Miri.Interpreter.Call.initFnCall, Miri.Interpreter.Call.initFnCall._f,
        Nat.brecOn, Miri.Interpreter.Call.initFnCallStep, bind, Bind.bind, pure, Pure.pure]
      rw [show ((some calleeAbi).any fun abi => !calls.abiCanUnwind abi) = true from by
        dsimp only [Option.any]; rw [h_canu]; rfl, ite_true_eq]
      rw [eStateM_bind_assoc, eStateM_bind_pure, eStateM_bind_assoc]
      change EStateM.bind (miriCleanupMirror calls c (List.toArray [])
        (if calls.deinitMovedPlace then
          EStateM.bind (calls.isForeignItem { kind := .Item fnTag, args := List.toArray [] }) fun b =>
            if b then Miri.Interpreter.Call.materializeAndDeinitArgs calls c argsArr
            else pure (argsArr, List.toArray [])
        else pure (argsArr, List.toArray []))) _ _ = _
      rw [eStateM_bind_ok h_ct1]
      rw [show ((List.toArray [] : Array (Miri.Memory.Pointer (Option Miri.Memory.Provenance))) ++ List.toArray []) = List.toArray [] from rfl]
      dsimp only
      rw [eStateM_bind_assoc]
      change EStateM.bind (miriCleanupMirror calls c (List.toArray [])
        (EStateM.bind (calls.findMirOrEvalFn c { kind := .Item fnTag, args := List.toArray [] }
          calleeAbi argsArr destRsp target .Unreachable) _)) _ _ = _
      rw [h_cleanup_bind_found]
      dsimp only
      rw [h_rc, show (false && !argsArr.isEmpty) = false from rfl, ite_false_eq]
      change EStateM.bind (Miri.Interpreter.Call.initStackFrame calls c { kind := .Item fnTag, args := List.toArray [] }
        ({ identity := .ofCanonicalIndex fnTag, body := toMiriBody rp.types calleeRbody } : Miri.Interpreter.LoadedBody)
        calleeAbi argsArr false destRsp (.goto target (toMiriUnwindAction .unreachable))) _ _ = _
      rw [eStateM_bind_err h_isf_err]
    | some argVals =>
      rw [h_asv] at h_isf
      dsimp only at h_isf
      dsimp only [act, req, Miri.Interpreter.Call.initFnCall, Miri.Interpreter.Call.initFnCall._f,
        Nat.brecOn, Miri.Interpreter.Call.initFnCallStep, bind, Bind.bind, pure, Pure.pure]
      rw [show ((some calleeAbi).any fun abi => !calls.abiCanUnwind abi) = true from by
        dsimp only [Option.any]; rw [h_canu]; rfl, ite_true_eq]
      rw [eStateM_bind_assoc, eStateM_bind_pure, eStateM_bind_assoc]
      change EStateM.bind (miriCleanupMirror calls c (List.toArray [])
        (if calls.deinitMovedPlace then
          EStateM.bind (calls.isForeignItem { kind := .Item fnTag, args := List.toArray [] }) fun b =>
            if b then Miri.Interpreter.Call.materializeAndDeinitArgs calls c argsArr
            else pure (argsArr, List.toArray [])
        else pure (argsArr, List.toArray []))) _ _ = _
      rw [eStateM_bind_ok h_ct1]
      rw [show ((List.toArray [] : Array (Miri.Memory.Pointer (Option Miri.Memory.Provenance))) ++ List.toArray []) = List.toArray [] from rfl]
      dsimp only
      rw [eStateM_bind_assoc]
      change EStateM.bind (miriCleanupMirror calls c (List.toArray [])
        (EStateM.bind (calls.findMirOrEvalFn c { kind := .Item fnTag, args := List.toArray [] }
          calleeAbi argsArr destRsp target .Unreachable) _)) _ _ = _
      rw [h_cleanup_bind_found]
      dsimp only
      rw [h_rc, show (false && !argsArr.isEmpty) = false from rfl, ite_false_eq]
      change EStateM.bind (Miri.Interpreter.Call.initStackFrame calls c { kind := .Item fnTag, args := List.toArray [] }
        ({ identity := .ofCanonicalIndex fnTag, body := toMiriBody rp.types calleeRbody } : Miri.Interpreter.LoadedBody)
        calleeAbi argsArr false destRsp (.goto target (toMiriUnwindAction .unreachable))) _ _ = _
      rw [eStateM_bind_ok h_isf]
      rw [eStateM_bind_assoc, eStateM_bind_ok (deallocateTempArgs_empty calls c _), eStateM_bind_pure]
      rfl

private theorem evalCallArgsOpt_pairs_match_aux (callerLocalsTys calleeLocals : List MirTy) :
    ∀ (startIdx : Nat) (slots slots' : List LocalSlot) (opnds : List Operand) (paramTys : List MirTy)
      (pairs : List (MirTy × Option Val)),
      SlotsMatchTys callerLocalsTys slots →
      (∀ (k : Nat) (ty : MirTy), MirSemantics.getElem? paramTys k = some ty →
        MirSemantics.getElem? calleeLocals (startIdx + k) = some ty) →
      evalCallArgsOpt callerLocalsTys slots opnds paramTys = .ok (pairs, slots') →
      pairs.length = paramTys.length ∧
      SlotsMatchTys callerLocalsTys slots' ∧
      (∀ (j : Nat) (ty : MirTy) (ov : Option Val),
        MirSemantics.getElem? pairs j = some (ty, ov) →
        MirSemantics.getElem? calleeLocals (startIdx + j) = some ty ∧ SlotMatchesTy ty (.immediate ov))
  | _, slots, _, [], [], pairs, h_inv, _, h_ok => by
    cases h_ok
    exact ⟨rfl, h_inv, fun j _ _ hj => by cases hj⟩
  | _, _, _, [], _ :: _, _, _, _, h_ok => by cases h_ok
  | _, _, _, _ :: _, [], _, _, _, h_ok => by cases h_ok
  | startIdx, slots, slots', op :: restArgs, pTy :: restParams, pairs, h_inv, h_map, h_ok => by
    dsimp only [evalCallArgsOpt] at h_ok
    cases h1 : evalCallArgOpt callerLocalsTys slots op pTy with
    | error _ => rw [h1] at h_ok; cases h_ok
    | ok pair1 =>
      cases pair1 with
      | mk ov slots₁ =>
        rw [h1] at h_ok; dsimp only at h_ok
        cases h2 : evalCallArgsOpt callerLocalsTys slots₁ restArgs restParams with
        | error _ => rw [h2] at h_ok; cases h_ok
        | ok pair2 =>
          cases pair2 with
          | mk pairs₂ slots₂ =>
            rw [h2] at h_ok; dsimp only at h_ok
            injection h_ok with h_eq; injection h_eq with hp hs
            cases hp; cases hs
            let ⟨h_inv1, h_slot1⟩ := evalCallArgOpt_preserves_slots_match h_inv h1
            have h_map2 : ∀ (k : Nat) (ty : MirTy), MirSemantics.getElem? restParams k = some ty →
                MirSemantics.getElem? calleeLocals ((startIdx + 1) + k) = some ty := by
              intro k ty hk
              rw [Nat.add_assoc, Nat.add_comm 1 k]
              exact h_map (k + 1) ty hk
            let ⟨h_len2, h_inv2, h_pm2⟩ := evalCallArgsOpt_pairs_match_aux callerLocalsTys calleeLocals
              (startIdx + 1) slots₁ slots' restArgs restParams pairs₂ h_inv1 h_map2 h2
            refine ⟨by simp [h_len2], h_inv2, ?_⟩
            intro j ty ov hj
            cases j with
            | zero =>
              dsimp only [MirSemantics.getElem?] at hj
              injection hj with h_p; injection h_p with h_ty h_ov
              subst h_ty; subst h_ov
              refine ⟨by
                have h0 := h_map 0 pTy rfl
                rw [Nat.add_zero] at h0
                exact h0, ?_⟩
              cases op with
              | copy _ | move _ => exact h_slot1
              | constant _ =>
                let ⟨v, hv, h_cv, h_ceq⟩ := h_slot1
                subst hv; subst h_ceq; exact h_cv
            | succ j' =>
              have h_sub := h_pm2 j' ty ov hj
              rw [Nat.add_assoc, Nat.add_comm 1 j'] at h_sub
              exact h_sub

private theorem evalCallArgsOpt_pairs_match (callerLocalsTys : List MirTy) (calleeBody : Body)
    (slots slots' : List LocalSlot) (opnds : List Operand) (pairs : List (MirTy × Option Val))
    (h_inv : SlotsMatchTys callerLocalsTys slots)
    (h_argc : calleeBody.argumentCount < calleeBody.locals.length)
    (h_ok : evalCallArgsOpt callerLocalsTys slots opnds
      (List.take calleeBody.argumentCount (List.drop 1 calleeBody.locals)) = .ok (pairs, slots')) :
    pairs.length = calleeBody.argumentCount ∧
    SlotsMatchTys callerLocalsTys slots' ∧
    (∀ (j : Nat) (ty : MirTy) (ov : Option Val),
      MirSemantics.getElem? pairs j = some (ty, ov) →
      MirSemantics.getElem? calleeBody.locals (j + 1) = some ty ∧ SlotMatchesTy ty (.immediate ov)) := by
  have h_len_td : (List.take calleeBody.argumentCount (List.drop 1 calleeBody.locals)).length =
      calleeBody.argumentCount := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left (Nat.le_sub_one_of_lt h_argc)
  have h_map : ∀ (k : Nat) (ty : MirTy),
      MirSemantics.getElem? (List.take calleeBody.argumentCount (List.drop 1 calleeBody.locals)) k = some ty →
      MirSemantics.getElem? calleeBody.locals (1 + k) = some ty := by
    intro k ty hk
    have hk_lt : k < calleeBody.argumentCount := by
      have h := mirGetElem?_lt_of_some hk
      rw [h_len_td] at h
      exact h
    rw [getElem?_take_drop_param calleeBody.locals calleeBody.argumentCount k hk_lt h_argc] at hk
    rw [Nat.add_comm 1 k]
    exact hk
  let ⟨h_len, h_inv', h_pm⟩ := evalCallArgsOpt_pairs_match_aux callerLocalsTys calleeBody.locals
    1 slots slots' opnds (List.take calleeBody.argumentCount (List.drop 1 calleeBody.locals))
    pairs h_inv h_map h_ok
  refine ⟨h_len.trans h_len_td, h_inv', ?_⟩
  intro j ty ov hj
  have h := h_pm j ty ov hj
  rw [Nat.add_comm 1 j] at h
  exact h

private theorem callTerminator_common_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody calleeRbody : RefBody) (body calleeBody : Body)
    (rbb : RefBasicBlock) (bb : BasicBlock) (f : FrameState) (callers : List FrameState)
    (callerCache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory) (amem : MemoryState)
    (calleeDefId calleeFnTag : Nat) (sysrootOp? : Option SysrootNumOp)
    (rargs : List RefOperand) (args : List Operand) (rdst : RefPlace) (dst : Place)
    (target : Option BasicBlockId) (unwind : UnwindAction)
    (h_bdec : decodeBody rp.types rbody = some body)
    (_h_rbb : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = some rbb)
    (_h_rbb_dec : decodeBasicBlock rp.types rbb = some bb)
    (h_c_len : callerCache.length = body.locals.length)
    (h_tr : refTopRelevanceValid (ctx.below.size + 1) ctx.topRel?)
    (_h_loc : ctx.locOverride = none)
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_callee : refResolveCalleeBody rp calleeFnTag = some (calleeRbody, calleeBody.locals))
    (h_cbdec : decodeBody rp.types calleeRbody = some calleeBody)
    (h_dargs : mapOption (decodeOperand rp.types) rargs = some args)
    (h_ddst : decodePlace rp.types rdst = some dst)
    (h_call_admitted : callTargetAdmitted body bb calleeBody args dst target unwind = true)
    (h_nb : calleeBody.basicBlocks.isEmpty = false)
    (h_sa : storageAnnotationsInBounds calleeBody = true)
    (h_dv : discriminantTypesValid calleeBody = true)
    (h_cv : castTypesValid calleeBody = true)
    (h_av : assignTypesValid calleeBody = true)
    (h_csupp : calleeBody.locals.all isSupportedScalarOrUnitTy = true) :
    let st := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals callerCache mem ctrl cm
    let funcOp : Miri.MIR.Operand :=
      .Constant ⟨⟨0⟩, none, .Val .ZeroSized (fnTyBase rp.types + calleeFnTag)⟩
    let miriTerm : Miri.MIR.Terminator := {
      sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Call funcOp ⟨rargs.map (toMiriSpannedOperand rp.types)⟩ (toMiriPlace rdst) target
        (toMiriUnwindAction unwind) .Normal ⟨0⟩
    }
    let res := (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).terminator c miriTerm st
    match evalCallTerminator body bb f callers amem cm calleeDefId sysrootOp? calleeBody args dst target unwind with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = some k
    | .done _ => False
    | .step s' =>
      ∃ callerLocals' callerCache',
        callerCache' = callCacheTouch dst.localId args callerCache ∧
        callerCache'.length = body.locals.length ∧
        SlotsMatchTys body.locals callerLocals' ∧
        MirSemantics.getElem? callerCache' dst.localId = some true ∧
        (∃ dstTy retTy calleeLocals argVals,
          MirSemantics.getElem? body.locals dst.localId = some dstTy ∧
          isSupportedScalarOrUnitTy dstTy = true ∧
          MirSemantics.getElem? calleeBody.locals 0 = some retTy ∧
          dstTy.beq retTy = true ∧
          calleeLocals = initLocalsLoop calleeBody argVals 0 calleeBody.locals ∧
          s' = {
            frames := {
              defId := calleeDefId
              blockIdx := 0
              stmtIdx := 0
              locals := calleeLocals
              sysrootOp? := sysrootOp?
              retDst? := some dst
              retTarget? := target
            } :: { f with locals := callerLocals' } :: callers
            callerMem := cm
            mem := amem
          } ∧
          let oldFr := mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'
          let calleeCtx := SimFrameCtx.call rp.types (ctx.below.push oldFr) (some (ctx.below.size + 1))
            calleeFnTag ctx.below.size dst.localId dstTy target
          let calleeCache := calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals
          res = (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals
            calleeLocals calleeCache mem ctrl cm, .ok ())) := by
  intro st funcOp miriTerm res
  have h_locs : decodeLocalTys rp.types rbody.locals = some body.locals := by
    dsimp only [decodeBody] at h_bdec
    cases h_l : decodeLocalTys rp.types rbody.locals with
    | none => rw [h_l] at h_bdec; cases h_bdec
    | some ls =>
      rw [h_l] at h_bdec
      cases h_b : mapOption (decodeBasicBlock rp.types) rbody.basicBlocks with
      | none => rw [h_b] at h_bdec; cases h_bdec
      | some bs => rw [h_b] at h_bdec; injection h_bdec with hb; subst hb; rfl
  have h_rarg_eq : calleeRbody.argumentCount = calleeBody.argumentCount := by
    dsimp only [decodeBody] at h_cbdec
    cases h_l : decodeLocalTys rp.types calleeRbody.locals with
    | none => rw [h_l] at h_cbdec; cases h_cbdec
    | some ls =>
      rw [h_l] at h_cbdec
      cases h_b : mapOption (decodeBasicBlock rp.types) calleeRbody.basicBlocks with
      | none => rw [h_b] at h_cbdec; cases h_cbdec
      | some bs => rw [h_b] at h_cbdec; injection h_cbdec with hb; subst hb; rfl
  have h_cta_orig := h_call_admitted
  dsimp only [callTargetAdmitted] at h_call_admitted
  simp only [Bool.and_eq_true] at h_call_admitted
  let ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h_dst_pe⟩, h_disj⟩, h_argc_beq⟩, h_blt_bool⟩, h_dst_ret_pair⟩, h_cmatch⟩ :=
    h_call_admitted
  have h_argc : args.length = calleeBody.argumentCount := Nat.eq_of_beq_eq_true h_argc_beq
  have h_blt : calleeBody.argumentCount < calleeBody.locals.length := nat_lt_of_blt_eq_true h_blt_bool
  have h_dst_info : ∃ dstTy retTy,
      MirSemantics.getElem? body.locals dst.localId = some dstTy ∧
      MirSemantics.getElem? calleeBody.locals 0 = some retTy ∧
      isSupportedScalarOrUnitTy dstTy = true ∧ dstTy.beq retTy = true := by
    cases h_dl : MirSemantics.getElem? body.locals dst.localId with
    | none => rw [h_dl] at h_dst_ret_pair; cases h_dst_ret_pair
    | some dTy =>
      cases h_rl : MirSemantics.getElem? calleeBody.locals 0 with
      | none => rw [h_dl, h_rl] at h_dst_ret_pair; cases h_dst_ret_pair
      | some rTy =>
        rw [h_dl, h_rl, Bool.and_eq_true] at h_dst_ret_pair
        exact ⟨dTy, rTy, rfl, rfl, h_dst_ret_pair.1, h_dst_ret_pair.2⟩
  let ⟨dstTy, retTy, h_dst_ty, h_ret_ty, h_dst_supp, h_dst_ret_beq⟩ := h_dst_info
  let ⟨dstSlot, h_dst_slot⟩ := getElem?_some_of_length_eq (SlotsMatchTys.length_eq h_inv).symm h_dst_ty
  let ⟨_b_dst_cb, h_dst_cb⟩ := mirGetElem?_some_of_lt (xs := callerCache) (i := dst.localId) (by rw [h_c_len]; exact mirGetElem?_lt_of_some h_dst_ty)
  have h_rdst_inv := decodePlace_inv h_ddst
  have h_miri_rdst : toMiriPlace rdst = { localId := dst.localId, projection := Array.empty } := by
    dsimp only [toMiriPlace]; rw [h_rdst_inv.2.trans h_dst_pe, h_rdst_inv.1]; rfl
  have h_rdisj : refMoveDefinitelyDisjoint rargs rdst = true := by
    rw [refMoveDefinitelyDisjoint_eq_moveDefinitelyDisjoint h_dargs h_ddst]; exact h_disj
  have h_eval_call_term_unfold :
      evalCallTerminator body bb f callers amem cm calleeDefId sysrootOp? calleeBody args dst target unwind =
        match evalCallArgs body.locals f.locals amem
            (args.any fun a => match a with | .move _ => true | _ => false) args
            (List.take calleeBody.argumentCount (List.drop 1 calleeBody.locals)) with
        | .error k => .fault k
        | .ok (argVals, callerLocals', mem') =>
          match MirSemantics.getElem? callerLocals' dst.localId with
          | none => .fault .unsupported
          | some .dead => .fault .undefined
          | some (.indirect _) => .fault .unsupported
          | some (.partialTuple _) => .fault .unsupported
          | some (.immediate _) =>
            .step {
              frames := {
                defId := calleeDefId
                blockIdx := 0
                stmtIdx := 0
                locals := initLocalsLoop calleeBody argVals 0 calleeBody.locals
                sysrootOp? := sysrootOp?
                retDst? := some dst
                retTarget? := target
              } :: { f with locals := callerLocals' } :: callers
              callerMem := cm
              mem := mem'
            } := by
    dsimp only [evalCallTerminator]
    rw [h_cta_orig, h_nb, h_sa, h_dv, h_cv, h_av, h_csupp]
    rfl
  let calls := Miri.Interpreter.ExecutionMachine.callHooks (refExecCfg rp) refLimits
  have h_fi0 : calls.frameIndex st = .ok ctx.below.size st :=
    callHooks_frameIndex_ok rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals callerCache mem ctrl cm
  have h_gf0 : calls.getFrame st =
      .ok (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals callerCache) st :=
    currentFrame_mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals callerCache mem ctrl cm
  have h_ep : calls.evalPlace c (toMiriPlace rdst) false st =
      .ok (.frameLocal ctx.below.size dst.localId none (refLocalLayoutForTy rp.types dstTy)
          (.ofAllocationToken 0))
        (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals
          (cacheTouch callerCache dst.localId) mem ctrl cm) := by
    rw [h_miri_rdst]
    exact callHooks_evalPlace_local_ok rp c ctx rbody f.blockIdx f.stmtIdx body.locals
      f.locals callerCache mem ctrl cm dst.localId false dstTy dstSlot h_locs h_c_len h_dst_ty h_dst_slot
  let cache1 := cacheTouch callerCache dst.localId
  have h_c1_len : cache1.length = body.locals.length := by rw [cacheTouch_length, h_c_len]
  have h_ea := evalCalleeAndArgs_ref_eq rp c ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache1
    mem ctrl cm calleeFnTag calleeRbody calleeBody.locals rargs args rdst h_locs h_c1_len h_inv
    h_callee h_rdisj h_dargs (h_argc.trans h_rarg_eq.symm) (by rw [h_rarg_eq]; exact h_blt)
    (by rw [h_rarg_eq]; exact h_cmatch)
  have h_opt_vs := evalCallArgsOpt_vs_evalCallArgs body.locals amem
    (args.any fun a => match a with | .move _ => true | _ => false) f.locals args
    (List.take calleeBody.argumentCount (List.drop 1 calleeBody.locals)) h_inv h_cmatch
  rw [h_eval_call_term_unfold]
  have h_cf_unfold :
      res =
        let oldIndex := st.stack.frames.size
        let oldLoc := st.stack.currentFrame?.map (·.location)
        let r := Miri.Interpreter.MachineHooks.run
          (Miri.Interpreter.Call.evalCallTerminator calls c 8 miriTerm) st
        match r.2 with
        | .error error => (r.1, .error error)
        | .ok () =>
          if target.isSome && r.1.stack.frames.size == oldIndex &&
              r.1.stack.currentFrame?.map (·.location) == oldLoc then
            (r.1, .error (.invalidProgram "evaluating this call made no progress"))
          else (r.1, .ok ()) := rfl
  rw [h_cf_unfold]
  have h_ect_eq :
      Miri.Interpreter.Call.evalCallTerminator calls c 8 miriTerm st =
        EStateM.bind
          (Miri.Interpreter.Call.evalCalleeAndArgs calls c funcOp
            ⟨rargs.map (toMiriSpannedOperand rp.types)⟩ (toMiriPlace rdst))
          (fun evaluated =>
            EStateM.bind
              (Miri.Interpreter.Call.initFnCall calls c 8 {
                callee := evaluated.callee
                callerAbi := evaluated.callerAbi
                callerFnAbi := evaluated.fnAbi
                args := evaluated.args
                withCallerLocation := evaluated.withCallerLocation
                destination := .frameLocal ctx.below.size dst.localId none
                  (refLocalLayoutForTy rp.types dstTy) (.ofAllocationToken 0)
                target := target
                unwind := if Option.any calls.abiCanUnwind evaluated.fnAbi = true then
                    toMiriUnwindAction unwind else .Unreachable
                tempAllocs := evaluated.tempAllocs
              })
              fun _ =>
                if target.isSome = true then
                  EStateM.bind calls.frameIndex fun __do_lift =>
                    if (__do_lift == ctx.below.size) = true then
                      EStateM.bind calls.getFrame fun __do_lift =>
                        if (__do_lift.location == (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx
                            body.locals f.locals callerCache).location) = true then
                          throw (Miri.Interpreter.StepError.invalidProgram "evaluating this call made no progress")
                        else pure ()
                    else pure ()
                else pure ())
          (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache1 mem ctrl cm) := by
    dsimp only [Miri.Interpreter.Call.evalCallTerminator, miriTerm, bind, Bind.bind]
    rw [eStateM_bind_ok h_fi0, eStateM_bind_ok h_gf0]
    rw [eStateM_bind_ok h_ep]
  dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
  rw [h_ect_eq]
  dsimp only at h_ea
  rw [h_rarg_eq] at h_ea
  cases h_opt : evalCallArgsOpt body.locals f.locals args (List.take calleeBody.argumentCount (List.drop 1 calleeBody.locals)) with
  | error k =>
    rw [h_opt] at h_ea h_opt_vs
    dsimp only at h_opt_vs
    let ⟨hk_eq, err, st', h_ea_err, h_fk⟩ := h_ea
    rw [h_opt_vs.2, eStateM_bind_err h_ea_err]
    exact ⟨err, st', rfl, h_opt_vs.1.symm ▸ h_fk⟩
  | ok pair =>
    cases pair with
    | mk pairs callerLocals' =>
      rw [h_opt] at h_ea h_opt_vs
      dsimp only at h_opt_vs
      let ⟨cache', calleeAbi, h_abi_ok, h_c'_eq, h_c'_len, h_c'_pres, h_inv', h_ea_ok⟩ := h_ea
      rw [eStateM_bind_ok h_ea_ok]
      dsimp only
      have h_abi_canu : calls.abiCanUnwind calleeAbi = false := by
        dsimp only [refFnAbiOfBody] at h_abi_ok
        cases h_ne : (List.take calleeRbody.argumentCount (List.drop 1 calleeBody.locals)).length !=
            calleeRbody.argumentCount <;> rw [h_ne] at h_abi_ok
        · rw [h_ret_ty] at h_abi_ok
          injection h_abi_ok with h_fa
          rw [← h_fa]; rfl
        · cases h_abi_ok
      rw [show Option.any calls.abiCanUnwind (some calleeAbi) = false from h_abi_canu, ite_false_eq]
      let ⟨h_pairs_len, _, h_pairs_match⟩ :=
        evalCallArgsOpt_pairs_match body.locals calleeBody f.locals callerLocals' args pairs
          h_inv h_blt h_opt
      have h_disj_mv : ∀ p, p ∈ MirSemantics.movePlaceList args → p.localId ≠ dst.localId := by
        intro p hp
        let ⟨rp', hrp', hid⟩ := movePlaceList_decode_eq rp.types rargs args h_dargs p hp
        have h_rdst_ne : rp'.localId ≠ rdst.localId :=
          refPlacesDisjointAux_not_mem_end (refMovePlaceList rargs) [] rdst h_rdisj rp' hrp'
        rw [hid, ← h_rdst_inv.1]
        exact h_rdst_ne
      have h_dst_same : MirSemantics.getElem? callerLocals' dst.localId = some dstSlot :=
        (evalCallArgsOpt_dst_preserved body.locals dst.localId f.locals callerLocals' args
          (List.take calleeBody.argumentCount (List.drop 1 calleeBody.locals)) pairs h_disj_mv h_opt).trans
          h_dst_slot
      have h_dst_sm : SlotMatchesTy dstTy dstSlot := SlotsMatchTys.getElem? h_inv' h_dst_ty h_dst_same
      have h_dst_c1 : MirSemantics.getElem? cache1 dst.localId = some true :=
        getElem?_cacheTouch_self h_dst_cb
      have h_dst_c' : MirSemantics.getElem? cache' dst.localId = some true := h_c'_pres dst.localId h_dst_c1
      have h_ct_c' : cacheTouch cache' dst.localId = cache' := cacheTouch_eq_self_of_true h_dst_c'
      cases dstSlot with
      | indirect _ => cases h_dst_sm
      | partialTuple _ => cases h_dst_sm
      | dead =>
        have h_ifc := initFnCall_ref_eq rp c ctx rbody calleeRbody body calleeBody f.blockIdx f.stmtIdx
          callerLocals' cache' mem ctrl cm calleeFnTag dst dstTy target calleeAbi pairs none true
          h_bdec h_cbdec h_callee h_abi_ok h_c'_len h_tr h_csupp h_blt_bool h_sa h_nb h_dst_ty
          (by rw [h_ret_ty]; exact h_dst_ret_beq) h_dst_same h_pairs_len h_pairs_match
        dsimp only [ite_true] at h_ifc
        let ⟨err, st', h_ifc_err, h_fk⟩ := h_ifc
        rw [eStateM_bind_err h_ifc_err]
        cases h_asv : allSomeVals pairs with
        | none =>
          rw [h_asv] at h_opt_vs
          rw [h_opt_vs]
          dsimp only
          exact ⟨err, st', rfl, h_fk⟩
        | some _ =>
          rw [h_asv] at h_opt_vs
          rw [h_opt_vs]
          dsimp only
          rw [h_dst_same]
          exact ⟨err, st', rfl, h_fk⟩
      | immediate optDstVal =>
        have h_ifc := initFnCall_ref_eq rp c ctx rbody calleeRbody body calleeBody f.blockIdx f.stmtIdx
          callerLocals' cache' mem ctrl cm calleeFnTag dst dstTy target calleeAbi pairs optDstVal false
          h_bdec h_cbdec h_callee h_abi_ok h_c'_len h_tr h_csupp h_blt_bool h_sa h_nb h_dst_ty
          (by rw [h_ret_ty]; exact h_dst_ret_beq) h_dst_same h_pairs_len h_pairs_match
        dsimp only [ite_false] at h_ifc
        cases h_asv : allSomeVals pairs with
        | none =>
          rw [h_asv] at h_ifc h_opt_vs
          dsimp only at h_ifc
          let ⟨err, st', h_ifc_err, h_fk⟩ := h_ifc
          rw [h_opt_vs, eStateM_bind_err h_ifc_err]
          exact ⟨err, st', rfl, h_fk⟩
        | some argVals =>
          rw [h_asv] at h_ifc h_opt_vs
          dsimp only at h_ifc
          rw [h_ct_c'] at h_ifc
          rw [h_opt_vs]
          dsimp only
          rw [h_dst_same]
          dsimp only
          rw [eStateM_bind_ok h_ifc]
          have h_prog_ok :
              (if target.isSome = true then
                EStateM.bind calls.frameIndex fun __do_lift =>
                  if (__do_lift == ctx.below.size) = true then
                    EStateM.bind calls.getFrame fun __do_lift =>
                      if (__do_lift.location == (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx
                          body.locals f.locals callerCache).location) = true then
                        throw (Miri.Interpreter.StepError.invalidProgram "evaluating this call made no progress")
                      else pure ()
                  else pure ()
              else pure ())
              (mkGenSimState rp
                (SimFrameCtx.call rp.types (ctx.below.push
                    (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' cache'))
                  (some (ctx.below.size + 1)) calleeFnTag ctx.below.size dst.localId dstTy target)
                calleeRbody 0 0 calleeBody.locals (initLocalsLoop calleeBody argVals 0 calleeBody.locals)
                (calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals) mem ctrl cm) =
              .ok () (mkGenSimState rp
                (SimFrameCtx.call rp.types (ctx.below.push
                    (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' cache'))
                  (some (ctx.below.size + 1)) calleeFnTag ctx.below.size dst.localId dstTy target)
                calleeRbody 0 0 calleeBody.locals (initLocalsLoop calleeBody argVals 0 calleeBody.locals)
                (calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals) mem ctrl cm) := by
            cases h_tg : target.isSome with
            | false => rw [ite_false_eq]; rfl
            | true =>
              rw [ite_true_eq]
              dsimp only [bind, Bind.bind, pure, Pure.pure]
              have h_fi1 := callHooks_frameIndex_ok rp
                (SimFrameCtx.call rp.types (ctx.below.push
                    (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' cache'))
                  (some (ctx.below.size + 1)) calleeFnTag ctx.below.size dst.localId dstTy target)
                calleeRbody 0 0 calleeBody.locals (initLocalsLoop calleeBody argVals 0 calleeBody.locals)
                (calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals) mem ctrl cm
              dsimp only [calls]
              rw [eStateM_bind_ok h_fi1]
              have h_sz_ne :
                  ((SimFrameCtx.call rp.types (ctx.below.push
                      (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' cache'))
                    (some (ctx.below.size + 1)) calleeFnTag ctx.below.size dst.localId dstTy target).below.size ==
                    ctx.below.size) = false := by
                dsimp only [SimFrameCtx.call]
                rw [Array.size_push]
                exact beq_false_of_ne (Nat.ne_of_gt (Nat.lt_succ_self _))
              exact congrFun (by rw [h_sz_ne, ite_false_eq] : _ = EStateM.pure ()) _
          rw [h_prog_ok]
          dsimp only
          have h_cf_sz :
              ((mkGenSimState rp
                  (SimFrameCtx.call rp.types (ctx.below.push
                      (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' cache'))
                    (some (ctx.below.size + 1)) calleeFnTag ctx.below.size dst.localId dstTy target)
                  calleeRbody 0 0 calleeBody.locals (initLocalsLoop calleeBody argVals 0 calleeBody.locals)
                  (calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals) mem ctrl cm).stack.frames.size ==
                st.stack.frames.size) = false := by
            dsimp only [st, mkGenSimState, mkRefMiriStackState, SimFrameCtx.call]
            rw [Array.size_push, Array.size_push, Array.size_push]
            exact beq_false_of_ne (Nat.ne_of_gt (Nat.lt_succ_self _))
          rw [show (target.isSome && _ && _) = false from by
            cases h_tg : target.isSome <;> simp [h_cf_sz]]
          rw [ite_false_eq]
          exact ⟨callerLocals', cache', h_c'_eq, h_c'_len, h_inv', h_dst_c',
            dstTy, retTy, initLocalsLoop calleeBody argVals 0 calleeBody.locals, argVals,
            h_dst_ty, h_dst_supp, h_ret_ty, h_dst_ret_beq, rfl, rfl, rfl⟩

private theorem sysrootNumBody_assignTypesValid (op : SysrootNumOp) :
    assignTypesValid (sysrootNumBody op) = true := by
  cases op with | mk k w s =>
  cases k <;> cases w <;> cases s <;> rfl

private theorem callTerminator_sysroot_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (body : Body)
    (rbb : RefBasicBlock) (bb : BasicBlock) (f : FrameState) (callers : List FrameState)
    (callerCache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory) (amem : MemoryState)
    (op : SysrootNumOp) (rargs : List RefOperand) (args : List Operand)
    (rdst : RefPlace) (dst : Place) (target : Option BasicBlockId) (unwind : UnwindAction)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = some rbb)
    (h_rbb_dec : decodeBasicBlock rp.types rbb = some bb)
    (h_rt : rbb.terminator = .sysrootCall op rargs rdst target unwind)
    (h_c_len : callerCache.length = body.locals.length)
    (h_tr : refTopRelevanceValid (ctx.below.size + 1) ctx.topRel?)
    (h_loc : ctx.locOverride = none)
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_cta : callTargetAdmitted body bb (sysrootNumBody op) args dst target unwind = true)
    (h_dargs : mapOption (decodeOperand rp.types) rargs = some args)
    (h_ddst : decodePlace rp.types rdst = some dst) :
    let st := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals callerCache mem ctrl cm
    let miriTerm := toMiriTerminator rp.types rbb.terminator
    let res := (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).terminator c miriTerm st
    match evalCallTerminator body bb f callers amem cm 0 (some op) (sysrootNumBody op) args dst target unwind with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = some k
    | .done _ => False
    | .step s' =>
      ∃ callerLocals' callerCache',
        callerCache' = callCacheTouch dst.localId args callerCache ∧
        callerCache'.length = body.locals.length ∧
        SlotsMatchTys body.locals callerLocals' ∧
        MirSemantics.getElem? callerCache' dst.localId = some true ∧
        (∃ dstTy retTy calleeLocals argVals,
          MirSemantics.getElem? body.locals dst.localId = some dstTy ∧
          isSupportedScalarOrUnitTy dstTy = true ∧
          MirSemantics.getElem? (sysrootNumBody op).locals 0 = some retTy ∧
          dstTy.beq retTy = true ∧
          calleeLocals = initLocalsLoop (sysrootNumBody op) argVals 0 (sysrootNumBody op).locals ∧
          s' = {
            frames := {
              defId := 0
              blockIdx := 0
              stmtIdx := 0
              locals := calleeLocals
              sysrootOp? := some op
              retDst? := some dst
              retTarget? := target
            } :: { f with locals := callerLocals' } :: callers
            callerMem := cm
            mem := amem
          } ∧
          let oldFr := mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'
          let calleeCtx := SimFrameCtx.call rp.types (ctx.below.push oldFr) (some (ctx.below.size + 1))
            (fnTagForSysroot op) ctx.below.size dst.localId dstTy target
          let calleeCache := calleeInitCacheLoop (sysrootNumBody op).argumentCount 0 (sysrootNumBody op).locals
          res = (mkGenSimState rp calleeCtx (sysrootNumRefBody rp.types op) 0 0 (sysrootNumBody op).locals
            calleeLocals calleeCache mem ctrl cm, .ok ())) := by
  intro st miriTerm res
  have h_dst_ty_int : ∃ dstTy,
      MirSemantics.getElem? body.locals dst.localId = some dstTy ∧
      dstTy.beq (.int op.width op.signed) = true := by
    have h_cta' := h_cta
    dsimp only [callTargetAdmitted] at h_cta'
    simp only [Bool.and_eq_true] at h_cta'
    have h_pair := h_cta'.1.2
    cases h_dl : MirSemantics.getElem? body.locals dst.localId with
    | none => rw [h_dl] at h_pair; cases h_pair
    | some dTy =>
      rw [h_dl] at h_pair
      have h_rl : MirSemantics.getElem? (sysrootNumBody op).locals 0 = some (.int op.width op.signed) := rfl
      rw [h_rl, Bool.and_eq_true] at h_pair
      exact ⟨dTy, rfl, h_pair.2⟩
  let ⟨dstTy, h_dst_ty, h_dreq⟩ := h_dst_ty_int
  have h_dst_eq : dstTy = .int op.width op.signed := MirTy.eq_of_beq h_dreq
  rw [h_dst_eq] at h_dst_ty
  let ⟨_, _, h_in⟩ := decodeBody_local_mem_types h_bdec h_dst_ty
  have h_cbdec : decodeBody rp.types (sysrootNumRefBody rp.types op) = some (sysrootNumBody op) :=
    decodeBody_sysrootNumRefBody rp op h_in
  have h_callee_res : refResolveCalleeBody rp (fnTagForSysroot op) =
      some (sysrootNumRefBody rp.types op, (sysrootNumBody op).locals) := by
    dsimp only [refResolveCalleeBody, fnTagForSysroot]
    have h_mod : (2 * sysrootNumOpCode op + 1).mod 2 = 1 := by
      change HMod.hMod (2 * sysrootNumOpCode op + 1) 2 = 1
      rw [Nat.mul_add_mod]
    have h_div : (2 * sysrootNumOpCode op + 1).div 2 = sysrootNumOpCode op := by
      change HDiv.hDiv (2 * sysrootNumOpCode op + 1) 2 = sysrootNumOpCode op
      rw [Nat.mul_add_div (by decide : 0 < 2)]
      exact Nat.add_zero _
    rw [h_mod, h_div, show ((1 == 0) = false) from rfl, ite_false_eq, sysrootNumOpOfCode_eq]
    rfl
  have h_comm := callTerminator_common_ref_eq rp c ctx rbody (sysrootNumRefBody rp.types op)
    body (sysrootNumBody op) rbb bb f callers callerCache mem ctrl cm amem 0 (fnTagForSysroot op) (some op)
    rargs args rdst dst target unwind h_bdec h_rbb h_rbb_dec h_c_len h_tr h_loc h_inv
    h_callee_res h_cbdec h_dargs h_ddst h_cta
    rfl rfl rfl rfl (sysrootNumBody_assignTypesValid op) (by cases op.kind <;> rfl)
  dsimp only [res, miriTerm]
  rw [h_rt]
  exact h_comm

private theorem callTerminator_crate_ref_eq (rp : RefProg) (p : Program) (c : Choice)
    (ctx : SimFrameCtx) (rbody calleeRbody : RefBody) (body calleeBody : Body)
    (rbb : RefBasicBlock) (bb : BasicBlock) (f : FrameState) (callers : List FrameState)
    (callerCache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory) (amem : MemoryState)
    (calleeDefId : DefId) (rargs : List RefOperand) (args : List Operand)
    (rdst : RefPlace) (dst : Place) (target : Option BasicBlockId) (unwind : UnwindAction)
    (_h_pdec : decodeProg rp = some p)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = some rbb)
    (h_rbb_dec : decodeBasicBlock rp.types rbb = some bb)
    (h_rt : rbb.terminator = .call calleeDefId rargs rdst target unwind)
    (h_c_len : callerCache.length = body.locals.length)
    (h_tr : refTopRelevanceValid (ctx.below.size + 1) ctx.topRel?)
    (h_loc : ctx.locOverride = none)
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_rcbody : MirSemantics.getElem? rp.bodies calleeDefId = some calleeRbody)
    (h_cbdec : decodeBody rp.types calleeRbody = some calleeBody)
    (h_cta : callTargetAdmitted body bb calleeBody args dst target unwind = true)
    (h_dargs : mapOption (decodeOperand rp.types) rargs = some args)
    (h_ddst : decodePlace rp.types rdst = some dst)
    (h_csat : callBodyStaticAdmitted p calleeBody = true) :
    let st := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals callerCache mem ctrl cm
    let miriTerm := toMiriTerminator rp.types rbb.terminator
    let res := (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).terminator c miriTerm st
    match evalCallTerminator body bb f callers amem cm calleeDefId none calleeBody args dst target unwind with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = some k
    | .done _ => False
    | .step s' =>
      ∃ callerLocals' callerCache',
        callerCache' = callCacheTouch dst.localId args callerCache ∧
        callerCache'.length = body.locals.length ∧
        SlotsMatchTys body.locals callerLocals' ∧
        MirSemantics.getElem? callerCache' dst.localId = some true ∧
        (∃ dstTy retTy calleeLocals argVals,
          MirSemantics.getElem? body.locals dst.localId = some dstTy ∧
          isSupportedScalarOrUnitTy dstTy = true ∧
          MirSemantics.getElem? calleeBody.locals 0 = some retTy ∧
          dstTy.beq retTy = true ∧
          calleeLocals = initLocalsLoop calleeBody argVals 0 calleeBody.locals ∧
          s' = {
            frames := {
              defId := calleeDefId
              blockIdx := 0
              stmtIdx := 0
              locals := calleeLocals
              sysrootOp? := none
              retDst? := some dst
              retTarget? := target
            } :: { f with locals := callerLocals' } :: callers
            callerMem := cm
            mem := amem
          } ∧
          let oldFr := mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'
          let calleeCtx := SimFrameCtx.call rp.types (ctx.below.push oldFr) (some (ctx.below.size + 1))
            (fnTagForCrate calleeDefId) ctx.below.size dst.localId dstTy target
          let calleeCache := calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals
          res = (mkGenSimState rp calleeCtx calleeRbody 0 0 calleeBody.locals
            calleeLocals calleeCache mem ctrl cm, .ok ())) := by
  intro st miriTerm res
  have h_clocs : decodeLocalTys rp.types calleeRbody.locals = some calleeBody.locals := by
    dsimp only [decodeBody] at h_cbdec
    cases h_l : decodeLocalTys rp.types calleeRbody.locals with
    | none => rw [h_l] at h_cbdec; cases h_cbdec
    | some ls =>
      rw [h_l] at h_cbdec
      cases h_b : mapOption (decodeBasicBlock rp.types) calleeRbody.basicBlocks with
      | none => rw [h_b] at h_cbdec; cases h_cbdec
      | some bs => rw [h_b] at h_cbdec; injection h_cbdec with hb; subst hb; rfl
  have h_callee_res : refResolveCalleeBody rp (fnTagForCrate calleeDefId) =
      some (calleeRbody, calleeBody.locals) := by
    dsimp only [refResolveCalleeBody, fnTagForCrate]
    have h_mod : (2 * calleeDefId).mod 2 = 0 := by
      change HMod.hMod (2 * calleeDefId) 2 = 0
      rw [Nat.mul_comm]; exact Nat.mul_mod_left calleeDefId 2
    have h_div : (2 * calleeDefId).div 2 = calleeDefId := by
      change HDiv.hDiv (2 * calleeDefId) 2 = calleeDefId
      exact Nat.mul_div_right calleeDefId (by decide)
    rw [h_mod, h_div, show ((0 == 0) = true) from rfl, ite_true_eq, h_rcbody]
    dsimp only
    rw [h_clocs]
  dsimp only [callBodyStaticAdmitted, singleBodyStaticAdmitted] at h_csat
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h_csat
  let ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h_nb⟩, _⟩, h_sa⟩, h_dv⟩, h_cv⟩, _⟩, h_csupp⟩, _⟩, h_av⟩ :=
    h_csat
  have h_comm := callTerminator_common_ref_eq rp c ctx rbody calleeRbody body calleeBody rbb bb f callers
    callerCache mem ctrl cm amem calleeDefId (fnTagForCrate calleeDefId) none
    rargs args rdst dst target unwind h_bdec h_rbb h_rbb_dec h_c_len h_tr h_loc h_inv
    h_callee_res h_cbdec h_dargs h_ddst h_cta h_nb h_sa h_dv h_cv h_av h_csupp
  dsimp only [res, miriTerm]
  rw [h_rt]
  exact h_comm

private theorem array_eq_singleton_of_toList_reverse {α : Type} {xs : Array α} {x : α}
    (h : xs.toList.reverse = [x]) : xs = Array.mk [x] := by
  cases xs with
  | mk l =>
    dsimp only at h
    have h_rev := congrArg List.reverse h
    rw [List.reverse_reverse] at h_rev
    exact congrArg Array.mk h_rev

private theorem array_eq_push_of_toList_reverse {α : Type} {xs : Array α}
    {top : α} {rest : List α}
    (h : xs.toList.reverse = top :: rest) :
    xs = (⟨rest.reverse⟩ : Array α).push top := by
  cases xs with
  | mk l =>
    dsimp only at h
    have h_rev := congrArg List.reverse h
    rw [List.reverse_reverse, List.reverse_cons] at h_rev
    dsimp only [Array.push]
    rw [List.concat_eq_append]
    exact congrArg Array.mk h_rev

private theorem frameSimInv_root_eq_mkGenSimState (rp : RefProg) (_p : Program)
    (f : FrameState) (body : Body) (rbody : RefBody)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (cache : List Bool) (topRel? : Option Nat)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (rframes : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (rf : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (h_rev : rframes.toList.reverse = [rf])
    (h_rf : rf = mkRefMiriFrame rp.types f.defId rbody f.blockIdx f.stmtIdx
      (liftLocalsCached rp.types body.locals f.locals cache) retPlace) :
    let ctx : SimFrameCtx := { SimFrameCtx.root f.defId retPlace with topRel? := topRel? }
    mkRefMiriStackState rframes topRel? mem ctrl cm =
      mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache mem ctrl cm := by
  rw [array_eq_singleton_of_toList_reverse h_rev, h_rf]
  rfl

private theorem callFrameSimInv_push_eq_mkGenSimState (rp : RefProg) (_p : Program)
    (f : FrameState) (body : Body) (rbody : RefBody)
    (cache : List Bool) (fnTag callerIdx : Nat) (dstLocalId : LocalId) (dstTy : MirTy)
    (retTarget? : Option BasicBlockId) (topRel? : Option Nat)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory)
    (rframes : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (rcallee : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (rrestFrames : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (h_rev : rframes.toList.reverse = rcallee :: rrestFrames)
    (h_rf : rcallee = mkRefMiriCallFrame rp.types fnTag rbody f.blockIdx f.stmtIdx
      (liftLocalsCached rp.types body.locals f.locals cache) callerIdx dstLocalId dstTy retTarget?) :
    let ctx : SimFrameCtx := SimFrameCtx.call rp.types ⟨rrestFrames.reverse⟩ topRel? fnTag
      callerIdx dstLocalId dstTy retTarget?
    mkRefMiriStackState rframes topRel? mem ctrl cm =
      mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache mem ctrl cm := by
  rw [array_eq_push_of_toList_reverse h_rev, h_rf]
  rfl

private theorem framesSimInv_length_eq {rp : RefProg} {p : Program}
    {retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {fs : List FrameState}
    {rfs : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    (h : FramesSimInv rp p retPlace fs rfs) : rfs.length = fs.length := by
  induction h with
  | root => rfl
  | push _ _ _ _ _ _ _ _ _ _ _ _ ih => simp [ih]

private theorem activeThread?_mkRefMiriStackState
    (frames : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (topRel? : Option Nat)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory) :
    (match (mkRefMiriStackState frames topRel? mem ctrl cm).machine.threads.activeThread? with
     | some th => th.topUserRelevantFrame
     | none => none) = topRel? := rfl

private theorem mkRefMiriStackState_activeThread?
    (frames : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (topRel? : Option Nat)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) (cm : CallerMemory) :
    ∃ th,
      (mkRefMiriStackState frames topRel? mem ctrl cm).machine.threads.activeThread? = some th ∧
      th.topUserRelevantFrame = topRel? :=
  ⟨_, rfl, rfl⟩

private theorem attachCallers_nil (r : Trusted.MirSemantics.StepResult State TerminalOut) :
    attachCallers [] r = r := rfl

private theorem updateCacheLoop_stepTouchesLocal_stmt (body : Body) (f : FrameState)
    (bb : BasicBlock) (stmt : StatementKind)
    (h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (h_st : MirSemantics.getElem? bb.statements f.stmtIdx = some stmt)
    (cache : List Bool) :
    updateCacheLoop (stepTouchesLocal body f) 0 cache = stmtCacheTouch stmt cache := by
  cases stmt with
  | nop | storageLive _ | storageDead _ | unsupported =>
    have h_fn : stepTouchesLocal body f = fun _ => false := by
      funext idx; dsimp only [stepTouchesLocal]; rw [h_bb]; dsimp only; rw [h_st]
    rw [h_fn]; exact updateCacheLoop_false _ 0 cache (fun _ _ => rfl)
  | assign dst rv =>
    have h_fn : stepTouchesLocal body f =
        fun idx => Nat.beq dst.localId idx || rvalueTouchesLocal rv idx := by
      funext idx; dsimp only [stepTouchesLocal]; rw [h_bb]; dsimp only; rw [h_st]
    rw [h_fn]; exact updateCacheLoop_rvalueCacheTouch dst.localId rv cache

private theorem updateCacheLoop_stepTouchesLocal_term (body : Body) (f : FrameState)
    (bb : BasicBlock)
    (h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (h_st : MirSemantics.getElem? bb.statements f.stmtIdx = none)
    (h_len : Nat.beq f.stmtIdx bb.statements.length = true)
    (cache : List Bool) :
    updateCacheLoop (stepTouchesLocal body f) 0 cache = termCacheTouch bb.terminator cache := by
  have h_fn_gen :
      stepTouchesLocal body f =
        match bb.terminator with
        | .switchInt discr _ => operandTouchesLocal discr
        | .assert cond _ _ _ _ => operandTouchesLocal cond
        | _ => fun _ => false := by
    funext idx
    dsimp only [stepTouchesLocal]
    rw [h_bb]; dsimp only; rw [h_st]; dsimp only; rw [h_len, ite_true_eq]
    cases bb.terminator <;> rfl
  rw [h_fn_gen]
  cases h_t : bb.terminator with
  | switchInt discr _ => exact updateCacheLoop_operandCacheTouch cache discr
  | assert cond _ _ _ _ => exact updateCacheLoop_operandCacheTouch cache cond
  | goto _ | return_ | unreachable | unwindResume
  | call _ _ _ _ _ | sysrootCall _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported =>
    exact updateCacheLoop_false _ 0 cache (fun _ _ => rfl)

private theorem calleeTys_head_eq_of_beq {tys : List MirTy} {retTy dstTy : MirTy}
    (h_get : MirSemantics.getElem? tys 0 = some retTy)
    (h_beq : dstTy.beq retTy = true) :
    tys[0]?.getD .unit = dstTy := by
  cases tys with
  | nil => cases h_get
  | cons hd _ =>
    injection h_get with h_hd
    subst h_hd
    exact (MirTy.eq_of_beq h_beq).symm

private theorem decodeTerminator_call_inv {types : List MirTy}
    {callee : DefId} {rargs : List RefOperand} {rdst : RefPlace}
    {tgt : Option BasicBlockId} {unwind : UnwindAction} {t : TerminatorKind}
    (h : decodeTerminator types (.call callee rargs rdst tgt unwind) = some t) :
    ∃ args dst,
      mapOption (decodeOperand types) rargs = some args ∧
      decodePlace types rdst = some dst ∧
      t = .call callee args dst tgt unwind := by
  dsimp only [decodeTerminator, optMap2] at h
  cases h_a : mapOption (decodeOperand types) rargs with
  | none => rw [h_a] at h; cases h
  | some args =>
    rw [h_a] at h
    cases h_d : decodePlace types rdst with
    | none => rw [h_d] at h; cases h
    | some dst =>
      rw [h_d] at h
      injection h with h_eq
      exact ⟨args, dst, rfl, rfl, h_eq.symm⟩

private theorem decodeTerminator_sysrootCall_inv {types : List MirTy}
    {op : SysrootNumOp} {rargs : List RefOperand} {rdst : RefPlace}
    {tgt : Option BasicBlockId} {unwind : UnwindAction} {t : TerminatorKind}
    (h : decodeTerminator types (.sysrootCall op rargs rdst tgt unwind) = some t) :
    ∃ args dst,
      mapOption (decodeOperand types) rargs = some args ∧
      decodePlace types rdst = some dst ∧
      t = .sysrootCall op args dst tgt unwind := by
  dsimp only [decodeTerminator, optMap2] at h
  cases h_a : mapOption (decodeOperand types) rargs with
  | none => rw [h_a] at h; cases h
  | some args =>
    rw [h_a] at h
    cases h_d : decodePlace types rdst with
    | none => rw [h_d] at h; cases h
    | some dst =>
      rw [h_d] at h
      injection h with h_eq
      exact ⟨args, dst, rfl, rfl, h_eq.symm⟩

private theorem decodeBody_argumentCount {types : List MirTy} {rbody : RefBody} {body : Body}
    (h : decodeBody types rbody = some body) :
    rbody.argumentCount = body.argumentCount :=
  (decodeBody_inv h).1

private theorem decodeBody_locals {types : List MirTy} {rbody : RefBody} {body : Body}
    (h : decodeBody types rbody = some body) :
    decodeLocalTys types rbody.locals = some body.locals :=
  (decodeBody_inv h).2.1

private theorem updateCacheLoop_callTouchesCallerLocal (body : Body) (f : FrameState)
    (bb : BasicBlock) (args : List Operand) (dst : Place) (cache : List Bool)
    (h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (h_t : (∃ callee tgt uw, bb.terminator = .call callee args dst tgt uw) ∨
      (∃ op tgt uw, bb.terminator = .sysrootCall op args dst tgt uw)) :
    updateCacheLoop (callTouchesCallerLocal body f) 0 cache =
      callCacheTouch dst.localId args cache := by
  have h_fn : callTouchesCallerLocal body f =
      fun idx => Nat.beq dst.localId idx || args.any fun a => operandTouchesLocal a idx := by
    funext idx
    dsimp only [callTouchesCallerLocal]
    rw [h_bb]; dsimp only
    cases h_t with
    | inl h1 => let ⟨_, _, _, h_bt⟩ := h1; rw [h_bt]
    | inr h2 => let ⟨_, _, _, h_bt⟩ := h2; rw [h_bt]
  rw [h_fn]
  exact updateCacheLoop_callCacheTouch dst.localId args cache

private theorem decodeTerminator_ne_call {types : List MirTy}
    {rt : RefTerminatorKind} {t : TerminatorKind}
    (h_nc : (∀ c a d g u, rt ≠ .call c a d g u) ∧ (∀ o a d g u, rt ≠ .sysrootCall o a d g u))
    (h_dec : decodeTerminator types rt = some t) :
    (∀ c a d g u, t ≠ .call c a d g u) ∧ (∀ o a d g u, t ≠ .sysrootCall o a d g u) := by
  cases rt with
  | call c a d g u => exact False.elim (h_nc.1 c a d g u rfl)
  | sysrootCall o a d g u => exact False.elim (h_nc.2 o a d g u rfl)
  | switchInt discr _ =>
    dsimp only [decodeTerminator, optMap] at h_dec
    cases h_op : decodeOperand types discr with
    | none => rw [h_op] at h_dec; cases h_dec
    | some _ =>
    rw [h_op] at h_dec; cases h_dec
    constructor <;> (intro _ _ _ _ _ h; cases h)
  | assert cond _ _ _ _ =>
    dsimp only [decodeTerminator, optMap] at h_dec
    cases h_op : decodeOperand types cond with
    | none => rw [h_op] at h_dec; cases h_dec
    | some _ =>
      rw [h_op] at h_dec; cases h_dec
      constructor <;> (intro _ _ _ _ _ h; cases h)
  | goto _ | return_ | unreachable | unwindResume | unsupported =>
    dsimp only [decodeTerminator] at h_dec
    cases h_dec
    constructor <;> (intro _ _ _ _ _ h; cases h)
  | coreCall _ rargs rdst _ _ =>
    dsimp only [decodeTerminator, optMap2] at h_dec
    cases h_a : mapOption (decodeOperand types) rargs with
    | none => rw [h_a] at h_dec; cases h_dec
    | some _ =>
      rw [h_a] at h_dec
      cases h_d : decodePlace types rdst with
      | none => rw [h_d] at h_dec; cases h_dec
      | some _ =>
        rw [h_d] at h_dec; cases h_dec
        constructor <;> (intro _ _ _ _ _ h; cases h)

private theorem array_back?_push {α : Type} (arr : Array α) (x : α) :
    (arr.push x).back? = some x := by
  simp [Array.back?]

private theorem array_reverse_cons_push {α : Type} (hd : α) (tl : List α) :
    (⟨(hd :: tl).reverse⟩ : Array α) = (⟨tl.reverse⟩ : Array α).push hd := by
  simp [Array.push, List.reverse_cons, List.concat_eq_append]

private theorem getElem?_liftLocalsCached_layout_isSome (types : List MirTy) :
    ∀ (tys : List MirTy) (slots : List LocalSlot) (cache : List Bool) (id : Nat)
      {ls : Miri.Interpreter.LocalState Miri.Memory.Provenance Miri.Interpreter.LocalLayout},
      tys.length = slots.length →
      slots.length = cache.length →
      MirSemantics.getElem? (liftLocalsCached types tys slots cache) id = some ls →
      ls.layout.isSome = true →
      MirSemantics.getElem? cache id = some true
  | [], _, _, _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, h1, _, _, _ => by cases h1
  | _ :: _, _ :: _, [], _, _, _, h2, _, _ => by cases h2
  | ty :: tys, slot :: slots, b :: bs, 0, ls, _, _, h_get, h_is => by
    dsimp only [liftLocalsCached, MirSemantics.getElem?] at h_get
    injection h_get with h_eq
    subst h_eq
    cases b with
    | true => rfl
    | false => dsimp only [refLocalStateOfSlotWithCache] at h_is; cases h_is
  | ty :: tys, slot :: slots, b :: bs, i + 1, ls, h1, h2, h_get, h_is =>
    getElem?_liftLocalsCached_layout_isSome types tys slots bs i
      (Nat.succ.inj h1) (Nat.succ.inj h2) h_get h_is

private theorem getElem?_replicate_true :
    ∀ {xs : List α} {i : Nat} {x : α},
      MirSemantics.getElem? xs i = some x →
      MirSemantics.getElem? (List.replicate xs.length true) i = some true
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, i + 1, _, h => getElem?_replicate_true (xs := xs) h

private theorem decodeTerminator_ne_return {types : List MirTy}
    {rt : RefTerminatorKind} {t : TerminatorKind}
    (h_nr : rt ≠ .return_)
    (h_dec : decodeTerminator types rt = some t) :
    t ≠ .return_ := by
  cases rt with
  | return_ => exact False.elim (h_nr rfl)
  | goto _ | unreachable | unwindResume | unsupported =>
    dsimp only [decodeTerminator] at h_dec
    cases h_dec
    intro h_eq; cases h_eq
  | switchInt discr _ =>
    dsimp only [decodeTerminator, optMap] at h_dec
    cases h_op : decodeOperand types discr with
    | none => rw [h_op] at h_dec; cases h_dec
    | some _ => rw [h_op] at h_dec; cases h_dec; intro h_eq; cases h_eq
  | assert cond _ _ _ _ =>
    dsimp only [decodeTerminator, optMap] at h_dec
    cases h_op : decodeOperand types cond with
    | none => rw [h_op] at h_dec; cases h_dec
    | some _ => rw [h_op] at h_dec; cases h_dec; intro h_eq; cases h_eq
  | call _ rargs rdst _ _ | sysrootCall _ rargs rdst _ _
  | coreCall _ rargs rdst _ _ =>
    dsimp only [decodeTerminator, optMap2] at h_dec
    cases h_a : mapOption (decodeOperand types) rargs with
    | none => rw [h_a] at h_dec; cases h_dec
    | some _ =>
      rw [h_a] at h_dec
      cases h_d : decodePlace types rdst with
      | none => rw [h_d] at h_dec; cases h_dec
      | some _ => rw [h_d] at h_dec; cases h_dec; intro h_eq; cases h_eq

private theorem array_set_push_last {α : Type} (arr : Array α) (x y : α)
    (h : (arr.push x).size - 1 < (arr.push x).size) :
    (arr.push x).set ((arr.push x).size - 1) y h = arr.push y := by
  apply Array.toList_inj.mp
  simp [Array.push, List.concat_eq_append]

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases h_b : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true h_b))

private theorem nat_beq_comm (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  cases h : Nat.beq a b with
  | true =>
    have h_eq : a = b := Nat.eq_of_beq_eq_true h
    rw [h_eq]; exact (Nat.beq_refl _).symm
  | false =>
    cases h2 : Nat.beq b a with
    | false => rfl
    | true =>
      have h_eq : b = a := Nat.eq_of_beq_eq_true h2
      rw [h_eq, Nat.beq_refl] at h; cases h

private theorem evalAssertFailure_done_aborted {msg : AssertKind}
    {ps : PanicStrategy} {uw : UnwindAction} {cm : CallerMemory} {lh : Bool}
    {out : TerminalOut}
    (h : evalAssertFailure msg ps uw cm lh = .done out) : out = .aborted cm := by
  dsimp only [evalAssertFailure] at h
  cases msg with
  | misalignedPtrDeref | nullPtrDeref | unsupported | overflowNeg => cases h
  | boundsCheck | divByZero | remByZero =>
    cases lh <;> cases ps <;> cases uw <;>
      first
      | (injection h with h_eq; exact h_eq.symm)
      | cases h
  | overflow op =>
    cases op <;>
      first
      | cases h
      | (cases lh <;> cases ps <;> cases uw <;>
          first
          | (injection h with h_eq; exact h_eq.symm)
          | cases h)

/-- A non-`return` terminator finishes (`.done`) only by a `--panic abort`
`.assert` failure, carrying the unchanged `CallerMemory`. -/
private theorem evalTerminator_done_aborted_of_ne_return {body : Body}
    {bb : BasicBlock} {f : FrameState} {mem : MemoryState} {cm : CallerMemory}
    {ps : PanicStrategy} {lh : Bool} {out : TerminalOut}
    (h_nr : bb.terminator ≠ .return_)
    (h_ev : evalTerminator body bb f mem cm ps lh = .done out) :
    out = .aborted cm := by
  cases h_t : bb.terminator with
  | return_ => exact False.elim (h_nr h_t)
  | goto _ | unreachable | unwindResume
  | call _ _ _ _ _ | sysrootCall _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported =>
    dsimp only [evalTerminator] at h_ev
    rw [h_t] at h_ev
    cases h_ev
  | assert cond expected msg target uw =>
    dsimp only [evalTerminator] at h_ev
    rw [h_t] at h_ev
    dsimp only at h_ev
    cases h_op : evalPrimitiveOperand body.locals f.locals mem cond with
    | error k => rw [h_op] at h_ev; cases h_ev
    | ok tr =>
      rw [h_op] at h_ev
      dsimp only at h_ev
      cases h_v : tr.1 with
      | bool b =>
        rw [h_v] at h_ev
        dsimp only at h_ev
        cases h_b : (b == expected) with
        | true => rw [h_b] at h_ev; cases h_ev
        | false =>
          rw [h_b] at h_ev
          exact evalAssertFailure_done_aborted h_ev
      | scalar _ | char _ | unit | enumVal _ _ | tuple _ | ptr _ | slicePtr _ _
      | rangeTo _ | rangeFrom _ | bytes _ | array _ | ordering _ | optionVal _ | range _ _
      | boxPtr _ _ | vec _ _ _ =>
        rw [h_v] at h_ev; dsimp only at h_ev; cases h_ev
  | switchInt discr targets =>
    dsimp only [evalTerminator] at h_ev
    rw [h_t] at h_ev
    dsimp only at h_ev
    cases h_op : evalPrimitiveOperand body.locals f.locals mem discr with
    | error k => rw [h_op] at h_ev; cases h_ev
    | ok tr =>
      rw [h_op] at h_ev
      dsimp only at h_ev
      cases h_v : tr.1 with
      | scalar sv =>
        rw [h_v] at h_ev; dsimp only at h_ev
        cases h_b : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;> rw [h_b] at h_ev <;> cases h_ev
      | bool b =>
        rw [h_v] at h_ev; dsimp only at h_ev
        cases h_b : evalBoolSwitchBranches b targets.otherwise targets.branches <;> rw [h_b] at h_ev <;> cases h_ev
      | char ch =>
        rw [h_v] at h_ev; dsimp only at h_ev
        cases h_b : evalCharSwitchBranches ch targets.otherwise targets.branches <;> rw [h_b] at h_ev <;> cases h_ev
      | ptr _ | optionVal _ | range _ _ | boxPtr _ _ | vec _ _ _ => rw [h_v] at h_ev; dsimp only at h_ev; cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;> dsimp only at h_ev <;> cases h_ev
      | ordering _ => rw [h_v] at h_ev; dsimp only at h_ev; cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;> dsimp only at h_ev <;> cases h_ev
      | unit => rw [h_v] at h_ev; dsimp only at h_ev; cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;> dsimp only at h_ev <;> cases h_ev
      | enumVal _ _ => rw [h_v] at h_ev; dsimp only at h_ev; cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;> dsimp only at h_ev <;> cases h_ev
      | tuple _ => rw [h_v] at h_ev; dsimp only at h_ev; cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;> dsimp only at h_ev <;> cases h_ev
      | bytes _ => rw [h_v] at h_ev; dsimp only at h_ev; cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;> dsimp only at h_ev <;> cases h_ev
      | slicePtr _ _ => rw [h_v] at h_ev; dsimp only at h_ev; cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;> dsimp only at h_ev <;> cases h_ev
      | rangeTo _ => rw [h_v] at h_ev; dsimp only at h_ev; cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;> dsimp only at h_ev <;> cases h_ev
      | rangeFrom _ => rw [h_v] at h_ev; dsimp only at h_ev; cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;> dsimp only at h_ev <;> cases h_ev
      | array _ =>
        rw [h_v] at h_ev; dsimp only at h_ev
        cases h_brs : targets.branches <;> rw [h_brs] at h_ev <;>
          dsimp only at h_ev <;> cases h_ev

private theorem array_push_size_sub_one {α : Type} (arr : Array α) (x : α) :
    (arr.push x).size - 1 = arr.size := by
  rw [Array.size_push]
  exact Nat.add_sub_cancel _ _

private theorem evalNonRootReturn_step_inv {p : Program} {body callerBody : Body}
    {bb : BasicBlock} {f caller : FrameState} {rest : List FrameState}
    {mem : MemoryState} {cm : CallerMemory} {tgt : BasicBlockId}
    {callerLocals' : List LocalSlot} {mem' : MemoryState}
    (h_cb : activeFrameBody p caller = some callerBody)
    (h_cinv : SlotsMatchTys callerBody.locals caller.locals)
    (h_ev : evalNonRootReturn p body bb f caller rest mem cm =
      .step { frames := { caller with blockIdx := tgt, stmtIdx := 0, locals := callerLocals' } :: rest,
              callerMem := cm, mem := mem' }) :
    SlotsMatchTys callerBody.locals callerLocals' := by
  dsimp only [evalNonRootReturn] at h_ev
  cases h_cl : (bb.cleanup || localsHaveIndirect f.locals) with
  | true => rw [h_cl, ite_true_eq] at h_ev; cases h_ev
  | false =>
    rw [h_cl, ite_false_eq] at h_ev
    have h_next :
        ∀ retVal : Val,
          (show Trusted.MirSemantics.StepResult State TerminalOut from
            match f.retDst? with
            | none => Trusted.MirSemantics.StepResult.fault FaultKind.unsupported
            | some dst =>
              if !dst.projection.isEmpty then Trusted.MirSemantics.StepResult.fault FaultKind.unsupported
              else
                match activeFrameBody p caller with
                | none => Trusted.MirSemantics.StepResult.fault FaultKind.unsupported
                | some cBody =>
                  match MirSemantics.getElem? cBody.locals dst.localId with
                  | none => Trusted.MirSemantics.StepResult.fault FaultKind.unsupported
                  | some dstTy =>
                    match writePlace caller.locals mem dst.localId dstTy retVal with
                    | Except.error k => Trusted.MirSemantics.StepResult.fault k
                    | Except.ok (cLocals', amem') =>
                      match f.retTarget? with
                      | none => Trusted.MirSemantics.StepResult.fault FaultKind.undefined
                      | some tgt' =>
                        Trusted.MirSemantics.StepResult.step
                          { frames := { caller with blockIdx := tgt', stmtIdx := 0, locals := cLocals' } :: rest,
                            callerMem := cm, mem := amem' }) =
            .step { frames := { caller with blockIdx := tgt, stmtIdx := 0, locals := callerLocals' } :: rest,
                    callerMem := cm, mem := mem' } →
          SlotsMatchTys callerBody.locals callerLocals' := by
      intro retVal h_step
      cases h_rd : f.retDst? with
      | none => rw [h_rd] at h_step; cases h_step
      | some dst =>
        rw [h_rd] at h_step
        dsimp only at h_step
        cases h_pe : dst.projection.isEmpty with
        | false => rw [h_pe] at h_step; cases h_step
        | true =>
          rw [h_pe] at h_step
          dsimp only [Bool.not, ite_false_eq] at h_step
          rw [h_cb] at h_step
          dsimp only at h_step
          cases h_dty : MirSemantics.getElem? callerBody.locals dst.localId with
          | none => rw [h_dty] at h_step; cases h_step
          | some dstTy =>
            rw [h_dty] at h_step
            dsimp only at h_step
            cases h_wp : writePlace caller.locals mem dst.localId dstTy retVal with
            | error k => rw [h_wp] at h_step; cases h_step
            | ok pair =>
              cases pair with
              | mk cLocals' amem' =>
                rw [h_wp] at h_step
                dsimp only at h_step
                cases h_rt : f.retTarget? with
                | none => rw [h_rt] at h_step; cases h_step
                | some tgt' =>
                  rw [h_rt] at h_step
                  injection h_step with h_st_eq
                  have h_fr_eq : { caller with blockIdx := tgt', stmtIdx := 0, locals := cLocals' } =
                      { caller with blockIdx := tgt, stmtIdx := 0, locals := callerLocals' } := by
                    injection h_st_eq with h_fs
                    exact (List.cons.inj h_fs).1
                  have h_loc_eq : cLocals' = callerLocals' := congrArg FrameState.locals h_fr_eq
                  rw [← h_loc_eq]
                  exact (writePlace_slotsMatchTys h_cinv h_dty h_wp).1
    cases h_sl0 : MirSemantics.getElem? f.locals 0 with
    | none => rw [h_sl0] at h_ev; cases h_ev
    | some sl =>
      rw [h_sl0] at h_ev
      cases sl with
      | dead => cases h_ev
      | partialTuple _ => cases h_ev
      | immediate o =>
        cases o with
        | none => cases h_ev
        | some v => exact h_next v h_ev
      | indirect mp =>
        dsimp only at h_ev
        cases h_rty : MirSemantics.getElem? body.locals 0 with
        | none => rw [h_rty] at h_ev; cases h_ev
        | some rTy =>
          rw [h_rty] at h_ev
          dsimp only at h_ev
          cases h_ld : loadIndirect mem rTy mp with
          | error k => rw [h_ld] at h_ev; cases h_ev
          | ok ov =>
            rw [h_ld] at h_ev
            cases ov with
            | none => cases h_ev
            | some v => exact h_next v h_ev

private theorem updateMiriLocalsLoop_nonRootReturn (types : List MirTy)
    (callerBody : Body) (callerLocals callerLocals' : List LocalSlot)
    (callerCache : List Bool) (dstId : LocalId)
    (h_inv : SlotsMatchTys callerBody.locals callerLocals)
    (h_inv' : SlotsMatchTys callerBody.locals callerLocals')
    (h_c_len : callerCache.length = callerBody.locals.length)
    (h_dst_c : MirSemantics.getElem? callerCache dstId = some true) :
    updateMiriLocalsLoop types (fun idx => Nat.beq idx dstId) 0
        callerBody.locals callerLocals'
        (liftLocalsCached types callerBody.locals callerLocals callerCache) =
      liftLocalsCached types callerBody.locals callerLocals' callerCache := by
  have h_fn : (fun idx => Nat.beq idx dstId) = (fun idx => Nat.beq dstId idx) := by
    funext idx; exact nat_beq_comm idx dstId
  rw [h_fn]
  have h_upd := updateMiriLocalsLoop_liftLocalsCached types (fun idx => Nat.beq dstId idx)
    0 callerBody.locals callerLocals' callerLocals callerCache
    (SlotsMatchTys.length_eq h_inv').symm
    ((SlotsMatchTys.length_eq h_inv').trans (SlotsMatchTys.length_eq h_inv).symm)
    ((SlotsMatchTys.length_eq h_inv).trans h_c_len.symm)
  rw [updateCacheLoop_cacheTouch, cacheTouch_eq_self_of_true h_dst_c] at h_upd
  exact h_upd

private theorem attachCallers_step_eq (callers : List FrameState)
    (s' : State) :
    attachCallers callers (.step s') = .step { s' with frames := s'.frames ++ callers } := by
  cases callers with
  | nil => cases s'; simp [attachCallers]
  | cons _ _ => rfl

private theorem attachCallers_fault_eq (callers : List FrameState) (k : FaultKind) :
    attachCallers callers (.fault k) = .fault k := by
  cases callers <;> rfl

private theorem evalRefStep_eq_base_aux (rp : RefProg) (p : Program) (s : State) (rs : RefState)
    (f : FrameState) (callers : List FrameState) (body : Body) (rbody : RefBody)
    (h_dec : decodeProg rp = some p)
    (hs : s.frames = f :: callers)
    (h_body : activeFrameBody p f = some body)
    (h_rbody : activeRefFrameBody rp f = some rbody)
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true)
    (c : Choice)
    (rframes : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (retTy : MirTy)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (topRel? : Option Nat)
    (_h_smem : s.mem = entryMemory)
    (h_ert : entryRetTy? p = some retTy)
    (h_rty : rs.retTy = retTy)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, rs.retPlace))
    (h_ctrl : RefControlValid ctrl)
    (h_tr : refTopRelevanceValid rframes.size topRel?)
    (h_miri : rs.miri = mkRefMiriStackState rframes topRel? mem ctrl s.callerMem)
    (rfsRev : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (h_rev_eq : rframes.toList.reverse = rfsRev)
    (h_fsim : FramesSimInv rp p rs.retPlace (f :: callers) rfsRev) :
    evalRefStep rp c rs =
      stepResultToRefOutcome (mapStepRes rp body rbody f rs (evalStep p c s)) := by
  have ⟨h_ps, h_lh⟩ := decodeProg_panicStrategy h_dec
  cases h_fsim with
  | @root _ rf h_defId h_sro h_rdst h_rtgt h_fs =>
    let ⟨body_sim, rbody_sim, cache, h_bs, h_rbs, h_bdec, h_arg, h_sa, h_dv, h_cv,
      h_act, h_calls, h_all_static, h_supp, h_inv, h_pc, h_crep, h_rf⟩ := h_fs
    have h_act_b : activeFrameBody p f = some body_sim := by
      dsimp only [activeFrameBody]; rw [h_sro]; exact h_bs
    have h_act_rb : activeRefFrameBody rp f = some rbody_sim := by
      dsimp only [activeRefFrameBody]; rw [h_sro]; exact h_rbs
    rw [h_body] at h_act_b; injection h_act_b with hb_eq; subst hb_eq
    rw [h_rbody] at h_act_rb; injection h_act_rb with hrb_eq; subst hrb_eq
    have h_ret_ty : MirSemantics.getElem? body.locals 0 = some retTy := by
      dsimp only [entryRetTy?] at h_ert
      rw [← h_defId, h_bs] at h_ert
      exact h_ert
    let ctx : SimFrameCtx := { SimFrameCtx.root f.defId rs.retPlace with topRel? := topRel? }
    let st := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache mem ctrl s.callerMem
    have h_miri_eq : rs.miri = st := by
      rw [h_miri]
      exact frameSimInv_root_eq_mkGenSimState rp p f body rbody rs.retPlace cache topRel?
        mem ctrl s.callerMem rframes rf h_rev_eq h_rf
    have h_rframes_sz : rframes.size = 1 := by
      rw [array_eq_singleton_of_toList_reverse h_rev_eq]; rfl
    have h_tr_ctx : refTopRelevanceValid (ctx.below.size + 1) ctx.topRel? := by
      dsimp only [ctx, SimFrameCtx.root]
      change refTopRelevanceValid 1 topRel?
      rw [← h_rframes_sz]; exact h_tr
    let ⟨_, _, h_bbs_dec, _, _⟩ := decodeBody_inv h_bdec
    have h_c_len : cache.length = body.locals.length := by rw [h_crep, List.length_replicate]
    have h_clear_st :
        ({ st with machine := { st.machine with pendingMoveDeinit := false } } :
          MiriStepState) = st := rfl
    have h_step_eq :
        Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
          let r := Miri.Interpreter.Step.step
            (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
            c st
          ({ r.1 with machine := { r.1.machine with pendingMoveDeinit := false } }, r.2) := by
      rw [h_miri_eq]
      dsimp only [Miri.Interpreter.ExecutionMachine.step]
      rw [h_clear_st]
    have h_st_cf :
        st.stack.currentFrame? =
          some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) := rfl
    have h_mf_loc :
        (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).location =
          .mir ⟨f.blockIdx, f.stmtIdx⟩ := rfl
    have h_mframe_bb : ∀ (bbIdx : BasicBlockId),
        (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).body.basicBlocks[bbIdx]? =
          (MirSemantics.getElem? rbody.basicBlocks bbIdx).map (toMiriBasicBlock rp.types) := by
      intro bbIdx
      dsimp only [mkGenSimFrame, toMiriBody]
      rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map]
    cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
    | none =>
      have h_rbb_none : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = none :=
        (mapOption_getElem? h_bbs_dec f.blockIdx).1 h_bb
      have h_em_err :
          Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
            (st, .error (.invalidBlock f.blockIdx)) := by
        rw [h_step_eq]
        dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [h_st_cf]; dsimp only
        rw [h_mf_loc]; dsimp only
        rw [h_mframe_bb f.blockIdx, h_rbb_none]; rfl
      rw [evalRefStep_of_err rp c rs st (.invalidBlock f.blockIdx) .unsupported h_lt
        rfl h_em_err]
      dsimp only [evalStep]
      rw [hs]; dsimp only; rw [h_body]; dsimp only; rw [h_bb]; rfl
    | some bb =>
      let ⟨rbb, h_rbb, h_rbb_dec⟩ := (mapOption_getElem? h_bbs_dec f.blockIdx).2 bb h_bb
      let ⟨h_stmts_dec, h_term_dec, _⟩ := decodeBasicBlock_inv h_rbb_dec
      have h_mb :
          (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals
            cache).body.basicBlocks[f.blockIdx]? =
            some (toMiriBasicBlock rp.types rbb) := by
        rw [h_mframe_bb f.blockIdx, h_rbb]; rfl
      have h_mstmt : ∀ (si : Nat),
          (toMiriBasicBlock rp.types rbb).statements[si]? =
            (MirSemantics.getElem? rbb.statements si).map (toMiriStatement rp.types) := by
        intro si
        dsimp only [toMiriBasicBlock]
        rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map]
      cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx with
      | some stmt =>
        let ⟨rstmt, h_rstmt, h_rstmt_dec⟩ :=
          (mapOption_getElem? h_stmts_dec f.stmtIdx).2 stmt h_st
        have h_evS := step_evalStatement_ref_eq rp c ctx rbody body f
          cache mem ctrl s.callerMem s.mem rstmt stmt h_bdec h_c_len (Or.inl h_crep) h_arg h_supp h_inv
          h_rstmt_dec
          (fun dst src srcTy ety dstTy h_st_eq =>
            discriminantTypesValid_stmt h_dv h_bb (by rw [← h_st_eq]; exact h_st) src srcTy ety dstTy rfl)
          (fun dst opnd castTy dstTy h_st_eq =>
            castTypesValid_stmt h_cv h_bb (by rw [← h_st_eq]; exact h_st) opnd castTy dstTy rfl)
        have h_step_stmt_err :
            ∀ (err : Miri.Interpreter.StepError) (st₁ : MiriStepState),
              Miri.Interpreter.Step.evalStatement
                  (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                  c (toMiriStatement rp.types rstmt) st = (st₁, .error err) →
              Miri.Interpreter.Step.step
                  (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                  c st = (st₁, .error err) := by
          intro err st₁ h_ev_err
          dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
          rw [h_st_cf]; dsimp only
          rw [h_mf_loc]; dsimp only
          rw [h_mb]; dsimp only
          rw [h_mstmt f.stmtIdx, h_rstmt]; dsimp only [Option.map]
          rw [h_ev_err]
        have h_step_stmt_ok :
            ∀ (slots' : List LocalSlot) (cache' : List Bool),
              Miri.Interpreter.Step.evalStatement
                  (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                  c (toMiriStatement rp.types rstmt) st =
                (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem, .ok ()) →
              Miri.Interpreter.Step.step
                  (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                  c st =
                (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals slots' cache' mem ctrl s.callerMem, .ok true) := by
          intro slots' cache' h_ev_ok
          dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
          rw [h_st_cf]; dsimp only
          rw [h_mf_loc]; dsimp only
          rw [h_mb]; dsimp only
          rw [h_mstmt f.stmtIdx, h_rstmt]; dsimp only [Option.map]
          rw [h_ev_ok]; dsimp only
          rw [show (st.stack.frames.size - 1 !=
              (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack.frames.size - 1) = false from by
            dsimp only [st, mkGenSimState, mkRefMiriStackState]
            rw [Array.size_push, Array.size_push]
            simp]
          rw [ite_false_eq]
          rw [show (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack.currentFrame? =
              some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache') from by
            dsimp only [mkGenSimState, mkRefMiriStackState]
            exact stack_currentFrame?_push _ _]
          dsimp only [mkGenSimFrame]
          rw [show ctx.locOverride = none from rfl]
          dsimp only
          have h_lt_sz :
              (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack.frames.size - 1 <
              (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack.frames.size := by
            dsimp only [mkGenSimState, mkRefMiriStackState]
            rw [Array.size_push]
            exact Nat.lt_succ_self _
          rw [dite_eq_left_of_eq_true (eq_true h_lt_sz)]
          change ({ stack := _, machine := _ }, Except.ok true) =
            (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals slots' cache' mem ctrl s.callerMem, Except.ok true)
          exact congrArg
            (fun frs =>
              (({ stack := { (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack with frames := frs },
                  machine := (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).machine } :
                  MiriStepState),
               Except.ok true))
            (array_set_push_last _ _ _ h_lt_sz)
        have h_evalStep_stmt : evalStep p c s = evalStatement body f s.mem s.callerMem stmt := by
          dsimp only [evalStep]
          rw [hs]; dsimp only; rw [h_body]; dsimp only
          rw [h_bb]; dsimp only; rw [h_st]
          exact attachCallers_nil _
        rw [h_evalStep_stmt]
        cases h_es : evalStatement body f s.mem s.callerMem stmt with
        | fault k =>
          rw [h_es] at h_evS
          let ⟨err, st', h_err, h_fk⟩ := h_evS
          have h_em_err :
              Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
            rw [h_step_eq, h_step_stmt_err err st' h_err]
          rw [evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
        | done _ => rw [h_es] at h_evS; exact False.elim h_evS
        | step s' =>
          rw [h_es] at h_evS
          let ⟨slots', h_s'_eq, h_ok_s⟩ := h_evS
          subst h_s'_eq
          have h_inv' : SlotsMatchTys body.locals slots' := by
            let ⟨w', hw', _, h_w, _⟩ := evalStatement_step_inv h_bb h_st h_inv h_es
            injection hw' with h_fs
            injection h_fs with h_feq
            subst h_feq
            exact h_w
          have h_em_ok :
              Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals
                  slots' (stmtCacheTouch stmt cache) mem ctrl s.callerMem, .ok true) := by
            rw [h_step_eq, h_step_stmt_ok slots' (stmtCacheTouch stmt cache) h_ok_s]; rfl
          have h_nc : nextRefControlForStep body f ctrl = ctrl := by
            dsimp only [nextRefControlForStep]
            rw [h_bb]; dsimp only; rw [h_st]
          dsimp only [evalRefStep, mapStepRes]
          rw [h_lt, ite_not_true_eq, h_em_ok]
          change (if (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals
                slots' (stmtCacheTouch stmt cache) mem ctrl s.callerMem).stack.frames.isEmpty then _
              else _) = _
          rw [show (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals
              slots' (stmtCacheTouch stmt cache) mem ctrl s.callerMem).stack.frames.isEmpty = false from rfl,
            ite_false_eq]
          rw [h_miri_eq]
          dsimp only [liftStackStep, st, mkGenSimState]
          rw [show (mkRefMiriStackState (ctx.below.push
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem).stack.frames.size = 1 from rfl,
            show (Nat.beq 1 1) = true from rfl, ite_true_eq]
          rw [show (mkRefMiriStackState (ctx.below.push
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem).stack.frames[0]? =
              some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) from rfl]
          dsimp only
          let ⟨th, h_th, h_trel⟩ := mkRefMiriStackState_activeThread?
            (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
            ctx.topRel? mem ctrl s.callerMem
          rw [h_th]; dsimp only; rw [h_trel]
          rw [show (mkRefMiriStackState (ctx.below.push
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem).machine.memory = mem from rfl]
          rw [show (mkRefMiriStackState (ctx.below.push
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem).machine.user.control = ctrl from rfl]
          rw [h_nc]
          have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types (stepTouchesLocal body f)
            0 body.locals slots' f.locals cache
            (SlotsMatchTys.length_eq h_inv').symm
            ((SlotsMatchTys.length_eq h_inv').trans (SlotsMatchTys.length_eq h_inv).symm)
            ((SlotsMatchTys.length_eq h_inv).trans h_c_len.symm)
          rw [updateCacheLoop_stepTouchesLocal_stmt body f bb stmt h_bb h_st cache] at h_upd
          rw [show (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).locals.toList =
              liftLocalsCached rp.types body.locals f.locals cache from rfl, h_upd]
          rfl
      | none =>
        have h_rstmt_none : MirSemantics.getElem? rbb.statements f.stmtIdx = none :=
          (mapOption_getElem? h_stmts_dec f.stmtIdx).1 h_st
        have h_le : f.stmtIdx ≤ bb.statements.length := h_pc bb h_bb
        have h_ge : bb.statements.length ≤ f.stmtIdx := mirGetElem?_ge_of_none h_st
        have h_eq_len : f.stmtIdx = bb.statements.length := Nat.le_antisymm h_le h_ge
        have h_beq_len : Nat.beq f.stmtIdx bb.statements.length = true := by
          rw [h_eq_len]; exact Nat.beq_refl _
        have h_bt :
            (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).beforeTerminator c st =
              (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache
                mem (advanceRefControl ctrl) s.callerMem, .ok ()) := by
          dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
            Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
            Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
          rw [beforeTerminator_ref_eq (st := st) h_ctrl rfl]
          rfl
        have h_step_term :
            Miri.Interpreter.Step.step
                (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                c st =
              let r := (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).terminator
                c (toMiriTerminator rp.types rbb.terminator)
                (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache
                  mem (advanceRefControl ctrl) s.callerMem)
              (r.1, r.2.map fun _ => true) := by
          dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
          rw [h_st_cf]; dsimp only
          rw [h_mf_loc]; dsimp only
          rw [h_mb]; dsimp only
          rw [h_mstmt f.stmtIdx, h_rstmt_none]; dsimp only [Option.map]
          change (match ((Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).beforeTerminator c st).snd with
            | Except.error error =>
              (((Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).beforeTerminator c st).fst,
                Except.error error)
            | Except.ok () =>
              let r := (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).terminator c
                (toMiriBasicBlock rp.types rbb).terminator
                ((Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).beforeTerminator c st).fst
              (r.1, r.2.map fun _ => true)) = _
          rw [h_bt]
          rfl
        have h_nc : nextRefControlForStep body f ctrl = advanceRefControl ctrl := by
          dsimp only [nextRefControlForStep]
          rw [h_bb]; dsimp only; rw [h_st]; dsimp only; rw [h_beq_len, ite_true_eq]
        have h_evalStep_term :
            evalStep p c s =
              match bb.terminator with
              | .call callee args dst target unwind =>
                match MirSemantics.getElem? p.bodies callee with
                | none => .fault .unsupported
                | some calleeBody =>
                  evalCallTerminator body bb f [] s.mem s.callerMem
                    callee none calleeBody args dst target unwind
              | .sysrootCall op args dst target unwind =>
                evalCallTerminator body bb f [] s.mem s.callerMem
                  0 (some op) (sysrootNumBody op) args dst target unwind
              | .return_ => evalTerminator body bb f s.mem s.callerMem
                  rp.panicStrategy rp.hasLocalPanicHandler
              | _ => attachCallers [] (evalTerminator body bb f s.mem s.callerMem
                  rp.panicStrategy rp.hasLocalPanicHandler) := by
          dsimp only [evalStep]
          rw [hs]; dsimp only; rw [h_body]; dsimp only; rw [h_bb]; dsimp only
          rw [h_st]; dsimp only; rw [h_beq_len, ite_true_eq, h_ps, h_lh]
          cases bb.terminator <;> rfl
        rw [h_evalStep_term]
        cases h_rterm : rbb.terminator with
        | call callee rargs rdst tgt unwind =>
          rw [h_rterm] at h_term_dec
          let ⟨args, dst, h_dargs, h_ddst, h_bterm⟩ := decodeTerminator_call_inv h_term_dec
          rw [h_bterm]
          dsimp only
          have h_calls_bb := list_all_mirGetElem? h_calls h_bb
          rw [h_bterm] at h_calls_bb
          dsimp only at h_calls_bb
          cases h_cbody : MirSemantics.getElem? p.bodies callee with
          | none => rw [h_cbody] at h_calls_bb; cases h_calls_bb
          | some calleeBody =>
            rw [h_cbody] at h_calls_bb
            dsimp only at h_calls_bb
            dsimp only
            let ⟨calleeRbody, h_rcbody, h_cbdec⟩ :=
              (mapOption_getElem? (decodeProg_inv h_dec).2.2.2.2 callee).2 calleeBody h_cbody
            have h_any : bodyHasAnyCall body = true :=
              bodyHasAnyCall_of_call body f.blockIdx bb h_bb callee args dst tgt unwind h_bterm
            have h_all_st := h_all_static
            dsimp only [allCallBodiesStaticAdmitted] at h_all_st
            rw [h_any, ite_true_eq, Bool.and_eq_true] at h_all_st
            have h_csat : callBodyStaticAdmitted p calleeBody = true :=
              all_getElem?_eq_true h_all_st.2 h_cbody
            have h_evC := callTerminator_crate_ref_eq rp p c ctx rbody calleeRbody body calleeBody
              rbb bb f [] cache mem (advanceRefControl ctrl) s.callerMem s.mem
              callee rargs args rdst dst tgt unwind
              h_dec h_bdec h_rbb h_rbb_dec h_rterm h_c_len h_tr_ctx rfl h_inv
              h_rcbody h_cbdec (bool_and_split h_calls_bb).2 h_dargs h_ddst h_csat
            dsimp only at h_evC
            dsimp only [st] at h_step_term
            rw [h_rterm] at h_step_term
            cases h_ec : evalCallTerminator body bb f [] s.mem s.callerMem callee none calleeBody args dst tgt unwind with
            | fault k =>
              rw [h_ec] at h_evC
              let ⟨err, st', h_err, h_fk⟩ := h_evC
              rw [h_rterm] at h_err
              rw [h_err] at h_step_term
              have h_em_err :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
                rw [h_step_eq, h_step_term]; rfl
              rw [evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
            | done _ => rw [h_ec] at h_evC; exact False.elim h_evC
            | step s' =>
              rw [h_ec] at h_evC
              let ⟨callerLocals', callerCache', h_cc_eq, h_cc_len, h_cl_inv, h_dst_true,
                dstTy, retTy, calleeLocals, argVals, h_dst_ty, h_dst_supp, h_cret_ty, h_beq,
                _, h_s'_eq, h_res_eq⟩ := h_evC
              subst h_s'_eq
              rw [h_rterm] at h_res_eq
              rw [h_res_eq] at h_step_term
              have h_em_ok :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    (mkGenSimState rp (SimFrameCtx.call rp.types
                        (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'))
                        (some (ctx.below.size + 1)) (fnTagForCrate callee) ctx.below.size dst.localId dstTy tgt)
                      calleeRbody 0 0 calleeBody.locals calleeLocals
                      (calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals)
                      mem (advanceRefControl ctrl) s.callerMem, .ok true) := by
                rw [h_step_eq, h_step_term]; rfl
              dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
              rw [h_lt, ite_not_true_eq, h_em_ok]
              change (if (mkGenSimState _ _ _ _ _ _ _ _ _ _ _).stack.frames.isEmpty then _ else _) = _
              rw [show (mkGenSimState rp (SimFrameCtx.call rp.types
                    (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'))
                    (some (ctx.below.size + 1)) (fnTagForCrate callee) ctx.below.size dst.localId dstTy tgt)
                  calleeRbody 0 0 calleeBody.locals calleeLocals
                  (calleeInitCacheLoop calleeBody.argumentCount 0 calleeBody.locals)
                  mem (advanceRefControl ctrl) s.callerMem).stack.frames.isEmpty = false from rfl,
                ite_false_eq]
              rw [h_miri_eq]
              dsimp only [st, mkGenSimState]
              rw [show nextRefControlForStep body f (mkRefMiriStackState
                  (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).machine.user.control = advanceRefControl ctrl from h_nc]
              let ⟨th, h_th, _⟩ := mkRefMiriStackState_activeThread?
                (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem
              rw [h_th]
              dsimp only [liftStackStep]
              rw [show (Nat.beq (List.length [] + 2)
                  (mkRefMiriStackState (ctx.below.push
                    (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                    ctx.topRel? mem ctrl s.callerMem).stack.frames.size) = false from rfl,
                ite_false_eq]
              rw [show (Nat.beq (List.length [] + 2)
                  ((mkRefMiriStackState (ctx.below.push
                    (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                    ctx.topRel? mem ctrl s.callerMem).stack.frames.size + 1)) = true from rfl,
                ite_true_eq]
              rw [show (mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames.back? =
                  some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) from rfl]
              dsimp only
              rw [refResolveCalleeBody_crate rp callee calleeRbody calleeBody.locals h_rcbody (decodeBody_locals h_cbdec)]
              dsimp only
              rw [decodeBody_argumentCount h_cbdec]
              rw [calleeTys_head_eq_of_beq h_cret_ty h_beq]
              have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types (callTouchesCallerLocal body f)
                0 body.locals callerLocals' f.locals cache
                (SlotsMatchTys.length_eq h_cl_inv).symm
                ((SlotsMatchTys.length_eq h_cl_inv).trans (SlotsMatchTys.length_eq h_inv).symm)
                ((SlotsMatchTys.length_eq h_inv).trans h_c_len.symm)
              rw [updateCacheLoop_callTouchesCallerLocal body f bb args dst cache h_bb
                (Or.inl ⟨callee, tgt, unwind, h_bterm⟩), ← h_cc_eq] at h_upd
              rw [show (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).locals.toList =
                  liftLocalsCached rp.types body.locals f.locals cache from rfl, h_upd]
              rfl
        | sysrootCall op rargs rdst tgt unwind =>
          rw [h_rterm] at h_term_dec
          let ⟨args, dst, h_dargs, h_ddst, h_bterm⟩ := decodeTerminator_sysrootCall_inv h_term_dec
          rw [h_bterm]
          dsimp only
          have h_calls_bb := list_all_mirGetElem? h_calls h_bb
          rw [h_bterm] at h_calls_bb
          dsimp only at h_calls_bb
          have h_evC := callTerminator_sysroot_ref_eq rp c ctx rbody body
            rbb bb f [] cache mem (advanceRefControl ctrl) s.callerMem s.mem
            op rargs args rdst dst tgt unwind
            h_bdec h_rbb h_rbb_dec h_rterm h_c_len h_tr_ctx rfl h_inv
            h_calls_bb h_dargs h_ddst
          dsimp only at h_evC
          dsimp only [st] at h_step_term
          rw [h_rterm] at h_step_term
          cases h_ec : evalCallTerminator body bb f [] s.mem s.callerMem 0 (some op) (sysrootNumBody op) args dst tgt unwind with
          | fault k =>
            rw [h_ec] at h_evC
            let ⟨err, st', h_err, h_fk⟩ := h_evC
            rw [h_rterm] at h_err
            rw [h_err] at h_step_term
            have h_em_err :
                Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                  ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
              rw [h_step_eq, h_step_term]; rfl
            rw [evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
          | done _ => rw [h_ec] at h_evC; exact False.elim h_evC
          | step s' =>
            rw [h_ec] at h_evC
            let ⟨callerLocals', callerCache', h_cc_eq, h_cc_len, h_cl_inv, h_dst_true,
              dstTy, retTy, calleeLocals, argVals, h_dst_ty, h_dst_supp, h_cret_ty, h_beq,
              _, h_s'_eq, h_res_eq⟩ := h_evC
            subst h_s'_eq
            rw [h_rterm] at h_res_eq
            rw [h_res_eq] at h_step_term
            have h_em_ok :
                Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                  (mkGenSimState rp (SimFrameCtx.call rp.types
                      (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'))
                      (some (ctx.below.size + 1)) (fnTagForSysroot op) ctx.below.size dst.localId dstTy tgt)
                    (sysrootNumRefBody rp.types op) 0 0 (sysrootNumBody op).locals calleeLocals
                    (calleeInitCacheLoop (sysrootNumBody op).argumentCount 0 (sysrootNumBody op).locals)
                    mem (advanceRefControl ctrl) s.callerMem, .ok true) := by
              rw [h_step_eq, h_step_term]; rfl
            dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
            rw [h_lt, ite_not_true_eq, h_em_ok]
            change (if (mkGenSimState _ _ _ _ _ _ _ _ _ _ _).stack.frames.isEmpty then _ else _) = _
            rw [show (mkGenSimState rp (SimFrameCtx.call rp.types
                  (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'))
                  (some (ctx.below.size + 1)) (fnTagForSysroot op) ctx.below.size dst.localId dstTy tgt)
                (sysrootNumRefBody rp.types op) 0 0 (sysrootNumBody op).locals calleeLocals
                (calleeInitCacheLoop (sysrootNumBody op).argumentCount 0 (sysrootNumBody op).locals)
                mem (advanceRefControl ctrl) s.callerMem).stack.frames.isEmpty = false from rfl,
              ite_false_eq]
            rw [h_miri_eq]
            dsimp only [st, mkGenSimState]
            rw [show nextRefControlForStep body f (mkRefMiriStackState
                (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).machine.user.control = advanceRefControl ctrl from h_nc]
            let ⟨th, h_th, _⟩ := mkRefMiriStackState_activeThread?
              (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem
            rw [h_th]
            dsimp only [liftStackStep]
            rw [show (Nat.beq (List.length [] + 2)
                (mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames.size) = false from rfl,
              ite_false_eq]
            rw [show (Nat.beq (List.length [] + 2)
                ((mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames.size + 1)) = true from rfl,
              ite_true_eq]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).stack.frames.back? =
                some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) from rfl]
            dsimp only
            rw [refResolveCalleeBody_sysroot]
            dsimp only
            rw [show (sysrootNumRefBody rp.types op).argumentCount = (sysrootNumBody op).argumentCount from rfl]
            rw [show ([MirTy.int op.width op.signed, MirTy.int op.width op.signed, MirTy.int op.width op.signed][0]?.getD MirTy.unit) = dstTy from
              calleeTys_head_eq_of_beq h_cret_ty h_beq]
            have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types (callTouchesCallerLocal body f)
              0 body.locals callerLocals' f.locals cache
              (SlotsMatchTys.length_eq h_cl_inv).symm
              ((SlotsMatchTys.length_eq h_cl_inv).trans (SlotsMatchTys.length_eq h_inv).symm)
              ((SlotsMatchTys.length_eq h_inv).trans h_c_len.symm)
            rw [updateCacheLoop_callTouchesCallerLocal body f bb args dst cache h_bb
              (Or.inr ⟨op, tgt, unwind, h_bterm⟩), ← h_cc_eq] at h_upd
            rw [show (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).locals.toList =
                liftLocalsCached rp.types body.locals f.locals cache from rfl, h_upd]
            rfl
        | return_ | goto _ | unreachable | unwindResume
        | switchInt _ _ | assert _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported =>
          have h_noncall :
              (∀ callee args dst tgt uw, rbb.terminator ≠ .call callee args dst tgt uw) ∧
              (∀ op args dst tgt uw, rbb.terminator ≠ .sysrootCall op args dst tgt uw) := by
            constructor
            · intro callee args dst tgt uw h_eq; rw [h_rterm] at h_eq; cases h_eq
            · intro op args dst tgt uw h_eq; rw [h_rterm] at h_eq; cases h_eq
          have h_evT := evalTerminator_ref_eq rp c ctx rbody body rbb bb f retTy cache
            rs.retPlace mem (advanceRefControl ctrl) s.callerMem s.mem h_bdec h_c_len h_bb h_rbb
            h_rbb_dec rfl (fun _ => ⟨f.defId, rfl, h_tr_ctx, h_ret_ty, h_init⟩) h_noncall
            h_act h_supp h_inv
          dsimp only at h_evT
          have h_bnoncall := decodeTerminator_ne_call h_noncall h_term_dec
          rw [h_rterm] at h_step_term
          have h_rhs_ev :
              (match bb.terminator with
                | .call callee args dst target unwind =>
                  match MirSemantics.getElem? p.bodies callee with
                  | none => .fault .unsupported
                  | some calleeBody =>
                    evalCallTerminator body bb f [] s.mem s.callerMem callee none calleeBody args dst target unwind
                | .sysrootCall op args dst target unwind =>
                  evalCallTerminator body bb f [] s.mem s.callerMem 0 (some op) (sysrootNumBody op) args dst target unwind
                | .return_ => evalTerminator body bb f s.mem s.callerMem
                    rp.panicStrategy rp.hasLocalPanicHandler
                | _ => attachCallers [] (evalTerminator body bb f s.mem s.callerMem
                    rp.panicStrategy rp.hasLocalPanicHandler)) =
              evalTerminator body bb f s.mem s.callerMem
                rp.panicStrategy rp.hasLocalPanicHandler := by
            cases h_rt_eq : bb.terminator with
            | return_ => rfl
            | call c a d g u => exact False.elim (h_bnoncall.1 c a d g u h_rt_eq)
            | sysrootCall o a d g u => exact False.elim (h_bnoncall.2 o a d g u h_rt_eq)
            | goto _ | unreachable | unwindResume
            | switchInt _ _ | assert _ _ _ _ _
            | coreCall _ _ _ _ _ | unsupported => exact attachCallers_nil _
          rw [h_rhs_ev]
          cases h_et : evalTerminator body bb f s.mem s.callerMem
              rp.panicStrategy rp.hasLocalPanicHandler with
          | fault k =>
            rw [h_et] at h_evT
            let ⟨err, st', h_err, h_fk⟩ := h_evT
            rw [h_rterm] at h_err
            rw [h_err] at h_step_term
            have h_em_err :
                Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                  ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
              rw [h_step_eq, h_step_term]; rfl
            rw [evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
          | done out =>
            rw [h_et] at h_evT
            cases out with
            | unwound uw => exact False.elim h_evT
            | aborted cm' =>
              let ⟨st', h_err_t, h_cm'⟩ := h_evT
              rw [h_rterm] at h_err_t
              rw [h_err_t] at h_step_term
              have h_em_err :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    ({ st' with machine := { st'.machine with pendingMoveDeinit := false } },
                     .error (.termination (.abort "panic abort"))) := by
                rw [h_step_eq, h_step_term]; rfl
              dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
              rw [h_lt, ite_not_true_eq, h_em_err]
              dsimp only
              rw [h_cm']
            | returned rv =>
              cases rv with
              | mk v cm' =>
                let ⟨st', h_st'_eq, h_empty, h_rv, h_cm'⟩ := h_evT
                rw [h_rterm] at h_st'_eq
                rw [h_st'_eq] at h_step_term
                have h_em_ok :
                    Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                      ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .ok true) := by
                  rw [h_step_eq, h_step_term]; rfl
                dsimp only [evalRefStep, stepResultToRefOutcome, mapStepRes]
                rw [h_lt, ite_not_true_eq, h_em_ok]
                dsimp only
                rw [h_empty, ite_true_eq, h_rty, h_rv, h_cm']
          | step s' =>
            rw [h_et] at h_evT
            let ⟨tgt, slots', h_s'_eq, h_res_eq⟩ := h_evT
            subst h_s'_eq
            have h_inv' : SlotsMatchTys body.locals slots' := by
              let ⟨_, hw', _, h_w, _⟩ := evalTerminator_step_inv h_inv h_et
              injection hw' with h_fs
              injection h_fs with h_feq
              subst h_feq
              exact h_w
            rw [h_rterm] at h_res_eq
            rw [h_res_eq] at h_step_term
            have h_em_ok :
                Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                  (mkGenSimState rp ctx rbody tgt 0 body.locals
                    slots' (termCacheTouch bb.terminator cache) mem (advanceRefControl ctrl) s.callerMem, .ok true) := by
              rw [h_step_eq, h_step_term]; rfl
            dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
            rw [h_lt, ite_not_true_eq, h_em_ok]
            change (if (mkGenSimState rp ctx rbody tgt 0 body.locals
                  slots' (termCacheTouch bb.terminator cache) mem (advanceRefControl ctrl) s.callerMem).stack.frames.isEmpty then _
                else _) = _
            rw [show (mkGenSimState rp ctx rbody tgt 0 body.locals
                slots' (termCacheTouch bb.terminator cache) mem (advanceRefControl ctrl) s.callerMem).stack.frames.isEmpty = false from rfl,
              ite_false_eq]
            rw [h_miri_eq]
            dsimp only [liftStackStep, st, mkGenSimState]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).stack.frames.size = 1 from rfl,
              show (Nat.beq 1 1) = true from rfl, ite_true_eq]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).stack.frames[0]? =
                some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) from rfl]
            dsimp only
            let ⟨th, h_th, h_trel⟩ := mkRefMiriStackState_activeThread?
              (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem
            rw [h_th]; dsimp only; rw [h_trel]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).machine.memory = mem from rfl]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).machine.user.control = ctrl from rfl]
            rw [h_nc]
            have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types (stepTouchesLocal body f)
              0 body.locals slots' f.locals cache
              (SlotsMatchTys.length_eq h_inv').symm
              ((SlotsMatchTys.length_eq h_inv').trans (SlotsMatchTys.length_eq h_inv).symm)
              ((SlotsMatchTys.length_eq h_inv).trans h_c_len.symm)
            rw [updateCacheLoop_stepTouchesLocal_term body f bb h_bb h_st h_beq_len cache] at h_upd
            rw [show (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).locals.toList =
                liftLocalsCached rp.types body.locals f.locals cache from rfl, h_upd]
            rfl
  | @push _ caller rest rcallee rcaller rrest callerBody calleeBody dst dstTy retTy_sim
      h_caller_sim h_caller_b h_callee_b h_ret_dst h_dst_proj h_dst_ty h_dst_supp
      h_cret_ty h_beq h_ret_tgt h_rc_ls h_cf =>
    let ⟨body_sim, rbody_sim, cache, fnTag, h_bs, h_rbs, h_bdec, h_fnTag, h_crate_body,
      h_sys_defId, h_arg, h_sa, h_dv, h_cv, h_act, h_av, h_calls, h_all_static, h_supp,
      h_inv, h_pc, h_c_len, h_rf⟩ := h_cf
    rw [h_body] at h_bs; injection h_bs with hb_eq; subst hb_eq
    rw [h_body] at h_callee_b; injection h_callee_b with hcb_eq; subst hcb_eq
    rw [h_rbody] at h_rbs; injection h_rbs with hrb_eq; subst hrb_eq
    subst h_fnTag
    have h_rrest_len : rrest.length = rest.length := by
      have h_l := framesSimInv_length_eq h_caller_sim
      simp [List.length_cons] at h_l
      exact h_l
    let below : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra) :=
      ⟨(rcaller :: rrest).reverse⟩
    have h_below_sz : below.size = rest.length + 1 := by
      dsimp only [below]
      simp [List.length_reverse, List.length_cons, h_rrest_len]
    have h_rframes_sz : rframes.size = rest.length + 2 := by
      have h_l := congrArg List.length h_rev_eq
      simp [List.length_reverse, List.length_cons, h_rrest_len] at h_l
      exact h_l
    have h_tr_ctx : refTopRelevanceValid (below.size + 1) topRel? := by
      rw [show below.size + 1 = rframes.size from by rw [h_below_sz, h_rframes_sz]]
      exact h_tr
    have h_topRel_eq : topRel? = some below.size := by
      cases h_tr_c : topRel? with
      | none =>
        rw [h_tr_c] at h_tr
        dsimp only [refTopRelevanceValid] at h_tr
        rw [h_rframes_sz] at h_tr
        cases Nat.succ.inj h_tr
      | some idx =>
        rw [h_tr_c] at h_tr
        dsimp only [refTopRelevanceValid] at h_tr
        rw [h_rframes_sz] at h_tr
        have h_idx : idx = below.size :=
          (h_tr.2.trans (Nat.add_sub_cancel (rest.length + 1) 1)).trans h_below_sz.symm
        rw [h_idx]
    let ctx : SimFrameCtx := SimFrameCtx.call rp.types below topRel?
      (match f.sysrootOp? with | some op => fnTagForSysroot op | none => fnTagForCrate f.defId)
      rest.length dst.localId dstTy f.retTarget?
    let st := mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache mem ctrl s.callerMem
    have h_miri_eq : rs.miri = st := by
      rw [h_miri]
      exact callFrameSimInv_push_eq_mkGenSimState rp p f body rbody cache
        (match f.sysrootOp? with | some op => fnTagForSysroot op | none => fnTagForCrate f.defId)
        rest.length dst.localId dstTy f.retTarget? topRel? mem ctrl s.callerMem
        rframes rcallee (rcaller :: rrest) h_rev_eq h_rf
    let ⟨_, _, h_bbs_dec, _, _⟩ := decodeBody_inv h_bdec
    have h_clear_st :
        ({ st with machine := { st.machine with pendingMoveDeinit := false } } :
          MiriStepState) = st := rfl
    have h_step_eq :
        Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
          let r := Miri.Interpreter.Step.step
            (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
            c st
          ({ r.1 with machine := { r.1.machine with pendingMoveDeinit := false } }, r.2) := by
      rw [h_miri_eq]
      dsimp only [Miri.Interpreter.ExecutionMachine.step]
      rw [h_clear_st]
    have h_st_cf :
        st.stack.currentFrame? =
          some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) := by
      dsimp only [st, mkGenSimState, mkRefMiriStackState]
      exact stack_currentFrame?_push _ _
    have h_mf_loc :
        (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).location =
          .mir ⟨f.blockIdx, f.stmtIdx⟩ := rfl
    have h_mframe_bb : ∀ (bbIdx : BasicBlockId),
        (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).body.basicBlocks[bbIdx]? =
          (MirSemantics.getElem? rbody.basicBlocks bbIdx).map (toMiriBasicBlock rp.types) := by
      intro bbIdx
      dsimp only [mkGenSimFrame, toMiriBody]
      rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map]
    cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
    | none =>
      have h_rbb_none : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = none :=
        (mapOption_getElem? h_bbs_dec f.blockIdx).1 h_bb
      have h_em_err :
          Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
            (st, .error (.invalidBlock f.blockIdx)) := by
        rw [h_step_eq]
        dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [h_st_cf]; dsimp only
        rw [h_mf_loc]; dsimp only
        rw [h_mframe_bb f.blockIdx, h_rbb_none]; rfl
      rw [evalRefStep_of_err rp c rs st (.invalidBlock f.blockIdx) .unsupported h_lt
        rfl h_em_err]
      dsimp only [evalStep]
      rw [hs]; dsimp only; rw [h_body]; dsimp only; rw [h_bb]; rfl
    | some bb =>
      let ⟨rbb, h_rbb, h_rbb_dec⟩ := (mapOption_getElem? h_bbs_dec f.blockIdx).2 bb h_bb
      let ⟨h_stmts_dec, h_term_dec, _⟩ := decodeBasicBlock_inv h_rbb_dec
      have h_mb :
          (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals
            cache).body.basicBlocks[f.blockIdx]? =
            some (toMiriBasicBlock rp.types rbb) := by
        rw [h_mframe_bb f.blockIdx, h_rbb]; rfl
      have h_mstmt : ∀ (si : Nat),
          (toMiriBasicBlock rp.types rbb).statements[si]? =
            (MirSemantics.getElem? rbb.statements si).map (toMiriStatement rp.types) := by
        intro si
        dsimp only [toMiriBasicBlock]
        rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map]
      cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx with
      | some stmt =>
        let ⟨rstmt, h_rstmt, h_rstmt_dec⟩ :=
          (mapOption_getElem? h_stmts_dec f.stmtIdx).2 stmt h_st
        have h_evS := step_evalStatement_ref_eq rp c ctx rbody body f
          cache mem ctrl s.callerMem s.mem rstmt stmt h_bdec h_c_len
          (Or.inr (assignTypesValid_stmt h_av h_bb h_st))
          h_arg h_supp h_inv h_rstmt_dec
          (fun dst src srcTy ety dstTy h_st_eq =>
            discriminantTypesValid_stmt h_dv h_bb (by rw [← h_st_eq]; exact h_st) src srcTy ety dstTy rfl)
          (fun dst opnd castTy dstTy h_st_eq =>
            castTypesValid_stmt h_cv h_bb (by rw [← h_st_eq]; exact h_st) opnd castTy dstTy rfl)
        have h_step_stmt_err :
            ∀ (err : Miri.Interpreter.StepError) (st₁ : MiriStepState),
              Miri.Interpreter.Step.evalStatement
                  (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                  c (toMiriStatement rp.types rstmt) st = (st₁, .error err) →
              Miri.Interpreter.Step.step
                  (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                  c st = (st₁, .error err) := by
          intro err st₁ h_ev_err
          dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
          rw [h_st_cf]; dsimp only
          rw [h_mf_loc]; dsimp only
          rw [h_mb]; dsimp only
          rw [h_mstmt f.stmtIdx, h_rstmt]; dsimp only [Option.map]
          rw [h_ev_err]
        have h_step_stmt_ok :
            ∀ (slots' : List LocalSlot) (cache' : List Bool),
              Miri.Interpreter.Step.evalStatement
                  (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                  c (toMiriStatement rp.types rstmt) st =
                (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem, .ok ()) →
              Miri.Interpreter.Step.step
                  (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                  c st =
                (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals slots' cache' mem ctrl s.callerMem, .ok true) := by
          intro slots' cache' h_ev_ok
          dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
          rw [h_st_cf]; dsimp only
          rw [h_mf_loc]; dsimp only
          rw [h_mb]; dsimp only
          rw [h_mstmt f.stmtIdx, h_rstmt]; dsimp only [Option.map]
          rw [h_ev_ok]; dsimp only
          rw [show (st.stack.frames.size - 1 !=
              (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack.frames.size - 1) = false from by
            dsimp only [st, mkGenSimState, mkRefMiriStackState]
            rw [Array.size_push, Array.size_push]
            simp]
          rw [ite_false_eq]
          rw [show (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack.currentFrame? =
              some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache') from by
            dsimp only [mkGenSimState, mkRefMiriStackState]
            exact stack_currentFrame?_push _ _]
          dsimp only [mkGenSimFrame]
          rw [show ctx.locOverride = none from rfl]
          dsimp only
          have h_lt_sz :
              (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack.frames.size - 1 <
              (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack.frames.size := by
            dsimp only [mkGenSimState, mkRefMiriStackState]
            rw [Array.size_push]
            exact Nat.lt_succ_self _
          rw [dite_eq_left_of_eq_true (eq_true h_lt_sz)]
          change ({ stack := _, machine := _ }, Except.ok true) =
            (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals slots' cache' mem ctrl s.callerMem, Except.ok true)
          exact congrArg
            (fun frs =>
              (({ stack := { (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).stack with frames := frs },
                  machine := (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals slots' cache' mem ctrl s.callerMem).machine } :
                  MiriStepState),
               Except.ok true))
            (array_set_push_last _ _ _ h_lt_sz)
        have h_evalStep_stmt :
            evalStep p c s = attachCallers (caller :: rest) (evalStatement body f s.mem s.callerMem stmt) := by
          dsimp only [evalStep]
          rw [hs]; dsimp only; rw [h_body]; dsimp only; rw [h_bb]; dsimp only; rw [h_st]
        rw [h_evalStep_stmt]
        cases h_es : evalStatement body f s.mem s.callerMem stmt with
        | fault k =>
          rw [h_es] at h_evS
          let ⟨err, st', h_err, h_fk⟩ := h_evS
          have h_em_err :
              Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
            rw [h_step_eq, h_step_stmt_err err st' h_err]
          rw [evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
        | done _ => rw [h_es] at h_evS; exact False.elim h_evS
        | step s' =>
          rw [h_es] at h_evS
          let ⟨slots', h_s'_eq, h_ok_s⟩ := h_evS
          subst h_s'_eq
          have h_inv' : SlotsMatchTys body.locals slots' := by
            let ⟨w', hw', _, h_w, _⟩ := evalStatement_step_inv h_bb h_st h_inv h_es
            injection hw' with h_fs
            injection h_fs with h_feq
            subst h_feq
            exact h_w
          have h_em_ok :
              Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals
                  slots' (stmtCacheTouch stmt cache) mem ctrl s.callerMem, .ok true) := by
            rw [h_step_eq, h_step_stmt_ok slots' (stmtCacheTouch stmt cache) h_ok_s]; rfl
          have h_nc : nextRefControlForStep body f ctrl = ctrl := by
            dsimp only [nextRefControlForStep]
            rw [h_bb]; dsimp only; rw [h_st]
          dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome, attachCallers]
          rw [h_lt, ite_not_true_eq, h_em_ok]
          change (if (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals
                slots' (stmtCacheTouch stmt cache) mem ctrl s.callerMem).stack.frames.isEmpty then _
              else _) = _
          have h_ne_emp : (mkGenSimState rp ctx rbody f.blockIdx (f.stmtIdx + 1) body.locals
              slots' (stmtCacheTouch stmt cache) mem ctrl s.callerMem).stack.frames.isEmpty = false := by
            dsimp only [mkGenSimState, mkRefMiriStackState]
            exact array_isEmpty_push_false _ _
          rw [h_ne_emp, ite_false_eq]
          rw [h_miri_eq]
          dsimp only [st, mkGenSimState]
          let ⟨th, h_th, h_trel⟩ := mkRefMiriStackState_activeThread?
            (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
            ctx.topRel? mem ctrl s.callerMem
          rw [h_th]; dsimp only; rw [h_trel]
          rw [show (mkRefMiriStackState (ctx.below.push
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem).machine.memory = mem from rfl]
          rw [show (mkRefMiriStackState (ctx.below.push
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem).machine.user.control = ctrl from rfl]
          rw [h_nc]
          dsimp only [liftStackStep, List.cons_append, List.nil_append]
          rw [show (mkRefMiriStackState (ctx.below.push
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem).stack.frames.size = rest.length + 2 from by
            dsimp only [mkRefMiriStackState]
            rw [Array.size_push]; change below.size + 1 = rest.length + 2; rw [h_below_sz]]
          rw [show (Nat.beq (rest.length + 2) (rest.length + 2)) = true from Nat.beq_refl _, ite_true_eq]
          rw [show (mkRefMiriStackState (ctx.below.push
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem).stack.frames.back? =
              some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) from
            array_back?_push _ _]
          dsimp only
          rw [show (mkRefMiriStackState (ctx.below.push
              (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem).stack.frames.pop = ctx.below from
            array_pop_push_eq _ _]
          have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types (stepTouchesLocal body f)
            0 body.locals slots' f.locals cache
            (SlotsMatchTys.length_eq h_inv').symm
            ((SlotsMatchTys.length_eq h_inv').trans (SlotsMatchTys.length_eq h_inv).symm)
            ((SlotsMatchTys.length_eq h_inv).trans h_c_len.symm)
          rw [updateCacheLoop_stepTouchesLocal_stmt body f bb stmt h_bb h_st cache] at h_upd
          rw [show (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).locals.toList =
              liftLocalsCached rp.types body.locals f.locals cache from rfl, h_upd]
          rfl
      | none =>
        have h_rstmt_none : MirSemantics.getElem? rbb.statements f.stmtIdx = none :=
          (mapOption_getElem? h_stmts_dec f.stmtIdx).1 h_st
        have h_le : f.stmtIdx ≤ bb.statements.length := h_pc bb h_bb
        have h_ge : bb.statements.length ≤ f.stmtIdx := mirGetElem?_ge_of_none h_st
        have h_eq_len : f.stmtIdx = bb.statements.length := Nat.le_antisymm h_le h_ge
        have h_beq_len : Nat.beq f.stmtIdx bb.statements.length = true := by
          rw [h_eq_len]; exact Nat.beq_refl _
        have h_bt :
            (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).beforeTerminator c st =
              (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache
                mem (advanceRefControl ctrl) s.callerMem, .ok ()) := by
          dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
            Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
            Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
          rw [beforeTerminator_ref_eq (st := st) h_ctrl rfl]
          rfl
        have h_step_term :
            Miri.Interpreter.Step.step
                (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                c st =
              let r := (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).terminator
                c (toMiriTerminator rp.types rbb.terminator)
                (mkGenSimState rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache
                  mem (advanceRefControl ctrl) s.callerMem)
              (r.1, r.2.map fun _ => true) := by
          dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
          rw [h_st_cf]; dsimp only
          rw [h_mf_loc]; dsimp only
          rw [h_mb]; dsimp only
          rw [h_mstmt f.stmtIdx, h_rstmt_none]; dsimp only [Option.map]
          change (match ((Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).beforeTerminator c st).snd with
            | Except.error error =>
              (((Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).beforeTerminator c st).fst,
                Except.error error)
            | Except.ok () =>
              let r := (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).terminator c
                (toMiriBasicBlock rp.types rbb).terminator
                ((Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits).beforeTerminator c st).fst
              (r.1, r.2.map fun _ => true)) = _
          rw [h_bt]
          rfl
        have h_nc : nextRefControlForStep body f ctrl = advanceRefControl ctrl := by
          dsimp only [nextRefControlForStep]
          rw [h_bb]; dsimp only; rw [h_st]; dsimp only; rw [h_beq_len, ite_true_eq]
        have h_evalStep_term :
            evalStep p c s =
              match bb.terminator with
              | .call callee args dst target unwind =>
                match MirSemantics.getElem? p.bodies callee with
                | none => .fault .unsupported
                | some calleeBody =>
                  evalCallTerminator body bb f (caller :: rest) s.mem s.callerMem
                    callee none calleeBody args dst target unwind
              | .sysrootCall op args dst target unwind =>
                evalCallTerminator body bb f (caller :: rest) s.mem s.callerMem
                  0 (some op) (sysrootNumBody op) args dst target unwind
              | .return_ => evalNonRootReturn p body bb f caller rest s.mem s.callerMem
              | _ => attachCallers (caller :: rest) (evalTerminator body bb f s.mem s.callerMem
                  rp.panicStrategy rp.hasLocalPanicHandler) := by
          dsimp only [evalStep]
          rw [hs]; dsimp only; rw [h_body]; dsimp only; rw [h_bb]; dsimp only
          rw [h_st]; dsimp only; rw [h_beq_len, ite_true_eq, h_ps, h_lh]
          cases bb.terminator <;> rfl
        rw [h_evalStep_term]
        cases h_rterm : rbb.terminator with
        | call callee rargs rdst tgt unwind =>
          rw [h_rterm] at h_term_dec
          let ⟨args, dst', h_dargs, h_ddst, h_bterm⟩ := decodeTerminator_call_inv h_term_dec
          rw [h_bterm]
          dsimp only
          have h_calls_bb := list_all_mirGetElem? h_calls h_bb
          rw [h_bterm] at h_calls_bb
          dsimp only at h_calls_bb
          cases h_cbody : MirSemantics.getElem? p.bodies callee with
          | none => rw [h_cbody] at h_calls_bb; cases h_calls_bb
          | some nextCalleeBody =>
            rw [h_cbody] at h_calls_bb
            dsimp only at h_calls_bb
            dsimp only
            let ⟨calleeRbody, h_rcbody, h_cbdec⟩ :=
              (mapOption_getElem? (decodeProg_inv h_dec).2.2.2.2 callee).2 nextCalleeBody h_cbody
            have h_any : bodyHasAnyCall body = true :=
              bodyHasAnyCall_of_call body f.blockIdx bb h_bb callee args dst' tgt unwind h_bterm
            have h_all_st := h_all_static
            dsimp only [allCallBodiesStaticAdmitted] at h_all_st
            rw [h_any, ite_true_eq, Bool.and_eq_true] at h_all_st
            have h_csat : callBodyStaticAdmitted p nextCalleeBody = true :=
              all_getElem?_eq_true h_all_st.2 h_cbody
            have h_evC := callTerminator_crate_ref_eq rp p c ctx rbody calleeRbody body nextCalleeBody
              rbb bb f (caller :: rest) cache mem (advanceRefControl ctrl) s.callerMem s.mem
              callee rargs args rdst dst' tgt unwind
              h_dec h_bdec h_rbb h_rbb_dec h_rterm h_c_len h_tr_ctx rfl h_inv
              h_rcbody h_cbdec (bool_and_split h_calls_bb).2 h_dargs h_ddst h_csat
            dsimp only at h_evC
            dsimp only [st] at h_step_term
            rw [h_rterm] at h_step_term
            cases h_ec : evalCallTerminator body bb f (caller :: rest) s.mem s.callerMem
                callee none nextCalleeBody args dst' tgt unwind with
            | fault k =>
              rw [h_ec] at h_evC
              let ⟨err, st', h_err, h_fk⟩ := h_evC
              rw [h_rterm] at h_err
              rw [h_err] at h_step_term
              have h_em_err :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
                rw [h_step_eq, h_step_term]; rfl
              rw [evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
            | done _ => rw [h_ec] at h_evC; exact False.elim h_evC
            | step s' =>
              rw [h_ec] at h_evC
              let ⟨callerLocals', callerCache', h_cc_eq, h_cc_len, h_cl_inv, h_dst_true,
                dstTy', retTy', calleeLocals, argVals, h_dst_ty', h_dst_supp', h_cret_ty', h_beq',
                _, h_s'_eq, h_res_eq⟩ := h_evC
              subst h_s'_eq
              rw [h_rterm] at h_res_eq
              rw [h_res_eq] at h_step_term
              have h_em_ok :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    (mkGenSimState rp (SimFrameCtx.call rp.types
                        (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'))
                        (some (ctx.below.size + 1)) (fnTagForCrate callee) ctx.below.size dst'.localId dstTy' tgt)
                      calleeRbody 0 0 nextCalleeBody.locals calleeLocals
                      (calleeInitCacheLoop nextCalleeBody.argumentCount 0 nextCalleeBody.locals)
                      mem (advanceRefControl ctrl) s.callerMem, .ok true) := by
                rw [h_step_eq, h_step_term]; rfl
              dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
              rw [h_lt, ite_not_true_eq, h_em_ok]
              change (if (mkGenSimState _ _ _ _ _ _ _ _ _ _ _).stack.frames.isEmpty then _ else _) = _
              have h_ne_emp : (mkGenSimState rp (SimFrameCtx.call rp.types
                    (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'))
                    (some (ctx.below.size + 1)) (fnTagForCrate callee) ctx.below.size dst'.localId dstTy' tgt)
                  calleeRbody 0 0 nextCalleeBody.locals calleeLocals
                  (calleeInitCacheLoop nextCalleeBody.argumentCount 0 nextCalleeBody.locals)
                  mem (advanceRefControl ctrl) s.callerMem).stack.frames.isEmpty = false := by
                dsimp only [mkGenSimState, mkRefMiriStackState]
                exact array_isEmpty_push_false _ _
              rw [h_ne_emp, ite_false_eq]
              rw [h_miri_eq]
              dsimp only [st, mkGenSimState]
              rw [show nextRefControlForStep body f (mkRefMiriStackState
                  (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).machine.user.control = advanceRefControl ctrl from h_nc]
              let ⟨th, h_th, _⟩ := mkRefMiriStackState_activeThread?
                (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem
              rw [h_th]
              dsimp only [liftStackStep]
              have h_osz : (mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames.size = rest.length + 2 := by
                dsimp only [mkRefMiriStackState]
                rw [Array.size_push]; change below.size + 1 = rest.length + 2; rw [h_below_sz]
              rw [h_osz]
              have h_beq_false : Nat.beq (List.length (caller :: rest) + 2) (rest.length + 2) = false := by
                dsimp only [List.length_cons]
                rw [Nat.add_right_comm rest.length 1 2]
                exact nat_beq_false_of_ne (Nat.succ_ne_self _)
              have h_beq_true : Nat.beq (List.length (caller :: rest) + 2) (rest.length + 2 + 1) = true := by
                dsimp only [List.length_cons]
                exact Nat.beq_refl _
              rw [h_beq_false, ite_false_eq, h_beq_true, ite_true_eq]
              rw [show (mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames.back? =
                  some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) from
                array_back?_push _ _]
              dsimp only
              rw [refResolveCalleeBody_crate rp callee calleeRbody nextCalleeBody.locals h_rcbody (decodeBody_locals h_cbdec)]
              dsimp only
              rw [decodeBody_argumentCount h_cbdec]
              rw [calleeTys_head_eq_of_beq h_cret_ty' h_beq']
              have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types (callTouchesCallerLocal body f)
                0 body.locals callerLocals' f.locals cache
                (SlotsMatchTys.length_eq h_cl_inv).symm
                ((SlotsMatchTys.length_eq h_cl_inv).trans (SlotsMatchTys.length_eq h_inv).symm)
                ((SlotsMatchTys.length_eq h_inv).trans h_c_len.symm)
              rw [updateCacheLoop_callTouchesCallerLocal body f bb args dst' cache h_bb
                (Or.inl ⟨callee, tgt, unwind, h_bterm⟩), ← h_cc_eq] at h_upd
              rw [show (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).locals.toList =
                  liftLocalsCached rp.types body.locals f.locals cache from rfl, h_upd]
              rw [show (mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames.pop = ctx.below from
                array_pop_push_eq _ _]
              rw [show rest.length + 2 - 1 = ctx.below.size from by
                change rest.length + 2 - 1 = below.size; rw [h_below_sz]; exact Nat.add_sub_cancel (rest.length + 1) 1]
              rw [show rest.length + 2 = ctx.below.size + 1 from by change rest.length + 2 = below.size + 1; rw [h_below_sz]]
              rfl
        | sysrootCall op rargs rdst tgt unwind =>
          rw [h_rterm] at h_term_dec
          let ⟨args, dst', h_dargs, h_ddst, h_bterm⟩ := decodeTerminator_sysrootCall_inv h_term_dec
          rw [h_bterm]
          dsimp only
          have h_calls_bb := list_all_mirGetElem? h_calls h_bb
          rw [h_bterm] at h_calls_bb
          dsimp only at h_calls_bb
          have h_evC := callTerminator_sysroot_ref_eq rp c ctx rbody body
            rbb bb f (caller :: rest) cache mem (advanceRefControl ctrl) s.callerMem s.mem
            op rargs args rdst dst' tgt unwind
            h_bdec h_rbb h_rbb_dec h_rterm h_c_len h_tr_ctx rfl h_inv
            h_calls_bb h_dargs h_ddst
          dsimp only at h_evC
          dsimp only [st] at h_step_term
          rw [h_rterm] at h_step_term
          cases h_ec : evalCallTerminator body bb f (caller :: rest) s.mem s.callerMem
              0 (some op) (sysrootNumBody op) args dst' tgt unwind with
          | fault k =>
            rw [h_ec] at h_evC
            let ⟨err, st', h_err, h_fk⟩ := h_evC
            rw [h_rterm] at h_err
            rw [h_err] at h_step_term
            have h_em_err :
                Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                  ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
              rw [h_step_eq, h_step_term]; rfl
            rw [evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
          | done _ => rw [h_ec] at h_evC; exact False.elim h_evC
          | step s' =>
            rw [h_ec] at h_evC
            let ⟨callerLocals', callerCache', h_cc_eq, h_cc_len, h_cl_inv, h_dst_true,
              dstTy', retTy', calleeLocals, argVals, h_dst_ty', h_dst_supp', h_cret_ty', h_beq',
              _, h_s'_eq, h_res_eq⟩ := h_evC
            subst h_s'_eq
            rw [h_rterm] at h_res_eq
            rw [h_res_eq] at h_step_term
            have h_em_ok :
                Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                  (mkGenSimState rp (SimFrameCtx.call rp.types
                      (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'))
                      (some (ctx.below.size + 1)) (fnTagForSysroot op) ctx.below.size dst'.localId dstTy' tgt)
                    (sysrootNumRefBody rp.types op) 0 0 (sysrootNumBody op).locals calleeLocals
                    (calleeInitCacheLoop (sysrootNumBody op).argumentCount 0 (sysrootNumBody op).locals)
                    mem (advanceRefControl ctrl) s.callerMem, .ok true) := by
              rw [h_step_eq, h_step_term]; rfl
            dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
            rw [h_lt, ite_not_true_eq, h_em_ok]
            change (if (mkGenSimState _ _ _ _ _ _ _ _ _ _ _).stack.frames.isEmpty then _ else _) = _
            have h_ne_emp : (mkGenSimState rp (SimFrameCtx.call rp.types
                  (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals callerLocals' callerCache'))
                  (some (ctx.below.size + 1)) (fnTagForSysroot op) ctx.below.size dst'.localId dstTy' tgt)
                (sysrootNumRefBody rp.types op) 0 0 (sysrootNumBody op).locals calleeLocals
                (calleeInitCacheLoop (sysrootNumBody op).argumentCount 0 (sysrootNumBody op).locals)
                mem (advanceRefControl ctrl) s.callerMem).stack.frames.isEmpty = false := by
              dsimp only [mkGenSimState, mkRefMiriStackState]
              exact array_isEmpty_push_false _ _
            rw [h_ne_emp, ite_false_eq]
            rw [h_miri_eq]
            dsimp only [st, mkGenSimState]
            rw [show nextRefControlForStep body f (mkRefMiriStackState
                (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).machine.user.control = advanceRefControl ctrl from h_nc]
            let ⟨th, h_th, _⟩ := mkRefMiriStackState_activeThread?
              (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem
            rw [h_th]
            dsimp only [liftStackStep]
            have h_osz : (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).stack.frames.size = rest.length + 2 := by
              dsimp only [mkRefMiriStackState]
              rw [Array.size_push]; change below.size + 1 = rest.length + 2; rw [h_below_sz]
            rw [h_osz]
            have h_beq_false : Nat.beq (List.length (caller :: rest) + 2) (rest.length + 2) = false := by
              dsimp only [List.length_cons]
              rw [Nat.add_right_comm rest.length 1 2]
              exact nat_beq_false_of_ne (Nat.succ_ne_self _)
            have h_beq_true : Nat.beq (List.length (caller :: rest) + 2) (rest.length + 2 + 1) = true := by
              dsimp only [List.length_cons]
              exact Nat.beq_refl _
            rw [h_beq_false, ite_false_eq, h_beq_true, ite_true_eq]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).stack.frames.back? =
                some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) from
              array_back?_push _ _]
            dsimp only
            rw [refResolveCalleeBody_sysroot]
            dsimp only
            rw [show (sysrootNumRefBody rp.types op).argumentCount = (sysrootNumBody op).argumentCount from rfl]
            rw [show ([MirTy.int op.width op.signed, MirTy.int op.width op.signed, MirTy.int op.width op.signed][0]?.getD MirTy.unit) = dstTy' from
              calleeTys_head_eq_of_beq h_cret_ty' h_beq']
            have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types (callTouchesCallerLocal body f)
              0 body.locals callerLocals' f.locals cache
              (SlotsMatchTys.length_eq h_cl_inv).symm
              ((SlotsMatchTys.length_eq h_cl_inv).trans (SlotsMatchTys.length_eq h_inv).symm)
              ((SlotsMatchTys.length_eq h_inv).trans h_c_len.symm)
            rw [updateCacheLoop_callTouchesCallerLocal body f bb args dst' cache h_bb
              (Or.inr ⟨op, tgt, unwind, h_bterm⟩), ← h_cc_eq] at h_upd
            rw [show (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).locals.toList =
                liftLocalsCached rp.types body.locals f.locals cache from rfl, h_upd]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).stack.frames.pop = ctx.below from
              array_pop_push_eq _ _]
            rw [show rest.length + 2 - 1 = ctx.below.size from by
              change rest.length + 2 - 1 = below.size; rw [h_below_sz]; exact Nat.add_sub_cancel (rest.length + 1) 1]
            rw [show rest.length + 2 = ctx.below.size + 1 from by change rest.length + 2 = below.size + 1; rw [h_below_sz]]
            rfl
        | return_ =>
          rw [h_rterm] at h_term_dec
          injection h_term_dec with h_bt_eq
          rw [← h_bt_eq]
          dsimp only
          have h_eq_ty : MirTy.beq retTy_sim dstTy = true := by
            rw [← MirTy.eq_of_beq h_beq]; exact MirTy.beq_refl _
          cases h_caller_sim with
          | root h_c_defId h_c_sro h_c_rdst h_c_rtgt h_c_fs =>
            let ⟨cBodySim, callerRbody, callerCache, h_c_bs, h_c_rbs, h_c_bdec, _, _, _, _,
              _, _, _, h_c_supp, h_c_inv, _, h_c_crep, h_c_rf⟩ := h_c_fs
            have h_c_act : activeFrameBody p caller = some cBodySim := by
              dsimp only [activeFrameBody]; rw [h_c_sro]; exact h_c_bs
            rw [h_caller_b] at h_c_act; injection h_c_act with hc_eq; subst hc_eq
            let callerCtx : SimFrameCtx :=
              { SimFrameCtx.root caller.defId rs.retPlace with topRel? := some 0 }
            have h_rcaller_eq : rcaller = mkGenSimFrame rp callerCtx callerRbody
                caller.blockIdx caller.stmtIdx callerBody.locals caller.locals callerCache :=
              h_c_rf
            have h_dst_c : MirSemantics.getElem? callerCache dst.localId = some true := by
              rw [h_c_crep]; exact getElem?_replicate_true h_dst_ty
            have h_ctx_below : ctx.below = callerCtx.below.push rcaller := rfl
            have h_ctx_tr : ctx.topRel? = some ctx.below.size := by
              dsimp only [ctx]; rw [h_topRel_eq]; rfl
            have h_ctx_rp : ctx.retPlace = .frameLocal callerCtx.below.size dst.localId none
                (refLocalLayoutForTy rp.types dstTy)
                (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0) := rfl
            have h_evR := nonRootReturn_ref_eq rp p c ctx callerCtx rbody callerRbody
              body callerBody rbb bb f caller retTy_sim dstTy cache callerCache rcaller []
              mem (advanceRefControl ctrl) s.callerMem s.mem dst
              h_bdec h_c_bdec h_c_len h_rbb h_rbb_dec h_rterm h_cret_ty h_dst_ty h_eq_ty
              h_dst_c h_ret_dst h_dst_proj h_caller_b h_supp h_c_supp h_inv h_c_inv
              h_rcaller_eq h_ctx_below h_ctx_tr rfl h_ctx_rp rfl rfl
            dsimp only at h_evR
            dsimp only [st] at h_step_term
            rw [h_rterm] at h_step_term
            cases h_enr : evalNonRootReturn p body bb f caller [] s.mem s.callerMem with
            | fault k =>
              rw [h_enr] at h_evR
              let ⟨err, st', h_err, h_fk⟩ := h_evR
              rw [h_err] at h_step_term
              have h_em_err :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
                rw [h_step_eq, h_step_term]; rfl
              rw [evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
            | done _ => rw [h_enr] at h_evR; exact False.elim h_evR
            | step s' =>
              rw [h_enr] at h_evR
              let ⟨tgt, callerLocals', h_s'_eq, h_res_eq⟩ := h_evR
              subst h_s'_eq
              have h_cinv' : SlotsMatchTys callerBody.locals callerLocals' :=
                evalNonRootReturn_step_inv h_caller_b h_c_inv h_enr
              rw [h_res_eq] at h_step_term
              have h_em_ok :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    (mkGenSimState rp { callerCtx with topRel? := some callerCtx.below.size }
                      callerRbody tgt 0 callerBody.locals callerLocals' callerCache
                      mem (advanceRefControl ctrl) s.callerMem, .ok true) := by
                rw [h_step_eq, h_step_term]; rfl
              dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
              rw [h_lt, ite_not_true_eq, h_em_ok]
              change (if (mkGenSimState _ _ _ _ _ _ _ _ _ _ _).stack.frames.isEmpty then _ else _) = _
              rw [show (mkGenSimState rp { callerCtx with topRel? := some callerCtx.below.size }
                    callerRbody tgt 0 callerBody.locals callerLocals' callerCache
                    mem (advanceRefControl ctrl) s.callerMem).stack.frames.isEmpty = false from rfl,
                ite_false_eq]
              rw [h_miri_eq]
              dsimp only [st, mkGenSimState]
              rw [show nextRefControlForStep body f (mkRefMiriStackState
                  (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).machine.user.control = advanceRefControl ctrl from h_nc]
              let ⟨th, h_th, _⟩ := mkRefMiriStackState_activeThread?
                (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem
              rw [h_th]
              dsimp only [liftStackStep]
              rw [show (mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames.size = 2 from rfl,
                show (Nat.beq 2 1) = false from rfl, ite_false_eq,
                show (Nat.beq 2 2) = true from rfl, ite_true_eq]
              rw [show (mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames[0]? = some rcaller from rfl,
                h_ret_dst]
              dsimp only
              rw [h_rcaller_eq]
              dsimp only [mkGenSimFrame]
              rw [toMiriBody_locals_filterMap_resolveTy h_c_bdec]
              have h_c_len' : callerCache.length = callerBody.locals.length := by
                rw [h_c_crep, List.length_replicate]
              rw [updateMiriLocalsLoop_nonRootReturn rp.types callerBody caller.locals callerLocals'
                callerCache dst.localId h_c_inv h_cinv' h_c_len' h_dst_c]
              rfl
          | @push _ grandCaller grandRest _ rGrandCaller rGrandRest grandBody callerBody_sim
              cDst cDstTy cRetTy_sim
              h_gc_sim h_gc_b h_c_b h_c_rdst h_c_dst_proj h_c_dst_ty h_c_dst_supp
              h_c_cret_ty h_c_beq h_c_ret_tgt h_c_rc_ls h_c_cf =>
            let ⟨cBodySim, callerRbody, callerCache, callerFnTag, h_c_bs, h_c_rbs, h_c_bdec,
              h_c_fnTag, h_c_crate_body, h_c_sys_defId, _, _, _, _, _, _, _, _, h_c_supp,
              h_c_inv, _, h_caller_c_len, h_c_rf⟩ := h_c_cf
            rw [h_caller_b] at h_c_bs; injection h_c_bs with hcb_eq; subst hcb_eq
            rw [h_caller_b] at h_c_b; injection h_c_b with hcb2_eq; subst hcb2_eq
            subst h_c_fnTag
            have h_rgr_len : rGrandRest.length = grandRest.length := by
              have h_l := framesSimInv_length_eq h_gc_sim
              simp [List.length_cons] at h_l
              exact h_l
            let callerCtx : SimFrameCtx := SimFrameCtx.call rp.types
              ⟨(rGrandCaller :: rGrandRest).reverse⟩ (some (grandRest.length + 1))
              (match caller.sysrootOp? with | some op => fnTagForSysroot op | none => fnTagForCrate caller.defId)
              grandRest.length cDst.localId cDstTy caller.retTarget?
            have h_cbelow_sz : callerCtx.below.size = grandRest.length + 1 := by
              dsimp only [callerCtx, SimFrameCtx.call]
              simp [List.length_reverse, List.length_cons, h_rgr_len]
            have h_rcaller_eq : rcaller = mkGenSimFrame rp callerCtx callerRbody
                caller.blockIdx caller.stmtIdx callerBody.locals caller.locals callerCache :=
              h_c_rf
            have h_dst_c : MirSemantics.getElem? callerCache dst.localId = some true := by
              let ⟨ls, h_rc_get, h_rc_is⟩ := h_rc_ls
              rw [h_rcaller_eq] at h_rc_get
              dsimp only [mkGenSimFrame, mkRefMiriCallFrame] at h_rc_get
              rw [array_getElem?_eq_mirGetElem?] at h_rc_get
              exact getElem?_liftLocalsCached_layout_isSome rp.types callerBody.locals caller.locals
                callerCache dst.localId (SlotsMatchTys.length_eq h_c_inv).symm
                ((SlotsMatchTys.length_eq h_c_inv).trans h_caller_c_len.symm) h_rc_get h_rc_is
            have h_ctx_below : ctx.below = callerCtx.below.push rcaller := by
              change (⟨(rcaller :: rGrandCaller :: rGrandRest).reverse⟩ : Array _) =
                (⟨(rGrandCaller :: rGrandRest).reverse⟩ : Array _).push rcaller
              exact array_reverse_cons_push _ _
            have h_ctx_tr : ctx.topRel? = some ctx.below.size := by
              dsimp only [ctx]; rw [h_topRel_eq]; rfl
            have h_ctx_rp : ctx.retPlace = .frameLocal callerCtx.below.size dst.localId none
                (refLocalLayoutForTy rp.types dstTy)
                (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0) := by
              dsimp only [ctx, SimFrameCtx.call]
              rw [h_cbelow_sz]
              rfl
            have h_evR := nonRootReturn_ref_eq rp p c ctx callerCtx rbody callerRbody
              body callerBody rbb bb f caller retTy_sim dstTy cache callerCache rcaller
              (grandCaller :: grandRest) mem (advanceRefControl ctrl) s.callerMem s.mem dst
              h_bdec h_c_bdec h_c_len h_rbb h_rbb_dec h_rterm h_cret_ty h_dst_ty h_eq_ty
              h_dst_c h_ret_dst h_dst_proj h_caller_b h_supp h_c_supp h_inv h_c_inv
              h_rcaller_eq h_ctx_below h_ctx_tr rfl h_ctx_rp rfl rfl
            dsimp only at h_evR
            dsimp only [st] at h_step_term
            rw [h_rterm] at h_step_term
            cases h_enr : evalNonRootReturn p body bb f caller (grandCaller :: grandRest) s.mem s.callerMem with
            | fault k =>
              rw [h_enr] at h_evR
              let ⟨err, st', h_err, h_fk⟩ := h_evR
              rw [h_err] at h_step_term
              have h_em_err :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
                rw [h_step_eq, h_step_term]; rfl
              rw [evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
            | done _ => rw [h_enr] at h_evR; exact False.elim h_evR
            | step s' =>
              rw [h_enr] at h_evR
              let ⟨tgt, callerLocals', h_s'_eq, h_res_eq⟩ := h_evR
              subst h_s'_eq
              have h_cinv' : SlotsMatchTys callerBody.locals callerLocals' :=
                evalNonRootReturn_step_inv h_caller_b h_c_inv h_enr
              rw [h_res_eq] at h_step_term
              have h_em_ok :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    (mkGenSimState rp { callerCtx with topRel? := some callerCtx.below.size }
                      callerRbody tgt 0 callerBody.locals callerLocals' callerCache
                      mem (advanceRefControl ctrl) s.callerMem, .ok true) := by
                rw [h_step_eq, h_step_term]; rfl
              dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
              rw [h_lt, ite_not_true_eq, h_em_ok]
              change (if (mkGenSimState _ _ _ _ _ _ _ _ _ _ _).stack.frames.isEmpty then _ else _) = _
              have h_ne_emp : (mkGenSimState rp { callerCtx with topRel? := some callerCtx.below.size }
                    callerRbody tgt 0 callerBody.locals callerLocals' callerCache
                    mem (advanceRefControl ctrl) s.callerMem).stack.frames.isEmpty = false := by
                dsimp only [mkGenSimState, mkRefMiriStackState]
                exact array_isEmpty_push_false _ _
              rw [h_ne_emp, ite_false_eq]
              rw [h_miri_eq]
              dsimp only [st, mkGenSimState]
              rw [show nextRefControlForStep body f (mkRefMiriStackState
                  (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).machine.user.control = advanceRefControl ctrl from h_nc]
              let ⟨th, h_th, _⟩ := mkRefMiriStackState_activeThread?
                (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem
              rw [h_th]
              dsimp only [liftStackStep]
              have h_osz : (mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames.size = grandRest.length + 3 := by
                dsimp only [mkRefMiriStackState]
                rw [Array.size_push]; change below.size + 1 = grandRest.length + 3; rw [h_below_sz]; rfl
              rw [h_osz]
              have h_beq_f1 : Nat.beq (List.length grandRest + 2) (grandRest.length + 3) = false :=
                nat_beq_false_of_ne (Nat.ne_of_lt (Nat.lt_succ_self _))
              have h_beq_f2 : Nat.beq (List.length grandRest + 2) (grandRest.length + 3 + 1) = false :=
                nat_beq_false_of_ne (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)))
              have h_beq_t : Nat.beq (List.length grandRest + 2 + 1) (grandRest.length + 3) = true :=
                Nat.beq_refl _
              rw [h_beq_f1, ite_false_eq, h_beq_f2, ite_false_eq, h_beq_t, ite_true_eq]
              have h_pop1 : (mkRefMiriStackState (ctx.below.push
                  (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                  ctx.topRel? mem ctrl s.callerMem).stack.frames.pop = callerCtx.below.push rcaller := by
                change (ctx.below.push _).pop = callerCtx.below.push rcaller
                rw [array_pop_push_eq, h_ctx_below]
              rw [h_pop1, array_back?_push, h_ret_dst]
              dsimp only
              have h_c_res :
                  refResolveCalleeBody rp (match caller.sysrootOp? with
                    | some op => fnTagForSysroot op | none => fnTagForCrate caller.defId) =
                    some (callerRbody, callerBody.locals) := by
                cases h_csro : caller.sysrootOp? with
                | some op =>
                  dsimp only [activeFrameBody] at h_caller_b
                  dsimp only [activeRefFrameBody] at h_c_rbs
                  rw [h_csro] at h_caller_b h_c_rbs
                  injection h_caller_b with h_cb_sys
                  injection h_c_rbs with h_crb_sys
                  subst h_cb_sys h_crb_sys
                  exact refResolveCalleeBody_sysroot rp op
                | none =>
                  have h_get_cb := h_c_crate_body h_csro
                  dsimp only [activeRefFrameBody] at h_c_rbs
                  rw [h_csro] at h_c_rbs
                  exact refResolveCalleeBody_crate rp caller.defId callerRbody callerBody.locals
                    h_c_rbs (decodeBody_locals h_c_bdec)
              rw [h_rcaller_eq]
              dsimp only [mkGenSimFrame, mkRefMiriCallFrame, callerCtx, SimFrameCtx.call]
              rw [h_c_res]
              dsimp only
              rw [updateMiriLocalsLoop_nonRootReturn rp.types callerBody caller.locals callerLocals'
                callerCache dst.localId h_c_inv h_cinv' h_caller_c_len h_dst_c]
              rw [array_pop_push_eq]
              rw [array_push_size_sub_one]
              rfl
        | goto _ | unreachable | unwindResume
        | switchInt _ _ | assert _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported =>
          have h_noncall :
              (∀ callee args dst tgt uw, rbb.terminator ≠ .call callee args dst tgt uw) ∧
              (∀ op args dst tgt uw, rbb.terminator ≠ .sysrootCall op args dst tgt uw) := by
            constructor
            · intro callee args dst tgt uw h_eq; rw [h_rterm] at h_eq; cases h_eq
            · intro op args dst tgt uw h_eq; rw [h_rterm] at h_eq; cases h_eq
          have h_evT := evalTerminator_ref_eq rp c ctx rbody body rbb bb f (MirTy.unit) cache
            rs.retPlace mem (advanceRefControl ctrl) s.callerMem s.mem h_bdec h_c_len h_bb h_rbb
            h_rbb_dec rfl (fun h_eq => by rw [h_rterm] at h_eq; cases h_eq) h_noncall
            h_act h_supp h_inv
          dsimp only at h_evT
          have h_bnoncall := decodeTerminator_ne_call h_noncall h_term_dec
          have h_bne_ret : bb.terminator ≠ .return_ :=
            decodeTerminator_ne_return (fun h_eq => by rw [h_rterm] at h_eq; cases h_eq) h_term_dec
          have h_rhs_ev :
              (match bb.terminator with
                | .call callee args dst target unwind =>
                  match MirSemantics.getElem? p.bodies callee with
                  | none => .fault .unsupported
                  | some calleeBody =>
                    evalCallTerminator body bb f (caller :: rest) s.mem s.callerMem callee none calleeBody args dst target unwind
                | .sysrootCall op args dst target unwind =>
                  evalCallTerminator body bb f (caller :: rest) s.mem s.callerMem 0 (some op) (sysrootNumBody op) args dst target unwind
                | .return_ => evalNonRootReturn p body bb f caller rest s.mem s.callerMem
                | _ => attachCallers (caller :: rest) (evalTerminator body bb f s.mem s.callerMem
                    rp.panicStrategy rp.hasLocalPanicHandler)) =
              attachCallers (caller :: rest) (evalTerminator body bb f s.mem s.callerMem
                rp.panicStrategy rp.hasLocalPanicHandler) := by
            cases h_rt_eq : bb.terminator with
            | return_ => exact False.elim (h_bne_ret h_rt_eq)
            | call c a d g u => exact False.elim (h_bnoncall.1 c a d g u h_rt_eq)
            | sysrootCall o a d g u => exact False.elim (h_bnoncall.2 o a d g u h_rt_eq)
            | goto _ | unreachable | unwindResume
            | switchInt _ _ | assert _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported => rfl
          rw [h_rhs_ev]
          rw [h_rterm] at h_step_term
          cases h_et : evalTerminator body bb f s.mem s.callerMem
              rp.panicStrategy rp.hasLocalPanicHandler with
          | fault k =>
            rw [h_et] at h_evT
            let ⟨err, st', h_err, h_fk⟩ := h_evT
            rw [h_rterm] at h_err
            rw [h_err] at h_step_term
            have h_em_err :
                Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                  ({ st' with machine := { st'.machine with pendingMoveDeinit := false } }, .error err) := by
              rw [h_step_eq, h_step_term]; rfl
            rw [attachCallers_fault_eq, evalRefStep_of_err rp c rs _ err k h_lt h_fk h_em_err]; rfl
          | done out =>
            rw [h_et] at h_evT
            cases out with
            | aborted cm' =>
              let ⟨st', h_err_t, h_cm'⟩ := h_evT
              rw [h_rterm] at h_err_t
              rw [h_err_t] at h_step_term
              have h_em_err :
                  Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                    ({ st' with machine := { st'.machine with pendingMoveDeinit := false } },
                     .error (.termination (.abort "panic abort"))) := by
                rw [h_step_eq, h_step_term]; rfl
              dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome, attachCallers]
              rw [h_lt, ite_not_true_eq, h_em_err]
              dsimp only
              rw [h_cm']
            | returned _ =>
              have h_ab := evalTerminator_done_aborted_of_ne_return h_bne_ret h_et
              cases h_ab
            | unwound _ => exact False.elim h_evT
          | step s' =>
            rw [h_et] at h_evT
            let ⟨tgt, slots', h_s'_eq, h_res_eq⟩ := h_evT
            subst h_s'_eq
            have h_inv' : SlotsMatchTys body.locals slots' := by
              let ⟨_, hw', _, h_w, _⟩ := evalTerminator_step_inv h_inv h_et
              injection hw' with h_fs
              injection h_fs with h_feq
              subst h_feq
              exact h_w
            rw [h_rterm] at h_res_eq
            rw [h_res_eq] at h_step_term
            have h_em_ok :
                Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                  (mkGenSimState rp ctx rbody tgt 0 body.locals
                    slots' (termCacheTouch bb.terminator cache) mem (advanceRefControl ctrl) s.callerMem, .ok true) := by
              rw [h_step_eq, h_step_term]; rfl
            dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome, attachCallers, List.cons_append, List.nil_append]
            rw [h_lt, ite_not_true_eq, h_em_ok]
            change (if (mkGenSimState _ _ _ _ _ _ _ _ _ _ _).stack.frames.isEmpty then _ else _) = _
            have h_ne_emp : (mkGenSimState rp ctx rbody tgt 0 body.locals
                slots' (termCacheTouch bb.terminator cache) mem (advanceRefControl ctrl) s.callerMem).stack.frames.isEmpty = false := by
              dsimp only [mkGenSimState, mkRefMiriStackState]
              exact array_isEmpty_push_false _ _
            rw [h_ne_emp, ite_false_eq]
            rw [h_miri_eq]
            dsimp only [st, mkGenSimState]
            let ⟨th, h_th, h_trel⟩ := mkRefMiriStackState_activeThread?
              (ctx.below.push (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
              ctx.topRel? mem ctrl s.callerMem
            rw [h_th]; dsimp only; rw [h_trel]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).machine.memory = mem from rfl]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).machine.user.control = ctrl from rfl]
            rw [h_nc]
            dsimp only [liftStackStep]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).stack.frames.size = rest.length + 2 from by
              dsimp only [mkRefMiriStackState]
              rw [Array.size_push]; change below.size + 1 = rest.length + 2; rw [h_below_sz]]
            rw [show (Nat.beq (rest.length + 2) (rest.length + 2)) = true from Nat.beq_refl _, ite_true_eq]
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).stack.frames.back? =
                some (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache) from
              array_back?_push _ _]
            dsimp only
            rw [show (mkRefMiriStackState (ctx.below.push
                (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache))
                ctx.topRel? mem ctrl s.callerMem).stack.frames.pop = ctx.below from
              array_pop_push_eq _ _]
            have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types (stepTouchesLocal body f)
              0 body.locals slots' f.locals cache
              (SlotsMatchTys.length_eq h_inv').symm
              ((SlotsMatchTys.length_eq h_inv').trans (SlotsMatchTys.length_eq h_inv).symm)
              ((SlotsMatchTys.length_eq h_inv).trans h_c_len.symm)
            rw [updateCacheLoop_stepTouchesLocal_term body f bb h_bb h_st h_beq_len cache] at h_upd
            rw [show (mkGenSimFrame rp ctx rbody f.blockIdx f.stmtIdx body.locals f.locals cache).locals.toList =
                liftLocalsCached rp.types body.locals f.locals cache from rfl, h_upd]
            rfl

/-- One $M_{\text{ref}}$ step via `Miri.Interpreter.ExecutionMachine.step` from
a simulated state computes exactly the lifted $M_{\text{anneal}}$ step. -/
theorem evalRefStep_eq_base : EvalRefStepEqClaim := by
  intro rp p s rs f callers body rbody h_dec h_sim hs h_body h_rbody h_lt c
  let ⟨rframes, retTy, mem, ctrl, topRel?, _, _, h_smem, h_ert, h_rty,
    h_init, h_ctrl, h_tr, h_miri, h_fsim⟩ := h_sim
  rw [hs] at h_fsim
  exact evalRefStep_eq_base_aux rp p s rs f callers body rbody h_dec hs h_body h_rbody h_lt c
    rframes retTy mem ctrl topRel? h_smem h_ert h_rty h_init h_ctrl h_tr h_miri
    rframes.toList.reverse rfl h_fsim

end Anneal.MirCorrespondence
