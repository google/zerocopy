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

private theorem eStateM_bind_ok {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {s s₁ : σ} {a : α}
    (h : m s = .ok a s₁) :
    EStateM.bind m f s = f a s₁ := by
  dsimp only [EStateM.bind]; rw [h]

private theorem eStateM_bind_err {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {s s₁ : σ} {e : ε}
    (h : m s = .error e s₁) :
    EStateM.bind m f s = .error e s₁ := by
  dsimp only [EStateM.bind]; rw [h]

private theorem eStateM_bind_pure {ε σ α β : Type} (a : α)
    (f : α → EStateM ε σ β) (s : σ) :
    EStateM.bind (EStateM.pure a) f s = f a s := rfl

private theorem ite_false_eq {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

private theorem ite_true_eq {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

private theorem ite_not_true_eq {α : Type} (a b : α) :
    (if (!true) = true then a else b) = b := rfl

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

private theorem mirSetElem?_some_of_lt {α : Type} (xs : List α) (i : Nat)
    (v : α) (hi : i < xs.length) :
    ∃ xs', MirSemantics.setElem? xs i v = some xs' := by
  induction xs generalizing i with
  | nil => cases hi
  | cons x rest ih =>
    cases i with
    | zero => exact ⟨v :: rest, rfl⟩
    | succ j =>
      let ⟨rest', h_r⟩ := ih j (Nat.lt_of_succ_lt_succ hi)
      exact ⟨x :: rest', by dsimp only [MirSemantics.setElem?]; rw [h_r]⟩

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

private theorem discriminantTypesValid_stmt {body : Body} {bb : BasicBlock}
    {blockIdx : BasicBlockId} {stmtIdx : Nat} {dst : Place} {rv : Rvalue}
    (h_dv : discriminantTypesValid body = true)
    (h_bb : MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (h_st : MirSemantics.getElem? bb.statements stmtIdx = some (.assign dst rv)) :
    ∀ (src : Place) (ety : EnumTy) (dstTy : MirTy),
      rv = .discriminant src →
      dst.projection.isEmpty = true →
      src.projection.isEmpty = true →
      MirSemantics.getElem? body.locals src.localId = some (.enum ety) →
      MirSemantics.getElem? body.locals dst.localId = some dstTy →
      enumAdmitted ety = true →
      dstTy = .int ety.discrWidth ety.discrSigned := by
  intro src ety dstTy h_rv h_dpe h_spe h_sty h_dty h_adm
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
  rw [h_dpe, h_spe, Bool.and_self, ite_true_eq] at h_st_ok
  rw [h_sty] at h_st_ok
  change
    (match MirSemantics.getElem? body.locals dst.localId with
     | some dstTy =>
       if enumAdmitted ety then
         MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
       else true
     | none => true) = true at h_st_ok
  rw [h_dty] at h_st_ok
  change
    (if enumAdmitted ety = true then
      MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
    else true) = true at h_st_ok
  rw [h_adm, ite_true_eq] at h_st_ok
  exact MirTy.eq_of_beq h_st_ok

private theorem discriminantTypesValid_stmt_ordering {body : Body}
    {bb : BasicBlock} {blockIdx : BasicBlockId} {stmtIdx : Nat} {dst : Place}
    {rv : Rvalue}
    (h_dv : discriminantTypesValid body = true)
    (h_bb : MirSemantics.getElem? body.basicBlocks blockIdx = some bb)
    (h_st :
      MirSemantics.getElem? bb.statements stmtIdx = some (.assign dst rv)) :
    ∀ (src : Place) (dstTy : MirTy),
      rv = .discriminant src →
      dst.projection.isEmpty = true →
      src.projection.isEmpty = true →
      MirSemantics.getElem? body.locals src.localId = some .ordering →
      MirSemantics.getElem? body.locals dst.localId = some dstTy →
      dstTy = .int .i8 true := by
  intro src dstTy h_rv h_dpe h_spe h_sty h_dty
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
  rw [h_dpe, h_spe, Bool.and_self, ite_true_eq] at h_st_ok
  rw [h_sty] at h_st_ok
  change
    (match MirSemantics.getElem? body.locals dst.localId with
     | some dstTy => MirTy.beq dstTy (.int .i8 true)
     | none => true) = true at h_st_ok
  rw [h_dty] at h_st_ok
  exact MirTy.eq_of_beq h_st_ok

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
          SlotsMatchTys.setElem? h_inv h_ty (slot' := .dead) trivial h_set,
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
    {s' : State}
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_step : evalTerminator body bb f amem callerMem = .step s') :
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
    · cases h_step
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _
  | unsupported =>
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
      | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ | ordering _ =>
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
    (h_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_inv : SlotsMatchTys body.locals f.locals)
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
        exact evalTerminator_step_inv h_inv h_step
    | some stmt =>
      rw [h_st] at h_step
      exact evalStatement_step_inv h_bb h_st h_inv h_step

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

/-! ## Section 2: `StorageLive`, `StorageDead`, and `Step.evalStatement` -/

private theorem currentFrame_mkSimState' (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :
    Miri.Interpreter.MachineHooks.currentFrame
      (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
        retPlace mem ctrl cm) =
      .ok (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace)
        (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
          retPlace mem ctrl cm) := rfl

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
  | indirect _ => exact False.elim h_sm

private theorem storageLiveDyn_ref_eq (rp : RefProg)
    (defId : DefId) (rbody : RefBody) (body : Body)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (localId : LocalId)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_inv : SlotsMatchTys body.locals slots) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx body.locals slots
      retPlace mem ctrl cm
    let res := Miri.Interpreter.MachineHooks.storageLiveDyn
      (refStorageHooks rp.types) localId .none st
    match MirSemantics.getElem? body.locals localId with
    | none => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = .unsupported
    | some localTy =>
      match MirSemantics.setElem? slots localId (liveUninitSlot localTy) with
      | none => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = .unsupported
      | some slots' =>
        res = .ok () (mkSimState rp defId rbody blockIdx stmtIdx body.locals slots'
          retPlace mem ctrl cm) := by
  intro st res
  have h_cf := currentFrame_mkSimState' rp defId rbody blockIdx stmtIdx
    body.locals slots retPlace mem ctrl cm
  have h_len := SlotsMatchTys.length_eq h_inv
  cases h_ty : MirSemantics.getElem? body.locals localId with
  | none =>
    have h_gl := mkSimFrame_getLocal_none_left rp defId rbody blockIdx stmtIdx
      body.locals slots retPlace localId h_ty
    have h_err :
        res = .error (.stack (.invalidLocal localId (liftLocals rp.types body.locals slots).length)) st := by
      dsimp only [res, Miri.Interpreter.MachineHooks.storageLiveDyn, bind, Bind.bind,
        pure, Pure.pure]
      rw [eStateM_bind_ok h_cf, h_gl]
      rfl
    exact ⟨_, _, h_err, rfl⟩
  | some localTy =>
    dsimp only
    let ⟨slot, h_sl⟩ := getElem?_some_of_length_eq h_len.symm h_ty
    let ⟨slots', h_set⟩ := mirSetElem?_some_of_lt slots localId
      (liveUninitSlot localTy) (mirGetElem?_lt_of_some h_sl)
    rw [h_set]
    dsimp only
    let ⟨tid, h_rty, _⟩ := decodeBody_local_mem_types h_bdec h_ty
    have h_bl :
        (mkSimFrame rp defId rbody blockIdx stmtIdx body.locals slots retPlace).body.locals[localId]? =
          some (canonicalTyId rp.types tid) := by
      dsimp only [mkSimFrame, mkRefMiriFrame, toMiriBody]
      rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map, h_rty]
      rfl
    have h_gl := mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx
      body.locals slots retPlace localId localTy slot h_ty h_sl
    have h_rep := mkSimFrame_replaceLocalValue_some rp defId rbody blockIdx
      stmtIdx body.locals slots slots' retPlace localId localTy slot
      (liveUninitSlot localTy) h_ty h_sl h_set
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
    have h_alw : Miri.Interpreter.MachineHooks.afterLocalWrite localId true st =
        .ok () st := rfl
    rw [eStateM_bind_ok h_alw, eStateM_bind_pure, eStateM_bind_ok h_cf, h_gl]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure, h_rep]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure]
    have h_scf :
        Miri.Interpreter.MachineHooks.setCurrentFrame
          (mkSimFrame rp defId rbody blockIdx stmtIdx body.locals slots' retPlace) st =
        .ok () (mkSimState rp defId rbody blockIdx stmtIdx body.locals slots'
          retPlace mem ctrl cm) := rfl
    rw [eStateM_bind_ok h_scf]
    cases slot with
    | dead => rfl
    | immediate optVal => cases optVal <;> rfl
    | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)

private theorem storageDead_ref_eq (rp : RefProg)
    (defId : DefId) (rbody : RefBody) (body : Body)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (localId : LocalId)
    (h_inv : SlotsMatchTys body.locals slots) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx body.locals slots
      retPlace mem ctrl cm
    let res := Miri.Interpreter.MachineHooks.storageDead
      (refStorageHooks rp.types) localId st
    if Nat.beq localId 0 then
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = .unsupported
    else
      match MirSemantics.setElem? slots localId .dead with
      | none => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = .unsupported
      | some slots' =>
        res = .ok () (mkSimState rp defId rbody blockIdx stmtIdx body.locals slots'
          retPlace mem ctrl cm) := by
  intro st res
  have h_cf := currentFrame_mkSimState' rp defId rbody blockIdx stmtIdx
    body.locals slots retPlace mem ctrl cm
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
      have h_gl := mkSimFrame_getLocal_none_right rp defId rbody blockIdx stmtIdx
        body.locals slots retPlace (n + 1) h_sl_none
      have h_err :
          res = .error (.stack (.invalidLocal (n + 1) (liftLocals rp.types body.locals slots).length)) st := by
        dsimp only [res, Miri.Interpreter.MachineHooks.storageDead, bind, Bind.bind,
          pure, Pure.pure]
        rw [h_ne0, ite_false_eq, eStateM_bind_ok h_cf, h_gl]
        rfl
      exact ⟨_, _, h_err, rfl⟩
    | some slots' =>
      let ⟨slot, h_sl⟩ := getElem?_some_of_setElem?_some h_set
      let ⟨localTy, h_ty⟩ := getElem?_some_of_length_eq h_len h_sl
      have h_gl := mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx
        body.locals slots retPlace (n + 1) localTy slot h_ty h_sl
      have h_rep := mkSimFrame_replaceLocalValue_some rp defId rbody blockIdx
        stmtIdx body.locals slots slots' retPlace (n + 1) localTy slot .dead
        h_ty h_sl h_set
      dsimp only [res, Miri.Interpreter.MachineHooks.storageDead, bind, Bind.bind,
        pure, Pure.pure]
      rw [h_ne0, ite_false_eq, eStateM_bind_ok h_cf, h_gl]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      dsimp only [slotToMiriLocalValue] at h_rep
      rw [eStateM_bind_pure, h_rep]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      have h_scf :
          Miri.Interpreter.MachineHooks.setCurrentFrame
            (mkSimFrame rp defId rbody blockIdx stmtIdx body.locals slots' retPlace) st =
          .ok () (mkSimState rp defId rbody blockIdx stmtIdx body.locals slots'
            retPlace mem ctrl cm) := rfl
      rw [eStateM_bind_ok h_scf]
      cases slot with
      | dead => rfl
      | immediate optVal => cases optVal <;> rfl
      | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)

private theorem step_evalStatement_ref_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (body : Body) (f : FrameState)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (amem : MemoryState) (rstmt : RefStatementKind)
    (stmt : StatementKind)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_arg : Nat.blt body.argumentCount body.locals.length = true)
    (h_supp : body.locals.all isSupportedScalarOrUnitTy = true)
    (h_inv : SlotsMatchTys body.locals f.locals)
    (h_st_dec : decodeStmt rp.types rstmt = some stmt)
    (h_discr_ty :
      ∀ (dst src : Place) (ety : EnumTy) (dstTy : MirTy),
        stmt = .assign dst (.discriminant src) →
        dst.projection.isEmpty = true →
        src.projection.isEmpty = true →
        MirSemantics.getElem? body.locals src.localId = some (.enum ety) →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        enumAdmitted ety = true →
        dstTy = .int ety.discrWidth ety.discrSigned)
    (h_ord_discr_ty :
      ∀ (dst src : Place) (dstTy : MirTy),
        stmt = .assign dst (.discriminant src) →
        dst.projection.isEmpty = true →
        src.projection.isEmpty = true →
        MirSemantics.getElem? body.locals src.localId = some .ordering →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        dstTy = .int .i8 true)
    (h_cast_ty :
      ∀ (dst : Place) (opnd : Operand) (castTy dstTy : MirTy),
        stmt = .assign dst (.cast .intToInt opnd castTy) →
        dst.projection.isEmpty = true →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        dstTy = castTy) :
    let st := mkSimState rp defId rbody f.blockIdx f.stmtIdx body.locals f.locals
      retPlace mem ctrl cm
    let res := Miri.Interpreter.Step.evalStatement
      (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
      c (toMiriStatement rp.types rstmt) st
    match evalStatement body f amem cm stmt with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = k
    | .done _ => False
    | .step s' =>
      ∃ slots',
        s' = { frames := [{ f with stmtIdx := f.stmtIdx + 1, locals := slots' }],
               callerMem := cm, mem := amem } ∧
        res = (mkSimState rp defId rbody f.blockIdx f.stmtIdx body.locals slots'
          retPlace mem ctrl cm, .ok ()) := by
  intro st res
  cases rstmt with
  | nop =>
    injection h_st_dec with h_eq; subst h_eq
    exact ⟨f.locals, rfl, rfl⟩
  | storageLive localId =>
    injection h_st_dec with h_eq; subst h_eq
    have h_sl := storageLiveDyn_ref_eq rp defId rbody body f.blockIdx f.stmtIdx
      f.locals retPlace mem ctrl cm localId h_bdec h_inv
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
    have h_sd := storageDead_ref_eq rp defId rbody body f.blockIdx f.stmtIdx
      f.locals retPlace mem ctrl cm localId h_inv
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
        have h_ev := evalRvalueIntoPlace_ref_eq rp c defId rbody body f.blockIdx
          f.stmtIdx f.locals amem retPlace mem ctrl cm rdst dst rrv rv h_bdec h_supp
          h_inv h_pl h_rv (fun src ety dstTy h_eq_rv =>
            h_discr_ty dst src ety dstTy (by rw [h_eq_rv]))
          (fun src dstTy h_eq_rv =>
            h_ord_discr_ty dst src dstTy (by rw [h_eq_rv]))
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
    have h_ev := evalRvalueIntoPlace_ref_eq rp c defId rbody body f.blockIdx
      f.stmtIdx f.locals amem retPlace mem ctrl cm ⟨0, []⟩ ⟨0, []⟩ .unsupported
      .unsupported h_bdec h_supp h_inv rfl rfl (fun _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
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
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (optVal : Option Val)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal)) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.PlaceMachine.localToOp (refExecCfg rp).compiler c id st =
      .ok ⟨.immediate (optValToMiriImm ty optVal),
        refLocalLayoutForTy rp.types ty⟩ st := by
  intro st
  have h_cf := currentFrame_mkSimState' rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_gl := mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty (.immediate optVal) h_ty h_sl
  have h_go := mkSimFrame_getLocalOperand_live rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty optVal h_ty h_sl
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_ll :
      Miri.Interpreter.PlaceMachine.layoutLocal (refExecCfg rp).compiler c id st =
        .ok (refLocalLayoutForTy rp.types ty) st := by
    dsimp only [Miri.Interpreter.PlaceMachine.layoutLocal, bind, Bind.bind,
      pure, Pure.pure]
    rw [eStateM_bind_ok h_cf, h_gl]
    rfl
  dsimp only [Miri.Interpreter.PlaceMachine.localToOp,
    Miri.Interpreter.PlaceMachine.localToOpCore, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_ll, eStateM_bind_ok h_cf, h_go]
  simp only [h_sz, Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

private theorem placeMachine_localToOp_dead (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.PlaceMachine.localToOp (refExecCfg rp).compiler c id st =
      .error (.stack (.localExpectedLive id)) st := by
  intro st
  have h_cf := currentFrame_mkSimState' rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_gl := mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty .dead h_ty h_sl
  have h_go := mkSimFrame_getLocalOperand_dead rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty h_ty h_sl
  have h_ll :
      Miri.Interpreter.PlaceMachine.layoutLocal (refExecCfg rp).compiler c id st =
        .ok (refLocalLayoutForTy rp.types ty) st := by
    dsimp only [Miri.Interpreter.PlaceMachine.layoutLocal, bind, Bind.bind,
      pure, Pure.pure]
    rw [eStateM_bind_ok h_cf, h_gl]
    rfl
  dsimp only [Miri.Interpreter.PlaceMachine.localToOp,
    Miri.Interpreter.PlaceMachine.localToOpCore, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_ll, eStateM_bind_ok h_cf, h_go]
  rfl

private theorem popRaw_mkSimState (rp : RefProg)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    let fr := mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace
    ∃ stPop : Miri.Interpreter.MachineHooks.State Unit RefUser,
      Miri.Interpreter.TypedMachineBindings.popRaw
          (Miri.Interpreter.TypedMachineBindings.retagHooks
            (refExecCfg rp).access (refExecCfg rp).retag) st =
        .ok fr stPop ∧
      stPop.stack.frames = Array.empty ∧
      stPop.machine.memory = mem ∧
      stPop.machine.dataRace = none ∧
      stPop.machine.pendingMoveDeinit = false ∧
      stPop.machine.user.callerMem = cm := by
  intro st fr
  refine ⟨{ st with
    stack := Miri.Interpreter.Stack.empty
    machine := { st.machine with
      threads := { st.machine.threads with
        threads := st.machine.threads.threads.mapIdx fun index thread =>
          if index == st.machine.threads.activeThread.toNat then
            { thread with topUserRelevantFrame := none }
          else thread } } }, ?_, rfl, rfl, rfl, rfl, rfl⟩
  rfl

private theorem returnFromCurrentFrame_ref_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (body : Body) (rbb : RefBasicBlock)
    (bb : BasicBlock) (f : FrameState) (retTy : MirTy)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (amem : MemoryState)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = some rbb)
    (h_rbb_dec : decodeBasicBlock rp.types rbb = some bb)
    (h_rterm : rbb.terminator = .return_)
    (h_ret_ty : MirSemantics.getElem? body.locals 0 = some retTy)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, retPlace))
    (h_supp : body.locals.all isSupportedScalarOrUnitTy = true)
    (h_inv : SlotsMatchTys body.locals f.locals) :
    let st := mkSimState rp defId rbody f.blockIdx f.stmtIdx body.locals f.locals
      retPlace mem ctrl cm
    let res := (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfig rp) refLimits).terminator c
      (toMiriTerminator rp.types .return_) st
    match evalTerminator body bb f amem cm with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = k
    | .done (.returned ⟨v, cm'⟩) =>
      ∃ st',
        res = (st', .ok ()) ∧
        st'.stack.frames.isEmpty = true ∧
        refReadReturnVal st'.machine.memory retTy retPlace = .ok v ∧
        st'.machine.user.callerMem = cm'
    | .done (.unwound _) => False
    | .step s' =>
      ∃ tgt slots',
        s' = { frames := [{ f with blockIdx := tgt, stmtIdx := 0, locals := slots' }],
               callerMem := cm, mem := amem } ∧
        res = (mkSimState rp defId rbody tgt 0 body.locals slots'
          retPlace mem ctrl cm, .ok ()) := by
  intro st res
  let ⟨_, h_term_dec, h_cl_eq⟩ := decodeBasicBlock_inv h_rbb_dec
  rw [h_rterm] at h_term_dec
  injection h_term_dec with h_bb_term
  have h_st_cf :
      st.stack.currentFrame? =
        some (mkSimFrame rp defId rbody f.blockIdx f.stmtIdx body.locals f.locals retPlace) := rfl
  have h_mf_loc :
      (mkSimFrame rp defId rbody f.blockIdx f.stmtIdx body.locals f.locals retPlace).location =
        .mir ⟨f.blockIdx, f.stmtIdx⟩ := rfl
  have h_mb :
      (mkSimFrame rp defId rbody f.blockIdx f.stmtIdx body.locals f.locals retPlace).body.basicBlocks[f.blockIdx]? =
        some (toMiriBasicBlock rp.types rbb) := by
    dsimp only [mkSimFrame, mkRefMiriFrame, toMiriBody]
    rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map, h_rbb]
    rfl
  have h_len := SlotsMatchTys.length_eq h_inv
  have h_ret_supp : isSupportedScalarOrUnitTy retTy = true :=
    list_all_mirGetElem? (p := isSupportedScalarOrUnitTy) h_supp h_ret_ty
  have h_ret_res : resolveTy rp.types (tyIdFor rp.types retTy) = some retTy := by
    let ⟨_, _, h_ts⟩ := decodeBody_local_mem_types h_bdec h_ret_ty
    exact (resolveTy_tyIdFor_of_mem h_ts).2
  cases h_cl : bb.cleanup with
  | true =>
    have h_rcl : rbb.cleanup = true := h_cl_eq.trans h_cl
    have h_ev_t : evalTerminator body bb f amem cm = .fault .unsupported := by
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
    | dead =>
      have h_ev_t : evalTerminator body bb f amem cm = .fault .undefined := by
        dsimp only [evalTerminator]
        rw [← h_bb_term]
        dsimp only
        rw [h_cl, ite_false_eq, h_sl₀]
      rw [h_ev_t]
      have h_ro := placeMachine_localToOp_dead rp c defId rbody f.blockIdx f.stmtIdx
        body.locals f.locals retPlace mem ctrl cm 0 retTy h_ret_ty h_sl₀
      have h_ro' :
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits)).place.localToOp
            c 0 st = .error (.stack (.localExpectedLive 0)) st := h_ro
      have h_err : res = (st, .error (.stack (.localExpectedLive 0))) := by
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
      have h_ro := placeMachine_localToOp_live rp c defId rbody f.blockIdx f.stmtIdx
        body.locals f.locals retPlace mem ctrl cm 0 retTy optVal h_ret_ty h_sl₀
      let ⟨stPop, h_pop, h_pop_fr, h_pop_mem, h_pop_dr, h_pop_pmd, h_pop_cm⟩ :=
        popRaw_mkSimState rp defId rbody f.blockIdx f.stmtIdx body.locals f.locals
          retPlace mem ctrl cm
      have h_ro' :
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits)).place.localToOp
            c 0 st =
          .ok ⟨.immediate (optValToMiriImm retTy optVal),
            refLocalLayoutForTy rp.types retTy⟩ st := h_ro
      have h_pop' :
          Miri.Interpreter.TypedMachineBindings.popRaw
            (Miri.Interpreter.TypedMachineBindings.retagHooks
              (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).access
              (Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits).retag)
            st =
          .ok (mkSimFrame rp defId rbody f.blockIdx f.stmtIdx body.locals f.locals retPlace) stPop := h_pop
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
        dsimp only [mkSimFrame, mkRefMiriFrame,
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
        dsimp only [mkSimFrame, mkRefMiriFrame,
          Miri.Interpreter.RuntimeStackPlace.toRuntimePlace]
        simp only [h_cp, Bool.or_false]
        rfl
      have h_sm := SlotsMatchTys.getElem? h_inv h_ret_ty h_sl₀
      cases optVal with
      | none =>
        have h_ev_t : evalTerminator body bb f amem cm = .fault .undefined := by
          dsimp only [evalTerminator]
          rw [← h_bb_term]
          dsimp only
          rw [h_cl, ite_false_eq, h_sl₀]
        rw [h_ev_t]
        let ⟨msg, st', h_ub⟩ := copyReturn_uninit_ub rp c retTy mem retPlace stPop
          h_init h_pop_mem h_pop_dr h_pop_pmd h_sm h_ret_supp h_ret_res
        exact ⟨_, _, h_step_copy_err _ _ h_ub, rfl⟩
      | some v =>
        have h_ev_t : evalTerminator body bb f amem cm = .done (.returned ⟨v, cm⟩) := by
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

private theorem toNat_bvExtractLsb_trunc (w : IntWidth) (a : BitVec 128) :
    (bvExtractLsb (w.bitWidth - 1) 0 (truncateBits w a)).toNat =
      (truncateBits w a).toNat := by
  dsimp only [bvExtractLsb, bvExtractLsb']
  rw [nat_shiftRight_zero, BitVec.toNat_ofNat, intWidth_lsb_width,
    toNat_truncateBits]
  exact Nat.mod_eq_of_lt (Nat.mod_lt a.toNat (intWidth_modulus_pos w))

private theorem signExtendBits_inj (w : IntWidth) (a b : BitVec 128)
    (h : signExtendBits w (truncateBits w a) =
      signExtendBits w (truncateBits w b)) :
    truncateBits w a = truncateBits w b := by
  dsimp only [signExtendBits] at h
  rw [bvToInt_eq_toInt, bvToInt_eq_toInt, ← bitVec_signExtend_eq,
    ← bitVec_signExtend_eq, BitVec.toInt_signExtend, BitVec.toInt_signExtend] at h
  have h_eq_low : ∀ {k : Nat} (x y : BitVec k),
      k ≤ 128 →
      x.toInt.bmod (HPow.hPow 2 (min 128 k)) =
        y.toInt.bmod (HPow.hPow 2 (min 128 k)) →
      x = y := by
    intro k x y hk hbmod
    rw [Nat.min_eq_right hk, ← BitVec.toInt_ofInt, BitVec.ofInt_toInt,
      ← BitVec.toInt_ofInt, BitVec.ofInt_toInt] at hbmod
    exact BitVec.toInt_inj.mp hbmod
  have hk : w.bitWidth - 1 - 0 + 1 ≤ 128 := by cases w <;> decide
  have hlow := h_eq_low _ _ hk h
  apply BitVec.eq_of_toNat_eq
  rw [← toNat_bvExtractLsb_trunc w a, ← toNat_bvExtractLsb_trunc w b, hlow]

private theorem decodeScalar_eq_iff (w : IntWidth) (s : Bool)
    (a b : BitVec 128) :
    (decodeScalar ⟨w, s, a⟩ == decodeScalar ⟨w, s, b⟩) =
      (truncateBits w a == truncateBits w b) := by
  cases h_tb : (truncateBits w a == truncateBits w b) with
  | true =>
    have h_eq := eq_of_beq h_tb
    dsimp only [decodeScalar]
    rw [h_eq]
    exact beq_self_eq_true _
  | false =>
    cases h_dc : (decodeScalar ⟨w, s, a⟩ == decodeScalar ⟨w, s, b⟩) with
    | false => rfl
    | true =>
      have h_eq := eq_of_beq h_dc
      have h_teq : truncateBits w a = truncateBits w b := by
        cases s with
        | true => exact signExtendBits_inj w a b h_eq
        | false =>
          dsimp only [decodeScalar, ite_false_eq] at h_eq
          injection h_eq with h_nat
          exact BitVec.eq_of_toNat_eq h_nat
      rw [h_teq, beq_self_eq_true] at h_tb
      cases h_tb

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
      ∃ err, res = (st, .error err) ∧ stepErrorFaultKind err = .unsupported
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
      rw [decodeScalar_eq_iff]
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

private theorem eStateM_bind_error {ε σ α β : Type} {x : EStateM ε σ α}
    {f : α → EStateM ε σ β} {s s' : σ} {e : ε}
    (h : x s = .error e s') : EStateM.bind x f s = .error e s' := by
  dsimp only [EStateM.bind]; rw [h]

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
      ∃ err, res = (st, .error err) ∧ stepErrorFaultKind err = k
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
        rw [eStateM_bind_error h_step_bin]
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
        stepErrorFaultKind err = k
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
        stepErrorFaultKind err = k
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
      ∃ err, res = (st, .error err) ∧ stepErrorFaultKind err = k
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
      rw [eStateM_bind_error h_step_bin]
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
      .unsupported := by
  have h_gen : ∀ w' : IntWidth,
      Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance) v
          (toMiriSize w') = .error e →
      stepErrorFaultKind (Miri.Interpreter.ScalarOps.scalarError e) =
        .unsupported := by
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
    ∃ err, res = (st, .error err) ∧ stepErrorFaultKind err = .unsupported := by
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
      rw [eStateM_bind_error (scalarOps_classify_pair' rp c st w s h_res)]
    rw [eStateM_bind_error h_bin]
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
        stepErrorFaultKind err = k
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
        | scalar _ | ptr _ | bool _ | ordering _ | unit | enumVal _ _
        | tuple _ | bytes _ =>
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
        stepErrorFaultKind err = .unsupported := by
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

private theorem evalTerminator_ref_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (body : Body) (rbb : RefBasicBlock)
    (bb : BasicBlock) (f : FrameState) (retTy : MirTy)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (amem : MemoryState)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_rbb : MirSemantics.getElem? rbody.basicBlocks f.blockIdx = some rbb)
    (h_rbb_dec : decodeBasicBlock rp.types rbb = some bb)
    (h_ret_ty : MirSemantics.getElem? body.locals 0 = some retTy)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, retPlace))
    (h_supp : body.locals.all isSupportedScalarOrUnitTy = true)
    (h_inv : SlotsMatchTys body.locals f.locals) :
    let st := mkSimState rp defId rbody f.blockIdx f.stmtIdx body.locals f.locals
      retPlace mem ctrl cm
    let res := (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfig rp) refLimits).terminator c
      (toMiriTerminator rp.types rbb.terminator) st
    match evalTerminator body bb f amem cm with
    | .fault k =>
      ∃ err st', res = (st', .error err) ∧ stepErrorFaultKind err = k
    | .done (.returned ⟨v, cm'⟩) =>
      ∃ st',
        res = (st', .ok ()) ∧
        st'.stack.frames.isEmpty = true ∧
        refReadReturnVal st'.machine.memory retTy retPlace = .ok v ∧
        st'.machine.user.callerMem = cm'
    | .done (.unwound _) => False
    | .step s' =>
      ∃ tgt slots',
        s' = { frames := [{ f with blockIdx := tgt, stmtIdx := 0, locals := slots' }],
               callerMem := cm, mem := amem } ∧
        res = (mkSimState rp defId rbody tgt 0 body.locals slots'
          retPlace mem ctrl cm, .ok ()) := by
  intro st
  let ⟨_, h_term_dec, _⟩ := decodeBasicBlock_inv h_rbb_dec
  cases h_rt : rbb.terminator with
  | goto target =>
    intro res
    rw [h_rt] at h_term_dec
    injection h_term_dec with h_eq
    dsimp only [evalTerminator]
    rw [← h_eq]
    exact ⟨target, f.locals, rfl, rfl⟩
  | return_ =>
    exact returnFromCurrentFrame_ref_eq rp c defId rbody body rbb bb f retTy
      retPlace mem ctrl cm amem h_bdec h_rbb h_rbb_dec h_rt h_ret_ty h_init
      h_supp h_inv
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
  | assert rcond _ _ _ _ =>
    intro res
    rw [h_rt] at h_term_dec
    dsimp only [decodeTerminator, optMap] at h_term_dec
    cases h_c : decodeOperand rp.types rcond with
    | none => rw [h_c] at h_term_dec; cases h_term_dec
    | some _ =>
      rw [h_c] at h_term_dec
      injection h_term_dec with h_eq
      dsimp only [evalTerminator]
      rw [← h_eq]
      exact ⟨_, _, rfl, rfl⟩
  | call _ rargs rdst _ _ =>
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
      dsimp only
      have h_evD := evalPrimitiveOperand_ref_eq rp c defId rbody f.blockIdx
        f.stmtIdx body.locals f.locals amem retPlace mem ctrl cm
        (Miri.Interpreter.OperandPath.instruction "discriminant")
        rdiscr discr none h_inv h_d (fun _ _ h_ty =>
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
          let ⟨discrTy, h_dcv, h_dpr, h_dres, h_okD⟩ := h_evD
          let st₁ := mkSimState rp defId rbody f.blockIdx f.stmtIdx body.locals
            slotsAfterDiscr retPlace mem ctrl cm
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
              exact ⟨tgt, slotsAfterDiscr, by rw [h_amem], rfl⟩
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
                exact ⟨tgt, slotsAfterDiscr, by rw [h_amem], rfl⟩
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
                  exact ⟨tgt, slotsAfterDiscr, by rw [h_amem], rfl⟩
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
                    rfl⟩
                | cons hd tl =>
                  rw [h_br] at h_loop
                  dsimp only at h_loop
                  let ⟨err, h_lr, h_fk⟩ := h_loop
                  dsimp only
                  rw [h_lr]
                  exact ⟨err, st₁, rfl, h_fk⟩

/-! ## Section 4: `ExecutionMachine.step` Simulation (`EvalRefStepEqClaim`) -/

private theorem evalRefStep_of_err (rp : RefProg) (c : Choice) (rs : RefState)
    (st' : MiriStepState) (err : Miri.Interpreter.StepError)
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true)
    (h_step : Miri.Interpreter.ExecutionMachine.step
        (refExecutionConfig rp) refLimits c rs.miri = (st', .error err)) :
    evalRefStep rp c rs = faultToRefOutcome (stepErrorFaultKind err) := by
  dsimp only [evalRefStep]
  rw [h_lt, ite_not_true_eq, h_step]
  cases err with
  | undefinedBehavior _ => rfl
  | stack se => cases se <;> rfl
  | _ => rfl

/-- One $M_{\text{ref}}$ step via `Miri.Interpreter.ExecutionMachine.step` from
a simulated state computes exactly the lifted $M_{\text{anneal}}$ step. -/
theorem evalRefStep_eq_base : EvalRefStepEqClaim := by
  intro rp p s rs f body rbody h_dec h_sim hs h_body h_rbody h_lt c
  let ⟨f_sim, rf, retTy, mem, ctrl, _, hs_sim, _, h_defId, h_ert, h_rty,
    h_init, h_ctrl, h_miri, h_fsim⟩ := h_sim
  rw [hs] at hs_sim
  injection hs_sim with hf_eq
  subst hf_eq
  let ⟨body_sim, rbody_sim, h_bs, h_rbs, h_bdec, h_arg, _, h_dv, h_cv, h_supp,
    h_inv, h_pc, h_rf⟩ := h_fsim
  rw [h_body] at h_bs; injection h_bs with hb_eq; subst hb_eq
  rw [h_rbody] at h_rbs; injection h_rbs with hrb_eq; subst hrb_eq
  have h_ret_ty : MirSemantics.getElem? body.locals 0 = some retTy := by
    dsimp only [entryRetTy?] at h_ert
    rw [← h_defId, h_body] at h_ert
    exact h_ert
  let ⟨_, _, h_bbs_dec, _, _⟩ := decodeBody_inv h_bdec
  let st := mkSimState rp f.defId rbody f.blockIdx f.stmtIdx body.locals
    f.locals rs.retPlace mem ctrl s.callerMem
  have h_miri_eq : rs.miri = st := by rw [h_miri, h_rf]
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
        some (mkSimFrame rp f.defId rbody f.blockIdx f.stmtIdx body.locals f.locals rs.retPlace) := rfl
  have h_mf_loc :
      (mkSimFrame rp f.defId rbody f.blockIdx f.stmtIdx body.locals f.locals rs.retPlace).location =
        .mir ⟨f.blockIdx, f.stmtIdx⟩ := rfl
  have h_mframe_bb : ∀ (bbIdx : BasicBlockId),
      (mkSimFrame rp f.defId rbody f.blockIdx f.stmtIdx body.locals f.locals
        rs.retPlace).body.basicBlocks[bbIdx]? =
      (MirSemantics.getElem? rbody.basicBlocks bbIdx).map
        (toMiriBasicBlock rp.types) := by
    intro bbIdx
    dsimp only [mkSimFrame, mkRefMiriFrame, toMiriBody]
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
      rw [h_st_cf]
      dsimp only
      rw [h_mf_loc]
      dsimp only
      rw [h_mframe_bb f.blockIdx, h_rbb_none]
      rfl
    rw [evalRefStep_of_err rp c rs st (.invalidBlock f.blockIdx) h_lt h_em_err]
    dsimp only [evalStep]
    rw [hs]
    dsimp only
    rw [h_body]
    dsimp only
    rw [h_bb]
    rfl
  | some bb =>
    let ⟨rbb, h_rbb, h_rbb_dec⟩ :=
      (mapOption_getElem? h_bbs_dec f.blockIdx).2 bb h_bb
    let ⟨h_stmts_dec, h_term_dec, _⟩ := decodeBasicBlock_inv h_rbb_dec
    have h_mb :
        (mkSimFrame rp f.defId rbody f.blockIdx f.stmtIdx body.locals f.locals
          rs.retPlace).body.basicBlocks[f.blockIdx]? =
          some (toMiriBasicBlock rp.types rbb) := by
      rw [h_mframe_bb f.blockIdx, h_rbb]; rfl
    have h_mstmt : ∀ (si : Nat),
        (toMiriBasicBlock rp.types rbb).statements[si]? =
          (MirSemantics.getElem? rbb.statements si).map
            (toMiriStatement rp.types) := by
      intro si
      dsimp only [toMiriBasicBlock]
      rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map]
    cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx with
    | some stmt =>
      let ⟨rstmt, h_rstmt, h_rstmt_dec⟩ :=
        (mapOption_getElem? h_stmts_dec f.stmtIdx).2 stmt h_st
      have h_evS := step_evalStatement_ref_eq rp c f.defId rbody body f
        rs.retPlace mem ctrl s.callerMem s.mem rstmt stmt h_bdec h_arg h_supp h_inv
        h_rstmt_dec (fun dst src ety dstTy h_st_eq =>
          discriminantTypesValid_stmt h_dv h_bb (by rw [← h_st_eq]; exact h_st)
            src ety dstTy rfl)
        (fun dst src dstTy h_st_eq =>
          discriminantTypesValid_stmt_ordering h_dv h_bb
            (by rw [← h_st_eq]; exact h_st) src dstTy rfl)
        (fun dst opnd castTy dstTy h_st_eq =>
          castTypesValid_stmt h_cv h_bb (by rw [← h_st_eq]; exact h_st)
            opnd castTy dstTy rfl)
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
        rw [h_st_cf]
        dsimp only
        rw [h_mf_loc]
        dsimp only
        rw [h_mb]
        dsimp only
        rw [h_mstmt f.stmtIdx, h_rstmt]
        dsimp only [Option.map]
        rw [h_ev_err]
      have h_step_stmt_ok :
          ∀ (slots' : List LocalSlot),
            Miri.Interpreter.Step.evalStatement
                (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                c (toMiriStatement rp.types rstmt) st =
              (mkSimState rp f.defId rbody f.blockIdx f.stmtIdx body.locals
                slots' rs.retPlace mem ctrl s.callerMem, .ok ()) →
            Miri.Interpreter.Step.step
                (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfig rp) refLimits)
                c st =
              (mkSimState rp f.defId rbody f.blockIdx (f.stmtIdx + 1) body.locals
                slots' rs.retPlace mem ctrl s.callerMem, .ok true) := by
        intro slots' h_ev_ok
        dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [h_st_cf]
        dsimp only
        rw [h_mf_loc]
        dsimp only
        rw [h_mb]
        dsimp only
        rw [h_mstmt f.stmtIdx, h_rstmt]
        dsimp only [Option.map]
        rw [h_ev_ok]
        rfl
      have h_evalStep_stmt : evalStep p c s = evalStatement body f s.mem s.callerMem stmt := by
        dsimp only [evalStep]
        rw [hs]
        dsimp only
        rw [h_body]
        dsimp only
        rw [h_bb]
        dsimp only
        rw [h_st]
      rw [h_evalStep_stmt]
      cases h_es : evalStatement body f s.mem s.callerMem stmt with
      | fault k =>
        rw [h_es] at h_evS
        let ⟨err, st', h_err, h_fk⟩ := h_evS
        have h_em_err :
            Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
              ({ st' with machine := { st'.machine with pendingMoveDeinit := false } },
               .error err) := by
          rw [h_step_eq, h_step_stmt_err err st' h_err]
        rw [evalRefStep_of_err rp c rs _ err h_lt h_em_err, h_fk]
        rfl
      | done _ =>
        rw [h_es] at h_evS; exact False.elim h_evS
      | step s' =>
        rw [h_es] at h_evS
        let ⟨slots', h_s'_eq, h_ok_s⟩ := h_evS
        subst h_s'_eq
        have h_em_ok :
            Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
              (mkSimState rp f.defId rbody f.blockIdx (f.stmtIdx + 1) body.locals
                slots' rs.retPlace mem ctrl s.callerMem, .ok true) := by
          rw [h_step_eq, h_step_stmt_ok slots' h_ok_s]
          rfl
        have h_nc : nextRefControlForStep body f rs.miri.machine.user.control = ctrl := by
          dsimp only [nextRefControlForStep]
          rw [h_bb]
          dsimp only
          rw [h_st, h_miri_eq]
          rfl
        dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
        rw [h_lt, ite_not_true_eq, h_em_ok, h_nc, h_miri_eq]
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
            (mkSimState rp f.defId rbody f.blockIdx f.stmtIdx body.locals f.locals
              rs.retPlace mem (advanceRefControl ctrl) s.callerMem, .ok ()) := by
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
              (mkSimState rp f.defId rbody f.blockIdx f.stmtIdx body.locals f.locals
                rs.retPlace mem (advanceRefControl ctrl) s.callerMem)
            (r.1, r.2.map fun _ => true) := by
        dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [h_st_cf]
        dsimp only
        rw [h_mf_loc]
        dsimp only
        rw [h_mb]
        dsimp only
        rw [h_mstmt f.stmtIdx, h_rstmt_none]
        dsimp only [Option.map]
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
      have h_evT := evalTerminator_ref_eq rp c f.defId rbody body rbb bb f retTy
        rs.retPlace mem (advanceRefControl ctrl) s.callerMem s.mem h_bdec h_rbb
        h_rbb_dec h_ret_ty h_init h_supp h_inv
      have h_evalStep_term : evalStep p c s = evalTerminator body bb f s.mem s.callerMem := by
        dsimp only [evalStep]
        rw [hs]
        dsimp only
        rw [h_body]
        dsimp only
        rw [h_bb]
        dsimp only
        rw [h_st]
        dsimp only
        rw [h_beq_len]
        rfl
      rw [h_evalStep_term]
      cases h_et : evalTerminator body bb f s.mem s.callerMem with
      | fault k =>
        rw [h_et] at h_evT
        let ⟨err, st', h_err, h_fk⟩ := h_evT
        have h_em_err :
            Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
              ({ st' with machine := { st'.machine with pendingMoveDeinit := false } },
               .error err) := by
          rw [h_step_eq, h_step_term, h_err]
          rfl
        rw [evalRefStep_of_err rp c rs _ err h_lt h_em_err, h_fk]
        rfl
      | done out =>
        cases out with
        | unwound _ =>
          rw [h_et] at h_evT
          exact False.elim h_evT
        | returned tv =>
          cases tv with
          | mk v cm' =>
            rw [h_et] at h_evT
            let ⟨st', h_ok_t, h_emp, h_rd, h_cm'⟩ := h_evT
            have h_em_ok :
                Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
                  ({ st' with machine := { st'.machine with pendingMoveDeinit := false } },
                   .ok true) := by
              rw [h_step_eq, h_step_term, h_ok_t]
              rfl
            dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
            rw [h_lt, ite_not_true_eq, h_em_ok]
            dsimp only
            rw [h_emp, ite_true_eq, h_rty, h_rd, h_cm']
      | step s' =>
        rw [h_et] at h_evT
        let ⟨tgt, slots', h_s'_eq, h_ok_t⟩ := h_evT
        subst h_s'_eq
        have h_em_ok :
            Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri =
              (mkSimState rp f.defId rbody tgt 0 body.locals slots' rs.retPlace
                mem (advanceRefControl ctrl) s.callerMem, .ok true) := by
          rw [h_step_eq, h_step_term, h_ok_t]
          rfl
        have h_nc : nextRefControlForStep body f rs.miri.machine.user.control =
            advanceRefControl ctrl := by
          dsimp only [nextRefControlForStep]
          rw [h_bb]
          dsimp only
          rw [h_st]
          dsimp only
          rw [h_beq_len, h_miri_eq]
          rfl
        dsimp only [evalRefStep, mapStepRes, stepResultToRefOutcome]
        rw [h_lt, ite_not_true_eq, h_em_ok, h_nc, h_miri_eq]
        rfl

end Anneal.MirCorrespondence
