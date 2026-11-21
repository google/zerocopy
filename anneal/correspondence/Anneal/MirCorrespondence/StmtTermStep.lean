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
import Anneal.MirCorrespondence.RvalueStep

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# Statement and Terminator Simulation (`Anneal.MirCorrespondence.StmtTermStep`)

Proves `evalRefStatement_eq`, `evalRefTerminator_eq`, and `evalRefStep_eq_base`.
-/

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

private abbrev RefStepState :=
  Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
    RefStepMachine

private abbrev RefMiriFrame :=
  Miri.Interpreter.Frame (Option Val) Miri.Interpreter.LocalLayout Unit

private theorem evalRefStatement_of_ok (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory)
    (stmt : RefStatementKind) (m' : RefStepMachine)
    (h_ev : Miri.Interpreter.Step.evalStatement
        (refStepHooksFor ts callerMem) ()
        (toMiriStatementForDispatch stmt)
        (mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt)) =
      ({ mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt) with
          machine := m' }, .ok ())) :
    evalRefStatement ts rframe callerMem stmt =
      .step {
        frames := [{
          rframe with
          stmtIdx := rframe.stmtIdx + 1
          locals := m'.locals
        }]
        callerMem
      } := by
  let st₀ := mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt)
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock false with
      statements := Array.mk [toMiriStatementForDispatch stmt] }
  let fr : RefMiriFrame :=
    { mkSingleLocalMiriFrame .dead false with
      body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
      location := .mir ⟨0, 0⟩ }
  have h_cf : st₀.stack.currentFrame? = some fr := rfl
  have h_loc : fr.location = .mir ⟨0, 0⟩ := rfl
  have h_bb : fr.body.basicBlocks[0]? = some blk := rfl
  have h_st : blk.statements[0]? = some (toMiriStatementForDispatch stmt) := rfl
  have h_step :
      Miri.Interpreter.Step.step (refStepHooksFor ts callerMem) () st₀ =
        ({ st₀ with
          stack := ⟨Array.mk [{ fr with location := .mir ⟨0, 1⟩ }]⟩
          machine := m' }, .ok true) := by
    unfold Miri.Interpreter.Step.step
    rw [h_cf]; dsimp only
    rw [h_loc]; dsimp only
    rw [h_bb]; dsimp only
    rw [h_st]; dsimp only
    rw [h_ev]; rfl
  unfold evalRefStatement
  rw [h_step]
  rfl

private theorem evalRefStatement_of_err (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory)
    (stmt : RefStatementKind) (st₁ : RefStepState)
    (err : Miri.Interpreter.StepError)
    (h_ev : Miri.Interpreter.Step.evalStatement
        (refStepHooksFor ts callerMem) ()
        (toMiriStatementForDispatch stmt)
        (mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt)) =
      (st₁, .error err)) :
    evalRefStatement ts rframe callerMem stmt =
      match err with
      | .undefinedBehavior _ => .fault .undefined
      | _ => .fault .unsupported := by
  let st₀ := mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt)
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock false with
      statements := Array.mk [toMiriStatementForDispatch stmt] }
  let fr : RefMiriFrame :=
    { mkSingleLocalMiriFrame .dead false with
      body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
      location := .mir ⟨0, 0⟩ }
  have h_cf : st₀.stack.currentFrame? = some fr := rfl
  have h_loc : fr.location = .mir ⟨0, 0⟩ := rfl
  have h_bb : fr.body.basicBlocks[0]? = some blk := rfl
  have h_st : blk.statements[0]? = some (toMiriStatementForDispatch stmt) := rfl
  have h_step :
      Miri.Interpreter.Step.step (refStepHooksFor ts callerMem) () st₀ =
        (st₁, .error err) := by
    unfold Miri.Interpreter.Step.step
    rw [h_cf]; dsimp only
    rw [h_loc]; dsimp only
    rw [h_bb]; dsimp only
    rw [h_st]; dsimp only
    rw [h_ev]; rfl
  unfold evalRefStatement
  rw [h_step]
  cases err <;> rfl

private theorem evalRefStatement_storageLive (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (localId : LocalId) :
    evalRefStatement ts rframe callerMem (.storageLive localId) =
      match MirSemantics.getElem? rframe.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? rframe.locals localId
            ⟨liveUninitSlot localTy, some localTy⟩ with
        | some rlocals' =>
          .step {
            frames := [{
              rframe with
              stmtIdx := rframe.stmtIdx + 1
              locals := rlocals'
            }]
            callerMem
          }
        | none => .fault .unsupported
      | _ => .fault .unsupported := by
  have h_sl :
      Miri.Interpreter.Step.evalStatement (refStepHooksFor ts callerMem) ()
          (toMiriStatementForDispatch (.storageLive localId))
          (mkRefStmtStepState rframe.locals
            (toMiriStatementForDispatch (.storageLive localId))) =
        let st₀ := mkRefStmtStepState rframe.locals
          (toMiriStatementForDispatch (.storageLive localId))
        match MirSemantics.getElem? rframe.locals localId with
        | some ⟨_, some localTy⟩ =>
          match MirSemantics.setElem? rframe.locals localId
              ⟨refLiveUninitSlot localTy, some localTy⟩ with
          | some rlocals' =>
            ({ st₀ with machine := { locals := rlocals', terminal := none } },
              .ok ())
          | none =>
            (st₀, .error (.unsupported "storageLive local out of bounds"))
        | _ =>
          (st₀,
            .error (.unsupported "storageLive missing cached layout")) := rfl
  cases h_get : MirSemantics.getElem? rframe.locals localId with
  | none =>
    rw [h_get] at h_sl
    exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sl
  | some rloc =>
    cases rloc with
    | mk slot optTy =>
      cases optTy with
      | none =>
        rw [h_get] at h_sl
        exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sl
      | some localTy =>
        dsimp only
        rw [h_get] at h_sl
        dsimp only at h_sl
        rw [refLiveUninitSlot_eq] at h_sl
        cases h_set : MirSemantics.setElem? rframe.locals localId
            ⟨liveUninitSlot localTy, some localTy⟩ with
        | none =>
          rw [h_set] at h_sl
          exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sl
        | some rlocals' =>
          rw [h_set] at h_sl
          exact evalRefStatement_of_ok ts rframe callerMem _ _ h_sl

private theorem evalRefStatement_storageDead_zero (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (localId : LocalId)
    (h0 : Nat.beq localId 0 = true) :
    evalRefStatement ts rframe callerMem (.storageDead localId) =
      .fault .unsupported := by
  cases localId with
  | zero => rfl
  | succ _ => cases h0

private theorem evalRefStatement_storageDead_nonzero (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (localId : LocalId)
    (h0 : Nat.beq localId 0 = false) :
    evalRefStatement ts rframe callerMem (.storageDead localId) =
      match MirSemantics.getElem? rframe.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? rframe.locals localId
            ⟨.dead, some localTy⟩ with
        | some rlocals' =>
          .step {
            frames := [{
              rframe with
              stmtIdx := rframe.stmtIdx + 1
              locals := rlocals'
            }]
            callerMem
          }
        | none => .fault .unsupported
      | _ => .fault .unsupported := by
  cases localId with
  | zero => cases h0
  | succ n =>
    have h_sd :
        Miri.Interpreter.Step.evalStatement (refStepHooksFor ts callerMem) ()
            (toMiriStatementForDispatch (.storageDead (n + 1)))
            (mkRefStmtStepState rframe.locals
              (toMiriStatementForDispatch (.storageDead (n + 1)))) =
          let st₀ := mkRefStmtStepState rframe.locals
            (toMiriStatementForDispatch (.storageDead (n + 1)))
          match MirSemantics.getElem? rframe.locals (n + 1) with
          | some ⟨_, some localTy⟩ =>
            match MirSemantics.setElem? rframe.locals (n + 1)
                ⟨.dead, some localTy⟩ with
            | some rlocals' =>
              ({ st₀ with machine := { locals := rlocals', terminal := none } },
                .ok ())
            | none =>
              (st₀, .error (.unsupported "storageDead local out of bounds"))
          | _ =>
            (st₀, .error (.unsupported "storageDead missing cached layout")) :=
      rfl
    cases h_get : MirSemantics.getElem? rframe.locals (n + 1) with
    | none =>
      rw [h_get] at h_sd
      exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sd
    | some rloc =>
      cases rloc with
      | mk slot optTy =>
        cases optTy with
        | none =>
          rw [h_get] at h_sd
          exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sd
        | some localTy =>
          dsimp only
          rw [h_get] at h_sd
          dsimp only at h_sd
          cases h_set : MirSemantics.setElem? rframe.locals (n + 1)
              ⟨.dead, some localTy⟩ with
          | none =>
            rw [h_set] at h_sd
            exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sd
          | some rlocals' =>
            rw [h_set] at h_sd
            exact evalRefStatement_of_ok ts rframe callerMem _ _ h_sd

private theorem evalRefStatement_assign (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (dst : RefPlace)
    (rvalue : RefRvalue) :
    evalRefStatement ts rframe callerMem (.assign dst rvalue) =
      match evalRefMiriRvalue ts rframe.locals (toMiriPlace dst)
          (toMiriRvalue rvalue) with
      | .error k => .fault k
      | .ok rlocalsAfterWrite =>
        .step {
          frames := [{
            rframe with
            stmtIdx := rframe.stmtIdx + 1
            locals := rlocalsAfterWrite
          }]
          callerMem
        } := by
  have h_as :
      Miri.Interpreter.Step.evalStatement (refStepHooksFor ts callerMem) ()
          (toMiriStatementForDispatch (.assign dst rvalue))
          (mkRefStmtStepState rframe.locals
            (toMiriStatementForDispatch (.assign dst rvalue))) =
        let st₀ := mkRefStmtStepState rframe.locals
          (toMiriStatementForDispatch (.assign dst rvalue))
        match evalRefMiriRvalue ts rframe.locals (toMiriPlace dst)
            (toMiriRvalue rvalue) with
        | .error k => (st₀, .error (faultToStepError k))
        | .ok rlocalsAfterWrite =>
          ({ st₀ with machine :=
              { locals := rlocalsAfterWrite, terminal := none } },
            .ok ()) := rfl
  cases h_rv : evalRefMiriRvalue ts rframe.locals (toMiriPlace dst)
      (toMiriRvalue rvalue) with
  | error k =>
    rw [h_rv] at h_as
    dsimp only at h_as
    rw [evalRefStatement_of_err ts rframe callerMem _ _ _ h_as]
    cases k <;> rfl
  | ok rlocalsAfterWrite =>
    rw [h_rv] at h_as
    dsimp only at h_as
    exact evalRefStatement_of_ok ts rframe callerMem _ _ h_as

theorem evalRefStatement_eq {ts : List MirTy} {body : Body} {f : FrameState}
    {callerMem : CallerMemory} {rstmt : RefStatementKind} {stmt : StatementKind}
    (h_len : f.locals.length = body.locals.length)
    (h_tys : ∀ (id : LocalId) (ty : MirTy),
      MirSemantics.getElem? body.locals id = some ty →
      ∃ tid, MirSemantics.getElem? ts tid = some ty)
    (h_dec : decodeStmt ts rstmt = some stmt) :
    evalRefStatement ts (liftFrame body.locals f) callerMem rstmt =
      mapStepRes body.locals (evalStatement body f callerMem stmt) := by
  cases rstmt with
  | nop =>
    injection h_dec with h_eq
    subst h_eq
    rfl
  | storageLive localId =>
    injection h_dec with h_eq
    subst h_eq
    rw [evalRefStatement_storageLive]
    dsimp only [evalStatement, liftFrame]
    cases h_ty : MirSemantics.getElem? body.locals localId with
    | none =>
      rw [getElem?_zipRefLocals_none_left h_ty]
      rfl
    | some localTy =>
      let ⟨slot, h_sl⟩ := getElem?_some_of_length_eq h_len.symm h_ty
      rw [getElem?_zipRefLocals_some h_ty h_sl]
      dsimp only
      cases h_set :
          MirSemantics.setElem? f.locals localId (liveUninitSlot localTy) with
      | none =>
        rw [setElem?_zipRefLocals_none h_set]
        rfl
      | some locals' =>
        rw [setElem?_zipRefLocals_some h_ty h_set]
        rfl
  | storageDead localId =>
    injection h_dec with h_eq
    subst h_eq
    dsimp only [evalStatement]
    cases h0 : Nat.beq localId 0
    · rw [evalRefStatement_storageDead_nonzero _ _ _ _ h0]
      dsimp only [liftFrame]
      cases h_set : MirSemantics.setElem? f.locals localId .dead with
      | none =>
        have h_sl_none := getElem?_none_of_setElem?_none h_set
        rw [getElem?_zipRefLocals_none_right h_sl_none]
        rfl
      | some locals' =>
        let ⟨slot, h_sl⟩ := getElem?_some_of_setElem?_some h_set
        let ⟨localTy, h_ty⟩ := getElem?_some_of_length_eq h_len h_sl
        rw [getElem?_zipRefLocals_some h_ty h_sl]
        dsimp only
        rw [setElem?_zipRefLocals_some h_ty h_set]
        rfl
    · rw [evalRefStatement_storageDead_zero _ _ _ _ h0]
      rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt, optMap2] at h_dec
    cases h_pl : decodePlace ts rdst with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some dst =>
      cases h_rv : decodeRvalue ts rrv with
      | none => rw [h_pl, h_rv] at h_dec; cases h_dec
      | some rv =>
        rw [h_pl, h_rv] at h_dec
        injection h_dec with h_eq
        subst h_eq
        rw [evalRefStatement_assign]
        dsimp only [evalStatement, liftFrame]
        rw [evalRefMiriRvalue_eq h_len h_tys h_pl h_rv]
        cases dst.projection.isEmpty
        · rfl
        · dsimp only [Bool.not, ite_false_eq_true]
          cases MirSemantics.getElem? body.locals dst.localId with
          | none => rfl
          | some dstTy =>
            dsimp only
            cases evalRvalue body.locals f.locals dstTy rv with
            | error _ => rfl
            | ok res =>
              cases res with
              | mk val localsAfterRval =>
                dsimp only
                cases writePlace localsAfterRval dst.localId dstTy val <;> rfl
  | unsupported =>
    injection h_dec with h_eq
    subst h_eq
    rfl

private theorem step_term_eq (ts : List MirTy) (callerMem : CallerMemory)
    (rlocals : List RefLocalState) (term : Miri.MIR.Terminator)
    (cleanup : Bool) :
    Miri.Interpreter.Step.step (refStepHooksFor ts callerMem) ()
        (mkRefTermStepState rlocals term cleanup) =
      let r := Miri.Interpreter.ControlFlow.evalTerminator
        (refTerminatorHooksFor ts callerMem) () term
        (mkRefTermStepState rlocals term cleanup)
      (r.1, r.2.map fun _ => true) := rfl

private theorem evalRefTerminator_eq_of_term (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory) :
    evalRefTerminator ts rbb rframe callerMem =
      match Miri.Interpreter.ControlFlow.evalTerminator
          (refTerminatorHooksFor ts callerMem) ()
          (toMiriTerminatorForDispatch rbb.terminator)
          (mkRefTermStepState rframe.locals
            (toMiriTerminatorForDispatch rbb.terminator) rbb.cleanup) with
      | (st', .ok ()) =>
        match st'.machine.terminal with
        | some res => res
        | none =>
          match extractMirLocation? st' with
          | some loc =>
            .step {
              frames := [{
                rframe with
                blockIdx := loc.block
                stmtIdx := loc.statementIndex
                locals := st'.machine.locals
              }]
              callerMem
            }
          | none => .fault .unsupported
      | (_, .error (.undefinedBehavior _)) => .fault .undefined
      | (_, _) => .fault .unsupported := by
  unfold evalRefTerminator
  rw [step_term_eq]
  cases Miri.Interpreter.ControlFlow.evalTerminator
      (refTerminatorHooksFor ts callerMem) ()
      (toMiriTerminatorForDispatch rbb.terminator)
      (mkRefTermStepState rframe.locals
        (toMiriTerminatorForDispatch rbb.terminator) rbb.cleanup) with
  | mk st' res =>
    cases res with
    | ok u => cases u; rfl
    | error e => cases e <;> rfl

private noncomputable def expectedReturnEval (rframe : RefFrameState)
    (callerMem : CallerMemory) :
    Option RefLocalState →
      Miri.Interpreter.StepResult RefStepState Unit
  | some ⟨.live (some retVal), some _⟩ =>
    ({ stack := Miri.Interpreter.Stack.empty
       machine :=
         { locals := rframe.locals
           terminal := some (.done (.returned ⟨retVal, callerMem⟩)) } },
     .ok ())
  | some ⟨.live none, some _⟩ | some ⟨.dead, some _⟩ =>
    ({ stack := Miri.Interpreter.Stack.empty
       machine := { locals := rframe.locals, terminal := none } },
     .error (.undefinedBehavior "uninit or dead return place"))
  | _ =>
    ({ stack := Miri.Interpreter.Stack.empty
       machine := { locals := rframe.locals, terminal := none } },
     .error (.unsupported "missing return place"))

private theorem evalTerminator_return_ref
    (hooks : Miri.Interpreter.TerminatorHooks (Option Val)
      Miri.Interpreter.LocalLayout Unit RefStepMachine Unit Unit Val)
    (st₀ stPop st₁ : RefStepState) (fr frPop : RefMiriFrame)
    (blk : Miri.MIR.BasicBlock)
    (out : Except Miri.Interpreter.StepError Unit)
    (h_cf : st₀.stack.currentFrame? = some fr)
    (h_loc : fr.location = .mir ⟨0, 0⟩)
    (h_bb : fr.body.basicBlocks[0]? = some blk)
    (h_cl_blk : blk.cleanup = false)
    (h_ro : hooks.toControlHooks.returnOperand () st₀ = (st₀, .ok ()))
    (h_pf : hooks.toControlHooks.popFrame () st₀ = (stPop, .ok frPop))
    (h_cp : hooks.toControlHooks.copyReturn () () frPop.returnPlace stPop =
      (st₁, out))
    (h_cl : hooks.toControlHooks.cleanupFrame () false frPop st₁ =
      (st₁, .ok .normal))
    (h_cont : frPop.returnContinuation = .stop false)
    (h_st : st₁.stack = Miri.Interpreter.Stack.empty) :
    Miri.Interpreter.ControlFlow.evalTerminator hooks ()
      (toMiriTerminatorForDispatch .return_) st₀ = (st₁, out) := by
  cases hooks with
  | mk ch _ _ _ _ _ _ _ _ =>
    cases ch with
    | mk _ ro pf cr cf _ =>
      dsimp only at h_ro h_pf h_cp h_cl
      unfold Miri.Interpreter.ControlFlow.evalTerminator
        Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      dsimp only [toMiriTerminatorForDispatch, Id.run, Bind.bind, Pure.pure]
      rw [h_cf]; dsimp only
      rw [h_loc]; dsimp only
      rw [h_bb]; dsimp only
      rw [h_cl_blk]
      have h_bne : (false != false) = false := rfl
      rw [h_bne]
      simp only [Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
        Bool.not_false]
      rw [h_ro]; dsimp only
      rw [h_pf]; dsimp only
      rw [h_cp]; dsimp only
      cases out with
      | error _ => rfl
      | ok u =>
        cases u
        rw [h_cl]; dsimp only
        rw [h_cont]; dsimp only
        rw [h_st]
        rfl

private theorem evalRefTerminator_return_false (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = false) :
    evalRefTerminator ts rbb rframe callerMem =
      match MirSemantics.getElem? rframe.locals 0 with
      | some ⟨.live (some retVal), some _⟩ =>
        .done (.returned ⟨retVal, callerMem⟩)
      | some ⟨.live none, some _⟩ | some ⟨.dead, some _⟩ =>
        .fault .undefined
      | _ => .fault .unsupported := by
  have h_case : ∀ (opt : Option RefLocalState),
      MirSemantics.getElem? rframe.locals 0 = opt →
      evalRefTerminator ts rbb rframe callerMem =
        match opt with
        | some ⟨.live (some retVal), some _⟩ =>
          .done (.returned ⟨retVal, callerMem⟩)
        | some ⟨.live none, some _⟩ | some ⟨.dead, some _⟩ =>
          .fault .undefined
        | _ => .fault .unsupported := by
    intro opt h_get
    rw [evalRefTerminator_eq_of_term, h_rt, h_cl]
    let st₀ := mkRefTermStepState rframe.locals
      (toMiriTerminatorForDispatch .return_) false
    let stPop : RefStepState :=
      { stack := Miri.Interpreter.Stack.empty
        machine := { locals := rframe.locals, terminal := none } }
    let blk : Miri.MIR.BasicBlock :=
      { refDummyMirBlock false with
        terminator := toMiriTerminatorForDispatch .return_ }
    let fr : RefMiriFrame :=
      { mkSingleLocalMiriFrame .dead false with
        body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
        location := .mir ⟨0, 0⟩ }
    have h_cf : st₀.stack.currentFrame? = some fr := rfl
    have h_loc : fr.location = .mir ⟨0, 0⟩ := rfl
    have h_bb : fr.body.basicBlocks[0]? = some blk := rfl
    have h_cp_eq :
        (refTerminatorHooksFor ts callerMem).toControlHooks.copyReturn () ()
          (mkSingleLocalMiriFrame .dead false).returnPlace stPop =
          expectedReturnEval rframe callerMem opt := by
      dsimp only [refTerminatorHooksFor,
        Miri.Interpreter.TerminatorHooks.toControlHooks, stPop]
      rw [h_get]
      cases opt with
      | none => rfl
      | some rloc =>
        cases rloc with
        | mk slot optTy =>
          cases slot with
          | dead => cases optTy <;> rfl
          | live optVal =>
            cases optVal with
            | none => cases optTy <;> rfl
            | some _ => cases optTy <;> rfl
    have h_st_empty :
        (expectedReturnEval rframe callerMem opt).1.stack =
          Miri.Interpreter.Stack.empty := by
      cases opt with
      | none => rfl
      | some rloc =>
        cases rloc with
        | mk slot optTy =>
          cases slot with
          | dead => cases optTy <;> rfl
          | live optVal =>
            cases optVal with
            | none => cases optTy <;> rfl
            | some _ => cases optTy <;> rfl
    have h_eval := evalTerminator_return_ref
      (refTerminatorHooksFor ts callerMem) st₀ stPop
      (expectedReturnEval rframe callerMem opt).1 fr
      (mkSingleLocalMiriFrame .dead false) blk
      (expectedReturnEval rframe callerMem opt).2
      h_cf h_loc h_bb rfl rfl rfl h_cp_eq rfl rfl h_st_empty
    change (match Miri.Interpreter.ControlFlow.evalTerminator
        (refTerminatorHooksFor ts callerMem) ()
        (toMiriTerminatorForDispatch .return_) st₀ with
      | (st', .ok ()) =>
        match st'.machine.terminal with
        | some res => res
        | none =>
          match extractMirLocation? st' with
          | some loc =>
            .step {
              frames := [{
                rframe with
                blockIdx := loc.block
                stmtIdx := loc.statementIndex
                locals := st'.machine.locals
              }]
              callerMem
            }
          | none => .fault .unsupported
      | (_, .error (.undefinedBehavior _)) => .fault .undefined
      | (_, _) => .fault .unsupported) = _
    rw [h_eval]
    cases opt with
    | none => rfl
    | some rloc =>
      cases rloc with
      | mk slot optTy =>
        cases slot with
        | dead => cases optTy <;> rfl
        | live optVal =>
          cases optVal with
          | none => cases optTy <;> rfl
          | some _ => cases optTy <;> rfl
  exact h_case _ rfl

private theorem evalRefTerminator_return_true (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = true) :
    evalRefTerminator ts rbb rframe callerMem = .fault .unsupported := by
  unfold evalRefTerminator
  rw [h_rt, h_cl]
  rfl

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

private theorem switchInt_forIn_cons {st : RefStepState}
    (cmp : Nat → RefStepState → Miri.Interpreter.StepResult RefStepState Bool)
    (caseBits : BitVec 128) (target otherwise : BasicBlockId)
    (rest : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (((caseBits, target) :: rest).map
        (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
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
        ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
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

private theorem switchInt_forIn_scalar {ts : List MirTy}
    {callerMem : CallerMemory}
    (rlocals : List RefLocalState) (mframe : RefMiriFrame)
    (sv : ScalarVal) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
        ({ stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } } : RefStepState),
        otherwise)
      (fun case __s =>
        have __s := __s.snd
        have state := __s.fst
        have target := __s.snd
        match case with
        | Miri.MIR.SwitchTarget.Case bits block =>
          match (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
              (.scalar sv) bits state with
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
      match evalSwitchBranches sv.width sv.bits otherwise branches with
      | .error _ =>
        (some ({ stack := ⟨Array.mk [mframe]⟩
                 machine := { locals := rlocals, terminal := none } },
               .error (faultToStepError .unsupported)),
         { stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } },
         otherwise)
      | .ok target =>
        (none,
         { stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } },
         target) := by
  induction branches with
  | nil =>
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest ih =>
    cases hd with
    | mk caseBits target =>
      rw [switchInt_forIn_cons
        (cmp := (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
          (.scalar sv))]
      rw [evalRefSwitchScalarCase_eq]
      dsimp only [evalSwitchBranches]
      cases (truncateBits sv.width caseBits != caseBits) with
      | true => rfl
      | false =>
        cases (truncateBits sv.width sv.bits ==
            truncateBits sv.width caseBits) with
        | false => exact ih
        | true => rfl

private theorem switchInt_forIn_bool {ts : List MirTy}
    {callerMem : CallerMemory}
    (rlocals : List RefLocalState) (mframe : RefMiriFrame)
    (b : Bool) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
        ({ stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } } : RefStepState),
        otherwise)
      (fun case __s =>
        have __s := __s.snd
        have state := __s.fst
        have target := __s.snd
        match case with
        | Miri.MIR.SwitchTarget.Case bits block =>
          match (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
              (.bool b) bits state with
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
      match evalBoolSwitchBranches b otherwise branches with
      | .error k =>
        (some ({ stack := ⟨Array.mk [mframe]⟩
                 machine := { locals := rlocals, terminal := none } },
               .error (faultToStepError k)),
         { stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } },
         otherwise)
      | .ok target =>
        (none,
         { stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } },
         target) := by
  induction branches with
  | nil =>
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest ih =>
    cases hd with
    | mk caseBits target =>
      rw [switchInt_forIn_cons
        (cmp := (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
          (.bool b))]
      rw [evalRefSwitchBoolCase_eq]
      dsimp only [evalBoolSwitchBranches]
      cases h_cl : evalConstLit .bool (.scalar caseBits) with
      | error k => rfl
      | ok v =>
        cases evalConstLit_bool_scalar_is_bool caseBits v h_cl with
        | intro cb h_cb =>
          subst h_cb
          cases cb <;> cases b
          · rfl
          · exact ih
          · exact ih
          · rfl

private theorem evalRefTerminator_switchInt (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (rdiscr : RefOperand) (targets : SwitchTargets)
    (h_rt : rbb.terminator = .switchInt rdiscr targets) :
    evalRefTerminator ts rbb rframe callerMem =
      match evalRefMiriOperandToSlot ts rframe.locals
          (toMiriOperand rdiscr) with
      | .error k => .fault k
      | .ok (ty, optVal, rlocalsAfterDiscr) =>
        match readRefPrimitiveSlot ty optVal with
        | .error k => .fault k
        | .ok discrVal =>
          let targetRes : Except FaultKind BasicBlockId :=
            match discrVal with
            | .scalar sv =>
              evalSwitchBranches sv.width sv.bits targets.otherwise
                targets.branches
            | .bool b =>
              evalBoolSwitchBranches b targets.otherwise targets.branches
            | _ => .error .unsupported
          match targetRes with
          | .error k => .fault k
          | .ok target =>
            .step {
              frames := [{
                rframe with
                blockIdx := target
                stmtIdx := 0
                locals := rlocalsAfterDiscr
              }]
              callerMem
            } := by
  rw [evalRefTerminator_eq_of_term, h_rt]
  let mirTerm : Miri.MIR.Terminator :=
    { sourceInfo := { span := { id := 0 }, scope := 0 }
      kind := .SwitchInt (toMiriOperand rdiscr)
        { cases := Array.mk
            (targets.branches.map (fun b => .Case b.1.toNat b.2))
          otherwise := targets.otherwise } }
  let mframe : RefMiriFrame := {
    mkSingleLocalMiriFrame .dead rbb.cleanup with
    body := {
      refDummyMirBody rbb.cleanup with
      basicBlocks := Array.mk [{ refDummyMirBlock rbb.cleanup with
        terminator := mirTerm }]
    }
    location := .mir ⟨0, 0⟩
  }
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
    toMiriTerminatorForDispatch, refTerminatorHooksFor,
    mkRefTermStepState, mkRefStepStateWith, Id.run, Bind.bind, Pure.pure]
  cases evalRefMiriOperandToSlot ts rframe.locals (toMiriOperand rdiscr) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨ty, optVal, rlocalsAfterDiscr⟩ := res
    dsimp only
    cases readRefPrimitiveSlot ty optVal with
    | error k => cases k <;> rfl
    | ok discrVal =>
      dsimp only
      cases discrVal with
      | scalar sv =>
        dsimp only
        rw [← Array.forIn_toList]
        dsimp only [Array.toList]
        rw [forIn_list_map_congr (g := fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
                (.scalar sv) bits state with
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
        · rw [@switchInt_forIn_scalar ts callerMem rlocalsAfterDiscr
            mframe sv targets.otherwise targets.branches]
          cases h_sw : evalSwitchBranches sv.width sv.bits targets.otherwise
              targets.branches with
          | error k =>
            have h_unsup :=
              evalSwitchBranches_error_eq_unsupported _ _ _ _ _ h_sw
            subst h_unsup
            rfl
          | ok target => rfl
        · intro x s
          cases (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
              (.scalar sv) x.1.toNat s.snd.fst with
          | mk next comparison =>
            cases comparison with
            | error _ => rfl
            | ok flag => cases flag <;> rfl
      | bool b =>
        dsimp only
        rw [← Array.forIn_toList]
        dsimp only [Array.toList]
        rw [forIn_list_map_congr (g := fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
                (.bool b) bits state with
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
        · rw [@switchInt_forIn_bool ts callerMem rlocalsAfterDiscr
            mframe b targets.otherwise targets.branches]
          cases evalBoolSwitchBranches b targets.otherwise targets.branches with
          | error k => cases k <;> rfl
          | ok target => rfl
        · intro x s
          cases (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
              (.bool b) x.1.toNat s.snd.fst with
          | mk next comparison =>
            cases comparison with
            | error _ => rfl
            | ok flag => cases flag <;> rfl
      | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => rfl

theorem evalRefTerminator_eq {ts : List MirTy} {body : Body}
    {rbb : RefBasicBlock}
    {bb : BasicBlock} {f : FrameState} {callerMem : CallerMemory}
    (h_len : f.locals.length = body.locals.length)
    (h_cleanup : rbb.cleanup = bb.cleanup)
    (h_term : decodeTerminator ts rbb.terminator = some bb.terminator) :
    evalRefTerminator ts rbb (liftFrame body.locals f) callerMem =
      mapStepRes body.locals (evalTerminator body bb f callerMem) := by
  cases h_rt : rbb.terminator with
  | goto target =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl
  | switchInt rdiscr targets =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap] at h_term
    cases h_d : decodeOperand ts rdiscr with
    | none => rw [h_d] at h_term; cases h_term
    | some discr =>
      rw [h_d] at h_term
      injection h_term with h_eq
      rw [evalRefTerminator_switchInt _ _ _ _ _ _ h_rt]
      unfold evalTerminator
      rw [← h_eq]
      dsimp only [liftFrame, evalPrimitiveOperand]
      rw [evalRefMiriOperandToSlot_eq h_d]
      cases evalOperandToSlot body.locals f.locals discr with
      | error _ => rfl
      | ok res =>
        let ⟨ty, optVal, localsAfterDiscr⟩ := res
        dsimp only [mapSlotRes]
        rw [readRefPrimitiveSlot_eq]
        cases isPrimitiveReadableTy ty
        · rfl
        · dsimp only [Bool.not, ite_false_eq_true]
          cases optVal with
          | none => rfl
          | some discrVal =>
            dsimp only
            cases discrVal with
            | scalar sv =>
              dsimp only
              cases evalSwitchBranches sv.width sv.bits targets.otherwise
                targets.branches <;> rfl
            | bool b =>
              dsimp only
              cases evalBoolSwitchBranches b targets.otherwise
                targets.branches <;> rfl
            | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => rfl
  | return_ =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    cases h_cl : bb.cleanup
    · rw [evalRefTerminator_return_false _ _ _ _ h_rt (h_cleanup.trans h_cl)]
      unfold evalTerminator
      rw [← h_eq, h_cl]
      dsimp only [liftFrame]
      cases h_sl : MirSemantics.getElem? f.locals 0 with
      | none =>
        rw [getElem?_zipRefLocals_none_right h_sl]
        rfl
      | some s =>
        let ⟨ty₀, h_ty⟩ := getElem?_some_of_length_eq h_len h_sl
        rw [getElem?_zipRefLocals_some h_ty h_sl]
        cases s with
        | dead => rfl
        | live o => cases o <;> rfl
    · rw [evalRefTerminator_return_true _ _ _ _ h_rt (h_cleanup.trans h_cl)]
      unfold evalTerminator
      rw [← h_eq, h_cl]
      rfl
  | unreachable =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl
  | unwindResume =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl
  | assert rcond exp msg t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap] at h_term
    cases h_c : decodeOperand ts rcond with
    | none => rw [h_c] at h_term; cases h_term
    | some c =>
      rw [h_c] at h_term
      injection h_term with h_eq
      unfold evalRefTerminator evalTerminator
      rw [h_rt, ← h_eq]
      rfl
  | call callee rargs rdst t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap2] at h_term
    cases h_a : mapOption (decodeOperand ts) rargs with
    | none => rw [h_a] at h_term; cases h_term
    | some args =>
      cases h_dst : decodePlace ts rdst with
      | none => rw [h_a, h_dst] at h_term; cases h_term
      | some dst =>
        rw [h_a, h_dst] at h_term
        injection h_term with h_eq
        unfold evalRefTerminator evalTerminator
        rw [h_rt, ← h_eq]
        rfl
  | unsupported =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl

theorem evalStatement_step_inv {body : Body} {f : FrameState}
    {callerMem : CallerMemory} {stmt : StatementKind} {s' : State}
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalStatement body f callerMem stmt = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := callerMem } ∧
      f'.defId = f.defId ∧
      f'.locals.length = body.locals.length := by
  cases stmt with
  | nop =>
    injection h_step with h_eq
    refine ⟨{ f with stmtIdx := f.stmtIdx + 1 }, h_eq.symm, rfl, h_len⟩
  | storageLive localId =>
    dsimp only [evalStatement] at h_step
    cases h_ty : MirSemantics.getElem? body.locals localId with
    | none => rw [h_ty] at h_step; cases h_step
    | some localTy =>
      rw [h_ty] at h_step
      dsimp only at h_step
      cases h_set :
          MirSemantics.setElem? f.locals localId (liveUninitSlot localTy) with
      | none => rw [h_set] at h_step; cases h_step
      | some locals' =>
        rw [h_set] at h_step
        injection h_step with h_eq
        refine ⟨{ f with stmtIdx := f.stmtIdx + 1, locals := locals' },
          h_eq.symm, rfl,
          (setElem?_length h_set).trans h_len⟩
  | storageDead localId =>
    dsimp only [evalStatement] at h_step
    cases h0 : Nat.beq localId 0 <;> rw [h0] at h_step
    · cases h_set : MirSemantics.setElem? f.locals localId .dead with
      | none => rw [h_set] at h_step; cases h_step
      | some locals' =>
        rw [h_set] at h_step
        injection h_step with h_eq
        refine ⟨{ f with stmtIdx := f.stmtIdx + 1, locals := locals' },
          h_eq.symm, rfl,
          (setElem?_length h_set).trans h_len⟩
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
        cases h_rv : evalRvalue body.locals f.locals dstTy rvalue with
        | error _ => rw [h_rv] at h_step; cases h_step
        | ok res =>
          rw [h_rv] at h_step
          cases res with | mk val localsAfterRval =>
          dsimp only at h_step
          cases h_wr : writePlace localsAfterRval dst.localId dstTy val with
          | error _ => rw [h_wr] at h_step; cases h_step
          | ok localsAfterWrite =>
            rw [h_wr] at h_step
            injection h_step with h_eq
            have h_len₁ := (evalRvalue_length h_rv).trans h_len
            have h_len₂ := (writePlace_length h_wr).trans h_len₁
            refine ⟨{ f with
                stmtIdx := f.stmtIdx + 1, locals := localsAfterWrite },
              h_eq.symm, rfl, h_len₂⟩
  | unsupported => cases h_step

theorem evalTerminator_step_inv {body : Body} {bb : BasicBlock}
    {f : FrameState} {callerMem : CallerMemory} {s' : State}
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalTerminator body bb f callerMem = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := callerMem } ∧
      f'.defId = f.defId ∧
      f'.locals.length = body.locals.length := by
  cases bb with | mk stmts term cleanup =>
  cases term with
  | goto target =>
    injection h_step with h_eq
    refine ⟨{ f with blockIdx := target, stmtIdx := 0 }, h_eq.symm, rfl, h_len⟩
  | return_ =>
    dsimp only [evalTerminator] at h_step
    cases cleanup
    · cases h_sl : MirSemantics.getElem? f.locals 0 with
      | none => rw [h_sl] at h_step; cases h_step
      | some s =>
        rw [h_sl] at h_step
        cases s with
        | dead => cases h_step
        | live o => cases o <;> cases h_step
    · cases h_step
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _
  | unsupported =>
    cases h_step
  | switchInt discr targets =>
    dsimp only [evalTerminator] at h_step
    cases h_d : evalPrimitiveOperand body.locals f.locals discr with
    | error _ => rw [h_d] at h_step; cases h_step
    | ok res =>
      rw [h_d] at h_step
      cases res with | mk discrVal localsAfterDiscr =>
      have h_len₁ := (evalPrimitiveOperand_length h_d).trans h_len
      dsimp only at h_step
      cases discrVal with
      | scalar sv =>
        dsimp only at h_step
        cases h_sw : evalSwitchBranches sv.width sv.bits targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_len₁⟩
      | bool b =>
        dsimp only at h_step
        cases h_sw : evalBoolSwitchBranches b targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_len₁⟩
      | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => cases h_step

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

theorem evalStep_step_inv {p : Program} {c : Choice} {s s' : State}
    {f : FrameState} {body : Body}
    (hs : s.frames = [f])
    (h_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalStep p c s = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := s.callerMem } ∧
      f'.defId = f.defId ∧
      f'.locals.length = body.locals.length := by
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
    cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx <;>
      rw [h_st] at h_step
    · dsimp only at h_step
      cases h_end : Nat.beq f.stmtIdx bb.statements.length <;>
        rw [h_end] at h_step
      · cases h_step
      · exact evalTerminator_step_inv h_len h_step
    · exact evalStatement_step_inv h_len h_step

/-- One $M_{\text{ref}}$ step from a simulated state computes exactly the
lifted $M_{\text{anneal}}$ step, with the caller sentinel restored beneath the
top frame. -/
theorem evalRefStep_eq_base : EvalRefStepEqClaim := by
  intro rp p s rs f rf retTy body h_dec hs hrs hcm h_body h_len hrf h_lt c
  let ⟨_, _, _, _, h_bodies⟩ := decodeProg_inv h_dec
  let ⟨rbody, h_rbody_get, h_rbody_dec⟩ :=
    (mapOption_getElem? h_bodies f.defId).2 body h_body
  let ⟨_, h_locs_dec, h_bbs_dec, _, _⟩ := decodeBody_inv h_rbody_dec
  have h_tys : ∀ (id : LocalId) (ty : MirTy),
      MirSemantics.getElem? body.locals id = some ty →
      ∃ tid, MirSemantics.getElem? rp.types tid = some ty := by
    intro id ty h_get
    let ⟨tid, _, h_tid⟩ := (mapOption_getElem? h_locs_dec id).2 ty h_get
    exact ⟨tid, h_tid⟩
  unfold evalRefStep evalStep
  rw [h_lt, hrs, hs, hrf, hcm]
  dsimp only [liftFrame, callerSentinelFrame]
  rw [h_rbody_get, h_body]
  dsimp only
  cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none =>
    rw [(mapOption_getElem? h_bbs_dec f.blockIdx).1 h_bb]
    rfl
  | some bb =>
    let ⟨rbb, h_rbb_get, h_rbb_dec⟩ :=
      (mapOption_getElem? h_bbs_dec f.blockIdx).2 bb h_bb
    let ⟨h_stmts_dec, h_term_dec, h_cleanup⟩ := decodeBasicBlock_inv h_rbb_dec
    rw [h_rbb_get]
    dsimp only
    cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx with
    | none =>
      rw [(mapOption_getElem? h_stmts_dec f.stmtIdx).1 h_st]
      rw [mapOption_length h_stmts_dec]
      dsimp only
      cases Nat.beq f.stmtIdx bb.statements.length
      · rfl
      · exact congrArg
          (stepResultToRefOutcome (callerSentinelFrame retTy)
            rs.stepsExecuted rs.maxSteps)
          (evalRefTerminator_eq h_len h_cleanup h_term_dec)
    | some stmt =>
      let ⟨rstmt, h_rstmt_get, h_rstmt_dec⟩ :=
        (mapOption_getElem? h_stmts_dec f.stmtIdx).2 stmt h_st
      rw [h_rstmt_get]
      dsimp only
      exact congrArg
        (stepResultToRefOutcome (callerSentinelFrame retTy)
          rs.stepsExecuted rs.maxSteps)
        (evalRefStatement_eq h_len h_tys h_rstmt_dec)

end Anneal.MirCorrespondence
