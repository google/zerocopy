-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirTotal.Ops
public import Anneal.MirWp.Execution
public import Anneal.AiPcc.BitArith
public import Anneal.AiPcc.Tnum
public import Anneal.AiPcc.WrappedInterval
public import Anneal.AiPcc.ReducedProduct
public import Anneal.AiPcc.MirBridge
public import Anneal.AiPcc.MirTransfer

public section

namespace Anneal.AiPcc

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal Anneal.MirWp

/-!
# Single-Pass Bourdoncle Cutpoint MIR PCC Checker (`Anneal.AiPcc.MirPcc`)

Verifies untrusted abstract-interpretation certificates over `MirAst.Body` in
a single linear pass over the CFG without fixed-point iteration in the kernel:

1. `checkMirCert`: checks a full per-block invariant map
   `List (Option MirAbsEnv)` (where `none` marks unreachable/dead blocks, such
   as traps), discharging both unbounded-iteration prefix fault-freedom
   (`Anneal.MirWp.SafeFrom`) and frame-independent return-value soundness
   (`ReturnsFrom`).
2. `verifyMirCutpoints`: validates that `rpoOrder` is a duplicate-free,
   full-coverage reverse-postorder permutation modulo `cutpoints`, materializes
   acyclic block states in one linear forward pass, and verifies the resulting
   post-fixpoint via `checkMirCert`.
-/

/-! ## 1. Statement-Prefix Stepping Helpers -/

/-- Runs `stepStmtAbs` across a full statement list left-to-right. -/
@[expose] def stepStmtsAbs (bodyLocals : List MirTy) (env : MirAbsEnv)
    (stmts : List StatementKind) : Option MirAbsEnv :=
  stmts.foldr
    (fun s ih e =>
      match stepStmtAbs bodyLocals e s with
      | some e' => ih e'
      | none => none)
    (fun e => some e)
    env

private theorem stepStmtsAbs_cons (bodyLocals : List MirTy) (env : MirAbsEnv)
    (s : StatementKind) (ss : List StatementKind) :
    stepStmtsAbs bodyLocals env (s :: ss) =
      match stepStmtAbs bodyLocals env s with
      | some env' => stepStmtsAbs bodyLocals env' ss
      | none => none := rfl

/-- Runs `stepStmtAbs` over the first `idx` statements of `stmts`. -/
@[expose] def stepStmtsTo (bodyLocals : List MirTy) (env : MirAbsEnv)
    (stmts : List StatementKind) (idx : Nat) : Option MirAbsEnv :=
  Nat.rec (motive := fun _ => MirAbsEnv → List StatementKind → Option MirAbsEnv)
    (fun e _ => some e)
    (fun _ ih e st =>
      match st with
      | [] => none
      | s :: ss =>
        match stepStmtAbs bodyLocals e s with
        | some e' => ih e' ss
        | none => none)
    idx env stmts

private theorem stepStmtsTo_succ_cons (bodyLocals : List MirTy)
    (env : MirAbsEnv) (s : StatementKind) (ss : List StatementKind) (k : Nat) :
    stepStmtsTo bodyLocals env (s :: ss) (k + 1) =
      match stepStmtAbs bodyLocals env s with
      | some env' => stepStmtsTo bodyLocals env' ss k
      | none => none := rfl

private theorem stepStmtsTo_of_stepStmtsAbs_step {bodyLocals : List MirTy} :
    ∀ {stmts : List StatementKind} {idx : Nat} {env curEnv exitEnv : MirAbsEnv}
      {stmt : StatementKind},
      stepStmtsAbs bodyLocals env stmts = some exitEnv →
      stepStmtsTo bodyLocals env stmts idx = some curEnv →
      compGetElem? stmts idx = some stmt →
      ∃ nextEnv,
        stepStmtAbs bodyLocals curEnv stmt = some nextEnv ∧
        stepStmtsTo bodyLocals env stmts (idx + 1) = some nextEnv
  | [], _, _, _, _, _, _, _, hGet => nomatch hGet
  | s :: ss, 0, env, curEnv, exitEnv, stmt, hAll, hTo, hGet => by
    injection hTo with hCur; subst hCur
    injection hGet with hSt; subst hSt
    rw [stepStmtsAbs_cons] at hAll
    cases h1 : stepStmtAbs bodyLocals env s with
    | none => rw [h1] at hAll; nomatch hAll
    | some env1 =>
      refine ⟨env1, rfl, ?_⟩
      rw [stepStmtsTo_succ_cons, h1]
      rfl
  | s :: ss, k + 1, env, curEnv, exitEnv, stmt, hAll, hTo, hGet => by
    rw [stepStmtsAbs_cons] at hAll
    rw [stepStmtsTo_succ_cons] at hTo
    cases h1 : stepStmtAbs bodyLocals env s with
    | none => rw [h1] at hAll; nomatch hAll
    | some env1 =>
      rw [h1] at hAll hTo
      cases stepStmtsTo_of_stepStmtsAbs_step hAll hTo hGet with
      | intro nextEnv hN =>
        refine ⟨nextEnv, hN.1, ?_⟩
        rw [stepStmtsTo_succ_cons, h1]
        exact hN.2

private theorem stepStmtsTo_len_eq {bodyLocals : List MirTy} :
    ∀ {stmts : List StatementKind} {env curEnv exitEnv : MirAbsEnv},
      stepStmtsAbs bodyLocals env stmts = some exitEnv →
      stepStmtsTo bodyLocals env stmts stmts.length = some curEnv →
      curEnv = exitEnv
  | [], env, curEnv, exitEnv, hAll, hTo => by
    injection hAll with h1; injection hTo with h2
    exact Eq.trans h2.symm h1
  | s :: ss, env, curEnv, exitEnv, hAll, hTo => by
    rw [stepStmtsAbs_cons] at hAll
    dsimp only [List.length] at hTo
    rw [stepStmtsTo_succ_cons] at hTo
    cases h1 : stepStmtAbs bodyLocals env s with
    | none => rw [h1] at hAll; nomatch hAll
    | some env1 =>
      rw [h1] at hAll hTo
      exact stepStmtsTo_len_eq hAll hTo

private theorem compGetElem?_some_of_lt {α : Type} :
    ∀ (xs : List α) (i : Nat), i < xs.length → ∃ x, compGetElem? xs i = some x
  | [], _, h => nomatch h
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, i + 1, h => compGetElem?_some_of_lt xs i (Nat.lt_of_succ_lt_succ h)

private theorem compGetElem?_none_of_len {α : Type} :
    ∀ (xs : List α), compGetElem? xs xs.length = none
  | [] => rfl
  | _ :: xs => compGetElem?_none_of_len xs

/-! ## 2. Full-Map Certificate Checker (`checkMirCert`) and Soundness -/

/-- Checks every feasible successor edge `(tgt, envT)` of a block against
`body.basicBlocks` and the certificate invariant map `invs`. -/
@[expose] def checkEdgesAgainstCert (body : Body) (invs : List (Option
    MirAbsEnv))
    (edges : List (BasicBlockId × MirAbsEnv)) : Bool :=
  edges.foldr
    (fun p ih =>
      (match compGetElem? body.basicBlocks p.1, compGetElem? invs p.1 with
       | some _, some (some invT) => mirAbsEnvLe p.2 invT
       | _, _ => false) && ih)
    true

private theorem checkEdgesAgainstCert_cons (body : Body)
    (invs : List (Option MirAbsEnv)) (t : BasicBlockId) (e : MirAbsEnv)
    (rest : List (BasicBlockId × MirAbsEnv)) :
    checkEdgesAgainstCert body invs ((t, e) :: rest) =
      ((match compGetElem? body.basicBlocks t, compGetElem? invs t with
        | some _, some (some invT) => mirAbsEnvLe e invT
        | _, _ => false) &&
       checkEdgesAgainstCert body invs rest) := rfl

private theorem checkEdgesAgainstCert_mem {body : Body}
    {invs : List (Option MirAbsEnv)} {edges : List (BasicBlockId × MirAbsEnv)}
    {tgt : BasicBlockId} {envT : MirAbsEnv}
    (hChk : checkEdgesAgainstCert body invs edges = true)
    (hMem : (tgt, envT) ∈ edges) :
    ∃ bbT invT,
      compGetElem? body.basicBlocks tgt = some bbT ∧
      compGetElem? invs tgt = some (some invT) ∧
      mirAbsEnvLe envT invT = true := by
  induction edges with
  | nil => nomatch hMem
  | cons hd rest ih =>
    cases hd with | mk t e =>
    rw [checkEdgesAgainstCert_cons] at hChk
    cases hMem with
    | head =>
      have hHead := bool_and_true_left hChk
      cases hBb : compGetElem? body.basicBlocks tgt with
      | none => rw [hBb] at hHead; nomatch hHead
      | some bbT =>
        cases hInv : compGetElem? invs tgt with
        | none => rw [hBb, hInv] at hHead; nomatch hHead
        | some optInv =>
          cases optInv with
          | none => rw [hBb, hInv] at hHead; nomatch hHead
          | some invT =>
            rw [hBb, hInv] at hHead
            exact ⟨bbT, invT, rfl, rfl, hHead⟩
    | tail _ hTail =>
      exact ih (bool_and_true_right hChk) hTail

/-- Checks one basic block `bb` under its certificate entry invariant `invOpt`.
Blocks with `invOpt = none` are dead/unreachable and skipped. -/
@[expose] def checkBlockCert (body : Body) (retInv : MirAbsSlot)
    (invs : List (Option MirAbsEnv)) (bb : BasicBlock)
    (invOpt : Option MirAbsEnv) : Bool :=
  match invOpt with
  | none => true
  | some entryEnv =>
    match stepStmtsAbs body.locals entryEnv bb.statements with
    | none => false
    | some exitEnv =>
      match stepTermAbs body.locals bb exitEnv with
      | none => false
      | some (.ret retSlot) => MirAbsSlot.le retSlot retInv
      | some (.edges succs) => checkEdgesAgainstCert body invs succs

/-- Pointwise check across all `(bb, invOpt)` pairs in `body.basicBlocks` and
`invs`. -/
@[expose] def checkAllBlocksCert (body : Body) (retInv : MirAbsSlot)
    (invs : List (Option MirAbsEnv)) (bbs : List BasicBlock)
    (os : List (Option MirAbsEnv)) : Bool :=
  bbs.foldr
    (fun bb ih curOs =>
      match curOs with
      | [] => false
      | invOpt :: rest =>
        checkBlockCert body retInv invs bb invOpt && ih rest)
    (fun curOs =>
      match curOs with
      | [] => true
      | _ :: _ => false)
    os

private theorem checkAllBlocksCert_get {body : Body} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)} :
    ∀ {bbs : List BasicBlock} {os : List (Option MirAbsEnv)} {i : Nat}
      {bb : BasicBlock} {invOpt : Option MirAbsEnv},
      checkAllBlocksCert body retInv invs bbs os = true →
      compGetElem? bbs i = some bb →
      compGetElem? os i = some invOpt →
      checkBlockCert body retInv invs bb invOpt = true
  | [], [], _, _, _, _, h1, _ => nomatch h1
  | [], _ :: _, _, _, _, h, _, _ => nomatch h
  | _ :: _, [], _, _, _, h, _, _ => nomatch h
  | _ :: _, _ :: _, 0, _, _, h, h1, h2 => by
    injection h1 with hb; injection h2 with ho; subst hb; subst ho
    exact bool_and_true_left h
  | _ :: bbs, _ :: os, i + 1, bb, invOpt, h, h1, h2 =>
    checkAllBlocksCert_get (bbs := bbs) (os := os)
      (bool_and_true_right h) h1 h2

/-- Full-map post-fixpoint certificate checker for `body`, starting from
`entryEnv` (whose length must match `body.locals.length`) at block `0` and
certifying guard-free return-value postcondition `retInv`. -/
@[expose] def checkMirCert (body : Body) (entryEnv : MirAbsEnv) (retInv :
    MirAbsSlot)
    (invs : List (Option MirAbsEnv)) : Bool :=
  Nat.beq entryEnv.length body.locals.length &&
  retInv.noRelGuard &&
  (match compGetElem? body.basicBlocks 0, compGetElem? invs 0 with
   | some _, some (some inv0) => mirAbsEnvLe entryEnv inv0
   | _, _ => false) &&
  checkAllBlocksCert body retInv invs body.basicBlocks invs

/-- Concrete state invariant maintained across all `Reach` transitions of a
certified `Body`. -/
@[expose] def MirPccInv (body : Body) (invs : List (Option MirAbsEnv)) (s :
    State) : Prop :=
  ∃ frame bb entryEnv curEnv,
    s.frames = [frame] ∧
    frame.defId = 0 ∧
    frame.sysrootOp? = none ∧
    compGetElem? body.basicBlocks frame.blockIdx = some bb ∧
    compGetElem? invs frame.blockIdx = some (some entryEnv) ∧
    frame.stmtIdx ≤ bb.statements.length ∧
    stepStmtsTo body.locals entryEnv bb.statements frame.stmtIdx = some curEnv ∧
    mirAbsEnvDenote body.locals curEnv frame.locals

private theorem mirPccInv_step_and_safe {body : Body} {retInv : MirAbsSlot}
    {invs : List (Option MirAbsEnv)} {s : State}
    (hAll : checkAllBlocksCert body retInv invs body.basicBlocks invs = true)
    (hInv : MirPccInv body invs s) :
    (∀ k, evalStep (bodyProg body) 0 s ≠ .fault k) ∧
    (∀ next, evalStep (bodyProg body) 0 s = .step next → MirPccInv body invs next) ∧
    (∀ retVal cMem,
      evalStep (bodyProg body) 0 s = .done (.returned ⟨retVal, cMem⟩) →
      ∃ retTy locals,
        compGetElem? body.locals 0 = some retTy ∧
        retInv.denote retTy locals (.immediate (some retVal))) := by
  cases hInv with | intro frame hInv =>
  cases hInv with | intro bb hInv =>
  cases hInv with | intro entryEnv hInv =>
  cases hInv with | intro curEnv hInv =>
  have hFrames := hInv.1
  have hDef0 := hInv.2.1
  have hSys := hInv.2.2.1
  have hBb := hInv.2.2.2.1
  have hInvB := hInv.2.2.2.2.1
  have hIdxLe := hInv.2.2.2.2.2.1
  have hTo := hInv.2.2.2.2.2.2.1
  have hDen := hInv.2.2.2.2.2.2.2
  have hBlkChk := checkAllBlocksCert_get hAll hBb hInvB
  dsimp only [checkBlockCert] at hBlkChk
  cases hStmts : stepStmtsAbs body.locals entryEnv bb.statements with
  | none => rw [hStmts] at hBlkChk; nomatch hBlkChk
  | some exitEnv =>
    rw [hStmts] at hBlkChk
    dsimp only at hBlkChk
    cases hTerm : stepTermAbs body.locals bb exitEnv with
    | none => rw [hTerm] at hBlkChk; nomatch hBlkChk
    | some out =>
      rw [hTerm] at hBlkChk
      cases Nat.eq_or_lt_of_le hIdxLe with
      | inr hIdxLt =>
        cases compGetElem?_some_of_lt bb.statements frame.stmtIdx hIdxLt with
        | intro stmt hStmt =>
          cases stepStmtsTo_of_stepStmtsAbs_step hStmts hTo hStmt with
          | intro nextEnv hNext =>
            cases stepStmtAbs_sound (body := body) (frame := frame)
                (mem := s.mem) (callerMem := s.callerMem) hDen hNext.1 with
            | intro locals' hEvalStmt =>
              have hEvalStep :
                  evalStep (bodyProg body) 0 s =
                    .step {
                      frames := [{ frame with
                        stmtIdx := frame.stmtIdx + 1, locals := locals' }]
                      callerMem := s.callerMem
                      mem := s.mem
                    } := by
                dsimp only [evalStep, bodyProg]
                rw [hFrames]
                dsimp only [activeFrameBody]
                rw [hSys, hDef0]
                dsimp only [Trusted.MirSemantics.getElem?]
                rw [← compGetElem?_eq, hBb]
                dsimp only
                rw [← compGetElem?_eq, hStmt]
                dsimp only [attachCallers]
                rw [← hDef0]
                have hStmtEq := hEvalStmt.1
                rw [hSys] at hStmtEq
                exact hStmtEq
              refine ⟨?_, ?_, ?_⟩
              · intro k hF; rw [hEvalStep] at hF; nomatch hF
              · intro next hStep
                rw [hEvalStep] at hStep
                injection hStep with hEq; subst hEq
                exact ⟨_, bb, entryEnv, nextEnv, rfl, hDef0, hSys, hBb, hInvB,
                  Nat.succ_le_of_lt hIdxLt, hNext.2, hEvalStmt.2⟩
              · intro _ _ hDone; rw [hEvalStep] at hDone; nomatch hDone
      | inl hIdxEq =>
        have hCurEq := stepStmtsTo_len_eq hStmts (by rw [← hIdxEq]; exact hTo)
        subst hCurEq
        have hNoneStmt : compGetElem? bb.statements frame.stmtIdx = none := by
          rw [hIdxEq]; exact compGetElem?_none_of_len bb.statements
        have hBeqLen : Nat.beq frame.stmtIdx bb.statements.length = true := by
          rw [hIdxEq, nat_beq_refl]
        have hEvalStepEq :
            evalStep (bodyProg body) 0 s =
              evalTerminator body bb frame s.mem s.callerMem := by
          dsimp only [evalStep, bodyProg]
          rw [hFrames]
          dsimp only [activeFrameBody]
          rw [hSys, hDef0]
          dsimp only [Trusted.MirSemantics.getElem?]
          rw [← compGetElem?_eq, hBb]
          dsimp only
          rw [← compGetElem?_eq, hNoneStmt]
          dsimp only
          rw [hBeqLen]
          cases hT : bb.terminator with
          | call _ _ _ _ _ =>
            dsimp only [stepTermAbs] at hTerm; rw [hT] at hTerm; nomatch hTerm
          | sysrootCall _ _ _ _ _ =>
            dsimp only [stepTermAbs] at hTerm; rw [hT] at hTerm; nomatch hTerm
          | _ => rfl
        have hTermS := stepTermAbs_sound (body := body) (bb := bb)
          (frame := frame) (mem := s.mem) (callerMem := s.callerMem) hDen hTerm
        cases out with
        | ret retSlot =>
          cases hTermS with | intro rv hTermS =>
          cases hTermS with | intro retTy hTermS =>
          have hTy0 := hTermS.1
          have hEvalT := hTermS.2.1
          have hRetDen := hTermS.2.2
          have hStepDone :
              evalStep (bodyProg body) 0 s =
                .done (.returned ⟨rv, s.callerMem⟩) :=
            Eq.trans hEvalStepEq hEvalT
          refine ⟨?_, ?_, ?_⟩
          · intro k hF; rw [hStepDone] at hF; nomatch hF
          · intro _ hSt; rw [hStepDone] at hSt; nomatch hSt
          · intro retVal cMem hDone
            rw [hStepDone] at hDone
            injection hDone with hOutEq
            injection hOutEq with hRetOutEq
            injection hRetOutEq with hRvEq _
            subst hRvEq
            exact ⟨retTy, frame.locals, hTy0, mirAbsSlot_le_sound hBlkChk hRetDen⟩
        | edges succs =>
          cases hTermS with | intro tgt hTermS =>
          cases hTermS with | intro envT hTermS =>
          cases hTermS with | intro locals' hTermS =>
          have hMem := hTermS.1
          have hEvalT := hTermS.2.1
          have hDenT := hTermS.2.2
          cases checkEdgesAgainstCert_mem hBlkChk hMem with | intro bbT hMemE =>
          cases hMemE with | intro invT hMemE =>
          have hBbT := hMemE.1
          have hInvT := hMemE.2.1
          have hLeT := hMemE.2.2
          have hStepNext :
              evalStep (bodyProg body) 0 s =
                .step {
                  frames := [{ frame with
                    blockIdx := tgt, stmtIdx := 0, locals := locals' }]
                  callerMem := s.callerMem
                  mem := s.mem
                } := Eq.trans hEvalStepEq hEvalT
          refine ⟨?_, ?_, ?_⟩
          · intro k hF; rw [hStepNext] at hF; nomatch hF
          · intro next hSt
            rw [hStepNext] at hSt
            injection hSt with hEq; subst hEq
            exact ⟨_, bbT, invT, invT, rfl, hDef0, hSys, hBbT, hInvT,
              Nat.zero_le _, rfl, mirAbsEnvLe_sound hLeT hDenT⟩
          · intro _ _ hDone; rw [hStepNext] at hDone; nomatch hDone

/-- Main PCC soundness theorem for `checkMirCert`: if `checkMirCert` returns
`true` on `body`, `entryEnv`, `retInv`, and `invs`, then for every concrete
start state `start` at `(defId := 0, blockIdx := 0, stmtIdx := 0)` whose locals
satisfy `entryEnv`:
1. `SafeFrom body start` holds (unbounded-iteration fault-freedom across all
   reachable states under `Trusted.MirSemantics.evalStep`), and
2. every normal return value `retVal` satisfies the frame-independent
   `retInv.valDenote`. -/
theorem checkMirCert_sound {body : Body} {entryEnv : MirAbsEnv}
    {retInv : MirAbsSlot} {invs : List (Option MirAbsEnv)}
    {start : State} {locals0 : List LocalSlot}
    (hChk : checkMirCert body entryEnv retInv invs = true)
    (hStartFrames : start.frames = [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                                      locals := locals0 }])
    (hEntry : mirAbsEnvDenote body.locals entryEnv locals0) :
    SafeFrom body start ∧
    (∀ retVal, ReturnsFrom body start retVal →
      ∃ retTy,
        compGetElem? body.locals 0 = some retTy ∧
        retInv.valDenote retTy retVal) := by
  dsimp only [checkMirCert] at hChk
  have hPre := bool_and_true_left hChk
  have hLen_NoG := bool_and_true_left hPre
  have hNoG := bool_and_true_right hLen_NoG
  have hEntryChk := bool_and_true_right hPre
  have hAll := bool_and_true_right hChk
  cases hBb0 : compGetElem? body.basicBlocks 0 with
  | none => rw [hBb0] at hEntryChk; nomatch hEntryChk
  | some bb0 =>
    cases hInv0 : compGetElem? invs 0 with
    | none => rw [hBb0, hInv0] at hEntryChk; nomatch hEntryChk
    | some opt0 =>
      cases opt0 with
      | none => rw [hBb0, hInv0] at hEntryChk; nomatch hEntryChk
      | some inv0 =>
        rw [hBb0, hInv0] at hEntryChk
        have hStartInv : MirPccInv body invs start :=
          ⟨{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := locals0 },
           bb0, inv0, inv0, hStartFrames, rfl, rfl, hBb0, hInv0, Nat.zero_le _,
           rfl,
           mirAbsEnvLe_sound hEntryChk hEntry⟩
        have hReachInv : ∀ s, Reach body start s → MirPccInv body invs s := by
          intro s hR
          induction hR with
          | refl => exact hStartInv
          | next _ hStep ih =>
            exact (mirPccInv_step_and_safe hAll ih).2.1 _ hStep
        refine ⟨?_, ?_⟩
        · intro s k hR
          exact (mirPccInv_step_and_safe hAll (hReachInv s hR)).1 k
        · intro retVal hRet
          cases hRet with | intro sEnd hRet =>
          cases (mirPccInv_step_and_safe hAll (hReachInv sEnd hRet.1)).2.2
              retVal ⟨[]⟩ hRet.2 with
          | intro retTy hRes =>
            cases hRes with | intro retLocals hRes =>
            exact ⟨retTy, hRes.1, mirAbsSlot_valDenote_of_denote hNoG hRes.2⟩

/-! ## 3. Single-Pass Bourdoncle Cutpoint Materializer & Verifier -/

/-- Lookup helper for an association list keyed by `BasicBlockId`. -/
@[expose] def lookupCutpoint? (id : BasicBlockId)
    (cps : List (BasicBlockId × MirAbsEnv)) : Option MirAbsEnv :=
  cps.foldr (fun p ih => if Nat.beq p.1 id then some p.2 else ih) none

/-- True iff `id` is a designated cutpoint in `cutpoints`. -/
@[expose] def isCutpoint (id : BasicBlockId)
    (cutpoints : List (BasicBlockId × MirAbsEnv)) : Bool :=
  (lookupCutpoint? id cutpoints).isSome

/-- True iff `x` appears in `xs` (`List.foldr` membership check). -/
@[expose] def natListContains (x : Nat) (xs : List Nat) : Bool :=
  xs.foldr (fun y acc => Nat.beq x y || acc) false

/-- True iff `xs` has no duplicate elements (`List.foldr` nodup check). -/
@[expose] def natListNodup (xs : List Nat) : Bool :=
  (xs.foldr
    (fun x st => (!natListContains x st.2 && st.1, x :: st.2))
    (true, [])).1

/-- Syntactic successor block IDs of `term` for CFG schedule validation. -/
@[expose] def syntacticTermTargets : TerminatorKind → List BasicBlockId
  | .goto target => [target]
  | .switchInt _ targets =>
    targets.branches.foldr (fun p acc => p.2 :: acc) [targets.otherwise]
  | .assert _ _ _ target unwind =>
    target :: (match unwind with | .cleanup b => [b] | _ => [])
  | .call _ _ _ target unwind | .coreCall _ _ _ target unwind
  | .sysrootCall _ _ _ target unwind | .callNe _ _ _ target unwind =>
    (match target with | some t => [t] | none => []) ++
      (match unwind with | .cleanup b => [b] | _ => [])
  | .drop _ target unwind =>
    target :: (match unwind with | .cleanup b => [b] | _ => [])
  | .return_ | .unreachable | .unwindResume | .unsupported => []

/-- Validates that `cutpoints` has pairwise-distinct in-range block keys and
that `rpoOrder` is a duplicate-free, full-coverage, `0`-headed reverse-postorder
permutation of `0 .. body.basicBlocks.length - 1` modulo `cutpoints` (every
syntactic CFG edge `u -> v` whose target `v` is not a designated cutpoint
advances strictly forward in `rpoOrder`). -/
@[expose] def validRpoSchedule (body : Body)
    (cutpoints : List (BasicBlockId × MirAbsEnv))
    (rpoOrder : List BasicBlockId) : Bool :=
  let n := body.basicBlocks.length
  let cpIds := cutpoints.foldr (fun p acc => p.1 :: acc) []
  let cpsValid :=
    natListNodup cpIds &&
    cpIds.foldr (fun id acc => Nat.blt id n && acc) true
  let headOk :=
    match rpoOrder with
    | [] => false
    | b0 :: _ => Nat.beq b0 0
  let permOk :=
    Nat.beq rpoOrder.length n &&
    headOk &&
    natListNodup rpoOrder &&
    rpoOrder.foldr (fun id acc => Nat.blt id n && acc) true
  let dagOk :=
    (rpoOrder.foldr
      (fun u st =>
        let succsOk :=
          match compGetElem? body.basicBlocks u with
          | none => false
          | some bb =>
            (syntacticTermTargets bb.terminator).foldr
              (fun v acc =>
                (isCutpoint v cutpoints || natListContains v st.2) && acc)
              true
        (succsOk && st.1, u :: st.2))
      (true, [])).1
  cpsValid && permOk && dagOk

/-- Builds the initial per-block invariant table of length `n`, populating block
`0` with `entryEnv` (unless `0` is overridden by a cutpoint) and every cutpoint
with its certified invariant. -/
@[expose] def seedBlockInvs (n : Nat) (entryEnv : MirAbsEnv)
    (cutpoints : List (BasicBlockId × MirAbsEnv)) : List (Option MirAbsEnv) :=
  Nat.rec (motive := fun _ => Nat → List (Option MirAbsEnv))
    (fun _ => [])
    (fun _ ih idx =>
      let initOpt :=
        match lookupCutpoint? idx cutpoints with
        | some env => some env
        | none => if Nat.beq idx 0 then some entryEnv else none
      initOpt :: ih (idx + 1))
    n 0

/-- Propagates one successor edge `(tgt, envT)` into `invs` when `tgt` is not a
cutpoint (joining with any existing acyclic incoming state). -/
@[expose] def propagateEdge (cutpoints : List (BasicBlockId × MirAbsEnv))
    (invs : List (Option MirAbsEnv)) (tgt : BasicBlockId)
    (envT : MirAbsEnv) : List (Option MirAbsEnv) :=
  if isCutpoint tgt cutpoints then
    invs
  else
    match compGetElem? invs tgt with
    | some none =>
      match compSetElem? invs tgt (some envT) with
      | some invs' => invs'
      | none => invs
    | some (some prev) =>
      match mirAbsEnvJoin prev envT with
      | some joined =>
        match compSetElem? invs tgt (some joined) with
        | some invs' => invs'
        | none => invs
      | none => invs
    | none => invs

/-- Single linear reverse-postorder pass materializing acyclic block invariants
from the entry state and Bourdoncle cutpoints. -/
@[expose] def materializeCutpoints (body : Body) (entryEnv : MirAbsEnv)
    (cutpoints : List (BasicBlockId × MirAbsEnv))
    (rpoOrder : List BasicBlockId) : List (Option MirAbsEnv) :=
  let init := seedBlockInvs body.basicBlocks.length entryEnv cutpoints
  rpoOrder.foldl
    (fun invs bbId =>
      match compGetElem? body.basicBlocks bbId, compGetElem? invs bbId with
      | some bb, some (some env) =>
        match stepStmtsAbs body.locals env bb.statements with
        | none => invs
        | some exitEnv =>
          match stepTermAbs body.locals bb exitEnv with
          | some (.edges succs) =>
            succs.foldl
              (fun acc e => propagateEdge cutpoints acc e.1 e.2)
              invs
          | _ => invs
      | _, _ => invs)
    init

/-- Single-pass Bourdoncle cutpoint verifier: validates `rpoOrder` as a
reverse-postorder permutation modulo `cutpoints` (a schedule-shape check for
single-pass propagation), materializes acyclic block states along `rpoOrder` in
one forward pass, and verifies the complete post-fixpoint via `checkMirCert`
(which carries the full soundness obligation in `verifyMirCutpoints_sound`). -/
@[expose] def verifyMirCutpoints (body : Body) (entryEnv : MirAbsEnv)
    (retInv : MirAbsSlot) (cutpoints : List (BasicBlockId × MirAbsEnv))
    (rpoOrder : List BasicBlockId) : Bool :=
  validRpoSchedule body cutpoints rpoOrder &&
  checkMirCert body entryEnv retInv
    (materializeCutpoints body entryEnv cutpoints rpoOrder)

/-- Soundness of `verifyMirCutpoints`: a single `rfl` proof of
`verifyMirCutpoints body entryEnv retInv cutpoints rpoOrder = true` establishes
both unbounded-iteration `SafeFrom body start` and `retInv.valDenote` on every
returned value. -/
theorem verifyMirCutpoints_sound {body : Body} {entryEnv : MirAbsEnv}
    {retInv : MirAbsSlot} {cutpoints : List (BasicBlockId × MirAbsEnv)}
    {rpoOrder : List BasicBlockId} {start : State} {locals0 : List LocalSlot}
    (hVer : verifyMirCutpoints body entryEnv retInv cutpoints rpoOrder = true)
    (hStartFrames : start.frames = [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                                      locals := locals0 }])
    (hEntry : mirAbsEnvDenote body.locals entryEnv locals0) :
    SafeFrom body start ∧
    (∀ retVal, ReturnsFrom body start retVal →
      ∃ retTy,
        compGetElem? body.locals 0 = some retTy ∧
        retInv.valDenote retTy retVal) :=
  checkMirCert_sound (bool_and_true_right hVer) hStartFrames hEntry

/-! ## 4. Zero-Manual-WP Auto-Proof Front-End (`AutoProve`) -/

namespace AutoProve

/-- Computable Pass-1 mirror of `Trusted.MirSemantics.stmtHasStorageMarker`. -/
@[expose] def stmtHasStorageMarkerComp (localId : LocalId) :
    StatementKind → Bool
  | .storageLive id | .storageDead id => Nat.beq id localId
  | _ => false

/-- Computable Pass-1 mirror of `Trusted.MirSemantics.hasStorageAnnotation`. -/
@[expose] def hasStorageAnnotationComp (body : Body) (localId : LocalId) :
    Bool :=
  body.basicBlocks.any (fun bb =>
    bb.statements.any (stmtHasStorageMarkerComp localId))

private theorem list_any_eq {α : Type} {f g : α → Bool}
    (h : ∀ x, f x = g x) : ∀ xs : List α, xs.any f = xs.any g
  | [] => rfl
  | x :: xs => by
    change (f x || xs.any f) = (g x || xs.any g)
    rw [h x, list_any_eq h xs]

private theorem stmtHasStorageMarkerComp_eq (localId : LocalId)
    (stmt : StatementKind) :
    stmtHasStorageMarkerComp localId stmt =
      stmtHasStorageMarker localId stmt := by
  cases stmt <;> rfl

theorem hasStorageAnnotationComp_eq (body : Body) (localId : LocalId) :
    hasStorageAnnotationComp body localId =
      hasStorageAnnotation body localId := by
  dsimp only [hasStorageAnnotationComp, hasStorageAnnotation]
  apply list_any_eq
  intro bb
  exact list_any_eq (stmtHasStorageMarkerComp_eq localId) bb.statements

/-- Top initialized abstract slot for a supported function argument or return
type (`.int w false`, `.int w true`, `.bool`, `.unit`). -/
@[expose] def argTopAbsSlot? : MirTy → Option MirAbsSlot
  | .int w false => some (.uint w (AbsVal.topInit (bitWidthComp w)))
  | .int w true => some (.sint w (AbsVal.topInit (bitWidthComp w)))
  | .bool => some (.bool (.top .none))
  | .unit => some .unit
  | _ => none

private theorem argTopAbsSlot?_noRelGuard {ty : MirTy} {slot : MirAbsSlot}
    (h : argTopAbsSlot? ty = some slot) : slot.noRelGuard = true := by
  cases ty with
  | int w s =>
    cases s <;> (injection h with hEq; subst hEq; rfl)
  | bool => injection h with hEq; subst hEq; rfl
  | unit => injection h with hEq; subst hEq; rfl
  | char | rawPtr _ _ | ref _ _ | tuple _ | enum _ | ordering
  | slice _ | str | rangeTo _ | rangeFrom _ | array _ _ | never | unsupported
  | option _ | range _ | vec _ | box _ | struct_ _ _ =>
    nomatch h

private theorem intWidth_eq_of_beq {w1 w2 : IntWidth}
    (h : IntWidth.beq w1 w2 = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | nomatch h

private theorem argTopAbsSlot?_sound {ty : MirTy} {slot : MirAbsSlot}
    {locals : List LocalSlot} {v : Val}
    (hSlot : argTopAbsSlot? ty = some slot)
    (hChk : checkVal v ty = true) :
    slot.denote ty locals (.immediate (some v)) := by
  dsimp only [checkVal] at hChk
  cases ty with
  | int w s =>
    cases v with
    | scalar sv =>
      dsimp only [Val.ty?] at hChk
      cases hWf : sv.wf with
      | false => rw [hWf] at hChk; nomatch hChk
      | true =>
        rw [hWf] at hChk
        have hwEq := intWidth_eq_of_beq (bool_and_true_left hChk)
        have hsEq : sv.signed = s := eq_of_beq (bool_and_true_right hChk)
        have hTrEq : truncateBits sv.width sv.bits = sv.bits := eq_of_beq hWf
        have hLt : sv.bits.toNat < modPow2 (bitWidthComp w) := by
          rw [← hTrEq, hwEq, truncateBits_toNat]
          exact nat_mod_lt _ (modPow2_pos (bitWidthComp w))
        cases s with
        | false =>
          injection hSlot with hEq; subst hEq
          exact ⟨rfl, hwEq, hsEq, hLt, absVal_topInit_sound hLt⟩
        | true =>
          injection hSlot with hEq; subst hEq
          exact ⟨rfl, hwEq, hsEq, hLt, absVal_topInit_sound hLt⟩
    | bool _ => dsimp only [Val.ty?, MirTy.beq] at hChk; nomatch hChk
    | char _ => dsimp only [Val.ty?, MirTy.beq] at hChk; nomatch hChk
    | ordering _ => dsimp only [Val.ty?, MirTy.beq] at hChk; nomatch hChk
    | unit => dsimp only [Val.ty?, MirTy.beq] at hChk; nomatch hChk
    | enumVal ety vi =>
      dsimp only [Val.ty?] at hChk
      cases hE : enumAdmitted ety && Nat.blt vi ety.discriminants.length <;>
        rw [hE] at hChk <;> nomatch hChk
    | tuple fs =>
      cases fs with
      | nil => nomatch hChk
      | cons x xs =>
        cases x with
        | scalar sv =>
          cases xs with
          | nil => nomatch hChk
          | cons y ys =>
            cases y with
            | bool _ =>
              cases ys with
              | cons _ _ => nomatch hChk
              | nil =>
                dsimp only [Val.ty?] at hChk
                cases hW : sv.wf <;> rw [hW] at hChk <;> nomatch hChk
            | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
            | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _
            | bytes _ | optionVal _ | range _ _ | vec _ _ _ | boxPtr _ _ =>
              nomatch hChk
        | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _
        | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _
        | bytes _ | optionVal _ | range _ _ | vec _ _ _ | boxPtr _ _ =>
          nomatch hChk
    | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | bytes _
    | optionVal _ | range _ _ | vec _ _ _ | boxPtr _ _ =>
      nomatch hChk
  | bool =>
    injection hSlot with hEq; subst hEq
    cases v with
    | bool _ => exact ⟨rfl, True.intro⟩
    | scalar sv =>
      dsimp only [Val.ty?] at hChk
      cases hWf : sv.wf <;> rw [hWf] at hChk <;> nomatch hChk
    | char _ | ordering _ | unit => nomatch hChk
    | enumVal ety vi =>
      dsimp only [Val.ty?] at hChk
      cases hE : enumAdmitted ety && Nat.blt vi ety.discriminants.length <;>
        rw [hE] at hChk <;> nomatch hChk
    | tuple fs =>
      cases fs with
      | nil => nomatch hChk
      | cons x xs =>
        cases x with
        | scalar sv =>
          cases xs with
          | nil => nomatch hChk
          | cons y ys =>
            cases y with
            | bool _ =>
              cases ys with
              | cons _ _ => nomatch hChk
              | nil =>
                dsimp only [Val.ty?] at hChk
                cases hW : sv.wf <;> rw [hW] at hChk <;> nomatch hChk
            | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
            | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _
            | bytes _ | optionVal _ | range _ _ | vec _ _ _ | boxPtr _ _ =>
              nomatch hChk
        | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _
        | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _
        | bytes _ | optionVal _ | range _ _ | vec _ _ _ | boxPtr _ _ =>
          nomatch hChk
    | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | bytes _
    | optionVal _ | range _ _ | vec _ _ _ | boxPtr _ _ =>
      nomatch hChk
  | unit =>
    injection hSlot with hEq; subst hEq
    cases v with
    | unit => exact ⟨rfl, rfl⟩
    | scalar sv =>
      dsimp only [Val.ty?] at hChk
      cases hWf : sv.wf <;> rw [hWf] at hChk <;> nomatch hChk
    | bool _ | char _ | ordering _ => nomatch hChk
    | enumVal ety vi =>
      dsimp only [Val.ty?] at hChk
      cases hE : enumAdmitted ety && Nat.blt vi ety.discriminants.length <;>
        rw [hE] at hChk <;> nomatch hChk
    | tuple fs =>
      cases fs with
      | nil => nomatch hChk
      | cons x xs =>
        cases x with
        | scalar sv =>
          cases xs with
          | nil => nomatch hChk
          | cons y ys =>
            cases y with
            | bool _ =>
              cases ys with
              | cons _ _ => nomatch hChk
              | nil =>
                dsimp only [Val.ty?] at hChk
                cases hW : sv.wf <;> rw [hW] at hChk <;> nomatch hChk
            | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
            | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _
            | bytes _ | optionVal _ | range _ _ | vec _ _ _ | boxPtr _ _ =>
              nomatch hChk
        | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _
        | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _
        | bytes _ | optionVal _ | range _ _ | vec _ _ _ | boxPtr _ _ =>
          nomatch hChk
    | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | array _ | bytes _
    | optionVal _ | range _ _ | vec _ _ _ | boxPtr _ _ =>
      nomatch hChk
  | char | rawPtr _ _ | ref _ _ | tuple _ | enum _ | ordering
  | slice _ | str | rangeTo _ | rangeFrom _ | array _ _ | never | unsupported
  | option _ | range _ | vec _ | box _ | struct_ _ _ =>
    nomatch hSlot

/-- Builds the abstract entry environment matching `initLocalsLoop` from index
`idx` over suffix `tys`. -/
@[expose] def buildEntryEnvLoop? (body : Body) :
    Nat → List MirTy → Option MirAbsEnv
  | _, [] => some []
  | idx, ty :: rest =>
    let slotOpt : Option MirAbsSlot :=
      if Nat.beq idx 0 then
        liveUninitAbsSlot? ty
      else if Nat.ble idx body.argumentCount then
        argTopAbsSlot? ty
      else if hasStorageAnnotationComp body idx then
        some .dead
      else
        liveUninitAbsSlot? ty
    match slotOpt, buildEntryEnvLoop? body (idx + 1) rest with
    | some s, some restEnv => some (s :: restEnv)
    | _, _ => none

/-- Builds the abstract entry environment for `body` matching `initLocalsLoop`
at function entry. Fails closed (`none`) if
`body.argumentCount ≥ body.locals.length` or any local has an unsupported
type. -/
@[expose] def buildEntryEnv? (body : Body) : Option MirAbsEnv :=
  if Nat.blt body.argumentCount body.locals.length then
    buildEntryEnvLoop? body 0 body.locals
  else
    none

private theorem liveUninitAbsSlot?_sound {ty : MirTy} {slot : MirAbsSlot}
    {locals : List LocalSlot} (h : liveUninitAbsSlot? ty = some slot) :
    slot.denote ty locals (liveUninitSlot ty) := by
  cases ty with
  | int w s =>
    cases s with
    | false =>
      injection h with hEq; subst hEq
      exact ⟨rfl, absVal_uninit_sound_none⟩
    | true =>
      injection h with hEq; subst hEq
      exact ⟨rfl, absVal_uninit_sound_none⟩
  | bool =>
    injection h with hEq; subst hEq
    exact ⟨rfl, True.intro⟩
  | unit =>
    injection h with hEq; subst hEq
    exact ⟨rfl, rfl⟩
  | char | rawPtr _ _ | ref _ _ | tuple _ | enum _ | ordering
  | slice _ | str | rangeTo _ | rangeFrom _ | array _ _ | never | unsupported
  | option _ | range _ | vec _ | box _ | struct_ _ _ =>
    nomatch h

private theorem checkArgsMatch_get {args : List Val} {paramTys : List MirTy} :
    ∀ {k : Nat} {ty : MirTy},
      checkArgsMatch args paramTys = true →
      compGetElem? paramTys k = some ty →
      ∃ v, Trusted.MirSemantics.getElem? args k = some v ∧ checkVal v ty = true := by
  induction args generalizing paramTys with
  | nil =>
    intro k ty hChk hGet
    cases paramTys with
    | nil => nomatch hGet
    | cons _ _ => nomatch hChk
  | cons a rest ih =>
    intro k ty hChk hGet
    cases paramTys with
    | nil => nomatch hChk
    | cons pt pts =>
      dsimp only [checkArgsMatch] at hChk
      cases k with
      | zero =>
        injection hGet with hEq; subst hEq
        exact ⟨a, rfl, bool_and_true_left hChk⟩
      | succ k' =>
        exact ih (bool_and_true_right hChk) hGet

private theorem compGetElem?_drop {α : Type} :
    ∀ (xs : List α) (n i : Nat),
      compGetElem? (xs.drop n) i = compGetElem? xs (n + i)
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, i => by rw [Nat.zero_add]; rfl
  | _ :: xs, n + 1, i => by
    rw [Nat.succ_add]
    exact compGetElem?_drop xs n i

private theorem compGetElem?_take_of_lt {α : Type} :
    ∀ (xs : List α) (n i : Nat),
      i < n → compGetElem? (xs.take n) i = compGetElem? xs i
  | [], 0, _, h => nomatch h
  | [], _ + 1, _, _ => rfl
  | _ :: _, 0, _, h => nomatch h
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: xs, n + 1, i + 1, h =>
    compGetElem?_take_of_lt xs n i (Nat.lt_of_succ_lt_succ h)

private theorem initLocalsLoop_length (body : Body) (args : List Val) :
    ∀ (idx : Nat) (tys : List MirTy),
      (initLocalsLoop body args idx tys).length = tys.length
  | _, [] => rfl
  | idx, _ :: rest => congrArg Nat.succ (initLocalsLoop_length body args (idx + 1) rest)

private theorem buildEntryEnvLoop?_length (body : Body) :
    ∀ {idx : Nat} {tys : List MirTy} {env : MirAbsEnv},
      buildEntryEnvLoop? body idx tys = some env → env.length = tys.length
  | _, [], _, h => by injection h with hEq; subst hEq; rfl
  | idx, ty :: rest, env, h => by
    dsimp only [buildEntryEnvLoop?] at h
    cases hS : (if Nat.beq idx 0 then liveUninitAbsSlot? ty
      else if Nat.ble idx body.argumentCount then argTopAbsSlot? ty
      else if hasStorageAnnotationComp body idx then some .dead
      else liveUninitAbsSlot? ty) with
    | none => rw [hS] at h; nomatch h
    | some s =>
      cases hR : buildEntryEnvLoop? body (idx + 1) rest with
      | none => rw [hS, hR] at h; nomatch h
      | some restEnv =>
        rw [hS, hR] at h
        injection h with hEq; subst hEq
        exact congrArg Nat.succ (buildEntryEnvLoop?_length body hR)

private theorem buildEntryEnvLoop?_slot_sound {body : Body} {args : List Val}
    {fullLocals : List LocalSlot}
    (hArgs : ValidEntryArgs body args) :
    ∀ {idx : Nat} {tys : List MirTy} {env : MirAbsEnv},
      (∀ k ty, compGetElem? tys k = some ty →
        compGetElem? body.locals (idx + k) = some ty) →
      buildEntryEnvLoop? body idx tys = some env →
      ∀ (k : Nat) (ty : MirTy) (s : MirAbsSlot) (cs : LocalSlot),
        compGetElem? tys k = some ty →
        compGetElem? env k = some s →
        compGetElem? (initLocalsLoop body args idx tys) k = some cs →
        s.denote ty fullLocals cs := by
  intro idx tys
  induction tys generalizing idx with
  | nil =>
    intro env _ _ k _ _ _ hTy _ _
    nomatch hTy
  | cons ty rest ih =>
    intro env hSuffix hBuild k tyK s cs hTy hEnvK hCs
    dsimp only [buildEntryEnvLoop?] at hBuild
    cases hS : (if Nat.beq idx 0 then liveUninitAbsSlot? ty
      else if Nat.ble idx body.argumentCount then argTopAbsSlot? ty
      else if hasStorageAnnotationComp body idx then some .dead
      else liveUninitAbsSlot? ty) with
    | none => rw [hS] at hBuild; nomatch hBuild
    | some s0 =>
      cases hR : buildEntryEnvLoop? body (idx + 1) rest with
      | none => rw [hS, hR] at hBuild; nomatch hBuild
      | some restEnv =>
        rw [hS, hR] at hBuild
        injection hBuild with hEnvEq; subst hEnvEq
        cases k with
        | zero =>
          injection hTy with hTyEq; subst hTyEq
          injection hEnvK with hSEq; subst hSEq
          dsimp only [initLocalsLoop, compGetElem?] at hCs
          injection hCs with hCsEq; subst hCsEq
          cases hZ : Nat.beq idx 0 with
          | true =>
            rw [hZ] at hS
            exact liveUninitAbsSlot?_sound hS
          | false =>
            rw [hZ] at hS
            cases hArg : Nat.ble idx body.argumentCount with
            | true =>
              rw [hArg] at hS
              have hIdxPos : 0 < idx := by
                cases idx with
                | zero => nomatch hZ
                | succ _ => exact Nat.zero_lt_succ _
              have hSubLt : idx - 1 < body.argumentCount := by
                have hLe := Nat.le_of_ble_eq_true hArg
                have h1 : (idx - 1) + 1 ≤ body.argumentCount := by
                  rw [Nat.sub_add_cancel hIdxPos]; exact hLe
                exact h1
              have hInBody : compGetElem? body.locals idx = some ty := by
                have h0 := hSuffix 0 ty rfl
                rw [Nat.add_zero] at h0; exact h0
              have hParamGet :
                  compGetElem? ((body.locals.drop 1).take body.argumentCount) (idx - 1) =
                    some ty := by
                rw [compGetElem?_take_of_lt _ _ _ hSubLt, compGetElem?_drop]
                have hAdd1 : 1 + (idx - 1) = idx := by
                  rw [Nat.add_comm, Nat.sub_add_cancel hIdxPos]
                rw [hAdd1]; exact hInBody
              cases checkArgsMatch_get hArgs hParamGet with
              | intro v hv =>
                rw [hv.1]
                exact argTopAbsSlot?_sound hS hv.2
            | false =>
              rw [hArg] at hS
              rw [← hasStorageAnnotationComp_eq body idx]
              cases hAnn : hasStorageAnnotationComp body idx with
              | true =>
                rw [hAnn] at hS
                injection hS with hSEq; subst hSEq
                rfl
              | false =>
                rw [hAnn] at hS
                exact liveUninitAbsSlot?_sound hS
        | succ k' =>
          have hSuffix' : ∀ m ty', compGetElem? rest m = some ty' →
              compGetElem? body.locals ((idx + 1) + m) = some ty' := by
            intro m ty' hm
            have hAdd : (idx + 1) + m = idx + (m + 1) := by
              rw [Nat.add_assoc, Nat.add_comm 1 m]
            rw [hAdd]
            exact hSuffix (m + 1) ty' hm
          exact ih hSuffix' hR k' tyK s cs hTy hEnvK hCs

/-- Soundness of `buildEntryEnv?`: the generated abstract entry environment
soundly abstracts `initLocalsLoop body args 0 body.locals` for every valid
entry argument list `args`. -/
theorem buildEntryEnv?_sound {body : Body} {env : MirAbsEnv} {args : List Val}
    (hBuild : buildEntryEnv? body = some env)
    (hArgs : ValidEntryArgs body args) :
    mirAbsEnvDenote body.locals env (initLocalsLoop body args 0 body.locals) := by
  dsimp only [buildEntryEnv?] at hBuild
  cases hLt : Nat.blt body.argumentCount body.locals.length with
  | false => rw [hLt] at hBuild; nomatch hBuild
  | true =>
    rw [hLt] at hBuild
    refine ⟨buildEntryEnvLoop?_length body hBuild,
            initLocalsLoop_length body args 0 body.locals, ?_⟩
    intro i ty s cs hTy hEnvI hCs
    exact buildEntryEnvLoop?_slot_sound hArgs
      (fun k ty' hk => by rw [Nat.zero_add]; exact hk) hBuild i ty s cs hTy hEnvI hCs

/-- Fuel-bounded DFS postorder helper prepending finished blocks onto `st.2`
(reverse postorder) while skipping edges into `cutpoints`. -/
@[expose] def rpoDfsVisit (body : Body)
    (cutpoints : List (BasicBlockId × MirAbsEnv)) (fuel : Nat) :
    BasicBlockId → List BasicBlockId × List BasicBlockId →
      List BasicBlockId × List BasicBlockId :=
  Nat.rec
    (motive := fun _ =>
      BasicBlockId → List BasicBlockId × List BasicBlockId →
        List BasicBlockId × List BasicBlockId)
    (fun _ st => st)
    (fun _ ih u st =>
      if !Nat.blt u body.basicBlocks.length || natListContains u st.1 then
        st
      else
        let st1 := (u :: st.1, st.2)
        let succs :=
          match compGetElem? body.basicBlocks u with
          | some bb => syntacticTermTargets bb.terminator
          | none => []
        let st2 :=
          succs.foldl
            (fun acc v =>
              if isCutpoint v cutpoints then acc
              else ih v acc)
            st1
        (st2.1, u :: st2.2))
    fuel

/-- Computes a reverse-postorder schedule of `body.basicBlocks` modulo
`cutpoints` using fuel-bounded DFS (`0` is visited last so it sits at the head
whenever no non-cutpoint edge enters `0`). -/
@[expose] def defaultRpoOrder (body : Body)
    (cutpoints : List (BasicBlockId × MirAbsEnv) := []) : List BasicBlockId :=
  match body.basicBlocks.length with
  | 0 => []
  | m + 1 =>
    let n := m + 1
    let stRest :=
      Nat.rec
        (motive := fun _ =>
          Nat → List BasicBlockId × List BasicBlockId →
            List BasicBlockId × List BasicBlockId)
        (fun _ st => st)
        (fun _ ih idx st =>
          ih (idx + 1) (rpoDfsVisit body cutpoints n idx st))
        m 1 ([], [])
    (rpoDfsVisit body cutpoints n 0 stRest).2

/-- Default top return invariant slot derived from `body.locals[0]`. -/
@[expose] def autoRetSlot? (body : Body) : Option MirAbsSlot :=
  match compGetElem? body.locals 0 with
  | some ty => argTopAbsSlot? ty
  | none => none

/-- Automatic cutpoint certificate verifier: builds `entryEnv` from `body` and
runs `verifyMirCutpoints`. -/
@[expose] def autoVerifyCutpoints (body : Body) (retInv : MirAbsSlot)
    (cutpoints : List (BasicBlockId × MirAbsEnv))
    (rpoOrder : List BasicBlockId := defaultRpoOrder body cutpoints) :
    Bool :=
  match buildEntryEnv? body with
  | none => false
  | some entryEnv => verifyMirCutpoints body entryEnv retInv cutpoints rpoOrder

/-- Automatic acyclic verifier with an explicit return-value postcondition
`retInv`. -/
@[expose] def autoVerifyAcyclicWithRet (body : Body) (retInv : MirAbsSlot)
    (rpoOrder : List BasicBlockId := defaultRpoOrder body []) :
    Bool :=
  autoVerifyCutpoints body retInv [] rpoOrder

/-- Automatic acyclic safety verifier: synthesizes both `entryEnv` and the top
return invariant from `body.locals` and verifies the body in one pass. -/
@[expose] def autoVerifyAcyclic (body : Body)
    (rpoOrder : List BasicBlockId := defaultRpoOrder body []) :
    Bool :=
  match autoRetSlot? body with
  | none => false
  | some retInv => autoVerifyAcyclicWithRet body retInv rpoOrder

/-- Soundness of `autoVerifyCutpoints`: proves both `Safe body args` and the
frame-independent return-value invariant `retInv.valDenote`. -/
theorem autoVerifyCutpoints_sound {body : Body} {retInv : MirAbsSlot}
    {cutpoints : List (BasicBlockId × MirAbsEnv)}
    {rpoOrder : List BasicBlockId} {args : List Val}
    (hVer : autoVerifyCutpoints body retInv cutpoints rpoOrder = true)
    (hArgs : ValidEntryArgs body args) :
    Safe body args ∧
    (∀ retVal, Returns body args retVal →
      ∃ retTy,
        compGetElem? body.locals 0 = some retTy ∧
        retInv.valDenote retTy retVal) := by
  dsimp only [autoVerifyCutpoints] at hVer
  cases hB : buildEntryEnv? body with
  | none => rw [hB] at hVer; nomatch hVer
  | some entryEnv =>
    rw [hB] at hVer
    exact verifyMirCutpoints_sound hVer rfl (buildEntryEnv?_sound hB hArgs)

/-- Soundness of `autoVerifyAcyclicWithRet`. -/
theorem autoVerifyAcyclicWithRet_sound {body : Body} {retInv : MirAbsSlot}
    {rpoOrder : List BasicBlockId} {args : List Val}
    (hVer : autoVerifyAcyclicWithRet body retInv rpoOrder = true)
    (hArgs : ValidEntryArgs body args) :
    Safe body args ∧
    (∀ retVal, Returns body args retVal →
      ∃ retTy,
        compGetElem? body.locals 0 = some retTy ∧
        retInv.valDenote retTy retVal) :=
  autoVerifyCutpoints_sound hVer hArgs

/-- Soundness of `autoVerifyAcyclic` for an arbitrary explicit `rpoOrder`. -/
theorem autoVerifyAcyclicOrder_sound {body : Body}
    {rpoOrder : List BasicBlockId} {args : List Val}
    (hVer : autoVerifyAcyclic body rpoOrder = true)
    (hArgs : ValidEntryArgs body args) :
    Safe body args := by
  dsimp only [autoVerifyAcyclic] at hVer
  cases hRet : autoRetSlot? body with
  | none => rw [hRet] at hVer; nomatch hVer
  | some retInv =>
    rw [hRet] at hVer
    exact (autoVerifyAcyclicWithRet_sound hVer hArgs).1

/-- Soundness of `autoVerifyAcyclic` using `defaultRpoOrder`: a single `rfl`
proof of `autoVerifyAcyclic body = true` establishes `Safe body args` for all
valid entry arguments `args`. -/
theorem autoVerifyAcyclic_sound {body : Body} {args : List Val}
    (hVer : autoVerifyAcyclic body (defaultRpoOrder body []) = true)
    (hArgs : ValidEntryArgs body args) :
    Safe body args :=
  autoVerifyAcyclicOrder_sound hVer hArgs

/-- One-liner `BodyVerified` discharge for any acyclic scalar/signed/unsigned/
bool/unit function verified by `autoVerifyAcyclic`. -/
theorem bodyVerified_of_autoVerifyAcyclic {p : Program} {defId : DefId}
    {body : Body} {safetyPre : List Val → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (hVer : autoVerifyAcyclic body (defaultRpoOrder body []) = true)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    BodyVerified p defId body safetyPre :=
  bodyVerified_of_safe h_body h_adm
    (fun _ hArgs _ => autoVerifyAcyclic_sound hVer hArgs) h_nocall

/-- One-liner `BodyVerified` discharge for any acyclic function with an
explicit `rpoOrder`. -/
theorem bodyVerified_of_autoVerifyAcyclicOrder {p : Program} {defId : DefId}
    {body : Body} {safetyPre : List Val → Prop}
    {rpoOrder : List BasicBlockId}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (hVer : autoVerifyAcyclic body rpoOrder = true)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    BodyVerified p defId body safetyPre :=
  bodyVerified_of_safe h_body h_adm
    (fun _ hArgs _ => autoVerifyAcyclicOrder_sound hVer hArgs) h_nocall

/-- One-liner `BodyVerified` discharge for a function verified by
`autoVerifyCutpoints` (supporting loops with Bourdoncle cutpoints). -/
theorem bodyVerified_of_autoVerifyCutpoints {p : Program} {defId : DefId}
    {body : Body} {safetyPre : List Val → Prop}
    {retInv : MirAbsSlot} {cutpoints : List (BasicBlockId × MirAbsEnv)}
    {rpoOrder : List BasicBlockId}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (hVer : autoVerifyCutpoints body retInv cutpoints rpoOrder = true)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    BodyVerified p defId body safetyPre :=
  bodyVerified_of_safe h_body h_adm
    (fun _ hArgs _ => (autoVerifyCutpoints_sound hVer hArgs).1) h_nocall

end AutoProve

end Anneal.AiPcc

end
