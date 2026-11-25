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
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Anneal.Framework.StepWp
public import Anneal.PureLift.Lens
public import Anneal.PureLift.PermTree
public import Anneal.PureLift.LoanGraph
public import Anneal.PureLift.SpatialPin
public import Anneal.PureLift.Plan

public section

namespace Anneal.PureLift

open Anneal.Framework.StepWp

/-!
# Constructive Loop Cutpoints and Block-Indexed CFG Certificates (`BlockCfg`)

Provides two complementary control-flow verification mechanisms over `FlowPlan`:
- `runWhileFlowSteps_cutpoint_sound`: proves that any `FlowPlan.whileLoop`
  satisfying an inductive loop invariant `Inv` and a ranking measure
  `rank : SymState Val → Nat` that strictly decreases on each taken iteration
  terminates in `.ok (.continuing sFinal)` with `Inv sFinal` and exit condition
  `false`, whenever the loop's fuel is at least the initial rank.
- `BasicBlock`, `stepBasicBlock`, `runBlockCfg`, and `modular_block_cfg_sound`:
  verify unstructured or multi-block control-flow graphs in $O(N)$ per-block
  verification conditions (`LocalBlockVC`), where each basic block's body is a
  `FlowPlan Val` evaluated via `evalPlan`.
-/

theorem runWhileFlowSteps_zero {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val))
    (s : SymState Val) :
    runWhileFlowSteps alg cond evalBody 0 s =
      (match evalRval alg cond s with
       | some cv =>
         match alg.asBool cv with
         | some false => .ok (.continuing s)
         | _ => .fail
       | none => .fail) := rfl

theorem runWhileFlowSteps_succ {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val))
    (k : Nat) (s : SymState Val) :
    runWhileFlowSteps alg cond evalBody (k + 1) s =
      (match evalRval alg cond s with
       | some cv =>
         match alg.asBool cv with
         | some false => .ok (.continuing s)
         | some true =>
           match evalBody s with
           | .ok (.continuing s') =>
             runWhileFlowSteps alg cond evalBody k s'
           | .ok (.returned out c m) => .ok (.returned out c m)
           | .ok (.guardedContinuing wrap1 s' c1 wrapMut1) =>
             prependGuardedWrap wrap1 c1 wrapMut1
               (runWhileFlowSteps alg cond evalBody k s')
           | .fail => .fail
         | none => .fail
       | none => .fail) := rfl

private def whileFlowStep {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val))
    (s : SymState Val) :
    Trusted.MirSemantics.StepResult (SymState Val) (SymState Val) :=
  match evalRval alg cond s with
  | some cv =>
    match alg.asBool cv with
    | some false => .done s
    | some true =>
      match evalBody s with
      | .ok (.continuing s') => .step s'
      | _ => .fault .unsupported
    | none => .fault .unsupported
  | none => .fault .unsupported

private theorem runWhileFlowSteps_of_execStep {Val : Type}
    (alg : ValAlgebra Val) (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val)) :
    ∀ (fuel : Nat) (s sFinal : SymState Val),
      execStepPred (whileFlowStep alg cond evalBody)
        (fun _ out => out = sFinal) (fun _ _ => False) (fuel + 1) s →
      runWhileFlowSteps alg cond evalBody fuel s = .ok (.continuing sFinal)
  | 0, s, sFinal, h => by
    rw [execStepPred_succ_iff] at h
    unfold whileFlowStep at h
    rw [runWhileFlowSteps_zero]
    cases hR : evalRval alg cond s with
    | none => rw [hR] at h; exact False.elim h
    | some cv =>
      rw [hR] at h; dsimp only at h; dsimp only
      cases hB : alg.asBool cv with
      | none => rw [hB] at h; exact False.elim h
      | some b =>
        rw [hB] at h
        cases b with
        | false => dsimp only at h; rw [h]
        | true =>
          dsimp only at h
          cases hEB : evalBody s with
          | fail => rw [hEB] at h; exact False.elim h
          | ok flow =>
            rw [hEB] at h
            cases flow with
            | continuing _ | returned _ _ _ | guardedContinuing _ _ _ _ =>
              exact False.elim h
  | k + 1, s, sFinal, h => by
    rw [execStepPred_succ_iff] at h
    unfold whileFlowStep at h
    rw [runWhileFlowSteps_succ]
    cases hR : evalRval alg cond s with
    | none => rw [hR] at h; exact False.elim h
    | some cv =>
      rw [hR] at h; dsimp only at h; dsimp only
      cases hB : alg.asBool cv with
      | none => rw [hB] at h; exact False.elim h
      | some b =>
        rw [hB] at h
        cases b with
        | false => dsimp only at h; rw [h]
        | true =>
          dsimp only at h; dsimp only
          cases hEB : evalBody s with
          | fail => rw [hEB] at h; exact False.elim h
          | ok flow =>
            rw [hEB] at h
            cases flow with
            | continuing st' =>
              exact runWhileFlowSteps_of_execStep alg cond evalBody k st'
                sFinal h
            | returned _ _ _ | guardedContinuing _ _ _ _ =>
              exact False.elim h

/-- Constructive loop cutpoint theorem for `runWhileFlowSteps`, discharged via
`StepWp.execStep_nat_rank_done`. If every state satisfying `Inv` either exits
(the condition is `false`) or takes an iteration to a state that satisfies
`Inv` and has strictly smaller `rank`, then from any `Inv` state whose rank is
at most `fuel`, the loop exits normally in a state satisfying `Inv`. -/
theorem runWhileFlowSteps_cutpoint_sound {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val))
    (Inv : SymState Val → Prop) (rank : SymState Val → Nat)
    (hStep : ∀ s, Inv s →
      Exists fun cv => evalRval alg cond s = some cv ∧
        (alg.asBool cv = some false ∨
         (alg.asBool cv = some true ∧
          Exists fun s' =>
            evalBody s = .ok (.continuing s') ∧
            Inv s' ∧ rank s' < rank s))) :
    ∀ fuel s, Inv s → rank s ≤ fuel →
      Exists fun sFinal =>
        runWhileFlowSteps alg cond evalBody fuel s =
          .ok (.continuing sFinal) ∧
        Inv sFinal ∧
        (Exists fun cv =>
          evalRval alg cond sFinal = some cv ∧ alg.asBool cv = some false) := by
  intro fuel s hInv hRank
  have hGen : ∀ st, Inv st →
      ((Exists fun cv =>
          evalRval alg cond st = some cv ∧ alg.asBool cv = some false) ∧
        whileFlowStep alg cond evalBody st = .done st) ∨
      (∃ st', whileFlowStep alg cond evalBody st = .step st' ∧
        Inv st' ∧ rank st' < rank st) := by
    intro st hI
    let ⟨cv, hEv, hBr⟩ := hStep st hI
    cases hBr with
    | inl hFalse =>
      refine Or.inl ⟨⟨cv, hEv, hFalse⟩, ?_⟩
      unfold whileFlowStep
      rw [hEv]
      dsimp only
      rw [hFalse]
    | inr hTrue =>
      let ⟨hB, s', hBody, hI', hLt⟩ := hTrue
      refine Or.inr ⟨s', ?_, hI', hLt⟩
      unfold whileFlowStep
      rw [hEv]
      dsimp only
      rw [hB]
      dsimp only
      rw [hBody]
  let ⟨sFinal, hExec, hInvF, hExitF⟩ :=
    execStep_nat_rank_done (whileFlowStep alg cond evalBody) Inv
      (fun st => Exists fun cv =>
        evalRval alg cond st = some cv ∧ alg.asBool cv = some false)
      rank hGen fuel s hInv hRank
  exact ⟨sFinal, runWhileFlowSteps_of_execStep alg cond evalBody fuel s sFinal hExec,
    hInvF, hExitF⟩

/-- Terminator of a `BasicBlock Val`. -/
inductive BlockTerm (Val : Type) where
  | goto (target : BlockId) : BlockTerm Val
  | branch (cond : RvalOp Val) (thenTarget elseTarget : BlockId) :
      BlockTerm Val
  | ret (retExpr : RvalOp Val) : BlockTerm Val

/-- Basic block whose straight-line or structured body is a `FlowPlan Val` and
whose exit is a `BlockTerm Val`. -/
structure BasicBlock (Val : Type) where
  body : FlowPlan Val
  term : BlockTerm Val

/-- Result of running one block for `runBlockCfg`, with states `State` and
return values `Ret`:
- `.jump nextBb st'`: continue at block `nextBb` in state `st'`,
- `.jumpWrapped wrapRet nextBb st'`: continue at `nextBb` in `st'`, and pass
  the value that the rest of the run returns through `wrapRet`. The wrapper
  folds in early returns that are pending on some paths (a symbolic branch in
  the block returned on one side only); it may reject the combined value
  (`none`), and then the run faults,
- `.convergedJump armSteps wrapRet nextBb st'`: a symbolic branch whose two
  arms reconverged at `nextBb` in joined state `st'` after executing at most
  `armSteps` basic blocks inside the arms; charges `armSteps` units of CFG fuel
  before continuing at `nextBb` and passes the eventual return value through
  `wrapRet`,
- `.branchJump mergeRet thenBb elseBb st'`: a branch on a symbolic condition.
  Both successors run from `st'`, and `mergeRet` combines their return values
  or rejects the combination (`none`), which makes the run fault,
- `.ret val`: return `val`, and
- `.fault`: the block failed. -/
inductive BlockStepResult (State Ret : Type) where
  | jump (nextBb : Nat) (st' : State)
  | jumpWrapped (wrapRet : Ret → Option Ret) (nextBb : Nat) (st' : State)
  | convergedJump (armSteps : Nat) (wrapRet : Ret → Option Ret)
      (nextBb : Nat) (st' : State)
  | branchJump (mergeRet : Ret → Ret → Option Ret) (thenBb elseBb : Nat)
      (st' : State)
  | ret (val : Ret)
  | fault

inductive BlockCfgOutcome (Ret : Type) where
  | ret (val : Ret)
  | diverged
  | fault

@[expose] def listGetOpt {α : Type} (idx : Nat) (xs : List α) : Option α :=
  xs.foldr
    (fun x ih n =>
      match n with
      | 0 => some x
      | n' + 1 => ih n')
    (fun _ => none)
    idx

/-- `some out` if `out` is free of borrow handles (`handleFreeOut`), and `none`
otherwise. -/
@[expose] def handleFreeOutOpt {Val : Type} (alg : ValAlgebra Val) (out : FuncOut Val) :
    Option (FuncOut Val) :=
  if handleFreeOut alg out then some out else none

/-- Trace the sequence of basic block indices reachable on the forward exit
spine from `bbIdx` within `fuel` steps, avoiding `visited` cycles. Follows
`.goto tgt`, and at `.branch _ tTgt fTgt` continues from the first common
convergence block of `tTgt` and `fTgt` (or records both arms' reachable blocks
if only one arm continues). -/
@[expose] def traceExitPath {Val : Type} (blocks : List (BasicBlock Val))
    (fuel : Nat) (bbIdx : BlockId) (visited : List BlockId) : List BlockId :=
  natFold (fun _ _ => [])
    (fun _ ih cur vis =>
      if elemLoanId cur vis then []
      else
        match listGetOpt cur blocks with
        | none => []
        | some bb =>
          let vis' := cur :: vis
          match bb.term with
          | .ret _ => [cur]
          | .goto tgt => cur :: ih tgt vis'
          | .branch _ tTgt fTgt =>
            if tTgt == fTgt then cur :: ih tTgt vis'
            else
              let pathT := ih tTgt vis'
              let pathF := ih fTgt vis'
              match pathT.find? (fun b => elemLoanId b pathF) with
              | some joinBb => cur :: ih joinBb vis'
              | none => cur :: (pathT ++ pathF))
    fuel bbIdx visited

/-- Find the first common convergence basic block on the forward exit spines of
`tTgt` and `fTgt`, if any. -/
@[expose] def findConvergenceBlock {Val : Type} (blocks : List (BasicBlock Val))
    (fuel : Nat) (tTgt fTgt : BlockId) (visited : List BlockId) :
    Option BlockId :=
  let pathT := traceExitPath blocks fuel tTgt visited
  let pathF := traceExitPath blocks fuel fTgt visited
  pathT.find? (fun b => elemLoanId b pathF)

/-- Prepend one basic-block transition and an optional guarded early-return
wrapper onto the `(steps, flow)` result of an `evalArmToJoin` recursive call. -/
@[expose] def prependArmStep {Val : Type}
    (wrapOpt : Option ((FuncOut Val → FuncOut Val) × Bool ×
      (Option (Val × (Val → Option (List Val))) →
        Option (Val × (Val → Option (List Val))))))
    (res : EvalOutcome (Nat × ExecFlow Val)) :
    EvalOutcome (Nat × ExecFlow Val) :=
  match res with
  | .fail => .fail
  | .ok (steps, flow) =>
    match wrapOpt with
    | none => .ok (steps + 1, flow)
    | some (wrapOut, valClean, wrapMut) =>
      match prependGuardedWrap wrapOut valClean wrapMut (.ok flow) with
      | .ok flow' => .ok (steps + 1, flow')
      | .fail => .fail

/-- Evaluate a branch arm starting at `bbIdx` in state `st` up to (but not
including) `joinBb`, within `fuel` block transitions, returning both the number
of basic-block transitions executed inside the arm and the resulting `ExecFlow`.
When `bbIdx == joinBb`, stops immediately with `.ok (0, .continuing st)` so
`joinBb` is evaluated once after the two arms join. -/
@[expose] def evalArmToJoin {Val : Type} (alg : ValAlgebra Val)
    (blocks : List (BasicBlock Val)) (fuel : Nat) (joinBb : BlockId)
    (bbIdx : BlockId) (st : SymState Val) :
    EvalOutcome (Nat × ExecFlow Val) :=
  natFold (fun _ _ _ => .fail)
    (fun _ ih stopBb cur curSt =>
      if cur == stopBb then .ok (0, .continuing curSt)
      else
        match listGetOpt cur blocks with
        | none => .fail
        | some bb =>
          let stepAfterBody
              (wOpt : Option ((FuncOut Val → FuncOut Val) × Bool ×
                (Option (Val × (Val → Option (List Val))) →
                  Option (Val × (Val → Option (List Val))))))
              (st' : SymState Val) : EvalOutcome (Nat × ExecFlow Val) :=
            match bb.term with
            | .goto tgt =>
              prependArmStep wOpt (ih stopBb tgt st')
            | .ret retExpr =>
              if !stateCleanAtReturn st' then .fail
              else
                match evalRval alg retExpr st' with
                | some rv =>
                  let baseOut : FuncOut Val :=
                    ⟨rv, collectRootMutVals st'.loans⟩
                  let out :=
                    match wOpt with
                    | some (wrapOut, _, _) => wrapOut baseOut
                    | none => baseOut
                  if !handleFreeOut alg out then .fail
                  else .ok (1, .returned out true none)
                | none => .fail
            | .branch cond tTgt fTgt =>
              match evalRval alg cond st' with
              | none => .fail
              | some cv =>
                match alg.asBool cv with
                | some true =>
                  prependArmStep wOpt (ih stopBb tTgt st')
                | some false =>
                  prependArmStep wOpt (ih stopBb fTgt st')
                | none =>
                  if tTgt == fTgt then
                    prependArmStep wOpt (ih stopBb tTgt st')
                  else
                    let innerConv :=
                      if (tTgt == stopBb) || (fTgt == stopBb) then some stopBb
                      else findConvergenceBlock blocks fuel tTgt fTgt [cur]
                    match innerConv with
                    | some midBb =>
                      match ih midBb tTgt st', ih midBb fTgt st' with
                      | .ok (kT, flowT), .ok (kF, flowF) =>
                        let kArms := Nat.max kT kF
                        match joinExecFlow alg cv flowT flowF with
                        | some (.continuing stMid) =>
                          match ih stopBb midBb stMid with
                          | .ok (kAfter, flowAfter) =>
                            prependArmStep wOpt
                              (.ok (kArms + kAfter, flowAfter))
                          | .fail => .fail
                        | some (.guardedContinuing wM stMid cM wmM) =>
                          match ih stopBb midBb stMid with
                          | .ok (kAfter, flowAfter) =>
                            match prependGuardedWrap wM cM wmM
                                (.ok flowAfter) with
                            | .ok flowAfter' =>
                              prependArmStep wOpt
                                (.ok (kArms + kAfter, flowAfter'))
                            | .fail => .fail
                          | .fail => .fail
                        | some (.returned outM cM mM) =>
                          prependArmStep wOpt
                            (.ok (kArms, .returned outM cM mM))
                        | none => .fail
                      | _, _ => .fail
                    | none =>
                      match ih stopBb tTgt st', ih stopBb fTgt st' with
                      | .ok (kT, flowT), .ok (kF, flowF) =>
                        let kArms := Nat.max kT kF
                        match joinExecFlow alg cv flowT flowF with
                        | some joined =>
                          prependArmStep wOpt (.ok (kArms, joined))
                        | none => .fail
                      | _, _ => .fail
          match evalPlan alg bb.body curSt with
          | .fail => .fail
          | .ok (.returned out valClean mutRet) =>
            if !valClean || !handleFreeOut alg out then .fail
            else .ok (1, .returned out true mutRet)
          | .ok (.guardedContinuing wrapOut st' valClean wrapMut) =>
            if !valClean then .fail
            else stepAfterBody (some (wrapOut, true, wrapMut)) st'
          | .ok (.continuing st') =>
            stepAfterBody none st')
    fuel joinBb bbIdx st

/-- Convert the joined `ExecFlow` at convergence block `joinBb` into a
`BlockStepResult` that charges `armSteps` basic-block transitions against CFG
fuel, optionally applying an outer pending early-return wrapper `outerWrap` from
the branching block itself. Returns `none` when both arms returned before
reaching `joinBb` so the caller falls back to `.branchJump`. -/
@[expose] def finishConvergedBranch {Val : Type} (alg : ValAlgebra Val)
    (armSteps : Nat)
    (outerWrap : Option (FuncOut Val → FuncOut Val))
    (joinBb : BlockId) (joined : ExecFlow Val) :
    Option (BlockStepResult (SymState Val) (FuncOut Val)) :=
  let applyOuter (out : FuncOut Val) : FuncOut Val :=
    match outerWrap with
    | some w => w out
    | none => out
  match joined with
  | .returned _ _ _ => none
  | .continuing stJoined =>
    some
      (.convergedJump armSteps
        (fun out => handleFreeOutOpt alg (applyOuter out))
        joinBb stJoined)
  | .guardedContinuing wrapJoined stJoined valClean _ =>
    if !valClean then some .fault
    else
      some
        (.convergedJump armSteps
          (fun out => handleFreeOutOpt alg (applyOuter (wrapJoined out)))
          joinBb stJoined)

/-- Execute one `BasicBlock Val` by running `evalPlan alg bb.body st` and
dispatching on `bb.term`. When a symbolic `.branch cond tTgt fTgt` reconverges
at a common block `joinBb` (`findConvergenceBlock`), both arms are evaluated up
to `joinBb` (`evalArmToJoin`), joined via `joinExecFlow`, and execution jumps
once to `joinBb` in the joined state via `.convergedJump` (charging
`Nat.max kT kF` arm steps against CFG fuel) so the post-join tail is not
duplicated. As in `evalFnValue`, every `FuncOut` that the CFG returns must be
free of borrow handles (`handleFreeOut`): a `.ret` terminator checks the value
it returns, and the wrappers of `.jumpWrapped`, `.convergedJump`, and
`.branchJump` check the value after merging in pending early returns or the
other successor's value. The merged value needs its own check: a pending early
return may hold a handle that the later block's value lacks, and no `ValAlgebra`
law makes a merge of handle-free values handle-free
(`runBlockCfg_stepBasicBlock_handleFree` states the result). -/
@[expose] def stepBasicBlock {Val : Type} (alg : ValAlgebra Val)
    (blocks : List (BasicBlock Val)) (bbIdx : BlockId)
    (st : SymState Val) : BlockStepResult (SymState Val) (FuncOut Val) :=
  match listGetOpt bbIdx blocks with
  | none => .fault
  | some bb =>
    match evalPlan alg bb.body st with
    | .fail => .fault
    | .ok (.returned out valClean _) =>
      if !valClean || !handleFreeOut alg out then .fault else .ret out
    | .ok (.guardedContinuing wrapOut st' valClean _) =>
      if !valClean then .fault
      else
        let wrapChecked (out : FuncOut Val) : Option (FuncOut Val) :=
          handleFreeOutOpt alg (wrapOut out)
        match bb.term with
        | .goto tgt => .jumpWrapped wrapChecked tgt st'
        | .branch cond tTgt fTgt =>
          match evalRval alg cond st' with
          | some cv =>
            match alg.asBool cv with
            | some true => .jumpWrapped wrapChecked tTgt st'
            | some false => .jumpWrapped wrapChecked fTgt st'
            | none =>
              -- Both successors coincide: run the target once instead of
              -- evaluating it twice and merging identical results.
              if tTgt == fTgt then .jumpWrapped wrapChecked tTgt st'
              else
                let convStep :
                    Option (BlockStepResult (SymState Val) (FuncOut Val)) :=
                  match findConvergenceBlock blocks (blocks.length + 1)
                      tTgt fTgt [bbIdx] with
                  | some joinBb =>
                    match evalArmToJoin alg blocks (blocks.length + 1)
                            joinBb tTgt st',
                          evalArmToJoin alg blocks (blocks.length + 1)
                            joinBb fTgt st' with
                    | .ok (kT, flowT), .ok (kF, flowF) =>
                      match joinExecFlow alg cv flowT flowF with
                      | some joined =>
                        finishConvergedBranch alg (Nat.max kT kF) (some wrapOut)
                          joinBb joined
                      | none => none
                    | _, _ => none
                  | none => none
                match convStep with
                | some res => res
                | none =>
                  .branchJump
                    (fun tOut fOut =>
                      handleFreeOutOpt alg
                        (wrapOut (mergeFuncOut alg cv tOut fOut)))
                    tTgt fTgt st'
          | none => .fault
        | .ret retExpr =>
          if !stateCleanAtReturn st' then .fault
          else
            match evalRval alg retExpr st' with
            | some rv =>
              let out := wrapOut ⟨rv, collectRootMutVals st'.loans⟩
              if !handleFreeOut alg out then .fault else .ret out
            | none => .fault
    | .ok (.continuing st') =>
      match bb.term with
      | .goto tgt => .jump tgt st'
      | .branch cond tTgt fTgt =>
        match evalRval alg cond st' with
        | some cv =>
          match alg.asBool cv with
          | some true => .jump tTgt st'
          | some false => .jump fTgt st'
          | none =>
            if tTgt == fTgt then .jump tTgt st'
            else
              let convStep :
                  Option (BlockStepResult (SymState Val) (FuncOut Val)) :=
                match findConvergenceBlock blocks (blocks.length + 1)
                    tTgt fTgt [bbIdx] with
                | some joinBb =>
                  match evalArmToJoin alg blocks (blocks.length + 1)
                          joinBb tTgt st',
                        evalArmToJoin alg blocks (blocks.length + 1)
                          joinBb fTgt st' with
                  | .ok (kT, flowT), .ok (kF, flowF) =>
                    match joinExecFlow alg cv flowT flowF with
                    | some joined =>
                      finishConvergedBranch alg (Nat.max kT kF) none
                        joinBb joined
                    | none => none
                  | _, _ => none
                | none => none
              match convStep with
              | some res => res
              | none =>
                .branchJump
                  (fun tOut fOut =>
                    handleFreeOutOpt alg (mergeFuncOut alg cv tOut fOut))
                  tTgt fTgt st'
        | none => .fault
      | .ret retExpr =>
        if !stateCleanAtReturn st' then .fault
        else
          match evalRval alg retExpr st' with
          | some rv =>
            let out : FuncOut Val := ⟨rv, collectRootMutVals st'.loans⟩
            if !handleFreeOut alg out then .fault else .ret out
          | none => .fault

/-- Internal fuel-and-delay loop for `runBlockCfg`. When `wait = wait' + 1`,
consumes one unit of `fuel` for an already-evaluated converged branch arm step
before executing `bb0`. -/
@[expose] def runBlockCfgLoop {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (fuel : Nat) (wait : Nat) (bb : Nat) (st : State) :
    BlockCfgOutcome Ret :=
  -- Use kernel-exposed `@Nat.rec` (compiled via `@[csimp]` to `Nat.recCompiled`)
  -- so downstream `module` proofs can reduce through `runBlockCfgLoop`.
  @Nat.rec (fun _ => Nat → Nat → State → BlockCfgOutcome Ret)
    (fun _ _ _ => .diverged)
    (fun _ ih wait0 bb0 st0 =>
      match wait0 with
      | wait' + 1 => ih wait' bb0 st0
      | 0 =>
        match stepBb bb0 st0 with
        | .fault => .fault
        | .ret v => .ret v
        | .jump nextBb st' => ih 0 nextBb st'
        | .jumpWrapped wrapRet nextBb st' =>
          match ih 0 nextBb st' with
          | .ret v =>
            match wrapRet v with
            | some v' => .ret v'
            | none => .fault
          | .diverged => .diverged
          | .fault => .fault
        | .convergedJump armSteps wrapRet nextBb st' =>
          match ih armSteps nextBb st' with
          | .ret v =>
            match wrapRet v with
            | some v' => .ret v'
            | none => .fault
          | .diverged => .diverged
          | .fault => .fault
        | .branchJump mergeRet thenBb elseBb st' =>
          match ih 0 thenBb st', ih 0 elseBb st' with
          | .ret vt, .ret vf =>
            match mergeRet vt vf with
            | some v => .ret v
            | none => .fault
          | .fault, _ => .fault
          | _, .fault => .fault
          | _, _ => .diverged)
    fuel wait bb st

/-- Run a block-indexed CFG for `fuel` basic-block transitions. A wrapper or
merge function that rejects its value makes the run fault. -/
@[expose] def runBlockCfg {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (bb : Nat) (st : State) (fuel : Nat) : BlockCfgOutcome Ret :=
  runBlockCfgLoop stepBb fuel 0 bb st

@[expose] def BlockCfgPartialSpec {Ret : Type} (out : BlockCfgOutcome Ret)
    (PostRet : Ret → Prop) : Prop :=
  match out with
  | .ret v => PostRet v
  | .diverged => True
  | .fault => False

/-- Per-block verification condition (`LocalBlockVC`) for compositional $O(N)$
CFG verification. A wrapper or merge function must accept every combination
of values satisfying `PostRet`, and produce a value satisfying `PostRet`. -/
@[expose] def LocalBlockVC {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop) : Prop :=
  ∀ bb st,
    BlockInv bb st →
    match stepBb bb st with
    | .fault => False
    | .ret v => PostRet v
    | .jump nextBb st' => BlockInv nextBb st'
    | .jumpWrapped wrapRet nextBb st' =>
      BlockInv nextBb st' ∧
      (∀ v, PostRet v →
        match wrapRet v with
        | some v' => PostRet v'
        | none => False)
    | .convergedJump _ wrapRet nextBb st' =>
      BlockInv nextBb st' ∧
      (∀ v, PostRet v →
        match wrapRet v with
        | some v' => PostRet v'
        | none => False)
    | .branchJump mergeRet thenBb elseBb st' =>
      BlockInv thenBb st' ∧ BlockInv elseBb st' ∧
      (∀ vt vf, PostRet vt → PostRet vf →
        match mergeRet vt vf with
        | some v => PostRet v
        | none => False)

theorem runBlockCfgLoop_succ_wait {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (fuel' wait' bb : Nat) (st : State) :
    runBlockCfgLoop stepBb (fuel' + 1) (wait' + 1) bb st =
      runBlockCfgLoop stepBb fuel' wait' bb st := rfl

theorem runBlockCfg_succ {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (bb : Nat) (st : State) (fuel' : Nat) :
    runBlockCfg stepBb bb st (fuel' + 1) =
      (match stepBb bb st with
       | .fault => .fault
       | .ret v => .ret v
       | .jump nextBb st' => runBlockCfg stepBb nextBb st' fuel'
       | .jumpWrapped wrapRet nextBb st' =>
         match runBlockCfg stepBb nextBb st' fuel' with
         | .ret v =>
           match wrapRet v with
           | some v' => .ret v'
           | none => .fault
         | .diverged => .diverged
         | .fault => .fault
       | .convergedJump armSteps wrapRet nextBb st' =>
         match runBlockCfgLoop stepBb fuel' armSteps nextBb st' with
         | .ret v =>
           match wrapRet v with
           | some v' => .ret v'
           | none => .fault
         | .diverged => .diverged
         | .fault => .fault
       | .branchJump mergeRet thenBb elseBb st' =>
         match runBlockCfg stepBb thenBb st' fuel',
               runBlockCfg stepBb elseBb st' fuel' with
         | .ret vt, .ret vf =>
           match mergeRet vt vf with
           | some v => .ret v
           | none => .fault
         | .fault, _ => .fault
         | _, .fault => .fault
         | _, _ => .diverged) := rfl

private def BlockCfgSpec {Ret : Type} (onFault : Prop)
    (out : BlockCfgOutcome Ret) (PostRet : Ret → Prop) : Prop :=
  match out with
  | .ret v => PostRet v
  | .diverged => True
  | .fault => onFault

private def LocalBlockSpecVC {State Ret : Type} (onFault : Prop)
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop) : Prop :=
  ∀ bb st,
    BlockInv bb st →
    match stepBb bb st with
    | .fault => onFault
    | .ret v => PostRet v
    | .jump nextBb st' => BlockInv nextBb st'
    | .jumpWrapped wrapRet nextBb st' =>
      BlockInv nextBb st' ∧
      (∀ v, PostRet v →
        match wrapRet v with
        | some v' => PostRet v'
        | none => onFault)
    | .convergedJump _ wrapRet nextBb st' =>
      BlockInv nextBb st' ∧
      (∀ v, PostRet v →
        match wrapRet v with
        | some v' => PostRet v'
        | none => onFault)
    | .branchJump mergeRet thenBb elseBb st' =>
      BlockInv thenBb st' ∧ BlockInv elseBb st' ∧
      (∀ vt vf, PostRet vt → PostRet vf →
        match mergeRet vt vf with
        | some v => PostRet v
        | none => onFault)

private theorem runBlockCfgLoop_spec_sound {State Ret : Type}
    {onFault : Prop}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop) (PostRet : Ret → Prop)
    (hLocal : LocalBlockSpecVC onFault stepBb BlockInv PostRet) :
    ∀ (fuel wait : Nat) (bb : Nat) (st : State),
      BlockInv bb st →
      BlockCfgSpec onFault (runBlockCfgLoop stepBb fuel wait bb st) PostRet
  | 0, _, _, _, _ => True.intro
  | fuel' + 1, wait' + 1, bb, st, hInv => by
    rw [runBlockCfgLoop_succ_wait]
    exact runBlockCfgLoop_spec_sound stepBb BlockInv PostRet hLocal
      fuel' wait' bb st hInv
  | fuel' + 1, 0, bb, st, hInv => by
    change BlockCfgSpec onFault (runBlockCfg stepBb bb st (fuel' + 1)) PostRet
    rw [runBlockCfg_succ]
    have hVC := hLocal bb st hInv
    cases hStep : stepBb bb st with
    | fault =>
      rw [hStep] at hVC
      exact hVC
    | ret v =>
      rw [hStep] at hVC
      exact hVC
    | jump nextBb st' =>
      rw [hStep] at hVC
      dsimp at hVC
      exact runBlockCfgLoop_spec_sound stepBb BlockInv PostRet hLocal
        fuel' 0 nextBb st' hVC
    | jumpWrapped wrapRet nextBb st' =>
      rw [hStep] at hVC
      dsimp at hVC
      dsimp [BlockCfgSpec]
      have ih := runBlockCfgLoop_spec_sound stepBb BlockInv PostRet hLocal
        fuel' 0 nextBb st' hVC.1
      cases hRun : runBlockCfg stepBb nextBb st' fuel' with
      | ret v =>
        change runBlockCfgLoop stepBb fuel' 0 nextBb st' = .ret v at hRun
        rw [hRun] at ih
        dsimp only
        have hWrap := hVC.2 v ih
        cases hW : wrapRet v with
        | none => rw [hW] at hWrap; exact hWrap
        | some v' => rw [hW] at hWrap; exact hWrap
      | diverged => exact True.intro
      | fault =>
        change runBlockCfgLoop stepBb fuel' 0 nextBb st' = .fault at hRun
        rw [hRun] at ih
        exact ih
    | convergedJump armSteps wrapRet nextBb st' =>
      rw [hStep] at hVC
      dsimp at hVC
      dsimp [BlockCfgSpec]
      have ih := runBlockCfgLoop_spec_sound stepBb BlockInv PostRet hLocal
        fuel' armSteps nextBb st' hVC.1
      cases hRun : runBlockCfgLoop stepBb fuel' armSteps nextBb st' with
      | ret v =>
        rw [hRun] at ih
        dsimp only
        have hWrap := hVC.2 v ih
        cases hW : wrapRet v with
        | none => rw [hW] at hWrap; exact hWrap
        | some v' => rw [hW] at hWrap; exact hWrap
      | diverged => exact True.intro
      | fault =>
        rw [hRun] at ih
        exact ih
    | branchJump mergeRet thenBb elseBb st' =>
      rw [hStep] at hVC
      dsimp at hVC
      dsimp [BlockCfgSpec]
      have ihT := runBlockCfgLoop_spec_sound stepBb BlockInv PostRet hLocal
        fuel' 0 thenBb st' hVC.1
      have ihF := runBlockCfgLoop_spec_sound stepBb BlockInv PostRet hLocal
        fuel' 0 elseBb st' hVC.2.1
      cases hRunT : runBlockCfg stepBb thenBb st' fuel' with
      | fault =>
        change runBlockCfgLoop stepBb fuel' 0 thenBb st' = .fault at hRunT
        rw [hRunT] at ihT
        exact ihT
      | diverged =>
        cases hRunF : runBlockCfg stepBb elseBb st' fuel' with
        | fault =>
          change runBlockCfgLoop stepBb fuel' 0 elseBb st' = .fault at hRunF
          rw [hRunF] at ihF
          exact ihF
        | diverged | ret _ => exact True.intro
      | ret vt =>
        cases hRunF : runBlockCfg stepBb elseBb st' fuel' with
        | fault =>
          change runBlockCfgLoop stepBb fuel' 0 elseBb st' = .fault at hRunF
          rw [hRunF] at ihF
          exact ihF
        | diverged => exact True.intro
        | ret vf =>
          change runBlockCfgLoop stepBb fuel' 0 thenBb st' = .ret vt at hRunT
          change runBlockCfgLoop stepBb fuel' 0 elseBb st' = .ret vf at hRunF
          rw [hRunT] at ihT
          rw [hRunF] at ihF
          dsimp only
          have hMerge := hVC.2.2 vt vf ihT ihF
          cases hM : mergeRet vt vf with
          | none => rw [hM] at hMerge; exact hMerge
          | some v => rw [hM] at hMerge; exact hMerge

theorem modular_block_cfg_loop_sound {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop)
    (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC stepBb BlockInv PostRet) :
    ∀ (fuel wait : Nat) (bb : Nat) (st : State),
      BlockInv bb st →
      BlockCfgPartialSpec (runBlockCfgLoop stepBb fuel wait bb st) PostRet :=
  runBlockCfgLoop_spec_sound stepBb BlockInv PostRet hLocal

/-- Compositional CFG soundness: if `LocalBlockVC` holds for every block, then
any `fuel`-step execution from an invariant-satisfying block state never faults
and satisfies `PostRet` whenever it returns. -/
theorem modular_block_cfg_sound {State Ret : Type}
    (stepBb : Nat → State → BlockStepResult State Ret)
    (BlockInv : Nat → State → Prop)
    (PostRet : Ret → Prop)
    (hLocal : LocalBlockVC stepBb BlockInv PostRet) :
    ∀ (fuel : Nat) (bb : Nat) (st : State),
      BlockInv bb st →
      BlockCfgPartialSpec (runBlockCfg stepBb bb st fuel) PostRet :=
  fun fuel bb st hInv =>
    modular_block_cfg_loop_sound stepBb BlockInv PostRet hLocal
      fuel 0 bb st hInv

/-- The promise a block result makes about the values the run returns through
it: a returned value, and every value that its wrapper or merge function
accepts, is free of borrow handles. -/
@[expose] def StepReturnsHandleFree {Val : Type} (alg : ValAlgebra Val) :
    BlockStepResult (SymState Val) (FuncOut Val) → Prop
  | .jump _ _ => True
  | .jumpWrapped wrapRet _ _ =>
    ∀ v out, wrapRet v = some out → handleFreeOut alg out = true
  | .convergedJump _ wrapRet _ _ =>
    ∀ v out, wrapRet v = some out → handleFreeOut alg out = true
  | .branchJump mergeRet _ _ _ =>
    ∀ vt vf out, mergeRet vt vf = some out → handleFreeOut alg out = true
  | .ret out => handleFreeOut alg out = true
  | .fault => True

theorem handleFreeOutOpt_eq_some {Val : Type} (alg : ValAlgebra Val)
    (out out' : FuncOut Val) (h : handleFreeOutOpt alg out = some out') :
    handleFreeOut alg out' = true := by
  unfold handleFreeOutOpt at h
  revert h
  cases hFree : handleFreeOut alg out with
  | true =>
    intro h
    injection h with hEq
    subst hEq
    exact hFree
  | false =>
    intro h
    nomatch h

theorem finishConvergedBranch_returnsHandleFree {Val : Type}
    (alg : ValAlgebra Val)
    (armSteps : Nat)
    (outerWrap : Option (FuncOut Val → FuncOut Val))
    (joinBb : BlockId) (joined : ExecFlow Val)
    (res : BlockStepResult (SymState Val) (FuncOut Val))
    (hFin :
      finishConvergedBranch alg armSteps outerWrap joinBb joined = some res) :
    StepReturnsHandleFree alg res := by
  unfold finishConvergedBranch at hFin
  revert hFin
  cases joined with
  | returned _ _ _ =>
    intro hFin
    nomatch hFin
  | continuing stJoined =>
    intro hFin
    injection hFin with hEq
    subst hEq
    exact fun _ out h => handleFreeOutOpt_eq_some alg _ out h
  | guardedContinuing wrapJoined stJoined valClean _ =>
    cases valClean with
    | false =>
      intro hFin
      injection hFin with hEq
      subst hEq
      exact True.intro
    | true =>
      intro hFin
      injection hFin with hEq
      subst hEq
      exact fun _ out h => handleFreeOutOpt_eq_some alg _ out h

theorem stepBasicBlock_returnsHandleFree {Val : Type} (alg : ValAlgebra Val)
    (blocks : List (BasicBlock Val)) (bbIdx : BlockId) (st : SymState Val) :
    StepReturnsHandleFree alg (stepBasicBlock alg blocks bbIdx st) := by
  unfold stepBasicBlock
  cases listGetOpt bbIdx blocks with
  | none => exact True.intro
  | some bb =>
    dsimp
    cases evalPlan alg bb.body st with
    | fail => exact True.intro
    | ok flow =>
      cases flow with
      | returned out valClean _ =>
        cases valClean with
        | false => exact True.intro
        | true =>
          dsimp
          cases hFree : handleFreeOut alg out with
          | false => exact True.intro
          | true => exact hFree
      | guardedContinuing wrapOut st' valClean _ =>
        cases valClean with
        | false => exact True.intro
        | true =>
          dsimp
          cases bb.term with
          | goto tgt =>
            exact fun _ out h => handleFreeOutOpt_eq_some alg _ out h
          | branch cond tTgt fTgt =>
            dsimp
            cases evalRval alg cond st' with
            | none => exact True.intro
            | some cv =>
              dsimp
              cases alg.asBool cv with
              | some b =>
                cases b <;>
                  exact fun _ out h => handleFreeOutOpt_eq_some alg _ out h
              | none =>
                dsimp
                cases tTgt == fTgt with
                | true =>
                  exact fun _ out h => handleFreeOutOpt_eq_some alg _ out h
                | false =>
                  dsimp
                  cases findConvergenceBlock blocks (blocks.length + 1)
                      tTgt fTgt [bbIdx] with
                  | none =>
                    exact fun _ _ out h => handleFreeOutOpt_eq_some alg _ out h
                  | some joinBb =>
                    dsimp
                    cases evalArmToJoin alg blocks (blocks.length + 1)
                        joinBb tTgt st' with
                    | fail =>
                      exact fun _ _ out h =>
                        handleFreeOutOpt_eq_some alg _ out h
                    | ok resT =>
                      cases resT with
                      | mk kT flowT =>
                        cases evalArmToJoin alg blocks (blocks.length + 1)
                            joinBb fTgt st' with
                        | fail =>
                          exact fun _ _ out h =>
                            handleFreeOutOpt_eq_some alg _ out h
                        | ok resF =>
                          cases resF with
                          | mk kF flowF =>
                            dsimp
                            cases joinExecFlow alg cv flowT flowF with
                            | none =>
                              exact fun _ _ out h =>
                                handleFreeOutOpt_eq_some alg _ out h
                            | some joined =>
                              dsimp
                              cases hFin :
                                  finishConvergedBranch alg (Nat.max kT kF)
                                    (some wrapOut) joinBb joined with
                              | none =>
                                exact fun _ _ out h =>
                                  handleFreeOutOpt_eq_some alg _ out h
                              | some res =>
                                exact finishConvergedBranch_returnsHandleFree
                                  alg (Nat.max kT kF) (some wrapOut) joinBb
                                  joined res hFin
          | ret retExpr =>
            dsimp
            cases stateCleanAtReturn st' with
            | false => exact True.intro
            | true =>
              dsimp
              cases evalRval alg retExpr st' with
              | none => exact True.intro
              | some rv =>
                dsimp
                cases hFree :
                    handleFreeOut alg
                      (wrapOut ⟨rv, collectRootMutVals st'.loans⟩) with
                | false => exact True.intro
                | true => exact hFree
      | continuing st' =>
        dsimp
        cases bb.term with
        | goto tgt => exact True.intro
        | branch cond tTgt fTgt =>
          dsimp
          cases evalRval alg cond st' with
          | none => exact True.intro
          | some cv =>
            dsimp
            cases alg.asBool cv with
            | some b => cases b <;> exact True.intro
            | none =>
              dsimp
              cases tTgt == fTgt with
              | true => exact True.intro
              | false =>
                dsimp
                cases findConvergenceBlock blocks (blocks.length + 1)
                    tTgt fTgt [bbIdx] with
                | none =>
                  exact fun _ _ out h => handleFreeOutOpt_eq_some alg _ out h
                | some joinBb =>
                  dsimp
                  cases evalArmToJoin alg blocks (blocks.length + 1)
                      joinBb tTgt st' with
                  | fail =>
                    exact fun _ _ out h =>
                      handleFreeOutOpt_eq_some alg _ out h
                  | ok resT =>
                    cases resT with
                    | mk kT flowT =>
                      cases evalArmToJoin alg blocks (blocks.length + 1)
                          joinBb fTgt st' with
                      | fail =>
                        exact fun _ _ out h =>
                          handleFreeOutOpt_eq_some alg _ out h
                      | ok resF =>
                        cases resF with
                        | mk kF flowF =>
                          dsimp
                          cases joinExecFlow alg cv flowT flowF with
                          | none =>
                            exact fun _ _ out h =>
                              handleFreeOutOpt_eq_some alg _ out h
                          | some joined =>
                            dsimp
                            cases hFin :
                                finishConvergedBranch alg (Nat.max kT kF)
                                  none joinBb joined with
                            | none =>
                              exact fun _ _ out h =>
                                handleFreeOutOpt_eq_some alg _ out h
                            | some res =>
                              exact finishConvergedBranch_returnsHandleFree
                                alg (Nat.max kT kF) none joinBb joined res hFin
        | ret retExpr =>
          dsimp
          cases stateCleanAtReturn st' with
          | false => exact True.intro
          | true =>
            dsimp
            cases evalRval alg retExpr st' with
            | none => exact True.intro
            | some rv =>
              dsimp
              cases hFree :
                  handleFreeOut alg ⟨rv, collectRootMutVals st'.loans⟩ with
              | false => exact True.intro
              | true => exact hFree

theorem runBlockCfgLoop_stepBasicBlock_handleFree {Val : Type}
    (alg : ValAlgebra Val) (blocks : List (BasicBlock Val))
    (fuel wait : Nat) (bb : Nat) (st : SymState Val) (out : FuncOut Val)
    (h : runBlockCfgLoop (stepBasicBlock alg blocks) fuel wait bb st = .ret out) :
    handleFreeOut alg out = true := by
  have hLocal : LocalBlockSpecVC True (stepBasicBlock alg blocks)
      (fun _ _ => True) (fun o => handleFreeOut alg o = true) := by
    intro b s _
    have hStep := stepBasicBlock_returnsHandleFree alg blocks b s
    cases hEq : stepBasicBlock alg blocks b s with
    | fault => exact True.intro
    | ret v =>
      rw [hEq] at hStep
      exact hStep
    | jump _ _ => exact True.intro
    | jumpWrapped wrapRet _ _ =>
      rw [hEq] at hStep
      refine ⟨True.intro, fun v _ => ?_⟩
      cases hW : wrapRet v with
      | none => exact True.intro
      | some out' => exact hStep v out' hW
    | convergedJump _ wrapRet _ _ =>
      rw [hEq] at hStep
      refine ⟨True.intro, fun v _ => ?_⟩
      cases hW : wrapRet v with
      | none => exact True.intro
      | some out' => exact hStep v out' hW
    | branchJump mergeRet _ _ _ =>
      rw [hEq] at hStep
      refine ⟨True.intro, True.intro, fun vt vf _ _ => ?_⟩
      cases hM : mergeRet vt vf with
      | none => exact True.intro
      | some out' => exact hStep vt vf out' hM
  have hSpec := runBlockCfgLoop_spec_sound (stepBasicBlock alg blocks)
    (fun _ _ => True) (fun o => handleFreeOut alg o = true) hLocal
    fuel wait bb st True.intro
  rw [h] at hSpec
  exact hSpec

/-- Every value that a CFG of basic blocks returns is free of borrow handles,
as `evalFnValue` requires of its result: no path through `.jumpWrapped`,
`.convergedJump`, or `.branchJump` skips the check. -/
theorem runBlockCfg_stepBasicBlock_handleFree {Val : Type}
    (alg : ValAlgebra Val) (blocks : List (BasicBlock Val)) :
    ∀ (fuel : Nat) (bb : Nat) (st : SymState Val) (out : FuncOut Val),
      runBlockCfg (stepBasicBlock alg blocks) bb st fuel = .ret out →
      handleFreeOut alg out = true :=
  fun fuel bb st out h =>
    runBlockCfgLoop_stepBasicBlock_handleFree alg blocks fuel 0 bb st out h

/-!
## CFG-to-`FlowPlan` Equivalence Certificates (`CfgCertificate`)
-/

/-- Certificate pairing a block-indexed CFG (`blocks`, `entryBb`, `fuel`) with
a structured `FlowPlan Val` and return expression `retExpr`, together with the
evidence `sound` that relates their executions: whenever the structured plan
returns `out` from an entry state, the CFG run for `fuel` block steps from the
same entry state returns the same `out`. Possessing a `CfgCertificate` thus
certifies the CFG-to-plan correspondence; it cannot be built for an unrelated
CFG and plan without proving `sound`. -/
structure CfgCertificate {Val : Type} (alg : ValAlgebra Val) where
  blocks : List (BasicBlock Val)
  entryBb : BlockId
  fuel : Nat
  plan : FlowPlan Val
  retExpr : RvalOp Val
  sound :
    ∀ (params : List (ParamInput Val)) (st0 : SymState Val)
      (out : FuncOut Val),
      initFnState alg params = .ok st0 →
      evalFnValue alg params plan retExpr = .ok out →
      runBlockCfg (stepBasicBlock alg blocks) entryBb st0 fuel = .ret out

/-- Single-block CFG equivalence (`cfg_certificate_step_sound`): executing a
1-block CFG `[⟨plan, .ret retExpr⟩]` for 1 step via `runBlockCfg` produces `.ret
out` whenever `evalFnValue alg params plan retExpr = .ok out`. -/
theorem cfg_certificate_step_sound {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) (st0 : SymState Val) (out : FuncOut Val)
    (hInit : initFnState alg params = .ok st0)
    (hEval : evalFnValue alg params plan retExpr = .ok out) :
    runBlockCfg (stepBasicBlock alg [⟨plan, .ret retExpr⟩]) 0 st0 1 =
      .ret out := by
  dsimp [evalFnValue] at hEval
  rw [hInit] at hEval
  dsimp at hEval
  rw [runBlockCfg_succ]
  dsimp [stepBasicBlock, listGetOpt]
  revert hEval
  cases hPlan : evalPlan alg plan st0 with
  | fail =>
    intro hFalse
    nomatch hFalse
  | ok flow =>
    cases flow with
    | returned out' valClean _ =>
      dsimp
      cases valClean with
      | false =>
        dsimp
        intro hFalse
        nomatch hFalse
      | true =>
        cases handleFreeOut alg out' with
        | false =>
          dsimp
          intro hFalse
          nomatch hFalse
        | true =>
          dsimp
          intro hEq
          injection hEq with hOut
          rw [hOut]
    | continuing stF =>
      dsimp
      cases hClean : stateCleanAtReturn stF with
      | false =>
        dsimp
        intro hFalse
        nomatch hFalse
      | true =>
        dsimp
        cases hRet : evalRval alg retExpr stF with
        | none =>
          dsimp
          intro hFalse
          nomatch hFalse
        | some retVal =>
          dsimp
          cases handleFreeOut alg ⟨retVal, collectRootMutVals stF.loans⟩ with
          | false =>
            dsimp
            intro hFalse
            nomatch hFalse
          | true =>
            dsimp
            intro hEq
            injection hEq with hOut
            rw [← hOut]
    | guardedContinuing guards stF valClean _ =>
      dsimp
      cases valClean with
      | false =>
        dsimp
        intro hFalse
        nomatch hFalse
      | true =>
        dsimp
        cases hClean : stateCleanAtReturn stF with
        | false =>
          dsimp
          intro hFalse
          nomatch hFalse
        | true =>
          dsimp
          cases hRet : evalRval alg retExpr stF with
          | none =>
            dsimp
            intro hFalse
            nomatch hFalse
          | some retVal =>
            dsimp
            cases handleFreeOut alg
                (guards ⟨retVal, collectRootMutVals stF.loans⟩) with
            | false =>
              dsimp
              intro hFalse
              nomatch hFalse
            | true =>
              dsimp
              intro hEq
              injection hEq with hOut
              rw [← hOut]

/-- Single-block `CfgCertificate`: the 1-block CFG `[⟨plan, .ret retExpr⟩]`
run for one step, certified by `cfg_certificate_step_sound`. -/
@[expose] def CfgCertificate.singleBlock {Val : Type} (alg : ValAlgebra Val)
    (plan : FlowPlan Val) (retExpr : RvalOp Val) : CfgCertificate alg where
  blocks := [⟨plan, .ret retExpr⟩]
  entryBb := 0
  fuel := 1
  plan := plan
  retExpr := retExpr
  sound := fun params st0 out hInit hEval =>
    cfg_certificate_step_sound alg params plan retExpr st0 out hInit hEval

/-- Sequential 2-block CFG equivalence (`cfg_seq_blocks_equiv`): a 2-block CFG
`[⟨p1, .goto 1⟩, ⟨p2, .ret retExpr⟩]` executed for 2 steps matches `evalPlan
alg (.seq p1 p2) st0` when `p1` falls through to `p2`. -/
theorem cfg_seq_blocks_equiv {Val : Type} (alg : ValAlgebra Val)
    (p1 p2 : FlowPlan Val) (retExpr : RvalOp Val)
    (st0 st1 stF : SymState Val) (retVal : Val)
    (hWf1 : WfPlan alg p1) (hWf2 : WfPlan alg p2)
    (h1 : evalPlan alg p1 st0 = .ok (.continuing st1))
    (h2 : evalPlan alg p2 st1 = .ok (.continuing stF))
    (hClean : stateCleanAtReturn stF = true)
    (hRet : evalRval alg retExpr stF = some retVal)
    (hFree : handleFreeOut alg ⟨retVal, collectRootMutVals stF.loans⟩ = true) :
    runBlockCfg
      (stepBasicBlock alg [⟨p1, .goto 1⟩, ⟨p2, .ret retExpr⟩])
      0 st0 2 =
      .ret ⟨retVal, collectRootMutVals stF.loans⟩ ∧
    evalPlan alg (.seq p1 p2) st0 = .ok (.continuing stF) := by
  have hLeft :
      runBlockCfg
        (stepBasicBlock alg [⟨p1, .goto 1⟩, ⟨p2, .ret retExpr⟩])
        0 st0 2 =
        .ret ⟨retVal, collectRootMutVals stF.loans⟩ := by
    rw [runBlockCfg_succ]
    dsimp [stepBasicBlock, listGetOpt]
    rw [h1]
    dsimp
    rw [runBlockCfg_succ]
    dsimp [stepBasicBlock, listGetOpt]
    rw [h2]
    dsimp
    rw [hClean]
    dsimp
    rw [hRet]
    dsimp
    rw [hFree]
    rfl
  have hRight :
      evalPlan alg (.seq p1 p2) st0 = .ok (.continuing stF) := by
    rw [evalPlan_seq alg p1 p2 st0 hWf1 hWf2]
    rw [h1]
    exact h2
  exact ⟨hLeft, hRight⟩

/-- Loop CFG equivalence (`cfg_certificate_while_sound`): for the 3-block loop
CFG `[⟨.skip, .branch cond 1 2⟩, ⟨body, .goto 0⟩, ⟨.skip, .ret retExpr⟩]`
(block `0` branches to body block `1` on `true` and to exit block `2` on
`false`), every execution of `runWhileFlowSteps alg cond (evalPlan alg body)
fuel st` that terminates in `.ok (.continuing stFinal)` with a clean return
state reaches `.ret` in `runBlockCfg` within `2 * fuel + 2` basic-block steps
with the same `FuncOut Val`. -/
theorem cfg_certificate_while_sound {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val) (body : FlowPlan Val) (retExpr : RvalOp Val) :
    ∀ (fuel : Nat) (st stFinal : SymState Val) (retVal : Val),
      runWhileFlowSteps alg cond (evalPlan alg body) fuel st =
        .ok (.continuing stFinal) →
      stateCleanAtReturn stFinal = true →
      evalRval alg retExpr stFinal = some retVal →
      handleFreeOut alg ⟨retVal, collectRootMutVals stFinal.loans⟩ = true →
      runBlockCfg
        (stepBasicBlock alg
          [⟨.skip, .branch cond 1 2⟩,
           ⟨body, .goto 0⟩,
           ⟨.skip, .ret retExpr⟩])
        0 st (2 * fuel + 2) =
        .ret ⟨retVal, collectRootMutVals stFinal.loans⟩
  | 0, st, stFinal, retVal, hWhile, hClean, hRet, hFree => by
    rw [runWhileFlowSteps_zero] at hWhile
    revert hWhile
    cases hCond : evalRval alg cond st with
    | none =>
      intro hFalse
      nomatch hFalse
    | some cv =>
      dsimp
      cases hBool : alg.asBool cv with
      | none =>
        intro hFalse
        nomatch hFalse
      | some b =>
        cases b with
        | true =>
          intro hFalse
          nomatch hFalse
        | false =>
          dsimp
          intro hEq
          injection hEq with hFlow
          injection hFlow with hSt
          subst hSt
          change
            runBlockCfg
              (stepBasicBlock alg
                [⟨.skip, .branch cond 1 2⟩,
                 ⟨body, .goto 0⟩,
                 ⟨.skip, .ret retExpr⟩])
              0 st 2 =
              .ret ⟨retVal, collectRootMutVals st.loans⟩
          rw [runBlockCfg_succ]
          dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
            stepPlanOp, FlowPlan.skip]
          rw [hCond]
          dsimp
          rw [hBool]
          dsimp
          rw [runBlockCfg_succ]
          dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
            stepPlanOp, FlowPlan.skip]
          rw [hClean]
          dsimp
          rw [hRet]
          dsimp
          rw [hFree]
          rfl
  | k + 1, st, stFinal, retVal, hWhile, hClean, hRet, hFree => by
    rw [runWhileFlowSteps_succ] at hWhile
    revert hWhile
    cases hCond : evalRval alg cond st with
    | none =>
      intro hFalse
      nomatch hFalse
    | some cv =>
      dsimp
      cases hBool : alg.asBool cv with
      | none =>
        intro hFalse
        nomatch hFalse
      | some b =>
        cases b with
        | false =>
          dsimp
          intro hEq
          injection hEq with hFlow
          injection hFlow with hSt
          subst hSt
          have hStep1 :
              stepBasicBlock alg
                [⟨.skip, .branch cond 1 2⟩,
                 ⟨body, .goto 0⟩,
                 ⟨.skip, .ret retExpr⟩] 0 st = .jump 2 st := by
            dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
              stepPlanOp, FlowPlan.skip]
            rw [hCond]
            dsimp
            rw [hBool]
          have hStep2 :
              stepBasicBlock alg
                [⟨.skip, .branch cond 1 2⟩,
                 ⟨body, .goto 0⟩,
                 ⟨.skip, .ret retExpr⟩] 2 st =
                .ret ⟨retVal, collectRootMutVals st.loans⟩ := by
            dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
              stepPlanOp, FlowPlan.skip]
            rw [hClean]
            dsimp
            rw [hRet]
            dsimp
            rw [hFree]
            rfl
          have hArith : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by
            rw [Nat.mul_add]
          rw [hArith, runBlockCfg_succ, hStep1]
          dsimp
          rw [runBlockCfg_succ, hStep2]
        | true =>
          dsimp
          cases hBody : evalPlan alg body st with
          | fail =>
            intro hFalse
            nomatch hFalse
          | ok flow =>
            cases flow with
            | returned _ _ _ =>
              intro hFalse
              nomatch hFalse
            | guardedContinuing wrap1 st' c1 wrapMut1 =>
              dsimp [prependGuardedWrap]
              cases runWhileFlowSteps alg cond (evalPlan alg body) k st' with
              | fail =>
                intro hFalse
                nomatch hFalse
              | ok flowRec =>
                cases flowRec <;> (intro hFalse; nomatch hFalse)
            | continuing st' =>
              dsimp
              intro hRec
              have ih :=
                cfg_certificate_while_sound alg cond body retExpr k st'
                  stFinal retVal hRec hClean hRet hFree
              have hStep1 :
                  stepBasicBlock alg
                    [⟨.skip, .branch cond 1 2⟩,
                     ⟨body, .goto 0⟩,
                     ⟨.skip, .ret retExpr⟩] 0 st = .jump 1 st := by
                dsimp [stepBasicBlock, listGetOpt, evalPlan, evalPlanOps,
                  stepPlanOp, FlowPlan.skip]
                rw [hCond]
                dsimp
                rw [hBool]
              have hStep2 :
                  stepBasicBlock alg
                    [⟨.skip, .branch cond 1 2⟩,
                     ⟨body, .goto 0⟩,
                     ⟨.skip, .ret retExpr⟩] 1 st = .jump 0 st' := by
                dsimp [stepBasicBlock, listGetOpt]
                rw [hBody]
              have hArith : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by
                rw [Nat.mul_add]
              rw [hArith, runBlockCfg_succ, hStep1]
              dsimp
              rw [runBlockCfg_succ, hStep2]
              exact ih

/-!
## Kernel-Checked Unit Tests
-/

theorem test_listGetOpt :
    listGetOpt 0 [10, 20, 30] = some 10 ∧
    listGetOpt 2 [10, 20, 30] = some 30 ∧
    listGetOpt 3 [10, 20, 30] = none :=
  ⟨rfl, rfl, rfl⟩

@[expose] def testCfgStep (bb : Nat) (st : Nat) : BlockStepResult Nat Nat :=
  match bb with
  | 0 => if st == 0 then .jump 2 st else .jump 1 (st - 1)
  | 1 => .jump 0 st
  | 2 => .ret (st + 100)
  | _ => .fault

theorem test_runBlockCfg_countdown :
    runBlockCfg testCfgStep 0 3 10 = .ret 100 ∧
    runBlockCfg testCfgStep 0 3 2 = .diverged ∧
    runBlockCfg testCfgStep 99 0 1 = .fault :=
  ⟨rfl, rfl, rfl⟩

/-- Unit tests for `stepBasicBlock` and `runBlockCfg` across
`.jumpWrapped` (when `evalPlan` returns `.guardedContinuing` before a `.goto` or
`.branch` terminator) and `.branchJump` (when a `.branch` terminator has a
symbolic condition `alg.asBool cv = none`). -/
theorem test_blockCfg_jumpWrapped_and_symbolic_branchJump :
    let guardedGotoBlocks : List (BasicBlock LensTestVal) :=
      [ ⟨.branch (.use (.localSub 0 []))
           (.earlyReturn [] [] (.constVal (.atom 10)))
           (.act (.assign (.localSub 1 []) (.constVal (.atom 20)))),
         .goto 1⟩
      , ⟨.act (.assign (.localSub 1 []) (.constVal (.atom 30))),
         .ret (.use (.localSub 1 []))⟩ ]
    let symBranchBlocks : List (BasicBlock LensTestVal) :=
      [ ⟨.skip, .branch (.use (.localSub 0 [])) 1 2⟩
      , ⟨.act (.assign (.localSub 1 []) (.constVal (.atom 111))),
         .ret (.use (.localSub 1 []))⟩
      , ⟨.act (.assign (.localSub 1 []) (.constVal (.atom 222))),
         .ret (.use (.localSub 1 []))⟩ ]
    let symDiamondBlocks : List (BasicBlock LensTestVal) :=
      [ ⟨.skip, .branch (.use (.localSub 0 [])) 1 2⟩
      , ⟨.act (.assign (.localSub 1 []) (.constVal (.atom 111))),
         .goto 3⟩
      , ⟨.act (.assign (.localSub 1 []) (.constVal (.atom 222))),
         .goto 3⟩
      , ⟨.skip, .ret (.constVal (.atom 1))⟩ ]
    (match initFnState lensTestValAlg [⟨.byVal, .node (.atom 1) (.atom 0)⟩] with
     | .ok stSym =>
       runBlockCfg (stepBasicBlock lensTestValAlg guardedGotoBlocks) 0 stSym 3 =
         .ret
           ⟨lensTestValAlg.zipVal (.node (.atom 1) (.atom 0))
              (.atom 10) (.atom 30), []⟩ ∧
       runBlockCfg (stepBasicBlock lensTestValAlg symBranchBlocks) 0 stSym 3 =
         .ret
           ⟨lensTestValAlg.zipVal (.node (.atom 1) (.atom 0))
              (.atom 111) (.atom 222), []⟩ ∧
       runBlockCfg (stepBasicBlock lensTestValAlg symDiamondBlocks) 0 stSym 2 =
         .diverged ∧
       runBlockCfg (stepBasicBlock lensTestValAlg symDiamondBlocks) 0 stSym 3 =
         .ret ⟨.atom 1, []⟩
     | .fail => False) :=
  ⟨rfl, rfl, rfl, rfl⟩

end Anneal.PureLift

end
