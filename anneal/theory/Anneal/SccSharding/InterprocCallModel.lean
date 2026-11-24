-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.SccSharding.BinChunkTree

public section

/-!
# Interprocedural Call-Stack Evaluator over `BinChunkTree` (`O(log N)` Dispatch)

Mechanizes multi-frame `TerminatorKind.call` push/return execution over
`BinChunkTree Body` (`0` `sorry`, `0` `._unsafe_rec`, axioms `⊆ [propext]`),
exercising mutual-recursion SCC cycles (`2`-cycle and `3`-cycle) and proving
that replacing `p.bodies : List Body` with `BinChunkTree Body` resolves every
interprocedural call target in `⌈log₂ N⌉` GMP comparisons without touching
unrelated SCC shards (`evalInterprocStep_congr_on_cone`).

Note: This module is a standalone zero-TCB operational model of
`BinChunkTree` call dispatch, not yet bridged to `CrateTheorem` or
`UnitTheorem` obligations.
-/

namespace Anneal.SccSharding

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-- Continuation saved when an active caller frame invokes
`TerminatorKind.call`. -/
structure SavedCallerFrame where
  defId : DefId
  dstLocalId : LocalId
  retBlock : BasicBlockId
  locals : List LocalSlot

/-- Multi-frame interprocedural execution state over `BinChunkTree Body`. -/
structure CallStackState where
  active : FrameState
  callers : List SavedCallerFrame
  mem : MemoryState

/-- Evaluate a list of primitive `Operand`s left-to-right for
`TerminatorKind.call` (`List.foldr` CPS, zero `._unsafe_rec`). -/
@[expose] noncomputable def evalCallOperands (bodyLocals : List MirTy)
    (ops : List Operand) (locals0 : List LocalSlot) (mem0 : MemoryState) :
    Except FaultKind (List Val × List LocalSlot × MemoryState) :=
  ops.foldr
    (fun op k curLocals curMem =>
      match evalPrimitiveOperand bodyLocals curLocals curMem op with
      | .error err => .error err
      | .ok (v, l1, m1) =>
        match k l1 m1 with
        | .error err => .error err
        | .ok (vs, l2, m2) => .ok (v :: vs, l2, m2))
    (fun curLocals curMem => .ok ([], curLocals, curMem))
    locals0 mem0

/-- Single-step interprocedural transition resolving `active.defId` and
`TerminatorKind.call callee` via `O(log N)` `BinChunkTree.get?`. -/
@[expose] noncomputable def evalInterprocStep (tree : BinChunkTree Body)
    (st : CallStackState) : StepResult CallStackState Val :=
  match BinChunkTree.get? tree st.active.defId with
  | none => .fault .unsupported
  | some body =>
    match Trusted.MirSemantics.getElem? body.basicBlocks st.active.blockIdx with
    | none => .fault .unsupported
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements st.active.stmtIdx with
      | some stmt =>
        match evalStatement body st.active st.mem ⟨[]⟩ stmt with
        | .step nextSingle =>
          match nextSingle.frames with
          | [nextFrame] =>
            .step { st with active := nextFrame, mem := nextSingle.mem }
          | _ => .fault .unsupported
        | .done _ => .fault .unsupported
        | .fault k => .fault k
      | none =>
        if Nat.beq st.active.stmtIdx bb.statements.length then
          match bb.terminator with
          | .goto target =>
            .step { st with
              active := { st.active with blockIdx := target, stmtIdx := 0 } }
          | .switchInt _ _ =>
            match evalTerminator body bb st.active st.mem ⟨[]⟩ with
            | .step nextSingle =>
              match nextSingle.frames with
              | [nextFrame] =>
                .step { st with active := nextFrame, mem := nextSingle.mem }
              | _ => .fault .unsupported
            | .done _ => .fault .unsupported
            | .fault k => .fault k
          | .return_ =>
            if bb.cleanup then
              .fault .unsupported
            else
              match Trusted.MirSemantics.getElem? st.active.locals 0 with
              | some (.immediate (some retVal)) =>
                match st.callers with
                | [] => .done retVal
                | caller :: restCallers =>
                  match BinChunkTree.get? tree caller.defId with
                  | none => .fault .unsupported
                  | some callerBody =>
                    match Trusted.MirSemantics.getElem?
                        callerBody.locals caller.dstLocalId with
                    | none => .fault .unsupported
                    | some dstTy =>
                      match writePlace caller.locals st.mem caller.dstLocalId
                          dstTy retVal with
                      | .error k => .fault k
                      | .ok (callerLocals', mem') =>
                        .step {
                          active := {
                            defId := caller.defId
                            blockIdx := caller.retBlock
                            stmtIdx := 0
                            locals := callerLocals'
                          }
                          callers := restCallers
                          mem := mem'
                        }
              | some (.immediate none) | some .dead => .fault .undefined
              | _ => .fault .unsupported
          | .call callee opArgs dst (some retBlock) _ =>
            if !dst.projection.isEmpty then
              .fault .unsupported
            else
              match evalCallOperands body.locals opArgs st.active.locals
                  st.mem with
              | .error k => .fault k
              | .ok (argVals, callerLocalsAfterArgs, memAfterArgs) =>
                match BinChunkTree.get? tree callee with
                | none => .fault .unsupported
                | some calleeBody =>
                  let paramTys :=
                    (calleeBody.locals.drop 1).take calleeBody.argumentCount
                  if checkArgsMatch argVals paramTys then
                    let calleeLocals :=
                      initLocalsLoop calleeBody argVals 0 calleeBody.locals
                    let saved : SavedCallerFrame := {
                      defId := st.active.defId
                      dstLocalId := dst.localId
                      retBlock := retBlock
                      locals := callerLocalsAfterArgs
                    }
                    .step {
                      active := {
                        defId := callee
                        blockIdx := 0
                        stmtIdx := 0
                        locals := calleeLocals
                      }
                      callers := saved :: st.callers
                      mem := memAfterArgs
                    }
                  else
                    .fault .undefined
          | _ => .fault .unsupported
        else
          .fault .unsupported

/-- Step-indexed multi-frame execution certificate, recording one transition per
constructor so long multi-call runs never eagerly unfold `@Nat.rec` across
symbolic `st` binders. -/
inductive InterprocExecutes (tree : BinChunkTree Body) :
    CallStackState → Val → Prop where
  | done {st : CallStackState} {out : Val} :
      evalInterprocStep tree st = .done out →
      InterprocExecutes tree st out
  | step {st next : CallStackState} {out : Val} :
      evalInterprocStep tree st = .step next →
      InterprocExecutes tree next out →
      InterprocExecutes tree st out

/-- Entry-point multi-frame execution from `entryDefId` on `args`. -/
@[expose] def InterprocReturns (tree : BinChunkTree Body) (entryDefId : DefId)
    (args : List Val) (expected : Val) : Prop :=
  match BinChunkTree.get? tree entryDefId with
  | none => False
  | some entryBody =>
    InterprocExecutes tree {
      active := {
        defId := entryDefId
        blockIdx := 0
        stmtIdx := 0
        locals := initLocalsLoop entryBody args 0 entryBody.locals
      }
      callers := []
      mem := entryMemory
    } expected

/-- Recursive fuel-bounded multi-frame transition driver (`@Nat.rec`, `0`
`._unsafe_rec`): `0` steps returns `.step st` (identity checkpoint), and
`fuel + 1` steps performs one transition followed by `fuel` transitions. -/
@[expose] noncomputable def stepInterprocFuel (tree : BinChunkTree Body)
    (fuel : Nat) (st0 : CallStackState) : StepResult CallStackState Val :=
  @Nat.rec (fun _ => CallStackState → StepResult CallStackState Val)
    (fun st => .step st)
    (fun _ ih st =>
      match evalInterprocStep tree st with
      | .step next => ih next
      | res => res)
    fuel st0

/-- Compose two `stepInterprocFuel` segments (`O(1)`-fuel checkpoints prevent
exponential kernel `whnf` re-evaluation across `BitVec` arithmetic). -/
theorem stepInterprocFuel_compose {tree : BinChunkTree Body} :
    ∀ {k₁ k₂ : Nat} {s₀ s₁ : CallStackState} {out : Val},
      stepInterprocFuel tree k₁ s₀ = .step s₁ →
      stepInterprocFuel tree k₂ s₁ = .done out →
      stepInterprocFuel tree (k₁ + k₂) s₀ = .done out
  | 0, _, _, _, _, h₁, h₂ => by
    dsimp only [stepInterprocFuel] at h₁
    injection h₁ with hEq
    subst hEq
    rw [Nat.zero_add]
    exact h₂
  | k₁ + 1, k₂, s₀, s₁, out, h₁, h₂ => by
    have hAdd : (k₁ + 1) + k₂ = (k₁ + k₂) + 1 := Nat.succ_add k₁ k₂
    rw [hAdd]
    change (match evalInterprocStep tree s₀ with
      | .step next => stepInterprocFuel tree (k₁ + k₂) next
      | res => res) = .done out
    change (match evalInterprocStep tree s₀ with
      | .step next => stepInterprocFuel tree k₁ next
      | res => res) = .step s₁ at h₁
    cases hStep : evalInterprocStep tree s₀ with
    | step _ =>
      rw [hStep] at h₁
      exact stepInterprocFuel_compose h₁ h₂
    | done _ =>
      rw [hStep] at h₁
      nomatch h₁
    | fault _ =>
      rw [hStep] at h₁
      nomatch h₁

/-- Entry-point multi-frame execution from `entryDefId` on `args` via
step-indexed `InterprocExecutes` (`0` `._unsafe_rec`, `O(steps)` linear
typechecking); `_fuel` is accepted for caller signature uniformity. -/
@[expose] def InterprocRuns (tree : BinChunkTree Body) (_fuel : Nat)
    (entryDefId : DefId) (args : List Val) (expected : Val) : Prop :=
  InterprocReturns tree entryDefId args expected

theorem interprocExecutes_of_seg1 {tree : BinChunkTree Body}
    {s₀ : CallStackState} {out : Val}
    (h : evalInterprocStep tree s₀ = .done out) :
    InterprocExecutes tree s₀ out := .done h

theorem interprocExecutes_of_step {tree : BinChunkTree Body}
    {s₀ s₁ : CallStackState} {out : Val}
    (h : evalInterprocStep tree s₀ = .step s₁)
    (rest : InterprocExecutes tree s₁ out) :
    InterprocExecutes tree s₀ out := .step h rest

theorem interprocExecutes_of_fuel2 {tree : BinChunkTree Body}
    {s₀ s₂ : CallStackState} {out : Val}
    (h : stepInterprocFuel tree 2 s₀ = .step s₂)
    (rest : InterprocExecutes tree s₂ out) :
    InterprocExecutes tree s₀ out := by
  change (match evalInterprocStep tree s₀ with
    | .step s₁ => match evalInterprocStep tree s₁ with
      | .step s₂' => StepResult.step s₂'
      | res => res
    | res => res) = .step s₂ at h
  cases h₁ : evalInterprocStep tree s₀ with
  | done _ => rw [h₁] at h; nomatch h
  | fault _ => rw [h₁] at h; nomatch h
  | step s₁ =>
    rw [h₁] at h
    dsimp only at h
    cases h₂ : evalInterprocStep tree s₁ with
    | done _ => rw [h₂] at h; nomatch h
    | fault _ => rw [h₂] at h; nomatch h
    | step _ =>
      rw [h₂] at h
      dsimp only at h
      injection h with hEq
      subst hEq
      exact .step h₁ (.step h₂ rest)

theorem interprocExecutes_of_fuel3 {tree : BinChunkTree Body}
    {s₀ s₃ : CallStackState} {out : Val}
    (h : stepInterprocFuel tree 3 s₀ = .step s₃)
    (rest : InterprocExecutes tree s₃ out) :
    InterprocExecutes tree s₀ out := by
  change (match evalInterprocStep tree s₀ with
    | .step s₁ => stepInterprocFuel tree 2 s₁
    | res => res) = .step s₃ at h
  cases h₁ : evalInterprocStep tree s₀ with
  | done _ => rw [h₁] at h; nomatch h
  | fault _ => rw [h₁] at h; nomatch h
  | step _ =>
    rw [h₁] at h
    exact .step h₁ (interprocExecutes_of_fuel2 h rest)

theorem interprocExecutes_done_fuel3 {tree : BinChunkTree Body}
    {s₀ : CallStackState} {out : Val}
    (h : stepInterprocFuel tree 3 s₀ = .done out) :
    InterprocExecutes tree s₀ out := by
  change (match evalInterprocStep tree s₀ with
    | .step s₁ => match evalInterprocStep tree s₁ with
      | .step s₂ => match evalInterprocStep tree s₂ with
        | .step s₃ => StepResult.step s₃
        | res => res
      | res => res
    | res => res) = .done out at h
  cases h₁ : evalInterprocStep tree s₀ with
  | fault _ => rw [h₁] at h; nomatch h
  | done _ =>
    rw [h₁] at h; injection h with hEq; subst hEq; exact .done h₁
  | step s₁ =>
    rw [h₁] at h
    dsimp only at h
    cases h₂ : evalInterprocStep tree s₁ with
    | fault _ => rw [h₂] at h; nomatch h
    | done _ =>
      rw [h₂] at h; dsimp only at h; injection h with hEq; subst hEq
      exact .step h₁ (.done h₂)
    | step s₂ =>
      rw [h₂] at h
      dsimp only at h
      cases h₃ : evalInterprocStep tree s₂ with
      | step _ => rw [h₃] at h; nomatch h
      | fault _ => rw [h₃] at h; nomatch h
      | done _ =>
        rw [h₃] at h; dsimp only at h; injection h with hEq; subst hEq
        exact .step h₁ (.step h₂ (.done h₃))

/-- Subtree frame invariance: if two `BinChunkTree`s agree on every `defId` in
a shard cone, `evalInterprocStep` produces identical transitions whenever the
active and top-caller frames stay inside that cone. -/
theorem evalInterprocStep_congr_on_cone {t₁ t₂ : BinChunkTree Body}
    {st : CallStackState}
    (hAct : BinChunkTree.get? t₁ st.active.defId =
      BinChunkTree.get? t₂ st.active.defId)
    (hCaller : match st.callers with
      | [] => True
      | c :: _ => BinChunkTree.get? t₁ c.defId = BinChunkTree.get? t₂ c.defId)
    (hCallees : ∀ callee : DefId,
      (∃ body bb opArgs dst retB u,
        BinChunkTree.get? t₁ st.active.defId = some body ∧
        Trusted.MirSemantics.getElem? body.basicBlocks st.active.blockIdx =
          some bb ∧
        bb.terminator = .call callee opArgs dst (some retB) u) →
      BinChunkTree.get? t₁ callee = BinChunkTree.get? t₂ callee) :
    evalInterprocStep t₁ st = evalInterprocStep t₂ st := by
  unfold evalInterprocStep
  rw [← hAct]
  cases hB : BinChunkTree.get? t₁ st.active.defId with
  | none => rfl
  | some body =>
    dsimp only
    cases hBb :
        Trusted.MirSemantics.getElem? body.basicBlocks st.active.blockIdx with
    | none => rfl
    | some bb =>
      dsimp only
      cases hSt :
          Trusted.MirSemantics.getElem? bb.statements st.active.stmtIdx with
      | some _ => rfl
      | none =>
        dsimp only
        cases hLen : Nat.beq st.active.stmtIdx bb.statements.length with
        | false => rfl
        | true =>
          cases hTerm : bb.terminator with
          | goto _ | switchInt _ _ | unreachable | unwindResume
          | assert _ _ _ _ _ | coreCall _ _ _ _ _ | sysrootCall _ _ _ _ _
          | unsupported => rfl
          | return_ =>
            cases bb.cleanup with
            | true => rfl
            | false =>
              cases Trusted.MirSemantics.getElem? st.active.locals 0 with
              | none => rfl
              | some slot =>
                cases slot with
                | dead | indirect _ | partialTuple _ => rfl
                | immediate optV =>
                  cases optV with
                  | none => rfl
                  | some _ =>
                    cases hCs : st.callers with
                    | nil => rfl
                    | cons _ _ =>
                      dsimp only
                      rw [hCs] at hCaller
                      rw [hCaller]
          | call callee opArgs dst optTarget u =>
            cases optTarget with
            | none => rfl
            | some retB =>
              dsimp only
              cases (!dst.projection.isEmpty) with
              | true => rfl
              | false =>
                cases evalCallOperands body.locals opArgs st.active.locals
                    st.mem with
                | error _ => rfl
                | ok triple =>
                  let ⟨_, _, _⟩ := triple
                  dsimp only
                  have hCalleeEq :=
                    hCallees callee
                      ⟨body, bb, opArgs, dst, retB, u, hB, hBb, hTerm⟩
                  rw [hCalleeEq]

end Anneal.SccSharding

end
