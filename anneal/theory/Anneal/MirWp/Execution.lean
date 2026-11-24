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
public import Anneal.MirWp.Core
public import Anneal.MirWp.Scalars
public import Anneal.MirWp.Reflection

public section

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics Anneal.Framework.StepWp

/-! ## Part III: Single-Body Execution, WP Bridge, Productive Invariants, and
Multi-Body Retagging

This part runs one body as the single-body unit program `bodyProg body`. One
step is the trusted transition `evalStep (bodyProg body) 0`, and the entry state
on `args` is `mkState 0 0 (initLocalsLoop body args 0 body.locals)`: one frame
at `defId := 0`, block `0`, and statement `0`, holding the locals that
`initState` builds. Every notion below is a proposition over these trusted
terms. The trusted semantics has no executable code, so a definition that
computed a step or a run would have to be exempted from code generation, which
`theory/` never does. Concrete runs therefore state the fuel-bounded weakest
precondition `RunsFrom` and prove it by `rfl`. -/

/-- Single-body program wrapper for unit-level execution of `body`. -/
@[expose] def bodyProg (body : Body) : Program :=
  { scope := .unit, pointerWidthBits := 64, mirProfileVersion := 1,
    bodies := [body] }

/-- Finite-step reachability in `body` under `evalStep (bodyProg body) 0`. -/
inductive Reach (body : Body) : State → State → Prop where
  | refl {state : State} : Reach body state state
  | next {start mid next : State} :
      Reach body start mid →
      evalStep (bodyProg body) 0 mid = .step next →
      Reach body start next

/-- Prefix fault-freedom of `body` starting from `start`. -/
@[expose] def SafeFrom (body : Body) (start : State) : Prop :=
  ∀ state kind, Reach body start state →
    evalStep (bodyProg body) 0 state ≠ .fault kind

/-- Prefix fault-freedom of `body` from its entry state on `args`. -/
@[expose] def Safe (body : Body) (args : List Val) : Prop :=
  SafeFrom body (mkState 0 0 (initLocalsLoop body args 0 body.locals))

/-- Normal return of `output` from `start` in `body`. -/
@[expose] def ReturnsFrom (body : Body) (start : State) (output : Val) : Prop :=
  ∃ state, Reach body start state ∧
    evalStep (bodyProg body) 0 state = .done (.returned ⟨output, ⟨[]⟩⟩)

/-- Normal return of `output` from the entry state of `body` on `args`. -/
@[expose] def Returns (body : Body) (args : List Val) (output : Val) : Prop :=
  ReturnsFrom body (mkState 0 0 (initLocalsLoop body args 0 body.locals))
    output

/-- Fuel-bounded run certificate: from `start`, `body` returns `output` within
`fuel` steps and never faults. It is the deterministic `c = 0` execution
predicate of `bodyProg body` with an exact return postcondition, so a concrete
run reduces by `rfl`. -/
abbrev RunsFrom (body : Body) (fuel : Nat) (start : State) (output : Val) :
    Prop :=
  execState (bodyProg body) fuel start
    (fun out => out = .returned ⟨output, ⟨[]⟩⟩)

/-- Fuel-bounded run certificate from the entry state of `body` on `args`. -/
abbrev Runs (body : Body) (fuel : Nat) (args : List Val) (output : Val) :
    Prop :=
  RunsFrom body fuel (mkState 0 0 (initLocalsLoop body args 0 body.locals))
    output

/-- Step-by-step normal-return certificate for `body`. Each constructor records
one rewritten transition, so long symbolic runs never accumulate an unnormalized
`whnf` term. -/
inductive Executes (body : Body) : State → Val → Prop where
  | ret {start : State} {value : Val} :
      evalStep (bodyProg body) 0 start = .done (.returned ⟨value, ⟨[]⟩⟩) →
      Executes body start value
  | next {start next : State} {value : Val} :
      evalStep (bodyProg body) 0 start = .step next →
      Executes body next value →
      Executes body start value

/-- Exact equivalence between program-level `Reaches (bodyProg body)` and
single-body `Reach body`. -/
theorem reaches_bodyProg_iff_reach {body : Body} {s₁ s₂ : State} :
    Reaches (bodyProg body) s₁ s₂ ↔ Reach body s₁ s₂ := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hStep ih =>
      let ⟨c, hc, hEval⟩ := hStep
      subst hc
      exact .next ih hEval
  · intro h
    induction h with
    | refl => exact .refl _
    | next _ hStep ih => exact .tail ih ⟨0, rfl, hStep⟩

/-- Prepend a single transition onto a `Reach` chain. -/
theorem reach_prepend {body : Body} {start next finish : State}
    (first : evalStep (bodyProg body) 0 start = .step next)
    (rest : Reach body next finish) :
    Reach body start finish :=
  reaches_bodyProg_iff_reach.mp
    (Reaches.head ⟨0, rfl, first⟩ (reaches_bodyProg_iff_reach.mpr rest))

/-- Case-split a `Reach` chain whose start state steps to `next`. -/
theorem reach_cases {body : Body} {start next finish : State}
    (first : evalStep (bodyProg body) 0 start = .step next)
    (reached : Reach body start finish) :
    finish = start ∨ Reach body next finish := by
  induction reached with
  | refl => exact .inl rfl
  | @next before after _ transition ih =>
    cases ih with
    | inl equal =>
      subst before
      have same : StepResult.step next = .step after :=
        first.symm.trans transition
      injection same with h_eq
      subst h_eq
      exact .inr .refl
    | inr rest => exact .inr (.next rest transition)

/-- No further states are reachable after a `.done (.returned ...)` step. -/
theorem reachable_after_return {body : Body} {start finish : State}
    {value : Val}
    (returned :
      evalStep (bodyProg body) 0 start = .done (.returned ⟨value, ⟨[]⟩⟩))
    (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    rw [returned] at transition
    cases transition

/-- No further states are reachable after a `.fault` step. -/
theorem reachable_after_fault {body : Body} {start finish : State}
    {reason : FaultKind}
    (faulted : evalStep (bodyProg body) 0 start = .fault reason)
    (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    rw [faulted] at transition
    cases transition

/-- A state that immediately returns is prefix-safe (`SafeFrom`). -/
theorem safeFrom_return {body : Body} {start : State} {value : Val}
    (returned :
      evalStep (bodyProg body) 0 start = .done (.returned ⟨value, ⟨[]⟩⟩)) :
    SafeFrom body start := by
  intro finish reason reached
  have same := reachable_after_return returned reached
  subst finish
  rw [returned]
  intro h
  cases h

/-- Prefix safety steps backward across a deterministic `.step` transition. -/
theorem safeFrom_next {body : Body} {start next : State}
    (first : evalStep (bodyProg body) 0 start = .step next)
    (rest : SafeFrom body next) :
    SafeFrom body start := by
  intro finish reason reached
  cases reach_cases first reached with
  | inl equal =>
    subst finish
    rw [first]
    intro h
    cases h
  | inr tail => exact rest finish reason tail

/-- Prefix safety composes backward across any finite `Reach` prefix. -/
theorem safeFrom_of_reach {body : Body} {start checkpoint : State}
    (segment : Reach body start checkpoint)
    (suffix : SafeFrom body checkpoint) :
    SafeFrom body start := by
  induction segment with
  | refl => exact suffix
  | next _ transition ih => exact ih (safeFrom_next transition suffix)

/-- Bridge from fuel-bounded `wpState (bodyProg body)` to `SafeFrom`: holds even
when symbolic branches return distinct values. -/
theorem safeFrom_of_wpState {body : Body} {fuel : Nat} {start : State}
    {post : TerminalOut → Prop}
    (hWp : wpState (bodyProg body) fuel start post) :
    SafeFrom body start := by
  intro state kind hReach hFault
  let ⟨fuel', hWp'⟩ :=
    wpOutcomeState_of_reaches hWp (reaches_bodyProg_iff_reach.mpr hReach)
  cases fuel' with
  | zero => exact hWp'
  | succ _ =>
    have hBranch := hWp'.2 0 rfl
    rw [hFault] at hBranch
    exact hBranch

/-- Exact equivalence between the step-by-step `Executes` certificate and the
fuel-bounded `RunsFrom` certificate (unifying single-body certificates with the
core WP calculus). -/
theorem executes_iff_wpState {body : Body} {start : State} {value : Val} :
    Executes body start value ↔ ∃ fuel, RunsFrom body fuel start value := by
  constructor
  · intro execution
    induction execution with
    | @ret s val hRet =>
      refine ⟨1, ?_⟩
      dsimp only [RunsFrom, execState, execOutcomeState, execStepOutcome]
      rw [execStepPred_succ_iff, hRet]
    | @next s next val hStep _ ih =>
      let ⟨fuel, hExec⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      dsimp only [RunsFrom, execState, execOutcomeState, execStepOutcome]
      rw [execStepPred_succ_iff, hStep]
      exact hExec
  · intro hEx
    cases hEx with
    | intro fuel hExec =>
      induction fuel generalizing start with
      | zero => exact False.elim hExec
      | succ fuel ih =>
        dsimp only [RunsFrom, execState, execOutcomeState, execStepOutcome] at hExec
        rw [execStepPred_succ_iff] at hExec
        cases hStep : evalStep (bodyProg body) 0 start with
        | step next =>
          rw [hStep] at hExec
          exact .next hStep (ih hExec)
        | done out =>
          rw [hStep] at hExec
          dsimp only at hExec
          subst hExec
          exact .ret hStep
        | fault k =>
          rw [hStep] at hExec
          exact False.elim hExec

/-- Prepend a `Reach` segment onto an `Executes` suffix. -/
theorem executes_prepend {body : Body} {start checkpoint : State} {value : Val}
    (segment : Reach body start checkpoint)
    (suffix : Executes body checkpoint value) :
    Executes body start value := by
  induction segment with
  | refl => exact suffix
  | next _ transition ih => exact ih (.next transition suffix)

/-- Every `Executes` certificate establishes `SafeFrom` (derived directly from
`executes_iff_wpState` and `safeFrom_of_wpState`). -/
theorem executes_safe {body : Body} {start : State} {value : Val}
    (execution : Executes body start value) :
    SafeFrom body start :=
  let ⟨_, hExec⟩ := executes_iff_wpState.mp execution
  safeFrom_of_wpState (wpOutcomeState_of_execOutcomeState hExec)

/-- Every `Executes` certificate establishes `ReturnsFrom` (derived directly
from `executes_iff_wpState` and `exists_terminal_of_wpOutcomeState`). -/
theorem executes_returns {body : Body} {start : State} {value : Val}
    (execution : Executes body start value) :
    ReturnsFrom body start value := by
  let ⟨_, hExec⟩ := executes_iff_wpState.mp execution
  let ⟨sEnd, res, hReach, hTerm, hRes⟩ :=
    exists_terminal_of_wpOutcomeState
      (wpOutcomeState_of_execOutcomeState hExec)
  cases res with
  | step _ => exact False.elim hRes
  | fault _ => exact False.elim hRes
  | done out =>
    dsimp only at hRes
    subst hRes
    let ⟨c, hc, hEval⟩ := hTerm
    subst hc
    exact ⟨sEnd, reaches_bodyProg_iff_reach.mp hReach, hEval⟩

/-- Determinism of `Executes` against any `ReturnsFrom` witness (derived
directly from `wpOutcomeState_of_reaches`). -/
theorem executes_unique {body : Body} {start : State} {left right : Val}
    (execution : Executes body start left)
    (returned : ReturnsFrom body start right) :
    left = right := by
  let ⟨_, hExec⟩ := executes_iff_wpState.mp execution
  let ⟨finish, hReach, hRet⟩ := returned
  let ⟨fuel', hWp'⟩ :=
    wpOutcomeState_of_reaches (wpOutcomeState_of_execOutcomeState hExec)
      (reaches_bodyProg_iff_reach.mpr hReach)
  cases fuel' with
  | zero => exact False.elim hWp'
  | succ _ =>
    have hBranch := hWp'.2 0 rfl
    rw [hRet] at hBranch
    injection hBranch with hOut
    injection hOut with hVal _
    exact hVal.symm

/-- Every fuel-bounded run certificate yields an `Executes` certificate. -/
theorem run_executes {body : Body} {fuel : Nat} {start : State} {value : Val}
    (success : RunsFrom body fuel start value) :
    Executes body start value :=
  executes_iff_wpState.mpr ⟨fuel, success⟩

/-- A run certificate establishes prefix safety and normal return. -/
theorem run_success {body : Body} {fuel : Nat} {start : State} {value : Val}
    (success : RunsFrom body fuel start value) :
    SafeFrom body start ∧ ReturnsFrom body start value :=
  ⟨executes_safe (run_executes success),
    executes_returns (run_executes success)⟩

/-- A run certificate from the entry state establishes `Safe` and `Returns`. -/
theorem run_initial_success {body : Body} {fuel : Nat} {args : List Val}
    {value : Val} (success : Runs body fuel args value) :
    Safe body args ∧ Returns body args value :=
  run_success success

/-- A run certificate determines the only value that `body` can return. -/
theorem run_result_unique {body : Body} {fuel : Nat} {start : State}
    {left right : Val}
    (success : RunsFrom body fuel start left)
    (returned : ReturnsFrom body start right) :
    left = right :=
  executes_unique (run_executes success) returned

/-- Inductive preservation of `invariant` across all `Reach` states. -/
theorem invariant_reachable {body : Body} {start finish : State}
    (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before →
      evalStep (bodyProg body) 0 before = .step after → invariant after)
    (reached : Reach body start finish) :
    invariant finish := by
  induction reached with
  | refl => exact entry
  | next _ transition ih => exact closed _ _ ih transition

/-- Inductive invariant rule for `SafeFrom` (supporting non-terminating loops).
-/
theorem safeFrom_invariant {body : Body} {start : State}
    (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before →
      evalStep (bodyProg body) 0 before = .step after → invariant after)
    (noFault : ∀ state, invariant state → ∀ reason,
      evalStep (bodyProg body) 0 state ≠ .fault reason) :
    SafeFrom body start := by
  intro finish reason reached
  have preserved := invariant_reachable invariant entry closed reached
  exact noFault finish preserved reason

/-- A state self-loop reaches only itself. -/
theorem reachable_selfLoop {body : Body} {start finish : State}
    (loop : evalStep (bodyProg body) 0 start = .step start)
    (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    have equal := loop.symm.trans transition
    injection equal with h_eq
    exact h_eq.symm

/-- Any immediate self-loop is prefix-safe. -/
theorem safeFrom_selfLoop {body : Body} {start : State}
    (loop : evalStep (bodyProg body) 0 start = .step start) :
    SafeFrom body start := by
  intro finish reason reached
  have same := reachable_selfLoop loop reached
  subst finish
  rw [loop]
  intro h
  cases h

/-- A productive state invariant holds at `start`, is closed under `.step`, and
ensures every invariant state takes a `.step` transition (ruling out both
`.fault` and `.done` simultaneously). -/
@[expose] def ProductiveInvariant (body : Body) (start : State)
    (invariant : State → Prop) : Prop :=
  invariant start ∧
  (∀ before after, invariant before →
    evalStep (bodyProg body) 0 before = .step after → invariant after) ∧
  (∀ state, invariant state →
    ∃ next, evalStep (bodyProg body) 0 state = .step next)

/-- Every `ProductiveInvariant` simultaneously establishes `SafeFrom` and
absence of normal `.done` termination from `start`. -/
theorem safeFrom_and_no_done_of_productiveInvariant
    {body : Body} {start : State} {invariant : State → Prop}
    (hInv : ProductiveInvariant body start invariant) :
    SafeFrom body start ∧
    ∀ s out, Reach body start s →
      evalStep (bodyProg body) 0 s ≠ .done out := by
  refine ⟨safeFrom_invariant invariant hInv.1 hInv.2.1 ?_, ?_⟩
  · intro s hs reason hFault
    let ⟨_, hStep⟩ := hInv.2.2 s hs
    rw [hStep] at hFault
    cases hFault
  · intro s out hReach hDone
    have hs := invariant_reachable invariant hInv.1 hInv.2.1 hReach
    let ⟨_, hStep⟩ := hInv.2.2 s hs
    rw [hStep] at hDone
    cases hDone

/-! ### Single-Pass Frame Retagging Between `bodyProg` and `entryProgForBody` -/

/-- Rewrite the active single-frame `defId` of `s` to `d`. -/
@[expose] def retagDefId (d : DefId) (s : State) : State :=
  match s.frames with
  | [f] => { s with frames := [{ f with defId := d }] }
  | _ => s

/-- True iff `s` has a single active stack frame at `defId = 0`. -/
@[expose] def IsSingleFrame0 (s : State) : Prop :=
  ∃ f : FrameState, s.frames = [f] ∧ f.defId = 0

/-- Every `mkState` at the default `defId` is a single frame at `defId = 0`. -/
theorem isSingleFrame0_mkState (blockIdx stmtIdx : Nat)
    (locals : List LocalSlot) :
    IsSingleFrame0 (mkState blockIdx stmtIdx locals) :=
  ⟨_, rfl, rfl⟩

/-- Single-pass `evalStatement` frame invariant and `retagDefId` commutation. -/
theorem evalStatement_frame_retag (body : Body) (defId : DefId)
    (f : FrameState) (m : MemoryState) (cm : CallerMemory)
    (stmt : StatementKind) (h_id : f.defId = 0) :
    (∀ s', evalStatement body f m cm stmt = .step s' → IsSingleFrame0 s') ∧
    evalStatement body { f with defId := defId } m cm stmt =
      match evalStatement body f m cm stmt with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  unfold evalStatement retagDefId
  cases stmt with
  | nop =>
    refine ⟨?_, rfl⟩
    intro s' hStep
    injection hStep with hEq; subst hEq
    exact ⟨_, rfl, h_id⟩
  | storageLive lid =>
    dsimp only
    cases Trusted.MirSemantics.getElem? body.locals lid with
    | none => exact ⟨(fun _ h => by cases h), rfl⟩
    | some ty =>
      dsimp only
      cases Trusted.MirSemantics.getElem? f.locals lid with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some old =>
        dsimp only
        cases setElem? f.locals lid (liveUninitSlot ty) with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some l' =>
          dsimp only
          cases deallocateLocal m old with
          | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
          | ok m' =>
            refine ⟨?_, rfl⟩
            intro s' hStep
            injection hStep with hEq; subst hEq
            exact ⟨_, rfl, h_id⟩
  | storageDead lid =>
    dsimp only
    cases Nat.beq lid 0 with
    | true => exact ⟨(fun _ h => by cases h), rfl⟩
    | false =>
      cases Trusted.MirSemantics.getElem? f.locals lid with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some old =>
        dsimp only
        cases setElem? f.locals lid .dead with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some l' =>
          dsimp only
          cases deallocateLocal m old with
          | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
          | ok m' =>
            refine ⟨?_, rfl⟩
            intro s' hStep
            injection hStep with hEq; subst hEq
            exact ⟨_, rfl, h_id⟩
  | assign dst rv =>
    dsimp only
    cases (!dst.projection.isEmpty) with
    | true => exact ⟨(fun _ h => by cases h), rfl⟩
    | false =>
      cases Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some dstTy =>
        dsimp only
        cases evalRvalue body.locals f.locals m dstTy rv with
        | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
        | ok triple =>
          cases triple with
          | mk v rest =>
            cases rest with
            | mk l₁ m₁ =>
              dsimp only
              cases writePlace l₁ m₁ dst.localId dstTy v with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                cases pair with
                | mk l' m' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep
                  injection hStep with hEq; subst hEq
                  exact ⟨_, rfl, h_id⟩
  | unsupported => exact ⟨(fun _ h => by cases h), rfl⟩

/-- Single-pass `evalTerminator` frame invariant and `retagDefId` commutation.
-/
theorem evalTerminator_frame_retag (body : Body) (bb : BasicBlock)
    (defId : DefId) (f : FrameState) (m : MemoryState) (cm : CallerMemory)
    (h_id : f.defId = 0) :
    (∀ s', evalTerminator body bb f m cm = .step s' → IsSingleFrame0 s') ∧
    evalTerminator body bb { f with defId := defId } m cm =
      match evalTerminator body bb f m cm with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  unfold evalTerminator jumpToBlock retagDefId
  cases bb.terminator with
  | goto target =>
    refine ⟨?_, rfl⟩
    intro s' hStep
    injection hStep with hEq; subst hEq
    exact ⟨_, rfl, h_id⟩
  | return_ =>
    dsimp only
    cases bb.cleanup with
    | true => exact ⟨(fun _ h => by cases h), rfl⟩
    | false =>
      cases Trusted.MirSemantics.getElem? f.locals 0 with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some slot =>
        cases slot with
        | dead => exact ⟨(fun _ h => by cases h), rfl⟩
        | partialTuple _ => exact ⟨(fun _ h => by cases h), rfl⟩
        | immediate opt =>
          cases opt <;> exact ⟨(fun _ h => by cases h), rfl⟩
        | indirect place =>
          dsimp only
          cases Trusted.MirSemantics.getElem? body.locals 0 with
          | none => exact ⟨(fun _ h => by cases h), rfl⟩
          | some retTy =>
            dsimp only
            cases loadIndirect m retTy place with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok opt =>
              cases opt <;> exact ⟨(fun _ h => by cases h), rfl⟩
  | unreachable => exact ⟨(fun _ h => by cases h), rfl⟩
  | switchInt discr targets =>
    dsimp only
    cases evalPrimitiveOperand body.locals f.locals m discr with
    | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
    | ok triple =>
      cases triple with
      | mk dv rest =>
        cases rest with
        | mk l₁ m₁ =>
          dsimp only
          cases dv with
          | scalar sv =>
            dsimp only
            cases evalSwitchBranches sv.width sv.bits targets.otherwise
                targets.branches with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok tgt =>
              refine ⟨?_, rfl⟩
              intro s' hStep
              injection hStep with hEq; subst hEq
              exact ⟨_, rfl, h_id⟩
          | bool b =>
            dsimp only
            cases evalBoolSwitchBranches b targets.otherwise
                targets.branches with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok tgt =>
              refine ⟨?_, rfl⟩
              intro s' hStep
              injection hStep with hEq; subst hEq
              exact ⟨_, rfl, h_id⟩
          | char c =>
            dsimp only
            cases evalCharSwitchBranches c targets.otherwise
                targets.branches with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok tgt =>
              refine ⟨?_, rfl⟩
              intro s' hStep
              injection hStep with hEq; subst hEq
              exact ⟨_, rfl, h_id⟩
          | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | ordering _ | unit | tuple _ | array _ | bytes _ | enumVal _ _ =>
            dsimp only
            cases targets.branches with
            | nil =>
              refine ⟨?_, rfl⟩
              intro s' hStep
              injection hStep with hEq; subst hEq
              exact ⟨_, rfl, h_id⟩
            | cons _ _ => exact ⟨(fun _ h => by cases h), rfl⟩
  | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | coreCall _ _ _ _ _
  | sysrootCall _ _ _ _ _ | unsupported =>
    exact ⟨(fun _ h => by cases h), rfl⟩

private theorem basicBlocks_getElem_hasCall_false
    {bbs : List BasicBlock} {blk : BasicBlockId} {bb : BasicBlock}
    (h_nocall : bbs.any (fun b =>
      match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false) = false)
    (h_bb : Trusted.MirSemantics.getElem? bbs blk = some bb) :
    (match bb.terminator with
     | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
     | _ => false) = false := by
  induction bbs generalizing blk with
  | nil => cases h_bb
  | cons b rest ih =>
    unfold List.any at h_nocall
    dsimp only at h_nocall
    cases hOr : (match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false)
    · rw [hOr, Bool.false_or] at h_nocall
      cases blk with
      | zero =>
        injection h_bb with hEq; subst hEq; exact hOr
      | succ blk' =>
        exact ih h_nocall h_bb
    · rw [hOr, Bool.true_or] at h_nocall
      cases h_nocall

private theorem bodyHasAnyCall_false_of_getElem? {body : Body}
    {blk : BasicBlockId} {bb : BasicBlock}
    (h_nocall : bodyHasAnyCall body = false)
    (h_bb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb) :
    (match bb.terminator with
     | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
     | _ => false) = false :=
  basicBlocks_getElem_hasCall_false h_nocall h_bb

/-- Every body in a list whose entries are all call-free has
`bodyHasAnyCall body = false`. -/
theorem bodyHasAnyCall_false_of_all {bodies : List Body} {defId : DefId}
    {body : Body}
    (h_body : Trusted.MirSemantics.getElem? bodies defId = some body)
    (h_all : bodies.all (fun b => !bodyHasAnyCall b) = true) :
    bodyHasAnyCall body = false := by
  induction bodies generalizing defId with
  | nil => cases h_body
  | cons b rest ih =>
    unfold List.all at h_all
    dsimp only at h_all
    cases hNot : !bodyHasAnyCall b with
    | false => rw [hNot, Bool.false_and] at h_all; cases h_all
    | true =>
      rw [hNot, Bool.true_and] at h_all
      cases defId with
      | zero =>
        injection h_body with hEq; subst hEq
        cases hCall : bodyHasAnyCall b with
        | false => rfl
        | true => rw [hCall] at hNot; cases hNot
      | succ idx => exact ih h_body h_all

/-- Any body whose `basicBlocks` equals a call-free list `bbs` has
`bodyHasAnyCall body = false`. -/
theorem bodyHasAnyCall_false_of_basicBlocks {body : Body}
    {bbs : List BasicBlock} (h_bbs : body.basicBlocks = bbs)
    (h_no : bbs.any (fun b =>
      match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false) = false) :
    bodyHasAnyCall body = false := by
  unfold bodyHasAnyCall
  rw [h_bbs]
  exact h_no

private def retagStepResult (defId : DefId) :
    StepResult State TerminalOut → StepResult State TerminalOut
  | .step next => .step (retagDefId defId next)
  | .done out => .done out
  | .fault k => .fault k

private theorem evalStep_attachCallers_nil_pair
    {defId : DefId} {r₁ r₂ : StepResult State TerminalOut}
    (h_inv : ∀ s', r₁ = .step s' → IsSingleFrame0 s')
    (h_eq : r₂ = retagStepResult defId r₁) :
    (∀ s', attachCallers [] r₁ = .step s' → IsSingleFrame0 s') ∧
    attachCallers [] r₂ = retagStepResult defId (attachCallers [] r₁) := by
  rw [h_eq]
  cases r₁ with
  | fault k => exact ⟨(fun _ h => by cases h), rfl⟩
  | done out => exact ⟨(fun _ h => by cases h), rfl⟩
  | step next =>
    let ⟨f', hf', h_id'⟩ := h_inv next rfl
    cases next with
    | mk frames cm mem =>
      dsimp only at hf'
      subst hf'
      refine ⟨?_, rfl⟩
      intro s' hs'
      dsimp only [attachCallers] at hs'
      injection hs' with hEq
      subst hEq
      exact ⟨f', rfl, h_id'⟩

/-- Combined single-step `IsSingleFrame0` preservation and `retagDefId`
simulation between `evalStep (bodyProg body) 0` and
`evalStep (entryProgForBody p defId) 0` for call-free bodies. -/
theorem evalStep_entryProg_frame {p : Program} {defId : DefId} {body : Body}
    {s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_f0 : IsSingleFrame0 s)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    (∀ s', evalStep (bodyProg body) 0 s = .step s' → IsSingleFrame0 s') ∧
    evalStep (entryProgForBody p defId) 0 (retagDefId defId s) =
      match evalStep (bodyProg body) 0 s with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  let ⟨f, hf, h_id⟩ := h_f0
  cases s with
  | mk frames cm mem =>
    dsimp only at hf
    subst hf
    cases h_sys : f.sysrootOp? with
    | some op =>
      unfold bodyProg evalStep retagDefId entryProgForBody
      dsimp only [activeFrameBody]
      rw [h_sys]
      dsimp only [Trusted.MirSemantics.getElem?]
      cases h_bb : Trusted.MirSemantics.getElem? (sysrootNumBody op).basicBlocks
          f.blockIdx with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some bb =>
        dsimp only
        cases Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
        | some stmt =>
          have h_st := evalStatement_frame_retag (sysrootNumBody op) defId f mem cm
            stmt h_id
          rw [h_sys] at h_st
          exact evalStep_attachCallers_nil_pair h_st.1 h_st.2
        | none =>
          dsimp only
          cases Nat.beq f.stmtIdx bb.statements.length with
          | false => exact ⟨(fun _ h => by cases h), rfl⟩
          | true =>
            rw [ite_bool_true rfl]
            have hTerm := evalTerminator_frame_retag (sysrootNumBody op) bb defId
              f mem cm h_id
            rw [h_sys] at hTerm
            cases hT : bb.terminator with
            | call _ _ _ _ _ | sysrootCall _ _ _ _ _ =>
              cases hBl : f.blockIdx with
              | zero =>
                rw [hBl] at h_bb
                dsimp [sysrootNumBody, Trusted.MirSemantics.getElem?] at h_bb
                injection h_bb with hEq
                rw [← hEq] at hT
                cases hT
              | succ _ =>
                rw [hBl] at h_bb
                dsimp [sysrootNumBody, Trusted.MirSemantics.getElem?] at h_bb
                cases h_bb
            | return_ =>
              exact hTerm
            | goto _ | switchInt _ _ | unreachable | unwindResume
            | assert _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported =>
              exact evalStep_attachCallers_nil_pair hTerm.1 hTerm.2
    | none =>
      unfold bodyProg evalStep retagDefId entryProgForBody
      dsimp only [activeFrameBody]
      rw [h_sys, h_body, h_id]
      dsimp only [Trusted.MirSemantics.getElem?]
      cases h_bb : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some bb =>
        dsimp only
        cases Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
        | some stmt =>
          have h_st := evalStatement_frame_retag body defId f mem cm stmt h_id
          rw [h_sys] at h_st
          exact evalStep_attachCallers_nil_pair h_st.1 h_st.2
        | none =>
          dsimp only
          cases Nat.beq f.stmtIdx bb.statements.length with
          | false => exact ⟨(fun _ h => by cases h), rfl⟩
          | true =>
            rw [ite_bool_true rfl]
            have hNoCallBB := bodyHasAnyCall_false_of_getElem? h_nocall h_bb
            have hTerm := evalTerminator_frame_retag body bb defId f mem cm h_id
            rw [h_sys] at hTerm
            cases hT : bb.terminator with
            | call _ _ _ _ _ => rw [hT] at hNoCallBB; cases hNoCallBB
            | sysrootCall _ _ _ _ _ => rw [hT] at hNoCallBB; cases hNoCallBB
            | return_ =>
              exact hTerm
            | goto _ | switchInt _ _ | unreachable | unwindResume
            | assert _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported =>
              exact evalStep_attachCallers_nil_pair hTerm.1 hTerm.2

/-- `IsSingleFrame0` is preserved by a single-body step for call-free bodies. -/
theorem isSingleFrame0_of_step {body : Body} {s s' : State}
    (h_f0 : IsSingleFrame0 s)
    (h_step : evalStep (bodyProg body) 0 s = .step s')
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    IsSingleFrame0 s' :=
  (evalStep_entryProg_frame (p := bodyProg body) (defId := 0) rfl h_f0
    h_nocall).1 s' h_step

/-- Every state reachable from a single-frame `defId = 0` state in a call-free
body is again a single frame at `defId = 0`. -/
theorem isSingleFrame0_of_reach {body : Body} {start s : State}
    (h_start : IsSingleFrame0 start)
    (h_reach : Reach body start s)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    IsSingleFrame0 s := by
  induction h_reach with
  | refl => exact h_start
  | next _ h_step ih => exact isSingleFrame0_of_step ih h_step h_nocall

/-- `evalStep (entryProgForBody p defId) 0` commutes with `retagDefId defId` on
single-frame `defId = 0` states for call-free bodies. -/
theorem evalStep_retagDefId {p : Program} {defId : DefId} {body : Body}
    {s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_f0 : IsSingleFrame0 s)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    evalStep (entryProgForBody p defId) 0 (retagDefId defId s) =
      match evalStep (bodyProg body) 0 s with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k :=
  (evalStep_entryProg_frame h_body h_f0 h_nocall).2

/-- Exact equivalence of `execOutcomeState` across `retagDefId` between
`entryProgForBody p defId` and `bodyProg body` for call-free bodies. -/
theorem execOutcomeState_entryProg_iff {p : Program} {defId : DefId}
    {body : Body} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    {fuel : Nat} {s : State} (h_f0 : IsSingleFrame0 s)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    execOutcomeState (entryProgForBody p defId) onDone onFault fuel
      (retagDefId defId s) ↔
    execOutcomeState (bodyProg body) onDone onFault fuel s :=
  execStepOutcome_bisim
    (step₁ := evalStep (bodyProg body) 0)
    (step₂ := evalStep (entryProgForBody p defId) 0)
    (Inv := IsSingleFrame0) (map := retagDefId defId)
    (fun _ s' hF hS => (evalStep_entryProg_frame h_body hF h_nocall).1 s' hS)
    (fun st hF => by
      have he := (evalStep_entryProg_frame h_body hF h_nocall).2
      cases hEv : evalStep (bodyProg body) 0 st <;> rw [hEv] at he <;> exact he)
    h_f0

/-- Exact equivalence of `wpOutcomeState` across `retagDefId` between
`entryProgForBody p defId` and `bodyProg body` for call-free bodies. -/
theorem wpOutcomeState_entryProg_iff {p : Program} {defId : DefId}
    {body : Body} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    {fuel : Nat} {s : State} (h_f0 : IsSingleFrame0 s)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    wpOutcomeState (entryProgForBody p defId) onDone onFault fuel
      (retagDefId defId s) ↔
    wpOutcomeState (bodyProg body) onDone onFault fuel s :=
  wpOutcomeState_iff_execOutcomeState.trans
    ((execOutcomeState_entryProg_iff h_body h_f0 h_nocall).trans
      wpOutcomeState_iff_execOutcomeState.symm)

/-- Entry initialization equation specialized to `entryProgForBody p defId`,
stated as the retagged entry state of `bodyProg body`. -/
theorem initState_entryProgForBody {p : Program} {defId : DefId} {body : Body}
    {args : List Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args) :
    initState (entryProgForBody p defId) { args := args } =
      .ok (retagDefId defId
        (mkState 0 0 (initLocalsLoop body args 0 body.locals))) :=
  initState_eq_ok (p := entryProgForBody p defId) h_body h_adm h_args

/-- Project a state of `entryProgForBody p defId` reachable from a retagged
single-frame state back to `Reach body` via `retagDefId`. -/
theorem reach_of_reaches_entryProg {p : Program} {defId : DefId} {body : Body}
    {start s_d : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_start : IsSingleFrame0 start)
    (h_reaches :
      Reaches (entryProgForBody p defId) (retagDefId defId start) s_d)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    ∃ s : State, s_d = retagDefId defId s ∧ Reach body start s := by
  induction h_reaches with
  | refl => exact ⟨start, rfl, .refl⟩
  | tail _ h_step ih =>
    let ⟨s, hs, h_reach_s⟩ := ih
    let ⟨c, hc, h_eval⟩ := h_step
    subst hc
    subst hs
    have h_f0 := isSingleFrame0_of_reach h_start h_reach_s h_nocall
    rw [evalStep_retagDefId h_body h_f0 h_nocall] at h_eval
    cases h_st : evalStep (bodyProg body) 0 s with
    | step next =>
      rw [h_st] at h_eval
      injection h_eval with h_eq
      exact ⟨next, h_eq.symm, .next h_reach_s h_st⟩
    | done _ => rw [h_st] at h_eval; cases h_eval
    | fault _ => rw [h_st] at h_eval; cases h_eval

/-- Lift a single-body `Reach` trace from a single-frame state to
`Reaches (entryProgForBody p defId)` via `retagDefId`. -/
theorem reaches_entryProg_of_reach {p : Program} {defId : DefId} {body : Body}
    {start s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_start : IsSingleFrame0 start)
    (h_reach : Reach body start s)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    Reaches (entryProgForBody p defId) (retagDefId defId start)
      (retagDefId defId s) := by
  induction h_reach with
  | refl => exact .refl _
  | next h_prev h_st ih =>
    have h_f0 := isSingleFrame0_of_reach h_start h_prev h_nocall
    refine .tail ih ⟨0, rfl, ?_⟩
    rw [evalStep_retagDefId h_body h_f0 h_nocall, h_st]

/-- Establish per-invocation `WellFormed (entryProgForBody p defId)` from
single-body `Safe body args`. -/
theorem wellFormed_entryProg_of_safe {p : Program} {defId : DefId}
    {body : Body} {args : List Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args)
    (h_safe : Safe body args)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    WellFormed (entryProgForBody p defId) { args := args } := by
  have h_init := initState_entryProgForBody h_body h_adm h_args
  refine ⟨⟨_, h_init, ?_⟩, ?_⟩
  · intro _ _
    exact ⟨0, rfl⟩
  · intro k h_fault
    unfold ReachesResult at h_fault
    rw [h_init] at h_fault
    let ⟨s_d, h_reaches, c, hc, h_eval⟩ := h_fault
    subst hc
    let ⟨s, hs, h_reach_s⟩ :=
      reach_of_reaches_entryProg h_body (isSingleFrame0_mkState 0 0 _)
        h_reaches h_nocall
    subst hs
    have h_f0 :=
      isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach_s h_nocall
    rw [evalStep_retagDefId h_body h_f0 h_nocall] at h_eval
    cases h_st : evalStep (bodyProg body) 0 s with
    | step _ => rw [h_st] at h_eval; cases h_eval
    | done _ => rw [h_st] at h_eval; cases h_eval
    | fault k' =>
      rw [h_st] at h_eval
      injection h_eval with h_k
      subst h_k
      exact h_safe s k' h_reach_s h_st

/-- Establish `BodyVerified p defId body safetyPre` from single-body `Safe`. -/
theorem bodyVerified_of_safe {p : Program} {defId : DefId} {body : Body}
    {safetyPre : List Val → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_safe : ∀ args : List Val,
      ValidEntryArgs body args →
      (body.isUnsafe = true → safetyPre args) →
      Safe body args)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    BodyVerified p defId body safetyPre :=
  ⟨h_body, h_adm, fun args h_args h_req =>
    wellFormed_entryProg_of_safe h_body h_adm h_args (h_safe args h_args h_req)
      h_nocall⟩

/-- Establish `Behavior (entryProgForBody p defId)` from single-body `Returns`.
-/
theorem behavior_of_returns {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args)
    (h_ret : Returns body args ret)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    Behavior (entryProgForBody p defId) { args := args }
      (.returned ⟨ret, ⟨[]⟩⟩) := by
  let ⟨s, h_reach, h_done⟩ := h_ret
  unfold Behavior ReachesResult
  rw [initState_entryProgForBody h_body h_adm h_args]
  refine ⟨retagDefId defId s,
    reaches_entryProg_of_reach h_body (isSingleFrame0_mkState 0 0 _) h_reach
      h_nocall,
    0, rfl, ?_⟩
  have h_f0 := isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach
    h_nocall
  rw [evalStep_retagDefId h_body h_f0 h_nocall, h_done]

/-- Invert `initState (entryProgForBody p defId) { args := args } = .ok s₀` into
`ValidEntryArgs body args` and the retagged entry state of `body` on `args`. -/
theorem initState_entryProgForBody_ok {p : Program} {defId : DefId}
    {body : Body} {args : List Val} {s₀ : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_init : initState (entryProgForBody p defId) { args := args } = .ok s₀) :
    ValidEntryArgs body args ∧
      s₀ = retagDefId defId
        (mkState 0 0 (initLocalsLoop body args 0 body.locals)) := by
  unfold initState at h_init
  unfold ValidEntryArgs mkState retagDefId
  dsimp only at h_init
  dsimp only
  rw [show (entryProgForBody p defId).pointerWidthBits = p.pointerWidthBits from rfl,
    show (entryProgForBody p defId).mirProfileVersion = p.mirProfileVersion from rfl,
    show (entryProgForBody p defId).bodies = p.bodies from rfl,
    show (entryProgForBody p defId).entryDefId = defId from rfl] at h_init
  cases h1 : Nat.beq p.pointerWidthBits 64
  · rw [ite_bool_true (by rw [h1]; rfl)] at h_init; cases h_init
  cases h2 : Nat.beq p.mirProfileVersion 1
  · rw [ite_bool_true (by rw [h1, h2]; rfl)] at h_init; cases h_init
  rw [ite_bool_false (by rw [h1, h2]; rfl)] at h_init
  rw [ite_bool_false (rfl : (!([].isEmpty)) = false)] at h_init
  rw [h_body] at h_init
  dsimp only at h_init
  cases h3 : body.basicBlocks.isEmpty
  · rw [ite_bool_false h3] at h_init
    cases h4 : Nat.blt body.argumentCount body.locals.length
    · rw [ite_bool_true (by rw [h4]; rfl)] at h_init; cases h_init
    rw [ite_bool_false (by rw [h4]; rfl)] at h_init
    cases h5 : storageAnnotationsInBounds body
    · rw [ite_bool_true (by rw [h5]; rfl)] at h_init; cases h_init
    rw [ite_bool_false (by rw [h5]; rfl)] at h_init
    cases h5d : discriminantTypesValid body
    · rw [ite_bool_true (by rw [h5d]; rfl)] at h_init; cases h_init
    rw [ite_bool_false (by rw [h5d]; rfl)] at h_init
    cases h5c : castTypesValid body
    · rw [ite_bool_true (by rw [h5c]; rfl)] at h_init; cases h_init
    rw [ite_bool_false (by rw [h5c]; rfl)] at h_init
    cases h6 : body.locals.all isSupportedScalarOrUnitTy
    · rw [ite_bool_true (by rw [h6]; rfl)] at h_init; cases h_init
    rw [ite_bool_false (by rw [h6]; rfl)] at h_init
    cases h6c : callsAdmitted (entryProgForBody p defId) body
    · rw [ite_bool_true (by rw [h6c]; rfl)] at h_init; cases h_init
    rw [ite_bool_false (by rw [h6c]; rfl)] at h_init
    cases h6a : allCallBodiesStaticAdmitted (entryProgForBody p defId) body
    · rw [ite_bool_true (by rw [h6a]; rfl)] at h_init; cases h_init
    rw [ite_bool_false (by rw [h6a]; rfl)] at h_init
    cases h7 : checkArgsMatch args ((body.locals.drop 1).take body.argumentCount)
    · rw [ite_bool_true (by rw [h7]; rfl)] at h_init; cases h_init
    rw [ite_bool_false (by rw [h7]; rfl)] at h_init
    injection h_init with hs
    exact ⟨rfl, hs.symm⟩
  · rw [ite_bool_true h3] at h_init; cases h_init

/-- Invert `Behavior (entryProgForBody p defId)` into `ValidEntryArgs` and
single-body `Returns` for call-free bodies. -/
theorem returns_of_behavior {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_beh : Behavior (entryProgForBody p defId) { args := args }
      (.returned ⟨ret, ⟨[]⟩⟩))
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    ValidEntryArgs body args ∧ Returns body args ret := by
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState (entryProgForBody p defId) { args := args } with
  | error _ => rw [h_init] at h_beh; cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨h_args, hs₀⟩ := initState_entryProgForBody_ok h_body h_init
    subst hs₀
    let ⟨s_d, h_reaches, c, hc, h_eval⟩ := h_beh
    subst hc
    let ⟨s, hs, h_reach⟩ :=
      reach_of_reaches_entryProg h_body (isSingleFrame0_mkState 0 0 _)
        h_reaches h_nocall
    subst hs
    have h_f0 := isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach
      h_nocall
    rw [evalStep_retagDefId h_body h_f0 h_nocall] at h_eval
    cases h_st : evalStep (bodyProg body) 0 s with
    | step _ => rw [h_st] at h_eval; cases h_eval
    | fault _ => rw [h_st] at h_eval; cases h_eval
    | done out =>
      rw [h_st] at h_eval
      injection h_eval with h_out
      subst h_out
      exact ⟨h_args, s, h_reach, h_st⟩

/-- Refute `Behavior (entryProgForBody p defId) { args := args } out` when no
state reachable from the entry state of `body` on `args` steps to
`.done out`. -/
theorem not_behavior_of_no_done {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {out : TerminalOut}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_no_done : ∀ s,
      Reach body (mkState 0 0 (initLocalsLoop body args 0 body.locals)) s →
      evalStep (bodyProg body) 0 s ≠ .done out)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    ¬ Behavior (entryProgForBody p defId) { args := args } out := by
  intro h_beh
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState (entryProgForBody p defId) { args := args } with
  | error _ => rw [h_init] at h_beh; cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨_, hs₀⟩ := initState_entryProgForBody_ok h_body h_init
    subst hs₀
    let ⟨s_d, h_reaches, c, hc, h_eval⟩ := h_beh
    subst hc
    let ⟨s, hs, h_reach⟩ :=
      reach_of_reaches_entryProg h_body (isSingleFrame0_mkState 0 0 _)
        h_reaches h_nocall
    subst hs
    have h_f0 := isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach
      h_nocall
    rw [evalStep_retagDefId h_body h_f0 h_nocall] at h_eval
    cases h_st : evalStep (bodyProg body) 0 s with
    | step _ => rw [h_st] at h_eval; cases h_eval
    | fault _ => rw [h_st] at h_eval; cases h_eval
    | done out' =>
      rw [h_st] at h_eval
      injection h_eval with h_out
      subst h_out
      exact h_no_done s h_reach h_st

/-- Constructively establish `Diverges (entryProgForBody p defId)` and absence
of normal `Behavior` from a single-body `ProductiveInvariant` at the entry
state, with zero `Classical.choice` axioms: the infinite trace iterates the
deterministic successor selector `next`. -/
theorem diverges_of_productiveInvariant {p : Program} {defId : DefId}
    {body : Body} {args : List Val} {invariant : State → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args)
    (h_inv : ProductiveInvariant body
      (mkState 0 0 (initLocalsLoop body args 0 body.locals)) invariant)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    Diverges (entryProgForBody p defId) { args := args } ∧
    ∀ out, ¬ Behavior (entryProgForBody p defId) { args := args } out := by
  let next : State → State := fun s =>
    match evalStep (bodyProg body) 0 s with
    | .step s' => s'
    | _ => s
  have hNext : ∀ s s', evalStep (bodyProg body) 0 s = .step s' →
      evalStep (bodyProg body) 0 s = .step (next s) := by
    intro s s' hs
    change evalStep (bodyProg body) 0 s =
      .step (match evalStep (bodyProg body) 0 s with
        | .step s' => s'
        | _ => s)
    rw [hs]
  let iter : Nat → State :=
    Nat.rec (mkState 0 0 (initLocalsLoop body args 0 body.locals))
      (fun _ s => next s)
  have hIter : ∀ n : Nat,
      invariant (iter n) ∧
      Reach body (mkState 0 0 (initLocalsLoop body args 0 body.locals))
        (iter n) ∧
      evalStep (bodyProg body) 0 (iter n) = .step (iter (n + 1)) := by
    intro n
    induction n with
    | zero =>
      let ⟨s', hs'⟩ := h_inv.2.2 _ h_inv.1
      exact ⟨h_inv.1, .refl, hNext _ s' hs'⟩
    | succ n ih =>
      have hNextInv : invariant (iter (n + 1)) := h_inv.2.1 _ _ ih.1 ih.2.2
      let ⟨s'', hs''⟩ := h_inv.2.2 (iter (n + 1)) hNextInv
      exact ⟨hNextInv, .next ih.2.1 ih.2.2, hNext _ s'' hs''⟩
  refine ⟨?_, fun out => not_behavior_of_no_done h_body
    (fun s hReach =>
      (safeFrom_and_no_done_of_productiveInvariant h_inv).2 s out hReach)
    h_nocall⟩
  refine ⟨_, initState_entryProgForBody h_body h_adm h_args,
    fun n => retagDefId defId (iter n), rfl, ?_⟩
  intro n
  refine ⟨0, rfl, ?_⟩
  have hStepN := hIter n
  have hF0 :=
    isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) hStepN.2.1 h_nocall
  rw [evalStep_retagDefId h_body hF0 h_nocall, hStepN.2.2]

/-! ## Part IV: 64-Bit Scalar / Bitwise Assignment Steps and Range Indexing -/

/-- Zero-extended 64-bit scalars satisfy `checkVal` at `(.int .i64 false)`. -/
theorem checkVal_u64_bvZeroExtend (w : BitVec 64) :
    checkVal (.scalar ⟨.i64, false, bvZeroExtend 128 w⟩) (.int .i64 false) =
      true := by
  rw [← truncateBits_i64_bvZeroExtend w]
  exact checkVal_u64_truncateBits (bvZeroExtend 128 w)

/-- Relational predicate asserting that the active frame's `.assign` RHS
evaluates to `out`. -/
@[expose] def EvalAssignVal (body : Body) (s : State) (out : Val) : Prop :=
  match s.frames with
  | [frame] =>
    match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
      | some (.assign dst rvalue) =>
        match Trusted.MirSemantics.getElem? body.locals dst.localId with
        | some dstTy =>
          match evalRvalue body.locals frame.locals s.mem dstTy rvalue with
          | .ok (val, _, _) => val = out
          | .error _ => False
        | none => False
      | _ => False
    | none => False
  | _ => False

/-- Relational predicate asserting that stepping an `.assign` statement to a
`u64` local while overriding the written value with `overrideVal` reaches
`next`. -/
@[expose] def EvalAssignWith (body : Body) (s : State)
    (overrideVal : Val) (next : State) : Prop :=
  match s.frames with
  | [frame] =>
    match frame.sysrootOp? with
    | some _ => False
    | none =>
      match Nat.beq frame.defId 0 with
      | false => False
      | true =>
      match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => False
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some (.assign dst rvalue) =>
          match dst.projection.isEmpty with
          | false => False
          | true =>
            match Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => False
            | some dstTy =>
              match MirTy.beq dstTy (.int .i64 false) with
              | false => False
              | true =>
                match evalRvalue body.locals frame.locals s.mem dstTy rvalue with
                | .error _ => False
                | .ok (_, localsAfterRval, memAfterRval) =>
                  match Trusted.MirSemantics.getElem?
                      localsAfterRval dst.localId with
                  | none => False
                  | some .dead => False
                  | some (.partialTuple _) => False
                  | some (.immediate _) =>
                    match setElem? localsAfterRval dst.localId
                        (.immediate (some overrideVal)) with
                    | some localsAfterWrite =>
                      (.step {
                        frames := [{
                          frame with
                          stmtIdx := frame.stmtIdx + 1
                          locals := localsAfterWrite
                        }]
                        callerMem := s.callerMem
                        mem := memAfterRval
                      } : StepResult State TerminalOut) = .step next
                    | none => False
                  | some (.indirect mplace) =>
                    match storeIndirect memAfterRval (.int .i64 false) mplace
                        overrideVal with
                    | .ok memAfterWrite =>
                      (.step {
                        frames := [{
                          frame with
                          stmtIdx := frame.stmtIdx + 1
                          locals := localsAfterRval
                        }]
                        callerMem := s.callerMem
                        mem := memAfterWrite
                      } : StepResult State TerminalOut) = .step next
                    | .error _ => False
        | _ => False
  | _ => False

private theorem step_eq_evalAssignWith_of_truncate {body : Body}
    {s next : State} {val : Val} {bits : BitVec 128}
    (h_trunc : truncateBits .i64 bits = bits)
    (h_val : EvalAssignVal body s val)
    (h_eq : val = .scalar ⟨.i64, false, bits⟩)
    (h_next : EvalAssignWith body s (.scalar ⟨.i64, false, bits⟩) next) :
    evalStep (bodyProg body) 0 s = .step next := by
  unfold EvalAssignVal at h_val
  unfold EvalAssignWith at h_next
  unfold bodyProg evalStep
  cases h_fr : s.frames with
  | nil => rw [h_fr] at h_next; cases h_next
  | cons frame rest =>
    cases rest with
    | cons _ _ => rw [h_fr] at h_next; cases h_next
    | nil =>
      rw [h_fr] at h_val h_next
      dsimp only at h_val h_next
      dsimp only
      cases h_sys : frame.sysrootOp? with
      | some _ => rw [h_sys] at h_next; cases h_next
      | none =>
        rw [h_sys] at h_next
        dsimp only at h_next
        cases h_def : Nat.beq frame.defId 0 with
        | false => rw [h_def] at h_next; cases h_next
        | true =>
          rw [h_def] at h_next
          dsimp only at h_next
          have h_def0 : frame.defId = 0 := Nat.eq_of_beq_eq_true h_def
          unfold activeFrameBody
          rw [h_sys, h_def0]
          rw [show Trusted.MirSemantics.getElem? [body] 0 = some body from rfl]
          dsimp only
          cases h_bb :
              Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
          | none => rw [h_bb] at h_next; cases h_next
          | some bb =>
            rw [h_bb] at h_val h_next
            dsimp only at h_val h_next
            dsimp only
            cases h_st :
                Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
            | none => rw [h_st] at h_next; cases h_next
            | some stmt =>
              rw [h_st] at h_val h_next
              dsimp only
              cases stmt with
              | nop | storageLive _ | storageDead _ | unsupported =>
                cases h_next
              | assign dst rvalue =>
                dsimp only at h_val h_next
                unfold evalStatement
                dsimp only
                cases h_proj : dst.projection.isEmpty with
                | false => rw [h_proj] at h_next; cases h_next
                | true =>
                  rw [h_proj] at h_next
                  rw [ite_bool_false (rfl : (!true) = false)]
                  dsimp only at h_next
                  cases h_dst :
                      Trusted.MirSemantics.getElem? body.locals dst.localId with
                  | none => rw [h_dst] at h_next; cases h_next
                  | some dstTy =>
                    rw [h_dst] at h_val h_next
                    dsimp only at h_val h_next
                    dsimp only
                    cases h_ty : MirTy.beq dstTy (.int .i64 false) with
                    | false => rw [h_ty] at h_next; cases h_next
                    | true =>
                      rw [h_ty] at h_next
                      dsimp only at h_next
                      have h_ty_eq := MirTy.beq_iff.mp h_ty
                      subst h_ty_eq
                      cases h_rv : evalRvalue body.locals frame.locals s.mem
                          (.int .i64 false) rvalue with
                      | error k => rw [h_rv] at h_val; cases h_val
                      | ok triple =>
                        cases triple with
                        | mk v_rv rest =>
                          cases rest with
                          | mk localsAfterRval memAfterRval =>
                            rw [h_rv] at h_val h_next
                            dsimp only at h_val h_next
                            dsimp only
                            have h_vw : v_rv = .scalar ⟨.i64, false, bits⟩ :=
                              h_val.trans h_eq
                            rw [h_vw]
                            unfold writePlace
                            rw [ite_bool_false (by
                              rw [checkVal_int_iff.mpr ⟨bits, rfl, h_trunc⟩]
                              rfl)]
                            cases h_slot : Trusted.MirSemantics.getElem?
                                localsAfterRval dst.localId with
                            | none => rw [h_slot] at h_next; cases h_next
                            | some slot =>
                              rw [h_slot] at h_next
                              cases slot with
                              | dead => cases h_next
                              | partialTuple _ => cases h_next
                              | immediate _ =>
                                dsimp only at h_next
                                dsimp only
                                cases h_set : setElem? localsAfterRval dst.localId
                                    (.immediate (some (.scalar ⟨.i64, false, bits⟩))) with
                                | none => rw [h_set] at h_next; cases h_next
                                | some localsAfterWrite =>
                                  rw [h_set] at h_next
                                  rw [h_sys]
                                  dsimp only [attachCallers]
                                  exact h_next
                              | indirect mplace =>
                                dsimp only at h_next
                                dsimp only
                                cases h_store : storeIndirect memAfterRval
                                    (.int .i64 false) mplace
                                    (.scalar ⟨.i64, false, bits⟩) with
                                | error k => rw [h_store] at h_next; cases h_next
                                | ok memAfterWrite =>
                                  rw [h_store] at h_next
                                  rw [h_sys]
                                  dsimp only [attachCallers]
                                  exact h_next

/-- Rewrite a symbolic `evalStep` for a `u64` assignment using an equivalent
normalized `BitVec 64` result. -/
theorem step_eq_evalAssignWith {body : Body} {s next : State} {val : Val}
    {w : BitVec 64}
    (h_val : EvalAssignVal body s val)
    (h_eq : val = .scalar ⟨.i64, false, bvZeroExtend 128 w⟩)
    (h_next : EvalAssignWith body s
      (.scalar ⟨.i64, false, bvZeroExtend 128 w⟩) next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate (truncateBits_i64_bvZeroExtend w)
    h_val h_eq h_next

/-- Step an assignment whose RHS evaluates to `BitVec 64` value `x`. -/
theorem step_u64Use {body : Body} {s next : State} (x : BitVec 64)
    (h_val : EvalAssignVal body s
      (.scalar ⟨.i64, false, bvZeroExtend 128 x⟩))
    (h_next : EvalAssignWith body s
      (.scalar ⟨.i64, false, bvZeroExtend 128 x⟩) next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith h_val rfl h_next

/-- Step an assignment whose RHS evaluates to 64-bit bitwise AND of `x` and
`y`. -/
theorem step_u64And {body : Body} {s next : State} (x y : BitVec 64)
    (h_val : EvalAssignVal body s
      (.scalar ⟨.i64, false,
        truncateBits .i64 (bvAnd (truncateBits .i64 (bvZeroExtend 128 x))
          (truncateBits .i64 (bvZeroExtend 128 y)))⟩))
    (h_next : EvalAssignWith body s (u64BitAndVal x y) next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate
    (truncateBits_i64_ofNat_lt
      (Anneal.NatBitwise.land_lt_two_pow x.isLt y.isLt))
    h_val (u64BitAnd_sem_eq x y) h_next

/-- Step an assignment whose RHS evaluates to 64-bit bitwise OR of `x` and
`y`. -/
theorem step_u64Or {body : Body} {s next : State} (x y : BitVec 64)
    (h_val : EvalAssignVal body s
      (.scalar ⟨.i64, false,
        truncateBits .i64 (bvOr (truncateBits .i64 (bvZeroExtend 128 x))
          (truncateBits .i64 (bvZeroExtend 128 y)))⟩))
    (h_next : EvalAssignWith body s (u64BitOrVal x y) next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate
    (truncateBits_i64_ofNat_lt
      (Anneal.NatBitwise.lor_lt_two_pow x.isLt y.isLt))
    h_val (u64BitOr_sem_eq x y) h_next

/-- Step an assignment whose RHS evaluates to 64-bit left shift of `x` by
`k`. -/
theorem step_u64Shl {body : Body} {s next : State} (x : BitVec 64) (k : Nat)
    (h_val : EvalAssignVal body s
      (.scalar ⟨.i64, false,
        truncateBits .i64 (bvOfInt 128
          (.ofNat (Nat.shiftLeft
            (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩))
    (h_next : EvalAssignWith body s (u64ShlVal x k) next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith h_val
    ((u64Shl_sem_eq x k).trans (u64ShlVal_eq x k)) h_next

/-- Step an assignment whose RHS evaluates to 64-bit logical right shift of
`x` by `k`. -/
theorem step_u64Shr {body : Body} {s next : State} (x : BitVec 64) (k : Nat)
    (h_val : EvalAssignVal body s
      (.scalar ⟨.i64, false,
        truncateBits .i64 (bvOfInt 128
          (.ofNat (Nat.shiftRight
            (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩))
    (h_next : EvalAssignWith body s (u64ShrVal x k) next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate
    (truncateBits_i64_ofNat_lt
      (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt))
    h_val (u64Shr_sem_eq x k) h_next

/-- A finite conjunction supplies one checked proposition for each index. -/
@[expose] def CheckRange (n : Nat) : (Nat → Prop) → Prop :=
  Nat.rec (fun _ => True) (fun _ ih p => p 0 ∧ ih (fun i => p (i + 1))) n

/-- Unfold `CheckRange` at `0`. -/
theorem checkRange_zero (p : Nat → Prop) : CheckRange 0 p = True := rfl

/-- Unfold `CheckRange` at `n + 1`. -/
theorem checkRange_succ (n : Nat) (p : Nat → Prop) :
    CheckRange (n + 1) p = (p 0 ∧ CheckRange n (fun i => p (i + 1))) := rfl

/-- Every index `i < n` satisfies `p i` when `CheckRange n p` holds. -/
theorem checkRange_sound (n : Nat) (p : Nat → Prop)
    (checked : CheckRange n p) : ∀ i, i < n → p i := by
  induction n generalizing p with
  | zero =>
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    intro i hi
    cases i with
    | zero => exact checked.1
    | succ i => exact ih _ checked.2 i (Nat.lt_of_succ_lt_succ hi)

/-! ### Flat `entryLocals` Helper (Avoiding Quadratic `initLocalsLoop` Re-Evaluation) -/

/-- Argument-independent local-slot tail for locals beyond `argumentCount`
(`argumentCount + 1 .. body.locals.length - 1`). Compute once for a fixed
`body` (e.g.
`theorem myTail_eq : entryLocalsTail Captured.body_0 = [...] := rfl`) so
symbolic stepping never re-runs `initLocalsLoop` / `hasStorageAnnotation`. -/
@[expose] noncomputable def entryLocalsTail (body : Body) : List LocalSlot :=
  initLocalsLoop body [] (body.argumentCount + 1)
    (body.locals.drop (body.argumentCount + 1))

/-- Flat entry-locals frame built directly from `body.locals[0]`, `args`, and a
pre-evaluated argument-independent `tail` (`entryLocalsTail body`). -/
@[expose] noncomputable def entryLocals (body : Body) (args : List Val)
    (tail : List LocalSlot) : List LocalSlot :=
  match body.locals with
  | [] => []
  | retTy :: _ =>
    liveUninitSlot retTy ::
      (args.map (fun v => LocalSlot.immediate (some v)) ++ tail)

private theorem initLocalsLoop_tail_indep (body : Body) (args : List Val) :
    ∀ (idx : Nat) (tys : List MirTy),
      body.argumentCount < idx →
      initLocalsLoop body args idx tys = initLocalsLoop body [] idx tys
  | _, [], _ => rfl
  | idx, ty :: rest, hGt => by
    unfold initLocalsLoop
    have hNe0 : Nat.beq idx 0 = false := by
      cases idx with
      | zero => exact False.elim (Nat.not_lt_zero _ hGt)
      | succ _ => rfl
    have hBle : Nat.ble idx body.argumentCount = false := by
      cases hb : Nat.ble idx body.argumentCount with
      | false => rfl
      | true =>
        exact False.elim (Nat.not_le_of_gt hGt (Nat.le_of_ble_eq_true hb))
    rw [hNe0, hBle]
    exact congrArg (List.cons _)
      (initLocalsLoop_tail_indep body args (idx + 1) rest
        (Nat.lt_succ_of_lt hGt))

private theorem getElem?_drop_eq {α : Type} :
    ∀ (xs : List α) (k : Nat),
      match xs.drop k with
      | [] => Trusted.MirSemantics.getElem? xs k = none
      | x :: _ => Trusted.MirSemantics.getElem? xs k = some x
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, k + 1 => getElem?_drop_eq xs k

private theorem list_drop_add {α : Type} :
    ∀ (n m : Nat) (xs : List α), (xs.drop n).drop m = xs.drop (n + m)
  | 0, m, xs => by rw [Nat.zero_add]; rfl
  | n + 1, m, [] => by
    rw [Nat.succ_add]
    cases m <;> rfl
  | n + 1, m, _ :: xs => by
    rw [Nat.succ_add]
    exact list_drop_add n m xs

private theorem list_length_drop {α : Type} :
    ∀ (n : Nat) (xs : List α), (xs.drop n).length = xs.length - n
  | 0, xs => by rw [Nat.sub_zero]; rfl
  | n + 1, [] => by
    change ([] : List α).length = 0 - (n + 1)
    rw [Nat.zero_sub]; rfl
  | n + 1, _ :: xs => by
    change (xs.drop n).length = (xs.length + 1) - (n + 1)
    rw [Nat.succ_sub_succ]
    exact list_length_drop n xs

private theorem list_length_take_of_le {α : Type} :
    ∀ (n : Nat) (xs : List α), n ≤ xs.length → (xs.take n).length = n
  | 0, _, _ => rfl
  | _ + 1, [], h => nomatch h
  | n + 1, _ :: xs, h =>
    congrArg Nat.succ (list_length_take_of_le n xs (Nat.le_of_succ_le_succ h))

private theorem initLocalsLoop_cons (body : Body) (args : List Val)
    (idx : Nat) (ty : MirTy) (rest : List MirTy) :
    initLocalsLoop body args idx (ty :: rest) =
      (if Nat.beq idx 0 then
         liveUninitSlot ty
       else if Nat.ble idx body.argumentCount then
         match Trusted.MirSemantics.getElem? args (idx - 1) with
         | some v => .immediate (some v)
         | none => .dead
       else if hasStorageAnnotation body idx then
         .dead
       else
         liveUninitSlot ty) :: initLocalsLoop body args (idx + 1) rest := rfl

private theorem initLocalsLoop_append_args (body : Body) (args : List Val) :
    ∀ (k : Nat) (tys : List MirTy),
      k ≤ body.argumentCount →
      body.argumentCount - k ≤ tys.length →
      args.length = body.argumentCount →
      initLocalsLoop body args (k + 1) tys =
        (args.drop k).map (fun v => LocalSlot.immediate (some v)) ++
          initLocalsLoop body [] (body.argumentCount + 1)
            (tys.drop (body.argumentCount - k))
  | k, tys, hKLe, hRemLe, hLen => by
    induction tys generalizing k with
    | nil =>
      have hEq : body.argumentCount - k = 0 := Nat.eq_zero_of_le_zero hRemLe
      have hKGe : body.argumentCount ≤ k := Nat.le_of_sub_eq_zero hEq
      have hKEq : k = body.argumentCount := Nat.le_antisymm hKLe hKGe
      subst hKEq
      have hDropNil : args.drop body.argumentCount = [] := by
        have hL : (args.drop body.argumentCount).length = 0 := by
          rw [list_length_drop, hLen, Nat.sub_self]
        cases hD : args.drop body.argumentCount with
        | nil => rfl
        | cons _ _ => rw [hD] at hL; nomatch hL
      rw [hDropNil, Nat.sub_self]
      rfl
    | cons ty rest ih =>
      cases Nat.eq_or_lt_of_le hKLe with
      | inl hKEq =>
        subst hKEq
        rw [Nat.sub_self]
        have hDropNil : args.drop body.argumentCount = [] := by
          have hL : (args.drop body.argumentCount).length = 0 := by
            rw [list_length_drop, hLen, Nat.sub_self]
          cases hD : args.drop body.argumentCount with
          | nil => rfl
          | cons _ _ => rw [hD] at hL; nomatch hL
        rw [hDropNil]
        dsimp only [List.map, List.nil_append, List.drop]
        exact initLocalsLoop_tail_indep body args (body.argumentCount + 1)
          (ty :: rest) (Nat.lt_succ_self body.argumentCount)
      | inr hKLt =>
        have hBle : Nat.ble (k + 1) body.argumentCount = true :=
          Nat.ble_eq_true_of_le hKLt
        have hSub : (k + 1) - 1 = k := Nat.add_sub_cancel k 1
        have hKLtArgs : k < args.length := by rw [hLen]; exact hKLt
        have hDrop := getElem?_drop_eq args k
        cases hDr : args.drop k with
        | nil =>
          have hDropLen : (args.drop k).length = args.length - k :=
            list_length_drop k args
          rw [hDr] at hDropLen
          have hPos : 0 < args.length - k := Nat.sub_pos_of_lt hKLtArgs
          rw [← hDropLen] at hPos
          nomatch hPos
        | cons v vs =>
          rw [hDr] at hDrop
          have hStepLhs :
              initLocalsLoop body args (k + 1) (ty :: rest) =
                LocalSlot.immediate (some v) ::
                  initLocalsLoop body args (k + 1 + 1) rest := by
            rw [initLocalsLoop_cons, hBle, hSub, hDrop]
            rfl
          rw [hStepLhs]
          dsimp only [List.map, List.cons_append]
          apply congrArg (List.cons (LocalSlot.immediate (some v)))
          have hRemPos : 0 < body.argumentCount - k := Nat.sub_pos_of_lt hKLt
          have hRemEq : body.argumentCount - k = (body.argumentCount - (k + 1)) + 1 := by
            rw [Nat.sub_succ]
            exact (Nat.sub_add_cancel hRemPos).symm
          have hRemLeRest : body.argumentCount - (k + 1) ≤ rest.length := by
            rw [hRemEq] at hRemLe
            exact Nat.le_of_succ_le_succ hRemLe
          have hDropStep : (ty :: rest).drop (body.argumentCount - k) =
              rest.drop (body.argumentCount - (k + 1)) := by
            rw [hRemEq]; rfl
          have hArgsDropSucc : args.drop (k + 1) = vs := by
            have h1 := list_drop_add k 1 args
            rw [hDr] at h1
            exact h1.symm
          rw [hDropStep, ← hArgsDropSucc]
          exact ih (k + 1) hKLt hRemLeRest

/-- Rewrites `initLocalsLoop body args 0 body.locals` into the flat
`entryLocals body args tail` list using a one-time proof
`hTail : entryLocalsTail body = tail`, avoiding repeated O(|locals|·|stmts|)
`hasStorageAnnotation` scanning during symbolic proofs (`#4292`). -/
theorem initLocalsLoop_eq_entryLocals {body : Body} {args : List Val}
    {tail : List LocalSlot}
    (hValid : ValidEntryArgs body args)
    (hArgLt : body.argumentCount < body.locals.length)
    (hTail : entryLocalsTail body = tail) :
    initLocalsLoop body args 0 body.locals = entryLocals body args tail := by
  have hArgsLen : args.length = body.argumentCount := by
    have hL := checkArgsMatch_length hValid
    have hLe : body.argumentCount ≤ (body.locals.drop 1).length := by
      rw [list_length_drop 1 body.locals]
      exact Nat.le_pred_of_lt hArgLt
    rw [list_length_take_of_le _ _ hLe] at hL
    exact hL
  cases hLocs : body.locals with
  | nil =>
    rw [hLocs] at hArgLt
    nomatch hArgLt
  | cons retTy rest =>
    dsimp only [entryLocals]
    rw [hLocs]
    unfold initLocalsLoop
    dsimp only
    apply congrArg (List.cons (liveUninitSlot retTy))
    have hRemLe : body.argumentCount - 0 ≤ rest.length := by
      rw [hLocs] at hArgLt
      rw [Nat.sub_zero]
      exact Nat.le_of_lt_succ hArgLt
    have hApp := initLocalsLoop_append_args body args 0 rest
      (Nat.zero_le _) hRemLe hArgsLen
    have hDropRest : rest.drop (body.argumentCount - 0) =
        body.locals.drop (body.argumentCount + 1) := by
      rw [hLocs, Nat.sub_zero]; rfl
    rw [hDropRest] at hApp
    dsimp only [List.drop] at hApp
    rw [hApp, ← hTail]
    rfl

/-- Establish `Safe body args` from `SafeFrom` on a pre-flattened entry-locals
frame `locals0` (`hLoc : initLocalsLoop body args 0 body.locals = locals0`). -/
theorem safe_of_entryLocals {body : Body} {args : List Val}
    {locals0 : List LocalSlot}
    (hLoc : initLocalsLoop body args 0 body.locals = locals0)
    (hSafe : SafeFrom body (mkState 0 0 locals0)) :
    Safe body args := by
  unfold Safe
  rw [hLoc]
  exact hSafe

/-- Establish `Returns body args out` from `ReturnsFrom` on a pre-flattened
entry-locals frame `locals0`. -/
theorem returns_of_entryLocals {body : Body} {args : List Val}
    {locals0 : List LocalSlot} {out : Val}
    (hLoc : initLocalsLoop body args 0 body.locals = locals0)
    (hRet : ReturnsFrom body (mkState 0 0 locals0) out) :
    Returns body args out := by
  unfold Returns
  rw [hLoc]
  exact hRet

/-- Establish `Safe body args ∧ Returns body args out` from `Executes` on a
pre-flattened entry-locals frame `locals0`. -/
theorem executes_of_entryLocals {body : Body} {args : List Val}
    {locals0 : List LocalSlot} {out : Val}
    (hLoc : initLocalsLoop body args 0 body.locals = locals0)
    (hExec : Executes body (mkState 0 0 locals0) out) :
    Safe body args ∧ Returns body args out :=
  ⟨safe_of_entryLocals hLoc (executes_safe hExec),
   returns_of_entryLocals hLoc (executes_returns hExec)⟩

end Anneal.MirWp

end
