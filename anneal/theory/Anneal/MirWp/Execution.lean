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

open Trusted.MirAst Trusted.MirSemantics

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
@[expose] def bodyProg (body : Body) (endian : TargetEndian := .little) : Program :=
  { scope := .unit, pointerWidthBits := 64, targetEndian := endian,
    mirProfileVersion := 1, bodies := [body] }

/-- Finite-step reachability in `body` under
`evalStep (bodyProg body endian) 0`. -/
inductive Reach (endian : TargetEndian) (body : Body) :
    State → State → Prop where
  | refl {state : State} : Reach endian body state state
  | next {start mid next : State} :
      Reach endian body start mid →
      evalStep (bodyProg body endian) 0 mid = .step next →
      Reach endian body start next

/-- Prefix fault-freedom of `body` starting from `start`. -/
@[expose] def SafeFrom (endian : TargetEndian) (body : Body) (start : State) : Prop :=
  ∀ state kind, Reach endian body start state →
    evalStep (bodyProg body endian) 0 state ≠ .fault kind

/-- Prefix fault-freedom of `body` from its entry state on `args`. -/
@[expose] def Safe (endian : TargetEndian) (body : Body) (args : List Val) : Prop :=
  SafeFrom endian body (mkState 0 0 (initLocalsLoop body args 0 body.locals))

/-- Normal return of `output` from `start` in `body`. -/
@[expose] def ReturnsFrom (endian : TargetEndian) (body : Body) (start : State)
    (output : Val) : Prop :=
  ∃ state, Reach endian body start state ∧
    evalStep (bodyProg body endian) 0 state = .done (.returned ⟨output, ⟨[]⟩⟩)

/-- Normal return of `output` from the entry state of `body` on `args`. -/
@[expose] def Returns (endian : TargetEndian) (body : Body) (args : List Val)
    (output : Val) : Prop :=
  ReturnsFrom endian body
    (mkState 0 0 (initLocalsLoop body args 0 body.locals)) output

/-- Fuel-bounded run certificate: from `start`, `body` returns `output` within
`fuel` steps and never faults. It is the deterministic `c = 0` execution
predicate of `bodyProg body endian` with an exact return postcondition, so a
concrete run reduces by `rfl`. -/
abbrev RunsFrom (endian : TargetEndian) (body : Body) (fuel : Nat)
    (start : State) (output : Val) : Prop :=
  execState (bodyProg body endian) fuel start
    (fun out => out = .returned ⟨output, ⟨[]⟩⟩)

/-- Fuel-bounded run certificate from the entry state of `body` on `args`. -/
abbrev Runs (endian : TargetEndian) (body : Body) (fuel : Nat)
    (args : List Val) (output : Val) : Prop :=
  RunsFrom endian body fuel
    (mkState 0 0 (initLocalsLoop body args 0 body.locals)) output

/-- Step-by-step normal-return certificate for `body`. Each constructor records
one rewritten transition, so long symbolic runs never accumulate an unnormalized
`whnf` term. -/
inductive Executes (endian : TargetEndian) (body : Body) :
    State → Val → Prop where
  | ret {start : State} {value : Val} :
      evalStep (bodyProg body endian) 0 start = .done (.returned ⟨value, ⟨[]⟩⟩) →
      Executes endian body start value
  | next {start next : State} {value : Val} :
      evalStep (bodyProg body endian) 0 start = .step next →
      Executes endian body next value →
      Executes endian body start value

/-- Exact equivalence between program-level `Reaches (bodyProg body endian)` and
single-body `Reach endian body`. -/
theorem reaches_bodyProg_iff_reach {endian : TargetEndian} {body : Body}
    {s₁ s₂ : State} :
    Reaches (bodyProg body endian) s₁ s₂ ↔ Reach endian body s₁ s₂ := by
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
theorem reach_prepend {endian : TargetEndian} {body : Body}
    {start next finish : State}
    (first : evalStep (bodyProg body endian) 0 start = .step next)
    (rest : Reach endian body next finish) :
    Reach endian body start finish :=
  reaches_bodyProg_iff_reach.mp
    (Reaches.head ⟨0, rfl, first⟩ (reaches_bodyProg_iff_reach.mpr rest))

/-- Case-split a `Reach` chain whose start state steps to `next`. -/
theorem reach_cases {endian : TargetEndian} {body : Body}
    {start next finish : State}
    (first : evalStep (bodyProg body endian) 0 start = .step next)
    (reached : Reach endian body start finish) :
    finish = start ∨ Reach endian body next finish := by
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
theorem reachable_after_return {endian : TargetEndian} {body : Body}
    {start finish : State} {value : Val}
    (returned :
      evalStep (bodyProg body endian) 0 start = .done (.returned ⟨value, ⟨[]⟩⟩))
    (reached : Reach endian body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    rw [returned] at transition
    cases transition

/-- No further states are reachable after a `.fault` step. -/
theorem reachable_after_fault {endian : TargetEndian} {body : Body}
    {start finish : State} {reason : FaultKind}
    (faulted : evalStep (bodyProg body endian) 0 start = .fault reason)
    (reached : Reach endian body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    rw [faulted] at transition
    cases transition

/-- A state that immediately returns is prefix-safe (`SafeFrom`). -/
theorem safeFrom_return {endian : TargetEndian} {body : Body}
    {start : State} {value : Val}
    (returned :
      evalStep (bodyProg body endian) 0 start = .done (.returned ⟨value, ⟨[]⟩⟩)) :
    SafeFrom endian body start := by
  intro finish reason reached
  have same := reachable_after_return returned reached
  subst finish
  rw [returned]
  intro h
  cases h

/-- Prefix safety steps backward across a deterministic `.step` transition. -/
theorem safeFrom_next {endian : TargetEndian} {body : Body}
    {start next : State}
    (first : evalStep (bodyProg body endian) 0 start = .step next)
    (rest : SafeFrom endian body next) :
    SafeFrom endian body start := by
  intro finish reason reached
  cases reach_cases first reached with
  | inl equal =>
    subst finish
    rw [first]
    intro h
    cases h
  | inr tail => exact rest finish reason tail

/-- Prefix safety composes backward across any finite `Reach` prefix. -/
theorem safeFrom_of_reach {endian : TargetEndian} {body : Body}
    {start checkpoint : State}
    (segment : Reach endian body start checkpoint)
    (suffix : SafeFrom endian body checkpoint) :
    SafeFrom endian body start := by
  induction segment with
  | refl => exact suffix
  | next _ transition ih => exact ih (safeFrom_next transition suffix)

/-- Bridge from fuel-bounded `wpState (bodyProg body)` to `SafeFrom`: holds even
when symbolic branches return distinct values. -/
theorem safeFrom_of_wpState {endian : TargetEndian} {body : Body} {fuel : Nat}
    {start : State} {post : TerminalOut → Prop}
    (hWp : wpState (bodyProg body endian) fuel start post) :
    SafeFrom endian body start := by
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
theorem executes_iff_wpState {endian : TargetEndian} {body : Body}
    {start : State} {value : Val} :
    Executes endian body start value ↔
      ∃ fuel, RunsFrom endian body fuel start value := by
  constructor
  · intro execution
    induction execution with
    | @ret s val hRet =>
      refine ⟨1, ?_⟩
      change (match evalStep (bodyProg body endian) 0 s with
        | .step st' => False
        | .done out => out = .returned ⟨val, ⟨[]⟩⟩
        | .fault _ => False)
      rw [hRet]
    | @next s next val hStep _ ih =>
      let ⟨fuel, hExec⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      change (match evalStep (bodyProg body endian) 0 s with
        | .step st' =>
          execState (bodyProg body endian) fuel st'
            (fun out => out = .returned ⟨val, ⟨[]⟩⟩)
        | .done out => out = .returned ⟨val, ⟨[]⟩⟩
        | .fault _ => False)
      rw [hStep]
      exact hExec
  · intro hEx
    cases hEx with
    | intro fuel hExec =>
      induction fuel generalizing start with
      | zero => exact False.elim hExec
      | succ fuel ih =>
        change (match evalStep (bodyProg body endian) 0 start with
          | .step st' =>
            execState (bodyProg body endian) fuel st'
              (fun out => out = .returned ⟨value, ⟨[]⟩⟩)
          | .done out => out = .returned ⟨value, ⟨[]⟩⟩
          | .fault _ => False) at hExec
        cases hStep : evalStep (bodyProg body endian) 0 start with
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
theorem executes_prepend {endian : TargetEndian} {body : Body}
    {start checkpoint : State} {value : Val}
    (segment : Reach endian body start checkpoint)
    (suffix : Executes endian body checkpoint value) :
    Executes endian body start value := by
  induction segment with
  | refl => exact suffix
  | next _ transition ih => exact ih (.next transition suffix)

/-- Every `Executes` certificate establishes `SafeFrom` (derived directly from
`executes_iff_wpState` and `safeFrom_of_wpState`). -/
theorem executes_safe {endian : TargetEndian} {body : Body}
    {start : State} {value : Val}
    (execution : Executes endian body start value) :
    SafeFrom endian body start :=
  let ⟨_, hExec⟩ := executes_iff_wpState.mp execution
  safeFrom_of_wpState (wpOutcomeState_of_execOutcomeState hExec)

/-- Every `Executes` certificate establishes `ReturnsFrom` (derived directly
from `executes_iff_wpState` and `exists_terminal_of_wpOutcomeState`). -/
theorem executes_returns {endian : TargetEndian} {body : Body}
    {start : State} {value : Val}
    (execution : Executes endian body start value) :
    ReturnsFrom endian body start value := by
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
theorem executes_unique {endian : TargetEndian} {body : Body}
    {start : State} {left right : Val}
    (execution : Executes endian body start left)
    (returned : ReturnsFrom endian body start right) :
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
theorem run_executes {endian : TargetEndian} {body : Body} {fuel : Nat}
    {start : State} {value : Val}
    (success : RunsFrom endian body fuel start value) :
    Executes endian body start value :=
  executes_iff_wpState.mpr ⟨fuel, success⟩

/-- A run certificate establishes prefix safety and normal return. -/
theorem run_success {endian : TargetEndian} {body : Body} {fuel : Nat}
    {start : State} {value : Val}
    (success : RunsFrom endian body fuel start value) :
    SafeFrom endian body start ∧ ReturnsFrom endian body start value :=
  ⟨executes_safe (run_executes success),
    executes_returns (run_executes success)⟩

/-- A run certificate from the entry state establishes `Safe` and `Returns`. -/
theorem run_initial_success {endian : TargetEndian} {body : Body} {fuel : Nat}
    {args : List Val} {value : Val} (success : Runs endian body fuel args value) :
    Safe endian body args ∧ Returns endian body args value :=
  run_success success

/-- A run certificate determines the only value that `body` can return. -/
theorem run_result_unique {endian : TargetEndian} {body : Body} {fuel : Nat}
    {start : State} {left right : Val}
    (success : RunsFrom endian body fuel start left)
    (returned : ReturnsFrom endian body start right) :
    left = right :=
  executes_unique (run_executes success) returned

/-- Inductive preservation of `invariant` across all `Reach` states. -/
theorem invariant_reachable {endian : TargetEndian} {body : Body}
    {start finish : State}
    (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before →
      evalStep (bodyProg body endian) 0 before = .step after → invariant after)
    (reached : Reach endian body start finish) :
    invariant finish := by
  induction reached with
  | refl => exact entry
  | next _ transition ih => exact closed _ _ ih transition

/-- Inductive invariant rule for `SafeFrom` (supporting non-terminating loops).
-/
theorem safeFrom_invariant {endian : TargetEndian} {body : Body} {start : State}
    (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before →
      evalStep (bodyProg body endian) 0 before = .step after → invariant after)
    (noFault : ∀ state, invariant state → ∀ reason,
      evalStep (bodyProg body endian) 0 state ≠ .fault reason) :
    SafeFrom endian body start := by
  intro finish reason reached
  have preserved := invariant_reachable invariant entry closed reached
  exact noFault finish preserved reason

/-- A state self-loop reaches only itself. -/
theorem reachable_selfLoop {endian : TargetEndian} {body : Body}
    {start finish : State}
    (loop : evalStep (bodyProg body endian) 0 start = .step start)
    (reached : Reach endian body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    have equal := loop.symm.trans transition
    injection equal with h_eq
    exact h_eq.symm

/-- Any immediate self-loop is prefix-safe. -/
theorem safeFrom_selfLoop {endian : TargetEndian} {body : Body} {start : State}
    (loop : evalStep (bodyProg body endian) 0 start = .step start) :
    SafeFrom endian body start := by
  intro finish reason reached
  have same := reachable_selfLoop loop reached
  subst finish
  rw [loop]
  intro h
  cases h

/-- A productive state invariant holds at `start`, is closed under `.step`, and
ensures every invariant state takes a `.step` transition (ruling out both
`.fault` and `.done` simultaneously). -/
@[expose] def ProductiveInvariant (endian : TargetEndian) (body : Body) (start : State)
    (invariant : State → Prop) : Prop :=
  invariant start ∧
  (∀ before after, invariant before →
    evalStep (bodyProg body endian) 0 before = .step after → invariant after) ∧
  (∀ state, invariant state →
    ∃ next, evalStep (bodyProg body endian) 0 state = .step next)

/-- Every `ProductiveInvariant` simultaneously establishes `SafeFrom` and
absence of normal `.done` termination from `start`. -/
theorem safeFrom_and_no_done_of_productiveInvariant
    {endian : TargetEndian} {body : Body} {start : State}
    {invariant : State → Prop}
    (hInv : ProductiveInvariant endian body start invariant) :
    SafeFrom endian body start ∧
    ∀ s out, Reach endian body start s →
      evalStep (bodyProg body endian) 0 s ≠ .done out := by
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
theorem evalStatement_frame_retag {endian : TargetEndian} (body : Body)
    (defId : DefId) (f : FrameState) (m : MemoryState) (cm : CallerMemory)
    (stmt : StatementKind) (h_id : f.defId = 0) :
    (∀ s', evalStatement endian body f m cm stmt = .step s' →
      IsSingleFrame0 s') ∧
    evalStatement endian body { f with defId := defId } m cm stmt =
      match evalStatement endian body f m cm stmt with
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
        cases evalRvalue endian body.locals f.locals m dstTy rv with
        | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
        | ok triple =>
          cases triple with
          | mk v rest =>
            cases rest with
            | mk l₁ m₁ =>
              dsimp only
              cases writePlace endian l₁ m₁ dst.localId dstTy v with
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
theorem evalTerminator_frame_retag {endian : TargetEndian} (body : Body)
    (bb : BasicBlock) (defId : DefId) (f : FrameState) (m : MemoryState)
    (cm : CallerMemory) (h_id : f.defId = 0) :
    (∀ s', evalTerminator endian body bb f m cm = .step s' →
      IsSingleFrame0 s') ∧
    evalTerminator endian body bb { f with defId := defId } m cm =
      match evalTerminator endian body bb f m cm with
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
        | immediate opt =>
          cases opt <;> exact ⟨(fun _ h => by cases h), rfl⟩
        | indirect place =>
          dsimp only
          cases Trusted.MirSemantics.getElem? body.locals 0 with
          | none => exact ⟨(fun _ h => by cases h), rfl⟩
          | some retTy =>
            dsimp only
            cases loadIndirect endian m retTy place with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok opt =>
              cases opt <;> exact ⟨(fun _ h => by cases h), rfl⟩
  | unreachable => exact ⟨(fun _ h => by cases h), rfl⟩
  | switchInt discr targets =>
    dsimp only
    cases evalPrimitiveOperand endian body.locals f.locals m discr with
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
          | ptr _ | ordering _ | unit | tuple _ | bytes _ | enumVal _ _ =>
            dsimp only
            cases targets.branches with
            | nil =>
              refine ⟨?_, rfl⟩
              intro s' hStep
              injection hStep with hEq; subst hEq
              exact ⟨_, rfl, h_id⟩
            | cons _ _ => exact ⟨(fun _ h => by cases h), rfl⟩
  | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    exact ⟨(fun _ h => by cases h), rfl⟩

/-- Combined single-step `IsSingleFrame0` preservation and `retagDefId`
simulation between `evalStep (bodyProg body) 0` and
`evalStep (entryProgForBody p defId) 0`. -/
theorem evalStep_entryProg_frame {p : Program} {defId : DefId} {body : Body}
    {s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_f0 : IsSingleFrame0 s) :
    (∀ s', evalStep (bodyProg body p.targetEndian) 0 s = .step s' →
      IsSingleFrame0 s') ∧
    evalStep (entryProgForBody p defId) 0 (retagDefId defId s) =
      match evalStep (bodyProg body p.targetEndian) 0 s with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  let ⟨f, hf, h_id⟩ := h_f0
  cases s with
  | mk frames cm mem =>
    dsimp only at hf
    subst hf
    unfold bodyProg evalStep retagDefId entryProgForBody
    dsimp only
    rw [h_body, h_id]
    dsimp only [Trusted.MirSemantics.getElem?]
    cases Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx with
    | none => exact ⟨(fun _ h => by cases h), rfl⟩
    | some bb =>
      dsimp only
      cases Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
      | some stmt =>
        exact evalStatement_frame_retag body defId f mem cm stmt h_id
      | none =>
        dsimp only
        cases Nat.beq f.stmtIdx bb.statements.length with
        | false => exact ⟨(fun _ h => by cases h), rfl⟩
        | true =>
          exact evalTerminator_frame_retag body bb defId f mem cm h_id

/-- `IsSingleFrame0` is preserved by a single-body step. -/
theorem isSingleFrame0_of_step {endian : TargetEndian} {body : Body}
    {s s' : State}
    (h_f0 : IsSingleFrame0 s)
    (h_step : evalStep (bodyProg body endian) 0 s = .step s') :
    IsSingleFrame0 s' :=
  (evalStep_entryProg_frame (p := bodyProg body endian) (defId := 0) rfl h_f0).1
    s' h_step

/-- Every state reachable from a single-frame `defId = 0` state is again a
single frame at `defId = 0`. -/
theorem isSingleFrame0_of_reach {endian : TargetEndian} {body : Body}
    {start s : State}
    (h_start : IsSingleFrame0 start)
    (h_reach : Reach endian body start s) :
    IsSingleFrame0 s := by
  induction h_reach with
  | refl => exact h_start
  | next _ h_step ih => exact isSingleFrame0_of_step ih h_step

/-- `evalStep (entryProgForBody p defId) 0` commutes with `retagDefId defId` on
single-frame `defId = 0` states. -/
theorem evalStep_retagDefId {p : Program} {defId : DefId} {body : Body}
    {s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_f0 : IsSingleFrame0 s) :
    evalStep (entryProgForBody p defId) 0 (retagDefId defId s) =
      match evalStep (bodyProg body p.targetEndian) 0 s with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k :=
  (evalStep_entryProg_frame h_body h_f0).2

/-- Exact equivalence of `execOutcomeState` across `retagDefId` between
`entryProgForBody p defId` and `bodyProg body p.targetEndian`. -/
theorem execOutcomeState_entryProg_iff {p : Program} {defId : DefId}
    {body : Body} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body) :
    ∀ {fuel : Nat} {s : State},
      IsSingleFrame0 s →
      (execOutcomeState (entryProgForBody p defId) onDone onFault fuel
        (retagDefId defId s) ↔
       execOutcomeState (bodyProg body p.targetEndian) onDone onFault fuel s)
  | 0, _, _ => Iff.rfl
  | fuel + 1, s, h_f0 => by
    have hFrame := evalStep_entryProg_frame h_body h_f0
    change (match evalStep (entryProgForBody p defId) 0
          (retagDefId defId s) with
        | .step st' =>
          execOutcomeState (entryProgForBody p defId) onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k) ↔
      (match evalStep (bodyProg body p.targetEndian) 0 s with
        | .step st' =>
          execOutcomeState (bodyProg body p.targetEndian) onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k)
    rw [hFrame.2]
    cases hSt : evalStep (bodyProg body p.targetEndian) 0 s with
    | step next =>
      exact execOutcomeState_entryProg_iff h_body (hFrame.1 next hSt)
    | done out => exact Iff.rfl
    | fault k => exact Iff.rfl

/-- Exact equivalence of `wpOutcomeState` across `retagDefId` between
`entryProgForBody p defId` and `bodyProg body p.targetEndian`. -/
theorem wpOutcomeState_entryProg_iff {p : Program} {defId : DefId}
    {body : Body} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    {fuel : Nat} {s : State} (h_f0 : IsSingleFrame0 s) :
    wpOutcomeState (entryProgForBody p defId) onDone onFault fuel
      (retagDefId defId s) ↔
    wpOutcomeState (bodyProg body p.targetEndian) onDone onFault fuel s :=
  wpOutcomeState_iff_execOutcomeState.trans
    ((execOutcomeState_entryProg_iff h_body h_f0).trans
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
      Reaches (entryProgForBody p defId) (retagDefId defId start) s_d) :
    ∃ s : State, s_d = retagDefId defId s ∧ Reach p.targetEndian body start s := by
  induction h_reaches with
  | refl => exact ⟨start, rfl, .refl⟩
  | tail _ h_step ih =>
    let ⟨s, hs, h_reach_s⟩ := ih
    let ⟨c, hc, h_eval⟩ := h_step
    subst hc
    subst hs
    have h_f0 := isSingleFrame0_of_reach h_start h_reach_s
    rw [evalStep_retagDefId h_body h_f0] at h_eval
    cases h_st : evalStep (bodyProg body p.targetEndian) 0 s with
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
    (h_reach : Reach p.targetEndian body start s) :
    Reaches (entryProgForBody p defId) (retagDefId defId start)
      (retagDefId defId s) := by
  induction h_reach with
  | refl => exact .refl _
  | next h_prev h_st ih =>
    have h_f0 := isSingleFrame0_of_reach h_start h_prev
    refine .tail ih ⟨0, rfl, ?_⟩
    rw [evalStep_retagDefId h_body h_f0, h_st]

/-- Establish per-invocation `WellFormed (entryProgForBody p defId)` from
single-body `Safe p.targetEndian body args`. -/
theorem wellFormed_entryProg_of_safe {p : Program} {defId : DefId}
    {body : Body} {args : List Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args)
    (h_safe : Safe p.targetEndian body args) :
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
        h_reaches
    subst hs
    have h_f0 :=
      isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach_s
    rw [evalStep_retagDefId h_body h_f0] at h_eval
    cases h_st : evalStep (bodyProg body p.targetEndian) 0 s with
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
      Safe p.targetEndian body args) :
    BodyVerified p defId body safetyPre :=
  ⟨h_body, h_adm, fun args h_args h_req =>
    wellFormed_entryProg_of_safe h_body h_adm h_args (h_safe args h_args h_req)⟩

/-- Establish `Behavior (entryProgForBody p defId)` from single-body `Returns`.
-/
theorem behavior_of_returns {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args)
    (h_ret : Returns p.targetEndian body args ret) :
    Behavior (entryProgForBody p defId) { args := args }
      (.returned ⟨ret, ⟨[]⟩⟩) := by
  let ⟨s, h_reach, h_done⟩ := h_ret
  unfold Behavior ReachesResult
  rw [initState_entryProgForBody h_body h_adm h_args]
  refine ⟨retagDefId defId s,
    reaches_entryProg_of_reach h_body (isSingleFrame0_mkState 0 0 _) h_reach,
    0, rfl, ?_⟩
  have h_f0 := isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach
  rw [evalStep_retagDefId h_body h_f0, h_done]

/-- Invert `initState (entryProgForBody p defId) { args := args } = .ok s₀` into
`ValidEntryArgs body args` and the retagged entry state of `body` on `args`. -/
theorem initState_entryProgForBody_ok {p : Program} {defId : DefId}
    {body : Body} {args : List Val} {s₀ : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_init : initState (entryProgForBody p defId) { args := args } = .ok s₀) :
    ValidEntryArgs body args ∧
      s₀ = retagDefId defId
        (mkState 0 0 (initLocalsLoop body args 0 body.locals)) := by
  unfold initState entryProgForBody at h_init
  unfold ValidEntryArgs mkState retagDefId
  dsimp only at h_init
  dsimp only
  rw [h_body] at h_init
  dsimp only at h_init
  cases h1 : Nat.beq p.pointerWidthBits 64 <;>
    cases h2 : Nat.beq p.mirProfileVersion 1 <;>
    cases h3 : body.basicBlocks.isEmpty <;>
    cases h4 : Nat.blt body.argumentCount body.locals.length <;>
    cases h5 : storageAnnotationsInBounds body <;>
    cases h5d : discriminantTypesValid body <;>
    cases h5c : castTypesValid body <;>
    cases h6 : body.locals.all isSupportedScalarOrUnitTy <;>
    cases h7 : checkArgsMatch args
      ((body.locals.drop 1).take body.argumentCount) <;>
    rw [h1, h2, h3, h4, h5, h5d, h5c, h6, h7] at h_init <;>
    cases h_init
  exact ⟨rfl, rfl⟩

/-- Invert `Behavior (entryProgForBody p defId)` into `ValidEntryArgs` and
single-body `Returns`. -/
theorem returns_of_behavior {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_beh : Behavior (entryProgForBody p defId) { args := args }
      (.returned ⟨ret, ⟨[]⟩⟩)) :
    ValidEntryArgs body args ∧ Returns p.targetEndian body args ret := by
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
        h_reaches
    subst hs
    have h_f0 := isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach
    rw [evalStep_retagDefId h_body h_f0] at h_eval
    cases h_st : evalStep (bodyProg body p.targetEndian) 0 s with
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
      Reach p.targetEndian body
        (mkState 0 0 (initLocalsLoop body args 0 body.locals)) s →
      evalStep (bodyProg body p.targetEndian) 0 s ≠ .done out) :
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
        h_reaches
    subst hs
    have h_f0 := isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach
    rw [evalStep_retagDefId h_body h_f0] at h_eval
    cases h_st : evalStep (bodyProg body p.targetEndian) 0 s with
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
    (h_inv : ProductiveInvariant p.targetEndian body
      (mkState 0 0 (initLocalsLoop body args 0 body.locals)) invariant) :
    Diverges (entryProgForBody p defId) { args := args } ∧
    ∀ out, ¬ Behavior (entryProgForBody p defId) { args := args } out := by
  let next : State → State := fun s =>
    match evalStep (bodyProg body p.targetEndian) 0 s with
    | .step s' => s'
    | _ => s
  have hNext : ∀ s s',
      evalStep (bodyProg body p.targetEndian) 0 s = .step s' →
      evalStep (bodyProg body p.targetEndian) 0 s = .step (next s) := by
    intro s s' hs
    change evalStep (bodyProg body p.targetEndian) 0 s =
      .step (match evalStep (bodyProg body p.targetEndian) 0 s with
        | .step s' => s'
        | _ => s)
    rw [hs]
  let iter : Nat → State :=
    Nat.rec (mkState 0 0 (initLocalsLoop body args 0 body.locals))
      (fun _ s => next s)
  have hIter : ∀ n : Nat,
      invariant (iter n) ∧
      Reach p.targetEndian body
        (mkState 0 0 (initLocalsLoop body args 0 body.locals)) (iter n) ∧
      evalStep (bodyProg body p.targetEndian) 0 (iter n) =
        .step (iter (n + 1)) := by
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
      (safeFrom_and_no_done_of_productiveInvariant h_inv).2 s out hReach)⟩
  refine ⟨_, initState_entryProgForBody h_body h_adm h_args,
    fun n => retagDefId defId (iter n), rfl, ?_⟩
  intro n
  refine ⟨0, rfl, ?_⟩
  have hStepN := hIter n
  have hF0 :=
    isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) hStepN.2.1
  rw [evalStep_retagDefId h_body hF0, hStepN.2.2]

/-! ## Part IV: 64-Bit Scalar / Bitwise Assignment Steps and Range Indexing -/

/-- Zero-extended 64-bit scalars satisfy `checkVal` at `(.int .i64 false)`. -/
theorem checkVal_u64_bvZeroExtend (w : BitVec 64) :
    checkVal (.scalar ⟨.i64, false, bvZeroExtend 128 w⟩) (.int .i64 false) =
      true := by
  rw [← truncateBits_i64_bvZeroExtend w]
  exact checkVal_u64_truncateBits (bvZeroExtend 128 w)

/-- Relational predicate asserting that the active frame's `.assign` RHS
evaluates to `out`. -/
@[expose] def EvalAssignVal (endian : TargetEndian) (body : Body) (s : State)
    (out : Val) : Prop :=
  match s.frames with
  | [frame] =>
    match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
      | some (.assign dst rvalue) =>
        match Trusted.MirSemantics.getElem? body.locals dst.localId with
        | some dstTy =>
          match evalRvalue endian body.locals frame.locals s.mem dstTy rvalue with
          | .ok (val, _, _) => val = out
          | .error _ => False
        | none => False
      | _ => False
    | none => False
  | _ => False

/-- Relational predicate asserting that stepping an `.assign` statement to a
`u64` local while overriding the written value with `overrideVal` reaches
`next`. -/
@[expose] def EvalAssignWith (endian : TargetEndian) (body : Body) (s : State)
    (overrideVal : Val) (next : State) : Prop :=
  match s.frames with
  | [frame] =>
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
                match evalRvalue endian body.locals frame.locals s.mem dstTy
                    rvalue with
                | .error _ => False
                | .ok (_, localsAfterRval, memAfterRval) =>
                  match Trusted.MirSemantics.getElem?
                      localsAfterRval dst.localId with
                  | none => False
                  | some .dead => False
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
                    match storeIndirect endian memAfterRval (.int .i64 false)
                        mplace overrideVal with
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

private theorem step_eq_evalAssignWith_of_truncate {endian : TargetEndian}
    {body : Body} {s next : State} {val : Val} {bits : BitVec 128}
    (h_trunc : truncateBits .i64 bits = bits)
    (h_val : EvalAssignVal endian body s val)
    (h_eq : val = .scalar ⟨.i64, false, bits⟩)
    (h_next : EvalAssignWith endian body s (.scalar ⟨.i64, false, bits⟩)
      next) :
    evalStep (bodyProg body endian) 0 s = .step next := by
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
      cases h_def : Nat.beq frame.defId 0 with
      | false => rw [h_def] at h_next; cases h_next
      | true =>
        rw [h_def] at h_next
        dsimp only at h_next
        have h_def0 : frame.defId = 0 := Nat.eq_of_beq_eq_true h_def
        rw [h_def0]
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
                    cases h_rv : evalRvalue endian body.locals frame.locals s.mem
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
                            | immediate _ =>
                              dsimp only at h_next
                              dsimp only
                              cases h_set : setElem? localsAfterRval dst.localId
                                  (.immediate (some (.scalar ⟨.i64, false, bits⟩))) with
                              | none => rw [h_set] at h_next; cases h_next
                              | some localsAfterWrite =>
                                rw [h_set] at h_next
                                exact h_next
                            | indirect mplace =>
                              dsimp only at h_next
                              dsimp only
                              cases h_store : storeIndirect endian
                                  memAfterRval (.int .i64 false) mplace
                                  (.scalar ⟨.i64, false, bits⟩) with
                              | error k => rw [h_store] at h_next; cases h_next
                              | ok memAfterWrite =>
                                rw [h_store] at h_next
                                exact h_next

/-- Rewrite a symbolic `evalStep` for a `u64` assignment using an equivalent
normalized `BitVec 64` result. -/
theorem step_eq_evalAssignWith {endian : TargetEndian} {body : Body}
    {s next : State} {val : Val} {w : BitVec 64}
    (h_val : EvalAssignVal endian body s val)
    (h_eq : val = .scalar ⟨.i64, false, bvZeroExtend 128 w⟩)
    (h_next : EvalAssignWith endian body s
      (.scalar ⟨.i64, false, bvZeroExtend 128 w⟩) next) :
    evalStep (bodyProg body endian) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate (truncateBits_i64_bvZeroExtend w)
    h_val h_eq h_next

/-- Step an assignment whose RHS evaluates to `BitVec 64` value `x`. -/
theorem step_u64Use {endian : TargetEndian} {body : Body} {s next : State}
    (x : BitVec 64)
    (h_val : EvalAssignVal endian body s
      (.scalar ⟨.i64, false, bvZeroExtend 128 x⟩))
    (h_next : EvalAssignWith endian body s
      (.scalar ⟨.i64, false, bvZeroExtend 128 x⟩) next) :
    evalStep (bodyProg body endian) 0 s = .step next :=
  step_eq_evalAssignWith h_val rfl h_next

/-- Step an assignment whose RHS evaluates to 64-bit bitwise AND of `x` and
`y`. -/
theorem step_u64And {endian : TargetEndian} {body : Body} {s next : State}
    (x y : BitVec 64)
    (h_val : EvalAssignVal endian body s
      (.scalar ⟨.i64, false,
        truncateBits .i64 (bvAnd (truncateBits .i64 (bvZeroExtend 128 x))
          (truncateBits .i64 (bvZeroExtend 128 y)))⟩))
    (h_next : EvalAssignWith endian body s (u64BitAndVal x y) next) :
    evalStep (bodyProg body endian) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate
    (truncateBits_i64_ofNat_lt
      (Anneal.NatBitwise.land_lt_two_pow x.isLt y.isLt))
    h_val (u64BitAnd_sem_eq x y) h_next

/-- Step an assignment whose RHS evaluates to 64-bit bitwise OR of `x` and
`y`. -/
theorem step_u64Or {endian : TargetEndian} {body : Body} {s next : State}
    (x y : BitVec 64)
    (h_val : EvalAssignVal endian body s
      (.scalar ⟨.i64, false,
        truncateBits .i64 (bvOr (truncateBits .i64 (bvZeroExtend 128 x))
          (truncateBits .i64 (bvZeroExtend 128 y)))⟩))
    (h_next : EvalAssignWith endian body s (u64BitOrVal x y) next) :
    evalStep (bodyProg body endian) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate
    (truncateBits_i64_ofNat_lt
      (Anneal.NatBitwise.lor_lt_two_pow x.isLt y.isLt))
    h_val (u64BitOr_sem_eq x y) h_next

/-- Step an assignment whose RHS evaluates to 64-bit left shift of `x` by
`k`. -/
theorem step_u64Shl {endian : TargetEndian} {body : Body} {s next : State}
    (x : BitVec 64) (k : Nat)
    (h_val : EvalAssignVal endian body s
      (.scalar ⟨.i64, false,
        truncateBits .i64 (bvOfInt 128
          (.ofNat (Nat.shiftLeft
            (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩))
    (h_next : EvalAssignWith endian body s (u64ShlVal x k) next) :
    evalStep (bodyProg body endian) 0 s = .step next :=
  step_eq_evalAssignWith h_val
    ((u64Shl_sem_eq x k).trans (u64ShlVal_eq x k)) h_next

/-- Step an assignment whose RHS evaluates to 64-bit logical right shift of
`x` by `k`. -/
theorem step_u64Shr {endian : TargetEndian} {body : Body} {s next : State}
    (x : BitVec 64) (k : Nat)
    (h_val : EvalAssignVal endian body s
      (.scalar ⟨.i64, false,
        truncateBits .i64 (bvOfInt 128
          (.ofNat (Nat.shiftRight
            (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩))
    (h_next : EvalAssignWith endian body s (u64ShrVal x k) next) :
    evalStep (bodyProg body endian) 0 s = .step next :=
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

end Anneal.MirWp

end
