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
public import Init.Data.Nat.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.Framework.StepWp
public import Anneal.MirWp.Core
public import Anneal.MirWp.Execution
public import Anneal.MirWp.V2Memory

public section

/-!
# Quantitative Step-Bound Core (`Anneal.StepBound.Core`)

Pass-1-portable (`0` Trusted LOC, zero banned tactics, zero `._unsafe_rec`)
step-bounded execution predicates and adequacy bridges over the trusted MIR
small-step semantics:

- **Profile v1 (`ReachesDoneWithin`, `ExecWithinSteps`):** Explicit step-budget
  predicates over `Step` / `initState`, proved equivalent to
  `Anneal.MirWp.wpProg` and `Anneal.MirWp.execProg`, ruling out infinite MIR
  step traces (`¬ Diverges`) and discharging `WellFormed` / `Behavior` /
  `SatisfiesPost` (guaranteeing normal `.returned` return when `post` rejects
  `.unwound`).
- **Profile v2 (`ReachesDoneWithinV2`, `ExecWithinStepsV2`):** Explicit
  step-budget predicates over `StepV2` / `initStateV2`, proved constructively
  equivalent to `Anneal.MirWp.execStateV2` and `Anneal.MirWp.execProgV2`,
  ruling out infinite MIR `.step` traces (`¬ DivergesV2`) and discharging
  `WellFormedV2`, `BehaviorV2`, `SatisfiesPostV2` (`v2_adequacy_bounded`), and
  `SafeContractV2` (`satisfiesSafeContractV2_of_execWithinStepsV2`). Under
  `--panic abort`, `.done (.aborted _)` stops MIR stepping without bounding
  unverified panic hooks, so `post` (or `EffectMaskV2.noAbort`) must reject
  `.aborted` and `.unwound` to guarantee normal termination.
- **Sequential Trace Composition (`StepsToV1`, `StepsToV2`, `BoundedReachV1`,
  `BoundedReachV2`):** Composable exact and upper-bounded multi-step `.step`
  relations, plus direct interoperability with `StepStageCut`.
- **Refutation & Tight-Budget Non-Vacuity Helpers:** Deterministic step-count
  lemmas refuting `ReachesDoneWithinV2` / `ExecWithinStepsV2` on infinite traces
  (`DivergesV2`), under-budget bounds (`bound ≤ k`), faulting trajectories, or
  postcondition failures.

All step bounds count **deterministic MIR abstract-machine small steps**
(`Step` / `StepV2`), not physical CPU cycles or microarchitectural caches.
-/

namespace Anneal.StepBound

open Trusted.MirAst Trusted.MirSemantics
open Anneal.Framework.StepWp Anneal.MirWp

/-! ## 1. Determinism of Trusted Profile v1 and v2 Steps -/

/-- Profile v1 `Step` is deterministic and equivalent to `evalStep p 0 s = res`
because `ValidChoice p s c` holds iff `c = 0`. -/
theorem stepV1_iff_evalStep {p : Program} {s : State}
    {res : StepResult State TerminalOut} :
    Step p s res ↔ evalStep p 0 s = res := by
  constructor
  · intro hStep
    let ⟨c, hChoice, hEval⟩ := hStep
    cases hChoice
    exact hEval
  · intro hEval
    exact ⟨0, rfl, hEval⟩

/-- Profile v1 `Step` yields a unique `StepResult`. -/
theorem stepV1_deterministic {p : Program} {s : State}
    {r₁ r₂ : StepResult State TerminalOut}
    (h₁ : Step p s r₁) (h₂ : Step p s r₂) : r₁ = r₂ := by
  have he₁ := stepV1_iff_evalStep.mp h₁
  have he₂ := stepV1_iff_evalStep.mp h₂
  rw [← he₁, he₂]

/-- Profile v2 `StepV2` is deterministic and equivalent to
`evalStepV2 p s = res`. -/
theorem stepV2_iff_evalStepV2 {p : Program} {s : State}
    {res : StepResult State TerminalOut} :
    StepV2 p s res ↔ evalStepV2 p s = res := by
  constructor
  · intro hStep
    let ⟨c, _, hEval⟩ := hStep
    exact hEval
  · intro hEval
    exact ⟨0, rfl, hEval⟩

/-- Profile v2 `StepV2` yields a unique `StepResult`. -/
theorem stepV2_deterministic {p : Program} {s : State}
    {r₁ r₂ : StepResult State TerminalOut}
    (h₁ : StepV2 p s r₁) (h₂ : StepV2 p s r₂) : r₁ = r₂ := by
  have he₁ := stepV2_iff_evalStepV2.mp h₁
  have he₂ := stepV2_iff_evalStepV2.mp h₂
  rw [← he₁, he₂]

/-! ## 2. Profile v1 `ReachesDoneWithin` & `ExecWithinSteps` -/

/-- State `s` reaches `.done out` in Profile v1 within at most `bound` MIR
steps with `post out` (never faulting or exceeding `bound`; rules out `.unwound`
when `post` rejects unwinding). Uses `@Nat.rec` to stay free of `.eq_1` /
`._unsafe_rec`. -/
@[expose] def ReachesDoneWithin (p : Program) (post : TerminalOut → Prop) :
    Nat → State → Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih s =>
      (∃ out : TerminalOut, Step p s (.done out) ∧ post out) ∨
      (∃ s' : State, Step p s (.step s') ∧ ih s'))

/-- Program `p` on Profile v1 query `q` initializes cleanly and reaches
`.done out` satisfying `post out` within at most `bound` MIR steps. -/
@[expose] def ExecWithinSteps (p : Program) (q : Query) (bound : Nat)
    (post : TerminalOut → Prop) : Prop :=
  ∃ s₀ : State,
    initState p q = .ok s₀ ∧
    ReachesDoneWithin p post bound s₀

/-- Zero step budget is uninhabited (`ReachesDoneWithin ... 0 s ↔ False`). -/
theorem reachesDoneWithin_zero_iff (p : Program) (post : TerminalOut → Prop)
    (s : State) :
    ReachesDoneWithin p post 0 s ↔ False :=
  Iff.rfl

/-- Successor unfolding for `ReachesDoneWithin`. -/
theorem reachesDoneWithin_succ_iff (p : Program) (post : TerminalOut → Prop)
    (b : Nat) (s : State) :
    ReachesDoneWithin p post (b + 1) s ↔
      (∃ out : TerminalOut, Step p s (.done out) ∧ post out) ∨
      (∃ s' : State, Step p s (.step s') ∧ ReachesDoneWithin p post b s') :=
  Iff.rfl

/-- Direct base introduction on a Profile v1 `.done` transition. -/
theorem reachesDoneWithin_of_done {p : Program} {post : TerminalOut → Prop}
    {s : State} {out : TerminalOut}
    (hDone : Step p s (.done out)) (hPost : post out) :
    ReachesDoneWithin p post 1 s :=
  Or.inl ⟨out, hDone, hPost⟩

/-- Direct step introduction on a Profile v1 `.step` transition. -/
theorem reachesDoneWithin_of_step {p : Program} {post : TerminalOut → Prop}
    {b : Nat} {s s' : State}
    (hStep : Step p s (.step s')) (hRest : ReachesDoneWithin p post b s') :
    ReachesDoneWithin p post (b + 1) s :=
  Or.inr ⟨s', hStep, hRest⟩

/-- Monotonicity of `ReachesDoneWithin` in the step budget (`b₁ ≤ b₂`). -/
theorem ReachesDoneWithin.mono {p : Program} {post : TerminalOut → Prop} :
    ∀ {b₁ b₂ : Nat} {s : State},
      b₁ ≤ b₂ →
      ReachesDoneWithin p post b₁ s →
      ReachesDoneWithin p post b₂ s
  | 0, _, _, _, h => False.elim h
  | k + 1, b₂, s, hLe, h => by
    cases b₂ with
    | zero => cases hLe
    | succ b₂' =>
      cases h with
      | inl hDone => exact Or.inl hDone
      | inr hStep =>
        let ⟨s', hs, hRest⟩ := hStep
        exact Or.inr ⟨s', hs,
          ReachesDoneWithin.mono (Nat.le_of_succ_le_succ hLe) hRest⟩

/-- Postcondition weakening for `ReachesDoneWithin`. -/
theorem ReachesDoneWithin.weaken {p : Program} {post₁ post₂ : TerminalOut → Prop}
    (hImp : ∀ out, post₁ out → post₂ out) :
    ∀ {b : Nat} {s : State},
      ReachesDoneWithin p post₁ b s →
      ReachesDoneWithin p post₂ b s
  | 0, _, h => False.elim h
  | k + 1, s, h => by
    cases h with
    | inl hDone =>
      let ⟨out, hs, hp⟩ := hDone
      exact Or.inl ⟨out, hs, hImp out hp⟩
    | inr hStep =>
      let ⟨s', hs, hRest⟩ := hStep
      exact Or.inr ⟨s', hs, ReachesDoneWithin.weaken hImp hRest⟩

/-- Step-budget monotonicity for Profile v1 `ExecWithinSteps`. -/
theorem ExecWithinSteps.mono {p : Program} {q : Query}
    {post : TerminalOut → Prop} {b₁ b₂ : Nat} (hLe : b₁ ≤ b₂)
    (h : ExecWithinSteps p q b₁ post) :
    ExecWithinSteps p q b₂ post := by
  let ⟨s₀, hInit, hReach⟩ := h
  exact ⟨s₀, hInit, ReachesDoneWithin.mono hLe hReach⟩

/-- Postcondition weakening for Profile v1 `ExecWithinSteps`. -/
theorem ExecWithinSteps.weaken {p : Program} {q : Query} {b : Nat}
    {post₁ post₂ : TerminalOut → Prop} (hImp : ∀ out, post₁ out → post₂ out)
    (h : ExecWithinSteps p q b post₁) :
    ExecWithinSteps p q b post₂ := by
  let ⟨s₀, hInit, hReach⟩ := h
  exact ⟨s₀, hInit, ReachesDoneWithin.weaken hImp hReach⟩

/-- Profile v1 equivalence between `ReachesDoneWithin` and `wpState`. -/
theorem reachesDoneWithin_iff_wpState {p : Program}
    {post : TerminalOut → Prop} :
    ∀ {b : Nat} {s : State},
      ReachesDoneWithin p post b s ↔ wpState p b s post
  | 0, _ => Iff.rfl
  | b + 1, s => by
    constructor
    · intro h
      have hRes : ∃ res, evalStep p 0 s = res := ⟨evalStep p 0 s, rfl⟩
      cases h with
      | inl hDone =>
        let ⟨out, hStep, hPost⟩ := hDone
        have hEq := stepV1_iff_evalStep.mp hStep
        unfold wpState wpOutcomeState wpStepOutcome
        rw [wpStepPred_succ_iff]
        refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
        cases hc
        rw [hEq]
        exact hPost
      | inr hStep =>
        let ⟨s', hStepS, hRest⟩ := hStep
        have hEq := stepV1_iff_evalStep.mp hStepS
        unfold wpState wpOutcomeState wpStepOutcome
        rw [wpStepPred_succ_iff]
        refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
        cases hc
        rw [hEq]
        exact (reachesDoneWithin_iff_wpState (b := b) (s := s')).mp hRest
    · intro h
      unfold wpState wpOutcomeState wpStepOutcome at h
      rw [wpStepPred_succ_iff] at h
      let ⟨⟨c0, hc0⟩, hAll⟩ := h
      have hZero := hAll 0 rfl
      cases hc0
      cases hEval : evalStep p 0 s with
      | step s' =>
        rw [hEval] at hZero
        exact Or.inr ⟨s', stepV1_iff_evalStep.mpr hEval,
          (reachesDoneWithin_iff_wpState (b := b) (s := s')).mpr hZero⟩
      | done out =>
        rw [hEval] at hZero
        exact Or.inl ⟨out, stepV1_iff_evalStep.mpr hEval, hZero⟩
      | fault _ =>
        rw [hEval] at hZero
        exact False.elim hZero

/-- Profile v1 equivalence between `ReachesDoneWithin` and `execState`. -/
theorem reachesDoneWithin_iff_execState {p : Program}
    {post : TerminalOut → Prop} {b : Nat} {s : State} :
    ReachesDoneWithin p post b s ↔ execState p b s post := by
  exact Iff.trans reachesDoneWithin_iff_wpState
    wpOutcomeState_iff_execOutcomeState

/-- Profile v1 program-level equivalence between `ExecWithinSteps` and
`wpProg`. -/
theorem execWithinSteps_iff_wpProg {p : Program} {b : Nat} {q : Query}
    {post : TerminalOut → Prop} :
    ExecWithinSteps p q b post ↔ wpProg p b q post := by
  unfold ExecWithinSteps wpProg
  cases hInit : initState p q with
  | error e =>
    constructor
    · intro ⟨s₀, hOk, _⟩
      cases hOk
    · intro hFalse
      exact False.elim hFalse
  | ok s₀ =>
    constructor
    · intro ⟨s₁, hOk, hReach⟩
      cases hOk
      exact reachesDoneWithin_iff_wpState.mp hReach
    · intro hWp
      exact ⟨s₀, rfl, reachesDoneWithin_iff_wpState.mpr hWp⟩

/-- Profile v1 program-level equivalence between `ExecWithinSteps` and
`execProg`. -/
theorem execWithinSteps_iff_execProg {p : Program} {b : Nat} {q : Query}
    {post : TerminalOut → Prop} :
    ExecWithinSteps p q b post ↔ execProg p b q post :=
  Iff.trans execWithinSteps_iff_wpProg wpProg_iff_execProg

/-- Any `ExecWithinSteps` witness rules out Profile v1 divergence. -/
theorem not_diverges_of_execWithinSteps {p : Program} {q : Query} {b : Nat}
    {post : TerminalOut → Prop} (h : ExecWithinSteps p q b post) :
    ¬ Diverges p q :=
  not_diverges_of_wpProg (execWithinSteps_iff_wpProg.mp h)

/-- Full Profile v1 soundness from `ExecWithinSteps`: well-formedness,
postcondition satisfaction, and absence of MIR `.step` divergence (`¬ Diverges`;
normal return holds when `post` rejects `.unwound`). -/
theorem wellFormed_and_spec_of_execWithinSteps {p : Program} {q : Query}
    {b : Nat} {post : TerminalOut → Prop} (h : ExecWithinSteps p q b post) :
    WellFormed p q ∧ SatisfiesPost p q post ∧ ¬ Diverges p q := by
  have hWp := execWithinSteps_iff_wpProg.mp h
  have hBase := wellFormed_and_spec_of_wp_base p q b post hWp
  exact ⟨hBase.1.1, hBase.1, hBase.2.1⟩

/-! ## 3. Profile v2 `ReachesDoneWithinV2` & `ExecWithinStepsV2` -/

/-- State `s` reaches `.done out` in Profile v2 within at most `bound` MIR
steps with `post out` (never faulting or exceeding `bound`; rejecting `.aborted`
and `.unwound` in `post` guarantees normal `.returned` exit). Uses `@Nat.rec`
so the theory library avoids equation helpers and `._unsafe_rec`. -/
@[expose] def ReachesDoneWithinV2 (p : Program) (post : TerminalOut → Prop) :
    Nat → State → Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih s =>
      (∃ out : TerminalOut, StepV2 p s (.done out) ∧ post out) ∨
      (∃ s' : State, StepV2 p s (.step s') ∧ ih s'))

/-- Program `p` on Profile v2 query `q` initializes cleanly and reaches
`.done out` satisfying `post out` within at most `bound` MIR steps. -/
@[expose] def ExecWithinStepsV2 (p : Program) (q : Query) (bound : Nat)
    (post : TerminalOut → Prop) : Prop :=
  ∃ s₀ : State,
    initStateV2 p q = .ok s₀ ∧
    ReachesDoneWithinV2 p post bound s₀

/-- Zero step budget is uninhabited (`ReachesDoneWithinV2 ... 0 s ↔ False`). -/
theorem reachesDoneWithinV2_zero_iff (p : Program) (post : TerminalOut → Prop)
    (s : State) :
    ReachesDoneWithinV2 p post 0 s ↔ False :=
  Iff.rfl

/-- Successor unfolding for `ReachesDoneWithinV2`. -/
theorem reachesDoneWithinV2_succ_iff (p : Program) (post : TerminalOut → Prop)
    (b : Nat) (s : State) :
    ReachesDoneWithinV2 p post (b + 1) s ↔
      (∃ out : TerminalOut, StepV2 p s (.done out) ∧ post out) ∨
      (∃ s' : State, StepV2 p s (.step s') ∧ ReachesDoneWithinV2 p post b s') :=
  Iff.rfl

/-- Direct base introduction from `StepV2 p s (.done out)`. -/
theorem reachesDoneWithinV2_of_done {p : Program} {post : TerminalOut → Prop}
    {s : State} {out : TerminalOut}
    (hDone : StepV2 p s (.done out)) (hPost : post out) :
    ReachesDoneWithinV2 p post 1 s :=
  Or.inl ⟨out, hDone, hPost⟩

/-- Direct base introduction from `evalStepV2 p s = .done out`. -/
theorem reachesDoneWithinV2_of_eval_done {p : Program}
    {post : TerminalOut → Prop} {s : State} {out : TerminalOut}
    (hDone : evalStepV2 p s = .done out) (hPost : post out) :
    ReachesDoneWithinV2 p post 1 s :=
  Or.inl ⟨out, stepV2_iff_evalStepV2.mpr hDone, hPost⟩

/-- Direct step introduction from `StepV2 p s (.step s')`. -/
theorem reachesDoneWithinV2_of_step {p : Program} {post : TerminalOut → Prop}
    {b : Nat} {s s' : State}
    (hStep : StepV2 p s (.step s')) (hRest : ReachesDoneWithinV2 p post b s') :
    ReachesDoneWithinV2 p post (b + 1) s :=
  Or.inr ⟨s', hStep, hRest⟩

/-- Direct step introduction from `evalStepV2 p s = .step s'`. -/
theorem reachesDoneWithinV2_of_eval_step {p : Program}
    {post : TerminalOut → Prop} {b : Nat} {s s' : State}
    (hStep : evalStepV2 p s = .step s')
    (hRest : ReachesDoneWithinV2 p post b s') :
    ReachesDoneWithinV2 p post (b + 1) s :=
  Or.inr ⟨s', stepV2_iff_evalStepV2.mpr hStep, hRest⟩

/-- Monotonicity of `ReachesDoneWithinV2` in the step budget (`b₁ ≤ b₂`). -/
theorem ReachesDoneWithinV2.mono {p : Program} {post : TerminalOut → Prop} :
    ∀ {b₁ b₂ : Nat} {s : State},
      b₁ ≤ b₂ →
      ReachesDoneWithinV2 p post b₁ s →
      ReachesDoneWithinV2 p post b₂ s
  | 0, _, _, _, h => False.elim h
  | k + 1, b₂, s, hLe, h => by
    cases b₂ with
    | zero => cases hLe
    | succ b₂' =>
      cases h with
      | inl hDone => exact Or.inl hDone
      | inr hStep =>
        let ⟨s', hs, hRest⟩ := hStep
        exact Or.inr ⟨s', hs,
          ReachesDoneWithinV2.mono (Nat.le_of_succ_le_succ hLe) hRest⟩

/-- Postcondition weakening for `ReachesDoneWithinV2`. -/
theorem ReachesDoneWithinV2.weaken {p : Program}
    {post₁ post₂ : TerminalOut → Prop}
    (hImp : ∀ out, post₁ out → post₂ out) :
    ∀ {b : Nat} {s : State},
      ReachesDoneWithinV2 p post₁ b s →
      ReachesDoneWithinV2 p post₂ b s
  | 0, _, h => False.elim h
  | k + 1, s, h => by
    cases h with
    | inl hDone =>
      let ⟨out, hs, hp⟩ := hDone
      exact Or.inl ⟨out, hs, hImp out hp⟩
    | inr hStep =>
      let ⟨s', hs, hRest⟩ := hStep
      exact Or.inr ⟨s', hs, ReachesDoneWithinV2.weaken hImp hRest⟩

/-- Step-budget monotonicity for Profile v2 `ExecWithinStepsV2`. -/
theorem ExecWithinStepsV2.mono {p : Program} {q : Query}
    {post : TerminalOut → Prop} {b₁ b₂ : Nat} (hLe : b₁ ≤ b₂)
    (h : ExecWithinStepsV2 p q b₁ post) :
    ExecWithinStepsV2 p q b₂ post := by
  let ⟨s₀, hInit, hReach⟩ := h
  exact ⟨s₀, hInit, ReachesDoneWithinV2.mono hLe hReach⟩

/-- Postcondition weakening for Profile v2 `ExecWithinStepsV2`. -/
theorem ExecWithinStepsV2.weaken {p : Program} {q : Query} {b : Nat}
    {post₁ post₂ : TerminalOut → Prop} (hImp : ∀ out, post₁ out → post₂ out)
    (h : ExecWithinStepsV2 p q b post₁) :
    ExecWithinStepsV2 p q b post₂ := by
  let ⟨s₀, hInit, hReach⟩ := h
  exact ⟨s₀, hInit, ReachesDoneWithinV2.weaken hImp hReach⟩

/-- Constructive equivalence between `ReachesDoneWithinV2` and `execStateV2`.
-/
theorem reachesDoneWithinV2_iff_execStateV2 {p : Program}
    {post : TerminalOut → Prop} :
    ∀ {b : Nat} {s : State},
      ReachesDoneWithinV2 p post b s ↔ execStateV2 p b s post
  | 0, _ => Iff.rfl
  | b + 1, s => by
    constructor
    · intro h
      cases h with
      | inl hDone =>
        let ⟨out, hStep, hPost⟩ := hDone
        exact execOutcomeStateV2_done (stepV2_iff_evalStepV2.mp hStep) hPost
      | inr hStep =>
        let ⟨s', hStepS, hRest⟩ := hStep
        exact execOutcomeStateV2_step (stepV2_iff_evalStepV2.mp hStepS)
          ((reachesDoneWithinV2_iff_execStateV2 (b := b) (s := s')).mp hRest)
    · intro h
      change (match evalStepV2 p s with
        | .step st' => execStateV2 p b st' post
        | .done out => post out
        | .fault _ => False) at h
      cases hEval : evalStepV2 p s with
      | step s' =>
        rw [hEval] at h
        exact Or.inr ⟨s', stepV2_iff_evalStepV2.mpr hEval,
          (reachesDoneWithinV2_iff_execStateV2 (b := b) (s := s')).mpr h⟩
      | done out =>
        rw [hEval] at h
        exact Or.inl ⟨out, stepV2_iff_evalStepV2.mpr hEval, h⟩
      | fault _ =>
        rw [hEval] at h
        exact False.elim h

/-- Bridge between `execStateV2` and generic `StepWp.execStepPred` on
`evalStepV2 p`. -/
theorem execStateV2_iff_execStepPred {p : Program} {post : TerminalOut → Prop} :
    ∀ {b : Nat} {s : State},
      execStateV2 p b s post ↔
      execStepPred (evalStepV2 p) (fun _ => post) (fun _ _ => False) b s
  | 0, _ => Iff.rfl
  | b + 1, s => by
    constructor
    · intro h
      change (match evalStepV2 p s with
        | .step st' => execStateV2 p b st' post
        | .done out => post out
        | .fault _ => False) at h
      rw [execStepPred_succ_iff]
      cases hEval : evalStepV2 p s with
      | step s' =>
        rw [hEval] at h
        exact (execStateV2_iff_execStepPred (b := b) (s := s')).mp h
      | done out =>
        rw [hEval] at h
        exact h
      | fault k =>
        rw [hEval] at h
        exact False.elim h
    · intro h
      rw [execStepPred_succ_iff] at h
      cases hEval : evalStepV2 p s with
      | step s' =>
        rw [hEval] at h
        exact execOutcomeStateV2_step hEval
          ((execStateV2_iff_execStepPred (b := b) (s := s')).mpr h)
      | done out =>
        rw [hEval] at h
        exact execOutcomeStateV2_done hEval h
      | fault k =>
        rw [hEval] at h
        exact False.elim h

/-- Program-level equivalence between `ExecWithinStepsV2` and `execProgV2`. -/
theorem execWithinStepsV2_iff_execProgV2 {p : Program} {b : Nat} {q : Query}
    {post : TerminalOut → Prop} :
    ExecWithinStepsV2 p q b post ↔ execProgV2 p b q post := by
  unfold ExecWithinStepsV2 execProgV2
  cases hInit : initStateV2 p q with
  | error e =>
    constructor
    · intro ⟨s₀, hOk, _⟩
      cases hOk
    · intro hFalse
      exact False.elim hFalse
  | ok s₀ =>
    constructor
    · intro ⟨s₁, hOk, hReach⟩
      cases hOk
      exact reachesDoneWithinV2_iff_execStateV2.mp hReach
    · intro hExec
      exact ⟨s₀, rfl, reachesDoneWithinV2_iff_execStateV2.mpr hExec⟩

/-- Any `ExecWithinStepsV2` witness rules out Profile v2 divergence. -/
theorem not_divergesV2_of_execWithinStepsV2 {p : Program} {q : Query} {b : Nat}
    {post : TerminalOut → Prop} (h : ExecWithinStepsV2 p q b post) :
    ¬ DivergesV2 p q := by
  intro hDiv
  let ⟨s₀, hInit, trace, hTr0, hSteps⟩ := hDiv
  let ⟨s₁, hInit', hReach⟩ := h
  rw [hInit] at hInit'
  cases hInit'
  rw [← hTr0] at hReach
  exact not_infinite_trace_of_execOutcomeStateV2 trace
    (reachesDoneWithinV2_iff_execStateV2.mp hReach) hSteps

/-- Full Profile v2 soundness from `ExecWithinStepsV2`: well-formedness,
postcondition satisfaction, and absence of infinite MIR `.step` traces
(`¬ DivergesV2`; under `--panic abort`, `post` must exclude `.aborted` and
`.unwound` to guarantee non-aborting termination). -/
theorem wellFormed_and_spec_of_execWithinStepsV2 {p : Program} {q : Query}
    {b : Nat} {post : TerminalOut → Prop} (h : ExecWithinStepsV2 p q b post) :
    WellFormedV2 p q ∧ SatisfiesPostV2 p q post ∧ ¬ DivergesV2 p q := by
  have hBase := wellFormed_and_spec_of_execV2_base p q b post
    (execWithinStepsV2_iff_execProgV2.mp h)
  exact ⟨hBase.1.1, hBase.1, hBase.2.1⟩

/-- Generalized Profile v2 adequacy theorem for arbitrary postconditions:
bundles `ExecWithinStepsV2`, `WellFormedV2`, `¬ DivergesV2`, `SatisfiesPostV2`,
and existential witnessing of an actual terminal outcome satisfying `post`. -/
theorem v2_adequacy_bounded_post {p : Program} {q : Query} {s₀ : State}
    {bound : Nat} {post : TerminalOut → Prop}
    (hInit : initStateV2 p q = .ok s₀)
    (hSteps : ReachesDoneWithinV2 p post bound s₀) :
    ExecWithinStepsV2 p q bound post ∧
    WellFormedV2 p q ∧
    ¬ DivergesV2 p q ∧
    SatisfiesPostV2 p q post ∧
    (∃ out : TerminalOut, BehaviorV2 p q out ∧ post out) := by
  have hWithin : ExecWithinStepsV2 p q bound post := ⟨s₀, hInit, hSteps⟩
  have hSound := wellFormed_and_spec_of_execWithinStepsV2 hWithin
  have hExecS : execStateV2 p bound s₀ post :=
    reachesDoneWithinV2_iff_execStateV2.mp hSteps
  let ⟨sEnd, res, hReach, hStepEnd, hOut⟩ :=
    exists_terminal_of_execOutcomeStateV2 hExecS
  cases res with
  | step _ => exact False.elim hOut
  | fault _ => exact False.elim hOut
  | done out =>
    have hBeh : BehaviorV2 p q out := by
      unfold BehaviorV2 ReachesResultV2
      rw [hInit]
      exact ⟨sEnd, hReach, hStepEnd⟩
    exact ⟨hWithin, hSound.1, hSound.2.2, hSound.2.1, ⟨out, hBeh, hOut⟩⟩

/-- Exact-return Profile v2 adequacy theorem (`out = .returned ret`):
bundles `ExecWithinStepsV2`, `WellFormedV2`, `BehaviorV2`, `¬ DivergesV2`, and
universal postcondition lift. Promoted cleanly without banned tactics. -/
theorem v2_adequacy_bounded {p : Program} {q : Query} {s₀ : State}
    {bound : Nat} {ret : Out}
    (hInit : initStateV2 p q = .ok s₀)
    (hSteps : ReachesDoneWithinV2 p (fun out => out = .returned ret) bound s₀) :
    ExecWithinStepsV2 p q bound (fun out => out = .returned ret) ∧
    WellFormedV2 p q ∧
    BehaviorV2 p q (.returned ret) ∧
    ¬ DivergesV2 p q ∧
    ∀ post : TerminalOut → Prop, post (.returned ret) → SatisfiesPostV2 p q post := by
  have hWithin :
      ExecWithinStepsV2 p q bound (fun out => out = .returned ret) :=
    ⟨s₀, hInit, hSteps⟩
  have hProg : execProgV2 p bound q (fun out => out = .returned ret) :=
    execWithinStepsV2_iff_execProgV2.mp hWithin
  have hSpec := spec_and_behaviorV2_of_exec_eq hProg
  exact ⟨hWithin, hSpec⟩

/-- Tie `ExecWithinStepsV2` to `SatisfiesSafeContractV2`: when
`contract.behaviorPre q` implies
`ExecWithinStepsV2 p q bound (contract.post q)`,
`SatisfiesSafeContractV2 p q contract` holds alongside `WellFormedV2` and
`¬ DivergesV2`. With `contract.effects = EffectMaskV2.noAbort`,
`contract.post q` rejects both `.unwound` and `.aborted` (including
`--panic abort` hooks). -/
theorem satisfiesSafeContractV2_of_execWithinStepsV2 {p : Program} {q : Query}
    {bound : Nat} {contract : SafeContractV2}
    (hPre : contract.behaviorPre q →
      ExecWithinStepsV2 p q bound (contract.post q)) :
    SatisfiesSafeContractV2 p q contract ∧
    (contract.behaviorPre q → WellFormedV2 p q ∧ ¬ DivergesV2 p q) := by
  refine ⟨fun hDom => ?_, fun hDom => ?_⟩
  · exact (wellFormed_and_spec_of_execWithinStepsV2 (hPre hDom)).2.1
  · have hS := wellFormed_and_spec_of_execWithinStepsV2 (hPre hDom)
    exact ⟨hS.1, hS.2.2⟩

/-- Body-level `SafeContractV2` soundness from bounded MIR execution: discharges
`BodySatisfiesSafeContractV2 p defId body contract` directly from per-query
`ExecWithinStepsV2` witnesses. -/
theorem bodySatisfiesSafeContractV2_of_execWithinStepsV2 {p : Program}
    {defId : DefId} {body : Body} {contract : SafeContractV2}
    {boundOf : Query → Nat}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 p body = true)
    (hAll : ∀ q : Query, ValidEntryArgsV2 body q → contract.behaviorPre q →
      ExecWithinStepsV2 (entryProgForBody p defId) q (boundOf q)
        (contract.post q)) :
    BodySatisfiesSafeContractV2 p defId body contract :=
  ⟨hBody, hAdm, fun q hValid hPre =>
    (satisfiesSafeContractV2_of_execWithinStepsV2
      (hAll q hValid)).1 hPre⟩

/-! ## 4. Sequential Trace Relations (`StepsToV1`, `StepsToV2`,
`BoundedReach`) -/

/-- Exact `n`-step Profile v1 `.step` transition sequence `s₁ →^n s₂`. -/
inductive StepsToV1 (p : Program) : Nat → State → State → Prop where
  | refl (s : State) : StepsToV1 p 0 s s
  | step {n : Nat} {s s' s'' : State} :
      Step p s (.step s') →
      StepsToV1 p n s' s'' →
      StepsToV1 p (n + 1) s s''

/-- Single `.step` lifting for `StepsToV1`. -/
theorem StepsToV1.single {p : Program} {s s' : State}
    (hStep : Step p s (.step s')) : StepsToV1 p 1 s s' :=
  StepsToV1.step hStep (StepsToV1.refl s')

/-- Exact `k1 + k2` sequential composition for `StepsToV1`. -/
theorem StepsToV1.trans {p : Program} {k₁ k₂ : Nat} {s₀ s₁ s₂ : State}
    (h₁ : StepsToV1 p k₁ s₀ s₁) (h₂ : StepsToV1 p k₂ s₁ s₂) :
    StepsToV1 p (k₁ + k₂) s₀ s₂ := by
  induction h₁ with
  | refl _ =>
    rw [Nat.zero_add]
    exact h₂
  | @step n _ _ _ hs _ ih =>
    rw [Nat.succ_add n k₂]
    exact StepsToV1.step hs (ih h₂)

/-- Prepending a Profile v1 `StepsToV1` trace onto `ReachesDoneWithin`. -/
theorem reachesDoneWithin_of_stepsTo {p : Program} {post : TerminalOut → Prop}
    {k₁ k₂ : Nat} {s₀ s₁ : State}
    (hPrefix : StepsToV1 p k₁ s₀ s₁) (hRest : ReachesDoneWithin p post k₂ s₁) :
    ReachesDoneWithin p post (k₁ + k₂) s₀ := by
  induction hPrefix with
  | refl _ =>
    rw [Nat.zero_add]
    exact hRest
  | step hs _ ih =>
    rw [Nat.succ_add]
    exact reachesDoneWithin_of_step hs (ih hRest)

/-- Upper-bounded Profile v1 multi-step reachability (`∃ k ≤ bound`). -/
@[expose] def BoundedReachV1 (p : Program) (stopPred : State → Prop)
    (bound : Nat) (s : State) : Prop :=
  ∃ k : Nat, ∃ s' : State, k ≤ bound ∧ StepsToV1 p k s s' ∧ stopPred s'

/-- Zero-step reflexivity for `BoundedReachV1`. -/
theorem BoundedReachV1.refl {p : Program} {stopPred : State → Prop}
    (bound : Nat) {s : State} (hP : stopPred s) :
    BoundedReachV1 p stopPred bound s :=
  ⟨0, s, Nat.zero_le bound, StepsToV1.refl s, hP⟩

/-- Budget monotonicity for `BoundedReachV1`. -/
theorem BoundedReachV1.mono {p : Program} {stopPred : State → Prop}
    {b₁ b₂ : Nat} {s : State} (hLe : b₁ ≤ b₂)
    (h : BoundedReachV1 p stopPred b₁ s) :
    BoundedReachV1 p stopPred b₂ s := by
  let ⟨k, s', hk, hSteps, hP⟩ := h
  exact ⟨k, s', Nat.le_trans hk hLe, hSteps, hP⟩

/-- Sequential composition (`b₁ + b₂`) for `BoundedReachV1`. -/
theorem BoundedReachV1.trans {p : Program} {P Q : State → Prop}
    {b₁ b₂ : Nat} {s₀ : State}
    (h₁ : BoundedReachV1 p P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ → BoundedReachV1 p Q b₂ s₁) :
    BoundedReachV1 p Q (b₁ + b₂) s₀ := by
  let ⟨k₁, s₁, hk₁, hSteps₁, hP⟩ := h₁
  let ⟨k₂, s₂, hk₂, hSteps₂, hQ⟩ := h₂ s₁ hP
  exact ⟨k₁ + k₂, s₂, Nat.add_le_add hk₁ hk₂,
    StepsToV1.trans hSteps₁ hSteps₂, hQ⟩

/-- Bind a Profile v1 `BoundedReachV1` prefix with a `ReachesDoneWithin` suffix.
-/
theorem BoundedReachV1.bind_done {p : Program} {P : State → Prop}
    {post : TerminalOut → Prop} {b₁ b₂ : Nat} {s₀ : State}
    (h₁ : BoundedReachV1 p P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ → ReachesDoneWithin p post b₂ s₁) :
    ReachesDoneWithin p post (b₁ + b₂) s₀ := by
  let ⟨k₁, s₁, hk₁, hSteps₁, hP⟩ := h₁
  exact ReachesDoneWithin.mono (Nat.add_le_add_right hk₁ b₂)
    (reachesDoneWithin_of_stepsTo hSteps₁ (h₂ s₁ hP))

/-- Exact `n`-step Profile v2 `.step` transition sequence `s₁ →^n s₂`. -/
inductive StepsToV2 (p : Program) : Nat → State → State → Prop where
  | refl (s : State) : StepsToV2 p 0 s s
  | step {n : Nat} {s s' s'' : State} :
      StepV2 p s (.step s') →
      StepsToV2 p n s' s'' →
      StepsToV2 p (n + 1) s s''

/-- Single `.step` lifting for `StepsToV2`. -/
theorem StepsToV2.single {p : Program} {s s' : State}
    (hStep : StepV2 p s (.step s')) : StepsToV2 p 1 s s' :=
  StepsToV2.step hStep (StepsToV2.refl s')

/-- Single `evalStepV2 p s = .step s'` lifting for `StepsToV2`. -/
theorem StepsToV2.of_eval_step {p : Program} {s s' : State}
    (hStep : evalStepV2 p s = .step s') : StepsToV2 p 1 s s' :=
  StepsToV2.single (stepV2_iff_evalStepV2.mpr hStep)

/-- Exact `k1 + k2` sequential composition for `StepsToV2`. -/
theorem StepsToV2.trans {p : Program} {k₁ k₂ : Nat} {s₀ s₁ s₂ : State}
    (h₁ : StepsToV2 p k₁ s₀ s₁) (h₂ : StepsToV2 p k₂ s₁ s₂) :
    StepsToV2 p (k₁ + k₂) s₀ s₂ := by
  induction h₁ with
  | refl _ =>
    rw [Nat.zero_add]
    exact h₂
  | @step n _ _ _ hs _ ih =>
    rw [Nat.succ_add n k₂]
    exact StepsToV2.step hs (ih h₂)

/-- Lift an exact `StepsToV2` chain to `ReachesV2`. -/
theorem StepsToV2.to_reachesV2 {p : Program} {k : Nat} {s₀ s₁ : State}
    (h : StepsToV2 p k s₀ s₁) : ReachesV2 p s₀ s₁ := by
  induction h with
  | refl s => exact ReachesV2.refl s
  | step hs _ ih => exact ReachesV2.head hs ih

/-- Lift an exact `StepsToV2` chain to `StepStageCut (evalStepV2 p)`. -/
theorem StepsToV2.to_stepStageCut {p : Program} {k : Nat} {s₀ s₁ : State}
    (h : StepsToV2 p k s₀ s₁) : StepStageCut (evalStepV2 p) k s₀ s₁ := by
  induction h with
  | refl s => exact StepStageCut.refl (evalStepV2 p) 0 s
  | step hs _ ih =>
    exact StepStageCut.step (stepV2_iff_evalStepV2.mp hs) ih

/-- Prepending a Profile v2 `StepsToV2` trace onto `ReachesDoneWithinV2`. -/
theorem reachesDoneWithinV2_of_stepsTo {p : Program} {post : TerminalOut → Prop}
    {k₁ k₂ : Nat} {s₀ s₁ : State}
    (hPrefix : StepsToV2 p k₁ s₀ s₁)
    (hRest : ReachesDoneWithinV2 p post k₂ s₁) :
    ReachesDoneWithinV2 p post (k₁ + k₂) s₀ := by
  induction hPrefix with
  | refl _ =>
    rw [Nat.zero_add]
    exact hRest
  | step hs _ ih =>
    rw [Nat.succ_add]
    exact reachesDoneWithinV2_of_step hs (ih hRest)

/-- Prepending a Profile v2 `StepsToV2` trace onto `execStateV2`. -/
theorem execStateV2_of_stepsTo {p : Program} {post : TerminalOut → Prop}
    {k₁ k₂ : Nat} {s₀ s₁ : State}
    (hPrefix : StepsToV2 p k₁ s₀ s₁)
    (hRest : execStateV2 p k₂ s₁ post) :
    execStateV2 p (k₁ + k₂) s₀ post :=
  reachesDoneWithinV2_iff_execStateV2.mp
    (reachesDoneWithinV2_of_stepsTo hPrefix
      (reachesDoneWithinV2_iff_execStateV2.mpr hRest))

/-- Upper-bounded Profile v2 multi-step reachability (`∃ k ≤ bound`). -/
@[expose] def BoundedReachV2 (p : Program) (stopPred : State → Prop)
    (bound : Nat) (s : State) : Prop :=
  ∃ k : Nat, ∃ s' : State, k ≤ bound ∧ StepsToV2 p k s s' ∧ stopPred s'

/-- Zero-step reflexivity for `BoundedReachV2`. -/
theorem BoundedReachV2.refl {p : Program} {stopPred : State → Prop}
    (bound : Nat) {s : State} (hP : stopPred s) :
    BoundedReachV2 p stopPred bound s :=
  ⟨0, s, Nat.zero_le bound, StepsToV2.refl s, hP⟩

/-- Exact `StepsToV2` introduction into `BoundedReachV2`. -/
theorem BoundedReachV2.of_exact {p : Program} {stopPred : State → Prop}
    {k bound : Nat} {s s' : State}
    (hk : k ≤ bound) (hSteps : StepsToV2 p k s s') (hP : stopPred s') :
    BoundedReachV2 p stopPred bound s :=
  ⟨k, s', hk, hSteps, hP⟩

/-- Step-prefix introduction into `BoundedReachV2`. -/
theorem BoundedReachV2.step {p : Program} {stopPred : State → Prop}
    {b : Nat} {s s' : State}
    (hStep : StepV2 p s (.step s')) (hRest : BoundedReachV2 p stopPred b s') :
    BoundedReachV2 p stopPred (b + 1) s := by
  let ⟨k, s'', hk, hSteps, hP⟩ := hRest
  exact ⟨k + 1, s'', Nat.succ_le_succ hk, StepsToV2.step hStep hSteps, hP⟩

/-- Budget monotonicity for `BoundedReachV2`. -/
theorem BoundedReachV2.mono {p : Program} {stopPred : State → Prop}
    {b₁ b₂ : Nat} {s : State} (hLe : b₁ ≤ b₂)
    (h : BoundedReachV2 p stopPred b₁ s) :
    BoundedReachV2 p stopPred b₂ s := by
  let ⟨k, s', hk, hSteps, hP⟩ := h
  exact ⟨k, s', Nat.le_trans hk hLe, hSteps, hP⟩

/-- Postcondition weakening for `BoundedReachV2`. -/
theorem BoundedReachV2.weaken {p : Program} {P Q : State → Prop}
    {b : Nat} {s : State} (hImp : ∀ s', P s' → Q s')
    (h : BoundedReachV2 p P b s) :
    BoundedReachV2 p Q b s := by
  let ⟨k, s', hk, hSteps, hP⟩ := h
  exact ⟨k, s', hk, hSteps, hImp s' hP⟩

/-- Sequential composition (`b₁ + b₂`) for `BoundedReachV2`. -/
theorem BoundedReachV2.trans {p : Program} {P Q : State → Prop}
    {b₁ b₂ : Nat} {s₀ : State}
    (h₁ : BoundedReachV2 p P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ → BoundedReachV2 p Q b₂ s₁) :
    BoundedReachV2 p Q (b₁ + b₂) s₀ := by
  let ⟨k₁, s₁, hk₁, hSteps₁, hP⟩ := h₁
  let ⟨k₂, s₂, hk₂, hSteps₂, hQ⟩ := h₂ s₁ hP
  exact ⟨k₁ + k₂, s₂, Nat.add_le_add hk₁ hk₂,
    StepsToV2.trans hSteps₁ hSteps₂, hQ⟩

/-- Bind a Profile v2 `BoundedReachV2` prefix with a `ReachesDoneWithinV2`
suffix (`b₁ + b₂`). -/
theorem BoundedReachV2.bind_done {p : Program} {P : State → Prop}
    {post : TerminalOut → Prop} {b₁ b₂ : Nat} {s₀ : State}
    (h₁ : BoundedReachV2 p P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ → ReachesDoneWithinV2 p post b₂ s₁) :
    ReachesDoneWithinV2 p post (b₁ + b₂) s₀ := by
  let ⟨k₁, s₁, hk₁, hSteps₁, hP⟩ := h₁
  exact ReachesDoneWithinV2.mono (Nat.add_le_add_right hk₁ b₂)
    (reachesDoneWithinV2_of_stepsTo hSteps₁ (h₂ s₁ hP))

/-- Bind a Profile v2 `BoundedReachV2` prefix with an `execStateV2` suffix
(`b₁ + b₂`). -/
theorem BoundedReachV2.bind_exec {p : Program} {P : State → Prop}
    {post : TerminalOut → Prop} {b₁ b₂ : Nat} {s₀ : State}
    (h₁ : BoundedReachV2 p P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ → execStateV2 p b₂ s₁ post) :
    execStateV2 p (b₁ + b₂) s₀ post :=
  reachesDoneWithinV2_iff_execStateV2.mp
    (BoundedReachV2.bind_done h₁
      (fun s₁ hP => reachesDoneWithinV2_iff_execStateV2.mpr (h₂ s₁ hP)))

/-- Bridge `StepStageCut (evalStepV2 p) f₁ s₀ s₁` into `ReachesDoneWithinV2`
at total step budget `f₁ + f₂`. -/
theorem reachesDoneWithinV2_of_stepStageCut {p : Program}
    {post : TerminalOut → Prop} {f₁ f₂ : Nat} {s₀ s₁ : State}
    (hCut : StepStageCut (evalStepV2 p) f₁ s₀ s₁)
    (hCont : ReachesDoneWithinV2 p post f₂ s₁) :
    ReachesDoneWithinV2 p post (f₁ + f₂) s₀ := by
  have hContE :
      execStepPred (evalStepV2 p) (fun _ => post) (fun _ _ => False) f₂ s₁ :=
    execStateV2_iff_execStepPred.mp
      (reachesDoneWithinV2_iff_execStateV2.mp hCont)
  exact reachesDoneWithinV2_iff_execStateV2.mpr
    (execStateV2_iff_execStepPred.mpr
      (execStepPred_of_stepStageCut hCut hContE))

/-! ## 5. Non-Vacuity & Tight-Budget Refutation Lemmas -/

/-- An infinite `StepV2` trace starting from `s₀` refutes `ReachesDoneWithinV2`
at every finite bound `bound`. -/
theorem not_reachesDoneWithinV2_of_infinite_trace {p : Program}
    {post : TerminalOut → Prop} (trace : Nat → State)
    (hSteps : ∀ n : Nat, StepV2 p (trace n) (.step (trace (n + 1)))) :
    ∀ (bound : Nat) (n : Nat), ¬ ReachesDoneWithinV2 p post bound (trace n)
  | 0, _, h => False.elim h
  | b + 1, n, h => by
    cases h with
    | inl hDone =>
      let ⟨out, hD, _⟩ := hDone
      have hEq := stepV2_deterministic (hSteps n) hD
      cases hEq
    | inr hStep =>
      let ⟨s', hS, hRest⟩ := hStep
      have hEq := stepV2_deterministic (hSteps n) hS
      cases hEq
      exact not_reachesDoneWithinV2_of_infinite_trace trace hSteps b (n + 1) hRest

/-- Divergence (`DivergesV2 p q`) refutes `ExecWithinStepsV2 p q bound post` for
every finite step budget and postcondition. -/
theorem not_execWithinStepsV2_of_divergesV2 {p : Program} {q : Query}
    (hDiv : DivergesV2 p q) (bound : Nat) (post : TerminalOut → Prop) :
    ¬ ExecWithinStepsV2 p q bound post := by
  intro hWithin
  exact not_divergesV2_of_execWithinStepsV2 hWithin hDiv

/-- Any `bound ≤ k` is strictly insufficient when deterministic execution takes
`k` `.step` transitions via `StepsToV2 p k s s'`. -/
theorem not_reachesDoneWithinV2_of_stepsTo_ge {p : Program}
    {post : TerminalOut → Prop} :
    ∀ {k bound : Nat} {s s' : State},
      StepsToV2 p k s s' →
      bound ≤ k →
      ¬ ReachesDoneWithinV2 p post bound s
  | _, 0, _, _, _, _, h => False.elim h
  | 0, b + 1, _, _, _, hLe, _ => by cases hLe
  | k + 1, b + 1, s, s', hSteps, hLe, hReach => by
    cases hSteps with
    | step hStepS hTail =>
      cases hReach with
      | inl hDone =>
        let ⟨_, hD, _⟩ := hDone
        have hEq := stepV2_deterministic hStepS hD
        cases hEq
      | inr hNext =>
        let ⟨s₁, hS₁, hRest⟩ := hNext
        have hEq := stepV2_deterministic hStepS hS₁
        cases hEq
        exact not_reachesDoneWithinV2_of_stepsTo_ge hTail
          (Nat.le_of_succ_le_succ hLe) hRest

/-- If `s` reaches `s'` in `k` `.step` transitions and `s'` steps to
`.done out` where `¬ post out`, then `ReachesDoneWithinV2 p post bound s` fails
for all `bound`. -/
theorem not_reachesDoneWithinV2_of_stepsTo_done_fail {p : Program}
    {post : TerminalOut → Prop} :
    ∀ {k bound : Nat} {s s' : State} {out : TerminalOut},
      StepsToV2 p k s s' →
      StepV2 p s' (.done out) →
      ¬ post out →
      ¬ ReachesDoneWithinV2 p post bound s
  | _, 0, _, _, _, _, _, _, h => False.elim h
  | 0, _ + 1, s, s', out, hSteps, hDoneEnd, hNotPost, hReach => by
    cases hSteps with
    | refl _ =>
      cases hReach with
      | inl hD =>
        let ⟨out', hD', hP⟩ := hD
        have hEq := stepV2_deterministic hDoneEnd hD'
        cases hEq
        exact hNotPost hP
      | inr hS =>
        let ⟨_, hS', _⟩ := hS
        have hEq := stepV2_deterministic hDoneEnd hS'
        cases hEq
  | k + 1, b + 1, s, s', out, hSteps, hDoneEnd, hNotPost, hReach => by
    cases hSteps with
    | step hStepS hTail =>
      cases hReach with
      | inl hD =>
        let ⟨_, hD', _⟩ := hD
        have hEq := stepV2_deterministic hStepS hD'
        cases hEq
      | inr hNext =>
        let ⟨s₁, hS₁, hRest⟩ := hNext
        have hEq := stepV2_deterministic hStepS hS₁
        cases hEq
        exact not_reachesDoneWithinV2_of_stepsTo_done_fail hTail hDoneEnd
          hNotPost hRest

/-- If `s` reaches `s'` in `k` `.step` transitions and `s'` faults, then
`ReachesDoneWithinV2 p post bound s` fails for all `bound`. -/
theorem not_reachesDoneWithinV2_of_stepsTo_fault {p : Program}
    {post : TerminalOut → Prop} :
    ∀ {k bound : Nat} {s s' : State} {f : FaultKind},
      StepsToV2 p k s s' →
      StepV2 p s' (.fault f) →
      ¬ ReachesDoneWithinV2 p post bound s
  | _, 0, _, _, _, _, _, h => False.elim h
  | 0, _ + 1, s, s', f, hSteps, hFault, hReach => by
    cases hSteps with
    | refl _ =>
      cases hReach with
      | inl hD =>
        let ⟨_, hD', _⟩ := hD
        have hEq := stepV2_deterministic hFault hD'
        cases hEq
      | inr hS =>
        let ⟨_, hS', _⟩ := hS
        have hEq := stepV2_deterministic hFault hS'
        cases hEq
  | k + 1, b + 1, s, s', f, hSteps, hFault, hReach => by
    cases hSteps with
    | step hStepS hTail =>
      cases hReach with
      | inl hD =>
        let ⟨_, hD', _⟩ := hD
        have hEq := stepV2_deterministic hStepS hD'
        cases hEq
      | inr hNext =>
        let ⟨s₁, hS₁, hRest⟩ := hNext
        have hEq := stepV2_deterministic hStepS hS₁
        cases hEq
        exact not_reachesDoneWithinV2_of_stepsTo_fault hTail hFault hRest

end Anneal.StepBound

end
