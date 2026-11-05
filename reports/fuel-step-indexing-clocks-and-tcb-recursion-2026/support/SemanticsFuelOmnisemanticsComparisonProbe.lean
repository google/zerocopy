-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Core

/-!
# Relational Step-Indexing, Functional Fuel, Clocked Big-Step, and Inductive Omnisemantics

Self-contained, `prelude`-only Lean 4.34.1 mechanization comparing four ways of
representing potentially non-terminating operational semantics in a verification
TCB and proof layer:

1. **Relational Step-Indexed Prefixes (`ReachesPrefix`, `Trusted/StepResult.lean`)**:
   Anneal's TCB representation, which uses a `Nat` step counter as an inductive
   index over a small-step relation with propositional demonic choice
   (`StepResult.choice`), silent divergence (`.diverges`), and productive
   reactivity (`.reacts`).
2. **Functional Fuel Evaluators (`evalFuel`)**:
   Deterministic small-step iteration fueled by `Nat`, proven equivalent to
   `ReachesPrefix` on deterministic transitions.
3. **Functional Big-Step / CakeML-Style Clocked Semantics (`evalClocked`)**:
   Big-step evaluation with a loop/call clock `ck : Nat` and `.timeout` (Owens
   et al., ESOP 2016), showing why single-function clocked big-step requires a
   lexicographic measure `(ck, stmt)` (or a two-layer `evalStmtStep` +
   `evalClocked` split in `prelude`), and proving **Clock Monotonicity**
   (`evalClocked_mono`) and divergence characterization
   (`∀ ck, evalClocked ck = .timeout`).
4. **Inductive Omnisemantics (`OmniSem`, Charguéraud et al. TOPLAS 2023) and
   Anneal's `ExecNormal` (`theory/Anneal/Lowering.lean`)**:
   Fuel-free inductive big-step semantics, proving both equivalence to
   `∃ n, ReachesPrefix ... n` and fuel-free backward simulation for
   step-contracting `goto`-chain coalescing (`lowerBody_simulates`).

Every declaration in this file is checked directly by the Lean 4 kernel under
`prelude` with zero `sorry` axioms and zero `Classical.choice` dependencies.
-/

namespace SemanticsFuelOmnisemanticsComparisonProbe

/-!
## Section 1: Anneal's Relational Step-Indexed `ReachesPrefix` (`Trusted/StepResult.lean`)
-/

inductive TerminationKind (Val : Type u) where
  | normal (retVal : Val)
  | unwind
  deriving DecidableEq

inductive StepResult (State : Type u) (Event : Type v) (Val : Type w) where
  | step (events : List Event) (nextState : State)
  | choice (branches : State → Prop)
  | terminated (kind : TerminationKind Val)
  | failed

inductive PrefixOut (State : Type u) (Event : Type v) (Val : Type w) where
  | running (state : State)
  | terminated (kind : TerminationKind Val)
  | failed

def PrefixOut.isSafe : PrefixOut State Event Val → Prop
  | .failed => False
  | _ => True

/-- Relational step-indexed finite prefix execution (`Trusted/StepResult.lean:89-108`). -/
inductive ReachesPrefix {Prog : Type x} {State : Type u} {Event : Type v}
    {Val : Type w}
    (step : Prog → State → StepResult State Event Val → Prop) (prog : Prog) :
    Nat → State → List Event → PrefixOut State Event Val → Prop where
  | zero (s : State) :
      ReachesPrefix step prog 0 s [] (.running s)
  | step {n : Nat} {s s' : State} {ev1 ev2 : List Event}
      {out : PrefixOut State Event Val} :
      step prog s (.step ev1 s') →
      ReachesPrefix step prog n s' ev2 out →
      ReachesPrefix step prog (n + 1) s (ev1 ++ ev2) out
  | choice {n : Nat} {s s' : State} {branches : State → Prop}
      {ev : List Event} {out : PrefixOut State Event Val} :
      step prog s (.choice branches) →
      branches s' →
      ReachesPrefix step prog n s' ev out →
      ReachesPrefix step prog (n + 1) s ev out
  | terminated {n : Nat} {s : State} {k : TerminationKind Val} :
      step prog s (.terminated k) →
      ReachesPrefix step prog (n + 1) s [] (.terminated k)
  | failed {n : Nat} {s : State} :
      step prog s .failed →
      ReachesPrefix step prog (n + 1) s [] .failed

inductive EventualOut (Event : Type v) (Val : Type w) where
  | terminated (trace : List Event) (kind : TerminationKind Val)
  | diverges (trace : List Event)
  | reacts (trace : Nat → Event)
  | failed

def EventualOut.isSafe : EventualOut Event Val → Prop
  | .failed => False
  | _ => True

def EventualOut.isProductive : EventualOut Event Val → Prop
  | .terminated _ _ => True
  | .diverges _ => True
  | .reacts _ => True
  | .failed => False

/-- Coinduction-free eventual behavior relation (`Trusted/StepResult.lean:119-149`). -/
def eventualBehaviorOf {Prog : Type x} {State : Type u} {Event : Type v}
    {Val : Type w}
    (step : Prog → State → StepResult State Event Val → Prop)
    (prog : Prog) (init : State) (out : EventualOut Event Val) : Prop :=
  match out with
  | .terminated trace kind =>
    ∃ steps : Nat,
      ReachesPrefix step prog steps init trace (.terminated kind)
  | .failed =>
    ∃ steps : Nat, ∃ trace : List Event,
      ReachesPrefix step prog steps init trace .failed
  | .diverges trace =>
    ∃ traj : Nat → State,
      (∃ steps : Nat,
        ReachesPrefix step prog steps init trace (.running (traj 0))) ∧
      (∀ k : Nat,
        ∃ n : Nat,
          ReachesPrefix step prog (n + 1) (traj k) [] (.running (traj (k + 1))))
  | .reacts infTrace =>
    ∃ (traj : Nat → State) (segSteps : Nat → Nat) (segEvent : Nat → Event),
      traj 0 = init ∧
      infTrace = segEvent ∧
      (∀ k : Nat,
        ReachesPrefix step prog (segSteps k + 1) (traj k) [segEvent k]
          (.running (traj (k + 1))))

/-!
### 1.1 Proving Infinite-Loop Safety Without Coinductive Types

Consider a program whose transition relation always steps silently from `s` to
`s` (`r = .step [] s`). We prove that:
1. Every finite prefix `ReachesPrefix` of any length `n : Nat` is `.running s`
   (and therefore never `.failed`), and
2. `eventualBehaviorOf` produces `.diverges []` (making the loop both safe and
   productive under `prelude` without coinductive types).
-/

def silentLoopStep (_prog : Unit) (s : Nat)
    (r : StepResult Nat Empty Unit) : Prop :=
  r = .step [] s

theorem silentLoop_reaches_running (n : Nat) :
    ∀ (s : Nat) (tr : List Empty) (out : PrefixOut Nat Empty Unit),
      ReachesPrefix silentLoopStep () n s tr out →
      tr = [] ∧ out = .running s := by
  induction n with
  | zero =>
    intro s tr out h
    cases h
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro s tr out h
    cases h with
    | @step _ _ s' _ _ _ hstep hrest =>
      dsimp [silentLoopStep] at hstep
      injection hstep with hev hs'
      subst hev
      subst hs'
      have ⟨htr, hout⟩ := ih s' _ out hrest
      subst htr
      exact ⟨rfl, hout⟩
    | choice hstep => cases hstep
    | terminated hstep => cases hstep
    | failed hstep => cases hstep

/-- **Theorem (Silent Infinite Loop Never Faults and Admits `.diverges []`):** -/
theorem silentLoop_safe_and_diverges (init : Nat) :
    (∀ out, eventualBehaviorOf silentLoopStep () init out → out.isSafe) ∧
    eventualBehaviorOf silentLoopStep () init (.diverges []) := by
  refine ⟨?_, ?_⟩
  · intro out hev
    cases out with
    | terminated _ _ => trivial
    | diverges _ => trivial
    | reacts _ => trivial
    | failed =>
      cases hev with
      | intro steps htr =>
        cases htr with
        | intro tr hreach =>
          have ⟨_, hout⟩ := silentLoop_reaches_running steps init tr .failed hreach
          cases hout
  · refine ⟨fun _ => init, ⟨0, ReachesPrefix.zero init⟩, fun _ => ⟨0, ?_⟩⟩
    exact ReachesPrefix.step (ev1 := []) (ev2 := []) rfl (ReachesPrefix.zero init)

/-!
### 1.2 Demonic Non-Determinism (`StepResult.choice`) Refutes Unsafe Branches

When `StepResult.choice` branches to both a safe state (`1`) and a faulting
state (`2`), `eventualBehaviorOf` includes `.failed`, so universal safety over
`eventualBehaviorOf` rejects the program cleanly.
-/

def demonicBranches (s' : Nat) : Prop :=
  s' = 1 ∨ s' = 2

def demonicStep (_prog : Unit) (s : Nat)
    (r : StepResult Nat Empty Unit) : Prop :=
  (s = 0 ∧ r = .choice demonicBranches) ∨
  (s = 1 ∧ r = .terminated (.normal ())) ∨
  (s = 2 ∧ r = .failed)

theorem demonicStep_reaches_failed :
    eventualBehaviorOf demonicStep () 0 .failed := by
  refine ⟨2, [], ?_⟩
  exact ReachesPrefix.choice (s' := 2) (Or.inl ⟨rfl, rfl⟩) (Or.inr rfl)
    (ReachesPrefix.failed (n := 0) (Or.inr (Or.inr ⟨rfl, rfl⟩)))

/-!
## Section 2: Functional Fuel Evaluator (`evalFuel`) vs. Relational `ReachesPrefix`

For a **deterministic** step function `stepFn : State → StepResultDet State Val`,
we define a functional fuel-based evaluator `evalFuel` and prove exact
equivalence with `ReachesPrefix`.
-/

inductive StepResultDet (State : Type u) (Val : Type w) where
  | step (nextState : State)
  | terminated (kind : TerminationKind Val)
  | failed

def StepResultDet.toStepResult :
    StepResultDet State Val → StepResult State Empty Val
  | .step s' => .step [] s'
  | .terminated k => .terminated k
  | .failed => .failed

/-- Functional fuel-based small-step evaluator. -/
def evalFuel (stepFn : State → StepResultDet State Val) :
    Nat → State → PrefixOut State Empty Val
  | 0, s => .running s
  | fuel + 1, s =>
    match stepFn s with
    | .step s' => evalFuel stepFn fuel s'
    | .terminated k => .terminated k
    | .failed => .failed

def detRel (stepFn : State → StepResultDet State Val) (_prog : Unit)
    (s : State) (r : StepResult State Empty Val) : Prop :=
  r = (stepFn s).toStepResult

/-- **Theorem (`evalFuel` Completeness w.r.t. `ReachesPrefix`):** -/
theorem evalFuel_to_reachesPrefix (stepFn : State → StepResultDet State Val)
    (n : Nat) (s : State) :
    ReachesPrefix (detRel stepFn) () n s [] (evalFuel stepFn n s) := by
  induction n generalizing s with
  | zero => exact ReachesPrefix.zero s
  | succ k ih =>
    dsimp [evalFuel]
    cases hstep : stepFn s with
    | step s' =>
      have hrel : detRel stepFn () s (.step [] s') := by
        dsimp [detRel]; rw [hstep]; rfl
      exact ReachesPrefix.step (ev1 := []) (ev2 := []) hrel (ih s')
    | terminated kind =>
      have hrel : detRel stepFn () s (.terminated kind) := by
        dsimp [detRel]; rw [hstep]; rfl
      exact ReachesPrefix.terminated hrel
    | failed =>
      have hrel : detRel stepFn () s .failed := by
        dsimp [detRel]; rw [hstep]; rfl
      exact ReachesPrefix.failed hrel

/-- **Theorem (`evalFuel` Soundness w.r.t. `ReachesPrefix`):** -/
theorem reachesPrefix_to_evalFuel (stepFn : State → StepResultDet State Val)
    (n : Nat) :
    ∀ (s : State) (tr : List Empty) (out : PrefixOut State Empty Val),
      ReachesPrefix (detRel stepFn) () n s tr out →
      tr = [] ∧ out = evalFuel stepFn n s := by
  induction n with
  | zero =>
    intro s tr out h
    cases h
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro s tr out h
    dsimp [evalFuel]
    cases h with
    | @step _ _ s_next ev1 ev2 _ hrel hrest =>
      dsimp [detRel] at hrel
      cases hfn : stepFn s with
      | step s' =>
        rw [hfn] at hrel
        injection hrel with hev hs'
        subst hev; subst hs'
        exact ih s_next ev2 out hrest
      | terminated _ => rw [hfn] at hrel; cases hrel
      | failed => rw [hfn] at hrel; cases hrel
    | choice hrel =>
      dsimp [detRel] at hrel
      cases hfn : stepFn s <;> (rw [hfn] at hrel; cases hrel)
    | terminated hrel =>
      dsimp [detRel] at hrel
      cases hfn : stepFn s with
      | step _ => rw [hfn] at hrel; cases hrel
      | terminated kind =>
        rw [hfn] at hrel
        injection hrel with hk
        subst hk
        exact ⟨rfl, rfl⟩
      | failed => rw [hfn] at hrel; cases hrel
    | failed hrel =>
      dsimp [detRel] at hrel
      cases hfn : stepFn s with
      | step _ => rw [hfn] at hrel; cases hrel
      | terminated _ => rw [hfn] at hrel; cases hrel
      | failed => exact ⟨rfl, rfl⟩

/-!
## Section 3: Functional Big-Step Semantics / CakeML-Style Clocked Evaluator

In Functional Big-Step Semantics (Owens, Myreen, Kumar, Tan, ESOP 2016), an
evaluator is written in big-step style over syntax, carrying a clock `ck : Nat`
that is decremented **only** on loop unrollings / recursive calls and returns
`.timeout` when `ck = 0`.

Crucially, a naive single-function `evalClocked (ck : Nat) (stmt : Stmt)` is
**lexicographically** recursive on `(ck, stmt)` (since `.seq s1 s2` preserves
`ck` while shrinking `stmt`, whereas `.whileNonZero body` shrinks `ck` while
preserving `.whileNonZero body`). In a `prelude`-only TCB without lexicographic
`WellFounded.fix`, the exact same two-layer structural/fuel decomposition used
in `Trusted/MirSemantics.lean` (`validStep` + `validFuel`) makes clocked
big-step evaluation purely structural:
1. `evalStmtStep`: structural recursion on `stmt : Stmt` (0 clock ticks on
   `.seq`, `.skip`, `.incr`, `.assertPos`), and
2. `evalClocked`: structural recursion on `ck : Nat` (1 clock tick per loop
   iteration).
-/

inductive Stmt where
  | skip
  | incr
  | assertPos
  | seq (s1 s2 : Stmt)
  | whileNonZero (body : Stmt)

inductive ClockOut (State : Type u) where
  | done (s : State)
  | timeout
  | fault
  deriving DecidableEq

/-- Inner structural recursion on `Stmt` (`0` clock ticks on `.seq`). -/
def evalStmtStep (loopStep : Stmt → Nat → ClockOut Nat) :
    Stmt → Nat → ClockOut Nat
  | .skip, s => .done s
  | .incr, s => .done (s + 1)
  | .assertPos, s => if Nat.beq s 0 then .fault else .done s
  | .seq s1 s2, s =>
    match evalStmtStep loopStep s1 s with
    | .done s' => evalStmtStep loopStep s2 s'
    | .timeout => .timeout
    | .fault => .fault
  | .whileNonZero body, s =>
    if Nat.beq s 0 then
      .done s
    else
      match evalStmtStep loopStep body s with
      | .done s' => loopStep (.whileNonZero body) s'
      | .timeout => .timeout
      | .fault => .fault

/-- Outer structural recursion on `ck : Nat` (`1` clock tick per loop back-edge). -/
def evalClocked : Nat → Stmt → Nat → ClockOut Nat
  | 0, _, _ => .timeout
  | ck + 1, stmt, s => evalStmtStep (evalClocked ck) stmt s

/-- Monotonicity of `evalStmtStep` with respect to its loop continuation. -/
theorem evalStmtStep_mono (loop1 loop2 : Stmt → Nat → ClockOut Nat)
    (hloop : ∀ stmt s out, loop1 stmt s = out → out ≠ .timeout →
      loop2 stmt s = out)
    (stmt : Stmt) :
    ∀ (s : Nat) (out : ClockOut Nat),
      evalStmtStep loop1 stmt s = out →
      out ≠ .timeout →
      evalStmtStep loop2 stmt s = out := by
  induction stmt with
  | skip =>
    intro s out heval _
    exact heval
  | incr =>
    intro s out heval _
    exact heval
  | assertPos =>
    intro s out heval _
    exact heval
  | seq s1 s2 ih1 ih2 =>
    intro s out heval hnot
    dsimp [evalStmtStep] at heval ⊢
    revert heval
    cases h1 : evalStmtStep loop1 s1 s with
    | done s' =>
      intro heval
      rw [ih1 s (.done s') h1 (by intro h; cases h)]
      exact ih2 s' out heval hnot
    | timeout =>
      intro heval
      exact False.elim (hnot heval.symm)
    | fault =>
      intro heval
      rw [ih1 s .fault h1 (by intro h; cases h)]
      exact heval
  | whileNonZero body ihBody =>
    intro s out heval hnot
    dsimp [evalStmtStep] at heval ⊢
    cases hzero : Nat.beq s 0 with
    | true =>
      rw [hzero] at heval
      exact heval
    | false =>
      rw [hzero] at heval
      dsimp at heval ⊢
      revert heval
      cases hbody : evalStmtStep loop1 body s with
      | done s' =>
        intro heval
        rw [ihBody s (.done s') hbody (by intro h; cases h)]
        exact hloop (.whileNonZero body) s' out heval hnot
      | timeout =>
        intro heval
        exact False.elim (hnot heval.symm)
      | fault =>
        intro heval
        rw [ihBody s .fault hbody (by intro h; cases h)]
        exact heval

/-- **Theorem (Clock Monotonicity — Owens et al. ESOP 2016):**
    Once `evalClocked ck stmt s` produces a non-timeout outcome (`.done s'` or
    `.fault`), increasing the clock to `ck + extra` preserves the exact same
    outcome! -/
theorem evalClocked_mono (ck extra : Nat) :
    ∀ (stmt : Stmt) (s : Nat) (out : ClockOut Nat),
      evalClocked ck stmt s = out →
      out ≠ .timeout →
      evalClocked (ck + extra) stmt s = out := by
  induction ck with
  | zero =>
    intro stmt s out heval hnot
    exact False.elim (hnot heval.symm)
  | succ k ih =>
    intro stmt s out heval hnot
    have hsucc : (k + 1) + extra = (k + extra) + 1 :=
      Nat.succ_add k extra
    rw [hsucc]
    dsimp [evalClocked] at heval ⊢
    exact evalStmtStep_mono (evalClocked k) (evalClocked (k + extra))
      ih stmt s out heval hnot

/-- **Theorem (Divergence as Universal Timeout in Clocked Semantics):**
    For the infinite loop `while s != 0 { skip }` starting at `s = 1`, every
    clock `ck : Nat` returns `.timeout` (and never `.fault`). -/
theorem whileSkip_diverges_all_clocks (ck : Nat) :
    evalClocked ck (.whileNonZero .skip) 1 = .timeout := by
  induction ck with
  | zero => rfl
  | succ k ih =>
    dsimp [evalClocked, evalStmtStep]
    exact ih

/-!
## Section 4: Inductive Omnisemantics (`OmniSem`) and Anneal's `ExecNormal` (`theory/Anneal/Lowering.lean`)

Charguéraud et al. (TOPLAS 2023) observed that a single **inductive** predicate
`OmniSem step s Q` (meaning: starting from `s`, every nondeterministic path
terminates safely in a state satisfying postcondition `Q`) captures both safety
and total correctness for terminating executions **without fuel, clocks, or
coinduction**.

In `theory/Anneal/Lowering.lean:34-44`, Anneal uses `ExecNormal`, the
deterministic specialization of inductive omnisemantics, to prove compiler
lowering simulations (`lowerBody_simulates`, `Lowering.lean:535-605`) where
`goto`-chain coalescing contracts multiple small steps into one step.
-/

/-- Inductive Omnisemantics over `StepResult`: a single derivation tree proves
    that all nondeterministic execution paths from `s` terminate normally at a
    value satisfying `post : Val → Prop`, with **zero step counters**. -/
inductive OmniSem {Prog : Type x} {State : Type u} {Event : Type v}
    {Val : Type w}
    (step : Prog → State → StepResult State Event Val → Prop)
    (prog : Prog) (post : Val → Prop) : State → Prop where
  | terminated {s : State} {v : Val} :
      step prog s (.terminated (.normal v)) →
      post v →
      OmniSem step prog post s
  | step {s s' : State} {ev : List Event} :
      step prog s (.step ev s') →
      OmniSem step prog post s' →
      OmniSem step prog post s
  | choice {s : State} {branches : State → Prop} :
      step prog s (.choice branches) →
      (∃ s0, branches s0) →
      (∀ s', branches s' → OmniSem step prog post s') →
      OmniSem step prog post s

/-- Anneal's fuel-free inductive execution relation `ExecNormal`
    (`theory/Anneal/Lowering.lean:34-44`) for deterministic transitions. -/
inductive ExecNormal (stepFn : State → StepResultDet State Val) :
    State → Val → Prop where
  | term {s : State} {v : Val} :
      stepFn s = .terminated (.normal v) →
      ExecNormal stepFn s v
  | step {s s' : State} {v : Val} :
      stepFn s = .step s' →
      ExecNormal stepFn s' v →
      ExecNormal stepFn s v

theorem evalFuel_to_execNormal (stepFn : State → StepResultDet State Val)
    (n : Nat) :
    ∀ (s : State) (v : Val),
      evalFuel stepFn n s = .terminated (.normal v) →
      ExecNormal stepFn s v := by
  induction n with
  | zero =>
    intro s v h
    cases h
  | succ k ih =>
    intro s v h
    dsimp [evalFuel] at h
    revert h
    cases hfn : stepFn s with
    | step s' =>
      intro h
      exact ExecNormal.step hfn (ih s' v h)
    | terminated kind =>
      intro h
      injection h with hk
      subst hk
      exact ExecNormal.term hfn
    | failed =>
      intro h
      cases h

/-- **Theorem (`ExecNormal` Soundness & Completeness w.r.t. `ReachesPrefix`):**
    `ExecNormal stepFn s v` holds if and only if there exists a step bound
    `n : Nat` such that `ReachesPrefix` reaches `.terminated (.normal v)`. -/
theorem execNormal_iff_exists_reachesPrefix
    (stepFn : State → StepResultDet State Val) (s : State) (v : Val) :
    ExecNormal stepFn s v ↔
      ∃ n : Nat,
        ReachesPrefix (detRel stepFn) () n s [] (.terminated (.normal v)) := by
  constructor
  · intro hexec
    induction hexec with
    | term hterm =>
      refine ⟨1, ReachesPrefix.terminated (n := 0) ?_⟩
      dsimp [detRel]
      rw [hterm]
      rfl
    | step hstep _ ih =>
      cases ih with
      | intro n hreach =>
        refine ⟨n + 1, ReachesPrefix.step (ev1 := []) (ev2 := []) ?_ hreach⟩
        dsimp [detRel]
        rw [hstep]
        rfl
  · intro hex
    cases hex with
    | intro n hreach =>
      have ⟨_, heval⟩ := reachesPrefix_to_evalFuel stepFn n s []
        (.terminated (.normal v)) hreach
      exact evalFuel_to_execNormal stepFn n s v heval.symm

/-!
### 4.1 Step-Contracting Compiler Lowering (`goto`-Chain Coalescing)

Why does `theory/Anneal/Lowering.lean` prove `lowerBody_simulates` over
`ExecNormal` rather than directly over `ReachesPrefix ... (n : Nat)`?

When a compiler pass coalesces a 2-step `goto` chain `bb0 -> bb1 -> bb2` into a
1-step jump `bb0 -> bb2`, one step in the lowered program corresponds to **two**
steps in the source program. In a step-indexed relation `ReachesPrefix ... n`,
the step index `n` is not preserved (`n` lowered steps become `n' ≥ n` source
steps). In `ExecNormal`, step counts are erased into the inductive derivation,
so one lowered `.step` simply unfolds into two `ExecNormal.step` constructors!
-/

inductive CfgInstr where
  | goto (target : Nat)
  | ret (val : Nat)

def cfgStep (code : Nat → Option CfgInstr) (pc : Nat) :
    StepResultDet Nat Nat :=
  match code pc with
  | some (.goto target) => .step target
  | some (.ret v) => .terminated (.normal v)
  | none => .failed

/-- One-hop `goto` coalescing: if `pc` jumps to `mid`, and `mid` immediately
    jumps to `dst`, coalesce `pc` to jump directly to `dst`. -/
def coalesceGoto (code : Nat → Option CfgInstr) (pc : Nat) :
    Option CfgInstr :=
  match code pc with
  | some (.goto mid) =>
    match code mid with
    | some (.goto dst) => some (.goto dst)
    | _ => some (.goto mid)
  | other => other

/-- **Theorem (Fuel-Free Backward Simulation of `goto` Coalescing via `ExecNormal`):**
    Any terminating execution of `coalesceGoto code` is a valid execution of
    `code`, proved by direct structural induction on `ExecNormal` with **zero
    step-counter arithmetic**. -/
theorem coalesceGoto_simulates_execNormal (code : Nat → Option CfgInstr)
    (pc v : Nat)
    (h : ExecNormal (cfgStep (coalesceGoto code)) pc v) :
    ExecNormal (cfgStep code) pc v := by
  induction h with
  | @term pc_term v_term hterm =>
    dsimp [cfgStep, coalesceGoto] at hterm
    revert hterm
    cases hcode : code pc_term with
    | none => intro h; cases h
    | some instr =>
      cases instr with
      | ret val =>
        intro hterm
        dsimp at hterm
        injection hterm with hkind
        injection hkind with hval
        subst hval
        exact ExecNormal.term (by dsimp [cfgStep]; rw [hcode])
      | goto mid =>
        dsimp
        cases code mid with
        | none => intro h; cases h
        | some midInstr =>
          cases midInstr <;> (intro h; cases h)
  | @step pc_cur pc_next v_res hstep _ ih =>
    dsimp [cfgStep, coalesceGoto] at hstep
    revert hstep
    cases hcode : code pc_cur with
    | none => intro h; cases h
    | some instr =>
      cases instr with
      | ret _ => intro h; cases h
      | goto mid =>
        dsimp
        cases hmid : code mid with
        | none =>
          intro hstep
          dsimp at hstep
          injection hstep with hnext
          subst hnext
          exact ExecNormal.step (by dsimp [cfgStep]; rw [hcode]) ih
        | some midInstr =>
          cases midInstr with
          | ret _ =>
            intro hstep
            dsimp at hstep
            injection hstep with hnext
            subst hnext
            exact ExecNormal.step (by dsimp [cfgStep]; rw [hcode]) ih
          | goto dst =>
            intro hstep
            dsimp at hstep
            injection hstep with hnext
            subst hnext
            -- The 1-step coalesced jump `pc_cur -> dst` expands into TWO
            -- uncoalesced steps `pc_cur -> mid -> dst` with zero arithmetic!
            exact ExecNormal.step (by dsimp [cfgStep]; rw [hcode])
              (ExecNormal.step (by dsimp [cfgStep]; rw [hmid]) ih)

/-- **Theorem (Step-Dilated Simulation on `ReachesPrefix` Recovered via `ExecNormal`):**
    Bridging `coalesceGoto_simulates_execNormal` through
    `execNormal_iff_exists_reachesPrefix` recovers the step-indexed backward
    simulation (`n` steps in `coalesceGoto code` simulate in `∃ n', n'` steps
    in `code`) without ever performing arithmetic on `n` during the CFG case
    split! -/
theorem coalesceGoto_simulates_reachesPrefix_dilated
    (code : Nat → Option CfgInstr) (n pc v : Nat)
    (h : ReachesPrefix (detRel (cfgStep (coalesceGoto code))) () n pc []
      (.terminated (.normal v))) :
    ∃ n' : Nat,
      ReachesPrefix (detRel (cfgStep code)) () n' pc []
        (.terminated (.normal v)) := by
  have hexec := (execNormal_iff_exists_reachesPrefix
    (cfgStep (coalesceGoto code)) pc v).mpr ⟨n, h⟩
  exact (execNormal_iff_exists_reachesPrefix (cfgStep code) pc v).mp
    (coalesceGoto_simulates_execNormal code pc v hexec)

end SemanticsFuelOmnisemanticsComparisonProbe
