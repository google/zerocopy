-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Control.Except
import Miri.Interpreter.ExecutionMachine
import Trusted.MirAst
import Trusted.MirModel
import Trusted.Correspondence.Codec
import Trusted.Correspondence.State
import Trusted.Correspondence.Config

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Reference Step Engine and Trace Predicates (`Trusted.Correspondence.Eval`)

Drives $M_{\text{ref}}$ single-step transitions directly through
`Miri.Interpreter.ExecutionMachine.step` over `refExecutionConfig rp` and
`refLimits`, exposes `RefAllowedStep` via `ExecutionMachine.AllowedStep` (tied
to `RefStep` by `RefStepSoundForAllowedStepClaim`), and defines both aggregate
and choice-coupled reference trace predicates (`RefStep`, `RefReaches`,
`RefReachesOutcome`, `RefWellFormed`, `RefBehavior`, `RefDiverges`,
`RefReachesAtChoices`, `RefValidPrefixAtChoices`, `RefReachesOutcomeAtChoices`,
`RefBehaviorAtChoices`, `RefDivergesAtChoices`). Imports only `Init.*`,
`Miri.*`, `Trusted.MirAst`, `Trusted.MirModel`, and
`Trusted.Correspondence.{Codec,State,Config}`, never `Trusted.MirSemantics`.
-/

/-- Single-step evaluator of $M_{\text{ref}}$: checks the outer step budget
`rs.stepsExecuted < rs.maxSteps` first (returning `.exhaustedStepLimit` when
exhausted) and otherwise executes one MIR statement or terminator directly via
`Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c
rs.miri`:

> "pub fn step(&mut self) -> InterpResult<'tcx, bool> {
>     if self.stack().is_empty() { return interp_ok(false); }
>     ...
>     let basic_block = &self.body().basic_blocks[loc.block];
>     if let Some(stmt) = basic_block.statements.get(loc.statement_index) {
>         self.eval_statement(stmt)?;
>         ...
>         return interp_ok(true);
>     }
>     let terminator = basic_block.terminator();
>     self.eval_terminator(terminator)?;
>     interp_ok(true)
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

- `(miri', .ok true)` with `miri'.stack.frames.isEmpty = true`: the entry
  frame executed `Return`, copied and validated `_0` into `rs.retPlace` inside
  `miri'.machine.memory`, and popped the stack; `refReadReturnVal` decodes the
  returned `Val` from `rs.retPlace` in `miri'.machine.memory`.
- `(miri', .ok true)` with non-empty stack: returns `.running` with `miri'`
  and `stepsExecuted := rs.stepsExecuted + 1`.
- `(_, .error (.undefinedBehavior _))` and `(_, .error (.stack
  (.localExpectedLive _)))`: map to `.ub`.
- All other errors (`.invalidBlock`, `.unsupported`, `.invalidProgram`,
  `.stack .cannotMakeReturnPlaceDead`, etc.) and `(_, .ok false)` map to
  `.blocked`. -/
noncomputable def evalRefStep (rp : RefProg) (c : Choice)
    (rs : RefState) : RefOutcome :=
  if !Nat.blt rs.stepsExecuted rs.maxSteps then
    .exhaustedStepLimit
  else
    match Miri.Interpreter.ExecutionMachine.step
        (refExecutionConfig rp) refLimits c rs.miri with
    | (miri', .ok true) =>
      if miri'.stack.frames.isEmpty then
        match refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace with
        | .ok retVal =>
          .returned (.returned ⟨retVal, miri'.machine.user.callerMem⟩)
        | .error k => faultToRefOutcome k
      else
        .running {
          rs with
          miri := miri'
          stepsExecuted := rs.stepsExecuted + 1
        }
    | (_, .ok false) => .blocked
    | (miri', .error (.termination (.abort _))) =>
      .returned (.aborted miri'.machine.user.callerMem)
    | (_, .error (.undefinedBehavior _)) => .ub
    | (_, .error (.stack (.localExpectedLive _))) => .ub
    | (_, .error _) => .blocked

/-- Reference single-step relation directly instantiating
`Miri.Interpreter.ExecutionMachine.AllowedStep` over `refExecutionConfig rp`
and admissible choices `c = 0`. -/
def RefAllowedStep (rp : RefProg)
    (before after : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (outcome : Except Miri.Interpreter.StepError Bool) : Prop :=
  Miri.Interpreter.ExecutionMachine.AllowedStep
    (refExecutionConfig rp) (fun _ c => c = 0) before after outcome

/-- Relational small-step transition of $M_{\text{ref}}$. -/
def RefStep (rp : RefProg) (rs : RefState)
    (out : RefOutcome) : Prop :=
  ∃ c : Choice, ValidRefChoice rp rs c ∧ evalRefStep rp c rs = out

/-- Unbounded finite-step reachability in $M_{\text{ref}}$, chaining `rs₃` from
`RefStep rp rs₂ (.running rs₃)` unmodified. -/
inductive RefReaches (rp : RefProg) : RefState → RefState → Prop where
  | refl (rs : RefState) : RefReaches rp rs rs
  | tail {rs₁ rs₂ rs₃ : RefState} :
      RefReaches rp rs₁ rs₂ →
      RefStep rp rs₂ (.running rs₃) →
      RefReaches rp rs₁ rs₃

/-- Outcome `out` is reached from `(rp, q)` under step budget `maxSteps`. -/
def RefReachesOutcome (rp : RefProg) (q : Query)
    (maxSteps : Nat) (out : RefOutcome) : Prop :=
  match initRefState rp q maxSteps with
  | .error k => out = faultToRefOutcome k
  | .ok rs₀ => ∃ rs : RefState, RefReaches rp rs₀ rs ∧ RefStep rp rs out

/-- All-prefix well-formedness in $M_{\text{ref}}$: quantifies universally over
all step budgets `maxSteps : Nat`. -/
def RefWellFormed (rp : RefProg) (q : Query) : Prop :=
  ∀ maxSteps : Nat,
    (∃ rs₀ : RefState, initRefState rp q maxSteps = .ok rs₀ ∧
      ∀ rs : RefState, RefReaches rp rs₀ rs →
        ∃ c : Choice, ValidRefChoice rp rs c) ∧
    ¬ RefReachesOutcome rp q maxSteps .ub ∧
    ¬ RefReachesOutcome rp q maxSteps .blocked

/-- Observable terminal behavior in $M_{\text{ref}}$: quantifies existentially
over a sufficient step budget `maxSteps : Nat`. -/
def RefBehavior (rp : RefProg) (q : Query)
    (out : TerminalOut) : Prop :=
  ∃ maxSteps : Nat, RefReachesOutcome rp q maxSteps (.returned out)

/-- Divergence in $M_{\text{ref}}$: initialization succeeds at step budget `0`
with `rs₀`, and there exists an infinite reference execution trace
`trace : Nat → RefState` starting at `trace 0 = rs₀` such that at every step
`n`, executing `trace n` with `stepsExecuted := n` and step budget
`maxSteps := n + 1` transitions via `RefStep` to
`.running { trace (n + 1) with stepsExecuted := n + 1, maxSteps := n + 1 }`. -/
def RefDiverges (rp : RefProg) (q : Query) : Prop :=
  ∃ rs₀ : RefState,
    initRefState rp q 0 = .ok rs₀ ∧
    ∃ trace : Nat → RefState,
      trace 0 = rs₀ ∧
      ∀ n : Nat,
        RefStep rp
          { trace n with stepsExecuted := n, maxSteps := n + 1 }
          (.running
            { trace (n + 1) with
              stepsExecuted := n + 1, maxSteps := n + 1 })

/-! ## Choice-Coupled Reference Trace Predicates -/

/-- Choice-coupled finite-step reachability in $M_{\text{ref}}$ along an
explicit sequence of admissible choices. -/
inductive RefReachesAtChoices (rp : RefProg) :
    RefState → List Choice → RefState → Prop where
  | nil (rs : RefState) : RefReachesAtChoices rp rs [] rs
  | cons {rs₁ rs₂ rs₃ : RefState} {c : Choice} {cs : List Choice} :
      ValidRefChoice rp rs₁ c →
      evalRefStep rp c rs₁ = .running rs₂ →
      RefReachesAtChoices rp rs₂ cs rs₃ →
      RefReachesAtChoices rp rs₁ (c :: cs) rs₃

/-- Admissible finite execution prefix in $M_{\text{ref}}$ along `choices`
under some sufficient step budget `maxSteps`. -/
def RefValidPrefixAtChoices (rp : RefProg) (q : Query)
    (choices : List Choice) : Prop :=
  ∃ maxSteps : Nat, ∃ rs₀ rs : RefState,
    initRefState rp q maxSteps = .ok rs₀ ∧
    RefReachesAtChoices rp rs₀ choices rs

/-- Choice-coupled outcome reachability in $M_{\text{ref}}$ under step budget
`maxSteps`: entry faults consume `choices = []`, while post-entry transitions
consume `prefixChoices ++ [c]`. -/
def RefReachesOutcomeAtChoices (rp : RefProg) (q : Query)
    (choices : List Choice) (maxSteps : Nat) (out : RefOutcome) : Prop :=
  match initRefState rp q maxSteps with
  | .error k => choices = [] ∧ out = faultToRefOutcome k
  | .ok rs₀ =>
    ∃ (prefixChoices : List Choice) (c : Choice) (rs : RefState),
      choices = prefixChoices ++ [c] ∧
      RefReachesAtChoices rp rs₀ prefixChoices rs ∧
      ValidRefChoice rp rs c ∧
      evalRefStep rp c rs = out

/-- Choice-coupled observable terminal behavior in $M_{\text{ref}}$ along
`choices`. -/
def RefBehaviorAtChoices (rp : RefProg) (q : Query)
    (choices : List Choice) (out : TerminalOut) : Prop :=
  ∃ maxSteps : Nat,
    RefReachesOutcomeAtChoices rp q choices maxSteps (.returned out)

/-- Choice-coupled divergence in $M_{\text{ref}}$ along an infinite choice
stream `choiceStream : Nat → Choice`. -/
def RefDivergesAtChoices (rp : RefProg) (q : Query)
    (choiceStream : Nat → Choice) : Prop :=
  ∃ rs₀ : RefState,
    initRefState rp q 0 = .ok rs₀ ∧
    ∃ trace : Nat → RefState,
      trace 0 = rs₀ ∧
      ∀ n : Nat,
        ValidRefChoice rp
          { trace n with stepsExecuted := n, maxSteps := n + 1 }
          (choiceStream n) ∧
        evalRefStep rp (choiceStream n)
          { trace n with stepsExecuted := n, maxSteps := n + 1 } =
          .running
            { trace (n + 1) with
              stepsExecuted := n + 1, maxSteps := n + 1 }

end Trusted.Correspondence
