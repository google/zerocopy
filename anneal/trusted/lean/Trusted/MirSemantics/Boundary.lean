-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
module
prelude
public import Init.NotationExtra
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.State
public import Trusted.MirSemantics.Step

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Outer Theorem-Stating Boundary (`Trusted.MirSemantics.Boundary`)

Execution predicates (`Step`, `Reaches`, `ReachesResult`, `WellFormed`,
`Behavior`, `Diverges`, `SatisfiesPost`) and top-level verification judgments
(`BodyVerified`, `Specs`, `Crate`, `ProgramVerified`, `CrateTheorem`,
`UnitTheorem`). Isolated from step-rule submodules so changes to the outer
human-audited theorem boundary stay diff-isolated from evolving operational
rules.
-/

/-- Relational small-step transition quantifying over admissible demonic
choices. -/
noncomputable def Step (p : Program) (s : State)
    (res : StepResult State TerminalOut) : Prop :=
  ∃ c : Choice, ValidChoice p s c ∧ evalStep p c s = res

/-- Unbounded finite-step reachability of intermediate states from `s₁` to
`s₂`. -/
inductive Reaches (p : Program) : State → State → Prop where
  | refl (s : State) : Reaches p s s
  | tail {s₁ s₂ s₃ : State} :
      Reaches p s₁ s₂ →
      Step p s₂ (.step s₃) →
      Reaches p s₁ s₃

/-- Outcome `res` is reached from `(p, q)` (either at entry via
`initState p q = .error k` or in finitely many steps from `s₀` when
`initState p q = .ok s₀`). -/
noncomputable def ReachesResult (p : Program) (q : Query)
    (res : StepResult State TerminalOut) : Prop :=
  match initState p q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : State, Reaches p s₀ s ∧ Step p s res

/-- All-prefix well-formedness in $M_{\text{anneal}}$:
1. `initState p q = .ok s₀` and every reachable state has at least one
   admissible choice (`ValidChoice p s c`), preventing vacuous demonic choice;
   and
2. No reachable step (including `initState`) faults with `.undefined` or
   `.unsupported`. -/
noncomputable def WellFormed (p : Program) (q : Query) : Prop :=
  (∃ s₀ : State, initState p q = .ok s₀ ∧
    ∀ s : State, Reaches p s₀ s → ∃ c : Choice, ValidChoice p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResult p q (.fault k))

/-- Observable terminal behavior of `(p, q)` in $M_{\text{anneal}}$. -/
noncomputable def Behavior (p : Program) (q : Query) (out : TerminalOut) :
    Prop :=
  ReachesResult p q (.done out)

/-- Divergence of `(p, q)` in $M_{\text{anneal}}$: from the initial state `s₀`,
there exists a single coherent infinite execution trace `trace : Nat → State`
starting at `s₀` (`trace 0 = s₀`) in which every transition
`trace n → trace (n + 1)` is a valid non-terminating step.

`Behavior` and `ReachesResult` describe only finite executions that stop, so
two semantics with the same finite outcomes could still differ in whether an
execution runs forever. `Diverges` makes non-termination observable alongside
finite outcomes so downstream equivalence proofs can relate both. -/
noncomputable def Diverges (p : Program) (q : Query) : Prop :=
  ∃ s₀ : State,
    initState p q = .ok s₀ ∧
    ∃ trace : Nat → State,
      trace 0 = s₀ ∧
      ∀ n : Nat, Step p (trace n) (.step (trace (n + 1)))

/-- Universal partial-correctness contract satisfaction in
$M_{\text{anneal}}$. -/
noncomputable def SatisfiesPost (p : Program) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  WellFormed p q ∧ ∀ out : TerminalOut, Behavior p q out → post out

/-!
## Choice-Coupled Execution Predicates

Choice-indexed versions of reachability, finite prefix admissibility, outcome
reachability, terminal behavior, and divergence in $M_{\text{anneal}}$. These
predicates couple each step's demonic choice `c : Choice` across finite choice
lists `choices : List Choice` and infinite choice streams
`choiceStream : Nat → Choice` so correspondence proofs prevent cross-branch
outcome permutation when nondeterministic choices are introduced.
-/

/-- Choice-coupled finite-step reachability in $M_{\text{anneal}}$ along an
explicit sequence of admissible demonic choices. -/
inductive ReachesAtChoices (p : Program) :
    State → List Choice → State → Prop where
  | nil (s : State) : ReachesAtChoices p s [] s
  | cons {s₁ s₂ s₃ : State} {c : Choice} {cs : List Choice} :
      ValidChoice p s₁ c →
      evalStep p c s₁ = .step s₂ →
      ReachesAtChoices p s₂ cs s₃ →
      ReachesAtChoices p s₁ (c :: cs) s₃

/-- Admissible finite execution prefix in $M_{\text{anneal}}$ along `choices`,
including prefixes that stop before terminating or faulting. -/
def ValidPrefixAtChoices (p : Program) (q : Query)
    (choices : List Choice) : Prop :=
  ∃ s₀ s : State,
    initState p q = .ok s₀ ∧ ReachesAtChoices p s₀ choices s

/-- Choice-coupled outcome reachability in $M_{\text{anneal}}$: entry faults
consume `choices = []`, while post-entry transitions consume `prefixChoices ++
[c]`. -/
def ReachesResultAtChoices (p : Program) (q : Query)
    (choices : List Choice) (res : StepResult State TerminalOut) : Prop :=
  match initState p q with
  | .error k => choices = [] ∧ res = .fault k
  | .ok s₀ =>
    ∃ (prefixChoices : List Choice) (c : Choice) (s : State),
      choices = prefixChoices ++ [c] ∧
      ReachesAtChoices p s₀ prefixChoices s ∧
      ValidChoice p s c ∧
      evalStep p c s = res

/-- Choice-coupled observable terminal behavior of `(p, q)` in
$M_{\text{anneal}}$. -/
def BehaviorAtChoices (p : Program) (q : Query)
    (choices : List Choice) (out : TerminalOut) : Prop :=
  ReachesResultAtChoices p q choices (.done out)

/-- Choice-coupled divergence of `(p, q)` in $M_{\text{anneal}}$ along an
infinite choice stream `choiceStream : Nat → Choice`. -/
def DivergesAtChoices (p : Program) (q : Query)
    (choiceStream : Nat → Choice) : Prop :=
  ∃ s₀ : State,
    initState p q = .ok s₀ ∧
    ∃ trace : Nat → State,
      trace 0 = s₀ ∧
      ∀ n : Nat,
        ValidChoice p (trace n) (choiceStream n) ∧
        evalStep p (choiceStream n) (trace n) = .step (trace (n + 1))

/-!
## Multi-Body Program, Crate, and Proof-Unit Verification Judgments

The definitions below state the top-level per-body (`BodyVerified`),
program-wide (`ProgramVerified`), and captured-artifact (`CrateTheorem` and
`UnitTheorem`) obligations targeted by Anneal's verification pipeline.

Explicit semantic scoping notes for human auditors:
1. **Value-only entry memory (`callerMem = ⟨[]⟩`):** `BodyVerified` and
   `Specs.safety` quantify over value arguments `args : List Val` paired with
   empty caller memory `{ args := args, callerMem := ⟨[]⟩ }`, matching
   `initState`'s rejection of non-empty `callerMem` while pointer and reference
   entry parameters remain outside the supported domain.
2. **Interprocedural calls fail closed:** `entryProgForBody p defId` retains
   `p.bodies` so the program environment carries all sibling definitions, while
   any reachable `TerminatorKind.call` steps to `.fault .unsupported` and
   therefore refutes `WellFormed` fail-closed.
3. **Fault-freedom vs. termination (`WellFormed` vs. `Diverges`):**
   `WellFormed` establishes absence of `.fault .undefined` (UB) and
   `.fault .unsupported` (unmodeled constructs) across all executions while
   permitting infinite loops (`Diverges`); termination or functional
   input-output contracts are expressed in `Specs.property`.
4. **Whole-crate completeness is an external producer obligation:**
   `CrateTheorem` checks `c.program.scope = .crate` and `ProgramVerified` over
   every body in `c.program.bodies`. Guaranteeing that `c.program.bodies`
   actually includes every executable body and reachable callee in the compiled
   crate is an external obligation of the capture producer (such as a future
   `anneal-rustc-capture` emitter), not checked by `Trusted.MirSemantics`
   alone. -/

/-- Override `entryDefId` of `p` to execute body `defId` as the root function in
`initState` / `WellFormed` / `Behavior`. -/
noncomputable def entryProgForBody (p : Program) (defId : DefId) : Program :=
  { p with entryDefId := defId }

/-- Check that `args` matches the parameter types `locals[1..=argumentCount]` of
`body` in length and well-formed `Val.ty?`. -/
noncomputable def ValidEntryArgs (body : Body) (args : List Val) : Prop :=
  checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) = true

/-- Check that all bodies in `bodies` carry non-empty, pairwise-distinct
`identity` keys so two functions can never collide in `Specs.safety`. Uses a
single pass over `bodies` into a balanced Red-Black Tree (`IdentityRbTree`) so
crate-scale captures stay $O(N \log N)$ and shallow within Lean's default
`maxRecDepth`. -/
noncomputable def bodiesHaveUniqueIdentities (bodies : List Body) : Bool :=
  bodiesHaveUniqueIdentitiesAux bodies .empty

/-- Unconditional static admission predicate for `(p, body)`: checks 64-bit
target layout, MIR semantic profile version 1, non-empty `body.identity`,
non-empty basic blocks, `argumentCount < locals.length`, in-bounds storage
annotations, well-typed `Discriminant` and `Cast` destinations, and supported
local types
(`isSupportedScalarOrUnitTy`) even when `body` has uninhabited (`MirTy.never`)
parameters and `ValidEntryArgs body args` is vacuously empty. -/
noncomputable def BodyStaticAdmitted (p : Program) (body : Body) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    !stringIsEmpty body.identity &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    discriminantTypesValid body &&
    castTypesValid body &&
    body.locals.all isSupportedScalarOrUnitTy

/-- Verification judgment for a single MIR function body `body` at index `defId`
in `p`:
1. `getElem? p.bodies defId = some body` binds `body` to the indexed function
   body in `p` (preventing callers from passing an unrelated `body`—such as an
   uninhabited `MirTy.never`-parameter stub—while executing `p.bodies[defId]`);
2. `BodyStaticAdmitted p body = true` holds unconditionally (independent of
   whether `ValidEntryArgs body args` is inhabited); and
3. For every well-typed argument list `args` (with empty `callerMem := ⟨[]⟩`),
   assuming `safetyPre args` only when `body.isUnsafe = true`, executing
   `entryProgForBody p defId` on `{ args := args }` is `WellFormed` (never
   reaches `.fault .undefined` or `.fault .unsupported`; non-terminating loops
   remain permitted unless ruled out by `Specs.property`). -/
noncomputable def BodyVerified (p : Program) (defId : DefId) (body : Body)
    (safetyPre : List Val → Prop) : Prop :=
  getElem? p.bodies defId = some body ∧
  BodyStaticAdmitted p body = true ∧
  ∀ args : List Val,
    ValidEntryArgs body args →
    (body.isUnsafe = true → safetyPre args) →
    WellFormed (entryProgForBody p defId) { args := args }

/-- Specification bundle for a captured MIR crate or proof unit:
- `safety identity args`: caller-obligation safety precondition (over value
  arguments `args` with `callerMem = ⟨[]⟩`) for an `unsafe` function with
  canonical path `identity` (ignored on safe functions, where
  `body.isUnsafe = false`);
- `property p`: functional correctness or termination specification over `p`. -/
structure Specs where
  safety : String → List Val → Prop := fun _ _ => True
  property : Program → Prop := fun _ => True

/-- Captured MIR verification subject pairing `program : Program` with its
reviewed specification bundle `specs : Specs`, so top-level obligations
(`CrateTheorem` and `UnitTheorem`) take a single captured `Crate` value. -/
structure Crate where
  program : Program
  specs : Specs := ⟨fun _ _ => True, fun _ => True⟩

/-- Verification judgment for a non-empty program `p` and `specs`:
1. `p.pointerWidthBits = 64` and `p.mirProfileVersion = 1`;
2. `p.bodies` is non-empty and `p.entryDefId < p.bodies.length` (preventing
   vacuous satisfaction on empty body lists or dangling `entryDefId`s);
3. Every body in `p.bodies` has a non-empty, pairwise-distinct `identity`
   (`bodiesHaveUniqueIdentities p.bodies = true`);
4. Every body `(defId, body)` in `p.bodies` satisfies `BodyVerified` under
   `specs.safety body.identity`; and
5. `specs.property p` holds. -/
noncomputable def ProgramVerified (p : Program) (specs : Specs) : Prop :=
  Nat.beq p.pointerWidthBits 64 = true ∧
  Nat.beq p.mirProfileVersion 1 = true ∧
  !p.bodies.isEmpty = true ∧
  Nat.blt p.entryDefId p.bodies.length = true ∧
  bodiesHaveUniqueIdentities p.bodies = true ∧
  (∀ (defId : DefId) (body : Body),
    getElem? p.bodies defId = some body →
    BodyVerified p defId body (specs.safety body.identity)) ∧
  specs.property p

/-- Top-level one-argument verification obligation for a whole-crate capture
(`c.program.scope = .crate`). Completeness of `c.program.bodies` with respect
to the compiled Rust crate (including every executable body and reachable
callee) is an external obligation of the capture producer (such as a future
`anneal-rustc-capture` emitter), not checked by this predicate alone. -/
noncomputable def CrateTheorem (c : Crate) : Prop :=
  c.program.scope = .crate ∧ ProgramVerified c.program c.specs

/-- Top-level one-argument verification obligation for a selected proof-unit
capture (`c.program.scope = .unit`). -/
noncomputable def UnitTheorem (c : Crate) : Prop :=
  c.program.scope = .unit ∧ ProgramVerified c.program c.specs

end Trusted.MirSemantics

end
