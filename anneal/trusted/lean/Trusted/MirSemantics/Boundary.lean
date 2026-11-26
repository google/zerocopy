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
finite outcomes so downstream equivalence proofs can relate both. Note that
`.aborted` under `--panic abort` is modeled as a terminal outcome
(`.done (.aborted _)`), not an infinite step trace, even though the unverified
panic runtime or hook may diverge instead of aborting the process; accordingly,
`¬ Diverges p q` makes no termination claim on paths that reach `.aborted`. -/
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
2. **Multi-frame intra-crate and pinned-sysroot calls:**
   `TerminatorKind.call` pushes an intra-crate callee frame indexed in
   `p.bodies`. `callsAdmitted` refuses calls to `unsafe fn` callees, so no
   callee's `Specs.safety` is consulted at a call site; only the entry body's
   precondition constrains a run. `TerminatorKind.sysrootCall` steps into the
   pinned `sysrootNumBody op` (`core::num` verified at capture time against
   `tcx.instance_mir`); indirect and unmodeled external calls fault with
   `.fault .unsupported`.
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
annotations, well-typed `Discriminant` and `Cast` destinations and `Assert`
conditions, supported local
types (`isSupportedScalarOrUnitTy`), valid intra-crate and pinned-sysroot
call sites (`callsAdmitted`), and—whenever `body` contains any call—all bodies
in `p.bodies` (`allCallBodiesStaticAdmitted`), even when `body` has
uninhabited (`MirTy.never`) parameters and `ValidEntryArgs body args` is
vacuously empty. -/
noncomputable def BodyStaticAdmitted (p : Program) (body : Body) : Bool :=
  singleBodyStaticAdmitted p body && allCallBodiesStaticAdmitted p body

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
   remain permitted unless ruled out by `Specs.property`). Under opt-in
   `--panic abort` (`p.panicStrategy = .abort`), failed safe `Assert`s
   terminate cleanly as `.aborted`, so panic-freedom under `--panic abort`
   requires an explicit `noAbort` postcondition in `Specs.property`.
   Profile v1 `.assert` stepping has `lean-miri` correspondence
   (`CanaryD17AssertPanicAbortClaim`, empty `callerMem`). -/
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

/-!
## Profile v2 Memory- and Pointer-Aware Verification Judgments
-/

/-- Profile v2 small-step transition over `evalStepV2`. -/
noncomputable def StepV2 (p : Program) (s : State)
    (res : StepResult State TerminalOut) : Prop :=
  ∃ c : Choice, ValidChoice p s c ∧ evalStepV2Choice p c s = res

/-- Profile v2 unbounded finite-step reachability from `s₁` to `s₂`. -/
inductive ReachesV2 (p : Program) : State → State → Prop where
  | refl (s : State) : ReachesV2 p s s
  | tail {s₁ s₂ s₃ : State} :
      ReachesV2 p s₁ s₂ →
      StepV2 p s₂ (.step s₃) →
      ReachesV2 p s₁ s₃

/-- Profile v2 outcome reachability from `(p, q)` using `initStateV2` and
`StepV2`. -/
noncomputable def ReachesResultV2 (p : Program) (q : Query)
    (res : StepResult State TerminalOut) : Prop :=
  match initStateV2 p q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : State, ReachesV2 p s₀ s ∧ StepV2 p s res

/-- Profile v2 all-prefix well-formedness (`initStateV2` succeeds, every
reachable state admits a valid choice, and no reachable step faults). -/
noncomputable def WellFormedV2 (p : Program) (q : Query) : Prop :=
  (∃ s₀ : State, initStateV2 p q = .ok s₀ ∧
    ∀ s : State, ReachesV2 p s₀ s → ∃ c : Choice, ValidChoice p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResultV2 p q (.fault k))

/-- Profile v2 observable terminal behavior of `(p, q)`. -/
noncomputable def BehaviorV2 (p : Program) (q : Query) (out : TerminalOut) :
    Prop :=
  ReachesResultV2 p q (.done out)

/-- Profile v2 divergence of `(p, q)`: an infinite productive step trace from
`initStateV2 p q`. Note that `.aborted` under `--panic abort` is modeled as a
terminal outcome (`.done (.aborted _)`), not an infinite step trace, even
though the unverified panic runtime or hook may diverge instead of aborting the
process; accordingly, `¬ DivergesV2 p q` makes no termination claim on paths
that reach `.aborted`. -/
noncomputable def DivergesV2 (p : Program) (q : Query) : Prop :=
  ∃ s₀ : State,
    initStateV2 p q = .ok s₀ ∧
    ∃ trace : Nat → State,
      trace 0 = s₀ ∧
      ∀ n : Nat, StepV2 p (trace n) (.step (trace (n + 1)))

/-- Profile v2 universal partial-correctness contract satisfaction. -/
noncomputable def SatisfiesPostV2 (p : Program) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  WellFormedV2 p q ∧ ∀ out : TerminalOut, BehaviorV2 p q out → post out

/-- Profile v2 entry validity predicate over `q : Query`:
1. `q.callerMem` has valid distinct non-zero `allocId`s (`validCallerMemory`);
2. `q.args` matches `locals[1..=argumentCount]` (`checkArgsMatchV2`);
3. every reference (`&T`, `&mut T`, `&[T]`, `&mut [T]`) passed at entry obeys
   `refsValidInMemList` (reference validity plus initialized, `decodeValV2`
   pointee bytes, narrowing quantification for unsafe callers over uninit
   memory) and mutable borrow disjointness (`spansPairwiseDisjoint`), while raw
   pointers remain unconstrained (so unsafe functions must explicitly discharge
   raw pointer safety in `SpecsV2.safety`).

Item 3 is a hypothesis of `BodyVerifiedV2`, not a runtime check, so anything
it requires beyond Rust's actual contract narrows the quantified inputs. Two
parts rest on rules that are not settled upstream, and receipts record
them as assumptions:
- (i) Every `&T`/`&mut T`/`&[T]` argument points to an initialized, valid
  pointee. The Reference calls this point debated
  (`src/behavior-considered-undefined.md:195-199`, `rust-lang/reference`
  `ad35aca481751a06afeb23820a672b0f3b11a476`):

  > "* A reference or [`Box<T>`] must be aligned and non-null, it cannot be
  >   [dangling], and it must point to a valid value (in case of dynamically
  >   sized types, using the actual dynamic type of the pointee as determined
  >   by the metadata). Note that the last point (about pointing to a valid
  >   value) remains a subject of some debate."

  Miri does not enforce it recursively by default. If Rust relaxes it, a
  caller could legally pass `&mut u8` to uninitialized memory, and a body
  verified under this hypothesis could read it and hit UB that the proof
  never covered.
- (ii) Every `&mut` argument points into a `.mut` allocation, even for
  zero-sized pointees. The only rustc check of this kind runs in CTFE mode
  and skips `size == Size::ZERO`
  (`compiler/rustc_const_eval/src/interpret/validity.rs:821-838`,
  `rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). -/
noncomputable def ValidEntryArgsV2 (body : Body) (q : Query) : Prop :=
  let paramTys := (body.locals.drop 1).take body.argumentCount
  let entryMem := entryMemoryWithCaller q.callerMem
  validCallerMemory q.callerMem = true ∧
  checkArgsMatchV2 q.args paramTys = true ∧
  refsValidInMemList entryMem paramTys q.args = true ∧
  spansPairwiseDisjoint (refAccessSpansList paramTys q.args) = true

mutual
  /-- Return `true` when `ty` is a reference or an option, range, tuple, or
  fixed-size array containing one. Profile v2 pointees never contain
  references or pointers (`isSupportedV2LocalTy`), so only algebraic and
  fixed-array nesting need inspection. Kept exhaustive over `MirTy` so adding
  new aggregate/container constructors forces updating reference tracking. -/
  noncomputable def tyHasRefV2 : MirTy → Bool
    | .ref _ _ => true
    | .array elem _ => tyHasRefV2 elem
    | .option e | .rangeTo e | .rangeFrom e | .range e => tyHasRefV2 e
    | .tuple fs => tyListHasRefV2 fs
    | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
    | .rawPtr _ _ | .slice _ | .str | .unsupported => false

  noncomputable def tyListHasRefV2 : List MirTy → Bool
    | [] => false
    | t :: ts => tyHasRefV2 t || tyListHasRefV2 ts
end

/-- Return `true` when `p` accesses local `lid`. (`ProjectionElem` carries no
local indices in Profile v2.) -/
noncomputable def placeMentionsLocalV2 (lid : LocalId) (p : Place) : Bool :=
  Nat.beq p.localId lid

/-- Return `true` when `opnd` reads or moves from local `lid`. -/
noncomputable def operandMentionsLocalV2 (lid : LocalId) : Operand → Bool
  | .copy p | .move p => placeMentionsLocalV2 lid p
  | .constant _ => false

/-- Return `true` when any operand in `ops` mentions local `lid`. -/
noncomputable def operandListMentionsLocalV2 (lid : LocalId) :
    List Operand → Bool
  | [] => false
  | op :: ops =>
    operandMentionsLocalV2 lid op || operandListMentionsLocalV2 lid ops

/-- Return `true` when `rv` mentions local `lid` in any operand or place. -/
noncomputable def rvalueMentionsLocalV2 (lid : LocalId) : Rvalue → Bool
  | .use op | .useRetag op | .unaryOp _ op | .cast _ op _
  | .repeat_ op _ _ | .aggregateRangeTo _ op | .aggregateRangeFrom _ op =>
    operandMentionsLocalV2 lid op
  | .binaryOp _ lhs rhs =>
    operandMentionsLocalV2 lid lhs || operandMentionsLocalV2 lid rhs
  | .discriminant p | .ref _ p | .addressOf _ p | .fakeAddressOf p =>
    placeMentionsLocalV2 lid p
  | .aggregateRange _ startOp endOp =>
    operandMentionsLocalV2 lid startOp || operandMentionsLocalV2 lid endOp
  | .aggregateOption _ _ (some op) => operandMentionsLocalV2 lid op
  | .aggregateOption _ _ none => false
  | .aggregateTuple ops | .aggregateArray _ ops =>
    operandListMentionsLocalV2 lid ops
  | .unsupported => false

/-- Return `true` when `term` mentions local `lid` in any operand or
destination place. -/
noncomputable def terminatorMentionsLocalV2 (lid : LocalId) :
    TerminatorKind → Bool
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => false
  | .switchInt discr _ => operandMentionsLocalV2 lid discr
  | .assert cond _ _ _ _ => operandMentionsLocalV2 lid cond
  | .call _ args dst _ _ | .coreCall _ args dst _ _
  | .sysrootCall _ args dst _ _ =>
    operandListMentionsLocalV2 lid args || placeMentionsLocalV2 lid dst

/-- Check static well-typedness of `.fakeAddressOf src` into unprojected local
`dstId`: `src` must be `⟨baseId, [.deref]⟩` with `baseId != dstId`,
`locals[baseId]?` must be `.ref _ pt` or `.rawPtr _ pt` with
`!isOverflowPairTy pt`, and `locals[dstId]?` must be `.rawPtr .shared pt`. -/
noncomputable def fakeAddressOfTypesMatchV2 (locals : List MirTy)
    (dstId : LocalId) (src : Place) : Bool :=
  !Nat.beq src.localId dstId &&
    match src.projection with
    | [.deref] =>
      match getElem? locals src.localId, getElem? locals dstId with
      | some (.ref _ pt), some dstTy
      | some (.rawPtr _ pt), some dstTy =>
        !isOverflowPairTy pt && MirTy.beq dstTy (.rawPtr .shared pt)
      | _, _ => false
    | _ => false

/-- Return `true` when `stmt` is an unprojected `.fakeAddressOf` assignment to
local `lid`. -/
noncomputable def stmtAssignsFakeAddressOfToV2 (lid : LocalId) :
    StatementKind → Bool
  | .assign dst rv =>
    match rv with
    | .fakeAddressOf _ => Nat.beq dst.localId lid && dst.projection.isEmpty
    | _ => false
  | _ => false

/-- Check that `stmt` uses candidate fake-metadata local `lid` exclusively as
a well-typed unprojected `.fakeAddressOf (*base)` destination (`base != lid`)
or as an unprojected `.unaryOp .ptrMetadata` operand (into a destination other
than `lid`), plus `StorageLive`/`StorageDead` markers. -/
noncomputable def stmtRespectsFakePtrMetadataLocalV2 (locals : List MirTy)
    (lid : LocalId) : StatementKind → Bool
  | .assign dst rv =>
    if placeMentionsLocalV2 lid dst then
      dst.projection.isEmpty &&
        match rv with
        | .fakeAddressOf src => fakeAddressOfTypesMatchV2 locals lid src
        | _ => false
    else if rvalueMentionsLocalV2 lid rv then
      match rv with
      | .unaryOp .ptrMetadata opnd =>
        match opnd with
        | .copy p | .move p => Nat.beq p.localId lid && p.projection.isEmpty
        | .constant _ => false
      | _ => false
    else
      true
  | .storageLive _ | .storageDead _ | .nop | .unsupported => true

/-- Return `true` when local `lid` of `body` is a compiler-synthesized
`RawPtrKind::FakeForPtrMetadata` temporary:
1. `lid > body.argumentCount` (neither `_0` nor a caller parameter);
2. `body.locals[lid]? = some (.rawPtr .shared pt)` (top-level `*const` local);
3. at least one statement in `body` assigns `.fakeAddressOf` to `⟨lid, []⟩`;
4. every statement and terminator in `body` uses `lid` exclusively as an
   unprojected `.fakeAddressOf (*base)` destination (`base != lid`) or as an
   unprojected `.unaryOp .ptrMetadata` operand (never dereferenced, reborrowed,
   cast, offset, copied elsewhere, passed to calls, or returned). -/
noncomputable def isFakePtrMetadataLocalV2 (body : Body)
    (lid : LocalId) : Bool :=
  Nat.blt body.argumentCount lid &&
    match getElem? body.locals lid with
    | some (.rawPtr .shared _) =>
      body.basicBlocks.any (fun bb =>
        bb.statements.any (stmtAssignsFakeAddressOfToV2 lid)) &&
        body.basicBlocks.all (fun bb =>
          bb.statements.all
            (stmtRespectsFakePtrMetadataLocalV2 body.locals lid) &&
            !terminatorMentionsLocalV2 lid bb.terminator)
    | _ => false

/-- Check that every `.fakeAddressOf` rvalue in `body` assigns into an
unprojected local satisfying `isFakePtrMetadataLocalV2 body dst.localId` (even
in bodies without reference locals). -/
noncomputable def bodyFakeAddressOfValidV2 (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        match rv with
        | .fakeAddressOf _ =>
          dst.projection.isEmpty && isFakePtrMetadataLocalV2 body dst.localId
        | _ => true
      | _ => true))

/-- Loop over `locals` starting at index `idx`, returning `true` if any local
contains a raw pointer (`tyHasRawPtrV2`) and is not a metadata-only
`FakeForPtrMetadata` temporary (`isFakePtrMetadataLocalV2`). -/
noncomputable def bodyHasRawPtrLocalLoopV2 (body : Body) :
    Nat → List MirTy → Bool
  | _, [] => false
  | idx, ty :: rest =>
    (tyHasRawPtrV2 ty && !isFakePtrMetadataLocalV2 body idx) ||
      bodyHasRawPtrLocalLoopV2 body (idx + 1) rest

/-- Return `true` when `body` declares any non-`FakeForPtrMetadata` raw-pointer
local (including raw pointers nested inside tuples or arrays). -/
noncomputable def bodyHasRawPtrLocalV2 (body : Body) : Bool :=
  bodyHasRawPtrLocalLoopV2 body 0 body.locals

/-- Return `true` when `body` has both reference-typed and non-fake
raw-pointer-typed locals.

Profile v2 does not model Rust's pointer aliasing rules. The Rust Reference
(`src/behavior-considered-undefined.md:36-39`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`) lists as undefined behavior:

> "* Breaking the pointer aliasing rules. The exact aliasing rules are not
>   determined yet, but here is an outline of the general principles: `&T`
>   must point to memory that is not mutated while they are live (except for
>   data inside an [`UnsafeCell<U>`]), and `&mut T` must point to memory that
>   is not read or written by any pointer not derived from the reference and
>   that no other reference points to while they are live."

Rather than approximate these rules, Profile v2 admits only bodies that
cannot create or use conflicting references themselves. Every value a body
creates lives in a local of its type, so a body without real raw-pointer locals
creates references only from other references. The borrow checker then rules
out conflicting uses, since Profile v2 has no `UnsafeCell`. A `*const` local
used exclusively for `RawPtrKind::FakeForPtrMetadata` + `UnOp::PtrMetadata`
(`isFakePtrMetadataLocalV2`) never incurs a retag in Miri and can never be
dereferenced, reborrowed, cast, offset, or escaped, so exempting it cannot
derive references from raw pointers or access referenced memory through raw
pointers. A body without reference locals creates no references at all. Mixing
references with any other raw-pointer local would let a body derive overlapping
references from raw pointers, or access referenced memory through raw pointers,
so `BodyStaticAdmittedV2` rejects such bodies.

This does not cover the aliasing permission of raw-pointer arguments: a
raw-pointer-only body that writes through a `*mut` argument the caller derived
from a live `&T` is undefined behavior that Profile v2 does not detect. Callers
must pass raw pointers whose provenance permits the accesses the body makes,
which receipts record as an assumption. -/
noncomputable def bodyMixesRefsAndRawPtrsV2 (body : Body) : Bool :=
  tyListHasRefV2 body.locals && bodyHasRawPtrLocalV2 body

/-- Unconditional static admission predicate for Profile v2
(`p.mirProfileVersion = 2`) and `(p, body)`, which also rejects bodies that mix
reference and non-fake raw-pointer locals (`bodyMixesRefsAndRawPtrsV2`) or
misuse `Rvalue.fakeAddressOf` (`bodyFakeAddressOfValidV2`). -/
noncomputable def BodyStaticAdmittedV2 (p : Program) (body : Body) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 2 &&
    !stringIsEmpty body.identity &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    discriminantTypesValidV2 body &&
    castTypesValid body &&
    assertConditionTypesValid body &&
    !bodyMixesRefsAndRawPtrsV2 body &&
    bodyFakeAddressOfValidV2 body &&
    body.locals.all isSupportedV2LocalTy

/-- Profile v2 verification judgment for a single body `body` at index `defId`
in `p`, quantifying over both `q.args` and caller-supplied heap/stack memory
`q.callerMem`.

Profile v2 does not model Rust's aliasing rules (Stacked Borrows or Tree
Borrows). Reference validity and mutable-reference disjointness are checked
only for entry arguments (`ValidEntryArgsV2`) and for the returned value
(`evalTerminatorV2`). References created inside a body are checked only for
liveness, bounds, alignment, mutability, and initialization
(`refValidInMem`). For bodies containing references, excluding non-fake
raw-pointer locals via `BodyStaticAdmittedV2` (`bodyMixesRefsAndRawPtrsV2`)
prevents deriving conflicting `&mut` references from raw pointers, while
raw-pointer-only bodies omit intra-body aliasing checks (`Stacked` or
`Tree Borrows`, recorded in receipt assumptions).

Under opt-in `--panic abort` (`p.panicStrategy = .abort`,
`p.hasLocalPanicHandler = false`), failed safe `Assert`s and admitted
`core::panicking::{panic, panic_nounwind}` calls (`CoreCallOp.panicAbort`)
terminate cleanly as `.aborted` carrying post-mutation `CallerMemory`, so
`BodyVerifiedV2` alone permits safe-panic aborts; panic-freedom under
`--panic abort` requires an explicit `EffectMaskV2.noAbort` `SafeContractV2`
obligation in `SpecsV2.property`. Crates defining a crate-local
`#[panic_handler]` (`p.hasLocalPanicHandler = true`) keep failing safe
`Assert`s and `CoreCallOp.panicAbort` calls fail-closed as
`.fault .unsupported`. Note that Profile v2 `.assert` / `.panicAbort` /
`.aborted` paths with non-empty `callerMem` do not yet have a `lean-miri`
simulation proof (unlike Profile v1's empty-`callerMem`
`CanaryD17AssertPanicAbortClaim`). -/
noncomputable def BodyVerifiedV2 (p : Program) (defId : DefId) (body : Body)
    (safetyPre : Query → Prop) : Prop :=
  getElem? p.bodies defId = some body ∧
  BodyStaticAdmittedV2 p body = true ∧
  ∀ q : Query,
    ValidEntryArgsV2 body q →
    (body.isUnsafe = true → safetyPre q) →
    WellFormedV2 (entryProgForBody p defId) q

/-- Profile v2 specification bundle pairing query-level `safety` (receiving both
arguments and `callerMem`) with program-wide `property`. -/
structure SpecsV2 where
  safety : String → Query → Prop := fun _ _ => True
  property : Program → Prop := fun _ => True

/-- Profile v2 captured MIR verification subject pairing `program : Program`
with `specs : SpecsV2`. -/
structure CrateV2 where
  program : Program
  specs : SpecsV2 := ⟨fun _ _ => True, fun _ => True⟩

/-- Profile v2 program-wide verification judgment for `p`
(`mirProfileVersion = 2`) and `specs : SpecsV2`. -/
noncomputable def ProgramVerifiedV2 (p : Program) (specs : SpecsV2) : Prop :=
  Nat.beq p.pointerWidthBits 64 = true ∧
  Nat.beq p.mirProfileVersion 2 = true ∧
  !p.bodies.isEmpty = true ∧
  Nat.blt p.entryDefId p.bodies.length = true ∧
  bodiesHaveUniqueIdentities p.bodies = true ∧
  (∀ (defId : DefId) (body : Body),
    getElem? p.bodies defId = some body →
    BodyVerifiedV2 p defId body (specs.safety body.identity)) ∧
  specs.property p

/-- Profile v2 top-level one-argument verification obligation for a whole-crate
capture (`c.program.scope = .crate`). -/
noncomputable def CrateTheoremV2 (c : CrateV2) : Prop :=
  c.program.scope = .crate ∧ ProgramVerifiedV2 c.program c.specs

/-- Profile v2 top-level one-argument verification obligation for a selected
proof-unit (`Trusted.MirSemantics.UnitTheoremV2`). -/
noncomputable def UnitTheoremV2 (c : CrateV2) : Prop :=
  c.program.scope = .unit ∧ ProgramVerifiedV2 c.program c.specs

/-- Allowed terminal-effect mask for Profile v2 postcondition contracts
(fail-closed by default: aborting paths are forbidden unless explicitly
enabled with `allowAbort := true`). -/
structure EffectMaskV2 where
  allowAbort : Bool := false

/-- Effect mask that rejects aborting paths (`allowAbort := false`). -/
def EffectMaskV2.noAbort : EffectMaskV2 := { allowAbort := false }

/-- Profile v2 contract specification for partial-domain functions. The six
contract vocabulary declarations (`EffectMaskV2`, `EffectMaskV2.noAbort`,
`SafeContractV2`, `SafeContractV2.post`, `SatisfiesSafeContractV2`, and
`BodySatisfiesSafeContractV2`) are rooted in `TrustedBoundary.lean` via
`Trusted.MirSemantics.SafeContractSoundnessClaimV2` and instantiated by user
specifications in `SpecsV2.property`:
- `behaviorPre q`: behavioral / non-panic domain precondition;
- `effects`: terminal-effect mask controlling whether `.aborted` is permitted
  (defaults fail-closed to `{ allowAbort := false }`);
- `postReturn q out`: postcondition when execution returns `out`;
- `postAbort q callerMem`: postcondition on post-mutation `CallerMemory` when
  execution aborts under `--panic abort` (defaults fail-closed to `False`). -/
structure SafeContractV2 where
  behaviorPre : Query → Prop := fun _ => True
  effects : EffectMaskV2 := { allowAbort := false }
  postReturn : Query → Out → Prop := fun _ _ => True
  postAbort : Query → CallerMemory → Prop := fun _ _ => False

/-- Terminal-outcome predicate induced by `contract : SafeContractV2` on entry
query `q`. -/
noncomputable def SafeContractV2.post (contract : SafeContractV2)
    (q : Query) : TerminalOut → Prop
  | .returned out => contract.postReturn q out
  | .unwound _ => False
  | .aborted callerMem =>
    contract.effects.allowAbort = true ∧ contract.postAbort q callerMem

/-- Satisfaction of `contract : SafeContractV2` by `p` at entry `q` under
`contract.behaviorPre q`. -/
noncomputable def SatisfiesSafeContractV2 (p : Program) (q : Query)
    (contract : SafeContractV2) : Prop :=
  contract.behaviorPre q → SatisfiesPostV2 p q (contract.post q)

/-- Body-level `SafeContractV2` judgment quantifying over all
`ValidEntryArgsV2` inputs for `body` at `defId` in `p`. -/
noncomputable def BodySatisfiesSafeContractV2 (p : Program) (defId : DefId)
    (body : Body) (contract : SafeContractV2) : Prop :=
  getElem? p.bodies defId = some body ∧
  BodyStaticAdmittedV2 p body = true ∧
  ∀ q : Query,
    ValidEntryArgsV2 body q →
    SatisfiesSafeContractV2 (entryProgForBody p defId) q contract

end Trusted.MirSemantics

end
