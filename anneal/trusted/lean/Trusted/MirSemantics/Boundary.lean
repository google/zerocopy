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
annotations, well-typed `Discriminant` and `Cast` destinations, supported local
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

/-- Profile v2 divergence of `(p, q)`. -/
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
  /-- Return `true` when `ty` is a reference or a tuple containing one. Profile
  v2 pointees never contain references or pointers (`isSupportedV2LocalTy`),
  so only tuple nesting needs inspection. -/
  noncomputable def tyHasRefV2 : MirTy → Bool
    | .ref _ _ => true
    | .tuple fs => tyListHasRefV2 fs
    | _ => false

  noncomputable def tyListHasRefV2 : List MirTy → Bool
    | [] => false
    | t :: ts => tyHasRefV2 t || tyListHasRefV2 ts
end

mutual
  /-- Return `true` when `ty` is a raw pointer or a tuple containing one. -/
  noncomputable def tyHasRawPtrV2 : MirTy → Bool
    | .rawPtr _ _ => true
    | .tuple fs => tyListHasRawPtrV2 fs
    | _ => false

  noncomputable def tyListHasRawPtrV2 : List MirTy → Bool
    | [] => false
    | t :: ts => tyHasRawPtrV2 t || tyListHasRawPtrV2 ts
end

/-- Return `true` when `body` has both reference-typed and raw-pointer-typed
locals.

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
creates lives in a local of its type, so a body without raw-pointer locals
creates references only from other references. The borrow checker then rules
out conflicting uses, since Profile v2 has no `UnsafeCell`. A body without
reference locals creates no references at all. Mixing the two would let a body
derive overlapping references from raw pointers, or access referenced memory
through raw pointers, so `BodyStaticAdmittedV2` rejects such bodies.

This does not cover the aliasing permission of raw-pointer arguments: a
raw-pointer-only body that writes through a `*mut` argument the caller derived
from a live `&T` is undefined behavior that Profile v2 does not detect. Callers
must pass raw pointers whose provenance permits the accesses the body makes,
which receipts record as an assumption. -/
noncomputable def bodyMixesRefsAndRawPtrsV2 (body : Body) : Bool :=
  tyListHasRefV2 body.locals && tyListHasRawPtrV2 body.locals

/-- Unconditional static admission predicate for Profile v2
(`p.mirProfileVersion = 2`) and `(p, body)`, which also rejects bodies that mix
reference and raw-pointer locals (`bodyMixesRefsAndRawPtrsV2`). -/
noncomputable def BodyStaticAdmittedV2 (p : Program) (body : Body) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 2 &&
    !stringIsEmpty body.identity &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    discriminantTypesValid body &&
    castTypesValid body &&
    !bodyMixesRefsAndRawPtrsV2 body &&
    body.locals.all isSupportedV2LocalTy

/-- Profile v2 verification judgment for a single body `body` at index `defId`
in `p`, quantifying over both `q.args` and caller-supplied heap/stack memory
`q.callerMem`.

Profile v2 does not model Rust's aliasing rules (Stacked Borrows or Tree
Borrows). Reference validity and mutable-reference disjointness are checked
only for entry arguments (`ValidEntryArgsV2`) and for the returned value
(`evalTerminatorV2`). References created inside a body are checked only for
liveness, bounds, alignment, mutability, and initialization
(`refValidInMem`). For bodies containing references, excluding raw-pointer
locals via `BodyStaticAdmittedV2` (`bodyMixesRefsAndRawPtrsV2`) prevents
deriving conflicting `&mut` references from raw pointers, while raw-pointer-only
bodies omit intra-body aliasing checks (`Stacked` or `Tree Borrows`, recorded in
receipt assumptions). -/
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

end Trusted.MirSemantics

end
