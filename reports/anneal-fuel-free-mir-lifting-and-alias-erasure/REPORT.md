<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Fuel-Free MIR Proof Lifting, Alias Erasure, and Lean 4 Elaboration Scaling

## Summary

Foundational Rust verifiers built over small-step or fuel-indexed operational
Mid-Level Intermediate Representation (MIR) interpreters face two coupled
scaling bottlenecks when verification proofs are authored directly against raw
machine states:

1. **Per-Block Fuel and State-Plumbing Boilerplate:** Hand-written basic-block
   context records (`BlockCtx`), explicit `Nat` step budgets (`fuel`), and
   tactic iteration counts (`iterate k`) break whenever `rustc` inserts a
   `StorageLive`, `StorageDead`, or temporary slot, inflating proof size to
   $1{,}000\text{--}1{,}600$ lines per 20-line Rust function.
2. **Global Memory and Tree Borrows Alias Obligations:** Threading a stateful
   `Memory` record (`globals`, `borrows`, `callerLocals`, `activeProtectors`,
   allocation metadata) through every pure arithmetic statement or disjoint
   `&mut` reborrow forces quadratic borrow-tree non-interference reasoning and
   causes Lean 4 Weak Head Normal Form (`whnf`) / `dsimp` blowups when symbolic
   `List.set` chains or closure-captured reference environments accumulate.

Combining a self-contained Lean 4 (`v4.34.1`) mechanization
(`support/FuelFreeMirLiftingAndLensesProbe.lean`) with controlled empirical
measurements across a 7-function Rust protocol-parsing and frame-checksum suite
(`WireframeDemo`, preserved in `support/wireframe_benchmark_metrics.json`)
establishes eight findings:

- **F-01 (Existential Fuel Synthesis Over a `prelude`-Only Small-Step TCB):**
  Defining a flat Kleene information order (`FuelOrder`) over bounded-fuel
  evaluator outcomes (`outOfFuel ≤ r`) yields a fuel-free weakest-precondition
  predicate (`MirWpConverges` / `MirNoCallWpConverges`) whose sequential bind
  and control-flow rules synthesize finite step budgets existentially (`1 + k`,
  `k₁ + k₂`) while keeping `WellFounded.fix`, `partial_fixpoint`, and
  `Classical.choice` completely out of the `prelude`-only Trusted Computing Base
  (TCB).
- **F-02 (Tier 1 Syntactic Purity and Once-and-for-All `Memory` Erasure):**
  A computable AST check (`checkPureMir` / `checkPureMirWithCallees`) that
  rejects pointer dereferences (`.deref`), address-taking rvalues
  (`Rvalue.{ref, rawPtr, threadLocalRef, shallowInitBox, copyForDeref}`),
  pointer-provenance casts/offsets (`CastKind.ptrToPtr`, `BinOp.offset`), and
  retags enables a lockstep frame simulation (`MirFrameSim`) from a memory-free
  `PureState` (`bb`, `stmtIdx`, `env`; simplified to `pc`, `env` in the probe)
  to the full `MachineState`, erasing the entire `Memory` record (`mem' = mem₀`)
  once in shared theory rather than per proof.
- **F-03 (Opaque-Body Lifting via `LiftBlock` and Flat `forcePureEnv?` List
  Normalization):** Keeping lifted block theorems (`LiftBlock body bbIdx env
  post fuel`, bridged once via `lift_PureMirConverges`) parametric in an opaque
  `post : Value → Prop` prevents `whnf` from copying downstream CFG branches
  across diamond joins (`liftBlock_diamond_shared`, eliminating $O(2^B)$ term
  duplication across $B$ diamonds), while spine-eager environment rebuilding
  (`forcePureEnv?`) collapses nested `List.set` chains into a flat slot literal
  by `rfl` (`chained_sets_collapse_rfl`).
- **F-04 (Untrusted Lifting Rules and `#mir_lift` Outside the TCB Audit
  Boundary):** Authoring constructive `LiftBlock` / `LiftStmtsTerminator` rules
  (for parametric `Proof/*.lean` targets under `TrustedBoundary`) alongside an
  interactive `#mir_lift` command elaborator (for closed `argCount = 0`
  constants in both call-free `LiftBlock` and linked-callee `LiftFrame` modes)
  adds zero axioms and zero lines to `Trusted/`, because every proof term
  reduces to kernel-checked primitives replayed by the standalone auditor.
- **F-05 (The Closure-Captured `Rvalue.ref` Companion Bottleneck):** Rust
  contract macros that lower `#[spec]` `requires` / `ensures` clauses into
  closures capturing arguments by shared reference (`&arg`) emit `Rvalue.ref`
  and `ProjectionElem.deref` inside companion MIR bodies (`checkPureMir =
  false`). Stepping even the first `Rvalue.ref` with memory-carrying `rfl` rules
  exceeds `400,000` elaboration heartbeats; lifting pure companions via the
  `#mir_lift_spec` theorem family (`mirBoolPredicateHolds_*_of_pureExec`) and
  folding closure-capturing companions via `holdBoolReq_of_mirBool` + count-free
  `repeat` and `hold_mirBool_of_blockLinear` cuts pure-body proof times to
  `1.4–3.7 s` (vs. `11.1–32.4 s` when dominated by closure-capturing
  companions).
- **F-06 (Fuel-Free Bounded Loops via `forRangeUp` and Header-Targeted
  `runCfgToBlock`):** Whereas no single fuel constant `K` can halt a symbolic
  `[0, n)` loop across all `n` (`no_uniform_fuel_countUp`), coupling a
  structural `[lo, hi)` range fold (`forRangeUp`) with a block-targeted CFG
  stepper (`runCfgToBlock`, which takes one mandatory step to leave a loop
  header and then halts immediately at the next target-block entry, `.halted`,
  or `.faulted`) discharges symbolic loops with zero step numerals
  (`countUp_wpConverges_all_n`) and cuts loop-equivalence heartbeats on
  `checksum_frame_fast` from `655,752k` to `72,097k` (`-89.0%`).
- **F-07 (Tier 2 Separation-Logic Lenses for Whole-Slot and Sibling-Field `&mut`
  Borrows):** Focusing caller allocations and struct subplaces through lawful
  bidirectional lenses (`MutLens`, `MutLens.comp`, `DisjointLenses`) with Tree
  Borrows parent/child reservation-activation invariants (`SepLensStateInv`,
  `SepSubplaceLensStateInv`) reduces `&mut` mutation proofs (including sibling
  reborrows `&mut s.x` and `&mut s.y` on a single struct slot) to pure value
  updates without alias case splits (`subplaceFieldLens_disjoint`,
  `liftLens_twoBorrowAdd_sound`).
- **F-08 (Empirical Proof Compression, Shared-Theory Amortization, and `whnf` /
  `kabstract` Scaling Laws):** Migrating the 7-function `WireframeDemo` suite
  from manual `BlockCtx`/fuel proofs to the two-tier lifting stack reduces proof
  LOC from `8,009` to `1,421` (`-82.3%`), reduces `BlockCtx` and manual CFG-fuel
  occurrences from `111` to `0`, and cuts total elaboration heartbeats from
  `1,388,934k` to `665,228k` (`-52.1%`) with `0` bytes changed in the trusted
  semantics, while `+2,972` net LOC of reusable theory amortizes within a single
  7-function crate (`45.1%` of the `6,588` lines saved).

## Applicability

The findings in this report govern the interaction of four concrete subjects
identified in `REPORT.json`:

1. **Lean 4 (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`,
   `v4.34.1`):** Kernel definitional equality (`whnf` / `isDefEq`), `dsimp`
   `SimpTheorems` discrimination-tree construction, `cases` / `kabstract`
   motive abstraction over nested `match` scrutinees, `IO.getNumHeartbeats`
   allocation accounting under `-DElab.async=false`, and Lean 4 `CommandElabM`
   elaboration.
2. **Rust Runtime MIR (`rust-lang/rust` at
   `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `1.98.0-nightly`):** Executable
   runtime MIR control-flow graphs (`Runtime(PostCleanup)` and
   `Runtime(Optimized)`; `BasicBlockData`, `StatementKind`, `Rvalue`,
   `TerminatorKind`, `SwitchTargets`) and closure capture lowering for contract
   companion functions.
3. **Anneal Trust Boundary and MIR Verification Architecture (`joshlf/anneal` at
   `5fc1139f2208b3c9cfb513573c4a731cc32bb457`,
   `f2bc17e9be87b777d63c785b31f3370ff058d69b`, and
   `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`):** The architectural split
   documented in `docs/{architecture,design,trust-model}.md` (`5fc1139f`) and
   enforced by the role-aware syntax and axiom allow-list in
   `trusted/audit/TrustedBoundary.lean` (`f2bc17e9`, `c065b55a`) between a
   `prelude`-only small-step MIR operational semantics in `trusted/lean/`
   (`SourceRole.trusted`, term-mode proofs only) and an untrusted proof layer in
   `theory/` (`SourceRole.theory`). Because the captured MIR semantics (`40`
   `Trusted` modules, `9,589` trusted kernel declarations), proof-lifting
   modules (`24,183` total replayed declarations), and `WireframeDemo` benchmark
   corpus were evaluated as extensions over that baseline TCB architecture, all
   mathematical definitions, invariants, and empirical datasets are defined
   self-containedly below and preserved in `support/`.
4. **Program-Logics and Bidirectional-Lens Foundations:** Decompilation into
   logic and functional big-step semantics (Myreen et al. FMCAD 2012; Owens et
   al. ESOP 2016), inductive omnisemantics (Charguéraud et al. TOPLAS 2023),
   interaction trees (Xia et al. POPL 2020), pure functional Rust translation
   (Ho & Protzenko ICFP 2022), Tree Borrows aliasing semantics (Villani et al.
   PLDI 2025), and bidirectional view-update lenses (Foster et al. TOPLAS 2007).

Exact empirical timings and heartbeat counts apply to `x86_64-unknown-linux-gnu`
under Lean `v4.34.1` with `-DwarningAsError=true`; deterministic heartbeat
counts (`IO.getNumHeartbeats` under `set_option Elab.async false`) are
load-independent across runs on identical `.olean` imports, whereas wall-clock
seconds vary with host CPU contention. The structural soundness theorems in
`support/FuelFreeMirLiftingAndLensesProbe.lean` hold constructively in Lean
`v4.34.1` `Init` using only `propext` (zero `Classical.choice`, zero `sorryAx`).

## Findings

### F-01: Existential Fuel Synthesis Over a `prelude`-Only Small-Step TCB

`Basis: source + execution + derived`

In a foundational verifier whose `Trusted/` layer compiles under Lean 4's
`prelude` directive (importing only `Init.Core` and `Init.NotationExtra`), the
operational MIR evaluator cannot use `WellFounded.fix` (which pulls in `Init.WF`
and blocks symbolic `whnf` behind opaque `Acc` proofs) or `partial_fixpoint`
(which injects `Classical.choice` via `CCPO.csup`). The trusted evaluator
therefore exposes a total, structurally recursive step-indexed transition
function:

```lean
inductive FuelResult (α : Type) where
  | outOfFuel : FuelResult α
  | halted (v : α) : FuelResult α
  | faulted : FuelResult α

def evalFuel {σ α : Type} (step : σ → Step σ α) : Nat → σ → FuelResult α
  | 0, _ => .outOfFuel
  | k + 1, s =>
    match step s with
    | .cont s' => evalFuel step k s'
    | .done v => .halted v
    | .fault => .faulted
```

Exposing `k : Nat` directly in user proof obligations creates severe maintenance
fragility: every basic block or loop proof must supply concrete numerals (`fuel
:= 29`, `fuel := 36 * n + 5`) and discharge linear-arithmetic inequalities
(`k ≥ ...`) whenever compiler MIR optimizations add or elide a temporary slot,
and no fixed constant `K : Nat` can satisfy a symbolic loop bound `n : Nat`
(`no_uniform_fuel_countUp`, lines 828–835 of
`support/FuelFreeMirLiftingAndLensesProbe.lean`).

Equipping `FuelResult α` with the flat Kleene information order `FuelOrder`
(`outOfFuel ≤ r` for all `r`, `halted v₁ ≤ halted v₂ ↔ v₁ = v₂`, and
`faulted ≤ faulted`) yields unconditional fuel monotonicity (`evalFuel_mono` in
`support/FuelFreeMirLiftingAndLensesProbe.lean:96-106`): whenever `k₁ ≤ k₂`,
`FuelOrder (evalFuel step k₁ s) (evalFuel step k₂ s)`, so any `.halted v`
outcome is stable under arbitrary fuel increases (`FuelOrder.halted_stable`).

Consequently, the proof layer defines fuel-free total convergence predicates by
existentially quantifying the step budget once:

```lean
def WpConverges {σ α : Type}
    (step : σ → Step σ α) (s : σ) (post : α → Prop) : Prop :=
  ∃ k v, evalFuel step k s = .halted v ∧ post v
```

(instantiated in Anneal's MIR layer as `MirWpConverges` for general call-capable
execution and `MirNoCallWpConverges` for intraprocedural call-free execution,
alongside finite-segment `StepsTo` / `MirStepsConverges`). Sequential
composition (`StepsTo.bind_wp`, lines 134–144 of the probe) synthesizes the
combined witness `k + 1` (or `k₁ + k₂`) behind the existential quantifier,
bridging cleanly to TCB prefix safety (`ReachesPrefix`) at the final contract
boundary without exposing a single `Nat` step numeral in user proofs.

### F-02: Tier 1 Syntactic Purity and Once-and-for-All `Memory` Erasure

`Basis: source + execution + derived`

In Anneal's MIR operational semantics, a full `MachineState` pairs the active
`frame : StackFrame` (`blockIdx`, `stmtIdx`, `locals : List LocalSlot`) with a
12-field global `Memory` record (`nextAllocId`, `globals`, `borrows`, `nextTag`,
`callees`, `traitImpls`, `callStack`, `activeCallee`, `activeProtectors`,
`nextProtector`, `callerLocals`, and `fnPtrs`). Even when a Rust function
performs only scalar, tuple, struct, enum, or fixed-array value computations,
stepping directly on `MachineState` forces Lean's kernel to carry and compare
all 12 `Memory` fields at every assignment.

Tier 1 alias erasure eliminates `Memory` completely for the syntactically pure
MIR fragment via a decidable AST checker `checkPureMir : CapturedMir → Bool`
(extended interprocedurally to `checkPureMirWithCallees`). A MIR body passes
`checkPureMir` if and only if every basic block satisfies five syntactic
exclusions:

1. **Places:** No `ProjectionElem.deref` or `ProjectionElem.unwrapUnsafeBinder`
   anywhere in read or write places (`checkPureProg_rejects_deref`, lines
   204–207 of the probe; local projections `.field`, `.downcast`,
   `.constantIndex`, `.subslice`, `.index`, and `.opaqueCast` on local
   arrays/aggregates are permitted).
2. **Rvalues:** No address-taking or provenance-inspecting rvalues
   (`Rvalue.{ref, rawPtr, threadLocalRef, shallowInitBox, copyForDeref}`), no
   pointer-offset binary operations (`BinOp.offset`, which consults
   `mem.borrows` for bounds/provenance), and no stack-reference pointer casts
   (`CastKind.{pointerCoercion, fnPtrToPtr, ptrToPtr}` in intraprocedural
   `checkPureMir`, where `.ptrToPtr` on stack references invokes
   `deriveStackElemThinPtr` to allocate a fresh stack-element borrow tag in
   `mem.borrows`). Note that `Rvalue.len`, `Rvalue.discriminant`, and
   `Rvalue.wrapUnsafeBinder` *are* memory-independent once `splitLastDeref? p =
   none` holds, provided enum variant indices match valid layout entries; pure
   raw-pointer aggregate construction (`Rvalue.aggregate (AggregateKind.rawPtr _
   _) ops`) also remains pure whenever its operands are pure.
3. **Constants:** No indirect or pointer-backed slice constants
   (`ConstValue.indirect`, `ConstValue.slice (ConstScalar.ptr _ _) _`).
4. **Statements:** Only `StatementKind.{assign, setDiscriminant, storageLive,
   storageDead, nop, coverage, constEvalCounter, placeMention, deinit}` (with
   pure places/rvalues) and `StatementKind.intrinsic
   (NonDivergingIntrinsic.assume op)` (with pure `op`), rejecting
   `StatementKind.{retag, backwardIncompatibleDropHint}` and non-`assume`
   intrinsics such as `NonDivergingIntrinsic.copyNonOverlapping` (`FakeRead` and
   `AscribeUserType` are already erased before `Runtime(PostCleanup)` MIR).
5. **Terminators:** Only intraprocedural pure control flow
   (`TerminatorKind.{goto, switchInt, return_, assert, drop, unreachable,
   unwindResume, unwindTerminate}` with pure operands/places, rejecting `.call`,
   `.tailCall`, and `.inlineAsm`) for `checkPureMir`, or resolved pure callees,
   modular spec-verified callees (guarded by `classifyRustIntrinsic? defPath =
   none`), and direct pure scalar intrinsics (`exact_div` via
   `resolveIntrinsicIsSigned`, `bswap`, `ctpop`, `const_eval_select`) for
   `PureMirModularConverges`.

Over this fragment, execution reduces to a memory-free `PureState` (`bb`,
`stmtIdx`, `env : List SlotState` in `PureMirExec`, simplified to a flat two-
field `{ pc : Nat, env : List SlotState }` in the standalone probe) linked to
`MachineState` at an arbitrary caller memory `mem₀` by the lockstep frame
simulation (`MirFrameSim mem₀ ps ms`). The simulation theorems
(`stepPure_simulates` and `wpConverges_of_pureExec` in
`support/FuelFreeMirLiftingAndLensesProbe.lean:277-349`) prove once and for all
that `checkPureMir body = true` implies `ms.memory` remains definitionally equal
to `mem₀` at every step and return, discharging frame preservation (`mem' =
mem₀`) and panic freedom (`verifyMirNoPanic_of_pureExec`) with zero Tree Borrows
obligations. Three companion bridges extend this pure execution discipline to
signed scalars, interprocedural calls, and monomorphized layouts:

- **Closed-Form Modular Two's-Complement Scalars (`signExtendMod` and
  `signExtendMod_nonneg_id` in
  `support/FuelFreeMirLiftingAndLensesProbe.lean:941-958`):** Expressing
  two's-complement conversion (`toSignedRange`) and width extension
  (`signExtendMod`) as closed-form modular arithmetic over `2 ^ srcBits` and `2
  ^ dstBits` avoids recursive bit-blasted `BitVec` extraction loops.
- **Stack-Suffix Callee Frame Invariance (`pushBaseStack` and
  `pushBaseStack_step_comm` in
  `support/FuelFreeMirLiftingAndLensesProbe.lean:961-972`):** Splicing an
  arbitrary caller `baseStack` underneath the active callee frame (`calleeStack
  ++ baseStack`) commutes definitionally with top-frame transitions, enabling
  compositional callee summaries (`ActiveRootMemory`) and capture-free
  `core::intrinsics::const_eval_select((a₀, …), comptime_fn, runtime_fn)`
  closures (`_1 : .closure defPath []`, whose MIR body prepends unit environment
  local `_1 = .tuple []` before unpacked tuple arguments while rejecting
  closures with captured upvars).
- **Monomorphic Layout Instantiation and Function-Pointer Transmute Provenance
  (`TransmuteVal`, `evalTransmuteCast`, and `instantiated_transmute_roundtrip`
  in `support/FuelFreeMirLiftingAndLensesProbe.lean:976-999`):** Uninstantiated
  generic ADT layout entries carry a `0`-byte placeholder (`sizeBytes = 0` on
  polymorphic `Wrapper<T>`), which would truncate `CastKind.transmute` payloads
  to `0` bits; substituting concrete monomorphic parameter layouts
  (`LayoutTable.instantiateForBody`) before stepping preserves both full scalar
  bit-width and thin function-pointer provenance across `CastKind.fnPtrToPtr`
  and byte-level `CastKind.transmute`.

### F-03: Opaque-Body `LiftBlock` and Flat `forcePureEnv?` Normalization

`Basis: source + execution + derived`

Even after erasing `Memory` to `PureState`, naively unfolding a whole-function
symbolic evaluator across $B$ sequential `if`/`match` diamonds causes an
$O(2^B)$ term-size explosion when each diamond duplicates the continuation term.
Following Myreen, Gordon, and Slind's decompilation-into-logic discipline (FMCAD
2012), opaque-body proof lifting factors each basic block `bbIdx` into a
standalone judgment parametric in an *opaque* postcondition `post : Value →
Prop` (with internal per-path step depth `fuel` packaged existentially once at
entry by `lift_PureMirConverges`):

```lean
def LiftBlock (body : CapturedMir) (bbIdx : BasicBlockIdx)
    (env : PureEnv) (post : Value → Prop) (fuel : Nat) : Prop :=
  wpPureMirExec fuel body { bb := bbIdx, stmtIdx := 0, env := env } post
```

Within a single block, statement lists step via `LiftStmtsTerminator`:
- `LiftStmtsTerminator.cons_eval` / `cons_eval_norm`: evaluates one statement
  on concrete/symbolic `env` slots and advances to the tail;
- `LiftStmtsTerminator.eval_rest`: evaluates an entire remaining straight-line
  statement suffix and terminator in a single compiled fast-evaluator pass when
  no mid-block case split is needed (cutting `decode_wire_header.lean`
  elaboration from `18.8 s` / `44,866k` heartbeats to `3.7 s` / `22,947k`
  heartbeats);
- `LiftStmtsTerminator.{term_goto, term_return, term_switchInt, term_assert,
  term_drop}`: reduces the block terminator into references to successor
  `LiftBlock body bb_next env' post fuel'` hypotheses, where `post` remains an
  atomic variable so sequential diamond joins share a single join-block theorem
  rather than duplicating downstream diamonds (`twoDiamondCfg` and
  `liftBlock_diamond_shared` in
  `support/FuelFreeMirLiftingAndLensesProbe.lean:405-445`).

A critical Lean 4 `whnf` hazard arises when symbolic values are written into
`env : List SlotState` via chained `List.set` calls:
`(((env.set 0 v₀).set 3 v₃).set 1 .uninit)` does not eagerly collapse to a flat
`[v₀, .uninit, ...]` spine unless spine reduction is forced, causing deeply
nested `List.set` towers to accumulate across blocks. Defining a spine-forcing
rebuilder (`forcePureEnv env := env.map id`, or `forcePureEnv?` in the partial
option lifter) and bridging via `set_eq_of_forcePureEnv rfl` collapses arbitrary
concrete-index `List.set` chains into a flat list literal in one `rfl` check
(`chained_sets_collapse_rfl` in
`support/FuelFreeMirLiftingAndLensesProbe.lean:461-465`).

### F-04: Untrusted Lifting Rules and `#mir_lift` Elaboration Outside the TCB

`Basis: normative + source + execution`

Under Anneal's trust architecture (`joshlf/anneal` at
`5fc1139f2208b3c9cfb513573c4a731cc32bb457` and
`f2bc17e9be87b777d63c785b31f3370ff058d69b`), `trusted/lean/` contains only the
MIR AST, operational semantics, and refinement definitions; metaprogramming
(`Lean.Elab.Command`) and general tactics are excluded from `SourceRole.trusted`
by `trusted/audit/TrustedBoundary.lean`. The untrusted layer splits lifting
into two complementary components:

1. **Kernel-Audited Lifting Rules (`MirLiftCore` + `PureMirExec`, inside
   `SourceRole.theory`):** Parametric (`argCount > 0`) item proofs under
   `Proof/*.lean`—which are re-parsed under `TrustedBoundary` and forbid custom
   `elab`/`macro`/`syntax` declarations—apply the constructive `LiftBlock`,
   `LiftStmtsTerminator.{cons_eval, cons_eval_norm, eval_rest, term_*}`, and
   pure companion (`mirBoolPredicateHolds_*_of_pureExec`) theorems directly. For
   this same `TrustedBoundary` reason, a prototype `#mir_lift_spec` command
   elaborator (`MirSpecLift.lean`, `-139` LOC in Section `F-08.2`) was retired
   in favor of the kernel-audited `mirBoolPredicateHolds_*_of_pureExec` theorem
   family in `PureMirExec`, which works directly inside `Proof/*.lean`.
2. **Closed-Body `#mir_lift` Command Elaborator (`MirLift`, outside
   `TrustedBoundary`):** For closed (`argCount = 0`) `CapturedMir` test and
   exploration constants, `#mir_lift` inspects the `CapturedMir` `body` at
   command-elaboration time and synthesizes kernel-checked declarations in two
   modes: call-free mode (`#mir_lift [(residual := true)] <item>` over
   `LiftBlock`, emitting `<item>_model := ()` and `<item>_lift_sound`, and
   abstracting cyclic loop headers to `LiftResidualBlock` hypotheses when
   `residual := true`) and frame/linked-callee mode
   (`#mir_lift (callees := [c₁, …]) <item>` over `LiftFrame`, also usable with
   `callees := []` to synthesize a normalized `Value` `<item>_model`,
   `<item>_lift_sound`, and `<item>_verified : VerificationResult <item> _ _`).

Because Lean's kernel type-checks every proof term and `check_trusted.py`
replays all `24,183` downstream declarations from scratch against the `40`
`Trusted` modules (`9,589` declarations), neither `MirLiftCore` nor `#mir_lift`
widens the trusted computing base.

### F-05: The Closure-Captured `Rvalue.ref` Companion Bottleneck

`Basis: source + execution`

Empirical profiling across `WireframeDemo` uncovered a sharp asymmetry between
main function bodies and generated contract companions:

- In `frame_total_len`, `clamp_payload_window`, and `parse_compression_flag`,
  the main Rust function bodies take scalar arguments by value and pass
  `checkPureMir = true`; applying the `LiftBlock` / `LiftStmtsTerminator` rules
  discharges each main body in `1.4–3.2 s`.
- When a `#[spec]` `requires` or `ensures` companion body is also syntactically
  pure (`checkPureMir = true`), the `#mir_lift_spec` theorem family in
  `PureMirExec` (`mirBoolPredicateHolds_of_pureExec`,
  `mirBoolPredicateHolds_intro_of_pureExec`,
  `mirBoolPredicateHolds_elim_of_pureExec`, and
  `mirBoolPredicateHolds_elim_of_uniqueTruePath`) discharges the companion
  without touching `Memory`.
- However, procedural contract macros that lower inline `#[spec]` `requires`
  and `ensures` clauses into helper closures capturing outer parameters by
  shared reference (`&hdr_len`, `&payload_len`, `&ret`) emit `Rvalue.ref` and
  `ProjectionElem.deref` inside the companion `CapturedMir`, causing
  `checkPureMir` to return `false`. Attempting to step even the first
  `Rvalue.ref` of such a companion through generic memory-carrying `rfl` lifting
  rules exceeds `400,000` heartbeats because `whnf` unfolds Tree Borrows tag
  allocation and protector registration over symbolic `Memory` fields.

Isolating this bottleneck by replacing only the closure-capturing companion
lemmas with `sorry` in a throwaway measurement probe reduces total file
elaboration time from `32.4 s` to `1.5 s` on `frame_total_len.lean`, from
`22.2 s` to `1.4 s` on `clamp_payload_window.lean`, and from `11.1 s` to `3.2 s`
on `parse_compression_flag.lean`. Until contract macro lowering passes Copy
scalars by value into companion bodies (or erases read-only shared borrows via a
shared-lens fast path), closure-capturing companions should invert preconditions
via `holdBoolReq_of_mirBool` with count-free `repeat` unfolding and prove
postconditions via `hold_mirBool_of_blockLinear` (which steps the companion's
straight-line basic blocks under a fixed per-companion step budget
`defaultSpecSteps` without re-evaluating full CFG reachability).

### F-06: Fuel-Free Bounded Loops via `forRangeUp` and `runCfgToBlock`

`Basis: source + execution + derived`

Acyclic `LiftBlock` unfolding does not terminate on cyclic loop headers
(`while i < n` or `for i in lo..hi`). Early loop proofs that paired `forRangeUp`
with fixed per-segment step counts (`runCfgSteps 29` for loop entry,
`runCfgSteps 36` per loop body, `runCfgSteps 5` for exit) leaked fragile magic
numbers back into user proofs and forced `dsimp` to step absorbing states when
counts overshot.

The fuel-free loop architecture combines two primitives:

1. **Structural Range Fold (`forRangeUp` + `wpConverges_forRangeUp`,
   `support/FuelFreeMirLiftingAndLensesProbe.lean:470-570`):** Indexes `[lo,
   hi)` by `rem = hi - i` and proves once in theory that if each iteration `[i,
   i + 1)` steps from `inv i acc` to `inv (i + 1) (step i ... acc)` and the loop
   exit converges from `inv hi (forRangeUp lo hi init step)`, then the entire
   loop satisfies `WpConverges` (`mirNoCallWpConverges_forRangeUp`) with zero
   fuel numerals (`countUp_wpConverges_all_n`, lines 841–867, contrasting with
   `no_uniform_fuel_countUp`, lines 828–835).
2. **Header-Targeted Block Evaluator (`runCfgToBlock`, modeled by
   `runUntilTarget`, `runToTarget`, `stepsTo_of_runToTarget_reached`,
   `wpConverges_of_runToTarget_halted`, `runToTarget_mono_bound`,
   `runCfgToBlock`, `stepsTo_of_runCfgToBlock_reached`, and
   `wpConverges_of_runCfgToBlock_halted` in
   `support/FuelFreeMirLiftingAndLensesProbe.lean:573-797`):** Takes one
   mandatory initial step (so calling `runCfgToBlock body targetBb` at loop
   header `targetBb` advances into the loop body rather than halting in zero
   steps) and then steps `runCfgUntilAux` up to internal ceiling
   `Nat.add (length body.basicBlocks) 256`, checking `cfgAtBlock targetBb` after
   each step and halting immediately upon the next entry into `targetBb` **or**
   reaching `.halted` / `.faulted`. Stopping immediately on target re-entry or
   terminal outcomes prevents `dsimp` from overshooting the loop header or
   spinning through remaining recursion fuel (`runToTarget_mono_bound`), and
   deriving `Nat.add (length body.basicBlocks) 256` inside `runCfgToBlock`
   exposes zero numeric step bounds at user call sites while avoiding user
   `dsimp only` unfold-list omissions.

On `WireframeDemo/checksum_frame_safe` (a 4-lane byte checksum loop) and
`checksum_frame_fast` (an unrolled word-wise fast path proved equivalent to
`checksum_frame_safe`), switching to `runCfgToBlock` + `forRangeUp` + exported
`safe_noCallWpConverges` cut `checksum_frame_safe` heartbeats from `180,914k` to
`64,596k` (`-64.3%`) and cut `checksum_frame_fast` from `432` LOC / `57.1 s` /
`655,752k` heartbeats to `174` LOC / `21.4 s` / `72,097k` heartbeats (`-89.0%`).

### F-07: Tier 2 Separation-Logic Lenses for Whole-Slot and Subplace `&mut`

`Basis: normative + source + execution + derived`

Functions that mutate caller state through `&mut T` references (such as
`WireframeDemo/advance_cursor(&mut Cursor, usize)`) fail Tier 1 `checkPureMir`
because dereference reads `(*p).field` and writes `(*p).field = v` touch
`Memory.callerLocals` and check Tree Borrows permissions (`Active` / `Reserved`
child tags and active function-entry protectors; Villani et al., PLDI 2025).

Tier 2 alias erasure (`SepLogicLenses`) recovers pure value reasoning without a
full Iris heap logic by packaging each mutable borrow as a lawful bidirectional
lens `MutLens S A` (Foster et al., TOPLAS 2007; mechanized in
`support/FuelFreeMirLiftingAndLensesProbe.lean:873-935`):

```lean
structure MutLens (S A : Type) where
  get : S → A
  put : S → A → S
  put_get : ∀ s v, get (put s v) = v
  put_put : ∀ s v₁ v₂, put (put s v₁) v₂ = put s v₂
  get_put : ∀ s, put s (get s) = s
```

Paired with `DisjointLenses l₁ l₂` (`l₁.get (l₂.put s b) = l₁.get s`, symmetric
read-over-write preservation, and write commutativity `l₁.put (l₂.put s b) a =
l₂.put (l₁.put s a) b`), the relational state invariant `SepLensStateInv` (for
distinct caller allocations) and `SepSubplaceLensStateInv` (for disjoint
projection prefixes `&mut s.fst` and `&mut s.snd` within the *same* caller
allocation via `MutLens.comp allocLens fstLens` and `MutLens.comp allocLens
sndLens`) maintain two invariants across `LiftLensBlock`:

1. Each `&mut` parameter's pointer provenance resolves to its dedicated lens
   footprint with a Tree Borrows child tag whose write transitions preserve the
   permissions of all sibling disjoint lenses (`invalidateDerefWriteBorrows`
   touches only overlapping byte ranges). Furthermore, when an aggregate
   allocation `.aggregate 0 (f₀ :: rest)` stores field `0` at root offset
   `(allocId, 0)`, resolving `(allocId, 0)` through `SubplaceLocalSepProp` to
   `field0` and its subplace child tag (`TreeFieldExclusiveBorrow`) rather than
   the whole struct proves that mutating any sibling field `fieldIdx > 0`
   preserves `field0`, the parent root tag, and `field0`'s tag without requiring
   root address `(allocId, 0)` to be unallocated (`AggregateSlot`,
   `writeSubplaceField1`, and `subplaceWrite_sibling_preserves_field0` in
   `support/FuelFreeMirLiftingAndLensesProbe.lean:1003-1024`).
2. Consequently, dereference reads and writes erase to pure `get`/`put` value
   transformations (`subplaceFieldLens_disjoint` and
   `liftLens_twoBorrowAdd_sound` in
   `support/FuelFreeMirLiftingAndLensesProbe.lean:916-935`), discharging
   `advance_cursor.lean` in `231` LOC and `5,504k` heartbeats (`3.0 s`) with
   zero manual fuel or alias case splits.

### F-08: Benchmark Synthesis, Amortization, and `whnf` / `kabstract` Scaling

`Basis: source + execution + derived`

#### 1. `WireframeDemo` 7-Function Proof Compression and Heartbeat Reduction

Table 1 summarizes the measured transition from the last complete hand-written
`BlockCtx`/fuel proof corpus to the normalized two-tier lifted proof corpus
across all seven `WireframeDemo` functions (full machine-readable metrics in
`support/wireframe_benchmark_metrics.json`; deterministic heartbeats measured in
thousands via `IO.getNumHeartbeats` under `-DElab.async=false` on Lean
`v4.34.1`):

| Function | Primary Lifting Route | Manual `BlockCtx` LOC | Lifted LOC | $\Delta$ LOC | `BlockCtx` (`Base` $\to$ `Lifted`) | Initial Lifted Heartbeats ($10^3$) | Normalized Heartbeats ($10^3$) | $\Delta$ Heartbeats | Seq. Wall Clock |
| :--- | :--- | ---: | ---: | ---: | :---: | ---: | ---: | ---: | ---: |
| `advance_cursor` | `verifyStatefulMir_of_sepLenses` + `LiftLensBlock` | 227 | 231 | +1.8% | `0 → 0` | 5,771 | 5,504 | -4.6% | 3.0 s |
| `checksum_frame_fast` | `verifyStatefulEquivMir_of_wpConverges` + `runCfgToBlock` | 1,592 | 174 | -89.1% | `28 → 0` | 655,752 | 72,097 | -89.0% | 21.4 s |
| `checksum_frame_safe` | `verifyStatefulMirNoPanic_of_wpConverges` + `forRangeUp` | 1,242 | 275 | -77.9% | `26 → 0` | 180,914 | 64,596 | -64.3% | 11.8 s |
| `clamp_payload_window` | `verifyMirNoPanic_of_pureExec` + `LiftBlock` rules | 1,595 | 187 | -88.3% | `26 → 0` | 187,030 | 186,993 | 0.0% | 22.2 s |
| `decode_wire_header` | `verifyMirNoPanic_of_pureExec` + `LiftBlock` (`eval_rest`) | 979 | 272 | -72.2% | `0 → 0` | 44,866 | 22,947 | -48.9% | 3.7 s |
| `frame_total_len` | `verifyMirNoPanic_of_pureExec` + `LiftBlock` rules | 1,268 | 169 | -86.7% | `23 → 0` | 249,768 | 250,106 | +0.1% | 32.4 s |
| `parse_compression_flag` | `verifyMirNoPanic_of_pureExec` + `LiftBlock` rules | 1,106 | 113 | -89.8% | `8 → 0` | 64,833 | 62,985 | -2.9% | 11.1 s |
| **Total** | | **8,009** | **1,421** | **-82.3%** | **`111 → 0`** | **1,388,934** | **665,228** | **-52.1%** | **105.6 s** |

Across all seven proofs, manual `BlockCtx` occurrences drop from `111` to `0`,
explicit CFG fuel numerals (`defaultCfgSteps`, `runCfgSteps`) and fixed tactic
round counts (`iterate k`) drop to `0`, no file raises `maxHeartbeats` above
`800,000`, and `trusted/lean/` incurs `0` bytes of diff during the proof
migration.

#### 2. Shared Theory Amortization

During the 7-function `WireframeDemo` proof migration, incremental proof-layer
additions contributed `+2,972` net LOC across reusable theory modules
(`MirLiftCore.lean` `1,594 → 4,480` `+2,886`, `MirLoops.lean` `651 → 692` `+41`,
`SepLogicLenses.lean` `13,655 → 13,677` `+22`, `SymReflect.lean` `7,125 → 7,301`
`+176`, removal of redundant `MirSpecLift.lean` `-139`, and `PureMirExec.lean`
cleanup `18,475 → 18,461` `-14`), before subsequent interprocedural and
intrinsic extensions brought the post-integration modules to `20,564` LOC
(`PureMirExec.lean`), `4,517` LOC (`MirLiftCore.lean`), `730` LOC
(`MirLift.lean`), and `13,718` LOC (`SepLogicLenses.lean`). Because the
7-function `WireframeDemo` crate alone shrinks by `6,588` LOC, the migration
theory delta (`2,972 / 6,588 = 45.11%`) amortizes more than $2\times$ within a
single small crate and carries zero marginal theory cost for subsequent crates.

#### 3. Four Lean 4 `4.34.1` Elaboration Scaling Traps and Remedies

Profiling the post-integration simulation and translation modules
(`PureMirExec.lean` at `20,564` LOC and `FunctionalTranslationTests.lean`) with
`-Dprofiler=true` isolated four general Lean 4 kernel/elaborator performance
traps:

1. **Per-Step `dsimp only` `SimpTheorems` Discrimination-Tree Rebuilds (`53 s →
   5 s`):** Passing an 80-symbol `dsimp only [...]` list on every small step of
   a MIR interpreter forces Lean 4 to rebuild a transient `SimpTheorems`
   discrimination tree indexing `~400` generated equation lemmas per step.
   Replacing `dsimp only` stepping with raw-state `whnf` `rfl` transitions and
   minimal per-construct unfold lists cut `FunctionalTranslationTests` compile
   time by $10.6\times$ (`53.0 s → 5.0 s`).
2. **Inline `match` Scrutinees Failing `kabstract` Inside `cases` (`85 s → 51 s
   → 35.1 s`):** Running `cases` on a scrutinee containing an unreduced inline
   `match` (such as `match expected with | true => 1 | false => 0` or `match
   currentBody with | .some b => b.layouts | .none => emptyLayoutTable`) creates
   a local auxiliary matcher `_match_k` that fails `kabstract` syntactic
   matching against a compiled auxiliary matcher inside `Trusted/`, leaving the
   goal LHS unabstracted before `rfl`. Hoisting `cases expected` / `cases
   currentBody` *before* the outer `cases` iota-reduces both sides first,
   allowing deletion of `187` lines of synchronous nested-`match` restatement
   boilerplate and cutting `PureMirExec.lean` standalone compile time from
   `85 s` to `35.1 s` (`.olean` size `38 MB → 32 MB`).
3. **Higher-Order `unfold` + `change` over Multi-Variant Phase Matches:**
   Unfolding a top-level dispatcher (`stepMirFn`) and unifying against an
   explicit multi-arm `match curBody.phase` term spent `~5.5 s` of CPU across
   five proofs; factoring a boolean `if isRuntimeMirPhase ... then ... else ...`
   bridge lemma (`stepMirFn_eq_ite`) reduced dispatch rewriting to constant
   time.
4. **Cross-Module `_private` Equation-Lemma Realization Collisions:** When two
   independent downstream modules (`PureMirExec` and a test module) both trigger
   lazy realization of `evalRvalue.eq_28` or `evalOperands.eq_def`, Lean embeds
   module-private `_private.<Mod>.0.*` splitter helpers into the realized proof
   terms, causing `importModules` environment merges in standalone `.olean`
   auditors to flag foreign private helper collisions. Replacing bare
   `evalRvalue` / `evalOperands` entries in `simp only` with
   constructor-specific `rfl` projection lemmas reduced cross-module collisions
   to `0` across all `31` audited downstream targets.

## Boundaries

- **Parametric Bodies in `#mir_lift` and Closure-Capturing `#[spec]` Companions
  (`unsupported`):** The `#mir_lift` command elaborator (`MirLift.lean`)
  operates only on closed (`argCount = 0`) `CapturedMir` constants outside
  `TrustedBoundary`; parametric (`argCount > 0`) `Proof/*.lean` targets are
  **unsupported** by `#mir_lift` and instead apply the `LiftBlock` /
  `LiftStmtsTerminator` rules directly. Similarly, pure companion lifting
  (`mirBoolPredicateHolds_*_of_pureExec`) requires `checkPureMir = true`;
  closure-capturing companions (`&x`, emitting `Rvalue.ref` and
  `ProjectionElem.deref`) are **unsupported** by Tier 1 pure lifting and must
  use `holdBoolReq_of_mirBool` + count-free `repeat` and
  `hold_mirBool_of_blockLinear` (`defaultSpecSteps`).
- **Interior Mutability, Raw-Pointer Arithmetic, and Dynamic Allocation Aliasing
  (`known not to apply` for Tier 1; `unsupported` for Tier 2 `MutLens`):** Tier
  1 `checkPureMir` explicitly rejects `.deref`, `Rvalue.rawPtr`,
  `CastKind.ptrToPtr`, and `BinOp.offset`, so Tier 1 alias erasure is **known
  not to apply** to any pointer-dereferencing body. Tier 2 `SepLogicLenses`
  models statically disjoint exclusive `&mut` borrows (requiring `.active` Tree
  Borrows permissions rather than shared `&T` references) and disjoint
  struct-field subplaces, and currently leaves `UnsafeCell` interior mutability,
  overlapping raw-pointer arithmetic (`ptr::add`), heap allocator reuse, and
  cyclic/re-entrant borrow graphs **unsupported**.
- **Unbounded `while` Loops, Diverging Reactive Loops, and Unwinding Paths
  (`known not to apply` for `forRangeUp` / `MirWpConverges`):** `forRangeUp`
  governs finite `[lo, hi)` loops with a structural `hi - i` measure, and
  `MirWpConverges` characterizes terminating normal-return executions. Infinite
  event loops (`loop {}`), reactive trace emission, and panic-unwinding cleanup
  paths are **known not to apply** and must be reasoned about directly over the
  TCB's `ReachesPrefix` and `eventualBehaviorOf` relations.
- **Automated Loop-Invariant Synthesis and Multi-Crate Scale (`not examined`):**
  `forRangeUp` requires a human- or agent-supplied loop invariant `inv : Nat →
  α → State → Prop`, and empirical LOC/heartbeat measurements in
  `support/wireframe_benchmark_metrics.json` cover the 7-function
  `WireframeDemo` suite, `FrameTutor` (6 files), and `MirVerification` rather
  than multi-thousand-line crates (`not examined`). Whether SMT-backed invariant
  inference (`lean-auto` / `grind`) further reduces `forRangeUp` proof size on
  nested byte-slice loops remains **unknown**.

## Evidence

- **Self-Contained Lean `4.34.1` Mechanization
  (`support/FuelFreeMirLiftingAndLensesProbe.lean`, 1027 lines):**
  - `FuelOrder`, `FuelOrder.{refl, trans, halted_stable}`, `evalFuel`,
    `evalFuel_mono`, `WpConverges`, `WpConverges.of_done`, `StepsTo`,
    `StepsTo.bind_wp` (Lines 55–144): Kleene fuel monotonicity and existential
    fuel synthesis (`F-01`).
  - `Memory`, `SlotState`, `MachineState`, `PureState`, `MirFrameSim`,
    `checkPureStmt`, `checkPureProg`, `checkPureProg_rejects_deref`,
    `stepPure_simulates`, `evalFuel_of_pureExec`, `wpConverges_of_pureExec`
    (Lines 152–349): Tier 1 syntactic purity and once-and-for-all `Memory`
    erasure (`F-02`).
  - `ToyBlock`, `CfgState`, `stepCfg`, `LiftBlock`, `LiftBlock.of_cont`,
    `twoDiamondCfg`, `liftBlock_diamond_shared`, `forcePureEnv`,
    `set_eq_of_forcePureEnv`, `chained_sets_collapse_rfl` (Lines 355–465):
    Opaque-`post` two-diamond sequential sharing and spine-eager slot-list
    normalization by `rfl` (`F-03`).
  - `forRangeUpAux`, `forRangeUp`, `forRangeUp_eq_init_of_ge`,
    `forRangeUpAux_induction`, `forRangeUp_induction`,
    `wpConverges_forRangeUpAux`, `wpConverges_forRangeUp`, `TargetOutcome`,
    `runUntilTarget`, `runToTarget`, `stepsTo_of_runToTarget_reached`,
    `wpConverges_of_runToTarget_halted`, `runToTarget_mono_bound`,
    `runCfgToBlock`, `stepsTo_of_runCfgToBlock_reached`,
    `wpConverges_of_runCfgToBlock_halted`, `LoopState`, `countUpBlocks`,
    `stepCountUp`, `no_uniform_fuel_countUp`, `countUp_wpConverges_all_n` (Lines
    470–867): Block-targeted mandatory-step and early-halting soundness,
    impossibility of uniform constant fuel on symbolic bounds, and zero-numeral
    operational loop convergence (`F-01`, `F-06`).
  - `MutLens`, `MutLens.comp`, `DisjointLenses`, `fstLens`, `sndLens`,
    `subplaceFieldLens_disjoint`, `liftLens_twoBorrowAdd_sound` (Lines 873–935):
    Tier 2 bidirectional lenses and sibling-field reborrow disjointness
    (`F-07`).
  - `signExtendMod`, `signExtendMod_nonneg_id`, `pushBaseStack`,
    `pushBaseStack_step_comm`, `TransmuteVal`, `evalTransmuteCast`,
    `instantiated_transmute_roundtrip`, `AggregateSlot`, `writeSubplaceField1`,
    `subplaceWrite_sibling_preserves_field0` (Lines 941–1024): Closed-form
    two's-complement sign extension, stack-suffix callee frame invariance,
    monomorphic `transmute` layout and function-pointer provenance preservation,
    and field-`0` vs. root-offset `(allocId, 0)` subplace framing (`F-02`,
    `F-07`).
- **Preserved Empirical Dataset and Automated Verifier (`support/`):**
  - `support/wireframe_benchmark_metrics.json`: Per-function LOC, `BlockCtx`
    counts, manual fuel counts, deterministic elaboration heartbeats
    (`IO.getNumHeartbeats`, `-DElab.async=false`), sequential wall-clock times,
    companion isolation timings, shared-theory migration deltas (`+2,972` LOC),
    and post-integration module LOC (`PureMirExec.lean` `20,564` LOC) + scaling
    measurements observed on `2026-11-07` (`F-05`, `F-06`, `F-08`).
  - `support/verify_probes.py`: Standalone Python 3 verification script checking
    80-column formatting and string-preserving comment-stripped absence of
    `sorry`/`admit`/`axiom`/`native_decide`, running Lean `4.34.1` on
    `FuelFreeMirLiftingAndLensesProbe.lean`, auditing `#print axioms` on all 22
    exported theorems (`propext` / `Quot.sound` only), verifying zero fuel/step
    numerals in `countUp_wpConverges_all_n`, cross-checking report probe line
    citations and prose width, and verifying every sum, delta, ratio, and module
    LOC figure in `wireframe_benchmark_metrics.json`.
- **Primary Upstream Source and Literature Coordinates:**
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`
    (`v4.34.1`): kernel `whnf`, `Meta/KAbstract.lean`,
    `Meta/Tactic/Simp/SimpTheorems.lean`, and `Elab/Command.lean`.
  - `rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
    (`1.98.0-nightly`): `compiler/rustc_middle/src/mir/syntax.rs` (`Rvalue`,
    `StatementKind`, `TerminatorKind`, `ProjectionElem`).
  - `joshlf/anneal` at `5fc1139f2208b3c9cfb513573c4a731cc32bb457`
    (`docs/{architecture,design,trust-model}.md`),
    `f2bc17e9be87b777d63c785b31f3370ff058d69b`
    (`trusted/audit/TrustedBoundary.lean`), and
    `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` (baseline repository snapshot).
  - Literature: Myreen, Gordon, and Slind (FMCAD 2012,
    `10.1109/FMCAD.2012.6462558`, IEEE Xplore `6462558`), Owens et al. (ESOP
    2016, `10.1007/978-3-662-49498-1_23`), Villani et al. (PLDI 2025,
    `10.1145/3735592`), Ho & Protzenko (ICFP 2022, `10.1145/3547647`),
    Charguéraud et al. (TOPLAS 2023, `10.1145/3579834`), Xia et al. (POPL 2020,
    `10.1145/3371119`), Foster et al. (TOPLAS 2007, `10.1145/1232420.1232424`).

## Revalidation

From the package directory
(`reports/anneal-fuel-free-mir-lifting-and-alias-erasure/`), run the standalone
probe and dataset verifier:

```bash
python3 support/verify_probes.py
```

This single command:
1. Checks `support/FuelFreeMirLiftingAndLensesProbe.lean` with Lean `v4.34.1`
   (automatically wrapping in `anneal-lean-run --mode file --concurrency 1` when
   installed) and asserts exit status `0`, `<= 80`-column formatting, and zero
   warnings or stdout/stderr;
2. Audits `#print axioms` across all 22 mechanized theorems to confirm
   constructive validity (zero `sorryAx`, zero `Classical.choice`) and verifies
   that `countUp_wpConverges_all_n` contains zero fuel/step numerals; and
3. Recomputes and cross-checks every per-function and aggregate LOC, `BlockCtx`,
   heartbeat, shared-theory amortization, and post-integration module LOC figure
   in `support/wireframe_benchmark_metrics.json`, plus `REPORT.md` /
   `REPORT.json` probe declaration line citations, 80-column prose width, and
   public-hygiene invariants.

When updating the report metadata or checking corpus-wide invariants from the
`reference` repository root, run:

```bash
python3 tools/reference.py catalog
python3 tools/reference.py check
```
