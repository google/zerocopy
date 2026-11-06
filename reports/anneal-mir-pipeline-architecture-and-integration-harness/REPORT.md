# Anneal Three-Stage MIR Verification Pipeline Architecture, Soundness Refinement, Dual-Profile Capture, and Integration Test Harness

## Summary

### Part I — Three-Stage MIR Pipeline Architecture, Place Initialization, PME Completeness, Assert Semantics, and Stage 3 Lowering

Anneal verifies Rust crates across a three-stage pipeline (`docs/architecture.md:102-146`
at `d79b0c070cf4115b523fe6ee62c1e72504de2254`):

1. **Stage 1 (`trusted/rustc-capture`)** intercepts `rustc`'s
   `mir_drops_elaborated_and_const_checked` query (`Runtime(PostCleanup)` MIR)
   and emits a pure Lean 4 crate AST (`Mir.lean`), specification stubs
   (`Spec.lean`), and top-level theorem target (`Theorem.lean`).
2. **Stage 2 (`trusted/lean/Trusted/`)** defines the Trusted Computing Base
   (TCB) MIR syntax (`MirAst.lean`), small-step operational semantics and
   post-monomorphization checks (`MirSemantics.lean`), step-indexed trace
   refinement (`StepResult.lean`), and abstract `Language`/`Tool` verification
   interfaces (`Refinement.lean`), audited at the `.olean` kernel level by
   `trusted/audit/TrustedBoundary.lean` and `trusted/audit/src/lib.rs`.
3. **Stage 3 (`theory/Anneal/`)** proves verified semantic lemmas, Stage 3 IR
   simplifications, and `decide`-driven bounded symbolic execution in
   `theory/Anneal/MirLemmas.lean` outside the TCB.

Cross-checking the Stage 1 extractor (`trusted/rustc-capture/src/`), Stage 2
semantics (`trusted/lean/Trusted/`), `.olean` boundary auditor
(`trusted/audit/`), and Stage 3 proof engine (`theory/Anneal/`) against `rustc`
(`1.96.0-nightly` and `1.98.0-nightly`) and Lean 4 (`v4.28.0` and `v4.34.1`)
establishes five load-bearing soundness and architectural results:

- **F-01 (Partial Moves and Path-Sensitive `.uninit`):** Translating projected
  moves (`Operand::Move(_1.0)`) to a non-destructive `Rvalue.field0` read
  (`trusted/rustc-capture/src/extract.rs:472-485`,
  `trusted/lean/Trusted/MirSemantics.lean:589-597`) is unsound when
  `StorageDead(_1)` is absent or deferred on non-`Copy` types, allowing a moved
  field or whole aggregate to be read a second time. Conversely, resetting the
  entire root local `_1` to `none` breaks valid Rust programs that subsequently
  move or read sibling fields (`_1.1`). Representing places compositionally as
  `(LocalId, List PlaceElem)` with a leaf `MirVal.uninit` constructor written back
  at the moved projection path—gated by recursive `isFullyInitFuel` checks on
  (a) terminal whole-value reads (`proj = []`), (b) intermediate `.deref` hops,
  and (c) terminal reference creation (`Rvalue.ref`)—restores exact
  field-granularity initialization soundness.
- **F-02 (`StatementKind::PlaceMention` Erasure and `-Z mir-preserve-ub`):**
  Under default compiler flags, `rustc`'s `RemovePlaceMention` pass
  (`3-1-002.RemovePlaceMention`) erases `PlaceMention((*_1))` before
  `3-2-000.runtime-post-cleanup` (`mir_drops_elaborated_and_const_checked`),
  causing `unsafe { let _ = *dangling_ptr; }` and `let _ = partially_moved;` to
  vanish before Stage 1 capture (`extract.rs:529-549`). Passing
  `-Z mir-preserve-ub` retains `StatementKind::PlaceMention` in
  `Runtime(PostCleanup)` MIR, and evaluating `Stmt.placeMention p` via
  `evalPlaceRead` (including `isFullyInitFuel`) rejects invalid dereferences and
  uninitialized places.
- **F-03 (Post-Monomorphization Error Completeness via Two-Stage `ConstsTotal`
  and `MonoAdmitted`):** Syntactically dead generic branches such as
  `if false { let _ = Fail::<T>::C; }` are never reached by dynamic execution of
  `basic_blocks` (and are erased from `basic_blocks` in `Runtime(Optimized)` by
  `SimplifyConstCondition` + `SimplifyLocals`), yet `rustc` records
  `Fail::<T>::C` in `Body::required_consts` (and `Body::mentioned_items` for
  functions, drops, and closures in `optimized_mir`) and rejects
  `dead_branch_pme::<u8>()` during monomorphization with `error[E0080]`.
  Single-quantifier PME predicates either lock out valid compile-time guards
  (`const { assert!(size_of::<T>() == 8); }`, as in
  `theory/Anneal/MirLemmas.lean:3726-`) if they require `ConstSucceeds` over
  all `ValidTySizes`, or fail open vacuously if `evalTyByteSize ... = some sz`
  is placed on the left-hand side of an implication on `.unsupported` or
  oversized types. A two-stage predicate—`ConstsTotal` requiring positive type
  sizing (`∃ sz`) and `ConstSucceeds ∨ ConstUnwinds` over all `ValidTySizes`
  (`≤ maxTypeSize`), paired with `MonoAdmitted` requiring `ConstSucceeds` and
  valid mentioned-type layouts at the active `s.tySizes` in `initMirState`—is
  both sound and non-vacuous.
- **F-04 (Compiler-Inserted `TerminatorKind::Assert` vs. `core::panicking::panic`
  and Multi-Config `CONFIGS`):** `rustc` lowers checked integer arithmetic
  (`+`, `-`, `*`), division/remainder (`/`, `%`), and bounds checks to
  `TerminatorKind::Assert`, whereas user `assert!(...)` and
  `const { assert!(...) }` lower to `SwitchInt` + `TerminatorKind::Call` to
  `core::panicking::panic`. Because `PrefixOutcome.isSafe`
  (`trusted/lean/Trusted/StepResult.lean:59-63`) treats `.terminated .unwind` as
  safe and `EnsuresRetLibInv` (`MirSemantics.lean:1011-1015`) only constrains
  normal returns, stepping `Terminator.assert` failure to `.unwind` makes
  `bad_overflow(x: u8)` (`let y = x + 1; if y == 0 { unsafe { unreachable_unchecked() } }`)
  verify as safe under `-C overflow-checks=on` (`x = 255` unwinds) while
  executing `unreachable` Undefined Behavior (`.failed`) in `--release`
  (`-C overflow-checks=off`, where `255 + 1` wraps to `0`). `Terminator.assert`
  failure must therefore step to `.failed`, `CONFIGS`
  (`trusted/rustc-capture/src/main.rs:325-328`) must hold `-C overflow-checks=on`
  and `-Z mir-preserve-ub` invariant across `-C debug-assertions=on/off`, and
  emitted `BodyId`/`AdtId`/`SpanId` indices must be assigned by deterministic
  reachability order rather than raw `LocalDefId::local_def_index` (which shifts
  when `#[cfg(debug_assertions)]` items are present).
- **F-05 (Flat `BodyId` Tables, `.olean` Boundary Constraints, Frame-Relative
  `returnRefsOk`, and In-Place Stage 3 `lowerBody`):** Embedding `MirBody` by
  value inside `Terminator.call1` (`trusted/lean/Trusted/MirAst.lean:193-235`)
  forces a `mutual inductive` block whose structural recursion cannot be
  elaborated in `SourceRole.trusted` without `.olean`-forbidden `._unsafe_rec`
  or `WellFounded.fix` (`trusted/audit/TrustedBoundary.lean:208-239, 644-665`),
  compelling Stage 3 (`theory/Anneal/MirLemmas.lean:305-308, 3549-3560`) to use
  manual `@Terminator.casesOn` and fuel-bounded `beqMirBodyFuel 8`. Replacing
  inline `MirBody` trees with a flat `BodyId`-indexed `BodyDecl` table,
  replacing five dummy `opaque Target*` declarations
  (`MirSemantics.lean:1045-1108`) with `Obligation.assumed`, making
  `returnRefsOk` frame-relative (`s.frameId == 0` vs. `targetFrameId < s.frameId`),
  and canonicalizing PC coordinates in `MirReturn` enables in-place
  `BlockId`-preserving Stage 3 `lowerBody : MirBody → MirBody` simulation.

### Part II — Integration Test Harness Architecture, Path-Independent Dual-Profile MIR Capture, and Two-Stage Boundary Validation

- **Twelve of nineteen historical `google/zerocopy` Anneal/Hermes integration
  test failure modes are eliminated by construction in `joshlf/anneal`, while
  seven survive or mutate into new forms.** Replacing Charon, Aeneas, Lake, and
  Mathlib with direct `rustc_driver` `Runtime(PostCleanup)` capture
  (`anneal-rustc-capture`), direct `lean` CLI compilation over a 10-module
  prefix, and `.olean` kernel environment inspection (`anneal-audit`) removes
  `.lake/packages/mathlib` disk amplification, Lake lockfile churn, `Lake.DSL`
  elaboration OOMs, and Cargo `RUSTC_WORKSPACE_WRAPPER` cache poisoning.
  However, process-local `BUILT_CAPTURE` and `PREFIX_CACHE` lifetimes, quadratic
  $O(N^2)$ `Proof.lean` reduction scaling under fixture coalescing, opaque
  `Anneal.proveCrate Mir.crate rfl` negative test errors, strict target crate
  file allowlists, and dual-profile (`debug` vs. `release`) MIR divergence
  remain active architectural constraints.
  Basis: Direct source inspection of `joshlf/anneal` at
  `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)` and `google/zerocopy` at
  `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`, paired with empirical timing and
  memory probes in `support/capture_and_scaling_metrics.json`.

- **`anneal-rustc-capture` emits byte-for-byte deterministic `Mir.lean` files
  across arbitrary filesystem paths without `--remap-path-prefix`.** The
  extractor locks `src/lib.rs` by `(st_dev, st_ino)` via `GuardedFileLoader`,
  hooks `mir_drops_elaborated_and_const_checked` before `Steal<Body>` is stolen
  by `mir_for_ctfe` or `optimized_mir`, keys all item and body tables by
  crate-local `DefIndex` in `BTreeMap`/`BTreeSet` with topological dependency
  sorting, and omits source spans and file paths from `Mir.lean`. Capturing the
  same crate from shallow and deeply nested directory trees produces identical
  792-byte outputs (`SHA-256 =
  44e0972a75b52b1a7a1dd9dab8a8bd0f9366f18b3ab7fe0415de46352e79d594`).
  Basis: Source inspection of
  `trusted/rustc-capture/src/{main,hook,items,lean}.rs` at
  `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)` and empirical determinism probe in
  `support/capture_and_scaling_metrics.json`.

- **Every `anneal-rustc-capture` invocation runs two sequential in-process
  `rustc_driver::run_compiler` passes (`debug` and `release`) in `21.7–23.2 ms`
  (`78.4 MB` max RSS) and rejects any crate whose captured `Mir.lean` differs
  between profiles.** Checked integer arithmetic (`x + 1`), `debug_assert!`, and
  `#[cfg(debug_assertions)]` fail closed because `-Cdebug-assertions` and
  `-Coverflow-checks` alter `Runtime(PostCleanup)` MIR. By contrast,
  `wrapping_add`, integer division `x / y` (which emits an unconditional
  division-by-zero `TerminatorKind::Assert` in both profiles), and raw pointer
  dereferences produce identical `Mir.lean` across both configurations.
  Basis: Source inspection of
  `trusted/rustc-capture/src/main.rs:342-345,569-578` and empirical dual-profile
  probes in `support/capture_and_scaling_metrics.json`.

- **Diagnostic and unsupported-construct handling splits across five distinct
  layers: four fail-fast `anneal-rustc-capture` layers and one fail-closed Lean
  `MirAst` sentinel layer.** CLI validation (`main.rs`), input detective checks
  (`check_inputs`), crate item inventory (`items.rs`), and doc-comment parsing
  (`spec.rs`) abort capture with `anneal-rustc-capture: unsupported crate: ...`
  and exit code `1`. Conversely, `extract.rs` lowers unsupported types,
  statements, Rvalues, and terminators inside function bodies into `.unmodeled`
  and `.unsupported` `MirAst` constructors so private uncalled helpers do not
  break capture; public functions containing those sentinels fail closed during
  Lean proof checking.
  Basis: Source inspection of
  `trusted/rustc-capture/src/{main,items,spec,extract}.rs` and empirical
  diagnostic probes in `support/capture_and_scaling_metrics.json`.

- **`validate_target_crate` and `check_cargo_boundary` require integration test
  fixtures to materialize into clean temporary crate directories
  (`TempCrateDir`) executed by a zero-dependency Rust test harness.**
  `validate_target_crate` enforces a closed 5-file allowlist (`CRATE_FILES`) and
  `#[serde(deny_unknown_fields)]` on `Cargo.toml`, rejecting any fixture
  directory that contains sidecar test metadata (`anneal.toml`,
  `expected.stderr`, or `target/`). Furthermore, because `BUILT_CAPTURE`
  (`1.90s`) and `PREFIX_CACHE` (`15.13s`) are process-local `static
  Mutex<BTreeMap<...>>` caches and `trusted/root-manifest.sha256` locks the
  129-package `Cargo.lock`, running fixtures in-process through
  `cargo_anneal::run_with_io` inside a single zero-dependency integration test
  binary avoids both `17.03s` per-process cold rebuilds and TCB dependency
  bloat.
  Basis: Source inspection of `trusted/cargo-anneal/src/lib.rs:536-687,860,1076`
  and `trusted/cargo-anneal/tests/verify_id.rs` at
  `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)`.

## Applicability

### Part I — Three-Stage MIR Pipeline Architecture, Place Initialization, PME Completeness, Assert Semantics, and Stage 3 Lowering

These findings apply to:

- **`joshlf/anneal` (`flat-BodyId minimal-TCB` branch at commit
  `d79b0c070cf4115b523fe6ee62c1e72504de2254 (with three-stage MIR pipeline definitions inlined above and preserved in `support/RefinementSoundnessProbes.lean`)` and `main` branch architecture
  documentation at commit `d79b0c070cf4115b523fe6ee62c1e72504de2254`):**
  - Stage 1 extractor and emitter: `trusted/rustc-capture/src/{main.rs, hook.rs, extract.rs, items.rs, ir.rs, lean.rs, spec.rs}`.
  - Stage 2 TCB definitions: `trusted/lean/Trusted/{Refinement.lean, StepResult.lean, MirAst.lean, MirSemantics.lean}` and `trusted/lean/foundation-lock.json`.
  - `.olean` and workspace boundary auditor: `trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/{lib.rs, main.rs}`, and `trusted/cargo-anneal/src/lib.rs`.
  - Stage 3 proof library: `theory/Anneal/{Refinement.lean, StepResult.lean, MirLemmas.lean}`.
- **Rust compiler (`rust-lang/rust`):**
  - `rustc 1.96.0-nightly` (`+nightly`, commit `fd0c901b00ee1e08a250039cdb90258603497e20`, LLVM 22.1.0).
  - `rustc 1.98.0-nightly` (`+nightly`, commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, LLVM 22.1.6).
- **Lean 4 theorem prover (`leanprover/lean4`):**
  - `v4.28.0` (commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`, pinned in `joshlf/anneal/lean-toolchain`).
  - `v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`).

### Part II — Integration Test Harness Architecture, Path-Independent Dual-Profile MIR Capture, and Two-Stage Boundary Validation

| Subject | Kind | Version | Revision |
| :--- | :--- | :--- | :--- |
| `joshlf/anneal` | repository | `flat-BodyId minimal-TCB` | `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)` |
| `google/zerocopy` | repository | `main` | `8fb35253fbc703cb2cd0997f4efcda76cf9062b6` |
| `rust-lang/rust` | repository | `1.98.0-nightly (2026-05-30)` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` |
| `leanprover/lean4` | repository | `v4.34.1` | `5045d0056413266e57c625dcd7c365b10e377c52` |

These findings apply to `joshlf/anneal`'s `flat-BodyId minimal-TCB` architecture at
`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)` (built atop `main` at
`c00e36ade29c57830f07c934774abb347471060c` and `StepResult-refinement baseline` at
`f938c18db56c49e82dde95506894a9b58b76b227 (with PME operational semantics formulation preserved in `support/`)`) under its pinned `rustc
1.98.0-nightly` and Lean `v4.34.1` toolchains (`trusted/toolchain.toml`).

### Inlined Core Anneal Refinement and MIR Semantic Definitions

To keep this reference self-contained without depending on unmerged prototype branches or external worktrees, the exact Lean 4 definitions of the core refinement, small-step machine, ADT invariant admissibility, interprocedural call, boolean AST equality, and crate-level verification judgments referenced across this report are reproduced below (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`, `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `theory/Anneal/MirLemmas.lean`):

```lean
/-- Constructive partiality carrier representing `B ∪ {UB}`: `defined` is
`False` exactly when the computation exhibits undefined behavior. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Query-indexed partial behaviors: for each query, either UB or a predicate
describing the set of permitted outcomes. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A semantic language with program-indexed initial-state domain `dom`. -/
structure Language where
  Prog  : Type
  Query : Type
  Out   : Type
  sem   : Prog → Behavior Query Out
  dom   : Prog → Query → Prop

/-- Domain-intersected precondition non-vacuity: some query is in `dom` *and*
satisfies `pre`. There is deliberately no "or `dom` is empty" alternative: an
empty domain is how a model limit at function entry shows up, so accepting it
would turn every such limit into vacuous verification. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn (L : Language)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog` against
`(pre, post)` within `prog`'s own domain `L.dom prog`. -/
def Language.Verified (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn (L.dom prog) pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- A named proof obligation with private constructor. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

/-- Obligation representing an explicit, unproved assumption (`prop := False`)
that can only be discharged when `id` appears in the crate's `waived` TCB list. -/
abbrev Obligation.assumed {Id : Type} (id : Id) : Obligation Id :=
  ⟨id, False⟩

/-- Waiver-aware verification judgment requiring distinct obligation IDs,
distinct waivers permitted by `policy`, and discharge of all unwaived obligations. -/
def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  NoDupIds (obligations.map Obligation.id) ∧
  NoDupIds waived ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))
```

```lean
/-- Admissibility of an ADT representation invariant `adtInv`
(`r[expr.struct.safety]`, `src/expressions/struct-expr.md`).
If safe code can build a struct directly (all fields public and safe), the
invariant must accept every structurally valid payload, in every state. -/
def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  NoDupIds (adts.map AdtDecl.id) ∧
  ∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ (s : MirState) (payload : MirTy) (inner : MirVal),
      decl.payloadTy = some payload →
      inner.valid adts defaultAdtInv s 0 payload →
      adtInv decl.id inner

/-- Lowered MIR block terminators, including static single-argument calls
`Terminator.call1` referencing a `BodyId` in `Crate.bodies` (or a nested
`MirBody` in the recursive first-order variant). -/
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | panic
  | unwindResume
  | unwindTerminate
  | drop (place : Place) (target : BlockId)
  | assert (cond : Operand) (expected : Bool) (target : BlockId)
  | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
  | switchIntGeneral (discr : Operand) (targets : List (Nat × BlockId))
      (otherwise : BlockId)
  | callSizeOf (dst : Place) (ty : MirTy) (target : BlockId)
  | callTransmuteCopy (dst : Place) (srcTy dstTy : MirTy) (op : Operand)
      (target : BlockId)
  | call1 (dst : Place) (callee : BodyId) (arg : Operand)
      (target : BlockId) (typeArgs : List MirTy := [])
  | call (dst : Place) (args : List Operand) (target : Option BlockId)
  | tailCall (args : List Operand)
  | yield (val : Operand) (resume : BlockId) (resumeArg : Place)
  | coroutineDrop
  | falseEdge (realTarget : BlockId) (imaginaryTarget : BlockId)
  | falseUnwind (realTarget : BlockId)
  | inlineAsm

/-- Per-function obligation inventory under `adts`, `bodies`, and `adtInv`. -/
def CapturedFn.obligations (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) : List (Obligation TCBItem) :=
  [
    Obligation.assumed (TCBItem.rustcLowering fn.name fn.bodyId),
    Obligation.wellFormedAndSpecsOn (TCBItem.fnVerified fn.name fn.bodyId)
      (MirLang adts bodies) (fn.effectivePre adts bodies adtInv)
      (fn.effectiveSpecs adts bodies adtInv) (fn.resolveBody bodies)
  ]

/-- Top-level theorem required of every verified Rust crate. -/
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  NoDupIds (c.bodies.map (fun d => d.id.index)) ∧
  NoDupIds (c.functions.map CapturedFn.name) ∧
  AdmissibleAdtInv c.adts c.adtInv ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResult defaultTrustPolicy c.tcb
      (fn.obligations c.adts c.bodies c.adtInv)))
```

```lean
/-- Fuel-bounded structural boolean equality on recursive `MirBody` trees
(before flat `BodyId` indirection). -/
noncomputable def beqMirBodyFuel : Nat → MirBody → MirBody → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    listBeq beqMirTy a.argTys b.argTys &&
    beqMirTy a.retTy b.retTy &&
    a.localCount == b.localCount &&
    listBeq (beqBasicBlock (beqMirBodyFuel fuel)) a.blocks b.blocks &&
    listBeq (beqRcPair (beqMirBodyFuel fuel)) a.requiredConsts b.requiredConsts

/-- Fuel-free structural boolean equality on `MirBody`, enabled by flat `BodyId`
indirection in `Crate.bodies`. -/
def beqMirBody (a b : MirBody) : Bool :=
  listBeq beqMirTy a.argTys b.argTys &&
  beqMirTy a.retTy b.retTy &&
  a.localCount == b.localCount &&
  listBeq beqBasicBlock a.blocks b.blocks &&
  listBeq beqRcPair a.requiredConsts b.requiredConsts
```

## Findings

### Part I — Three-Stage MIR Pipeline Architecture, Place Initialization, PME Completeness, Assert Semantics, and Stage 3 Lowering

#### F-01: Partial Moves Out of Composite Places (`Operand::Move(_1.0)`) and Path-Sensitive `MirVal.uninit`

`Basis: source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. In `trusted/rustc-capture/src/extract.rs:456-487`, `BodyCx::rvalue`
     translates `mir::Rvalue::Use(mir::Operand::Move(p), _)` when
     `!p.projection.is_empty()` and `p.projection == [ProjectionElem::Field(0, _)]`
     on a local struct to `ir::Rvalue::Field0(local_index(l))` (lines 472–485),
     identical to `Operand::Copy(_l.0)` (lines 458–471). In
     `trusted/lean/Trusted/MirSemantics.lean:589-597`, `evalMirStmt` evaluates
     `.assign dst (.field0 src)` as a non-destructive read that leaves
     `s.locals src.index` unchanged, whereas bare-local `evalOperand` on
     `.move src` (`MirSemantics.lean:501-506`) sets
     `updateLocal locals src.index none`.
  2. When a non-`Copy` aggregate field is moved (`let a = p.0;`), `rustc` emits
     `_2 = move (_1.0: NonCopy)` in `Runtime(PostCleanup)` MIR without emitting
     `StorageDead(_1)` until `_1` exits scope. Under the non-destructive
     `Rvalue.field0` semantics, a subsequent read or move of `_1.0` or of the
     whole struct `_1` succeeds (`nonDestructiveField0_allows_double_move`).
  3. Conversely, if `Operand::Move(p)` resets the entire root local `p.local` to
     `none`, moving `p.0` destroys sibling fields and causes valid Rust code
     `let a = p.0; let b = p.1;` (`partial_move_sibling`) to fail closed on
     `_3 = move (_1.1: NonCopy)` (`naiveRootReset_breaks_sibling_move`).
  4. Representing places compositionally as `Place = (LocalId, List PlaceElem)`
     (`PlaceElem := .deref | .field (idx : Nat)`), adding a leaf constructor
     `MirVal.uninit`, writing `MirVal.uninit` back to path `p` on
     `Operand.move p` via `updateProj`, and gating three operations with
     recursive `isFullyInitFuel` checks is both sound and complete for nested
     aggregates:
     - **Gate (a) — Terminal read (`proj = []` in `evalProjFuel`):** Rejects
       reading, moving, or place-mentioning `.uninit` or any `.adt`/`.tuple`
       containing `.uninit` at any nested leaf, while allowing `.field idx`
       steps to project initialized sibling fields out of partially moved
       aggregates (`pathSensitive_allows_sibling_field_move`,
       `pathSensitive_rejects_removed_field`,
       `pathSensitive_rejects_whole_aggregate_read`).
     - **Gate (b) — Intermediate dereference (`.deref :: rest` in
       `evalProjFuel` and `resolveRefTargetFuel`):** Evaluates `evalProjFuel` on
       the dereferenced target path `target.proj` (enforcing `isFullyInitFuel`
       on the referent value) before projecting `rest`, rather than
       concatenating `target.proj ++ rest`. Without Gate (b), if `r = &_1` is
       created while `_1` is fully initialized and `_1.0` is later moved,
       projecting `(*r).1` via path concatenation unsoundly reads sibling field
       `1` through an invalidated whole-struct reference
       (`pathSensitive_rejects_deref_projection_through_partially_moved_struct`).
     - **Gate (c) — Terminal reference creation (`proj = []` in
       `resolveRefTargetFuel` for `Rvalue.ref`):** Enforces `isFullyInitFuel` on
       the target value at `p` so borrowing `&_1` of a partially moved struct
       fails closed while borrowing an initialized sibling field `&(_1.1)`
       succeeds (`pathSensitive_rejects_whole_aggregate_ref_but_allows_sibling_ref`).
- **Evidence:**
  - `joshlf/anneal` (`d79b0c070cf4115b523fe6ee62c1e72504de2254 (with three-stage MIR pipeline definitions inlined above and preserved in `support/RefinementSoundnessProbes.lean`)`):
    `trusted/rustc-capture/src/extract.rs:437-516` (`BodyCx::operand`,
    `BodyCx::rvalue`), `trusted/lean/Trusted/MirAst.lean:64-131` (`Operand`,
    `Rvalue`), and `trusted/lean/Trusted/MirSemantics.lean:501-508, 589-605`
    (`evalOperand`, `evalMirStmt`).
  - Empirical `rustc` MIR capture in
    [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs)
    (lines 27–34, `partial_move_sibling`) and
    [support/mir_subtleties_output.json](support/mir_subtleties_output.json)
    (lines 18–26 and 199–207): across both `rustc 1.96.0-nightly` and
    `rustc 1.98.0-nightly`, `3-2-000.runtime-post-cleanup.after.mir` emits
    `_2 = move (_1.0: NonCopy);` followed by `_3 = move (_1.1: NonCopy);` with
    no `StorageDead(_1)`.
  - Mechanized Lean 4 proofs in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 35–286 (`nonDestructiveField0_allows_double_move`,
    `naiveRootReset_breaks_sibling_move`,
    `pathSensitive_allows_sibling_field_move`,
    `pathSensitive_rejects_removed_field`,
    `pathSensitive_rejects_whole_aggregate_read`,
    `pathSensitive_rejects_whole_aggregate_ref_but_allows_sibling_ref`,
    `pathSensitive_rejects_deref_projection_through_partially_moved_struct`).

---

#### F-02: `StatementKind::PlaceMention` Erasure in `Runtime(PostCleanup)` and Retention via `-Z mir-preserve-ub`

`Basis: source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. In `trusted/rustc-capture/src/extract.rs:529-549`, `BodyCx::stmt` rejects
     `mir::StatementKind::PlaceMention`, assuming that runtime cleanup passes
     have removed it alongside `FakeRead` and `AscribeUserType`.
  2. In `rustc` (`1.96.0-nightly` and `1.98.0-nightly`), place-mention bindings
     such as `unsafe { let _ = *p; }` (`place_mention_raw_ptr`) lower to
     `PlaceMention((*_1));` in `1-1-000.built.after.mir`. Under default flags,
     pass `3-1-002.RemovePlaceMention` erases `PlaceMention((*_1));` before
     `3-2-000.runtime-post-cleanup.after.mir`
     (`mir_drops_elaborated_and_const_checked`), leaving only `_0 = const (); return;`.
     Consequently, dereferencing a null or dangling pointer or mentioning a
     partially moved aggregate in `let _ = ...;` is erased before Stage 1
     inspects the `Runtime(PostCleanup)` body.
  3. Passing `-Z mir-preserve-ub` to `rustc` disables `RemovePlaceMention`,
     preserving `PlaceMention((*_1));` in both
     `3-2-000.runtime-post-cleanup.after.mir` and
     `3-3-000.runtime-optimized.after.mir`.
  4. Translating `mir::StatementKind::PlaceMention(place)` to
     `Stmt.placeMention place` and evaluating it via `evalPlaceRead` (which
     traverses projections, resolves intermediate dereferences, and enforces
     `isFullyInitFuel`) steps valid initialized places to `s.nextStmt s.locals`
     and steps dangling dereferences or uninitialized/partially moved places to
     `.failed` (`placeMention_rejects_dangling_and_partially_moved`).
- **Evidence:**
  - `joshlf/anneal` (`d79b0c070cf4115b523fe6ee62c1e72504de2254 (with three-stage MIR pipeline definitions inlined above and preserved in `support/RefinementSoundnessProbes.lean`)`):
    `trusted/rustc-capture/src/extract.rs:529-549` (`BodyCx::stmt`).
  - Empirical `rustc` MIR pass dumps in
    [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs)
    (lines 36–44, `place_mention_raw_ptr`) and
    [support/mir_subtleties_output.json](support/mir_subtleties_output.json)
    (lines 27–55 and 208–236).
  - Mechanized Lean 4 proof in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 288–317 (`placeMention_rejects_dangling_and_partially_moved`).

---

#### F-03: Post-Monomorphization Error (PME) Completeness Across `required_consts`, `mentioned_items`, and Two-Stage `ConstsTotal` / `MonoAdmitted`

`Basis: source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. In `rustc` (`1.96.0-nightly` and `1.98.0-nightly`), a constant referenced
     inside a syntactically dead branch (`if false { let _ = Fail::<T>::C; }` in
     `dead_branch_pme<T>`) is recorded in `Body::required_consts` during
     `1-1-008.PromoteTemps`. At `3-2-000.runtime-post-cleanup.after.mir`
     (`mir_drops_elaborated_and_const_checked`), `bb1` (`_3 = const Fail::<T>::C;`)
     is still present behind `_2 = const false; switchInt(move _2)`, while
     `Body::mentioned_items` is still `None` (`MentionedItems` runs in
     `optimized_mir` prior to `3-2-013.SimplifyConstCondition-after-inst-simplify`
     and `3-2-014.SimplifyLocals-before-const-prop`, which erase `bb1` from
     `3-3-000.runtime-optimized.after.mir`). When `dead_branch_pme::<u8>()` is
     monomorphized (`--emit=obj`), `rustc` evaluates `required_consts` and
     rejects the crate with `error[E0080]` (`evaluation of Fail::<u8>::C failed`).
     Conversely, code after an unconditional `return` (`return 0; let _ = Fail::<T>::C;`)
     is stripped by `1-1-006.SimplifyCfg-initial` before `PromoteTemps` and does
     not trigger `E0080`.
  2. Because dynamic execution of `dead_branch_pme` takes the `false` branch of
     `switchInt` and never reaches `bb1`, checking constants only when reached
     along dynamic execution traces misses PMEs in dead branches. Moreover, in
     `trusted/lean/Trusted/MirSemantics.lean:243` (`tySizeStep`), `.param idx => some (tySizes idx)`
     places no upper bound on `tySizes idx`, whereas `rustc` rejects any
     monomorphized type exceeding `isize::MAX` (`c.layout.maxTypeSize = 9223372036854775807`
     on 64-bit targets).
  3. Collapsing PME checking into a single quantifier exhibits two dual soundness/completeness hazards:
     - **Single-quantifier lockout (`SingleQuantifierStrictConstsTotal_locks_out_pme_guard`):**
       Requiring every reachable constant in `requiredConsts` / `mentionedItems`
       to evaluate to `ConstSucceeds` over *all* `ValidTySizes` makes
       `ConstsTotal` false whenever a generic function uses a compile-time PME
       guard (`const { assert!(core::mem::size_of::<T>() == 8); }`, as tested in
       `inlineConstPmeCrate` at `theory/Anneal/MirLemmas.lean:3726-`),
       because at `tySizes 0 = 1` the guard panics (`ConstUnwinds`). That empties
       `initMirState` and falsifies `NonVacuousOn`.
     - **Vacuous implication precondition (`ImplicationLHSConstsTotal_vacuous_on_unsupported_ty`):**
       Placing `mapOpt (evalTyByteSize c tySizes) typeArgs = some argSizes` on
       the left-hand side of an implication `→` makes `ConstsTotal` vacuously
       true whenever `typeArgs` contains `MirTy.unsupported` or a type whose size
       exceeds `maxTypeSize`, failing open even if the constant body triggers
       CTFE Undefined Behavior (`.failed`). Similarly, calling
       `instantiateBody c cid []` instead of `instantiateBody c cid typeArgs`
       fails the arity guard `body.typeParamCount == typeArgs.length` on generic
       constants.
  4. A **two-stage** PME predicate resolves both hazards (`twoStagePme_sound_and_nonvacuous`):
     - **Stage 1 (`ConstsTotal c b` across all `ValidTySizes c b.typeParamCount tySizes`):**
       Requires that no reachable body is `none` (`¬ ReachableBody c b none`) and
       that for every reachable required or mentioned constant `(cid, typeArgs)`,
       there *positively exist* (`∃ argSizes constBody`) evaluated byte sizes
       `mapOpt (evalTyByteSize c tySizes) typeArgs = some argSizes` and
       instantiated body `instantiateBody c cid typeArgs = some constBody` such
       that `ConstSucceeds c tySizes constBody ∨ ConstUnwinds c tySizes constBody`.
       This guarantees that no monomorphization ever triggers CTFE UB (`.failed`)
       or encounters an unmodeled type/body.
     - **Stage 2 (`MonoAdmitted c s.tySizes b` in `initMirState` at active `s.tySizes`):**
       Requires that every reachable `MentionedItem.tyLayout ty` has a valid
       layout (`∃ sz, evalTyByteSize c s.tySizes ty = some sz`) and every
       reachable required or mentioned constant satisfies
       `ConstSucceeds c s.tySizes constBody`. Including `MonoAdmitted` in
       `initMirState` gives runtime verification the exact hypothesis that
       compile-time `const { assert!(...) }` guards succeeded (e.g.,
       `s.tySizes 0 = 8`), while `NonVacuousOn` guarantees at least one admitted
       monomorphization exists.
- **Evidence:**
  - `joshlf/anneal` (`d79b0c070cf4115b523fe6ee62c1e72504de2254 (with three-stage MIR pipeline definitions inlined above and preserved in `support/RefinementSoundnessProbes.lean`)`):
    `trusted/rustc-capture/src/hook.rs:86-109`,
    `trusted/rustc-capture/src/extract.rs:196-203, 271-323`,
    `trusted/lean/Trusted/MirSemantics.lean:238-259, 895-983`, and
    `theory/Anneal/MirLemmas.lean:3721-3769` (`inlineConstPmeCrate`).
  - Empirical `rustc` MIR dumps and monomorphization probe in
    [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs)
    (lines 46–66, `Fail<T>::C`, `dead_branch_pme`) and
    [support/mir_subtleties_output.json](support/mir_subtleties_output.json)
    (lines 6–17 and 187–198).
  - Mechanized Lean 4 proofs in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 319–463 (`SingleQuantifierStrictConstsTotal_locks_out_pme_guard`,
    `ImplicationLHSConstsTotal_vacuous_on_unsupported_ty`,
    `twoStagePme_sound_and_nonvacuous`).

---

#### F-04: Compiler-Inserted `TerminatorKind::Assert` vs. `core::panicking::panic` (`assert!`) and Multi-Config `CONFIGS` Equivalence

`Basis: source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. Across `rustc 1.96.0-nightly` and `rustc 1.98.0-nightly`, user-level
     `assert!(x > 0)` (`explicit_assert`) and `const { assert!(...) }`
     (`Fail<T>::C`) lower to `TerminatorKind::SwitchInt` branching on failure to
     `TerminatorKind::Call` invoking `core::panicking::panic` (`Known::Panic` in
     `trusted/rustc-capture/src/extract.rs:120-131, 677-679`), under all four
     `(debug-assertions=yes/no) × (overflow-checks=yes/no)` combinations. By
     contrast, `TerminatorKind::Assert` (`extract.rs:567-568`) is emitted for
     compiler-inserted safety/overflow checks: checked arithmetic
     (`AddWithOverflow`, `SubWithOverflow`, `MulWithOverflow` when
     `-C overflow-checks=yes`), division/remainder by zero (`Div`, `Rem`), and
     bounds checks.
  2. In `trusted/lean/Trusted/StepResult.lean:59-63`, `PrefixOutcome.isSafe`
     defines `.terminated .unwind` as safe (`True`), and `EnsuresRetLibInv`
     (`trusted/lean/Trusted/MirSemantics.lean:1011-1015`) only constrains normal
     returns (`.terminated tr (.normal r)`). If `Terminator.assert` failure steps
     to `.terminated .unwind` (treating compiler-inserted `Assert` like user
     `panic!`), then on:
     ```rust
     pub fn bad_overflow(x: u8) -> u8 {
         let y = x + 1;
         if y == 0 {
             unsafe { core::hint::unreachable_unchecked() }
         }
         y
     }
     ```
     under `-C overflow-checks=yes` (debug mode), input `x = 255` sets the
     overflow flag in `AddWithOverflow(255, 1) = (0, true)` and steps via
     `Terminator.assert` to `.terminated .unwind` (`isSafe = True`), while all
     `x < 255` produce `y = x + 1 ≠ 0` and return normally. Thus `bad_overflow`
     verifies as sound (`naiveAssertUnwind_unsound_on_bad_overflow.1`)! Yet in
     `--release` (`-C overflow-checks=no`), `rustc` lowers `x + 1` to wrapping
     `BinOp::Add`, so `x = 255` wraps to `y = 0`, enters `if y == 0`, and
     executes `unreachable_unchecked()` (`.failed` — immediate Undefined
     Behavior, `naiveAssertUnwind_unsound_on_bad_overflow.2`).
  3. Stepping `Terminator.assert` failure to `.failed` (while keeping
     `Callee.panic` stepping to `.terminated .unwind`) rejects `bad_overflow` at
     `x = 255` in both debug and release modes and guarantees that any input
     proven free of `.failed` under `-C overflow-checks=yes` never overflows and
     therefore has identical semantics under `-C overflow-checks=no`
     (`fixedAssertFailed_sound_across_profiles`).
  4. In `trusted/rustc-capture/src/main.rs:325-328, 550-559`, `CONFIGS` runs
     `("debug", &["-Cdebug-assertions=on", "-Coverflow-checks=on"])` and
     `("release", &["-Cdebug-assertions=off", "-Coverflow-checks=off"])` and
     requires byte-for-byte identical `Mir.lean` output. Because `+`, `-`, and
     `*` lower to `AddWithOverflow` + `Assert` when `overflow-checks=on` and to
     `Add` without `Assert` when `overflow-checks=off`, varying `overflow-checks`
     in `CONFIGS` rejects every Rust function containing integer arithmetic!
     Holding `-C overflow-checks=on` and `-Z mir-preserve-ub` invariant across
     both `-C debug-assertions=on` and `-C debug-assertions=off` passes verifies
     both profiles when paired with `Terminator.assert` failure stepping to
     `.failed`.
  5. In `trusted/rustc-capture/src/hook.rs:86, 108` and `items.rs:193, 576`,
     items and bodies are indexed by raw `LocalDefId::local_def_index` (`DefIdx`).
     When a crate contains a `#[cfg(debug_assertions)]` item (`debug_only_helper`
     in `mir_subtleties_specimen.rs:68-71`), `rustc` includes it under
     `-C debug-assertions=yes` and omits it under `-C debug-assertions=no`,
     shifting `LocalDefId` indices of subsequent items. Assigning `BodyId`,
     `AdtId`, and `SpanId` sequentially by deterministic reachability order from
     root functions (keying the capture map by `DefPathHash`) makes emitted IDs
     invariant to unreferenced `#[cfg(debug_assertions)]` items.
- **Evidence:**
  - `joshlf/anneal` (`d79b0c070cf4115b523fe6ee62c1e72504de2254 (with three-stage MIR pipeline definitions inlined above and preserved in `support/RefinementSoundnessProbes.lean`)`):
    `trusted/rustc-capture/src/main.rs:325-328, 550-559`,
    `trusted/rustc-capture/src/hook.rs:86-109`,
    `trusted/rustc-capture/src/extract.rs:120-131, 567-568, 677-679`,
    `trusted/lean/Trusted/StepResult.lean:59-63`, and
    `trusted/lean/Trusted/MirSemantics.lean:1011-1015`.
  - Empirical `rustc` profile matrix in
    [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs)
    (lines 68–99) and
    [support/mir_subtleties_output.json](support/mir_subtleties_output.json)
    (lines 56–176 and 237–357).
  - Mechanized Lean 4 proofs in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 465–547 (`naiveAssertUnwind_unsound_on_bad_overflow`,
    `fixedAssertFailed_sound_across_profiles`).

---

#### F-05: Lean 4 TCB AST Structure, `.olean` Boundary Auditing (`TrustedBoundary.lean`), Frame-Relative `returnRefsOk`, and In-Place Stage 3 Lowering (`lowerBody`)

`Basis: documentation + source + execution + derived`

- **Status:** `confirmed`
- **Confidence:** `high`
- **Claim:**
  1. **Eliminating `mutual inductive` `MirBody` via Flat `BodyId` Tables:**
     In `trusted/lean/Trusted/MirAst.lean:193-235`, `Terminator`, `BasicBlock`,
     and `MirBody` form a `mutual inductive ... structure` block because
     `Terminator.call1` embeds `(callee : MirBody)` by value (line 214) and
     `MirBody.requiredConsts` embeds `List (MirBody × List MirTy)` (line 234).
     In `trusted/audit/TrustedBoundary.lean:208-239, 314-321, 644-665`,
     `SourceRole.trusted` modules (`trusted/lean/`) are restricted to
     `allowedTrustedSyntaxKinds` (forbidding `byTactic`, `partial`, `unsafe`,
     and `termination_by`/`decreasing_by`) and Phase 2 `.olean` auditing rejects
     any constant with `isUnsafe` (`._unsafe_rec`) or `isPartial`, as well as
     any reference to `WellFounded.fix`. Because Lean 4's structural recursion
     elaborator cannot reduce nested/mutual recursion over `MirBody` without
     `WellFounded.fix` or `._unsafe_rec`, Stage 3 (`theory/Anneal/MirLemmas.lean`)
     cannot derive `BEq MirBody` or use standard `match` in total recursive
     functions over `MirBody`, forcing manual `@Terminator.casesOn` recursors
     (`MirLemmas.lean:305-308`) and a fuel-bounded equality `beqMirBodyFuel 8`
     (`MirLemmas.lean:3549-3560`) that silently returns `false` on call chains
     deeper than 8. Replacing inline `MirBody` trees with a flat `BodyId`-indexed
     table `Crate.bodies : List BodyDecl` (where `BodyDecl` orthogonally pairs
     `payload : BodyPayload` with `contract : Option FnContract`) makes
     `Terminator` and `MirBody` non-recursive (`flatBody_decidableEq_refl`).
  2. **Replacing 5 Dummy `opaque Target*` Declarations with `Obligation.assumed`:**
     In `trusted/lean/Trusted/MirSemantics.lean:1045-1108`, five declarations
     (`TargetArtifact`, `rustc`, `opaque TargetSem`, `TargetLang`, `rustcCodec`)
     exist solely to construct an unprovable `Obligation.compiles` for
     `TCBItem.rustcLowering` (`MirSemantics.lean:1134-1135`). Defining
     `def Obligation.assumed {Id : Type} (id : Id) : Obligation Id := ⟨id, False⟩`
     in `Trusted/Refinement.lean` expresses unprovable, waiver-gated obligations
     (`rustcLowering`, `assumedContract`, `unverifiedFn`) in 2 lines with zero
     `opaque` symbols.
  3. **`foundation-lock.json` and `TrustedBoundary.lean` Syntax Allowlist
     Constraints:**
     `trusted/lean/foundation-lock.json` locks only the 38 `Init.*` modules
     transitively imported by `Init.NotationExtra` and `Init.Core` (including
     `Init.Data.String.Bootstrap` rather than `Init.Data.String.Basic`, and
     `Init.Data.Int.Basic` without `Init.Data.Int.Order`). In addition,
     `TrustedBoundary.allowedNotationSyntaxKinds`
     (`TrustedBoundary.lean:274-280`) permits only `+`, `-`, `*`, `/`, `%`, `<`,
     `≤`, `>`, `≥`, `=`, `≠`, `==`, `!=`, `&&`, `||`, `!`, `++`, `::`, `∧`, `∨`,
     `¬`, `↔`, and `∈`, rejecting unary negation (`` `«term-_» ``),
     exponentiation (`` `«term_^_» ``), and `∉` (`` `«term_∉_» ``) in
     `SourceRole.trusted` and `SourceRole.spec` files (requiring `Nat.pow`,
     `Int.negOfNat`, and `¬ (... ∈ ...)`).
  4. **Frame-Relative `returnRefsOk` (`Bool`):**
     In `trusted/lean/Trusted/MirSemantics.lean:307-326`, `MirVal.returnRefsOk`
     checks whether references inside a return value outlive the returning stack
     frame. Returning `Bool` (rather than `Prop`) allows `evalMirTerminator` to
     branch via `if ... then` without `Decidable` instances or tactics inside
     `SourceRole.trusted`. Furthermore, the survival check must be
     frame-relative (`returnRefsOk_frame_relative_correctness`): at the root
     frame (`s.frameId == 0`), a returned reference must target frame `0` at a
     caller-owned slot (`localCount ≤ targetLocalIdx`), whereas at an inline
     callee frame (`s.frameId > 0`), any reference targeting a strictly older
     caller frame (`targetFrameId < s.frameId`) survives callee exit even when
     `targetLocalIdx < calleeBody.localCount`.
  5. **In-Place Stage 3 Lowering (`lowerBody : MirBody → MirBody`) and
     PC-Canonicalized `MirReturn`:**
     In `docs/architecture.md:133-146` (`d79b0c070cf4115b523fe6ee62c1e72504de2254`),
     Stage 3 (`theory/`) simplifies Stage 2 MIR before symbolic evaluation.
     Stripping `Stmt.storageLive` or `Stmt.storageDead` during Stage 3 lowering
     is unsound because `evalMirStmt` (`MirSemantics.lean:633-638`) increments
     `s.localGens` via `bumpGen` to invalidate dangling references to dead stack
     locals. Even for pure no-op stripping (`Stmt.nop`), root
     `Terminator.return_` in `MirSemantics.lean:744` returns
     `.terminated (.normal ⟨retVal, s⟩)` carrying the full `MirState` `s`
     (including `s.block` and `s.stmtIdx`). Stripping `Stmt.nop` changes
     `s.stmtIdx` at `return_` (`rawReturn_distinguishes_nop_stripping`),
     falsifying `ExecNormal c (lowerBody b) s P → ExecNormal c b s P` for
     general postconditions `P : MirReturn → Prop` unless root
     `Terminator.return_` canonicalizes PC coordinates (`block := 0, stmtIdx := 0`
     or `pc := .terminated .normal`) in `MirReturn.state` and `lowerBody` updates
     blocks in place (`lowerBody_preserves_block_count`,
     `canonicalReturn_preserves_lowerBlock`).
- **Evidence:**
  - `joshlf/anneal` (`d79b0c070cf4115b523fe6ee62c1e72504de2254 (with three-stage MIR pipeline definitions inlined above and preserved in `support/RefinementSoundnessProbes.lean`)`):
    `trusted/lean/Trusted/MirAst.lean:193-282`,
    `trusted/lean/Trusted/MirSemantics.lean:307-326, 633-638, 740-750, 1045-1150`,
    `trusted/lean/foundation-lock.json:1-800`,
    `trusted/audit/TrustedBoundary.lean:208-321, 644-665`, and
    `theory/Anneal/MirLemmas.lean:305-308, 3549-3560`.
  - `joshlf/anneal` (`d79b0c070cf4115b523fe6ee62c1e72504de2254`):
    `docs/architecture.md:102-146`.
  - Mechanized Lean 4 proofs in
    [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean),
    lines 549–695 (`returnRefsOk_frame_relative_correctness`,
    `flatBody_decidableEq_refl`, `lowerBody_preserves_block_count`,
    `rawReturn_distinguishes_nop_stripping`,
    `canonicalReturn_preserves_lowerBlock`).

### Part II — Integration Test Harness Architecture, Path-Independent Dual-Profile MIR Capture, and Two-Stage Boundary Validation

#### Six-Generation Historical Retrospective: Eliminated vs. Surviving Failure Modes

Basis: Direct architectural comparison between `google/zerocopy`
(`8fb35253fbc703cb2cd0997f4efcda76cf9062b6`, `cargo-anneal` V1 and V2) and
`joshlf/anneal` (`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)`,
`trusted/{rustc-capture,cargo-anneal,audit,lean}`).

Across six generations of integration and UI test frameworks in
`google/zerocopy` (Hermes `compiletest_rs` skeleton -> Anneal V1 per-test Lake
sandboxes -> Anneal V1 shared-`.lake` worktrees and `ui-anneal` -> Anneal V1
coalesced `verify_Pass.rs` / `verify_Fail.rs` suites -> Anneal V2 Charon-free
4-tier test pyramid -> `joshlf/anneal`), nineteen distinct failure modes
emerged. Twelve of those nineteen failure modes are eliminated by construction
in `joshlf/anneal`, while seven survive or mutate:

| Historical Failure Mode (`google/zerocopy` V1 & V2) | Status in `joshlf/anneal` (`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)`) | Mechanism / Architectural Disposition |
| :--- | :--- | :--- |
| 1. `.lake/packages/mathlib` disk amplification (`4.2 GB` per test sandbox, `>100 GB` disk exhaustion) | **Eliminated** | No Mathlib dependency and no per-test `.lake` copies; the 10-module `Trusted.*` + `Anneal.*` prefix compiles once into `17.13 MB` of `.olean`s inside `PREFIX_CACHE` (`trusted/cargo-anneal/src/lib.rs:1076`). |
| 2. `lake build` lockfile (`lake-manifest.json`) churn & git fetch races | **Eliminated** | `cargo-anneal` invokes `lean` directly (`lib.rs:1185-1197`) with explicit `LEAN_PATH` and zero `lake` subprocesses during `cargo anneal verify`. |
| 3. `Lake.DSL` / Mathlib import elaboration OOM (`>8 GB` per worker) | **Eliminated** | All Lean files use `prelude` (`Trusted/*.lean`, `Anneal/*.lean`) with selective `Init` imports; peak prefix compilation RSS is `437.3 MB` (`Anneal.MirLemmas`). |
| 4. Charon + Aeneas single-file `.llbc` serialization bottleneck | **Eliminated** | `anneal-rustc-capture` extracts `Runtime(PostCleanup)` MIR directly in-process via `rustc_driver` in `21.7–23.2 ms`. |
| 5. Cargo `RUSTC_WORKSPACE_WRAPPER` fingerprint caching skipping capture | **Eliminated** | `cargo-anneal` invokes `anneal-rustc-capture` directly on `src/lib.rs` (`lib.rs:956-982`) rather than wrapping `cargo check`. |
| 6. Fragile `Regex` scraping of Lean/Charon human-readable logs | **Eliminated** | `anneal-audit` inspects `.olean` binary kernel `Environment` structures directly via `lean_initialize` and `AnnealAudit.auditImports` (`trusted/audit/src/lib.rs:283-427`). |
| 7. `ANNEAL_FORCE_VERIFY_SUCCESS` / env-var production escape hatches | **Eliminated** | `child_command` (`lib.rs:282-292`) calls `cmd.env_clear()` and sets only `PATH="/usr/bin:/bin"`, `HOME`, `TMPDIR`, and tool-specific library paths. |
| 8. Unsound `axiom` / `sorryAx` smuggling in generated proofs | **Eliminated** | Two-stage `.olean` audit (`TrustedBoundary.olean` + target `Mir.olean`/`Proof.olean`) rejects all non-allowlisted axioms, `sorryAx`, opaque constants, and `implemented_by` overrides. |
| 9. `std` vs. `core` sysroot resolution mismatches in UI tests | **Eliminated** | Target crates are restricted to `#![no_std]` (`items.rs:200-206`) compiled against the pinned toolchain sysroot (`--sysroot <tc/rust>`). |
| 10. Multi-crate workspace dependency resolution drift in test fixtures | **Eliminated** | `validate_target_crate` (`lib.rs:640-675`) rejects any `[dependencies]`, `[dev-dependencies]`, `[build-dependencies]`, or `[workspace]` table in a target crate's `Cargo.toml`. |
| 11. Stale `.anneal/` artifact reuse after source edits | **Eliminated** | `check_target_crate_files` (`lib.rs:596-638`) rejects pre-existing `.anneal/` files unless modified; `write_atomic` (`lib.rs:820-858`) atomically replaces `.anneal/Mir.lean` and `.anneal/Proof.lean` via `O_CREAT | O_EXCL` tempfiles + `fs::rename`. |
| 12. TOCTOU race between `src/lib.rs` validation and `rustc` reading disk | **Eliminated** | `GuardedFileLoader` (`trusted/rustc-capture/src/main.rs:76-226`) verifies `(st_dev, st_ino)` across `lstat` and `fstat` and serves `src/lib.rs` from a locked in-memory buffer across both compiler passes. |
| 13. Process-local `BUILT_CAPTURE` & `PREFIX_CACHE` cold-start penalty | **Survives (Mutated)** | `BUILT_CAPTURE` (`1.90s`) and `PREFIX_CACHE` (`15.13s`) live in in-memory `static Mutex<BTreeMap<...>>` maps backed by ephemeral `TempDir`s (`lib.rs:860,1076`). Subprocess CLI tests or separate `tests/*.rs` binaries pay the full `17.03s` cold build per process. |
| 14. Quadratic $O(N^2)$ verification scaling under fixture coalescing | **Survives (Mutated)** | Coalescing $N$ functions into one crate hits $O(N^2)$ Lean kernel reduction in `checkNoDupIds` (`MirLemmas.lean:4103-4142`) and `proveFnsLoop`: optimal at $N = 10$ (`56.7 ms/fn`), degrading to `5.04s` and `703.1 MB` RSS at $N = 50$. |
| 15. Opaque negative test failure attribution ("passing for the wrong reason") | **Survives (Mutated)** | `Anneal.proveCrate Mir.crate rfl` fails with the identical unreduced type mismatch (`Anneal.checkCrate Mir.crate = []`) regardless of *why* verification failed unless `Anneal.proveCrateOpt Mir.crate` is evaluated via `lean --run`. |
| 16. Strict `validate_target_crate` rejection of sidecar fixture files | **Survives (New)** | `CRATE_FILES` (`lib.rs:587-593`) and `#[serde(deny_unknown_fields)]` forbid sidecar files (`anneal.toml`, `expected.stderr`, `target/`) or custom `Cargo.toml` metadata inside target crate directories. |
| 17. Dual-profile (`debug` vs. `release`) MIR divergence on standard Rust idioms | **Survives (New)** | `anneal-rustc-capture` compiles every crate under both `debug` and `release` flags (`main.rs:342-345`) and rejects checked `+`/`-`/`*`, `debug_assert!`, and `#[cfg(debug_assertions)]`. |
| 18. Silent `.unmodeled` / `.unsupported` lowering in `extract.rs` | **Survives (New)** | `extract.rs` lowers unsupported types, statements, Rvalues, and terminators to `.unmodeled`/`.unsupported` rather than emitting capture errors, deferring failure to Lean kernel checking. |
| 19. Lean 4 CLI root-containment error when `cwd` is outside `/tmp` | **Survives (New)** | Invoking `lean` without `--root` requires the `.lean` input path to reside beneath `cwd` (`input file '...' must be contained in root directory`), requiring `cmd.current_dir("/")` (`lib.rs:285`). |

#### `anneal-rustc-capture` Determinism, `GuardedFileLoader`, and Dual-Profile `CONFIGS`

Basis: Source inspection of
`trusted/rustc-capture/src/{main,hook,items,lean}.rs` at
`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)` and empirical probes in
`support/capture_and_scaling_metrics.json`.

##### Path-Independent Byte-for-Byte Determinism

`anneal-rustc-capture` guarantees deterministic output across arbitrary working
directories and filesystem layouts through four mechanisms:

1. **Inode-Pinned In-Memory Source Loading (`GuardedFileLoader`):**
   `GuardedFileLoader::new` (`trusted/rustc-capture/src/main.rs:102-151`)
   canonicalizes `--src` and `--sysroot`, opens `--src` with `O_RDONLY |
   O_NOFOLLOW`, verifies that `lstat` and `fstat` report a regular file with
   identical `(st_dev, st_ino)`, and reads the bytes into `Arc<[u8]>`. Both
   in-process `rustc_driver` runs read `src/lib.rs` from that pinned buffer
   while rejecting any symlink or non-sysroot file access (`main.rs:159-219`).
2. **Pre-Steal `Runtime(PostCleanup)` Hook:** `override_queries`
   (`trusted/rustc-capture/src/hook.rs:42-78`) overrides
   `queries.mir_drops_elaborated_and_const_checked`—the terminal query of the
   `Runtime(PostCleanup)` phase—cloning `Body<'tcx>` inside `steal.borrow()`
   before downstream `mir_for_ctfe` or `optimized_mir` queries steal the buffer.
   The hook guards against nested or synthetic `TyCtxt` invocations via
   `tcx.sess.opts.unstable_opts.treat_err_as_bug.is_none()` (`hook.rs:64-67`).
3. **`DefIndex`-Ordered Collections and Topological Sorting:**
   `collect_crate_items` (`trusted/rustc-capture/src/items.rs:49-189`) stores
   ADTs, traits, trait implementations, and functions in `BTreeMap`/`BTreeSet`
   keyed by crate-local `DefIndex::as_u32()` (`def_id_index`), and orders
   emitted `BodyDecl` records via deterministic depth-first topological sort
   (`dependency_order`, `items.rs:236-291`).
4. **Span-Free Rendering:** `render_mir_module`
   (`trusted/rustc-capture/src/lean.rs:26-48`) emits pure Lean 4 AST literals
   (`Trusted.Crate`) with zero source spans, file paths, or symbol hashes.

Empirically (`support/capture_and_scaling_metrics.json`), capturing `pub fn
id(x: usize) -> usize { x }` from a shallow path (`det_a/sample/src/lib.rs`) and
a 9-level nested path (`det_b/very/deep/nested/<depth-9>/src/lib.rs`) produces
byte-for-byte identical 792-byte `Mir.lean` files (`SHA-256 =
44e0972a75b52b1a7a1dd9dab8a8bd0f9366f18b3ab7fe0415de46352e79d594`) in `21.8 ms`
and `23.2 ms`, respectively (`78.46 MB` max RSS). No `--remap-path-prefix` flag
is required for positive `Mir.lean` goldens.

##### Dual-Profile (`debug` vs. `release`) MIR Equivalence Gate

`anneal-rustc-capture` defines two compilation configurations in
`trusted/rustc-capture/src/main.rs:342-345`:

```rust
const CONFIGS: [(&str, &[&str]); 2] = [
    ("debug", &["-Cdebug-assertions=on", "-Coverflow-checks=on"]),
    ("release", &["-Cdebug-assertions=off", "-Coverflow-checks=off"]),
];
```

`run` (`main.rs:514-580`) executes `rustc_driver::run_compiler` sequentially for
`"debug"` and `"release"` inside the same OS process (`~21.7–23.2 ms` total for
both runs combined) and compares the rendered `Mir.lean` strings (`if other !=
rendered`, `main.rs:569-578`). Because both passes pass `-Zmir-opt-level=0`
(`compiler_args` at `main.rs:394`), the only differences between the two passes
are `cfg(debug_assertions)`, `-Cdebug-assertions`, and `-Coverflow-checks`:

| Rust Construct | Capture Result (`rc`) | Wall Time | Empirical Behavior Across `debug` and `release` `CONFIGS` |
| :--- | :--- | :--- | :--- |
| `pub fn add1(x: usize) -> usize { x + 1 }` | `1` (Rejected) | `23.1 ms` | `debug` emits `Rvalue::BinaryOp(AddWithOverflow, ...)` + `TerminatorKind::Assert`; `release` emits `Rvalue::BinaryOp(Add, ...)` + `Goto`. Fails with `its MIR differs between the debug and release configurations`. |
| `pub fn add1(x: usize) -> usize { x.wrapping_add(1) }` | `0` (Accepted) | `23.2 ms` | Both configurations lower `wrapping_add` through the intrinsic call to identical `1,087 B` `Mir.lean`. |
| `pub fn check(x: usize) -> usize { debug_assert!(x != 0); x }` | `1` (Rejected) | `22.9 ms` | `debug_assert!` expands to a conditional panic branch only when `cfg(debug_assertions)` is enabled. |
| `pub fn div(x: usize, y: usize) -> usize { x / y }` | `0` (Accepted) | `23.1 ms` | Both `debug` and `release` emit the unconditional division-by-zero `TerminatorKind::Assert` in `Runtime(PostCleanup)` MIR (`1,699 B` `Mir.lean`), which then fails closed in Lean proof checking because `Terminator.assert` is unproved for unconstrained `y`. |
| `#[cfg(debug_assertions)] pub fn f() {}` | `1` (Rejected) | `21.7 ms` | Item inventory differs between `debug` and `release`. |
| `pub unsafe fn read_ptr(p: *const usize) -> usize { unsafe { *p } }` | `0` (Accepted) | `23.2 ms` | Note that `rustc` only inserts `ub_checks` alignment/null assertions inside `core` library methods (`ptr::read`, `NonNull::new_unchecked`), not on raw built-in `*p` place projections (`825 B` `Mir.lean`). |

#### Five-Layer Diagnostic and Unsupported-Construct Taxonomy

Basis: Source inspection of
`trusted/rustc-capture/src/{main,items,spec,extract}.rs` at
`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)` and empirical probes in
`support/capture_and_scaling_metrics.json`.

Integration tests that assert on negative or unsupported inputs must distinguish
between errors caught during capture (layers 1–4, which exit with code `1` and a
deterministic `anneal-rustc-capture:` stderr prefix) and unsupported MIR body
constructs (layer 5, which succeed during capture with exit code `0` and fail
closed during Lean proof checking):

1. **Layer 1 — CLI & Target File Guards (`main.rs:246-339`):** Missing or
   duplicate CLI flags, non-2024 `--edition`, invalid `--crate-name`, or
   symlinked/disallowed file paths in `GuardedFileLoader` fail with
   `anneal-rustc-capture: <reason>`.
2. **Layer 2 — Source & Attribute Detective Scan (`check_inputs`,
   `main.rs:482-505`):** Scans the parsed AST before HIR/MIR lowering and
   rejects multiple source files, `include!` / `include_str!` / `include_bytes!`
   macros, `#[path = ...]` module redirects, and tool/diagnostic attributes
   (`#[rustc_*]`, `#[diagnostic::*]`).
3. **Layer 3 — Crate Item Inventory (`collect_crate_items`,
   `items.rs:49-234`):** Requires `#![no_std]` (`crate must declare #![no_std]`)
   and rejects unsupported top-level items (`Enum`, `Union`, `Static`, `Const`,
   `ForeignMod`, `GlobalAsm`, `Macro`), `unsafe trait` (`trait ... is unsafe`),
   `unsafe impl` (`impl ... is unsafe`), multi-field structs with `invariant`
   clauses (`declares an Anneal invariant clause, which is only supported on
   single-field usize structs`), and `requires` clauses on safe functions (`safe
   function ... has a requires clause; only unsafe fn items may declare
   preconditions`). Note that `items.rs` diagnostics format `DefId`s with the
   crate disambiguator hash (for example, `DefId(0:3 ~ sample[f687]::E)`), which
   depends on `--crate-name` but not on filesystem path because
   `--remap-path-prefix` / virtual loader paths are fixed.
4. **Layer 4 — Doc-Comment Specification Parser (`parse_anneal_spec`,
   `spec.rs:27-350`):** Rejects unknown thread-safety keywords, duplicate `///
   ```anneal` blocks, malformed `requires` / `ensures` / `invariant` clauses
   (`unsupported Anneal block on ...: unsupported ensures clause ...; expected
   result == <ident>`), and `is_safe` clauses outside trait declarations.
5. **Layer 5 — Fail-Closed MIR Body Lowering (`extract_body`,
   `extract.rs:23-391`):** Unlike layers 1–4, `extract_body` does **not** abort
   `anneal-rustc-capture` when a function body uses an unmodeled type (such as
   `&mut T`, raw pointers `*const T`, arrays, or tuples), an unsupported
   projection (`Deref` or nested fields), an unsupported `Rvalue`
   (`CheckedBinaryOp`, `Cast`, `Discriminant`), or an unsupported
   `TerminatorKind` (`SwitchInt` with $\ge 2$ targets, multi-arg calls, or
   inline `Asm`). Instead, `extract.rs` lowers them to `MirTy.unmodeled`,
   `Place.unsupported`, `Rvalue.unsupported`, `Stmt.unsupported`, or
   `Terminator.unsupported` (`extract.rs:68,94,159,205,361`). This design allows
   a crate to contain private uncalled helper functions using arbitrary Rust
   constructs (`probe_private_uncalled_fn` in
   `support/capture_and_scaling_metrics.json` exits `0` with `1,353 B`
   `Mir.lean`), while any public or reachable function whose body contains an
   unsupported sentinel fails closed inside `Anneal.proveCrate`.

### Two-Stage Boundary Audit, `validate_target_crate`, and Harness Architecture

Basis: Source inspection of `trusted/audit/{TrustedBoundary.lean,src/lib.rs}`,
`trusted/cargo-anneal/src/lib.rs:536-687,860-1315`, and
`trusted/cargo-anneal/tests/verify_id.rs` at
`c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)`.

#### Two-Stage `.olean` Boundary Audit (`anneal-audit`)

`cargo-anneal` enforces Lean trust-boundary integrity in two distinct stages
(`trusted/cargo-anneal/src/lib.rs:1060-1073,1208-1231`):

- **Stage 1 — Prefix Audit (`verify_lean_workspace_In_process`):** Compiles
  `trusted/audit/TrustedBoundary.lean` (which imports `Trusted` and `Anneal`)
  and invokes `anneal_audit::verify_boundary_olean_in_process`. This checks four
  invariants across the entire transitive `Environment` of the 10-module prefix
  (`trusted/audit/src/lib.rs:283-427`):
  1. Every `Trusted.*` module `.olean` matches the fresh compilation of
     `trusted/lean/Trusted/*.lean` byte-for-byte.
  2. Only `propext`, `Quot.sound`, and `Classical.choice` appear as axioms;
     `sorryAx` and custom `axiom` declarations are rejected (`[E-AUDIT-AXIOM]`).
  3. Only Lean stdlib allowlisted `opaque` declarations (`OPAQUE_ALLOWLIST`)
     exist (`[E-AUDIT-OPAQUE]`).
  4. Zero `implemented_by` or `extern` C overrides exist (`[E-AUDIT-CSIMP]`).
- **Stage 2 — Per-Crate Target Audit (`audit_target_crate_oleans`):** After
  compiling `.anneal/Mir.lean` and `.anneal/Proof.lean` into a temporary staging
  directory, `cargo-anneal` audits `[Mir, Proof]` via
  `verify_imported_modules_in_process` and asserts that `Proof.olean` exports
  `Proof.crate_verified : Trusted.CrateTheorem Mir.crate` as a genuine
  `ConstantInfo.thmInfo` (`verify_theorem_constant_in_process`,
  `trusted/audit/src/lib.rs:429-481`), blocking `def`, `axiom`, or `opaque`
  spoofing of `Proof.crate_verified`.

#### `validate_target_crate` Constraints on Test Fixtures

`validate_target_crate` (`trusted/cargo-anneal/src/lib.rs:594-687`) enforces two
strict structural checks before invoking `anneal-rustc-capture`:

1. **Closed 5-File Directory Allowlist (`CRATE_FILES`, `lib.rs:587-638`):**
   Every file under the target crate root is discovered via a recursive walk
   that rejects symlinks and rejects any relative path not in: `["Cargo.toml",
   "Cargo.lock", "src/lib.rs", ".anneal/Mir.lean", ".anneal/Proof.lean"]`.
   Furthermore, if `.anneal/Mir.lean` or `.anneal/Proof.lean` already exists on
   disk before `cargo anneal verify` runs and differs from the freshly generated
   content, `write_verified_outputs` (`lib.rs:761-818`) rejects the run
   (`refusing to overwrite modified file`).
2. **Closed `Cargo.toml` Schema (`#[serde(deny_unknown_fields)]`,
   `lib.rs:536-584`):** `TargetCargoToml` and `TargetPackage` use
   `#[serde(deny_unknown_fields)]` and permit only `package.{name, version,
   edition, publish}` plus `[lib] path = "src/lib.rs"`, rejecting any
   `[package.metadata.*]`, `[dependencies]`, or `[features]` tables.

Consequently, **a checked-in directory of target crates cannot store sidecar
test expectations (`anneal.toml`, `expected.stderr`, `README.md`) or build
artifacts (`target/`) inside the fixture crate directory**. Instead, fixtures
should be stored as single `.rs` source files with structured leading `//~`
expectation headers (for example, `//~ outcome: pass` or `//~ outcome:
fail-proof`, `//~ error-scope: make_nonzero`, `//~ error-msg: unproved safe
NonZeroUsize function`) and materialized on demand into a clean `TempCrateDir`
containing only a synthetic `Cargo.toml` and `src/lib.rs`.

#### Zero-Dependency In-Process Test Harness vs. External Runners

At `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)`, `Cargo.lock` contains 129
packages (127 from `crates.io-index` plus `anneal-audit` and `cargo-anneal`) and
is SHA-256 locked by `trusted/root-manifest.sha256` (enforced by
`check_cargo_boundary` in `verify_id.rs:647`). Comparing the four candidate Rust
integration test harness architectures:

| Harness Architecture | New Crates in `Cargo.lock` | Shares `BUILT_CAPTURE` (`1.90s`) & `PREFIX_CACHE` (`15.13s`)? | Per-Fixture CLI Filtering (`cargo test <name>`) | Verdict for `joshlf/anneal` |
| :--- | :--- | :--- | :--- | :--- |
| 1. Subprocess CLI per test (`Command::new(CARGO_BIN_EXE_cargo-anneal)`) | `0` | **No** — rebuilds `anneal-rustc-capture` and all 10 Lean prefix modules (`17.03s`) in *every* subprocess | Yes | **Unsuitable** for fixture suites (reserve for 1–2 CLI smoke tests). |
| 2. External `datatest-stable` or `libtest-mimic` (`harness = false`) | `2–9` | Yes (within one binary) | Yes | **Disfavored** by `AGENTS.md` dependency discipline: requires updating `Cargo.lock` and `trusted/root-manifest.sha256` for trivial directory iteration. |
| 3. Single integration test binary (`trusted/cargo-anneal/tests/verify_id.rs` or `litmus.rs`) invoking `cargo_anneal::run_with_io` in-process | `0` | **Yes** — pays the `17.03s` cold build once per binary and `~0.23s` per warm 1-fn crate (`~56.7 ms/fn` when coalesced at $N = 10$) | Yes (via `#[test]` functions or `include_dir` / `build.rs` test generation) | **Recommended** — zero external dependencies, zero `root-manifest.sha256` churn, and full in-process `PREFIX_CACHE` reuse. |

## Boundaries

### Part I — Three-Stage MIR Pipeline Architecture, Place Initialization, PME Completeness, Assert Semantics, and Stage 3 Lowering

- **Raw pointer provenance, byte-level representation, and Tree/Stacked Borrows (`not examined`):**
  Both the current `MirSemantics.lean` and the path-sensitive `Place` +
  `MirVal.uninit` model represent references symbolically as paths
  `(FrameId, LocalId, List PlaceElem)` with per-local generation counters
  (`localGens`) rather than a byte-addressed memory model with pointer
  provenance or aliasing trees. Reinterpreting casts, union field aliasing, and
  sub-scalar byte slices remain outside the modeled fragment.
- **Unwinding cleanup pads (`TerminatorKind::Resume`, `UnwindAction::Cleanup`) (`not examined`):**
  Stage 1 (`trusted/rustc-capture/src/extract.rs:584-592`) and Stage 2
  (`trusted/lean/Trusted/MirSemantics.lean`) model unwinding as a direct
  transition to `.terminated .unwind` without executing landing-pad drop glue
  blocks along the unwind path.
- **Full `rustc_private` query-hook behaviour on `Runtime(Optimized)` (`not examined`):**
  Stage 1 (`trusted/rustc-capture/src/hook.rs:86-109`) captures MIR from
  `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`). Extending
  the query hook to cross-check `optimized_mir` (`Runtime(Optimized)`) directly
  inside `rustc-capture` was probed via `rustc` MIR dumps but not integrated into
  `hook.rs`.

### Part II — Integration Test Harness Architecture, Path-Independent Dual-Profile MIR Capture, and Two-Stage Boundary Validation

- This report evaluates `anneal-rustc-capture`, `cargo-anneal`, and
  `anneal-audit` at `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)`, where proof
  generation is non-extensible (`emit_proof_module` emits a fixed
  `Anneal.proveCrate Mir.crate rfl` script and `cargo-anneal` rejects
  user-supplied `.anneal/Proof.lean` overrides via `check_target_crate_files`).
- Detailed Lean 4 kernel compilation scaling curves ($N = 1..50$), negative
  failure-reason attribution (`Anneal.proveCrateOpt`), concrete `ExecNormal`
  kernel stepping, and TCB semantic mutation testing of
  `Trusted/MirSemantics.lean` are covered in the companion report
  ``anneal-lean-verification-scaling-attribution-and-mutation-oracles-2026``.
- Timing and RSS measurements were recorded on an x86_64 Linux workstation using
  `anneal-lean-run` resource bounds and will vary in absolute wall-clock time on
  other hardware, though structural complexity ratios and cache lifetimes are
  machine-independent.

## Evidence

### Part I — Three-Stage MIR Pipeline Architecture, Place Initialization, PME Completeness, Assert Semantics, and Stage 3 Lowering

| Artifact / Source | Type | Role | Description |
| :--- | :--- | :--- | :--- |
| `joshlf/anneal` @ `d79b0c070cf4115b523fe6ee62c1e72504de2254 (with three-stage MIR pipeline definitions inlined above and preserved in `support/RefinementSoundnessProbes.lean`)` | Git commit | `source` | Primary Anneal repository checkout (`trusted/rustc-capture`, `trusted/lean`, `trusted/audit`, `trusted/cargo-anneal`, `theory/Anneal`). |
| `joshlf/anneal` @ `d79b0c070cf4115b523fe6ee62c1e72504de2254` | Git commit | `documentation` | Architecture specification (`docs/architecture.md:102-146`) defining the three-stage MIR pipeline. |
| [support/mir_subtleties_specimen.rs](support/mir_subtleties_specimen.rs) | Rust source | `execution` | `#![no_std]` specimen exercising partial moves, `PlaceMention`, dead-branch PME constants, checked arithmetic `Assert` vs. `assert!` panic, and `#[cfg(debug_assertions)]` item shifts. |
| [support/probe_rustc_mir_subtleties.py](support/probe_rustc_mir_subtleties.py) | Python script | `execution` | Reproducible probe driver executing `rustc +nightly` and `rustc +nightly` across MIR phases and flag matrices. |
| [support/mir_subtleties_output.json](support/mir_subtleties_output.json) | JSON capture | `execution` | Golden output captured from `probe_rustc_mir_subtleties.py` across `rustc 1.96.0-nightly` (`fd0c901b00ee1e08a250039cdb90258603497e20`) and `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). |
| [support/RefinementSoundnessProbes.lean](support/RefinementSoundnessProbes.lean) | Lean 4 source | `execution + derived` | Zero-`sorry`, zero-axiom mechanized proofs of Findings F-01 through F-05, verified under `leanprover/lean4:v4.28.0` and `leanprover/lean4:v4.34.1`. |

### Part II — Integration Test Harness Architecture, Path-Independent Dual-Profile MIR Capture, and Two-Stage Boundary Validation

- `joshlf/anneal` at `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b (with flat-`BodyId` minimal-TCB definitions inlined above and preserved in `support/`)`:
  - `trusted/rustc-capture/src/main.rs:76-226` (`GuardedFileLoader` `(st_dev,
    st_ino)` verification and path restriction), `L342-345` (`CONFIGS` `"debug"`
    and `"release"`), `L482-505` (`check_inputs`), and `L514-580` (dual-profile
    compiler execution and byte-equality gate).
  - `trusted/rustc-capture/src/hook.rs:42-78`
    (`mir_drops_elaborated_and_const_checked` query override and
    `treat_err_as_bug.is_none()` guard).
  - `trusted/rustc-capture/src/items.rs:49-291` (`DefIndex`-keyed
    `BTreeMap`/`BTreeSet` collection and `dependency_order` topological sort).
  - `trusted/rustc-capture/src/spec.rs:27-350` (`/// ```anneal` doc-comment
    parser).
  - `trusted/rustc-capture/src/extract.rs:23-391` (fail-closed `.unmodeled` and
    `.unsupported` lowering).
  - `trusted/cargo-anneal/src/lib.rs:282-292` (`child_command` with
    `env_clear()` and `current_dir("/")`), `L536-687` (`TargetCargoToml`,
    `CRATE_FILES`, and `validate_target_crate`), `L860` (`BUILT_CAPTURE`), and
    `L1076` (`PREFIX_CACHE`).
  - `trusted/cargo-anneal/tests/verify_id.rs:1-817` (`TempCrateDir`, 20
    in-process integration tests, and `check_cargo_boundary`).
  - `trusted/audit/src/lib.rs:283-481` (`verify_boundary_olean_in_process` and
    `verify_theorem_constant_in_process`).
- Local reproducible data in this package:
  - [`support/capture_and_scaling_metrics.json`](support/capture_and_scaling_metrics.json)
    (path determinism SHA-256 receipts, dual-profile divergence timings,
    diagnostic taxonomy exit codes/stderr strings, and workspace manifest
    metrics).

## Revalidation

### Part I — Three-Stage MIR Pipeline Architecture, Place Initialization, PME Completeness, Assert Semantics, and Stage 3 Lowering

To reproduce the `rustc` MIR phase and flag-matrix probe across
`nightly` and `nightly`:

```console
python3 support/probe_rustc_mir_subtleties.py
```

To recheck the mechanized Lean 4 proofs in `support/RefinementSoundnessProbes.lean`
under both `leanprover/lean4:v4.28.0` and `leanprover/lean4:v4.34.1`:

```console
elan run leanprover/lean4:v4.28.0 lean support/RefinementSoundnessProbes.lean
elan run leanprover/lean4:v4.34.1 lean support/RefinementSoundnessProbes.lean
```

### Part II — Integration Test Harness Architecture, Path-Independent Dual-Profile MIR Capture, and Two-Stage Boundary Validation

Revalidate this report when any of the following change:

1. `trusted/rustc-capture/src/main.rs` modifies `CONFIGS` (`"debug"` vs.
   `"release"` compiler flags) or `GuardedFileLoader`.
2. `trusted/rustc-capture/src/extract.rs` changes how unsupported MIR types,
   statements, or terminators are lowered vs. rejected during capture.
3. `trusted/cargo-anneal/src/lib.rs` changes `CRATE_FILES`, `TargetCargoToml`
   validation, or persists `BUILT_CAPTURE` / `PREFIX_CACHE` to disk across OS
   processes.
4. `trusted/toolchain.toml` updates the pinned `rustc` nightly or Lean 4
   revision.
