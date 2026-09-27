# `unreachable_unchecked` semantics at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `core::hint::unreachable_unchecked() -> !` is an unsafe promise that control flow cannot reach the call. Reaching it is undefined behavior. It is not a faster panic with weaker diagnostics, and it is not merely a hint that an optimizer may ignore.

The stable wrapper performs an optional unsafe-precondition check and then calls the `core::intrinsics::unreachable` compiler intrinsic. That check is diagnostic instrumentation, not part of the safety contract: its own implementation says it is optional and cannot be relied on for safety. In const evaluation and Miri, the wrapper's language-UB precondition check is deliberately disabled because the interpreter diagnoses the underlying UB directly.

rustc's `LowerIntrinsics` pass rewrites the `unreachable` intrinsic to `TerminatorKind::Unreachable`. The MIR definition states that executing this terminator is UB. A pinned MIR-opt golden diff records exactly this transformation. This is the compiler-level reason that `unreachable_unchecked` can justify elimination of branches, checks, and downstream code.

For verification, the correct proof obligation is therefore **non-reachability**. A verifier may encode the operation as an impossible/false execution path only if it also preserves the obligation that no valid Rust execution reaches that point. Modeling it as ordinary panic, recoverable failure, unspecified divergence, or a harmless no-return operation is unsound for proving source behavior. If an upstream optimization has already removed the path using this assumption, the source-to-model argument must preserve the assumption or independently prove its premise.

No fresh compilation, Miri run, or code-generation experiment was performed. The report is grounded in the exact pinned library/compiler source and checked-in rustc/Miri test artifacts.

## Applicability

The findings apply to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, corresponding to the Anneal-era `nightly-2026-05-31` source used by the current primitive-semantics corpus; and
- the bundled Rust Reference revision `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` for the general undefined-behavior rules.

The primary API is `core::hint::unreachable_unchecked`. Its implementation delegates to the unstable `core::intrinsics::unreachable`; this report examines both because the intrinsic supplies the compiler semantics of the stable wrapper.

The report distinguishes three layers:

1. **Rust/library contract** — what the unsafe caller must establish;
2. **diagnostic instrumentation** — optional checks that may detect a violation in some configurations; and
3. **compiler IR semantics** — how the intrinsic becomes an unreachable MIR terminator that optimizers may exploit.

Those layers must not be collapsed. In particular, observing a debug-time diagnostic does not weaken the caller's safety obligation.

## Findings

### Reaching `unreachable_unchecked` is undefined behavior

The stable API documentation says that the call site is asserted to be unreachable and states under `# Safety` that reaching the function is undefined behavior. It further warns that if the promise is wrong, the compiler may produce nonsensical instructions even in apparently unrelated code.

The Rust Reference independently classifies invoking undefined behavior through compiler intrinsics as UB and emphasizes that `unsafe` does not make undefined behavior permissible. The wrapper's implementation eventually invokes precisely such an intrinsic.

Basis: **documentation + normative Reference + source** — `library/core/src/hint.rs`; Rust Reference `src/behavior-considered-undefined.md`.

### The operation returns `!`; a valid execution never returns a value

The stable wrapper and the underlying intrinsic both have return type `!`. The Reference's validity rules also state that a value of type `!` must never exist.

This does not mean “the function may diverge.” Its specific contract is stronger: the call itself must be unreachable. A verifier that models the call as arbitrary nontermination would admit executions that Rust declares undefined.

Basis: **source + normative Reference + derived** — `library/core/src/hint.rs`; `library/core/src/intrinsics/mod.rs`; Rust Reference invalid-value rules.

### The stable wrapper delegates to the `unreachable` compiler intrinsic

At this revision, the implementation is structurally:

1. invoke `assert_unsafe_precondition!(check_language_ub, ..., () => false)`; then
2. invoke `intrinsics::unreachable()`.

The intrinsic is `const unsafe fn unreachable() -> !`, is marked `#[rustc_intrinsic]` and `#[rustc_nounwind]`, and its documentation states that reaching it is undefined behavior. The documentation explicitly contrasts it with `unreachable!()`.

Basis: **source** — `library/core/src/hint.rs`; `library/core/src/intrinsics/mod.rs`.

### The precondition check is optional instrumentation, not a safety mechanism

`assert_unsafe_precondition!` documents that language-UB checks are enabled at runtime according to UB-check/debug-assertion configuration. Its generated failure path uses `panic_nounwind_fmt`. The diagnostic text itself states that the check is optional and cannot be relied on for safety.

For `check_language_ub`, the check is intentionally disabled during const evaluation and under Miri. Those evaluators have their own UB detection. Therefore the presence, absence, or exact failure mode of the wrapper check does not define `unreachable_unchecked` semantics.

A consequence is that a violating native execution may appear to terminate with a precondition diagnostic in some builds, while another build may optimize under the impossible-path assumption. Code cannot use that diagnostic behavior as a fallback contract.

Basis: **source + derived** — `library/core/src/ub_checks.rs`; `library/core/src/hint.rs`.

### rustc lowers the intrinsic call to MIR `Unreachable`

The pinned `LowerIntrinsics` pass matches `sym::unreachable` and replaces the call terminator with `TerminatorKind::Unreachable`.

The corresponding checked-in MIR-opt fixture contains a direct intrinsic call and expects `unreachable;`. Its golden diff shows the call

`std::intrinsics::unreachable() -> unwind unreachable`

being replaced by the MIR `unreachable` terminator.

This is not an inference from backend behavior; it is an explicit transformation in the pinned MIR pipeline.

Basis: **source + checked-in compiler test artifact** — `compiler/rustc_mir_transform/src/lower_intrinsics.rs`; `tests/mir-opt/lower_intrinsics.rs`; `tests/mir-opt/lower_intrinsics.unreachable.LowerIntrinsics.panic-unwind.diff`.

### Executing the resulting MIR terminator is UB

The pinned MIR syntax documentation defines `TerminatorKind::Unreachable` as a terminator that can never be reached and states directly that executing it is UB.

The interpreter's UB error vocabulary includes `Unreachable`, rendered as `entering unreachable code`. This matches the checked-in Miri and const-eval regression expectations for a reached `unreachable_unchecked` call.

Basis: **source + checked-in compiler/Miri test artifacts** — `compiler/rustc_middle/src/mir/syntax.rs`; `compiler/rustc_middle/src/mir/interpret/error.rs`; `src/tools/miri/tests/fail/unreachable.{rs,stderr}`; `tests/ui/consts/const_unsafe_unreachable_ub.{rs,stderr}`.

### Miri and const evaluation diagnose the semantic UB directly

The Miri regression fixture calls `std::hint::unreachable_unchecked()` in `main`; the preserved expected stderr classifies the result as `Undefined Behavior: entering unreachable code`. Miri's own README lists reaching `unreachable_unchecked` as a violation of an intrinsic precondition that it detects.

A const-eval UI test similarly evaluates a branch that reaches `unreachable_unchecked`; the expected compiler diagnostic is `E0080: entering unreachable code`.

These are useful discriminator artifacts because `check_language_ub` intentionally suppresses the wrapper's optional precondition check in Miri and const evaluation. The reported failure therefore reflects interpreter handling of the underlying unreachable operation rather than reliance on the wrapper check.

Basis: **source + checked-in expected-output artifacts + derived** — `library/core/src/ub_checks.rs`; Miri and const-eval tests listed under Evidence.

### `unreachable!()` has different semantics

The safe `unreachable!()` macro is documented as a panic: if the supposedly impossible path is reached, the program takes panic behavior. Its documentation names `unreachable_unchecked` as the unsafe counterpart and says the latter causes UB when reached.

Accordingly:

- `unreachable!()` preserves a defined failure path subject to Rust's panic strategy and unwind/abort rules;
- `unreachable_unchecked()` supplies a soundness promise from which the compiler may reason that the path does not occur at all.

Replacing one with the other changes program semantics, not just performance or diagnostics.

Basis: **documentation + source** — `library/core/src/macros/mod.rs`; `library/core/src/hint.rs`.

### `assert_unchecked(false)` is the same class of unsafe promise

At this revision, `core::hint::assert_unchecked` documents itself as logically equivalent to `if !cond { unreachable_unchecked(); }` and says that passing `false` is immediate UB. It recommends calling `unreachable_unchecked` directly instead of writing `assert_unchecked(false)`.

For a verifier, both APIs therefore introduce proof obligations rather than recoverable assertions. The surface syntax differs, but a false premise reaches the same semantic class of UB.

Basis: **documentation + source** — `library/core/src/hint.rs`.

### Optimizers are entitled to exploit the promise beyond the call site

The stable documentation explicitly explains that the compiler can eliminate branches that invariably lead to `unreachable_unchecked`, and its example uses the promise to eliminate a later division-by-zero check. This follows from ordinary UB reasoning: a compiler need only preserve behavior of well-defined executions, so an execution that violates the unreachable promise need not retain intuitive local behavior.

This is why “it happens to trap in my debug build” is not a valid justification. The optional check can disappear, and transformations justified by the promise can affect surrounding code.

Basis: **documentation + derived** — `library/core/src/hint.rs`; lowering to MIR `Unreachable`.

### The verification obligation is path exclusion, not panic handling

For source-level verification, reaching `unreachable_unchecked` makes the execution invalid under Rust semantics. A sound proof can handle the operation in either of two equivalent ways:

- prove from the path condition that the call is unreachable and then close the branch; or
- introduce an explicit obligation such as `path_condition -> False` and require that obligation to be discharged.

What is not sound is to close the branch without retaining the obligation, or to translate the operation into an ordinary panic/failure result whose caller may catch, ignore, or reason about as defined control flow.

This distinction matters when the compiler has already optimized using the promise. Since `LowerIntrinsics` creates a MIR `Unreachable` terminator and later MIR passes may propagate or simplify unreachable control flow, a verifier consuming later MIR must not infer “there was never source behavior here” merely from the missing branch. It needs provenance for the assumption or an independent proof that the branch is impossible.

Basis: **derived from the documented contract + pinned MIR lowering**.

### Unsafe abstraction boundaries must carry the premise outward

If an unsafe helper calls `unreachable_unchecked` based on a precondition supplied by its caller, the helper is sound only when that precondition is enforced by its unsafe API contract or established internally before the call. If a safe API can drive execution to the intrinsic, the safe abstraction is unsound.

The Reference states the general rule: unsafe code is responsible for ensuring that safe clients cannot trigger UB. `unreachable_unchecked` is a direct instance of that rule because its sole semantic prerequisite is non-reachability.

For Anneal-style verification, a report or proof should therefore identify the source of the non-reachability fact: a checked condition, an enum/type invariant, an unsafe caller obligation, an earlier proof, or another sound semantic fact. “Compiler says unreachable” is not itself a source-level justification when compiler reachability may already depend on UB assumptions.

Basis: **normative Reference + documentation + derived**.

## Boundaries

**No fresh execution.** This investigation did not compile a probe, invoke Miri, inspect generated assembly, or compare optimization levels. Checked-in `.stderr` and MIR-diff files are preserved upstream test expectations, not new execution evidence from this run.

**No exhaustive optimizer survey.** The report pins the direct `LowerIntrinsics` transformation and the semantic meaning of MIR `Unreachable`. It does not enumerate every later MIR or backend optimization that can propagate the assumption or erase dependent code.

**No backend-specific codegen guarantee.** LLVM, Cranelift, and GCC backend encodings of unreachable control flow were not compared. The Rust-level and MIR-level safety conclusions do not depend on a particular backend instruction sequence.

**Optional UB-check behavior is not stable fallback behavior.** The current wrapper has an optional precondition check, but the report deliberately does not promise that every native debug build traps in a particular way. The source explicitly says the check cannot be relied on for safety.

**Miri is a detector, not the language definition.** Its checked-in diagnostic is evidence that this pinned tool recognizes the violation. The semantic claim comes from the Rust/library contract and MIR semantics, not from “Miri rejects it.”

**No Charon/Aeneas translation claim.** This report establishes the Rust/rustc side of the primitive. Whether Charon preserves the operation or only the already-lowered MIR `Unreachable`, and how Aeneas represents the resulting obligation, belong to their pinned translation reports.

**No claim that all syntactic unreachable code needs this intrinsic.** Ordinary control-flow impossibility, the safe `unreachable!()` macro, uninhabited-type reasoning, compiler-created unreachable MIR, and `unreachable_unchecked` can all produce or interact with unreachable regions for different reasons. The unsafe API specifically introduces a caller-owned soundness promise.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### Rust core library and intrinsic contracts

Subject: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `library/core/src/hint.rs`, blob `90326e649058bee9f49c1e600a054f2805a3ab4f`
  - `unreachable_unchecked` API contract and implementation;
  - optimizer warning and examples;
  - `assert_unchecked` equivalence and safety contract.
- `library/core/src/intrinsics/mod.rs`, blob `78d7314c58110b49839894a0f69377f4ee0d1204`
  - `intrinsics::unreachable` declaration, `!` return, `rustc_nounwind`, and UB documentation.
- `library/core/src/ub_checks.rs`, blob `f25781ea8ce5aef2c332b19246c1b5c7e041b2c6`
  - optional unsafe-precondition instrumentation;
  - `panic_nounwind_fmt` failure path;
  - `check_language_ub` disabling in const-eval and Miri.
- `library/core/src/macros/mod.rs`, blob `c21191dbc19be8e56fd42a46499032442c97776a`
  - safe `unreachable!()` panic contract and explicit contrast with `unreachable_unchecked`.

### rustc MIR semantics and lowering

Same Rust revision.

- `compiler/rustc_mir_transform/src/lower_intrinsics.rs`, blob `fe53d301c5574101399b60d38451a57b24c43535`
  - `sym::unreachable` becomes `TerminatorKind::Unreachable`.
- `compiler/rustc_middle/src/mir/syntax.rs`, blob `07eaa085fabc9742d0d51c73eeba91dcc9e67d2e`
  - MIR `Unreachable` definition and UB semantics.
- `compiler/rustc_middle/src/mir/interpret/error.rs`, blob `7d9f6903d3ef0e5a441081bb0aba3b50280b7449`
  - interpreter `Unreachable` error rendered as `entering unreachable code`.
- `tests/mir-opt/lower_intrinsics.rs`, blob `e8a770147741598a84e52e340d285fe59611c2f0`
  - checked-in test source for intrinsic lowering.
- `tests/mir-opt/lower_intrinsics.unreachable.LowerIntrinsics.panic-unwind.diff`, blob `2b715ac1d635b0c8991d475250f611192a8308f0`
  - checked-in golden diff showing call-to-terminator lowering.

### Interpreter regression artifacts

Same Rust revision.

- `src/tools/miri/README.md`, blob `3d0716a082d4334cf1642aac1c165738c1a353a9`
  - lists a reached `unreachable_unchecked` among detected intrinsic-precondition violations.
- `src/tools/miri/tests/fail/unreachable.rs`, blob `3389d5b9ddeafd46d2748f3f863596ea7947da96`
- `src/tools/miri/tests/fail/unreachable.stderr`, blob `ab8ba4a68e5feea69fd2a1811876f9e9693bc94c`
  - expected Miri UB diagnostic.
- `tests/ui/consts/const_unsafe_unreachable_ub.rs`, blob `39f053951276ed77a76edb816c0fc819efc799ea`
- `tests/ui/consts/const_unsafe_unreachable_ub.stderr`, blob `7d2448cc3c6dfcf06245404408d6f158912f6cdb`
  - expected const-eval `E0080` diagnostic.

### Rust Reference

Subject: `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`
  - `unsafe` does not permit UB;
  - unsafe abstractions must prevent safe clients from triggering UB;
  - invoking UB through compiler intrinsics is UB;
  - a `!` value must never exist.

## Revalidation

For another Rust revision, the cheapest reliable check is:

1. inspect `core::hint::unreachable_unchecked` in `library/core/src/hint.rs` and confirm its safety contract and implementation;
2. inspect `core::intrinsics::unreachable` in `library/core/src/intrinsics/mod.rs`;
3. inspect `LowerIntrinsics` for the handling of the `unreachable` intrinsic;
4. inspect the MIR definition of `TerminatorKind::Unreachable`;
5. inspect `ub_checks.rs` only to characterize diagnostic instrumentation, not to redefine the safety contract; and
6. compare the Miri and const-eval unreachable regression fixtures for changes in interpreter treatment.

A minimal capable-surface execution probe should then compile three cases with the exact toolchain:

- a direct reached `unsafe { hint::unreachable_unchecked() }` under native debug and optimized builds;
- the same operation under Miri; and
- a const evaluation that reaches the operation.

Preserve exact commands, `rustc -Vv`, stderr, exit status, optimization/debug-assertion settings, and MIR before/after `LowerIntrinsics`. A useful MIR discriminator is that the direct intrinsic call becomes `unreachable;` after the pass.

For verifier integration, add a separate semantic regression:

- one branch where a path condition proves the call unreachable and the proof succeeds;
- one branch where the call is reachable and verification must fail or emit an undischarged UB obligation; and
- one case where optimized MIR has already removed code downstream of the assumption, to confirm the source-to-model coverage layer does not silently treat that deletion as proof of safety.

Do not accept a test merely because a debug build emits a precondition diagnostic. The required invariant is that no well-defined modeled execution reaches the operation.
