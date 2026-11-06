# Rust Panic, Unwind, Abort, Divergence, and `unreachable_unchecked` Semantics Across Source, MIR, and Charon

## Summary

In Rust at `nightly` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), computations that fail to produce an ordinary return value inhabit five semantically distinct outcome classes that a sound verification system must never conflate: (1) **unwinding panic** (traverses Rust stack frames, executes `Drop` destructors on live values, and may be caught at an enclosing `std::panic::catch_unwind` or thread boundary); (2) **aborting panic or unwind termination** (terminates the process in finite time without further Rust stack unwinding); (3) **nontermination** (infinite execution such as `loop {}`); (4) **early local control transfer** (`return`, `break`, `continue`); and (5) **undefined behavior** (such as reaching `core::hint::unreachable_unchecked()`, which invalidates the entire program execution and permits arbitrary compiler optimization).

Key findings across the language specification, standard-library primitives, `rustc` Mid-level Intermediate Representation (MIR), and Charon extraction:

1. **Divergence (`!`) vs. termination and correctness taxonomy:** The Rust Reference defines a *diverging* expression as one that never completes normal execution and assigns it the uninhabited never type `!`. Because `loop {}`, `panic!`, process abort, and `unreachable_unchecked()` all have type `!`, a `!` return type proves only the absence of a normal return value. Verification claims must therefore distinguish **normal-return partial correctness** (if an execution returns normally, the postcondition holds, paired with an independent proof of UB-freedom) from **normal-return total correctness** (every in-scope execution reaches a normal return in finite time, Satisfies the postcondition, and is UB-free) or explicitly outcome-indexed contracts. Panic-freedom, unwind-freedom, finite termination, and UB-freedom are pairwise independent properties.
2. **Safe panic primitives vs. configuration-gated assertions and unsafe unchecked unwraps:** Safe failure primitives (`panic!`, `assert!`, `assert_eq!`, `assert_ne!`, `Option::{unwrap, expect}`, `Result::{unwrap, expect}`, `unreachable!`, `todo!`, `unimplemented!`) route rejected branches through defined panic machinery (`core::panicking::panic_fmt` or, under `panic=immediate-abort`, the abort intrinsic). By contrast, `debug_assert!`, `debug_assert_eq!`, and `debug_assert_ne!` expand under `if cfg!(debug_assertions)` and provide no runtime guarantee when debug assertions are disabled. Unsafe `Option::unwrap_unchecked` and `Result::{unwrap_unchecked, unwrap_err_unchecked}` replace the panic branch with `core::hint::unreachable_unchecked()`, converting the rejected variant into caller-side undefined behavior.
3. **`core::hint::unreachable_unchecked` and `assert_unchecked` lowering (`LowerIntrinsics`):** `unreachable_unchecked()` wraps an optional diagnostic check (`assert_unsafe_precondition!(check_language_ub, ...)`) around the `core::intrinsics::unreachable` compiler intrinsic. The wrapper check is explicitly non-load-bearing for safety and is disabled during const evaluation and under Miri so those evaluators diagnose the underlying UB directly (`E0080` and `Undefined Behavior: entering unreachable code`). `rustc`'s `LowerIntrinsics` pass rewrites `intrinsics::unreachable()` into `TerminatorKind::Unreachable`, authorizing downstream passes to prune reaching branches. Sound verification must treat `unreachable_unchecked()` as a proof obligation that the path condition is false (`path_condition -> False`), never as a safe panic or benign divergence.
4. **`rustc` MIR panic/unwind control flow and `AbortUnwindingCalls`:** MIR separates `TerminatorKind::Return`, `UnwindResume`, `UnwindTerminate(reason)`, `Unreachable`, `Assert`, and `Call { target, unwind }`, where `UnwindAction` is `Continue`, `Cleanup(bb)`, `Terminate(reason)`, or `Unreachable`. The required `AbortUnwindingCalls` pass rewrites `UnwindResume` and call unwind edges according to `-C panic=abort`, target unwind support, and caller/callee ABI unwind permissions.
5. **Charon ULLBC/LLBC translation boundaries (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`):** Charon maps `Return` to `Return`, `UnwindResume` to `UnwindResume`, `UnwindTerminate` to `Abort(AbortKind::UnwindTerminate)`, and `Unreachable` to `Abort(AbortKind::UndefinedBehavior)`. However, Charon collapses recognized panic calls (`panic`, `panic_fmt`, `begin_panic`) directly into `Abort(AbortKind::Panic(...))` while discarding their MIR `unwind` edge, attaches a synthetic `Abort(UndefinedBehavior)` continuation block to unrecognized `target: None` calls, and removes explicit MIR bounds/overflow/division-by-zero `Assert` terminators during `reconstruct_fallible_operations`.

## Applicability

The findings in this report apply to the pinned toolchain and specification subjects recorded in `REPORT.json`:

- **Rust compiler and standard library:** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly`), covering `library/core/src/{macros,option.rs,result.rs,panicking.rs,hint.rs,intrinsics/mod.rs,ub_checks.rs}`, `library/std/src/panic.rs`, `compiler/rustc_middle/src/mir/{syntax.rs,interpret/error.rs}`, and `compiler/rustc_mir_transform/src/{abort_unwinding_calls.rs,lower_intrinsics.rs}`.
- **Rust Reference:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (bundled submodule of `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), specifically `src/{divergence.md,panic.md,behavior-considered-undefined.md,types/never.md,expressions/loop-expr.md}`.
- **Charon extractor:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (version `0.1.210`, pinned by Aeneas `nightly-2026.06.03`).

**Multi-version and configuration scope:**
- The language-level distinctions among normal return, unwinding panic, aborting panic, semantic nontermination, and undefined behavior—as well as the standard-library contracts of `panic!`, `assert!`, `debug_assert!`, `Option`/`Result` unwraps, and `hint::unreachable_unchecked`—are stable normative/library rules at the examined `nightly` snapshot and across standard Rust releases.
- Compiler-configuration flags materially alter lowered semantics within the same compiler revision:
  - `-C panic=unwind` vs. `-C panic=abort` (and the unstable `-C panic=immediate-abort` core path) changes whether panics traverse Rust stack frames and run destructors or terminate immediately (`AbortUnwindingCalls`).
  - `-C debug-assertions` (`cfg!(debug_assertions)`) controls whether `debug_assert!`, `debug_assert_eq!`, and `debug_assert_ne!` emit runtime checks.
  - `-C ub-checks` (coupled with `check_language_ub` outside const-eval and Miri) controls whether `unreachable_unchecked` emits an optional `panic_nounwind_fmt` diagnostic trap before reaching `intrinsics::unreachable()`.

## Findings

### 1. Rust Outcome Taxonomy and Verification Correctness Terminology

`Basis: normative | derived`

Under the pinned Rust Reference (`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, `src/divergence.md`, `src/types/never.md`, `src/panic.md`, `src/expressions/loop-expr.md`, `src/behavior-considered-undefined.md`), source expressions and function calls partition into distinct semantic outcomes:

| Outcome Class | Normative Status | Stack Cleanup (`Drop`) | Finite Termination? | Normal Return Value? | Verification Obligation / Role |
| --- | --- | --- | --- | --- | --- |
| **Normal return** | Defined | Scope-exit drops run | Yes | Yes (`T`) | Must satisfy postcondition $Q$. |
| **Unwinding panic** (`panic=unwind`) | Defined | Runs live destructors across unwinding frames | Yes (if uncaught or caught + finishes) | No (at panicking frame; `!`) | Observable effectful path; may mutate state via `Drop` or be caught by enclosing `catch_unwind`. |
| **Aborting panic / terminate** (`panic=abort`, `UnwindTerminate`) | Defined | Skips Rust stack unwind | Yes (process terminates) | No (`!`) | Finite non-returning exit; postconditions on return values do not apply. |
| **Semantic nontermination** (`loop {}`) | Defined | None after loop lock-in | No (infinite steps) | No (`!`) | Satisfies normal-return partial correctness vacuously; violates total correctness. |
| **Undefined behavior (UB)** (`unreachable_unchecked`, invalid values) | **Forbidden** | Unspecified / arbitrary | Unspecified | Unspecified | Must be proved unreachable (`False`) on all in-scope executions; never an acceptable outcome. |

From this taxonomy, five verification principles follow (**derived**):
1. **Divergence (`!`) is narrower than nontermination in one direction and broader in another:** Every semantically nonterminating expression fails to complete normally, but a diverging expression of type `!` (such as `panic!()`, `std::process::abort()`, or `return`) need not run forever.
2. **Normal-return partial correctness vs. total correctness:** Because the Rust Reference does not normatively define "partial correctness" or "total correctness," specifications must qualify them explicitly:
   - *Normal-return partial correctness* for precondition $P$ and postcondition $Q$: for every in-scope execution starting in $P$, no step exhibits UB, and *if* the function returns normally, the resulting state/value satisfies $Q$.
   - *Normal-return total correctness* for $P$ and $Q$: every in-scope execution starting in $P$ is UB-free, reaches a normal return in finite time (excluding infinite loops, unwinding panics, and process aborts), and satisfies $Q$.
3. **Independence of panic-freedom, unwind-freedom, termination, and UB-freedom:**
   - A panic-free function (`fn spin() -> ! { loop {} }`) can fail to terminate; a terminating function (`panic!()` under `panic=abort`) is not panic-free.
   - Under `panic=abort`, a function is trivially unwind-free across Rust frames yet can still panic and abort the process.
   - A panic-free function can exhibit pointer UB, and a UB-free function can intentionally call `panic!()`.
4. **Callee normal return vs. enclosing recovery:** When `std::panic::catch_unwind` catches an unwinding panic, the outer recovery computation may return `Err(payload)` normally, but the panicking inner callee still did not return a value of its declared return type.

### 2. Safe Panic Primitives, `debug_assert!`, and Unchecked `Option`/`Result` Unwraps

`Basis: normative | documentation | source | derived`

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (cataloged in `support/rust-panic-primitives/semantics-matrix.json` and `support/rust-panic-primitives/source-map.json`), standard-library failure primitives divide into three verification categories:

| Primitive Family | Source Location (`library/core/src/...`) | Failure Condition | Semantic Outcome on Failure | Key Evaluation and Configuration Invariants |
| --- | --- | --- | --- | --- |
| `panic!`, `unreachable!`, `todo!`, `unimplemented!` | `macros/panic.md`, `macros/mod.rs`, `panicking.rs` | Reaching the macro invocation | **Defined panic** (`panic_fmt` with `can_unwind = true`, or abort intrinsic under `panic=immediate-abort`) | `#[track_caller]`; whether regular `panic!` payload is `&str` or `String` is explicitly unspecified. Const-eval turns reached panics into compile-time failure. |
| `assert!(cond, ...)` | `macros/mod.rs` (built-in macro) | `!cond` | **Defined panic** | Always active regardless of `debug_assertions`; custom format arguments are evaluated **only** when `!cond`. |
| `assert_eq!(left, right, ...)`, `assert_ne!(left, right, ...)` | `macros/mod.rs` | `!*left == *right` / `*left == *right` | **Defined panic** (`panicking::assert_failed`) | Evaluates `(&$left, &$right)` **exactly once** before comparison; custom message arguments are evaluated only in the failure branch. |
| `debug_assert!`, `debug_assert_eq!`, `debug_assert_ne!` | `macros/mod.rs` | `!cond` when `cfg!(debug_assertions)` is true | **Defined panic** if `cfg!(debug_assertions)`; **no-op** if `!cfg!(debug_assertions)` | Expands to `if cfg!(debug_assertions) { assert!(...); }`. Unsafe code must **never** rely on `debug_assert!` to establish a soundness invariant. |
| `Option::{unwrap, expect}`, `Result::{unwrap, expect}` | `option.rs`, `result.rs` | `None` / `Err(e)` | **Defined panic** (`unwrap_failed` / `expect_failed`) | Safe consuming projections. Under `panic=immediate-abort`, `Result::unwrap` skips `E: Debug` formatting before aborting. |
| `Option::unwrap_unchecked`, `Result::{unwrap_unchecked, unwrap_err_unchecked}` | `option.rs`, `result.rs` | `None` / `Err(_)` / `Ok(_)` | **Undefined behavior** (`hint::unreachable_unchecked()`) | `unsafe fn`; `Result::unwrap_unchecked` suppresses dropping `Err(e)` (`ManuallyDrop`) and invokes `hint::unreachable_unchecked()`. |

### 3. `core::hint::unreachable_unchecked`, `assert_unchecked`, and `LowerIntrinsics`

`Basis: normative | documentation | source | derived`

Inspecting `library/core/src/hint.rs`, `library/core/src/intrinsics/mod.rs`, `library/core/src/ub_checks.rs`, and `compiler/rustc_mir_transform/src/lower_intrinsics.rs` at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`support/rust-unreachable-unchecked/semantics-matrix.json` and `support/rust-unreachable-unchecked/source-map.json`) separates three layers of `unreachable_unchecked`:

1. **Source contract (`library/core/src/hint.rs`, blob `90326e649058bee9f49c1e600a054f2805a3ab4f`):**
   - `pub const unsafe fn unreachable_unchecked() -> !` requires the caller to prove that control flow can never reach the call site. `core::hint::assert_unchecked(cond: bool)` is documented as logically equivalent to `if !cond { unsafe { unreachable_unchecked() } }`.
2. **Optional diagnostic instrumentation (`library/core/src/ub_checks.rs`, blob `f25781ea8ce5aef2c332b19246c1b5c7e041b2c6`):**
   - Before calling `intrinsics::unreachable()`, `unreachable_unchecked` invokes `assert_unsafe_precondition!(check_language_ub, "hint::unreachable_unchecked must never be reached", () => false)`.
   - When runtime UB checks are enabled, a violation calls `core::panicking::panic_nounwind_fmt` with a message explicitly stating that the check is optional and cannot be relied on for safety.
   - Crucially, `check_language_ub` is **disabled during const evaluation and under Miri** so that those interpreters reach `intrinsics::unreachable()` directly and report semantic UB (`E0080: entering unreachable code` in `tests/ui/consts/const_unsafe_unreachable_ub.stderr` and `Undefined Behavior: entering unreachable code` in `src/tools/miri/tests/fail/unreachable.stderr`).
3. **MIR lowering (`compiler/rustc_mir_transform/src/lower_intrinsics.rs`, blob `fe53d301c5574101399b60d38451a57b24c43535`):**
   - `LowerIntrinsics` matches calls to `sym::unreachable` (`core::intrinsics::unreachable`, which is `#[rustc_intrinsic]` and `#[rustc_nounwind]`) and replaces the `Call` terminator with `TerminatorKind::Unreachable`, as captured in `tests/mir-opt/lower_intrinsics.unreachable.LowerIntrinsics.panic-unwind.diff`.
   - Because subsequent MIR and LLVM passes may eliminate branches and checks upstream of `TerminatorKind::Unreachable`, a verifier consuming post-lowering or optimized MIR must discharge `path_condition -> False` at every `Unreachable` terminator rather than assuming the branch is benignly dead.

### 4. `rustc` MIR Representations, `AbortUnwindingCalls`, and Charon Translation

`Basis: source | derived`

Comparing `rustc` MIR (`compiler/rustc_middle/src/mir/syntax.rs`, `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`) against Charon (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/src/ast/{gast.rs,ullbc_ast.rs}`, `charon/src/bin/charon-driver/translate/translate_bodies.rs`, `charon/src/transform/resugar/reconstruct_fallible_operations.rs`) reveals both preserved and collapsed control-flow edges:

| `rustc` MIR Construct | `rustc` MIR Semantics (`syntax.rs` / `abort_unwinding_calls.rs`) | Pinned Charon ULLBC/LLBC Translation (`0.1.210`) | Verification Consequence |
| --- | --- | --- | --- |
| `TerminatorKind::Return` | Normal function return to caller. | `Return` | Preserved directly. |
| `TerminatorKind::UnwindResume` | Resumes stack unwinding at end of cleanup path. Rewritten by `AbortUnwindingCalls` to `UnwindTerminate(Abi)` if body cannot unwind, or `Unreachable` if target lacks unwind support. | `UnwindResume` | Preserved when present in extracted MIR phase. |
| `TerminatorKind::UnwindTerminate(reason)` | Aborts execution during unwind (e.g., `Reason::Abi` or `Reason::InCleanup`). | `Abort(AbortKind::UnwindTerminate)` | Distinguishes unwind-triggered process termination from UB and ordinary panic. |
| `TerminatorKind::Unreachable` | Executing this terminator is immediate UB. | `Abort(AbortKind::UndefinedBehavior)` | Preserves UB obligation (`path_condition -> False`). |
| Recognized panic call (`panic`, `panic_fmt`, `begin_panic`) | `Call { target: None, unwind: UnwindAction }` (carries explicit `Cleanup(bb)` or `Continue` unwind edge). | `Abort(AbortKind::Panic(name))` (**discards the MIR `unwind` edge**; source contains a `TODO` on handling the unwind target). | Charon retains the fact that the path panics, but loses the intra-function cleanup CFG edge from that panic call. |
| Unrecognized diverging call (`Call { target: None, .. }`) | Callee has return type `!` (may loop forever, panic, or abort). | Emits ordinary `Call` targeting a synthetic basic block containing `Abort(AbortKind::UndefinedBehavior)`. | Preserves caller CFG well-formedness, but does not classify whether the callee loops, panics, or aborts. |
| `TerminatorKind::Assert { cond, expected, msg, target, unwind }` | Runtime bounds, overflow, or division-by-zero check; panics and follows `unwind` on failure. | Removed by `reconstruct_fallible_operations` when recognized, folding the failure check into verification-side array/slice/arithmetic semantics. | Absence of an explicit `Assert` branch in LLBC does not mean the Rust operation cannot panic; the operation's model semantics must enforce the check. |

## Boundaries

- **Not examined:**
  - Fresh execution of `rustc`, Miri, or Charon on new panic/unwind test fixtures (this report relies on pinned compiler/library/Charon source and checked-in upstream test artifacts).
  - Target-specific unwinder implementations (DWARF `.eh_frame`, Windows SEH, WebAssembly exceptions), custom `#[panic_handler]` implementations in `no_std` binaries, or `std::panic::set_hook` payload inspection.
  - Exhaustive enumeration of every `rustc` MIR optimization or LLVM pass that propagates `TerminatorKind::Unreachable`.
- **Unknown:**
  - How future versions of Charon and Aeneas will translate the currently discarded MIR `unwind` edge on recognized panic calls (`AbortKind::Panic`).
- **Known not to apply:**
  - A return type of `!` does **not** imply nontermination (`loop {}`), panic-freedom, unwind-freedom, or UB-freedom.
  - `debug_assert!` does **not** establish a runtime invariant in builds where `cfg!(debug_assertions)` is false.
  - `Option::unwrap_unchecked` and `Result::unwrap_unchecked` are **not** optimization hints that fall back to panicking; reaching their rejected variant is undefined behavior.
  - The optional `assert_unsafe_precondition!` trap inside `core::hint::unreachable_unchecked` is **not** part of its safety contract and is suppressed in const evaluation and Miri.
- **Unsupported:**
  - At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `std::panic::catch_unwind` is not symbolically interpreted (preserved as an opaque external call in `charon/tests/ui/simple/catch-unwind.out`), and recognized panic calls do not preserve their MIR cleanup target edge.

## Evidence

### Primary Upstream Sources

- **Rust Reference (`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`):**
  - `src/divergence.md` (blob `5e25d6d0d944ae8a62236ce7e46f347ded3fbfcc`): diverging expressions never complete normal execution.
  - `src/types/never.md` (blob `fe30bce74d6ab02eb06b9d6a852f9dc3e523eec2`): `!` has no values and marks functions that never return normally.
  - `src/panic.md` (blob `2be7e42fb2c3d4c752202f87aa07c890d68e437b`): `unwind` vs. `abort` handlers, destructor cleanup during unwind, `catch_unwind`, and FFI unwind boundaries.
  - `src/expressions/loop-expr.md` (blob `8e67295482c3826c841585172560d93b2823510f`): `loop` without `break` diverges.
  - `src/behavior-considered-undefined.md` (blob `373052061c50fc2f6d1c07a91960d40bac505284`): whole-program UB invalidity, compiler-intrinsic UB, uninhabited `!` values, and invalid ABI unwinding.
- **Rust standard library and compiler (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
  - `library/core/src/macros/panic.md` (blob `6bd23b3072ed9a2266ef029ac09f2266e45ed27b`) and `library/core/src/macros/mod.rs` (blob `c21191dbc19be8e56fd42a46499032442c97776a`): `panic!`, `assert!`, `assert_eq!`, `assert_ne!`, `debug_assert*!`, `unreachable!`, `todo!`, `unimplemented!`.
  - `library/core/src/option.rs` (blob `a490a26aa0ff3b3b56bb1f5a3c2a74109cbc839d`) and `library/core/src/result.rs` (blob `f0e1a1def49d14d40e180d65123494765dbfdae0`): safe vs. `_unchecked` unwrap methods.
  - `library/core/src/panicking.rs` (blob `3609dd1fe2e02e639d5ad52b5979c03f69463431`): `panic_fmt`, `panic_nounwind_fmt`, `assert_failed`, and `panic=immediate-abort` dispatch.
  - `library/core/src/hint.rs` (blob `90326e649058bee9f49c1e600a054f2805a3ab4f`), `library/core/src/intrinsics/mod.rs` (blob `78d7314c58110b49839894a0f69377f4ee0d1204`), and `library/core/src/ub_checks.rs` (blob `f25781ea8ce5aef2c332b19246c1b5c7e041b2c6`): `unreachable_unchecked`, `assert_unchecked`, `intrinsics::unreachable`, and `check_language_ub`.
  - `compiler/rustc_middle/src/mir/syntax.rs` (blob `07eaa085fabc9742d0d51c73eeba91dcc9e67d2e`), `compiler/rustc_middle/src/mir/interpret/error.rs` (blob `7d9f6903d3ef0e5a441081bb0aba3b50280b7449`), `compiler/rustc_mir_transform/src/lower_intrinsics.rs` (blob `fe53d301c5574101399b60d38451a57b24c43535`), and `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`.
  - Checked-in compiler/Miri artifacts at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`: `tests/mir-opt/lower_intrinsics.rs` (blob `e8a770147741598a84e52e340d285fe59611c2f0`), `tests/mir-opt/lower_intrinsics.unreachable.LowerIntrinsics.panic-unwind.diff` (blob `2b715ac1d635b0c8991d475250f611192a8308f0`), `src/tools/miri/README.md` (blob `3d0716a082d4334cf1642aac1c165738c1a353a9`), `src/tools/miri/tests/fail/unreachable.{rs,stderr}` (blobs `3389d5b9ddeafd46d2748f3f863596ea7947da96` and `ab8ba4a68e5feea69fd2a1811876f9e9693bc94c`), and `tests/ui/consts/const_unsafe_unreachable_ub.{rs,stderr}` (blobs `39f053951276ed77a76edb816c0fc819efc799ea` and `7d2448cc3c6dfcf06245404408d6f158912f6cdb`).
- **Charon source and checked-in test outputs (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`):**
  - `charon/src/ast/gast.rs`, `charon/src/ast/ullbc_ast.rs`, `charon/src/bin/charon-driver/translate/translate_bodies.rs`, `charon/src/transform/resugar/reconstruct_fallible_operations.rs`, and `charon/tests/ui/{panics.out,diverging.out,simple/catch-unwind.out}`.

### Preserved Package Support Artifacts

- **Panic primitives contract matrix and source map (observed 2026-09-27):**
  - `support/rust-panic-primitives/semantics-matrix.json`
  - `support/rust-panic-primitives/source-map.json`
- **`unreachable_unchecked` contract matrix and source map (observed 2026-09-27):**
  - `support/rust-unreachable-unchecked/semantics-matrix.json`
  - `support/rust-unreachable-unchecked/source-map.json`

## Revalidation

1. **Source diffing on toolchain upgrades:**
   - Diff `src/{divergence.md,panic.md,types/never.md,behavior-considered-undefined.md}` in `rust-lang/reference`.
   - Diff `library/core/src/{macros/mod.rs,option.rs,result.rs,panicking.rs,hint.rs,intrinsics/mod.rs,ub_checks.rs}` and `compiler/rustc_mir_transform/src/{lower_intrinsics.rs,abort_unwinding_calls.rs}` in `rust-lang/rust` against the line ranges in `support/rust-panic-primitives/source-map.json` and `support/rust-unreachable-unchecked/source-map.json`.
   - Diff Charon's `AbortKind`, `translate_bodies.rs` (especially recognized panic calls and `target: None` calls), and `reconstruct_fallible_operations.rs`.
2. **Discriminator probes on an execution-capable surface:**
   - Compile a small crate containing each row of `support/rust-panic-primitives/semantics-matrix.json` and `support/rust-unreachable-unchecked/semantics-matrix.json` under the four-way matrix `{-C panic=unwind, -C panic=abort} × {-C debug-assertions=yes, -C debug-assertions=no}` with `--emit=mir`.
   - Confirm that `LowerIntrinsics` still rewrites `core::intrinsics::unreachable()` to `TerminatorKind::Unreachable`, that `AbortUnwindingCalls` rewrites `UnwindResume` and unwind edges under `-C panic=abort`, and that Miri and const evaluation reject a reached `hint::unreachable_unchecked()` with `entering unreachable code` rather than relying on the optional `ub_checks` wrapper trap.
