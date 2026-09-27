# Panic-producing Rust primitives at nightly-2026-05-31

## Summary

At Rust `nightly-2026-05-31`, ordinary panic-producing primitives and their unchecked counterparts have fundamentally different verification obligations.

`panic!`, `assert!`, `assert_eq!`, `assert_ne!`, `Option::unwrap`/`expect`, `Result::unwrap`/`expect`, `unreachable!`, `todo!`, and `unimplemented!` use defined panic behavior when their failure condition occurs. Depending on the selected panic handler and strategy, a panic can unwind or terminate the process. A verifier therefore needs a distinct panic outcome; it must not translate these failure paths as undefined behavior merely because they return `!`.

`Option::unwrap_unchecked` and `Result::{unwrap_unchecked,unwrap_err_unchecked}` instead require the caller to prove that the failing variant is impossible. Their wrong-variant branches call `hint::unreachable_unchecked`; reaching those branches is undefined behavior. The safe and unchecked methods are consequently not interchangeable proof rules.

`debug_assert!` and its equality variants add a separate configuration boundary. Their assertion branch exists only when the `debug_assertions` configuration predicate is true. The source explicitly warns that replacing `assert!` with `debug_assert!` is appropriate only in safe code. A verifier analyzing unsafe invariants must therefore model the selected `debug_assertions` configuration rather than treating a debug assertion as a permanent precondition.

Exact panic text, payload representation, hook output, and backtrace behavior are generally weaker evidence than the control-flow class. The core documentation explicitly leaves the regular `panic!` payload representation as either `&str` or `String` unspecified. For Anneal-facing reasoning, preserve whether execution returns normally, panics, or invokes undefined behavior before preserving presentation details.

Basis: pinned Rust core **source/documentation** + pinned Rust Reference **normative** panic semantics + **derived** verification distinctions. No fresh program was executed for this report.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the source revision behind the Anneal-era `nightly-2026-05-31` toolchain used for these primitive contracts; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision associated with that compiler snapshot.

The report covers the semantic boundary relevant to verification: which input/condition returns a value, which invokes a defined panic, which depends on `debug_assertions`, and which is unsafe undefined behavior.

It does not repeat the corpus's broader panic/unwind/abort control-flow taxonomy. In particular, this report uses "panics" for the Rust panic mechanism and does not imply that every panic unwinds. The pinned Reference permits standard-library panic handling by either stack unwinding or process abort, with the strategy selected by compiler configuration and target support. A custom `#[panic_handler]` in `no_std` code can implement other non-returning behavior consistent with its required `fn(&PanicInfo) -> !` signature.

It also does not model exact diagnostic formatting as a program-semantic contract unless a primitive's documented API specifically makes that text relevant.

## Findings

### A safe panic is a defined failure path, not undefined behavior

The pinned Reference defines panic as a mechanism that prevents normal function return in response to an error condition. It describes the standard `std` handlers as `unwind` and `abort`; the former unwinds the stack and can potentially be recovered, while the latter aborts the process.

The core `panic!` documentation says the macro panics the current thread. The implementation routes ordinary formatted panic paths through the `panic_fmt` language item. Unless the special `panic=immediate-abort` configuration is selected, `panic_fmt` constructs `PanicInfo` with `can_unwind = true` and calls the program's panic handler. Under `panic=immediate-abort`, it directly invokes the abort intrinsic instead.

For verification, the primary distinction is therefore:

```text
ordinary completion | panic outcome | undefined behavior
```

A panic is not a normal return, but neither is it automatically undefined behavior. Whether a particular verification contract accepts panicking executions is a higher-level policy question; the external Rust fact is that these outcomes are distinct.

Basis: pinned Reference **normative** panic semantics + core **source/documentation**.

### `panic!` is the common explicit safe entry point

At this revision, `panic!` is a compiler built-in macro. Core documents it as panicking the current thread and ultimately routes its ordinary string/formatted forms through the panic machinery.

The current implementation carries caller-location information with `#[track_caller]`. The default `std` hook commonly reports a message and source location, but that presentation is not a stable semantic identity. In particular, the core documentation states that a regular `panic!` payload can be represented as either `&str` or `String`, and which one is used is unspecified.

A verifier should therefore retain the fact that the path panics and, when user-visible diagnostics matter, the source location/payload expression. It should not make proof validity depend on one concrete internal payload representation.

Basis: core **source/documentation**.

### `assert!` has an always-active panic contract

The pinned core source defines `assert!` as a compiler built-in macro. Its documentation says it asserts that a boolean expression is true at runtime and invokes `panic!` if the expression cannot be evaluated to true.

The format arguments of the custom-message form are documented to be evaluated only if the assertion fails. This matters if those expressions have side effects. A transformation that eagerly evaluates custom assertion arguments would not preserve the primitive's behavior.

For verification, an ordinary assertion can be modeled as:

```text
evaluate cond
if cond:
    continue
else:
    panic
```

The assertion is not a caller-side safety precondition. If it fails, the defined behavior is panic.

Basis: core **documentation/source**.

### `assert_eq!` and `assert_ne!` evaluate the compared expressions once

Unlike the built-in `assert!` declaration, the equality and inequality macros expose their expansion in core.

`assert_eq!` first matches on `(&$left, &$right)`, compares the borrowed values, and calls `panicking::assert_failed` only when they differ. `assert_ne!` has the same structure but panics when the values compare equal. The custom formatting arguments are constructed inside the failure branch.

This structure has two verification-relevant consequences:

1. each compared operand expression is evaluated once; and
2. failure-message arguments are not evaluated on the success path.

A semantics-preserving translation should not duplicate either compared expression merely because the mathematical equality relation is pure.

Basis: core **source**.

### Debug assertions are configuration-dependent checks

`debug_assert!` expands to:

```text
if cfg!(debug_assertions) {
    assert!(...)
}
```

`debug_assert_eq!` and `debug_assert_ne!` similarly gate their ordinary assertion forms on the same configuration predicate.

The documentation states that optimized builds do not execute these checks by default unless `-C debug-assertions` enables them, while the expansion remains type-checked. It also explicitly warns that allowing an inconsistent state to continue is only non-unsafe when this occurs in safe code, and recommends replacing `assert!` with `debug_assert!` only in safe code.

This makes `debug_assert!` unsuitable as an unconditional proof assumption. A verifier must determine the compilation configuration:

- with `debug_assertions = true`, the failure branch is a panic path;
- with `debug_assertions = false`, the check does not execute and establishes no runtime condition.

If unsafe code is sound only because a debug assertion checked an invariant, disabling that assertion does not turn the invariant into a compiler guarantee. The program has a soundness bug if later unsafe operations require a fact that safe callers can violate.

Basis: core **source/documentation** + **derived** verification consequence.

### `Option::unwrap` and `expect` panic on `None`

`Option::unwrap` is a safe, consuming operation:

```text
Some(value) -> value
None        -> panic
```

The source implements the `None` branch through a cold `unwrap_failed` helper that calls the ordinary panic machinery. `Option::expect` has the same value/panic split but forwards its supplied message through `expect_failed`.

Both methods are `#[track_caller]`. That affects diagnostic attribution, not the success/failure semantics.

A verifier modeling `unwrap` as a partial mathematical projection has two sound choices:

- retain an explicit panic outcome on `None`; or
- prove `is_some()` and then simplify the call to the contained value.

It is unsound to silently treat `unwrap` as returning an arbitrary value on `None`.

Basis: core **source/documentation**.

### `Result::unwrap` and `expect` panic on `Err`

`Result::unwrap` is likewise a safe branch split:

```text
Ok(value) -> value
Err(error) -> panic
```

The ordinary non-`immediate-abort` helper formats the `Err` value through its `Debug` implementation, which explains the method's `E: Debug` bound. `Result::expect` uses the caller-supplied message and the same failure helper.

Under the special `panic=immediate-abort` configuration, core has a separate helper that does not construct the `dyn Debug` formatting machinery before panicking/aborting. Thus the semantic requirement is not "the `Debug` formatter definitely executes on every failing configuration." The durable rule is that the `Err` case is a panic path, with formatting behavior dependent on the panic configuration and implementation.

The same proof discipline as `Option::unwrap` applies: retain the panic outcome or establish `is_ok()` before replacing the operation by a projection.

Basis: core **source/documentation**.

### The unchecked unwrap variants replace panic with a safety obligation

At the same revision:

- `Option::unwrap_unchecked(None)` is documented as undefined behavior and implements the `None` arm with `hint::unreachable_unchecked()`;
- `Result::unwrap_unchecked(Err(_))` is documented as undefined behavior, forgets the error value in that branch, and invokes `hint::unreachable_unchecked()`; and
- `Result::unwrap_err_unchecked(Ok(_))` invokes `hint::unreachable_unchecked()`.

These methods do not mean "unwrap, but omit a dynamic check while retaining a panic if the invariant is wrong." They change the contract: the caller must ensure the rejected variant is impossible. Violating that promise is undefined behavior.

A verifier should therefore assign different obligations:

| Primitive | Rejected variant/condition | Semantic outcome |
| --- | --- | --- |
| `Option::unwrap` | `None` | panic |
| `Option::unwrap_unchecked` | `None` | undefined behavior |
| `Result::unwrap` | `Err` | panic |
| `Result::unwrap_unchecked` | `Err` | undefined behavior |
| `Result::unwrap_err_unchecked` | `Ok` | undefined behavior |

The separate `unreachable_unchecked` report owns the detailed unreachable intrinsic semantics. Here the important fact is that unchecked unwraps inherit that unsafe contract.

Basis: core **source/documentation**.

### `unreachable!`, `todo!`, and `unimplemented!` are safe panic shorthands

The safe `unreachable!` macro documents that it always panics if reached. Its own documentation explicitly contrasts it with `unreachable_unchecked`, which causes undefined behavior if reached.

`todo!` and `unimplemented!` are also panic shorthands. Their source expands fixed-message forms through core panicking helpers and custom-message forms through `panic!`.

For verification, these constructs can therefore share a panic outcome even though their diagnostic intent differs:

- `unreachable!`: programmer believes a safe path is unreachable;
- `todo!`: unfinished implementation;
- `unimplemented!`: deliberately unsupported/unimplemented operation.

Their descriptive intent does not turn the path into undefined behavior.

Basis: core **source/documentation**.

### `!` does not tell you why execution does not return

Many primitives in this report have return type `!`, as does `unreachable_unchecked`. That type says the call does not return normally; it does not classify the reason.

At this revision, at least these materially different behaviors can inhabit non-returning control flow:

- defined panic that may unwind;
- defined panic that aborts;
- an explicit abort;
- infinite execution; and
- undefined behavior from an unsafe unreachable promise.

A verification IR that collapses every `!`-typed operation to one undifferentiated "unreachable" node loses information needed to distinguish safe panic paths from UB assumptions.

Basis: pinned panic semantics + core source + **derived** consequence.

### Const evaluation turns a reached panic into a compile-time failure

`panic_fmt` is the language item used for const-evaluated panics, and the compiler hooks it during const evaluation. When a panic-producing expression must be evaluated in a constant context and its panic branch is reached, compilation/const evaluation fails rather than producing a runtime panic that can later execute.

This is an evaluation-stage distinction, not a different success condition for `unwrap` or `assert!`. A source-level verifier should know whether it is reasoning about a runtime operation that survives compilation or a required constant evaluation that the compiler must complete.

Basis: core **source** + **derived** stage distinction.

## Boundaries

**No fresh execution.** The report is grounded in exact pinned source and Reference text. It does not preserve runtime transcripts for each macro/method under unwind and abort configurations.

**No complete panic ABI report.** FFI unwind boundaries, catch-unwind behavior, destructor cleanup, double panics, panic hooks, and target-specific unwinder behavior belong to the broader panic/unwind subject.

**No guarantee of exact panic text.** Messages shown by `unwrap`, assertions, or convenience macros are useful diagnostics but are not treated here as stable semantic ABI. `panic!` payload representation is explicitly unspecified between regular string representations.

**No claim that `debug_assertions` follows optimization in every invocation.** Optimized builds disable debug assertions by default, but `-C debug-assertions` can override that. The actual compiler configuration is authoritative.

**No claim that a disabled debug assertion's expression executes.** The expansion places the assertion under a `cfg!(debug_assertions)` branch. The expression is still type-checked, but runtime evaluation is configuration-dependent.

**No equivalence between safe and unchecked unwraps.** Their successful variants coincide, but their rejected variants differ between panic and undefined behavior.

**No inference from the `!` type alone.** Non-returning type information does not distinguish panic, abort, divergence, or UB.

**No modeling policy is prescribed.** Whether an Anneal theorem requires panic-freedom, allows panic as a specified outcome, or proves only partial correctness is an Anneal design decision. This report preserves the Rust facts required to make that decision.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary Rust subject:

- repository: `rust-lang/rust`
- revision: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
- toolchain date: `2026-05-31`

Pinned files:

- `library/core/src/macros/panic.md`, blob `6bd23b3072ed9a2266ef029ac09f2266e45ed27b` — `panic!` user contract and payload caveat.
- `library/core/src/macros/mod.rs`, blob `c21191dbc19be8e56fd42a46499032442c97776a` — `panic!`, assertions, debug assertions, `unreachable!`, `todo!`, and `unimplemented!` macro definitions/documentation.
- `library/core/src/option.rs`, blob `a490a26aa0ff3b3b56bb1f5a3c2a74109cbc839d` — `Option::{unwrap,expect,unwrap_unchecked}` and failure helpers.
- `library/core/src/result.rs`, blob `f0e1a1def49d14d40e180d65123494765dbfdae0` — `Result::{unwrap,expect,unwrap_unchecked,unwrap_err_unchecked}` and failure helpers.
- `library/core/src/panicking.rs`, blob `3609dd1fe2e02e639d5ad52b5979c03f69463431` — `panic_fmt`, `panic_nounwind_fmt`, ordinary panic helper, panic-handler dispatch, and immediate-abort branch.
- `library/core/src/hint.rs`, blob `90326e649058bee9f49c1e600a054f2805a3ab4f` — `unreachable_unchecked` used by unchecked unwraps.

Primary Reference subject:

- repository: `rust-lang/reference`
- revision: `ad35aca481751a06afeb23820a672b0f3b11a476`
- `src/panic.md`, blob `2be7e42fb2c3d4c752202f87aa07c890d68e437b` — panic mechanism, panic handler, standard unwind/abort handlers, and strategy.
- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284` — unsafe code remains subject to UB rules and compiler-intrinsic UB remains UB.

No execution evidence is claimed.

## Revalidation

For a later Rust toolchain, the cheapest reliable revalidation is:

1. Identify the exact `rust-lang/rust` commit and its Reference revision.
2. Re-read `library/core/src/macros/panic.md` and `library/core/src/macros/mod.rs`.
   - Confirm ordinary `assert!` still panics on false.
   - Confirm equality assertions' operand-evaluation structure.
   - Confirm debug assertions' configuration gate.
3. Re-read `Option::{unwrap,expect,unwrap_unchecked}` and `Result::{unwrap,expect,unwrap_unchecked,unwrap_err_unchecked}`.
   - Record any changed success/failure variants.
   - Confirm whether unchecked variants still lower their rejected cases to an unsafe unreachable assumption.
4. Re-read `library/core/src/panicking.rs`.
   - Confirm the ordinary panic and non-unwinding panic entry points.
   - Confirm how the selected panic configurations reach the handler or abort.
5. Re-read the Reference panic chapter for changes to the panic-handler/strategy model.
6. If Anneal depends on exact generated control flow rather than source contracts, compile tiny fixtures for each row of `semantics-matrix.json` under:
   - unwind strategy;
   - abort strategy;
   - debug assertions on;
   - debug assertions off.
7. Preserve MIR or execution output only for distinctions the source-level rules do not settle.

The critical regression assertions are semantic, not textual:

- safe rejected variants/failed assertions remain panic paths;
- unchecked rejected variants remain UB obligations;
- debug assertions remain configuration-dependent;
- non-returning operations are not collapsed merely because they share type `!`.
