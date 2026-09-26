# Panic, unwind, abort, and divergence in Rust/MIR at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the Rust outcomes that all fail to return normally are not interchangeable. A computation can return normally, unwind, terminate the process, execute undefined behavior, or fail to terminate. Rust's type-level notion of divergence deliberately groups several of those possibilities: an expression of type `!` never completes normal execution, but that fact alone does not say whether it panics, aborts, loops forever, or otherwise cannot return.

MIR preserves more control-flow detail than the source-level `!` type. Normal completion uses `Return`. A call with `target: None` is known not to return normally. Potentially unwinding terminators carry an `UnwindAction` that can continue unwinding, enter cleanup code, terminate, or declare unwinding unreachable. Cleanup blocks end with `UnwindResume` or `UnwindTerminate` rather than ordinary `Return`. `Unreachable` is different again: MIR explicitly documents executing it as undefined behavior, not as ordinary nontermination.

The panic strategy changes those distinctions before code generation. Under unwind, a panic may traverse Rust frames and run destructors. Under abort, no Rust stack unwinding occurs. rustc's required `AbortUnwindingCalls` MIR pass rewrites unwind paths so that a body or target that may not unwind either terminates or marks the unwind edge unreachable as appropriate. The panic strategy is therefore part of the compilation subject's semantics, not merely a linker preference.

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, Charon retains several distinctions but not the complete rustc unwind graph in every case. It preserves normal return and unwind-resume, maps rustc unwind termination to `Abort(UnwindTerminate)`, and maps MIR `Unreachable` to `Abort(UndefinedBehavior)`. Recognized panic calls become `Abort(Panic(...))`; that translation path explicitly ignores the call's MIR unwind edge. Charon's fallible-operation reconstruction can also move panic behavior from explicit control-flow checks into the semantics of reconstructed array, slice, and arithmetic operations.

No fresh rustc, Charon, or runtime execution was performed. The report uses the pinned Rust Reference, exact rustc and Charon source, and checked-in Charon output fixtures. Those fixtures are preserved upstream execution artifacts, not execution performed on this surface.

## Applicability

- Rust compiler: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler revision behind Anneal's pinned Charon toolchain for nightly-2026-05-31.
- Rust Reference: `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.
- Charon: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`, pinned by Aeneas nightly-2026.06.03.

The Rust Reference defines the language-level panic and divergence distinctions used below. rustc source establishes the exact MIR representation and panic-strategy rewriting at the pinned compiler revision. Charon source establishes what the pinned extractor preserves or collapses. This report does not infer adjacent-version continuity.

## Findings

### Divergence means absence of normal completion, not one particular failure mode

The Rust Reference defines a diverging expression as one that never completes normal execution. Expressions of type `!` are diverging, and the never type has no values. An infinite `loop` without an associated `break` is one source of divergence; `panic!` is another.

Those cases have different runtime behavior. An infinite loop can keep executing indefinitely. A panic can unwind or abort depending on the selected panic handler and other boundaries. A function returning `!` therefore promises that it does not return normally; the type does not identify why.

Basis: **normative** Rust Reference.

### Panic strategy distinguishes recoverable unwinding from non-recoverable termination

The Rust Reference describes the standard library's two panic handlers as `unwind` and `abort`. The unwind handler traverses Rust frames and runs destructors for live objects while searching for a recovery point. The abort handler terminates the process and does not perform that Rust stack unwind. `catch_unwind` only catches unwinding panics; it cannot turn an aborting panic into a normal return.

The `-C panic` compiler option selects the panic strategy. The Reference also notes that abort-strategy compilation permits the optimizer to assume that unwinding across Rust frames is impossible. Panic strategy must therefore be part of any claim that distinguishes cleanup, recovery, and process termination.

Basis: **normative** Rust Reference + pinned standard-library **source**.

### MIR represents normal return, unwinding, termination, and UB separately

`TerminatorKind::Return` is the ordinary normal-return terminator. `UnwindResume` ends a cleanup frame by continuing stack unwinding. `UnwindTerminate` ends the frame by terminating execution. `Unreachable` is explicitly documented as a terminator that must never execute; executing it is undefined behavior.

Potentially panicking MIR terminators carry an `UnwindAction`. `Continue` continues unwinding without local cleanup, `Cleanup(bb)` enters a cleanup block, `Terminate(reason)` terminates if unwinding occurs, and `Unreachable` says an unwind on that edge would itself be undefined behavior. These alternatives are semantically different even though none is an ordinary successful return.

Basis: pinned rustc **source**, `compiler/rustc_middle/src/mir/syntax.rs`.

### A diverging call has no normal successor, but MIR does not encode its cause in `target`

`TerminatorKind::Call` stores an optional normal target. The pinned MIR documentation says `target: None` means the call necessarily diverges. That field records absence of normal continuation; it does not say whether the callee loops forever, panics, aborts, or terminates another way.

The same call separately carries an unwind action. A consumer that needs to distinguish total correctness, panic freedom, unwind behavior, and mere absence of normal return must therefore keep the normal-successor fact separate from the unwind/outcome facts.

Basis: pinned rustc **source**.

### Assertions are normal control flow plus a panic edge, not UB by default

MIR `Assert` evaluates a Boolean condition. On success it proceeds to its normal target. On failure it initiates a panic and follows the terminator's unwind policy. The MIR source explicitly notes that an unwind cleanup path need not execute under `panic=abort`.

This matters for verification terminology. A bounds check or overflow check that panics is not equivalent to `Unreachable` merely because both prevent the normal successor from executing. `Unreachable` means execution of that MIR point is UB; a failing assertion invokes Rust's panic behavior.

Basis: pinned rustc **source**.

### `panic=abort` changes the MIR unwind graph through a required pass

`AbortUnwindingCalls` is a required rustc MIR pass. Its source explains the invariant it enforces for `panic=abort`: Rust-defined functions are treated as non-unwinding, while foreign functions may still be declared with unwind-capable ABIs.

The pass rewrites `UnwindResume` to `UnwindTerminate(Abi)` when the enclosing body may not unwind, or to `Unreachable` when the target cannot support unwinding at all. For individual calls and other unwind-capable terminators, it removes cleanup edges when the operation cannot unwind and converts continued unwinding to termination when the callee may unwind but the caller may not.

Thus a MIR consumer must bind its conclusion to the MIR phase and panic configuration it receives. An unwind edge present before this pass and an abort-strategy body after this pass are not interchangeable representations.

Basis: pinned rustc **source**, `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`.

### Unwinding is behavior-bearing because cleanup can run destructors

The Reference's unwind contract requires cleanup of live Rust objects while an unwind crosses Rust frames. MIR makes that work visible through cleanup basic blocks and unwind actions. The separate drop-elaboration report in this corpus establishes when potential drops become precise runtime drop behavior.

Consequently, replacing unwind with generic failure can lose program behavior even when the final operation never returns successfully. Destructors may mutate memory, release resources, invoke user code, or themselves panic. Whether those effects matter to a verification promise depends on the promise, but the distinction cannot be discarded merely because both paths are non-successful.

Basis: **normative** Rust Reference + pinned rustc **source** + existing corpus drop report.

### FFI unwind permission is part of the outcome boundary

The Rust Reference permits unwinding across only appropriate ABI boundaries. Unwinding across a frame whose ABI does not permit it is undefined behavior. The pinned compiler's unwind-abort pass uses ABI information when deciding whether a body or call can unwind and when an unwind must terminate.

This report uses that fact only to characterize the panic/unwind boundary. It does not attempt a complete FFI report.

Basis: **normative** Rust Reference + pinned rustc **source**.

### Charon preserves explicit outcome categories for several MIR terminators

The pinned ULLBC AST has separate `Return`, `UnwindResume`, and `Abort(AbortKind)` terminators. `AbortKind` distinguishes `Panic`, `UndefinedBehavior`, and `UnwindTerminate`.

The rustc-to-Charon body translator maps MIR `Return` to `Return`, `UnwindResume` to `UnwindResume`, `UnwindTerminate` to `Abort(UnwindTerminate)`, and `Unreachable` to `Abort(UndefinedBehavior)`. Those mappings preserve a useful distinction among normal return, continuing unwind, process termination caused by unwind policy, and UB.

Basis: pinned Charon **source**, `charon/src/ast/gast.rs`, `charon/src/ast/ullbc_ast.rs`, and `charon/src/bin/charon-driver/translate/translate_bodies.rs`.

### Recognized panic calls collapse their MIR unwind edge in Charon

The same Charon translator recognizes Rust panic language items and names such as `panic`, `panic_fmt`, and `begin_panic`. It turns those calls directly into `Abort(AbortKind::Panic(...))`. The source asserts that the rustc normal target is absent and contains a TODO asking whether it should do something with the unwind edge.

The resulting Charon panic node therefore says that this path panics, but it does not retain the MIR choice among continuing unwind, entering a particular cleanup block, or terminating at that call site. A downstream proof that cares about unwind cleanup cannot recover that edge solely from the final panic node.

Basis: pinned Charon **source**.

### Charon gives a synthetic UB continuation to other no-return calls

For a non-recognized call whose rustc normal target is absent, the pinned translator synthesizes a target block containing `Abort(UndefinedBehavior)` and emits an ordinary Charon call targeting that block. If the callee obeys its no-return contract, the synthetic target is never reached; if control returned there, the model treats that impossible return as UB.

This preserves the caller CFG shape without changing the source-level fact that the callee has no normal return. It still does not identify whether the callee's actual non-returning behavior is infinite execution, process termination, or another supported effect.

Basis: pinned Charon **source**.

### Charon can move panic checks from control flow into operation semantics

The `reconstruct_fallible_operations` pass states that rustc inserts runtime checks for bounds, overflow, and division by zero that lead to panics. Charon removes recognized dynamic checks because the verification-side semantics of array, slice, and arithmetic operations account for those failures instead.

After that transformation, absence of an explicit panic branch is not evidence that the Rust operation cannot panic. A verifier must know whether the reconstructed operation's semantics retained the relevant failure outcome.

Basis: pinned Charon **source**, `charon/src/transform/resugar/reconstruct_fallible_operations.rs`.

### Checked-in Charon artifacts preserve panic and no-return examples

The pinned repository contains generated LLBC specimens rather than only source comments. `charon/tests/ui/panics.out` shows explicit panic functions as `panic(...)` and an assertion failure as `assert(...) else panic(...)`. `charon/tests/ui/diverging.out` shows a Rust function returning `!` whose body ends in panic and a caller whose invocation of that function has no later normal-return sequence. `charon/tests/ui/simple/catch-unwind.out` represents `std::panic::catch_unwind` as an opaque external function at this pin.

These files are historical generated artifacts checked into the pinned repository. They are evidence that upstream observed those shapes when producing its fixtures; this report did not regenerate them.

Basis: preserved upstream **execution** artifacts paired with pinned **source**; no fresh execution.

### Verification terminology should keep four questions separate

The pinned sources support four independent questions that are easy to collapse:

1. Can execution return normally?
2. Can execution panic and unwind through this frame?
3. Can execution terminate the process or hit UB?
4. Can execution continue forever without terminating?

A `!` return type directly addresses only the first. MIR and Charon provide additional outcome information, but Charon's transformations can deliberately collapse unwind detail. A total-correctness claim, a panic-freedom claim, and a partial-correctness claim therefore require different evidence.

Basis: **derived** from the normative and source distinctions above.

## Boundaries

- No fresh rustc invocation, MIR dump, Charon extraction, runtime panic, or unwind experiment was performed.
- The report does not provide a full semantics of Rust exceptions, panic payloads, hooks, thread boundaries, or foreign exceptions.
- FFI is covered only far enough to establish that unwind permission is an ABI-sensitive semantic boundary.
- The report does not claim `panic=abort` and an explicit process-abort API are interchangeable in every observable respect. It establishes that the abort panic strategy does not perform ordinary Rust stack unwinding.
- The report does not characterize asynchronous cancellation, coroutine destruction, signals, `longjmp`, process exit, or OS termination semantics.
- Infinite execution is characterized at the language/control-flow level. No fairness, liveness, resource-consumption, or scheduler model is supplied.
- A MIR CFG cycle is not by itself proof of nontermination; control flow may leave the cycle. The report therefore does not infer semantic nontermination from arbitrary cycles.
- `Call { target: None }` establishes absence of a normal return edge in the MIR representation; it does not by itself prove why the callee cannot return.
- The report does not prove semantic correctness of rustc's panic lowering, Charon's translation, or Charon's reconstructed fallible-operation semantics.
- Charon's recognized panic translation loses the call's explicit MIR unwind edge. This report does not establish how a later Aeneas backend reconstructs or approximates that lost cleanup behavior.
- Checked-in `.out` files are preserved upstream artifacts, not fresh execution from this report.
- No Anneal result taxonomy or proof architecture is selected.

## Evidence

**Normative Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`:

- `src/panic.md`: panic handlers, panic strategy, unwind cleanup, recoverability, and FFI unwind restrictions.
- `src/divergence.md`: diverging expressions as expressions that never complete normal execution.
- `src/types/never.md`: `!` has no values and identifies functions that never return normally.
- `src/expressions/loop-expr.md`: infinite `loop` without associated `break` is diverging.
- `src/behavior-considered-undefined.md`: invalid `!` values and UB from unwinding across a non-unwinding boundary.

**Rust compiler source.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:

- `compiler/rustc_middle/src/mir/syntax.rs`: `TerminatorKind::{Return, UnwindResume, UnwindTerminate, Unreachable, Call, Assert}`, `UnwindAction`, and `UnwindTerminateReason`.
- `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`: required abort/unwind rewrite based on target support, callee unwind capability, enclosing ABI, and panic strategy.
- `library/std/src/panic.rs`: `catch_unwind` catches unwinding panics but not aborting panics; foreign unwind caveats.

**Charon source.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/src/ast/gast.rs`: `AbortKind::{Panic, UndefinedBehavior, UnwindTerminate}`.
- `charon/src/ast/ullbc_ast.rs`: ULLBC call/unwind/abort/return terminators.
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`: rustc terminator translation, recognized panic calls, synthetic UB continuation for calls with no normal target.
- `charon/src/transform/resugar/reconstruct_fallible_operations.rs`: removal of recognized runtime checks in favor of verifier-side fallible operation semantics.

**Preserved Charon artifacts.** Same Charon revision:

- `charon/tests/ui/panics.rs` with `charon/tests/ui/panics.out`.
- `charon/tests/ui/diverging.rs` with `charon/tests/ui/diverging.out`.
- `charon/tests/ui/simple/catch-unwind.rs` with `charon/tests/ui/simple/catch-unwind.out`.

No evidence in this report is fresh **execution**. The checked-in output files pre-existed at the pinned commit.

## Revalidation

For a later Rust/Charon pin, first diff the narrow source surfaces above. Confirm the Rust Reference's panic/divergence rules, rustc's MIR terminators and `UnwindAction`, and `AbortUnwindingCalls`. Then inspect Charon's `AbortKind`, rustc terminator translation, recognized-panic special case, and fallible-operation reconstruction.

On an execution-capable surface, use one minimal crate containing: a normal-return function, `loop {}`, an explicit `panic!`, a failing `assert!`, a call to a `fn() -> !`, a destructor with an observable side effect, and an unwind-permitting versus non-unwinding ABI boundary. Dump MIR under both `-C panic=unwind` and `-C panic=abort`, then extract with the exact paired Charon revision. Preserve commands, target triple, MIR phase, LLBC, stderr, exit status, revisions, and hashes.

That probe should check three discriminators: whether cleanup/drop edges differ between panic strategies; how no-normal-return calls are represented; and which panic/unwind distinctions survive into LLBC. It establishes those concrete representations at that exact toolchain. It does not by itself prove end-to-end Rust semantic adequacy or total-correctness reasoning.
