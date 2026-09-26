# Rust const evaluation and const functions at nightly-2026-05-31

## Summary

At the Rust compiler revision behind Anneal-era nightly-2026-05-31, `const fn` does not mean “this function always runs at compile time.” It means the function is eligible to be called in a const context. A call from a const context is interpreted by the compiler during compilation, using the compilation target's environment. The same `const fn` called outside a const context behaves like the same function without the `const` qualifier and executes normally at runtime unless ordinary optimization happens to fold it.

Required constant evaluation is therefore a distinct execution mode with additional admissibility and evaluation rules. Const contexts must contain constant expressions; failures encountered while a required const value is being computed are compile-time errors. Outside const contexts, syntactically constant expressions may be evaluated early, but that is not guaranteed.

The pinned compiler implements required CTFE with a MIR interpreter using `mir_for_ctfe` and a `CompileTimeMachine`. The machine rejects calls to functions that are not const-eligible, enforces CTFE-specific memory restrictions, reports a panic as a const-evaluation error, and does not support unwinding during const evaluation. It also has CTFE-specific intrinsics and hooks. Thus a verifier should not identify “Rust runtime execution” with “rustc CTFE execution” merely because both start from Rust source or MIR.

The unstable `const_eval_select` intrinsic makes the distinction explicit by permitting separate compile-time and runtime implementations. Its own documentation requires equivalent end-to-end behavior when reachable from stable code, but the implementations can differ. That is a compatibility obligation, not evidence that CTFE and runtime follow identical internal paths.

No fresh rustc or CTFE execution was performed.

## Applicability

Primary compiler subject:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
- toolchain date: nightly-2026-05-31

Normative language source:

- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`

The report covers the language-level meaning of const contexts and const functions, together with the pinned compiler's CTFE implementation boundary. It does not infer behavior for adjacent compiler revisions.

## Findings

### Const contexts require compile-time evaluation

The Rust Reference defines constant evaluation as computing expression results during compilation. Expressions in const contexts must be constant expressions and are always evaluated at compile time.

Const contexts include array lengths, repeat lengths, constant and static initializers, enum discriminants, const generic arguments, and explicit const blocks.

Outside those contexts, an expression that is eligible for constant evaluation may be evaluated at compile time, but the language does not guarantee that it will be.

Basis: **normative**.

### A const function is callable in const contexts; it is not permanently a compile-time function

The Reference defines a const function as a function that can be called from a const context. When called there, rustc interprets it at compile time.

When the same function is called outside a const context, the Reference says it behaves as though it did not have the `const` qualifier.

This is the central distinction for verification. `const fn` adds a permitted execution mode; it does not replace the function's ordinary runtime meaning.

Basis: **normative**.

### CTFE uses the compilation target's environment

The Reference specifies that a const function evaluated during compilation is interpreted in the environment of the compilation target rather than the build host. It gives target pointer width as an example: `usize` follows the target.

A CTFE result therefore belongs to the selected target configuration. Host properties should not be substituted for target properties when reasoning about a constant value.

Basis: **normative**.

### Required CTFE turns evaluation failures into compilation failures

The Reference states that behaviors such as out-of-bounds indexing or arithmetic overflow are compiler errors when the value must be evaluated in a const context. Outside a const context, the same source shape is not necessarily evaluated during compilation and may instead fail when executed at runtime.

Thus “the compiler accepted this expression syntactically” and “the compiler successfully evaluated this const” are separate claims.

Basis: **normative**.

### Const evaluation permits only a restricted expression and operation set

The Reference enumerates the expression forms permitted in constant expressions. The set includes control flow, loops, const-function calls, dereferences under specified rules, and many ordinary operators, but remains a subset of unrestricted Rust execution.

Const functions are themselves restricted: their bodies may use only constant expressions, they may not be async, and their parameter and return types must be compatible with const contexts.

The exact permitted subset is version-sensitive. A verifier should bind any CTFE claim to the compiler revision rather than treating “const Rust” as a timeless fixed language.

Basis: **normative**.

### The pinned compiler runs CTFE through a dedicated MIR interpreter

The const-evaluation query path ultimately enters `eval_in_interpreter`, constructs an `InterpCx` using `CompileTimeMachine`, and evaluates the selected `GlobalId`. The machine loads function bodies using `mir_for_ctfe` for ordinary items.

This is not the same implementation path as native code generation and execution. CTFE is an interpreter over compiler MIR with an explicit machine policy.

Basis: **source**.

### The CTFE machine applies execution-mode-specific restrictions

`CompileTimeMachine` tracks whether mutable global memory may be accessed and whether alignment must be checked. The const-evaluation query enables mutable-global access for static initializers but deliberately rejects it for ordinary const values so that consts retain the required value semantics.

The source comment describes ordinary const evaluation as needing to behave “as if” evaluated at runtime while still imposing CTFE restrictions that preserve const semantics.

This distinction matters: CTFE is intended to model allowed constant computation, not to expose every runtime capability.

Basis: **source**.

### Calls during CTFE must be const-eligible

When the interpreter resolves a function call, it rejects an ordinary function that is not a const function, except for compiler-controlled special cases such as const-trait machinery. A const-eligible function is then interpreted through its MIR.

This enforcement is separate from ordinary runtime calling. The same source function may be callable at runtime even when rustc would reject calling it from a const context.

Basis: **source**.

### Panic during required CTFE is an evaluation error, not stack unwinding

The CTFE machine's call interface explicitly notes that unwinding is not supported in const evaluation. Its panic hook constructs a const-evaluation panic error containing the message and source location.

This is a concrete example of execution-mode divergence. Runtime Rust can use an unwinding panic strategy, while required CTFE does not model that panic as a recoverable stack unwind through const frames.

Basis: **source**.

### The unstable const/runtime selection intrinsic proves that implementation paths can differ

The pinned core library exposes the unstable intrinsic `const_eval_select`. It accepts one function to call during const evaluation and another for runtime execution.

Its documentation says Rust has not stabilized the ability for ordinary const functions to observe whether they are running at compile time. For stable-facing uses, the two implementations must therefore preserve equivalent end-to-end behavior even though their code can differ.

This is an important limit on a common inference: equal language-level behavior does not imply identical implementation or intermediate semantics between CTFE and runtime.

Basis: **source** + **documentation**.

### Const evaluation is not a substitute for runtime verification

A successful compile-time evaluation establishes the result for that required const computation under the selected target and CTFE rules. It does not by itself show that every runtime call of the same const function takes the same compiler path, performs no runtime effects, or is evaluated during compilation.

Conversely, reasoning only about runtime execution can miss compile-time rejection or CTFE-specific restrictions that determine whether a program is accepted.

For Anneal-style verification, CTFE and runtime should therefore be treated as related but distinct execution modes whenever the verified claim depends on when evaluation occurs.

Basis: **derived** from the normative and source distinctions above.

## Boundaries

- No fresh rustc invocation, CTFE probe, MIR dump, or runtime execution was performed.
- This report does not inventory every constant-expression restriction at the pinned revision; it records the governing model and the restrictions most relevant to execution-mode reasoning.
- It does not characterize compile-time evaluation performed only as an optimizer choice outside a required const context.
- It does not prove semantic equivalence between rustc CTFE and generated runtime machine code.
- It does not claim that every compiler optimization of a runtime expression uses the CTFE interpreter.
- It does not characterize all CTFE intrinsics, allocation rules, provenance rules, or interpreter diagnostics.
- `const_eval_select` is unstable. Its presence demonstrates a compiler-supported split between const and runtime implementations; this report does not claim stable Rust exposes that split as a general programming model.
- Static initialization has different mutable-global-access rules from ordinary const values and is not exhaustively analyzed here.
- Generic const expressions and their solver behavior are outside this report.
- No Anneal architecture or proof boundary is selected.

## Evidence

**Normative Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/const_eval.md`, blob `c06b343b041ee7c596cfa34385d62d25358ee7e6`: constant expressions, const contexts, mandatory versus optional compile-time evaluation, and const-function semantics.

**Compiler source.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_const_eval/src/const_eval/eval_queries.rs`, blob `62ec0d2ef8bf49bc37098d1a49a3a7bc89168781`: const-evaluation query path and construction of the compile-time interpreter.
- `compiler/rustc_const_eval/src/const_eval/machine.rs`, blob `1dee2f34371e8fe41e732b742a06ab96e975e77e`: `CompileTimeMachine`, CTFE MIR loading, const-call checks, panic handling, memory-access policy, and interpreter hooks.
- `library/core/src/intrinsics/mod.rs`, blob `78d7314c58110b49839894a0f69377f4ee0d1204`: `const_eval_select` and its const/runtime equivalence contract.

No evidence above is fresh **execution**.

## Revalidation

For another compiler revision, first diff:

1. the const-context and const-function sections of `reference/src/const_eval.md`;
2. `rustc_const_eval::const_eval::eval_queries`;
3. `CompileTimeMachine::load_mir`, function-call handling, panic handling, and global-memory policy;
4. the `const_eval_select` intrinsic contract.

On an execution-capable surface, use one small crate containing the same `const fn` in four situations: a required const initializer, a const block, an ordinary runtime call, and a `const_eval_select`-backed standard-library-style helper. Include a target-width-dependent computation and a deliberately failing required const expression. Record compiler diagnostics, MIR used for CTFE, and runtime output for at least two target configurations when practical. The probe establishes behavior for those inputs and targets; it does not prove equivalence of CTFE and runtime for arbitrary Rust.
