# Aeneas infinite and diverging execution at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`), Aeneas has a real semantic representation for divergence in generated Lean, but it does not support every Rust source form that can diverge.

Recursive translated functions use Lean's `partial_fixpoint`; Aeneas's `Result α` has a distinct `div` value that is the bottom element of the partial order used by that fixed-point construction. Divergence is discovered conservatively by source analysis: direct or mutual recursion, any loop, or a call to an already-known diverging function sets `can_diverge`. A nonrecursive caller of a recursive translated function can therefore propagate the callee's `div` result without itself becoming a recursive Lean definition.

The important source-language boundary is unconditional loops. During symbolic loop interpretation, Aeneas computes the loop's break context and rejects `NoBreak` with the explicit error `(Infinite) loops which do not contain breaks are not supported yet`. Thus a Rust `loop { ... }` that has no break path is not translated into a Lean computation whose result is simply `div`; at this pin it is an unsupported translation case. Loops with a break path can be lowered to generated recursive helpers, which may themselves denote divergence through `partial_fixpoint` if an execution continues forever.

For Anneal, these are different claims: Aeneas can model nontermination of supported partial recursive computations, and proofs using the standard `WP.spec` can rule out `div` for covered inputs; but Aeneas does not provide complete source-level coverage of all infinite Rust executions. No fresh Aeneas execution was performed for this report.

## Applicability

This report applies to Aeneas revision `ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`, and primarily to its Lean backend as selected by current Anneal.

It complements the existing `aeneas-partial-functions-nightly-2026-06-03` and `aeneas-recursion-termination-nightly-2026-06-03` reports. Those reports establish the `partial_fixpoint`/`Result.div` model and the proof-level termination boundary. This report specializes the broader #3720 question: which potentially infinite executions are represented, which are rejected, and where the effect analysis is intentionally conservative or incomplete.

The paired Charon revision is `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`). This report starts from the structured LLBC consumed by Aeneas and does not independently characterize which Rust source forms Charon accepts.

## Findings

### Aeneas explicitly tracks whether a function may diverge

`src/llbc/FunsAnalysis.ml` computes `can_diverge` for each function declaration group. Its documented rule is that a function may diverge if it is recursive, contains a loop, or calls a function that can diverge.

The implementation follows that rule for ordinary statically resolved calls. A call to another function in the current recursive group sets both `can_diverge` and `is_rec`. A call to an already analyzed regular function propagates the callee's `can_diverge`. Encountering any loop sets `can_diverge` immediately.

A mutually recursive declaration group receives one shared effect summary, so if the group contains recursive calls, every member carries the same divergence classification.

Basis: **source**.

### Trait-method divergence is not propagated by this analysis

The same regular-call visitor gives trait methods special treatment: it assumes they can fail but cannot diverge and are not stateful. The source has a TODO noting that this can cause issues when fuel is used.

This means `can_diverge` is not a complete semantic oracle for all possible dynamic/trait dispatch behavior at this revision. That limitation is less visible in the ordinary Lean path because Lean rejects Aeneas's fuel mode and an actual call to a generated partial function can still return `div`. It is nevertheless a boundary on interpreting the analysis flag as a proof that a function cannot diverge.

Basis: **source**.

### Recursive generated Lean definitions represent divergence through `partial_fixpoint`

The Lean extractor maps every recursive declaration kind to the post-qualifier `partial_fixpoint`. Aeneas's Lean `Result α` type has three outcomes: success, failure, and `div`; its partial-order/CCPO instances use `div` as the bottom element, and monadic bind propagates divergence.

The checked-in `BaseTutorial.lean` makes the intended semantics explicit with `i32_id`: on nonnegative inputs the function reaches zero, while on negative inputs it can recurse indefinitely. The definition is a `partial_fixpoint`, not a total recursive definition accepted by a termination proof.

The resulting semantic model distinguishes divergence from failure. A panic-like path is `fail e`; a nonterminating partial computation is `div`.

Basis: pinned Aeneas **source** + checked-in tutorial **source artifact**.

### A caller can diverge without being syntactically recursive

Because Aeneas propagates `can_diverge` through ordinary calls, a nonrecursive Rust function can be classified as potentially diverging when it invokes a partial callee. Its generated Lean body need not itself be a `partial_fixpoint`: it can simply call the callee and propagate the result through the monadic operations.

If the callee denotes `div`, `Result.bind` propagates `div` rather than invoking the continuation. Divergence therefore composes through ordinary translated calls; `partial_fixpoint` is needed at the recursive fixed-point boundary, not at every transitive caller.

Basis: **source** plus **derived** consequence of the effect analysis and `Result.bind` semantics.

### Loops with possible exits are treated as potentially divergent

Every LLBC loop sets `can_diverge`, regardless of whether a later proof can establish that the loop exits. Symbolic loop translation computes a fixed point at the loop entrance and a context for the break paths. Supported loops are then synthesized into the pure representation and can be transformed into generated recursive loop helpers.

Those helpers use the same recursive extraction machinery as other translated recursion. An execution that keeps taking the continue path can therefore remain semantically partial even when the source loop has a syntactic break path somewhere else.

This conservative treatment is appropriate for a source-level loop whose exit depends on runtime state: existence of a break edge is not a proof that every execution reaches it.

Basis: **source**.

### A loop with no break path is rejected rather than modeled as `div`

The sharper boundary appears in `src/interp/InterpLoops.ml`. During symbolic loop interpretation, Aeneas calls `compute_loop_break_context`. If the result is `NoBreak`, translation raises the explicit error:

`(Infinite) loops which do not contain breaks are not supported yet`

This is not merely a proof limitation. The symbolic translation stops instead of constructing a pure loop whose semantics is unconditional divergence.

A syntactically infinite Rust loop such as `loop { continue; }` therefore cannot be assumed to translate to `Result.div` at this revision. The general partial-function machinery demonstrates that Aeneas has a semantic bottom for nontermination, but the loop interpreter does not route this unsupported source shape into that bottom.

Basis: **source**.

### Concrete-mode loop interpretation can itself run indefinitely

The concrete loop interpreter is structurally different from symbolic translation. For `Continue 0`, it reevaluates the current loop body and recursively processes the next result, with a comment noting that this can repeat an indefinite number of times.

A genuinely nonterminating concrete-mode loop can therefore cause the Aeneas interpreter itself not to return. This path is used for Aeneas's concrete testing facilities, not for constructing the Lean translation, and should not be confused with the generated `Result.div` semantics.

Basis: **source**.

### Lean fuel mode is not an available escape hatch

Aeneas has generic `-use-fuel` machinery: when enabled, functions classified `can_diverge` can receive a fuel parameter, and exhausting fuel can represent bounded approximation of divergence. The CLI describes the option as using fuel to control divergence.

At this pinned revision, however, `src/Main.ml` explicitly rejects `-use-fuel` for the Lean backend. Anneal therefore cannot rely on fuel to make unsupported infinite Lean translations executable or to convert source-level infinite loops into bounded Lean functions.

The ordinary Lean choices are the partial fixed-point path for supported recursive translations and optional decreases clauses for selected recursive definitions. Decreases clauses concern proving termination; they do not add support for a `NoBreak` loop that the symbolic loop interpreter rejects before extraction.

Basis: **source**.

### Standard `WP.spec` proofs exclude divergence for the invocation proved

Aeneas's Lean WP layer treats both failure and divergence as specification failure. `spec div P` is false, and the library gives an equivalence between `spec m P` and existence of an `ok` result satisfying `P`.

Consequently, after a supported partial computation has been translated, a proof of its ordinary Aeneas specification establishes termination and successful completion for the inputs covered by the theorem. This does not make the generated function total, and it does not say anything about a source construct that failed translation in the first place.

Basis: pinned Aeneas Lean **source**.

## Boundaries

- No fresh Aeneas, Charon, or Lean execution was performed.
- This report does not claim complete Rust nontermination semantics. In particular, source-level loops without break paths are explicitly unsupported at the pinned Aeneas revision.
- `can_diverge = false` is not a semantic proof of termination. Trait-method calls are one documented hole in the propagation logic, and external/model behavior has separate authority in the corpus.
- Concrete interpreter nontermination and generated Lean `Result.div` are different mechanisms. The former can hang the translating/test process; the latter is a value in the semantic model used for supported partial definitions.
- The dedicated loops report remains the authority for complete loop lowering, inputs/outputs, fixed-point contexts, and generated helper shape. This report uses loop internals only to establish the divergence boundary.
- The dedicated recursion/termination and partial-function reports remain the authority for Lean's `partial_fixpoint`, CCPO construction, and proof workflow. This report records only the parts needed to connect those mechanisms to the infinite-execution question.
- No claim is made that Aeneas preserves every distinction among Rust divergence, process abort, panic, undefined behavior, blocking I/O, concurrency deadlock, or externally modeled nonreturning calls. Failure/unwind and semantic-omission subjects cover adjacent boundaries.

## Evidence

**Aeneas subject:** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`). Revalidated 2026-09-27.

Primary pinned source:

- `src/llbc/FunsAnalysis.ml`, blob `a2678ba12e8baaaf14fc99c3f061b10edae2da86`: definition and propagation of `can_diverge`; recursion, loops, transitive calls, and the trait-method limitation.
- `src/interp/InterpLoops.ml`, blob `94630c8c9052e326782cc6f71b1f346df451f3e5`: concrete indefinite reevaluation and symbolic rejection of `NoBreak` loops.
- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`: recursive Lean declaration kinds map to `partial_fixpoint`.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: emission of recursive post-qualifiers.
- `backends/lean/Aeneas/Std/Primitives.lean`, blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`: `Result.ok`, `Result.fail`, `Result.div`, bind propagation, and the flat partial order/CCPO support.
- `backends/lean/Aeneas/Std/WP.lean`, blob `018c456bcab5374de0b09b17eda0df1a48e2288b`: `spec` rejects divergence and failure.
- `src/pure/PureMicroPassesGeneral.ml`, blob `32d37b2363a69b9cf8a765b6446deb753aadc27b`: generic fuel insertion conditioned on `can_diverge`.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: `-use-fuel` CLI semantics and explicit rejection of fuel for Lean.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: divergence/fuel configuration.
- `tests/lean/BaseTutorial.lean`, blob `52a9947feab2f607729e23c10dfc9e12bba02d41`: checked-in partial recursive example and explicit explanation of `div`.

Related current reference reports:

- `reports/aeneas-partial-functions-nightly-2026-06-03/REPORT.md`, blob `0e26ea4d4efb818f7d6cd037dd35bf9fd12b4df3`: detailed `partial_fixpoint` / `Result.div` semantics and proof boundary.
- `reports/aeneas-recursion-termination-nightly-2026-06-03/REPORT.md`, blob `b220c5537bff84096b0f2d00972576f9f4eb4507`: recursion classification, termination proof behavior, and optional decreases/fuel mechanisms.
- `reports/aeneas-panic-error-unwind-nightly-2026-06-03/REPORT.md`, blob `aa7a1b6a7db80d9037bce35882b33beea219b9e0`: distinction between modeled failure and divergence.

There is no fresh **execution** evidence in this package.

## Revalidation

For a future Aeneas revision, first inspect `FunsAnalysis.ml` for the exact sources and propagation rules of `can_diverge`. Then inspect `InterpLoops.ml` around `compute_loop_break_context`: the decisive compatibility question is whether `NoBreak` still raises an unsupported-loop error or is lowered to an explicit divergent semantic computation.

Also revalidate `ExtractBase.ml`, `Primitives.lean`, and `WP.lean` so that recursive partial definitions still use a bottom/divergence model and success specifications still exclude it. If Lean fuel support becomes available, inspect both the fuel insertion pass and generated Lean rather than assuming the generic fuel implementation applies unchanged.

On an execution-capable surface, use a narrow matrix:

1. a self-recursive function that diverges on a subset of inputs;
2. a nonrecursive function that calls that partial function;
3. a loop with a reachable break and an input for which execution can continue forever; and
4. an unconditional `loop {}` / no-break loop.

Preserve Rust, LLBC, generated Lean or translation error, stderr, and exact revisions. For supported cases, prove one terminating-input `WP.spec` theorem and inspect the generated `partial_fixpoint` structure. For the unconditional loop, determine whether the source-level `NoBreak` rejection remains the actual observable behavior. This matrix distinguishes semantic divergence of supported translations from unsupported infinite source shapes.
