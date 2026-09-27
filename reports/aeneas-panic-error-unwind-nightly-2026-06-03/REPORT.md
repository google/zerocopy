# Aeneas panic, failure, and unwind representation at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, ordinary Rust failure is translated into the pure `Result` monad rather than a Rust unwinding semantics. A generated Lean function can return `ok v`, `fail e`, or—when partial-function machinery is involved—`div`. The Lean support library distinguishes several `Error` tags, including `panic`, assertion failure, overflow, division by zero, and out-of-bounds, but those tags are not a lossless encoding of Rust failure causes.

The most important loss happens before the final Lean output. The paired Charon revision preserves `UnwindResume` in ULLBC, but ULLBC→LLBC restructuring turns it into `Abort(Panic(None))`; ordinary call unwind edges are ignored by that conversion. Aeneas then treats every LLBC `Abort` kind alike: `Panic`, `UndefinedBehavior`, and `UnwindTerminate` all enter the same symbolic panic path. That path becomes a generic pure failure and, for Lean, `fail panic`. Aeneas therefore cannot reconstruct Rust cleanup edges, `catch_unwind`-style recovery behavior, or even the distinction between Charon's UB/termination/panic abort categories from its ordinary LLBC input.

Failure tags can be simplified further. Checked-in generated Lean shows a direct panic path as `fail panic`, but a conditional `panic!()` can become `massert`; `massert` fails with `assertionFailure`. The pure micro-pass explicitly rewrites `if b then e else fail panic` into `massert b; e`. The semantically stable fact for ordinary Aeneas proofs is therefore usually “this path fails,” not the exact `Error` constructor that explains why.

Aeneas's standard weakest-precondition interface reflects that abstraction. `spec (fail e) p` is false for every error `e`, just as `spec div p` is false. Proving an ordinary generated specification therefore rules out modeled failure and divergence on the proved inputs, but it does not prove the detailed Rust panic/unwind behavior that was already erased upstream.

No fresh Charon, Aeneas, Lean, or Rust execution was performed. The report uses exact pinned source and checked-in generated Lean artifacts.

## Applicability

The primary subject is Aeneas release `nightly-2026.06.03`, commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`, selected by Anneal. Its relevant input producer is Charon `0.1.210`, commit `a535e914f74db4fd9e6be7048f4233270d8945c0`.

This report follows the ordinary Charon LLBC → Aeneas symbolic execution → pure AST → Lean extraction path. It describes what that path retains about failure and what it loses about Rust unwind control flow. It does not claim that Rust panics, UB, abort, and divergence are semantically equivalent; the companion corpus report `rust-panic-unwind-abort-divergence-nightly-2026-05-31` establishes that they are not.

The report also does not treat the generated `Error` tag as a Rust exception type. Aeneas uses the tag inside its pure result model, and transformation passes may change which tag a syntactically equivalent failure uses while preserving the success/failure behavior relevant to ordinary WP proofs.

## Findings

### Charon erases ordinary unwind edges before Aeneas sees LLBC

The paired Charon revision has a distinct ULLBC `UnwindResume` terminator. During ULLBC→LLBC restructuring, however, `UnwindResume` becomes `Abort(AbortKind::Panic(None))`. The same conversion handles a normal call's `on_unwind` field as `_` and carries only the normal target, with the source TODO `Have unwinds in the LLBC`.

Assertions retain only a summarized failure kind. The converter reads the assertion's unwind block and records its `AbortKind`; if the block does not reduce to an abort, it defaults the failure kind to `Panic(None)`. The structured LLBC statement language itself has `Assert { ... on_failure: AbortKind }`, `Call`, `Abort(AbortKind)`, and `Return`, but no `UnwindResume` statement.

Consequently, Aeneas's normal structured input does not contain the original Rust cleanup graph. A downstream proof cannot recover which destructors ran on an unwind path or where a panic could have been caught from this LLBC alone.

Basis: pinned Charon **source** + **derived** consequence.

### Aeneas collapses all LLBC abort kinds into one symbolic panic outcome

The pinned Aeneas statement interpreter matches `Abort _` without inspecting the `AbortKind`. In concrete mode it returns its internal `Panic` evaluation result. In symbolic mode it stops that execution branch and synthesizes `SA.Panic`.

This is broader than Rust `panic!()`. At the paired Charon revision, `AbortKind` also represents `UndefinedBehavior` and `UnwindTerminate`. Because Aeneas ignores the kind at this boundary, the functional translation does not preserve Charon's distinction among panic, UB, and unwind termination.

Assertions follow the same failure channel. A concrete false assertion evaluates to `Panic`; a symbolic assertion continues down the success branch while synthesizing an assertion node whose failing alternative becomes pure failure later.

Basis: pinned Aeneas **source** + paired Charon **source** + **derived** distinction.

### The pure translation turns the symbolic panic channel into `Result.fail`

`SymbolicToPure.translate_fun_decl_body` installs a `mk_panic` callback. That callback builds `Result.fail` with the pure AST's `error_failure_id`. The Lean extractor maps this failure ID to the Lean constructor name `panic`.

Normal return from a function whose effect information says it can fail is wrapped in `Result.ok`. For ordinary non-global, non-builtin functions at this revision, `FunsAnalysis` deliberately forces `can_fail = true` even if its syntactic/transitive analysis found no failure. Its comment says the analysis is not yet used to remove the error monad from ordinary extracted functions. Thus a generated `Result` type is not itself evidence that the Rust body contains a possible panic.

The same analysis nevertheless records actual failure propagation: assertions and panic nodes set `can_fail`, fallible unary/binary operations do so, and calls propagate callee failure information. Those facts matter for analyses and special cases, even though ordinary functions currently remain result-valued regardless.

Basis: pinned Aeneas **source**.

### Lean's result model has failure categories, but they are not a faithful Rust panic taxonomy

The pinned Lean primitives define:

- `Result.ok v` for success;
- `Result.fail e` for modeled failure; and
- `Result.div` for modeled divergence.

`Error` includes `assertionFailure`, `integerOverflow`, `divisionByZero`, `arrayOutOfBounds`, `maximumSizeExceeded`, `panic`, and `undef`. For example, `massert b` yields `ok ()` when `b` holds and `fail assertionFailure` otherwise.

Those constructors are useful inside the pure model, but source-to-source preservation of the exact tag is not guaranteed. The pure `intro_massert` pass explicitly rewrites a conditional with a `fail panic` branch into an `massert`. The checked-in `NoNestedBorrows.lean` artifact demonstrates both shapes at the pinned revision: `panic_mut_borrow` is generated as `fail panic`, while `test_panic` and `test_panic_msg` are generated as `massert (¬ b)`.

The durable interpretation is therefore that both paths can fail. Code that depends on whether the final error tag is `panic` versus `assertionFailure` needs a narrower source/codegen claim and should not infer that distinction from the original Rust panic form alone.

Basis: pinned Aeneas **source** + checked-in generated **execution** artifact.

### Generated pattern-match and recursive examples expose `fail panic` directly

The pinned generated `NoNestedBorrows.lean` contains several direct witnesses. `split_list` maps the `List.Nil` branch to `fail panic`. `list_nth_shared` does the same for an out-of-range traversal that reaches `Nil`, while successful branches return through `ok`. `panic_mut_borrow` is simply `fail panic` despite taking and returning mutable-state information in the Rust source.

These artifacts show that panic is an ordinary value in the generated pure control-flow model; it is not represented by Lean's own exception mechanism or process failure.

Basis: checked-in generated **execution** artifact + pinned **source**.

### Ordinary WP specifications reject every modeled failure, independent of its tag

The pinned `Aeneas.Std.WP` defines `spec` over the pure `Result`. Its simplification theorems establish `spec (ok x) p ↔ p x`, `spec (fail e) p ↔ False`, and `spec div p ↔ False`.

For the ordinary success-oriented specification used by generated proofs, the exact `Error` tag therefore disappears from the proof obligation: any `fail e` falsifies the specification. A completed `spec` proof for a selected input can establish that the modeled execution reaches `ok` rather than `fail` or `div`.

That result is narrower than Rust panic/unwind correctness. It does not restore dropped cleanup edges or distinguish a panic from an LLBC abort that Aeneas had already collapsed into the same symbolic panic channel.

Basis: pinned Aeneas Lean **source** + **derived** proof boundary.

## Boundaries

- **Known not to apply:** this model is not a faithful encoding of Rust stack unwinding. Charon's LLBC conversion has already discarded ordinary call unwind edges and rewritten unwind-resume before Aeneas's functional interpreter runs.
- **Known not to preserve:** Aeneas's functional translation does not preserve Charon `AbortKind` distinctions at the statement-interpreter boundary. In particular, a Charon `UndefinedBehavior` abort and a panic abort enter the same Aeneas symbolic panic path.
- **Not an error-tag guarantee:** generated `Error` constructors should not be treated as a stable one-to-one provenance record for Rust failure causes. The `intro_massert` rewrite gives a concrete counterexample.
- **Not examined:** this report does not characterize a separate operational model for Rust `catch_unwind`, foreign-exception boundaries, platform unwinding ABIs, or destructor execution during unwind. The ordinary LLBC path lacks enough unwind structure to infer those behaviors.
- **Not fresh execution:** no new Rust→Charon→Aeneas run was performed on this surface. Checked-in generated Lean is historical execution evidence from the pinned repository.
- **Separate subject:** nontermination and partial-function machinery are covered by separate durable work in this corpus. `Result.div` is included here only to distinguish failure from divergence in the proof interface.

## Evidence

Observed 2026-09-26.

Primary Aeneas source, all at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `src/llbc/FunsAnalysis.ml`, especially the `visit_Assert`, `visit_Panic`, call propagation, and final `can_fail` forcing logic: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/llbc/FunsAnalysis.ml>
- `src/interp/InterpStatements.ml`, especially `eval_assertion` and `eval_statement`'s `Abort _` case: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/interp/InterpStatements.ml>
- `src/symbolic/SymbolicToPure.ml`, `translate_fun_decl_body` and `mk_panic`: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/symbolic/SymbolicToPure.ml>
- `src/pure/Pure.ml`, built-in result/error IDs: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/pure/Pure.ml>
- `src/extract/ExtractBase.ml`, Lean mapping of `error_failure_id` to `panic`: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/extract/ExtractBase.ml>
- `src/pure/PureMicroPassesGeneral.ml`, `intro_massert_visitor`: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/src/pure/PureMicroPassesGeneral.ml>
- `backends/lean/Aeneas/Std/Primitives.lean`, `Error`, `Result`, and `massert`: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/Aeneas/Std/Primitives.lean>
- `backends/lean/Aeneas/Std/WP.lean`, `spec`, `spec_ok`, `spec_fail`, and `spec_div`: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/Aeneas/Std/WP.lean>
- checked-in generated `tests/lean/NoNestedBorrows.lean`, including `test_panic`, `test_panic_msg`, `split_list`, `panic_mut_borrow`, and `list_nth_shared`: <https://github.com/AeneasVerif/aeneas/blob/ac9f1bc5262a5e4ff1e24ca78617121382202727/tests/lean/NoNestedBorrows.lean>

Paired Charon source, all at `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/src/ast/llbc_ast.rs`, structured LLBC statement kinds: <https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/ast/llbc_ast.rs>
- `charon/src/transform/control_flow/ullbc_to_llbc.rs`, especially the `UnwindResume`, `Call`, and `Assert` conversion: <https://github.com/AeneasVerif/charon/blob/a535e914f74db4fd9e6be7048f4233270d8945c0/charon/src/transform/control_flow/ullbc_to_llbc.rs>

Existing corpus context: `rust-panic-unwind-abort-divergence-nightly-2026-05-31` records the upstream Rust/rustc and Charon distinctions before this Aeneas-specific collapse; `aeneas-rust-to-lean-translation-nightly-2026-06-03` records the general function/result translation.

## Revalidation

For a newer Aeneas/Charon pair, the cheapest discriminators are source-local:

1. inspect Charon's structured LLBC statement enum and `ullbc_to_llbc` handling of `UnwindResume`, call unwind edges, and assertion unwind blocks;
2. inspect Aeneas `InterpStatements.eval_statement` for whether it still matches `Abort _` without the kind;
3. inspect `SymbolicToPure.translate_fun_decl_body` for the panic callback and the Lean extraction mapping of its error ID;
4. inspect `Primitives.lean` and `WP.lean` for `Result`, `Error`, `massert`, and `spec_fail`/`spec_div`; and
5. regenerate or diff the tiny `test_panic`, `panic_mut_borrow`, and `split_list` fixtures to detect changes in direct panic versus `massert` output.

If any of those points changes, re-evaluate the end-to-end distinction among Rust panic, unwind cleanup, Charon abort kinds, Aeneas failure, and Lean proof obligations. A generated fixture alone cannot establish unwind fidelity; that requires checking the upstream control-flow representation as well.