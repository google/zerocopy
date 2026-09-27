# Anneal V1 `isValid`: known-unsound boundary checks, not a global type invariant

## Summary

Historical Anneal V1 does **not** provide a sound global `isValid` type-invariant mechanism at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. The implementation says so directly: an explicit `isValid` annotation is rejected unless the user passes `--unsound-allow-is-valid`.

With that opt-in enabled, `isValid` still has a useful but narrower meaning. Anneal generates validity proof obligations at selected **Anneal-annotated function boundaries**: for function inputs, non-unit returns, and the post-state of direct `&mut` arguments. That is local contract checking. It is not enough to maintain a Rust type invariant globally, because ordinary safe, unannotated Rust can construct or mutate invariant-carrying fields without crossing an Anneal verification boundary.

There is a second independent hole. `Anneal.IsValid` has a low-priority generic fallback whose predicate is `True`. The current V1 standard library has no recursive `IsValid` instances for `Option` or product types. Therefore wrapping a type with a nontrivial invariant in a common compound type can erase the invariant at the compound boundary. Open, unmerged PR #3179 adds product and `Option` instances and tests for exactly this problem, while noting that other holes remain.

For future Anneal design, the durable lesson is to distinguish **where an invariant is defined** from **where the language/toolchain forces it to be preserved**. A proof obligation on selected function boundaries is not a sound type invariant unless every invariant-breaking construction or mutation is forced through a checked boundary, or the representation is otherwise sealed strongly enough to make unchecked mutation impossible.

## Applicability

The primary subject is the historical V1 implementation retained under `anneal/v1` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. This report describes that implementation and the contemporaneous issues which explain why it was deliberately gated as unsound.

The second subject is open PR #3179 at head `ef0b8ebe7011311bce0e8fa2fe4a3aa5d95c1e6c`. It is evidence of a proposed partial repair to the compound-type problem; it is **not** part of the current V1 implementation and must not be treated as current behavior.

The report concerns the V1 `isValid` mechanism only. It does not evaluate current Anneal V2's invariant architecture, V1 `isSafe`, the separate lifetime-erasure problem, or whether Rust's eventual unsafe-fields design is sufficient for a future Anneal invariant system.

No fresh Anneal/Lean execution was performed for this report. Execution-oriented claims below are limited to the behavior encoded in checked-in test configuration and expected-output fixtures; implementation claims come from exact source inspection.

## Findings

### `isValid` is disabled by default because V1 knows it is unsound

`validate_artifacts` takes an `unsound_allow_is_valid` boolean. When that boolean is false, any parsed type carrying an explicit `isValid` clause produces an `AnnealError::Unsoundness` and causes validation to fail. The diagnostic says that `` `isValid` annotations are unsound and require the --unsound-allow-is-valid flag. `` `main.rs` invokes this validation before Charon and Aeneas.

The CLI definition is unusually explicit about the reason. Its documentation says that Rust does not require invariant-carrying fields to be `unsafe`; consequently, code without an Anneal annotation can modify those fields without an unsafe block, leaving Anneal no signal that a soundness-relevant operation needs verification.

The checked-in `unsound_is_valid_error` fixture encodes this as a regression contract. Its source contains only a trivial `isValid self := true` type annotation; its test configuration expects failure without the opt-in, and its expected stderr contains the same unsoundness diagnostic.

Basis: source + checked-in regression artifacts.

This gate is the strongest current safety property of V1 `isValid`: users who do not explicitly opt into known unsoundness cannot accidentally rely on it.

### With the opt-in enabled, V1 enforces validity at annotated function boundaries

The generator turns `isValid` into Lean typeclass obligations around an Anneal-annotated function:

- every function argument contributes `h_<arg>_is_valid : Anneal.IsValid.isValid <arg>` to `Pre`;
- every non-unit return contributes `h_ret_is_valid : Anneal.IsValid.isValid ret` to `Post`;
- every direct `&mut` argument contributes `h_<arg>'_is_valid : Anneal.IsValid.isValid <arg>'` to `Post`.

The generated fields use `verify_is_valid` as an automatic proof tactic, and users can override an injected validity field with an explicit proof. Generator unit tests assert the presence of the injected argument and return fields. The end-to-end `is_valid_verification` fixture opts in with `--unsound-allow-is-valid`; its checked-in expected output shows Lean failing to synthesize `h_ret_is_valid` for deliberately problematic returned values.

Basis: source + checked-in regression artifacts.

These obligations are real local contracts. If an annotated function accepts an invariant-carrying value, Anneal can require the caller's proof context to establish validity; if the function returns such a value or mutates a direct `&mut` parameter, its proof must establish the corresponding postcondition.

### Function-boundary checking does not make the invariant global

The generator operates on Anneal artifacts and injects checks into Anneal-generated specifications. It does not transform every Rust construction or field mutation into a validity obligation. The CLI documentation and tracking issue #3107 identify this as the central soundness gap: an unannotated safe function can mutate a field that participates in `isValid`, even though that mutation may invalidate the predicate.

A minimal derived example is:

```rust
/// ```anneal
/// isValid self := self.x.val > 0
/// ```
struct Positive {
    x: u32,
}

fn break_invariant(p: &mut Positive) {
    p.x = 0;
}
```

Assuming the V1 opt-in is enabled, an Anneal-annotated boundary involving `Positive` may carry an `IsValid Positive` obligation. But the safe, unannotated assignment in `break_invariant` does not become unsafe merely because `x` participates in the predicate, and Anneal does not automatically insert a proof obligation there. The invariant can therefore be broken between checked boundaries.

Basis: source + issue #3107 + derived example.

This is why the V1 CLI describes `isValid` as effectively advisory. The missing mechanism is not merely a stronger theorem prover; it is a language/tooling hook that forces invariant-sensitive mutations through an auditable boundary. Issue #3107 points to unsafe fields as the intended direction. Issue #3088 separately records the design question of whether preservation should be checked at function boundaries, construction/mutation sites, or some combination.

### The generic `True` fallback creates an independent compound-type hole

`Anneal.lean` defines:

```lean
class IsValid (α : Type) where
  isValid : α → Prop

instance (priority := low) defaultIsValid {α : Type} : IsValid α where
  isValid _ := True
```

The fallback makes unmodeled types easy to compose: any type without a more-specific instance is considered valid. The problem is that this also applies to compound types unless Anneal defines recursive instances for them.

At the examined V1 revision, repository-wide code search under `anneal/v1` finds the generic fallback and generated user-type instances, but no `IsValid (Option ...)` or product instance in the V1 standard library. An annotated function returning `Option<Positive>` or `(Positive, U)` still gets `h_ret_is_valid`, but the proposition is about the **compound** Lean type. Without a more-specific compound instance, typeclass resolution may use `defaultIsValid`, reducing the compound's validity obligation to `True` rather than recursively checking `Positive`.

Issue #3087 records exactly this concern for tuples and other compound types. Open PR #3179 supplies direct corroborating evidence: it proposes recursive binary-product and `Option` instances plus tests where an invalid `Positive` nested inside those types must make verification fail. Its description calls the patch a draft fix for #3087 and states that other soundness holes remain, including structs and other builtins.

Basis: source + repository search + issue #3087 + unmerged PR source/history + derived typeclass consequence.

The mutation-boundary and compound-type problems are independent. Fixing recursive container instances would not make unannotated field mutation safe. Conversely, forcing all field mutation through checked boundaries would not by itself make a generic `IsValid (Option T) := True` preserve `T`'s invariant.

### User-defined type annotations do generate specific instances

The compound hole does not mean all explicit predicates are ignored. `generate_type` emits a specific `Anneal.IsValid <Type>` instance for an annotated struct, enum, or union and inserts the user's `isValid` clause into that instance. Its unit tests assert this behavior for a simple struct predicate.

Basis: source.

Thus the failure mode is compositional: the invariant can exist and be enforced directly for `Positive`, while a wrapper such as `Option Positive` can fall back to `True` unless the wrapper has its own recursive instance. This distinction matters when reusing V1 evidence: direct obligations on an explicitly annotated type and obligations on arbitrary containing types do not have the same strength.

## Boundaries

**Known not to apply without the opt-in:** normal V1 verification rejects explicit `isValid` annotations. The unsound mechanisms discussed here become available only after `--unsound-allow-is-valid` is enabled.

**Not a claim that every unannotated function escapes every check:** a value can later cross an annotated boundary and fail a validity obligation there. The soundness problem is that invalid state can exist and influence behavior before such a boundary, and the system does not force all invariant-sensitive operations through one.

**Not a complete inventory of compound holes:** the report establishes the generic fallback and the absence of product/`Option` recursion in current V1, with #3179 as a partial proposed repair. It does not enumerate every Rust/Lean type constructor that needs recursive validity semantics. PR #3179 itself says additional holes remain.

**No fresh execution:** the report did not rerun the V1 fixtures, compile PR #3179, or construct a new counterexample. Checked-in expected stderr is evidence of intended/regression-tested behavior, not a fresh runtime observation from this report.

**Historical scope:** `anneal/v1` is retained as an old prototype. Its design documents explicitly warn that known differences from the current project need not be reconciled there. The report is therefore useful as design history and a source of failure modes, not as current V2 authority.

**Adjacent soundness issues are separate:** lifetime erasure, `isSafe`, source-discovery totality, and other V1 soundness gaps have their own #3720 subjects. They can compound `isValid` problems in a full verification story but are not required to establish the two holes documented here.

## Evidence

All source paths below were inspected at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` unless otherwise stated.

- `anneal/v1/src/Anneal.lean`, blob `727199a54622d56dd429f2b3b178748f2cc5b7f1`, especially lines 41-47: `IsValid` and the generic `True` fallback; lines 78-109: the default validity proof tactic.
- `anneal/v1/src/generate.rs`, blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`, lines 703-740 and 761-790: generated `Pre`/`Post` validity fields; lines 946-1016: generated per-type `IsValid` instances; tests around lines 1587-1602, 2100-2127, and 2303-2326 assert the relevant generated forms.
- `anneal/v1/src/validate.rs`, blob `2259c939e4bba4b2c329b9751a2a3e86601c416c`, lines 18-53: unsoundness gate for explicit type invariants.
- `anneal/v1/src/resolve.rs`, blob `9a44f652961e0bfe62bc4c2efecd550dea361fab`, lines 53-67: CLI rationale for `--unsound-allow-is-valid`, including the unannotated safe-mutation hole.
- `anneal/v1/src/main.rs`, blob `3d363b977df790b266fe2a0635da1c294ec1b7c2`, lines 165-183: validation precedes Charon/Aeneas and receives the opt-in flag.
- `anneal/v1/tests/fixtures/unsound_is_valid_error/anneal.toml`, blob `8804cb21908dfc53b9ef72795971f93f750ef4c5`, plus `expected.stderr`, blob `862acc655de05edc81cdb4a1076e446911d1598b`: checked-in rejection behavior without opt-in.
- `anneal/v1/tests/fixtures/is_valid_verification/anneal.toml`, blob `8827bcf333460ba98a9db75b2af8bee76b7d29b0`, plus `expected.stderr`, blob `bd4f8b8c1a3e822eb9180f8d0d4fc14fc46e7b1e`: checked-in opt-in integration fixture and generated-return validity failure.
- `anneal/v1/docs/design/design.md`, blob `f09bf3c9ecd828fb457006853632bc824b1218df`: historical intended semantics for type invariants. This is descriptive design evidence, not stronger authority than the implementation and explicit unsoundness gate.
- Issue #3087, **`isValid` soundness hole?**, observed open on 2026-09-27: identifies the generic-fallback/compound-type problem.
- Issue #3107, **Tracking issue for ensuring `isValid` soundness**, observed open on 2026-09-27: identifies unannotated safe mutation as a soundness gap and records unsafe fields as the intended direction.
- Issue #3088, **Overhaul named/unnamed propositions, type invariants**, observed open on 2026-09-27: records the unresolved placement question for invariant checks.
- PR #3179, **basic option + product instances for isValid**, observed open and unmerged at head `ef0b8ebe7011311bce0e8fa2fe4a3aa5d95c1e6c`: adds recursive product/`Option` instances and corresponding tests as a partial repair.

`source-map.json` preserves these exact source identities and mutable-history observation points. `invariant-enforcement-matrix.json` summarizes the checked and unchecked boundaries in machine-readable form.

## Revalidation

For another V1 revision, the cheapest discriminating revalidation is:

1. inspect the `Anneal.IsValid` class and all in-scope instances, especially the generic fallback and recursive instances for products, `Option`, arrays, slices, user structs, and any other compound forms relevant to Anneal-generated signatures;
2. inspect `generate_function` for the exact places where `IsValid.isValid` is injected into pre/postconditions, including mutable post-state;
3. inspect validation/CLI handling for whether explicit `isValid` remains gated behind an unsound opt-in;
4. check whether Rust-side construction or field mutation is forced through a mechanism Anneal can recognize and verify, rather than merely assuming annotated function boundaries are complete;
5. rerun a small negative matrix: direct invalid return, invalid `&mut` post-state, unannotated safe mutation, `Option<InvariantType>`, product containing `InvariantType`, and at least one nested user-defined compound type.

If a future implementation removes the opt-in gate, do not infer that `isValid` became sound from that change alone. Require evidence that both independent classes of holes are closed: **complete preservation boundaries** and **compositional validity semantics**.
