# Charon drop and destructor semantics at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), a Charon `Drop` is not one fixed operation. Its meaning depends first on the rustc MIR phase Charon extracted. Built/analysis-phase MIR becomes a **conditional** drop whose eventual runtime behavior may depend on moves, partial initialization, or later drop elaboration. Runtime MIR becomes a **precise** drop that denotes a concrete call to the selected `Destruct::drop_in_place` implementation. `--precise-drops` raises local extraction to at least elaborated MIR, adds explicit `Destruct` obligations, and asks Charon to recover drop glue.

Charon represents destructor dispatch explicitly. It gives drops a `drop_in_place` function pointer and represents destruction through a `Destruct` trait. For ADTs and closures, Charon can materialize synthetic drop-glue bodies; a user `Drop::drop` body remains an ordinary translated function, while the synthetic `Destruct::drop_in_place` body performs the full glue sequence, including the user destructor and field destruction when that glue is available. Generic drop glue can instead be `<missing>`, and opacity can make it opaque. Charon explicitly warns that precise drop-glue extraction for polymorphic types can make rustc panic.

Rustc's elaborated drop-state machinery is visible in precise output as ordinary control flow and state. Checked-in Charon goldens show partial moves becoming field-specific drops and path-dependent initializedness becoming Boolean branches. Charon does not retain a separate high-level "drop flag" abstraction in final LLBC.

One representation boundary is especially important for downstream verification: ULLBC retains a drop's normal and unwind targets, but ULLBC→LLBC deliberately discards the unwind target for both `Drop` and `Call`. The pinned source marks this with `TODO: Have unwinds in the LLBC`. `--desugar-drops` therefore does not preserve unwind cleanup in final LLBC merely by turning a precise drop into a call. A consumer that needs Rust panic/unwind destruction semantics cannot reconstruct those discarded edges from final LLBC alone.

No fresh Charon execution was performed. The report relies on pinned implementation source and Charon's checked-in source/golden test pairs. It complements `rust-drop-elaboration-nightly-2026-05-31`, which documents the upstream rustc drop-elaboration boundary and Aeneas's treatment of LLBC drops.

## Applicability

The findings apply to Charon repository `AeneasVerif/charon`, revision `a535e914f74db4fd9e6be7048f4233270d8945c0`, package version `0.1.210`. This is the Charon revision pinned by the Aeneas release selected by current Anneal.

Several findings are configuration-sensitive:

- Charon defaults the current crate to promoted MIR unless another MIR level is requested.
- `--precise-drops` raises the requested level to at least elaborated MIR and enables additional drop-related translation behavior.
- `--desugar-drops` rewrites only precise drops into ordinary `drop_in_place` calls.
- An item's actual MIR phase, not merely the command-line default, determines whether Charon labels its drops `Conditional` or `Precise`. Non-local MIR availability can therefore differ from local current-crate extraction.
- Item opacity and genericity affect whether a `drop_in_place` body is concrete, opaque, or missing.

"ULLBC" below means Charon's unstructured, MIR-like control-flow representation. "LLBC" means the structured-control-flow form produced by the pinned ULLBC→LLBC pass. This report describes Charon's representation and transformations; it does not assert that those transformations are semantically correct with respect to Rust.

## Findings

### `DropKind` records whether rustc has already made destruction precise

Charon's common AST defines two drop kinds.

`DropKind::Precise` is a real drop. Charon documents it as a call to `<T as Destruct>::drop_in_place(&raw mut place)` that also marks the place moved-out-of. The source says precise drops come from elaborated or optimized MIR.

`DropKind::Conditional` is a pre-elaboration drop. Charon's own comment deliberately leaves its exact runtime meaning open: the eventual operation may become a partial drop, may depend on the path by which control arrived, or may participate in async destruction. It can also name an unaligned place in a packed struct, which would not be a valid operand for a precise drop.

The body translator derives the kind from the actual rustc body phase: `Built` and `Analysis` map to `Conditional`; `Runtime` maps to `Precise`. It then translates every MIR `Drop` terminator into a ULLBC `Drop` containing the kind, translated place, selected `drop_in_place` function pointer, normal target, and unwind target.

A downstream consumer therefore cannot interpret a serialized `Drop` correctly from the node name alone. It must preserve or deliberately resolve the `DropKind` distinction.

Basis: **source**.

### `--precise-drops` changes both MIR phase and the type-level destruction interface

The `--precise-drops` option does more than choose prettier output. Its documentation says it:

- adds explicit `Destruct` bounds to generic parameters;
- raises the MIR level to at least elaborated MIR; and
- attempts to retrieve drop glue for all types.

`TranslateOptions::new` implements those consequences by raising `mir_level`, setting `add_destruct_bounds`, and setting `translate_poly_drop_glue` from `precise_drops`.

This is a semantic configuration boundary. A report about drop behavior must record whether precise drops were enabled rather than treating the option as presentation-only.

Basis: **source**.

### Charon makes destruction dispatch explicit through `Destruct::drop_in_place`

When translating a MIR drop, Charon solves the synthetic destruction obligation for the dropped type and constructs a function pointer to that type's `drop_in_place` method. The translated `Destruct::drop_in_place` signature is unsafe `*mut Self -> ()`.

For ADTs and closures, Charon also creates an implicit `Destruct` implementation and installs the corresponding `drop_in_place` method. This gives polymorphic code an explicit trait-level handle for destruction. Checked-in output shows generic code using its `T: Destruct` proof to select `TraitClause::drop_in_place`, while concrete types use their translated or opaque implementation.

This representation is separate from Rust's user-defined `Drop` trait. A type may have a translated `Drop::drop` method and a separate synthetic `Destruct::drop_in_place` method that represents the full glue operation.

Basis: **source** + checked-in upstream golden artifacts.

### A synthetic drop-glue body can include the user destructor and field destructors

The checked-in `desugar_drops_to_calls` fixture defines `Point` with a user `Drop::drop` and two `Box` fields. With `--precise-drops --desugar-drops`, Charon's expected LLBC contains:

1. an ordinary translated `impl_Drop_for_Point::drop` function for the user body;
2. a synthetic `impl_Destruct_for_Point::drop_in_place` function;
3. within that synthetic function, a call to `Drop::drop`; then
4. calls to the `drop_in_place` implementations for `x` and `y`.

The final call site does not call `Drop::drop` directly. It calls the synthetic `Destruct::drop_in_place`, which contains the complete destruction sequence that Charon recovered from rustc drop glue.

This distinction matters when a proof depends on destructor side effects. Modeling only the source `Drop::drop` method does not by itself model destruction of fields after that method returns.

Basis: pinned **source** + checked-in upstream golden **execution artifact**. No fresh execution was performed for this report.

### Drop-glue availability is explicit and configuration-dependent

Charon's `translate_drop_in_place_method_body` only tries to build a synthetic body for an ADT or closure. For those items it translates glue when at least one of these conditions holds:

- `translate_poly_drop_glue` is enabled;
- Charon is monomorphizing;
- the definition is synthetic; or
- the definition has no generics.

Otherwise the body is `Missing`.

The `manual-drop-impl` golden demonstrates this boundary without `--precise-drops`: generic `Foo<T>` has a normal translated user `Drop::drop`, but its synthetic `Destruct::drop_in_place<T>` is `<missing>`, and the generic caller contains a `conditional_drop` that points to that missing glue.

If the item is configured opaque, Charon emits an opaque body instead. If Charon does attempt to retrieve polymorphic drop glue, it wraps rustc's `drop_glue_shim` query in `catch_unwind`; the source warns that rustc is known to panic for some polymorphic types and recommends making the relevant `Destruct` implementation opaque as a workaround.

"The drop function pointer is present" therefore does not imply "the complete destructor implementation is present."

Basis: **source** + checked-in upstream golden artifact.

### Precise MIR turns dynamic initializedness into ordinary LLBC state and control flow

Rustc drop elaboration can introduce Boolean drop flags and split a whole-value drop into drops of remaining initialized fields. Charon translates the resulting MIR operations rather than preserving a separate source-level drop-state abstraction.

Two checked-in Charon goldens make that concrete:

- `conditional-drop`, run with `--precise-drops`, contains a Boolean local that is set when a `Box` becomes initialized, cleared before a move, tested before the final `drop`, and cleared afterward.
- `partial-drop`, also run with `--precise-drops`, moves `f.x` and finishes with precise drops of only `f.y` and `f.z`.

For a verifier consuming precise LLBC, these branches, assignments, moves, and field-specific drops are the relevant representation. The original source-level fact that they arose from rustc's drop-flag/open-drop machinery is no longer a distinct LLBC node.

Basis: checked-in upstream golden **execution artifacts** + **derived** interpretation consistent with the pinned rustc report.

### No-op destruction can disappear from the body

Charon recognizes a built-in/auto `NoopDestruct` proof. The ordinary cleanup pass replaces a `Drop` using such a proof with a `Goto`. If `--desugar-drops` is enabled, the drop-desugaring pass performs the same elimination before constructing a call.

Consequently, absence of a `Drop` node is not sufficient evidence that no source scope ended there. Charon intentionally removes destruction that its translated trait proof says is a no-op.

Basis: **source**.

### `--desugar-drops` converts precise drops to ordinary calls, but not conditional drops

The `desugar_drops` transformation matches only `DropKind::Precise`. For a non-no-op drop it creates a temporary raw mutable pointer with `&raw mut place`, creates a unit destination, and replaces the `Drop` terminator with an ordinary `Call` to the retained `drop_in_place` function pointer. It preserves the ULLBC normal and unwind targets on that call.

Conditional drops remain conditional-drop nodes because Charon cannot replace their intentionally underspecified pre-elaboration semantics with an unconditional `drop_in_place` call.

The `desugar_drops_to_calls` golden shows the final structured output after this rewrite: concrete drops appear as raw-pointer construction followed by `drop_in_place` calls, while scalar no-op drops disappear.

Basis: **source** + checked-in upstream golden artifact.

### ULLBC preserves drop unwind edges; LLBC discards them

ULLBC represents a drop as a terminator with both `target` and `on_unwind`. Charon's MIR translator also preserves rustc unwind actions: continue becomes `UnwindResume`, unreachable becomes undefined-behavior abort, terminate becomes `UnwindTerminate`, and cleanup points to the translated cleanup block.

The checked-in `drop_after_overflow` ULLBC fixture shows this structure directly. A conditional drop on an unwind path has its own unwind target, and the target can terminate if another unwind happens during cleanup.

The ULLBC→LLBC conversion does not preserve that edge. In `ullbc_to_llbc.rs`, the `Drop` arm destructures `on_unwind: _` and contains the comment `TODO: Have unwinds in the LLBC`; it emits only an LLBC `Drop(place, fn_ptr, kind)` followed by the normal target. The adjacent `Call` arm does the same thing for call unwind targets.

This is a representation loss, not merely a pretty-printing difference. Final LLBC at this revision does not contain enough control-flow information to recover the discarded destructor unwind branch.

Basis: **source** + checked-in upstream ULLBC artifact.

### Desugaring a drop does not fix LLBC's unwind-information loss

`--desugar-drops` preserves the unwind target while the body is still ULLBC because it rewrites a precise `Drop` to a ULLBC `Call` carrying the same `on_unwind` block. But ULLBC→LLBC separately discards `on_unwind` for calls.

Therefore the combination `--precise-drops --desugar-drops` can make destructor dispatch explicit as ordinary calls while still losing the cleanup edge when Charon produces final LLBC. A downstream consumer that needs panic/unwind semantics must address that boundary separately; changing the syntactic form from `Drop` to `Call` is not sufficient.

Basis: **source** + **derived** consequence of the two pinned transformation implementations.

### The existing rust-drop report and this Charon report answer different questions

`rust-drop-elaboration-nightly-2026-05-31` establishes why Rust destruction is conditional on initializedness, how rustc elaborates potential drops, Charon's broad phase distinction, and Aeneas's default treatment of LLBC drops. This report narrows in on Charon's own destruction interface: synthetic `Destruct` dispatch, glue-body availability, the precise/conditional representation, checked-in Charon transformation examples, desugaring, no-op filtering, and ULLBC→LLBC unwind loss.

For Rust-level verification, the two boundaries compose: rustc determines which runtime destruction operations exist, while Charon determines what of those operations and their control flow reaches the selected exported representation.

Basis: existing corpus report + pinned Charon **source**.

## Boundaries

- No fresh Charon, rustc, Aeneas, or Lean execution was performed. Checked-in `.out` files are upstream-preserved expected-output artifacts, not observations produced by this run.
- This report does not prove Charon's drop translation sound or equivalent to Rust. It records the pinned implementation and preserved fixture outputs.
- It does not exhaustively characterize async/coroutine destruction. `DropKind::Conditional` explicitly names async drop as one possible outcome of pre-elaboration drop semantics; async/coroutine representation is a separate corpus subject.
- It does not exhaustively characterize dynamic-trait/vtable destruction, packed-field edge cases, arrays/slices of every shape, or every standard-library drop-glue shim. The retained mechanisms are enough to identify the relevant representation boundaries, not to enumerate every type.
- It does not claim `--precise-drops` works for every polymorphic item. Charon documents a rustc-panic failure mode and exposes opacity as a workaround.
- It does not claim a missing or opaque `drop_in_place` body has no runtime effect. Those states mean the body is not available in the translated representation under the relevant configuration.
- It does not characterize how Aeneas or another consumer compensates for LLBC's missing unwind edges. The existing rust-drop report separately records Aeneas's pinned drop evaluator.
- It does not generalize the behavior to adjacent Charon revisions. Current Charon source has continued to evolve its drop representation after this pinned subject.

## Evidence

**Source — Charon.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210).

- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: `--precise-drops`, `--desugar-drops`, MIR-level raising, `add_destruct_bounds`, and `translate_poly_drop_glue`.
- `charon/src/ast/gast.rs`, blob `23044319a8f763d241912c5d693ed94cf597682f`: `DropKind::{Precise, Conditional}` and the documented semantic distinction.
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`, blob `c03ca8077f131a2ef701e9d27eaa9e69bb617124`: MIR-phase-to-`DropKind` mapping, MIR-drop translation, and unwind-action translation.
- `charon/src/bin/charon-driver/translate/translate_drops.rs`, blob `948ac38b6de14f5a8d97036a41eb02ec14df0b98`: `Destruct::drop_in_place` selection, synthetic trait impls, glue-body extraction, generic-body omission, opacity, and rustc-panic handling.
- `charon/src/ast/ullbc_ast.rs`, blob `3c6179f10742b2ee82c8ca07e6d51be6c8dc7694`: ULLBC drop fields and explicit normal/unwind targets.
- `charon/src/ast/llbc_ast.rs`, blob `40f29f8a4b19f98e929b5fe82b8a009d813120ad`: structured LLBC `Drop(place, fn_ptr, kind)` representation.
- `charon/src/transform/normalize/desugar_drops.rs`, blob `b84f1d30fce1a74a21f7b9abd449657e9227954f`: precise-drop-to-call rewrite and no-op elimination.
- `charon/src/transform/simplify_output/filter_trivial_drops.rs`, blob `0ca1b0cdcdce96ba0b846f96ed458b3b1fec8d37`: ordinary no-op-drop removal.
- `charon/src/transform/control_flow/ullbc_to_llbc.rs`, blob `07322359e92f92a4d8b55865a67257bedacb0a62`: structured conversion and explicit dropping of `on_unwind` for `Drop` and `Call`.
- `charon/src/transform/mod.rs`, blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`: ordering of drop desugaring, trait-reference normalization, trivial-drop filtering, and control-flow reconstruction.

**Documentation — Charon.** Same revision.

- `docs/transformations.md`, blob `7e3f7c6ed096aa053920905f1939ad80675ddd52`: ULLBC/LLBC control-flow-reconstruction boundary.

**Preserved upstream golden artifacts — Charon.** Same revision. These are checked into Charon's own UI test suite; this report did not rerun them.

- `charon/tests/ui/simple/conditional-drop.rs` / `.out`, source blob `c73e5d839cf73de371d13cb5396b5b45f029f119`, output blob `7756b7f034da81c048427c7ff07fa99ad7a8f4ca`: elaborated path-dependent drop flag rendered as ordinary Boolean/control flow.
- `charon/tests/ui/simple/partial-drop.rs` / `.out`, source blob `26dc918728ad1066d796ca6515920376b217baa0`, output blob `18fd3c81d126a7f34ed86d0e82428a5fcc56d994`: partial move followed by field-specific precise drops.
- `charon/tests/ui/simple/manual-drop-impl.rs` / `.out`, source blob `754f09f78d70e2f1829fa1e90ebb59533d4f7c1e`, output blob `c68cc6bd2876cb1ccedfd59fedb36e48ce2e3d05`: generic user `Drop::drop` alongside missing synthetic generic drop glue and a conditional drop.
- `charon/tests/ui/desugar_drops_to_calls.rs` / `.out`, source blob `bb377ca2fe5e86e7c810361e21a4f39150ecc662`, output blob `a712096b45a69a39508242fc7636fc9a7232c39d`: precise-drop desugaring and complete concrete `Point` glue containing the user destructor plus field drops.
- `charon/tests/ui/drop_after_overflow.rs` / `.out`, source blob `acb626efe4dc9ee41ec8a93bf0bdfd8b2cdd17b7`, output blob `5b0e52a7003bb1574c001beda3b9601c3182d1e7`: ULLBC cleanup/unwind targets around conditional destruction.
- `charon/tests/ui/explicit-drop-bounds.rs` / `.out`, source blob `8e7c4053cac2cdd5974db1e18cb988b0a0977d8d`, output blob `4c24700cc207f45d8e408d42fc72613bf2aee771`: explicit `Destruct` obligations in precise generic output.

**Related corpus evidence.** `reports/rust-drop-elaboration-nightly-2026-05-31` at current `google/zerocopy` `reference` documents rustc's drop-elaboration algorithm, the upstream initializedness obligation, and the pinned Aeneas drop evaluator. `reports/charon-ullbc-llbc-schema-nightly-2026-06-03` documents the broader ULLBC/LLBC schema and transformation boundary.

No evidence gathered by this report is fresh **execution**.

## Revalidation

For another Charon revision, the cheapest source-level discriminator is:

1. Resolve the exact Charon revision actually consumed by the relevant Aeneas/Anneal subject.
2. Diff `options.rs` for MIR defaults, `--precise-drops`, `--desugar-drops`, and generic-glue controls.
3. Diff `ast/gast.rs`, `ast/ullbc_ast.rs`, and `ast/llbc_ast.rs` for `DropKind` and drop/call representation changes.
4. Diff `translate_bodies.rs` and `translate_drops.rs` for MIR-phase selection, unwind mapping, `Destruct` dispatch, and synthetic glue generation.
5. Diff `normalize/desugar_drops.rs` and `filter_trivial_drops.rs` for drop-removal or drop-to-call semantics.
6. Most importantly, inspect the `Drop` and `Call` arms of `control_flow/ullbc_to_llbc.rs`. If they still discard `on_unwind`, final LLBC still lacks those explicit cleanup edges; if LLBC has gained an unwind representation, re-evaluate the downstream boundary rather than carrying this report's conclusion forward.

On a capable execution surface, rerun the pinned-style compact fixture set rather than a broad workspace:

- one path-dependent move that requires a drop flag;
- one partial move that requires field-specific destruction;
- one generic type with a user `Drop` implementation;
- one concrete type with a user `Drop` implementation and drop-requiring fields;
- one panic-capable path whose cleanup drops a value.

Generate final ULLBC and LLBC with default settings, with `--precise-drops`, and with `--precise-drops --desugar-drops`. Preserve exact command lines, revisions, JSON artifacts, and hashes. Compare `DropKind`, selected `drop_in_place` references, synthetic glue bodies, normal/unwind targets, and the structured LLBC result. That probe revalidates the representation boundary; proving semantic equivalence to Rust remains a separate task.