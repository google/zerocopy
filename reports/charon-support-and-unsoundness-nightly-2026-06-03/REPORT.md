# Charon support, failure modes, and known semantic hazards at Aeneas nightly-2026.06.03

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, the Charon revision pinned by Aeneas `nightly-2026.06.03`, Charon's support boundary is not a simple supported/unsupported feature list. The pinned source has three materially different failure classes:

1. constructs Charon rejects or records as translation errors;
2. constructs it represents only partially or opaquely;
3. transformations that succeed but deliberately change or lose semantics.

The highest-risk pinned semantic hazard is source-explicit. `--index-to-function-calls` rewrites array/slice indexing by creating references, and its own option documentation warns that the transformation "may introduce UB" when indexing behind a raw pointer. The Aeneas preset enables this transformation. Upstream issue #583 was closed after making the pass optional, not after making the Aeneas configuration semantically faithful. At this pinned revision, the transformation source still lacks a raw-pointer exclusion and the Aeneas preset still enables it.

A second active correctness limitation affects the Aeneas preset's associated-type lifting. Charon issue #534 remains open and the pinned `expand_associated_types` source documents that quantified bound lifetimes are not tracked correctly. The issue's example turns an associated-type equality containing `&'a ()` under `for<'a>` into one containing an erased lifetime. This is a known representation error in a transformation Aeneas requests with `lift_associated_types("*")`.

A third important boundary is failure signaling. Charon continues after registered extraction errors by default, serializes a `CrateData` whose `has_errors` bit says the output is partial, and normally exits successfully unless `--error-on-warnings` or `--abort-on-error` changes the policy. Individual failed bodies/items can become `Body::Error` or declaration error nodes. Charon's OCaml JSON reader, used by Aeneas at the paired revision, accepts the third top-level JSON field but discards it; it does not propagate `has_errors` into the returned crate. A pipeline that checks neither Charon's diagnostics nor the partial-artifact marker can therefore accept an incomplete extraction. Historical Anneal V1 explicitly passed `--abort-on-error` and checked Charon's status/diagnostics, which mitigated this particular path; that historical behavior is not a current V2 architecture commitment.

The pinned source also explicitly rejects coroutines/async lowering in several MIR positions, unsafe lifetime binders, reborrow rvalues, and some `dyn Trait` combinations. Its rustc-UI test harness classifies several unstable feature families as unsupported. Other limitations are configuration-specific: default promoted MIR can contain conditional drops, while `--precise-drops` raises the MIR level to elaborated; standard-library bodies require a MIR-bearing/custom sysroot to be available; and the Aeneas preset enables fallible-operation reconstruction that explicitly loses unwinding information.

The checked-in `docs/limitations.md` is useful but stale at this pin. Several issues it still lists as missing or unsound were closed before the pinned commit, while source-visible hazards such as #583 remain relevant under the Aeneas preset despite their issue being closed. This report therefore treats pinned source plus issue chronology as authority instead of copying the limitations page verbatim.

No fresh Charon, rustc, or Aeneas execution was performed. The conclusions below are source/history conclusions pinned to exact revisions.

## Applicability

Primary Charon subject:

- repository: `AeneasVerif/charon`
- revision: `a535e914f74db4fd9e6be7048f4233270d8945c0`
- Charon version: `0.1.210`
- commit timestamp: 2026-06-01T23:08:07Z
- relationship: pinned by Aeneas `nightly-2026.06.03`

Paired Aeneas subject:

- repository: `AeneasVerif/aeneas`
- revision: `ac9f1bc5262a5e4ff1e24ca78617121382202727`
- relationship: Anneal's selected Aeneas release and consumer of Charon LLBC

Anneal context:

- repository: `google/zerocopy`
- revision: `41f5b37afe7060fd9fe08c00b200672cd76d77b9`
- current V2 authority lives under `anneal/`;
- `anneal/v1/` is used only as historical evidence for the old orchestration's error policy.

"Unsupported" below means the pinned source or a pre-pin upstream tracking issue explicitly identifies the construct/configuration as unsupported. It does not mean this report proves that every Rust program outside the listed set is supported.

"Known semantic hazard" includes both upstream-labeled unsoundness and source-documented transformations that can change behavior relevant to a Rust-level proof. The term does not imply a security vulnerability in Charon itself.

## Findings

### The Aeneas preset enables a source-documented UB-introducing indexing rewrite

`CliOpts::index_to_function_calls` is documented in the pinned `charon/src/options.rs` as transforming array/slice indexing into builtin functions. The same comment warns that this can introduce undefined behavior because the pass creates references that did not exist in the source MIR, including when the indexed place is behind a raw pointer.

`Preset::Aeneas` sets `index_to_function_calls = true`.

The pinned implementation in
`charon/src/transform/simplify_output/index_to_function_calls.rs` confirms the mechanism. For an index/subslice projection it:

1. constructs a shared or mutable borrow of the indexed subplace;
2. calls a Charon builtin indexing function with that reference;
3. replaces the original place projection with a dereference of the returned reference.

The visitor recursively handles places and has no guard that stops this transformation merely because the subplace was reached through a raw-pointer dereference.

Upstream issue #583 calls this behavior "unsound" for access behind a raw pointer. The issue was closed on 2025-12-08 with the maintainer comment that making `index_to_function_calls` optional was sufficient. That closure is not evidence that the transformation became faithful when enabled. At the pinned revision, it is optional globally but still selected by `Preset::Aeneas`.

This distinction is critical for Anneal: Aeneas-preset LLBC may contain references synthesized by Charon that the Rust program did not create. A Rust-level UB-freedom argument cannot silently assume this rewrite preserves raw-pointer semantics.

Basis: **source** + upstream bug history. No execution was required to establish the configured transformation.

### Aeneas requires the same preset that enables the indexing rewrite

At `AeneasVerif/aeneas@ac9f1bc…`, `src/Main.ml` checks that imported LLBC records `preset = Some Aeneas`. If not, Aeneas emits an error telling the user to regenerate the crate with `--preset=aeneas`.

Therefore the indexing hazard is not merely attached to an obscure optional mode that Anneal can ignore while using stock Aeneas. The paired Aeneas consumer expects the preset in which Charon enables it.

Anneal could choose a different future boundary, patch the toolchain, or justify/restrict the transform. This report does not choose among those designs.

Basis: **source**.

### Associated-type lifting still mishandles quantified lifetimes at the pin

`Preset::Aeneas` also adds `"*"` to `lift_associated_types`. The pinned implementation of
`charon/src/transform/normalize/expand_associated_types.rs` documents a limitation: bound lifetimes in quantified clauses are not tracked correctly, referencing upstream issue #534.

Issue #534 remains open. Its reproducer is a predicate of the form:

`T: for<'a> Trait<'a, Type = &'a ()>`.

The reported transformed output erases the lifetime inside the associated-type argument, yielding a form equivalent to `&'_ ()` instead of preserving its relationship to the quantifier.

This is not merely missing cosmetic lifetime naming. It changes a type-level relationship that can matter to downstream proof obligations. The existing Anneal lifetime report separately documents broader region preservation/erasure boundaries; the item-8 fact here is narrower: an Aeneas-selected Charon transformation has a known pinned correctness bug involving quantified lifetimes.

Basis: **source** + open upstream bug #534.

### A formerly documented bound-lifetime trait-resolution unsoundness is historical, not pinned-active evidence

`docs/limitations.md` still lists issue #584 under "Known unsoundnesses." Issue #584 reported that trait resolution erased bound lifetime information and could identify distinct types.

However, #584 was closed on 2025-07-02, well before the pinned June 2026 Charon commit. Its maintainer comment points to a hax fix. This report therefore does **not** classify #584 as a pinned-active bug merely because the limitations page still lists it.

This is one example of why the limitations page must be reconciled with source and chronology rather than treated as an exact support manifest.

Basis: **documentation/history**; absence from the active list is a conservative classification, not a fresh regression test.

### Fallible-operation reconstruction intentionally loses unwinding information

The pinned option documentation for `reconstruct_fallible_operations` says the pass replaces a bounds/check-plus-UB-on-overflow pattern with a panic-on-overflow operation and explicitly states: "This loses unwinding information."

`Preset::Aeneas` enables this pass.

That is an intentional abstraction rather than an upstream bug. It is nevertheless semantically material for any Anneal property that depends on unwinding edges, cleanup behavior, or distinctions between normal failure and unwind paths. A proof consumer must either establish that the lost unwind information is irrelevant to its claim or use a different extraction boundary.

Basis: **source**.

### Coroutines and async remain explicitly unsupported in the pinned translator

The pinned translation source rejects coroutine-related constructs in multiple places:

- coroutine types produce "Coroutine types are not supported yet";
- coroutine/coroutine-closure aggregate rvalues produce "Coroutines are not supported";
- `CoroutineDrop`, `Yield`, and related terminators are rejected;
- coroutine-specific assertion kinds are rejected.

Issue #609, "Support async," was opened before the pinned revision and remains open. Its design discussion explicitly says full async support requires choosing how to represent the compiler's coroutine transformation versus a higher-level effectful view.

Therefore ordinary Rust syntax lowering successfully through rustc does not imply that Charon can translate the resulting MIR. Async/coroutine code is a source-explicit unsupported family at this pin.

Basis: **source** + upstream tracking issue #609.

### Unsafe Rust is broadly admitted, but several unsafe-language mechanisms are not

The old blanket "Support unsafe code" issue #280 was closed in 2024; Charon does translate raw pointers and many unsafe MIR operations.

That does not mean every unsafe-language mechanism is supported. The pinned body translator explicitly rejects:

- `UnwrapUnsafeBinder` projections;
- `WrapUnsafeBinder` rvalues;
- reborrow rvalues used for Reborrow traits.

It also contains an unimplemented branch for deep fake borrows used by deref patterns.

Thus the useful support statement is not "unsafe supported" or "unsafe unsupported." Raw pointers and unsafe operations are in the AST, but specific newer/less common MIR mechanisms can still fail translation.

Basis: **source**.

### Some trait-object combinations and type forms fail explicitly

The pinned trait-object translator rejects a `dyn Trait` whose predicate set contains multiple method-bearing predicates. Other vtable construction paths raise translation errors when they encounter non-dyn-compatible or unsupported virtual-impl shapes.

The type translator explicitly errors on unsupported alias kinds, inference/placeholder types that escape expected compiler phases, coroutine types, and Hax `Todo` type forms.

These failures are preferable to silent translation, but they mean "Charon supports dyn Trait" and similar broad tracker labels must be read as scoped claims rather than complete coverage of every legal combination.

Basis: **source**.

### Constant translation may preserve an unsupported value as opaque while registering an error

The pinned constant translator handles many constant forms. For unsupported constant casts and Hax `Todo` constants, however, it registers an error and emits `ConstantExprKind::Opaque` rather than inventing detailed semantics.

This is an example of the partial-output model: a serialized crate can contain a placeholder corresponding to a translation failure. Downstream consumers must inspect the extraction's error state rather than assuming every syntactically present node has complete semantics.

Basis: **source**.

### The pinned rustc-UI harness encodes an explicit unsupported-feature set

`nix/rustc-tests.nix` runs Charon against a pinned rustc UI test corpus and classifies several feature gates as `unsupported-feature` without attempting Charon translation:

- `generic_const_exprs`;
- `adt_const_params`;
- `min_generic_const_args`;
- `effects`;
- `transmutability`;
- `loop_match`;
- `default_type_parameter_fallback`.

The harness also excludes tests requiring build/test settings it does not model, such as revisions, auxiliary crates, compile flags, target-only conditions, and several compiletest-specific directives.

These are source-defined harness exclusions, not results freshly observed by this report. Some are unstable Rust features and do not imply missing support for stable Rust with the same surface syntax.

Basis: **source**.

### Additional pre-pin trackers record unsupported contracts and custom-pointer unsizing

Two open upstream issues predate the pinned commit and remain relevant boundaries:

- #646 tracks translation of experimental Rust contract annotations.
- #855 tracks unsizing through custom smart pointers using `CoerceUnsized`/`Unsize`.

Because these are feature-request trackers, this report treats them as known unsupported/unfinished areas, not as proof that every nearby rustc representation fails in the same way.

Basis: upstream **documentation/history**.

### Default promoted MIR does not provide the strongest drop semantics

The pinned options define four MIR levels: built, promoted, elaborated, and optimized. The default is promoted. Charon documents elaborated as the first MIR level containing all runtime drop information.

`--precise-drops` raises the requested MIR level to at least elaborated and asks Charon to translate drop glue. Without it, `DropKind::Conditional` remains possible and its source documentation says the exact semantics can depend on later rustc elaboration.

Issue #152 was closed before the pin because Charon gained an elaborated-MIR path; the maintainer explicitly noted that the remaining problem was making later MIR the default. Issue #543, tracking strong later-MIR support, remained open at the pinned commit and was closed only on 2026-06-26.

So `docs/limitations.md` saying simply "Drops" are missing is stale/overbroad at the pin. The precise pinned fact is configuration-dependent: Charon can request elaborated MIR for more precise drops, but the default promoted extraction may not expose final runtime drop behavior.

Basis: **source** + issue chronology.

### Type layout is present for some types despite the stale limitations page

`docs/limitations.md` also lists layout information as missing. Issue #581 records that layout support for types without generics was added before the pinned commit. The pinned source contains layout structures, representation options, variant layouts, field offsets, discriminant machinery, and translation code for rustc layout data.

That does not make layout coverage complete: generic/monomorphization cases remain limited. But the pinned support state is no longer "no layout information."

Basis: **source** + issue #581 history.

### Foreign and standard-library bodies depend on whether MIR was encoded into metadata/sysroot

A declaration may exist with `Body::Missing` when Charon cannot retrieve a body. Historical issue #545 documents the core limitation: the normal shipped standard library does not provide all MIR bodies needed for whole-world extraction. The maintainers demonstrated a workaround using a custom/Miri sysroot built with MIR available.

This is not the same as Charon rejecting the Rust language feature. It is an extraction-availability boundary. A "whole reachable program" claim must account for opaque/missing external bodies and the sysroot/dependency build configuration used.

Basis: **source** + upstream history.

### Charon continues after translation errors by default

`ErrorCtx::new` initializes `continue_on_failure = true`. `register_error!` records an error and increments `error_count`; if continuation is enabled it returns to the caller instead of aborting the process.

Translation code catches both ordinary translation errors and panics at item/body granularity. Failed type declarations can become `TypeDeclKind::Error`; failed bodies can become `Body::Error`; item panics are registered as extraction errors and translation continues.

This is a deliberate best-effort extraction model.

Basis: **source**.

### Partial LLBC is serialized and can exit with status 0 under default Charon error policy

`CrateData` contains `has_errors`, documented as meaning that the serialized crate contains only a partial description of the input. `CrateData::new` sets it from the transform context's error state.

The Charon driver serializes the output before applying the final `error_on_warnings` exit policy. If errors were registered and `--error-on-warnings` is not set, `run_charon` returns `Ok(error_count)`; `main` prints a warning but exits successfully. If `--error-on-warnings` is set, it returns Charon error status 1 after serialization. `--abort-on-error` instead disables continuation and turns the first registered translation error into a panic path.

The outer driver uses distinct exit classes:

- Charon/serialization failure: status 1;
- rustc failure: status 2;
- uncaught outer Charon panic: status 101;
- successful best-effort extraction with warnings: status 0.

Therefore process success alone does not mean the serialized crate is complete under default options.

Basis: **source**.

### The paired Aeneas JSON reader discards Charon's partial-artifact marker

At `AeneasVerif/charon@a535e914…`, `charon-ml/src/OfJson.ml` implements the parser that the paired Aeneas uses. Its `crate_of_json` accepts either:

- exactly `charon_version` plus `translated`; or
- those two fields plus one arbitrary third field.

It validates the Charon version, parses `translated`, and returns the crate fields. It does not retain or inspect the third field, which is where Charon serializes `has_errors`.

As a result, Aeneas cannot recover the partial-artifact bit from the parsed crate through this path. A caller that feeds it a Charon file after ignoring Charon's warnings/status can lose the fact that Charon reported incomplete extraction.

This is a source-level fail-open risk in composition, not evidence that Aeneas itself promises to validate Charon completeness.

Basis: **source**.

### Historical Anneal V1 explicitly mitigated Charon's permissive default

Current `google/zerocopy` still contains the historical V1 implementation under `anneal/v1/`. Its Charon invocation:

- passes `--preset=aeneas`;
- passes `--abort-on-error`;
- watches structured compiler diagnostics for errors/ICEs;
- requires Charon's process status to succeed.

Thus the V1 orchestrator did not rely on Charon's default status-0-on-warnings behavior. This is useful historical evidence for why fail-closed orchestration is needed.

V1 is not current V2 design authority. The current V2 design intentionally has not frozen the exact Rust/Charon/Aeneas boundary.

Basis: **source**, historical Anneal evidence.

### The pinned rustc-test harness has a useful failure taxonomy even without fresh execution

`nix/rustc-tests.nix` classifies test outcomes into:

- success;
- unsupported build settings;
- unsupported feature;
- stack overflow/timeout;
- internal compiler error;
- panic;
- failure in rustc;
- failure in Charon.

For expected-pass tests, it separately checks whether an LLBC file was actually produced and records whether Charon emitted warnings.

This taxonomy is a durable model for revalidation because it distinguishes unsupported configuration, compiler rejection, Charon rejection, panic/ICE, timeout, and successful-but-warning-bearing extraction.

Basis: **source**. No current counts from that harness are claimed.

### The limitations document must be treated as an index, not a pinned manifest

At the pinned revision, `docs/limitations.md` still lists:

- #583 and #584 as "known unsoundnesses";
- foreign/std bodies, drops, layout information, and body lifetime information as missing.

The source/history evidence above shows different statuses:

- #583 remains semantically relevant when its optional pass is enabled; Aeneas enables it.
- #584 was closed/fixed before the pin and is not treated here as pinned-active.
- drop information is configuration-dependent and can be made more precise with elaborated MIR.
- monomorphic layout information exists at the pin.
- std/foreign body availability depends on encoded MIR/sysroot configuration.
- body lifetime information remains intentionally limited, as documented separately by the existing lifetime report.

Future support audits should start from the pinned source and issue chronology, using `docs/limitations.md` as a lead list rather than a complete truth table.

Basis: **derived** from **source** and issue history.

## Boundaries

- No fresh compiler, Charon, Aeneas, rustc-UI suite, or LLBC experiment was run.
- This is an inventory of **known/documented** unsupported and incorrect behavior at the exact pin, not a proof that all unlisted Rust features are supported.
- The rustc-UI harness exclusions are harness policy, not empirical failure counts from this run.
- The #583 conclusion is configuration-specific: the problematic transformation is optional, but the Aeneas preset enables it.
- The #534 conclusion applies to associated-type lifting/normalization involving quantified lifetimes; it does not imply all lifetime handling is incorrect.
- #584 is not called active because its upstream issue was closed before the pin. This report did not rerun its historical reproducer.
- Async/coroutine support is explicitly rejected in the pinned translator; this report does not investigate whether isolated compiler-generated coroutine-adjacent types can appear in otherwise supported code.
- External/std body availability depends on how dependencies and the sysroot were built.
- Layout support is partial; this report does not inventory every layout shape.
- `--precise-drops` availability does not prove perfect drop translation for every polymorphic program; the option itself documents rustc limitations.
- Charon's `has_errors` behavior is established from source. Whether a particular higher-level wrapper notices stderr or exit status is wrapper-specific.
- Anneal V1's `--abort-on-error` behavior is historical evidence only; no V2 architecture is inferred from it.
- This report does not evaluate Aeneas's semantic treatment after it successfully parses LLBC; that is covered by later Aeneas reports.
- The separate end-to-end source-correspondence report must assess whether semantic omissions can be detected at the user-facing proof boundary.

## Evidence

**Source — primary Charon subject.**
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

Key files and symbols:

- `docs/limitations.md`: upstream-maintained lead list of limitations, reconciled here against pin source/history.
- `charon/src/options.rs`:
  - `CliOpts::index_to_function_calls` warning that the pass can introduce UB behind raw pointers;
  - `Preset::Aeneas`;
  - `MirLevel`;
  - `TranslateOptions::new`;
  - `abort_on_error` / `error_on_warnings`.
- `charon/src/transform/simplify_output/index_to_function_calls.rs`:
  `IndexVisitor::transform_place` and the pass's `should_run`.
- `charon/src/transform/normalize/expand_associated_types.rs`:
  module-level documented limitations, including issue #534.
- `charon/src/bin/charon-driver/translate/translate_types.rs`:
  explicit unsupported coroutine/type cases and layout translation.
- `charon/src/bin/charon-driver/translate/translate_bodies.rs`:
  unsafe-binder/reborrow/coroutine failures and item-body error capture.
- `charon/src/bin/charon-driver/translate/translate_trait_objects.rs`:
  unsupported dyn-trait combinations.
- `charon/src/bin/charon-driver/translate/translate_constants.rs`:
  unsupported constants becoming opaque with registered errors.
- `charon/src/bin/charon-driver/translate/translate_items.rs`:
  per-item error/panic capture and error declaration nodes.
- `charon/src/errors.rs`: `ErrorCtx`, `register_error!`, continuation policy.
- `charon/src/export.rs`: `CrateData::has_errors` and partial-output serialization.
- `charon/src/bin/charon-driver/main.rs`: serialization-before-final-error-policy and process exit classes.
- `charon-ml/src/OfJson.ml`: JSON reader that discards the third top-level field.
- `nix/rustc-tests.nix`: explicit unsupported-feature/build-setting filters and result taxonomy.

**Upstream issue history.**

- Charon #583, "handling of indexing in unsafe code is unsound"; closed 2025-12-08 after optionalizing the pass.
- Charon #584, bound-lifetime trait-resolution unsoundness; closed 2025-07-02, with maintainer note pointing to a hax fix.
- Charon #534, quantified lifetimes in associated-type removal; open at observation.
- Charon #609, async support; open at observation.
- Charon #646, contract annotations; open at observation.
- Charon #855, custom-smart-pointer unsizing; open at observation.
- Charon #152, drop elaboration; closed 2025-10-22 after elaborated MIR became selectable.
- Charon #543, later MIR support; still open at the pinned commit and closed 2026-06-26.
- Charon #581, type layouts; monomorphic layout support landed before the pin.
- Charon #545, foreign/std body availability and custom MIR-bearing sysroots.

**Source — paired Aeneas.**
`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`,
`src/Main.ml`: requires imported LLBC to record `Preset::Aeneas`.

**Source — historical Anneal V1 mitigation.**
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`,
`anneal/v1/src/charon.rs`: passes `--preset=aeneas` and
`--abort-on-error`, parses compiler diagnostics, and rejects unsuccessful Charon status.

No evidence above is labeled **execution**. This report performed no fresh execution.

## Revalidation

For a later Aeneas/Charon pin, perform source checks first:

1. Resolve the exact Charon commit packaged by the selected Aeneas release.
2. Diff `docs/limitations.md`, but do not trust it alone. Reconcile every listed issue against source and closure date.
3. Diff `options.rs`, especially `Preset::Aeneas`, `index_to_function_calls`, `reconstruct_fallible_operations`, MIR level, and error-policy options.
4. Inspect `index_to_function_calls.rs` for an explicit raw-pointer exclusion or a semantic redesign. If Aeneas still enables it and the transformation still creates references through raw-pointer indexing, retain the #583 hazard.
5. Recheck `expand_associated_types.rs` and #534 for quantified-lifetime preservation.
6. Search translation source for `unsupported`, `unimplemented!`, `todo!`, and error-producing Hax/MIR cases.
7. Recheck the rustc-UI harness's hard-coded unsupported features and failure taxonomy.
8. Recheck `ErrorCtx`, `CrateData::has_errors`, driver exit policy, and the Charon-ML/Aeneas deserializer's treatment of the partial-artifact marker.
9. Recheck how the actual Anneal orchestration invokes Charon. Do not assume the V1 `--abort-on-error` mitigation persists.

On a capable execution surface, run four minimal discriminating experiments at the exact revisions:

**Raw-pointer indexing transform.**
Compile a function that indexes an array/slice reached through a raw pointer. Extract once with `--preset=aeneas` and once with indexing-to-function-calls disabled. Inspect LLBC for a synthesized reference around the raw-pointer-derived place. This establishes the concrete encoding for that revision; it does not by itself prove Rust-level unsoundness beyond the source/upstream model.

**Quantified associated-type lifetime.**
Use the #534-style
`for<'a> Trait<'a, Type = &'a ()>` fixture with the Aeneas preset. Inspect whether the same bound lifetime survives in the transformed trait clause. A mismatch directly discriminates the known bug.

**Partial-artifact signaling.**
Use a small construct the exact pin explicitly rejects. Run Charon under:
(a) default continuation,
(b) `--error-on-warnings`,
(c) `--abort-on-error`.
Record exit status, whether an LLBC file exists, its `has_errors` value, and any `Body::Error`/opaque/error node. Then feed the default partial JSON to the paired Aeneas parser and observe whether it rejects specifically because of Charon's partial marker. This validates the source-derived fail-open composition claim.

**MIR/drop configuration.**
Extract a function with conditional/partial drops under default promoted MIR and under `--precise-drops`/elaborated MIR. Compare `DropKind`, generated drop glue, and failure behavior. This establishes the exact configured drop semantics; it does not prove all rustc drop paths are faithfully modeled.

Preserve the fixtures, commands, serialized artifacts, stderr/stdout, exit statuses, exact revisions, and hashes. Those experiments are deferred here solely because this scheduled surface is source-research oriented.
