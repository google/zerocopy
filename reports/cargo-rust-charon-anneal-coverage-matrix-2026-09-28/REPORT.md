# Cargo compilation coverage through Charon and Anneal V1

## Summary

Cargo's workspace unit graph, actual rustc command capture, Charon output, and one Anneal V1 proof answer different coverage questions. In this fixture Cargo built 12 units for the workspace/all-targets path, but the successful V1 proof was only for the `coverage_app` library with `selected` enabled. Build-script output and a procedural-macro expansion appeared in that library's LLBC/model; a normal dependency stayed opaque, and a separate consumer's LLBC represented the proof-bearing library function as foreign. Cargo target coverage must therefore be tied to the exact selected extraction roots and emitted obligations, not inferred from what Cargo compiled.

This is executed evidence for #3725 recommendations R06, R15, R23, R31, R32, and R37.

## Applicability

Observed on macOS aarch64 with Cargo 1.98.0-nightly (`fbb61be30`, 2026-05-26), rustc 1.98.0-nightly (`f8a08b688`, 2026-05-30), Charon 0.1.210 at `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, Aeneas at `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`, Lean 4.30.0-rc2 at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, and retained Anneal V1 at `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`.

The Cargo fixture is dependency-free and has a library, binary, integration test, unit test, build script, proc-macro crate, feature-gated function, local shared crate, and second consumer package. The proof run selected only the library target and `selected` feature. These results do not establish behavior for other Cargo versions, targets, profiles, or Charon revisions.

## Findings

### Compilation and verification roots are separate sets

`cargo -Z unstable-options build --offline --workspace --all-targets --unit-graph` reported 12 units and 9 roots. An actual `cargo build --offline --workspace --all-targets` recorded 14 rustc command invocations in the wrapper log; `cargo test --offline --workspace` completed successfully. These commands include separate contexts such as build-script-build and proc-macro host units alongside target units. This is evidence about Cargo's selected work, not a count of functions translated or proved.

`cargo -Z unstable-options build --offline --package coverage_app --lib --features selected --unit-graph` reported 7 units and one root. The retained unit graph and manifests are in `support/`. This was the Cargo selection used for the focused verification invocation.

Basis: **execution**. The unit graph captures Cargo's resolved units and roots; the wrapper separately records actual rustc invocations. Neither is a Charon declaration inventory.

### Feature resolution is unit- and command-sensitive

The workspace all-targets graph contains distinct `shared` feature sets: a build-side unit with `build-api`, and target/test units with the union `dev-api`, `macro-api`, and `target-api`. The selected library-only graph has the build-side set and a target-side `target-api` set, without `dev-api`. Feature unification within one Cargo unit does not imply that every unit has the same set. The V1 scanner discovers an annotation behind `#[cfg(feature = "selected")]` even when the verification command omits that feature; Charon/rustc then fails because the declaration is cfg-removed. The exact no-feature verification exited 1. This is a failure of that observed path, not an assertion that all cfg combinations panic.

Basis: **execution** + **derived**. The command-specific feature arrays are preserved in the unit graphs. The scanner/extraction distinction follows from the annotation being present in source while the declaration is absent from the selected compilation.

### Generated and macro-expanded code can enter the selected crate's translation

The build script writes `BUILD_VALUE = 17` into Cargo's `OUT_DIR`; a proc macro emits `proc_generated() = 29`; the library function `library_subject` references both. Charon's LLBC has local declarations for the macro expansion, included generated constant, library function, and selected function. Aeneas output represents the generated constant as `17#u32` and the macro result as a local function returning `29#u32`.

This shows that these outputs can be represented in this specific library extraction. It does not preserve complete provenance from build-script inputs or macro implementation to each declaration, nor does it prove every generated declaration has an Anneal contract. The V1 proof invocation verified only the annotated feature-gated function; its theorem was `selected_feature_subject.spec`, with postcondition `ret.val = 101` (see `support/v1-generated-selected-spec.lean`).

Basis: **execution**. Reproducer sources, Charon's local/foreign function projection, Aeneas `Funs.lean`, and the generated V1 specification are retained in `support/`.

### Dependency code is not implied by proving a consumer crate

The normal local dependency `shared::target_value` appears as an external/opaque call in the library's Aeneas model. Separately extracting the `consumer` binary succeeds, but its LLBC marks `coverage_app::selected_feature_subject` non-local with foreign opacity and no local body. The consumer's own extraction therefore does not translate the dependency body just because Cargo compiled that dependency. A dependency needs its own extraction/verification subject or a justified trusted model to enter the assurance claim.

Direct Charon selection of the workspace binary or integration-test target failed in this fixture with `extern location for coverage_app does not exist` for the expected rlib. This report preserves the observed failure but does not infer that Charon cannot support those targets in all configurations; the exact Cargo target/features/fingerprint combination is part of the subject.

Basis: **execution** + **derived**. Charon locality and opacity are preserved in compact JSON projections. The inference is limited to the missing dependency body in this selected output.

### Successful compilation is not a checked-obligation count

The full Cargo build and test establish compilation and test behavior for the fixture. `cargo-anneal verify --manifest-path .../coverage_app/Cargo.toml --features selected --lib` separately exited 0 for the annotated library function. It did not establish verification of `library_subject`, the generated constant, the proc-macro implementation, the binary, integration test, or `shared::target_value`. The generated V1 theorem was separately elaborated and queried with `#print axioms`; that establishes only Lean elaboration and the theorem's Lean axiom dependencies, not Rust-to-LLBC semantic correspondence.

## Boundaries

- The dependency-free fixture demonstrates a coverage accounting method, not representative package behavior or Cargo/Charon completeness.
- Only one annotated function had an Anneal proof. Build-script and macro-generated values were translated, but their full provenance and contract coverage were not proved.
- Cargo's successful test run does not establish verification, and Charon/Aeneas output does not by itself establish checked theorem obligations.
- No feature-interaction sweep, profile comparison, cross-target comparison, source-snapshot race, stale artifact control, interruption test, or cross-version ladder was run here.
- The binary/integration extraction failure and feature-disabled failure are configuration-specific observations. They are not language-wide or product-wide support claims.
- No correspondence theorem between Rust execution and LLBC/Aeneas semantics was established.

## Evidence

The source workspace and `Cargo.lock` are under `support/workspace/`; it has no external dependencies. The unit-graph JSON paths and rustc wrapper command logs are sanitized. `support/charon-aeneas-functions.json` and `support/charon-consumer-functions.json` preserve relevant declaration locality and opacity without the full LLBC serialization. `support/aeneas-Funs-replayed.lean` preserves the generated model excerpt, and `support/v1-generated-selected-spec.lean` is the V1-generated theorem source. `support/command-results.json` records the result matrix. A replay succeeded after setting `DYLD_LIBRARY_PATH` to the installed Nix Rust toolchain library directory and giving Charon a fresh `CARGO_TARGET_DIR`. With the existing Cargo target state, the same library command exited 0 but emitted no file at the requested destination; with the fresh target, it emitted LLBC. The captured locality/opacity projections matched the earlier run, although raw LLBC and generated `Funs.lean` hashes differed; no byte-level determinism claim is made. `support/replay-results.json` records both runs and hashes.

Executed commands included:

```console
cargo -Z unstable-options build --offline --workspace --all-targets --unit-graph
cargo build --offline --workspace --all-targets
cargo test --offline --workspace
cargo -Z unstable-options build --offline --package coverage_app --lib --features selected --unit-graph
charon cargo --preset aeneas --dest charon-aeneas -- --package coverage_app --lib --features selected --offline
cargo-anneal verify --manifest-path coverage_app/Cargo.toml --features selected --lib
charon cargo --preset aeneas --dest charon-consumer -- --package consumer --bin consumer --offline
```

The selected V1 verification, Aeneas Lean generation, separate Lake build, and theorem axiom query exited 0. A corrected fresh-target replay of Charon and Aeneas also exited 0; its output projections are preserved separately. The no-feature verification exited 1. Direct Charon binary/integration extraction exited 101 because Cargo could not locate the expected local rlib. Local build directories and generated caches are not included.

## Revalidation

From `support/workspace`, rerun the commands above with the stated versions. Compare the two unit graphs first, then inspect Charon's local/foreign declarations and the generated Aeneas model. Run V1 verification only with the selected feature and library target. For any new Cargo command or feature combination, record the unit graph, rustc invocations, extracted declarations, annotated obligations, and final theorem names independently. Use a clean output directory to avoid confusing cached or stale outputs with newly selected coverage.
