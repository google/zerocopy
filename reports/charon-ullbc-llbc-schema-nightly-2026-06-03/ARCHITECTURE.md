# Charon architecture and rustc integration at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), Charon is a two-stage rustc-driver pipeline rather than a post-hoc parser for compiler artifacts. The `charon` executable handles the pinned toolchain, Cargo or direct-rustc orchestration, and option transport. The sibling `charon-driver` executable links against `rustc_private`, runs rustc with callbacks, extracts Rust items and MIR while a live `TyCtxt` is available, then hands a Rust-independent translated crate to Charon's transformation and serialization layer.

Cargo mode is part of that architecture. Instead of reconstructing rustc command lines itself, `charon` invokes Cargo with `RUSTC_WRAPPER=charon-driver`. Cargo therefore supplies dependency artifacts, `--extern` arguments, target configuration, features, and the other compiler arguments for each build unit. The wrapper sees those rustc invocations but translates only selected target-side primary-package units; dependency and host-side invocations such as build scripts and procedural macros run through rustc normally. Charon forces an explicit Cargo `--target` when the caller omitted one so the driver can distinguish host and target invocations.

Extraction is deliberately early. `CharonCallbacks::after_expansion` calls the translation entry point before MIR-based analysis, because rustc queries can steal earlier MIR bodies. The driver then allows rustc analysis to continue and stops in `after_analysis`; selected units have code generation disabled. Charon can request built, promoted, drop-elaborated, or optimized MIR for local items, with fallback to optimized MIR when an earlier body is no longer available. Non-local items have narrower MIR availability.

The resulting crate is not serialized immediately. After the rustc-facing translation returns and the `TyCtxt` has been dropped, Charon runs its own transformation pipeline over ULLBC, optionally reconstructs structured control flow into LLBC, performs cleanup and consistency checks, and then serializes `CrateData`. This gives a useful architectural boundary: rustc/Cargo integration determines what compiler facts enter the translated crate; later Charon passes transform that captured representation without further rustc interaction.

No fresh Cargo, rustc, or Charon execution was performed. The report establishes the pinned source architecture and its explicit selection rules; it does not empirically characterize every Cargo workspace, target, wrapper, or multi-target invocation pattern.

## Applicability

This report applies to:

- Charon repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- package version `0.1.210`;
- embedded Rust toolchain `nightly-2026-05-31`.

The report covers the `charon cargo` and `charon rustc` front ends, the `charon-driver` rustc integration, MIR acquisition, item-worklist extraction, post-rustc transformation, and serialization boundaries.

It does not characterize the separate multi-target merge algorithm in detail, destination-file behavior when several primary Cargo units are selected, or the semantics of individual transformation passes beyond what is needed to locate the architectural boundary. Those are separate subjects in the reference inventory.

The Charon revision is the one coupled to the Aeneas release used by current Anneal, as recorded by the existing `aeneas-charon-compatibility-nightly-2026-06-03` report. This report does not infer the same architecture for adjacent Charon revisions.

## Findings

### The public executable and the rustc driver have different responsibilities

The Charon package builds both `charon` and `charon-driver`. Its manifest describes `charon` as the main entry point that manages the toolchain and Cargo and describes `charon-driver` as the rustc driver, dynamically linked to rustc libraries and not intended to be invoked directly.

The split is visible in the implementation. The `charon` executable parses the public CLI, selects Cargo or direct-rustc mode, arranges the pinned toolchain, and transports `CliOpts`. The driver imports rustc-private crates, runs `rustc_driver::run_compiler` with Charon callbacks, translates while compiler state is alive, and returns a `TransformCtx`.

This makes the driver the compiler-integration boundary and the outer executable the build-orchestration boundary.

Basis: Charon **source** + upstream **documentation**.

### Cargo mode delegates compilation-unit construction and rustc argv construction to Cargo

The wrapper source explains why it uses Cargo: reconstructing exact rustc arguments for a real crate, especially dependency `--extern` paths, is difficult and duplicates Cargo's work. `translate_with_cargo` therefore runs Cargo's `build` subcommand with:

- `RUSTC_WRAPPER` set to the sibling `charon-driver`;
- `CHARON_USING_CARGO=1`;
- serialized Charon options in `CHARON_ARGS`;
- the caller's Cargo arguments appended after Charon's own setup.

The driver consequently receives the rustc argv that Cargo chose for each unit. Charon is not independently reconstructing Cargo's unit graph or dependency command lines at this boundary.

This is an architectural delegation, not a claim that Cargo's command line alone captures every semantic input to compilation. The separate Cargo reports cover unit identity and feature resolution.

Basis: Charon **source** + upstream **documentation**.

### The wrapper compiles non-selected Cargo units normally and translates selected target units

Setting `RUSTC_WRAPPER` means the driver is invoked for every rustc process Cargo routes through the wrapper. Charon distinguishes those invocations with two tests:

1. in Cargo mode, absence of `CARGO_PRIMARY_PACKAGE` marks a workspace dependency;
2. presence of an explicit `--target` marks a target-side invocation rather than a host-side build-script or procedural-macro invocation.

The driver translates a unit only when it is both a primary package and target-side. Otherwise it invokes rustc with `RunCompilerNormallyCallbacks`.

The outer wrapper makes the second test usable even for ordinary host-target builds by adding `--target <rustc-host>` to the Cargo command whenever the user did not provide a target. Host-side build scripts and proc macros then remain distinguishable because Cargo does not pass that target argument to their host compilation.

This source rule explains why build scripts and procedural macros can participate in compilation without themselves becoming the selected Charon translation unit.

Basis: Charon **source**.

### Charon's pinned Rust toolchain is part of the executable integration contract

The repository's `charon/rust-toolchain` selects `nightly-2026-05-31` with `rustc-dev`, `llvm-tools-preview`, `rust-src`, and `miri`. `toolchain.rs` embeds that file into the `charon` binary.

Outside Charon's Nix environment, the wrapper runs Cargo and the driver through `rustup run <pinned-channel> ...`, installing the pinned channel and components if needed. In the Nix path, `CHARON_TOOLCHAIN_IS_IN_PATH` tells the wrapper to use the already-provided toolchain. `driver_cmd` still arranges the Cargo-wrapper calling convention by inserting `rustc` as argv[1].

The rustc-private integration is therefore revision-sensitive by construction. A Charon binary is not merely a parser that can be assumed to accept arbitrary neighboring rustc internals.

Basis: Charon **source** + repository toolchain configuration.

### The rustc callbacks extract before MIR-based analysis and stop before code generation

For a selected unit, `CharonCallbacks::config` adjusts rustc configuration and `after_expansion` calls `translate_crate::translate`.

The source gives a concrete reason for this callback: borrow checking and other MIR analysis can steal earlier MIR query results, while Charon may need built MIR. Extracting in `after_expansion` keeps those query results available.

The callback does not immediately stop compilation. It returns `Compilation::Continue`; `after_analysis` later returns `Compilation::Stop`. For selected translation units, `set_no_codegen` also enables rustc's no-codegen mode and restricts output to metadata. Thus Charon uses rustc analysis as part of extraction but does not require native code generation for the selected unit.

Basis: Charon **source**.

### Charon deliberately changes MIR-related compiler options for extraction

For both translated and normally compiled wrapped units, `set_mir_options` enables `always_encode_mir`, sets MIR optimization level 0, enables `mir_preserve_ub`, and disables the `CheckAlignment` MIR pass.

These settings are part of the pinned extraction environment. They mean the MIR Charon observes is not simply “whatever a default rustc build would have produced” at this revision.

For selected units, Charon can additionally skip borrow checking when explicitly requested. That option replaces the `mir_borrowck` query result with an empty result. It is therefore a semantic configuration boundary, not a presentation flag.

Basis: Charon **source**.

### MIR acquisition depends on locality and requested MIR level

`get_mir_for_def_id_and_level` distinguishes local and non-local definitions.

For local definitions, Charon can query:

- built MIR;
- promoted MIR;
- drop-elaborated and const-checked MIR;
- optimized MIR.

If an earlier local MIR body has already been stolen, it falls back to optimized MIR.

For non-local functions, only the MIR rustc made available through metadata can be queried. Charon uses optimized MIR for available non-global functions and CTFE MIR for relevant globals and const functions. The source notes that `-Zalways-encode-mir` improves MIR availability for dependencies Charon compiled itself, but does not make arbitrary standard-library MIR available.

A report or consumer must therefore bind “the MIR Charon sees” to item locality and configured MIR level. There is no single universal phase for every item in a translated crate.

Basis: Charon **source**.

### Item extraction is a recursive worklist, not a flat dump of every rustc definition

`translate_crate::translate` constructs Charon's translation context and seeds a worklist from configured starting points. If the user supplied none, `TranslateOptions::new` inserts the strict pattern `crate`. Alternative roots can come from explicit patterns, a marker attribute, or public items.

Translating an item can discover referenced items and enqueue them. The loop continues until the queue is empty. Opacity controls whether Charon translates an item's body or only its outer declaration; local-crate items are transparent by default, while foreign items are foreign/opaque by default unless options change that treatment.

Some rustc item kinds are deliberately not registered as standalone translated items. At this revision, `ExternCrate`, `GlobalAsm`, `Macro`, and `Use` return no translation kind. Other reports cover the semantic consequences for global assembly and generated code.

“Extract the complete crate” therefore means Charon's recursively selected semantic representation under these translation and opacity rules, not a byte-for-byte or one-rustc-item-per-output inventory.

Basis: Charon **source** + upstream **documentation** + **derived** qualification.

### Charon drops rustc state before its main transformation pipeline

At the end of `translate_crate::translate`, Charon returns a `TransformCtx` containing translated data, options, and error state; the source comment explicitly notes that returning it drops the hax state and rustc `tcx`.

Back in `charon-driver/main.rs`, `run_charon` then calls `run_transformation_passes`. Those passes normalize item/type information, transform ULLBC bodies, optionally reconstruct structured control flow into LLBC, clean the result, recover comments, reorder declarations, and run consistency checks. Serialization happens only after those passes.

This separates two kinds of evidence:

- rustc-facing extraction source determines how compiler state is captured into Charon's representation;
- Charon transformation source determines how that captured representation is rewritten before final ULLBC/LLBC output.

A later consumer investigating information loss must identify which side of this boundary removed or synthesized the information.

Basis: Charon **source** + **derived** architectural distinction.

### Serialized output records the Charon version and can represent partial extraction

`CrateData` contains the translated crate, the Charon version, and `has_errors`. Charon's deserializer currently rejects a serialized file whose version string differs from the running library's version. If translation accumulated errors but publication was still permitted by the selected error policy, serialization labels the result as partial through `has_errors`.

This is relevant to architecture because successful file creation is not, by itself, evidence that extraction was complete. Consumers need to inspect Charon's error state and version compatibility as separate conditions.

Basis: Charon **source**.

### Direct `charon rustc` uses the same driver but shifts build-context responsibility to the caller

The `charon rustc` subcommand appends the user-supplied rustc arguments, ensures an explicit target if one was absent, serializes `CHARON_ARGS`, and launches the same sibling driver under the pinned toolchain.

It therefore bypasses Cargo's build-unit and dependency-argv construction without bypassing the rustc callback architecture. The caller must supply a rustc command line sufficient for the source being translated.

Basis: Charon **source**.

## Boundaries

- No fresh Cargo, rustc, Charon, LLBC, or runtime execution was performed.
- The report establishes source-defined control flow and selection predicates; it does not empirically enumerate the exact rustc processes Cargo emits for every target, profile, workspace, feature set, or Cargo version.
- Multiple selected primary Cargo targets and destination-file interactions are not characterized here. They belong to the separate Charon multi-target/multi-unit subjects.
- The report does not claim that `CARGO_PRIMARY_PACKAGE` plus explicit `--target` is infallible for every Cargo scenario. It records the heuristic this pinned Charon implementation uses.
- It does not claim that `always_encode_mir` makes all dependency or standard-library MIR available. The source explicitly describes narrower availability.
- It does not characterize the semantics of every Charon transformation pass. Existing ULLBC/LLBC reports cover representation and transformation details.
- It does not establish that direct `charon rustc` and Cargo mode are behaviorally equivalent for arbitrary projects.
- It does not generalize the rustc callback point, MIR queries, or wrapper protocol to another Charon or rustc revision.
- It does not choose an Anneal integration architecture. It preserves the upstream boundary an Anneal design would integrate with.

## Evidence

**Documentation and source:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `README.md`, blob `6470a71c857dcb64be248cdb5dfe67576d914c99`: crate extraction purpose, ordinary Cargo-like usage, serialized LLBC interface, alpha-status boundary.
- `docs/usage.md`, blob `8731e44a3caa5ca3fc54c001ce2579b1a3ad4bde`: Cargo-oriented invocation, pinned-nightly requirement, ULLBC/LLBC overview.
- `docs/what_charon_does_for_you.md`, blob `b0e9b32a11b78f106c7edf953bb0f60967de8cb2`: rustc-extraction and normalization responsibilities.
- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: package version, `charon_lib`, `charon`, and `charon-driver` roles.
- `charon/rust-toolchain`, blob `3c98116ae62afb83263fa1654037badaf569e1c1`: pinned nightly, components, and targets.
- `charon/src/bin/charon/main.rs`, blob `b4460ce4cd3baa32308718e79b6e194860b042a6`: Cargo-wrapper orchestration, `RUSTC_WRAPPER`, `CHARON_USING_CARGO`, `CHARON_ARGS`, explicit target insertion, direct-rustc mode, and multi-target dispatch.
- `charon/src/bin/charon/cli.rs`, blob `3580a74c6079079510aba318949810bc1a95a15f`: public Cargo/rustc subcommands and forwarded arguments.
- `charon/src/bin/charon/toolchain.rs`, blob `b35d1d0236cd7e1c5f68ad5b80b3371b82f2e784`: embedded toolchain, rustup/Nix selection, driver command construction.
- `charon/src/bin/charon/toml_config.rs`, blob `7bf93adcd601d300180b89315190591643de5e8e`: per-package Charon configuration and rustc flags.
- `charon/src/bin/charon-driver/main.rs`, blob `ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`: rustc-private driver entry point, post-rustc transformations, serialization, and error-code mapping.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`: compiler setup, wrapper-unit selection, callback point, no-codegen mode, MIR configuration, and stop-after-analysis behavior.
- `charon/src/bin/charon-driver/translate/get_mir.rs`, blob `a1cd9ba131a1362dda55e85c25f29f4a9e28df69`: MIR-level selection, stolen-body fallback, dependency MIR availability, CTFE MIR.
- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`: translation roots, recursive worklist, item-kind registration, opacity, and the rustc-state-to-`TransformCtx` boundary.
- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: MIR levels, root-selection options, opacity configuration, Aeneas preset, and output controls.
- `charon/src/transform/mod.rs`, blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`: post-extraction ULLBC/LLBC transformation ordering.
- `charon/src/export.rs`, blob `d5428958eb870f9f8531a8d193385c6be782338a`: `CrateData`, Charon-version check, partial-output marker, and serialization.

No evidence above is fresh **execution**.

## Revalidation

For another Charon revision, first diff the small set of files that defines the architectural seams:

1. `charon/Cargo.toml` and `charon/rust-toolchain`;
2. `charon/src/bin/charon/main.rs` and `toolchain.rs`;
3. `charon/src/bin/charon-driver/driver.rs`;
4. `translate/get_mir.rs` and the `translate` worklist in `translate_crate.rs`;
5. `options.rs`;
6. `transform/mod.rs` and `export.rs`.

The cheapest execution probe, when a capable surface is available, is a tiny pinned Cargo workspace containing one primary library or binary, a normal target dependency, a build script, and a procedural-macro dependency. Run Charon with Cargo verbose output under the exact pinned toolchain and preserve the Cargo/rustc commands, relevant wrapper environment, Charon output, and hashes. Confirm which invocations are host versus target, which carry `CARGO_PRIMARY_PACKAGE`, which are compiled normally, and which produce translated output.

Then repeat with direct `charon rustc` for one self-contained source file and preserve the exact argv and output. This tests the wrapper/driver boundary and selection rules for that revision. It does not establish multi-primary-target behavior, cross-target merging, performance, or semantic correctness of the extracted MIR.
