# Charon release upgrade checklist for Anneal

## Summary

Changing Anneal's Charon revision is not a version-string substitution. At the current baseline, Anneal selects Aeneas `nightly-2026.06.03`, whose source resolves to `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`. That Aeneas revision pins `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`; Charon reports package version `0.1.210` and pins Rust `nightly-2026-05-31`. Aeneas's release construction copies `charon`, `charon-driver`, and Charon's `rust-toolchain` from that locked input into the release tree.

Those identities are coupled, but they are not interchangeable labels. Charon's own `nightly-2026.06.03` tag names a different Charon commit even though both revisions report `0.1.210`. At the two known revisions, the examined LLBC JSON/version machinery happens to be byte-identical, but the version gate itself cannot establish semantic equivalence between same-version commits. An upgrade therefore has to resolve and validate the exact producer commit, compiler, effective Charon options, transformation pipeline, serialized and in-memory interfaces, Aeneas consumer, and packaged runtime.

The most important Charon-specific risk is that a process can produce a serialized artifact without that artifact being complete. At the baseline, `CrateData` records `has_errors`, and the driver serializes before applying the optional final `error_on_warnings` policy. Under default continuation, registered translation errors can therefore coexist with an output file and a successful process status. Any Anneal upgrade must re-establish a fail-closed boundary rather than treating process success or file existence as sufficient evidence.

The checklist in `upgrade-checklist.json` turns the current exact-pin corpus into twelve gates. It deliberately separates source-defined checks from empirical ones. Source review can identify a changed preset, schema, transform, error policy, or reachability rule. It cannot establish packaged-runtime viability, byte determinism, race behavior, or the concrete result of the composed Rust→Charon→Aeneas path. Those properties require discriminating execution on a capable surface.

This report defines the baseline and revalidation obligations. It does not approve any newer Charon revision.

## Applicability

The baseline is:

- Anneal authority: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`;
- Aeneas release: `nightly-2026.06.03` at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`;
- Aeneas-pinned Charon: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon package version: `0.1.210`;
- Charon Rust toolchain: `nightly-2026-05-31` with `rustc-dev`, `llvm-tools-preview`, `rust-src`, and `miri` listed as components.

At this Aeneas revision, `charon-pin` and the locked `charon` flake input both select `a535e914…`. The release derivation copies `charon-portable`'s `charon` and `charon-driver` binaries plus the Charon `rust-toolchain` into the Aeneas release. That is the Charon producer intended for Aeneas's LLBC consumer.

Current Anneal also has a separately resolved Charon Rust dependency in its source history. The published Aeneas–Charon compatibility report establishes that the currently executing V2 tool selection points at the Aeneas-bundled Charon and that the separate `charon_lib` edge is not active at the examined authority. The checklist nevertheless treats a future in-process `charon_lib` edge separately: compiling against Charon's Rust API and consuming serialized LLBC are different compatibility surfaces.

Use this checklist when changing the Charon revision packaged with or paired to Anneal's selected Aeneas, when changing an equivalent Charon producer, or when activating a different Charon library/wire edge in Anneal. It is not a general upstream Charon release checklist. A narrower test can satisfy a gate when it directly establishes the Anneal-relevant property; a broad upstream test suite cannot waive a missing Anneal-specific property.

## Findings

### 1. Resolve the exact producer before comparing behavior

The first upgrade artifact should record this chain with immutable identities:

`Anneal revision → Aeneas release/revision → Aeneas charon-pin + lock → Charon commit → Charon package version → Charon rust-toolchain`.

The baseline contains two mechanical checks worth preserving. Aeneas's `charon-pin` names `a535e914…`, and its `flake.lock` records the same revision. Aeneas also carries an installation check that compares an installed Charon checkout with the expected pin. Its release derivation builds/copies the Charon binaries from the locked input rather than choosing a same-date Charon tag independently.

That distinction is material because Charon package version `0.1.210` is not a commit identity. Charon's own `nightly-2026.06.03` tag can name a different source revision while retaining the same package version. Same-date labels across Aeneas and Charon likewise do not compose transitively.

For an upgrade, resolve the proposed Aeneas source first, read its Charon pin and lock, and record the exact binaries or archives Anneal will consume. If the pin and lock disagree, or if artifact provenance cannot be tied to the reviewed source, the upgrade should stop before semantic comparison.

Basis: direct Aeneas **source** plus the published exact-revision Aeneas–Charon compatibility report.

### 2. Treat Charon and its Rust nightly as one rustc-private unit

Charon's rustc-facing driver is not portable across arbitrary Rust releases. At the baseline, `charon/rust-toolchain` selects `nightly-2026-05-31` and lists rustc-private-support components. Charon's manifest explicitly separates the ordinary `charon_lib` from the rustc-facing binary feature, and the published toolchain report shows that the driver imports rustc-private crates and dynamically links rustc libraries.

The outer `charon` wrapper exists partly to establish this runtime. The ordinary path can use rustup to select the embedded channel. The Nix path can assert `CHARON_TOOLCHAIN_IS_IN_PATH`, in which case the wrapper trusts the supplied `PATH` rather than proving that the compiler there matches the embedded channel.

A Charon upgrade must therefore re-resolve the proposed `rust-toolchain`, compare the compiler and components with Anneal's packaged Rust sysroot, and exercise the actual provisioning path. A successful build in an upstream checkout does not establish that Anneal's relocated archive finds the same compiler or runtime libraries. Record `rustc -vV` or equivalent exact compiler identity from the packaged environment when execution is available.

Basis: direct Charon `rust-toolchain`/manifest **source**, current Anneal packaging **source**, and the published Charon toolchain contract.

### 3. Freeze the production-effective Charon configuration, not only the executable revision

The Aeneas preset is semantic configuration. At the baseline, `Preset::Aeneas` enables associated-type lifting, Box treatment, operation-to-function-call rewriting, index-to-function-call rewriting, fallible-operation reconstruction, assert reconstruction, marker-trait hiding, allocator hiding, unused-self-clause removal, ADT-clause removal, and item-variable unbinding.

These options feed an ordered transformation pipeline. The exact pass ordering matters: some passes document dependencies on the MIR statement shape and on whether another pass has already reconstructed or inserted statements. Charon also exposes MIR-level choices, start roots, inclusion/opacity rules, precise-drop behavior, warning/error policy, serialization format, and Cargo-versus-direct-rustc invocation modes.

The upgrade comparison should therefore preserve an effective configuration snapshot and diff `CliOpts`, `Preset::Aeneas`, the pass list, and `should_run` predicates. A new Charon revision can retain the same binary name and LLBC envelope while changing the meaning of the Aeneas preset or a default that the preset leaves untouched.

The production invocation matters too. `charon cargo` delegates build-unit selection and rustc command construction to Cargo through `RUSTC_WRAPPER`; `charon rustc` gives that responsibility to the caller. They reach the same rustc-driver architecture but do not define the same compilation subject automatically. Revalidate the mode Anneal actually uses.

Basis: direct Charon options/transform **source** and the published CLI/preset architecture reports.

### 4. Revalidate the LLBC wire and `charon_lib` API as different interfaces

At the baseline, JSON and Postcard serialize the same logical `CrateData` envelope: Charon version, translated crate, and `has_errors`. Rust deserialization requires exact equality between the embedded version string and `charon_lib::VERSION`, which is `CARGO_PKG_VERSION`. The generated OCaml side used by Aeneas has its own corresponding exact-version check.

This version rule is conservative across different package versions, but it is not an independent schema identity. Same-version commits exist. Repository policy and CI reduce risk by requiring version bumps around generated AST-reader changes, yet that policy is not a theorem that every semantically relevant producer change changes the package version.

For an upgrade, diff the envelope, AST/schema definitions, generated readers, and version machinery. Preserve representative LLBC specimens from fixed Rust inputs and decode them with the intended Aeneas consumer. If Anneal starts embedding `charon_lib`, separately compile/review that exact API edge. A Rust library consumer is coupled at compile time to public structs/modules/functions; a file consumer is coupled at run time to the serialized schema and version gate.

Basis: direct `export.rs`/`lib.rs` **source** and the published serialization/library-wire reports.

### 5. Diff the transformation pipeline as semantics, not implementation detail

Charon's output is not raw rustc MIR. The baseline transformation pipeline normalizes, resugars, simplifies, restructures control flow, optionally rewrites operations, and performs post-transformation checks. Several passes explicitly depend on ordering or on a precise rustc MIR shape. The Aeneas preset turns on a subset whose output is tailored to Aeneas's consumer.

That makes a Charon upgrade semantically wider than an LLBC parser/schema check. A new revision can emit the same schema while changing reconstructed asserts, fallible operations, indexing, associated-type representation, trait structure, constants, drops, intrinsics, or control-flow shape.

The efficient upgrade review is claim-specific. Diff the pass pipeline and the passes activated by the production options first. Then regenerate a compact LLBC corpus that exercises the changed regions. Review structural output diffs together with the source-level semantic obligation they represent. A textual change can be harmless; a byte-identical file can still coexist with a changed unsupported/failure boundary elsewhere.

Basis: direct transformation **source** plus the current Charon/Aeneas reference corpus.

### 6. Rebuild the support and fail-closed boundary

Charon deliberately supports best-effort extraction. At the baseline, translation code can register errors and continue. `CrateData::new` stores the resulting error state in `has_errors`. The driver then serializes `CrateData` before the final `error_on_warnings` check. With continuation enabled and the final strict option absent, an output file can therefore exist even though Charon encountered translation errors; the process can finish through the warning path rather than a hard Charon failure.

This behavior is not a defect by itself. It is a consumer contract. For Anneal, however, a proof about partial or placeholder LLBC cannot silently stand for a proof about the original Rust program. A Charon upgrade must recheck continuation, error registration, placeholder/error nodes, `has_errors`, serialization order, process exit classes, and the Aeneas reader's treatment of the envelope.

The support matrix is revision-sensitive as well. The baseline corpus records explicit failures and known/conditional hazards involving async/coroutines, quantified associated-type lifetimes, certain unsafe/rustc MIR constructs, trait-object/type forms, constant lowering, drops, layout, and external-body availability. The checklist does not assume that newer Charon support is monotonic. A formerly rejected construct becoming accepted is itself a semantic change requiring review.

A useful execution matrix includes one success, one warning/partial-result case, one explicit unsupported construct, one compiler failure, and one Charon panic/ICE discriminator. The result should record exit status, artifact existence, `has_errors`, and downstream Aeneas behavior.

Basis: direct export/driver **source** and the published support/unsoundness report.

### 7. Revalidate translation coverage and source identity together

Charon translates a semantic compiler program, not every source byte. Under the default `crate` start root it structurally explores the current crate, then follows semantic references. Foreign definitions enter according to reachability and opacity; external bodies additionally depend on whether rustc has MIR available. `cfg`, Cargo features, target selection, generated source, procedural macros, build scripts, and sysroot metadata all affect the compiler program presented to Charon.

An upgrade should therefore recheck start-root semantics, include/opaque/exclude behavior, dependency-body availability, target/cfg handling, and any production use of `--start-from`. A changed selector or opacity rule can narrow proof coverage without changing the syntax of the resulting LLBC.

Source correspondence is a second part of the same gate. The baseline corpus distinguishes Charon's typed semantic item IDs from its simplified human-readable names and records the exact file/span/location/comment structures used downstream. If Anneal diagnostics or proof annotations depend on these mappings, diff those structures and verify fixed fixtures still map to justified Rust locations. Do not infer identity from printed names alone.

Basis: published dependency/source-coverage, start-from, and item/span reports backed by pinned Charon **source**.

### 8. Recheck multi-target and multi-primary-unit behavior if the production path can encounter it

Charon's own `--targets` mode deliberately fans out translation per target and then merges the resulting crates. This is different from a single `charon cargo` invocation that causes Cargo to invoke `charon-driver` for multiple primary target units.

At the baseline, per-target fan-out gives each target a temporary output before merge. Multiple primary Cargo units, by contrast, inherit one Charon output policy. With an explicit shared destination, they can name the same output; without one, crate-name-derived paths can still collide when names coincide. The pinned source contains no general per-primary-unit aggregation protocol for that case.

If Anneal's production subject is guaranteed to produce one primary unit and one target, record that invariant and keep this gate narrow. Otherwise exercise the exact unit graph and destination policy. Cross-target merging also deserves a discriminating case where the same semantic item differs across targets, so a change in deduplication or synthetic dispatch cannot pass unnoticed.

Basis: published multi-target/multi-primary behavior report.

### 9. Pair the producer with the exact Aeneas consumer selected by the dependency graph

The baseline Aeneas source mechanically pins Charon `a535e914…`; its release packages the matching producer, and Aeneas consumes LLBC through Charon-generated OCaml definitions/readers. This is stronger evidence than matching release dates.

The same-date counterexample is instructive: Aeneas `nightly-2026.06.03` does not imply Charon `nightly-2026.06.03`. The latter names another Charon commit. The two exact commits happen to share the examined parser/schema blobs and version `0.1.210`, but that observation is revision-specific and cannot be promoted to a compatibility rule.

For an upgrade, use the Aeneas revision that actually selects the proposed Charon. Run representative LLBC through that exact Aeneas consumer. If Anneal has another Charon revision in its Rust dependency graph, either prove the edge remains non-executing or validate the active cross-revision boundary directly. Do not let a same package version suppress this check.

Basis: direct Aeneas pin/lock/release **source** plus the published Aeneas–Charon compatibility analysis.

### 10. Separate same-revision determinism from upgrade drift

Two different questions need different evidence:

1. Does one exact Charon build produce the same artifact repeatedly from the same effective compiler inputs and options?
2. Does a proposed new Charon revision produce an artifact that is compatible with the old one for Anneal's purposes?

The first matters to byte-addressed caches, reproducible archives, golden fixtures, and change detection. The second is a migration/interface question. A new revision can be perfectly deterministic while intentionally producing different LLBC.

This scheduled research surface did not run Charon, so it does not establish baseline byte determinism. If Anneal depends on it, repeat the production-mode extraction from a clean state, record effective environment and tool identities, and compare hashes and normalized semantic output. Then separately compare old and new revisions on the same fixture corpus.

Do not use a passing repeated-run test as proof of semantic equivalence, and do not treat every cross-version byte difference as a bug. Use the diff to locate the semantic review.

Basis: derived from the pinned source/corpus; the required determinism result itself remains **execution** evidence.

### 11. Validate the exact packaged runtime, not only a Charon checkout

Aeneas's release recipe copies the locked Charon binaries and Charon `rust-toolchain` into its release tree. Anneal then repackages toolchain components across Linux x86_64/aarch64 and macOS x86_64/aarch64 and supplies its own managed Rust environment.

A source-level compatibility review cannot establish that these binaries run after packaging and relocation. Charon's driver depends on the selected rustc-private runtime; host dynamic-library paths and the outer wrapper's toolchain-selection behavior matter. An upstream `--help`/`--version` smoke test is weaker than a real compiler extraction because it does not necessarily load or exercise the complete driver path.

For every host Anneal claims, run the exact artifact Anneal will install. Translate a small crate through the bundled `charon` and `charon-driver`, using the managed Rust sysroot and the same environment policy as production. Record the artifact hashes and host triple with the result.

Basis: Aeneas/Anneal packaging **source** plus the Charon toolchain/runtime report.

### 12. Finish with one integrated corpus that crosses the actual boundary

Component diffs narrow the risk; they do not prove the composition. The final acceptance gate should run a small corpus through the exact packaged Rust compiler, Charon producer, and Aeneas consumer that Anneal intends to use.

At minimum, preserve fixtures for:

- ordinary scalar/ADT control flow;
- shared and mutable borrowing;
- a raw-pointer or other unsafe operation that Anneal intends to support;
- a loop or recursion case;
- traits/associated types;
- a dependency/foreign-reference case;
- an expected Charon failure or partial-output discriminator.

For each fixture, preserve the Rust source and build configuration, rustc/Charon/Aeneas identities, effective Charon options, LLBC, diagnostics, output hashes, and downstream result. If a source review identified a changed pass or failure boundary, add a fixture that distinguishes that change rather than relying only on generic smoke tests.

Passing this corpus is still not a proof that Charon preserves all Rust semantics. It is integration/regression evidence around separately justified semantic and trust boundaries. Its purpose is to make accidental toolchain mismatches and changed operational contracts fail closed during an upgrade.

Basis: **derived** from the independent Charon boundaries above.

## Boundaries

- No newer Charon revision was selected or evaluated. This report defines revalidation gates; it does not approve an upgrade.
- No fresh Rust, Charon, Aeneas, Cargo, Nix, or packaged-toolchain execution was performed for this report.
- The report does not establish same-revision Charon byte determinism. That is an empirical property when Anneal relies on exact bytes.
- The report does not claim package version `0.1.210` is unsafe or insufficient by itself. It claims only that the version string is not a commit identity and cannot prove equivalence between same-version source revisions.
- The current same-version/same-date examples are exact historical evidence, not a claim that all nearby Charon revisions differ materially.
- The Aeneas preset values and transformation pipeline are revision-specific. A later redesign may replace them with a different contract; the checklist then requires semantic comparison rather than preserving option names mechanically.
- The support/failure inventory is known/documented coverage, not proof that every unlisted Rust feature is supported.
- The multi-primary-output concern applies only when a Cargo invocation can produce more than one selected primary unit under one Charon destination policy.
- The current source-correspondence structures can change legitimately. The required property is preservation or reviewed migration of Anneal's downstream assumptions, not byte-identical metadata.
- `charon_lib` and serialized LLBC remain separate compatibility surfaces. A future architecture may use one, both, or neither; apply only the gates corresponding to active edges.
- The machine-readable checklist is subordinate to current Anneal authority and the exact candidate dependency graph. It is not a frozen architecture decision.

## Evidence

**Direct Charon source.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `rust-toolchain` (`4e348eda…`) selects `nightly-2026-05-31` and lists rustc-private-support components and targets;
- `charon/Cargo.toml` (`8c993620…`) records version `0.1.210`, the `charon_lib`/`charon`/`charon-driver` target split, and the optional rustc-private feature boundary;
- `charon/src/options.rs` (`f08f8bae…`) defines `CliOpts` and the exact baseline `Preset::Aeneas` option set;
- `charon/src/transform/mod.rs` (`8d9ec016…`) defines the ordered transformation pipeline and pass predicates;
- `charon/src/export.rs` (`d5428958…`) defines `CrateData`, the exact package-version check, `has_errors`, and JSON/Postcard serialization;
- `charon/src/lib.rs` (`a5530a17…`) defines `VERSION` as `CARGO_PKG_VERSION` and exposes the library-side read/API surface;
- `charon/src/bin/charon-driver/main.rs` (`ab74f3f3…`) serializes the transformed crate before applying the optional final strict warning/error policy.

**Direct Aeneas source.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `charon-pin` (`06dbe0db…`) selects `a535e914…`;
- `flake.lock` (`d6862b6e…`) locks the same Charon input;
- `scripts/check-charon-install.sh` (`59507e54…`) checks an installed Charon against the expected source revision;
- `flake.nix` (`05e71549…`) builds the release using the locked Charon input and copies `charon`, `charon-driver`, and that input's `rust-toolchain` into the release;
- `src/Main.ml` (`b3f373f8…`) is part of the Aeneas-side LLBC consumer/configuration boundary.

**Direct Anneal source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix` (`433fcf5c…`), selects Aeneas `nightly-2026.06.03`, packages Rust `2026-05-31`, and constructs the multi-host toolchain environment used around the Aeneas/Charon release.

**Published exact-pin synthesis.** Current `google/zerocopy` `reference` at `e1ef8f81d5e12ea48c35023ef8da740ca9dbfd10` supplies the report evidence listed in `source-map.json`, including Charon toolchain coupling, serialization/API boundaries, CLI invocation modes, process/library architecture, Aeneas–Charon pin compatibility, support/failure behavior, source identity/spans, dependency coverage, multi-target behavior, wire/library compatibility, and start-root semantics.

**Derived checklist.** `upgrade-checklist.json` maps those independent boundaries into acceptance gates. The gate order is intentional: immutable identity and compiler coupling come first; option/schema/semantic/failure/source-coverage boundaries follow; consumer/package/determinism checks then establish the concrete composition; the final corpus verifies that the exact integrated path still works.

## Revalidation

For a proposed Charon upgrade, use `upgrade-checklist.json` as a per-candidate evidence record rather than copying the baseline conclusions forward.

A narrow efficient sequence is:

1. Resolve the proposed Aeneas and Charon commits, package version, Charon Rust toolchain, and concrete release/archive hashes. Stop if the dependency graph is internally inconsistent.
2. Diff `rust-toolchain`, `Cargo.toml`, `options.rs`, `transform/mod.rs`, `export.rs`, the AST/schema, generated Aeneas/OCaml readers, and the driver error/serialization path against the baseline.
3. Identify which changed facts can affect Anneal's supported Rust subset, proof/source-correspondence assumptions, or runtime packaging. Add focused checks for those changes instead of rerunning unrelated experiments blindly.
4. Build or obtain the exact producer/consumer artifacts Anneal will ship. Verify compiler/runtime identity in the packaged environment on every supported host.
5. Run fixed Rust inputs through old and proposed Charon revisions under the production-effective options. Preserve LLBC and diagnostics. Repeat the proposed revision when same-revision byte determinism matters.
6. Feed the proposed producer's LLBC to the exact Aeneas consumer selected by the new dependency graph. Include a known failure/partial-output case and confirm that Anneal's orchestration rejects it as promise input.
7. If `charon_lib` is active in the proposed Anneal architecture, separately compile and test that exact API edge. Do not infer in-memory compatibility from LLBC success.
8. Run the integrated corpus through the exact installed/relocated artifact. Preserve input, tool identities, effective options, outputs, diagnostics, and hashes as upgrade evidence.
9. Review every checklist gate as pass, intentional reviewed change, inapplicable with justification, or blocker. Do not treat an unchecked empirical gate as satisfied by source inspection.

For future baseline refreshes, update this report only when the exact selected Charon/Aeneas/Anneal identities or one of the material contracts above changes. A new package version or commit should normally receive a new precisely identified report rather than silently mutating the evidence for this subject.