# Charon dependency extraction and source coverage at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), Charon does not import Cargo dependencies wholesale into LLBC. Cargo supplies the selected crate's rustc invocation and compiled dependency metadata; Charon then starts from configured semantic entry points and recursively enqueues definitions that translation actually reaches. Under the default `crate` entry point, Charon traverses the current crate's transparent module tree, so the selected crate is covered structurally rather than only along its runtime call graph. Definitions in other crates enter when a translated item refers to them, when an explicitly selected foreign start pattern reaches them, or when translation of required type/trait/signature structure registers them.

The same rule applies whether an external crate came from crates.io, a path dependency, a Git dependency, or the Rust sysroot. Charon's serialized item metadata distinguishes **local crate** from **foreign crate**, and names/files retain crate and source-path information, but Charon does not attach Cargo's package-source category as an inclusion policy. Registry/path/Git origin is therefore not an extraction class in the Charon semantic model. What matters for reachability is compiler identity and semantic reference; what matters for extraction depth is the item's opacity and the compiler information available for that nonlocal definition.

Foreign items default to `ItemOpacity::Foreign`. For functions and most non-type items this is body-opaque: Charon retains enough declaration/signature structure for references but does not normally translate the implementation. Foreign types are intentionally different: public enums and structs with all-public fields may be translated structurally, while private representation remains hidden. `--include` or `--extract-opaque-bodies` can request deeper foreign translation, but a request is not a guarantee that rustc has a body available.

MIR availability creates the main standard-library/dependency asymmetry. Charon configures rustc with `-Zalways-encode-mir`, so dependencies compiled as part of the Cargo build can expose more MIR through metadata. The pinned source explicitly says this does not make arbitrary standard-library MIR available: nonlocal functions generally use optimized MIR only when rustc reports it available, while relevant constants/statics/const functions may use CTFE MIR. Thus “reachable foreign definition” and “foreign body available for translation” are separate facts.

“Whole crate” has a similarly precise boundary. With default entry point `crate` and normal transparency, Charon traverses the current crate's module/inherent-impl structure and recursively processes registerable item definitions, including nested compiler definitions that its traversal discovers. But Charon begins after Rust parsing, configuration, name resolution, and macro expansion, and normally extracts promoted MIR. Source removed by `cfg`, syntax that expanded into different definitions, or distinctions already erased by rustc are not recoverable merely because the selected root is the whole crate. At the MIR boundary, rustc and Charon also remove disconnected control-flow blocks. Conversely, build-script-generated Rust that rustc actually consumes and procedural-macro-generated target syntax are part of the selected target crate after expansion and can be covered like equivalent handwritten Rust, subject to ordinary Charon support and reachability rules.

No fresh Cargo, rustc, or Charon execution was performed. The report uses the exact pinned Charon source and checked-in tests, plus existing reference reports that separately establish the rustc preprocessing and generated-source boundaries. It establishes the source-defined inclusion and coverage model; it does not empirically measure completeness on arbitrary workspaces or prove that every Rust construct Charon attempts to translate is translated soundly.

## Applicability

This report applies to:

- Charon repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon version `0.1.210`;
- embedded Rust toolchain `nightly-2026-05-31`.

It concerns two tightly coupled #3720 subjects:

- **Charon dependency extraction** — which local and foreign definitions enter a translation and how external-crate source kind affects that decision;
- **Charon source-code coverage** — what Charon's default “whole crate” entry point does and does not cover once rustc preprocessing and Charon's own reachability rules are taken into account.

Cargo's package-resolution rules and exact compilation-unit construction are covered by the existing Cargo reports. This report begins at Charon's rustc-driver boundary and asks which compiler definitions become Charon items.

“Foreign” means “not in the rustc local crate” at this extraction boundary. It is not synonymous with FFI. A crates.io package, path dependency, Git dependency, `core`, `alloc`, and `std` are all foreign crates when the selected target crate is translated. Rust `extern { ... }` declarations are a separate language construct and are covered by the existing FFI report.

The report assumes the default non-monomorphizing mode unless a finding explicitly discusses another option. `--start-from`, `--opaque`, and related selection controls are described in dedicated companion reports and are used here only to explain how they alter the default coverage boundary.

## Findings

### Cargo supplies dependency compilation; Charon does not reconstruct the dependency graph

In Cargo mode, Charon installs `charon-driver` as `RUSTC_WRAPPER`. Cargo constructs the build graph and rustc command lines, including the `--extern` arguments and compiled metadata paths for dependencies. The wrapper compiles dependency and host-side units normally and translates the selected target-side primary unit.

The selected rustc process therefore already has rustc's view of the crates available to the target. Charon does not separately walk Cargo's package graph and copy each package into LLBC.

Basis: pinned Charon **source** plus the existing architecture report.

### Default translation starts from the current crate, not from every dependency crate

`TranslateOptions::new` inserts a strict `crate` start pattern when no other start selector is configured. `translate_crate` resolves that root and calls `enqueue_module_item`.

The crate root is a transparent local module by default. Translating a transparent module enqueues its contained definitions. Transparent submodules and inherent-impl containers similarly enqueue their members. This structural traversal is why Charon's ordinary default is meaningfully “the whole current crate” rather than “functions reachable from `main`.”

Basis: Charon **source** and upstream **documentation**.

### New foreign items are pulled in by semantic references

Charon's translation queue is recursive. `register_and_enqueue` gives a referenced definition a Charon item ID and queues its `TransItemSource`; the main translation loop continues until no queued items remain. The source explicitly describes this as translating referenced, potentially external items.

References arise from more than call expressions. Translating signatures, types, trait references, impl relationships, constants, globals, associated items, vtables, and other semantic structure can register additional definitions. Consequently, the foreign closure is a semantic dependency closure, not merely a runtime function-call graph.

Basis: Charon **source**.

### Unused dependency crates and unused foreign definitions are not included merely because Cargo built them

Because Charon begins from semantic roots and adds foreign items through encountered references, a Cargo dependency's presence in the rustc compilation environment does not itself enqueue that crate root or every definition in the dependency.

An otherwise unused dependency may therefore contribute no ordinary Charon declarations. Likewise, one referenced function from a dependency does not imply that unrelated functions in the same dependency are translated.

This is a **derived** consequence of the work-queue algorithm and default root. It is not an empirical claim that Cargo never injects compiler-visible references for other reasons; such compiler-injected references, if encountered by Charon, participate in the same semantic rule.

Basis: Charon **source** + **derived** consequence.

### Cargo source kind is not a Charon extraction category

At this boundary, Charon records whether an item is local to the selected rustc crate and gives it a structured Rust name. `ItemMeta.is_local` is computed from the compiler definition's locality. It does not encode “registry dependency,” “path dependency,” or “Git dependency.”

File records carry a crate name and normalized source filename, which can preserve useful provenance. Charon normalizes sysroot paths and paths beneath Cargo home to reduce machine-specific differences. Those paths can help identify where source came from, but they do not turn Cargo source kind into a reachability rule.

Thus local/path/registry/Git distinctions belong primarily to Cargo/package provenance. Once rustc presents a nonlocal definition to Charon, Charon's selection logic treats it as a foreign definition under the same reachability and opacity machinery.

Basis: Charon **source** + **derived** boundary distinction.

### Explicit foreign roots are possible

The `--start-from` resolver searches the local crate and external crates known to rustc. Pinned tests successfully use standard-library roots such as `std::iter::once`, trait methods, and primitive-type methods.

An external definition can therefore become an entry point even when the current crate does not otherwise refer to it. This changes reachability, but opacity still controls how deeply Charon translates that root.

Basis: Charon **source** + checked-in **execution** fixture.

### Foreign definitions default to the `Foreign` opacity class

The default opacity table starts with `_ → Foreign` and then makes the current `crate` transparent. As a result, definitions outside the selected crate normally remain `Foreign` unless a more precise include/opaque/exclude pattern applies.

For functions and globals, `Foreign` is effectively body-opaque. Charon retains the declaration/signature needed by local references without normally importing the implementation.

This keeps the translated foreign closure narrower than a source-level clone of every dependency implementation.

Basis: Charon **source** + upstream **documentation**.

### Foreign types deliberately preserve more structure when Rust visibility permits it

`Foreign` is not identical to `Opaque` for ADTs. Charon's `ItemOpacity` contract allows structural translation of an external enum and of an external struct whose relevant fields are public. Private representation is not exposed merely because the type is referenced.

This matters for downstream type reasoning: a dependency can contribute concrete variant/field structure even while its functions remain body-opaque.

Basis: Charon **source**.

### Requesting a foreign body and having a foreign body are separate conditions

`--include` or `--extract-opaque-bodies` can make a foreign definition transparent from Charon's policy perspective. That only asks Charon to translate the contents; the compiler must still provide those contents.

`get_mir.rs` explicitly handles nonlocal bodies by returning `None` when MIR is unavailable. A body requested through a permissive opacity policy therefore does not create MIR that rustc did not encode.

Basis: Charon **source**.

### Charon asks rustc to encode MIR for dependencies it compiles

The driver sets `always_encode_mir = true` on wrapped rustc compilations. Charon's MIR-loading source explains the consequence: this makes MIR available for more dependencies that Charon/Cargo compiled as part of the build.

For a nonlocal ordinary function, Charon uses optimized MIR when rustc reports that MIR is available. Nonlocal bodies do not have the same menu of early MIR levels as local definitions.

Basis: Charon **source**.

### The standard library has a narrower body-availability boundary

The same source explicitly says `always_encode_mir` does not apply retroactively to the prebuilt standard library. Charon generally sees standard-library MIR only where the distributed metadata contains it—for example relevant const bodies and generic/inlineable functions.

Standard-library items can still be registered and represented as foreign declarations/signatures/types. But requesting transparency for an arbitrary non-generic std function does not establish that its MIR is present.

This is the important practical difference between ordinary Cargo-built dependencies and the sysroot: not a different reachability algorithm, but different available compiler artifacts.

Basis: Charon **source**.

### Path and registry dependencies share the same semantic inclusion rule

A path dependency and a crates.io dependency may have different filesystem/package provenance, but both are external rustc crates when translating the selected target. If the current crate refers to an item from either, Charon can register the foreign definition; if no semantic path reaches it, Cargo provenance alone does not include it.

The same statement applies to Git dependencies. This report found no pinned Charon source branch in the extraction algorithm that changes reachability according to Cargo source kind.

Basis: **source** + **derived** absence-of-distinction claim scoped to the inspected extraction code.

### “Whole current crate” is structural coverage, not source-text coverage

With default `crate` root and transparent local modules, Charon structurally explores current-crate items even if no runtime call reaches them. That includes local module contents and definitions discovered under item containers according to Charon's supported item taxonomy.

But this boundary begins after rustc has parsed, configured, expanded, resolved, type-checked, and lowered the program far enough for Charon's `after_expansion` extraction path. There is no promise that every byte or source syntax node maps to a Charon item.

Basis: Charon **source** + existing rustc pipeline report.

### `cfg`-excluded code is outside the selected compiler program

Rust conditional compilation removes disabled constructs before Charon's extraction. A default whole-crate root cannot recover a definition that rustc excluded from the configured crate.

Coverage must therefore be parameterized by the exact Cargo/rustc configuration—features, target, cfg values, generated environment, and selected compilation subject. “Whole crate” means the configured compiler crate, not every branch of source text under every possible build configuration.

Basis: existing corpus **normative/source** evidence + **derived** implication for Charon.

### Procedural-macro output is inside the target crate; the proc-macro implementation is not

Procedural macro output is expanded into target-crate syntax before Charon's callback. Generated target items and operations can therefore enter Charon's ordinary local-item traversal and MIR translation.

The proc-macro crate itself is a host-side dependency compiled normally by the Cargo wrapper. Its implementation is not part of the selected target crate's default Charon output.

Basis: existing generated-Rust report + Charon driver **source**.

### Build-script-generated source is included only if rustc actually consumes it

A build script is likewise a separate host program. Files written to `OUT_DIR` are not automatically Charon input. When target Rust includes or modules in generated source, rustc parses that source into the selected target crate; surviving generated items then participate in Charon's normal local coverage.

Native libraries, linker scripts, environment effects, and other non-Rust build-script products do not become Rust MIR merely because they affect the build.

Basis: existing generated-Rust report + **derived** Charon boundary.

### Local nested definitions are not limited to externally nameable module paths

Rust permits nested items, closures, anonymous consts, and compiler-synthesized definitions. The existing local-item report establishes that compiler identity extends below ordinary source paths.

The pinned Charon fixtures also preserve nested-item extraction under module/function roots. Charon's compiler-derived traversal is therefore broader than a source scan of canonical Rust paths. Exact coverage still depends on the particular item kind being registerable and supported.

Basis: existing corpus evidence + checked-in Charon **execution** fixture.

### MIR/control-flow reachability is a second, lower-level coverage boundary

Even when a function item itself is covered, not every source operation necessarily survives into its extracted MIR. The existing MIR report establishes that rustc removes disconnected MIR blocks before Charon's default promoted-MIR extraction, Charon traverses MIR blocks from `START_BLOCK`, and later Charon transformations can remove newly inaccessible blocks.

Therefore “function present in LLBC” is not equivalent to “every syntactic operation in that function's source is represented.” Coverage claims must name both item coverage and the semantics of the selected compiler representation.

Basis: existing corpus **source/derived** evidence.

### Opacity can deliberately create source-coverage holes

An opaque local function remains represented by its signature but not its body. An opaque module stops structural traversal of its contents, although an independently referenced child can still be reached according to that child's own opacity.

A custom `--start-from` similarly narrows entry-point coverage. The default whole-crate statement therefore applies only under the corresponding default selection/opacity policy; CLI/source filters can deliberately choose a smaller theorem domain.

Basis: companion Charon start/opacity reports.

### Unsupported or failed extraction is not successful coverage

The pinned Charon failure report establishes that translation can reject unsupported constructs, panic/catch an extraction failure, or emit partial output marked with `has_errors` depending on error policy. A serialized item set is not evidence of complete semantic coverage if errors occurred.

For Anneal, a coverage claim must therefore pair the selected semantic domain with fail-closed handling of Charon's error/partial-output signals.

Basis: existing Charon failure report + **derived** implication.

## Boundaries

- No fresh Cargo, rustc, Charon, or LLBC execution was performed.
- The report does not enumerate a large real workspace to empirically prove that every dependency source kind behaves identically. The source-level claim is narrower: the inspected Charon inclusion algorithm branches on compiler locality, references, opacity, item kind, and MIR availability, not Cargo registry/path/Git source kind.
- Cargo feature/target/package resolution is not re-derived here; the existing Cargo reports define the configured compilation subject that reaches Charon.
- “Whole current crate” does not mean every possible cfg configuration, every source byte, every historical macro input, every host build program, or every native linked artifact.
- The report does not claim that every local Rust item kind is supported by Charon. The support/unsoundness report records pinned unsupported cases.
- The report does not claim that every foreign item body can be recovered with `--include` or `--extract-opaque-bodies`; compiler metadata availability remains a hard boundary.
- The report does not claim that path normalization is a stable package-source identity mechanism.
- The report does not prove semantic correctness of translated dependency bodies or structures.
- Performance/scaling of very large dependency closures remains empirical and is not established here.
- Multi-target aggregation can union per-target translated state; that separate behavior is covered by the existing multi-target report.

## Evidence

**Primary Charon subject:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`: crate root initialization; item registration/enqueueing; dependency-source bookkeeping; recursive translation queue.
- `charon/src/bin/charon-driver/translate/translate_items.rs`, blob `7964644be017856c6d165545a67bd6ef06e0c85c`: transparent module/inherent-impl/foreign-module traversal; foreign/opaque type handling; item translation behavior.
- `charon/src/bin/charon-driver/translate/get_mir.rs`, blob `a1cd9ba131a1362dda55e85c25f29f4a9e28df69`: local versus nonlocal MIR loading, optimized-MIR availability, CTFE fallback, and the explicit standard-library limitation.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`: `always_encode_mir`, MIR extraction options, and selected-crate wrapper boundary.
- `charon/src/bin/charon-driver/translate/resolve_path.rs`, blob `b091bf23f897cee6b84e0136b41426a7de9d91f2`: resolution across local/external rustc crates and the special `crate` local alias.
- `charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`: `is_local`; file crate-name/source-path registration and normalization.
- `charon/src/ast/meta.rs`, blob `7a80a92ea1b3f3eaff1758554001e32019473237`: `ItemOpacity`, `ItemMeta.is_local`, file metadata.
- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: default `crate` start point and foreign/current-crate opacity policy.
- `docs/what_charon_translates.md`, blob `780949ef1304a89e34c87b04958d65dbc3bf0810`: upstream description of entry points, dependency-driven selection, foreign opacity, and reachability.
- `charon/tests/cargo/dependencies/src/main.rs`, blob `ab7719b680082503d0bc6df9079fe71cff9f6461`, and its manifest blob `4fc7413db8afca5528ce3a2b53d6e0b54758d505`: checked-in Cargo dependency fixture.
- `charon/tests/ui/filtering/inner-items.rs` and `.out` (documented in the local/nested-items and start-from reports): preserved execution evidence that nested definitions can appear under selected roots.

**Existing reference synthesis used rather than repeated:**

- `charon-ullbc-llbc-schema-nightly-2026-06-03/ARCHITECTURE.md`: Cargo-wrapper/rustc-driver boundary.
- `charon-start-from-nightly-2026-06-03`: entry-point reachability.
- `charon-opaque-nightly-2026-06-03`: opacity semantics.
- `charon-support-and-unsoundness-nightly-2026-06-03`: support/failure boundaries.
- `rustc-mir-before-charon-nightly-2026-05-31`: MIR phase and CFG reachability boundary.
- `generated-rust-visibility-nightly-2026-05-31`: build-script/proc-macro generated target Rust.
- `rust-local-nested-items-nightly-2026-05-31`: compiler identity below canonical source paths.
- Cargo compilation-subject/unit-graph/feature-resolution reports: configured Cargo domain.

No evidence gathered in this report is fresh **execution**. Checked-in `.out` and test fixtures are upstream preserved execution/test evidence with the provenance stated above.

## Revalidation

For a future Charon revision, first diff these source seams:

1. default `start_from` and opacity construction in `options.rs`;
2. `enqueue_module_item`, `register_and_enqueue`, and the main work queue in `translate_crate.rs`;
3. module/type/function foreign handling in `translate_items.rs`;
4. local/nonlocal MIR queries in `get_mir.rs` and rustc MIR flags in `driver.rs`;
5. external-crate resolution in `resolve_path.rs`;
6. `ItemMeta.is_local` and file provenance in `translate_meta.rs`/`ast/meta.rs`.

On a capable execution surface, use a small Cargo workspace with one root package plus:

- one crates.io dependency;
- one path dependency;
- one Git dependency or a second path dependency standing in for source-kind comparison if network-free reproducibility is required;
- one completely unused dependency;
- one dependency with two functions where only one is referenced;
- one public external enum, one all-public struct, and one struct with a private field;
- calls/references to `core`/`std` generic/inlineable and ordinary non-generic functions;
- generated Rust via `build.rs` + `include!` and a proc-macro-generated local function;
- a cfg-disabled local item and an unreachable local function.

Preserve Cargo's verbose rustc invocations, exact package/source identities, Charon options, final ULLBC/LLBC, and error output. Compare default translation with `--include`/`--extract-opaque-bodies` and with explicit foreign `--start-from` roots.

The discriminator should confirm:

- unused packages do not appear merely because they are in Cargo's resolved graph;
- only semantically reached foreign definitions/structure enter by default;
- registry/path/Git source kind does not change Charon reachability for otherwise equivalent compiler references;
- public foreign ADT structure versus private representation follows `Foreign` policy;
- ordinary Cargo-built dependency MIR is more available than arbitrary prebuilt std MIR;
- generated target Rust is covered while generator implementations remain host-side;
- cfg-excluded code remains absent;
- Charon error/partial-output state is handled separately from nominal item presence.

That probe would empirically confirm these rules for the exact tested workspace and toolchain. It would not establish performance at ecosystem scale or semantic correctness of each translation.
