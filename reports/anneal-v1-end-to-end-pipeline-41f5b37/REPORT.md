# Anneal V1 end-to-end verification pipeline

## Summary

Retained Anneal V1 is a staged Rust-to-Lean verification pipeline with two distinct views of the input program. Anneal first resolves Cargo packages and targets and scans Rust source for inline `anneal` annotations. That scan supplies the annotated items, source spans, and Charon entry points. Charon then compiles the selected target through Rust MIR and emits one LLBC file per selected annotated target; Aeneas translates that LLBC into Lean definitions; Anneal separately turns the scanned annotations into Lean specifications and proofs that import the Aeneas-generated definitions; Lake prepares the generated project; and `lean --json` checks each Anneal specification file. Lean diagnostics are mapped through Anneal-generated sidecar mappings back to the original Rust source.

The implementation spine is `prepare_and_run` in `anneal/v1/src/main.rs`:

```text
Cargo resolve
    ↓
Anneal source scan ───────────────┐
    ↓                             │ annotations + source spans
run-wide output lock              │
    ↓                             │
Anneal structural validation      │
    ↓                             │
Charon / rustc → LLBC             │
    ↓                             │
Aeneas → Lean functional model    │
    ↓                             │
Anneal annotation generation ◀────┘
    ↓
Lake dependency/model build
    ↓
Lean JSON check of Anneal specs
    ↓
map generated-Lean diagnostics back to Rust
```

`verify`, `generate`, and `expand` share almost all of that prefix. `verify` continues through the Lean checks; `generate` materializes the Lean workspace without the final verification build/check; `expand` prints Aeneas and Anneal generated Lean after extraction/translation. `setup` is separate: it installs or resolves the omnibus toolchain containing the Charon/Aeneas/Rust/Lean inputs that the pipeline consumes.

For the checklist phrase “final useful revision,” this report uses the current retained V1 implementation at `41f5b37afe7060fd9fe08c00b200672cd76d77b9`. This is a stronger reproducible coordinate than guessing a pre-V2 historical point. The core verification files inspected here (`main.rs`, `resolve.rs`, `scanner.rs`, `charon.rs`, `aeneas.rs`, `generate.rs`, and `diagnostics.rs`) are the retained V1 implementation moved under `anneal/v1` by the V1/V2 reorganization commit `dbb81cc7759bb6b21b82a1ca98bb32e9676f8655`; the current README now explicitly marks the subtree as historical rather than current Anneal design authority. The report is therefore about the final retained V1 pipeline, not current V2 architecture.

## Applicability

The primary source identity is `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, under `anneal/v1`. The package manifest identifies this retained implementation as `cargo-anneal` `0.1.0-alpha.24`. Its build metadata pins Aeneas revision `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` and Lean `leanprover/lean4:v4.30.0-rc2`. Tool installation is mediated by Exocrate; the verification code resolves the installed Charon, Aeneas, Rust, and Lean paths from that installation.

The report reconstructs the normal command/data path implemented by source. It does not claim that every combination of Cargo flags, Rust features, target kinds, unsupported Charon constructs, Aeneas translations, or Lean proofs succeeds. The scanner is explicitly CFG-agnostic, and the pipeline has numerous fail-closed checks described below.

The V1/V2 reorganization commit `dbb81cc...` is used only to establish the historical status boundary: the V1 implementation was moved under `anneal/v1`. Current `anneal/v1/README.md` was later annotated to say that V1 is historical and is not current project design authority. Current behavior claims in this report are bound to `41f5b37...`, not inferred from the older commit message.

Basis: **source** at `41f5b37...` plus **source history** at `dbb81cc...` and the current V1 status marker.

## Findings

### `prepare_and_run` is the common pipeline spine

`main.rs` implements four user-visible subcommands: `verify`, `setup`, `expand`, and `generate`. `verify`, `expand`, and `generate` all enter `prepare_and_run`.

`prepare_and_run` performs, in order:

1. `resolve::resolve_roots` — resolve Cargo workspace/package/target selection;
2. `scanner::scan_workspace` — scan selected source trees for Anneal annotations and compute Charon `start_from` roots;
3. return early if no annotated artifact exists;
4. `roots.lock_run_root()` — acquire exclusive access to the workspace-specific Anneal output root;
5. `validate::validate_artifacts` — reject malformed/forbidden annotation structures before translation;
6. `charon::run_charon` — compile/extract LLBC;
7. `aeneas::run_aeneas` — translate LLBC and prepare the Lean project; and
8. invoke the subcommand-specific callback.

This ordering matters. In particular, Anneal's source scanner runs before Charon, while Anneal's generated Lean specification file is produced only after Charon and Aeneas have completed. The V1 agent documentation describes “Specification Generation” as occurring “in parallel” with Aeneas at a conceptual level, but the inspected implementation executes these stages sequentially. A future reconstruction should follow the source ordering when diagnosing files, locks, or failure propagation.

Basis: **source**, `anneal/v1/src/main.rs`, `main` and `prepare_and_run`; **documentation** comparison with `docs/agent/01_philosophy_and_pipeline.md`.

### Cargo resolution determines concrete compilation artifacts before source scanning

`resolve_roots` invokes `cargo metadata`, forwards feature-resolution flags, resolves selected workspace packages, and flattens Cargo targets into explicit `AnnealTarget` values. It supports library-like targets, binaries, examples, and tests; build scripts and benches are not selected as verification roots by this resolver.

Each target records an absolute source path and manifest path. Default selection includes library-like and binary targets for the current package, while explicit `--lib`, `--bin`, `--bins`, `--example`, `--examples`, `--test`, and `--tests` alter selection. External selected packages outside the Cargo workspace root are rejected.

Anneal derives two filesystem domains from Cargo's target directory:

```text
<target>/anneal/cargo_target/
    shared Cargo dependency-build output used by Charon invocations

<target>/anneal/<workspace-root-hash>/
    workspace-specific Anneal run root, protected by an exclusive directory lock
```

The run root contains the LLBC and generated Lean trees. The stable workspace-root hash prevents unrelated workspaces sharing a target directory from colliding, while the global `cargo_target` directory intentionally permits dependency build reuse across runs.

Basis: **source**, `anneal/v1/src/resolve.rs`, `Roots`, `LockedRoots`, `resolve_roots`, and `resolve_run_roots`.

### The source scanner supplies annotations and Charon roots; it is not the Rust compiler

`scanner::scan_workspace` recursively reads the selected target's Rust source and identifies Anneal-annotated items. It returns an `AnnealArtifact` per target containing:

- the package/target identity;
- the target kind and manifest path;
- parsed annotated items with source locations; and
- a deduplicated set of `start_from` strings for Charon.

For items whose fully qualified name is considered reliable, the scanner uses the exact item path as a Charon start root. For impl/trait/foreign contexts where naming is not reliable, it falls back to the containing module, deliberately widening Charon's extraction scope.

The scanner is not a second Rust front end. Its own comments state that it is CFG-agnostic: it may inspect a file or declaration that the selected Rust configuration does not compile, and it can skip source files that do not exist because they might be cfg-gated. Charon/rustc later sees the actual Cargo target and feature selection. This creates an important V1 correspondence boundary: the scanner supplies annotation intent and source spans; Charon supplies compiler-derived program structure.

Basis: **source**, `anneal/v1/src/scanner.rs`, `AnnealArtifact`, `scan_workspace`, and `process_file_recursive`.

### Artifact slugs connect the scanner, LLBC, Aeneas output, Anneal output, and Lake modules

Each `AnnealArtifact` derives a Lean-compatible slug from the package name, target name, target kind, and a stable SHA-256-derived hash that includes the manifest path. V1 uses this slug consistently across stages:

```text
llbc/<Slug>.llbc
lean/generated/<Slug>/Funs.lean
lean/generated/<Slug>/Types.lean
lean/generated/<Slug>/FunsExternal.lean        (when needed)
lean/generated/<Slug>/TypesExternal.lean       (when needed)
lean/generated/<Slug>/<Slug>.lean              Anneal specification/proof file
lean/generated/<Slug>/<Slug>.lean.map          Rust↔generated-Lean source map
```

The manifest-path component avoids collisions between packages or targets that otherwise share names. The target-kind component also distinguishes different compilation modes for the same Cargo target name.

Basis: **source**, `anneal/v1/src/scanner.rs`, `AnnealArtifact::artifact_slug`, `llbc_file_name`, and `lean_spec_file_name`; **source** consumers in `charon.rs` and `aeneas.rs`.

### Charon is invoked as the compiler-derived extraction stage

For each annotated artifact, V1 invokes the installed Charon with its managed Rust toolchain placed first in `PATH` and the corresponding Rust libraries in the host dynamic-library path. The constructed operation is equivalent to:

```text
charon cargo
  --preset=aeneas
  --dest-file <run-root>/llbc/<Slug>.llbc
  --abort-on-error
  [--opaque <item> ...]
  --start-from <sorted,comma-separated-roots>
  --
  --message-format=json
  --manifest-path <artifact Cargo.toml>
  <target selector>
  <feature flags>
```

`CARGO_TARGET_DIR` points at Anneal's shared global Cargo target directory.

Annotated functions using V1's `unsafe(axiom)` mode are passed to Charon as `--opaque` items. This is the extraction-side half of V1's axiom mechanism: Aeneas will see an external/opaque function rather than translating its Rust body. The detailed soundness meaning of `unsafe(axiom)` is a separate report subject.

The `--start-from` roots are sorted for deterministic argument ordering. V1 explicitly caps the joined start-root argument at 32,768 bytes and fails rather than relying on platform command-line limits beyond that point.

Charon stdout is parsed as Cargo JSON messages. Compiler errors/ICEs are rendered through Anneal's diagnostic mapper. Unstructured stderr is drained concurrently so unexpected Charon failure can still be surfaced. Any structured error or unsuccessful process exit aborts the pipeline.

Basis: **source**, `anneal/v1/src/charon.rs`, `run_charon`.

### Aeneas consumes LLBC and materializes the functional Lean model

`run_aeneas` stages the Lean project in a temporary sibling directory before replacing the live generated workspace. For each annotated artifact it invokes Aeneas approximately as:

```text
aeneas
  -backend lean
  -dest <temporary-lean>/generated/<Slug>
  -split-files
  -abort-on-error
  <run-root>/llbc/<Slug>.llbc
```

The expected Aeneas outputs include `Funs.lean` and `Types.lean`, plus external templates when Charon marked functions/types opaque. V1 fails if an artifact that contains functions or types should have produced the corresponding Aeneas file but did not. When no such items exist, it can create an empty placeholder so later imports remain structurally valid.

V1 then applies compatibility patches to Aeneas output. It wraps `Funs.lean` in a `noncomputable section` and renames one Lean keyword collision; it also rewrites the generated discriminant attribute form in `Types.lean`. When Aeneas emits `FunsExternal_Template.lean` or `TypesExternal_Template.lean`, Anneal copies the template to the active external file if no active file exists.

This means the Lean model consumed by V1 is not simply untouched Aeneas output. The end-to-end subject includes Anneal's post-translation patching and external-file materialization.

Basis: **source**, `anneal/v1/src/aeneas.rs`, `run_aeneas`, `patch_funs`, and `patch_discriminants`.

### The generated Lean project separates installed dependencies from workspace-owned verification files

After per-artifact Aeneas translation, V1 writes:

- `anneal/Config.lean`;
- `anneal/Anneal.lean` (the Anneal Lean prelude);
- `lean-toolchain`;
- `lakefile.lean`; and
- a generated root `lake-manifest.json`.

The Lakefile requires Aeneas directly from the installed toolchain archive and declares separate Lean libraries for generated model modules and Anneal support code. The generated root manifest imports Aeneas and the dependency closure described by Aeneas's own manifest as path dependencies relative to the final generated workspace.

Once generation succeeds, V1 replaces the existing Lean workspace with the staged one. On reruns it preserves the old workspace's `.lake` directory by moving it into the staged workspace before the swap. The code comments correctly qualify this as not strictly atomic: if an old directory exists, it is removed before the staged directory is renamed into place.

The clean-workspace/read-only-archive and Lake-cache semantics are deep enough to have their own reference reports. For end-to-end pipeline purposes, the key fact is that Aeneas model generation also prepares the complete Lake project in which Anneal's own proof files will later be checked.

Basis: **source**, `anneal/v1/src/aeneas.rs`, `run_aeneas`, `generated_lake_manifest`, and `write_lake_manifest`; adjacent corpus coverage for archive/cache details.

### Anneal's own generated Lean is produced from the earlier source scan

The subcommand callback runs only after `run_aeneas` has prepared the model workspace. `generate_lean_workspace` walks the same scanned `AnnealArtifact` values and calls `generate::generate_artifact` for each annotated target.

The generated specification file imports:

```text
Anneal
Aeneas.Std.Scalar.Core
<Slug>.Funs
<Slug>.Types
```

and then emits Lean structures/theorems/axioms derived from the inline Rust annotations. It also invokes `inject_builtins`, opens Aeneas namespaces, and enters a noncomputable section. The detailed specification ABI and known V1 soundness limitations are separate subjects.

For each generated specification file, V1 also serializes a `.lean.map` sidecar containing mappings from generated-Lean byte ranges to original Rust source byte ranges. It writes a top-level `Generated.lean` that imports the generated model modules and any external modules.

This is where V1 joins its two earlier views of the program: Aeneas definitions came from Charon's compiler-derived LLBC; Anneal specifications and source mappings came from the independent source scan. The generated Anneal file imports the Aeneas definitions and states/proves claims about them.

Basis: **source**, `anneal/v1/src/aeneas.rs`, `generate_lean_workspace`; `anneal/v1/src/generate.rs`, `generate_artifact` and the mapping-producing builder.

### `verify` checks dependencies/models first, then checks each Anneal spec directly

`verify_lean_workspace` first calls `generate_lean_workspace`, then `run_lake`.

The first Lean command is:

```text
lake --keep-toolchain --old build Generated Anneal
```

This prepares/builds the generated model and Anneal support libraries. V1 then checks each Anneal-generated `<Slug>.lean` individually using:

```text
lake --keep-toolchain env lean --json generated/<Slug>/<Slug>.lean
```

The direct `lean --json` phase is the decisive proof-checking pass for the user specifications. V1 parses JSON diagnostics, resolves line/column positions to generated-file byte offsets, maps those byte spans through `<Slug>.lean.map`, and renders resulting diagnostics against the original Rust source. Any error-severity diagnostic makes verification fail.

Thus a successful `cargo anneal verify` means this staged pipeline reached the Lean checks without any stage declaring failure. It does not mean that V1 executed the verified Rust program, nor does it independently establish that Charon/Aeneas/Anneal's translations are sound. Those are trust/correctness questions beyond pipeline topology.

Basis: **source**, `anneal/v1/src/aeneas.rs`, `verify_lean_workspace`, `run_lake`, `resolve_mapping`; `anneal/v1/src/diagnostics.rs`, `DiagnosticMapper`.

### `generate` and `expand` are inspection cuts through the same pipeline

`cargo anneal generate` runs resolution, scanning, validation, Charon, and Aeneas just like `verify`, then generates the Anneal specification files and source maps without invoking `run_lake`. It prints the generated Lean workspace path and a suggested manual Lake build command. It is therefore an inspection/debugging cut immediately before verification.

`cargo anneal expand` also runs the common prefix through Aeneas. Its callback prints existing Aeneas-generated Lean (`Types.lean`, `TypesExternal.lean`, `Funs.lean`, and `FunsExternal.lean` when present) and/or freshly generated Anneal code according to `--emit`. It does not perform the final Lean proof check.

These commands are useful when reconstructing a failure: `expand` exposes the translation/generation text; `generate` preserves the complete workspace suitable for manual Lean iteration; `verify` adds the actual automated proof-checking phase.

Basis: **source**, `anneal/v1/src/main.rs`, command dispatch; `anneal/v1/src/aeneas.rs`, `generate_lean_workspace`.

### V1 fails closed at multiple stage boundaries, but those checks are not a soundness proof

The pipeline contains explicit failure boundaries:

- malformed or structurally invalid Anneal annotations fail before Charon;
- Charon is invoked with `--abort-on-error`, and compiler diagnostic errors or a nonzero exit fail the run;
- Aeneas is invoked with `-abort-on-error`, and a nonzero exit fails the run;
- missing expected `Funs.lean` or `Types.lean` is treated as a translation failure rather than silently filled in;
- Lake build failure aborts verification; and
- Lean error diagnostics from the generated specification files abort verification.

Those checks prevent many partial-pipeline states from being mistaken for success. They do not discharge the semantic trust boundary between Rust, LLBC, Aeneas-generated Lean, Anneal-generated Lean, and the actual machine execution. V1's known unsoundness/coverage holes, translation assumptions, and explicit axioms are distinct checklist subjects and should not be inferred away from a successful process exit.

Basis: **source** across `validate.rs`, `charon.rs`, and `aeneas.rs`; **derived** distinction between process fail-closedness and semantic soundness.

### `setup` supplies the tool universe but is not part of each verification run

`cargo anneal setup` resolves or installs an Exocrate archive into a configured installation location. `Toolchain::resolve` later exposes paths for:

```text
<root>/aeneas/bin/charon
<root>/aeneas/bin/aeneas
<root>/aeneas/backends/lean
<root>/rust/bin + lib
<root>/lean/bin + sysroot
<root>/lake-cache
```

`verify`, `generate`, and `expand` assume that this toolchain can be resolved. The setup/archive provenance, checksum, relocation, read-only behavior, and cross-platform viability are separate report subjects; this report records only their role in the end-to-end data flow.

Basis: **source**, `anneal/v1/src/setup.rs`, `Toolchain` and `run_setup`; package metadata in `anneal/v1/Cargo.toml`.

## Boundaries

**No fresh V1 execution was performed.** The pipeline was reconstructed from immutable source and repository history. Exact command arguments and artifact relationships are source facts; runtime success, timings, actual generated bytes, and host-dependent behavior were not re-observed.

**“Final useful revision” is treated as a reproducible source identity, not a claim about the exact last calendar moment when V1 was useful.** The report pins the current retained V1 source at `41f5b37...`, with the V1/V2 reorganization as its historical boundary. It does not assert that no post-reorganization maintenance change affected V1. In fact, retained setup/archive integration continued to receive maintenance; current-source identity is therefore the safer coordinate for the complete retained pipeline.

**The scanner/compiler correspondence is not proven here.** The scanner is intentionally CFG-agnostic and does its own source traversal. The report identifies where scanner-derived annotations and compiler-derived LLBC meet; it does not prove that every annotation maps to exactly the intended compiler item under every Cargo configuration.

**The generated-Lean ABI is not characterized exhaustively.** This report records which files flow between stages and how they are imported. Separate reports should carry theorem naming, data representation, `isValid`/`isSafe`, axiom, and coverage details.

**A successful Lean check is not an end-to-end translation-correctness theorem.** V1 trusts substantial tooling and translation machinery. No theorem is established here relating actual Rust machine behavior to the generated Lean model.

**Lake/cache behavior is summarized only enough to place it in the pipeline.** Read-only archive reuse, relocation, cache-key behavior, clean/cache equivalence, and concurrency are separate subjects with stronger dedicated evidence.

**Current V2 architecture is out of scope.** The current repository explicitly marks `anneal/v1` as historical. Similar filenames or goals in current Anneal do not imply the same pipeline.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary retained V1 source at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/v1/src/main.rs`, blob `3d363b977df790b266fe2a0635da1c294ec1b7c2`: CLI dispatch and `prepare_and_run` ordering.
- `anneal/v1/src/resolve.rs`, blob `9a44f652961e0bfe62bc4c2efecd550dea361fab`: Cargo resolution, target flattening, run-root hashing, and output locking.
- `anneal/v1/src/scanner.rs`, blob `44b66417a827192b87d4cad3e62421e8ca497d28`: source scanning, entry-point construction, artifact slug/file naming, and CFG-agnostic boundary.
- `anneal/v1/src/charon.rs`, blob `7e33bda392770d04397f7172296d9a7f25c6e180`: Charon invocation, LLBC destination, `--start-from`, `--opaque`, target/feature forwarding, and diagnostics.
- `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`: Aeneas invocation, generated Lean workspace construction, output patching, root manifest, spec generation orchestration, Lake build, direct Lean JSON checks, and source-map consumption.
- `anneal/v1/src/generate.rs`, blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`: Anneal-generated Lean and source mappings.
- `anneal/v1/src/diagnostics.rs`, blob `cd27b771e2f22bdb104c5335a70cfde3207e8fdb`: mapping/rendering diagnostics back into the user's workspace.
- `anneal/v1/src/setup.rs`, blob `32216cedf11c5d6d4b5a4618d8d7bf2578e44b4d`: installed toolchain layout and setup/resolve boundary.
- `anneal/v1/Cargo.toml`, blob `f545b31c8e15a3cc5b5bbaf277abb9e56afc2e33`: package version and retained Aeneas/Lean build pins.
- `anneal/v1/README.md`, blob `2bfda6336f87bf3cd785a19286363ab13423bd7d`: user commands and current historical-V1 status marker.
- `anneal/v1/docs/agent/01_philosophy_and_pipeline.md`, blob `39f0e1569e6c9f7d74722c78bdcae550e31bdb9c`: descriptive V1 mental model used only where consistent with source; its “in parallel” wording is not used to override implementation ordering.

Historical boundary:

- `google/zerocopy@dbb81cc7759bb6b21b82a1ca98bb32e9676f8655`, PR #3487, “Reorganize Anneal v1 and v2,” 2026-07-31. At that revision the inspected core pipeline blobs for `main.rs`, `resolve.rs`, `scanner.rs`, `charon.rs`, `aeneas.rs`, `generate.rs`, and `diagnostics.rs` match the current retained blobs listed above. Current setup code has received later maintenance, which is one reason this report binds complete behavior to `41f5b37...` rather than calling `dbb81cc...` the final implementation revision.
- `google/zerocopy@7e9de53b88121c58588984437ac500a2d1449080`, PR #3698, 2026-09-17: adds the explicit status marker that `anneal/v1` is historical and not current design authority.

Evidence roles are **source**, **documentation**, **source history**, and **derived** synthesis. There is no fresh **execution** evidence in this report.

## Revalidation

The cheapest revalidation for another retained V1 revision is to walk the orchestration spine rather than rereading the whole subtree:

1. inspect `main.rs::prepare_and_run` and record the stage order;
2. inspect `resolve.rs` and `scanner.rs` for target selection, output-root ownership, annotation discovery, and `start_from` construction;
3. inspect `charon.rs::run_charon` for exact LLBC inputs/outputs and compiler flags;
4. inspect `aeneas.rs::run_aeneas` for exact Aeneas inputs/outputs and generated-project construction;
5. inspect `generate_lean_workspace` and `generate.rs::generate_artifact` for Anneal's specification/source-map products; and
6. inspect `run_lake` for the exact build and proof-check commands plus diagnostic mapping.

A narrow behavioral specimen can then validate the source reconstruction. Use one tiny Cargo crate containing one annotated function and one `unsafe(axiom)` leaf. Run `cargo anneal generate` and preserve:

```text
resolved target identity
artifact slug
llbc/<Slug>.llbc
generated/<Slug>/{Funs,Types,FunsExternal,<Slug>}.lean
generated/<Slug>/<Slug>.lean.map
Generated.lean
lakefile.lean
lake-manifest.json
```

Then run `cargo anneal verify` with one deliberately failing proof and confirm that the Lean JSON diagnostic is remapped to the expected Rust span. This single specimen checks stage connectivity and diagnostic round-tripping; it does not establish semantic translation correctness. For that stronger question, the Charon/Aeneas/Anneal correspondence and trust assumptions must be revalidated separately.