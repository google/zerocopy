# Safe pruning of Lean package trees for Anneal

## Summary

A Lean/Lake package tree cannot be pruned safely by classifying filenames as “source,” “build output,” and “metadata” in the abstract. At Lean/Lake `v4.30.0-rc2`, a loaded `Package` carries a configuration file, dependency declarations, target declarations, scripts, hooks, test/lint drivers, source and build-directory settings, README and license-file paths, and native/build settings. Lean libraries and executables may choose their own source roots. A Lean-authored `lakefile.lean` is executable Lean configuration rather than a declarative file list. Which files are dispensable therefore depends on the consumer operations that the pruned tree must continue to support.

Current Anneal uses a narrower, purpose-specific policy. It first materializes and builds the pinned Aeneas/Lake dependency universe, primes Aeneas package configuration, rewrites and checks traces, and only then runs `anneal/prune-lake-cache.py`. The script applies dependency-closure pruning only to Mathlib modules; for every package it also deletes a fixed set of repository/documentation/test paths and every `*.ltar`, then removes empty directories. That operation intentionally does **not** preserve arbitrary upstream package functionality. For example, it deletes `README.md` and `LICENSE`, even though those are Lake's default `readmeFile` and `licenseFiles`, and it deletes `test/` and `tests/`, even though Lake targets can use arbitrary source directories. For non-Mathlib packages, the log message “Keeping all Lean modules” does not include Lean files under a subsequently deleted `test/` or `tests/` directory.

The current ordering gives several deletions a defensible Anneal-specific basis: Mathlib cache archives have already been expanded into the prepared build tree, package configuration has already been primed, and the final archive has explicit presence checks for selected configuration and compiled artifacts. It does not, however, prove a general “safe package pruning” property. A sound reusable pruning rule needs an explicit supported-consumer contract plus evidence that every file removed is outside the transitive file/target/configuration dependencies of those consumers. When that proof is unavailable, retaining the file is the conservative action.

This report separates that package-tree safety question from Mathlib module reachability and native-artifact inventory. The existing dependency-closure investigation determines which Mathlib modules are needed; this report determines what must be true before deleting other package-tree content.

## Applicability

The Lake model is pinned to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), the Lean revision used by the current Anneal toolchain basis. The Anneal behavior is pinned to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. The selected Aeneas Lean project is `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

“Safe” in this report is relative to a declared consumer surface. Removing a file is safe for a consumer set only when every supported operation in that set has the same required semantics without the file. A pruning policy may legitimately preserve generated-workspace compilation while dropping upstream tests, release tooling, documentation commands, or Reservoir metadata. It must not silently call those discarded capabilities preserved.

This report does not claim that the current Anneal pruning policy has been end-to-end execution-validated after every deletion. It identifies the source-defined safety conditions, records what current Anneal deliberately removes, and gives a discriminating validation procedure. Native-library completeness and cross-platform artifact portability remain separate report subjects.

## Findings

### Package-tree reachability is broader than Lean module imports

At this Lake revision, `Package` contains more than source modules and dependency locations. Its state includes the package configuration, configuration-file path, manifest-file path, dependency configurations, target declarations, default targets, scripts, post-update hooks, test/lint drivers, and package-level build settings.

`PackageConfig` also names paths that are semantically visible to Lake. These include `srcDir`, `buildDir`, Lean/native library directories, executable and intermediate-output directories, `licenseFiles`, and `readmeFile`. The defaults for the last two are `#[\"LICENSE\"]` and `README.md`.

Lean targets widen the reachable source set further. `LeanLib.srcDir` joins the package source directory with a library-specific `srcDir`; `LeanExe` similarly derives its root module from executable configuration. A package can therefore place a supported target under a directory whose name looks like test or auxiliary material.

A pruning algorithm that considers only `import` edges answers a narrower question: which Lean modules are needed to elaborate selected modules. It does not determine which files the package configuration, selected targets, scripts, release commands, test/lint drivers, or other supported operations require.

Basis: **source** in Lake `Package.lean`, `PackageConfig.lean`, `LeanLib.lean`, and `LeanExe.lean`; the distinction between module closure and package-operation closure is **derived**.

### Lean-authored package configuration is executable state, not a static manifest of file dependencies

Lake v4.30.0-rc2 supports package configuration authored in Lean. Loading that configuration reconstructs package declarations, targets, scripts, hooks, and related state. The selected Aeneas package itself demonstrates computed configuration: its `lakefile.lean` uses `run_io` to inspect the `CI` environment and sets `AeneasMeta.precompileModules` from that result.

This matters to pruning because there is no filename-only rule that can prove an arbitrary auxiliary file irrelevant to arbitrary Lean configuration. A Lean configuration or script can perform IO or construct target settings dynamically. A generic package-tree pruner would need either a much stronger sandbox/dependency model or an explicitly restricted set of supported operations and package-specific validation.

The practical consequence is not “never prune.” It is that pruning must be justified by a closed consumer contract. Anneal can drop functionality it does not promise to preserve, but it should make that boundary explicit and test the functionality it does promise.

Basis: **source** in Lake's package/configuration model and pinned Aeneas `backends/lean/lakefile.lean`; the safety consequence is **derived**.

### Current Anneal deliberately deletes files that Lake models as package metadata

`anneal/prune-lake-cache.py` deletes these names from every package when present:

- files: `.gitignore`, `.gitattributes`, `README.md`, `LICENSE`, `bors.toml`, `.pre-commit-config.yaml`, `.gitpod.yml`;
- directories: `.github`, `.vscode`, `.devcontainer`, `.docker`, `docs`, `tests`, `test`;
- every `*.ltar` recursively.

It then removes empty directories.

At the pinned Lake revision, `README.md` and `LICENSE` are not merely conventional repository names. They are the defaults of `PackageConfig.readmeFile` and `PackageConfig.licenseFiles`. A package that relies on the defaults still points at those paths after Anneal removes the files.

That does not make the runtime archive unusable for Anneal. It establishes a precise boundary: the pruned tree is not a semantics-preserving copy for all Lake/package operations. Reservoir/package-publication metadata, source redistribution expectations, and any command that consumes those configured paths are outside the preserved surface unless independently restored.

Basis: **source** in Anneal `prune-lake-cache.py` plus Lake `PackageConfig.lean`; the loss of generic metadata-preserving equivalence is **derived**.

### “Keep all non-Mathlib Lean modules” has a directory-deletion exception

For packages other than Mathlib, `prune_package` initially treats every discovered `.lean` file outside `.lake` as used. It therefore performs no module-reachability deletion on those files.

The same function then calls `remove_package_metadata`, which recursively deletes `tests/` and `test/`. A `.lean` source file below either directory disappears at this later step despite the earlier “Keeping all Lean modules for non-Mathlib package” policy and log message.

Lake permits libraries and executables to choose source roots, so a package may legitimately make a target depend on such a directory. Current Anneal's unit test for non-Mathlib preservation puts `Aesop/Core.lean` and `Aesop/Unused.lean` in ordinary source paths and verifies that `docs/` is removed; it does not cover a Lean target rooted below `test/` or `tests/`.

The safe interpretation is therefore: current Anneal preserves ordinary non-Mathlib Lean source outside the fixed metadata-directory deletion set. It does not preserve every possible non-Mathlib Lean target.

Basis: **source** in Anneal `prune-lake-cache.py` and `test_prune_lake_cache.py`, plus Lake target-directory configuration; the corrected interpretation is **derived**.

### Current Anneal's phase ordering gives `*.ltar` removal a narrower justification

The current flake separates Mathlib cache acquisition from cache materialization. `mathlib-cache-download` runs `lake exe cache get-` to obtain linked `.ltar` archives without decompressing them. `mathlib-cache-unpacked` then invokes the pinned native `leantar` and expands every cache archive into the prepared tree. The later Aeneas build copies those prepared packages/build products, performs an offline Lake build, primes package configuration, rewrites/checks traces, and only afterward invokes `prune-lake-cache.py`, which removes remaining `*.ltar` files.

Within this exact construction pipeline, those cache archives are inputs to an earlier materialization stage rather than the only retained copy of the selected compiled artifacts. The final archive is intended to consume the expanded package/build tree.

This does not imply that `.ltar` is universally disposable. A consumer surface that includes `lake exe cache` restoration, cache publication, or future lazy materialization could require archive content again. The justification comes from Anneal's phase ordering and supported consumer model, not from the file extension.

Basis: **source** in current `anneal/flake.nix` and `prune-lake-cache.py`; the phase-specific deletion argument is **derived**.

### Configuration and manifest state remain part of the prepared consumer tree

Current Anneal does not delete package `lakefile.lean`/`lakefile.toml`, `lake-manifest.json`, or the `.lake/config` tree through `remove_package_metadata`. Its archive-layout check requires, among other things, the Aeneas Lean package configuration source, Aeneas and Mathlib compiled package configuration `.olean`s, the Mathlib manifest, and at least one retained Mathlib `.olean`.

That retention is consistent with Lake v4.30.0-rc2's state model. Lean-authored package configuration has a package-local compiled configuration cache; locked dependency loading uses the root manifest as a flattened dependency closure; package configuration still describes targets and other package behavior. Deleting these merely because compilation has already happened would remove state that later generated workspaces can still need to load the packages.

The layout check is a presence check, not semantic completeness proof. It demonstrates that Anneal recognizes a required floor of package/config/build state. It does not prove every other retained or removed path is classified correctly.

Basis: **source** in current `anneal/flake.nix`; related exact-pin Lake behavior is established by the corpus reports on configuration ownership and transitive path dependencies; the “required floor, not completeness proof” distinction is **derived**.

### The safe pruning unit is a consumer contract, not a package directory

A reusable safe-pruning procedure can be expressed in four steps:

1. Define supported operations precisely: for example, load a generated workspace, import specified libraries, run the Lean server, or execute selected Lake targets. Excluded operations such as upstream tests, linting, releases, cache republishing, or Reservoir packaging must be explicit.
2. Enumerate the files and package state those operations can reach through package configuration, manifests, target roots, imports, scripts/hooks, configuration caches, native artifacts, and tool-specific state.
3. Remove only paths outside that closure, preserving a conservative margin where dependency extraction is incomplete.
4. Validate the pruned tree through the actual supported operations in the same read-only/offline/relocated conditions expected in deployment.

For current Anneal, Mathlib import closure can supply one component of step 2, but it cannot substitute for the other package-level dependencies. Fixed-name deletion is acceptable only when the supported-consumer evidence establishes that those names are outside the required closure.

Basis: **derived** synthesis from the pinned Lake and Anneal source above.

## Boundaries

**No fresh post-prune execution.** This investigation did not run Lake, Lean, Aeneas, or Anneal against a newly pruned tree. It therefore does not claim that every currently supported generated-workspace operation succeeds after the present deletion set.

**No full file-access audit of every pinned transitive package.** The selected Aeneas manifest names Mathlib plus eight inherited packages at precise revisions. This report did not prove that every configuration/script in those packages avoids each deleted path. The current pruning code has no general source-audit mechanism that would make such a proof automatic.

**No claim that documentation and licensing files are operationally required for Anneal verification.** The source establishes that Lake models default paths for them and that Anneal removes them. Whether a particular deployment is permitted or required to redistribute specific license/notice files is a legal/distribution question outside this technical report.

**Mathlib module reachability is separate.** The candidate report on Mathlib dependency-closure pruning covers the source/import graph and trace-derived roots. This report relies on that boundary rather than repeating the closure research.

**Native artifact completeness is separate.** The module-prefix deletion under `.lake/build/lib/lean` and `.lake/build/ir` does not by itself inventory static/shared libraries, executables, plugins, precompiled module libraries, or platform-specific outputs. Those are covered by the separate native-artifact subject.

**Empty-directory semantics are not validated.** `remove_empty_dirs` can delete a directory that a later script expects to exist even when it contains no retained file. No current evidence proves that such directory existence is irrelevant to every supported operation.

**Future Lake versions may change ownership or cache behavior.** The report is pinned to v4.30.0-rc2. In particular, configuration ownership after Lean 4.31 is already tracked as a separate subject.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary Anneal subject: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/prune-lake-cache.py`, blob `b0eb8eaa5ecefad9766a155994968712826ed996`: fixed metadata/file deletion lists, recursive `.ltar` removal, Mathlib-only module closure, non-Mathlib module policy, module artifact deletion, root Mathlib-cache deletion, and empty-directory cleanup.
- `anneal/tests/test_prune_lake_cache.py`, blob `596603415cf21be8b1e7b585e67bd37631b9a522`: current regression coverage for Mathlib reachability/deletion and ordinary non-Mathlib source preservation.
- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: cache download/unpack phases, offline build, package-config priming, trace rewriting/checks, pruning order, final archive construction, and archive-layout presence checks.

Primary Lake subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`: loaded package state, target declarations, scripts/hooks, manifest/config paths, metadata paths, build paths, and target lookup.
- `src/lake/Lake/Config/PackageConfig.lean`, blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`: configurable source/build/native/executable paths, default `licenseFiles := #[\"LICENSE\"]`, default `readmeFile := \"README.md\"`, test/lint drivers, artifact-cache settings, and other package semantics.
- `src/lake/Lake/Config/LeanLib.lean`, blob `077efb6c244fd53bab5dead6c850d40161c96e7f`: library-specific `srcDir`, roots, native facets/libraries, plugins, and build options.
- `src/lake/Lake/Config/LeanExe.lean`, blob `a80b70cffcbcab8efa8fd2c2673ac1810197feeb`: executable root module, source lookup, output file, and link inputs.
- `src/lake/Lake/DSL/Config.lean`, blob `6117c673ceabaf06da02ab4914f0f4fbd2f23f95`: Lean configuration elaboration support and runtime configuration values.

Selected Aeneas subject: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

- `backends/lean/lakefile.lean`, blob `c32062866e2f88d2eb768b904745e7104edddb0d`: default `Aeneas` and `AeneasMeta` libraries, computed `precompileModules` via `run_io`, and `extract` executable target.
- `backends/lean/lake-manifest.json`, blob `1a5af703163d8b39f4311aafe22ae171788179ee`: exact selected Mathlib revision and inherited package/revision/configuration-file identities.

Relevant existing corpus context:

- `reports/lake-configuration-ownership-v4-30-0-rc2`: package-local configuration/cache ownership at the selected Lake pin.
- `reports/lake-transitive-path-dependencies-v4-30-0-rc2`: flattened locked dependency closure and manifest coordinate rules.
- uncommitted candidate `1df2a4e2-2786-4436-8b07-551e66cbcc94`: Mathlib dependency-closure pruning; used only as salvage context, not as committed/native authority.

Evidence roles are **source** and **derived**. There is no fresh **execution** evidence.

## Revalidation

For another Anneal revision, first diff `PACKAGE_META_FILES`, `PACKAGE_META_DIRS`, `remove_package_metadata`, `prune_package`, and the pruning call site. Then inspect the selected Lake version's package/target configuration model: source roots, target declarations, config/manifest ownership, scripts/hooks, metadata paths, native output paths, and artifact-cache behavior.

For current Anneal, the highest-value execution probe is a consumer-contract test rather than another filename inventory:

1. construct the exact prepared package tree before pruning;
2. record every supported generated-workspace operation and selected target;
3. run those operations once against the unpruned tree in offline mode;
4. apply the exact pruning step;
5. make the prepared dependency universe read-only and relocate it to the deployment shape;
6. run the same operations again, with machine-observable evidence of every source/config/artifact path opened or rebuilt;
7. compare results and fail if the pruned run needs a removed file, attempts network access, mutates the shared dependency tree, or silently rebuilds an artifact that the prepared archive promised to supply.

Add two small negative regression fixtures to the pruning unit tests. One package should put a supported `lean_lib` or `lean_exe` source under `tests/`; pruning must preserve it or reject the package policy instead of deleting it silently. A second package should make an explicitly supported configuration/script depend on a nominal “metadata” path; the test should demonstrate that fixed-name deletion alone cannot establish safety.

Finally, preserve a machine-readable allowlist/contract for the exact consumer surface Anneal intends to ship. Revalidation can then distinguish an intentional scope reduction (“upstream tests are not shipped”) from an accidental regression (“a supported generated workspace lost a required path”).
