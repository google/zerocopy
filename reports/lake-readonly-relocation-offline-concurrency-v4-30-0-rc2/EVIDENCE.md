# Evidence

All current Lake source evidence is pinned to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). Blob identities are listed so later readers can distinguish source movement from semantic changes.

## Current-pin Lake source

### Dependency and manifest model

- **source** — `src/lake/Lake/Config/Dependency.lean`, blob `a06fad9cd1da3df2ab1b2c6aaaba38535e64a0f1`.
  - `DependencySrc.path` documents a path relative to the dependent package directory.
- **source** — `src/lake/Lake/Load/Manifest.lean`, blob `760eb81419762fb0ab11393e93082930645e2b6d`.
  - `PackageEntrySrc.path` documents a path relative to the package containing the manifest.
  - `PackageEntry.inDirectory` prefixes path entries when inherited through package directories.
- **source** — `src/lake/Lake/Load/Resolve.lean`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`.
  - `Workspace.materializeDeps` consumes locked manifest entries.
  - `Workspace.updateAndMaterialize` constructs/materializes updated dependency state and saves the manifest.
- **source** — `src/lake/Lake/Load/Materialize.lean`, blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`.
  - Path manifest entries are re-rooted under `wsDir`.
  - Existing Git repositories already at the locked revision skip fetch; absent or mismatched repositories clone/fetch/update.
- **source** — `src/lake/Lake/Load/Workspace.lean`, blob `9f25dd62bc752ede695a25fc20371157eb65d64b`.
  - A present manifest takes the locked `materializeDeps` path; a missing manifest takes `updateAndMaterialize`.

### CLI and offline/cache controls

- **source** — `src/lake/Lake/CLI/Main.lean`, blob `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`.
  - The CLI parses `--offline`.
  - `mkLoadConfig` does not propagate the `offline` field.
  - `lake build` loads the workspace through that `LoadConfig`.
  - `new` and `init` pass `opts.offline` directly to initialization functions.
- **source** — `src/lake/Lake/CLI/Init.lean`, blob `2af0cfd3a005601b6dfb88f3277496d01e54d6f5`.
  - Initialization has an explicit `offline` parameter.
- **source** — `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`.
  - `LAKE_NO_CACHE` controls package build-cache downloads.
  - `LAKE_CACHE_DIR` controls the local Lake cache location.
- **source** — `src/lake/Lake/Config/PackageConfig.lean`, blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`.
  - Documents local/offline artifact-cache behavior.
  - The default permits cache reads but not package cache writes; restore-all defaults false.
- **source** — `src/lake/Lake/Config/Monad.lean` at the pinned revision.
  - `Package.isArtifactCacheReadable` defaults to true.
  - `Package.isArtifactCacheWritable` defaults to false.
  - `Package.restoreAllArtifacts` defaults to false.
  - `getNoCache` reads Lake's `noCache` setting rather than acting as a general network policy.

### Build writes and artifact cache

- **source** — `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`.
  - Successful build actions write trace metadata.
  - File hashing may create adjacent `.hash` files.
  - Cache artifact saving uses content-addressed paths and race-tolerant create behavior.
  - Restoring a cache artifact can hard-link/copy into a package path and write a `.hash` file.
  - Cache lookup can download a missing artifact from a configured cache service.
- **source** — `src/lake/Lake/Build/Actions.lean`, blob `5b3ab3cc3e9f45b8c695e31680342acc795004c7`.
  - Compilation creates output directories/files and writes Lean setup files.
- **source** — `src/lake/Lake/Config/Cache.lean`, blob `607e6b92108f30e0a57d0de682f7faa283d7d470`.
  - Cache-map readers use shared file locks; update/write uses exclusive locks.
  - Per-input output mappings are ordinary files in the cache hierarchy.
- **source** — `src/lake/Lake/Util/Lock.lean`, blob `78f109574faedcfedd6d142ed51b5b700082aa63`.
  - States that Lake does not currently use a global lock file and records why the prior build lock was removed.
- **source** — `src/lake/Lake/Build/Trace.lean`, blob `656c991fab8a6475802373224514ec7e73f9b18b`.
  - Defines hash/mtime build traces used by the reuse decision.

### Adjacent corpus report

- **source-derived reference report** — `reports/lake-state-model-v4-30-0-rc2/` on `google/zerocopy` `reference` at `741b0f90dfef1cd572249a88f8f1f8e79f5912cf`.
  - Establishes the package/workspace/manifest/build/trace layers at the same Lake pin.
  - Explicitly leaves relocation, read-only consumption, offline behavior, concurrent sharing, and clean/cache equivalence to separate work.

## Historical Anneal evidence

These records explain why Anneal V1 adopted the prepared-state contract and preserve a regression test for it. They are not normative Lake documentation.

- **historical rationale** — `google/zerocopy` issue/PR #3297, “Replace per-test Lean clone pool with Lake artifact cache”.
  - Records use of a shared artifact cache and shared pre-checked-out dependencies for integration tests.
  - URL: `https://github.com/google/zerocopy/issues/3297`
- **historical rationale** — #3304, “Use Lean artifact cache; use local-filesystem git dep”.
  - Records that a non-Git filesystem dependency allowed Lake to treat user-global package state as mutable and caused races under parallel Anneal commands.
  - URL: `https://github.com/google/zerocopy/issues/3304`
- **historical rationale** — #3305, “Cleanup test infrastructure and implement atomic setup”.
  - Records replacement of the worker/cache clone pool with a shared artifact-cache design and cites roughly 100 GB consumption in a run with about 100 parallel workers under the earlier design.
  - URL: `https://github.com/google/zerocopy/issues/3305`
- **historical rationale** — #3306, “In setup, recursively cache Lean sources”.
  - Records conversion of transitive Lean dependencies to filesystem-local Git sources so materialization could clone locally rather than from the internet.
  - URL: `https://github.com/google/zerocopy/issues/3306`
- **historical rationale** — #3450, “Remove v1 Lake cache symlinks”.
  - Records that `--old` alone was insufficient with fresh input mtimes and that missing root manifest state caused writes into read-only package configuration trees.
  - Records the move to complete relative manifests and prepared archive state.
  - URL: `https://github.com/google/zerocopy/issues/3450`
- **historical execution-oriented regression evidence** — #3453, “Check archive Lake cache reuse in tests”.
  - Records an integration test for a fully read-only installed Aeneas archive consumed by a fresh workspace with a complete relative manifest and `--old`.
  - URL: `https://github.com/google/zerocopy/issues/3453`

## Checked-in historical test and implementation

Pinned here to current `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`; these files live under `anneal/v1/` and are historical design evidence.

- **historical source/test** — `anneal/v1/tests/integration.rs`, blob `8fc6f6b9b4d4785e532e0647466a2e2373fe709a`.
  - `assert_archive_lake_cache_reuse` checks that the installed Aeneas archive has no write bits.
  - It creates a fresh workspace, writes a relative locked manifest, runs `lake --old build Generated`, and runs Lean diagnostics.
- **historical source** — `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`.
  - Verification runs `lake --old build` against the installed archive contract.
  - `configure_lake_command` removes `CI` because differing package configuration otherwise invalidates the prebuilt archive and causes attempted rebuild/removal inside the read-only tree.
- **historical test metadata** — `anneal/v1/tests/fixtures/archive_lake_cache_reuse/anneal.toml`, blob `bd44e3c3bcd404965d3355b98a8db4c2131fcb28`.
  - States the test purpose: a Nix-built archive should be usable read-only by a fresh generated Lake workspace with a complete relative manifest.

## Evidence classification

- The pinned Lake implementation is **source** evidence for control flow, filesystem operations, cache decisions, and locking at v4.30.0-rc2.
- Source comments and the Lake README are **documentation** where they describe intended behavior.
- Anneal PR descriptions are **historical rationale** and preserved engineering observations.
- Checked-in V1 test code is **historical execution-oriented regression evidence**: it records what the test exercises, but this report did not rerun it.
- Statements about the safest Anneal architecture are **derived** from those facts and remain subject to the execution boundary in `BOUNDARIES.md`.