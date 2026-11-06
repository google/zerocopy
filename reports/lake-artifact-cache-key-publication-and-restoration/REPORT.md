# Lake Artifact-Cache Architecture, Key Semantics, Environment Policy, Publication, Restoration, and Coverage Boundaries

## Summary

Across Lean 4 and Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `Lake version 5.0.0-src+5045d00`), and `v4.35.0-rc3` (`leanprover/lean4@470d5ce1400764999581fd26d5d72b00d990b0f4`), Lake's local artifact cache separates build-input identity from artifact-content identity across two local storage layers:

1. **Content-addressed artifact store (`artifacts/{hash}.{ext}`):** Each cached file is identified by an `ArtifactDescr` recording a 64-bit non-cryptographic Lake `Hash` over its contents (raw bytes for binary outputs; CRLF-to-LF normalized text for text outputs) plus its file extension.
2. **Package-scoped input-to-output mapping store (`outputs/<package-scope>/<input-hash>.json`):** A package cache scope (`Package.cacheScope`, derived from `Package.baseName`) and the current build job's dependency-trace hash (`inputHash := depTrace.hash`) map to a `CacheOutput` JSON document (`CacheOutput.schemaVersion : String := "2026-02-25"`) containing structured output descriptors and optional remote cache-service/scope metadata.

Key architectural and cross-version findings established by source inspection:

- **Target-specific key semantics and weak-argument exclusions:** Lake does not hash an entire workspace directory or command line automatically. A target's `inputHash` changes only when its `BuildTrace` (`MixTrace`) changes. Built-in module and native builders mix source/import content hashes, the Lean toolchain Git hash (`ws.lakeEnv.leanGithash`), host platform (`System.Platform.target`) for native targets, logical module name, package ID, traced options, and `traceArgs`, while deliberately excluding path-shaped `weakArgs` (such as `-I` and `-L` flags) and narrowing native/platform traces when `platformIndependent = true`.
- **Decoupled location and asymmetric read/write policy:** `LAKE_CACHE_DIR` selects where the cache root lives (nonempty path `P` selects `P`; empty string `""` sets `noSystemCache := true` and falls back to `<root-package>/.lake/cache` rather than disabling caching; unset prefers the Elan toolchain cache, then system cache, then `<root-package>/.lake/cache`). `LAKE_ARTIFACT_CACHE` sets the tri-state workspace policy (`true`, `false`, or unset `none`). Per-package policy checks `package.enableArtifactCache? <|> workspace.enableArtifactCache?`, defaulting to **readable (`true`) but not writable (`false`)**.
- **Ordered, non-transactional publication and trace-based recovery:** On a cacheable build (`OutputStatus.isCacheable = true`, excluding `--old` modification-time-only hits), Lake writes the target `.trace`, publishes content-addressed artifact bytes via race-tolerant hard-link/create-if-absent helpers (`Cache.saveArtifact`), and then writes the output mapping via `Cache.writeOutputs`. Saved target `.trace` files and cache mappings share `inputHash` and can recover missing mappings when writes are enabled.
- **Selective restoration:** `restoreArtifact` materializes a resolved cached artifact at a local build path (preferring `IO.FS.hardLink` and falling back to `copyFile` plus a `.hash` sidecar) only when the destination path does not already exist. Non-writable readable packages restore cache hits into `.lake/build`; writable packages can consume cache-resident paths directly unless `restoreAllArtifacts` is enabled.
- **Explicit non-coverage boundaries:** Only targets routed through `buildArtifactUnlessUpToDate` or custom cache-aware serializers (`ModuleOutputArtifacts`) participate. Local-only builders such as `ExternLib.sharedFacet` (`buildLeanSharedLibOfStatic` via `buildFileUnlessUpToDate'`), source files, dependency checkouts, workspace manifests, and package build archives (`maybeFetchBuildCache` from Reservoir or GitHub releases) sit outside the per-target artifact cache.
- **Version evolution (`v4.30.0-rc2` → `v4.34.1` → `v4.35.0-rc3`):**
  - In `v4.34.1`, `Lake/Config/Cache.lean` adds `overwrite : Bool := true` to `writeOutputsCore` (line 434) and `writeOutputs` (line 449), where `true` calls `IO.FS.writeFile` and `false` calls `writeFileIfNew`.
  - In `v4.30.0-rc2`, malformed JSON in `Cache.readOutputs?` logged an invalid-JSON warning and returned `none` directly inside `readOutputs?`. In `v4.34.1`, `readOutputs?` (`Lake/Config/Cache.lean`, line 463) throws an error via `error`, which `getArtifactsUsingCache?` (`Lake/Build/Common.lean`, line 521) catches, logs at verbose level, and converts to `none` (cache miss).
  - In `v4.34.1`, `Lake/Build/Module.lean` adds `.ir.sig` alongside `.olean`, `.olean.server`, `.olean.private`, `.ilean`, and `.c` in module artifact handling.
  - In `v4.34.1`, `buildArtifactUnlessUpToDate` (`Lake/Build/Common.lean`, lines 724–731) inserts artifact descriptions into the build context's optional `outputsRef?` when `pkg.isRoot`. In `v4.35.0-rc3` (`470d5ce1400764999581fd26d5d72b00d990b0f4`, lines 667–672 and 724–735), `Internal.getOutputsRef?` changes that predicate to `pkg.wsIdx = ctx.outputsIdx`, while preserving the direct `Cache.writeOutputs pkg.cacheScope inputHash art.descr` call (lines 719–720).

## Applicability

This report synthesizes source-level findings across five pinned upstream revisions declared in `REPORT.json`:

1. **Lean 4 / Lake `v4.30.0-rc2`:** `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
2. **Lean 4 / Lake `v4.34.1`:** `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`Lake version 5.0.0-src+5045d00`).
3. **Lean 4 / Lake `v4.35.0-rc3`:** `leanprover/lean4` revision `470d5ce1400764999581fd26d5d72b00d990b0f4` (with upstream comparison snapshot at `193c3589a4fc16c4059261ab38cfa365eb24f323`).
4. **Mathlib `v4.30.0-rc2`:** `leanprover-community/mathlib4` revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (paired toolchain `leanprover/lean4:v4.30.0-rc2`).
5. **Mathlib `v4.34.1`:** `leanprover-community/mathlib4` revision `d13f23b723b8a846827a245b89c10fc7d3f11612` (paired toolchain `leanprover/lean4:v4.34.1`, plus `v4.35.0-rc3` tag `c55e6e786f49471c72fbddbec5415808896aec1e` and comparison tip `302343bb9a029d4edab4f736703f0736896c1b64`).

The findings govern Lake's local content-addressed artifact cache (`Lake/Config/Artifact.lean`, `Lake/Config/Cache.lean`, `Lake/Build/Common.lean`, `Lake/Build/Module.lean`, `Lake/Build/Trace.lean`, `Lake/Config/Env.lean`, `Lake/Config/Workspace.lean`, `Lake/Config/Package.lean`, `Lake/Config/Monad.lean`, and `Lake/Build/ExternLib.lean`).

 behaviors shared across `v4.30.0-rc2`, `v4.34.1`, and `v4.35.0-rc3` are stated first in each finding, followed by explicit version-specific deltas. Where the constituent cohort reviews also tracked compiled-configuration placement (`Lake/Load/Config.lean` and `Lake/Load/Lean/Elab.lean`) or LSP `waitForDiagnostics` version comparison (`Lean/Server/FileWorker/RequestHandling.lean`), those source comparisons are summarized for completeness while full configuration-ownership and Mathlib `.ltar` protocol details are covered in their dedicated packages.

## Findings

### 1. Dual-Layer Cache Architecture: Content-Addressed Artifacts vs. Input-Hash Mappings

Across `v4.30.0-rc2`, `v4.34.1`, and `v4.35.0-rc3`, Lake's artifact cache separates the identity of build inputs from the identity of build outputs:

- **Artifact content identity (`ArtifactDescr` and `Artifact`):** Defined in `src/lake/Lake/Config/Artifact.lean`, `ArtifactDescr` contains a 64-bit `Hash` over artifact contents and a file extension (`ext`). Its cache-relative path (`ArtifactDescr.relPath`) is `{hash}.{ext}`, stored under `<cache>/artifacts/{hash}.{ext}`. `Artifact` extends `ArtifactDescr` with a runtime preferred filesystem `path`, human-facing `name`, and modification time (`mtime`). `ToOutputJson Artifact` serializes only the `ArtifactDescr` relative path string; runtime paths and modification times are reconstructed when outputs are resolved.
- **Input-to-output mapping (`CacheOutput`):** Defined in `src/lake/Lake/Config/Cache.lean` (`CacheOutput.schemaVersion : String := "2026-02-25"` at line 339, `structure CacheOutput` at line 341 in `v4.34.1`), `Cache.outputsFile` places each mapping at:
  ```text
  <cache>/outputs/<package-scope>/<input-hash>.json
  ```
  where `<package-scope>` is `Package.cacheScope` (the package's `baseName` rendered as a string) and `<input-hash>` is the dependency-trace hash (`depTrace.hash`). `CacheOutput` wraps structured output JSON (`ResolveOutputs` and `CacheMap.collectOutputDescrs` recursively walk arrays and objects to recover embedded artifact descriptions) alongside optional remote-cache `service` and `scope` metadata.
- **Remote-origin recovery:** In `resolveArtifact`, Lake first checks whether `<cache>/artifacts/{hash}.{ext}` exists locally (`getArtifact?`, line 407 in `v4.34.1` `Cache.lean`). If the local file is absent and the `CacheOutput` entry specifies both a remote cache service and remote scope, Lake downloads the artifact (`downloadArtifactCore` / `downloadArtifact`), verifies its content hash against the expected `ArtifactDescr` hash, deletes the file on mismatch, and marks verified downloads read-only before returning. A purely local mapping without remote service metadata fails closed when its artifact file is missing.

Basis: **source** (`src/lake/Lake/Config/Artifact.lean`, `src/lake/Lake/Config/Cache.lean`, `src/lake/Lake/Build/Common.lean`; indexed in `support/lake-artifact-cache-architecture/evidence-index.json`).

### 2. Artifact-Cache Key Semantics and Target Trace Construction

Lake does not compute a universal cache key from package revisions or raw CLI invocations. Instead, `buildArtifactUnlessUpToDate` (`src/lake/Lake/Build/Common.lean`) reads the current job trace (`let depTrace ← getTrace`) and sets `let inputHash := depTrace.hash`.

- **Explicit trace composition (`BuildTrace` / `MixTrace`):** Defined in `src/lake/Lake/Build/Trace.lean` (`MixTrace` at line 62, `Hash` at line 100, `checkAgainstHash` at line 378, `checkAgainstTime` at line 386 in `v4.34.1`), `BuildTrace` carries a caption, nested input traces, a 64-bit `Hash`, and an `mtime`. `BuildTrace.mix` combines hashes via `Hash.mix`, and `JobM.addTrace` mixes a trace into the current job state. Human-readable trace captions do not affect `depTrace.hash`.
- **File hashing and `.hash` sidecar trust:** Binary inputs (`inputBinFile`) hash raw bytes; text inputs (`inputTextFile` / `computeTextFileHash`) normalize CRLF line endings to LF before hashing so line-ending differences across platforms do not alter the key. When `trustHash` is enabled (the default unless `--rehash` is passed), `fetchFileHash` reuses a neighboring `.hash` sidecar without re-reading the file bytes. Coherent `.hash` sidecars are therefore a correctness precondition whenever hashes are trusted.
- **Toolchain and platform traces:** `addLeanTrace` mixes `.ofHash (pureHash ws.lakeEnv.leanGithash)` rather than hashing the absolute toolchain installation path, allowing toolchain relocation when the Lean Git commit hash is unchanged. Native object, library, and executable builders (`buildO`, `buildLeanO`, `buildSharedLib`, `buildLeanSharedLib`, `buildLeanExe` in `Lake/Build/Common.lean`, with compilation actions `compileLeanModule` at line 29, `compileO` at line 111, `compileStaticLib` at line 137, and `compileSharedLib` at line 149 of `Lake/Build/Actions.lean` in `v4.34.1`) call `addPlatformTrace`, mixing `System.Platform.target` into the trace.
- **Deliberate exclusion of path-shaped `weakArgs`:** Native builders and module builders separate `traceArgs` from `weakArgs` (`weakLeanArgs`). Both are passed to the compiler or linker, but only `traceArgs` are mixed into `BuildTrace` via `addPureTrace`. System-dependent include and library search paths (`-I`, `-L`) passed as `weakArgs` can relocate without changing `inputHash`.
- **Module trace composition and `platformIndependent` narrowing:** In `src/lake/Lake/Build/Module.lean` (`Module.recBuildLean` and `Module.presetupFacetConfig` at line 630 in `v4.34.1`), a Lean module's `leanArts` trace mixes the Lean Git hash trace, source file trace, traced Lean options (`traceOptions` hashing `-Dname=value`), module-system flag, module name, package ID (`Package.id?`), traced `leanArgs`, and the dependency setup trace. During dependency setup:
  - if `platformIndependent` is `none`, Lake mixes both the general dependency trace and native-library trace;
  - if `platformIndependent = some false`, Lake mixes both traces plus `addPlatformTrace`;
  - if `platformIndependent = some true`, Lake mixes only the general dependency trace, omitting native-library and platform traces.
- **Non-participating metadata:** Package semantic version, Git revision, repository URL, and the target output file path passed to `buildArtifactUnlessUpToDate` are not automatically mixed into `inputHash`. Furthermore, saved `.trace` files and cache output mappings share the exact same `inputHash` contract (`savedTrace.depHash == inputHash`).

Basis: **source** + **derived** (`src/lake/Lake/Build/Trace.lean`, `src/lake/Lake/Build/Common.lean`, `src/lake/Lake/Build/Module.lean`, `src/lake/Lake/Build/Job/Monad.lean`, `src/lake/Lake/Build/Job/Basic.lean`; indexed in `support/lake-artifact-cache-key-semantics/evidence-index.json`).

### 3. Environment Variables (`LAKE_CACHE_DIR`, `LAKE_ARTIFACT_CACHE`, `LAKE_NO_CACHE`) and Policy Precedence

Lake separates cache directory selection, local artifact-cache read/write permissions, and remote/package build-cache downloads (`src/lake/Lake/Config/Env.lean`, lines 39, 43, 47–56, 176–177, 296, 311; `src/lake/Lake/Config/Workspace.lean`, line 31; `src/lake/Lake/Config/Monad.lean`; `src/lake/Lake/Config/InstallPath.lean`):

| Incoming `LAKE_CACHE_DIR` | `Lake.Env` / `Workspace.computeLakeCache` resolution |
| --- | --- |
| Nonempty path `P` | Sets both `lakeCache?` and `lakeSystemCache?` to `P`; workspace uses `P`. |
| Empty string `""` | Sets `noSystemCache := true` and leaves shared cache coordinates unset; non-bootstrap workspace falls back to `<root-package>/.lake/cache`. Does **not** disable artifact caching. |
| Unset | Uses Elan toolchain cache when Elan and a nonempty toolchain name are present; else system cache; else `<root-package>/.lake/cache`. |

`Workspace.augmentedEnvVars` (`lake env`) unconditionally exports `LAKE_CACHE_DIR=<workspace.lakeCache.dir>`, normalizing an incoming empty `LAKE_CACHE_DIR=` into the concrete workspace-local `.lake/cache` path for child processes.

`LAKE_ARTIFACT_CACHE` is parsed by `envToBool?` (`InstallPath.lean`):
- **True spellings (case-insensitive):** `y`, `yes`, `t`, `true`, `on`, `1`.
- **False spellings (case-insensitive):** `n`, `no`, `f`, `false`, `off`, `0`.
- **Unset / unrecognized (including `""`):** `none`.

Effective per-package read/write permissions evaluate a two-level fallback chain with asymmetric defaults:
```lean
readable := package.enableArtifactCache? <|> workspace.enableArtifactCache? |>.getD true
writable := package.enableArtifactCache? <|> workspace.enableArtifactCache? |>.getD false
where
workspace.enableArtifactCache? := environment.enableArtifactCache? <|> rootPackage.enableArtifactCache?
```

| Cache Location | Effective Package Policy | Operational Consequence |
| --- | --- | --- |
| `<root>/.lake/cache` (e.g., `LAKE_CACHE_DIR=""`) | Unset (default) | Reads seeded local cache (`readable = true`); does not write new entries (`writable = false`). |
| `<root>/.lake/cache` | `true` | Reads and populates workspace-local `.lake/cache`. |
| Shared/explicit `LAKE_CACHE_DIR` | Unset (default) | Reads seeded shared cache; does not populate it. |
| Shared/explicit `LAKE_CACHE_DIR` | `true` | Reads and populates shared cache. |
| Any location | `false` | Generic artifact-cache read and write paths are both disabled for the package. |

Separately, `LAKE_NO_CACHE` (and `--no-cache`) controls `env.noCache`, which disables downloading package build caches (`maybeFetchBuildCache`) unless overridden; it is distinct from `LAKE_CACHE_DIR`.

Basis: **source** + **documentation** (`support/lake-cache-environment/environment-matrix.json`, `support/lake-cache-environment/source-map.json`).

### 4. Publication Ordering, Restoration Mechanics, and Version Deltas (`v4.30.0-rc2` vs. `v4.34.1` vs. `v4.35.0-rc3`)

#### Publication and Trace Recovery State Machine
In `buildArtifactUnlessUpToDate` (`src/lake/Lake/Build/Common.lean`), publication and lookup follow an ordered, non-transactional state machine (modeled in `support/lake-artifact-cache-publication-restoration/publication-restoration-state-machine.json`):

1. **Writable package path (`isArtifactCacheWritable = true`):**
   - Lake queries `getArtifacts? inputHash savedTrace pkg`, checking the package's `outputs/<scope>/<input-hash>.json` mapping first (`getArtifactsUsingCache?`) and falling back to output descriptors in the target's saved `.trace` file (`getArtifactsUsingTrace?`) when `savedTrace.depHash == inputHash`.
   - If `getArtifactsUsingTrace?` succeeds while the package mapping is missing, a writable package attempts to backfill `outputs/<scope>/<input-hash>.json` via `writeOutputs`; failure of this trace-recovery backfill is caught and logged only as a warning.
   - If cache/trace lookup misses, Lake runs the local freshness/build check (`buildUnlessUpToDate?` / `buildAction`). When a fresh build succeeds, `buildAction` writes the target `.trace` file before returning.
   - If the resulting `OutputStatus.isCacheable` is `true` (which holds for freshly built and hash-up-to-date results, but is `false` for modification-time-only `--old` hits), Lake calls `cacheArtifact` (`Cache.saveArtifact`) **first** and `Cache.writeOutputs` **second**. Direct `writeOutputs` failure on this path is uncaught and aborts the build action after artifact bytes are already in `artifacts/`.
2. **Non-writable package path (`isArtifactCacheWritable = false`):**
   - Lake checks local target freshness first (`SavedTrace.replayIfUpToDate'`).
   - If the local target is missing or stale and `isArtifactCacheReadable` is `true`, Lake queries `getArtifactsUsingCache?` and forces `restore := true` so a cache hit is materialized at the conventional `.lake/build` path.
3. **Race-tolerant artifact byte creation (`Cache.saveArtifact`):**
   - If `artifacts/{hash}.{ext}` already exists, `saveArtifact` trusts the existing path without rehashing its bytes.
   - Otherwise, for binary files Lake marks the built file read-only where possible and attempts `IO.FS.hardLink`. If `hardLink` fails with `alreadyExists`, Lake accepts the concurrent creator's file; on other errors (such as cross-device links), it falls back to `writeBinFileIfNew` (`IO.FS.Mode.writeNew`, treating `alreadyExists` as success). Text files normalize CRLF to LF and use `writeFileIfNew`.
4. **Restoration (`restoreArtifact`) and fetch-trace synthesis:**
   - On a cache hit, if `savedTrace.replayOrFetchIfUpToDate inputHash` indicates the saved local trace does not match `inputHash`, Lake removes any stale local output file and writes a synthetic fetch trace (`BuildMetadata.ofFetch`, setting `synthetic := true`, `depHash := inputHash`, and empty `inputs`/`log`) before calling `restoreArtifact`.
   - `restoreArtifact file art` checks `file.pathExists`. If `file` already exists, it skips hard-link/copy and `.hash` writes and returns `art.useLocalFile file`. If `file` is absent, it creates parent directories, tries `IO.FS.hardLink art.path file`, falls back to `copyFile` (marking the copy read-only), writes the local `<file>.hash` sidecar, and returns the local path.
   - Writable packages leave cache hits at their cache-resident paths unless the caller requests restoration or `Package.restoreAllArtifacts` is `true` (`Module.restoreNeededArtifacts` restores `.ilean` locally while leaving `.olean` in the cache unless `restoreAllArtifacts = true`).

#### Cross-Version Source Deltas (`v4.30.0-rc2` → `v4.34.1` → `v4.35.0-rc3`)

| Mechanism | `v4.30.0-rc2` (`3dc1a088b6d2`) | `v4.34.1` (`5045d0056413`) | `v4.35.0-rc3` (`470d5ce14007`) |
| --- | --- | --- | --- |
| `Cache.writeOutputsCore` / `Cache.writeOutputs` (`Lake/Config/Cache.lean`) | Calls `IO.FS.writeFile file (toJson out).pretty` directly (unconditional overwrite, no temp-file rename or lock). | Adds `overwrite : Bool := true` parameter (`writeOutputsCore` at line 434, `writeOutputs` at line 449): `true` calls `IO.FS.writeFile`; `false` calls `writeFileIfNew`. | Retains `v4.34.1` `overwrite : Bool := true` signature and behavior (only a deprecation message typo changes in `Cache.lean`). |
| Malformed JSON in `Cache.readOutputs?` (`Lake/Config/Cache.lean` & `Lake/Build/Common.lean`) | `readOutputs?` (lines 454–467) logs an `"invalid JSON"` warning locally and returns `none`. | `readOutputs?` (line 463) throws an error via `error`; `getArtifactsUsingCache?` (`Common.lean`, line 521) catches the error, logs it at verbose level, and returns `none`. | Same as `v4.34.1`. |
| Context `outputsRef?` insertion after `buildArtifactUnlessUpToDate` (`Lake/Build/Common.lean`) | Inserts into `outputsRef?` only when `pkg.isRoot`. | Inserts into `outputsRef?` only when `pkg.isRoot` (lines 724–731). Direct `Cache.writeOutputs` remains unconditional on cacheable writable builds. | Introduces `Internal.getOutputsRef?` (lines 667–672), routing insertion when `pkg.wsIdx = ctx.outputsIdx` (lines 724–735). Direct `Cache.writeOutputs` at lines 719–720 is unchanged. |
| Module cached artifact facets (`Lake/Build/Module.lean`) | `.olean`, `.olean.server`, `.olean.private`, `.ilean`, `.ir`, `.c`, `.bc`, `.ltar`. | Adds `.ir.sig` artifact facet (lines 266, 468–471) alongside `.olean`, `.olean.server`, `.olean.private`, `.ilean` (lines 678–710), and `.c`. | Retains `.ir.sig` and module system facets. |

Basis: **source** (`support/lake-artifact-cache-publication-restoration/source-map.json`, `support/lean-lake-430rc2-to-4341-source-review/matrix.json`, `support/lean-lake-4350rc3-output-reference-routing-source-followup/mapped_source_results.json`, and raw source snapshots under `support/lean-lake-4350rc3-output-reference-routing-source-followup/raw/leanprover/lean4/`).

### 5. Non-Coverage Boundaries: What Lake's Artifact Cache Does Not Store

Seeding `LAKE_CACHE_DIR` does not snapshot a workspace or build directory (`support/lake-artifact-cache-noncoverage/evidence-index.json`):

1. **Local-only build helpers (`buildFileUnlessUpToDate'` and `buildUnlessUpToDate?`):** Targets that use `buildFileUnlessUpToDate'` check only the local `.trace` file and never query or populate `LAKE_CACHE_DIR`. A concrete built-in example is `ExternLib.sharedFacet` (`buildLeanSharedLibOfStatic` in `src/lake/Lake/Build/ExternLib.lean`), which compiles a shared library from a static library via `buildFileUnlessUpToDate' dynlib` even though other shared-library helpers in `Lake/Build/Common.lean` use `buildArtifactUnlessUpToDate`.
2. **Source files and dependency checkouts:** Input jobs (`inputTextFile`, `inputBinFile`, `inputFile`) hash existing source files into `BuildTrace` without copying them into `artifacts/`. Dependency checkouts are managed by `Lake/Load/Materialize.lean`, not by the artifact cache.
3. **Standalone `.trace` and `.hash` sidecars and module setup state:** `.trace` and `.hash` files are local build metadata, not standalone content-addressed entries in `artifacts/` (except where `Module.packLtar` bundles a module's `.trace` file inside a higher-level `.ltar` archive). Similarly, module IR/setup control files (`mod.irSetupFile` via `buildUnlessUpToDate?`) are local-only.
4. **Package build archives (`maybeFetchBuildCache`):** In `src/lake/Lake/Build/Package.lean`, `Package.maybeFetchBuildCache` and `Package.fetchBuildArchive` download Reservoir barrels or GitHub release tarballs and unpack them into `self.buildDir` using local trace freshness. That channel is completely separate from `<cache>/outputs/` and `<cache>/artifacts/`.
5. **Workspace control plane and custom targets:** `lake-manifest.json`, `.lake/package-overrides.json`, compiled `lakefile.olean` configuration caches, and custom targets that do not explicitly invoke `buildArtifactUnlessUpToDate` are outside the artifact cache.

Basis: **source** + **derived** (`src/lake/Lake/Build/Common.lean`, `src/lake/Lake/Build/ExternLib.lean`, `src/lake/Lake/Build/Module.lean`, `src/lake/Lake/Build/Package.lean`).

## Boundaries

- **Execution status (`not examined` at `v4.34.1` and `v4.35.0-rc3`):** The architectural, key-semantics, publication/restoration, non-coverage, and `v4.30.0-rc2` → `v4.34.1` → `v4.35.0-rc3` source reviews in this package are source-only inspections (with checked-in test inspection for environment variables). Runtime behavior under filesystem contention, power loss, or malformed JSON recovery at `v4.34.1` and `v4.35.0-rc3` was **not examined** in this package (see the companion `lake-cache-seeded-equivalence-and-concurrency` report for executed `v4.30.0-rc2` cache and concurrency probes).
- **Non-cryptographic hashes (`known not to apply`):** Lake's `Hash` is a 64-bit `UInt64` non-cryptographic hash (`src/lake/Lake/Build/Trace.lean`, line 100), and local cache hits in `saveArtifact` and `resolveArtifact` trust existing content-addressed filenames without rehashing local bytes. Lake hashes must not be treated as cryptographic integrity or tamper-resistance commitments.
- **No atomic multi-writer mapping transaction (`unsupported`):** Even with `overwrite : Bool` in `v4.34.1`, the default `overwrite = true` path in `Cache.writeOutputsCore` uses `IO.FS.writeFile` without a temporary-file-and-rename protocol, lock, or `fsync`.
- **Broader `v4.30.0-rc2` cohort rows (`unknown` from source diff alone):** In the bounded 161-report source review (`support/lean-lake-430rc2-to-4341-source-review/matrix.json`), outside the 3 directly diffed Lake claims (`Cache.readOutputs?` error routing and the 2 `.lake/config` hoisting rows), the remaining 158 cohort rows were marked unresolved in that bounded review and require claim-specific source/execution checks rather than assuming continuity.

## Evidence

### Primary Upstream Source Blobs (`v4.30.0-rc2` @ `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`)
- `src/lake/Lake/Config/Artifact.lean` (blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`): `artifactPath`, `ArtifactDescr`, `ArtifactDescr.relPath`, `Artifact`, `Artifact.useLocalFile`, `Artifact.trace`.
- `src/lake/Lake/Config/Cache.lean` (blob `607e6b92108f30e0a57d0de682f7faa283d7d470`): `Cache`, `artifactDir`, `outputsDir`, `outputsFile`, `writeOutputsCore`, `writeOutputs`, `readOutputs?`, `CacheOutput`, `CacheMap`, `downloadArtifactCore`.
- `src/lake/Lake/Build/Common.lean` (blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`): `BuildMetadata`, `SavedTrace.replayIfUpToDate'`, `replayOrFetchIfUpToDate`, `fetchFileHash`, `Cache.saveArtifact`, `getArtifactsUsingCache?`, `getArtifactsUsingTrace?`, `getArtifacts?`, `resolveArtifact`, `restoreArtifact`, `buildFileUnlessUpToDate'`, `buildArtifactUnlessUpToDate`, `addLeanTrace`, `addPlatformTrace`, `addPureTrace`.
- `src/lake/Lake/Build/Trace.lean` (blob `656c991fab8a6475802373224514ec7e73f9b18b`): `Hash`, `BuildTrace`, `MixTrace`, `computeTextFileHash`.
- `src/lake/Lake/Build/Module.lean` (blob `21c5f343112a1690390188642a05d6092432ab84`): `Module.recBuildLean`, `ModuleOutputArtifacts`, `cacheOutputArtifacts`, `restoreNeededArtifacts`, `restoreAllArtifacts`, `packLtar`, `platformIndependent`.
- `src/lake/Lake/Build/ExternLib.lean` (blob `9ed94d229d3ca5d41173941e157d31f9b9f6b814`): `buildLeanSharedLibOfStatic` (`ExternLib.sharedFacet`).
- `src/lake/Lake/Build/Package.lean` (blob `2f55a2a5fde4280b2b61945f88c4e0b31d1b0ce3`): `maybeFetchBuildCache`, `fetchBuildArchive`.
- `src/lake/Lake/Config/Env.lean` (blob `eed315c538de746a891d18f72564e88aea64e969`), `src/lake/Lake/Config/InstallPath.lean` (blob `e309253fe8c39aa90ce48de295305d160286a9b1`), `src/lake/Lake/Config/Workspace.lean` (blob `b9c01f130240ae7c65ee298778351ddbe312374e`), `src/lake/Lake/Config/Package.lean` (blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`), `src/lake/Lake/Config/PackageConfig.lean` (blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`), `src/lake/Lake/Config/Monad.lean` (blob `59e032d7c516298a494c070abb948eafe2474184`), `src/lake/Lake/Util/IO.lean` (blob `35f92bf0053f3fca99f771f1b268f35760667d40`).
- Checked-in Lake tests at `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`: `tests/lake/tests/env/test.sh` (blob `4cdee6b9ed39234ab584fa0f47697351b2f98f10`, lines 32–53) and `tests/lake/tests/cache/test.sh` (blob `4c0134409f65b9e563cb3d7f26a1e550c013c140`, lines 26–39).

### Primary Upstream Source Files (`v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52` & `v4.35.0-rc3` @ `470d5ce1400764999581fd26d5d72b00d990b0f4`)
- `src/lake/Lake/Config/Cache.lean` at `v4.34.1` (1,101 lines, SHA-256 `c3ee5a7565a656d8...`, preserved at `support/lean-lake-4350rc3-output-reference-routing-source-followup/raw/leanprover/lean4/5045d0056413266e57c625dcd7c365b10e377c52/src/lake/Lake/Config/Cache.lean`) and at `v4.35.0-rc3` (`support/lean-lake-4350rc3-output-reference-routing-source-followup/raw/leanprover/lean4/470d5ce1400764999581fd26d5d72b00d990b0f4/src/lake/Lake/Config/Cache.lean`).
- `src/lake/Lake/Build/Common.lean` at `v4.34.1` (1,112 lines, SHA-256 `03c6017c49303720287e76e7c31decea54f1fddec5d0d7fd358e036e3b48575c`, preserved at `support/lean-lake-4350rc3-output-reference-routing-source-followup/raw/leanprover/lean4/5045d0056413266e57c625dcd7c365b10e377c52/src/lake/Lake/Build/Common.lean`), at `v4.35.0-rc3` (SHA-256 `ac4245ce6f64078d0204503c0340d27572e331c2a3df452b29432b463fe2fccd`, preserved at `support/lean-lake-4350rc3-output-reference-routing-source-followup/raw/leanprover/lean4/470d5ce1400764999581fd26d5d72b00d990b0f4/src/lake/Lake/Build/Common.lean`), and at later HEAD `193c3589a4fc16c4059261ab38cfa365eb24f323` (SHA-256 `653f29fa0b07ef75ee9f097f76d7183d2f508dfca1343c40cb648df7b11896e6`, preserved at `support/lean-lake-4350rc3-output-reference-routing-source-followup/raw/leanprover/lean4/193c3589a4fc16c4059261ab38cfa365eb24f323/src/lake/Lake/Build/Common.lean`).
- `src/lake/Lake/Build/Module.lean` at `v4.34.1` (1,553 lines, SHA-256 `4a84a2896dedea36...`), `src/lake/Lake/Build/Trace.lean` at `v4.34.1` (391 lines, SHA-256 `ae8987432fdb2f72...`), `src/lake/Lake/Build/Actions.lean` at `v4.34.1` (212 lines, SHA-256 `9c7d7101f89eb1d0...`), `src/lake/Lake/Config/Env.lean` at `v4.34.1` (344 lines, SHA-256 `bc976a2f9ae48066...`), and `src/lake/Lake/Config/Workspace.lean` at `v4.34.1` (435 lines, SHA-256 `80ae4168ce567b92...`).

### Package Support Artifacts
- `support/lake-artifact-cache-architecture/evidence-index.json`
- `support/lake-artifact-cache-key-semantics/evidence-index.json`
- `support/lake-artifact-cache-noncoverage/evidence-index.json`
- `support/lake-artifact-cache-publication-restoration/publication-restoration-state-machine.json`
- `support/lake-artifact-cache-publication-restoration/source-map.json`
- `support/lake-cache-environment/environment-matrix.json`
- `support/lake-cache-environment/source-map.json`
- `support/lean-lake-430rc2-to-4341-source-review/matrix.json`, `support/lean-lake-430rc2-to-4341-source-review/frozen-cohort.csv`, and `support/lean-lake-430rc2-to-4341-source-review/check_matrix.py`
- `support/lean-lake-4350rc3-output-reference-routing-source-followup/mapped_source_results.json`, `support/lean-lake-4350rc3-output-reference-routing-source-followup/upstream_refs.json`, `support/lean-lake-4350rc3-output-reference-routing-source-followup/verification-manifest.json`, `support/lean-lake-4350rc3-output-reference-routing-source-followup/COHORT-NOTE.md`, `support/lean-lake-4350rc3-output-reference-routing-source-followup/check.py`, and `support/lean-lake-4350rc3-output-reference-routing-source-followup/check_mapped_sources.py`

## Revalidation

1. **Offline support verification:**
   - Run `python3 -B support/lean-lake-4350rc3-output-reference-routing-source-followup/check.py` (with `--reference-root` when validating against the historical reference checkout) to verify retained SHA-256 digests, release refs, and mapped source predicates across `v4.34.1` and `v4.35.0-rc3`.
   - Diff the preserved raw `Common.lean` and `Cache.lean` files directly:
     ```bash
     diff -u support/lean-lake-4350rc3-output-reference-routing-source-followup/raw/leanprover/lean4/5045d0056413266e57c625dcd7c365b10e377c52/src/lake/Lake/Build/Common.lean \
             support/lean-lake-4350rc3-output-reference-routing-source-followup/raw/leanprover/lean4/470d5ce1400764999581fd26d5d72b00d990b0f4/src/lake/Lake/Build/Common.lean
     ```
2. **Targeted source revalidation on a newer Lake revision:**
   - Inspect `ArtifactDescr` (`Lake/Config/Artifact.lean`), `Cache.outputsFile`, `Cache.writeOutputsCore`, and `Cache.readOutputs?` (`Lake/Config/Cache.lean`) for schema or atomicity changes.
   - Inspect `buildArtifactUnlessUpToDate`, `getArtifactsUsingCache?`, `getArtifactsUsingTrace?`, `Cache.saveArtifact`, and `restoreArtifact` (`Lake/Build/Common.lean`) for lookup precedence, error handling on malformed JSON, `outputsRef?` predicate routing, and `OutputStatus.isCacheable` gating.
   - Inspect `Env.compute` (`Lake/Config/Env.lean`), `Workspace.computeLakeCache` (`Lake/Config/Workspace.lean`), and `Package.isArtifactCacheReadable` / `isArtifactCacheWritable` (`Lake/Config/Monad.lean`) for `LAKE_CACHE_DIR` and `LAKE_ARTIFACT_CACHE` semantics.
3. **Minimal execution probe:**
   - Using `anneal-lean-run`, construct a two-package fixture under a controlled `LAKE_CACHE_DIR` with `LAKE_ARTIFACT_CACHE=true`, build the producer to populate `artifacts/{hash}.{ext}` and `outputs/<scope>/<input-hash>.json`, and test: (a) read-only consumer cache fetch with `restore := true`, (b) trace-based mapping backfill after deleting `outputs/<scope>/<input-hash>.json`, and (c) cache-miss fallback after writing malformed JSON to `outputs/<scope>/<input-hash>.json` under `-v --no-ansi`.
