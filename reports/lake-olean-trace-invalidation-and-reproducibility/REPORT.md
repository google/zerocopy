# Lake Module `.olean` Invalidation, Build-Trace State Model, External SDK Identity, and Command/Environment Reproducibility

## Summary

In Lean 4 and Lake across `v4.30.0-rc2` (`leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52`, `Lake version 5.0.0-src+5045d00`), Lake separates six distinct state layers that must not be conflated when designing reproducible builds or prepared verification archives:
1. **Configuration state** (`Package`, `Workspace`, `Lake.Env`, `LakeConfig`) loaded from `lakefile.lean` / `lakefile.toml` and process environment.
2. **Dependency materialization state** (`lake-manifest.json`), which locks dependency paths and Git commits (`rev` / `inputRev`) without tracking compiled artifact freshness.
3. **Logical build identity** (`BuildKey` and `FacetConfig`), which names modules, packages, package targets, and typed facet projections (`leanArts`, `.olean`, `.olean.server`, `.olean.private`, `.ilean`, `.ir` / `.ir.sig`, `.c`, `.o`, `static`, `shared`).
4. **Execution state** (`Job α` and `JobState`), which tracks asynchronous tasks, build logs, `JobAction` (`unknown`, `replay`, `fetch`, `build`), `wantsRebuild` under `--no-build` (exit code `3` and sibling `*.trace.nobuild` files), and elapsed build time.
5. **Artifact state**, consisting of Lean-emitted module outputs and native build products stored under `<pkgDir>/.lake/build` or in Lake's content-addressed artifact cache (`{hash}.{ext}`).
6. **Freshness state** (`BuildTrace`, persisted `BuildMetadata` in `*.trace` files, and 64-bit `UInt64` content hashes in `*.hash` sidecars), which governs whether existing outputs are reused, fetched from cache, or rebuilt.

For a module's aggregate `leanArts` compilation (`Module.recBuildLean`), ordinary reuse (`SavedTrace.replayIfUpToDate'`) requires the newly computed dependency hash (`depTrace.hash`) to equal the saved `BuildMetadata.depHash` in `<Module>.trace` and all required outputs to exist. The top-level `leanArts` trace mixes eight components in order:
1. `mod.setup` job trace (which mixes `extraDep` trace, imported-module exported artifact and transitive traces from `ModuleImportInfo` / `Module.computeExportInfo`, and—conditioned on `platformIndependent`—`libTrace` for precompiled/external/dynamic libraries and plugins plus `platformTrace`);
2. Lean toolchain trace (`addLeanTrace`, hashing `ws.lakeEnv.leanGithash`, which comes from `Lean.githash` or `lean --githash` unless overridden by `LEAN_GITHASH`);
3. Module own-source trace (`Hash.ofText contents`, which normalizes CRLF to LF before hashing and treats the file path as an unhashed `BuildTrace.caption`);
4. Effective `setup.options` (`LeanOptions` combining build-type, package, and library `leanOptions`);
5. Module-system participation (`setup.isModule : Bool`);
6. Logical module name (`mod.name : Name`);
7. Lean package identifier (`mod.pkg.id?`, which is `none` for bootstrap packages and `some origName` otherwise, excluding `Package.version`); and
8. Non-weak Lean arguments (`mod.leanArgs`, combining build-type args and package/library `moreLeanArgs`, while deliberately excluding `weakLeanArgs` even though `weakLeanArgs` are prepended to the `lean` invocation).

An empirical execution canary on `v4.30.0-rc2` (`arm64-apple-darwin24.6.0`) and the June 2026 Anneal V1 macOS arm64 omnibus bundle (SHA-256 `b4e0a5b420eb441e37564c365f06c215f61a3b825fc3df37293da7c3010d2b81`) demonstrated two critical operational boundaries for external prebuilt SDKs:
- **External `LEAN_PATH` vs. extended sysroot**: `lake env` exports `Workspace.augmentedLeanPath` (which includes inherited `LEAN_PATH`), whereas `Module.buildLean` passes `Workspace.leanPath` (workspace package library directories only), causing `lake build` to fail on `import Sdk` when `Sdk.olean` is provided solely via `LEAN_PATH`. Placing `Sdk.olean` inside an extended Lean sysroot works only when **both** the `lean` (49,968 bytes) and `lake` (51,840 bytes) launcher binaries are copied (not symlinked) into the overlay's `bin/`, because `Lean.getBuildDir` resolves `IO.appDir` and `findLakeInstall?` resolves `IO.appPath`.
- **Silent stale proof reuse across sysroot SDK switches**: Because sysroot module artifacts are not traced by Lake's local module `depTrace`, switching `LEAN_SYSROOT` from frozen SDK v1 (`sdkValue = 10`, `Sdk.olean` SHA-256 `e1733ea9a13718cff38370c3bfd8943e2a9c0550ba53768cb631390b01315dea`) to frozen SDK v2 (`sdkValue = 20`, `Sdk.olean` SHA-256 `140067d410c7281b5541ef536b549c9edd58dbd47428a95e0af2dbfd5a05e6a1`) with unchanged consumer files replayed the stale `Client.olean` (SHA-256 `4b2214fb7481862b29f89ad74ea7a83c7e200f079a9826479963ee7c253a203a`, `depHash` `90b5218aeee20417`), allowing `#check clientProof` (`clientValue = sdkValue`) to succeed while `#eval decide (clientValue = sdkValue)` evaluated to `false`. Binding the consumer package name or an imported identity module to the SDK digest forced recompilation and rejected the false proof (exit code `1`).

Basis: source + execution + derived synthesis across `leanprover/lean4` (`v4.30.0-rc2` and `v4.34.1`), `AeneasVerif/aeneas` (`ac9f1bc5262a5e4ff1e24ca78617121382202727`), `google/zerocopy` (`41f5b37afe7060fd9fe08c00b200672cd76d77b9`), and the June 2026 macOS arm64 omnibus bundle (`b4e0a5b420eb441e37564c365f06c215f61a3b825fc3df37293da7c3010d2b81`).

## Applicability

The findings in this report apply to the following pinned subjects recorded in `REPORT.json` and cross-version baselines:
- **Lean 4 and Lake `v4.29.0`**: `leanprover/lean4` revision `98dc76e3c0a9b856c9b98726b713fb04fab16740` (historical comparison baseline for Lake trace and hash artifacts).
- **Lean 4 and Lake `v4.30.0-rc2`**: `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`Lake version 5.0.0-src+3dc1a08`), including the macOS arm64 (`arm64-apple-darwin24.6.0`) executables `lean` (49,968 bytes, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`) and `lake` (51,840 bytes, SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`).
- **Lean 4 and Lake `v4.31.0`**: `leanprover/lean4` revision `68218e876d2a38b1985b8590fff244a83c321783` (configuration-cache hoisting boundary).
- **Lean 4 and Lake `v4.34.1`**: `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`Lake version 5.0.0-src+5045d00`).
- **Anneal V1 macOS arm64 prebuilt Aeneas and Mathlib bundle**: `Anneal V1 macOS arm64 omnibus bundle, June 2026`, SHA-256 `b4e0a5b420eb441e37564c365f06c215f61a3b825fc3df37293da7c3010d2b81` (containing `libaeneas_AeneasMeta.dylib`, SHA-256 `0ffa1ca9ecf894cd4256c75a049287dd285225767c0b41ae9b2e9a3e6e7e4745`).
- **Aeneas Lean workspace**: `AeneasVerif/aeneas` revision `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).
- **Anneal authority and packaging**: `google/zerocopy` revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

### Scope and Subject Relationships

This report unifies:
1. The **Lake state model** (`Workspace`, `Package`, `Manifest`, `BuildKey`, `FacetConfig`, `Job`, `BuildTrace`, `BuildMetadata`, and `.hash` sidecars; detailed narrative preserved in [`support/lake-state-model/FINDINGS.md`](support/lake-state-model/FINDINGS.md)).
2. **Module `.olean` / `leanArts` invalidation rules** (`Module.recFetchInput`, `Module.recFetchSetup`, `Module.recBuildLean`, `platformIndependent`, `--old` mtime fallback, and configuration negative space).
3. **Lean-to-Lake trace and artifact-hash handoff** (`Lean.githash` / `LEAN_GITHASH`, 64-bit `UInt64` binary `.hash` sidecars, and per-output selective invalidation for `.olean`, `.olean.server`, `.olean.private`, and `.ir` / `.ir.sig`).
4. **Command and environment reproducibility inputs** (`LakeOptions`, `LoadConfig`, `BuildConfig`, `Lake.Env`, installation discovery, native compiler precedence, and `lake env` projection limits).
5. **External prebuilt SDK invalidation execution canary** (preserved in [`support/lean-external-sdk-invalidation/observations.json`](support/lean-external-sdk-invalidation/observations.json) and [`support/lean-external-sdk-invalidation/fixtures/`](support/lean-external-sdk-invalidation/fixtures/)).
6. **The 12-gate Lake upgrade checklist for Anneal** (preserved in [`support/lake-behavior-upgrade-checklist/lake-upgrade-checklist.json`](support/lake-behavior-upgrade-checklist/lake-upgrade-checklist.json)).

## Findings

### 1. Layered Lake State Model: Workspace, Build Keys, Jobs, Traces, and Sidecars

As detailed in [`support/lake-state-model/FINDINGS.md`](support/lake-state-model/FINDINGS.md), Lake's architecture separates configuration/dependency state from build-execution and freshness state:
- **`Workspace` and `Package`**: `loadWorkspaceRoot` loads the system `LakeConfig` and root `Package` (`lakefile.lean` preferred over `lakefile.toml` when both exist) before `loadWorkspace` resolves dependencies. Each loaded `Package` owns its `wsIdx`, `baseName`, `origName`, `keyName := baseName.num wsIdx`, `dir`, `relDir`, `buildDir` (default `.lake/build`), and `manifestFile` (`lake-manifest.json`).
- **`BuildKey` and `FacetConfig`**: Build requests are identified by typed `BuildKey` variants (`module`, `package`, `packageModule`, `packageTarget`, and `facet` over another key). A `FacetConfig` specifies expected input target kind, fetch function, output data kind, CLI buildability, and memoization policy in the build store.
- **`Job α` and `JobState`**: Fetching a target or facet through the topological/suspending build scheduler produces an asynchronous `Job α` carrying a `JobState` (`BuildTrace`, accumulated log, `JobAction` in `{unknown, replay, fetch, build}`, `wantsRebuild : Bool`, and build duration). Under `--no-build` (`BuildConfig.noBuild`), entering `buildAction` sets `wantsRebuild := true`, writes a diagnostic sibling `<target>.trace.nobuild` if `<target>.trace` exists, and exits with status `3`.
- **`BuildTrace` and `BuildMetadata`**: `BuildTrace` (`src/lake/Lake/Build/Trace.lean` in `v4.30.0-rc2`; `src/lean/lake/Lake/Build/Trace.lean`, 391 lines, SHA-256 `ae8987432fdb2f72...` in `v4.34.1`, with `MixTrace` at line 62, `Hash` at line 100, `checkAgainstHash` at line 378, and `checkAgainstTime` at line 386) combines a `caption : String`, child `inputs : Array BuildTrace`, a 64-bit `Hash` (`UInt64`), and `mtime : MTime`. Mixing two traces mixes their hashes and takes the maximum `mtime` without hashing the caption strings. Persisted `BuildMetadata` (schema `"2025-09-10"` in `v4.30.0-rc2`) records `depHash`, captioned `inputs`, optional `outputs` JSON, `log`, and `synthetic : Bool`.
- **Freshness decision (`SavedTrace.replayIfUpToDate'` and `buildUnlessUpToDate?`)**: In both `v4.30.0-rc2` (`Lake/Build/Common.lean` lines 190–267) and `v4.34.1` (`src/lean/lake/Lake/Build/Common.lean`, 1,112 lines, SHA-256 `03c6017c49303720...`, `SavedTrace.replayIfUpToDate'` at line 242, `buildUnlessUpToDate?` at line 349, `buildUnlessUpToDate` at line 368), Lake checks whether `depTrace.hash == saved.depHash` and required output files exist. If so, it replays `saved.log`. Only when `--old` (`BuildConfig.oldMode`) is enabled does a hash mismatch or missing trace fall back to comparing output modification times against `oldTrace` (`srcTrace.mtime` for modules).

Basis: source.

### 2. Module `leanArts` / `.olean` Invalidation Rules and Configuration Negative Space

Before `Module.recBuildLean` (`src/lake/Lake/Build/Module.lean` lines 874–970 in `v4.30.0-rc2`) checks `<Module>.trace` or queries the artifact cache, it constructs `depTrace` by mixing these exact components in order:

| Order | Trace Component | Source Mechanism | Invalidation Effect on Ordinary Module Reuse |
| ---: | --- | --- | --- |
| 1 | `mod.setup` job trace | `Module.recFetchSetup` (`Module.lean` lines 493–552) | Any change to `extraDep` trace, imported module export/transitive traces, or (when included by `platformIndependent`) `libTrace` / `platformTrace` invalidates. |
| 2 | Lean toolchain trace | `addLeanTrace` (`Build/Common.lean` lines 37–51; `Build/Run.lean` lines 25–34) | Hashes `ws.lakeEnv.leanGithash`. Any change to the detected Lean Git hash or `LEAN_GITHASH` override invalidates. |
| 3 | Module own-source trace | `Module.recFetchInput` (`Module.lean` lines 29–42) + `Hash.ofText` (`Trace.lean` lines 168–182) | Reads `.lean` source directly (no `.hash` sidecar), normalizes `\r\n` (CRLF) to `\n` (LF), and hashes the text. Caption is file path (unhashed). Semantic text edits invalidate; CRLF/LF-only edits and path-only moves do not alter this component. |
| 4 | `setup.options` | `traceOptions` over `LeanLib.leanOptions` (`LeanLib.lean` lines 123–197) | Combines build-type, package, and library `leanOptions`. Any effective option change invalidates. |
| 5 | `setup.isModule` | `Bool` trace | Toggling experimental module-system mode invalidates. |
| 6 | `mod.name` | `Name` trace (`Config/Module.lean` lines 14–25) | Renaming the logical module invalidates even if file bytes are unchanged. |
| 7 | `mod.pkg.id?` | `Option PkgId` (`Config/Package.lean` lines 152–165) | Hashes `none` for bootstrap packages and `some origName` otherwise. Changing `origName` invalidates; changing `Package.version` alone does not. |
| 8 | `mod.leanArgs` | `Array String` trace (`LeanConfig.lean` lines 154–180) | Combines build-type `leanArgs` and package/library `moreLeanArgs`. Changing `moreLeanArgs` invalidates; changing `weakLeanArgs` does **not**. |

#### Setup Trace Partitioning by `platformIndependent`

In `Module.recFetchSetup`, Lake separates `depTrace` (`extraDep` job trace + `info.trace` from parsed imports) from `libTrace` (traces of imported precompiled libraries, package external libraries, `dynlibs`, and `plugins`):

| Effective `platformIndependent` | Setup Trace Mixed into `leanArts` `depTrace` |
| --- | --- |
| `none` (default in Aeneas and Mathlib) | `depTrace` + `libTrace` (platform sensitivity propagates naturally from any native library/plugin in `libTrace`) |
| `some false` | `depTrace` + `libTrace` + host `platformTrace` (`System.Platform.target`) |
| `some true` | `depTrace` only (`libTrace` and `platformTrace` are omitted; Lake's docstring notes this is an unchecked configuration assertion) |

#### Configuration Negative Space (Edits That Do Not Directly Change `leanArts` `depTrace`)

Because Lake hashes effective projected values rather than raw `lakefile.lean` / `lakefile.toml` text, the following changes do **not** directly alter a module's `leanArts` dependency hash:
- `weakLeanArgs` (passed to `lean` in `Module.buildLean` at lines 849–861, but excluded from `recBuildLean`'s trace);
- `moreServerOptions` (used only by language-server setup);
- `moreLeancArgs`, `weakLeancArgs`, `moreLinkArgs`, and `weakLinkArgs` (consumed by downstream C compilation and linking facets rather than `leanArts`);
- Package `version`, `description`, `keywords`, `readmeFile`, or `licenseFiles`;
- Workspace or package directory paths that only alter `BuildTrace.caption` strings.

Basis: source + derived synthesis.

### 3. Lean-to-Lake Identity Handoff and Selective Per-Output `.hash` Sidecars

Lake does not inspect internal `.olean` headers to determine build freshness. Instead, the boundary between Lean and Lake consists of two mechanisms:
1. **Input toolchain identity (`leanGithash`)**: `LeanInstall.get` (`src/lake/Lake/Config/InstallPath.lean`, blob `e309253fe8c39aa90ce48de295305d160286a9b1`) uses compiled-in `Lean.githash` when Lake and Lean are collocated, or runs `lean --githash` otherwise. `Lake.Env.leanGithash` (`src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`) substitutes `LEAN_GITHASH` when that environment variable is non-empty. `Workspace.mkBuildContext'` (`src/lake/Lake/Build/Run.lean`, blob `afae31b7d20a37e6a505d4dc7a9ce875467faf7e`) wraps that string in `BuildTrace.ofHash (pureHash ws.lakeEnv.leanGithash)`.
2. **Post-compilation 64-bit output content hashes (`Module.computeArtifacts`)**: After `compileLeanModule` (`Lake/Build/Actions.lean` line 29) finishes, `Module.buildLean` clears existing `.hash` sidecars and calls `computeArtifact` -> `fetchFileHash` -> `computeBinFileHash` (`Lake/Build/Trace.lean` and `Lake/Build/Common.lean`) over each emitted binary file without CRLF normalization, writing a 16-hex-digit `UInt64` digest to `<output>.hash`. When `BuildConfig.trustHash` is `true` (default; disabled by `-H` / `--rehash`), subsequent builds read and trust existing `.hash` sidecars instead of rehashing the artifact bytes.

#### Selective Downstream Import Invalidation

`Module.computeExportInfo` (`Lake/Build/Module.lean` lines 434–479) and `ModuleImportInfo.addImport` (lines 257–352) construct distinct export traces from individual output artifact hashes (`tests/lake/tests/module/test.sh`, blob `50aeb17645d5f77296ca718cb5ceeb6db9f54f88`):
- **Public edit** (changes `<Mod>.olean.hash`): invalidates direct public importers and transitive public consumers.
- **Private edit** (preserves `<Mod>.olean.hash`, changes `<Mod>.olean.private.hash`): leaves ordinary public importers up to date while invalidating `import all` consumers.
- **Server edit** (changes `<Mod>.olean.server.hash`): leaves ordinary batch public importers up to date while updating server-mode consumers.
- **Meta/IR edit** (preserves `<Mod>.olean.hash`, changes `<Mod>.ir.hash` or `.ir.sig.hash` in `v4.34.1`): invalidates `meta` and `import all` consumers while leaving ordinary public importers current.

Basis: source + checked-in test source.

### 4. Command and Environment Reproducibility Surface

Lake constructs `Lake.Env` (`Lake/Config/Env.lean`), `LoadConfig` (`Lake/Load/Config.lean`), and `BuildConfig` (`Lake/Build/Context.lean`) from CLI flags (`Lake/CLI/Main.lean`) and process environment variables:

| Input Category | Flags / Environment Variables | Reproducibility Role & Precedence |
| --- | --- | --- |
| Workspace & config path | `-d` / `--dir`, `-f` / `--file`, ambient `cwd` | Selects `wsDir` and `relConfigFile` (`lakefile.lean` vs. `lakefile.toml`). |
| Dependency & config overrides | `--packages=<file>`, `.lake/package-overrides.json`, `-K<key>=<val>` | Replaces locked manifest entries by name (`LoadConfig.packageOverrides`) or passes options to Lean `lakefile` elaboration (`LoadConfig.lakeOpts`). |
| Lifecycle & validation mode | `--update`, `--keep-toolchain`, `--reconfigure` (`-R`), `--old`, `--rehash` (`-H`), `--no-build` | Switches between locked load and update, forces `lakefile` re-elaboration, enables mtime fallback (`oldMode`), disables `.hash` sidecar trust (`trustHash := false`), or fails with exit code `3` when a target needs building. |
| Cache policy & location | `--no-cache`, `--try-cache`, `LAKE_NO_CACHE`, `LAKE_ARTIFACT_CACHE`, `LAKE_CACHE_DIR`, `LAKE_CONFIG`, `LAKE_CACHE_KEY`, `LAKE_CACHE_ARTIFACT_ENDPOINT`, `LAKE_CACHE_REVISION_ENDPOINT`, `LAKE_CACHE_SERVICE` | CLI `--no-cache` (`some true`) and `--try-cache` (`some false`) override `LAKE_NO_CACHE`. `LAKE_CACHE_DIR` has three states: unset (uses Elan toolchain cache or user `~/.lake/cache`), non-empty path (sets both `lakeCache?` and `lakeSystemCache?`), or **empty string `""`** (`noSystemCache := true`, disabling system cache fallback). `LAKE_CONFIG` overrides `~/.lake/config.toml`. |
| Toolchain & Lean discovery | `ELAN_TOOLCHAIN`, `LEAN_SYSROOT`, `LEAN`, `LAKE_OVERRIDE_LEAN`, `LEAN_GITHASH`, `LAKE_HOME`, `ELAN_HOME`, `ELAN` | `LEAN_SYSROOT` takes precedence over `LEAN` (empty `LEAN=""` disables `LEAN` discovery; fallback is `lean --print-prefix` on `PATH`). `LAKE_OVERRIDE_LEAN=true` forces independent Lean discovery even when `lake` and `lean` are collocated. `LEAN_GITHASH` overrides the Lean commit hash mixed into `leanTrace`. |
| Native C compiler & archiver | `LEAN_CC`, bundled `clang`, `CC`, `cc` on `PATH`; `LEAN_AR`, bundled `llvm-ar`, `AR`, `ar` on `PATH` | `LeanInstall.get` resolves C compiler and archiver in exact four-tier precedence; bundled `clang` also alters default compiler flags. |
| Remote dependency endpoints | `LAKE_PKG_URL_MAP`, `RESERVOIR_API_URL`, `RESERVOIR_API_BASE_URL` | `LAKE_PKG_URL_MAP` remaps Git URLs by package name. `RESERVOIR_API_URL` overrides `RESERVOIR_API_BASE_URL ++ "/v1"` (default `https://reservoir.lean-lang.org/api/v1`). |
| Search paths & `lake env` | `LEAN_PATH`, `LEAN_SRC_PATH`, `PATH`, `LD_LIBRARY_PATH` / `DYLD_LIBRARY_PATH` | `lake env` exports `Workspace.augmentedEnvVars` (prepending workspace package `bin`, `lib/lean`, `src`, and shared-library paths), which is an observable projection rather than a complete build digest. |
| `--offline` CLI trap | `--offline` (`LakeOptions.offline`) | Parsed into `LakeOptions.offline` and passed to `lake new` / `lake init`, but **omitted** from `LakeOptions.mkLoadConfig` during `lake build`. `lake build --offline` does not enforce network denial. |

Basis: source.

### 5. External Prebuilt SDK Invalidation Canary and Launcher Coherency (`v4.30.0-rc2` Execution)

Executed on 2026-10-03 on `arm64-apple-darwin24.6.0` using `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`) and preserved in [`support/lean-external-sdk-invalidation/observations.json`](support/lean-external-sdk-invalidation/observations.json), [`support/lean-external-sdk-invalidation/check.py`](support/lean-external-sdk-invalidation/check.py), [`support/lean-external-sdk-invalidation/reproduce.py`](support/lean-external-sdk-invalidation/reproduce.py), and [`support/lean-external-sdk-invalidation/fixtures/`](support/lean-external-sdk-invalidation/fixtures/):

1. **`lake env` vs. `lake build` external `LEAN_PATH` split**:
   - Two tiny SDK versions were compiled once and frozen: SDK v1 (`def sdkValue : Nat := 10`, [`support/lean-external-sdk-invalidation/fixtures/Sdk-v1.lean`](support/lean-external-sdk-invalidation/fixtures/Sdk-v1.lean), `Sdk.olean` SHA-256 `e1733ea9a13718cff38370c3bfd8943e2a9c0550ba53768cb631390b01315dea`) and SDK v2 (`def sdkValue : Nat := 20`, [`support/lean-external-sdk-invalidation/fixtures/Sdk-v2.lean`](support/lean-external-sdk-invalidation/fixtures/Sdk-v2.lean), `Sdk.olean` SHA-256 `140067d410c7281b5541ef536b549c9edd58dbd47428a95e0af2dbfd5a05e6a1`).
   - With `LEAN_PATH=<frozen-SDK-lib>`, `lake env` included `<frozen-SDK-lib>` (`Workspace.augmentedLeanPath` in `Lake/Config/Workspace.lean` lines 288–327), but `lake build Client` failed with `unknown module prefix 'Sdk'` because `Module.buildLean` (`Lake/Build/Module.lean` lines 849–861) passes `getLeanPath` (`Workspace.leanPath`, containing only workspace package library directories).
2. **Extended sysroot launcher coherency**:
   - **Overlay 1 (symlinked `bin/lean`)**: Failed to import `Sdk.olean` placed under the overlay's `lib/lean` because `Lean.getBuildDir` (`src/lean/Lean/Util/Path.lean` lines 84–85) resolves `IO.appDir` through the symlink to the stock sysroot.
   - **Overlay 2 (copied 49,968-byte `bin/lean`, symlinked `bin/lake`)**: `lake build Client` succeeded when `LEAN_SYSROOT` pointed at the overlay with `LAKE_OVERRIDE_LEAN=true`, but `lake env lean Inspect.lean` still resolved the stock installation because `findLakeInstall?` (`src/lake/Lake/Config/InstallPath.lean` lines 347–360) resolved `IO.appPath` from the symlinked `lake` binary.
   - **Overlay 3 (coherent copied `bin/lean` and `bin/lake`, symlinked runtime/library tree)**: `lake env lean --print-prefix` returned the overlay sysroot, `lake build` and `lake setup-file` succeeded, and on the June 2026 macOS arm64 omnibus bundle (`b4e0a5b420eb441e37564c365f06c215f61a3b825fc3df37293da7c3010d2b81`) a private module importing `AeneasMeta.Saturate.Tactic` dynamically loaded `libaeneas_AeneasMeta.dylib` (SHA-256 `0ffa1ca9ecf894cd4256c75a049287dd285225767c0b41ae9b2e9a3e6e7e4745`) with zero writes to the read-only bundle.
3. **Silent stale proof replay across sysroot SDK switch and invalidation controls**:
   - Consumer [`support/lean-external-sdk-invalidation/fixtures/Client.lean`](support/lean-external-sdk-invalidation/fixtures/Client.lean) (SHA-256 `32360b65999d561922aaebccd74e9caef29e6a471f594ae091ea189356aeb81e`) and [`support/lean-external-sdk-invalidation/fixtures/consumer-lakefile.lean`](support/lean-external-sdk-invalidation/fixtures/consumer-lakefile.lean) (SHA-256 `d85e761d1073b61f157c0c346fd930d787631603ee47ce1c0611e7f8ca98c9dd`) define `def clientValue : Nat := 10` and `theorem clientProof : clientValue = sdkValue := by decide`.

| Consumer Execution Cell | Exit Code | `#eval clientValue` | `#eval sdkValue` | `#eval decide (clientValue = sdkValue)` | `#check clientProof` | Local `Client.olean` SHA-256 & `depHash` |
| --- | ---: | ---: | ---: | --- | --- | --- |
| Build & inspect against frozen SDK v1 (`sdkValue = 10`) | `0` | `10` | `10` | `true` | available (`clientValue = sdkValue`) | `4b2214fb7481862b29f89ad74ea7a83c7e200f079a9826479963ee7c253a203a` (`depHash` `90b5218aeee20417`, `Client.trace` SHA-256 `8e60db6762802f1089f9cc9626bb2d90924fdac363ea1547e965cf5b11069b86`) |
| Switch `LEAN_SYSROOT` to frozen SDK v2 (`sdkValue = 20`), keep consumer bytes & mtime identical | `0` | `10` | `20` | `false` | **still available** (stale proof replayed!) | Reused unchanged `4b2214fb7481...` (`depHash` `90b5218aeee20417`) |
| Control A: rename root package `probe_consumer` -> `probe_consumer_renamed` on SDK v2 | `1` | — | — | — | rejected (`decide` failed) | `mod.pkg.id?` changed -> forced rebuild |
| Control B: update imported local `SdkIdentity.lean` from `"v1"` to `"v2"` on SDK v2 | `1` | — | — | — | rejected (`decide` failed) | Imported local `.olean` hash changed -> forced rebuild |
| Control C: run `lake clean` before building on SDK v2 | `1` | — | — | — | rejected (`decide` failed) | Missing local outputs -> forced rebuild |

Because sysroot modules are not part of `ModuleImportInfo`'s workspace package artifact traces, Lake's `depHash` (`90b5218aeee20417`) does not change when an extended sysroot's prebuilt `.olean` changes while `leanGithash` stays constant. Any system that injects prebuilt libraries via an extended sysroot must bind the consumer's traced inputs (`LEAN_GITHASH`, root package name, or a generated `SdkIdentity` module) to the cryptographic digest of the SDK bundle.

Basis: execution + source + derived synthesis.

### 6. Version Deltas (`v4.30.0-rc2` to `v4.34.1`) and Upgrade Gates

Comparing `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) with `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) across the 12 upgrade gates in [`support/lake-behavior-upgrade-checklist/lake-upgrade-checklist.json`](support/lake-behavior-upgrade-checklist/lake-upgrade-checklist.json) (source map in [`support/lake-behavior-upgrade-checklist/source-map.json`](support/lake-behavior-upgrade-checklist/source-map.json)) establishes these exact `v4.34.1` deltas:

1. **Artifact cache schema bump and malformed-JSON error handling (`Lake/Config/Cache.lean` & `Lake/Build/Common.lean`)**:
   - In `v4.34.1`, `src/lean/lake/Lake/Config/Cache.lean` (1,101 lines, SHA-256 `c3ee5a7565a656d8...`) sets `CacheOutput.schemaVersion : String := "2026-02-25"` (line 339, `structure CacheOutput` at line 341) and defines `getArtifact?` at line 407.
   - `writeOutputsCore` (line 434) and `writeOutputs` (line 449) add an `overwrite : Bool := true` parameter (`true` invokes `IO.FS.writeFile`; `false` invokes `writeFileIfNew`).
   - In `v4.30.0-rc2`, `Cache.readOutputs?` logged a warning and returned `none` directly when an output mapping JSON file was malformed or had an incompatible schema. In `v4.34.1`, `readOutputs?` (line 463) throws an error via `error`, which is caught by `getArtifactsUsingCache?` in `src/lean/lake/Lake/Build/Common.lean` (line 521), logged at verbose level, and converted to `none` (cache miss).
2. **Module-system `.ir.sig` artifact facet (`Lake/Build/Module.lean`)**:
   - In `v4.34.1`, `src/lean/lake/Lake/Build/Module.lean` (1,553 lines, SHA-256 `4a84a2896dedea36...`, `Module.presetupFacetConfig` at line 630) adds `.ir.sig` alongside `.olean`, `.olean.server`, `.olean.private`, `.ilean` (lines 678–710), and `.c` (lines 266, 468–471).
3. **Configuration cache hoisting (`Lake/Load/Config.lean` & `Lake/Load/Lean/Elab.lean`)**:
   - Gate 3 of the upgrade checklist notes that in `v4.30.0-rc2`, Lean-authored dependency `lakefile.lean` files compiled into `<pkgDir>/.lake/config/<pkgName>/`. In `v4.31.0` and `v4.34.1`, `LoadConfig.configDir` (`Config.lean` line 83) writes all compiled configuration files under the root workspace's `<wsDir>/.lake/config/<pkgIdx>/`.
4. **CLI entry points (`Lake/CLI/Main.lean`)**:
   - In `v4.34.1`, `src/lean/lake/Lake/CLI/Main.lean` (1,333 lines, SHA-256 `3afad780df8292a7...`) parses `--no-build` at line 283, dispatches `lake.build` at line 918, `setupFile` (`lake setup-file`) at lines 1021 and 1289, and `serve` (`lake serve`) at line 1151, while `src/lean/lake/Lake/Config/Env.lean` (344 lines, SHA-256 `bc976a2f9ae48066...`) handles `LAKE_NO_CACHE` (lines 39, 176, 296), `LAKE_ARTIFACT_CACHE` (lines 43, 177, 311), and `LAKE_CACHE_DIR` (lines 47–56), and `src/lean/lake/Lake/Config/Workspace.lean` (435 lines, SHA-256 `80ae4168ce567b92...`) defines `computeLakeCache` at line 31.

Basis: source across `v4.30.0-rc2` and `v4.34.1`.

## Boundaries

- **Cryptographic collision resistance of `.hash` and `.trace` digests — `known not to apply`**: Lake's `Hash` is a 64-bit non-cryptographic `UInt64` hash (`src/lake/Lake/Build/Trace.lean` includes an explicit TODO to replace the built-in hash with a cryptographic hash) and is **known not to apply** as a security or adversarial-authenticity digest.
- **Toolchain binary identity from `leanTrace` alone — `known not to apply`**: Because `LEAN_GITHASH` can override `ws.lakeEnv.leanGithash`, a matching `leanTrace` is **known not to apply** as proof that the same physical `lean` binary was executed unless `LEAN_GITHASH` is controlled.
- **Arbitrary subprocess environment hermeticity — `not examined`**: While Lake's own `Lake.Env` surface is inventoried above, environment variables read by arbitrary user `run_io` blocks, custom `lakefile` scripts, `clang`, `ar`, `git`, or `curl` were **not examined** exhaustively; see [`support/lake-state-model/BOUNDARIES.md`](support/lake-state-model/BOUNDARIES.md).
- **Network isolation from `lake build --offline` — `known not to apply` / `unsupported`**: Passing `--offline` to `lake build` is **known not to apply** to `LoadConfig` in `v4.30.0-rc2` and is **unsupported** as a build-time firewall.
- **Live LSP server behavior on the coherent extended-sysroot overlay — `not examined`**: The `lean-external-sdk-invalidation` canary verified `lake build`, `lake setup-file`, and `lake env lean` on the coherent copied-launcher view, but live `lean --server` edit sessions on that overlay were **not examined**.

## Evidence

### 1. Pinned `leanprover/lean4` Sources (`v4.30.0-rc2` @ `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`)

See [`support/lake-state-model/EVIDENCE.md`](support/lake-state-model/EVIDENCE.md) and [`support/lake-behavior-upgrade-checklist/source-map.json`](support/lake-behavior-upgrade-checklist/source-map.json):
- `src/lake/Lake/Build/Module.lean` (blob `21c5f343112a1690390188642a05d6092432ab84`, lines 29–42, 110–163, 257–552, 708–743, 849–970): `Module.recFetchInput`, `ModuleImportInfo`, `fetchImportInfo`, `Module.computeExportInfo`, `Module.recFetchSetup`, `Module.checkExists`, `Module.buildLean`, and `Module.recBuildLean`.
- `src/lake/Lake/Build/Common.lean` (blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`, lines 33–51, 190–267, 740–830): `addPlatformTrace`, `addLeanTrace`, `BuildMetadata`, `SavedTrace.replayIfUpToDate'`, `buildUnlessUpToDate?`, `fetchFileHash`, and `computeArtifact`.
- `src/lake/Lake/Build/Trace.lean` (blob `656c991fab8a6475802373224514ec7e73f9b18b`, lines 168–182, 317–380): `Hash` (`UInt64`), `Hash.ofText` (CRLF normalization), `computeBinFileHash`, and `BuildTrace.mix`.
- `src/lake/Lake/Build/Run.lean` (blob `afae31b7d20a37e6a505d4dc7a9ce875467faf7e`, lines 25–34) & `src/lake/Lake/Build/Context.lean` (blob `8f2eda8d462334f933f112d7ebc4acd3e9553568`): `mkBuildContext'`, `leanTrace`, `BuildConfig` (`oldMode`, `trustHash`, `noBuild`).
- `src/lake/Lake/Build/ModuleArtifacts.lean` (blob `9863290328250c33d9933b1569387d96ec244da8`) & `src/lake/Lake/Config/Artifact.lean` (blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`): `ArtifactDescr`, `Artifact.trace`, and per-module artifact descriptors.
- `src/lake/Lake/Config/LeanConfig.lean` (blob `9fdd5a656c4316ee6beb45bdc9a1be4dd8d5d42a`, lines 154–220), `src/lake/Lake/Config/LeanLib.lean` (blob `077efb6c244fd53bab5dead6c850d40161c96e7f`, lines 123–240), `src/lake/Lake/Config/Module.lean` (blob `f8b938e16fe53ada616364033b8d8353baa733ee`, lines 14–25), and `src/lake/Lake/Config/Package.lean` (blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`, lines 152–165).
- `src/lake/Lake/CLI/Main.lean` (blob `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`), `src/lake/Lake/Load/Config.lean` (blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`), `src/lake/Lake/Config/Env.lean` (blob `eed315c538de746a891d18f72564e88aea64e969`), `src/lake/Lake/Config/InstallPath.lean` (blob `e309253fe8c39aa90ce48de295305d160286a9b1`, lines 347–360), `src/lake/Lake/Config/Workspace.lean` (blob `b9c01f130240ae7c65ee298778351ddbe312374e`, lines 288–327), `src/lake/Lake/Config/Monad.lean` (lines 136–154), and `src/lean/Lean/Util/Path.lean` (lines 84–85).
- `tests/lake/tests/module/test.sh` (blob `50aeb17645d5f77296ca718cb5ceeb6db9f54f88`): selective invalidation across `.olean.hash`, `.olean.private.hash`, `.olean.server.hash`, and `.ir.hash`.

### 2. Pinned `leanprover/lean4` Sources (`v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`)

- `src/lean/lake/Lake/Config/Cache.lean` (1,101 lines, SHA-256 `c3ee5a7565a656d8...`): `CacheOutput.schemaVersion := "2026-02-25"` (line 339), `getArtifact?` (line 407), `writeOutputsCore` (line 434), `writeOutputs` (line 449), `readOutputs?` (line 463).
- `src/lean/lake/Lake/Build/Common.lean` (1,112 lines, SHA-256 `03c6017c49303720...`): `SavedTrace.replayIfUpToDate'` (line 242), `buildUnlessUpToDate?` (line 349), `buildUnlessUpToDate` (line 368), `getArtifactsUsingCache?` (line 521).
- `src/lean/lake/Lake/Build/Trace.lean` (391 lines, SHA-256 `ae8987432fdb2f72...`): `MixTrace` (line 62), `Hash` (line 100), `checkAgainstHash` (line 378), `checkAgainstTime` (line 386).
- `src/lean/lake/Lake/Build/Actions.lean` (212 lines, SHA-256 `9c7d7101f89eb1d0...`): `compileLeanModule` (line 29), `compileO` (line 111), `compileStaticLib` (line 137), `compileSharedLib` (line 149).
- `src/lean/lake/Lake/Build/Module.lean` (1,553 lines, SHA-256 `4a84a2896dedea36...`): `Module.presetupFacetConfig` (line 630), `.olean.server`, `.olean.private`, and `.ir.sig` facets (lines 266, 468–471, 678–710).
- `src/lean/lake/Lake/Config/Env.lean` (344 lines, SHA-256 `bc976a2f9ae48066...`), `src/lean/lake/Lake/Config/Workspace.lean` (435 lines, SHA-256 `80ae4168ce567b92...`), and `src/lean/lake/Lake/CLI/Main.lean` (1,333 lines, SHA-256 `3afad780df8292a7...`).

### 3. Execution Artifacts and Preserved Support Material

- **External SDK invalidation canary (2026-10-03)**: [`support/lean-external-sdk-invalidation/observations.json`](support/lean-external-sdk-invalidation/observations.json) (20 guarded execution cells), [`support/lean-external-sdk-invalidation/check.py`](support/lean-external-sdk-invalidation/check.py), [`support/lean-external-sdk-invalidation/reproduce.py`](support/lean-external-sdk-invalidation/reproduce.py), and source fixtures [`support/lean-external-sdk-invalidation/fixtures/Client.lean`](support/lean-external-sdk-invalidation/fixtures/Client.lean), [`support/lean-external-sdk-invalidation/fixtures/Client-identity.lean`](support/lean-external-sdk-invalidation/fixtures/Client-identity.lean), [`support/lean-external-sdk-invalidation/fixtures/Inspect.lean`](support/lean-external-sdk-invalidation/fixtures/Inspect.lean), [`support/lean-external-sdk-invalidation/fixtures/Sdk-v1.lean`](support/lean-external-sdk-invalidation/fixtures/Sdk-v1.lean), [`support/lean-external-sdk-invalidation/fixtures/Sdk-v2.lean`](support/lean-external-sdk-invalidation/fixtures/Sdk-v2.lean), [`support/lean-external-sdk-invalidation/fixtures/SdkIdentity-v1.lean`](support/lean-external-sdk-invalidation/fixtures/SdkIdentity-v1.lean), [`support/lean-external-sdk-invalidation/fixtures/SdkIdentity-v2.lean`](support/lean-external-sdk-invalidation/fixtures/SdkIdentity-v2.lean), [`support/lean-external-sdk-invalidation/fixtures/consumer-lakefile.lean`](support/lean-external-sdk-invalidation/fixtures/consumer-lakefile.lean), [`support/lean-external-sdk-invalidation/fixtures/consumer-identity-lakefile.lean`](support/lean-external-sdk-invalidation/fixtures/consumer-identity-lakefile.lean), and [`support/lean-external-sdk-invalidation/fixtures/sdk-lakefile.lean`](support/lean-external-sdk-invalidation/fixtures/sdk-lakefile.lean).
- **Lake state model and upgrade checklist support**: [`support/lake-state-model/FINDINGS.md`](support/lake-state-model/FINDINGS.md), [`support/lake-state-model/BOUNDARIES.md`](support/lake-state-model/BOUNDARIES.md), [`support/lake-state-model/EVIDENCE.md`](support/lake-state-model/EVIDENCE.md), [`support/lake-state-model/REVALIDATION.md`](support/lake-state-model/REVALIDATION.md), [`support/lake-behavior-upgrade-checklist/lake-upgrade-checklist.json`](support/lake-behavior-upgrade-checklist/lake-upgrade-checklist.json), and [`support/lake-behavior-upgrade-checklist/source-map.json`](support/lake-behavior-upgrade-checklist/source-map.json).
- **Aeneas & Anneal packaging sources**: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`backends/lean/lean-toolchain` blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`; `backends/lean/lake-manifest.json` blob `1a5af703163d8b39f4311aafe22ae171788179ee`) and `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix` blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`).

## Revalidation

1. **Offline verification of preserved SDK invalidation evidence**:
   ```bash
   python3 support/lean-external-sdk-invalidation/check.py
   ```
2. **Active replay of the external SDK invalidation canary on an installed toolchain**:
   ```bash
   python3 support/lean-external-sdk-invalidation/reproduce.py \
     --lean-root /path/to/lean-toolchain \
     --scratch /path/to/nonexistent-scratch-dir \
     --run
   ```
3. **Source and behavioral revalidation on a new Lean/Lake release** (see [`support/lake-state-model/REVALIDATION.md`](support/lake-state-model/REVALIDATION.md) and [`support/lake-behavior-upgrade-checklist/lake-upgrade-checklist.json`](support/lake-behavior-upgrade-checklist/lake-upgrade-checklist.json)):
   - Diff `Module.recFetchInput`, `Module.recFetchSetup`, `Module.recBuildLean`, `Module.computeExportInfo`, `SavedTrace.replayIfUpToDate'`, `getArtifactsUsingCache?`, `CacheOutput.schemaVersion`, and `Lake.Env.compute`.
   - Execute the single-dimension mutation matrix on a two-module workspace (own-source semantic edit vs. CRLF-only edit vs. path relocation, `leanOptions`, `moreLeanArgs` vs. `weakLeanArgs`, `origName` vs. `Package.version`, public vs. private/server/IR import edits, `--old` vs. default hash checking, and `--rehash` vs. trusted `.hash` sidecars).
