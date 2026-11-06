# Lake Configuration Elaboration, `.lake/config` Cache Invalidation, Priming, and Workspace Ownership

## Summary

Across Lean 4 and Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), `v4.30.0` final (`leanprover/lean4@d024af099ca4bf2c86f649261ebf59565dc8c622`), `v4.31.0` (`leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783`), and `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), Lake splits persistent mutable state across three ownership domains—the **root workspace** (`<wsDir>`), each **loaded package** (`<pkgDir>`), and the **Lake artifact cache** (`LAKE_CACHE_DIR` or `<wsDir>/.lake/cache`)—with a decisive architectural shift in compiled Lean configuration cache placement between `v4.30.0-rc2` and `v4.30.0`/`v4.31.0`/`v4.34.1`:

1. **Compiled configuration cache hoisting (`v4.30.0-rc2` vs. `v4.30.0`, `v4.31.0`, and `v4.34.1`):**
   - At `v4.30.0-rc2` (`3dc1a088b6d2`), `importConfigFile` (`Lake/Load/Lean/Elab.lean`) derived `configDir` from package-local `cfg.lakeDir` (`cfg.pkgDir / ".lake"`), writing `<pkgDir>/.lake/config/<pkgName>/lakefile.{olean,olean.trace,olean.lock}` inside each dependency's own source tree even though `ConfigTrace` validated workspace-assigned `idx` and `name`. Sharing a path dependency across workspaces with different dependency indices or without a pre-primed cache forced dependency-local writes and failed on read-only dependency trees.
   - Starting in commit `41ecccec6d1244c5f89be2fc76638f22ba37cbc6` (present in `v4.30.0` final `d024af099ca4`, `v4.31.0` `68218e876d2a`, and `v4.34.1` `5045d0056413`), `LoadConfig.configDir` (`Lake/Load/Config.lean`, line 83 in `v4.34.1`) is hoisted to the consumer workspace:
     ```lean
     cfg.wsDir / defaultLakeDir / "config" / toString cfg.pkgIdx
     ```
     and `importConfigFile` (`Lake/Load/Lean/Elab.lean`, lines 180–185 in `v4.34.1`) writes `.olean` (plus `.olean.private` and `.olean.server` when applicable), `.olean.trace`, and `.olean.lock` under `<wsDir>/.lake/config/<pkgIdx>/`.
   - **Residual package-local directory creation caveat:** Even in `v4.30.0`, `v4.31.0`, and `v4.34.1`, `LoadConfig.lakeDir` remains `cfg.pkgDir / defaultLakeDir`, and the missing-trace branch of `importConfigFile` still calls `IO.FS.createDirAll cfg.lakeDir`. An already-prepared read-only dependency whose `<pkgDir>/.lake` directory exists is unaffected, whereas a pristine read-only dependency without `.lake` still encounters a directory-creation attempt on a trace miss.
2. **`.lake/config` trace schema, freshness predicate, and locking:**
   - `ConfigTrace` (`lakefile.olean.trace`) serializes six fields: `idx : Nat`, `name : Name`, `platform : String`, `leanHash : String`, `configHash : Hash` (CRLF-normalized text hash via `computeTextFileHash`), and `options : NameMap String` (`-K` Lake options).
   - The ordinary `upToDate` check compares `olean.pathExists`, `idx`, `name`, `configHash`, `platform`, and `leanHash`, but **omits** `cfg.lakeOpts` (`-K`) and `cfg.leanOpts`. Stale-trace automatic re-elaboration reuses `trace.options` unless `-R` / `--reconfigure` is passed.
   - Readers take a shared lock on `.olean.trace`; stale readers attempt a non-blocking `tryLock` on `.olean.lock` before upgrading to an exclusive trace lock, failing fast with `"could not acquire an exclusive configuration lock"` on concurrent reconfiguration.
   - TOML configurations (`lakefile.toml` via `loadTomlConfig` in `Lake/Load/Toml.lean`) parse directly into `Package` without creating a `.lake/config` slot.
3. **Executed multi-version verification (`v4.30.0-rc2`, `v4.30.0`, `v4.31.0`, `v4.34.1`):**
   - A 24-run matrix comparing `v4.30.0-rc2` and `v4.30.0` final (`support/lake-frozen-package-config-ownership/`) proved that `v4.30.0` final replayed a read-only dependency across reordered dependencies and missing consumer manifests by writing `.lake/config/{0,1,2}` under the consumer, whereas `v4.30.0-rc2` exited `1` (permission denied on `probe_shared/.lake/config/probe_shared/lakefile.olean.lock`). Both versions exited `3` and attempted to write `probe_shared/.lake/build/lib/lean/Shared.trace.nobuild` when `Shared.olean` was deleted under `--no-build`.
   - An 8-command runtime probe across `v4.31.0` and `v4.34.1` (`support/lake-configuration-ownership-431-434-runtime/`) confirmed identical numeric slot placement (`a/.lake/config/1/`, `b/.lake/config/2/`, and TOML root `t/.lake/config/1/` with no `t/.lake/config/0/`) and observed creation of an empty `shared/.lake` directory on first load.

## Applicability

This report synthesizes source and runtime evidence across the five subjects in `REPORT.json`:

1. **Lean 4 / Lake `v4.30.0-rc2`:** `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`component: Lake`).
2. **Lean 4 / Lake `v4.30.0` final:** `leanprover/lean4` revision `d024af099ca4bf2c86f649261ebf59565dc8c622`.
3. **Lean 4 / Lake `v4.31.0`:** `leanprover/lean4` revision `68218e876d2a38b1985b8590fff244a83c321783` (115 commits ahead of hoisting commit `41ecccec6d1244c5f89be2fc76638f22ba37cbc6`).
4. **Lean 4 / Lake `v4.34.1`:** `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`Lake version 5.0.0-src+5045d00`, `component: Lake`).
5. **Anneal V1 package-config priming implementation:** `google/zerocopy` revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix` and `anneal/v1/src/aeneas.rs`).

## Findings

### 1. Workspace-Owned vs. Package-Owned Mutable State

Across `v4.30.0-rc2` through `v4.34.1`, Lake (`src/lake/Lake/Config/Workspace.lean`, 435 lines, SHA-256 `80ae4168ce567b92...` in `v4.34.1`; `src/lake/Lake/Config/Package.lean`; `src/lake/Lake/Load/Manifest.lean`, 313 lines, SHA-256 `8b01bdff19b7e4cb...` in `v4.34.1`; `src/lake/Lake/Load/Resolve.lean`, 627 lines, SHA-256 `f90d1e01f6ee9d60...` in `v4.34.1`; `src/lake/Lake/Load/Materialize.lean`) partitions persistent filesystem state by package and workspace directories:

| Mutable State Class | Effective Owner | Default Location (`v4.30.0-rc2`) | Default Location (`v4.30.0` / `v4.31.0` / `v4.34.1`) | Shared Across Two Workspaces Sharing One Path Dependency? |
| --- | --- | --- | --- | --- |
| Root manifest (`Manifest.load` at line 258, `tryLoadEntries` at line 301 of `Manifest.lean`) | Root workspace | `<wsDir>/lake-manifest.json` | `<wsDir>/lake-manifest.json` | **No** (unless root workspace directory is shared). |
| Root toolchain file (`Workspace.updateToolchain`) | Root workspace | `<wsDir>/lean-toolchain` | `<wsDir>/lean-toolchain` | **No**. |
| Remote Git dependency checkouts (`PackageEntry.materialize` at `Resolve.lean` lines 32, 310) | Root workspace | `<wsDir>/.lake/packages/<pkg>` | `<wsDir>/.lake/packages/<pkg>` | **No** (cloned per workspace). |
| Package overrides (`Workspace.packageOverridesFile`) | Root workspace | `<wsDir>/.lake/package-overrides.json` | `<wsDir>/.lake/package-overrides.json` | **No**. |
| Package build outputs, `.trace`, `.trace.nobuild`, and `.hash` sidecars (`Package.buildDir`) | Each package | `<pkgDir>/.lake/build/...` | `<pkgDir>/.lake/build/...` | **Yes** (no cross-process package-build lock in `Lake/Util/Lock.lean`). |
| Compiled Lean package configuration (`importConfigFile`) | Package (`v4.30.0-rc2`) → **Workspace (`v4.30.0+`)** | `<pkgDir>/.lake/config/<pkgName>/lakefile.{olean,olean.trace,olean.lock}` | `<wsDir>/.lake/config/<pkgIdx>/lakefile.{olean,olean.trace,olean.lock}` (plus residual `createDirAll <pkgDir>/.lake` on missing trace) | **Yes in `v4.30.0-rc2`; No in `v4.30.0` / `v4.31.0` / `v4.34.1`**. |
| Local Lake artifact cache (`computeLakeCache` at `Workspace.lean` line 31) | Environment / toolchain / system cache, else root fallback | `LAKE_CACHE_DIR`, Elan/system cache, or `<wsDir>/.lake/cache` | `LAKE_CACHE_DIR`, Elan/system cache, or `<wsDir>/.lake/cache` | Intentionally shareable when configured; governed by `isArtifactCacheReadable` / `isArtifactCacheWritable`. |

Unlike Git dependencies—which `Dependency.materialize` clones into `<wsDir>/.lake/packages/<name>`—path dependencies retain their external `<pkgDir>` directly (`wsDir / relPkgDir`). During `Workspace.resolveDepsCore` (`Resolve.lean`, lines 195 and 505 in `v4.34.1`), Lake constructs a `LoadConfig` carrying both `wsDir := ws.dir` and `pkgDir := dep.pkgDir`, along with `pkgIdx` and `pkgName`.

Basis: **source** + **derived** (`src/lake/Lake/Config/Workspace.lean`, `src/lake/Lake/Config/Package.lean`, `src/lake/Lake/Load/Materialize.lean`, `src/lake/Lake/Load/Resolve.lean`, `src/lake/Lake/Util/Lock.lean`).

### 2. `.lake/config` Contents, Invalidation Predicate, Locking, and Option Persistence

In `src/lake/Lake/Load/Lean/Elab.lean` (299 lines, SHA-256 `5b3d30d5a9001514...` in `v4.34.1`; blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab` in `v4.30.0-rc2`; blob `b3908d0cebb44cac15e48baa41cb439f6f94eaa5` in `v4.31.0`), `importConfigFile` manages the compiled cache for Lean-authored `lakefile.lean` files:

1. **Persisted files:**
   - `lakefile.olean` (and in `v4.34.1` lines 180–185, `.olean`, `.olean.private`, and `.olean.server` paths): the compiled Lean environment for the configuration module.
   - `lakefile.olean.trace`: JSON serialization of `ConfigTrace`:
     ```lean
     structure ConfigTrace where
       idx        : Nat
       name       : Name
       platform   : String
       leanHash   : String
       configHash : Hash
       options    : NameMap String
     ```
   - `lakefile.olean.lock`: auxiliary lock file used to upgrade from a shared trace lock to exclusive reconfiguration without deadlocking.
2. **Freshness (`upToDate`) predicate and `-K` / `leanOpts` omission:**
   - Unless `cfg.reconfigure` (`-R`) is true, Lake acquires a shared lock on `lakefile.olean.trace`, parses `ConfigTrace`, and accepts the cached `.olean` if and only if:
     1. `olean.pathExists` is `true`;
     2. `trace.idx == cfg.pkgIdx`;
     3. `trace.name == cfg.pkgName`;
     4. `trace.configHash == (← computeTextFileHash cfg.configFile)` (CRLF-to-LF normalized content hash in `Lake/Build/Trace.lean`);
     5. `trace.platform == System.Platform.target`; and
     6. `trace.leanHash == cfg.lakeEnv.leanGithash`.
   - `ConfigTrace.options` (`cfg.lakeOpts` passed via `-K`) and `cfg.leanOpts` are **not** compared in `upToDate`. If those six checks pass, Lake imports `lakefile.olean` even if `-K` options changed on the CLI. If one of the compared fields is stale, automatic re-elaboration passes `trace.options` (the old persisted `-K` map) to `elabConfig`; only a missing trace or explicit `-R` / `--reconfigure` uses current `cfg.lakeOpts`.
   - If `lakefile.olean.trace` is valid JSON that fails full `ConfigTrace` decoding, Lake attempts to extract the `"options"` field and re-elaborate; if JSON parsing or `"options"` extraction fails, Lake errors with `"compiled configuration is invalid; run with '-R' to reconfigure"`.
3. **Failure-safe write ordering and non-blocking lock upgrade:**
   - Before re-elaborating a stale configuration, Lake removes the old `lakefile.olean` **first** and writes/truncates the new `lakefile.olean.trace` **second**, before running `elabConfig` and `Lean.writeModule`. If elaboration fails mid-way, the absent `.olean` forces automatic reconfiguration on the next run instead of leaving a valid `.olean` paired with a mismatched trace.
   - When a trace does not exist, Lake opens it with `IO.FS.Mode.writeNew`; if another process wins the creation race (`alreadyExists`), Lake falls back to opening the existing trace for validation.
   - When an existing trace is stale, a reader holding a shared trace lock cannot block waiting for an exclusive trace lock without risking a two-reader upgrade deadlock. Instead, Lake calls non-blocking `tryLock` on `lakefile.olean.lock`. The winner releases its shared trace lock, reopens the trace read/write under an exclusive lock, releases `.olean.lock`, and reconfigures; a loser immediately fails with:
     ```text
     could not acquire an exclusive configuration lock; another process may already be reconfiguring the package
     ```
4. **TOML bypass:** `loadPackageCore` (`src/lake/Lake/Load/Package.lean`) dispatches `lakefile.toml` to `loadTomlConfig` (`src/lake/Lake/Load/Toml.lean`), which parses and decodes the `Package` in memory without invoking `importConfigFile` or creating a `.lake/config` slot.

Basis: **source** (`src/lake/Lake/Load/Config.lean`, `src/lake/Lake/Load/Lean/Elab.lean`, `src/lake/Lake/Load/Package.lean`, `src/lake/Lake/Load/Toml.lean`, `src/lake/Lake/Build/Trace.lean`).

### 3. Hoisting of Compiled Configurations (`v4.30.0`, `v4.31.0`, and `v4.34.1` vs. `v4.30.0-rc2`) and `v4.30.0-rc2` Priming

#### How `v4.30.0-rc2` Required Consumer-Identity Priming (`anneal/flake.nix`)
Because `v4.30.0-rc2` stored compiled dependency configurations at `<pkgDir>/.lake/config/<pkgName>/lakefile.{olean,olean.trace}` while checking `trace.idx == cfg.pkgIdx` and `trace.name == cfg.pkgName`, a read-only dependency archive had to be primed under the exact `(idx, name)` identity that downstream consumers would assign (`support/lake-package-config-priming/source-map.json`).

In `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, and `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`), Anneal V1's `aeneas-config-primer` creates a temporary consumer workspace whose sole direct requirement is `require aeneas from "@AENEAS_ROOT@"`, runs `lake --old build Generated`, and asserts that `.lake/config/aeneas/lakefile.olean` exists inside the Aeneas package before freezing the archive. Because V1 generated workspaces also declare `aeneas` as their first direct dependency alongside a pre-populated relative `lake-manifest.json`, both primer and consumer load `aeneas` with `(idx = 0, name = aeneas)` (in `v4.30.0-rc2`'s dependency list indexing prior to root-slot `0` unification), hitting the read-only `.olean.trace` under a shared lock without mutating the Aeneas tree.

#### How `v4.30.0` Final, `v4.31.0`, and `v4.34.1` Hoist `.lake/config` into `<wsDir>/.lake/config/<pkgIdx>`
Upstream commit `41ecccec6d1244c5f89be2fc76638f22ba37cbc6` (`feat: lake: hoist compiled configurations (#13683)`, merged into `v4.30.0` final `d024af099ca4bf2c86f649261ebf59565dc8c622`, `v4.31.0` `68218e876d2a38b1985b8590fff244a83c321783`, and `v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52`) adds `LoadConfig.configDir` (`src/lake/Lake/Load/Config.lean`, line 83 in `v4.34.1`, SHA-256 `7292223420baa665...`):
```lean
public def LoadConfig.configDir (cfg : LoadConfig) : FilePath :=
  cfg.wsDir / defaultLakeDir / "config" / toString cfg.pkgIdx
```
and switches `importConfigFile` (`src/lake/Lake/Load/Lean/Elab.lean`) to place `lakefile.olean`, `lakefile.olean.trace`, and `lakefile.olean.lock` inside `cfg.configDir` (`<wsDir>/.lake/config/<pkgIdx>/`).

- **Elimination of cross-workspace `.lake/config` contention:** Root Lean packages occupy `<wsDir>/.lake/config/0/`, and dependencies occupy `<wsDir>/.lake/config/1/`, `<wsDir>/.lake/config/2/`, etc. (tested in `tests/lake/examples/deps/test.sh`, blob `d526c2852d68a6df92cdd00acba30772983a8de8`). Two workspaces sharing a dependency checkout at different indices or without pre-primed dependency `.lake/config` directories compile their configuration caches inside their own workspace `.lake/config/<pkgIdx>` directories.
- **No fallback to legacy package-local `.lake/config/<name>`:** `v4.30.0`+, `v4.31.0`, and `v4.34.1` do not read legacy `<pkgDir>/.lake/config/<name>` caches.
- **Residual `IO.FS.createDirAll cfg.lakeDir` on missing trace:** In `importConfigFile`, when the workspace-owned `traceFile` (`<wsDir>/.lake/config/<pkgIdx>/lakefile.olean.trace`) does not yet exist, Lake still executes `IO.FS.createDirAll cfg.lakeDir` (`<pkgDir>/.lake`). If `<pkgDir>/.lake` already exists (as in any prebuilt dependency tree), `createDirAll` is a no-op; if `<pkgDir>` has no `.lake` directory at all, first load attempts to create `<pkgDir>/.lake`.

Basis: **source** (`support/lake-configuration-ownership/source-map-v1.json`, `support/lake-frozen-package-config-ownership/source-map.json`, `support/lake-package-config-priming/source-map.json`).

### 4. Executed Multi-Version Verification (`v4.30.0-rc2`, `v4.30.0`, `v4.31.0`, and `v4.34.1`)

#### A. 24-Run Read-Only Dependency Replay Matrix: `v4.30.0-rc2` vs. `v4.30.0` Final
Executed on macOS arm64 (`support/lake-frozen-package-config-ownership/observations.json`, `support/lake-frozen-package-config-ownership/state-snapshots.json`, `support/lake-frozen-package-config-ownership/runtime-identity.json`, and `support/lake-frozen-package-config-ownership/repro.py`) across `v4.30.0-rc2` (`3dc1a088b6d2`, `Shared.trace` `depHash = 8569e9315b04983e`) and `v4.30.0` final (`d024af099ca4`, `Shared.trace` `depHash = b885d924048f9691`), with 2 preparation runs and 10 serial consumer cells per toolchain against a read-only (`chmod -R a-w`) prebuilt `probe_shared` (`Shared.lean`: `def sharedValue : Nat := 7`) and `probe_pad`:

| Consumer Cell | `v4.30.0-rc2` (`3dc1a088b6d2`) Outcome | `v4.30.0` Final (`d024af099ca4`) Outcome | Producer Tree Mutation Check |
| --- | --- | --- | --- |
| **1. Same-context consumer (`work/a`)** with relative manifest | Exit `0`, `Replayed Shared`, built `Client`. | Exit `0`, `Replayed Shared`, built `Client`. | 100% unchanged before/after. |
| **2. Relocated deeper consumer (`work/nested/deeper/b`)** with relative manifest | Exit `0`, `Replayed Shared`, built `Client`. | Exit `0`, `Replayed Shared`, built `Client`. | 100% unchanged before/after. |
| **3. Renamed root package (`work/name`)** with relative manifest | Exit `0`, `Replayed Shared`, built `Client`. | Exit `0`, `Replayed Shared`, built `Client`. | 100% unchanged before/after. |
| **4. Reordered dependencies (`work/index`, changing `probe_shared` workspace index)** | **Exit `1` (Permission denied):** attempted write to `source/probe_shared/.lake/config/probe_shared/lakefile.olean.lock`. | **Exit `0` (`Replayed Shared`):** wrote compiled configs under consumer `work/index/.lake/config/{0,1,2}`. | 100% unchanged (blocked on RC2; untouched on final). |
| **5. Missing consumer `lake-manifest.json` (`work/nomanifest`)** | **Exit `1` (Permission denied):** attempted write to `source/probe_shared/.lake/config/probe_shared/lakefile.olean.lock`. | **Exit `0` (`Replayed Shared`):** wrote manifest and `.lake/config/{0,1,2}` under consumer `work/nomanifest/`. | 100% unchanged. |
| **6–8. Local consumer edit (`sharedValue + 2`), no-op rebuild, and `--old build Client`** | All 3 exited `0` (`Replayed Shared`). | All 3 exited `0` (`Replayed Shared`). | 100% unchanged. |
| **9–10. Healthy `--no-build` vs. damaged copy (missing `Shared.olean`) `--no-build`** | Healthy exited `0`; damaged copy **exited `3`** and failed trying to write `probe_shared/.lake/build/lib/lean/Shared.trace.nobuild` (permission denied). | Healthy exited `0`; damaged copy **exited `3`** and failed trying to write `probe_shared/.lake/build/lib/lean/Shared.trace.nobuild` (permission denied). | 100% unchanged. |

All 24 guarded runs completed in `15.791 s` total wall time (peak process-group RSS `1,003.359 MiB` against a `1.5 GiB` cap, minimum free host RAM `30%`, minimum free disk `26.884 GiB`).

#### B. 8-Command Runtime Probe: `v4.31.0` vs. `v4.34.1`
Executed via `support/lake-configuration-ownership-431-434-runtime/probe.py` (`LAKE_NO_NET=1`, running `lake --keep-toolchain update` serially in Workspace A, Workspace B with an extra `filler` dependency shifting `shared` from index `1` to index `2`, Workspace A reload, and TOML-authored root Workspace T) and recorded in `support/lake-configuration-ownership-431-434-runtime/results.json`:

| Toolchain | Lean Commit | `lake` Binary SHA-256 | Workspace `a/.lake/config/1/lakefile.olean.trace` (`idx=1, name=shared`) SHA-256 | Workspace `b/.lake/config/2/lakefile.olean.trace` (`idx=2, name=shared`) SHA-256 |
| --- | --- | --- | --- | --- |
| `v4.31.0` | `68218e876d2a38b1985b8590fff244a83c321783` | `58261a1a2fa1a362376c71e02ca854a093e71cc5e6ea64b287a931cb2565273d` | `716e38bf6d4d6b05927ab8359cf9a5ec46455a6fee53e81626e177926efc30f9` | `239465b996551391b07ff67b3f99a2a03e6170d38167034a244fdfdb47197ea1` |
| `v4.34.1` | `5045d0056413266e57c625dcd7c365b10e377c52` | `c8c24f1398162ab4004e2a869952d8469f54293651151feaad4526f2b8474c6e` | `4afb906bc3a42bf095f75fccc889f9644d995ad3d576d26a4925e57f7700d389` | `5c9bf313df6dcd985f71010f055a44cbae0a55fe8ae94ca42ff9156b2bc35c89` |

Key runtime observations across both `v4.31.0` and `v4.34.1` (all 8 commands exited `0`, longest command `2.5351 s`, peak sampled group RSS `686,960 KiB`, peak scratch `1,104,443` bytes, minimum sampled reclaimable RAM `21.87%`, minimum free disk `13,065,048,064` bytes):
- Workspace B's load at `b/.lake/config/2/` left Workspace A's tree (`a/.lake/config/{0,1}/`) 100% unchanged in file hashes, sizes, mtimes, ctimes, and inodes.
- No compiled configuration files were written inside `shared/`; however, `shared/` **did acquire an empty `shared/.lake` directory** on Workspace A's first load in both `v4.31.0` and `v4.34.1`, confirming the residual `IO.FS.createDirAll cfg.lakeDir` call in `importConfigFile`.
- Workspace T (`lakefile.toml`) compiled its Lean dependency into `t/.lake/config/1/` (`idx=1, name=shared`) and created **no `t/.lake/config/0` root slot** in either version.

Basis: **execution** + **source** (`support/lake-frozen-package-config-ownership/observations.json`, `support/lake-configuration-ownership-431-434-runtime/results.json`).

## Boundaries

- **Hoisting `.lake/config` does not hoist `.lake/build` (`known not to apply`):** Across all examined versions (`v4.30.0-rc2` through `v4.34.1`), `Package.buildDir` remains `<pkgDir>/.lake/build`. Out-of-date dependency modules or missing artifacts under `--no-build` (`Shared.trace.nobuild`) still attempt writes under `<pkgDir>/.lake/build`.
- **Residual `<pkgDir>/.lake` directory creation on pristine read-only dependencies (`known not to apply` without `.lake`):** Because `importConfigFile` in `v4.30.0`, `v4.31.0`, and `v4.34.1` still calls `IO.FS.createDirAll cfg.lakeDir` when the workspace-owned `.olean.trace` is absent, a read-only dependency tree must already contain its `<pkgDir>/.lake` directory before first consumer configuration load.
- **Unexamined filesystem lock and multi-GiB archive behavior (`not examined`):** Lock semantics on network filesystems (NFS) and full Aeneas/Mathlib archive relocation at `v4.34.1` were **not examined** in these synthetic two- and three-package probes.
- **Arbitrary `lakefile.lean` relocation (`unknown` without per-package check):** Although `ConfigTrace` omits workspace and package paths and stores `nameExt`, `dirExt`, and `optsExt` in non-persistent `EnvExtension`s (`src/lake/Lake/DSL/Extensions.lean`), user `lakefile.lean` declarations that embed absolute paths at elaboration time can still persist them inside `lakefile.olean`.

## Evidence

### Pinned Upstream Revisions and Source Blobs
- **Lean 4 / Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`):**
  - `src/lake/Lake/Load/Config.lean` (blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`)
  - `src/lake/Lake/Load/Lean/Elab.lean` (blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`)
  - `src/lake/Lake/Load/Lean.lean` (blob `b38ee619b42d8293fc9e4ffb4b8e2f4b1508c1e7`)
  - `src/lake/Lake/Load/Toml.lean` (blob `b9893aa31ad6b3784cbfd35ebed8ff1bf0706161`)
  - `src/lake/Lake/Load/Package.lean` (blob `e9e858a54048ffa96972d264dbd51ca35b4ba403`)
  - `src/lake/Lake/Load/Resolve.lean` (blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`)
  - `src/lake/Lake/Load/Materialize.lean` (blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`)
  - `src/lake/Lake/Load/Workspace.lean` (blob `9f25dd62bc752ede695a25fc20371157eb65d64b`)
  - `src/lake/Lake/DSL/Extensions.lean` (blob `2f9a53c0883887889a7c9dc104482b8612c9a73f`)
  - `src/lake/Lake/Config/Package.lean` (blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`)
  - `src/lake/Lake/Config/Workspace.lean` (blob `b9c01f130240ae7c65ee298778351ddbe312374e`)
  - `src/lake/Lake/Config/WorkspaceConfig.lean` (blob `e6074ad0e0b1f2660294a5771b34ce1d42d12e20`)
  - `src/lake/Lake/Config/Defaults.lean` (blob `03033b5a032e450540ad99cc7c3be73544ad7416`)
  - `src/lake/Lake/Config/Module.lean` (blob `f8b938e16fe53ada616364033b8d8353baa733ee`)
  - `src/lake/Lake/Util/Lock.lean` (blob `78f109574faedcfedd6d142ed51b5b700082aa63`)
- **Lean 4 / Lake `v4.30.0` final (`leanprover/lean4@d024af099ca4bf2c86f649261ebf59565dc8c622`):**
  - Mapped in `support/lake-frozen-package-config-ownership/source-map.json` and `support/lake-frozen-package-config-ownership/runtime-identity.json`.
- **Lean 4 / Lake `v4.31.0` (`leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783`) and hoisting commit `41ecccec6d1244c5f89be2fc76638f22ba37cbc6`:**
  - `src/lake/Lake/Load/Config.lean` (blob `afdb0a19d9f5443f3cd6081014601744e538c523`), `src/lake/Lake/Load/Lean/Elab.lean` (blob `b3908d0cebb44cac15e48baa41cb439f6f94eaa5`), `src/lake/Lake/Load/Resolve.lean` (blob `a316c67740973fd737e25eb351bea8249ffd64a6`), `src/lake/Lake/Load/Toml.lean` (blob `271d8c427a3beb1f6d4dcd90123e85e5fb3e8326`), `src/lake/Lake/Config/Package.lean` (blob `b9f5c489126703625009077caaeda05d3688e06f`), `src/lake/Lake/Config/Workspace.lean` (blob `5879e80f28e4679d164becc331db462b0995c635`), `tests/lake/examples/deps/test.sh` (blob `d526c2852d68a6df92cdd00acba30772983a8de8`).
- **Lean 4 / Lake `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
  - `src/lake/Lake/Load/Config.lean` (84 lines, SHA-256 `7292223420baa665...`, `LoadConfig.configDir` at line 83), `src/lake/Lake/Load/Lean/Elab.lean` (299 lines, SHA-256 `5b3d30d5a9001514...`, `importConfigFile` at lines 180–185), `src/lake/Lake/Load/Manifest.lean` (313 lines, SHA-256 `8b01bdff19b7e4cb...`), `src/lake/Lake/Load/Resolve.lean` (627 lines, SHA-256 `f90d1e01f6ee9d60...`), `src/lake/Lake/Config/Workspace.lean` (435 lines, SHA-256 `80ae4168ce567b92...`).
- **Anneal V1 (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`):**
  - `anneal/flake.nix` (blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`) and `anneal/v1/src/aeneas.rs` (blob `9b4618a20938315afc290744bbdfa498848620f4`).

### Preserved Package Support Material
- `support/lake-configuration-ownership/source-map-v1.json`
- `support/lake-package-config-priming/source-map.json`
- `support/lake-frozen-package-config-ownership/check.py`, `support/lake-frozen-package-config-ownership/repro.py`, `support/lake-frozen-package-config-ownership/observations.json`, `support/lake-frozen-package-config-ownership/runtime-identity.json`, `support/lake-frozen-package-config-ownership/source-map.json`, and `support/lake-frozen-package-config-ownership/state-snapshots.json`
- `support/lake-configuration-ownership-431-434-runtime/check.py`, `support/lake-configuration-ownership-431-434-runtime/probe.py`, `support/lake-configuration-ownership-431-434-runtime/results.json`, `support/lake-configuration-ownership-431-434-runtime/fixture/a/lakefile.lean`, `support/lake-configuration-ownership-431-434-runtime/fixture/b/lakefile.lean`, `support/lake-configuration-ownership-431-434-runtime/fixture/filler/lakefile.lean`, `support/lake-configuration-ownership-431-434-runtime/fixture/shared/lakefile.lean`, `support/lake-configuration-ownership-431-434-runtime/fixture/t/lakefile.toml`, and the captured `v4_31_0` and `v4_34_1` run artifacts under `support/lake-configuration-ownership-431-434-runtime/runs/`

## Revalidation

1. **Offline snapshot and matrix verification:**
   - Run `python3 -B support/lake-frozen-package-config-ownership/check.py` to verify the 24-cell `v4.30.0-rc2` vs. `v4.30.0` outcome matrix, compiler identities, and 20 before/after read-only producer inventory pairs.
   - Run `python3 -B support/lake-configuration-ownership-431-434-runtime/check.py` to verify the 8-command `v4.31.0` and `v4.34.1` snapshot invariants and `.olean` / `.trace` SHA-256 digests.
2. **Active probe execution on a newer toolchain:**
   - Using `anneal-lean-run`, run `python3 -B support/lake-configuration-ownership-431-434-runtime/probe.py` or `python3 -B support/lake-frozen-package-config-ownership/repro.py` against the target Lean/Lake toolchain.
   - Inspect `LoadConfig.configDir` (`Lake/Load/Config.lean`) and `importConfigFile` (`Lake/Load/Lean/Elab.lean`) to check whether the residual `IO.FS.createDirAll cfg.lakeDir` call in the missing-trace branch has been removed or whether a read-only dependency still requires a pre-existing `<pkgDir>/.lake` directory.
