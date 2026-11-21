# Lean 4 / Lake Incremental Artifact Caching (`LAKE_CACHE_DIR`) Inside Nix and CI

## Summary

- **Per-module Nix derivations (`buildLeanPackage`) are dead upstream and incompatible with modern Lake + mixed Rust/Lean pipelines:** Upstream `leanprover/lean4` deleted `nix/` and `nix/buildLeanPackage.nix` on `2025-08-14` (`535435955b482176e8d62a54deebcacdec0827db`), and `NixOS/nixpkgs` ships only the CMake Lean 4 compiler with no `buildLeanPackage` builder. At its last surviving revision (`f86b192ec24d`), `buildLeanPackage.nix` bypassed Lake completely, lacked Lean `v4.34+` `--setup` / `.olean.{server,private}` / `.ir.sig` outputs, spawned 3–4 derivations per module via IFD (`lean --deps-json`), and triggers two-level nested IFD when `.lean` sources are generated from Rust.
- **Coarse Nix derivations (`lake build` / `lenianiva/lean4-nix`) lose intra-package per-module `.olean` reuse:** A single input-addressed Nix derivation rebuilds every module on a 1-leaf `.lean` edit. `lenianiva/lean4-nix` (`2ad74592e34c`) is **per-package** (`buildDeps` + `mkPackage` + `lakeArtifacts`), caching external dependencies across leaf edits (like `crane`), but still rebuilds the entire root package on a 1-leaf edit, copies `.lake` trees, uses non-FOD `builtins.fetchGit`, and runs `autoPatchelfHook` on `bin/lean`.
- **Hybrid architecture (Nix closure for toolchain + deps, `LAKE_CACHE_DIR` for per-module `.olean` reuse) is the clean fit — with two sharp `LAKE_ARTIFACT_CACHE` operational regimes (verified on `v4.35.0` under `bwrap`):**
  - **Read-only `LAKE_CACHE_DIR` with `LAKE_ARTIFACT_CACHE` unset (`readable=true, writable=false`):** Works cleanly on both 100% cache hits (`0.152s`, exit `0`) and 1-leaf misses (`0.657s`, exit `0`), catching `EXDEV` (`error code: 18`) on cross-mount hardlinks and falling back to `copyFile` into `.lake/build/` with zero writes to `LAKE_CACHE_DIR`. `LAKE_NO_CACHE=true` does **not** disable local `LAKE_CACHE_DIR` reads in `v4.35.0`.
  - **Read-only `LAKE_CACHE_DIR` with `LAKE_ARTIFACT_CACHE=true` (`writable=true`):** Succeeds on 100% hit (leaving `.olean`s in `LAKE_CACHE_DIR` and restoring only `.ilean`s into `.lake/build/`), but **crashes fatally (`exit 1`, `failed to cache artifact: read-only file system (error code: 30)`)** on any cache miss.
  - **Read-write `LAKE_CACHE_DIR` (outside a Nix sandbox or via `bwrap --bind`) with `LAKE_ARTIFACT_CACHE=true`:** Reuses unchanged modules and publishes new leaf artifacts; `v4.35.0` also ships native S3/R2 `CacheService` (`lake cache get` / `put`). Because Lake's 64-bit `Hash` is non-cryptographic and `resolveArtifact` does not rehash local hits, untrusted PR CI should mount the shared `LAKE_CACHE_DIR` read-only (`LAKE_ARTIFACT_CACHE` unset) and restrict writes to trusted `main`/`merge_group` runs.

## Applicability

This report compares three CI caching architectures for mixed Rust + Lean 4 codebases (coarse Nix derivation, per-module Nix derivations, and hybrid Nix closure + `LAKE_CACHE_DIR`) across the 5 subjects in `REPORT.json`. Execution evidence (`support/probe_lake_ro_cache.py`, `support/probe_results.json`) was collected on `x86_64-unknown-linux-gnu` using `Lean 4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, `Lake version 5.0.0-src+eb6cafb`) inside `bwrap --ro-bind` / `--bind` mounts.

This report builds on (without duplicating) established Lake cache mechanics: dual-layer `<cache>/artifacts/{hash}.{ext}` (64-bit non-cryptographic `Hash`) + `<cache>/outputs/<scope>/<input-hash>.json`, default `readable=true / writable=false` policy, `v4.31.0+` workspace-hoisted `.lake/config/<pkgIdx>/`, `ExternLib.sharedFacet` non-coverage (`buildFileUnlessUpToDate'`), and `dontPatchELF = true` + FOD `fetchFromGitHub` + `lake build --packages` hermetic Nix packaging.

## Findings

### 1. Option A — Coarse Nix Derivation and `lenianiva/lean4-nix` Per-Package Caching

Basis: source (`lenianiva/lean4-nix@2ad74592e34c2e6ff5e8bec9d8abab8f4e9c3a37`, `lib/lake.nix`) + derived

- **Single coarse Nix derivation:** Because Nix derivations are input-addressed over all inputs (including `src`), editing 1 leaf `.lean` file (or 1 Rust file that regenerates 1 `.lean` file) alters `src`, yielding a new derivation hash and an empty `/build` directory with **0% per-module `.olean` reuse**.
- **Per-package split (`lenianiva/lean4-nix` `lib/lake.nix:103-209`):**
  - `buildDeps` parses `lake-manifest.json` (pure JSON import, no IFD) and creates one `mkLakeDerivation` per external Lake package; `mkPackage` symlinks dependencies into `.lake/packages/${depName}`, writes `.lake/package-overrides.json`, and optionally copies a prior `.lake` directory via `lakeArtifacts` (`prePatch`, L194–200).
  - **Remaining limits:** (1) Editing 1 leaf `.lean` file in the root workspace still invalidates and rebuilds **every** module in the root package; (2) `cp -R ${lakeArtifacts}/.lake . && chmod -R +w .lake` copies full `.lake` trees (noted as a `TODO: Use zstd tarball` at L86, L188); (3) uses non-FOD `builtins.fetchGit` (L120–123) and runs `autoPatchelfHook` on `bin/lean` (`lib/toolchain.nix`), altering binary hashes.

### 2. Option B — Per-Module Nix Derivations (`nix/buildLeanPackage.nix`)

Basis: source (`leanprover/lean4@535435955b482176e8d62a54deebcacdec0827db`, `leanprover/lean4@f86b192ec24dd3922d63f5ba05718ab5c4ef8e85`, `NixOS/nixpkgs` `pkgs/by-name/le/lean4/package.nix`) + derived

- **Removed upstream:** `leanprover/lean4` deleted `nix/` and `nix/buildLeanPackage.nix` in commit `535435955b482176e8d62a54deebcacdec0827db` (`2025-08-14`, `chore: remove broken Nix build (#9910)`). `NixOS/nixpkgs` (`lean4` `4.35.0`) packages only the CMake Lean 4 compiler with no `buildLeanPackage` builder.
- **Last surviving implementation (`f86b192ec24d`, 247 lines):** Discovered candidate files via `builtins.readDir` (`submodules`, L102–110), ran IFD `lean --deps-json --stdin` (L126–137) unless a manually maintained `modDepsFile` was checked in, and instantiated 3–4 derivations per module (`depRoot` symlink farm, `buildMod` with `outputs = [ "out" "ilean" "c" ]`, `compileMod`, optional `sharedLib`).
- **Structural incompatibilities with Lean `v4.34+` / Lake / mixed Rust+Lean:**
  1. **Complete Lake bypass:** Ignores `lakefile.toml`, `lakefile.lean`, `lake-manifest.json`, custom targets, and `extern_lib` build scripts.
  2. **Incompatible with Lean `v4.34+` module system:** Invokes raw `lean` via `LEAN_PATH` (L145, L162) rather than `--setup <mod>.setup.json` (`ModuleSetup`), and omits `.olean.server`, `.olean.private`, `.ir`, and `.ir.sig`.
  3. **IFD & nested-IFD explosion:** Default import discovery fails under `allow-import-from-derivation = false`; on mixed Rust+Lean pipelines where Rust codegen outputs `.lean` files into a derivation, `builtins.readDir` + `lean --deps-json` triggers **two-level nested IFD** plus 3–4 derivations per module (thousands of store paths and daemon IPC overhead on large workspaces).
  4. **Coarse `precompileModules`:** Package-wide boolean (L25) with manual `pluginDeps`/`nativeSharedLibs` threading.

### 3. Option C — Hybrid (Nix Closure + `LAKE_CACHE_DIR`) and Read-Only vs. Read-Write Regimes

Basis: source (`leanprover/lean4@eb6cafb7290e`: `src/lake/Lake/Build/Common.lean:500,648-666,689-735`, `Module.lean:1063-1115`, `Config/Env.lean:176-177`, `Config/Monad.lean:192-203`, `Config/Cache.lean:561-650`) + execution (`support/probe_lake_ro_cache.py`, `support/probe_results.json`)

#### 3.1 Read-Only vs. Read-Write `LAKE_CACHE_DIR` Execution Matrix (`v4.35.0`)

Executed inside `bwrap` over a 3-module workspace (`CacheProbe.Base` → `CacheProbe.Leaf` → `CacheProbe`, `LEAN_NUM_THREADS=1`, `LAKE_NO_CACHE=true`):

| Case | `bwrap` Cache Mount | `LAKE_ARTIFACT_CACHE` | Input State | Exit | Wall Time | `Base` / `Leaf` | Cache Mutated? | Observed Behavior |
| :--- | :--- | :--- | :--- | :---: | :---: | :--- | :---: | :--- |
| **1. Producer** | `--bind` (RW) | `true` | Clean (`leafVal=42`) | `0` | `5.966 s` | Built / Built | Yes (12 files, 3 `outputs/*.json`) | Populates `artifacts/` + `outputs/cacheprobe/*.json`. |
| **2. RO Default Full Hit** | `--ro-bind` (RO) | *(unset)* | Fresh (`leafVal=42`) | **`0`** | **`0.152 s`** | Reused / Reused | **No** | `EXDEV` (`error code: 18`) on cross-mount `hardLink` caught → `copyFile` fallback restores all 3 `.olean`s into `.lake/build/`. `LAKE_NO_CACHE=true` does **not** block local reads. |
| **3. RO Default Leaf Miss** | `--ro-bind` (RO) | *(unset)* | Fresh (`leafVal=99`) | **`0`** | **`0.657 s`** | **Reused / Built** | **No** | `Base` reused from RO cache; modified `Leaf` built locally with zero writes to RO cache. |
| **4. RO Writable Leaf Miss** | `--ro-bind` (RO) | **`true`** | Fresh (`leafVal=99`) | **`1`** | `0.356 s` | Reused / **Failed** | **No** | **Fatal crash:** `error: failed to cache artifact: read-only file system (error code: 30)` (`Common.lean:500`). |
| **5. RO Writable Full Hit** | `--ro-bind` (RO) | `true` | Fresh (`leafVal=42`) | `0` | `0.160 s` | Reused / Reused | **No** | Exits `0` on 100% hit, but restores `0` `.olean`s (only 3 `.ilean`s) into `.lake/build/` (`restoreAllArtifacts = false`). |
| **6. RW Writable Leaf Miss** | `--bind` (RW) | `true` | Fresh (`leafVal=99`) | **`0`** | **`0.656 s`** | **Reused / Built** | Yes (12 → 16 files) | `Base` reused; modified `Leaf` built and published to cache. |

#### 3.2 Key Operational Invariants and Pitfalls

1. **`LAKE_NO_CACHE=true` in `v4.35.0`:** `Env.lean:176-177` binds `LAKE_NO_CACHE` to `env.noCache` (disabling remote Reservoir/GitHub package archive fetches), **not** to `enableArtifactCache?` (which reads `LAKE_ARTIFACT_CACHE`). Thus `LAKE_NO_CACHE=true` + `LAKE_CACHE_DIR=<ro-path>` (with `LAKE_ARTIFACT_CACHE` unset) stays offline while reusing local `.art` files (verified in Cases 2 & 3).
2. **Silent `.olean` absence under `LAKE_ARTIFACT_CACHE=true`:** When `LAKE_ARTIFACT_CACHE=true` and `restoreAllArtifacts` is `false` (default), cache-hit `.olean`s stay in `LAKE_CACHE_DIR/artifacts/` (consumed via `ModuleSetup.importArts`) and are **not** materialized in `.lake/build/lib/lean/` (Case 5: `restored_oleans_in_build = []`). Auditors or packaging scripts scanning `.lake/build/` directly must resolve paths via `lake setup-file` / `ModuleSetup.importArts`, set `restoreAllArtifacts = true`, or leave `LAKE_ARTIFACT_CACHE` unset.
3. **Pure Nix sandbox vs. CI runner sandbox:**
   - **Inside a pure Nix sandbox:** `LAKE_CACHE_DIR` cannot be read-write across builds, but a downstream Nix derivation can consume a pre-built `depsCacheDrv` store path as a **read-only `LAKE_CACHE_DIR`** (`LAKE_ARTIFACT_CACHE` unset, `LAKE_NO_CACHE=true`, Cases 2 & 3). This caches frozen dependencies without crashing on workspace misses, though workspace edits still rebuild workspace modules.
   - **Outside a Nix sandbox (Nix/omnibus toolchain + `bwrap --bind` or CI workspace):** Setting `LAKE_CACHE_DIR` read-write with `LAKE_ARTIFACT_CACHE=true` gives sub-second per-module reuse on 1-leaf edits (Case 6). Persistence options: GHA `actions/cache` / host volume (requires external LRU eviction since Lake never GCs `LAKE_CACHE_DIR`), or Lake `v4.35.0`'s native S3/R2 `CacheService` (`Config/Cache.lean:561-650`, `curl --aws-sigv4 aws:amz:auto:s3`, `lake cache get`/`put`). Because `Cache.writeOutputsCore` uses non-atomic `IO.FS.writeFile`, concurrent CI jobs must not share a live writable `LAKE_CACHE_DIR` filesystem without per-job isolation or writer serialization.
4. **64-bit non-cryptographic cache trust boundary:** Because Lake's `Hash` is 64-bit non-cryptographic and `resolveArtifact` does not rehash local hits, untrusted PR CI jobs should mount the shared `main` `LAKE_CACHE_DIR` **read-only** (`LAKE_ARTIFACT_CACHE` unset, Case 3) and restrict writable publication to trusted `main`/`merge_group` runs.

### 4. Comparative Decision Matrix

Basis: source + execution + derived

| Criterion | Option A (Coarse Nix Drv / `lean4-nix` Per-Pkg) | Option B (Per-Module Nix Drvs / `buildLeanPackage`) | Option C (Hybrid: Nix Closure + `LAKE_CACHE_DIR`) |
| :--- | :--- | :--- | :--- |
| **Upstream status (`v4.34+`/`v4.35.0`)** | Supported (`lake build --packages` / `lean4-nix`) | **Deleted upstream** (`535435955b48`) | **First-class upstream** (Lake artifact cache + `CacheService`) |
| **1-leaf `.lean` edit cost** | Rebuilds entire root package (deps cached if split) | Rebuilds leaf + reverse deps (minus Nix eval/sandbox overhead) | **Rebuilds only leaf + reverse deps** (sub-second hit) |
| **Rust-generated `.lean` files** | Works naturally | **Two-level nested IFD** | **Works natively** (Lake hashes generated `.lean` content) |
| **Lean `v4.34+` modules & FFI** | Full Lake support | Broken (no `--setup`, no `.olean.{server,private}`/`.ir.sig`) | **Full Lake support** (except `ExternLib.sharedFacet` non-coverage) |
| **Hermeticity / TCB** | Strict Nix sandbox | Strict Nix sandbox (if IFD allowed) | Nix-pinned toolchain/deps; `LAKE_CACHE_DIR` is non-cryptographic (mount RO on PRs; audit `.olean` closure) |

## Boundaries

- **Live `lake cache get` / `lake cache put` S3/R2 execution (`not examined`):** `CacheService.{uploadS3, uploadService, downloadService}` was verified in `v4.35.0` source (`Config/Cache.lean:561-650`), not executed against a live S3/R2 or MinIO endpoint.
- **`LAKE_NO_CACHE` behavior on pre-`v4.35.0` releases (`not examined` here):** `Env.lean:176-177` and `bwrap` Cases 2–3 establish `v4.35.0` behavior; older Lake `v4.30`–`v4.34` versions were not re-probed for `LAKE_NO_CACHE` interaction.
- **`ExternLib.sharedFacet` caching (`unsupported` by `LAKE_CACHE_DIR`):** Targets built via `buildFileUnlessUpToDate'` bypass `LAKE_CACHE_DIR` and relink locally in fresh build directories.
- **Cache growth / eviction rates on full Mathlib-scale CI workloads (`not examined`):** Execution probe measured a 3-module workspace to verify mount/exit/restore invariants, not multi-GB throughput.

## Evidence

All new evidence was gathered or executed on `2026-11-21`:

- **`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`):** `src/lake/Lake/Build/Common.lean` (L500 `failed to cache artifact`, L648–666 `restoreArtifact` `hardLink` → `copyFile`, L689–735), `src/lake/Lake/Build/Module.lean` (L1063–1115), `src/lake/Lake/Config/Env.lean` (L176–177), `src/lake/Lake/Config/Monad.lean` (L192–203), `src/lake/Lake/Config/Cache.lean` (L561–650 `uploadS3` / `CacheService`).
- **`leanprover/lean4@535435955b482176e8d62a54deebcacdec0827db` (`2025-08-14`):** `chore: remove broken Nix build (#9910)` deleting `nix/` and `nix/buildLeanPackage.nix`.
- **`leanprover/lean4@f86b192ec24dd3922d63f5ba05718ab5c4ef8e85` (`2025-04-21`):** last surviving `nix/buildLeanPackage.nix` (L21–25, L61–83, L102–191).
- **`lenianiva/lean4-nix@2ad74592e34c2e6ff5e8bec9d8abab8f4e9c3a37` (`2026-10-30`):** `lib/lake.nix` (L86, L103–209), `lib/toolchain.nix`.
- **`NixOS/nixpkgs` (`pkgs/by-name/le/lean4/package.nix`, `4.35.0`):** CMake compiler package only.
- **Preserved execution probe:** [`support/probe_lake_ro_cache.py`](support/probe_lake_ro_cache.py) and [`support/probe_results.json`](support/probe_results.json) (6 `bwrap` cells on `x86_64-unknown-linux-gnu` with `Lean 4.35.0`).

## Revalidation

1. **Re-run the read-only / read-write `LAKE_CACHE_DIR` probe:** Execute `python3 support/probe_lake_ro_cache.py` on a target Lean/Lake release with `bwrap` installed (requiring ~10 seconds) and verify Cases 2, 3, 4, 5, and 6 exit codes, cache mutation counts, and restored `.olean` lists.
2. **Check `LAKE_NO_CACHE` and `CacheService` drift:** Diff `src/lake/Lake/Config/Env.lean`, `src/lake/Lake/Build/Common.lean`, and `src/lake/Lake/Config/Cache.lean` in `leanprover/lean4` against `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
3. **Check `lenianiva/lean4-nix` granularity:** Diff `lib/lake.nix` against `2ad74592e34c2e6ff5e8bec9d8abab8f4e9c3a37` to see whether per-module caching or FOD fetching was added.
