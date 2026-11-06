# Lake Clean-Build vs. Cache-Seeded Equivalence, Observability, and Concurrency

## Summary

Across Lean 4 and Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, paired with Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` and `d13f23b723b8a846827a245b89c10fc7d3f11612`), a Lake artifact-cache hit is a **same-traced-input substitution**, not an automatic proof that a clean rebuild would emit byte-identical outputs or that all build-tree metadata is identical:

1. **Three-layer clean vs. cache-seeded equivalence contract:**
   - **Producer-input identity:** Effective traced inputs (`depTrace.hash`) must match, while weak inputs (`weakArgs` / `weakLeanArgs`) must be held constant or explicitly justified.
   - **Output content identity:** Semantically consumed artifacts (`.olean`, `.olean.server`, `.olean.private`, `.ilean`, `.ir`, `.ir.sig` in `v4.34.1`, generated `.c`, `.bc`, and native binaries/libraries) must be compared by cryptographic digest (e.g., SHA-256) or with `--rehash`, rather than trusting preexisting 64-bit Lake `.hash` sidecars.
   - **Consumer behavior:** Downstream imports, `lake setup-file` (`ModuleSetup` resolved artifact identities rather than raw path strings), and `lean --json` / LSP diagnostics must match, while `.trace` bytes are **expected to differ** because clean builds write `BuildMetadata.ofBuild` (`synthetic = false`, populated `inputs` and `log`) whereas cache fetches write `BuildMetadata.ofFetch` (`synthetic = true`, empty `inputs` and `log`).
2. **Executed equivalence and concurrency probes (`v4.30.0-rc2` on macOS arm64):**
   - Clean, cache-seeded, and rebuilt runs produced byte-identical `Generated.olean` (SHA-256 `6ec0c3b7d9ecaef15b5e5458b7a0de40f41f252868f4004d2b58d9c6eb3e8302`), `Generated.ilean` (`1046a5ab5df732122fbf1a4a6267904d1943ab002a3839e6a2d37289cddf8bf4`), and `Generated.c` (`d18ac49a927969b7fb46c06339291a1160c07ca38489acb819e14dac70038b2d`) with identical `depHash` (`bf169a794ed0fefe`), while `Generated.trace` and `Generated.setup.json` differed only in absolute workspace paths.
   - Two concurrent consumers reading one frozen prebuilt dependency (with relative `lake-manifest.json` preseeded before first Lake invocation) both succeeded in `0.728 s` without mutating the producer. By contrast, two concurrent consumers sharing a writable source-only producer both executed `Dep` build actions (`0.87 s`), racing on the same `.lake/build` output paths. Two independent packages concurrently publishing to a shared `LAKE_ARTIFACT_CACHE` succeeded, and a third consumer fetched the cached outputs.
3. **Machine-observable reuse vs. rebuild signals and `.trace.nobuild` semantics:**
   - `lake build --no-build` (`Workspace.checkNoBuild`) exits with code `3` when an out-of-date target reaches `buildAction` (`wantsRebuild := true`), making it the primary gate for whether a builder action is needed—but it is **not** a mutation-free dry-run, because cache lookup, remote download, `restoreArtifact`, `.hash` writes, and synthetic trace writes happen before `buildAction`.
   - When `--no-build` aborts inside `buildAction` and the ordinary `*.trace` file already exists, Lake writes `*.trace.nobuild` containing the new expected `BuildMetadata` (`outputs: null`, empty `log`, `synthetic: false`). Lake never reads `*.trace.nobuild` during freshness checks, omits it when the primary `.trace` is absent, and removes it only after a subsequent `buildAction` succeeds.
   - Monitor output under `-v --no-ansi` reports per-job `JobAction` verbs (`Ran`, `Replayed`, `Fetched`, `Built`), where composite jobs merge actions via `max` (`unknown < replay < fetch < build`).

## Applicability

This report covers the five subjects declared in `REPORT.json`:

1. **Lean 4 / Lake `v4.30.0-rc2`:** `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`Lake version 5.0.0-src+3dc1a08`).
2. **Lean 4 / Lake `v4.34.1`:** `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`Lake version 5.0.0-src+5045d00`).
3. **Mathlib `v4.30.0-rc2`:** `leanprover-community/mathlib4` revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
4. **Mathlib `v4.34.1`:** `leanprover-community/mathlib4` revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.
5. **Anneal cache-seeding pipeline:** `google/zerocopy` revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix`).

Executed probe results (`support/lake-cache-concurrency-execution-probe/` and `support/lake-compact-cache-concurrency-and-mathlib-probes/`) were acquired on `arm64-apple-darwin24.6.0` with Lean/Lake `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`). Source-level equivalence, observability, and `.trace.nobuild` contracts apply across both `v4.30.0-rc2` and `v4.34.1`, with `v4.34.1` source deltas noted explicitly below.

## Findings

### 1. Clean-Build vs. Cache-Seeded Equivalence Contract

In both `v4.30.0-rc2` (`3dc1a088b6d2`) and `v4.34.1` (`5045d0056413`), Lake's artifact cache (`buildArtifactUnlessUpToDate` in `src/lake/Lake/Build/Common.lean`, line 521 for `getArtifactsUsingCache?` in `v4.34.1`, and `Module.recBuildLean` in `src/lake/Lake/Build/Module.lean`) substitutes cached output descriptors (`ModuleOutputDescrs` in `src/lake/Lake/Build/ModuleArtifacts.lean`) whenever `depTrace.hash` matches `inputHash`. Because the producer action does not run on a cache hit, Lake establishes a **reuse equivalence class** rather than a rebuild reproducibility proof.

| State or Observation | Clean vs. Cache-Seeded Requirement | Technical Rationale |
| --- | --- | --- |
| Effective traced source/config/toolchain inputs | **Equal** (unless testing a specific transformation) | Determines normal hash-mode `depTrace.hash` (`inputHash`). |
| Current Lake `depHash` / input cache key | **Equal** in hash-mode same-input tests | A differing `depHash` means Lake sees different traced inputs. |
| `.olean`, `.olean.server`, `.olean.private` bytes | **Byte-identical** when present and consumed | Compiler module outputs consumed by import and server paths. |
| `.ilean` bytes | **Byte-identical** | Restored locally by `Module.restoreNeededArtifacts` for LSP reference/navigation queries. |
| `.ir`, `.ir.sig` (`v4.34.1`), generated `.c`, `.bc` | **Byte-identical** for fixed platform/toolchain | Feed meta evaluation and native compilation (`Lake/Build/Actions.lean`). |
| Native `.o`, static/shared libraries, executables | **Byte-identical** when native equivalence is claimed | Built by `compileO`, `compileStaticLib`, `compileSharedLib` (`Actions.lean`, lines 111, 137, 149 in `v4.34.1`). |
| Lake `ArtifactDescr` (`{hash}.{ext}`) | **Equal** when output bytes match | Encodes Lake's 64-bit non-cryptographic content identity. |
| Preexisting `.hash` sidecar files | **Recompute or verify via SHA-256 / `--rehash`** | `fetchFileHash` trusts existing `.hash` sidecars when `trustHash` is enabled. |
| `.trace` file bytes | **Not required equal** | `BuildMetadata.ofBuild` (`synthetic = false`, full `inputs` and `log`) intentionally differs from `BuildMetadata.ofFetch` (`synthetic = true`, empty `inputs` and `log`). |
| Trace `depHash` and `outputs` descriptors | **Semantically equal** | The reuse-relevant fields inside `BuildMetadata`. |
| Artifact/cache/build-tree file paths, mtimes, hard links | **May differ** if consumers resolve identical content | `restoreNeededArtifacts` restores `.ilean` while leaving other artifacts in `LAKE_CACHE_DIR` unless `restoreAllArtifacts = true`. |
| Build monitor action label (`Built` vs. `Fetched`/`Replayed`) | **Expected to differ** | Confirms the producer built while the seeded consumer fetched or replayed. |
| `lake setup-file` (`ModuleSetup` JSON in `src/Lean/Setup.lean`) | **Semantically equal** (module, package, options, resolved artifact SHA-256s) | Raw JSON strings differ when `importArts`, `dynlibs`, or `plugins` point into `LAKE_CACHE_DIR` vs. `.lake/build`. |
| Downstream import elaboration and `lean --json` / LSP behavior | **Equal** | End-to-end semantic consumer equivalence check. |

#### Why Current Anneal Uses `lake --old build` Instead of Hash-Mode Equivalence
In `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, lines 293–490), Anneal downloads Mathlib's `.ltar` cache via `lake exe cache get-`, unpacks it into `.lake/build`, copies the products into vendored package trees, and rewrites Git dependencies to vendored path dependencies (lines 438–447). Because rewriting dependency manifests changes Lake dependency hashes (`depHash`), Anneal sets input modification times older than the unpacked artifacts and runs `lake --old build`. In `Lake/Build/Common.lean` (`SavedTrace.replayIfUpToDate'`, line 242 in `v4.34.1`), modification-time fallback (`OutputStatus.isCacheable = false`) accepts existing outputs despite `depHash` mismatch and deliberately withholds them from artifact-cache publication.

Basis: **source** + **derived** (`src/lake/Lake/Build/Common.lean`, `src/lake/Lake/Build/Module.lean`, `src/lake/Lake/Build/ModuleArtifacts.lean`, `src/Lean/Setup.lean`, and `anneal/flake.nix`).

### 2. Executed Cache Equivalence and Concurrency Probes (`v4.30.0-rc2`)

Two synthetic execution suites were run on `arm64-apple-darwin24.6.0` using pinned Lean/Lake `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lake` version `5.0.0-src+3dc1a08` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`, `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `LEAN_NUM_THREADS=1`, `MATHLIB_NO_CACHE_ON_UPDATE=1`).

In the primary fixture (`support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/probe.py`, SHA-256 `04ce02b0df9d64ceda7e5a98365ff3c9348258ffe01d7d15704ee212eb198d05`), producer package `probe_dep` defines `depValue : Nat := 7` in `Dep.lean`, and each consumer defines `Generated.lean` importing `Dep`, proving `depValue + 1 = 8` by `decide`, and evaluating `#eval depValue + 1`. Each consumer was preseeded before its first Lake command with a relative `lake-manifest.json` (SHA-256 `3c7645369d322de36fde6c8056e660d5e8a32c511b81bb2e99d050737e1ecfe2`) pointing `probe_dep` to the sibling `producer` directory.

| Experimental Cell | Observed Execution Outcome | Artifact & State Verification |
| --- | --- | --- |
| **1. Clean source-only producer + fresh consumer** (`support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/clean-inventory.json`) | `lake --keep-toolchain --no-cache --old build Generated` exited `0` in `3.728 s`; built both `Dep` and `Generated`; `#eval` printed `8`. `setup-file Generated.lean` and `env lean --json Generated.lean` both exited `0` (JSON reported `8`). | `Generated.olean` SHA-256: `6ec0c3b7d9ecaef15b5e5458b7a0de40f41f252868f4004d2b58d9c6eb3e8302`; `Generated.ilean` SHA-256: `1046a5ab5df732122fbf1a4a6267904d1943ab002a3839e6a2d37289cddf8bf4`; `Generated.c` SHA-256: `d18ac49a927969b7fb46c06339291a1160c07ca38489acb819e14dac70038b2d`; `Generated.trace` `depHash`: `bf169a794ed0fefe`. |
| **2. Two concurrent fresh consumers (`consumer-a`, `consumer-b`) against one copied and frozen prebuilt producer** (`support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/seeded-inventory.json`) | Both builds ran concurrently, exited `0` in `0.728 s`, printed `8`, and did not rebuild `Dep`. Both `setup-file` calls exited `0` (`importArts.Dep` resolved to the frozen producer `.olean`). Subsequent `--old --no-build build Dep` exited `0` (`All targets are up-to-date`). | Producer file SHA-256s, byte sizes, and `mtime_ns` remained 100% unchanged. Both consumers produced the exact same `Generated.olean`, `Generated.ilean`, and `Generated.c` SHA-256 digests and `depHash` (`bf169a794ed0fefe`) as the clean build. |
| **3. Two concurrent fresh consumers sharing one writable source-only producer** (`support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/shared-writable-inventory.json`) | Both exited `0` in `~0.87 s`, but **both processes reported building `Dep`** as well as `Generated`, concurrently writing the same `producer/.lake/build` output paths. | Demonstrates that Lake has no cross-process package-build lock (`src/lake/Lake/Util/Lock.lean` notes the historical build lock was removed); concurrent shared-producer writes race on `.lake/build`. |
| **4. Compact cache & concurrency probe suite** (`support/lake-compact-cache-concurrency-and-mathlib-probes/lake-execution/RESULTS.md` & `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-concurrency/RESULTS.md`) | With `LAKE_ARTIFACT_CACHE=true`, building populated 8 cache entries; clean, cache-seeded, and rebuilt runs matched on `.olean`, `.ilean`, and `.c` SHA-256s. Two independent source-identical packages concurrently publishing to a shared `LAKE_ARTIFACT_CACHE` both succeeded and a third consumer fetched the cached output. | Without a preseeded `lake-manifest.json` in `v4.30.0-rc2`, a consumer of a read-only dependency failed trying to create `.lake/config/<pkgName>/lakefile.olean.lock` inside the dependency (see `lake-configuration-elaboration-and-workspace-ownership` for the `v4.30.0`/`v4.31.0`/`v4.34.1` hoisting fix). |

Basis: **execution** + **source** (`support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/runs.json`, `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-execution/lake-runs.json`, `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-concurrency/cache-runs.json`).

### 3. Machine-Observable Reuse vs. Rebuild Signals (`--no-build`, `JobAction`, and `BuildMetadata.synthetic`)

No single Lake signal answers every reuse question (`support/lake-reuse-rebuild-observability/observability-matrix.json` and `support/lake-reuse-rebuild-observability/source-map.json`):

| Observability Question | Primary Machine Signal | Supporting Signal | What It Does **Not** Prove |
| --- | --- | --- | --- |
| Would a required builder action run? | `lake build --no-build` exit code (`0` = no builder needed; `3` = `noBuildCode` when `wantsRebuild = true`) or `Workspace.checkNoBuild` | `*.trace.nobuild` sidecar when preexisting `*.trace` was present | Does **not** prove zero filesystem writes, zero local/remote cache fetches, or zero network I/O. |
| What action class did Lake assign to a job? | `-v --no-ansi` monitor output lines: `Ran` (`unknown`), `Replayed` (`replay`), `Fetched` (`fetch`), `Built` (`build`) | In-process `JobState.action` (`src/lake/Lake/Build/Job/Basic.lean`) | `JobState.merge` takes `max` over `unknown < replay < fetch < build`, so composite `Built` hides subordinate `Fetched` or `Replayed` steps. |
| Was the persisted `.trace` written by a build or a cache fetch? | `BuildMetadata.synthetic` in `*.trace` JSON (`false` = `ofBuild`; `true` = `ofFetch` with empty `inputs`/`log`) | `depHash`, `outputs` descriptors, `inputs`, `log` | Records how the `.trace` file was created, not whether subsequent runs replayed it without rewriting. |
| Are output bytes unchanged and verified? | Independent SHA-256 digest of output files | `--rehash` (forces `fetchFileHash` to recompute file hashes instead of trusting `.hash` sidecars) | Equal bytes alone do not distinguish a deterministic rebuild from a replay or cache fetch. |

In `v4.34.1`, `src/lake/Lake/CLI/Main.lean` defines `--no-build` handling at line 283 and `lake.build` at line 918 (`setupFile` at lines 1021 and 1289; `serve` at line 1151), while `src/lake/Lake/Build/Common.lean` defines `SavedTrace.replayIfUpToDate'` at line 242, `buildUnlessUpToDate?` at line 349, `buildUnlessUpToDate` at line 368, and `getArtifactsUsingCache?` at line 521. Because `buildArtifactUnlessUpToDate` resolves and restores cached artifacts (and writes `.hash` sidecars and synthetic `.trace` files) *before* invoking `buildAction`, `lake build --no-build` can exit `0` while mutating `.lake/build` from the cache.

Basis: **source** + **documentation** (`src/lake/Lake/Build/Job/Basic.lean`, `src/lake/Lake/Build/Run.lean`, `src/lake/Lake/Build/Common.lean`, `src/lake/Lake/Build/Context.lean`, `src/lake/Lake/CLI/Help.lean`, `src/lake/Lake/CLI/Main.lean`).

### 4. `.trace.nobuild` Diagnostic Sidecar Semantics and Lifecycle

When an out-of-date target reaches `buildAction` (`src/lake/Lake/Build/Common.lean`, lines 295–327 in `v4.30.0-rc2`) with `noBuild = true`, Lake sets `wantsRebuild := true` and checks whether the target's ordinary `traceFile` (`<target>.trace`) already exists on disk:

1. **Guarded diagnostic emission:** Only when `traceFile.pathExists` is `true` does Lake write `noBuildTraceFile := traceFile.addExtension "nobuild"` (`<target>.trace.nobuild`) via:
   ```lean
   writeBuildTrace noBuildTraceFile depTrace Json.null {}
   ```
   This guard (introduced in upstream commit `9c852d2f8cc6819a546146aa48d49cc10d32a32a`, after `.nobuild` traces were introduced in `3e16f5332faba0844efb1524222df026095bff14` and tested in `tests/lake/tests/noBuild/test.sh`) prevents a `--no-build` check on an unbuilt package from creating `.lake/build` directories and interfering with subsequent cloud release archive fetches.
2. **Payload format:** `*.trace.nobuild` is serialized using `BuildMetadata.ofBuildCore` with the **current expected** `depTrace.inputs` and `depTrace.hash` (`depHash`), `outputs: null`, `log: []`, and `synthetic: false`. Diffing `*.trace` (old saved trace) against `*.trace.nobuild` (new expected trace) reveals exactly which traced input hash changed.
3. **Non-participation in freshness and non-authoritative lifecycle:**
   - Lake's up-to-date logic (`readTraceFile` and `SavedTrace.replayIfUpToDate'`) never reads `*.trace.nobuild`.
   - `buildAction` calls `removeFileIfExists noBuildTraceFile` only after a normal build body completes successfully. If a later build fails, or if inputs revert so the old `*.trace` becomes current again (returning early before `buildAction`), a stale `*.trace.nobuild` file remains on disk.
   - Conversely, `--no-build` failures that occur when `*.trace` is missing—or in specialized paths that set `wantsRebuild := true` outside `buildAction`, such as `Module.recBuildLtar` (`src/lake/Lake/Build/Module.lean`, lines 832–843 in `v4.30.0-rc2`) when an `.ltar` archive is absent—exit with code `3` without writing a `*.trace.nobuild` file.

Basis: **source** (`src/lake/Lake/Build/Common.lean`, `src/lake/Lake/Build/Module.lean`, `src/lake/Lake/Build/Run.lean`, `tests/lake/tests/noBuild/test.sh`).

## Boundaries

- **Single-platform synthetic execution scope (`not examined` on multi-GiB Mathlib or `v4.34.1` runtime):** The executed clean-vs-seeded and concurrency probes ran on macOS arm64 (`arm64-apple-darwin24.6.0`) on two-module synthetic fixtures at `v4.30.0-rc2`. Full Aeneas/Mathlib clean-vs-seeded rebuild equivalence and `v4.34.1` runtime execution of the concurrency probe were **not examined**.
- **Two-process concurrency trial is not a general safety proof (`unknown` under crash/interruption):** Successful two-consumer reads of a frozen dependency and one two-writer `LAKE_ARTIFACT_CACHE` run do not establish crash consistency or arbitrary multi-writer safety. Concurrent builds against a shared writable package directory are **known not to apply** as a safe pattern because both processes build and overwrite the same `<pkg>/.lake/build` outputs without a package-build lock.
- **`--offline` and `--no-cache` are not OS network sandboxes (`unsupported` as security boundaries):** Lake's `--offline` and `--no-cache` flags configure Lake's own cache/update paths; network denial must be enforced externally when required.
- **`lake --old` does not establish hash-mode key equivalence (`known not to apply`):** Old-mode mtime acceptance after manifest rewrites bypasses `depHash` mismatches and marks outputs non-cacheable (`OutputStatus.isCacheable = false`).

## Evidence

### Pinned Upstream Revisions and Source Blobs
- **Lean 4 / Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`):**
  - `src/lake/Lake/Build/Common.lean` (blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`)
  - `src/lake/Lake/Build/Trace.lean` (blob `656c991fab8a6475802373224514ec7e73f9b18b`)
  - `src/lake/Lake/Build/Module.lean` (blob `21c5f343112a1690390188642a05d6092432ab84`)
  - `src/lake/Lake/Build/ModuleArtifacts.lean` (blob `9863290328250c33d9933b1569387d96ec244da8`)
  - `src/lake/Lake/Build/Job/Basic.lean` (blob `1f0066910478137341388422d8d593ddffbaca18`)
  - `src/lake/Lake/Build/Run.lean` (blob `afae31b7d20a37e6a505d4dc7a9ce875467faf7e`)
  - `src/lake/Lake/Build/Context.lean` (blob `8f2eda8d462334f933f112d7ebc4acd3e9553568`)
  - `src/lake/Lake/Config/Artifact.lean` (blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`)
  - `src/lake/Lake/Config/Cache.lean` (blob `607e6b92108f30e0a57d0de682f7faa283d7d470`)
  - `src/lake/Lake/Config/Env.lean` (blob `eed315c538de746a891d18f72564e88aea64e969`)
  - `src/lake/Lake/Config/Monad.lean` (blob `59e032d7c516298a494c070abb948eafe2474184`)
  - `src/lake/Lake/CLI/Main.lean` (blob `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`)
  - `src/lake/Lake/CLI/Help.lean` (blob `aa96ac1b5fa65178418d4292b49d8086f0d6a9bb`)
  - `src/lake/Lake/Util/Lock.lean` (blob `78f109574faedcfedd6d142ed51b5b700082aa63`)
  - `src/Lean/Setup.lean` (blob `38e7f619e852e8ae17d13c94de35a25d279387b6`)
  - `tests/lake/tests/noBuild/test.sh` (blob `a538bb91d5429c8f60a8336aa572d65126bc6824`)
- **Lean 4 / Lake `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
  - `src/lake/Lake/Build/Common.lean` (1,112 lines, SHA-256 `03c6017c49303720...`), `src/lake/Lake/Build/Trace.lean` (391 lines, SHA-256 `ae8987432fdb2f72...`), `src/lake/Lake/Build/Actions.lean` (212 lines, SHA-256 `9c7d7101f89eb1d0...`), `src/lake/Lake/Build/Module.lean` (1,553 lines, SHA-256 `4a84a2896dedea36...`), `src/lake/Lake/Config/Cache.lean` (1,101 lines, SHA-256 `c3ee5a7565a656d8...`), `src/lake/Lake/CLI/Main.lean` (1,333 lines, SHA-256 `3afad780df8292a7...`).
- **Anneal (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`):**
  - `anneal/flake.nix` (blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, lines 293–490).
- **Mathlib (`leanprover-community/mathlib4`):**
  - `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (`v4.30.0-rc2`) and `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`).

### Preserved Package Support Material
- **Concurrency and clean/seeded execution probe (`support/lake-cache-concurrency-execution-probe/`):**
  - `support/lake-cache-concurrency-execution-probe/SUPPORT.md`
  - `support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/probe.py`
  - `support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/runs.json`
  - `support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/clean-inventory.json`
  - `support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/seeded-inventory.json`
  - `support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/shared-writable-inventory.json`
  - Preserved workspace trees under `support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/clean/`, `support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/seeded/`, and `support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/shared-writable/`.
- **Compact execution and concurrency probe suite (`support/lake-compact-cache-concurrency-and-mathlib-probes/`):**
  - `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-execution/RESULTS.md`
  - `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-execution/artifact-inventories.json`
  - `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-execution/batch-lsp-comparisons.json`
  - `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-execution/lake-runs.json`
  - `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-concurrency/RESULTS.md`
  - `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-concurrency/cache-runs.json`
  - `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-concurrency/followup-runs.json`
  - `support/lake-compact-cache-concurrency-and-mathlib-probes/lake-concurrency/lsp-events.json`
- **Reuse/rebuild observability matrices (`support/lake-reuse-rebuild-observability/`):**
  - `support/lake-reuse-rebuild-observability/observability-matrix.json`
  - `support/lake-reuse-rebuild-observability/source-map.json`

## Revalidation

1. **Rerun the synthetic equivalence and concurrency probe:**
   - Using `anneal-lean-run`, execute `support/lake-cache-concurrency-execution-probe/lake-cache-concurrency/probe.py` against the target Lean/Lake toolchain (`v4.30.0-rc2` or `v4.34.1`).
   - Verify that: (a) clean and cache-seeded consumers produce identical SHA-256 digests for `.olean`, `.ilean`, and `.c` (plus `.olean.server`, `.olean.private`, and `.ir.sig` when module-system facets are enabled in `v4.34.1`); (b) concurrent consumers against a frozen prebuilt dependency exit `0` with zero producer mutations; and (c) `setup-file` resolves imported artifacts to byte-identical `.olean` files.
2. **Verify observability and `.trace.nobuild` behavior:**
   - Build a single-module target cleanly, then run `lake build -v --no-ansi --no-build` and confirm exit code `0` with `Replayed` action output.
   - Modify one traced source input, run `lake build -v --no-ansi --no-build`, and confirm exit code `3` plus creation of `<target>.trace.nobuild` with `outputs: null` and the new expected `depHash`.
   - Revert the source edit without rebuilding, rerun `lake build --no-build`, and confirm exit code `0` even while the stale `<target>.trace.nobuild` file remains on disk until a subsequent `buildAction` completes.
