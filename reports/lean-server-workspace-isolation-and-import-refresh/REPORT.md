# Lean 4 Language Server Workspace Isolation, Concurrency, and Imported-Generation Refresh

## Summary

Across Lean 4 `v4.29.0` (`leanprover/lean4@98dc76e3c0a9b856c9b98726b713fb04fab16740`), `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), and `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), the Lean language server (`lean --server` and `lake serve`) provides per-open-document process isolation via child `lean --worker` processes, but **does not implement per-workspace configuration isolation inside a single server process** or live cross-module importing of unsaved open buffers:

1. **Single-Workspace Process Boundary (`Watchdog.lean`, `SetupFile.lean`, `Lake/CLI/Serve.lean`)**: One Lean language-server watchdog can manage many open document URIs, spawning a separate `lean --worker` subprocess per URI. However, `InitializeParams.rootUri?` is explicitly ignored in favor of the server process's current working directory (`ProtocolOverview.lean`), and LSP `workspaceFolders` / `workspace/didChangeWorkspaceFolders` are unimplemented TODOs (`Workspace.lean`, `Capabilities.lean`). Every worker inherits the watchdog's working directory, environment variables, and initialization parameters, and invokes `lake setup-file <file> -` without per-file directory or environment overrides. `lake serve` loads a single Lake `Workspace` (`LoadConfig`), configuring workspace modules via `findModuleBySrc?` and non-workspace files via `setupExternalModule` against that same loaded workspace rather than discovering a second project's Lake configuration.
2. **Concurrent Server Isolation, Cancellation, and Memory Scaling**:
   - In two-server direct `lean --server` concurrency tests sharing a read-only `Dep.olean` (mode `0444`, SHA-256 `b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71`), each server maintained isolated goals (`h : n = 1` vs. `h : n = 2`) and unsaved edits (`no goals` in `a1` while `b1` stayed unsolved), returned JSON-RPC error `{"code":-32800,"message":""}` on explicit `$/cancelRequest`, and deterministically reconstructed state after `SIGKILL` (`-9`) of watchdog PID `76746` (replaced by PID `76754` while peer PID `76747` stayed live).
   - Across four concurrent bare-core `lean --server` processes on an 8 GiB macOS arm64 host over 10 edit passes and 8 idle samples (`proc_pidinfo` RSS), 1 loaded server used `67.7 MB`, 4 loaded servers summed to `484,147,200` bytes, pass 1 reached `709,705,728` bytes, peak RSS after pass 5 reached `801,865,728` bytes, post-pass-10 idle settled at `639,385,600` bytes, and shutdown returned to `0` bytes (`38%` lowest reported free memory during the server run).
   - Across two concurrent servers over independent generated workspaces sharing one local immutable Aeneas/Mathlib dependency tree (`lake --offline build Generated`), 1 loaded server used `218,316,800` bytes RSS (`47%` free memory vs. `55%` baseline), 2 loaded servers used `361,938,944` bytes RSS (`30%` free memory, `56.1 GB` / `52.3 GiB` free disk), independent tactic edits (`trivial` $\rightarrow$ `exact True.intro`) peaked at `377,454,592` bytes RSS (`30%` free), and graceful restart of worker A while B remained live recorded `164,610,048` bytes RSS (`30%` free) before clean shutdown (`0` bytes RSS, `50%` free).
3. **Generated-File Ownership and Unsaved Cross-Module Import Boundaries**:
   - Under normative LSP 3.18 (`didOpen`, `didChange`, `didClose`) and `Lean.Server.Watchdog`, `didOpen` transfers document content ownership to the client; overwriting a generated `.lean` file on disk via Aeneas (`Translate.extract_file`) does not update an already-open LSP buffer until `didChange` or `didClose`/`didOpen`.
   - Under both direct `lean --server` and `lake --keep-toolchain --no-cache serve`, open buffers do **not** form a live cross-module import environment: editing an open producer `Dep.lean` buffer to version 2 (`sharedValue := 4`, SHA-256 `c9d2489f...`) while on-disk `Dep.lean` (`3f73ffee...`) and compiled `Dep.olean` define `sharedValue := 3` leaves both resident and newly opened `Consumer.lean` buffers proving `sharedValue = 3` (`no goals`). Opening a buffer-only module `OnlyBuffer.lean` with no on-disk file or `.olean` fails in importing documents with `unknown module prefix 'OnlyBuffer'`.
4. **Imported-Generation Staleness Across Workers and Versions (`v4.29.0` and `v4.30.0-rc2`)**:
   - After writing and rebuilding `Dep.olean` with `sharedValue := 4` (changing `Dep.olean` from `b44f5db1...` to `142f9093...` in direct mode, or `.lake/build/lib/lean/Dep.olean` from `edb5a581...` to `606f9991...` under `lake serve`) and sending `workspace/didChangeWatchedFiles`, an already-open consumer worker continues to return `no goals` (with `lake serve` emitting `"Imports are out of date and should be rebuilt"`), whereas a newly opened consumer or a closed-and-reopened consumer in the **same** server process loads the new `.olean` and reports the remaining goal `⊢ sharedValue = 3` (matching fresh batch `lean --json` exit `1`).
   - Querying the still-open old consumer again *after* the newly opened consumer has finished reporting `⊢ sharedValue = 3`—and again after an additional `0.5 s` delay and fresh `waitForDiagnostics`—still returns `no goals` identically in both `v4.29.0` (`2974847f...`) and `v4.30.0-rc2` (`b48bc5ab...`), proving that one server process simultaneously serves two different imported module generations across open workers until the stale worker is closed/reopened or restarted.

## Applicability

### Covered Versions and Repository Subjects

| Subject | Repository | Revision | Version / Digest |
| :--- | :--- | :--- | :--- |
| Lean 4 prior baseline | `leanprover/lean4` | `98dc76e3c0a9b856c9b98726b713fb04fab16740` | `v4.29.0` (`lean` SHA-256 `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37`) |
| Lean 4 baseline selected by Anneal | `leanprover/lean4` | `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` | `v4.30.0-rc2`, Lake `5.0.0-src+3dc1a08` (`lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`) |
| Lean 4 newer revalidation target | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | `v4.34.1` |
| Anneal workspace & source | `google/zerocopy` | `bd0956be95c5f798f0c0484921b9b9d1fc6e9988` / `41f5b37afe7060fd9fe08c00b200672cd76d77b9` | `anneal/src`, `anneal/flake.nix` |
| Aeneas Lean support library | `google/aeneas` | `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` | Generated workspace dependency |
| Aeneas translator | `AeneasVerif/aeneas` | `ac9f1bc5262a5e4ff1e24ca78617121382202727` | `nightly-2026.06.03` |
| Language Server Protocol | `microsoft/language-server-protocol` | `de9a671ae6ba374cc748a29c1c620cbc536302ff` | Specification `3.18` |

### Execution Environment

Runtime probes were executed on `arm64-apple-darwin24.6.0` (8 GiB physical RAM) with `LEAN_NUM_THREADS=1`, using both direct `lean --server` (`LEAN_PATH` pointing to compiled `.olean` fixtures) and `lake --keep-toolchain --no-cache serve` / `lake --offline build Generated`.

## Findings

### 1. Single-Workspace Process Architecture vs. Per-File Worker Isolation

#### Ignored `rootUri` and Unimplemented `workspaceFolders`

- **LSP root selection (`src/Lean/Server/ProtocolOverview.lean`, blob `4f493fc900319113e00a0a9c0f5eac4c3e5bb8e5`, line 58)**: Lean's server protocol overview explicitly documents a deviation from standard LSP: `InitializeParams.rootUri?` is ignored, and the language server uses the current working directory of the server process instead.
- **Unimplemented multi-folder capabilities**: Although `src/Lean/Data/Lsp/InitShutdown.lean` (blob `e964ff53076c2e5bb6eed1ac776bf721c7a1ff90`) parses `rootUri?` and `workspaceFolders?`, `src/Lean/Data/Lsp/Workspace.lean` (blob `bbe312565dd8958d38f333642d839fb5874faa0f`) leaves `WorkspaceFoldersServerCapabilities`, `DidChangeWorkspaceFoldersParams`, and `WorkspaceFoldersChangeEvent` as unimplemented TODOs, and `src/Lean/Data/Lsp/Capabilities.lean` (blob `886e54140b4571bfc1e6b28fcb75ad196df0199e`) advertises no workspace-folder capability.
- **Per-URI workers inherit watchdog context (`src/Lean/Server/Watchdog.lean`, `v4.30.0-rc2` blob `68ed22f9178c9ae917c595c364d23df902d9478f`; `v4.34.1` 1,789 lines, SHA-256 `b7effb6f7e34f7a3...`, `FileWorker` at line 229)**: The watchdog keys workers by `DocumentUri` and spawns `lean --worker` (`startFileWorker`) for each open file without a per-worker `cwd` or environment override. Each worker calls `Lean.determineLakePath` (`src/Lean/Util/LakePath.lean`, blob `ad9adf149c25c15df499e7baf4e5574cfd23ffe9`) and runs `lake setup-file <absolute-file-path> -` (`src/Lean/Server/FileWorker/SetupFile.lean`, blob `35a756819a8de5ebb05256bb39d83148f9f24145`, line 25) in that inherited process context.
- **Single loaded Lake workspace (`src/lake/Lake/CLI/Serve.lean`, blob `27d3e89530105b7ea9fe9f951b9459c1ee1f9cc9`; `src/lake/Lake/Load/Config.lean`, `v4.30.0-rc2` blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`, `v4.34.1` 84 lines, SHA-256 `7292223420baa665...`; `src/lake/Lake/Load/Package.lean`, blob `e9e858a54048ffa96972d264dbd51ca35b4ba403`; `src/lake/Lake/Build/Module.lean`, `v4.30.0-rc2` blob `21c5f343112a1690390188642a05d6092432ab84`, `v4.34.1` 1,553 lines, SHA-256 `4a84a2896dedea36...`, `Module.presetupFacetConfig` at line 630)**: `lake serve` loads one `Workspace` from `LoadConfig.wsDir` and spawns `lean --server` with that workspace's augmented environment and root `moreGlobalServerArgs`. When `lake setup-file` runs `setupServerModule`, files matching `findModuleBySrc?` use their workspace module configuration, while files outside the workspace use `setupExternalModule` against the **already-loaded** workspace rather than discovering a separate Lake project. (In `v4.31.0` through `v4.34.1`, `LoadConfig.configDir` at `src/lake/Lake/Load/Config.lean` line 83 and `src/lake/Lake/Load/Lean/Elab.lean` lines 180–185 additionally hoist compiled Lake configuration artifacts `.lake/config/<pkgIdx>/` into the root workspace's `.lake/` directory so read-only shared path dependencies are not mutated during workspace load.)

### 2. Concurrent Server Isolation, Cancellation, Watchdog Replacement, and Memory Scaling

#### Two-Server Shared-`.olean` Isolation, Cancellation, and Watchdog Kill/Restart (`support/lean-server-concurrency-experiment/`)

Using `support/lean-server-concurrency-experiment/lean-server-concurrency/probe.py` (SHA-256 `ad632d2d171d55d92929919d5593e63f5deeb2c86b4444b7b8b379ff6a4e0cd4`) and `support/lean-server-concurrency-experiment/lean-server-concurrency/transcript.json` (SHA-256 `1d499e67adf7177731f6beda67a9b228e8ae2e3a0d057ee9ac00294d51846fa0`), `support/lean-server-concurrency-experiment/lean-server-concurrency/shared/Dep.lean` (`def sharedValue : Nat := 3`) was compiled to read-only `support/lean-server-concurrency-experiment/lean-server-concurrency/shared/Dep.olean` (mode `0444`, SHA-256 `b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71`) and imported via `LEAN_PATH` by two simultaneous `lean --server` watchdogs (`0.779–1.034 s` session duration) in `a1/` (`support/lean-server-concurrency-experiment/lean-server-concurrency/a1/Proof.lean`, SHA-256 `2f1b9d3265d9685448c8e45d7e9da6a7e8c4eea51111fe333f913ed0268eac09`) and `b1/` (`support/lean-server-concurrency-experiment/lean-server-concurrency/b1/Proof.lean`, SHA-256 `b89c27cc6e74aae4da6a1a68f1ead46c9257561f10ed59181fb19f287f12ad24`):

| Event | Observed Server & Batch Behavior | Boundary / Constraint |
| :--- | :--- | :--- |
| Two live servers, same basename `Proof.lean` | `a1` returned goal with `h : n = 1` and `⊢ n + sharedValue = 1 + sharedValue`; `b1` returned `h : n = 2` and `⊢ n + sharedValue = 2 + sharedValue`. Both emitted `Elab.synthPlaceholder` and `Tactic.unsolvedGoals` matching `lean --json` exit `1` (batch 1-based `[3, 8]` vs. LSP 0-based `[2, 8]`). | One small file per `cwd`; no concurrent import mutations. |
| Unsaved edit in `a1` (version 2, matching `support/lean-server-concurrency-experiment/lean-server-concurrency/a2/Proof.lean`) | Replacing the placeholder with `exact congrArg (fun x => x + sharedValue) h` cleared `a1` version-2 diagnostics and returned `{"goals":[],"rendered":"no goals"}` after the tactic (matching batch `a2` exit `0`), while `b1` retained its `n = 2` goal and `a1/Proof.lean` on disk stayed at version 1. | Proves per-session snapshot isolation; pre-tactic cursor queries in solved `a1` still show the initial goal. |
| Explicit request cancellation (`$/cancelRequest`) | Sending `$/lean/plainGoal` (request ID 5) to `b1` followed immediately by `$/cancelRequest` returned JSON-RPC error `{"code":-32800,"message":""}` (`FileWorker.lean` lines 596, 869). | Cancellation races with elaboration; callers must still fence against late responses. |
| Close/reopen in same `cwd` | `didClose` then `didOpen` at version 3 with version-1 bytes in `a1` restored the two original errors and unsolved goal. | Same `cwd` and unchanged `Dep.olean`. |
| Watchdog `SIGKILL` and replacement | Killing `a1` watchdog PID `76746` (`-9`) and launching replacement PID `76754` on the recorded version-1 bytes reproduced both diagnostics and the original goal and exited `0`, while `b1` watchdog PID `76747` stayed live. | Deterministic reconstruction from client-retained source bytes; `Dep.olean` remained byte-identical (`b44f5db1...`). |

#### Four-Server Bare-Core vs. Two-Server Generated-Project Process-Tree RSS

Process-tree resident set size (`proc_pidinfo` via `support/lean-server-memory-and-protocol-concurrency/proc-tree.c` and `support/lean-v1-concurrent-workspace-server-reuse/proc-tree.c`) and system free memory (`memory_pressure -Q`) were measured across two multi-server workloads:

| Workload & Support Package | Concurrent Servers | Sample Stage | Summed Process-Tree RSS (Bytes) | System Free Memory (`memory_pressure -Q`) |
| :--- | :--- | :--- | ---: | ---: |
| Bare-core `lean --server` sharing `Dep.olean` (`support/lean-server-memory-and-protocol-concurrency/server-memory.py`, `support/lean-server-memory-and-protocol-concurrency/server-memory/transcript.json`, `support/lean-server-memory-and-protocol-concurrency/lsp-two-events.json`) | 1 server | Initial load (sample 1) | ~`67,700,000` (`67.7 MB`) | $\ge 38\%$ |
| Bare-core `lean --server` sharing `Dep.olean` | 4 servers | Initial load (all 4 loaded) | `484,147,200` | $\ge 38\%$ |
| Bare-core `lean --server` sharing `Dep.olean` | 4 servers | After edit pass 1 | `709,705,728` | $\ge 38\%$ |
| Bare-core `lean --server` sharing `Dep.olean` | 4 servers | Peak (after edit pass 5 of 10) | `801,865,728` | $\ge 38\%$ |
| Bare-core `lean --server` sharing `Dep.olean` | 4 servers | After 10 edit passes + 8 idle samples | `639,385,600` | $\ge 38\%$ |
| Bare-core `lean --server` sharing `Dep.olean` | 0 (stopped) | Clean shutdown | `0` | $\ge 38\%$ |
| Generated workspaces sharing immutable Aeneas/Mathlib tree (`support/lean-v1-concurrent-workspace-server-reuse/run.py`, `support/lean-v1-concurrent-workspace-server-reuse/concurrency-transcript.json`, `worker-a/`, `worker-b/`) | 0 (baseline) | Host baseline before launch | `0` | `55%` |
| Generated workspaces sharing immutable Aeneas/Mathlib tree | 1 server | Worker A loaded (`⊢ True` / `no goals`) | `218,316,800` | `47%` |
| Generated workspaces sharing immutable Aeneas/Mathlib tree | 2 servers | Workers A & B loaded (`56.1 GB` / `52.3 GiB` disk free) | `361,938,944` | `30%` |
| Generated workspaces sharing immutable Aeneas/Mathlib tree | 2 servers | Peak after edits (`trivial` $\rightarrow$ `exact True.intro`) | `377,454,592` | `30%` |
| Generated workspaces sharing immutable Aeneas/Mathlib tree | 2 servers | Graceful restart of Worker A while B stayed live | `164,610,048` | `30%` |
| Generated workspaces sharing immutable Aeneas/Mathlib tree | 0 (stopped) | Clean shutdown | `0` | `50%` |

### 3. Generated-File Interactive Workflows and Unsaved Cross-Module Imports

#### Three-Layer State Separation for Aeneas-Generated Lean (`support/lean-generated-file-interactive-workflows/`)

Combining normative LSP 3.18 (`_specifications/lsp/3.18/textDocument/{didOpen,didChange,didClose}.md`, blobs `f2bc2141ca7b4efdc1521493470cc631cf083d99`, `81e7475181818d44229c10dbcc25de7f3de83c69`, `e8c956a6402a8a7ff031839fa58fba5d39c11f6d`), Lean's server (`Watchdog.lean` blob `68ed22f9...`, `FileWorker.lean` blob `c803034e...`, `RequestCancellation.lean` blob `7d310d0c...`, `Language/Lean.lean` blob `124d4739...`), and Aeneas (`src/Translate.ml` blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`, `src/Main.ml` blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`, `src/Config.ml` blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355` emitting single-file or `-split-files` `Types.lean` / `Funs.lean` outputs) separates three distinct state layers recorded in `support/lean-generated-file-interactive-workflows/architecture-workflow.json` and `support/lean-generated-file-interactive-workflows/source-map.json`:

| Generated Artifact Role | What Changes First | What Does **Not** Happen Automatically | Required Transition Before Semantic Query |
| :--- | :--- | :--- | :--- |
| Generated `.lean` file is itself open in LSP | Aeneas overwrites disk bytes | Open LSP document does not adopt disk bytes (watchdog retains client text and restarts workers from retained `FileMap`) | Send versioned `didChange` with regenerated bytes, or `didClose` + `didOpen`, then await readiness. |
| Generated `.lean` file is closed | Aeneas overwrites disk bytes | No open-document state exists to update | Next `didOpen` supplies regenerated text; dependent imports still require compiled `.olean` artifacts. |
| Generated module is imported by an open proof file | Generated source and/or `.olean` changes | Dependent open worker does not switch to unsaved buffer or newly compiled `.olean` automatically | Compile/rebuild the dependency and refresh/restart (`didClose` + `didOpen` or worker restart) the dependent worker. |
| Regeneration alters split-module graph (`Types.lean`, `Funs.lean`) | Multiple files/imports appear, move, or change | Single-URI `didChange` does not reconstruct the package/import graph | Reconcile open documents, rebuild package artifacts, and restart affected workers against a single `(project identity, generated-package generation, document URI, document version, dependency generation, semantic readiness)` tuple. |

#### Empirical Proof That Open Buffers Do Not Import Unsaved Producer Edits (`lean --server` and `lake serve`)

Two complementary execution probes tested whether an open consumer document (`import Dep; theorem current : sharedValue = 3 := by rfl`, SHA-256 `304bffdabf0dfc2274583df1773c83655d985883b359f889c56860b407660059`) observes an unsaved `didChange` (version 2) in an open producer `Dep.lean` buffer (`def sharedValue : Nat := 4`, SHA-256 `c9d2489f2aab1d2e058b7952c3c179fa39a8b9ce2edcf63bb6d0070c27c0943d`) while on-disk `Dep.lean` (`def sharedValue : Nat := 3`, SHA-256 `3f73ffee4b6b6612fd97b89a1a9f46db69eb6a200ce3f4d322fba02e803c0b60`) and compiled `Dep.olean` remain at `3`:

| Launch Mode & Support Package | Initial `Dep.olean` SHA-256 (`sharedValue := 3`) | Unsaved Producer Edit (`sharedValue := 4`) Result | Buffer-Only Module (`OnlyBuffer.lean`) | Post-Rebuild `Dep.olean` SHA-256 (`sharedValue := 4`) + `didChangeWatchedFiles` |
| :--- | :--- | :--- | :--- | :--- |
| Direct `lean --server` (`support/lean-unsaved-cross-module-import/probe.py`, `transcript.json`, `check.py`) | `b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71` | Both resident consumer and newly opened consumer return `no goals` (matching batch exit `0` against old `.olean`). | Opening `OnlyBuffer.lean` (`onlyBufferValue := 9`) with no disk file/`.olean` yields `unknown module prefix 'OnlyBuffer'` in `ImportsOnlyBuffer.lean`. | `142f9093501e0337ed2634fe0070957086cead5140326fd70b7fc6c6e29bbaeb`: resident consumer still returns `no goals`; newly opened consumer and closed/reopened consumer return `⊢ sharedValue = 3` (matching batch exit `1`). |
| `lake --keep-toolchain --no-cache serve` (`support/lean-lake-unsaved-cross-module-import/probe.py`, `transcript.json`, `check.py`) | `edb5a5815bd08ea4a0a1011bd155ba187c92cac7c84ebcc2a63cf2f8dfae0bf4` | Both resident consumer and newly opened consumer return `no goals` (`lake setup-file` uses compiled `.olean`, not open buffer). | Not repeated in Lake run (covered in direct run). | `606f9991b03bfcc24fefc5070bfb6f434ba7377de57541085d271e8eb21552c2`: resident consumer still returns `no goals` + `"Imports are out of date and should be rebuilt"` diagnostic; newly opened and closed/reopened consumers return `⊢ sharedValue = 3` + `rfl` error (matching `lake env lean --json` exit `1`). |

### 4. Same-Server Imported-Generation Staleness Across `v4.29.0` and `v4.30.0-rc2`

To verify whether a single `lean --server` process can simultaneously serve stale and fresh imported module generations—and whether this behavior changed between `v4.29.0` (`98dc76e3c0a9b856c9b98726b713fb04fab16740`) and `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`)—`support/lean-same-server-dependency-generation/probe.py` and the cross-version suite `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v429/probe.py` and `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v430/probe.py` executed the following sequence:

1. Open `OldOpen.lean` (`theorem current : sharedValue = 3 := by rfl`) against `Dep.old.olean` (`sharedValue := 3`) and verify `$/lean/plainGoal` returns `no goals`.
2. Rebuild `Dep.olean` from `sharedValue := 4` while the server stays running and send `workspace/didChangeWatchedFiles`.
3. Query `OldOpen.lean`: it still returns `no goals`.
4. Open `NewOpen.lean` (identical proof bytes) in the **same** server process: `NewOpen.lean` loads the rebuilt `Dep.olean`, emits an `rfl` tactic failure diagnostic, and returns `⊢ sharedValue = 3`.
5. Query `OldOpen.lean` **again** after `NewOpen.lean` is ready (and in the cross-version probe, after an additional `0.5 s` delay and a fresh `waitForDiagnostics` request on `OldOpen.lean`): in both `v4.29.0` and `v4.30.0-rc2`, `OldOpen.lean` still returns `no goals` while `NewOpen.lean` in the same server holds `⊢ sharedValue = 3`.
6. Close and reopen `OldOpen.lean` at document version 2: it now spawns a fresh worker that loads the new `Dep.olean` and returns `⊢ sharedValue = 3`, agreeing with fresh batch `lean` exit `1`.

## Boundaries

- **Single-workspace process boundary (`unsupported`)**: Merging multiple independent Lake workspaces with conflicting `lean-toolchain` files, `lake-manifest.json` graphs, `LEAN_PATH` / `LEAN_SRC_PATH` directories, native plugins/dynlibs, or root server arguments into a single `lean --server` or `lake serve` process is unsupported across `v4.29.0`, `v4.30.0-rc2`, and `v4.34.1`.
- **Unsaved cross-module imports (`unsupported`)**: Importing unsaved edits from another open LSP buffer without writing and compiling `.olean` artifacts on disk is unsupported in both direct `lean --server` and `lake serve`.
- **Measured RSS scope (`not examined` for full Mathlib active-file fanout)**: Summed `proc_pidinfo` RSS across process trees (`801,865,728` bytes peak for 4 bare-core servers; `377,454,592` bytes peak for 2 generated-project servers) double-counts shared pages and is not macOS `phys_footprint`; multi-worker capacity under large active Mathlib file counts or hours-long sessions was not examined here.
- **No checked-in MCP bridge in `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`**: The inspected checkout had no MCP server implementation in `anneal/src`, so the state-tuple and worker-refresh rules are protocol requirements derived from Lean LSP behavior.

## Evidence

### Staged Support Artifacts and Verification Scripts

- **Two-Server Concurrency, Cancellation, and Watchdog Restart (`support/lean-server-concurrency-experiment/`)**:
  - `support/lean-server-concurrency-experiment/SUPPORT.md`
  - `support/lean-server-concurrency-experiment/lean-server-concurrency/probe.py` (SHA-256 `ad632d2d171d55d92929919d5593e63f5deeb2c86b4444b7b8b379ff6a4e0cd4`)
  - `support/lean-server-concurrency-experiment/lean-server-concurrency/transcript.json` (SHA-256 `1d499e67adf7177731f6beda67a9b228e8ae2e3a0d057ee9ac00294d51846fa0`)
  - `support/lean-server-concurrency-experiment/lean-server-concurrency/shared/Dep.lean` and `support/lean-server-concurrency-experiment/lean-server-concurrency/shared/Dep.olean` (SHA-256 `b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71`)
  - `support/lean-server-concurrency-experiment/lean-server-concurrency/a1/Proof.lean` (SHA-256 `2f1b9d3265d9685448c8e45d7e9da6a7e8c4eea51111fe333f913ed0268eac09`), `support/lean-server-concurrency-experiment/lean-server-concurrency/a2/Proof.lean`, and `support/lean-server-concurrency-experiment/lean-server-concurrency/b1/Proof.lean` (SHA-256 `b89c27cc6e74aae4da6a1a68f1ead46c9257561f10ed59181fb19f287f12ad24`)
- **Four-Server Bare-Core Memory and Protocol Concurrency (`support/lean-server-memory-and-protocol-concurrency/`)**:
  - `support/lean-server-memory-and-protocol-concurrency/server-memory.py`
  - `support/lean-server-memory-and-protocol-concurrency/proc-tree.c`
  - `support/lean-server-memory-and-protocol-concurrency/server-memory/transcript.json`
  - `support/lean-server-memory-and-protocol-concurrency/lsp-two-events.json`
- **Two-Server Generated Workspace Reuse and Memory (`support/lean-v1-concurrent-workspace-server-reuse/`)**:
  - `support/lean-v1-concurrent-workspace-server-reuse/run.py`, `support/lean-v1-concurrent-workspace-server-reuse/proc-tree.c`, `support/lean-v1-concurrent-workspace-server-reuse/concurrency-transcript.json`
  - `support/lean-v1-concurrent-workspace-server-reuse/worker-a/lake-manifest.json`, `support/lean-v1-concurrent-workspace-server-reuse/worker-a/lakefile.lean`, `support/lean-v1-concurrent-workspace-server-reuse/worker-a/lean-toolchain`, `support/lean-v1-concurrent-workspace-server-reuse/worker-a/generated/Generated.lean`, `support/lean-v1-concurrent-workspace-server-reuse/worker-a/generated/RelocateProbeRelocateProbe93d79f43b0c543cb/Funs.lean`, `support/lean-v1-concurrent-workspace-server-reuse/worker-a/generated/RelocateProbeRelocateProbe93d79f43b0c543cb/Types.lean`
  - `support/lean-v1-concurrent-workspace-server-reuse/worker-b/lake-manifest.json`, `support/lean-v1-concurrent-workspace-server-reuse/worker-b/lakefile.lean`, `support/lean-v1-concurrent-workspace-server-reuse/worker-b/lean-toolchain`, `support/lean-v1-concurrent-workspace-server-reuse/worker-b/generated/Generated.lean`, `support/lean-v1-concurrent-workspace-server-reuse/worker-b/generated/RelocateProbeRelocateProbe93d79f43b0c543cb/Funs.lean`, `support/lean-v1-concurrent-workspace-server-reuse/worker-b/generated/RelocateProbeRelocateProbe93d79f43b0c543cb/Types.lean`
- **Generated-File Interactive Workflow Model (`support/lean-generated-file-interactive-workflows/`)**:
  - `support/lean-generated-file-interactive-workflows/architecture-workflow.json`
  - `support/lean-generated-file-interactive-workflows/source-map.json`
- **Unsaved Cross-Module Imports (`support/lean-unsaved-cross-module-import/` and `support/lean-lake-unsaved-cross-module-import/`)**:
  - Direct server: `support/lean-unsaved-cross-module-import/probe.py` (SHA-256 `dfb4b0d6a351639d489dbc19ce80805d05b7b3b038b2a9ecb9bd21a8005a85d0`), `support/lean-unsaved-cross-module-import/transcript.json` (SHA-256 `0652723327833feb5ff3d5c9d1a7b1db6a60c409732ceb573697ac302e5ab379`), `support/lean-unsaved-cross-module-import/check.py`
  - Lake server: `support/lean-lake-unsaved-cross-module-import/probe.py` (SHA-256 `6813d11267d0b9fb220a20ea7a07cf256bc9c55e48a7f07895db60f4410107d9`), `support/lean-lake-unsaved-cross-module-import/transcript.json` (SHA-256 `27571384be052ed23502f45917a46896671a046e9226e53c8f905f9652035bb6`), `support/lean-lake-unsaved-cross-module-import/check.py`
- **Same-Server and Cross-Version Imported-Generation Refresh (`support/lean-same-server-dependency-generation/` and `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/`)**:
  - `support/lean-same-server-dependency-generation/probe.py`, `support/lean-same-server-dependency-generation/check.py`, `support/lean-same-server-dependency-generation/transcript.json`, `support/lean-same-server-dependency-generation/revalidation-transcript.json`, `support/lean-same-server-dependency-generation/simultaneous-transcript.json`, `support/lean-same-server-dependency-generation/fixture/Dep.lean`, `support/lean-same-server-dependency-generation/fixture/Dep.olean`, `support/lean-same-server-dependency-generation/fixture/OldOpen.lean`, `support/lean-same-server-dependency-generation/fixture/NewOpen.lean`
  - `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/check.py`
  - `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v429/probe.py`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v429/transcript.json`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v429/fixture/Dep.lean`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v429/fixture/Dep.old.olean`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v429/fixture/Dep.olean`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v429/fixture/OldOpen.lean`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v429/fixture/NewOpen.lean`
  - `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v430/probe.py`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v430/transcript.json`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v430/fixture/Dep.lean`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v430/fixture/Dep.old.olean`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v430/fixture/Dep.olean`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v430/fixture/OldOpen.lean`, `support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/v430/fixture/NewOpen.lean`

## Revalidation

1. **Offline Transcript Assertions**: Run the offline checkers without launching Lean:
   ```console
   python3 support/lean-unsaved-cross-module-import/check.py
   python3 support/lean-lake-unsaved-cross-module-import/check.py
   python3 support/lean-same-server-dependency-generation/check.py
   python3 support/lean-same-server-dependency-generation/check.py revalidation-transcript.json
   python3 support/lean-same-server-dependency-generation/check.py simultaneous-transcript.json
   python3 support/lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/check.py
   ```
2. **Live Probe Replay on a Target Toolchain**: Copy the support directories to a scratch workspace, set `LEAN_BIN` to the target `lean` binary (with `lake` adjacent for Lake probes), and execute:
   ```console
   LEAN_BIN=/path/to/lean python3 support/lean-unsaved-cross-module-import/probe.py
   LEAN_BIN=/path/to/lean python3 support/lean-lake-unsaved-cross-module-import/probe.py
   LEAN_BIN=/path/to/lean python3 support/lean-same-server-dependency-generation/probe.py
   ```
3. **Source Surface Audit for Future Releases**: Diff `src/Lean/Server/ProtocolOverview.lean`, `src/Lean/Data/Lsp/{InitShutdown,Workspace,Capabilities}.lean`, `src/Lean/Server/Watchdog.lean`, `src/Lean/Server/FileWorker/SetupFile.lean`, `src/lake/Lake/CLI/Serve.lean`, `src/lake/Lake/Load/Config.lean`, and `src/lake/Lake/Build/Module.lean` to check whether `rootUri` / `workspaceFolders` or per-worker workspace discovery has been implemented.
