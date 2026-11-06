# Lean 4 Language Server Tactic-State Queries, Goal Versioning, and Incremental Diagnostics

## Summary

Across Lean 4 `v4.29.0` (`leanprover/lean4@98dc76e3c0a9b856c9b98726b713fb04fab16740`), `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), and `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), the Lean language server exposes cursor-level tactic-state queries (`$/lean/plainGoal` and structured InfoView RPC `Lean.Widget.getInteractiveGoals`), versioned diagnostic barriers (`textDocument/waitForDiagnostics`), client-owned open-buffer semantics, and—starting in `v4.34.1`—an opt-in incremental diagnostic publication capability (`lean.incrementalDiagnosticSupport`):

1. **Two Goal-Query Interfaces Sharing Snapshot/`InfoTree` Lookup (`FileWorker.lean`, `RequestHandling.lean`, `InfoUtils.lean`)**:
   - Target documents must first be opened via `textDocument/didOpen`. Both goal APIs locate the asynchronous command/elaboration snapshot covering the cursor position and query `InfoTree.goalsAt?` (`findGoalsAt?`) to select `mctxBefore`/`goalsBefore` or `mctxAfter`/`goalsAfter`.
   - `$/lean/plainGoal` (`PlainGoalParams` extending unversioned `TextDocumentPositionParams`) returns `Option PlainGoal` (`{goals: Array String, rendered: String}`, with `goals: []` and `rendered: "no goals"` when solved at that position, or `null` outside tactic proofs).
   - Structured InfoView RPC connects a per-worker session via `$/lean/rpc/connect` (30 s timeout without 10 s `$/lean/rpc/keepAlive` notifications; worker restart invalidates sessions with `RpcNeedsReconnect`) and calls `$/lean/rpc/call` with `method: "Lean.Widget.getInteractiveGoals"` (`WidgetRequests.lean`), returning `Option InteractiveGoals` (`InteractiveGoal` in `src/Lean/Widget/InteractiveGoal.lean`, line 54 in `v4.34.1`, with structured hypotheses, tagged target, metavariable ID, and `WithRpcRef` context handles backed by `RpcObjectStore`).
   - Server protocol logging in `v4.30.0-rc2` and `v4.34.1` is enabled via `initialize.initializationOptions.logCfg.logDir` (`InitShutdown.lean` line 58, `Logging.lean` line 21, `Watchdog.lean` line 1748); setting `LEAN_SERVER_LOG_DIR` in the environment alone writes no log, and passing `logDir?` writes to the server `cwd`.
2. **Cross-Version Goal Completion Races and `waitForDiagnostics` Lower-Bound Semantics (`Extra.lean`, `RequestHandling.lean`)**:
   - In both `v4.30.0-rc2` and `v4.34.1`, `WaitForDiagnosticsParams` (`src/Lean/Data/Lsp/Extra.lean`, line 44 in `v4.34.1`) and `handleWaitForDiagnostics` (`src/Lean/Server/FileWorker/RequestHandling.lean`, line 467 in `v4.34.1`) check `p.version ≤ doc.meta.version`. Consequently, `waitForDiagnostics(version=1)` sent *after* document version 2 has completed returns `{}` immediately, and a subsequent unversioned `$/lean/plainGoal` returns version 2's goal (`no goals`).
   - Furthermore, across three direct `lean --server` runs (`v4.30.0-rc2`, SHA-256 `b48bc5ab...`) where version 1 was gated in a `run_tac` waiting for `v1.release` and an unsaved version-2 edit (`⊢ False`) was submitted, version 2 elaborated, completed `waitForDiagnostics(version=2)` (request ID 11), and returned its `⊢ False` goal (request ID 21, even when sent with an extra `textDocument.version: 1` field) **before** version 1 was released and **before** version 1's `waitForDiagnostics(version=1)` (ID 10) and `plainGoal` (`⊢ True`, ID 20) replies arrived. An offline client envelope state machine binding each request at submission time to `(process incarnation, URI, document version, source SHA-256, position)` (`support/lean-goal-envelope-replay/`) deterministically classified all 8 arrival/mutation/restart scenarios across all 3 runs.
3. **Open Buffer Authority Across External Overwrite, Rename, and File Deletion**:
   - Across three direct `lean --server` runs (`support/lean-lsp-open-buffer-path-disappearance/`), an open document edited in memory to version 2 (source B, `⊢ 2 = 2`, SHA-256 `ca471676...`) retained `⊢ 2 = 2` while its on-disk path `Open.lean` (initially source A, `⊢ 1 = 1`, `30089ee2...`) was overwritten externally with source C (`⊢ 3 = 3`, `c97e36df...`), notified via `workspace/didChangeWatchedFiles`, saved with B, and renamed to `Renamed.lean`. After closing `Open.lean` and opening `Renamed.lean`, physically deleting `Renamed.lean` on disk and sending a watched-delete event still left the open buffer serving `⊢ 2 = 2` until `didClose` (after which queries returned `-32801 Cannot process request to closed file`, and recreating `Renamed.lean` with C and reopening at version 2 returned `⊢ 3 = 3`).
4. **Incremental Diagnostic Publication Delta (`v4.30.0-rc2` vs. `v4.34.1`)**:
   - **Source delta**: `v4.30.0-rc2` (`FileWorker.lean` blob `c803034e...`) always publishes full replacement arrays (`stickyInteractiveDiagnostics ++ docInteractiveDiagnostics`) with no `isIncremental` field. `v4.34.1` (`Capabilities.lean` blob `12eec11b...`, `Diagnostics.lean` blob `9353793f...`, `FileWorker.lean` blob `cf8058ac...`, `FileWorker/Utils.lean` blob `e46f44a1...`) adds opt-in `lean.incrementalDiagnosticSupport?` client capability and optional `isIncremental? : Option Bool` on `PublishDiagnosticsParams` (`EditableDocumentCore.publishDiagnostics`), sending an initial full replacement (`isIncremental: false`) and subsequent append-only batches (`isIncremental: true`) unless reset by a sticky diagnostic.
   - **Runtime A/B execution**: Across 6 serialized direct `lean --server` sessions (`v4.30.0-rc2` `b48bc5ab...` vs. `v4.34.1` `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554` with `lean.incrementalDiagnosticSupport` set to `absent`, `false`, and `true` over `Open.lean` `d42fbf3d...` and `Edited.lean` `9caea97a...`), all `v4.30.0-rc2` runs and `v4.34.1` `absent`/`false` runs omitted `isIncremental`, whereas `v4.34.1` with `incrementalDiagnosticSupport: true` emitted `isIncremental: false, false` on its two substantive replacement publications (confirming runtime capability recognition; the two-line fixture did not trigger an `isIncremental: true` append batch).

## Applicability

### Covered Versions and Binary Identities

| Subject | Repository | Revision | Version & Binary SHA-256 |
| :--- | :--- | :--- | :--- |
| Lean 4 prior baseline | `leanprover/lean4` | `98dc76e3c0a9b856c9b98726b713fb04fab16740` | `v4.29.0` |
| Lean 4 baseline selected by Anneal | `leanprover/lean4` | `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` | `v4.30.0-rc2`, Lake `5.0.0-src+3dc1a08` (`lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`) |
| Lean 4 newer revalidation target | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | `v4.34.1` (`lean` SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`) |
| Anneal context | `google/zerocopy` | `41f5b37afe7060fd9fe08c00b200672cd76d77b9` / `bd0956be95c5f798f0c0484921b9b9d1fc6e9988` | `anneal/` |

## Findings

### 1. Tactic-State Query Architecture and Lifecycle (`$/lean/plainGoal` vs. InfoView RPC)

#### Source Architecture (`v4.30.0-rc2` and `v4.34.1`)

Detailed source analysis (`support/lean-server-tactic-state/FINDINGS.md`, `support/lean-server-tactic-state/BOUNDARIES.md`, `support/lean-server-tactic-state/EVIDENCE.md`, `support/lean-server-tactic-state/REVALIDATION.md`) and `v4.34.1` revalidation establish the following server invariants:

- **Watchdog and per-file worker dispatch**: `src/Lean/Server/Watchdog.lean` (`v4.34.1`: 1,789 lines, SHA-256 `b7effb6f7e34f7a3...`, `FileWorker` at line 229) manages per-URI `lean --worker` processes (`src/Lean/Server/FileWorker.lean`, `v4.34.1`: 1,091 lines, SHA-256 `c938b3b122afda96...`, `updateDocument` at line 568, `handleDidChange` at line 583). Target files must be opened via `textDocument/didOpen`.
- **Plain vs. structured interactive goals**:
  - `handlePlainGoal` (`src/Lean/Server/FileWorker/RequestHandling.lean`, `v4.34.1`: 568 lines, SHA-256 `98f9af1acd078638...`, `handlePlainGoal` at line 213, `handlePlainTermGoal` at line 244, `handleWaitForDiagnostics` at line 467) services `$/lean/plainGoal` (`PlainGoalParams` at `src/Lean/Data/Lsp/Extra.lean` line 104 in `v4.34.1`), returning pretty-printed `{goals: Array String, rendered: String}` or `null`.
  - `Lean.Widget.getInteractiveGoals` (`src/Lean/Server/FileWorker/WidgetRequests.lean`) runs over `$/lean/rpc/connect` and `$/lean/rpc/call` (`src/Lean/Server/Rpc/Basic.lean`), returning `Option InteractiveGoals` (`InteractiveGoal` at `src/Lean/Widget/InteractiveGoal.lean` line 54 in `v4.34.1`) with structured hypothesis bundles, tagged expression trees, metavariable IDs, and `WithRpcRef` handles into the worker's `RpcObjectStore`. Both paths call `FileWorker.getInteractiveGoals` and `InfoTree.goalsAt?` (`src/Lean/Server/InfoUtils.lean`).

#### Direct Protocol Lifecycle Transcript (`support/lean-tactic-state-protocol-transcript/`)

Executing `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/probe.py` (SHA-256 `c680ac1a59e9c6e62fbc9378138007c70f986c291cf0a6e13ee8f343cc471b3e`; raw transcript `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/transcript.json` SHA-256 `af2c3500fde8e86baa8bf93599f6ec3bd95787584f5c48359c47a0fc32c04a41`) on `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/Generated.lean` (`theorem demo (n : Nat) (h : n = 0) : n + 0 = 0 := by`) compared version 1 (`  exact ?_`) and unsaved version 2 (`  simpa using h`):

| Document Snapshot | Batch `lean --json` | Final LSP Diagnostics After `waitForDiagnostics` | `$/lean/plainGoal` Before Tactic (`line 1, char 2`) | `$/lean/plainGoal` After Tactic (`char 10` / `char 15`) |
| :--- | :--- | :--- | :--- | :--- |
| Version 1 (`exact ?_`, [`v1.golden.json`](support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/v1.golden.json)) | Exit `1`; placeholder and unsolved-goals errors with `n`, `h`, and `⊢ n + 0 = 0` | Two errors with identical substantive messages and context | One goal: `n : Nat\nh : n = 0\n⊢ n + 0 = 0` | Same unsolved goal (`n : Nat\nh : n = 0\n⊢ n + 0 = 0`) |
| Unsaved Version 2 (`simpa using h`, [`v2.golden.json`](support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/v2.golden.json)) | Exit `0`; no JSON lines | Empty (`[]`) | Same initial goal (`n : Nat\nh : n = 0\n⊢ n + 0 = 0`) | `goals: []`, `rendered: "no goals"` |

### 2. Cross-Version Goal Ordering Races, Old-Version Waits, and Client Envelope Replay

#### Newer Version Goal Completing Before Older Version Goal (`support/lean-lsp-cross-version-goal-completion/`)

In three runs of `support/lean-lsp-cross-version-goal-completion/probe.py` (SHA-256 `a26730557f916d66338bbffcbdb6ea9fa6fc562917886e5f7bf273ff385e46df`), `support/lean-lsp-cross-version-goal-completion/work/V1.lean` (proving `True` after a `run_tac` gate writing `v1.entered` and awaiting `v1.release`) was opened at version 1 (wait ID 10, `plainGoal` ID 20), then edited in memory to version 2 (`support/lean-lsp-cross-version-goal-completion/work/V2.lean`, writing `v2.entered` and leaving `⊢ False` at `exact ?_`, with wait ID 11 and `plainGoal` ID 21 supplying an extra ignored `textDocument.version: 1` field):

| Run & Transcript Digest | V2 Marker (`ms`) | V2 Wait Reply ID 11 (`ms`) | V2 Goal Reply ID 21 (`⊢ False`, `ms`) | V1 Gate Release (`ms`) | V1 Wait Reply ID 10 (`ms`) | V1 Goal Reply ID 20 (`⊢ True`, `ms`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| Run 1 ([`transcript-run1.json`](support/lean-lsp-cross-version-goal-completion/transcript-run1.json), `12514acc...`) | `4763.7` | `4960.4` | `4960.8` | `4961.1` | `4968.6` | `4968.8` |
| Run 2 ([`transcript-run2.json`](support/lean-lsp-cross-version-goal-completion/transcript-run2.json), `568711ed...`) | `1918.8` | `2108.4` | `2108.8` | `2109.0` | `2122.4` | `2122.8` |
| Run 3 ([`transcript-run3.json`](support/lean-lsp-cross-version-goal-completion/transcript-run3.json), `00561c96...`) | `1918.8` | `2113.1` | `2113.5` | `2113.7` | `2115.9` | `2116.2` |

#### Old-Version `waitForDiagnostics` Preceding Newer Goal (`support/lean-lsp-old-version-wait-race/`)

In `support/lean-lsp-old-version-wait-race/replay.py` (`support/lean-lsp-old-version-wait-race/transcript.json`, `Generated.lean`, `batch-v1.lean`, `batch-v2.lean`), after version 1 (`exact ?_`, goal `n : Nat ⊢ n = n`) and version 2 (`rfl`, `no goals`) both completed, sending `waitForDiagnostics` naming `version: 1` (request ID 13) succeeded immediately (`{}`) because `p.version ≤ doc.meta.version`, and the following unversioned `plainGoal` (ID 23) returned version 2's `no goals`.

#### Offline Client Envelope Replay (`support/lean-goal-envelope-replay/`)

Binding each request at submission time to `(process incarnation, URI, document version, source SHA-256, position)` in `support/lean-goal-envelope-replay/replay.py` (SHA-256 `c170f5444284cfcbd81177812d530e598e5dcd47c3da278d17f2b5bd20a91d41`) over `support/lean-goal-envelope-replay/scenarios.json` (`5367ddd76c8183421c34dae497a645ac0fd90c8abaf0b58ce94fed371be23ea6`) and `support/lean-goal-envelope-replay/expected.json` (`92ef8557ac393a9089f786dfd98e0cf66a07fe76c6c1adbb5e6cba4f436f1d46`) produced identical decisions across all three retained transcripts:

| Scenario | Reply Classifications | Final Latest Result | Evidence Role |
| :--- | :--- | :--- | :--- |
| Recorded V2 reply, then late V1 reply | `current_live`, `stale_snapshot` | `⊢ False` | Retained receive order; modeled client fence |
| V1 request explicitly marked historical | `current_live`, `historical_only` | `⊢ False` | Synthetic historical-caller intent on retained payloads |
| Old reply arrives first, after V2 edit | `stale_snapshot`, `current_live` | `⊢ False` | Counterfactual receive order |
| Old reply arrives before V2 edit | `current_live`, `current_live` | `⊢ False` | Counterfactual timing; V1 acceptance superseded on V2 edit |
| Restart to incarnation B, reusing URI/version/source/ID 20 | `expired_incarnation` | `none` | Synthetic process-incarnation collision control |
| Source bytes change while version remains 1 | `stale_snapshot` | `none` | Synthetic source-hash mutation control |
| Goal cursor position changes with same source/version | `stale_snapshot` | `none` | Synthetic position mutation control |
| Document URI changes with same source/version/position | `stale_snapshot` | `none` | Synthetic URI mutation control |

### 3. Open Buffer Surviving External Overwrite, Path Rename, and Deletion (`support/lean-lsp-open-buffer-path-disappearance/`)

Across three runs of `support/lean-lsp-open-buffer-path-disappearance/probe.py` (SHA-256 `1ce4753af627d2eb240d1f90c9575951c1340190b42ca102edbe7879a5dcc64a`) using source A (`support/lean-lsp-open-buffer-path-disappearance/work/Batch-1.lean`, SHA-256 `30089ee2...`, target `1 = 1`), source B (`support/lean-lsp-open-buffer-path-disappearance/work/Batch-2.lean`, SHA-256 `ca471676...`, target `2 = 2`), and source C (`support/lean-lsp-open-buffer-path-disappearance/work/Batch-3.lean`, SHA-256 `c97e36df...`, target `3 = 3`):

| Step | On-Disk Path State | Open URI and Version | `$/lean/plainGoal` After `waitForDiagnostics` |
| :--- | :--- | :--- | :--- |
| 1. Open A | `Open.lean` = A | `Open.lean`, V1 = A | `⊢ 1 = 1` |
| 2. Unsaved edit B | `Open.lean` = A | `Open.lean`, V2 = B | `⊢ 2 = 2` |
| 3. External overwrite C, no watched event | `Open.lean` = C | `Open.lean`, V2 = B | `⊢ 2 = 2` |
| 4. Send watched changed event | `Open.lean` = C | `Open.lean`, V2 = B | `⊢ 2 = 2` |
| 5. Physically save B, send `didSave` | `Open.lean` = B | `Open.lean`, V2 = B | `⊢ 2 = 2` |
| 6. Rename to `Renamed.lean`, send delete/create events | `Open.lean` absent; `Renamed.lean` = B | **old** `Open.lean`, V2 = B | `⊢ 2 = 2` |
| 7. Close old URI (`-32801` on closed query), open `Renamed.lean` | `Renamed.lean` = B | `Renamed.lean`, new V1 = B | `⊢ 2 = 2` |
| 8. Delete `Renamed.lean`, send watched delete event | `Renamed.lean` absent | `Renamed.lean`, V1 = B | `⊢ 2 = 2` |
| 9. Close (`-32801` on closed query), recreate C on disk, reopen | `Renamed.lean` = C | `Renamed.lean`, new V2 = C | `⊢ 3 = 3` |

### 4. Incremental Diagnostic Publication (`v4.30.0-rc2` vs. `v4.34.1`) and Multi-Version Source Review

#### Source Delta Between `v4.30.0-rc2` and `v4.34.1` (`support/lean-incremental-diagnostics-430rc2-to-4341-source-delta/`)

| Source File / Commit | `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) | `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Behavioral Delta |
| :--- | :--- | :--- | :--- |
| `src/Lean/Data/Lsp/Capabilities.lean` | `886e54140b4571bfc1e6b28fcb75ad196df0199e` | `12eec11b4270702ec13990fce25913b7f1c67ba4` | Adds `lean.incrementalDiagnosticSupport? : Option Bool := none` (lines 66–98). |
| `src/Lean/Data/Lsp/Diagnostics.lean` | `d15c1ce80d3699be7a5d92ebf6cea6725c3a4b34` | `9353793f7316dca0ba36b16a9fd6cec46e487441` | Adds optional `isIncremental? : Option Bool` on `PublishDiagnosticsParams` (lines 159–171). |
| `src/Lean/Server/FileWorker.lean` | `c803034ed8810f13a5ef38a603a21e610efca2bc` | `cf8058ac800a67394e26aa4752539ddd979877c1` | Passes resolved `incrementalDiagnosticSupport` into `EditableDocumentCore.publishDiagnostics` (lines 207–213). |
| `src/Lean/Server/FileWorker/Utils.lean` | `824a52e3de861ffbdde9597078d7946cb0306436` | `e46f44a1599800a6bd6bedb8db9729235d37f49e` | `EditableDocumentCore.publishDiagnostics` (lines 120–160) computes `useIncremental := incrementalDiagnosticSupport && ds.isIncremental`, emitting `some false` on initial/sticky replacement and `some true` on subsequent append slices (`publishedDiagsAmount`), or `none` when capability is absent/false. |

#### Six-Case Serialized LSP Runtime A/B (`support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/`)

Running `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/probe.py` across `v4.30.0-rc2` (`b48bc5ab...`) and `v4.34.1` (`1b370cfc...`) over `Open.lean` (`#check unknownA\n#check unknownB`, SHA-256 `d42fbf3d79611aa442bb233680e4f20af6848dc8f1f0c7be3c3dd4df22b5dcc7`) and `Edited.lean` (`#check Nat.zero\n#check unknownB`, SHA-256 `9caea97a94d2d9d37a3cb507278414674d173507a0ebf9db9e3c5024dc3ebfeb`) produced:

| Server / `incrementalDiagnosticSupport` Capability | Ordered `publishDiagnostics` Counts (`version:count`) | `isIncremental` Field on Substantive Publications | Peak Sampled Server-Group RSS |
| :--- | :--- | :--- | ---: |
| `v4.30.0-rc2` / `absent` | `1:0, 1:0, 1:1, 1:2, 2:2, 2:0` | absent | `293,328 KiB` |
| `v4.30.0-rc2` / `false` | `1:0, 1:2, 2:2, 2:0` | absent | `226,688 KiB` |
| `v4.30.0-rc2` / `true` | `1:0, 1:2, 2:2, 2:0` | absent | `227,248 KiB` |
| `v4.34.1` / `absent` | `1:0, 1:0, 1:1, 1:2, 2:2, 2:0` | absent | `319,024 KiB` |
| `v4.34.1` / `false` | `1:0, 1:2, 2:2, 2:0` | absent | `248,208 KiB` |
| `v4.34.1` / `true` | `1:0, 1:2, 2:2, 2:0` | `false`, `false` | `248,320 KiB` |

#### Bounded Source Review of Six Prior `v4.29.0`/`v4.30.0-rc2` Comparisons Against `v4.34.1` (`support/lean-429-430-comparison-to-4341-source-review/`)

| Prior Comparison Subject (`support/lean-429-430-comparison-to-4341-source-review/matrix.json`) | Prior Observation Retained at `v4.29.0` / `v4.30.0-rc2` | `v4.34.1` Source Review Classification |
| :--- | :--- | :--- |
| Clean/prepared and batch/live equivalence at cached Lean `v4.29.0` and `v4.30.0-rc2` pins | Clean/prepared and batch/live agreement in a small two-file fixture at both versions. | Historical evidence at those pins; `v4.34.1` runtime equivalence is covered in the companion Lake build package. |
| Transitive import, option, macro, plugin, and RPC lifecycle matrix | Already-open worker retained old transitive import (`7`), `pp.universes=false`, and `probetac` macro across both versions until reopened (`9`, `true`, `⊢ True`). | Historical evidence at those pins; `v4.34.1` runtime execution not run in this package. |
| Lean `v4.29.0` vs. `v4.30.0-rc2` Unicode LSP encoding-offer boundary | Identical UTF-16 diagnostic ranges (`16–27`), incremental edits, and wait responses across both pins; one advertised RPC capability field differed. | Historical evidence at those pins; `v4.34.1` runtime encoding replay not run in this package. |
| Lean compilation determinism and version diff | Byte-identical repeated clean and fetched-cache builds per version; version-specific advertised RPC capability field. | Historical evidence; `v4.34.1` batch determinism is covered in the companion Lake build package. |
| Imported-generation refresh behavior across Lean `v4.29.0` and `v4.30.0-rc2` | Identical stale-resident vs. fresh-new/reopened worker contrast in direct `lean --server` at both pins. | Historical evidence at those pins; `v4.34.1` source retains per-URI worker setup. |
| Lean goal replies arriving after a newer version has completed | Three `v4.30.0-rc2` runs where V2 wait and `⊢ False` goal completed before gated V1 wait and `⊢ True` goal. | Rechecked in `v4.34.1` source (`Extra.lean`, `RequestHandling.lean`, `Basic.lean`): `waitForDiagnostics` still checks `p.version ≤ doc.meta.version` and `PlainGoalParams` still uses unversioned `TextDocumentIdentifier`. |

## Boundaries

- **Unversioned goal responses (`known not to apply` as a snapshot lock)**: Neither `$/lean/plainGoal` nor `waitForDiagnostics(version=v)` locks the document to version `v`; `waitForDiagnostics` is a lower-bound barrier (`p.version ≤ doc.meta.version`), and `PlainGoalParams` ignores any extra `textDocument.version` JSON field.
- **Internal computation timestamp of late replies (`unknown`)**: The cross-version goal completion transcript proves client-visible arrival order and that V2's tactic, wait, and goal completed before V1's gate release and V1's reply arrival, but when Lean internally computed V1's goal object is unknown without server instrumentation.
- **Runtime `isIncremental: true` append branch (`not examined` at runtime)**: While `v4.34.1` source implements `isIncremental: true` append notifications in `EditableDocumentCore.publishDiagnostics`, the two-line `#check` fixture emitted `isIncremental: false, false` full replacements; triggering `isIncremental: true` at runtime requires a multi-snapshot streaming fixture.
- **Goal state is not whole-file verification**: Returning `no goals` or a local goal (`⊢ False`) at one cursor position does not establish whole-file elaboration success, absence of `sorry`/axioms, or Rust-to-Lean correspondence.

## Evidence

### Staged Support Artifacts and Verification Scripts

- **Language Server and Tactic-State Source Analysis (`support/lean-server-tactic-state/`)**:
  - `support/lean-server-tactic-state/FINDINGS.md`, `support/lean-server-tactic-state/BOUNDARIES.md`, `support/lean-server-tactic-state/EVIDENCE.md`, `support/lean-server-tactic-state/REVALIDATION.md`
- **Tactic-State Protocol Lifecycle (`support/lean-tactic-state-protocol-transcript/`)**:
  - `support/lean-tactic-state-protocol-transcript/SUPPORT.md`
  - `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/Generated.lean`
  - `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/probe.py` (SHA-256 `c680ac1a59e9c6e62fbc9378138007c70f986c291cf0a6e13ee8f343cc471b3e`)
  - `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/transcript.json` (SHA-256 `af2c3500fde8e86baa8bf93599f6ec3bd95787584f5c48359c47a0fc32c04a41`), `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/transcript-first.json`, `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/transcript-second.json`
  - `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/v1.golden.json`, `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/v2.golden.json`
  - `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/LSP_2026-09-27-18-38-07-2282-0400.log`, `support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/server-logs/LSP_2026-09-27-18-38-19-9066-0400.log`
- **Cross-Version Goal Completion Ordering Race (`support/lean-lsp-cross-version-goal-completion/`)**:
  - `support/lean-lsp-cross-version-goal-completion/probe.py` (SHA-256 `a26730557f916d66338bbffcbdb6ea9fa6fc562917886e5f7bf273ff385e46df`), `support/lean-lsp-cross-version-goal-completion/check.py`
  - `support/lean-lsp-cross-version-goal-completion/transcript-run1.json` (`12514acc62e577ad18cc446a32a28c23ba3fe1be070f279a22649c31f27c27c0`), `support/lean-lsp-cross-version-goal-completion/transcript-run2.json` (`568711ed5a7d758660dccb72a63ef3d6f0d242e286cd44fa8aaab72c8abff25e`), `support/lean-lsp-cross-version-goal-completion/transcript-run3.json` (`00561c961a49f9544ae4b5af181ce84335968582332df88bba68732b5c6ac8f8`)
  - `support/lean-lsp-cross-version-goal-completion/work/V1.lean`, `support/lean-lsp-cross-version-goal-completion/work/V2.lean`
- **Old-Version Diagnostics Wait Race (`support/lean-lsp-old-version-wait-race/`)**:
  - `support/lean-lsp-old-version-wait-race/replay.py`, `support/lean-lsp-old-version-wait-race/transcript.json`, `support/lean-lsp-old-version-wait-race/Generated.lean`, `support/lean-lsp-old-version-wait-race/batch-v1.lean`, `support/lean-lsp-old-version-wait-race/batch-v2.lean`
- **Offline Client Envelope Replay (`support/lean-goal-envelope-replay/`)**:
  - `support/lean-goal-envelope-replay/replay.py` (SHA-256 `c170f5444284cfcbd81177812d530e598e5dcd47c3da278d17f2b5bd20a91d41`), `support/lean-goal-envelope-replay/check.py`
  - `support/lean-goal-envelope-replay/scenarios.json` (`5367ddd76c8183421c34dae497a645ac0fd90c8abaf0b58ce94fed371be23ea6`), `support/lean-goal-envelope-replay/expected.json` (`92ef8557ac393a9089f786dfd98e0cf66a07fe76c6c1adbb5e6cba4f436f1d46`)
  - `support/lean-goal-envelope-replay/sources/V1.lean` (`17f79c983f479120cd5324330ee4cbf299922b90f55ad11957a2b9d7af3d0ad3`), `support/lean-goal-envelope-replay/sources/V2.lean` (`acf6662f56cbeff6ce95f35affefc9bb03e262079274a814e0d45f4bd8ce70e5`)
  - `support/lean-goal-envelope-replay/transcripts/transcript-run1.json`, `support/lean-goal-envelope-replay/transcripts/transcript-run2.json`, `support/lean-goal-envelope-replay/transcripts/transcript-run3.json`
- **Open Buffer Surviving Rename and Deletion (`support/lean-lsp-open-buffer-path-disappearance/`)**:
  - `support/lean-lsp-open-buffer-path-disappearance/probe.py` (SHA-256 `1ce4753af627d2eb240d1f90c9575951c1340190b42ca102edbe7879a5dcc64a`), `support/lean-lsp-open-buffer-path-disappearance/check.py`
  - `support/lean-lsp-open-buffer-path-disappearance/transcript-run1.json` (`70f46cd23d02f06219e958d146ec5fa64ee5d2696ae8d1654874496f51cd5940`), `support/lean-lsp-open-buffer-path-disappearance/transcript-run2.json` (`62e64813f7a44b5625483a634a138ab1e789aa8a6a76189862e111c30fdbf55f`), `support/lean-lsp-open-buffer-path-disappearance/transcript-run3.json` (`605bf3418174dfc0077cef67566cc0d3934a09044b91a5f1cd52208b20cc19d2`)
  - `support/lean-lsp-open-buffer-path-disappearance/work/Batch-1.lean`, `support/lean-lsp-open-buffer-path-disappearance/work/Batch-2.lean`, `support/lean-lsp-open-buffer-path-disappearance/work/Batch-3.lean`
- **Incremental Diagnostics Source Delta and Runtime A/B (`support/lean-incremental-diagnostics-430rc2-to-4341-source-delta/` and `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/`)**:
  - `support/lean-incremental-diagnostics-430rc2-to-4341-source-delta/check.py`, `support/lean-incremental-diagnostics-430rc2-to-4341-source-delta/fixture/Open.lean` (`d42fbf3d...`), `support/lean-incremental-diagnostics-430rc2-to-4341-source-delta/fixture/Edited.lean` (`9caea97a...`)
  - `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/check.py`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/probe.py`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/results.json`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/cleanup.json`
  - `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/fixture/Open.lean`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/fixture/Edited.lean`
  - Per-case raw directories (`events.jsonl`, `resources.jsonl`, `server.stderr`, `server.stdout.lsp`, `summary.json`) under `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/old-absent/summary.json`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/old-false/summary.json`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/old-true/summary.json`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/new-absent/summary.json`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/new-false/summary.json`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/new-true/summary.json`, and batch records under `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/batch-old-open/record.json`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/batch-old-edited/record.json`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/batch-new-open/record.json`, and `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/raw/batch-new-edited/record.json`.
- **Six-Item Cross-Version Source Review (`support/lean-429-430-comparison-to-4341-source-review/`)**:
  - `support/lean-429-430-comparison-to-4341-source-review/matrix.json`, `support/lean-429-430-comparison-to-4341-source-review/frozen-cohort.csv`, `support/lean-429-430-comparison-to-4341-source-review/version-inventory-ebcdcad-581.csv`, `support/lean-429-430-comparison-to-4341-source-review/baseline-report-paths.txt`, `support/lean-429-430-comparison-to-4341-source-review/check_matrix.py`.

## Revalidation

1. **Offline Transcript and Envelope Verification**: Run the offline checkers directly from the package root without launching Lean:
   ```console
   python3 -B support/lean-lsp-cross-version-goal-completion/check.py
   python3 -B support/lean-goal-envelope-replay/check.py
   python3 -B support/lean-lsp-open-buffer-path-disappearance/check.py
   python3 -B support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/check.py
   ```
2. **Source-Delta Check Against a Lean 4 Checkout**:
   ```console
   python3 support/lean-incremental-diagnostics-430rc2-to-4341-source-delta/check.py --source-root /path/to/lean4
   ```
3. **Live LSP Probe Re-Execution**: Copy the relevant support folder to a disposable directory, set `LEAN_BIN` to the target `lean` binary, and run `probe.py` or `replay.py` (`support/lean-tactic-state-protocol-transcript/lean-query-lifecycle/probe.py`, `support/lean-lsp-cross-version-goal-completion/probe.py`, `support/lean-lsp-old-version-wait-race/replay.py`, `support/lean-lsp-open-buffer-path-disappearance/probe.py`, `support/lean-incremental-diagnostics-lsp-runtime-ab-430rc2-to-4341/probe.py`).
