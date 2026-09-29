# Open Lean buffer survives its disk path's rename and deletion

## Summary

In three direct Lean 4.30.0-rc2 server runs, an open document kept its unsaved version-2 goal `⊢ 2 = 2` while its disk file changed to source C, was overwritten by a save of source B, and was renamed away from its original URI. After the client closed that URI and opened the renamed path, deleting the renamed file still left its open buffer queryable with B's goal. Closing it made goal requests fail with `-32801`; recreating the path with C and reopening returned C's `⊢ 3 = 3` goal. Disk hashes, versioned diagnostics, watched-file notifications, fresh batch controls, and every wire message are retained.

The earlier [save/format/watch loop](../anneal-3730-editor-save-format-watch-loop-2026-09-29/REPORT.md) had already shown a dirty Lean buffer surviving an external disk overwrite, then close/reopen from disk. This report adds **the same open document remaining queryable after its physical path disappears**, first by rename and then by deletion. It is component evidence for #3731 I012's disk/open-buffer ownership question, not an editor or Anneal host contract.

## Applicability

The execution used one direct `lean --server` process per run, one open URI at a time, `LEAN_NUM_THREADS=1`, macOS arm64, and the cached `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` release binary (SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`). No Lake workspace, user imports, plugins, generated Rust proof, actual editor, MCP broker, or background watcher was involved. The client sent explicit LSP watched-file notifications at selected steps; it did not depend on operating-system event delivery. Each server exited 0.

Sources A, B, and C are the same tiny unfinished theorem with target `1 = 1`, `2 = 2`, and `3 = 3`, respectively. Each fails fresh `lean --json` with placeholder and unsolved-goal errors, providing a distinctive goal/diagnostic sentinel without claiming whole-file success. Their exact bytes and hashes are under [`support/work`](support/work). The probe uses full-content `didChange`, a physical disk write before `didSave`, filesystem rename/unlink, and `didClose`/`didOpen`; document versions belong to their respective open incarnations.

## Findings

### The open document remained B while disk ownership changed

| Step | Disk path state | Open URI and version | Goal after a completed wait |
| --- | --- | --- | --- |
| Open A | `Open.lean` = A | `Open.lean`, V1 = A | `⊢ 1 = 1` |
| Unsaved edit B | `Open.lean` = A | `Open.lean`, V2 = B | `⊢ 2 = 2` |
| External overwrite C, no watched event | `Open.lean` = C | `Open.lean`, V2 = B | `⊢ 2 = 2` |
| Send watched changed event | `Open.lean` = C | `Open.lean`, V2 = B | `⊢ 2 = 2` |
| Physically save B, send `didSave` | `Open.lean` = B | `Open.lean`, V2 = B | `⊢ 2 = 2` |
| Rename, send old-delete/new-create events | `Open.lean` absent; `Renamed.lean` = B | **old** `Open.lean`, V2 = B | `⊢ 2 = 2` |
| Close old, open renamed | `Renamed.lean` = B | `Renamed.lean`, new V1 = B | `⊢ 2 = 2` |
| Delete renamed, send watched delete | `Renamed.lean` absent | `Renamed.lean`, V1 = B | `⊢ 2 = 2` |
| Close, recreate C, reopen | `Renamed.lean` = C | `Renamed.lean`, new V2 = C | `⊢ 3 = 3` |

The table's disk states are actual bytes and absence checks, not names inferred from LSP messages. The three source hashes were A `30089ee2…`, B `ca471676…`, C `c97e36df…`. Request pairs use `textDocument/waitForDiagnostics` for the named current version and `$/lean/plainGoal` at the same `(line 1, character 2)` position. All three runs produced the same goal and disk sequence. **Basis: execution** in the full [`run 1`](support/transcript-run1.json), [`run 2`](support/transcript-run2.json), and [`run 3`](support/transcript-run3.json) records, asserted by [`support/check.py`](support/check.py).

For the original URI, version-1 error diagnostics named `⊢ 1 = 1` and version-2 errors named `⊢ 2 = 2`; the later C disk overwrite did not produce a C diagnostic in its open V2 worker. The renamed URI's new version-1 diagnostics named B, and its reopened version-2 diagnostics named C. The notification-only `didChangeWatchedFiles` calls had no response of their own. The following waits and queries bound the observed state after sending them; the transcript does not prove an internal watcher handling point. **Basis: execution**.

### Close transfers the query boundary; the client supplies reopen text

After `didClose` of each URI, a goal request returned `-32801 Cannot process request to closed file`. Fresh batch Lean on the deleted `Renamed.lean` path exited 1 with `no such file or directory`. The probe then created C bytes at that path and sent `didOpen` with exactly C at a new document version 2; the server returned C's goal and C diagnostics, matching a fresh batch control's substantive errors. A separate reopen with B while disk was absent was not attempted. **Basis: execution**.

The physical B save overwrote disk C because the probe explicitly wrote B before sending `didSave`. Lean's goal stayed B and no additional conflict diagnostic was observed in this schedule. This is not evidence that Lean or an editor arbitrates external-write conflicts or chooses when a save is allowed. A product host must retain a buffer/disk identity and resolve such a conflict under its own policy before allowing a write. That last requirement is **derived** from the demonstrated divergence and harness-controlled overwrite; no Anneal conflict handler ran.

## Boundaries

- **Not examined:** a real editor's file-save conflict prompt, autosave, filesystem watcher delivery or coalescing, concurrent clients, another process writing during the save, or rollback after a failed disk write. The probe itself performs the disk mutations and sends LSP notifications.
- **Not established:** that a watched-file notification is processed at a particular internal point. The successful wait and goal establish the post-send response state for this fixture, while the notification has no acknowledgment.
- **Not examined:** generated models, imports, Lake setup, Lean workers that need a missing source path during setup, or an actual Anneal authority host. An open core-Lean buffer surviving its own pathname's disappearance does not establish those cases.
- **Not established:** proof acceptance. A/B/C all deliberately fail batch Lean and publish placeholder/unsolved-goal errors. The goal is local tactic state only.

## Evidence

- [`support/probe.py`](support/probe.py), SHA-256 `1ce4753af627d2eb240d1f90c9575951c1340190b42ca102edbe7879a5dcc64a`, creates only a tiny disposable workspace beside itself. It runs one direct server, three saved batch controls, and two later batch checks with 15-second batch, 12-second request, and 5-second shutdown limits. It checks the pinned binary hash before execution, drains the wire after shutdown, and performs no install or download.
- Complete JSON-RPC, disk state, version and batch records: [`run 1`](support/transcript-run1.json) SHA-256 `70f46cd23d02f06219e958d146ec5fa64ee5d2696ae8d1654874496f51cd5940`; [`run 2`](support/transcript-run2.json) `62e64813f7a44b5625483a634a138ab1e789aa8a6a76189862e111c30fdbf55f`; [`run 3`](support/transcript-run3.json) `605bf3418174dfc0077cef67566cc0d3934a09044b91a5f1cd52208b20cc19d2`. Private absolute work paths are tokenized as `$WORK`; full wire payloads and relative timestamps remain.
- [`support/check.py`](support/check.py) validates the three complete retained sequences offline, including exact source/disk hashes, request ordering, goal and diagnostic targets, closed-file errors, deleted-path batch failure, and clean server exits. It passed on 2026-09-29.
- The [v27 #3730/#3731 audit](../anneal-3730-3731-final-coverage-audit-2026-09-29-v27/REPORT.md) marks I012 partial and identifies the actual editor-host authority contract as the remaining product gate. The [editor shadow report](../anneal-3730-editor-mcp-shadow-authority-v4-30-0-rc2/REPORT.md) and [URI/history report](../anneal-3730-lean-uri-history-import-boundaries-2026-09-29/REPORT.md) supply adjacent bare-Lean cases; this package adds the path-disappearance transition of an already open document.

## Revalidation

Run `python3 -B support/check.py` to validate the retained records without starting Lean. To repeat, set `LEAN_BIN` to the exact pinned binary and run `python3 -B support/probe.py` three times, preserving each resulting `support/transcript.json` as `transcript-run1.json` through `transcript-run3.json`. The probe resets only its own `support/work` files and writes only its `support/transcript.json`. Confirm both path-absence checks occur before the B goals, both closed-file requests return `-32801`, and reopening from recreated C returns C with the matching batch errors. A different result under a changed Lean build needs a new binary identity and bounded replay.
