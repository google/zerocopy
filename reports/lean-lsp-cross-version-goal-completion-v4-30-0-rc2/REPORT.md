# Lean goal replies can arrive after a newer version has completed

## Summary

In three direct Lean 4.30.0-rc2 server runs, one document's version 2 elaborated, completed `waitForDiagnostics(version=2)`, and returned its `⊢ False` goal **before** outstanding version-1 wait and goal requests replied. The older wait then succeeded, and the older goal request returned `⊢ True`. A request sent after both versions completed with `waitForDiagnostics(version=1)` also succeeded. The goal replies matched their submitted queries in these runs, but arrival order cannot identify the latest document. The wait replies only establish that diagnostics for at least the requested version completed. A client that labels the late `⊢ True` goal with its current version-2 state would misattribute it.

The preceding [goal/edit race report](../anneal-3730-lean-protocol-races-v4-30-0-rc2/REPORT.md) established that an old reply could arrive after the client *sent* an edit, while leaving server-side edit processing order unknown. This experiment adds a newer-version tactic marker, completed newer-version wait, and newer-version goal reply before release of the older gated tactic. It still does not establish when Lean internally computed the older replies.

## Applicability

The probe used one direct `lean --server` process, one open URI, one client transport, `LEAN_NUM_THREADS=1`, and bare Lean plus `import Lean` on arm64 macOS. The binary was `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. It used no Lake workspace, user import, plugin, Anneal adapter, or generated Rust proof. The same binary ran the two fresh batch controls. All three server sessions exited cleanly.

Version 1 on disk and in the open buffer proved `True` after a `run_tac` command wrote `v1.entered` and waited for the probe to create `v1.release`. The unsaved version-2 replacement wrote `v2.entered`, then left a `False` goal at `exact ?_`. Exact sources and hashes are in [`support/work/V1.lean`](support/work/V1.lean), [`V2.lean`](support/work/V2.lean), and the transcript `subject` events. The gate and marker are fixture side effects, used only to order the two elaborations.

## Findings

### The current goal completed before the older goal reply

The client opened V1 and sent wait request 10. After the V1 gate marker appeared, it sent V1 `plainGoal` request 20, changed the same URI to V2, and sent wait request 11 for V2. The probe observed V2's own `v2.entered` marker while V1 was still gated. It then received V2 wait response 11 and sent goal request 21. Request 21 supplied an extra `textDocument.version: 1`, yet returned the **current V2** `⊢ False` goal. Only after that reply did the probe release V1. The old wait 10 then returned `{}`, followed by old goal 20 returning `⊢ True`. A later new wait 12 specifying version 1 returned `{}`.

| Run | V2 marker | V2 wait reply | V2 goal reply | V1 release | V1 wait reply | V1 goal reply |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 4763.7 | 4960.4 | 4960.8 | 4961.1 | 4968.6 | 4968.8 |
| 2 | 1918.8 | 2108.4 | 2108.8 | 2109.0 | 2122.4 | 2122.8 |
| 3 | 1918.8 | 2113.1 | 2113.5 | 2113.7 | 2115.9 | 2116.2 |

Times are milliseconds since each probe start, for **ordering only**. A reader thread recorded each complete inbound JSON-RPC frame when read; the main thread recorded sends and file-marker observations with the same monotonic clock. The V2 marker proves that the server executed V2's marked tactic before the old replies were read. The completed V2 wait and goal are explicit LSP barriers showing V2 was queryable before those replies. **Basis: execution**, three full wire records linked under Evidence and checked by [`support/check.py`](support/check.py).

Request 20 was submitted against V1 while its tactic was gated, and its `⊢ True` result is consistent with that query. The causality hazard is accepting its later arrival as a response for V2. The extra version key on request 21 did not constrain `plainGoal` in these runs; Lean's `PlainGoalParams` extends `TextDocumentPositionParams`, whose `textDocument` is an unversioned `TextDocumentIdentifier`. `waitForDiagnostics` explicitly allows a document version greater than or equal to the requested number, and its handler accepts `p.version ≤ doc.meta.version`. These source facts explain why wait 12 succeeds after V2 and why an old-version wait is not a snapshot lock. **Basis: source plus execution**; the exact pinned source locations are under Evidence.

### Batch and diagnostic controls keep local goals separate from file validity

Fresh `lean --json` over V1 exited 0 without diagnostics. V2 exited 1 with placeholder and unsolved-goal errors naming `⊢ False`. The V2 server published those two substantive errors before wait 11 replied. Its `⊢ False` goal was local tactic state in a failing file. The original on-disk `Proof.lean` remained V1 during the server exchange; V2 existed in the unsaved LSP buffer and in the separate batch control file. **Basis: execution**, retained source bytes, batch output, diagnostics notifications, and response order.

For #3731 I041, a client can associate request 20 with its submission-time `(process incarnation, URI, document version, source hash, position, import generation)` and reject it for a latest-version operation once V2 is current. It may retain the V1 result under an explicit historical-result contract. This is a **derived** adapter rule, not an implemented or verified Anneal fence. The [v27 coverage audit](../anneal-3730-3731-final-coverage-audit-2026-09-29-v27/REPORT.md) correctly keeps I041 partial at its product gate; this direct-server result sharpens only the out-of-order reply evidence.

## Boundaries

- **Unknown:** whether old request 20's answer was internally computed before or after Lean processed V2. The transcript establishes client-visible receive order, V2 tactic execution, V2 wait completion, and V2 goal completion before the old replies. It is not server-side instrumentation of request execution.
- **Not established:** every edit schedule or general cancellation behavior. This fixture uses one full-content edit and deliberately sends no explicit cancel. A different schedule could cancel the old request or deliver it sooner.
- **Not examined:** Anneal's exact source/import response envelope, a production client fence, projected Rust/Lean source, generated imports, Lake setup, RPC rich goals, multiple URIs, worker replacement, or complete verification acceptance. I041 remains partial.
- **Not established:** proof validity from a goal. V2's local goal coexists with fresh batch failure and two server errors.

## Evidence

- [`support/probe.py`](support/probe.py), SHA-256 `a26730557f916d66338bbffcbdb6ea9fa6fc562917886e5f7bf273ff385e46df`, builds the two source variants, runs batch controls, drives the direct server with a concurrent wire reader, and bounds marker/request waits. It writes only inside its own `support/` directory. The retained transcript paths and binary path are tokenized; complete payloads, event order, relative times, and process exits remain.
- Full wire and batch records: [`run 1`](support/transcript-run1.json), [`run 2`](support/transcript-run2.json), [`run 3`](support/transcript-run3.json). Their SHA-256 values are `12514acc62e577ad18cc446a32a28c23ba3fe1be070f279a22649c31f27c27c0`, `568711ed5a7d758660dccb72a63ef3d6f0d242e286cd44fa8aaab72c8abff25e`, and `00561c961a49f9544ae4b5af181ce84335968582332df88bba68732b5c6ac8f8`. The 3-run offline checker passed on 2026-09-29.
- Lean source at the identified commit: [`WaitForDiagnosticsParams`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Extra.lean#L37-L48), [`PlainGoalParams`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Extra.lean#L100-L105), [`TextDocumentIdentifier`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Basic.lean#L141-L144), [`TextDocumentPositionParams`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Basic.lean#L312-L315), and [`handleWaitForDiagnostics`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker/RequestHandling.lean#L466-L481). The [earlier race report](../anneal-3730-lean-protocol-races-v4-30-0-rc2/REPORT.md) explains the adjacent control.

## Revalidation

Run `python3 -B support/check.py` to check the retained evidence without starting Lean. For a fresh run, copy the package to a disposable directory, set `LEAN_BIN` to the absolute path of the identified cached binary, and run `python3 -B support/probe.py` three times. After each run, copy `support/transcript.json` to `support/transcript-run1.json`, `support/transcript-run2.json`, or `support/transcript-run3.json` respectively; then run the checker in that copy. The probe compares the binary hash before opening a server. Require the V1 gate before the edit, V2 marker and wait and goal replies before V1 release, then successful old wait and `⊢ True` goal replies. If the newer barrier or old reply changes, inspect the complete wire trace and the pinned server source before generalizing.
