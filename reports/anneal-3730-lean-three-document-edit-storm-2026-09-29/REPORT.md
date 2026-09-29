# Direct Lean edit burst with slow document and concurrent batch check

## Result

One pinned Lean 4.30.0-rc2 watchdog held a slow document at a `run_tac` file gate while a second open document received five full-text `didChange` notifications with versions **2, 4, 4, 3, 5**. A fresh `lean --json` batch checker was actively inside a separate timed `run_cmd` during the burst. The fast document's final version-5 diagnostics wait completed 253 ms after the burst, and its goal request completed 274 ms after the burst with `⊢ 5 = 5`. The batch exited 0; releasing the slow gate let its wait complete. The server exited 0.

This is a bounded I111 responsiveness and I112 delivered-event ordering cell. It demonstrates that one fast file reached its latest goal in this run while a different file was blocked and a batch process was active. It does **not** measure a production queue policy, many agents, a long edit storm, or absence of starvation under arbitrary load. The skipped, duplicate and late version numbers were delivered on one ordered stdio transport; the result establishes the final v5 observation only. It does not establish what Lean did with each intermediate version, nor dropped watcher/MCP events or reconnect reconciliation.

## Procedure and evidence

The fixture has two open server documents, `Slow.lean` and `FastA.lean`, plus `Batch.lean` for a fresh checker. The slow and batch gate markers establish active elaboration overlap. The batch gate held for 500 ms, while the fast final wait and goal completed in 253 ms and 274 ms after the burst. The version-5 `publishDiagnostics` notification arrived 243 ms after the burst and before the wait response. A later empty version-5 notification also appeared during shutdown; it is preserved without treating the last notification as a success oracle.

The full client/server LSP frames, monotonic event times, source hashes, batch output, gate order and process exits are in `support/transcript.json`; exact source and marker files are in `support/work`. One server and one batch process ran at a time. The recorded preflight showed at least 35% free memory, and sampled summed process-tree RSS peaked at 3,566,256 KiB under the 4,600,000 KiB abort threshold. Summed RSS can double-count shared pages and miss between-sample peaks. An initial three-open-document calibration exceeded this threshold and was stopped by the harness; this retained run uses two open documents.

The earlier protocol-race report tested one gated document and one edit; the multiclient broker report tested four sequential edits and a modeled dropped event. This package adds an actual two-document direct LSP burst during active fresh batch work. An Anneal scheduler, editor watcher, MCP transport and multi-agent query fairness remain outside the fixture.

## Recheck

Run `python3 support/check.py` for the saved offline check. `python3 support/probe.py` re-executes on the pinned local Lean binary and replaces only this package's `support/work` and transcript. Timing is a single observed schedule, not a latency distribution.
