# Lean server concurrency, memory, reuse, and protocol limits at v4.30.0-rc2

## Summary

Four concurrent direct `lean --server` processes, each opening one tiny file that imports the same prebuilt local `Dep.olean`, remained responsive through 10 edit rounds and eight idle samples. Summed process-tree RSS peaked at 801,865,728 bytes; after the edit rounds it settled near 639 MB. The processes were stopped cleanly and RSS returned to zero. This quantifies one small direct-server fixture and demonstrates independent concurrent sessions; it does not set a safe Anneal concurrency limit.

## Applicability

Lean is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), on macOS arm64. Four jobs had separate `Proof.lean` documents and JSON-RPC sessions and shared a frozen `Dep.olean`. The monitor used macOS `proc_pidinfo` resident-size observations for each Lean process and its descendants. The host had 8 GiB physical memory; the sample did not load Mathlib or plugins.

## Findings

### Memory observations

One loaded server used about 67.7 MB in the first sample. Four loaded servers summed to 484,147,200 bytes. After the first edit round the sum was 709,705,728 bytes; after five rounds the observed peak was 801,865,728 bytes; after ten rounds and all idle samples the total was about 639,385,600 bytes. At shutdown the measured aggregate was zero. The harness had a 1.5 GB aggregate RSS guard and a free-memory floor; neither fired. System-reported free memory reached 30% during a separate subsequent Lake workspace rebuild, not during the direct-server sample; the server transcript's lowest recorded value was 38%.

Summing RSS can double-count shared pages and is not macOS `phys_footprint`; it is a consistent process-resident measure for this run. Transcript, fixture files, and monitor source are preserved in `server-memory/`.

Basis: execution.

### Concurrency, cancellation, and isolation

Prior two-server protocol probes show that each process owns separate document versions, diagnostics, and goal state while importing the same immutable dependency OLean. Versioned `didOpen`/diagnostics/goal requests work after elaboration, and cancellation returns LSP error `-32800`; restarting reconstructs state from file bytes and tool configuration. The preserved `lsp-two-events.json` captures the concurrent sessions. A canceled, stale, or crashed request must not be reported as a completed proof result.

Basis: execution + protocol/source reports already in this corpus.

### Server reuse is conditional on all elaboration inputs

A long-lived process may reuse state only while document version, imported artifacts, search path, options, plugins, and toolchain context still match. Source or import edits require a completed new elaboration before querying. A server restart is a straightforward invalidation boundary because the document and import environment must be reconstructed. These are protocol/setup contracts; this fixture does not measure cache hit rates for repeated workspaces.

Basis: source + execution + derived.

## Boundaries

This is a direct Lean server on four tiny one-file workspaces sharing one small `.olean`. It excludes `lake serve`, Mathlib-scale imports, native plugins, hundreds of open files, real Anneal job overlap, cancellation storms, and sustained hours-long memory leaks. Process RSS is not unique physical footprint. There is no defensible production cap from this result alone. The current Zerocopy checkout has no MCP bridge implementation; MCP transport concurrency was therefore not exercised. LSP evidence is still meaningful independently of MCP.

## Evidence

- Lean source: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
- Direct server transcript: `server-memory/transcript.json`; harness: `server-memory.py`; process monitor source: `proc-tree.c`.
- Lean server source: `src/Lean/Server/Watchdog.lean`, `src/Lean/Server/Requests.lean`, `src/Lean/Server/RequestCancellation.lean`, and `src/Lean/Server/FileWorker/SetupFile.lean` at `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`; these identify the request, cancellation, elaboration, and setup paths discussed here.
- Existing protocol evidence: `lsp-two-events.json` and the corpus package `lean-server-concurrency-experiment-v4-30-0-rc2`.

## Revalidation

Repeat at the exact Lean build with frozen dependency artifacts and 1/2/4/8 servers; preserve JSON-RPC transcripts and sample each process tree at load, edits, idle, restart, and shutdown. Compare RSS and unique footprint separately if the host offers a permitted monitor. Increase to real generated projects only after a scratch and memory guard are active; add a production Anneal concurrency ceiling only after measuring Mathlib/plugins and peak active-file count. Test MCP only once an adapter executable and cancellation mapping are identified.
