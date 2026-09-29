# Two-project A→B→A routing over real Lean servers

## Summary

A small client-side router switched A→B→A between two private Lean 4.30.0-rc2 servers. A and B each had a same-named `Dep` module but defined `selected` as 11 and 22 respectively. A's unsaved version-2 edit made its `rfl` proof fail. After switching to B and back, routing to the original A process preserved that failing buffer and goal. B's proof remained valid under its own import. Closing A's server and reopening A from disk in a new server restored its saved valid proof; B remained live.

This adds a switch and unsaved-buffer lifecycle to the prior two-server import-collision experiment. It demonstrates a workable **synthetic router fixture**, not an editor extension, Anneal server pool, Lake workspace transition, or implemented project-switch contract.

## Applicability

- Lean binary: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `v4.30.0-rc2`, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997` on arm64 macOS 26.6.2.
- Direct `lean --server` only. Each process had a private current directory and `LEAN_PATH`, with `LEAN_NUM_THREADS=1`. There was no Lake project, Mathlib, plugin, Rust host document, or Anneal adapter.
- Each project contains `Dep.lean`, `Dep.olean`, and `Proof.lean`. Both proof files have the same basename and import name. A evaluates `selected` to 11 and B to 22. Exact source and compiled dependency artifacts are retained under `support/fixture/`; hashes and raw JSON-RPC traffic are in `support/results.json`.
- Preflight reported 41% system-wide free memory and 53,791,662,080 free disk bytes. The probe admitted two tiny loaded servers under a 1.8-GiB summed-RSS stop bound; it did not run a worker-count sweep.

## Findings

### The project route kept A's unsaved worker state when returning

The route was A PID 93693 → B PID 93696 → A PID 93693. In A, the saved version-1 proof `selected = 11 := by rfl` had no remaining goal and only the informational `#eval` diagnostic `11`. The client then sent an unsaved version-2 buffer with `selected = 99` while the on-disk proof stayed at `11`. Lean reported an `rfl` error and goal `⊢ selected = 99`.

B was opened under its own still-live server and reported `#eval` value `22`, no `rfl` error, and no remaining goal. When the router returned to the original A PID without closing its document, A still reported the version-2 error and `⊢ selected = 99`; its disk hash remained that of the saved valid proof. B later remained queryable and valid after A was restarted. The router selected a process by project label rather than by the shared `Proof.lean` basename.

Basis: **execution** in `support/results.json`. The router is a small Python harness with one active-project pointer and one server object per project; it does not negotiate LSP workspace-folder changes.

### Cold A reconstruction read disk, not the unsaved editor buffer

After a graceful shutdown of A PID 93693, a new A server PID 93703 opened the saved `Proof.lean` bytes from disk at version 1. The original valid `selected = 11` theorem again had no goal or `rfl` error. This is the expected result for that explicit disk reopen, and it shows why a real router must either preserve the old worker or replay an authoritative unsaved buffer after restart. The experiment did not implement such replay.

Basis: **execution** for old/new PIDs, hashes, diagnostics, and goals; **derived** for the router's buffer-replay obligation.

### Startup and process observations are small-sample costs

Initialization took 28.82 ms for A, 28.43 ms for B, and 27.02 ms for cold A. Initial diagnostic waits took 247.54 ms for A and 309.73 ms for B; returning to A's already-ready worker took 0.64 ms for the wait. Cold A's wait took 269.51 ms. These are one-run request latencies, not a throughput comparison or a predicted benefit from pooling.

At the two-server point, process-tree sampling found one watchdog and one file worker per project. Summed RSS was 399,261,696 bytes for A and 441,679,872 bytes for B, 840,941,568 bytes total. Summed RSS counts shared pages more than once and is not unique physical memory. Each graceful shutdown exited 0; all PIDs tracked immediately before each shutdown were absent afterward. The file workers had their own process groups, so cleanup was checked by tracked descendant PID rather than only by the watchdog's process-group ID.

Basis: **execution** using macOS `ps` snapshots and the JSON-RPC transcript.

## Relation to prior reports and remaining scope

`lean-server-multi-workspace-isolation-v4-30-0-rc2` established from pinned source that one Lean watchdog has one launch environment. `anneal-3730-server-topology-v4-30-0-rc2` executed the direct-server same-name import collision and the separate-server control. This report adds ordered project switching, unsaved buffer retention on warm return, disk-based reconstruction after A restart, and cleanup while B stays live. It does not need to repeat the one-watchdog collision.

- **#3730 H08 / #3731 I004, I153:** This is a bounded process-routing and reuse fixture. Real editor workspace-folder changes, generated Anneal projects, Lake setup, common dependency trees, many workers, brokers, and policy for server retirement remain untested.
- **#3731 I057:** Rust/embedded Lean coexistence, LSP proxy behavior, completion, hover, cancellation, and ordinary Rust feature routing were not exercised. This report provides no I057 editor-integration result.
- An actual editor may close documents, change URI ownership, or reinitialize servers on project switches. The synthetic router does none of those automatically. It sends only the explicitly recorded LSP open/change/query/shutdown messages.

## Evidence and revalidation

- `support/probe.py` — direct Lean client and minimal project router. It compiles both tiny `Dep.olean` files locally and refuses to overwrite an existing `support/work/` directory.
- `support/results.json` — time-ordered routed JSON-RPC traffic, hashes, goals, diagnostics, PIDs, request latencies, RSS snapshots, and shutdown checks. Local paths are scrubbed.
- `support/fixture/` — exact A/B source and compiled imported artifacts from the retained run.
- `support/check.py` — offline checks for route order, fixture hashes, goal/diagnostic differences, unsaved-versus-disk state, process-tree shape, and cleanup.

Run `python3 support/check.py` from this package directory. For fresh execution, copy the package, set `LEAN_BIN` to the pinned executable, and run `python3 support/probe.py`. It creates `support/work/` and rewrites `support/results.json` in the copy. Compare semantic outcomes and cleanup; PIDs and timings are observations rather than stable replay invariants.
