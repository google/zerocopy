# Guarded multi-minute Lean server worker ramp and RPC-reference soak

## Summary

On one 8 GiB macOS host, direct Lean 4.30.0-rc2 handled a sequential one/two/four-file-worker ramp plus a separate conflicting-import workspace over **188.97 seconds**. All four cells completed: 69 versioned edit/goal checks and eight initial goal checks kept the intended file-specific targets. Each cell closed/reopened its files once, invalidated its old RPC session, and returned current rich goals after reconnect. An interactive-goal info reference worked before release and failed with `-32602` after release; old sessions across reopen or watchdog restart failed with `-32900`. The four-worker cell peaked at 1,864,056,832 bytes sampled summed process-tree RSS, below the 3,355,443,200-byte guard. This is a small-import, three-minute component soak, not a long-term leak, Mathlib, or Anneal capacity result.

## Applicability

The subject is the executable in `REPORT.json`, launched as direct `lean --server` with `LEAN_NUM_THREADS=1`. Two privately compiled tiny modules have the same import name `Dep` but define `selected` as 11 in A and 22 in B. A's 1/2/4 worker cells ran **one watchdog at a time**, with separate watchdog restarts between cells; B's final one-worker cell used its own import path. Each file evaluates `selected`, checks the import by `rfl`, and exposes an intentionally open proof goal with a file-specific target. The run did not invoke Lake, Mathlib, native plugins, an MCP server, an Anneal adapter, or a Rust annotation.

The host reported 8,589,934,592 bytes physical RAM, 51% free at preflight, APFS with 53,524,456 KiB reported available, and 682.38 MiB swap used at both endpoints. The hard guards were 210 seconds from script start, 30 MiB allocated fixture disk, six tree processes, 3,355,443,200 bytes summed tree RSS, and 30% host free. A per-server monitor sampled these every half-second and would kill that process group on violation. The four-worker cell required an additional forecast below 80% of the RSS cap, at least 40% free host memory, and at least 85 seconds remaining. A skipped cell would be retained explicitly in the transcript; none was skipped in the completed run.

## Findings

### Worker ramp, edit correctness, and cleanup

| Cell | File workers + watchdog at stable sample | Edit rounds / checks | Stable summed RSS | End summed RSS | Stable / end summed `phys_footprint` | Cell elapsed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| A-1 | 2 | 9 / 9 | 465,879,040 B | 694,370,304 B | 123,118,208 / 350,135,680 B | 48.01 s |
| A-2 | 3 | 9 / 18 | 871,940,096 B | 824,852,480 B | 222,706,880 / 433,209,152 B | 50.15 s |
| A-4 | 5 | 9 / 36 | 1,694,547,968 B | 1,864,056,832 B | 431,992,704 / 598,831,296 B | 54.59 s |
| B-1 | 2 | 6 / 6 | 465,682,432 B | 437,420,032 B | 122,872,128 / 349,594,752 B | 32.34 s |

The two-worker stable RSS and one-worker stable RSS gave a four-worker linear forecast of 1,684,062,208 B; the host reported 47% free and 110 seconds remaining at admission. This forecast is a guard heuristic, not a scaling model. The largest sampled tree count was five processes; minimum sampled host free percentage was 42%. At finish, ten local files occupied 49,152 allocated bytes, and the temp-name scan found no temporary file. All four watchdogs exited 0 and their recorded process trees were empty after shutdown. The final swap-used snapshot was unchanged. **Basis: execution**, the guarded event stream.

Every open and edit check found its own target `n = 11 + file index` in A or `n = 22` in B, the appropriate `#eval selected`, and no failed import `rfl`. After round 5, each cell closed/reopened the files at document version 1, obtained a new RPC session, and rejected the previous session with `-32900 Outdated RPC session`. A-2 and A-4 also tried the prior **watchdog's** session on a reused URI before reconnecting; both rejected it with `-32900`. The B watchdog opened a file located in A and evaluated `selected` as 22, with A's `selected = 11` check failing. This is a same-name import context negative control: file URI did not override the watchdog's `LEAN_PATH`. **Basis: execution.**

### Rich RPC reference scope and bidirectional request IDs

In each cell, `Lean.Widget.getInteractiveGoals` returned an `InfoWithCtx` reference (wire value `{"p":"0"}` initially). `Lean.Widget.InteractiveDiagnostics.infoToInteractive` dereferenced it to a `Nat` popup. The reference remained callable after three in-place edits under that session. Sending `$/lean/rpc/release` then made dereference fail with `-32602` and `RPC reference '0' is not valid`. After close/reopen, a new session returned a usable reference, sometimes with the same wire value; the old session was rejected. These selected object and session observations support an incarnation-scoped client handle rule, not a claim that every rich object has the same lifetime or that release reclaimed a measured amount of memory.

An initial exploratory run aborted at 54.35 seconds because the *harness* matched an incoming `workspace/inlayHint/refresh` server request with numeric ID 23 to a pending client request ID 23. The corrected harness responds to that server request and accepts only messages **without a method** as replies to its client IDs. `support/pilot-id-collision.json` preserves the failed trace and clean process cleanup; it is a protocol-client negative control, not a failed Lean worker/soak observation. The corrected run's full transcript contains the server-initiated refresh messages and their acknowledgments. **Basis: execution for the wire trace; derived for the client routing rule.**

### Timing and memory interpretation

Across the completed run, 86 `waitForDiagnostics` requests had median 212.35 ms, 77 `plainGoal` requests median 0.8 ms, and 29 rich RPC calls median 0.6 ms. These are warm tiny-file request times in a paced script, not end-to-end Rust extraction or a throughput benchmark. The cells spent five seconds between edit rounds to observe process retention; the script made 33 independent five-second monitor records in addition to per-operation checks.

Summed `ps` RSS counts resident mappings in each process and can double-count shared pages. `phys_footprint` was queried sequentially per PID at only stable and end points; sums are neither atomic unique tree memory nor Linux PSS. PSS was unavailable on this macOS host. RSS rose in A-1 and A-4, but fell between A-2's stable and end samples and in B-1. With only three minutes, several restarts, paced edits, and no heap attribution, this cannot classify a leak or steady-state retention law. Half-second monitoring and per-operation samples can still miss shorter peaks. **Basis: execution** for values; **derived** for metric limitations.

## Boundaries

| Issue scope | New bounded result | Residual |
| --- | --- | --- |
| I041–I043 | Versioned current goals through 69 edits, reopen resets, rich query at one tactic position, and explicit server/client incarnation handling. | An exact-version query fence with causally delayed old responses, readiness phases, and nested/macro tactic-position semantics. |
| I044–I045 | Dereference across edit, explicit release failure, old-session rejection after reopen/restart, and bidirectional request-ID collision in a client pilot. | Expiry timer, broader reference classes and imported-environment changes, delayed *successful* old reply across internal worker replacement and same-transport client-ID reuse. |
| I047 | Latest-goal behavior under paced edits and reset versions. | Retained historical generation query, storage/expiry policy, and old-import reconstruction; this run is not a historical-query service. |
| I116–I118 | Three-minute paced edit/open/close/restart soak, RSS/`phys_footprint` samples, and direct Lean request latencies. | Hours-long leak/retention evidence, unique process-tree physical memory or Linux PSS, and whole-pipeline latency decomposition at representative imports. |
| I153–I154 | One watchdog with 1/2/4 tiny file workers, separate B watchdog, cross-URI wrong-import sentinel, and cleanup. | Matched MCP/broker/scratch-pool topologies, larger workers/imports, plugin contamination, parallel tests, and per-suite fixture sharing. |

No source/model/artifact attestation is returned by `plainGoal`; the source/OLean hashes and session labels in this package are harness-side evidence. The proof holes deliberately leave diagnostics, so a returned goal is not a checked theorem or Rust-level verification. The four-worker ramp is **not** four Lake consumers and does not justify Mathlib-scale inference.

## Evidence

Standard-library harness `support/probe.py` SHA-256 `64ea6982653f41e0be7050d41f7135e28f76f2e2712f5f2f580086bff351029d`; offline checker `support/check.py` SHA-256 `d790f7d2b868c35d07698915c4971ff6cdf4e1c390979ba0b05dc6b3631192e5`; complete corrected `support/transcript.json` SHA-256 `fef3401ba4ebf5a5a684d36e8c0d8a595a9945bd28471bc2cd4638ec96d8caaa`; exploratory `support/pilot-id-collision.json` SHA-256 `e1c9f08bdd6b4d63e07017b074ecf90168b97271b0faea5407c3ee7c0da32a3e`. The transcript tokenizes local work and Lean binary paths while preserving protocol bodies, process rows, timings, preflight/admission/guard decisions, source/OLean hashes, and cleanup. `support/work/` retains the small source and compiled import artifacts.

`python3 support/check.py` passed: `OK: 1679 events; 4 cells; multi-minute sentinel/RPC/resource/cleanup checks`. It verifies hashes, every goal sentinel, the 1/2/4 admission record, release/reopen/restart errors, wrong-import control, hard limits, and zero process trees after clean shutdown. It separately verifies that the archived pilot failed due to the named client request-ID collision and cleaned its processes. The [R11 short soak](../anneal-3730-lean-server-soak-context-rpc-2026-09-29/REPORT.md) and [R05 resource economics](../anneal-3730-resource-soak-contamination-2026-09-29/REPORT.md) are adjacent, narrower local observations; this report extends duration and combines the worker ramp with RPC references.

## Revalidation

First run `python3 support/check.py` against the archived evidence. To repeat on the same pin, run `LEAN_BIN=/absolute/path/to/lean python3 support/probe.py` from this package. It replaces its own `support/work` and `support/transcript.json` but retains the pilot file. Honor the preflight and live kill guards; a skipped cell is a measured non-result, not permission to raise caps. For another Lean build or host, record new binary/host identities and analyze protocol differences separately. Longer leak or realistic import-capacity claims need a new sustained, attributed, platform-appropriate experiment.
