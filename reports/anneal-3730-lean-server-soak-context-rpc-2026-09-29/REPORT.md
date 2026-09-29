# Bounded direct Lean server edit soak, import context, and RPC reference lifetime

## Summary

One direct Lean 4.30.0-rc2 watchdog at a time handled 12 edits in each of two tiny workspaces, two close/reopens per workspace, a clean server restart, and a client-side timeout followed by another clean restart. All 24 current goals retained their expected file value. Same-named `Dep` imports were **not** selected by URI: opening B's proof under A's server evaluated A's value and failed B's `rfl` check, whereas B's own fresh server evaluated B's value. An interactive-goal info reference could be dereferenced across an in-place edit within a live RPC session; explicitly releasing it made the next dereference fail. Old RPC sessions returned `-32900` after close/reopen and server restart. These are component protocol observations, not Anneal freshness or Mathlib-scale evidence.

## Applicability

The executable is the `lean --server` binary identified in `REPORT.json`, run directly on an 8,589,934,592-byte arm64 macOS host with `LEAN_NUM_THREADS=1`. There is no Lake project, Mathlib import, plugin, MCP server, or Anneal process. A and B each have a separate tiny compiled `Dep.olean` under the **same module name**: `selected := 11` and `selected := 22`. Each proof imports `Dep`, evaluates `selected`, has a definitional equality check, and leaves an intentionally open goal. The server process's `LEAN_PATH` selects the environment; opening a second absolute URI does not change it.

All servers ran sequentially; the only three-process point was one A watchdog with its A and wrong-import B file workers. This is longer in *edit count* than the earlier four-edit server resource trial and targeted RPC lifetime probes, but only about 15 seconds of elapsed work. It cannot classify a long-term leak.

## Findings

### Open/edit/close/restart behavior

A-first and B each completed 12 `didChange`/`waitForDiagnostics`/`plainGoal` rounds, closing and reopening after rounds 4 and 8 with the same URI and document version reset to 1. Every goal preserved `n = 11` for A or `n = 22` for B. Each reopen rejected the prior session with `-32900 Outdated RPC session` and a new session answered. A further full A watchdog shutdown/restart again rejected its old session and returned A's current goal through a new session. After the B timeout control, a fresh B watchdog opened the same URI, returned `n = 22` and answered a new rich RPC goal query. All five watchdogs exited with code 0 and had zero recorded descendant processes at the post-shutdown sample. **Basis: execution**, raw LSP messages, local client incarnation labels, and process rows in `support/transcript.json`.

The wrong-import control opened a B-source file under A's live watchdog. It received `#eval selected` = `11` and a failed `rfl` proving `selected = 22`, while B under its own watchdog received `22` without that `rfl` error. This repeats the earlier two-workspace topology limit inside a longer edit lifecycle. It does not assert that a server can represent independently configured workspaces merely because it accepts both URIs. **Basis: execution.**

### Selected rich RPC reference lifecycle

`Lean.Widget.getInteractiveGoals` returned an `InfoWithCtx` reference for the `Nat` hypothesis type, initially `{"p":"0"}` in each first worker. Calling `Lean.Widget.InteractiveDiagnostics.infoToInteractive` with that reference returned `Nat` popup content. The same reference was callable after three in-place edits under the same live session. Sending `$/lean/rpc/release` for it then made a repeated dereference fail with `-32602` and `RPC reference '0' is not valid` in both A and B. Later workers could also issue the wire value `{"p":"0"}`; that number is not a durable object identity. Close/reopen and watchdog restart made the old session unusable (`-32900`), so a client must treat session/worker incarnation as part of reference scope. **Basis: execution** for these exact calls; **derived** for the client identity rule.

This checks one info-popup reference, not arbitrary `ctx` values, tags, widget code actions, keep-alive expiration, import replacement under a live worker, or memory reclamation after release. The returned goal still contained `exact ?_`; successful RPC calls do not establish a checked proof.

### Client timeout and resource envelope

The client sent `waitForDiagnostics` for nonexistent version 999, applied a local 120 ms deadline, sent `$/cancelRequest`, and waited another five seconds. No final response arrived in that bounded wait. The same watchdog then answered a current `plainGoal` for version 1, shut down with code 0, and a fresh watchdog re-opened the URI and answered both plain and rich goals. This is a **clean client timeout and recovery path**, not proof that every pending Lean request is cancelled or that a response can never arrive later. The unresolved request is explicit in the transcript.

| Measure | Recorded value |
| --- | ---: |
| Stable A-first server + one worker, summed `ps` RSS | 464,584,704 B |
| Stable B server + one worker, summed `ps` RSS | 465,846,272 B |
| Stable sum of separate per-PID `phys_footprint` calls, A / B | 121,954,752 / 123,838,976 B |
| Maximum sampled tree RSS / process count | 695,058,432 B / 3 |
| Minimum sampled host free percentage | 45% |
| Final local allocation / files / temporary names found | 40,960 B / 8 / 0 |
| Elapsed wall time | 15.22 s |

The sampled A/B tree RSS rose from roughly 500 MB after the first edit to about 693–695 MB by the twelfth. This short pattern could reflect retained caches, allocator behavior, or other process effects; it does **not** establish a leak rate. macOS RSS summed across processes double-counts mappings. Separate `phys_footprint` calls are neither atomic nor Linux PSS; Linux PSS and unique tree-wide physical memory were unavailable. Swap usage reported 682.38 MiB before and after, but these snapshots cannot exclude transient paging. The hard guard was 2,202,009,600 B summed tree RSS, four tree processes, 16 MiB allocated local disk, 30% host free, and 160 seconds. No guard fired. The max measured process count was three. Median `waitForDiagnostics` latency was 211.6 ms (34 completed calls); median `plainGoal` and rich RPC call latency was 0.4 ms each (35 and 33 calls), under this tiny warm workload.

## Boundaries

| Issue IDs | Exact contribution here | Still needed |
| --- | --- | --- |
| I041–I043 | Current goals after 24 versioned edits/reopens and exact cursor queries; a client timeout control. | A real exact-version fence across causally delayed replies, parse/import/elaboration readiness phases, and nested/macro tactic positions. |
| I044–I045 | One `InfoWithCtx` dereference across edit, release invalidation, `-32900` on worker/server replacement, and process-incarnation records. | Context-object classes, keep-alive expiry, import replacement, late successful reply across **internal** worker replacement and request-ID reuse on one transport. |
| I046–I047 | Open proof-hole diagnostics and latest current goals; no historical result was requested. | I046's separate direct partial-elaboration matrix already covers its named classes. Historical retention/expiry after rapid edits remains untested here. |
| I048–I050 | Conflicting same-name import negative control under one watchdog. | Exact loaded-artifact attestation; wider transitive/options/macros/plugins and three launch modes are addressed in separate reports, not by this soak. |
| I113–I115 | Tiny local file allocation/process guard and `LEAN_NUM_THREADS=1`. | Full pipeline disk/write bill, realistic safe scaling, and nested Cargo/Aeneas/Lake/Lean parallelism control. |
| I116–I118 | 24 edits, four reopens, multiple clean restarts and sampled RSS/footprint/latency. | Hours/large projects for retention or leak classification, unique physical memory or Linux PSS, and end-to-end stage latency decomposition. |
| I119, I139 | No shared writable prepared tree or real parallel Anneal test. | Sharing strategy and integrated multi-consumer acceptance under load. |
| I153–I154 | One/two open tiny file workers, wrong-import contamination sentinel, scratch URI reuse, and cleanup. | Matched server/MCP/scratch-pool topology at larger counts and per-test/fixture/suite contamination across plugins and phases. |

No Anneal implementation, editor, MCP envelope, actual Rust annotation, batch trust oracle, or Mathlib-sized model was used. One successful small soak cannot demonstrate general concurrency safety, worker GC, or operational capacity. A `plainGoal` lacks an intrinsic source/import hash; the script's hashes and server labels are client-side evidence, not Lean attestation.

## Evidence

Standard-library replay harness `support/probe.py`, SHA-256 `ca1cfede5f46103417671350fc0dcc19fdd6f1746c766e358f60a27d7bfe8ced`; full chronological LSP/RPC/resource `support/transcript.json`, SHA-256 `e0e91b44b61f7f6ef5b1ed684fc2748bb31359660e1a7d48528767b0c0ed65aa`; offline `support/check.py`, SHA-256 `be554c194b64020791c1817b6a8d947a3abbea3b6de18bffccb65227d99cc844`. The transcript tokenizes local fixture and executable paths to `$WORK_URI`, `$WORK`, and `$LEAN_BIN`, retaining message bodies, status, timings, process IDs, guards, and source/OLean hashes. `support/work/` retains the two exact `Dep.lean`/`.olean` pairs and proof-source fixture.

`python3 support/check.py` returned `OK: 646 events; 24 edits, 4 reopens, reference release, wrong import, clean timeout/restart and cleanup`. This is a check of the archived local run, not a safety proof. The earlier [RPC lifetime](../anneal-3730-lean-rpc-lifetimes-v4-30-0-rc2/REPORT.md), [server topology](../anneal-3730-server-topology-v4-30-0-rc2/REPORT.md), and [resource economics](../anneal-3730-resource-economics-2026-09-29/REPORT.md) reports supply the narrower comparisons this run extends. The exact versioned RPC method/source context is Lean's `WidgetRequests.lean` and `InteractiveGoal.lean` at the commit in `REPORT.json`; this package's behavior is from direct execution rather than a source-derived universal guarantee.

## Revalidation

Run `python3 support/check.py` first. To repeat on the pinned local binary, set `LEAN_BIN=/absolute/path/to/lean` and run `python3 support/probe.py` from this package; it replaces only `support/work` and `support/transcript.json`. Preserve the guard and inspect any timeout or RPC error differences rather than assuming exact wire codes on a new Lean pin. Scale imports, duration, and worker count only under a separate resource budget and acceptance oracle; the tiny fixture's memory and latency are not a Mathlib or Anneal estimate.
