# Bounded Lean server file-worker soak and contamination sentinels

## Summary

On one 8 GiB arm64 macOS host, a direct Lean 4.30.0-rc2 server opened one, two, then four tiny imported files. All 25 exact-position goal queries retained their file-specific sentinels through three edits per cell. The four-worker cell was admitted only after a measured two-worker extrapolation. Its largest sampled process-tree summed RSS was 1,846,132,736 bytes, below the 3,355,443,200-byte guard. This is a small component workload, not evidence of Mathlib-scale capacity or an Anneal worker policy.

## Applicability

The subject is the identified Lean executable invoked as `lean --server`, with `LEAN_NUM_THREADS=1`, `LEAN_PATH` pointing to a private directory containing one directly compiled local `Dep.olean`, and four file workers under one server. The local module defines four distinct `Nat` constants; each scratch file imports it and leaves a proof hole whose goal contains its own constant/value pair. The host reported 8,589,934,592 bytes physical memory and APFS. The initial macOS `memory_pressure -Q` free percentage was 45%; it was 47–49% in subsequent recorded observations. The installed swap allocation and used amount did not change in the short run (2,048 MiB total, 682.38 MiB used).

This follows the separate [resource economics report](../anneal-3730-resource-economics-2026-09-29/REPORT.md), which measured at most two concurrent Lake consumers and two direct servers. The present test adds a guarded four *file-worker* cell on one direct server; it does not start four Lake builds.

## Findings

**Execution.** The one/two/four-worker cells all completed. At each cell, three edit/query rounds alternated file order. Every `$/lean/plainGoal` response contained the expected `probe0 = 7`, `probe1 = 9`, `probe2 = 11`, or `probe3 = 13`, with no other file's expected pair. The corresponding diagnostics referred to the same file's intended unsolved proof hole. There were 25 successful goal checks: 4, 7, and 14 by cell. These are contamination sentinels for this fixture, not a proof of general workspace isolation.

| Open files | Tree processes at stable sample | Summed RSS, stable | Sum of separately queried `phys_footprint`, stable | Largest sampled summed RSS in cell | Cell elapsed |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 460,505,088 B | 121,676,032 B | 535,871,488 B | 1,164.6 ms |
| 2 | 3 | 946,143,232 B | 304,298,816 B | 1,073,709,056 B | 1,958.8 ms |
| 4 | 5 | 1,842,298,880 B | 591,293,888 B | 1,846,132,736 B | 4,043.1 ms |

The process tree was one server plus one process per open file at the stable samples. The admission calculation extrapolated the observed one-to-two file RSS increase to two more workers and predicted 2,042,724,352 B; the recorded free percentage was 48%, so the four-worker cell passed the `<80% of 3.2 GiB guard` and `>=40% free` admission test. No runtime guard fired. The maximum sampled local disk allocation was 28,672 B in six files, including one `.olean`; no temporary file matching the script's temp-name scan appeared. After `didClose`, the process tree still listed five processes but its summed RSS fell to 306,495,488 B. After server shutdown it listed zero. The full run took 7.87 seconds.

The 25 `waitForDiagnostics` calls took 205.3–243.2 ms (median 213.1 ms); 25 goal requests took 0.7–1.8 ms (median 1.0 ms). These are local warm-session timings for tiny declarations, not independent cold-start benchmarks.

**Metric interpretation.** macOS `ps` RSS is a resident mapping count per process; summing it double-counts shared mappings and is a conservative process-tree indicator, not unique physical RAM. `footprint` reports each process's `phys_footprint`; summing separately captured values is also neither an atomic tree measurement nor Linux PSS. Linux PSS was unavailable on this macOS host and was not measured. `memory_pressure -Q` is a host-level percentage, not a byte count attributable to Lean. Samples can miss transient peaks. The unchanged swap-used observation cannot establish absence of short-lived paging.

For I113–I119, I139, I146, and I153–I154, this directly establishes only the bounded local cost, process count, scratch allocation, short edit retention, and sentinel results above. It does not establish scheduler fairness, longer-run retention, or deployment economics.

## Boundaries

- **Not examined:** Mathlib or other representative large import graphs; four simultaneous Lake consumers; full Anneal MCP process topology; longer soak, CI multiplexing, Windows/Linux, cold filesystem cache, or low-memory pressure. The fixture imports a compiled local module on top of Lean's small default environment. It is deliberately modest.
- **Not examined:** Linux PSS, macOS system-wide unique physical memory attributable to this process tree, or high-frequency peak sampling. `phys_footprint` came from sequential per-PID commands at stable cell points.
- **Unknown:** Whether the RSS growth across the three edits per cell reflects cache retention, allocator behavior, or a longer-term leak. Three rounds and 7.87 seconds do not distinguish them.
- **Known limitation of the sentinel:** Distinct names under a single `LEAN_PATH` detect file/response crossover in this run. They do not test conflicting same-name imports, cross-server cache identity, or multiple workspaces; those require separate topology/identity probes.
- The guard would record a skipped four-worker cell if the extrapolation or free-memory admission failed. It did not skip on this host. An unexpected resource excursion would abort and preserve the `fatal` and guard records in the transcript.

## Evidence

`support/probe.py` is the replayable standard-library-only harness; `support/check.py` validates the preserved observations without starting Lean. `transcript.json` retains every LSP client/server message, request latency, goal/diagnostic response, resource snapshot, guard decision, fixture hash, and cleanup event. The generated source and `.olean` are in `support/work/` for offline hash verification. Work paths in the transcript are redacted to `$WORK` / `$WORK_URI` and the exact Lean binary path to `$LEAN_BIN` for reproducibility; no semantic response was rewritten.

SHA-256: transcript `80b63975d220f3610136eac6a71dd7933033cb24c43ee0fbb1818e924f51a522`; probe script `4b721610dc0ab4a9058ecefa4f836616c3b78eb14d1dd44037382ab337db89ba`; checker `8b2a42de9ef71ccb32ca3526740f30c8c25d7011d409ba4f5a10dd006c2f3f6b`; `Dep.lean` `d785def40ffb819298d20b3b671e2150ae19cd2ada4faa88f1cd294f01529d8d`; `Dep.olean` `265a36096e2cf80aee1f32ef84a562bd702a19228ec48e0c43b0e2a44ca8b9d7`. The executable SHA-256 is in `REPORT.json` and the transcript. Observation date: 2026-09-29.

The command was `LEAN_BIN=<pinned v4.30.0-rc2>/bin/lean python3 support/probe.py` from this package directory. `python3 support/check.py` returned `OK: 363 events; 1/2/4 completed; 25 sentinel queries; guards and cleanup passed`. Hard limits were 180 seconds, 30 MiB locally allocated disk, six tree processes, 3.2 GiB summed tree RSS, and 30% reported free memory, with a stricter 40% admission floor for four workers. The probe sampled after each open/edit and at cell boundaries; these are sampling guards, not an out-of-process continuous watchdog.

## Revalidation

Run `python3 support/check.py` first to confirm the preserved evidence. For a new Lean build or host, point `LEAN_BIN` to that executable and run `python3 support/probe.py` in this package (it replaces only its own `support/work` fixture and `transcript.json`). Inspect any skipped cell and guard record before comparing measurements. Re-run under a larger import graph and longer duration before making scaling or leak claims.
