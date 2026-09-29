# Guarded direct Lean server edit/query/restart resource soak

## Summary

One pinned direct Lean LSP proof workspace ran for **336.55 seconds** across three consecutive server lifetimes and two restarts. Each lifetime lasted about 111.6 seconds, executed 21 versioned proof-buffer edits and 21 goal queries, then shut down cleanly. All **63** edited goals returned `⊢ depValue = 7`; a fresh server reopened the saved proof after each prior shutdown and returned the same goal. Thirty-six periodic full samples recorded macOS process-tree `footprint`, summed RSS, host free-memory percentage and an exact scratch-file/inode ledger. Every sample had one watchdog and one file worker, and each shutdown left zero processes in that owned tree.

After the first edit in each lifetime, the sampled group `footprint` remained near 332–333 MiB; its three end values were 332.6, 332.6 and 332.4 MiB. This bounded run found no steadily growing **sampled** footprint within a lifetime or across the two restarts. It does not classify a memory leak in a long-lived Anneal daemon, establish a hard transient peak, or represent Mathlib-scale imports. It provides a direct Lean component slice for #3730 J10 and #3731 I116/I122.

## Fixture, guard and observation method

The subject was Lean `v4.30.0-rc2`, revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, binary SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. An 8 GiB macOS arm64 host reported 49% system memory free at preflight. One private scratch directory on the internal APFS Data volume held `Dep.lean`, its compiled `Dep.olean`, and `Proof.lean`. The dependency OLean hash was `7ae5507721d0d228cfdb0c2399d6ef858bc918e48376470954b3600e40862cb3` throughout. No installation, download, backup volume or global state mutation was involved.

The proof file imports `Dep`, checks `depValue = 7`, and contains an open tactic goal. A server began with the saved proof, then received a full-text LSP edit adding a versioned trailing comment every five seconds. Each edit was followed by `textDocument/waitForDiagnostics` and `$/lean/plainGoal`. At the end of a lifetime, the final buffer was saved to disk; the next **fresh process** opened those saved bytes. The source hash handoff between successive lifetimes is retained in the transcript. The goal result checks ensure the script exercised elaboration and query state instead of leaving the process idle. This did not involve Lake, Mathlib, an MCP adapter, Rust annotations or an Anneal workspace.

The fixed guards were 390 seconds total, 4.5 GiB summed process-tree RSS or sampled group `footprint`, 20 MiB allocated scratch-file blocks, at most four descendant-tree processes and at least 25% host free memory. Preflight also required 35% free memory and over 5 GiB disk headroom. Each edit round checked the process tree, scratch disk and free-memory guard; about every ten seconds a full sample added macOS `footprint --noCategories --format bytes` for the watchdog plus file worker. A guard violation would kill the owned process group and stop the run. The recorded run had no violation. This periodic scheme cannot exclude a peak between checks or prove hard enforcement of instantaneous memory use.

## Observations

| Server lifetime | Edits and goals | Lifetime (s) | Group footprint start → after first edit → end (MiB) | Sampled footprint max (MiB) | Summed RSS start → end / sampled max (MiB) | Processes after shutdown |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 21 / 21 | 111.548 | 116.4 → 331.8 → 332.6 | 332.6 | 438.7 → 367.5 / 657.1 | 0 |
| 2 | 21 / 21 | 111.636 | 116.3 → 331.9 → 332.6 | 332.6 | 438.6 → 494.9 / 657.4 | 0 |
| 3 | 21 / 21 | 111.623 | 116.5 → 331.8 → 332.4 | 332.4 | 438.6 → 657.2 / 657.2 | 0 |

Each lifetime has 12 full samples. All 36 samples showed exactly two owned Lean processes. The minimum observed host free-memory percentage was 41%; the maximum was 53%. The maximum sampled group `footprint` was 332.6 MiB and maximum summed RSS was 657.4 MiB, well below the 4.5 GiB admission guard. The raw `footprint` text and per-process `phys_footprint` values are preserved at every sample, and the aggregate is independently summarized in [`support/sample-ledger.csv`](support/sample-ledger.csv). The first footprint sample preceded the first edit; the rise to about 332 MiB occurred with elaboration and then persisted during the subsequent paced edits. This is observed retention under a fixed tiny workload, not evidence of either a leak or a stable asymptote under larger workloads.

Summed RSS fluctuated substantially while the group `footprint` values were nearly identical across the three lifetimes. RSS counts resident mappings per process and can count shared pages more than once; `footprint` is macOS task memory accounting, not a direct count of unique host DRAM pages or an atomic peak. System memory percentage also moved with other machine activity. These measures should not be collapsed into a single resource-capacity number.

The disk ledger had exactly three regular files and four entries/inodes (including the directory root) at every full sample. Before the first save, file payload totaled 4,634 bytes; the saved trailing comment increased it to 4,659 bytes, with no further payload growth because later version numbers had the same width. File `st_blocks` charge stayed at 16,384 bytes. No extra workspace file, temporary build output or lingering process was observed. The dependency OLean hash remained unchanged; each saved `Proof.lean` hash became the next lifetime's initial disk-source hash. The disk inventory is deliberately narrow: it does not include Lean's toolchain, OS caches, logs outside this owned scratch directory or a real Anneal generation/archive tree.

## Coverage and residual

This extends the prior [three-minute direct Lean server probe](../anneal-3730-lean-multiminute-restart-resource-soak-2026-09-29/REPORT.md) with a single continuous tiny proof workload over about 5.6 minutes, two fresh-process restarts, a 36-row periodic physical-footprint/process-child/disk ledger and explicit source-hash continuity. It answers only a bounded **component** question: imported goals stayed queryable and resource samples did not drift upward after the initial elaboration plateau in these three lifetimes.

I116 and J10 still need sustained hours-long operation with representative generated imports, variable document sets, realistic use/idle phases, open/close/cancel/retry behavior, attribution of retained state versus actual leak, and a product daemon or server-pool lifecycle. I122 still needs Anneal restart reconstruction from durable generation identity, interrupted jobs, leases and cleanup after a crash, not just orderly direct-Lean shutdown and restart. Sampling every roughly ten seconds and guard checks every edit cannot certify short-lived peaks or OS-level unique physical memory. A future run should preserve the same loaded-module/import identity and workload rate when comparing long-term slopes.

## Evidence and revalidation

[`support/probe.py`](support/probe.py) is the bounded executable harness; [`support/results.json`](support/results.json) retains every goal/wait reply, version/hash, process tree, raw macOS `footprint` result, disk path/inode/size/hash row, admission input, guard setting and shutdown result. [`support/build_ledger.py`](support/build_ledger.py) deterministically derives [`support/sample-ledger.csv`](support/sample-ledger.csv); [`support/check.py`](support/check.py) verifies all three timed lifetimes, 63 edits/goals, 36 resource samples, source/artifact continuity and clean process exits. Both scripts passed on the retained result, and the package passed `reference._load_report` validation.

With the cached pin, run from this package using a new owned work path:

```console
python3 support/probe.py --lean /absolute/path/to/pinned/lean --work /owned/absent/work --out support
python3 support/build_ledger.py
python3 support/check.py
```

The 5.6-minute observation does not supply an hours-long guarantee or a safe production Anneal worker limit.
