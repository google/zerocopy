# Full-chain transient workspace accounting for issue #3731 I113

## Summary

One bounded replay of the existing tiny Rust→Charon→Aeneas→direct Lean→Lake→live server→fresh batch fixture recorded file-level snapshots at 24 stage boundaries and 331 intervening samples. The largest observed regular-file allocation in the disposable run directory was **4,825,088 bytes**. Cargo left **12 files, 5,838 logical bytes and 28,672 allocated bytes** in its target directory before the harness deleted it. The prior retained-file inventory could not count that temporary target. These are lower bounds on peak space and write activity, not an all-write trace.

## Applicability

This is one sequential worker on macOS arm64 APFS, using the exact cached nightly Cargo, Charon 0.1.210, Aeneas nightly-2026.06.03, Lean/Lake 4.30.0-rc2, and imported Aeneas OLean hashes recorded in [`support/observations.json.gz`](support/observations.json.gz). The pinned tool hashes matched the prior [full-chain package](../anneal-3730-full-lake-server-chain-2026-09-29/REPORT.md) before the run. Its tiny three-function Rust input, selected proof, offline Cargo and Lake settings, and cached dependency tree were reused. The direct six commands, Lake build, live goal request and fresh batch all succeeded. The selected live goal was `⊢ pipeline_workload.inc 0#u32 = Aeneas.Std.Result.ok 1#u32`.

System free memory was 45% and disk free space about 45 GiB immediately before this single replay. The run stopped under the existing 4,500,000 KiB sampled process-group RSS, 120-second and 25% memory guards, with an added 10 GiB disk floor. It completed in 72.508 seconds with 2,455,072 KiB sampled peak RSS, 30% minimum sampled free memory, no guard abort, and no remaining child process. No dependency was fetched or installed.

## Findings

The boundary snapshots traverse the disposable workspace without following the Lake package symlink. They record each regular file and symlink's relative path, logical size, `st_blocks × 512`, device and inode. The table excludes the probe's 20,480-byte allocated Python cache baseline and separately captured logs; the figures are worker-local file and symlink allocation at each named boundary, including the Rust target until cleanup.

| Boundary | File and symlink inodes | Logical bytes | Allocated bytes |
| --- | ---: | ---: | ---: |
| After Cargo/Charon | 16 | 22,250 | 57,344 |
| After Aeneas | 19 | 23,932 | 69,632 |
| After direct Lean proof | 26 | 52,354 | 118,784 |
| After Lake setup | 33 | 58,183 | 143,360 |
| After Lake build | 67 | 4,526,587 | 4,710,400 |
| After live server and fresh batch | 67 | 4,526,587 | 4,710,400 |
| After Cargo target cleanup | 55 | 4,520,749 | 4,681,728 |

Charon's stage added the 16,384-byte allocated LLBC plus 28,672 bytes in Cargo target files. Aeneas added 12,288 bytes of generated Lean source. Direct Lean reached 49,152 allocated bytes across seven consumer files, including the three copied generated modules and local OLeans. Lake setup added 24,576 bytes of project source/configuration and a package symlink. Lake build added 34 local `.lake` files totaling 4,468,404 logical and 4,567,040 allocated bytes. The symlink target is shared cached input and its contents are excluded. Server and fresh batch created no additional *worker-tree* regular file at their before/after boundaries. Six compressed harness logs consumed 94,208 allocated bytes by pre-cleanup; those are probe output, not a measured Anneal worker bill.

The 12 deleted target files include Cargo lock and fingerprint state; their exact names, inodes and sizes survive in the before/after raw rows. All 331 periodic samples stayed below the 4,825,088-byte boundary maximum. Sampling was scheduled every 0.20 seconds and at command boundaries; the actual spacing includes traversal time. It can miss short-lived `.tmp` files or rewrites, so **4,825,088 bytes is an observed maximum, not a proven true peak**. The final worker tree differs in some path-dependent hashes and allocation from the earlier run; this package reports this replay's bytes, while the earlier retained inventory reports its own saved tree.

The earlier [retained-file inventory](../anneal-3730-retained-full-chain-byte-timing-inventory-2026-09-29/REPORT.md) had the same 54 regular files and one symlink, 4,524,103 logical bytes **including the 99-byte symlink pathname**, and 4,698,112 allocated bytes. On that same convention, this replay ended with 4,520,848 logical and 4,681,728 allocated bytes: respectively 3,255 and 16,384 fewer. The path sets match exactly. The 3,255-byte difference is confined to `current.llbc` (93), three path-bearing Lake setup JSON files (558 total), and four Lake trace files (2,604 total); the four traces each occupy one fewer 4 KiB block. The table above counts regular-file payload only, excluding the symlink's 99-byte pathname from logical bytes. This direct comparison is of two executions' retained results; it does not turn the earlier final inventory into a transient-space measure.

Four selected external roots—Cargo home, Rustup home, the Aeneas backend and Lean toolchain—had identical before/after `du -sk` totals and unchanged root mtime/ctime. This establishes zero **net change at 1 KiB `du` resolution** in those roots during this replay; it is not a claim that no outside write occurred. The harness set `TMPDIR`, `TMP`, `TEMP`, and `XDG_CACHE_HOME` to its disposable directory; no files remained there at recorded boundaries. Basis: **execution** and arithmetic derived from preserved snapshots.

## Boundaries

This package addresses the transient/accounted-workspace portion of **I113**. It does not measure cumulative bytes written, overwritten blocks, APFS exclusive extents, directory inode counts, sub-200-ms temporary files, all file operations, or absolute peak temporary space. The previously published DYLD libc observer's compiled dylib was no longer available; no hook was used here. That observer itself captures only selected interposed libc calls and paths under its configured root, so even using it would not be a complete filesystem trace. `du` net equality cannot exclude create/delete cycles, same-size rewrites, paths outside the four selected roots, or concurrent unrelated writes. The redirected temporary environment does not prove every tool obeyed it.

No second worker, Anneal V2 service, representative Rust crate, changing proof workload, or shared-cache accounting was exercised. In I113's requested bill of materials, this adds exact observed worker-local stage attribution and one deleted Cargo-target term. Full outside-workspace write attribution, cumulative write bytes, true temporary peak, and classification of every worker-scaling byte remain open. The worker-local counts also do not include cached dependencies reachable through the `.lake/packages` symlink.

## Evidence

[`support/observations.json.gz`](support/observations.json.gz) preserves the complete 24 boundary rows, 331 interval totals, selected external-root counter pairs, resource readings, pin hashes and outcome summary. [`support/baseline-retained.json`](support/baseline-retained.json) preserves the prior run's 55 path/size/block entries for the exact comparison above. Its predecessor full-chain `results.json` SHA-256 was `8bb8a9d61054e8a6550b102c8985fc1befdac325d701c2814bc9bdc414b50f1c`. The local [`support/probe.py`](support/probe.py) is the exact stdlib instrumentation run from a fresh disposable directory under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/`; it imports the prior full-chain and combined-pipeline probes, then wraps command and server stages with snapshots. The retained script is tied to this local reference checkout and must be copied to a fresh scratch directory for a new replay. It refuses an existing work/log/result directory. The raw observations are self-contained for the accounting claims and can be checked without the toolchain.

The named previous [retained-file inventory](../anneal-3730-retained-full-chain-byte-timing-inventory-2026-09-29/REPORT.md) inventoried only final files from its earlier run. The [unprivileged file-event report](../anneal-3730-lake-unprivileged-file-event-observability-2026-09-29/REPORT.md) documents both a positive temporary OLean rename in a different tiny Lake fixture and the observer's coverage limits; that rename is not attributed to this run.

## Revalidation

Run `python3 support/check.py` to verify all preserved row and family sums, successful pipeline exits, resource floors, the 12 exact target deletions, observed maximum and selected outside-root net counters. For a new write/peak claim, rerun a fresh one-chain fixture with a system-level or validated process-tree file-event and byte counter, including outside-workspace paths; compare stage totals and retention under the same pinned tools. A new run should be admitted only with at least 25% free system memory and 10 GiB free disk.
