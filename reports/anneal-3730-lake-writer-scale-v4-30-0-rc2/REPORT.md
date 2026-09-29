# Lake shared-writer, frozen-consumer, and changed-definition controls

## Summary

On a tiny `v4.30.0-rc2` Lake fixture, two simultaneous consumers sharing one writable source-only producer did not both succeed: one exited with `compiled configuration is invalid; run with '-R' to reconfigure`. Four simultaneous consumers in a separate run all succeeded while each logged `Built Dep` against the same producer paths. This contrast shows why one successful writer race is not a general shared-build-tree contract. Frozen prebuilt producer controls with separate consumer build trees succeeded at 1, 2, and 4 processes without changing the producer inventory.

A controlled second run primed configuration, removed module outputs, then had two Lean writers enter the same dependency compilation. One process group was killed during an in-source pause; the survivor built the module and its consumer, and a later retry and `--no-build` check succeeded. This is one recovery schedule, not an interruption-safety proof.

An independent definition sentinel changed `depValue` from 7 to 9 while restoring the source file's old mtime. Hash-mode `--no-build` rejected the old OLean (exit 3); `--old --no-build` accepted it (exit 0). A consumer proof expecting 9 failed against the stale artifact and reported 7 until an ordinary rebuild produced a new OLean. After that, the old proof expecting 7 failed. Thus this fixture exposes the semantic consequence of mtime-based acceptance under shared mutable producer state.

## Applicability

The executed binaries were local Lean/Lake `v4.30.0-rc2` for `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. SHA-256: `lake` `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; `lean` `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. Host: macOS Darwin 25.6.0, arm64, APFS, 8 GiB physical RAM. Each fixture has one local dependency module `Dep` and one generated consumer module. All consumers receive complete relative path manifests before their first Lake invocation.

The scripts set `ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0-rc2`, `LEAN_NUM_THREADS=1`, `LAKE_CACHE_DIR=''`, `LAKE_ARTIFACT_CACHE=false`, and `MATHLIB_NO_CACHE_ON_UPDATE=1`; each Lake command includes `--keep-toolchain --no-cache`. These controls avoid an external cache in the writer comparison. They do not enforce a global one-worker limit inside an arbitrary Lake graph, though this graph has a serial import dependency. Calls are bounded by 25 seconds; the controlled parallel pairs are bounded by 10 seconds. No network dependency, Mathlib graph, native plugin, real Aeneas generated project, or actual Anneal runtime was exercised.

The hypotheses were: (1) sharing a writable producer build tree has observable collisions or requires a stronger writer contract; (2) separate writable consumer trees over a frozen producer can avoid those collisions in this small fixture; (3) a killed writer leaves a recoverable state under at least one controlled schedule; and (4) old-mode mtime fallback can accept a semantically stale imported definition. Successful simultaneous writers would support only that schedule, whereas a config/build error or wrong-definition sentinel would falsify an unconditional shared-writer or path/mtime freshness claim. The design impact is to retain explicit producer ownership and content/revision identity until a stronger shared-writer protocol is demonstrated.

## Findings

### Shared writable producer versus frozen prebuilt producer

For each count, fresh consumers were started in independent Lake processes. In the shared case they all resolved the same writable source-only producer and its `.lake` build directory. In the frozen case, a primer consumer built that producer in the same final directory, then was removed; the producer was made read-only and the fresh consumers kept separate writable directories. The table is one run per count and condition, with no claim of stable performance ranking.

| Consumers | Shared writable exits; group wall | Frozen producer exits; group wall | Sampled peak summed RSS, shared / frozen |
| ---: | --- | --- | ---: |
| 1 | `0`; 2.033 s | `0`; 1.058 s | 1,833,792 / 1,823,008 KiB |
| 2 | `0, 1`; 1.779 s | `0, 0`; 1.238 s | 1,834,160 / 3,666,992 KiB |
| 4 | `0, 0, 0, 0`; 4.131 s | `0, 0, 0, 0`; 1.605 s | 7,144,400 / 6,930,688 KiB |

The shared two-process loser failed while loading compiled configuration, before it logged a module build. In the four-process shared run, every consumer logged `Built Dep`, so four processes targeted the same dependency output paths. All frozen runs logged successful consumer builds and kept the producer's file SHA-256, size, and mtime inventory unchanged. The two-process shared failure is a concrete counterexample to unqualified concurrent workspace loading; four successful duplicate writers do not demonstrate atomic publication or safe interruption. Basis: **execution**.

A clean replay using the preserved script produced shared-writer exits `0`, `0,0`, and `0,0,0,0` at counts 1, 2, and 4; all frozen-consumer cells again passed with unchanged producer inventories. Thus the two-writer configuration failure was schedule-dependent in these two local runs. The replay's four-writer summed-RSS peak was 6,986,096 KiB; the script was not scaled further. The replay transcript is retained separately rather than replacing the failure run.

Per finished fixture, the producer had 13 files, about 105.5 KiB logical payload, and 148 KiB allocated blocks. A successful consumer had 14 files, about 119 KiB logical payload, and 164 KiB allocated blocks. These are file payload and `st_blocks` totals inside the fixture, not total bytes written or peak temporary space. The sampled RSS is a *sum* over Lake processes and descendants, obtained from macOS `ps` while they ran. It can double-count shared pages and is not unique physical memory. At the four-process cell its magnitude approached the host's 8 GiB RAM, so this probe did not increase worker count or repeat a long soak. Basis: **execution**.

### Controlled writer interruption after both compilers entered

The first attempted interruption is retained in `writer-scale-results.json`: one writer reached its in-source marker but the other failed with the same configuration error before reaching compilation. For the controlled follow-up, `interruption.py` first built both consumers sequentially to stabilize configuration, removed only their and the producer's module build directories, and relaunched both writers. `Dep.lean` wrote a distinct marker for each process and slept 1.5 seconds inside `run_cmd`. The script observed both markers, then sent `SIGKILL` to writer A's process group before its sleep elapsed. Writer A exited `-9`; writer B exited 0, logged `Built Dep` and `Built Generated`, and printed 7. A subsequent build replayed `Generated`, and `--no-build build Dep` reported all targets up to date. The final producer OLean SHA-256 was `750e919bd9db10c05dda7f98916f39a98e85b81d914fb09ec847d146640035bb`.

The paired run's sampled peak summed RSS was 3,630,016 KiB across four observed Lake/Lean processes. This schedule shows a surviving writer can recover a usable final tree after another writer is killed before module publication. It does not cover killing during output writes, trace writes, cache mapping publication, process restart, or power loss. Basis: **execution**.

The preserved interruption script was replayed from a second empty directory: both markers again appeared, A exited `-9`, B exited 0, and retry and `--no-build` both exited 0. The final producer OLean SHA-256 matched the first run. This adds one repeated schedule, not a general reliability estimate.

### Same-mtime changed-definition sentinel

The sentinel built a producer with `depValue := 7` and a consumer theorem expecting 7. It then wrote `depValue := 9` into the same `Dep.lean` and restored the file's original nanosecond mtime. Source SHA-256 changed from `195f6a0685fc4b969a2b7670245b5fcfe9b5061c7ec8bb16c7802996267d68bc` to `44acb75972b0addd77d692627d8d9318ced81820d30aef9622f8469d91bea16f`, while mtime equality was recorded in the result log.

The new consumer's `--no-build build Dep` exited 3 because the target needed rebuilding; `--old --no-build build Dep` exited 0 as up to date. Before rebuilding, `lake env lean --json Generated.lean` exited 1: the theorem expecting 9 failed, and `#eval` reported 7. The old OLean SHA-256 was `1655c61e49be501e366f40626eb3b524aa5795e87f78294c03dc1454aacc6350`. An ordinary new-consumer build exited 0, printed 9, and replaced the OLean with SHA-256 `bb5da5cf57ec84fd22a4f6e66a9964ee04647bd492e58af870e5618b6256dc25`. Rebuilding the old consumer then exited 1 because its theorem expecting 7 was false. The replay repeated these exit outcomes and source/OLean SHA-256 values. This distinguishes a stable module pathname and intentionally stable mtime from the actual definition generation. Basis: **execution**.

## Boundaries

- This report partially informs #3731 I100, I109, I113, I114, I151, and I154. I151 still needs a controlled kill at output/trace publication, conflicting *simultaneous* definitions, mapping/cache inspection, and a stronger positive writer contract. I154 has a changed-definition sentinel but not suite-order, plugin, worker-restart, or multi-test fixture matrices. I109 has one process-group kill and recovery, not timeout, disk, file-descriptor, or memory exhaustion handling. I113 has per-fixture logical/allocated file totals and sampled summed RSS, not all writes, peak temporary space, or unique physical memory. I114 has one tiny 1/2/4 sweep only.
- The two-consumer configuration error and four-consumer success are different schedules. They establish neither a failure frequency nor that four writers are safer than two. The controlled interruption was after both source-level markers and before the end of a deliberate compiler pause; the exact output-publication instant was not instrumented.
- The same-mtime sentinel demonstrates `--old` behavior for one source change. It does not characterize every trace, `--rehash`, hash-sidecar, or filesystem timestamp case.
- No Lean server, MCP process, scratch pool, or independent workspace topology was exercised, so this is not evidence for I153. No cross-process single-flight scheduler, lock-order proof, or old-result publication fence was implemented (I106–I108). No module pruning, native artifact, or cross-platform test was run.
- The small fixture's successful theorem and #eval are Lean checks only. They do not establish an Anneal Rust/model/proof correspondence or trust record.

## Evidence

The package preserves both runnable scripts and full sanitized command transcripts: [`support/probe.py`](support/probe.py) SHA-256 `3f6b2ab83e0675f92185873e311c045dd8d22752e8346806d4a50616f389e56b`, [`support/interruption.py`](support/interruption.py) SHA-256 `70e1f36d203e9c886c9ebbb446fe69fe77cf16cae11efd29e276a3c2db6924b8`, [`support/writer-scale-results.json`](support/writer-scale-results.json), [`support/interruption-results.json`](support/interruption-results.json), [`support/writer-scale-replay-results.json`](support/writer-scale-replay-results.json), and [`support/interruption-replay-results.json`](support/interruption-replay-results.json). Transcripts include commands, exits, stdout/stderr, sampled process peaks, file payload/allocated totals, inventories, and source/artifact hashes. Home/toolchain paths in logs are replaced by `$WORK`, `$LEAN_BIN`, and `$LEAN_LIB`; raw runs remain in the conversation-owned Meta/Data scratch directory. The report is **execution** evidence only. Relevant prior corpus reports include [the Lake cache concurrency probe](../lake-cache-concurrency-execution-probe-v4-30-0-rc2/REPORT.md) and [workspace/package mutable-state analysis](../lake-workspace-package-mutable-state-v4-30-0-rc2/REPORT.md).

## Revalidation

With the pinned local binaries and two new, empty owned work paths:

```console
python3 support/probe.py --lake /absolute/path/to/lake --lean /absolute/path/to/lean --work /new/path/writer-work --out /new/path/writer-output
python3 support/interruption.py --lake /absolute/path/to/lake --lean /absolute/path/to/lean --work /new/path/interrupt-work --out /new/path/interrupt-output
```

Check binary hashes and compare labelled outcomes, source/artifact SHA-256 values, and the marker/kill record. Do not compare exact wall times or infer physical memory from RSS sums. The four-process cell approaches this 8 GiB host's practical limit; select a lower-memory host budget or lower count before repeating or extending it.
