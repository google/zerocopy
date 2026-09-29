# Incremental-on shared Cargo target: cancellation and retry

## Summary

Two pinned Charon/Cargo consumers used one warmed, writable target with `CARGO_INCREMENTAL=1`. After changing A's Rust body and build script, the probe launched A, observed its build-script entry marker, launched B, and sent `SIGTERM` to A's process group while both groups were live. B logged a Cargo build-directory lock wait, then completed with parseable baseline LLBC. A's canceled request left no LLBC at its destination. A fresh Charon process retried the edited A source against the same shared target and emitted parseable LLBC. B and retried A matched separate cold-target body oracles for their respective source states. This is a small cancellation/recovery component for #3731 I080 and #3730 D06; it does not establish a general shared-target or Anneal cleanup policy.

## Scope and method

The probe used the retained two-crate `warm_probe` fixture from [the I080 target-layout matrix](../anneal-3731-i080-incremental-target-layout-matrix-2026-09-29/REPORT.md), copied byte for byte into `support/fixture-origin/`. A and B were independent, equal-length source roots. Their app has a path dependency and a build script that writes a `SNAPSHOT_VALUE` constant from `BUILD_VALUE` and `CARGO_MANIFEST_DIR` length. Both roots were first extracted into the same target, producing a warmed incremental cache. A then changed `step` from `wrapping_add(1)` to `wrapping_add(2)` and inserted a build-script entry marker plus a three-second sleep. B's source and build script stayed unchanged. The marker provides a deterministic interval for cancellation; this fixture's equal-length roots hold its known path-length input constant.

Pinned subjects were Charon 0.1.210 and nightly-2026-05-31 Cargo/rustc on macOS arm64 with 8 GiB RAM. Every request used `--offline --locked`, `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=1`, `RAYON_NUM_THREADS=1`, a private target and output destination, and a pinned local tool/Cargo environment. Here “private target” means private to this probe's scratch; A and B deliberately shared that one target. No dependency was fetched or installed. The exact commands and selected environment are in `support/probe.py` and `support/results.json`.

The probe required at least 10 GiB free disk and 30% system-wide free memory at preflight and every sample. It also guarded each selected process group at 1 GiB summed RSS, the whole private work tree at 100 MiB allocated, serial calls at 15 seconds, and the pair at 20 seconds. On a guard or timeout, the script terminates the process groups. These are experiment stops, not recommended service settings.

## Observations

| Step | Result | Incremental files in relevant target | Target allocation |
| --- | --- | ---: | ---: |
| Prewarm A, then B on shared target | Both exited 0 with baseline body map | 55, then 58 | 2,588, then 2,668 KiB |
| Cancel edited A; let B finish | A exited `-15` with no LLBC; B exited 0 with baseline body map | 109 after B | 3,752 KiB after B |
| Retry edited A on same shared target | Exited 0 with edited body map | 112 | 3,832 KiB |
| Cold edited-A and baseline-B oracles | Both exited 0 with matching body maps | 57 and 55 in their separate targets | 2,628 and 2,588 KiB |

The A marker was observed 0.468 seconds after launch. B started at 0.470 seconds, and a sampled state showed both process groups live before A was signaled at 0.662 seconds. A exited at 0.663 seconds while B remained live; B exited at 3.966 seconds. B's stderr includes `Blocking waiting for file lock on build directory`. That message shows a wait during this overlapping pair, but stderr does not timestamp lock acquisition or release. The build-script marker demonstrates entry into A's script, not an independently observed Cargo lock-owner identity. **Basis: execution.**

The five selected local function-body hashes in B's LLBC equaled the cold baseline-B oracle. The five hashes in retried A's LLBC equaled the cold edited-A oracle. Those two oracle maps differ only for `warm_probe::step` (baseline `0194e911c5ac…`, edited `5ffbb331be1e…`). The direct Charon processes for B and retried A exited 0, and their LLBCs reported `crate_name: warm_probe` with `has_errors: false`. A's canceled request produced no LLBC at its distinct destination. The retry's Cargo stderr reported completion in 0.04 seconds, so this sequence does not demonstrate that A's build script reran on retry; it demonstrates that the tested output projection was recovered. **Basis: execution.**

Preflight had 45% system-wide free memory and 46.28 GB free disk. The lowest sampled free memory was 43%, lowest free disk 46.27 GB, largest sampled process-group RSS sum 204,096 KiB, and largest private work allocation 9,116 KiB. No guard fired. After all commands, a separate `ps` read found no non-zombie members in the seven selected process groups. The script then removed its private work tree and recorded its absence. These samples can miss peaks or escaped descendants, and system-wide free memory includes other host activity. **Basis: execution.**

## Relationship to prior work and limits

The earlier [two-process shared-target report](../anneal-3731-i080-shared-cargo-target-two-process-2026-09-29/REPORT.md) canceled one owner while a companion completed, but used a fresh target with incremental compilation off and did not retry the canceled request in that target. The [incremental target-layout matrix](../anneal-3731-i080-incremental-target-layout-matrix-2026-09-29/REPORT.md) ran concurrent incremental-on pairs without edits or cancellation. The [source edit/revert report](../anneal-3731-i080-source-edit-revert-incremental-cache-2026-09-29/REPORT.md) tested dirty-source invalidation with incremental compilation on, but sequentially. This package adds the warmed incremental-on shared-target cancellation and same-target retry intersection.

- The tiny fixture is not a representative Anneal snapshot workload, sustained cache run, larger dependency graph, or many-worker resource comparison. A and B are separate local Charon processes, not Anneal-managed jobs.
- The marker was in a modified build script. The tested cancellation point does not cover every Cargo, Charon transformation, output, or publication stage. The original path-sensitive build-script stale-product counterexample remains applicable to roots of different lengths or environment closure.
- Empty selected process groups at one post-run instant do not establish escaped-descendant absence, long-term cleanup, or repeated cancellation recovery. This run did not deliberately kill the peer or interrupt the retry.
- Output checks cover five local serialized function bodies and selected LLBC metadata. They do not authenticate all LLBC fields, generated build-script product provenance, dependency closure, Postcard companions, downstream Aeneas/Lean meaning, or a transaction that preserves last-good output.
- #3731 **I080 remains partial / resource**: representative parallel consumers, sustained resource/lock tracing and many-worker cleanup remain. The result is also bounded evidence for #3730 **D06, Charon cancellation cleanup**, whose I078/I080/I105 mapping still needs stage-wide descendant cleanup and validated transactional publication in an Anneal owner.

## Evidence and revalidation

`support/probe.py` (SHA-256 `9e9249c178d5e42dc6d800bde65d4769d2883b127b15a4d3a48adfdf0a41ff6e`) is the exact executed script. `support/results.json` (SHA-256 `42822b050fc86ffa0506927e7ba19a9055c2b57c04d6914253b0682070667107`) retains fixture/tool hashes, commands, source and build-script hashes, full short stdout/stderr, event chronology, sampled resources and process groups, target inventories, output projections and cleanup. `support/artifacts/` retains the six successful raw LLBCs; `cancel-A.llbc` is deliberately absent. The observed work tree was `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/i080-incremental-cancel/work/` and was removed after the run. Retained absolute paths are provenance, not dependencies for checking copied packages.

Run `python3 -B support/check.py` from this package root to validate the retained observation without launching Charon or Cargo. To replay, copy the package to a disposable directory with the pinned installed tools, set `I080_CANCEL_WORK_ROOT` to a fresh private path, and run `python3 -B support/probe.py` there. The replay overwrites the copied outputs and may produce different timing, scheduling, target counts and raw hashes. Compare the cancellation ordering, peer completion, oracle body maps and guard behavior before interpreting any timing or footprint differences.
