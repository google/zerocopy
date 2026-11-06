# Source edit and revert in a shared Charon/Cargo target

## Summary

A bounded, offline source edit → rebuild → revert sequence tested a previously unobserved I080 cache transition. In a tiny two-crate fixture, two equal-length source roots used one writable Cargo target sequentially. Only root A changed its Rust `step` function from `wrapping_add(1)` to `wrapping_add(2)` and then reverted; root B stayed unchanged. With `CARGO_INCREMENTAL=0` and `1`, every shared-target LLBC matched the selected local function-body projection of an independent cold target at the corresponding source state. All 16 Charon requests exited 0 and yielded parseable LLBC. Incremental-on shared-target files grew over the sequence; incremental-off targets had no incremental files. This is additional partial I080 evidence, not a resource or invalidation policy for Anneal.

## Scope and method

The fixture is the byte-preserved `warm_probe` workspace from [`anneal-3731-i080-incremental-target-layout-matrix-2026-09-29`](../anneal-3731-i080-incremental-target-layout-matrix-2026-09-29/REPORT.md): an app, a path dependency, a build script, a generated constant and one selected library target. The pinned local subjects were Charon 0.1.210 and nightly-2026-05-31 Cargo/rustc on macOS arm64 with 8 GiB RAM. The probe used only installed tools, `--offline --locked`, `CARGO_BUILD_JOBS=1`, `RAYON_NUM_THREADS=1`, a 30-second command timeout, and preflight/invocation guards of 30% system-wide free memory and 10 GiB free disk. Its exact environment and commands are in `support/probe.py` and `support/results.json`.

For each incremental setting, the probe created fresh A and B source roots of equal absolute path length. It first extracted baseline and edited A into separately cold oracle targets, deleting those targets afterward. It then reused one shared target in this exact order: baseline A, baseline B, edited A, unchanged B, reverted A, unchanged B. A and B were separate Charon processes run one after another, not a concurrent pair. The edit changed one Rust expression, preserving the source file length. The original file SHA-256 `bbe231375dfe…` returned exactly after revert from edited SHA-256 `d264e3214d6b…`. Thus the build-script's path-length input and the peer's source stayed fixed while A's function body changed.

## Observations

| Incremental setting | Shared-target state | A `step` body versus oracle | B `step` body versus oracle | Incremental files after A, then B | Allocation after B |
| --- | --- | --- | --- | --- | ---: |
| Off | Baseline | Baseline | Baseline | 0, 0 | 1,256 KiB |
| Off | Edited A | Edited | Baseline | 0, 0 | 1,256 KiB |
| Off | Reverted A | Baseline | Baseline | 0, 0 | 1,256 KiB |
| On | Baseline | Baseline | Baseline | 55, 58 | 2,668 KiB |
| On | Edited A | Edited | Baseline | 61, 64 | 2,828 KiB |
| On | Reverted A | Baseline | Baseline | 67, 70 | 2,988 KiB |

All five selected local body hashes in each shared-target LLBC equaled those in the matching cold oracle, not merely the `step` hash. The cold oracle maps differed only for `warm_probe::step`: baseline hash `0194e911c5ac…` and edited hash `5ffbb331be1e…`. The unchanged B request retained the baseline map after both A transitions. Every command's stderr recorded compilation of `warm_probe`, and every resulting LLBC reported `crate_name: warm_probe` and `has_errors: false`. These are observed output and compiler-log relationships for this fixture, not a proof of complete LLBC semantic or dependency equality. **Basis: execution.**

Incremental-on oracle targets each had 55 incremental files when measured. In the shared target, the count rose from 55 after the first A request to 70 after the final B request, while target allocation rose from 2,588 to 2,988 KiB. The incremental-off shared target retained zero incremental files and 1,256 KiB allocation after each request. The numbers describe one short sequence and include Cargo/Charon target files; they are not steady-state growth rates or machine-wide disk cost. **Basis: execution.**

Preflight had 51% system-wide free memory and 48.87 GB free disk. The lowest sampled free memory during a request was 49%; the lowest sampled free disk was 48.87 GB. No guard or timeout fired. The scratch `work/` tree was removed after retaining output and target inventories; `support/results.json` records its absence and post-run headroom. This cleanup observation does not establish crash cleanup or absence of a descendant outside the completed direct processes. **Basis: execution.**

## Relationship to prior work and limits

The [warm-target controls](../anneal-3730-charon-warm-target-controls-2026-09-29/REPORT.md) already changed source bytes with incremental compilation disabled and found a stale **path-sensitive build-script product** when a longer copied source root reused another root's target. The [I080 target-layout matrix](../anneal-3731-i080-incremental-target-layout-matrix-2026-09-29/REPORT.md) already ran incremental-on/off private/shared targets with two concurrent processes, but never changed source. This package intersects source edit/revert, equal-length roots, a shared target and incremental-on state. It neither removes the earlier path-sensitive counterexample nor repeats the matrix's concurrent schedule.

- The fixture has two tiny path-only crates, one build script and one library. The probe lacks a representative snapshot workload, proc macros, multiple selected targets, registry dependencies, long-run reuse or an independent machine.
- Sequential calls cannot measure lock contention under a dirty shared target or cancellation during incremental reuse. No process was killed; the earlier I080 two-process report owns a separate incremental-off cancellation control.
- The checker validates five serialized local function bodies, input hashes, exits, guard samples and retained artifacts. It does not authenticate every LLBC field, generated build-script product provenance, source span, dependency closure or downstream Aeneas/Lean meaning. Equal source-root lengths deliberately hold this fixture's path-sensitive build-script value constant.
- The 0.1-second headroom sampling can miss transient memory peaks; it uses a system-wide percentage, not process-tree RSS. The temporary target count is an end-of-command inventory, not a precise peak or retained-cache cost.
- No Anneal owner, scheduler, resource policy, publication transaction or actual parallel snapshot consumers ran. I080 remains **partial / resource**; representative sustained workload, concurrent dirty-target cancellation, and many-worker cleanup remain open.

## Evidence and revalidation

`support/probe.py` (SHA-256 `014de68845008f2238863e17077ae7f429b17a44634f2620c8f34086404e72ca`) is the executed script. `support/fixture-origin/` preserves its input. `support/results.json` (SHA-256 `e1f8ac94a2bda6f93ca21d11c8fae4c6030bd2f9a9ac5491d2e4b36f981e1d4a`) records commands, selected environment, source hashes, complete short stdout/stderr, all exits and output projections, headroom samples, target inventories and cleanup. `support/artifacts/` holds all 16 raw LLBCs, each under 25 KiB. Observed scratch was `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/i080-source-edit-cache/work/`; it was removed after the run. Absolute paths in the retained transcript are provenance, not read dependencies for the checker.

Run `python3 support/check.py` from this package root to validate retained evidence without launching Cargo or Charon. To repeat execution, copy the package to a disposable directory with the pinned local tools, set `I080_WORK_ROOT` to a fresh private path, and run `python3 support/probe.py`; this overwrites the copy's results and LLBCs. Compare oracle relationships and resource guards before comparing timing, raw hashes or allocation.
