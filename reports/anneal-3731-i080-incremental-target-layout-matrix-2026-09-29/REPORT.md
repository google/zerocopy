# Incremental Cargo target layout for two Charon consumers

## Summary

On one small offline Cargo fixture, two Charon consumers completed from cold and warm targets in each of four cells: private or shared `CARGO_TARGET_DIR`, with `CARGO_INCREMENTAL=0` or `1`. All 16 requests exited 0 and produced parseable LLBC with the same selected local function-body projection. Shared targets emitted Cargo build-directory lock-wait messages; private targets did not. Incremental-on targets retained more files and bytes. This adds a narrow incremental-on comparison to the earlier two-process shared-target report for #3731 I080 and #3730 D03; it does not establish a production scheduling or resource policy.

## Applicability

The executable subjects were pinned Charon 0.1.210 and the cached nightly-2026-05-31 arm64 Cargo/rustc binaries identified in `REPORT.json`. The host was macOS arm64 with 8 GiB physical RAM. The probe used the retained two-crate `warm_probe` fixture from `anneal-3730-charon-warm-target-controls-2026-09-29` (source Git tree `af738e8e51a229bdc2940cc1caf176c2bec711b2`), copied byte for byte into `support/fixture-origin/`. Each cell created independent A and B source roots and inserted the same one-second sleep at the start of their copied `app/build.rs` files to allow overlap. The root paths had equal lengths within and across all four cells, so this fixture's `CARGO_MANIFEST_DIR`-length build-script value was held constant. Source files, package selection and output destinations were otherwise fixed by the probe.

The four cells ran sequentially. Within each cold or warm phase, exactly two fresh `charon cargo` processes ran concurrently, with distinct `.llbc` destinations. A warm phase reused its cell's target directory without source edits. Private layout used one target per root; shared layout used one target for both roots. Every process used `CARGO_BUILD_JOBS=1`, `RAYON_NUM_THREADS=1`, `CARGO_NET_OFFLINE=true`, pinned `RUSTUP_HOME`, `CARGO_HOME`, `PATH` and `DYLD_LIBRARY_PATH`, and `--offline --locked`. The command shape was:

```console
charon cargo --preset aeneas --dest-file "$SUPPORT/artifacts/<cell>/<phase>-<A-or-B>.llbc" -- --manifest-path "$SUPPORT/work/<cell>/<A-or-B>/Cargo.toml" --package warm_probe --lib --offline --locked
```

`support/probe.py` gives the exact path and environment construction. Preflight observed 46,609,092,608 free disk bytes and 49% system-wide free memory. A cell would stop and terminate its process groups if `memory_pressure -Q` reported less than 30% free memory, if free disk fell below 10 GiB, or if a phase exceeded 35 seconds. The lowest sampled values were 48% free memory and 43.40 GiB free disk; no guard fired. Only cached binaries and dependencies were used.

## Findings

### Cold and warm output remained parseable across the matrix

| Target layout | `CARGO_INCREMENTAL` | Cold phase elapsed | Warm phase elapsed | Final target allocation after warm | Incremental files after warm | Build-directory lock wait |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| Private, two targets | 0 | 1.722 s | 0.148 s | 1,260 KiB each | 0 each | None recorded |
| Private, two targets | 1 | 1.836 s | 0.141 s | 2,692 KiB each | 59 each | None recorded |
| Shared, one target | 0 | 1.595 s | 0.147 s | 1,260 KiB | 0 | Recorded in both phases |
| Shared, one target | 1 | 1.717 s | 0.147 s | 2,852 KiB | 65 | Recorded in both phases |

Both process groups had live members in at least one sample of every phase. Each of the 16 results exited 0, parsed as `warm_probe` LLBC with `has_errors: false`, and had a distinct raw SHA-256. All 16 produced the same map of five selected local declaration names to serialized `body` JSON hashes, including `SNAPSHOT_VALUE`; `support/results.json` retains each map and `support/artifacts/` retains all raw LLBCs. This is a fixture-specific equality of that projection, not a general LLBC semantic-equivalence proof. The raw hashes differ, so byte identity would reject otherwise matching projected bodies. **Basis: execution.**

The shared cells recorded `Blocking waiting for file lock on build directory` in one process's stderr in each cold and warm phase. The private cells recorded no such message. Cargo's stderr does not timestamp acquisition, and a message alone does not measure the exact wait duration. The phase elapsed values are one observed schedule each, with process launch, sampling and filesystem activity included; they are not throughput estimates. **Basis: execution.**

### Incremental state changed the small target footprint

After the cold phase, the private incremental-on targets each held 56 incremental files and about 1.389 MB of incremental file bytes; the one shared incremental-on target held 59 files and about 1.468 MB. After warm extraction these were 59 and about 1.468 MB per private target, versus 65 and about 1.627 MB in the shared target. Incremental-off targets held no files under an `incremental` path. The final total allocation for two private incremental-on targets was 5,384 KiB, versus 2,852 KiB for one shared target. These are temporary target-directory measurements under one tiny fixture, not machine-wide disk cost or retained-cache economics. **Basis: execution.**

For each cell, the probe counted regular target files and bytes after both processes had exited, sampled target allocation while they ran, checked the 16 process groups for remaining live members, then removed that cell's private work tree. `support/results.json` records no live members in the final process-group check, absence of the work tree after cleanup, and post-run headroom. That observation does not prove the absence of an escaped descendant or guarantee cleanup after an unplanned crash. **Basis: execution.**

## Boundaries

- The fixture has two tiny crates, one path dependency, one build script and one selected library target. It has no registry dependencies, representative Anneal snapshot consumers, larger dependency graph, sustained workload or independent host.
- The selected body projection hashes the serialized local declaration `body` values. It does not authenticate every LLBC field, source span, options, producer identity, dependency provenance or downstream Aeneas/Lean meaning. Equal-length source paths deliberately avoid this fixture's known path-sensitive stale-product counterexample; the earlier warm-target report documents that separate hazard.
- The incremental-on comparison ran cold then once warm, with no source mutation, cancellation, restart after kill or crash. The separate `anneal-3731-i080-shared-cargo-target-two-process-2026-09-29` report retains an incremental-off cancellation/companion observation. Incremental-on cancellation and long-run drift remain open.
- `memory_pressure -Q` gives system-wide free percentage at sampled instants. Process-group RSS sums in the raw transcript may double-count shared pages and miss peaks between samples. The 30% free-memory and 10-GiB disk thresholds bounded this run; they are not proposed production settings.
- Cargo lock messages and temporary target sizes cannot establish safe target sharing for changed source roots, build-script location inputs, arbitrary dependency caches or Anneal publication transactions.

## Evidence

- `support/probe.py` (SHA-256 `d7f5d76da27a817d550d380314feb18974c495c3bc1aac2261e3cdc588de26a0`) is the exact executed script. Its input bytes are retained in `support/fixture-origin/`; the script copied and modified only private fixture roots in the conversation scratch directory.
- `support/results.json` (SHA-256 `040f6e477a358b602af87298fbc8517cd5269e8803d4ede7e70762ae31d58828`) records the preflight, exact commands and selected environment construction, all phase samples, complete short stderr/stdout, exits, projections, target inventories and cleanup. `support/artifacts/` contains all 16 raw LLBC files (24,115 or 24,120 bytes each). `support/check.py` verifies the retained relationships without running Cargo or Charon.
- The observation was made on 2026-09-29 under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/i080-incremental-matrix/`; the transient `work/` tree was removed after its target measurements. Absolute scratch paths in LLBC and transcript are observation provenance, not replay dependencies.

## Revalidation

Run `python3 support/check.py` inside this report package to verify the preserved observation. To repeat the experiment, copy the whole package into a disposable directory with the pinned local tools and at least 10 GiB free, then run `python3 support/probe.py` there; the probe requires an absent `support/work/` path. Compare exits, parsed identities, selected body projections, lock messages, target footprints and headroom before comparing raw hashes or timing. A new run may have different scheduling, lock-message placement and raw bytes. Representative workload sizing and incremental-on cancellation require separate probes.
