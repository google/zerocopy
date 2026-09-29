# Bounded combined Charon–Aeneas–Lean workflow concurrency on tiny Rust crates

## Summary

Two complete private-root Rust→Charon→Aeneas→Lean workflows passed both serially and concurrently on the pinned local macOS tool bundle. Every generated Lean text and selected compiled OLean hash matched across six units in each retained run; all three `rfl` proofs per unit passed without `sorryAx`. A 4,000,000 KiB **sampled group RSS** guard admitted two concurrent workflows and rejected the four-worker ramp before execution. In the lower-overhead run, two unconstrained workflows took 25.946 s as a group versus 44.276 s serially, but phase times varied substantially across repetitions and instrumentation. This is a bounded component scheduling measurement, not an Anneal scheduler result or a capacity estimate.

## Applicability

The executed host was macOS arm64 with 8 GiB RAM. The local pinned tools were Charon 0.1.210, Aeneas nightly-2026.06.03, Rust nightly-2026-05-31 Cargo, and Lean 4.30.0-rc2. `support/results-*.json` records executable and cached `Aeneas.olean` hashes. No dependencies were installed or downloaded; Cargo used `--offline --locked`, each worker had a private crate, target, LLBC destination, generated Lean directory and consumer directory, and the Lean consumer reused the already cached Aeneas/Mathlib OLean tree. There was no Lake command, Lean server, editor, MCP endpoint, Anneal V1/V2 executable, shared writer, or integrated scheduler.

The fixture has three Rust functions (`inc`, `twice`, `choose`) using `u32::wrapping_add`. Charon emitted an LLBC file per worker; Aeneas one-shot CLI emitted `Types.lean`, `Funs.lean` and `Current.lean`; fresh Lean batch processes compiled those modules and checked three manually chosen `Result.ok` equations. Those equations are fixture claims, not Anneal annotations or a complete obligation oracle. `CARGO_BUILD_JOBS=1`, Cargo `-j 1`, `RAYON_NUM_THREADS=1`, Aeneas `-sequential` and `LEAN_NUM_THREADS=1` bounded configured inner work but did not cap OS threads or total child processes.

## Findings

### Complete two-workflow runs and admission

Each retained run prepared Cargo lockfiles offline before the timed cell. The timed cell began with Charon/Cargo startup and ended after the last Lean proof process exited. The serial cell executed two whole workflows successively. The unconstrained parallel cell launched both whole workflows at once; the gated cell allowed Charon and Aeneas overlap but serialized each worker's four Lean invocations with a one-slot semaphore. `support/probe.py` monitored process descendants and process groups about every 40 ms when not occupied with optional `footprint` readings. It stopped a cell if sampled RSS exceeded 4,000,000 KiB, process count exceeded 40, reported free memory fell below 25%, or duration exceeded 90 s. Preflight required at least 35% reported free memory and 10 GiB disk. Four-worker admission additionally required at least 45% free memory, more than 15 GiB disk and a two-worker sampled RSS peak under 1,000,000 KiB; both retained runs skipped it. **Basis: execution.**

| Run | Two serial | Two parallel | Two parallel, one Lean slot | Four parallel |
| --- | ---: | ---: | ---: | --- |
| Low-overhead group wall time | 44.276 s | 25.946 s | 25.868 s | Skipped |
| Low-overhead sampled peak RSS | 1,999,008 KiB | 3,599,968 KiB | 1,999,216 KiB | Skipped |
| `footprint`-instrumented group wall time | 19.770 s | 33.672 s | 54.797 s | Skipped |
| Instrumented sampled peak RSS | 2,061,632 KiB | 3,729,616 KiB | 1,900,032 KiB | Skipped |
| Instrumented largest complete sampled group `phys_footprint` sum | 330.7 MiB | 663.5 MiB | 331.9 MiB | Skipped |
| Largest sampled process count, instrumented | 3 | 6 | 6 | Skipped |

The physical-footprint values are sums of successful **sequential** `footprint --pid` calls over process IDs seen in one tree snapshot, not instantaneous group peaks. Incomplete snapshots are retained and excluded from the maxima above. RSS sums count resident pages per process and can double-count shared pages; it is a conservative admission signal, not the same quantity as physical footprint. Neither sampling method proves the true interval peak. The `footprint` calls were intrusive: in the instrumented parallel run, several Lean phases stretched well beyond their low-overhead counterparts. The low-overhead serial time also varied from the instrumented run, so the rank and ratios are only observations of these few local cells, not a reproducible throughput law. Exact per-phase timing and streams are in the transcripts. **Basis: execution.**

### Output and cleanup oracles

All six stage commands per worker exited 0: Charon/Cargo, Aeneas, three Lean module compilations and Lean proof checking. Each proof output named exactly `obl_inc`, `obl_twice` and `obl_choose`, each depending on `[propext, Classical.choice, Quot.sound]`; no accepted proof listed `sorryAx`. Across the six units of each retained run, Rust source, all three Aeneas-generated Lean files, proof text and `Current/Funs.olean` were byte-identical. Raw LLBC SHA-256 differed for all six private destinations; the prior [golden vertical report](../anneal-3730-rust-charon-aeneas-lean-golden-vertical-2026-09-29/REPORT.md) identified destination path and `short_names` ordering as differences in its specific fixture, but this run did not normalize or prove the cause of its own LLBC differences. All checked process-group cleanup trees were empty after each cell, and private Cargo targets were removed. **Basis: execution.**

This extends [R37](../anneal-3730-nested-parallelism-budget-2026-09-29/REPORT.md), which measured Charon/Cargo and direct Lean server ramps separately. Here the executed stages are combined in complete per-worker chains, but the Lean portion is batch, not a server, and all dependencies are cached. It informs #3731 I115 and #3730 J06/H08 only at this component level.

## Boundaries

The lower-overhead run is still sampled by `ps` and memory-pressure commands. Cargo lockfile generation and private-directory setup occur before its group timer; they are replayable setup but excluded from reported wall time. The 90-second cell cap and 4 GiB **sampled** RSS cap do not certify an unsampled instantaneous peak below 4 GiB. A prior exploratory two-worker attempt tripped the same RSS guard at 4,000,128 KiB during concurrent Lean proofs and was killed; that failed attempt did not preserve a complete machine transcript, so it is excluded from tables and output identity claims. It motivated retaining the one-Lean-slot control. The two retained unconstrained runs stayed below the sampled cap.

H08's actual workspace-folder switch, editor extension, LSP proxy, server ownership, restart and RPC behavior remain untested. J06/I115's Anneal scheduler, nested Lake workers, realistic generated projects and Mathlib-size *workload* (as opposed to cached imports), sustained load, multi-host behavior, independent peak-memory accounting and an adopted admission policy remain open. The four-worker cell was explicitly skipped, not extrapolated from two workers. Charon/Aeneas correctness and Rust-to-Lean semantic correspondence are not proved by successful local command exits or matching generated hashes.

## Evidence

- `support/probe.py` generates each worker's crate, executes the pinned tool chain with private destinations, applies the explicit guards, captures command lines/stdout/stderr/exits and hashes, and removes Cargo target trees. It uses only the Python standard library and installed local tools.
- `support/results-uninstrumented.json` is the retained lower-overhead timing/resource transcript; `support/results-instrumented.json` is the retained run with sampled per-PID physical footprint. Each preserves admission, preflight, phase seconds, sampled process trees, peak RSS, output SHA-256 and cleanup. The exact source/manifest/proof files from the later run are under `support/work/`; Cargo targets were discarded after measurement.
- `support/check.py` checks all retained successful stage exits, proof/axiom output, shared output identities, RSS caps, four-worker skip and cleanup without launching tools. `REPORT.json` identifies the pinned executable and imported Aeneas OLean bytes. SHA-256: `support/probe.py` `1112af01d3dc9a0cc7c2a17f25a0f15f9fbc19d56eba83ebc37154c8677c1f1f`; instrumented results `c545569d5e3f1c158cae24c1c8da18945fe3546cd194c3a70d8c86dc5e07450d`; lower-overhead results `d82e377414b01b1bb7002255e14846a08169c95057d0c763c2afbee69f992b82`.

## Revalidation

Run `python3 support/check.py` for retained-result consistency. For a fresh trial, remove only this package's `support/work/` after preserving previous transcripts, then run `python3 support/probe.py --footprint off --output new-uninstrumented.json`; repeat with `--footprint on --output new-instrumented.json` if physical-footprint sampling is needed. The script refuses an existing work path and skips four workers unless its conservative admission rule passes. Compare stage outcomes and hashes first; timing, sampled RSS and footprint will vary with host load, cache warmth and instrumentation. Never treat a skipped or guard-killed cell as a completed workflow.
