# Cached Aeneas generation retention and historical Lean goals

## Result

Four previously generated Aeneas variants were retained as separate historical generations: base, changed body, changed trait signature, and a nested module move. Their Rust, LLBC, generated Lean, compiled OLean and proof bytes were copied from the earlier pinned packages; no Rust, Charon or Aeneas stage was rerun. Fresh direct Lean servers, used **one at a time**, returned the expected historical goal for each generation. A fresh server restart for the oldest and newest generations returned the same goals. Recompiling the oldest generation from its retained generated Lean source, then using a fresh worker, returned the same old goal.

This is distinct I146/A05–A06 component evidence: the earlier R16 tier sweep used a synthetic value generator, while R44 inventoried one full-chain retained tree without historical-query costs. The four variants here are real cached Aeneas outputs, but they differ in source shape and are tiny; their times are individual observations, not a production cost curve.

## Retained bytes

The tiers count only each private generation's files. The Rust-only tier holds the `.rs` input; Rust+LLBC adds Charon's saved output; generated adds the three Lean modules and proof/historical source; compiled adds three OLean files. The cached Aeneas runtime, transitive Lean libraries, toolchain, and any shared package store are excluded.

| Most recent generations retained | Rust only | Rust + LLBC | Plus generated Lean/proof | Plus compiled OLean |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 183 B | 10,089 B | 12,249 B | 29,945 B |
| 2 | 576 B | 35,095 B | 41,202 B | 119,802 B |
| 4 | 1,304 B | 82,779 B | 96,704 B | 295,448 B |

These are logical payload bytes, not exclusive physical storage or a build's temporary peak. `support/results.json` retains each file's size, allocated blocks and SHA-256. The values do not scale linearly because the four underlying programs and generated outputs differ.

## Query and reconstruction controls

Each generation's selected `Proof.lean` passed a fresh `lean --json` check without `sorryAx`. A separate `Historical.lean` leaves a proof hole so `$/lean/plainGoal` can report the exact selected proposition. The changed-body generation returned `⊢ trait_reuse.core.use_step 1#u32 = Aeneas.Std.Result.ok 3#u32`; the base and signature generations returned the corresponding `2#u32` target under distinct imported OLean hashes; the moved generation returned its new `move_probe.moved.core.use_step` name. The separate import paths and recorded OLean hashes prevent treating the old query as a query of the newest module in this fixture.

| Fresh direct server | Open/wait/goal seconds from launch | Sampled server tree RSS |
| --- | ---: | ---: |
| Base | 1.818 | 2,046,528 KiB |
| Body | 1.970 | 2,095,040 KiB |
| Signature | 2.042 | 2,108,960 KiB |
| Move | 3.165 | 2,078,448 KiB |
| Restart base | 5.345 | 2,084,032 KiB |
| Restart move | 5.677 | 2,060,928 KiB |

A generated-source-only copy of base recompiled its three modules in 4.871 s, passed its fresh proof in 1.569 s, and produced the same historical goal in a fresh server in 1.946 s. These runs occurred sequentially against a warmed host and different import/source variants. Restart times varied substantially; the table cannot justify a worker-retention threshold or causal speedup estimate. The observed sampled summed RSS peak across sessions was 2,136,720 KiB, below the 3,300,000 KiB abort guard; the memory preflight was 51% free. RSS can double-count mapped pages and miss short peaks.

The Rust-only and Rust+LLBC tiers have byte bills here but no measured Charon/Aeneas reconstruction latency. There is no actual Anneal historical-query broker, exact-revision handle, expiration policy, GC lease, simultaneous 2/4 workers, or product projection. Only the generated-source-to-OLean recompilation and compiled-to-fresh-goal costs were executed.

## Recheck

Run `python3 support/check.py` to validate all retained bytes, tier arithmetic, seven goal replies, four fresh proof checks and the recompilation outcomes offline. `python3 support/probe.py` reacquires from the cached prior report trees and rewrites only this package's `support/work` and results. It requires the same pinned Lean and cached Aeneas runtime, more than 2 GiB free disk and at least 35% reported free memory; it admits at most one server and aborts if sampled summed RSS exceeds 3,300,000 KiB.
