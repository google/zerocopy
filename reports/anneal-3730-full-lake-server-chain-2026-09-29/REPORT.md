# Tiny Rust-to-Lake-to-server chain under an admission bound

## Question and executed subject

The prior [combined-pipeline report](../anneal-3730-combined-pipeline-concurrency-2026-09-29/REPORT.md) ran two private Rust→Charon→Aeneas→batch Lean chains but did not include Lake or a live server. This follow-up ran **one** complete private chain through offline Cargo/Charon, one-shot Aeneas, fresh direct Lean, cached Lake build, Lake-launched Lean server goal query, and fresh Lake-environment batch checking. It did not admit the two-worker cell. This is bounded component evidence for #3731 I115/I153 and #3730 J06/H08, not an Anneal scheduler or capacity result.

The source is the prior report's three-function tiny Rust fixture. The Aeneas `Current.Types`, `Current.Funs` and `Current` modules were copied byte-for-byte into a private Lake project. The project used the already cached Aeneas/Mathlib backend through an explicit path manifest and package symlink. Cargo ran `--offline --locked -j 1`; Lake had `LAKE_NO_NET=1`; `LEAN_NUM_THREADS=1` limited configured Lean work. No dependencies were installed or downloaded. The retained tool hashes in `support/results.json` identify nightly Cargo, Charon 0.1.210, Aeneas nightly-2026.06.03, Lean 4.30.0-rc2, Lake and imported `Aeneas.olean`.

## Observations

| Stage | Observed result |
| --- | --- |
| Direct Rust→Lean chain | Charon, Aeneas, three Lean module compiles and `Proof.lean` all exited 0 in 17.068 seconds. Three selected `rfl` obligations reported only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` in their theorem axiom output. |
| Lake build | `lake build -v` exited 0 in 12.045 seconds. Local `Current.Types`, `Current.Funs`, `Current` and `Proof` jobs were `Built`; the graph had 1,686 jobs including cached dependencies. `Proof.olean` was retained and hashed. |
| Live server | `lake --keep-toolchain --no-cache serve` opened the generated proof and returned one goal: `⊢ pipeline_workload.inc 0#u32 = Aeneas.Std.Result.ok 1#u32`. The `waitForDiagnostics` request succeeded. |
| Fresh batch | `lake env lean --json Proof.lean` exited 0. Its trace showed the same selected goal, and `#print axioms goal_inc` listed `[propext, Classical.choice, Quot.sound]`. |
| Cleanup | The monitored process tree was empty after orderly server shutdown and stage completion. |

The live notification stream included warnings replayed from the cached Aeneas dependency (`Aeneas/Std/Slice.lean` declarations use `sorry`), followed by the selected trace and axiom information. The selected `goal_inc` theorem's printed axiom list did not contain `sorryAx`; this is a local theorem oracle, not a claim that the entire dependency is `sorry`-free. Live and batch goal text agreed for the selected position. The generated module bytes used by Lake matched the direct chain's Aeneas outputs. Raw JSON-RPC messages, exact commands, source/artifact hashes and compressed full Lake/batch logs are retained.

## Resource gate and boundary

Preflight on this 8-GiB macOS host found 53% free system memory and 53,342,453,760 free disk bytes. The one-chain cell took 54.754 seconds, with 743 process-tree samples. Its sampled group RSS peak was 2,590,336 KiB across at most five observed processes; the minimum sampled system free memory was 32%. The guard capped sampled group RSS at 4,500,000 KiB, duration at 120 seconds, and required at least 25% free system memory. These samples can double-count shared pages and miss a transient peak; no hard physical-memory limit is proven.

The next cell was **skipped before execution**. After the one-chain run, system free memory was 40%, below the 45% two-worker threshold. Doubling the one-chain sampled peak projected 5,180,672 KiB, above the 3,000,000-KiB admission threshold; the one-chain peak also exceeded the 1,500,000-KiB per-chain gate. This conservative policy is an experiment rule, not an optimized scheduler. No two-worker Lake/server throughput, one-slot comparison, hard peak, large Rust/Mathlib workload, cache contention, editor workspace switch, or Anneal V2 endpoint was measured. The cached dependency graph is large, but the *new work* and proof are tiny.

R48 closes a local evidence gap between separate batch-chain and Lake/server reports: one trace now carries the same generated source through both Lake and live query. I115/I153/J06/H08 remain partial because an implemented Anneal scheduler and representative concurrent workload were not exercised. In particular, the skipped two-worker cell is not a completed concurrency result.

## Evidence and replay

`support/probe.py` is the standard-library harness. It imports the previous report's fixed fixture and process monitor, writes only this package's `support/work/`, and refuses existing work/log directories. `support/results.json` preserves stage exits, paths, timings, hashes, raw server messages, sampled process counts/RSS, admission decision and cleanup. `support/logs/*.gz` retains Lake and fresh-batch stdout/stderr; `support/work/` retains the generated source, private Lake manifest, local OLeans and proof. `support/check.py` validates these retained bytes and outcomes offline, including the skipped admission. It passed. `reference._load_report` also validated this package.

To replay, copy this report package and the referenced prior report, remove only the copy's `support/work/` and `support/logs/`, then run `python3 support/probe.py` and `python3 support/check.py` from the copy. It requires the exact cached local pins. Compare commands, hashes, goal/axiom semantics and admission facts; elapsed time, PIDs, RSS and transient diagnostic order may vary. If preflight or admission rejects a cell, preserve that skip rather than inferring an outcome.
