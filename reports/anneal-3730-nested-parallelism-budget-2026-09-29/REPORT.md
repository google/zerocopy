# R37: tiny nested parallelism budget (J06 / I115)

Observed 2026-09-29 on Darwin 25.6.0 arm64, 8 GiB RAM. This is a direct component experiment, not an Anneal scheduler or Mathlib capacity measurement. It fills part of J06/I115 by measuring simultaneous *outer* units and configured *inner* budgets for Charon's Cargo invocation and direct Lean servers.

## Reproduction and retained evidence

Run `python3 support/probe.py` from this package. It deletes and recreates only `support/work/`, measures an admission gate before each cell, and writes `support/results.json`. Run `python3 support/check.py` to validate retained files and results without starting any compiler. The generated Rust/Lean source, Cargo logs, LLBC files, tool hashes, process trees, thread and footprint samples, latencies, memory-pressure readings, and cleanup events are retained under `support/`. The probe and checker use only the Python standard library and the pinned, locally installed tools.

The ramp uses outer unit counts 1, 2, and 4, with inner settings 1 and 2. One Cargo unit is a tiny root crate with two local path dependencies and a 150 ms build script; each unit has a private target directory. Charon runs `cargo --preset aeneas` with `CARGO_BUILD_JOBS`, `RAYON_NUM_THREADS`, and Cargo `-j` set to the inner budget. One Lean unit is a direct `lean --server` process with one open proof file and its file worker; `LEAN_NUM_THREADS` is set to the inner budget. Lean's measured cold and warm operations are `didOpen`/`didChange`, `waitForDiagnostics`, and `$/lean/plainGoal`.

Every cell passed preflight of at least 25% reported free memory and more than 5 GiB free disk. Active Cargo groups had a 40 s duration limit, 32 process and 4,000,000 KiB summed RSS caps, plus a 25% memory-pressure floor. Lean groups had the process/RSS and admission checks. No guard fired; all 12 cells ran, and the cleanup tree was empty after every Cargo group and Lean shutdown. These are local safety limits, not validated production admission thresholds.

## Measurements

Cargo values below are group wall times. Process counts and RSS are sampled peaks during the cold group, while CPU is the largest sampled sum of `ps %CPU` values; it is not integrated CPU time. The short processes and intrusive `footprint` calls mean sampled peaks can miss true peaks and affect wall time.

| Outer × inner | Cold ms | Warm no-op ms | Warm source-edit ms | Cold sampled processes | Cold sampled RSS MiB | Cold max sampled %CPU |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 × 1 | 1593 | 109 | 457 | 5 | 174 | 26 |
| 1 × 2 | 670 | 110 | 447 | 3 | 37 | 6 |
| 2 × 1 | 839 | 111 | 567 | 6 | 73 | 11 |
| 2 × 2 | 803 | 113 | 574 | 6 | 74 | 7 |
| 4 × 1 | 1241 | 189 | 832 | 12 | 202 | 13 |
| 4 × 2 | 1218 | 114 | 801 | 12 | 143 | 12 |

Cold process trees included one `charon` and one Cargo process per unit, plus short-lived `charon-driver`, clang/linker, or build-script processes. With four outer units, up to 12 processes were sampled, even though each Cargo invocation was configured for only one or two jobs. Sampled Cargo thread counts included one thread per Charon wrapper and roughly 6–8 per Cargo process; the setting is a build-job limit, not an OS-thread-count limit. `footprint` succeeded for some live PIDs and returned missing values for others that exited during inspection; the raw `resource_sample` entries preserve both. Thus no complete Cargo-group physical-footprint maximum is asserted.

All 1/2/4 warm no-op Charon runs exited successfully but rewrote the LLBC file: its mtime **and SHA-256** changed in every unit. All comment-edit runs also changed output mtime. The no-op phase is therefore a warm invocation, not a stable-output cache hit. Its `Finished` messages and file identity are preserved in the result; byte differences could include generated metadata, and this experiment did not isolate their cause. The 1 × 1 cold outlier and similar cold timings at inner 1/2 do not establish a speedup: cells ran sequentially, filesystem/tool caches warmed across the ramp, and the sampling overhead was material on these subsecond tasks.

For Lean, each listed cold/warm latency is the slowest `waitForDiagnostics` reply among the cell's simultaneous units. The goal RPC followed the wait and returned `n : Nat ⊢ n = n` for every unit, both before and after edit. RSS is a stable `ps` sum of server and worker processes; `phys_footprint` is the sum of individually successful, sequentially sampled process values. These are different metrics.

| Outer × inner | Cold wait max ms | Warm wait max ms | Stable processes | Stable RSS MiB | Sampled phys_footprint MiB | Stable sampled %CPU |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 × 1 | 245 | 211 | 2 | 429 | 111 | 74 |
| 1 × 2 | 238 | 212 | 2 | 438 | 116 | 96 |
| 2 × 1 | 240 | 213 | 4 | 868 | 233 | 198 |
| 2 × 2 | 240 | 209 | 4 | 869 | 234 | 168 |
| 4 × 1 | 370 | 214 | 8 | 1735 | 480 | 524 |
| 4 × 2 | 355 | 214 | 8 | 1735 | 490 | 442 |

The four-unit cold wait was around 355–370 ms versus 238–245 ms for one or two units on this tiny workload, a local contention observation. The four warm waits stayed around 213–214 ms. Startup `initialize` response latencies, individual wait/goal latencies, and server/worker identities are in `results.json`. Each outer unit yielded one server plus one file worker. Setting `LEAN_NUM_THREADS=1` or `2` did not cap observed OS threads to 1 or 2: sampled server processes had five threads each, and workers had 6–12. `ps -M` measures all OS threads, including runtime/background threads; it does not measure how many executed Lean elaboration simultaneously. Stable sampled `%CPU` is a snapshot-style process statistic and is not a CPU-time budget.

## Scope and remaining I115/J06 work

The experiment demonstrates a replayable direct-component 1/2/4 admission ramp, nested Charon/Cargo process growth, and direct Lean server/worker resource growth on tiny files. It does **not** exercise Aeneas's internal parallelism, Lake job controls, a combined Rust→Charon→Aeneas→Lake→Lean scheduler, realistic Rust or Mathlib work, sustained high load, other operating systems, or an Anneal admission policy. A complete J06/I115 result still needs those inner-tool controls and representative load measured under an implemented orchestration layer. In particular, neither RSS nor the per-PID `phys_footprint` values here can be multiplied into a safe concurrent-user capacity.
