# `proofs-rs/lean-miri` Memory Specification Lemmas and Companion `*Verification.lean` Split Benchmarks

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Splitting `50` memory-specification theorems (`InitMask`, `ProvenanceMap`, `Allocation`) out of `proofs-rs/lean-miri` (`4c80e83f91826c785fb607de9b9f4efa4c3b87cf`) core runtime modules into dedicated companion `*Verification.lean` modules (`memory-specification-lemmas` variant, measured on `leanprover/lean4:v4.35.0`) achieves:

1. **Critical-Path Build Reduction (`[real measurement]`):** Across the 3 core memory modules (`InitMask`, `ProvenanceMap`, `Allocation`) imported by `Miri/Interpreter/*`, the companion split reduces critical-path wall delta over base from **`+12.760 s` to `+1.230 s`** (**`10.4×` less wall overhead**, `-11.53 s`), reduces `InitMask → Allocation` bottleneck delay from **`+12.400 s` to `+1.000 s`** (**`12.4×` reduction**), and cuts core `.olean` bloat from **`+8.56 MiB` to `+1.31 MiB`** (**`6.5×` smaller**, `-7.25 MiB` / `-84.7%`).
2. **Zero Runtime & Zero Downstream Regression (`[real measurement]`):** `0` runtime declarations (`def`, `structure`, `inductive`, `class`, `instance`, `abbrev`, `opaque`, `axiom`) and `0` visibility modifiers changed in core files (`-0` deletions); `0` modules in `Miri/Interpreter/*` (`307` `.olean`s, `232.52 MiB`), `Miri/TreeBorrows/*`, `Miri/Concurrency/*`, `Miri/Input/*`, or `Miri/Frontend/*` transitively import any `*Verification` module; `AllocationAccessVerification.lean` exhibits `0 B` `.olean` delta (`0.960 s` vs. `0.990 s` base).
3. **Profiler-Driven Proof Optimizations (`[real measurement]`):** Moving `WriteProof` theorems out of `InitMask.lean`'s inline `run_cmd` axiom scanner (`~1.3–1.8 s`), replacing broad `simp` over monadic `do` blocks (`8.09 s -> 0.188 s`, `~43×` faster), and eliminating large-context `omega` `_proof_1_k` closures cut net new `Miri` declarations in `AxiomAudit.lean` from `+2,933` (`78,617` total) to **`+1,416` (`77,100` total, `2.07×` fewer)**.

Full tables, profiler notes, and all 56 theorem names are preserved in [support/lean_miri_benchmark_report.md](support/lean_miri_benchmark_report.md).

## Applicability

- **Upstream Base:** `proofs-rs/lean-miri@4c80e83f91826c785fb607de9b9f4efa4c3b87cf` (`Merge pull request #87 from proofs-rs/perf/tree-borrows-on-demand-pruning`), Lean `v4.35.0`.
- **Compared Experimental Variants:**
  - `prev-in-file` (`804c5edae3b0dc48c3796c04953eb9297d1c91ee`): all 50 library theorems inline inside `Miri/Memory/{InitMask,ProvenanceMap,Allocation}.lean` (`+2,927 / -0` core lines; `+3,413 / -0` total).
  - `memory-specification-lemmas` companion split (`694b1295aa61da26afb616b5c501cf157038d050`): minimal equation bridges in core (`+1,048 / -0` core lines, `64.2%` reduction), with all heavy proof scripts in `Miri/Memory/{InitMaskVerification,ProvenanceMapVerification,AllocationVerification}.lean` (`+4,239 / -0` total across 9 files, `0` deletions).
- **Measurement Regime:** Same-host back-to-back 3-trial single-threaded runs (`LEAN_NUM_THREADS=1 lean -j1 -R <root> -o <tmp.olean> <file>`) using clean per-variant `LEAN_PATH` overlays over identical untouched upstream `.olean`s; medians reported.

## Findings

### Three-Way Core vs. Companion Module Benchmarks (`[real measurement]`)

Basis: `execution` (Lean `v4.35.0` 3-trial medians).

| Module | Base `4c80e83f` (Wall / User / `.olean`) | In-File `804c5eda` (Wall / `.olean`) | Split `694b1295` (Wall / User / `.olean`) | Split Delta vs. Base |
| :--- | :--- | :--- | :--- | :--- |
| `InitMask` (`641` base lines) | `3.370 s` / `2.880 s` / `1,837,496 B` (`1.75 MiB`) | `9.530 s` (`+6.160 s`) / `5,653,016 B` (`+3.64 MiB`) | `3.860 s` / `3.460 s` / `2,005,544 B` (`1.91 MiB`) | `+0.490 s` / `+0.580 s` / `+0.16 MiB` (`+221/-0` lines) |
| `ProvenanceMap` (`416` base lines) | `2.380 s` / `2.170 s` / `2,261,656 B` (`2.16 MiB`) | `2.740 s` (`+0.360 s`) / `2,805,360 B` (`+0.52 MiB`) | `2.610 s` / `2.350 s` / `2,548,384 B` (`2.43 MiB`) | `+0.230 s` / `+0.180 s` / `+0.27 MiB` (`+65/-0` lines) |
| `Allocation` (`1,206` base lines) | `11.390 s` / `10.870 s` / `4,452,544 B` (`4.25 MiB`) | `17.630 s` (`+6.240 s`) / `9,072,952 B` (`+4.41 MiB`) | `11.900 s` / `11.320 s` / `5,368,752 B` (`5.12 MiB`) | `+0.510 s` / `+0.450 s` / `+0.87 MiB` (`+762/-0` lines) |
| **Core 3 Sum** (`2,263` base lines) | **`17.140 s` / `15.920 s` / `8,551,696 B` (`8.16 MiB`)** | **`29.900 s` (`+12.760 s`) / `17,531,328 B` (`+8.56 MiB`)** | **`18.370 s` / `17.130 s` / `9,922,680 B` (`9.46 MiB`)** | **`+1.230 s` / `+1.210 s` / `+1.31 MiB`** (`+1,048/-0` lines) |

Off-critical-path companion modules (3-trial medians):
- `Miri/Memory/InitMaskVerification.lean` (`+1,134` lines, `7` `InitMask.WriteProof.*` theorems): `4.830 s` wall, `4.370 s` user, `3,317,176 B` (`.olean`), `248,628 B` (`.ilean`).
- `Miri/Memory/ProvenanceMapVerification.lean` (`+87` lines, `3` `ProvenanceMap.*` theorems): `0.600 s` wall, `0.400 s` user, `256,576 B` (`.olean`), `14,906 B` (`.ilean`).
- `Miri/Memory/AllocationVerification.lean` (`+1,480` lines, `39` `Allocation.*` theorems): `3.940 s` wall, `3.470 s` user, `2,640,160 B` (`.olean`), `303,413 B` (`.ilean`).
- Whole `Miri` library `.olean` footprint: `647` files, `547,028,200 B` (`521.69 MiB`, `+1.41%` vs. base); total added `.olean` bytes across all 6 modules dropped `15.5%` (`+8.56 MiB` -> `+7.23 MiB`); `Miri/Memory/AllocationAccessVerification.lean` remained `0.960 s` / `20,424 B` (`0` B delta); no-op incremental `lake build Miri` median `0.640 s`.

### Four Bottlenecks Identified & Eliminated via `-Dprofiler=true`

Basis: `execution` (`lean -Dprofiler=true -Dtrace.profiler=true -Dtrace.profiler.threshold=100`, `[real measurement]`).

1. **`InitMask.lean` `run_cmd` Axiom-Scan Tax (`~1.3–1.8 s` saved):** `InitMask.lean` runs an inline `run_cmd` scanning every `Miri.Memory.InitMask.WriteProof.*` declaration in the environment. Moving all `7` `WriteProof` theorems to `InitMaskVerification.lean` and placing the `6` equation bridges in `Miri.Memory.InitMask.Bridge` **after** `run_cmd` eliminated the scan overhead.
2. **`Allocation` `simp` Unfolding Over `do` Blocks (`8.09 s` $\to$ `0.188 s`, `~43×` speedup):** Replaced broad `simp` / `simp only` over `Id.run do` blocks (`prepareCopy_new_of_sub_ok` alone took `234 ms`) with `dsimp only` + targeted `rw [ite_eq_left/right, ...]`, factored `h_ovl_check` in `copyRepeatedly_step_bridge` and `readScalar_after_readUInt` across 4 scalar-read theorems, and replaced an `9.77 s` prototype `getBytesStripProvenance` `do`-equation header with two 5-line bridges (`~20 ms`).
3. **Giant-Context `omega` `_proof_1_k` Closure Explosion (`2.07×` fewer declarations):** Extracting pure arithmetic helper lemmas (`Nat`/`UInt64` bounds) and deduplicating `.Lazy`/`.Materialized` branches in `set_range_get` (addressing `findBit_spec` `42` closures and `copyRepeatedly_initialized_spec` `39` closures) cut net new `Miri` declarations from `+2,933` to `+1,416` and `AllocationVerification` type-checking from `2.69 s` to `0.576 s` (`4.7×` faster).
4. **Strict Module-Graph Isolation:** Automated import-graph traversal confirmed **only** `Miri`, `Miri.Memory`, `Miri.Memory.AllocationVerification`, `MiriTests`, `MiriTests.Allocation.MemoryLemmas`, `MiriTests.AxiomAudit`, and `docbuild.MiriApi` transitively import the `*Verification` modules.

### Full Verification Receipts (`[real measurement]` / `[kernel-checked proof]`)

Basis: `execution` on `694b1295aa61da26afb616b5c501cf157038d050` (`Lean v4.35.0`).

- `lake build Miri MiriTests miri_tests Miri.Frontend.ImportMIR Miri.Input.ExecutionChoicePolicy`: exit `0`, `752` jobs, `0` errors, `0` new warnings.
- `LEAN_NUM_THREADS=1 lake env lean -j1 -DwarningAsError=true` on the 3 `*Verification.lean` files + `MiriTests/Allocation/MemoryLemmas.lean`: exit `0`, `0` warnings.
- `lake exe miri_tests`: exit `0`, `Passed 49 self-contained runtime checks`.
- `MiriTests/AxiomAudit.lean`: `Axiom audit passed for 77100 Miri declarations; allowed: propext, Quot.sound, Classical.choice`.
- 1-to-1 `#print axioms` audit vs. `prev-in-file`: all `56 / 56` public theorems (`7` `InitMask.WriteProof`, `4` `ProvenanceMap` including `rangeEmpty_new`, `39` `Allocation`, `6` `MiriTests.Allocation.MemoryLemmas`) verified with axioms `⊆ {propext, Classical.choice, Quot.sound}` (`14` axiom-free, `0` `sorry`/`unsafe`/`opaque`/`native_decide`).
- `python3 tools/check_semantic_sources.py`: passed; core zero-deletion / theorem-only audit clean; `git apply --check` on detached `4c80e83f` exited `0` with zero fuzz.

## Boundaries

- **Rust exporter / reference-Miri comparison (`not examined`):** Rust exporter suites, reference-Miri comparison suites, and `examples/empty_function` were not executed locally (no runtime definitions or Rust exporter code were modified).
- **Variant provenance (`known not to apply` as published upstream commits):** The experimental commits (`804c5eda`, `694b1295`) represent staged local patches applied atop upstream `proofs-rs/lean-miri@4c80e83f`, rather than already-merged upstream commits.

## Evidence

- **Primary archived benchmark report:** [support/lean_miri_benchmark_report.md](support/lean_miri_benchmark_report.md) (`129` lines, observed `2026-11-23`).
- **Base revision & toolchain:** `proofs-rs/lean-miri@4c80e83f91826c785fb607de9b9f4efa4c3b87cf`, `leanprover/lean4:v4.35.0`, benchmarked across `Miri/Memory/{InitMask,ProvenanceMap,Allocation}.lean`, `*Verification.lean`, `MiriTests/Allocation/MemoryLemmas.lean`, and `MiriTests/AxiomAudit.lean`.

## Revalidation

1. Re-run `LEAN_NUM_THREADS=1 lean -j1 -R <root> -o <tmp.olean>` across `Miri/Memory/{InitMask,ProvenanceMap,Allocation}.lean` and `*Verification.lean` when upgrading Lean beyond `v4.35.0` or modifying `Miri/Memory/`.
2. Run `lake env lean MiriTests/AxiomAudit.lean`, `lake exe miri_tests`, and `python3 tools/check_semantic_sources.py` to confirm axiom bounds (`⊆ {propext, Quot.sound, Classical.choice}`), zero regressions, and import-graph isolation (`Miri/Interpreter/*` must not transitively import `*Verification`).
