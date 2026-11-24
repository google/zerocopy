# `proofs-rs/lean-miri` Memory Specification Lemmas — Benchmark & Verification Report

## Environment & Revisions

- **Upstream base (`main`):** `4c80e83f91826c785fb607de9b9f4efa4c3b87cf` (`Merge pull request #87 from proofs-rs/perf/tree-borrows-on-demand-pruning`)
- **Previous in-file staging (`prev-in-file`):** `804c5edae3b0dc48c3796c04953eb9297d1c91ee` (all 50 theorems inline inside `InitMask.lean`, `ProvenanceMap.lean`, `Allocation.lean`)
- **Optimized companion split (`memory-specification-lemmas`):** `694b1295aa61da26afb616b5c501cf157038d050`
- **Toolchain:** `leanprover/lean4:v4.35.0`
- **Benchmarking methodology:** Same-host back-to-back 3-trial isolated single-threaded runs (`LEAN_NUM_THREADS=1 lean -j1 -R <root> -o <tmp.olean> <file>`) using clean per-variant `LEAN_PATH` overlays over identical untouched upstream `.olean`s. All timings and `.olean` byte counts below are `[real measurement]`.

---

## 1. Architecture & Diff Summary (Companion `*Verification.lean` Split)

Following `lean-miri`'s native companion convention (`Miri/Memory/AllocationAccessVerification.lean` and `Miri/Concurrency/*Verification.lean`), 90%+ of the proof elaboration and `.olean` footprint was moved out of the three core runtime modules into dedicated companion modules:

| File | Base lines | Prev In-File (`804c5eda`) | Optimized Split (`694b1295`) | Notes |
| --- | ---: | ---: | ---: | --- |
| `Miri/Memory/InitMask.lean` | 641 | `+1,086 / -0` | **`+221 / -0`** | 6 equation bridges in `InitMask.Bridge` (placed **after** the existing `WriteProof` `run_cmd` axiom check) |
| `Miri/Memory/ProvenanceMap.lean` | 416 | `+94 / -0` | **`+65 / -0`** | `rangeEmpty_new` (1-line alias for `private theorem empty_range`) + 3 minimal `ProvenanceMap.new` bridges |
| `Miri/Memory/Allocation.lean` | 1,206 | `+1,747 / -0` | **`+762 / -0`** | Minimal `Allocation.Bridge` slice, `mapExtra`, constructor, checked-read, `readScalar`, write-step, and `copyRepeatedly`-step bridges |
| **Core 3 modules combined** | **2,263** | **`+2,927 / -0`** | **`+1,048 / -0`** | **64.2% fewer lines in core; `-0` deletions; `0` runtime/visibility edits** |
| `Miri/Memory/InitMaskVerification.lean` | — | — | `+1,134` (new) | 7 public `Miri.Memory.InitMask.WriteProof.*` theorems |
| `Miri/Memory/ProvenanceMapVerification.lean` | — | — | `+87` (new) | 3 public `Miri.Memory.ProvenanceMap.*` theorems (`readPtr_new`, `prepareCopy_new`, `applyCopy_empty`) |
| `Miri/Memory/AllocationVerification.lean` | — | — | `+1,480` (new) | All 39 public `Miri.Memory.Allocation.*` theorems |
| `Miri/Memory.lean` | 15 | `0` | `+3 / -0` | Imports the 3 companion `*Verification` modules alongside their core modules |
| `MiriTests.lean` | — | `+1 / -0` | `+1 / -0` | Imports `MiriTests.Allocation.MemoryLemmas` |
| `MiriTests/Allocation/MemoryLemmas.lean` | — | `+485` (new) | `+486` (new) | All 6 kernel-checked non-vacuity witness theorems |
| **Total diff** | — | **`+3,413 / -0`** | **`+4,239 / -0`** | **`9` files changed, `0` deletions** |

Zero runtime declarations (`def`, `structure`, `inductive`, `class`, `instance`, `abbrev`, `opaque`, `axiom`) and zero visibility modifiers were modified in any core file.

---

## 2. Three-Way Same-Host Isolated Benchmark (`[real measurement]`)

All 3 variants were measured back-to-back on the exact same host (`LEAN_NUM_THREADS=1 lean -j1 -o`, 3 trials each, median reported):

### 2.1 Core Critical-Path Modules (Imported by `Miri/Interpreter/*`)

| Module | Base `4c80e83f` (Wall / User / `.olean`) | Prev In-File `804c5eda` (Wall / User / `.olean`) | Optimized Split `694b1295` (Wall / User / `.olean`) | Delta vs. Base (Split) | Critical-Path Reduction vs. In-File |
| --- | --- | --- | --- | --- | --- |
| `InitMask` | `3.370 s` / `2.880 s` / `1,837,496 B` (`1.75 MiB`) | `9.530 s` (`+6.160 s`) / `8.970 s` / `5,653,016 B` (`+3.64 MiB`) | **`3.860 s` / `3.460 s` / `2,005,544 B` (`1.91 MiB`)** | **`+0.490 s` / `+0.580 s` / `+0.16 MiB`** | **12.6× less wall Δ, 22.7× less `.olean` Δ** |
| `ProvenanceMap` | `2.380 s` / `2.170 s` / `2,261,656 B` (`2.16 MiB`) | `2.740 s` (`+0.360 s`) / `2.530 s` / `2,805,360 B` (`+0.52 MiB`) | **`2.610 s` / `2.350 s` / `2,548,384 B` (`2.43 MiB`)** | **`+0.230 s` / `+0.180 s` / `+0.27 MiB`** | **1.6× less wall Δ, 1.9× less `.olean` Δ** |
| `Allocation` | `11.390 s` / `10.870 s` / `4,452,544 B` (`4.25 MiB`) | `17.630 s` (`+6.240 s`) / `17.020 s` / `9,072,952 B` (`+4.41 MiB`) | **`11.900 s` / `11.320 s` / `5,368,752 B` (`5.12 MiB`)** | **`+0.510 s` / `+0.450 s` / `+0.87 MiB`** | **12.2× less wall Δ, 5.0× less `.olean` Δ** |
| **Core 3 Sum** | **`17.140 s` / `15.920 s` / `8,551,696 B` (`8.16 MiB`)** | **`29.900 s` (`+12.760 s`) / `28.520 s` (`+12.600 s`) / `17,531,328 B` (`+8.56 MiB`)** | **`18.370 s` / `17.130 s` / `9,922,680 B` (`9.46 MiB`)** | **`+1.230 s` / `+1.210 s` / `+1.31 MiB`** | **10.4× less wall Δ (`-11.53 s`), 6.5× less `.olean` Δ (`-7.25 MiB`)** |

**Raw 3-trial wall arrays (`s`):**
- Base `4c80e83f`: `InitMask [3.37, 3.47, 3.23]`, `ProvenanceMap [2.24, 2.38, 2.96]`, `Allocation [14.29, 11.39, 11.02]`
- Prev In-File `804c5eda`: `InitMask [10.08, 9.53, 8.95]`, `ProvenanceMap [2.74, 2.74, 2.73]`, `Allocation [17.87, 17.46, 17.63]`
- Optimized Split `694b1295`: `InitMask [4.00, 3.86, 3.77]`, `ProvenanceMap [2.61, 2.56, 2.63]`, `Allocation [11.90, 12.01, 11.40]`

### 2.2 Companion `*Verification.lean` Modules (Off the Interpreter Critical Path)

| Companion Module | Wall Median (3 trials) | User CPU Median | `.olean` Size | `.ilean` Size |
| --- | --- | --- | ---: | ---: |
| `InitMaskVerification` | `4.830 s` `[4.83, 4.91, 4.69]` | `4.370 s` | `3,317,176 B` (`3.16 MiB`) | `248,628 B` |
| `ProvenanceMapVerification` | `0.600 s` `[0.60, 0.69, 0.59]` | `0.400 s` | `256,576 B` (`0.24 MiB`) | `14,906 B` |
| `AllocationVerification` | `3.940 s` `[3.94, 3.86, 4.03]` | `3.470 s` | `2,640,160 B` (`2.52 MiB`) | `303,413 B` |
| **Companion 3 Sum** | **`9.370 s`** | **`8.240 s`** | **`6,213,912 B` (`5.93 MiB`)** | **`566,947 B`** |

### 2.3 Parallel Build Critical Path & Whole-Library Totals

- **Critical-path bottleneck before `Miri/Interpreter/*` starts (`InitMask → Allocation`):**
  - Base `4c80e83f`: `3.370 + 11.390 = 14.760 s`
  - Prev In-File `804c5eda`: `9.530 + 17.630 = 27.160 s` (`+12.400 s` stall!)
  - Optimized Split `694b1295`: `3.860 + 11.900 = 15.760 s` (**`+1.000 s`**, **12.4× reduction**!)
- **All 6 modules summed sequentially (including ~1.8 s of fixed Lean process-startup/import overhead across 3 new modules):**
  - Wall delta vs. Base: `+12.760 s` (In-File) → **`+10.600 s`** (Split; `-2.16 s`)
  - User CPU delta vs. Base: `+12.600 s` (In-File) → **`+9.450 s`** (Split; `-3.15 s`)
  - Total added `.olean` bytes: `+8,979,632 B` (`+8.56 MiB`) → **`+7,584,896 B` (`+7.23 MiB`)** (`-1.33 MiB` / `-15.5%` total, and `-7.25 MiB` / `-84.7%` on core!)
  - Total `Miri` library `.olean` footprint: `647` files, `547,028,200 B` (`521.69 MiB`, `+1.41%` vs. base).
  - Net new `Miri` declarations audited by `MiriTests/AxiomAudit.lean`: `78,617` (In-File, `+2,933`) → **`77,100`** (Split, `+1,416` — **2.07× fewer auxiliary declarations**!).
- **Downstream critical-path importer check (`Miri/Memory/AllocationAccessVerification.lean`):**
  - Base: `0.990 s` `[0.99, 1.23, 0.97]`, `20,424 B`
  - Prev In-File: `0.980 s` `[0.99, 0.96, 0.98]`, `20,424 B`
  - Optimized Split: `0.960 s` `[0.96, 0.99, 0.96]`, `20,424 B` (`0` B `.olean` delta, zero regression).
- **No-op incremental `lake build Miri` (3 trials):** `0.730 s`, `0.640 s`, `0.640 s` (**median `0.640 s`**).

---

## 3. Profiler Hotspot Analysis & Specific Optimizations Applied

Profiling with `-Dprofiler=true -Dtrace.profiler=true -Dtrace.profiler.threshold=100` identified four main sources of elaboration and `.olean` overhead in the original in-file version (`804c5eda`), all of which were fixed:

1. **`InitMask.lean` `run_cmd` axiom-scan tax (`~1.3–1.8 s` eliminated):**
   - `InitMask.lean` contains an inline `run_cmd` that walks every `Miri.Memory.InitMask.WriteProof.*` declaration in the environment. Putting heavy proofs (or bridge lemmas) inside `WriteProof` forced the interpreter to walk hundreds of new auxiliary proof constants on every `InitMask` build.
   - **Fix:** Moved all 7 `WriteProof` theorems into `Miri/Memory/InitMaskVerification.lean` and placed the 6 minimal equation bridges in `Miri.Memory.InitMask.Bridge` **after** `run_cmd`.
2. **`Allocation` `simp` unfolding over `do` blocks (`8.09 s` → `0.188 s`, ~43× faster `simp` in `AllocationVerification`):**
   - In `804c5eda`, `Allocation.lean` spent `8.09 s` in `simp` unfolding monadic `Id.run do` blocks and running default simp sets, and `ProvenanceMap.prepareCopy_new_of_sub_ok` spent `234 ms` in a single `simp only` over `prepareCopy`.
   - **Fix:** Replaced broad `simp` / `simp only` over `do` blocks with `dsimp only` + targeted `rw [ite_eq_left/right, ...]` steps, factored `h_ovl_check` in `copyRepeatedly_step_bridge` to eliminate a duplicated continuation tail, factored `readScalar_after_readUInt` across the 4 scalar-read theorems, and replaced an expensive `getBytesStripProvenance` `do`-equation header (`9.77 s` in prototype) with two direct 5-line bridges (`getBytesStripProvenance_{uninit,ok}_bridge`, `~20 ms`).
3. **Giant-context `omega` `_proof_1_k` closure explosion (`2.07×` fewer new declarations):**
   - In `804c5eda`, `findBit_spec` (`42` closures) and `copyRepeatedly_initialized_spec` (`39` closures) ran `omega` inside large local contexts, abstracting huge context tuples into top-level `.olean` auxiliary theorems.
   - **Fix:** Extracted tiny pure arithmetic helper lemmas (`Nat` / `UInt64` bounds) and deduplicated `.Lazy`/`.Materialized` branches in `set_range_get`, cutting net new `Miri` declarations from `+2,933` down to `+1,416` and cutting `AllocationVerification` type checking from `2.69 s` to `0.576 s` (`4.7×` faster).
4. **Module-graph isolation for all runtime subsystems:**
   - Programmatic import-graph traversal across all `.lean` files confirmed that **ONLY** `Miri`, `Miri.Memory`, `Miri.Memory.AllocationVerification`, `MiriTests`, `MiriTests.Allocation.MemoryLemmas`, `MiriTests.AxiomAudit`, and `docbuild.MiriApi` transitively import any of the 3 new `*Verification` modules.
   - **Zero** modules in `Miri/Interpreter/*` (`307` `.olean`s, `232.52 MiB`), `Miri/TreeBorrows/*`, `Miri/Concurrency/*`, `Miri/Input/*`, or `Miri/Frontend/*` transitively import them (`0` B `.olean` delta on every untouched runtime module).

---

## 4. Full Verification Receipts

Every check below was executed locally on commit `694b1295aa61da26afb616b5c501cf157038d050` (`Lean v4.35.0`):

| Check | Status | Receipt |
| --- | --- | --- |
| `lake build Miri MiriTests miri_tests Miri.Frontend.ImportMIR Miri.Input.ExecutionChoicePolicy` | PASS (`[real measurement]`) | Exit `0`, `752` jobs completed, `0` errors, `0` new warnings in edited lines |
| `LEAN_NUM_THREADS=1 lake env lean -j1 -DwarningAsError=true` on all 3 new `*Verification.lean` + `MiriTests/Allocation/MemoryLemmas.lean` | PASS (`[kernel-checked proof]`) | Exit `0`, `0` warnings across all 4 files |
| `lake exe miri_tests` | PASS (`[real measurement]`) | Exit `0`, `Passed 49 self-contained runtime checks` |
| `LEAN_NUM_THREADS=1 lake env lean -j1 MiriTests/AxiomAudit.lean` | PASS (`[kernel-checked proof]`) | `Axiom audit passed for 77100 Miri declarations; allowed: propext, Quot.sound, Classical.choice` |
| 1-to-1 theorem & `#print axioms` audit vs. `prev-in-file` (`804c5eda`) | PASS (`[kernel-checked proof]`) | All `56/56` public theorems (`7` `InitMask.WriteProof` + `4` `ProvenanceMap` + `39` `Allocation` + `6` `MiriTests.Allocation.MemoryLemmas`) verified present with exact names, namespaces, and axioms `⊆ {propext, Classical.choice, Quot.sound}` (`14` axiom-free, `0` `sorry`/`unsafe`/`opaque`/`native_decide`) |
| `python3 tools/check_semantic_sources.py` | PASS (`[real measurement]`) | `Semantic-source lint passed: no panic/default-returning unsafe access constructs.` |
| Zero-deletion & theorem-only diff audit on core files (`4c80e83f..HEAD`) | PASS (`[real measurement]`) | `InitMask.lean` `+221/-0`, `ProvenanceMap.lean` `+65/-0`, `Allocation.lean` `+762/-0`; `0` non-theorem declarations added, `git diff --check` clean |
| Import-graph isolation check across all `Miri/**/*.lean` | PASS (`[real measurement]`) | `0` transitive importers in `Miri/Interpreter/*`, `Miri/TreeBorrows/*`, `Miri/Concurrency/*`, `Miri/Input/*`, `Miri/Frontend/*` |
| Clean `git apply --check` of exported patch on detached `4c80e83f` | PASS (`[real measurement]`) | Exit `0`, clean apply with zero fuzz |
| Rust exporter / reference-Miri comparison suites & `examples/empty_function` | **Not executed locally** | No runtime definitions or Rust exporter code were modified |

---

## 5. Complete List of Verified Public Theorems (50 Library + 6 Test Witnesses)

- **`Miri.Memory.InitMask.WriteProof` (7, in `InitMaskVerification.lean`):**
  `get_ok_of_wellFormed`, `set_range_get`, `isRangeInitialized_nonempty_iff`, `isRangeInitialized_after_setRange_true`, `isRangeInitialized_frame`, `prepareCopy_of_uniform`, `applyCopy_singleton`.
- **`Miri.Memory.ProvenanceMap` (4: `rangeEmpty_new` in `ProvenanceMap.lean` + 3 in `ProvenanceMapVerification.lean`):**
  `rangeEmpty_new`, `readPtr_new`, `prepareCopy_new`, `applyCopy_empty`.
- **`Miri.Memory.Allocation` (39, in `AllocationVerification.lean`):**
  `byteSize_withExtra`, `len_withExtra`, `align_withExtra`, `mutability_withExtra`, `provenanceMap_withExtra`, `initializationMask_withExtra`, `getBytesUnchecked_withExtra`, `byteSize_mapExtra`, `len_mapExtra`, `align_mapExtra`, `mutability_mapExtra`, `provenanceMap_mapExtra`, `initializationMask_mapExtra`, `getBytesUnchecked_mapExtra`, `getBytesStripProvenance_mapExtra`, `readScalar_mapExtra`, `writeBytes_mapExtra`, `clearProvenance_mapExtra`, `fromBytes_spec`, `fromBytes_exists`, `tryNew_spec`, `tryNew_exists`, `getBytesUnchecked_size`, `getBytesUnchecked_subrange`, `getBytesUnchecked_split`, `getBytesStripProvenance_uninit_err`, `getBytesStripProvenance_ok`, `readScalar_uninit_err`, `readScalar_int_of_bytes`, `readScalar_int_roundtrip`, `readScalar_ptr_roundtrip`, `readScalar_ptr_none_roundtrip`, `writeScalar_spec`, `writeBytes_zero_spec`, `writeBytes_spec`, `writeUninit_zero_spec`, `writeUninit_spec`, `copyRepeatedly_initialized_spec`, `copy_initialized_spec`.
- **`MiriTests.Allocation.MemoryLemmas` (6, in `MiriTests/Allocation/MemoryLemmas.lean`):**
  `initMask_materialized_chain`, `fromBytes_writeBytes_slices_and_mapExtra`, `tryNew_strip_and_writeUninit`, `writeScalar_and_readScalar_roundtrips`, `readScalar_int_of_bytes_endian`, `copy_and_copyRepeatedly_initialized`.
