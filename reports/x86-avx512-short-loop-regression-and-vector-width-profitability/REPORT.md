# Eliminating the AVX-512 and `x86-64-v4` Short-Loop Regression: Gather Suppression, Vector-Width Caps, and Predicated Tail-Folding in `rustc` 1.99.1 and LLVM 23.1.1

## Summary

In `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and bundled LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), compiling mixed Rust workloads with `-C target-cpu=x86-64-v4` or `-C target-cpu=native` on AVX-512 server hardware inflates static machine instruction count across the 8-kernel benchmark suite by **`+70.9%`** (`801` $\rightarrow$ `1,369` instructions) and degrades median execution time by **`-31.14%`** (`726.81` $\mu\text{s}$ $\rightarrow$ `953.16` $\mu\text{s}$ on `x86-64-v4`) and **`-43.47%`** (`1,042.76` $\mu\text{s}$ on `native`). Controlled per-kernel disassembly, target-feature isolation, and trip-count sweeps (`N \in \{4, 8, 12, 16, 24, 32, 48, 64, 128, 256, 1024, 16384\}`) establish the exact mechanisms and cure:

1. **LLVM 23.1.1 Already Sets `FeaturePrefer256Bit` on `x86-64-v4`—So 512-Bit `zmm` Loops Are Not the Primary Culprit**:
   - In `llvm/lib/Target/X86/X86.td`, the `x86-64-v4` processor model includes `FeaturePrefer256Bit` (`+prefer-256-bit`) by default. Consequently, under default `-C target-cpu=x86-64-v4`, `LoopVectorize` emits `284` 128-bit `xmm` instructions, `204` 256-bit `ymm` instructions, and only **`7` 512-bit `zmm` instructions** (confined to loop-preheader minimum/maximum reductions in `k6_zerocopy_endian`). Forcing full 512-bit vectorization via `-C target-feature=-prefer-256-bit` (`Counterfactual_Force512BitZMM`) jumps `zmm` instruction count from `7` to **`234`** and inflates total instructions to `1,558` (`+94.5%` over `x86-64`).
2. **Decomposition of the `x86-64-v4` / `native` Slowdown Across Four Concrete Mechanisms**:
   - **Mechanism 1 — Masked AVX-512 `vpgatherqd` Microcode Stalls (`+159.83` $\mu\text{s}$, `71.4%` of the regression)**: Enabling `x86-64-v4` activates `FeatureFastGather`, causing `LoopVectorize` to vectorize conditional indexed slice lookups (`if idx < data.len() { sum += data[idx] }` in `k1_slice_bounds_iter`) into 5 masked `vpgatherqd` (`{%k1}`) instructions. On Intel Xeon processors with Gather Data Sampling (GDS / Downfall) microcode mitigations, `k1_slice_bounds_iter` slows down by **$3.44\times$** (`65.55` $\mu\text{s}$ on `x86-64-v3` $\rightarrow$ `225.38` $\mu\text{s}$ on `x86-64-v4`). Passing `-C target-feature=+prefer-no-gather` eliminates all 5 `vpgatherqd` instructions and restores `k1_slice_bounds_iter` to **`66.71` $\mu\text{s}$**.
   - **Mechanism 2 — Vectorized Strided-Byte Induction Scalarization (`+63.97` $\mu\text{s}$, `28.6%` of the regression)**: In `k6_zerocopy_endian` (16-byte big/little-endian packet parsing), `AVX512DQ`/`AVX512VL` lowers the cost-model estimate of 64-bit vector shifts and bitwise ORs (`vpsrlq`, `vporq`), causing `LoopVectorize` to widen the induction variable into 18 `ymm` registers (`ymm2..ymm19`) and extract each byte offset back to scalar GPRs via `vmovq` + `vpextrq` + `vextracti32x4` (`15` extractions per iteration), slowing `k6_zerocopy_endian` from `93.15` $\mu\text{s}$ (`x86-64-v3`) to `157.12` $\mu\text{s}$ (`x86-64-v4`).
   - **Mechanism 3 — Multi-Tier Vector + Epilogue Cascade and Interleave Unrolling (`UF=2..4`) on Short Trip Counts ($N \le 32$)**: On the controlled trip-count sweep (`support/avx512_trip_count_sweep.csv`), capping the interleave factor via `-C llvm-args=--force-vector-interleave=1` (`StratD`) on `x86-64-v3` reduces per-1,000-element runtime at $N = 16$ from `1,829.39` ns to **`1,339.29` ns (`+26.8%` speedup)** and at $N = 32$ from `1,297.26` ns to **`1,035.74` ns (`+20.2%` speedup)** while shrinking static instructions from `1,224` to `1,066` (`-12.9%`).
   - **Mechanism 4 — 512-Bit `zmm` Preheader License Transitions**: Eliminating the remaining 7 `zmm` instructions in `k6_zerocopy_endian`'s preheader via `-C target-feature=-evex512,+prefer-no-gather` (`StratA`) recovers `201.43` $\mu\text{s}$ on `x86-64-v4` (`953.16` $\mu\text{s}$ $\rightarrow$ `751.73` $\mu\text{s}$).
3. **Why Unconditional AVX-512 Masked Tail-Folding (`--tail-folding-policy=prefer-fold-tail`) Shrinks Code by `-16.0%` (`1,369` $\rightarrow$ `1,150` Instructions) but Regresses Short Loops on `x86_64`, Whereas It Excels on AArch64 SVE (`neoverse-v1`)**:
   - In LLVM 23.1.1, the legacy `-prefer-predicate-over-epilogue` flag is replaced by `--tail-folding-policy={dont-fold-tail,prefer-fold-tail,must-fold-tail,disabled}` (`llvm/lib/Transforms/Vectorize/LoopVectorize.cpp`).
   - On `x86-64-v4`, `--tail-folding-policy=prefer-fold-tail` (`StratB`) folds scalar and vector epilogues into the main loop using `k1` masks, cutting total instructions across the 8 kernels from `1,369` to **`1,150` (`-16.0%`)** and branches from `158` to **`139` (`-12.0%`)** (for example, shrinking `k2_iter_combinators` from `157` to `57` instructions and `k8_simd_numeric_dot` from `110` to `52` instructions). However, because `x86_64` lacks a single-instruction loop-termination mask generator equivalent to AArch64 SVE's `whilelo`, computing `k1` lane masks and serializing masked memory operations inside the inner loop slows $N = 16$ from `3,099.15` ns to `3,585.07` ns (`-15.7%`).
   - On `aarch64-unknown-linux-gnu` with `-C target-cpu=neoverse-v1` (SVE), `--tail-folding-policy=prefer-fold-tail -C llvm-args=--sve-tail-folding=all -C llvm-args=--force-vector-interleave=1` (`StratE_PredicatedTail_UF1`) emits native `whilelo` predicate loops (`4` `whilelo` instructions), eliminating `100%` of scalar/NEON epilogue bloat and reducing total instructions across the 8 kernels from `813` (`3,436 B`) to **`598` instructions (`2,324 B`, `-26.4%` fewer instructions and `-32.4%` smaller `.text` than default `neoverse-v1`, and `-9.5%` smaller than baseline `generic` NEON!)**.

## Applicability

- **Subjects**: `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, released 2026-10-15) and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
- **Targets examined**: `x86_64-unknown-linux-gnu` (`-C target-cpu={x86-64, x86-64-v2, x86-64-v3, x86-64-v4, native}`, execution + disassembly) and `aarch64-unknown-linux-gnu` (`-C target-cpu={generic, neoverse-n1, neoverse-v1, apple-m1}`, object disassembly and size).
- **Relation to other corpus packages**: Extends `where-time-goes-in-rust-programs-hot-patterns-and-instruction-mix` and `llvm-compiled-rust-instruction-and-addressing-mode-frequencies`.

## Findings

### 1. Root-Cause Decomposition of the `x86-64-v4` and `native` Regression

`Basis: source + execution (support/run_avx512_vector_policy_sweep.py, support/avx512_policy_matrix.csv, support/avx512_and_sve_analysis.json)`

Table 1 decomposes per-kernel execution time ($\mu\text{s}$ for 25 iterations) and static instruction counts across the 8 Rust workload kernels:

| Kernel | `x86-64` (SSE2) Time ($\mu\text{s}$) / Insts | `x86-64-v3` (AVX2) Time ($\mu\text{s}$) / Insts | `x86-64-v4` (Default) Time ($\mu\text{s}$) / Insts | `x86-64-v4` + `prefer-no-gather` Time ($\mu\text{s}$) / Insts | `x86-64-v4` + `prefer-no-gather` + `UF=1` Time ($\mu\text{s}$) / Insts | Dominant Mechanism on `x86-64-v4` |
| :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| `k1_slice_bounds_iter` | `67.59` / `147` | `65.55` / `191` | **`225.38`** / `194` | **`66.71`** / `191` | **`63.01`** / `147` | 5 masked `vpgatherqd` instructions in conditional slice lookup cause a **$3.44\times$ slowdown** (`+159.83` $\mu\text{s}`); cured by `+prefer-no-gather`. |
| `k2_iter_combinators` | `51.08` / `66` | `48.03` / `110` | **`29.48`** / `157` | **`29.56`** / `157` | `33.89` / `102` | AVX-512VL 256-bit `vpmullq` + `vprolq` + `k`-mask filter achieves a **`+42.3%` speedup** over SSE2/AVX2. |
| `k3_utf8_scanner` | `164.80` / `45` | `241.24` / `45` | `164.77` / `45` | `164.80` / `45` | `164.80` / `45` | Data-dependent variable-step UTF-8 DFA stays scalar (`0` SIMD instructions); code-alignment sensitive on `v3`. |
| `k4_hash_crc_digest` | `74.74` / `98` | `74.69` / `126` | `74.69` / `126` | `74.69` / `126` | `74.70` / `126` | Serial 64-bit multiplicative hash chain (`rorx`/`imulq`). |
| `k5_sort_binary_search` | `69.26` / `87` | `67.38` / `87` | `67.35` / `87` | `67.87` / `87` | `67.81` / `87` | Short insertion sort ($N \le 64$) + branchless `cmov` binary search. |
| `k6_zerocopy_endian` | `138.32` / `217` | **`93.15`** / `501` | **`157.12`** / `596` | `157.14` / `596` | `157.56` / `483` | `x86-64-v4` widens strided packet induction variable into 18 `ymm` registers + 7 preheader `zmm` instructions and extracts 15 scalar byte addresses per iteration (`+63.97` $\mu\text{s}$ vs `x86-64-v3`). |
| `k7_enum_dyn_dispatch` | `194.76` / `56` | `150.81` / `54` | `150.84` / `54` | `194.76` / `54` | `176.58` / `54` | Indirect vtable call loop (`callq *0x18(%rax)`). |
| `k8_simd_numeric_dot` | `8.39` / `85` | **`2.06`** / `110` | `8.61` / `110` | `8.61` / `110` | `8.89` / `68` | Vectorized 256-bit `vpmulld` + `vpaddq` reduction ($N = 512$). |

---

### 2. Controlled Sweep of Five Vectorization Strategies on `x86_64`

`Basis: execution (support/avx512_policy_matrix.csv, support/avx512_trip_count_sweep.csv)`

Table 2 reports the full 8-kernel metrics across `-C target-cpu` levels and the five mitigation strategies:

| `target-cpu` | Strategy | Total Insts | SIMD Insts | `xmm` (128b) | `ymm` (256b) | `zmm` (512b) | `k`-Mask Insts | Gather Insts | Branch Insts | `.text` Bytes | Suite Median ($\mu\text{s}$) | vs. `x86-64` (%) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `x86-64` | `Default_Unconstrained` | 801 | 50 | 50 | 0 | 0 | 0 | 0 | 149 | 284,883 | 726.81 | `0.00%` |
| `x86-64-v2` | `Default_Unconstrained` | 974 | 157 | 157 | 0 | 0 | 0 | 0 | 152 | 285,747 | 779.06 | `-7.19%` |
| `x86-64-v3` | `Default_Unconstrained` | 1,224 | 351 | 192 | 137 | 0 | 0 | 0 | 166 | 289,795 | **702.47** | **`+3.35%`** |
| `x86-64-v3` | `StratD_InterleaveCap1_NoGather` | **1,066** | 236 | 131 | 83 | 0 | 0 | 0 | 156 | 287,507 | **709.25** | **`+2.42%`** |
| `x86-64-v4` | `Default_Unconstrained` | 1,369 | 517 | 284 | 204 | 7 | 20 | **5** | 158 | 290,899 | 953.16 | `-31.14%` |
| `x86-64-v4` | `Counterfactual_Force512BitZMM` (`-prefer-256-bit`) | 1,558 | 698 | 333 | 109 | **234** | 20 | **5** | 158 | 292,531 | 887.75 | `-22.14%` |
| `x86-64-v4` | `StratA_Cap256_NoEVEX512_NoGather` | 1,366 | 468 | 266 | 173 | **0** | 5 | **0** | 171 | 290,755 | **751.73** | **`-3.43%`** |
| `x86-64-v4` | `StratB_PredicatedTailFold_NoGather` | **1,150** | 362 | 202 | 131 | 7 | 8 | **0** | **139** | **288,019** | 769.06 | `-5.81%` |
| `x86-64-v4` | `StratC_MinTrip64_CheckCap4` | 1,366 | 468 | 266 | 173 | 7 | 5 | **0** | 171 | 290,755 | 755.94 | `-4.01%` |
| `x86-64-v4` | `StratD_InterleaveCap1_NoGather` | **1,157** | 318 | 186 | 103 | 7 | 1 | **0** | 156 | 288,275 | 781.93 | `-7.58%` |
| `native` | `Default_Unconstrained` | 1,363 | 512 | 280 | 201 | 9 | 22 | **5** | 158 | 290,867 | 1,042.76 | `-43.47%` |
| `native` | `StratD_InterleaveCap1_NoGather` | **1,150** | 313 | 182 | 100 | 9 | 3 | **0** | 156 | 288,211 | **778.93** | **`-7.17%`** (recovers `+263.83` $\mu\text{s}$!) |

Table 3 shows the trip-count crossover ($N \in \{4, 8, 16, 32, 64, 256, 1024, 16384\}$, measured in nanoseconds per 1,000 elements across `k8_simd_numeric_dot` + `k9_slice_affine_update` + `k1_slice_bounds_iter`):

| Configuration | $N=4$ | $N=8$ | $N=16$ | $N=32$ | $N=64$ | $N=256$ | $N=1024$ | $N=16384$ |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `x86-64` (`Default`) | 4,006.4 | 2,638.5 | 2,068.5 | 1,823.7 | 1,640.7 | 1,521.4 | 1,510.9 | 1,837.1 |
| `x86-64-v3` (`Default`, `UF=4`) | **3,130.9** | 2,171.9 | 1,829.4 | 1,297.3 | 963.9 | **764.5** | 785.3 | **1,029.9** |
| `x86-64-v3` (`StratD`, `UF=1` + `no-gather`) | 4,199.6 | **1,944.1** | **1,339.3** | **1,035.7** | **920.6** | 783.5 | **752.3** | 1,061.6 |
| `x86-64-v4` (`Default`, with `vpgatherqd`) | 4,346.7 | 3,507.1 | 3,099.2 | 2,673.1 | 2,556.1 | 2,420.6 | 2,574.7 | 2,512.0 |
| `x86-64-v4` (`StratD`, `UF=1` + `no-gather`) | 4,178.5 | 2,010.4 | 1,384.2 | 1,088.6 | 954.1 | 791.2 | 768.4 | 1,058.3 |

---

### 3. AArch64 NEON (`generic` / `neoverse-n1`) vs. SVE (`neoverse-v1`) Predicated Tail-Folding

`Basis: execution (support/avx512_and_sve_analysis.json)`

On `aarch64-unknown-linux-gnu`, enabling SVE (`-C target-cpu=neoverse-v1`) under default LLVM flags inflates static instructions by `+23.0%` (`661` $\rightarrow$ `813` instructions) and object `.text` size by **`+32.6%`** (`2,592 B` $\rightarrow$ `3,436 B`) because `LoopVectorize` emits scalable SVE main loops followed by fixed-width NEON and scalar epilogue loops. Enabling SVE `whilelo` predicated tail-folding with `UF=1` (`StratE_PredicatedTail_UF1`: `-C llvm-args=--tail-folding-policy=prefer-fold-tail -C llvm-args=--sve-tail-folding=all -C llvm-args=--force-vector-interleave=1`) eliminates all epilogue loops:

| AArch64 `target-cpu` | Strategy | Total Insts | NEON Insts | SVE Insts | `whilelo` Insts | Branch Insts | Object `.text` Bytes | vs. `generic` `.text` (%) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `generic` (NEON) | `Default_Unconstrained` | 661 | 99 | 0 | 0 | 110 | 2,592 | `0.0%` |
| `neoverse-n1` (NEON) | `Default_Unconstrained` | 697 | 101 | 0 | 0 | 121 | 2,828 | `+9.1%` |
| `neoverse-v1` (SVE) | `Default_Unconstrained` | 813 | 18 | 131 | 0 | 124 | 3,436 | `+32.6%` |
| `neoverse-v1` (SVE) | `StratB_PredicatedTailFold` | 652 | 8 | 68 | **4** | 109 | 2,544 | **`-1.9%`** |
| `neoverse-v1` (SVE) | `StratD_InterleaveCap1` | 651 | 5 | 38 | 0 | 119 | 2,672 | `+3.1%` |
| `neoverse-v1` (SVE) | `StratE_PredicatedTail_UF1` | **598** | **5** | **42** | **4** | **109** | **2,324** | **`-10.3%`** (`-32.4%` vs `neoverse-v1` default!) |

---

### 4. Target-CPU Vectorization Decision Table for the Verified `rustc` Backend

| Target Architecture & CPU Tier | Default Vector Register Width | Gather / Scatter Policy | Interleave Unroll Factor (`UF`) | Tail-Folding Policy | Rationale |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64` (`x86-64-v3`, AVX2) | 256-bit (`ymm`) | Disabled (`prefer-no-gather`) | `UF=1` when trip count unknown or $< 128$; `UF=2` for known $N \ge 128$ | Scalar epilogue (`dont-fold-tail`) | Avoids `VF=8, UF=4` (`min_trip=32`) branch cascades that penalize $8 \le N \le 64$ by `20%–27%`. |
| `x86_64` (`x86-64-v4` / `native`, AVX-512) | 256-bit (`+prefer-256-bit,-evex512`) unless loop has proven $N \ge 256$ and dense unit-stride loads | **Strictly disabled** (`+prefer-no-gather`) | `UF=1` when runtime checks or strided loads present; `UF=2` for dense unit-stride | Predicated `k`-mask tail-folding only for unit-stride loops without inner reductions; otherwise scalar epilogue | Prevents `3.44x` `vpgatherqd` GDS microcode penalty, eliminates 512-bit ZMM preheader frequency transitions, and suppresses strided-byte induction scalarization. |
| `aarch64` (`generic` / `neoverse-n1` / `apple-m1`, NEON) | 128-bit (`v0..v31`) | N/A | `UF=2` for dense arithmetic; `UF=1` for short slices | Scalar epilogue | Fixed 128-bit NEON has low preheader overhead (`VF=4`). |
| `aarch64` (`neoverse-v1` / SVE) | Scalable SVE (`z0..z31`) | Disabled for conditional bounds-checked indexing | `UF=1` | **`prefer-fold-tail` + `--sve-tail-folding=all`** (`whilelo`) | Native `whilelo` predicate generation shrinks code size by `-32.4%` (`3,436 B` $\rightarrow$ `2,324 B`) and eliminates multi-tier SVE $\rightarrow$ NEON $\rightarrow$ scalar epilogues. |

## Boundaries

- **AMD Zen 4 / Zen 5 AVX-512 Hardware Execution**: Runtime measurements in this package were collected on Intel Xeon hardware (where 512-bit `zmm` instructions and microcoded `vpgatherqd` incur heavy license and GDS penalties). Double-pumped 256-bit AVX-512 execution on AMD Zen 4 (`znver4`) and native 512-bit execution on Zen 5 (`znver5`) were not directly executed on physical AMD silicon.
- **Explicit Portable SIMD (`core::simd`)**: The vector-width caps and gather suppression rules above govern automatic loop and SLP vectorization of scalar Rust code; explicit 512-bit SIMD types in `core::arch::x86_64` must still lower to `zmm` instructions when target features permit.

## Evidence

- **Reproducible sweep harness and datasets**:
  - `support/run_avx512_vector_policy_sweep.py`
  - `support/avx512_policy_matrix.csv` (18 rows of `x86_64` CPU $\times$ strategy instruction, register-width, gather, branch, size, and runtime measurements)
  - `support/avx512_trip_count_sweep.csv` (120 rows across $N \in \{4, \dots, 16384\}$)
  - `support/avx512_and_sve_analysis.json` (per-kernel `k1`–`k8` instruction breakdowns, per-kernel runtimes, and AArch64 `generic` vs. `neoverse-v1` SVE `whilelo` tail-folding comparison)
- **Primary upstream source citations**:
  - `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):
    - `llvm/lib/Target/X86/X86.td` (`x86-64-v4` processor feature list including `FeaturePrefer256Bit` and `FeatureFastGather`)
    - `llvm/lib/Target/X86/X86TargetTransformInfo.cpp` (`X86TTIImpl::getRegisterBitWidth`, `X86TTIImpl::getMaxInterleaveFactor`, `X86TTIImpl::getGatherScatterOpCost`)
    - `llvm/lib/Transforms/Vectorize/LoopVectorize.cpp` (`--tail-folding-policy`, `--vectorizer-min-trip-count`, `--force-vector-interleave`, `--runtime-memory-check-threshold`)

## Revalidation

Run the self-contained sweep script with `rustc +1.99.1-x86_64-unknown-linux-gnu`:

```bash
python3 reports/x86-avx512-short-loop-regression-and-vector-width-profitability/support/run_avx512_vector_policy_sweep.py
```

Verify that:
1. Default `x86-64-v4` emits `5` `vpgatherqd` instructions in `k1_slice_bounds_iter` and `7` `zmm` instructions in `k6_zerocopy_endian`, slowing `k1` by $>3\times$;
2. Adding `-C target-feature=+prefer-no-gather,-evex512` eliminates all `vpgatherqd` and `zmm` instructions and recovers $>200$ $\mu\text{s}$ on `x86-64-v4` and `native`;
3. On `aarch64-unknown-linux-gnu` (`-C target-cpu=neoverse-v1`), `--tail-folding-policy=prefer-fold-tail --sve-tail-folding=all --force-vector-interleave=1` emits `4` `whilelo` instructions and reduces `.text` size by $>30\%$.
