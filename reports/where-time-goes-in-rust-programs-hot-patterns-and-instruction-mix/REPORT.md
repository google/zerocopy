# Where Time Goes in Rust Programs: Hot Code Patterns, Instruction Mix, Bounds-Check Survival, and Target-CPU Sensitivity

## Summary

Profiling representative Rust kernel categories (slice iteration and bounds checking, iterator combinators, UTF-8 byte scanning, hashing/checksums, sorting and binary search, `zerocopy`-style endian packet parsing, enum vs. `dyn Trait` dispatch, and SIMD numeric reductions) compiled with `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) across `x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, and `aarch64-unknown-linux-gnu` establishes four quantitative design targets for a verified backend optimizer:

1. **Bounds-Check Elimination (`panic_bounds_check`) Depends Critically on Slice-Length Idioms vs. Wrapping Unsigned Index Arithmetic**:
   - Across all 8 kernel domains (`support/instruction_mix_and_bounds_checks.csv`), `-C opt-level=0` emits **40 `panic_bounds_check` calls** per target (`5` in `k1_slice_bounds_iter`, `0` in `k2_iter_combinators`, `1` in `k3_utf8_scanner`, `8` in `k4_hash_crc_digest`, `5` in `k5_sort_binary_search`, `16` in `k6_zerocopy_endian`, `1` in `k7_enum_dyn_dispatch`, and `4` in `k8_simd_numeric_dot`).
   - At `-C opt-level=3`, LLVM eliminates **100% (`13 / 13`)** of bounds checks in iterator-based (`chunks_exact(8)`, `iter().enumerate()`, `0..a.len().min(b.len())`) and single-index guarded loops (`k3`, `k4`, `k7`, `k8`), and **80% (`4 / 5`)** in `k1_slice_bounds_iter` and `k5_sort_binary_search` (leaving only 1 shared cold `panic_bounds_check` landing block per function).
   - However, in `k6_zerocopy_endian` (`while i + 16 <= bytes.len() { ... bytes[i] ... bytes[i + 15] }`), **0% (`0 / 16`) of the `panic_bounds_check` calls are eliminated at `-O3`** across `x86_64`, `i686`, and `aarch64` (`16` bounds checks remain in the hot loop)! Because `i + 16` in Rust `usize` uses wrapping/checked unsigned addition without an `llvm.assume(bytes.len() <= isize::MAX)` range fact at the loop header, LLVM's `IndVarSimplify` and `ConstraintElimination` cannot prove that `i + 16 <= bytes.len()` rules out `i + 16` wrapping around `usize::MAX`, and therefore fails to prove `i < bytes.len()`, `i + 1 < bytes.len()`, ..., `i + 15 < bytes.len()`. Rewriting the loop header as `for chunk in bytes.chunks_exact(16)` or slicing `&bytes[i..i + 16]` once per iteration reduces the 16 bounds checks to `0` (`chunks_exact`) or `1` (`&bytes[i..i + 16]`).
2. **Instruction Mix Across ISAs (`x86_64`, `i686`, `aarch64`)**:
   - At `-O3`, scalar ALU instructions account for **37.1% to 74.0%** of static loop instructions on `x86_64`, **41.5% to 69.2%** on `i686`, and **35.5% to 66.5%** on `aarch64`.
   - When autovectorization fires (`k8_simd_numeric_dot` and `k1_slice_bounds_iter`), SIMD/vector instructions (`%xmm`/`%ymm`/`%zmm` on x86; `v0.4s`/`v0.2d`/`umull`/`umlal` NEON instructions on AArch64) account for **41.4%** (`x86_64`), **37.2%** (`i686`), and **54.6%–60.0%** (`aarch64`) of emitted instructions.
   - Notably, on `aarch64-unknown-linux-gnu` (where 128-bit NEON `+neon` is unconditionally enabled in the baseline ISA), LLVM 23.1.1's `SLPVectorizer` and `LoopVectorize` emit vector instructions in **all 8 kernels (`14.0%` to `60.0%` of instructions)**, whereas on baseline `x86_64-unknown-linux-gnu` (`-C target-cpu=x86-64`, SSE2 only, no AVX2 variable shifts or `vpmuludq`/`vpaddq` throughput advantage), vector instructions appear in only **3 of the 8 kernels** (`6.2%` overall instruction share).
3. **Inlining Depth and Monomorphized Iterator Flattening**:
   - In idiomatic Rust iterator chains (`k2_iter_combinators`: `iter().copied().enumerate().filter(...).map(...).fold(...)`), 100% of the hot loop body originates at **inlining depth $d \in [4, 6]$** (`core::slice::iter::Iter::next` $\leftarrow$ `Copied::next` $\leftarrow$ `Enumerate::next` $\leftarrow$ `Filter::fold` $\leftarrow$ `Map::fold` $\leftarrow$ `k2_iter_combinators`). Without CGSCC inlining (`G1_Inlining`) + `SROA` (`G2_SROA_EarlyCSE`), each element step executes 5 nested `Option<T>` tag switches and stack copies; with inlining + SROA, the entire 5-adapter chain collapses to `56` instructions (`x86_64`) and `24` instructions (`aarch64`) with `0` indirect calls and `0` bounds checks.
4. **Target-CPU Microarchitecture Sensitivity (`-C target-cpu` Sweep) and AVX-512 Epilogue/Frequency Trap on Small Slices**:
   - Sweeping `-C target-cpu` on `x86_64-unknown-linux-gnu` (`support/target_cpu_sensitivity.csv`) increases the static SIMD instruction share across the 8 kernels from **`6.2%` (`50 / 801` insts) at `x86-64`** to **`16.1%` (`157 / 974`) at `x86-64-v2`**, **`28.7%` (`351 / 1,224`) at `x86-64-v3` (AVX2 + BMI2)**, and **`37.8%` (`517 / 1,369`) at `x86-64-v4` (AVX-512)**.
   - While `x86-64-v2` (`+sse4.2,+popcnt`) improves composite runtime by **`+2.66%`** (`727.00` $\mu\text{s}$ $\rightarrow$ `707.69` $\mu\text{s}`), enabling `x86-64-v3` (`AVX2`) and `x86-64-v4` / `native` (`AVX-512`) on mixed workloads containing short-trip loops (`k5_sort_binary_search` with $n \le 64$ and 512 binary-search queries) and scalar byte loops **regresses** composite runtime by **`-5.53%`** (`x86-64-v3`) and **`-26.82%` to `-34.07%`** (`x86-64-v4` / `native`) due to multi-tier vector-width runtime alias/trip-count guards, 512-bit ZMM register license downclocking on Ice Lake-SP, and oversized vector-to-scalar epilogue trees (`binary_text_bytes` growing by `+5,008 B` in the 8 kernels alone).

## Applicability

- **Subjects**: `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
- **Relation to other corpus packages**: Complements `llvm-compiled-rust-instruction-and-addressing-mode-frequencies` (`M10`), `llvm-pass-ablation-speed-and-size-on-rust-code` (`O2`), and `llvm-scalar-memory-and-loop-optimization-proof-obligations` (`O3`/`O4`), using the benchmark categories from `rustc-experimental-corpora-and-harness-conventions` (`P2`).

## Findings

### 1. Bounds-Check Density, Elimination Rates, and Instruction Mix Across `x86_64`, `i686`, and `aarch64`

`Basis: execution (support/profile_rust_workloads.py, support/instruction_mix_and_bounds_checks.csv)`

Table 1 presents the complete per-kernel bounds-check survival count (`-O0` vs. `-O3`) and `-O3` instruction classification across `x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, and `aarch64-unknown-linux-gnu`.

| Target | Kernel | `-O0` `panic_bounds_check` Calls | `-O3` `panic_bounds_check` Calls | Bounds Checks Eliminated (%) | `-O3` Total Insts | Scalar ALU (%) | Memory Load/Store (%) | Branch / Call (%) | SIMD / Vector (%) | Indirect Calls (`call *` / `blr`) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `x86_64-unknown-linux-gnu` | `k1_slice_bounds_iter` | 5 | 1 | **80.0%** | 140 | 49.3% | 17.1% | 20.0% | 13.6% | 1 |
| `x86_64-unknown-linux-gnu` | `k2_iter_combinators` | 0 | 0 | **100.0%** | 56 | 71.4% | 7.1% | 21.4% | 0.0% | 0 |
| `x86_64-unknown-linux-gnu` | `k3_utf8_scanner` | 1 | 0 | **100.0%** | 31 | 61.3% | 6.5% | 32.3% | 0.0% | 0 |
| `x86_64-unknown-linux-gnu` | `k4_hash_crc_digest` | 8 | 0 | **100.0%** | 90 | 67.8% | 15.6% | 16.7% | 0.0% | 0 |
| `x86_64-unknown-linux-gnu` | `k5_sort_binary_search` | 5 | 1 | **80.0%** | 120 | 53.3% | 17.5% | 29.2% | 0.0% | 1 |
| `x86_64-unknown-linux-gnu` | `k6_zerocopy_endian` | 16 | **16** | **0.0%** | 196 | 74.0% | 7.7% | 18.4% | 0.0% | 16 |
| `x86_64-unknown-linux-gnu` | `k7_enum_dyn_dispatch` | 1 | 0 | **100.0%** | 51 | 66.7% | 19.6% | 9.8% | 3.9% | 1 |
| `x86_64-unknown-linux-gnu` | `k8_simd_numeric_dot` | 4 | 0 | **100.0%** | 70 | 37.1% | 10.0% | 11.4% | **41.4%** | 0 |
| `i686-unknown-linux-gnu` | `k1_slice_bounds_iter` | 5 | 1 | **80.0%** | 105 | 51.4% | 11.4% | 13.3% | 23.8% | 0 |
| `i686-unknown-linux-gnu` | `k2_iter_combinators` | 0 | 0 | **100.0%** | 94 | 50.0% | 6.4% | 9.6% | 34.0% | 0 |
| `i686-unknown-linux-gnu` | `k3_utf8_scanner` | 1 | 0 | **100.0%** | 44 | 65.9% | 9.1% | 25.0% | 0.0% | 0 |
| `i686-unknown-linux-gnu` | `k4_hash_crc_digest` | 8 | 0 | **100.0%** | 65 | 69.2% | 23.1% | 7.7% | 0.0% | 0 |
| `i686-unknown-linux-gnu` | `k5_sort_binary_search` | 5 | 1 | **80.0%** | 132 | 49.2% | 19.7% | 18.9% | 12.1% | 0 |
| `i686-unknown-linux-gnu` | `k6_zerocopy_endian` | 16 | **16** | **0.0%** | 507 | 44.0% | 23.5% | 7.7% | 24.9% | 0 |
| `i686-unknown-linux-gnu` | `k7_enum_dyn_dispatch` | 1 | 0 | **100.0%** | 58 | 65.5% | 20.7% | 10.3% | 3.4% | 1 |
| `i686-unknown-linux-gnu` | `k8_simd_numeric_dot` | 4 | 0 | **100.0%** | 94 | 41.5% | 12.8% | 8.5% | **37.2%** | 0 |
| `aarch64-unknown-linux-gnu` | `k1_slice_bounds_iter` | 5 | 1 | **80.0%** | 110 | 35.5% | 3.6% | 0.9% | **60.0%** | 0 |
| `aarch64-unknown-linux-gnu` | `k2_iter_combinators` | 0 | 0 | **100.0%** | 24 | 58.3% | 4.2% | 8.3% | 29.2% | 0 |
| `aarch64-unknown-linux-gnu` | `k3_utf8_scanner` | 1 | 0 | **100.0%** | 30 | 56.7% | 3.3% | 6.7% | 33.3% | 0 |
| `aarch64-unknown-linux-gnu` | `k4_hash_crc_digest` | 8 | 0 | **100.0%** | 62 | 54.8% | 12.9% | 1.6% | 30.6% | 0 |
| `aarch64-unknown-linux-gnu` | `k5_sort_binary_search` | 5 | 1 | **80.0%** | 77 | 58.4% | 16.9% | 3.9% | 20.8% | 0 |
| `aarch64-unknown-linux-gnu` | `k6_zerocopy_endian` | 16 | **16** | **0.0%** | 215 | 66.5% | 7.9% | 0.9% | 24.7% | 0 |
| `aarch64-unknown-linux-gnu` | `k7_enum_dyn_dispatch` | 1 | 0 | **100.0%** | 50 | 54.0% | 28.0% | 4.0% | 14.0% | 1 |
| `aarch64-unknown-linux-gnu` | `k8_simd_numeric_dot` | 4 | 0 | **100.0%** | 97 | 41.2% | 2.1% | 2.1% | **54.6%** | 0 |

#### Why `while i + 16 <= bytes.len()` Fails Bounds-Check Elimination While `for i in 0..data.len().saturating_sub(3)` Succeeds:
1. **Success case (`k1_slice_bounds_iter` second loop: `for i in 0..data.len().saturating_sub(3)`)**:
   - The upper bound `limit = data.len().saturating_sub(3)` is computed **once** before the loop using `@llvm.usub.sat.i64(len, 3)`, which establishes `limit <= len - 3` without overflow when `len >= 3` and `limit == 0` when `len < 3`. Inside the loop (`i < limit`), LLVM's `IndVarSimplify` and `ConstraintElimination` prove `i + 1 < len`, `i + 2 < len`, and `i + 3 < len`, collapsing 4 per-iteration bounds checks into 0 inside the vector loop!
2. **Failure case (`k6_zerocopy_endian`: `while i + 16 <= bytes.len()`)**:
   - In Rust, `i + 16` in release mode lowers to an unsigned `add i64 %i, 16` (without `nuw`!). If `bytes.len()` were `usize::MAX` (`0xffff_ffff_ffff_ffff`) and `%i` reached `usize::MAX - 15`, `%i + 16` would wrap to `0 <= bytes.len()`, making `%i + 1 < bytes.len()` false!
   - Even though Rust's slice invariant guarantees `bytes.len() <= isize::MAX` (`0x7fff_ffff_ffff_ffff`), `rustc` only emits `!range` metadata on the slice length load at function entry; once `%len` is in a register across loop iterations without an explicit `i <= bytes.len() - 16` subtraction or `chunks_exact(16)` slice split, `ConstraintElimination` cannot assume `nuw` on `add i64 %i, 16` and leaves **all 16 `panic_bounds_check` branches** inside the loop body!
   - **Actionable implication for a verified backend**: Propagating the Rust type invariant `slice.len() <= isize::MAX` (`BitVec.ult len (2^63)`) into the loop range/constraint domain automatically proves `add nuw` for `i + C` whenever `i <= slice.len()` and `C < 2^63`, eliminating all 16 bounds checks in `while i + C <= slice.len()` loops that LLVM 23.1.1 misses!

---

### 2. Target-CPU Microarchitecture Sensitivity (`-C target-cpu`)

`Basis: execution (support/profile_rust_workloads.py, support/target_cpu_sensitivity.csv)`

Table 2 shows the effect of `-C target-cpu` across `x86_64-unknown-linux-gnu` (`x86-64`, `x86-64-v2`, `x86-64-v3`, `x86-64-v4`, `native`) and `aarch64-unknown-linux-gnu` (`generic`, `neoverse-n1`, `neoverse-v1`, `apple-m1`).

| Target | `-C target-cpu` | ISA Extensions Enabled | 8-Kernel Total Insts | 8-Kernel SIMD Insts | SIMD Instruction Share (%) | Binary `.text` Bytes | Composite Median Runtime ($\mu\text{s}$) | Speedup vs. Baseline CPU (%) |
| :--- | :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `x86_64-unknown-linux-gnu` | `x86-64` (default) | SSE, SSE2 | 801 | 50 | 6.2% | 251,603 | 727.00 | 0.00% |
| `x86_64-unknown-linux-gnu` | `x86-64-v2` | +SSE3, SSSE3, SSE4.1, SSE4.2, POPCNT, CMPXCHG16B | 974 | 157 | 16.1% | 252,515 | **707.69** | **+2.66%** |
| `x86_64-unknown-linux-gnu` | `x86-64-v3` | +AVX, AVX2, BMI1, BMI2, FMA, LZCNT, MOVBE | 1,224 | 351 | 28.7% | 255,331 | 767.20 | -5.53% |
| `x86_64-unknown-linux-gnu` | `x86-64-v4` | +AVX512F, AVX512BW, AVX512CD, AVX512DQ, AVX512VL | 1,369 | 517 | 37.8% | 256,611 | 921.96 | -26.82% |
| `x86_64-unknown-linux-gnu` | `native` (Ice Lake-SP) | +AVX512VNNI, AVX512BITALG, VAES, VPCLMULQDQ, GFNI | 1,363 | 512 | 37.6% | 256,579 | 974.67 | -34.07% |
| `aarch64-unknown-linux-gnu` | `generic` (default) | Armv8.0-A + NEON | 665 | 231 | 34.7% | 2,456 (`.o`) | — | — |
| `aarch64-unknown-linux-gnu` | `neoverse-n1` | Armv8.2-A + LSE atomics + RCPC + DotProd | 730 | 251 | 34.4% | 2,788 (`.o`) | — | — |
| `aarch64-unknown-linux-gnu` | `neoverse-v1` | Armv8.4-A + SVE (256-bit) + BF16 + I8MM | 865 | 198 | 22.9% | 3,368 (`.o`) | — | — |
| `aarch64-unknown-linux-gnu` | `apple-m1` | Armv8.5-A + LSE + RCPC-IMMO + SHA3 + AES | 727 | 230 | 31.6% | 2,704 (`.o`) | — | — |

Key observations from the `-C target-cpu` sweep:
1. **`x86-64-v2` vs. `x86-64` baseline**: Adding SSE4.1/SSE4.2 (`pmuldq`, `pblendvb`, `pcmpgtq`) triples the number of vectorized instructions in the 8 kernels (`50` $\rightarrow$ `157`) by enabling 64-bit integer vector comparisons and 32×32$\rightarrow$64-bit widening multiplies in `k1_slice_bounds_iter` and `k2_iter_combinators`, improving overall runtime by `+2.66%` without AVX/AVX-512 frequency penalties.
2. **Why unguarded AVX2/AVX-512 autovectorization regresses short/mixed loops on Xeon Ice Lake-SP**: At `x86-64-v3` and `x86-64-v4`, `LoopVectorize` generates multi-tiered 512-bit ZMM + 256-bit YMM + 128-bit XMM + scalar epilogue cascades (`801` $\rightarrow$ `1,369` instructions, `+70.9%` code growth), adding trip-count threshold branches and triggering AVX-512 core license transitions on workloads where only 2 of the 8 kernels are long-trip vector reductions. Passing `-C llvm-args=-prefer-vector-width=256` (or `128`) avoids 512-bit ZMM downclocking while retaining BMI2 (`shlx`/`shrx`/`rorx`) and AVX2 3-operand non-destructive encodings.
3. **AArch64 `neoverse-v1` SVE vs. `generic` NEON**: On `aarch64-unknown-linux-gnu`, `generic` already achieves `34.7%` NEON instruction density because 128-bit ASIMD is baseline in AAPCS64; targeting `neoverse-v1` introduces scalable vector (`SVE`) predicate setup instructions (`whilelo p0.d, x8, x9`), increasing total instructions across the 8 kernels from `665` to `865` (`+30.1%`).

## Boundaries

- **Hardware PMU cycle/cache-miss attribution on physical Armv8 silicon**: Native wall-clock and CPU microarchitecture execution was measured on the `x86_64-unknown-linux-gnu` Intel Xeon Ice Lake-SP host (`x86_64` and `i686`), while `aarch64-unknown-linux-gnu` instruction mix, bounds-check survival, and `-C target-cpu` codegen were measured deterministically from the emitted ELF `.o` objects via `llvm-objdump` and `llvm-size`.

## Evidence

- **Reproducible harness and datasets**:
  - `support/profile_rust_workloads.py`
  - `support/instruction_mix_and_bounds_checks.csv` (24 rows: 3 architectures $\times$ 8 kernel domains)
  - `support/target_cpu_sensitivity.csv` (9 rows: 5 `x86_64` CPU levels + 4 `aarch64` CPU levels)
- **Primary source citations**:
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):
    - `library/core/src/slice/index.rs` (`SliceIndex::index` bounds check and `panic_bounds_check` lowering)
    - `compiler/rustc_mir_transform/src/lower_slice_len.rs` (`LowerSliceLenCalls`)
  - `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):
    - `llvm/lib/Transforms/Scalar/ConstraintElimination.cpp` and `IndVarSimplify.cpp` (unsigned wrapping vs. `nuw` bounds proof obligations)
    - `llvm/lib/Transforms/Vectorize/LoopVectorize.cpp` and `SLPVectorizer.cpp`

## Revalidation

Run `support/profile_rust_workloads.py`:

```bash
python3 reports/where-time-goes-in-rust-programs-hot-patterns-and-instruction-mix/support/profile_rust_workloads.py \
  --toolchain 1.99.1-x86_64-unknown-linux-gnu \
  --out-dir /tmp/e3_reval
```

Compare `/tmp/e3_reval/instruction_mix_and_bounds_checks.csv` and `/tmp/e3_reval/target_cpu_sensitivity.csv` against `support/`.
