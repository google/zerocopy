# Real `rustc` Ecosystem Vectorization Census, Floating-Point Reduction Semantics, and Xeon AVX-512 Silicon Reality

## Summary

Compiling **`7` real multi-module Rust ecosystem crates** (`miniz_oxide 0.9.1`, `memchr 2.8.3`, `crc32fast 1.5.5`, `base64 0.23.1`, `serde_json 1.0.154`, `regex-automata 0.4.19`, `jpeg-decoder 0.1.22`) across **`4` x86-64 CPU tiers** (`x86-64`, `x86-64-v3`, `x86-64-v4`, and `x86-64-v4` with `-C target-feature=-prefer-256-bit`) on real **`rustc 1.99.1` (`LLVM 23.1.1`)**, paired with native **`Intel Xeon` (Ice Lake-SP, Family 6 Model 106 Stepping 6, AVX-512F/BW/DQ/VL/CD/VNNI/VPOPCNTDQ/VBMI2) silicon execution** of **`15` numeric/FP/integer kernels × `6` trip counts (`N = 8..262,144`) × `4` tiers** (median of `9` interleaved rounds pinned via `taskset -c 12`) plus exact ULP/bit-level numerical auditing and static-only `aarch64` NEON/`+sve` disassembly, establishes five empirically grounded findings for verified-compiler vectorization and floating-point semantics:

1. **Ecosystem Vectorization Is Dominated by Straight-Line SLP (`3.6×–3.9×` Over LoopVectorize) and Hand-Written `std::arch` (`40.6%` at `x86-64-v3`), Not Classic Loop Auto-Vectorization:**
   - Across `1,493` compiled functions at `x86-64-v3`, **`190` (`12.73%`)** emit vector LLVM IR totaling **`4,788` vector instructions** (`4,565` compute/memory excluding `phi`/`freeze`).
   - Straight-line **SLP vectorization outnumbers LoopVectorize by `3.6×–3.9×` across every CPU tier** (`83` vs. `22` = `3.77×` on `x86-64`; **`113` vs. `29` = `3.90×` on `x86-64-v3`**; **`114` vs. `31` = `3.68×` on `x86-64-v4`**; `115` vs. `32` = `3.59×` on `x86-64-v4-zmm512`), with `108 / 113` (`95.6%`) of `x86-64-v3` SLP wins consisting of contiguous store coalescing (`stores_slp`).
   - LoopVectorize succeeds on only **`29 / 349` (`8.31%`)** of candidate loops at `x86-64-v3` (`6.23%`–`9.20%` across all tiers), blocked primarily by unidentifiable loop-live-out reductions (`171`), non-vectorizable calls (`144`), non-countable trip counts (`107`), missing induction variables (`80`), and early-exit control flow (`77`–`79`).
   - **Hand-written `std::arch` kernels** (`memchr`, `crc32fast`, `base64`, and `regex-automata`'s inlined `memchr` prefilters) account for **`1,942 / 4,788` (`40.56%`)** of all vector IR instructions at `x86-64-v3` (`52.58%` on baseline `x86-64`). Branchy parsers (`serde_json`) emit only `31` vector IR instructions across `165` functions (`2.42%`, `0` LoopVectorize hits).
2. **Pre-Legalization LLVM IR Emits Massive `>512`-Bit and Non-Power-of-Two Vectors, While `prefer-256-bit` Gates `512`-Bit Adoption:**
   - Even at `x86-64-v3` (`256`-bit hardware), LLVM emits **`133` `>512`-bit pre-legalization vector instructions**, rising to **`303`** on default `x86-64-v4` and **`517`** on `x86-64-v4-zmm512`—including non-power-of-two IR vectors such as **`<13 x i64>` (`832`-bit)** and `<5 x i8>` in `regex-automata`, **`<96 x i8>` (`768`-bit)** and `<192 x i8>` (`1,536`-bit) in `base64`, `<32 x float>` (`1,024`-bit) and **`<241 x i16>` (`3,856`-bit) / `<497 x i16>` (`7,952`-bit)** masked loads in `jpeg-decoder`, and `<64 x i64>` (`4,096`-bit) in `miniz_oxide` and `base64`. Any IR-level verified vector semantics that assumes fixed hardware widths (`<= 256`/`<= 512` bits) or power-of-two lane counts will reject real LLVM output.
   - Disabling LLVM's default `x86-64-v4` **`prefer-256-bit`** heuristic (`-C target-feature=-prefer-256-bit`) shifts `512`-bit vector IR instructions **`6.29×` upward (`385 -> 2,420`)** while cutting `256`-bit instructions from `2,381 -> 854`—and on real Ice Lake-SP silicon exposes why LLVM enables `prefer-256-bit` by default.
3. **Refutation of x86-64 Ordered-SIMD Floating-Point Speedup:**
   - On x86-64 across all four tiers (`SSE2`, `AVX2`, `AVX-512`, `AVX-512 ZMM512`), `core::intrinsics::simd::simd_reduce_add_ordered` (`k02` 4-lane and `k03` 8-lane) lowers exclusively to **serial scalar `addsd` / `vaddsd`** (`ymm = 0`, `zmm = 0`, `packed_fp = 0`), executing at **`0.98×–1.01×`** vs. scalar `k01` for `N >= 1,024` (`0.80×–0.84×` slower at `N = 32` due to chunking overhead). Although `100%` bit-exact with left-to-right IEEE-754 across all tiers and `N`, x86-64 has no ordered horizontal vector reduction instruction—in sharp contrast to static-only `aarch64` `+sve` disassembly, which emits `2`/`4`/`6` **`fadda`** instructions on `k01`/`k02`/`k03` (`runtime not measured on silicon`).
4. **Reassociated FP Yields `12.3×–15.2×` L1/L2 Speedups (`4.8×–5.1×` L3/DRAM) at the Cost of Cross-CPU Bit Divergence and Catastrophic Cancellation Shifts—While Explicit Source Trees Preserve Cross-Tier Determinism:**
   - Breaking strict left-to-right IEEE-754 ordering via `fadd_fast` or explicit multi-accumulator trees (`tree4`/`tree8`/`tree16`) achieves **`12.25×–15.18×` (`109.60 GB/s`)** for `f64` sum at `N = 1,024` and **`12.87×–16.21×` (`112.70 GB/s`, `15.24×` for `k09` on `v4-zmm512`)** for `f32` FMA dot product (`4.67×–5.13×` at `N = 262,144` once memory-bound).
   - **Exact ULP/bit divergence:** `fadd_fast`/`fmul_fast` produces **CPU-tier-dependent bit patterns** on identical well-conditioned inputs (`f64_well` at `N = 262,144`: `2` ULPs on SSE2 vs. `1` ULP on AVX2/AVX-512; `f32_dot_well` at `N = 262,144`: `71` ULPs on SSE2 vs. `76` ULPs on AVX2/AVX-512; and **three distinct bit patterns** at `N = 16,384`: `4` vs. `5` vs. `8` ULPs). Under period-4 cancellation (`[1e16, 1.0, -1e16, 1.0, ...]`, `N = 262,144`), strict IEEE-754 yields **`1.0`**, `fadd_fast` yields **`131,072.0`** (`7.656 × 10^16` ULPs from IEEE-754, matching exact mathematical sum), and `tree4`/`tree8`/`tree16` yield **`0.0`** (`4.607 × 10^18` ULPs); for `f32_dot_cancel4`, ordered yields **`1.0`**, `reassoc_fma` yields **`131,072.0`**, and `tree16_fma` yields **`49,152.0`**. Crucially, explicit source-level reduction trees (`tree4`/`tree8`/`tree16`/`tree16_fma`) are **`100%` bit-identical across all four CPU tiers**, making explicit tree reduction—not `fast`-math flags—the clean contract for verified high-throughput FP reductions.
   - **Silent `f32::mul_add` libcall trap:** On baseline `x86-64` without `+fma`, `f32::mul_add` in `k10_f32_dot_tree16_fma` emits `16` unrolled indirect `callq *%r13` calls to `libm` **`fmaf@GOTPCREL`** per iteration—running **`36.04×` slower** (`2.5583 ns/elem`, `3.13 GB/s`) than `x86-64-v3` hardware `vfmadd231ps` (`0.0710 ns/elem`, `112.70 GB/s`) at `N = 1,024`, and `2.24×` slower than ordered scalar `a * b + acc` on `x86-64`.
   - **Zero-reassociation elementwise FP:** `k11_f64_axpy_elementwise` (`y[i] = a * x[i] + y[i]`) reaches **`200.32 GB/s`** (`1.56×` over SSE2 at `N = 1,024`, `1.64×` at `N = 16,384`) with **`0` bit differences** across every element, trip count, and CPU tier.
5. **AVX-512 Silicon Reality Is Sharply Workload-Dependent (Opmask Wins vs. ZMM L2/L3 Bandwidth Regressions vs. `vpgatherqd` Slowdowns):**
   - **Genuine AVX-512 wins:** `k13_u8_byte_count` leverages AVX-512BW compare-to-opmask (`vpcmpeqb -> %k0..%k3` + `vpmovm2d`) to beat `x86-64-v3` even at `N = 8` (`1.16×` vs. `0.99×`) and `N = 32` (`1.62×` vs. `1.53×`), scaling to **`3.80×` (`29.79 GB/s`)** at `N = 16,384` and **`3.33×` (`26.10 GB/s`)** at `N = 262,144` under `x86-64-v4-zmm512`.
   - **Why LLVM's `prefer-256-bit` protects Ice Lake-SP:** Forcing full `512`-bit ZMM loops (`-prefer-256-bit`) causes severe **`1.46×–2.00×` L2/L3 bandwidth regressions** at `N = 16,384` relative to default `x86-64-v4` on `k04` (`52.13` vs. `90.18 GB/s`, `1.73×` slower), `k09` (`59.64` vs. `87.29 GB/s`, `1.46×` slower), `k11` AXPY (`66.38` vs. `132.83 GB/s`, `2.00×` slower; `1.76×` slower even at `N = 1,024`), and `k12` `u32` sum (`49.94` vs. `89.21 GB/s`, `1.79×` slower; `1.83×` slower at `N = 262,144`).
   - **`vpgatherqd` anti-optimization:** On `k15_u32_indexed_gather_sum`, LLVM leaves baseline `x86-64` scalar (`0` vector insns), emits AVX2 non-gather loads on `x86-64-v3`, and emits `5`–`9` **`vpgatherqd (%rdi,%zmm*,4), %ymm* {%k1}`** instructions on `x86-64-v4` / `v4-zmm512`—making AVX-512 **`1.27×–3.49×` slower** than scalar `x86-64` across every single trip count `N = 8..262,144` (`3.27×` slower at `N = 1,024`, `3.49×` at `N = 8`, `3.38×` at `N = 32` `v4-zmm512`).

## Applicability

This report documents empirical compiler-IR, remark, disassembly, numerical-accuracy, and native-silicon runtime measurements collected on `2026-11-20` against pinned upstream sources:

- **Compiler toolchain (`rust-lang/rust`, `[real measurement]`):**
  - `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, commit date `2026-10-13`, bundled **`LLVM 23.1.1`**, `cargo 1.99.1`), host triple `x86_64-unknown-linux-gnu`, using bundled `llvm-objdump` from the same toolchain sysroot.
- **Part A offline ecosystem crate corpus (`7` pinned crates compiled with `cargo +1.99.1 rustc --offline --release -C codegen-units=1 -C debuginfo=line-tables-only -C remark="loop-vectorize slp-vectorizer" --emit=llvm-ir`):**
  - `miniz_oxide 0.9.1` (`Frommi/miniz_oxide@4e582392df3a739d2b0dfd2c537dc33e8942be38`, `14` `.rs` files, `0` `std::arch` files).
  - `memchr 2.8.3` (`BurntSushi/memchr@5fdb40c054e1fff359a2f7bdf7f87a13b34b465d`, `45` `.rs` files, `9` `std::arch` files, `11` `#[target_feature]` files).
  - `crc32fast 1.5.5` (`srijs/rust-crc32fast@8a93d2a70c00ab3e72beda42014b18fad8e496ea`, `7` `.rs` files, `2` `std::arch` files).
  - `base64 0.23.1` (`marshallpierce/rust-base64@069bf7067b949f5c0a92b6ceb82492920502f2c2`, `22` `.rs` files, `1` `std::arch` file).
  - `serde_json 1.0.154` (`serde-rs/json@20572a6d066958542d79cdd6cf1a7cd9f0c8e1f8`, `37` `.rs` files, `0` `std::arch` files).
  - `regex-automata 0.4.19` (`rust-lang/regex@4226f214c56e584304520adb9080bcc4c792390e`, `72` `.rs` files, `0` direct `std::arch` files; inlines `memchr` prefilters).
  - `jpeg-decoder 0.1.22` (`image-rs/jpeg-decoder@3bf223f7dcaa03cf0422e9e79eaf936ff406686f`, `11` `.rs` files, `0` `std::arch` files).
- **Part B native execution host (`[real measurement]`):**
  - **CPU:** `GenuineIntel`, `Intel(R) Xeon(R) CPU @ 2.60GHz`, **Family `6`, Model `106`, Stepping `6` (Intel Xeon Ice Lake-SP / Sunny Cove server microarchitecture)**, `96` logical CPUs (`48` physical cores across `2` sockets), L1d `48 KiB`/core (`2.3 MiB` total), L1i `32 KiB`/core (`1.5 MiB` total), L2 `1.25 MiB`/core (`60 MiB` total), L3 `54 MiB`/socket (`108 MiB` total).
  - **Hardware SIMD/bit extensions present:** `sse`, `sse2`, `sse4_1`, `sse4_2`, `avx`, `avx2`, `fma`, `bmi1`, `bmi2`, `f16c`, `pclmulqdq`, `popcnt`, `aes`, `vaes`, `vpclmulqdq`, `gfni`, `sha_ni`, `avx512f`, `avx512bw`, `avx512cd`, `avx512dq`, `avx512vl`, `avx512ifma`, `avx512vbmi`, `avx512_vbmi2`, `avx512_vnni`, `avx512_bitalg`, `avx512_vpopcntdq`.
  - **Execution protocol:** All four x86-64 binaries compiled with `RUSTC_BOOTSTRAP=1 rustc +1.99.1 -C opt-level=3 -C codegen-units=1 -C target-cpu=<tier>` (plus `-C target-feature=-prefer-256-bit` for `x86-64-v4-zmm512`) and executed pinned to logical core `12` (`taskset -c 12`) with `1` warmup round followed by `9` interleaved measurement rounds across all `15` kernels and `6` trip counts (`N ∈ {8, 32, 128, 1024, 16384, 262144}`).
- **Static-only cross-architecture probe:** `aarch64-unknown-linux-gnu` (`default NEON` and `-C target-feature=+sve`) was cross-compiled strictly via `--emit=asm` to inspect instruction lowering (`fadda`, `fmla`, `z*`/`v*` registers); **runtime was NOT measured on AArch64 silicon**.
- **Verification architecture context (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Interprets how real-world LLVM vectorization idioms, width legalization, and FP reassociation contracts constrain verified-compiler translation validation and certificate-checking architectures (complementing `rust-llvm-o3-loop-and-slp-vectorization-idiom-census`, `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`, `x86-avx512-short-loop-regression-and-vector-width-profitability`, and `hybridtrace-vectorization-slp-and-loop-certificate-library`).

## Findings

### 1. Part A: Real Ecosystem Vectorization Census (`7` Crates × `4` CPU Tiers on `rustc 1.99.1` / `LLVM 23.1.1`)

`Basis: execution (support/e2_7_real_vectorization_and_fp_silicon.py, support/e2_7_real_vectorization_and_fp_silicon_summary.json, live cargo +1.99.1 rustc --emit=llvm-ir + LLVM optimization remarks)`

Compiling all `7` crates at `--release -C codegen-units=1 -C debuginfo=line-tables-only` and scanning every `define` body in the emitted `.ll` IR—while attributing each vectorized function to either `handwritten_std_arch` (via DWARF `!DIFile`/`!DILocation` inlining chains referencing `core_arch`/`stdarch`/`arch/x86`/`pclmulqdq`/`engine/simd` or `@llvm.x86.*` intrinsics) or `compiler_autovec_slp`—yields the complete four-tier census below.

#### Aggregate Four-Tier Vectorization Profile Across All `7` Crates

| Metric | `x86-64` (SSE2) | `x86-64-v3` (AVX2+FMA) | `x86-64-v4` (AVX-512 default) | `x86-64-v4-zmm512` (`-prefer-256-bit`) |
| :--- | ---: | ---: | ---: | ---: |
| Total LLVM functions (`define`) | `1,507` | `1,493` | `1,493` | `1,493` |
| Functions with vector IR (`%`) | `159` (`10.55%`) | `190` (`12.73%`) | `192` (`12.86%`) | `192` (`12.86%`) |
| Total vector IR instructions | `3,269` | `4,788` | `5,080` | `5,721` |
| Vector compute/mem (excl. `phi`/`freeze`) | `3,160` | `4,565` | `4,830` | `5,482` |
| **Width `<= 128`-bit** (`<128` / `=128`) | `2,649` (`816` / `1,833`) | `2,147` (`941` / `1,206`) | `2,011` (`894` / `1,117`) | `1,930` (`870` / `1,060`) |
| **Width `256`-bit** | `469` | `2,268` | `2,381` | `854` |
| **Width `512`-bit** | `124` | `240` | **`385`** | **`2,420`** (`6.29×`) |
| **Width `> 512`-bit (pre-legalization)** | `27` | `133` | `303` | **`517`** |
| Hand-written `std::arch` fns / instrs (`%`) | `46` / `1,719` (`52.58%`) | `39` / **`1,942` (`40.56%`)** | `39` / `1,942` (`38.23%`) | `39` / `1,938` (`33.88%`) |
| Compiler auto-vec / SLP fns / instrs (`%`) | `113` / `1,550` (`47.42%`) | `151` / `2,846` (`59.44%`) | `153` / `3,138` (`61.77%`) | `153` / `3,783` (`66.12%`) |
| **LoopVectorize success / missed (rate)** | `22` / `331` (`6.23%`) | **`29` / `320` (`8.31%`)** | `31` / `316` (`8.93%`) | `32` / `316` (`9.20%`) |
| **SLPVectorizer success / missed (rate)** | `83` / `909` (`8.37%`) | **`113` / `928` (`10.85%`)** | **`114` / `905` (`11.19%`)** | `115` / `900` (`11.33%`) |
| **SLP : LoopVectorize win ratio** | **`3.77×`** | **`3.90×`** | **`3.68×`** | **`3.59×`** |
| IR family: `shuffle`/`extract`/`insert` | `791` (`24.2%`) | `1,650` (`34.5%`) | `1,650` (`32.5%`) | `2,439` (`42.6%`) |
| IR family: `load`/`store` | `1,015` (`31.0%`) | `1,163` (`24.3%`) | `1,214` (`23.9%`) | `1,081` (`18.9%`) |
| IR family: `int_arith_bitwise` | `785` (`24.0%`) | `1,103` (`23.0%`) | `1,246` (`24.5%`) | `1,231` (`21.5%`) |
| IR family: `icmp`/`fcmp`/`select` | `333` | `303` | `322` | `313` |
| IR family: `x86_target_intrinsic` | `142` | `226` | `226` | `226` |
| IR family: `fp_arith` (100% `jpeg-decoder`) | `68` | `73` | `73` | `73` |
| IR family: `vector_reduce` | `26` | `45` | `50` | `50` |
| IR family: `masked_load/store/gather/scatter` | `0` | `2` | `49` | `69` |

*Note on function-count change (`1,507 -> 1,493`):* Enabling AVX2 statically at `x86-64-v3+` allows `memchr` (`43 -> 34` fns), `base64` (`44 -> 40` fns), and `regex-automata` (`1,080 -> 1,079` fns) to dead-eliminate runtime-CPUID SSE2/scalar fallback clones via `cfg!(target_feature = "avx2")` and inlining.

#### Per-Crate Vectorization Breakdown Across All `4` CPU Tiers

| Crate (Version) | Tier | Fns (Vec Fns) | Vec IR Instrs | Width (`<=128` / `256` / `512` / `>512`) | Origin (`std::arch` / Auto+SLP) | LV (`ok/miss`) | SLP (`ok/miss`) | Special Ops (`fp` / `mask` / `red` / `x86`) |
| :--- | :--- | ---: | ---: | :---: | :---: | :---: | :---: | :---: |
| **`miniz_oxide`** (`0.9.1`) | `x86-64` | `37` (`15`, `40.5%`) | `393` | `331 / 20 / 27 / 15` | `0 / 393` | `4 / 48` | `17 / 120` | `0 / 0 / 2 / 0` |
| | `x86-64-v3` | `37` (`15`, `40.5%`) | `578` | `210 / 298 / 31 / 39` | `0 / 578` | `6 / 44` | `23 / 133` | `0 / 2 / 5 / 0` |
| | `x86-64-v4` | `37` (`15`, `40.5%`) | `390` | `121 / 231 / 21 / 17` | `0 / 390` | `5 / 44` | `19 / 133` | `0 / 6 / 5 / 0` |
| | `v4-zmm512` | `37` (`15`, `40.5%`) | `263` | `78 / 31 / 134 / 20` | `0 / 263` | `5 / 44` | `19 / 133` | `0 / 5 / 5 / 0` |
| **`memchr`** (`2.8.3`) | `x86-64` | `43` (`18`, `41.9%`) | `925` | `659 / 266 / 0 / 0` | `925 / 0` | `2 / 34` | `2 / 73` | `0 / 0 / 14 / 0` |
| | `x86-64-v3` | `34` (`12`, `35.3%`) | `800` | `442 / 358 / 0 / 0` | `800 / 0` | `1 / 34` | `0 / 52` | `0 / 0 / 18 / 0` |
| | `x86-64-v4` | `34` (`12`, `35.3%`) | `800` | `442 / 358 / 0 / 0` | `800 / 0` | `1 / 34` | `0 / 52` | `0 / 0 / 18 / 0` |
| | `v4-zmm512` | `34` (`12`, `35.3%`) | `800` | `442 / 182 / 176 / 0` | `800 / 0` | `1 / 34` | `0 / 52` | `0 / 0 / 18 / 0` |
| **`crc32fast`** (`1.5.5`) | `x86-64` | `9` (`3`, `33.3%`) | `428` | `344 / 38 / 46 / 0` | `428 / 0` | `0 / 8` | `0 / 38` | `0 / 0 / 0 / 130` |
| | `x86-64-v3` | `9` (`3`, `33.3%`) | `647` | `459 / 90 / 98 / 0` | `647 / 0` | `0 / 8` | `0 / 37` | `0 / 0 / 0 / 202` |
| | `x86-64-v4` | `9` (`4`, `44.4%`) | `741` | `483 / 113 / 145 / 0` | `647 / 94` | `0 / 8` | `2 / 27` | `0 / 11 / 5 / 202` |
| | `v4-zmm512` | `9` (`4`, `44.4%`) | `741` | `483 / 113 / 145 / 0` | `647 / 94` | `0 / 8` | `2 / 27` | `0 / 11 / 5 / 202` |
| **`base64`** (`0.23.1`) | `x86-64` | `44` (`4`, `9.1%`) | `98` | `4 / 86 / 8 / 0` | `98 / 0` | `0 / 11` | `0 / 50` | `0 / 0 / 0 / 12` |
| | `x86-64-v3` | `40` (`5`, `12.5%`) | `328` | `8 / 300 / 18 / 2` | `196 / 132` | `1 / 9` | `0 / 42` | `0 / 0 / 0 / 24` |
| | `x86-64-v4` | `40` (`5`, `12.5%`) | `470` | `8 / 306 / 18 / 138` | `196 / 274` | `1 / 9` | `0 / 38` | `0 / 0 / 0 / 24` |
| | `v4-zmm512` | `40` (`5`, `12.5%`) | `726` | `8 / 172 / 278 / 268` | `196 / 530` | `1 / 9` | `0 / 34` | `0 / 0 / 0 / 24` |
| **`serde_json`** (`1.0.154`) | `x86-64` | `165` (`2`, `1.2%`) | `8` | `8 / 0 / 0 / 0` | `0 / 8` | `0 / 32` | `2 / 83` | `0 / 0 / 0 / 0` |
| | `x86-64-v3` | `165` (`4`, `2.4%`) | `31` | `31 / 0 / 0 / 0` | `0 / 31` | `0 / 32` | `4 / 86` | `0 / 0 / 0 / 0` |
| | `x86-64-v4` | `165` (`4`, `2.4%`) | `31` | `31 / 0 / 0 / 0` | `0 / 31` | `0 / 32` | `4 / 85` | `0 / 0 / 0 / 0` |
| | `v4-zmm512` | `165` (`4`, `2.4%`) | `31` | `31 / 0 / 0 / 0` | `0 / 31` | `0 / 32` | `4 / 85` | `0 / 0 / 0 / 0` |
| **`regex-automata`** (`0.4.19`) | `x86-64` | `1,080` (`106`, `9.8%`) | `864` | `840 / 24 / 0 / 0` | `268 / 596` | `10 / 169` | `57 / 474` | `0 / 0 / 0 / 0` |
| | `x86-64-v3` | `1,079` (`139`, `12.9%`) | `1,454` | `826 / 541 / 34 / 53` | `299 / 1,155` | `14 / 166` | `79 / 501` | `0 / 0 / 12 / 0` |
| | `x86-64-v4` | `1,079` (`140`, `13.0%`) | `1,655` | `852 / 582 / 130 / 91` | `299 / 1,356` | `16 / 162` | `81 / 495` | `0 / 22 / 12 / 0` |
| | `v4-zmm512` | `1,079` (`140`, `13.0%`) | `1,653` | `814 / 187 / 481 / 171` | `295 / 1,358` | `16 / 162` | `82 / 494` | `0 / 43 / 12 / 0` |
| **`jpeg-decoder`** (`0.1.22`) | `x86-64` | `129` (`11`, `8.5%`) | `553` | `463 / 35 / 43 / 12` | `0 / 553` | `6 / 29` | `5 / 71` | `68 / 0 / 10 / 0` |
| | `x86-64-v3` | `129` (`12`, `9.3%`) | `950` | `171 / 681 / 59 / 39` | `0 / 950` | `7 / 27` | `7 / 77` | `73 / 0 / 10 / 0` |
| | `x86-64-v4` | `129` (`12`, `9.3%`) | `993` | `74 / 791 / 71 / 57` | `0 / 993` | `8 / 27` | `8 / 75` | `73 / 10 / 10 / 0` |
| | `v4-zmm512` | `129` (`12`, `9.3%`) | `1,507` | `74 / 169 / 1,206 / 58` | `0 / 1,507` | `9 / 27` | `8 / 75` | `73 / 10 / 10 / 0` |

#### Key Architectural Takeaways from Part A

1. **SLP Store-Coalescing Dominance and LoopVectorize Rejection Distribution:**
   At `x86-64-v3`, SLP accounts for `113` vectorization wins (`108` `stores_slp`, `5` `general_list_slp`) vs. just `29` LoopVectorize wins (`8.31%` of `349` loop attempts). On `x86-64-v4`, `crc32fast`'s scalar slice-by-8 fallback table lookup even gets SLP-vectorized into `@llvm.masked.gather.v4i32.v4p0` (`6`), `@llvm.masked.gather.v8i32.v8p0` (`5`), and `@llvm.vector.reduce.xor.v16i32` (`5`). Meanwhile, the `1,072` `loop-vectorize (analysis)` diagnostics at `x86-64-v3` cluster tightly around Rust's control-flow and iterator structure:
   - `"value that could not be identified as reduction is used outside the loop"`: **`171`**
   - `"call instruction cannot be vectorized"`: **`144`**
   - `"could not determine number of loop iterations"`: **`107`**
   - `"loop induction variable could not be identified"`: **`80`**
   - `"Cannot vectorize early exit loop"` (+ complex writes `59`, + store without supported condition load `30`, + strided fault-only-first load `22`): **`77`** (`79` on `v4`) + `111` sub-reasons
   - `"instruction cannot be vectorized"` (`68`), `"instruction return type cannot be vectorized"` (`46`), `"Control flow cannot be substituted for a select"` (`45`), `"Loop contains an unsupported terminator"` (`36`).
2. **Pre-Legalization `>512`-Bit and Non-Power-of-Two IR Vectors:**
   LLVM's `LoopVectorize` and `SLPVectorizer` routinely construct arbitrarily wide and non-power-of-two virtual vectors before SelectionDAG legalization splits them into hardware registers. Observed top vector IR types include:
   - **Non-power-of-two lane counts:** `<13 x i64>` (`832`-bit, `60` occurrences in `regex-automata` at `v3`), `<5 x i8>` (`40`-bit, `50` occurrences in `regex-automata` at `v3`), `<96 x i8>` (`768`-bit, `7` occurrences in `base64` at `v4`), `<192 x i8>` (`1,536`-bit, `7` occurrences in `base64` at `v4-zmm512`), and extreme strided/interleaved masked loads **`<241 x i16>` (`3,856`-bit, `20` occurrences via `@llvm.masked.load.v241i16.p0` at `v4`)** and **`<497 x i16>` (`7,952`-bit, `20` occurrences via `@llvm.masked.load.v497i16.p0` at `v4-zmm512`)** in `jpeg-decoder`'s `Upsampler::new`.
   - **Wide `>512`-bit power-of-two IR vectors:** `<32 x float>` (`1,024`-bit, `19` occurrences in `jpeg-decoder`'s `color_convert_line_ycck` at `v3`/`v4`), `<128 x i8>` (`1,024`-bit CMYK inversion in `jpeg-decoder`), `<32 x i32>` (`1,024`-bit across `memchr`, `base64`, `jpeg-decoder`), `<16 x i64>` (`1,024`-bit across `miniz_oxide`, `regex-automata`), `<32 x i64>` (`2,048`-bit, `132` occurrences in `base64` at `v4`), `<64 x i32>` (`2,048`-bit), `<64 x i64>` (`4,096`-bit, `260` occurrences in `base64` and `20` in `miniz_oxide` at `v4-zmm512`), and `<128 x i32>` (`4,096`-bit in `base64` at `v3`).
   - **Design consequence for verified compilation:** Formal IR vector semantics and translation-validation checkers (e.g., `HybridTrace` / Alive2-style lane-splitting certificates) cannot hardcode `128`/`256`/`512`-bit vector sorts; they must be **width- and lane-count-polymorphic** (`Vec (n : Nat) (T : ScalarTy)`) and explicitly discharge pre-legalization vector splitting/widening.
3. **Six-Idiom Grounded Taxonomy (`I1`–`I6`):**
   Every observed vectorization event across all `7` crates falls into six concrete classes recorded in `support/e2_7_real_vectorization_and_fp_silicon_summary.json`: (`I1`) SLP contiguous stores & struct/table init (`108 / 113` SLP wins at `v3`), (`I2`) hand-written `std::arch` byte search, PCLMULQDQ folding (`@llvm.x86.pclmulqdq.{128,256,512}` = `190` calls at `v3`), and AVX2 `vpshufb`/`vpmaddubsw` base64 codecs (`40.56%` of vector IR at `v3`), (`I3`) interleaved/strided `>512`-bit pre-legalization loops (`133` -> `303` -> `517` instrs across `v3`/`v4`/`v4-zmm512`), (`I4`) associative integer & min/max reductions (`@llvm.vector.reduce.{add,or,xor,umax,umin}`, `45`–`50` instrs), (`I5`) zero-reassociation elementwise FP DSP (`73` `fp_arith` instrs, `100%` in `jpeg-decoder` YCbCr/YCCK color conversion), and (`I6`) branchy/unbounded loop barriers (`91.7%` LV rejection rate at `v3`; `serde_json` = `31` vec IR instrs total).
4. **Effect of LLVM's `prefer-256-bit` Policy on Emitted Vector IR:**
   Under default `x86-64-v4`, LLVM keeps most auto-vectorized loops at `256`-bit (`2,381` `256`-bit vs. `385` `512`-bit instructions) while selectively adopting EVEX opmasks (`49` `@llvm.masked.*` calls vs. `2` on `v3`) and `512`-bit SLP/gathers. Passing `-C target-feature=-prefer-256-bit` shifts LoopVectorize factors upward (`VF=64` appears `7` times, `VF=32` drops from `8 -> 4`), expands `512`-bit instructions **`6.29×` (`385 -> 2,420`)**, increases `>512`-bit pre-legalization vectors (`303 -> 517`), and inflates `shuffle`/`extract`/`insert` traffic by **`+47.8%` (`1,650 -> 2,439`)**—while `miniz_oxide` actually shrinks (`390 -> 263` vec instrs) as wider `512`-bit loads replace pairs of `256`-bit operations.

### 2. Part B: Native Xeon Ice Lake-SP AVX-512 Silicon Execution — Ordered-SIMD Refutation vs. Reassociated FP Speedups

`Basis: execution (support/e2_7_real_vectorization_and_fp_silicon.py, support/e2_7_real_vectorization_and_fp_silicon_summary.json, llvm-objdump -d on native x86-64 binaries, static-only rustc --target=aarch64-unknown-linux-gnu --emit=asm)`

To separate real hardware behavior from compiler cost-model speculation, Part B compiles `15` isolated `#[no_mangle] #[inline(never)] pub extern "C"` kernels at `-C opt-level=3 -C codegen-units=1` across all `4` x86-64 CPU tiers, verifies zero panic/bounds-check calls across all `60` compiled symbols via `llvm-objdump -d`, verifies exact numerical outputs and ULP distances against strict left-to-right IEEE-754 scalar execution, and executes `1` warmup round plus `9` interleaved measurement rounds pinned to logical core `12` (`taskset -c 12`) across `6` trip counts spanning L1d (`N = 8, 32, 128, 1024`), L2 (`N = 16,384`: `128 KiB` for `f64`/`f32`-dot, `384 KiB` for AXPY), and L3 (`N = 262,144`: `2 MiB` for `f64`, `6 MiB` for AXPY, `1 MiB` for `u32` sum, `256 KiB` for `u8` count). Every invariant check in `support/e2_7_real_vectorization_and_fp_silicon_summary.json` passed (`all_ordered_simd_bit_exact_with_scalar_across_all_tiers_and_N = true`, `all_f64_axpy_bit_exact_with_scalar_across_all_tiers_and_N = true`, `all_integer_kernels_exact_across_all_tiers_and_N = true`, `all_part_b_kernels_zero_panic_calls_in_disasm = true`).

#### Complete `llvm-objdump` Machine-Instruction Audit (`15` Kernels × `4` x86-64 Tiers)

| Kernel | `x86-64` (`tot / xmm / pfp / sfp / pint / maxW`) | `x86-64-v3` (`tot / ymm / pfp / sfp / fma / maxW`) | `x86-64-v4` (`tot / ymm / zmm / k / fma / gath / maxW`) | `v4-zmm512` (`tot / ymm / zmm / k / fma / gath / maxW`) |
| :--- | :---: | :---: | :---: | :---: |
| `k01_f64_sum_ordered_scalar` | `54 / 12 / 0 / 9 / 0 / 64b` | `54 / 0 / 0 / 9 / 0 / 64b` | `54 / 0 / 0 / 0 / 0 / 0 / 64b` | `54 / 0 / 0 / 0 / 0 / 0 / 64b` |
| `k02_f64_sum_ordered_simd_chunk4` | `97 / 38 / 0 / 21 / 0 / 64b` | `102 / 0 / 0 / 29 / 0 / 64b` | `102 / 0 / 0 / 0 / 0 / 0 / 64b` | `102 / 0 / 0 / 0 / 0 / 0 / 64b` |
| `k03_f64_sum_ordered_simd_chunk8` | `78 / 28 / 0 / 17 / 0 / 64b` | `95 / 0 / 0 / 33 / 0 / 64b` | `95 / 0 / 0 / 0 / 0 / 0 / 64b` | `95 / 0 / 0 / 0 / 0 / 0 / 64b` |
| `k04_f64_sum_reassoc_fadd_fast` | `53 / 13 / 3 / 2 / 0 / 128b` | `83 / 10 / 10 / 3 / 0 / 256b` | `83 / 10 / 0 / 0 / 0 / 0 / 256b` | `87 / 4 / 12 / 0 / 0 / 0 / 512b` |
| `k05_f64_sum_reassoc_tree4` | `114 / 41 / 10 / 12 / 0 / 128b` | `99 / 12 / 9 / 12 / 0 / 256b` | `128 / 18 / 0 / 11 / 0 / 0 / 256b` | `128 / 18 / 0 / 11 / 0 / 0 / 256b` |
| `k06_f64_sum_reassoc_tree8` | `146 / 73 / 22 / 12 / 0 / 128b` | `112 / 20 / 18 / 12 / 0 / 256b` | `104 / 5 / 10 / 0 / 0 / 0 / 512b` | `104 / 5 / 10 / 0 / 0 / 0 / 512b` |
| `k07_f64_sum_reassoc_tree16` | `111 / 61 / 10 / 20 / 0 / 128b` | `140 / 40 / 38 / 12 / 0 / 256b` | `126 / 0 / 26 / 0 / 0 / 0 / 512b` | `126 / 0 / 26 / 0 / 0 / 0 / 512b` |
| `k08_f32_dot_ordered` | `52 / 18 / 0 / 10 / 0 / 64b` | `64 / 0 / 0 / 18 / 0 / 64b` | `64 / 0 / 0 / 0 / 0 / 0 / 64b` | `64 / 0 / 0 / 0 / 0 / 0 / 64b` |
| `k09_f32_dot_reassoc_fma` | `52 / 21 / 6 / 2 / 0 / 128b` | `70 / 12 / 11 / 3 / 6 / 256b` | `70 / 12 / 0 / 0 / 6 / 0 / 256b` | `81 / 5 / 13 / 0 / 6 / 0 / 512b` |
| `k10_f32_dot_tree16_fma` | `229 / 122 / 0 / 16 / 0 / 64b`* | `150 / 22 / 10 / 25 / 19 / 256b` | `147 / 1 / 20 / 0 / 18 / 0 / 512b` | `147 / 1 / 20 / 0 / 18 / 0 / 512b` |
| `k11_f64_axpy_elementwise` | `70 / 24 / 4 / 6 / 0 / 128b` | `97 / 17 / 10 / 10 / 0 / 256b` | `97 / 17 / 0 / 0 / 0 / 0 / 256b` | `97 / 4 / 13 / 0 / 0 / 0 / 512b` |
| `k12_u32_wrapping_sum_reduce` | `46 / 12 / 0 / 0 / 9 / 128b` | `75 / 8 / 0 / 0 / 0 / 256b` | `75 / 8 / 0 / 0 / 0 / 0 / 256b` | `68 / 4 / 9 / 0 / 0 / 0 / 512b` |
| `k13_u8_byte_count` | `63 / 24 / 0 / 0 / 19 / 128b` | `103 / 17 / 0 / 0 / 0 / 256b` | `95 / 15 / 0 / 10 / 0 / 0 / 256b` | `94 / 5 / 13 / 10 / 0 / 0 / 512b` |
| `k14_u32_strided4_sum` | `56 / 24 / 0 / 0 / 15 / 128b` | `121 / 37 / 0 / 0 / 0 / 256b` | `89 / 9 / 9 / 0 / 0 / 0 / 512b` | `89 / 9 / 9 / 0 / 0 / 0 / 512b` |
| `k15_u32_indexed_gather_sum` | `52 / 0 / 0 / 0 / 0 / 0b` | `172 / 15 / 0 / 0 / 0 / 256b` | `93 / 15 / 10 / 10 / 0 / 5 / 512b` | `115 / 17 / 31 / 18 / 0 / 9 / 512b` |

*\*`k10_f32_dot_tree16_fma` on `x86-64` loads `fmaf@GOTPCREL(%rip)` into `%r13` and executes `16` unrolled indirect `callq *%r13` libcalls per loop iteration (`packed_fp = 0`, `fma = 0`).*

#### Refutation of x86-64 Ordered-SIMD Floating-Point Speedup (`k01` vs. `k02` vs. `k03`)

Any assumption that Rust's `simd_reduce_add_ordered` (`@llvm.vector.reduce.fadd` without `reassoc`) accelerates IEEE-754 left-to-right `f64` summation on x86-64 is **empirically refuted** by both machine disassembly and native Ice Lake-SP timing:

- **Machine code (`llvm-objdump`):** Across every x86-64 tier (`x86-64`, `x86-64-v3`, `x86-64-v4`, `x86-64-v4-zmm512`), `k02_f64_sum_ordered_simd_chunk4` and `k03_f64_sum_ordered_simd_chunk8` emit **`0` `ymm` instructions, `0` `zmm` instructions, `0` `%k` opmask instructions, and `0` packed FP instructions**. On `x86-64-v3`/`v4`/`v4-zmm512`, `k03` lowers directly to unrolled serial scalar **`vaddsd (%rdi), %xmm0, %xmm0` / `vaddsd 8(%rdi), %xmm0, %xmm0` / ...** (`33` scalar FP instructions, identical across all three AVX tiers), serialized by the 4-cycle Ice Lake-SP `vaddsd` loop-carried latency chain (`~1.19–1.20 ns/elem` at `~2.6–3.3 GHz`).
- **Measured runtime (`k03` vs. `k01` within each tier):**
  - `N = 8`: `0.978×–1.008×` (`0.5195–0.5560 ns/elem` vs. `0.5181–0.5596 ns/elem`).
  - `N = 32`: **`0.798×–0.838×` SLOWER** (`0.4194–0.4357 ns/elem` vs. `0.3347–0.3643 ns/elem`) because explicit `chunks_exact(8)` prologue/remainder setup adds branch overhead without reducing the serial FP dependency chain.
  - `N = 128`: `0.937×–0.999×`.
  - `N = 1,024`: **`0.983×–1.011×`** (`1.1052–1.1268 ns/elem`, `7.10–7.24 GB/s`).
  - `N = 16,384`: **`0.987×–1.010×`** (`1.1799–1.1973 ns/elem`, `6.68–6.78 GB/s`).
  - `N = 262,144`: **`0.990×–1.014×`** (`1.1903–1.2046 ns/elem`, `6.64–6.72 GB/s`).
- **Static-only cross-architecture contrast (`aarch64-unknown-linux-gnu`, `runtime not measured on silicon`):**
  Compiling the exact same `bench_lib.rs` with `rustc +1.99.1 --target=aarch64-unknown-linux-gnu -C opt-level=3 --emit=asm` shows a sharp ISA split:
  - **`aarch64` default (NEON):** Like x86-64, NEON lacks an ordered horizontal FP reduction instruction; `k01`, `k02`, and `k03` emit **`0` NEON vector instructions and `0` `fadda` instructions** (pure scalar `fadd d*`).
  - **`aarch64` with `-C target-feature=+sve`:** SVE *does* possess the strictly ordered horizontal reduction instruction **`fadda`**; LLVM emits **`2` `fadda` instructions in `k01`, `4` in `k02`, `6` in `k03`, `2` in `k08`, and `10` in `k05`** (plus `2` in `k06`/`k07` epilogues). Note that even `fadda` executes in strict sequential lane order inside the SVE vector pipeline and typically carries latency proportional to vector length—its actual throughput speedup or slowdown on Neoverse-V1/V2 was **not measured on silicon** here.

#### Reassociated FP Reductions (`k04`–`k07` `f64` Sum and `k08`–`k10` `f32` Dot) on Ice Lake-SP Silicon

Once strict left-to-right ordering is relaxed—either via `fadd_fast`/`fmul_fast` or via explicit multi-accumulator trees (`tree4`/`tree8`/`tree16`) that allow independent SIMD lanes to hide FP-add/FMA latency—throughput jumps by more than an order of magnitude in L1d/L2 before converging at L3/DRAM bandwidth:

| Kernel & Tier | `N = 32` (`ns/el` \| `GB/s`) | `N = 128` (`ns/el` \| `GB/s`) | `N = 1,024` (`ns/el` \| `GB/s` \| `vs. ord`) | `N = 16,384` (`ns/el` \| `GB/s` \| `vs. ord`) | `N = 262,144` (`ns/el` \| `GB/s` \| `vs. ord`) |
| :--- | :---: | :---: | :---: | :---: | :---: |
| **`k01` `f64` ord scalar (`x86-64`)** | `0.3386` \| `23.63` | `0.6459` \| `12.39` | `1.1077` \| `7.22` \| `1.00×` | `1.1819` \| `6.77` \| `1.00×` | `1.1920` \| `6.71` \| `1.00×` |
| **`k03` `f64` ord simd8 (`x86-64-v3`)** | `0.4194` \| `19.07` | `0.6750` \| `11.85` | `1.1088` \| `7.22` \| `1.00×` | `1.1817` \| `6.77` \| `1.00×` | `1.1904` \| `6.72` \| `1.00×` |
| **`k04` `f64` `fadd_fast` (`x86-64`)** | `0.2318` \| `34.52` | `0.1856` \| `43.11` | `0.2690` \| `29.74` \| `4.12×` | `0.2955` \| `27.07` \| `4.00×` | `0.3029` \| `26.41` \| `3.94×` |
| **`k04` `f64` `fadd_fast` (`v3`)** | `0.1831` \| `43.69` | `0.1035` \| `77.28` | `0.0904` \| `88.49` \| **`12.25×`** | `0.0933` \| `85.75` \| **`12.65×`** | `0.2450` \| `32.66` \| **`4.88×`** |
| **`k04` `f64` `fadd_fast` (`v4`)** | `0.1938` \| `41.27` | `0.1243` \| `64.36` | `0.0885` \| `90.40` \| **`12.63×`** | `0.0887` \| `90.18` \| **`13.43×`** | `0.2467` \| `32.43` \| **`4.89×`** |
| **`k04` `f64` `fadd_fast` (`v4-zmm512`)** | `0.1959` \| `40.84` | `0.1088` \| `73.51` | `0.0878` \| `91.15` \| **`12.71×`** | `0.1535` \| `52.13` \| `7.76×` | `0.2511` \| `31.86` \| `4.81×` |
| **`k07` `f64` `tree16` (`x86-64`)** | `0.1930` \| `41.46` | `0.1372` \| `58.31` | `0.1139` \| `70.21` \| `9.72×` | `0.1834` \| `43.62` \| `6.44×` | `0.2505` \| `31.94` \| `4.76×` |
| **`k07` `f64` `tree16` (`v3`)** | `0.1644` \| `48.65` | `0.0912` \| `87.71` | **`0.0730` \| `109.60` \| `15.18×`** | `0.0962` \| `83.12` \| **`12.27×`** | **`0.2329` \| `34.35` \| `5.13×`** |
| **`k07` `f64` `tree16` (`v4`)** | `0.1550` \| `51.60` | `0.1033` \| `77.47` | `0.0785` \| `101.91` \| `14.23×` | `0.1263` \| `63.32` \| `9.43×` | `0.2591` \| `30.88` \| `4.66×` |
| **`k07` `f64` `tree16` (`v4-zmm512`)** | `0.1519` \| `52.66` | `0.1072` \| `74.64` | `0.0804` \| `99.49` \| `13.88×` | `0.1270` \| `62.97` \| `9.37×` | `0.2415` \| `33.13` \| `5.00×` |
| **`k08` `f32` dot ordered (`x86-64`)** | `0.5916` \| `13.52` | `0.7924` \| `10.10` | `1.1398` \| `7.02` \| `1.00×` | `1.1826` \| `6.76` \| `1.00×` | `1.1937` \| `6.70` \| `1.00×` |
| **`k09` `f32` dot `fast` (`v3`)** | `0.1750` \| `45.73` | `0.1055` \| `75.80` | `0.0894` \| `89.45` \| **`12.87×`** | `0.0914` \| `87.50` \| **`12.97×`** | `0.2339` \| `34.20` \| **`5.10×`** |
| **`k09` `f32` dot `fast` (`v4`)** | `0.1788` \| `44.73` | `0.1002` \| `79.87` | `0.0890` \| `89.89` \| **`13.05×`** | `0.0916` \| `87.29` \| **`13.04×`** | `0.2465` \| `32.45` \| `4.90×` |
| **`k09` `f32` dot `fast` (`v4-zmm512`)** | `0.2612` \| `30.62` | `0.0970` \| `82.49` | **`0.0769` \| `104.05` \| `15.24×`** | `0.1341` \| `59.64` \| `8.95×` | `0.2589` \| `30.90` \| `4.67×` |
| **`k10` `f32` `tree16_fma` (`x86-64`)** | `2.6680` \| `3.00` | `2.6311` \| `3.04` | **`2.5583` \| `3.13` \| `0.45×`** | `2.5503` \| `3.14` \| `0.46×` | `2.5629` \| `3.12` \| `0.47×` |
| **`k10` `f32` `tree16_fma` (`v3`)** | `0.2576` \| `31.05` | `0.1023` \| `78.23` | **`0.0710` \| `112.70` \| `16.21×`** | `0.1072` \| `74.60` \| `11.06×` | `0.2345` \| `34.11` \| **`5.08×`** |
| **`k10` `f32` `tree16_fma` (`v4`)** | `0.3068` \| `26.08` | `0.1272` \| `62.88` | `0.0819` \| `97.68` \| `14.18×` | `0.1155` \| `69.28` \| `10.35×` | `0.2544` \| `31.44` \| `4.75×` |
| **`k10` `f32` `tree16_fma` (`v4-zmm512`)** | `0.3055` \| `26.19` | `0.1047` \| `76.38` | `0.0767` \| `104.31` \| **`15.28×`** | `0.1218` \| `65.68` \| `9.86×` | `0.2399` \| `33.34` \| **`5.04×`** |

Two critical engineering findings emerge directly from this table:

1. **Explicit Source-Level Trees Beat or Match `fadd_fast` Without Fast-Math Semantics:** At `N = 1,024`, explicit `k07_f64_sum_reassoc_tree16` on `x86-64-v3` reaches **`109.60 GB/s` (`15.18×`)** vs. `k04_f64_sum_reassoc_fadd_fast`'s `88.49 GB/s` (`12.25×`), and `k10_f32_dot_tree16_fma` reaches **`112.70 GB/s` (`16.21×` vs. same-tier ordered, `16.06×` vs. `x86-64` ordered)** vs. `k09`'s `89.45 GB/s` (`12.87×`)—because `16` explicit accumulator lanes map cleanly onto `4 × ymm` registers (filling Ice Lake-SP's dual `256`-bit FP-add/FMA pipelines with `4`-cycle latency without relying on compiler fast-math reassociation). Note also that `k05_f64_sum_reassoc_tree4` saturates at only `~35.26 GB/s` (`N = 1,024` on `v3`) because `4` scalar lanes collapse into a single `ymm` register (`1` active vector accumulator chain, still serialized by the `4`-cycle `vaddpd` latency), whereas `tree8` (`2 × ymm`, `65.36–74.13 GB/s`) and `tree16` (`4 × ymm`, `109.60 GB/s`) fully hide latency.
2. **The `f32::mul_add` `36×` Libcall Performance Cliff Without `+fma`:** Rust's `f32::mul_add(a, b, c)` guarantees single-rounding IEEE-754 FMA semantics, so on baseline `x86-64` (`-fma`) LLVM **cannot** lower `mul_add` to `mulss + addss` and instead emits **`movq fmaf@GOTPCREL(%rip), %r13`** followed by `16` unrolled `callq *%r13` libcalls per loop body. The result is catastrophic: `k10` drops to `2.5583 ns/elem` (`3.13 GB/s`) at `N = 1,024`—**`36.04×` slower** than `x86-64-v3` hardware `vfmadd231ps` (`0.0710 ns/elem`, `112.70 GB/s`), `25.73×` slower at `N = 128`, `23.78×` slower at `N = 16,384`, `10.93×` slower at `N = 262,144`, and `2.24×` slower than ordered scalar `a * b + acc` (`k08`) on baseline `x86-64`. Portable Rust numerical libraries that call `.mul_add(...)` without gating on `#[cfg(target_feature = "fma")]` or runtime CPUID dispatch silently suffer a `>10×–36×` regression on default `x86-64` builds.

### 3. Exact Numerical ULP and Catastrophic Cancellation Audit Across CPU Tiers

`Basis: execution (support/e2_7_real_vectorization_and_fp_silicon.py, support/e2_7_real_vectorization_and_fp_silicon_summary.json, Phase 1 deterministic ULP/bit comparator across all 4 tiers × 6 trip counts)`

Every binary executes an exact IEEE-754 bit-level comparison (`to_bits()` and signed-magnitude monotonic ULP distance) against strict left-to-right scalar summation (`k01`, `k08`) and `black_box`-guarded scalar AXPY (`k11`) before running timed rounds.

#### Cross-CPU-Tier Bit Divergence on Well-Conditioned Inputs (`f64_well` and `f32_dot_well`)

| Dataset & Trip Count | Kernel | `x86-64` (`bits` \| `ULP vs. LTR`) | `x86-64-v3` (`bits` \| `ULP`) | `x86-64-v4` (`bits` \| `ULP`) | `v4-zmm512` (`bits` \| `ULP`) | Cross-Tier Identical? |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`f64_well`, `N = 16,384`** | `ordered` (`k01`/`k02`/`k03`) | `0x40bfff1d72fd3f9a` \| `0` | identical | identical | identical | **Yes (bit-exact)** |
| | `reassoc_fadd_fast` (`k04`) | **`0x40bfff1d72fd3f9f` \| `5`** | **`0x40bfff1d72fd3f9e` \| `4`** | **`0x40bfff1d72fd3f9e` \| `4`** | **`0x40bfff1d72fd3f9e` \| `4`** | **NO (`2` patterns)** |
| | `tree4`/`tree8`/`tree16` (`k05`–`k07`) | `0x40bfff1d72fd3f9e` \| `4` | identical | identical | identical | **Yes (`100%`)** |
| **`f64_well`, `N = 262,144`** | `ordered` (`k01`/`k02`/`k03`) | `0x41006724d02f1dea` \| `0` | identical | identical | identical | **Yes (bit-exact)** |
| | `reassoc_fadd_fast` (`k04`) | **`0x41006724d02f1dec` \| `2`** | **`0x41006724d02f1deb` \| `1`** | **`0x41006724d02f1deb` \| `1`** | **`0x41006724d02f1deb` \| `1`** | **NO (`2` patterns)** |
| | `tree4` / `tree8` (`k05`/`k06`) | `0x41006724d02f1dec` \| `2` | identical | identical | identical | **Yes (`100%`)** |
| | `tree16` (`k07`) | `0x41006724d02f1deb` \| `1` | identical | identical | identical | **Yes (`100%`)** |
| **`f32_dot_well`, `N = 128`** | `reassoc_fma` (`k09`) | **`0xbfa55e0d` \| `0`** | `0xbfa55e0d` \| `0` | `0xbfa55e0d` \| `0` | **`0xbfa55e0e` \| `1`** | **NO (`2` patterns)** |
| **`f32_dot_well`, `N = 16,384`** | `ordered` (`k08`) | `0xc1b1dce8` \| `0` | identical | identical | identical | **Yes (bit-exact)** |
| | `reassoc_fma` (`k09`) | **`0xc1b1dcec` \| `4`** | **`0xc1b1dced` \| `5`** | **`0xc1b1dced` \| `5`** | **`0xc1b1dcf0` \| `8`** | **NO (`3` patterns!)** |
| | `tree16_fma` (`k10`) | `0xc1b1dcea` \| `2` | identical | identical | identical | **Yes (`100%`)** |
| **`f32_dot_well`, `N = 262,144`** | `ordered` (`k08`) | `0xc3a2f5a0` \| `0` | identical | identical | identical | **Yes (bit-exact)** |
| | `reassoc_fma` (`k09`) | **`0xc3a2f5e7` \| `71`** | **`0xc3a2f5ec` \| `76`** | **`0xc3a2f5ec` \| `76`** | **`0xc3a2f5ec` \| `76`** | **NO (`2` patterns)** |
| | `tree16_fma` (`k10`) | `0xc3a2f5ea` \| `74` | identical | identical | identical | **Yes (`100%`)** |

This table exposes an essential semantic distinction for verified compilation:
- **`fadd_fast` / `fmul_fast` violates cross-CPU reproducibility:** Because LLVM chooses the vector width (`VF = 2, 4, 8, 16`), interleave count (`IC`), and FMA contraction (`mulps+addps` on SSE2 vs. `vfmadd231ps` on AVX2/AVX-512) based on `-C target-cpu`, the exact same Rust binary source produces **three distinct bit outputs** on `f32_dot_well` at `N = 16,384` (`0xc1b1dcec`, `0xc1b1dced`, `0xc1b1dcf0`; `4` vs. `5` vs. `8` ULPs) and diverges between SSE2 and AVX2/AVX-512 at `N = 262,144` (`2` vs. `1` ULP in `f64_well`; `71` vs. `76` ULPs in `f32_dot_well`).
- **Explicit source-level trees (`tree4`/`tree8`/`tree16`/`tree16_fma`) preserve `100%` cross-tier bit-exactness:** Across all `6` trip counts and all `5` FP datasets, every single explicit tree kernel produces **identical bits on `x86-64`, `x86-64-v3`, `x86-64-v4`, and `x86-64-v4-zmm512`** (`cross_tier_differences_vs_x86_64` contains **zero** entries for `tree4`, `tree8`, `tree16`, or `tree16_fma`, even when `k10` switches between software `fmaf` on SSE2 and hardware `vfmadd231ps` on AVX2/AVX-512!). Because the associative grouping is explicitly fixed in source semantics, vectorization across the `16` independent lanes is **strictly bit-preserving** (`0` reassociation needed by the compiler).

#### Catastrophic Cancellation Audit (`N = 262,144`, Identical Across All `4` CPU Tiers)

| Dataset (`N = 262,144`) | Exact Math Sum | Ordered LTR (`k01`/`k02`/`k03`/`k08`) | `fadd_fast` / `reassoc_fma` (`k04`/`k09`) | `tree4` (`k05`) | `tree8` (`k06`) | `tree16` / `tree16_fma` (`k07`/`k10`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| **`f64_cancel4`** (`[1e16, 1, -1e16, 1, ...]`) | `131,072.0` | **`1.0`** (`0x3ff0000000000000`, `0` ULP) | **`131,072.0`** (`7.656 × 10^16` ULPs vs. LTR; `0.0` vs. math) | **`0.0`** (`4.607 × 10^18` ULPs) | **`0.0`** (`4.607 × 10^18` ULPs) | **`0.0`** (`4.607 × 10^18` ULPs) |
| **`f64_cancel8`** (`[1e16, 1, 1, 1, -1e16, 1, 1, 1, ...]`) | `196,608.0` | **`131,071.0`** (`0x40fffff000000000`, `0` ULP) | **`196,608.0`** (`2.252 × 10^15` ULPs vs. LTR; `0.0` vs. math) | **`196,608.0`** (`2.252 × 10^15` ULPs) | **`131,072.0`** (`6.872 × 10^10` ULPs) | **`131,072.0`** (`6.872 × 10^10` ULPs) |
| **`f32_dot_cancel4`** (`[2e7, 1, -2e7, 1, ...] · [1, ...]`) | `131,072.0` | **`1.0`** (`0x3f800000`, `0` ULP) | **`131,072.0`** (`1.426 × 10^8` ULPs vs. LTR; `0.0` vs. math) | — | — | **`49,152.0`** (`1.300 × 10^8` ULPs; `81,920.0` vs. math) |

*Exact algebraic mechanism behind the three-way split:*
- On `f64_cancel4`, `ulp(1e16) = 2.0`, so `1e16 + 1.0 == 1e16`. In strict left-to-right summation, each period of 4 starts at `acc = 1.0`, adds `1e16` (absorbing the previous `1.0`), absorbs the next `1.0`, subtracts `1e16` to `0.0`, and adds the trailing `1.0`—inductively resetting `acc` to **`1.0`** for every `N >= 4`.
- In `tree4`/`tree8`/`tree16`, lane `0` accumulates `+(N/4) × 1e16`, lane `1` accumulates `+(N/4)`, lane `2` accumulates `-(N/4) × 1e16`, and lane `3` accumulates `+(N/4)`. Because `ulp(k × 1e16) >= 2k`, combining `(lanes[0] + lanes[1]) + (lanes[2] + lanes[3])` absorbs both `+k` terms before the large opposite-sign terms cancel, collapsing the sum to **`0.0`**.
- In `fadd_fast`, LLVM's horizontal shuffle reduction (`vextractf128` + `vaddpd`) pairs lane `0` (`+k × 1e16`) with lane `2` (`-k × 1e16`) *before* adding lane `1` and lane `3`, canceling the `±1e16` terms first and recovering the exact mathematical sum **`131,072.0`**—yet diverging from IEEE-754 left-to-right semantics (`1.0`) by `131,071.0` (`76,561,193,665,298,432` ULPs).
- On `f32_dot_cancel4` (`N = 262,144`), `tree16_fma` accumulates `k = 16,384` per lane (`±16,384 × 2e7 = ±3.2768e11`, where `ulp(3.2768e11) = 32,768.0 = 2k`) and sums `lanes[0..16]` sequentially; round-to-nearest-even at the half-ULP tie boundary (`±k`) yields **`49,152.0` (`3 × 16,384`)**, disagreeing with strict IEEE-754 (`1.0`), exact math (`131,072.0`), and `tree4` (`0.0`). Thus, any compiler optimization that silently reassociates FP reductions can change results by **`100%` to `131,071×`**—and even *which* value is "better" depends on whether the program's specification is exact real arithmetic or bit-exact IEEE-754!

### 4. AVX-512 Hardware Reality: Opmask Wins, `prefer-256-bit` Bandwidth Protection, `vpgatherqd` Slowdowns, and Verified-Compiler Architecture

`Basis: execution (support/e2_7_real_vectorization_and_fp_silicon_summary.json, Ice Lake-SP native execution of k11–k15 and cross-tier comparison of x86-64-v4 vs. x86-64-v4-zmm512)`

#### Elementwise FP (`k11`) and Integer Kernels (`k12`–`k15`) Across All `6` Trip Counts and `4` Tiers

| Kernel (`B/el`) & Tier | `N = 8` (`ns/el` \| `vs. x64`) | `N = 32` (`ns/el` \| `vs. x64`) | `N = 128` (`ns/el` \| `vs. x64`) | `N = 1,024` (`ns/el` \| `GB/s` \| `vs. x64`) | `N = 16,384` (`ns/el` \| `GB/s` \| `vs. x64`) | `N = 262,144` (`ns/el` \| `GB/s` \| `vs. x64`) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **`k11` `f64_axpy` (`24 B`, `x86-64`)** | `0.4074` \| `1.00×` | `0.2352` \| `1.00×` | `0.1933` \| `1.00×` | `0.1867` \| `128.55` \| `1.00×` | `0.2906` \| `82.58` \| `1.00×` | `0.5364` \| `44.74` \| `1.00×` |
| **`k11` `f64_axpy` (`v3`)** | `0.4868` \| `0.84×` | `0.1572` \| `1.50×` | `0.1281` \| `1.51×` | **`0.1198` \| `200.32` \| `1.56×`** | **`0.1774` \| `135.25` \| `1.64×`** | `0.5489` \| `43.72` \| `0.98×` |
| **`k11` `f64_axpy` (`v4`)** | `0.7084` \| `0.58×` | `0.2198` \| `1.07×` | `0.1699` \| `1.14×` | `0.1412` \| `170.02` \| `1.32×` | `0.1807` \| `132.83` \| `1.61×` | `0.5689` \| `42.18` \| `0.94×` |
| **`k11` `f64_axpy` (`v4-zmm512`)** | `0.5791` \| `0.70×` | `0.3402` \| `0.69×` | `0.2462` \| `0.79×` | `0.2479` \| `96.81` \| **`0.75×`** | `0.3616` \| `66.38` \| **`0.80×`** | `0.6027` \| `39.82` \| `0.89×` |
| **`k12` `u32_sum` (`4 B`, `x86-64`)** | `0.2595` \| `1.00×` | `0.1104` \| `1.00×` | `0.0597` \| `1.00×` | `0.0645` \| `61.99` \| `1.00×` | `0.0790` \| `50.65` \| `1.00×` | `0.0893` \| `44.81` \| `1.00×` |
| **`k12` `u32_sum` (`v3`)** | `0.3354` \| `0.77×` | `0.0929` \| `1.19×` | `0.0426` \| `1.40×` | **`0.0414` \| `96.67` \| `1.56×`** | **`0.0447` \| `89.39` \| `1.77×`** | **`0.0553` \| `72.37` \| `1.62×`** |
| **`k12` `u32_sum` (`v4`)** | `0.3352` \| `0.77×` | `0.0984` \| `1.12×` | `0.0448` \| `1.33×` | `0.0414` \| `96.66` \| `1.56×` | `0.0448` \| `89.21` \| `1.76×` | `0.0601` \| `66.60` \| `1.49×` |
| **`k12` `u32_sum` (`v4-zmm512`)** | `0.3129` \| `0.83×` | `0.1106` \| `1.00×` | `0.0484` \| `1.23×` | `0.0434` \| `92.12` \| `1.49×` | `0.0801` \| `49.94` \| **`0.99×`** | `0.1100` \| `36.36` \| **`0.81×`** |
| **`k13` `u8_count` (`1 B`, `x86-64`)** | `0.4012` \| `1.00×` | `0.1905` \| `1.00×` | `0.1443` \| `1.00×` | `0.1283` \| `7.79` \| `1.00×` | `0.1275` \| `7.84` \| `1.00×` | `0.1276` \| `7.84` \| `1.00×` |
| **`k13` `u8_count` (`v3`)** | `0.4057` \| `0.99×` | `0.1248` \| `1.53×` | `0.0741` \| `1.95×` | `0.0562` \| `17.79` \| `2.28×` | `0.0537` \| `18.61` \| `2.37×` | `0.0532` \| `18.80` \| `2.40×` |
| **`k13` `u8_count` (`v4`)** | **`0.3466` \| `1.16×`** | **`0.1175` \| `1.62×`** | `0.0649` \| `2.22×` | `0.0486` \| `20.58` \| `2.64×` | `0.0447` \| `22.38` \| `2.85×` | `0.0491` \| `20.35` \| `2.60×` |
| **`k13` `u8_count` (`v4-zmm512`)** | `0.3562` \| `1.13×` | `0.1294` \| `1.47×` | **`0.0534` \| `2.70×`** | **`0.0405` \| `24.68` \| `3.17×`** | **`0.0336` \| `29.79` \| `3.80×`** | **`0.0383` \| `26.10` \| `3.33×`** |
| **`k14` `u32_strided4` (`4 B`, `x86-64`)** | `0.5232` \| `1.00×` | `0.2593` \| `1.00×` | `0.1723` \| `1.00×` | `0.1541` \| `25.95` \| `1.00×` | `0.2948` \| `13.57` \| `1.00×` | `0.5286` \| `7.57` \| `1.00×` |
| **`k14` `u32_strided4` (`v3`)** | `0.5079` \| `1.03×` | `0.2550` \| `1.02×` | `0.1753` \| `0.98×` | `0.1402` \| `28.53` \| `1.10×` | **`0.2149` \| `18.62` \| `1.37×`** | `0.5401` \| `7.41` \| `0.98×` |
| **`k14` `u32_strided4` (`v4`)** | `0.7314` \| `0.72×` | `0.3731` \| `0.70×` | `0.1972` \| `0.87×` | `0.1661` \| `24.08` \| `0.93×` | `0.2644` \| `15.13` \| `1.12×` | `0.5696` \| `7.02` \| `0.93×` |
| **`k14` `u32_strided4` (`v4-zmm512`)** | `0.5894` \| `0.89×` | `0.3209` \| `0.81×` | `0.1810` \| `0.95×` | `0.1517` \| `26.36` \| `1.02×` | `0.2736` \| `14.62` \| `1.08×` | `0.5844` \| `6.84` \| `0.90×` |
| **`k15` `u32_gather` (`8 B`, `x86-64`)** | **`0.4126` \| `1.00×`** | **`0.3574` \| `1.00×`** | **`0.3347` \| `1.00×`** | `0.3283` \| `24.36` \| `1.00×` | **`0.5469` \| `14.63` \| `1.00×`** | **`0.8759` \| `9.13` \| `1.00×`** |
| **`k15` `u32_gather` (`v3`)** | `0.5510` \| `0.75×` | `0.3630` \| `0.99×` | `0.3360` \| `1.00×` | **`0.3154` \| `25.36` \| `1.04×`** | `0.5830` \| `13.72` \| `0.94×` | `0.9830` \| `8.14` \| `0.89×` |
| **`k15` `u32_gather` (`v4`)** | **`1.4401` \| `0.29×`** | **`1.1595` \| `0.31×`** | **`1.0490` \| `0.32×`** | **`1.0740` \| `7.45` \| `0.31×`** | **`1.0122` \| `7.90` \| `0.54×`** | **`1.1081` \| `7.22` \| `0.79×`** |
| **`k15` `u32_gather` (`v4-zmm512`)** | **`1.4162` \| `0.29×`** | **`1.2067` \| `0.30×`** | **`1.1195` \| `0.30×`** | **`1.0584` \| `7.56` \| `0.31×`** | **`1.0276` \| `7.79` \| `0.53×`** | **`1.2029` \| `6.65` \| `0.73×`** |

Four concrete hardware lessons emerge from `k11`–`k15` and the `v4` vs. `v4-zmm512` ablation:

1. **Zero-Reassociation Elementwise FP (`k11_f64_axpy_elementwise`) Achieves Peak Bandwidth With Zero Bit Drift:**
   Because `sy[i] = a * sx[i] + sy[i]` performs independent lane-wise multiply and add (without FMA contraction on `a * sx[i] + sy[i]` in Rust, preserving exact IEEE-754 two-rounding semantics), `x86-64-v3` achieves **`200.32 GB/s`** at `N = 1,024` (`1.56×` over SSE2) and **`135.25 GB/s`** at `N = 16,384` (`1.64×` over SSE2) with **`0` bit differences** across every element, trip count, and tier. Notice that `k11` emits `0` FMA instructions across all four tiers because Rust forbids silent FP contraction unless the user explicitly calls `mul_add`.
2. **Compute-Bound Byte Scanning (`k13_u8_byte_count`) Delivers Real AVX-512 Wins Across Every Trip Count:**
   Unlike bandwidth-limited `f64`/`u32` kernels, `k13` processes `1` byte/element (`16 KiB` at `N = 16,384`, comfortably inside `48 KiB` L1d; `256 KiB` at `N = 262,144`, comfortably inside `1.25 MiB` L2) and converts byte comparisons into 32-bit counts. On `x86-64-v4`, AVX-512BW compare-to-opmask (`vpcmpeqb %xmm1, %xmm5, %k0` + `vpmovm2d %k0, %ymm5`, `10` `%k` instructions) outperforms `x86-64-v3` even at tiny `N = 8` (**`1.158×`** vs. `0.989×`) and `N = 32` (**`1.621×`** vs. `1.527×`), and full `512`-bit ZMM widening (`v4-zmm512`) scales cleanly to **`3.17×` (`24.68 GB/s`) at `N = 1,024`**, **`3.80×` (`29.79 GB/s`) at `N = 16,384`**, and **`3.33×` (`26.10 GB/s`) at `N = 262,144`**.
3. **Why LLVM's Default `prefer-256-bit` Protects Ice Lake-SP L2/L3 Bandwidth:**
   Comparing default `x86-64-v4` (`prefer-256-bit` active) against `x86-64-v4-zmm512` (`-C target-feature=-prefer-256-bit`) on the exact same silicon proves that blindly widening loops to `512`-bit `zmm` registers severely degrades L2/L3 streaming kernels on Ice Lake-SP:
   - `k04` (`f64` `fadd_fast`, `N = 16,384`): `v4` (`ymm`, `90.18 GB/s`) vs. `v4-zmm512` (`zmm`, `52.13 GB/s`) -> **`1.73×` regression**.
   - `k09` (`f32` dot `fma`, `N = 16,384`): `v4` (`ymm`, `87.29 GB/s`) vs. `v4-zmm512` (`zmm`, `59.64 GB/s`) -> **`1.46×` regression** (even though `v4-zmm512` won by `1.16×` inside L1d at `N = 1,024`: `104.05` vs. `89.89 GB/s`).
   - `k11` (`f64` AXPY): `v4` vs. `v4-zmm512` -> **`1.76×` regression at `N = 1,024`** (`170.02` vs. `96.81 GB/s`) and **`2.00×` regression at `N = 16,384`** (`132.83` vs. `66.38 GB/s`).
   - `k12` (`u32` wrapping sum): `v4` vs. `v4-zmm512` -> **`1.79×` regression at `N = 16,384`** (`89.21` vs. `49.94 GB/s`) and **`1.83×` regression at `N = 262,144`** (`66.60` vs. `36.36 GB/s`, dropping *below* baseline SSE2 `44.81 GB/s`!).
   - Furthermore, at short trip counts (`N = 8`), wide vector prologues regress `k04`, `k11`, `k12`, and `k14` on `v3`/`v4`/`v4-zmm512` (`0.58×–0.89×` vs. baseline SSE2 `x86-64`), confirming that `prefer-256-bit` plus selective EVEX opmasks is empirically justified on Ice Lake-SP.
4. **AVX-512 `vpgatherqd` Is `1.27×–3.49×` Slower Than Scalar `x86-64` Across Every Trip Count (`k15`):**
   On `k15_u32_indexed_gather_sum`, LLVM keeps `x86-64` completely scalar (`0` vector insns, `0.3283 ns/elem` at `N = 1,024`), uses AVX2 scalar-load + vector-pack on `x86-64-v3` (`gather = 0`, `0.3154 ns/elem` at `N = 1,024`), and emits **`5` `vpgatherqd (%rdi,%zmm*,4), %ymm* {%k1}`** instructions on `x86-64-v4` and **`9`** on `x86-64-v4-zmm512`. On Ice Lake-SP (including Gather Data Sampling microcode overhead and micro-op decomposition), hardware `vpgatherqd` underperforms scalar `x86-64` at **every single tested trip count**: **`3.49×` slower at `N = 8`**, **`3.24×` (`v4`) / `3.38×` (`v4-zmm512`) slower at `N = 32`**, **`3.13×` / `3.35×` slower at `N = 128`**, **`3.27×` / `3.22×` slower at `N = 1,024`**, **`1.85×` / `1.88×` slower at `N = 16,384`**, and **`1.27×` / `1.37×` slower at `N = 262,144`**. Notice that even in Part A, LLVM auto-emitted `@llvm.masked.gather` in `crc32fast` (`11` sites) and `regex-automata` (`5` sites) under `x86-64-v4`—a real compiler cost-model blind spot.

#### Architectural Guidance for Verified-Rust Vectorization (`joshlf/anneal` and Proof-Carrying Codegen)

Synthesizing Part A and Part B directly prioritizes verification engineering effort:

1. **Prioritize Straight-Line SLP + Hand-Written `std::arch` Intrinsics Before Complex Loop Vectorization:** Since `3.6×–3.9×` more real-world sites are SLP store coalescing (`108 / 113` at `v3`) and `40.6%` of all vector IR instructions come from explicit `std::arch` intrinsics (`memchr`, `crc32fast`, `base64`), a verified-compiler certificate library gets far higher ecosystem coverage from (a) width-polymorphic SLP store-pack / shuffle-equivalence rules (`I1`), (b) verified `std::arch` intrinsic semantics (`@llvm.x86.pclmulqdq.*`, `avx2.pshufb`, `avx2.pmadd.*`) (`I2`), and (c) bit-exact elementwise FP and associative integer reduction rules (`I4`, `I5`) than from chasing exotic loop-vectorizer heuristics (`8.3%` LV hit rate).
2. **Make Vector Semantics Width- and Lane-Count-Polymorphic:** Pre-legalization LLVM IR emits `<5 x i8>`, `<13 x i64>`, `<96 x i8>`, `<241 x i16>`, `<497 x i16>`, and `<64 x i64>` (`40` to `7,952` bits). Any IR-level verifier must model `Vec (n : Nat) T` abstractly and verify SelectionDAG legalization (splitting/widening to `xmm`/`ymm`/`zmm`) as a separate lane-reindexing step.
3. **Verify Explicit Multi-Accumulator Reduction Trees Instead of `fast`-Math Flags:** Explicit `tree16` / `tree16_fma` delivers **`15.18×` (`109.60 GB/s`)** `f64` and **`16.21×` (`112.70 GB/s`)** `f32` dot speedups on `x86-64-v3`, eliminates `fast`-math's cross-CPU bit non-determinism (`100%` identical bits across all `4` tiers), and allows the compiler backend to prove **bit-exact** preservation of the source tree without introducing an unsound real-number reassociation axiom into the TCB.
4. **Never Assume `simd_reduce_add_ordered` or Hardware Gather Are Profitable on x86-64:** Cost models and optimization oracles targeting Intel Ice Lake-SP must treat `simd_reduce_add_ordered` as scalar-latency (`1.0×`), retain `prefer-256-bit` for L2/L3 streaming kernels while permitting `512`-bit ZMM for compute-bound byte/opmask kernels (`k13`), guard `f32::mul_add` behind `+fma` to avoid the `36×` `fmaf` libcall cliff, and reject auto-vectorized `vpgatherqd` unless empirically proven profitable on the target microarchitecture.

## Boundaries

1. **Non-Host Microarchitectures (`not measured on silicon`):** All Part B runtime timings, GB/s throughputs, `prefer-256-bit` L2/L3 bandwidth comparisons, and `vpgatherqd` slowdowns were executed exclusively on **Intel Xeon Ice Lake-SP (`Family 6, Model 106, Stepping 6`)**. The following microarchitectures are **`not measured on silicon`** and must not be inferred from Ice Lake-SP results:
   - **AMD Zen 4** (`not measured on silicon`): Implements AVX-512 via double-pumped `256`-bit execution units with different clock-throttling and gather microcode behavior than Ice Lake-SP.
   - **AMD Zen 5** (`not measured on silicon`): Implements full-width `512`-bit execution pipelines without legacy Intel AVX-512 frequency downclocking; the `1.46×–2.00×` L2/L3 ZMM512 regressions observed on Ice Lake-SP are `unknown` on Zen 5.
   - **ARM Neoverse-V1** (`not measured on silicon`): SVE `256`-bit vector length and hardware `fadda` latency/throughput are `not measured on silicon`.
   - **Apple Silicon (M-series)** (`not measured on silicon`): Wide out-of-order NEON (`128`-bit) and AMX behavior are `not measured on silicon`.
2. **AArch64 NEON and `+sve` `fadda` Comparison (`static disassembly only`):** All `aarch64-unknown-linux-gnu` findings (`0` `fadda` on baseline NEON vs. `2`/`4`/`6` `fadda` instructions on `k01`/`k02`/`k03` under `-C target-feature=+sve`) come strictly from static `--emit=asm` cross-compilation (`static_cross_arch_disassembly` in `support/e2_7_real_vectorization_and_fp_silicon_summary.json`). Actual execution speed of SVE `fadda` vs. scalar `fadd` on Arm hardware is `not measured on silicon`.
3. **Short-Loop Timing Noise (`N = 8, 32`) and Host Microcode State:** Although all binaries were pinned to logical core `12` (`taskset -c 12`) and measured across `9` interleaved rounds after warmup, sub-nanosecond-per-element measurements at `N = 8` and `N = 32` remain sensitive to AVX-512 turbo-license transitions and OS timer jitter (observed relative IQRs up to `64%–133%` on `N = 8`/`32` `k04`–`k06`, dropping to `< 1%–5%` for most kernels at `N >= 1,024`). Additionally, the `1.27×–3.49×` `vpgatherqd` slowdown on Ice Lake-SP reflects the live production kernel/microcode state (including any active Gather Data Sampling mitigation) rather than an unmitigated silicon baseline.
4. **Unstable Compiler Interfaces Used in Part B:** Probing `fadd_fast`, `fmul_fast`, and `simd_reduce_add_ordered` requires `#![feature(core_intrinsics, repr_simd)]` under `RUSTC_BOOTSTRAP=1`. Furthermore, `-C target-feature=-prefer-256-bit` is an LLVM backend subtarget feature that triggers a `rustc` warning (`unknown and unstable feature specified for -Ctarget-feature: prefer-256-bit`) while passing through to LLVM; stable Rust code cannot rely on this flag directly.
5. **Part A Crate Corpus Representativeness (`7` General-Purpose Crates):** Part A measures `7` widely used pure-Rust and `std::arch` crates (`1,493`–`1,507` compiled functions) spanning compression, byte search, CRC, encoding, JSON parsing, regex automata, and JPEG decoding. It does **not** include dense linear algebra (`faer`, `nalgebra`), ML inference (`candle`), scientific HPC, or unstable `std::simd` crates, where floating-point vector density and LoopVectorize success rates are expected to be higher than the `73` FP instructions and `8.31%` LV rate observed here.
6. **Single-Core Measurement and Pinned Compiler Version (`rustc 1.99.1` / `LLVM 23.1.1`):** All Part B measurements are single-threaded (`1` pinned core) and reflect `LLVM 23.1.1` code generation. Multi-core aggregate memory-bandwidth scaling and vectorization cost models in newer or older LLVM releases are `not examined` and require direct re-execution.

## Evidence

| Artifact / Upstream Source | Immutable Pin / Coordinates | Evidence Role & What It Establishes |
| :--- | :--- | :--- |
| `support/e2_7_real_vectorization_and_fp_silicon.py` | Preserved in package (`support/`) | **Execution script:** Self-contained Part A (`7` crates × `4` tiers `cargo rustc --emit=llvm-ir` + LLVM remarks parser) and Part B (`15`-kernel Rust benchmark, exact ULP comparator, `llvm-objdump -d` analyzer, and static-only `aarch64` NEON/`+sve` cross-compiler). |
| `support/e2_7_real_vectorization_and_fp_silicon_summary.json` | Preserved in package (`support/`), observed `2026-11-20` | **Execution data (`245,876` bytes, lossless metrics):** Full host CPU metadata, all `4` invariant checks (`true`), complete Part A four-tier aggregates, all `7 × 4` per-crate IR/width/family/origin/intrinsic/remark tables, `6`-idiom taxonomy, complete Part B `15 × 4` `llvm-objdump` counts, `15 × 6 × 4` median/min/max/IQR timings and GB/s, full lossless cross-tier ULP/bit-diff verification, speedup summary, and static `aarch64` NEON/`+sve` counts. |
| `rust-lang/rust` (`rustc 1.99.1`, `LLVM 23.1.1`) | `58cf8f9c35b355199727627d07ae34a4e2846d67` | **Execution subject:** Compiler and bundled `LLVM 23.1.1` / `llvm-objdump` used for all Part A IR/remark runs, Part B native x86-64 binaries, and static AArch64 assembly emission. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | **Architecture reference:** Compiler-version-pinned `rustc` capture driver and trusted MIR/ISA verification boundary grounding Section 4's verified-compiler recommendations. |
| `Frommi/miniz_oxide` (`0.9.1`) | `4e582392df3a739d2b0dfd2c537dc33e8942be38` | **Part A crate:** Pure-Rust DEFLATE codec (`37` fns, `15` vec fns, `578` vec IR instrs at `v3`, `23` SLP vs. `6` LV wins, `<64 x i64>` pre-legalization vectors). |
| `BurntSushi/memchr` (`2.8.3`) | `5fdb40c054e1fff359a2f7bdf7f87a13b34b465d` | **Part A crate:** Explicit `std::arch` byte/substring search (`9` `std::arch` files, `800` hand-written vec IR instrs at `v3`–`v4-zmm512`, `18` `@llvm.vector.reduce.add` sites). |
| `srijs/rust-crc32fast` (`1.5.5`) | `8a93d2a70c00ab3e72beda42014b18fad8e496ea` | **Part A crate:** Explicit `PCLMULQDQ` folding (`202` `@llvm.x86.*` intrinsics at `v3+`, plus `11` auto-SLP `@llvm.masked.gather` sites on `v4`). |
| `marshallpierce/rust-base64` (`0.23.1`) | `069bf7067b949f5c0a92b6ceb82492920502f2c2` | **Part A crate:** Hybrid AVX2 `std::arch` + scalar codec (`24` `@llvm.x86.avx2.*` intrinsics; `<96 x i8>`, `<192 x i8>`, `<64 x i64>` pre-legalization vectors). |
| `serde-rs/json` (`1.0.154`) | `20572a6d066958542d79cdd6cf1a7cd9f0c8e1f8` | **Part A crate:** Branchy JSON parser/serializer (`165` fns, only `4` vec fns / `31` vec IR instrs at `v3`, `0` LV wins, `4` SLP wins). |
| `rust-lang/regex` (`regex-automata 0.4.19`) | `4226f214c56e584304520adb9080bcc4c792390e` | **Part A crate:** Multi-module NFA/DFA engine (`1,079` fns at `v3`, `139` vec fns, `1,454` vec IR instrs, `79` SLP vs. `14` LV wins, `<13 x i64>` and `<5 x i8>` non-power-of-two vectors, `43` masked scatter/gather/load/store sites at `v4-zmm512`). |
| `image-rs/jpeg-decoder` (`0.1.22`) | `3bf223f7dcaa03cf0422e9e79eaf936ff406686f` | **Part A crate:** Pure-Rust JPEG DSP (`100%` of Part A's `73` FP vector IR instrs; `<32 x float>`, `<241 x i16>`, and `<497 x i16>` masked loads in `Upsampler::new`). |

## Revalidation

1. **Re-run the complete Part A + Part B empirical suite on any x86-64 AVX-512 host (`rustc +1.99.1` installed via `rustup`, offline crates pre-cached in `$CARGO_HOME/registry/src/`):**
   ```bash
   python3 support/e2_7_real_vectorization_and_fp_silicon.py --out /tmp/e2_7_revalidate.json
   ```
   Verify all four keys in `invariant_checks` are `true`, confirm Part A IR/remark totals match `support/e2_7_real_vectorization_and_fp_silicon_summary.json` (deterministic for pinned `rustc 1.99.1` and crate versions), and inspect Part B `numerical_verification` bit patterns (deterministic across x86-64 CPUs supporting AVX-512).
2. **Verify exact x86-64 assembly lowerings (`vaddsd` in `k03`, `fmaf@GOTPCREL` in `k10`, `vpcmpeqb`/`%k` in `k13`, `vpgatherqd` in `k15`):**
   Extract `BENCH_RS` before `fn main()` from `support/e2_7_real_vectorization_and_fp_silicon.py` into `/tmp/bench_lib.rs` and run:
   ```bash
   for tier in x86-64 x86-64-v3 x86-64-v4; do
     RUSTC_BOOTSTRAP=1 rustc +1.99.1 --crate-type=lib -C opt-level=3 -C codegen-units=1 \
       -C target-cpu="$tier" --emit=asm -o "/tmp/bench_${tier}.s" /tmp/bench_lib.rs
   done
   grep -nE 'fmaf@GOTPCREL|vpgatherqd|vpcmpeqb.*%k|vaddsd' /tmp/bench_*.s | head -n 40
   ```
3. **Re-run static-only AArch64 NEON vs. `+sve` `fadda` check (no cross-target `rust-std` linker required, requires `aarch64-unknown-linux-gnu` `rust-std` component for `libcore`):**
   ```bash
   RUSTC_BOOTSTRAP=1 rustc +1.99.1 --target=aarch64-unknown-linux-gnu --crate-type=lib \
     -C opt-level=3 -C codegen-units=1 -C target-feature=+sve --emit=asm \
     -o /tmp/bench_aarch64_sve.s /tmp/bench_lib.rs
   grep -n '\bfadda\b' /tmp/bench_aarch64_sve.s
   ```
4. **Extend Part B to unmeasured microarchitectures (AMD Zen 4/5, ARM Neoverse-V1, Apple Silicon):**
   Compile and run `bench.rs` natively on each target machine (`-C target-cpu=native`, pinned via `taskset` / OS affinity) to close the `not measured on silicon` boundaries—especially testing whether AMD Zen 5 eliminates the `1.46×–2.00×` L2/L3 `zmm512` bandwidth regressions and `vpgatherqd` slowdowns observed on Intel Ice Lake-SP, and whether Neoverse-V1 SVE `fadda` achieves any speedup over scalar `fadd`.
