# Clean-Room Memory-Safe Media Codec Rewrites: Throughput, Vectorization Idioms, Aliasing Soundness, and Panic-Freedom Gaps

## Summary

Clean-room and refactored memory-safe media codec implementations (`rav1d`, `Symphonia`, `Wuffs`, `zune-image`, `rav1e`, `mp4parse-rust`, `image-rs/image`, and `NihAV`) demonstrate that memory safety does not impose a uniform throughput tax, nor does `#![forbid(unsafe_code)]` automatically confer denial-of-service safety or panic-freedom:

1. **Throughput bifurcates by kernel dimensionality and bitstream seriality.** For byte-oriented compression, lossless audio linear prediction, and 1D filter pipelines (`FLAC`, `ALAC`, `MP1`/`MP2`, `Deflate`, `GIF`, `PNG`), safe Rust auto-vectorization (`Symphonia`) and compile-time proof-elided C (`Wuffs`) routinely **outperform** reference C libraries (`FFmpeg`, `zlib`, `libpng`, `libgif`) by **1.15x to 6.58x** (`Symphonia` `0.51x–0.81x` runtime vs. `FFmpeg` on FLAC/ALAC; `Wuffs` `1.48x` vs. `zlib` Deflate and `1.55x–3.01x` vs. `libpng`). Conversely, for 2D block video codecs with complex intra-prediction, motion compensation, loop restoration, and context-adaptive binary/multi-symbol arithmetic coding (`AV1` in `rav1d` and `rav1e`, `JPEG` in `zune-jpeg`, `Indeo 4/5` in `NihAV`), pure scalar/auto-vectorized safe Rust lags hand-tuned C/SIMD by **1.3x to >2.3x**. Closing that gap requires either `core::arch` SIMD intrinsics (`zune-jpeg`, within `1.00x–1.34x` of `mozjpeg`) or retaining external NASM/GAS assembly (`rav1d` and `rav1e`, where `rav1d` still exhibits a **~5%–11%** control-plane overhead vs. C `dav1d` across the ~50% of execution time spent outside assembly).
2. **Bounds-check elimination (BCE) in `rustc`/LLVM fails silently on 64-bit strided and butterfly indexing.** Executed `rustc 1.98.0-nightly` (LLVM `22.1.6`, `-C opt-level=3 -C target-cpu=x86-64-v3`) probes confirm that naive `src[r * stride + c]` 2D block loops retain **16 `panic_bounds_check` landing pads** and emit **zero** vector instructions because `r * stride` can wrap modulo $2^{64}$. Rewriting into upfront `checked_mul` + `.get(..need)` + `chunks_exact(stride)` + `&[u8; 16]` array conversion eliminates **100%** of panic symbols and emits 4x-unrolled AVX2 `vpmovzxbw`/`vpaddw` loops. However, even `split_at_mut` in `Symphonia`'s `Imdct::imdct` (`symphonia-core/src/dsp/mdct.rs:94-137`) leaves 4 `panic_fmt` branches (unless `2 * n` overflow is guarded) and 2 inner-loop `panic_bounds_check` branches on forward/reverse strided-by-2 butterfly stores (`vec0[n2 - 1 - 2*i]`, `vec1[2*i]`).
3. **Concurrent/aliased frame pools are the primary soundness hazard in Rust video codecs.** Tile- and frame-threaded video decoding requires concurrent disjoint mutation of shared picture buffers and coexisting reference-frame reads. `NihAV`'s custom `NABufferRef<T>` (`nihav-core/src/refs.rs:57-108`) introduces immediate Rust aliasing undefined behavior (`unsafe impl<T> Send/Sync` without bounds on `T`, `&mut NABufferData<T>` creation inside `as_ref` and `clone`, and unchecked `DerefMut` on cloned references). `rav1d`'s `DisjointMut<T>` (`src/disjoint_mut.rs:34-156`) avoids intermediate whole-slice references via `UnsafeCell<T>` and provenanceless element constraints, checking interval disjointness dynamically in debug builds while leaving release-mode disjointness as an unverified proof obligation.
4. **Panic-freedom and fallible-allocation gaps remain widespread.** Among the audited Rust implementations, only `mozilla/mp4parse-rust` statically bans infallible heap allocation (shadowing `Vec`, `Box`, `HashMap`, and `String` at `mp4parse_capi/src/lib.rs:66-73` in favor of `TryVec`/`TryBox`/`TryHashMap` and enabling release `overflow-checks = true`), while only `google/wuffs` proves 100% compile-time absence of bounds, division-by-zero, and integer-overflow traps with zero dynamic allocation. `zune-jpeg` exhibits an explicit **SIMD-vs-scalar panic divergence** (`crates/zune-jpeg/src/idct/scalar.rs:160-166` vs. `avx2.rs:56-71`), `rav1d` compiles with `panic = "abort"` (`Cargo.toml:59`) where any residual `.unwrap()` or `assert!` terminates the host process, and `Symphonia` documents input-triggered panics on codecs below `"Excellent"` maturity (`README.md:68`).

## Applicability

This report characterizes and compares concrete, immutably pinned revisions of eight clean-room or C2Rust-refactored media libraries alongside their upstream C baselines (`dav1d` and `FFmpeg`) and an executed `rustc`/LLVM assembly probe:

- **`memorysafety/rav1d`** at `2e7216c20ac2a75de204d6c8d7268b75a45959b4` (`v1.1.1`, MSRV `1.85`), evaluated as a C-ABI drop-in replacement (`librav1d.a`) for **`videolan/dav1d`** (`9af5ae4eb5204706c7f381ec62635237179f172e`, internal `DAV1D_VERSION` baseline `966d63c1` recorded in `rav1d/src/lib.rs:216`).
- **`pdeljanov/Symphonia`** at `5f879df0bf309246a48d57caae457fd8c0e2a5cb` (`v0.6.1`, Edition 2024, MSRV `1.85`), evaluated as a `#![forbid(unsafe_code)]` audio decoder and container demuxer workspace compared against **`FFmpeg/FFmpeg`** (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`).
- **`google/wuffs`** at `a87f0bb85b9406d29f48a1c03b6f42c4585145f6` (`v0.3`), evaluated as a contrast point: a hermetic, zero-allocation DSL with compile-time refinement-type bounds/overflow proofs transpiling to C99 + SSE4.2/AVX2/NEON intrinsics.
- **`etemesi254/zune-image`** at `2cdbbf554e7da373d3418ab327a0db7c4abb50cd`, focusing on `zune-jpeg`, `zune-png`, and `zune-inflate` (`no_std`-capable Rust codecs restricting `unsafe` exclusively to runtime-dispatched `core::arch` SIMD intrinsics).
- **`rust-av/rav1e`** at `d2af1842f6e4b826e528ef4bf16c2454e177cd3f` (`v0.5.0`), evaluated as a clean-room Rust AV1 encoder combining safe Rust RDO/entropy coding with external NASM (`x86_64`) and GAS (`aarch64`) assembly.
- **`mozilla/mp4parse-rust`** at `d3a9abfc93b22687e5e5cd9df86697adcb7d5887` (`v0.17.0`), evaluated for production browser C-FFI (`mp4parse_capi`) OOM-fallible allocation and integer-overflow hardening.
- **`image-rs/image`** at `e70e9fe5073f4b298a33b72993847241a8eaaca6` (`v0.25.9`, MSRV `1.88.0`), evaluated as an ecosystem facade delegating format decoding across pure-Rust (`png`, `zune-jpeg`, `image-webp`, `gif`) and optional C (`dav1d`) backends under `Limits` resource accounting.
- **`NihAV`** (`https://git.nihav.org/nihav.git`) at `904a660eca4a646b4618d11bb6ef025a6e50f725`, evaluated as a multi-crate clean-room Rust legacy codec/demuxer suite authored by a former `FFmpeg`/`Libav` developer.
- **Executed compiler probe** using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with LLVM `22.1.6` targeting `x86_64-unknown-linux-gnu` (`-C opt-level=3 -C target-cpu=x86-64-v3`).

This package complements rather than repeats existing corpus coverage of entropy bitstream mathematics (`entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders`, `libwebp-huffman-tables-dav1d-rans-cdfs-and-lcms2-icc-tetrahedral-luts`), audio LPC fixed-point overflow theory (`webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows`), general compiler BCE theory (`type-validity-seeded-range-and-farkas-bounds-check-elimination`), borrow-checker disjoint-view limits (`borrow-checker-self-referential-views-disjoint-slices-and-polonius-limits`), and C2Rust strangulation workflows (`incremental-c2rust-lifting-mvee-shadow-execution-and-ffi-strangulation`).

## Findings

### 1. Quantitative Throughput Reality vs. Reference C Implementations

`Basis: documentation + source`

Published and in-repository benchmarks across `Symphonia`, `Wuffs`, `zune-image`, `rav1d`, and `NihAV` show a sharp structural split between codecs dominated by 1D sequential/vectorizable loops and codecs dominated by 2D strided predictors plus serial entropy state machines.

#### 1.1 `Symphonia` (`#forbid(unsafe_code)`) vs. Statically Linked `FFmpeg` (`BENCHMARKS.md:71-133`)

`Symphonia` (`5f879df0bf309246a48d57caae457fd8c0e2a5cb`, `BENCHMARKS.md:13-59`) measures single-threaded full-track decode time (`symphonia-play --decode-only` built with `-C target-cpu=native` vs. a custom statically linked `FFmpeg` `ffbench` harness that avoids `ffmpeg -f null` `S16LE` resampling and dynamic-linker startup overhead; 30 runs after 3 warmups via Hyperfine). Relative decode time $\text{Rel} = T_{\text{Symphonia}} / T_{\text{FFmpeg}}$ ($\text{Rel} < 1.0$ means `Symphonia` is faster):

| Audio Workload | Intel i7-4790K (`x86_64`, AVX2) | Apple M1 Pro (`aarch64`, NEON) | Raspberry Pi 4B (Cortex-A72) | Dominant Kernel Regime |
| :--- | :---: | :---: | :---: | :--- |
| **MP1** (44 kHz, 192 / 448 kbps) | `0.45x` / `0.48x` | `0.63x` / `0.64x` | `0.83x` / `0.87x` | Polyphase synthesis filterbank (auto-vectorized) |
| **MP2** (44 kHz, 128 / 384 kbps) | `0.60x` / `0.60x` | `0.72x` / `0.77x` | `0.91x` / `0.93x` | Subband dequantization + synthesis filter |
| **FLAC** (44k/16b, 48k/24b, 96k/24b) | `0.71x` / `0.72x` / `0.74x` | `0.64x` / `0.51x` / `0.57x` | `1.04x` / `0.96x` / `0.96x` | Rice residual reader + fixed/LPC predictor |
| **ALAC** (44k/16b, 96k/32b) | `0.73x` / `0.79x` | `0.81x` / `0.77x` | `0.81x` / `0.88x` | Adaptive Rice + dynamic predictor loop |
| **MP3** (44 kHz, 128 / 320 kbps) | `1.04x` / `0.84x` | `1.00x` / `0.81x` | `1.07x` / `0.95x` | Huffman + requantize + 36/12-pt IMDCT |
| **ADPCM IMA / MS** (44 kHz) | `0.83x` / `1.13x` | `1.51x` / `0.59x` | `1.05x` / `0.96x` | Serial nibble predictor (branch/codegen sensitive) |
| **Vorbis** (44 kHz, ~256 kbps) | `1.05x` | `1.24x` | `1.12x` | Floor1/residue VQ + power-of-2 FFT IMDCT |
| **AAC-LC** (#1 / #2, 44 kHz, 260 kbps) | `1.21x` / `1.19x` | `1.10x` / `1.10x` | `1.27x` / `1.25x` | Scale-factor bands + codebook VLC + IMDCT |

Key architectural takeaway: `Symphonia` achieves **26%–49% faster FLAC decoding** than single-threaded `FFmpeg` on `x86_64` and `M1 Pro` with **zero `unsafe` code**, because `FFmpeg`'s default `flacdec` C path pays function-pointer indirection and conservative aliasing assumptions while LLVM unrolls and vectorizes `Symphonia`'s fixed-order linear prediction and channel decorrelation slices. Conversely, on `AAC-LC` (`1.10x–1.27x` slower) and `M1 Pro` `Vorbis` (`1.24x` slower), `FFmpeg`'s hand-written `imdct_half` SIMD (`libavcodec/x86/fft.asm`, `libavcodec/aarch64/fft_neon.S`) outperforms `Symphonia`'s `Imdct` wrapper (`symphonia-core/src/dsp/mdct.rs:67-137`).

#### 1.2 `Wuffs` Compile-Time Proof-Elided C vs. C, Go, and Safe Rust (`doc/benchmarks.md:102-477`)

`Wuffs` (`a87f0bb85b9406d29f48a1c03b6f42c4585145f6`, measured on Intel Core i5-10210U, Clang 11 / GCC 10) demonstrates what happens when **100% of bounds and arithmetic-overflow checks are discharged at compile time** and combined with safe, typed SIMD intrinsics (`base.x86_sse42_utility`, `base.x86_avx2_utility`, `base.arm_neon_utility`):

| Format / Benchmark (`doc/benchmarks.md`) | `Wuffs` (Clang 11 / GCC 10) | Reference C (`mimic`) | Specialized C (`libdeflate` / `libspng`) | Safe Rust (`flate2`/`miniz_oxide` / `png` / `gif`) |
| :--- | :--- | :--- | :--- | :--- |
| **Deflate 100k** (`just_one_read`) | `521` / `522 MB/s` (`1.48x`) | `zlib 1.2.11`: `352 MB/s` (`1.00x`) | `libdeflate 1.7.1`: `507 MB/s` (`1.44x`) | `miniz_oxide 0.5.3`: `272 MB/s` (`0.77x`) |
| **Deflate 1k** (`full_init` vs `part_init`) | `195` (`0.81x`) / `226 MB/s` (`0.93x`) | `zlib 1.2.11`: `241 MB/s` (`1.00x`) | `libdeflate 1.7.1`: `326 MB/s` (`1.35x`) | `miniz_oxide 0.5.3`: `165 MB/s` (`0.68x`) |
| **Gzip 100k** (Deflate + CRC-32) | `527` / `550 MB/s` (`1.81x–1.89x`) | `zlib 1.2.11`: `291 MB/s` (`1.00x`) | `libdeflate 1.7.1`: `496 MB/s` (`1.70x`) | — |
| **Bzip2 10k / 100k** | `63.0` / `48.9 MB/s` (`1.86x` / `1.62x`) | `libbz2 1.0.8`: `33.8` / `30.2 MB/s` | — | — |
| **GIF 100k realistic / anim** | `225 MB/s` (`2.18x`) / `1.31 GB/s` (`6.58x`) | `libgif 5.1.9`: `103` / `199 MB/s` | — | `gif 0.11.4`: `113` (`1.10x`) / `513 MB/s` (`2.58x`) |
| **PNG 77k 8bpp / 552k 32bpp** | `1.00 GB/s` (`2.70x`) / `870 MB/s` (`3.01x`) | `libpng 1.6.37`: `370` / `289 MB/s` | `libspng 0.7.3`: `384` / `392 MB/s` | `png 0.17.5`: `330` (`0.89x`) / `299 MB/s` (`1.03x`) |
| **CRC-32 IEEE / Adler-32 100k** | `23.8 GB/s` (`14.7x`) / `26.4 GB/s` (`7.5x`) | `zlib 1.2.11`: `1.62` / `3.52 GB/s` | `libdeflate`: `25.4` / `49.4 GB/s` | — |

Notice the 1 KiB Deflate initialization cliff (`doc/benchmarks.md:168-170`): zero-initializing `Wuffs`'s ~40 KiB internal Huffman/history struct (`full_init`) drops 1 KiB decode throughput from `226 MB/s` to `195 MB/s` (`0.81x` vs. `zlib`), motivating `WUFFS_INITIALIZE__LEAVE_INTERNAL_BUFFERS_UNINITIALIZED` (`part_init`), which is sound only because `Wuffs` tracks initialized prefix lengths before reading history buffers.

#### 1.3 `zune-image` vs. `mozjpeg`, `libdeflate`, `spng`, and `image-rs` (`benchmarks/benchmark-results.md:65-129`)

On Apple Silicon (`Darwin` Criterion suite in `etemesi254/zune-image` at `2cdbbf554e7da373d3418ab327a0db7c4abb50cd`):

- **`zune-jpeg` vs. `mozjpeg` (`libjpeg-turbo` NASM/NEON):** On progressive JPEGs (`benchmarks/benchmark-results.md:100-107`), `zune-jpeg` **matches or beats** `mozjpeg` (`110.3 ms` vs. `121.2 ms` no-sampling progressive; `96.36 ms` vs. `97.23 ms` horizontal subsampling; within `3.3%` on HV/vertical progressive) because multi-scan Huffman/coefficient refinement is scalar-bitstream bound. On baseline JPEGs (`lines 88-99, 108-109`), `zune-jpeg` is **`1.097x` to `1.34x` slower** than `mozjpeg` (`54.83 ms` vs. `50.00 ms` no-sampling; `48.31 ms` vs. `36.28 ms` HVchroma). Remarkably, on `Darwin` (`aarch64`), `zune-jpeg` with intrinsics enabled (`54.81 ms`) vs. disabled (`55.44 ms`, `1.011x`, `lines 110-111`) shows only a `1.1%` difference because `zune-jpeg`'s Cargo feature table (`crates/zune-jpeg/README.md:190-195`) concentrated heaviest intrinsics in `x86` (`avx2`/`sse`) while scalar `idct_int` + Huffman bitbuffer refill dominate on AArch64.
- **`zune-png` vs. `image-rs/png` and C `spng` (`lines 115-129`):** Both Rust PNG decoders (`zune-png` and `image-rs/png`) **decisively outperform C `libspng` by `1.89x` to `3.31x`** (`163.7 ms` `image-rs/png` and `186.3 ms` `zune-png` vs. `541.2 ms` `spng` on 16 bpp; `139.7 ms` `zune-png` vs. `378.0 ms` `spng` on interlaced 8 bpp).
- **`zune-inflate` vs. `zlib-ng` and `libdeflate` (`lines 67-81`):** Pure-Rust `zune-inflate` beats `flate2`/`zlib-ng` by **`1.03x` to `1.88x`** (`203.6 MiB/s` vs. `108.2 MiB/s` on `enwiki`), while trailing C `libdeflate` by **`1.53x` to `2.51x`**.

#### 1.4 `rav1d` vs. `dav1d` and `NihAV` vs. `libavcodec`

- **`rav1d` (`memorysafety/rav1d` at `2e7216c20ac2a75de204d6c8d7268b75a45959b4`):** `rav1d` retains 100% of `dav1d`'s hand-written `x86`/`x86_64` NASM (`.asm`) and `arm`/`aarch64` GAS (`.S`) kernels (`build.rs:151-225`), which account for ~50% of AV1 decode wall-clock time (inverse transforms, CDEF, loop filter, Wiener/SGRproj loop restoration, 8-tap/warp motion compensation, film grain, and MSAC arithmetic symbol decoding). Across the remaining ~50% pure-Rust control plane (OBU/tile parsing, `refmvs` temporal MV projection, CDF updates, deblocking filter mask derivation `lf_mask.rs`, and multi-threaded task scheduling `thread_task.rs`), ISRG Prossimo / Immunant benchmarks report a **`5%`–`11%` end-to-end slowdown** relative to C `dav1d` (meaning the Rust control-plane half runs ~`10%`–`22%` slower than `dav1d`'s C control plane). When `asm` is disabled (`--no-default-features --features="bitdepth_8,bitdepth_16"`, `README.md:54`), decoding falls back to scalar/auto-vectorized Rust (`src/itx.rs`, `src/mc.rs`, `src/cdef.rs`), incurring a multi-fold (`2x–4x+`) throughput drop identical in nature to `dav1d -Denable_asm=false`.
- **`NihAV` (`904a660eca4a646b4618d11bb6ef025a6e50f725`):** In scalar-to-scalar comparisons (disabling `libavcodec` SIMD), `NihAV`'s clean-room Indeo 4/5 decoder initially ran **`2.36x` slower** than `libavcodec` (`31.6 s` vs. `13.4 s`) due to un-inlined `BitReader` calls and un-elided slice bounds checks on `for x in 0..w` block copy loops before manual `#[inline(always)]` and `copy_from_slice` rewrites.

---

### 2. Three-Tier SIMD Architecture: Auto-Vectorization vs. Intrinsics vs. External Assembly

`Basis: source`

Across the eight examined codebases, SIMD acceleration cleanly stratifies into three engineering tiers with distinct verification and maintenance profiles:

| Tier | Representative Crates & Files | Mechanism & Dispatch | `unsafe` Surface | Verification Cost |
| :--- | :--- | :--- | :--- | :--- |
| **Tier 1: Safe Auto-Vectorization** | `Symphonia` (`symphonia-core/src/dsp/`), `image-rs/png`, `zune-inflate` | `#![forbid(unsafe_code)]`; fixed-size chunks + `rustfft` (which internally uses `core::arch` when `opt-simd-*` enabled) | Zero in crate (`Symphonia` delegates FFT SIMD to `rustfft`, `README.md:181-188`) | **Lowest:** Pure MIR scalar semantics; no ISA model required |
| **Tier 1b: Proof-Checked Typed SIMD DSL** | `Wuffs` (`std/png/decode_filter_x86_sse42.wuffs:43-126`) | `choose cpu_arch >= x86_sse42` runtime function-pointer selection; `iterate (curr = args.curr)(length: 4, advance: 4, unroll: 2)` | Zero raw pointers; compiler proves `peek_u32le`/`poke_u32le!` in-bounds | **Low:** Bounded 128/256-bit pure bitvector operations; zero memory-safety obligations |
| **Tier 2: `core::arch` Target-Feature Intrinsics** | `zune-jpeg` (`crates/zune-jpeg/src/idct/avx2.rs:78-140`), `moxcms` in `image` (`Cargo.toml:45-52`) | `#[target_feature(enable = "avx2")] pub unsafe fn` dispatched via function pointers initialized after `is_x86_feature_detected!` and gated by `DecoderOptions::use_unsafe` | Localized to SIMD leaf modules (`#![cfg_attr(not(any(feature = "x86", feature = "neon")), forbid(unsafe_code))]`, `zune-jpeg/src/lib.rs:313`) | **Medium:** Must prove `_mm_loadu_si128` / `_mm_storeu_si128` pointer bounds + bit-equivalence (or error bound) vs. scalar twin |
| **Tier 3: External NASM / GAS Assembly** | `rav1d` (`build.rs:151-330`, 45 `.asm`/`.S` files), `rav1e` (`build.rs:78-143`, 24 `.asm` files + AArch64 `.S`) | Out-of-line `.asm` (NASM $\ge 2.14$) and `.S` (Clang/GCC GAS) linked as `librav1dasm.a` / `librav1easm.a`, called via `extern "C"` function tables (`wrap_fn_ptr!`, `src/wrap_fn_ptr.rs:41-99`) | **Unchecked C/assembly ABI boundary:** raw `*mut DynPixel`, signed `ptrdiff_t` strides, custom stack alignment (`STACK_ALIGNMENT 16`), red-zone/register clobbers, negative-stride pointer arithmetic (`README.md:137`) | **Highest:** Requires full machine-code ISA formalization (`x86_64` SSE2/SSSE3/AVX2/AVX-512ICL, `aarch64` NEON/DotProd/I8MM/SVE2) + ABI calling-convention proofs |

#### Why Tier 3 Persists in `rav1d` and `rav1e`

Inspecting `rav1d/build.rs:152-224` reveals **37 distinct x86_64 NASM translation units** (`cdef`, `filmgrain`, `ipred`, `itx`, `loopfilter`, `looprestoration`, `mc` across `sse`, `avx2`, and `avx512` for both `8bpc` and `16bpc`, plus `msac`, `pal`, `refmvs`) and **19 AArch64 GAS units** (including `mc_dotprod` and `mc16_sve` compiled with `-march=armv8.6-a+sve2`, `build.rs:317`). Three concrete technical barriers keep `rav1d` and `rav1e` on external assembly rather than `core::arch`:

1. **`msac` arithmetic decoder register pinning:** `msac.asm` / `msac.S` hand-schedules boolean/multi-symbol range-decoder state (`dif`, `rng`, `cnt`, CDF adaptation) across GPRs and SIMD lanes simultaneously without register spills; C/Rust compilers routinely spill `cnt`/`dif` across branches.
2. **Sub-block transpose and constant-table sharing across `.asm` sections:** `dav1d`'s x86 assembly uses `x86inc.asm` macro metaprogramming, shared `tables.asm` constants with negative-displacement PIC addressing, and cross-width VEX re-encoding (`FORCE_VEX_ENCODING`, `rav1d/build.rs:131`). Notably, `rav1d/build.rs:182-184` documents an upstream constant-coupling hazard (`// TODO(kkysen) avx2 shouldn't be in x86, but a const used in sse is defined in avx2 (a bug)`).
3. **Negative-Result Warning on Naive SIMD (`wuffs/std/png/decode_filter_x86_sse42.wuffs:15-41`):** More SIMD is not monotonically faster. `Wuffs` explicitly comments out `filter_1_distance_3_x86_sse42` and `filter_3_distance_3_x86_sse42` (3-byte RGB PNG Sub and Average filters), documenting that because each 3-byte pixel depends sequentially on the immediately preceding 3-byte pixel (`a[x] = raw[x] + a[x - 3]`), packing 3 bytes into `xmm` via `make_m128i_single_u32` + `_mm_add_epi8` + `poke_u24le!` incurs GPR$\leftrightarrow$XMM domain-crossing latency that **benchmarks slower than scalar C**, whereas 4-byte RGBA (`distance = 4`, `lines 43-58`) wins cleanly via aligned 32-bit `peek_u32le`/`poke_u32le!`.

---

### 3. LLVM Bounds-Check Elimination (BCE) Idioms and Executed Assembly Micro-Probe

`Basis: source + execution`

To isolate why safe Rust codec loops either match C SIMD or suffer 2x+ regressions and residual panic branches, a standalone 3-function probe (`bce_probe.rs`, preserved in full under **Evidence**) was compiled with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (LLVM `22.1.6`) using `--edition=2021 -C opt-level=3 -C target-cpu=x86-64-v3 --emit=asm`.

| Probe Function | Idiom Tested | Emitted x86-64-v3 Asm Lines | Panic Landing Pads Emitted | Vector Instructions Emitted |
| :--- | :--- | :---: | :--- | :--- |
| `naive_strided_u8_to_i16` | `for r in 0..rows { for c in 0..16 { dst[r*16+c] = i16::from(src[r*stride+c]) - 128; } }` | `353` | **16** (`panic_bounds_check` $\times 16$) | **0** (100% scalar) |
| `chunks_strided_u8_to_i16` | Upfront `rows.checked_mul(stride)` + `.get(..need)` + `.chunks_exact(stride)` + `(&s_row[..16]).try_into().unwrap()` | `130` | **0** (100% panic-free) | **4x-unrolled AVX2** (`vpmovzxbw`, `vpaddw`, `vmovdqu`) |
| `split_imdct_butterfly` | Modeled directly on `Symphonia` `Imdct::imdct` (`symphonia-core/src/dsp/mdct.rs:67-137`): `out.split_at_mut(n2)` $\times 4$ + `vec0[n2 - 1 - 2*i]` / `vec1[2*i]` | `122` | **6** (`panic_fmt` $\times 4$, `panic_bounds_check` $\times 2$) | **0 packed** (scalar `vmovss`/`vmulss` only) |

#### Root Causes Verified from Emitted Assembly

1. **64-bit `usize` modular wraparound defeats strided BCE (`naive_strided_u8_to_i16`):** Even though `c` ranges over `0..16`, Rust `usize` multiplication `r * stride` wraps modulo $2^{64}$ in release builds. LLVM cannot assume `r * stride + c` is monotone or `< src.len()`, so it unrolls the inner `0..16` loop into **16 separate bounds comparisons** jumping to `core::panicking::panic_bounds_check` and abandons AVX2 vectorization completely.
2. **Hoisted `checked_mul` + `chunks_exact` + fixed-array `[T; N]` (`chunks_strided_u8_to_i16`):** Checking `rows.checked_mul(stride)` and slicing `src.get(..need_src)` once before the loop establishes `s_row.len() == stride >= 16` in LLVM's ScalarEvolution/InstCombine pass. Notice that `(&s_row[..16]).try_into().unwrap()` inside the loop compiles to **zero instructions and zero panic symbols** because `stride >= 16` dominates the block; LLVM then emits pure `vpmovzxbw` + `vpaddw` + `vmovdqu` across 4 rows per outer iteration.
3. **Why `Symphonia`'s `Imdct::imdct` (`symphonia-core/src/dsp/mdct.rs:67-146`) retains panics and misses packed SIMD:**
   - First, guarding `out.len() < 2 * n` (`leaq (%r11,%r11), %rsi`) overflows `usize` when `n >= 2^{63}`: `2 * n` wraps to a small integer while `n2 = n >> 1 >= 2^{62}`, so LLVM cannot prove the four `out.split_at_mut(n2)` calls (`mdct.rs:94-96`) succeed and retains **4 `panic_fmt` landing pads**. Replacing `2 * n` with `n.checked_mul(2)` (or bounding `n <= 2 * MAX_SIZE` as a type invariant via `InRange`) eliminates all four `split_at_mut` panics.
   - Second, inside the post-FFT butterfly (`mdct.rs:100-118`), `i` ranges over `0..n4` where `n4 = n >> 2` and `n2 = n >> 1`. Because `n2` could have its bit 0 set if `(n & 3) != 0` wasn't propagated through shifts (`n2 = 2 * n4` holds only when bit 1 of `n` is 0!), and because `ri = n2 - 1 - 2 * i` steps backward by 2 while `fi = 2 * i` steps forward by 2, LLVM retains **2 `panic_bounds_check` guards inside `.LBB2_13`** and emits scalar `vmovss`/`vmulss` rather than 4-wide `vmulps`/`vshufps`! This explains both `Symphonia`'s source comment (`mdct.rs:139-141`) and its `1.10x–1.27x` lag behind `FFmpeg` on IMDCT-heavy `AAC-LC` and `Vorbis`.
4. **Value-range witness wrapper (`rav1d/src/in_range.rs:9-46`):** To propagate bitstream-validated integer bounds (such as AV1 `qindex` $\in [0, 255]$ or `tx_size` enum indices) across function boundaries where LLVM loses range metadata, `rav1d` defines `pub struct InRange<T, const MIN: u128, const MAX: u128>(T)` whose `get(self) -> T` injects `unsafe { std::hint::assert_unchecked(self.in_bounds()) }` (`src/in_range.rs:43`). Under formal verification, `InRange` is an ideal zero-cost refinement witness: proving `Self::new` / `Self::const_new` establishes the invariant once, and `assert_unchecked` becomes a machine-checked lemma rather than an unverified `unsafe` assumption.

---

### 4. Concurrent Frame-Pool Aliasing: `rav1d` `DisjointMut` vs. `NihAV` `NABufferRef` Unsoundness

`Basis: source + derived`

Video decoders exhibit an inherent data-access pattern that conflicts with safe Rust's `RwLock` / `&mut [T]` exclusivity:
- **Intra-frame spatial adjacency:** Reconstructing block $(x, y)$ mutates `plane[y..y+h][x..x+w]` while reading top/left edge pixels `plane[y-1][..]` and `plane[..][x-1]` from the **same** plane allocation (`rav1d/src/itx.rs:71-77, 128-134`).
- **Multi-threaded tile/superblock decoding & loop filtering:** Worker threads concurrently mutate disjoint tile columns or superblock rows of the same `Rav1dPicture` while motion compensation reads completed rows of reference frames (`rav1d/src/disjoint_mut.rs:23-26`).

Inspecting how `NihAV` and `rav1d` solve this problem reveals a critical soundness contrast:

1. **Unsound `NABufferRef<T>` in `NihAV` (`nihav-core/src/refs.rs:26-108`):**
   - `nihav-core/src/refs.rs:60-61` declares `unsafe impl<T> Sync for NABufferRef<T> {}` and `unsafe impl<T> Send for NABufferRef<T> {}` with **no `T: Send` or `T: Sync` trait bounds**, allowing non-thread-safe types (`Rc<Cell<u8>>`) to cross threads in safe code.
   - `as_ref(&self)` (`lines 84-90`) and `clone(&self)` (`lines 101-107`) execute `self.ptr.as_mut().unwrap()`, materializing a mutable reference `&mut NABufferData<T>` over the entire allocation (covering both `data: T` and `refs: AtomicUsize`) while shared `&T` references or concurrent clones exist—an immediate violation of Rust's aliasing rules (Stacked Borrows and Tree Borrows) and a data race on `refs` if accessed across threads via `&mut NABufferData<T>`.
   - `DerefMut` (`lines 97-99`) calls `self.as_mut().unwrap()` without checking `refs == 1`, allowing safe callers holding two cloned `NABufferRef<Vec<u8>>` handles to obtain simultaneous `&mut Vec<u8>` and `&Vec<u8>` references to the same buffer (`lines 6`: `"Currently it does not prevent code from reading the data that is being written to"`).

2. **Conditionally Sound `DisjointMut<T>` in `rav1d` (`src/disjoint_mut.rs:34-156`):**
   - `DisjointMut<T>` wraps `UnsafeCell<T>` (`line 38`) and requires `T: AsMutPtr` (`lines 57-58`), computing sub-slice raw pointers via `ptr::addr_of_mut!` / pointer offset without ever materializing an intermediate `&T` or `&mut T` over the whole container.
   - `Send` requires `T: Send` (`line 44`) and `Sync` requires `T: Sync` (`line 73`), plus a manual invariant (`lines 67-72`) that `T::Target` elements are **provenanceless** plain-old-data bytes/integers (`u8`, `u16`, `i16`), ensuring that even a hypothetical release-mode disjointness bug could only corrupt pixel values rather than forge pointer provenance.
   - Under `#[cfg(debug_assertions)]` (including the `opt-dev` and `checked-release` Cargo profiles, `Cargo.toml:51-70`), every `.index()` and `.index_mut()` returns a `DisjointImmutGuard` / `DisjointMutGuard` that registers live byte ranges in `bounds: debug::DisjointMutAllBounds` (`lines 35-36, 103-106`) and panics on any overlapping mutable borrow across all test vectors. In `[profile.release]`, `#[cfg_attr(not(debug_assertions), repr(transparent))]` compiles the guards down to bare `&'a [V]` / `&'a mut [V]` slices with **zero runtime lock or tracking overhead** (`lines 33, 97, 157`).

---

### 5. Panic-Freedom, Fallible Allocation, and SIMD-vs-Scalar Divergence Audit

`Basis: source`

Evaluating the eight implementations against Priority 1 (**UB-freedom**) and Priority 2 (**Panic-freedom / OOM-abort freedom** on adversarial media inputs) exposes five concrete vulnerability patterns that clean-room verification must eliminate:

| Project | Unchecked Heap Alloc (OOM Abort)? | Arithmetic Overflow Mode (Release) | Documented / Observed Panic Surfaces on Malformed Input | SIMD-vs-Scalar Behavioral / Panic Divergence |
| :--- | :--- | :--- | :--- | :--- |
| **`google/wuffs`** | **Zero alloc** (` Sans-I/O`, caller-owned `workbuf`) | **Compile-time proven impossible** (`wuffs gen` rejects unproven `c + 1`) | **Zero:** No panic, abort, division-by-zero, or OOB construct exists in generated C | Bit-exact mimic tests (`wuffs test`); SIMD uses explicit rounding corrections (`decode_filter_x86_sse42.wuffs:113-116`) |
| **`mozilla/mp4parse-rust`** | **Banned at compile time** (`struct Vec; struct Box; struct HashMap; struct String;` shadow stdlib at `mp4parse_capi/src/lib.rs:66-73`; uses `TryVec`/`TryBox`) | **`overflow-checks = true`** (`Cargo.toml:7-11`) + `CheckedInteger<i64>` (`lib.rs:133`) | Low: residual `.try_into()` / slice paths return `Mp4parseStatus::Invalid` / `Oom`, though `overflow-checks = true` turns unguarded arithmetic into panic unless wrapped | Scalar parser only (`no SIMD`) |
| **`memorysafety/rav1d`** | Custom `AlignedVec` / `rav1d_picture_alloc` (fallible C API returns `ENOMEM`, some internal `Vec`s infallible) | Wrapping (`panic = "abort"` in `dev` & `release`, `Cargo.toml:49, 59`) | **Process-terminating (`abort`):** `DisjointMutGuard::cast_slice` `.unwrap()` (`disjoint_mut.rs:117`), `wrap_fn_ptr!` default `unimplemented!()` (`wrap_fn_ptr.rs:76`), `assert!(w >= 4 && w <= 64)` (`itx.rs:55-57`) | Checked via `checkasm` + Meson differential conformance suite (`README.md:118-139`) |
| **`pdeljanov/Symphonia`** | Standard `Vec`/`Box` (`mdct.rs:43, 57`: `vec![...; n2]`) | Wrapping in release | **Explicitly documented (`README.md:68`):** `"Good"` status formats (`CAF`, `MKV/WebM`, `ADPCM`) `"may panic"`; `clippy::unwrap_used = "warn"` (`Cargo.toml:48`), not `deny`; `assert_eq!` in `Imdct::imdct` (`mdct.rs:76, 78`) | `Imdct` float associativity differs from `FFmpeg` SIMD within $\sim 10^{-5}$ (`mdct.rs:199`) |
| **`etemesi254/zune-image`** | Standard `alloc::vec::Vec` (bounded by `DecoderOptions` max dimensions) | Wrapping (`wa`/`ws`/`wm` explicit `wrapping_*` in `scalar.rs:16-28`, implicit `+` in `avx2.rs:130`) | **Explicitly tolerated (`zune-jpeg/README.md:160`):** `"Panics are okay, but should be fixed when reported"`; `clippy::panic` is `warn` (`lib.rs:300`) | **Confirmed panic divergence:** `scalar.rs:162-166` falls back to `&mut tmp` on short `out_vector`, whereas `avx2.rs:56-71, 136-140` calls `.get_mut(...).unwrap()` and panics! Also lossy upsampling/IDCT intentionally non-bit-exact with `libjpeg-turbo` (`README.md:173-175`) |
| **`rust-av/rav1e`** | Standard `Vec` + `AlignedVec` (`v_frame`) | Wrapping in release | Encoder `assert!` / `.unwrap()` in tiling, RDO, and `asm` dispatch | Tested via `check_asm` feature (`Cargo.toml:46`) and `decode_test_dav1d` round-trip |
| **`image-rs/image`** | Soft `Limits` (`max_alloc = 512 MiB` default, `src/io/limits.rs:53`), non-strict (`lines 37-40`) | Wrapping (`saturating_mul` in `limits.rs:147-149`) | `Limits::free_usize` explicitly `panic!`s if `u64::try_from(amount)` fails when `max_alloc.is_some()` (`limits.rs:170-172`), plus sub-decoder panics | Delegates JPEG to `zune-jpeg` (`Cargo.toml:69, 94`) and AVIF to `dav1d` (`Cargo.toml:57, 108`) |
| **`NihAV`** | Standard `Vec` + `NABufferRef` (`Box::new`) | Wrapping in release | `validate!` macro returns `DecoderError`, but extensive slice indexing `buf[idx]` and `NABufferRef::deref_mut` `.unwrap()` (`refs.rs:98`) | Scalar reference only |

#### Deep Dive: The `zune-jpeg` Scalar-vs-AVX2 Panic Divergence (`scalar.rs` vs. `avx2.rs`)

Direct comparison of `crates/zune-jpeg/src/idct/scalar.rs:159-166` and `crates/zune-jpeg/src/idct/avx2.rs:56-71, 136-140` at commit `2cdbbf554e7da373d3418ab327a0db7c4abb50cd` uncovers a concrete **differential panic bug** between the safe scalar fallback and the `#[target_feature(enable = "avx2")]` path:

- In `idct_int` (`scalar.rs:159-166`):
  ```rust
  // to prevent some bad images from crashing
  let mut tmp = [0; 8];
  let out: &mut [i16; 8] = out_vector
      .get_mut(pos..pos + 8)
      .unwrap_or(&mut tmp)
      .try_into()
      .unwrap();
  ```
  When a malformed JPEG geometry or stride causes `pos + 8 > out_vector.len()` (or `pos + 8` wraps? Note `pos + 8` can still overflow if `pos >= usize::MAX - 7`), `scalar.rs` absorbs the out-of-bounds write into stack-local `tmp` without panicking.
- In `idct_avx2` (`avx2.rs:56-71` and `136-140`):
  ```rust
  _mm_storeu_si128(
      ($out).get_mut($index..$index + 8).unwrap().as_mut_ptr().cast(),
      _mm256_extractf128_si256::<0>(c),
  );
  ```
  `idct_avx2` omits the `unwrap_or(&mut tmp)` fallback and calls `.unwrap()` unconditionally! Consequently, fuzzing or testing on a target with `DecoderOptions::set_use_unsafe(false)` (or on AArch64 where `avx2.rs` is compiled out) succeeds silently on short `out_vector` buffers that **deterministically panic on AVX2 hosts**. Furthermore, at `avx2.rs:130` (`((in_vector[0] + 4 + 1024) >> 3)`), signed `i32` addition `+` is used instead of `scalar.rs:32`'s `wa(wa(in_vector[0], 4), 1024)` (`wrapping_add`), creating a second divergence whenever debug/release overflow checks are enabled (`Cargo.toml` / fuzz builds).

---

### 6. Compile-Time, Dependency, and Binary-Size Footprints

`Basis: documentation + source`

1. **Binary Size Floor (`Wuffs` vs. C vs. Monomorphized Rust):**
   - `Wuffs` (`doc/binary-size.md:6-54, 115-125`) compiles **15 formats/codecs simultaneously** (Adler-32, BMP, Bzip2, CBOR, CRC-32, Deflate, GIF, Gzip, JSON, LZW, NIE, PNG, TGA, WBMP, Zlib + pixel format converters) into a **322,264-byte** `libwuffs.so` (`398,014 B` `libwuffs.a` with Clang 11). Individual object files are minuscule: `wuffs-std-deflate.o` is **25,344 B**, `wuffs-std-gif.o` + `wuffs-std-lzw.o` is **31,880 B** (vs. `51,940 B` `libgif.a`), and `wuffs-std-png.o` is **56,560 B** (vs. `374,338 B` `libpng16.a` — a **6.6x static footprint reduction**).
   - In contrast, Rust video codecs monomorphize entire pipelines across bitdepth traits: `rav1d` instantiates `inv_txfm_add_rust<const W: usize, const H: usize, const TYPE: TxfmType, BD: BitDepth>` (`src/itx.rs:137`) across `BitDepth8` (`u8`/`i16`) and `BitDepth16` (`u16`/`i32`) (`Cargo.toml:45-46`), requiring `lto = "fat"`, `codegen-units = 1`, and `panic = "abort"` (`Cargo.toml:57-60`) to strip landing pads and deduplicate monomorphized codegen—at the cost of serializing whole-crate LLVM optimization during release builds.
2. **Dependency Hygiene and Build-Time Toolchains:**
   - `rav1e` (`Cargo.toml:101-103, 70-88`) explicitly vendors `vergen` to shed transitive `failure` build times, gates `serde` and `wasm-bindgen` behind `noop_proc_macro` stubs (`src/lib.rs:70-88`) to avoid compiling `syn`/`quote` proc-macro graphs when serialization is unused, and hashes `.asm` inputs into `OUT_DIR/asm.hash` (`build.rs:34-75`) to skip redundant NASM invocations.
   - `zune-jpeg` and `zune-png` achieve sub-second clean compiles by depending **only on `zune-core`** (plus `zune-inflate` for PNG) with `#![no_std]` + `alloc` compatibility (`zune-jpeg/src/lib.rs:314-318`), whereas `image-rs/image` (`Cargo.toml:42-101`) pulls `moxcms`, `exr`, `ravif` (which transitively pulls `rav1e`!), `png`, `tiff`, `gif`, `image-webp`, `qoi`, `zune-jpeg`, and `rayon` under `default-formats`.
   - **Debug-Build Performance Cliff (`zune-jpeg/README.md:208-216`, `rav1d/Cargo.toml:51-55`):** Both `zune-jpeg` and `rav1d` document that unoptimized (`opt-level = 0`) Rust builds suffer catastrophic slowdowns (`10x–50x+`) on `core::arch` SIMD intrinsics and `DisjointMut` debug guards, requiring `[profile.opt-dev] opt-level = 1` (`rav1d`) or `[profile.dev.package.zune-jpeg] opt-level = 3` (`zune-jpeg`) even to run conformance tests without timeouts.

---

### 7. Clean-Rewrite & Formal Verification Implications

`Basis: derived`

Mapping the empirical evidence from all eight rewrites onto the four-level media verification stack yields concrete architectural rules for a formally verified clean-room media engine:

1. **Priority 1 (UB-Freedom):**
   - Audio, container demuxing, lossless compression, and still-image codecs (`FLAC`, `ALAC`, `MP1`–`MP3`, `Vorbis`, `Opus`, `WAV`, `OGG`, `MP4`, `MKV`, `PNG`, `GIF`, `Deflate`) require **zero external assembly and zero raw-pointer `unsafe`** to match or beat C/FFmpeg throughput, provided FFT/MDCT kernels use verified SIMD intrinsics or chunked butterflies.
   - High-bit-rate 2D block video codecs (`H.264`, `HEVC`, `VP9`, `AV1`) require **two** distinct verified `unsafe` substrates: (a) a formally verified disjoint-region capability wrapper replacing `rav1d`'s runtime-unchecked release `DisjointMut<T>` (`src/disjoint_mut.rs:60-65`) with static spatial-disjointness proofs over shared picture planes, and (b) machine-checked ISA semantics (`x86_64` AVX2/AVX-512, `aarch64` NEON/DotProd/SVE2) or verified `core::arch` lowering for 2D subpel MC, inverse transforms, CDEF/SAO/ALF, and CABAC/MSAC kernels.
2. **Priority 2 (Panic-Freedom & Fallible Allocation):**
   - `#![forbid(unsafe_code)]` (`Symphonia`, `zune-inflate`) leaves extensive panic surfaces (`panic_bounds_check`, `split_at_mut` `panic_fmt`, `assert!`, `.unwrap()`, and infallible `Vec` OOM aborts).
   - Adopting `mp4parse-rust`'s compile-time shadowing of `Vec`/`Box`/`HashMap`/`String` (`mp4parse_capi/src/lib.rs:66-73`) together with `Wuffs`-style `InRange` refinement witnesses (`rav1d/src/in_range.rs`) and hoisted `checked_mul` + `chunks_exact` loops simultaneously **proves panic-freedom** and **unlocks LLVM AVX2/NEON auto-vectorization** (as demonstrated in `chunks_strided_u8_to_i16`).
3. **Priority 3 (Reference & SIMD-vs-Scalar Equivalence):**
   - SIMD and scalar paths must share **identical domain preconditions and error/saturation behavior**. The `zune-jpeg` `scalar.rs` vs. `avx2.rs` discrepancy proves that bolting `unwrap()` onto a `#[target_feature]` kernel while scalar code uses `unwrap_or(&mut tmp)` creates target-specific crashes invisible to scalar fuzzing or scalar verification.
   - Where `Wuffs` proves that hardware instructions (`_mm_avg_epu8` rounding `(a + b + 1) >> 1`) differ by 1 LSB from codec specifications (PNG Filter 3 Average `(a + b) >> 1`), an algebraic 1-bit correction (`_mm_sub_epi8(avg, (a ^ b) & 1)`, `decode_filter_x86_sse42.wuffs:110-116`) achieves **bit-exact** SIMD-to-scalar equivalence at full vector throughput.
4. **Priority 4 (Functional Specification Conformance):**
   - Historical C artifacts in `FFmpeg` and `dav1d`—such as negative pointer strides (`rav1d` `Rav1dPictureDataComponentOffset`), out-of-band `AV_INPUT_BUFFER_PADDING_SIZE` overread slops, and global mutable function tables—are **legacy C workarounds**, not algorithmic necessities. `Wuffs` (`iterate` tail loops) and `zune-jpeg` (`ZCursor` lookahead bitbuffers) achieve C-beating or near-C throughput over exact-length slices without buffer overread padding.

## Boundaries

- **Not examined:** Multi-threaded scaling efficiency (`4`–`64` threads) of `rav1d`'s `parking_lot`-based frame/tile task scheduler (`src/thread_task.rs`) vs. `dav1d`'s `pthread` scheduler under contention was not benchmarked locally; reported `rav1d` `5%–11%` figures derive from upstream ISRG Prossimo / Immunant benchmark campaigns across single- and multi-threaded runs.
- **Not examined:** Rust `core::simd` (`#![feature(portable_simd)]`) codegen quality on `zune-imageprocs` (`crates/zune-imageprocs/src/premul_alpha/std_simd.rs`) was not micro-benchmarked across `aarch64` or `riscv64` targets; portable-SIMD legalization trade-offs are covered separately in corpus package `portable-simd-repr-simd-legalization-and-cross-arch-cost-certificates`.
- **Known not to apply:** `Wuffs`'s zero-allocation static-workbuf model (`README.md:57-64`) does **not** directly transfer without modification to multi-reference video codecs (`H.264` 16-frame DPB, `AV1` 8-slot reference pool with dynamic resolution changes / super-resolution), where caller-supplied frame pool arenas (`FrameBufferPool`) must still manage variable-count reference surfaces dynamically.
- **Known not to apply (Refuted Attractive Conclusion #1):** It is **false** that `#![forbid(unsafe_code)]` Rust media decoders are automatically safe against untrusted-input denial-of-service. Both `Symphonia` (`mdct.rs:76-78`, `README.md:68`) and `zune-jpeg` when compiled without `x86`/`neon` (`scalar.rs:166`, `README.md:160`) contain reachable panic paths and infallible heap allocations.
- **Known not to apply (Refuted Attractive Conclusion #2):** It is **false** that LLVM's optimizer automatically eliminates bounds checks on constant-width inner loops (`for c in 0..16`) over 2D strided slices (`src[r * stride + c]`). Without an explicit non-overflowing `rows.checked_mul(stride)` + subslice witness, 64-bit modular `usize` wraparound forces `rustc`/LLVM 22 to emit 16 `panic_bounds_check` branches and scalarize the loop.
- **Unsupported:** `rav1d` (`v1.1.1`) currently requires nightly Rust for `arm` (32-bit) and `riscv64` feature detection (`src/lib.rs:1-5`, `README.md:11-12`) and requires external NASM $\ge 2.14$ when the default `asm` feature is enabled on `x86`/`x86_64` (`build.rs:290`).

## Evidence

### Studied Upstream Repositories and Pinned Revisions

| Subject | Repository | Immutable Revision (40-hex SHA) | Key Inspected Paths & Lines |
| :--- | :--- | :--- | :--- |
| `rav1d` (`v1.1.1`) | `memorysafety/rav1d` | `2e7216c20ac2a75de204d6c8d7268b75a45959b4` | `Cargo.toml:39-70`, `build.rs:61-330`, `src/lib.rs:1-250`, `src/disjoint_mut.rs:1-170`, `src/in_range.rs:1-105`, `src/wrap_fn_ptr.rs:1-101`, `src/itx.rs:38-140` |
| `dav1d` | `videolan/dav1d` | `9af5ae4eb5204706c7f381ec62635237179f172e` | Reference C baseline mirrored by `rav1d` (`DAV1D_API_VERSION` `7.0.0`) |
| `Symphonia` (`v0.6.1`) | `pdeljanov/Symphonia` | `5f879df0bf309246a48d57caae457fd8c0e2a5cb` | `Cargo.toml:1-51`, `README.md:61-191`, `BENCHMARKS.md:1-140`, `symphonia-core/src/lib.rs:1-28`, `symphonia-core/src/dsp/mdct.rs:16-202`, `symphonia-core/src/io/bit.rs:1-140` |
| `Wuffs` (`v0.3`) | `google/wuffs` | `a87f0bb85b9406d29f48a1c03b6f42c4585145f6` | `README.md:12-242`, `doc/benchmarks.md:1-481`, `doc/binary-size.md:1-130`, `std/png/decode_filter_x86_sse42.wuffs:13-150` |
| `zune-image` | `etemesi254/zune-image` | `2cdbbf554e7da373d3418ab327a0db7c4abb50cd` | `README.md:1-155`, `benchmarks/benchmark-results.md:1-136`, `crates/zune-jpeg/README.md:155-230`, `crates/zune-jpeg/src/lib.rs:294-351`, `crates/zune-jpeg/src/idct/scalar.rs:15-293`, `crates/zune-jpeg/src/idct/avx2.rs:46-140` |
| `rav1e` (`v0.5.0`) | `rust-av/rav1e` | `d2af1842f6e4b826e528ef4bf16c2454e177cd3f` | `Cargo.toml:25-170`, `build.rs:34-150`, `src/lib.rs:70-245`, `src/asm/mod.rs:10-17` |
| `mp4parse-rust` (`v0.17.0`) | `mozilla/mp4parse-rust` | `d3a9abfc93b22687e5e5cd9df86697adcb7d5887` | `Cargo.toml:1-11`, `mp4parse/Cargo.toml:29-36`, `mp4parse_capi/src/lib.rs:37-160` |
| `image` (`v0.25.9`) | `image-rs/image` | `e70e9fe5073f4b298a33b72993847241a8eaaca6` | `Cargo.toml:42-111`, `src/lib.rs:191-263`, `src/io/limits.rs:32-178` |
| `NihAV` | `https://git.nihav.org/nihav.git` | `904a660eca4a646b4618d11bb6ef025a6e50f725` | `README.md:1-19`, `nihav-core/src/lib.rs:1-28`, `nihav-core/src/refs.rs:1-125`, `nihav-core/src/io/bitreader.rs:1-95` |
| `FFmpeg` | `FFmpeg/FFmpeg` | `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` | C audio/video baseline (`libavcodec`) |

### Preserved Standalone Assembly Micro-Probe (`bce_probe.rs`)

Observed on `2026-11-20` on `x86_64-unknown-linux-gnu` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with LLVM `22.1.6`:

```rust
#![crate_type = "lib"]

#[no_mangle]
pub fn naive_strided_u8_to_i16(src: &[u8], dst: &mut [i16], stride: usize, rows: usize) {
    for r in 0..rows {
        for c in 0..16 {
            dst[r * 16 + c] = i16::from(src[r * stride + c]) - 128;
        }
    }
}

#[no_mangle]
pub fn chunks_strided_u8_to_i16(src: &[u8], dst: &mut [i16], stride: usize, rows: usize) -> bool {
    if stride < 16 { return false; }
    let Some(need_src) = rows.checked_mul(stride) else { return false; };
    let Some(need_dst) = rows.checked_mul(16) else { return false; };
    let (Some(s_all), Some(d_all)) = (src.get(..need_src), dst.get_mut(..need_dst)) else {
        return false;
    };
    for (s_row, d_row) in s_all.chunks_exact(stride).zip(d_all.chunks_exact_mut(16)) {
        let s16: &[u8; 16] = (&s_row[..16]).try_into().unwrap();
        let d16: &mut [i16; 16] = d_row.try_into().unwrap();
        for i in 0..16 {
            d16[i] = i16::from(s16[i]) - 128;
        }
    }
    true
}

#[no_mangle]
pub fn split_imdct_butterfly(
    scratch: &[(f32, f32)],
    twiddle: &[(f32, f32)],
    out: &mut [f32],
    n: usize,
) -> bool {
    let n2 = n >> 1;
    let n4 = n >> 2;
    if n == 0 || (n & 3) != 0 || scratch.len() < n2 || twiddle.len() < n2 || out.len() < 2 * n {
        return false;
    }
    let (vec0, rest) = out.split_at_mut(n2);
    let (vec1, rest) = rest.split_at_mut(n2);
    let (vec2, vec3) = rest.split_at_mut(n2);
    let (vec3, _) = vec3.split_at_mut(n2);
    for (i, (&(xr, xi), &(wr, wi))) in scratch[..n4].iter().zip(twiddle[..n4].iter()).enumerate() {
        let re = wr * xr + wi * xi;
        let im = wi * xr - wr * xi;
        let fi = 2 * i;
        let ri = n2 - 1 - 2 * i;
        vec0[ri] = -im;
        vec1[fi] = im;
        vec2[ri] = re;
        vec3[fi] = re;
    }
    true
}
```

Reproduction command:

```bash
rustc --edition=2021 -C opt-level=3 -C target-cpu=x86-64-v3 --emit=asm bce_probe.rs -o bce_probe.s
```

Recorded symbol/instruction counts per function in `bce_probe.s`:
- `naive_strided_u8_to_i16`: `353` assembly lines, `16` calls to `_ZN4core9panicking18panic_bounds_check...`, `0` vector instructions.
- `chunks_strided_u8_to_i16`: `130` assembly lines, `0` panic calls (`[]`), `4x`-unrolled AVX2 `vpmovzxbw` + `vpaddw` + `vmovdqu` instructions.
- `split_imdct_butterfly`: `122` assembly lines, `4` calls to `panic_fmt` + `2` calls to `panic_bounds_check`, scalar `vmovss`/`vmulss`/`vsubss` instructions only.

## Revalidation

1. **Compiler BCE & Vectorization Regression Probe (<1 second):** Save the `bce_probe.rs` listing above to `/tmp/bce_probe.rs`, compile with `rustc --edition=2021 -C opt-level=3 -C target-cpu=x86-64-v3 --emit=asm /tmp/bce_probe.rs -o /tmp/bce_probe.s`, and check:
   - Whether `chunks_strided_u8_to_i16` still emits zero `panic` symbols and `vpmovzxbw` vector instructions;
   - Whether a newer LLVM release eliminates the 2 inner-loop `panic_bounds_check` branches or SLP-vectorizes `split_imdct_butterfly` when `out.len() < 2 * n` is strengthened to `n.checked_mul(2).is_none_or(|n_out| out.len() < n_out)`.
2. **`zune-jpeg` SIMD-vs-Scalar Panic Divergence Check:** Diff `crates/zune-jpeg/src/idct/scalar.rs` (`idct_int`) against `crates/zune-jpeg/src/idct/avx2.rs` (`idct_avx2` / `permute_store!`). If `avx2.rs` still invokes `.get_mut($index..$index + 8).unwrap()` while `scalar.rs` uses `.unwrap_or(&mut tmp)`, a minimal test passing a 64-element `[0i32; 64]` with `[1] = 1` and a 56-element `out_vector` (`stride = 8`) deterministically reproduces the AVX2 panic vs. scalar survival.
3. **`rav1d` Assembly & `DisjointMut` Audit:** Inspect `rav1d/Cargo.toml` (`[features]` and `[profile.release]`) and `rav1d/src/disjoint_mut.rs` to check whether `asm` remains enabled by default, whether `panic = "abort"` remains active, and whether `DisjointMut` has migrated any release-mode disjointness checks into static types.
4. **`NihAV` `NABufferRef` Soundness Check:** Inspect `nihav-core/src/refs.rs` (`unsafe impl<T> Send/Sync` and `impl<T> DerefMut for NABufferRef<T>`) on `git.nihav.org` to check whether `T: Send + Sync` bounds, `UnsafeCell<T>` interior mutability, or `refs == 1` exclusivity checks have been added; running `cargo +nightly miri test` on the 5-line clone-and-mutate snippet (`let mut a = NABufferRef::new(vec![0u8; 16]); let b = a.clone(); let r = &b[0]; a[0] = 1; let _ = *r;`) deterministically flags Stacked/Tree Borrows UB whenever `NABufferRef` remains unchanged.
