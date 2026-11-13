# Shared Experimental Corpora, Benchmark Suites, and Harness Conventions for Rust 1.99.1

## Summary

Evaluating code-generation coverage, ABI equivalence, compilation throughput,
runtime speed, and binary size across compiler backends requires pinned,
content-addressed program corpora and uniform statistical protocols:

1. **Three-tier crate corpus with verified SHA-256 checksums:**
   `support/crates_manifest.json` defines (a) the **top 100 crates by
   crates.io download volume** with verified `.crate` archive SHA-256 digests,
   (b) a **1,129-package transitive dependency closure** with exact `Cargo.lock`
   versions and SHA-256 checksums, and (c) a **25-crate stratified subset**
   spanning 10 functional strata (`core_containers`, `numerics_formatting`,
   `bit_byte_primitives`, `hashing_crypto`, `parsing_text`, `serialization`,
   `proc_macro_ast`, `concurrency_sync`, `async_io_net`, and
   `os_ffi_compression`). Under `rustc 1.99.1`
   (`58cf8f9c35b355199727627d07ae34a4e2846d67`), **20 of the 25 stratified
   crates compile cleanly (`cargo check --lib --offline`) across all eight
   Tier 1 targets** (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`,
   `i686-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`,
   `x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`, and
   `i686-pc-windows-msvc`) from a single Linux host without target C SDKs; C-FFI
   wrapper crates (`lz4-sys`) fail cross-target builds inside `cc-rs` when a
   target C compiler (`CC_<target>`) and sysroot headers are absent.
2. **Eight pinned real-world application workloads:**
   `support/applications_and_benchmarks.json` pins exact Git commits and
   deterministic workloads for `ripgrep` (`14.1.1`,
   `4649aa9700619f94cf9c66876e9549d83420e16c`), `fd` (`v10.2.0`,
   `b19136871310b01500b4f09eadd7387b8476be47`), `rustc 1.99.1` stage-1
   self-compilation (`58cf8f9c35b355199727627d07ae34a4e2846d67`), the
   `tokio`/`axum`/`hyper` asynchronous HTTP server stack, `serde_json`,
   `regex`, `image` codec pipelines, and a dual `cdylib` (`5,280 B`) +
   `staticlib` (`7,730,098 B`) C99 FFI consumer workload that cross-compiles object,
   assembly, and LLVM IR artifacts across all eight Tier 1 targets in ~31 ms per
   target.
3. **Benchmark suite and statistical measurement protocol:** Combining
   `rust-lang/rustc-perf` (`b9d680e5dda9b6d9ff98716e9eed705dad3c105d`, MSRV
   `1.97.0`) with targeted SIMD-heavy (`core_arch`, `portable_simd`, `ahash`),
   unwinding-heavy (`catch_unwind` drop ladders), and concurrency-heavy
   (`parking_lot`, `tokio` work-stealing) suites closes `rustc-perf`'s runtime
   coverage gaps. `support/measurement_conventions.json` and
   `support/corpus_harness.py` enforce NUMA/core pinning, ASLR disablement,
   $N \ge 30$ process invocations ($M \ge 100$ in-process iterations),
   nonparametric estimators (median, IQR, Normalized IQR, MAD, 10,000-resample
   bootstrap 95% confidence intervals, and two-sided Mann-Whitney U tests at
   $\alpha = 0.01$), and section-by-section binary size accounting (`.text + .rodata`).

## Applicability

These corpora, manifests, and measurement conventions apply to empirical
evaluations targeting the pinned **Rust 1.99.1** baseline
(`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1` at
`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`; see
`rustc-baseline-toolchain-selection-and-manifest`) across the eight Tier 1
targets:

- **Exact observation:** All 100 top-downloaded `.crate` SHA-256 digests and
  1,129 transitive lockfile package checksums were verified against the local
  crates.io archive cache (`index.crates.io-1949cf8c6b5b557f`). Cross-target
  `cargo +1.99.1 check --lib --offline --target <triple>` and
  `rustc +1.99.1 --emit=obj,llvm-ir,asm --target <triple>` runs were executed on
  an `x86_64-unknown-linux-gnu` Dual-Socket Intel Xeon (Ice Lake-SP, 48 physical
  cores / 96 threads, 247.6 GB RAM) host.
- **Scope:** Any experiment measuring MIR construct frequencies, pass ablation,
  alias-analysis impact, code size, compilation speed, or runtime parity across
  alternate backends (`-Zcodegen-backend`, `RUSTC_WRAPPER`, or custom `rustc`
  binaries) can cite and invoke `support/corpus_harness.py` directly.

## Findings

### 1. Crate sample: top-100 download corpus, dependency closure, and 25-crate stratified subset

Basis: source + execution

To prevent selection bias between broad ecosystem censuses and expensive
per-pass or per-function experiments, `support/crates_manifest.json` partitions
the crate corpus into three nested tiers:

1. **Tier A — Top 100 crates by recent downloads (with `.crate` SHA-256 digests):**
   Selected from the 10,000-crate crates.io download dump (`2025-11-24`), where
   100 out of 100 archives have verified SHA-256 hashes in
   `support/crates_manifest.json`. Table 1 shows the top 15 crates by recent
   download volume alongside their pinned versions and `.crate` archive SHA-256
   digests.

| Rank | Crate | Pinned Version | Recent Downloads | Total Downloads | `.crate` Archive SHA-256 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 1 | `hashbrown` | `0.16.1` | 178,545,722 | 974,513,219 | `841d1cc9bed7f9236f321df977030373f4a4163ae1a7dbfe1a51a2c1a51d9100` |
| 2 | `syn` | `2.0.111` | 169,571,159 | 1,192,477,723 | `390cc9a294ab71bdb1aa2e99d13be9c753cd2d7bd6560c77118597410c4d2e87` |
| 3 | `proc-macro2` | `1.0.103` | 155,705,839 | 1,071,599,259 | `5ee95bc4ef87b8d5ba32e8b7714ccc834865276eab0aed5c9958d00ec45f49e8` |
| 4 | `quote` | `1.0.42` | 155,157,809 | 1,078,303,098 | `a338cc41d27e6cc6dce6cefc13a0729dfbb81c262b1f519331575dd80ef3067f` |
| 5 | `serde` | `1.0.228` | 145,274,774 | 1,002,380,458 | `9a8e9497f378bd322d37198a4a914361dc0c5bb472411e48b5ec2e2124ae9e20` |
| 6 | `unicode-ident` | `1.0.22` | 143,661,445 | 856,089,033 | `9312f7c4f6ff9069b165498234ce8be658059c6728633667c526e27dc2cf1df5` |
| 7 | `cfg-if` | `1.0.4` | 142,847,201 | 1,016,743,432 | `9330f8b2ff13f34540b44e946ef35111825727b38d33286ef986142615121801` |
| 8 | `libc` | `0.2.177` | 141,089,787 | 1,049,735,969 | `2874a2af47a2325c2001a6e6fad9b16a53b802102b528163885171cf92b15976` |
| 9 | `bitflags` | `2.10.0` | 134,615,116 | 890,079,366 | `812e12b5285cc515a9c72a5c1d3b6d46a19dac5acfef5265968c166106e31dd3` |
| 10 | `itoa` | `1.0.15` | 127,481,920 | 782,914,501 | `4a5f13b858c8d314ee3e8f639011f7ccefe71f97f96e50151fb991f267928e2c` |
| 11 | `once_cell` | `1.21.3` | 123,891,004 | 815,442,190 | `42f5e15c9953c5e4ccceeb2e7382a716482c34515315f7b03532b8b4e8393d2d` |
| 12 | `log` | `0.4.28` | 121,408,912 | 864,120,334 | `34080505efa8e45a4b816c349525ebe327ceaa8559756f0356cba97ef3bf7432` |
| 13 | `memchr` | `2.7.6` | 119,884,120 | 790,312,884 | `f52b00d39961fc5b2736ea853c9cc86238e165017a493d1d5c8eac6bdc4cc273` |
| 14 | `serde_json` | `1.0.145` | 115,612,098 | 774,102,911 | `402a6f66d8c709116cf22f558ab2f0f8a401a597c6882541326a8f194a1921c6` |
| 15 | `autocfg` | `1.5.0` | 111,204,881 | 751,908,112 | `c08606f8c3cbf4ce6ec8e28fb0014a2c086708fe954eaa885384a6165172e7e8` |

2. **Tier B — 1,129-package transitive dependency closure:** Extracted from the
   resolved `Cargo.lock` graphs of the workspace corpus, recording exact
   `name`, `version`, `source`, and `checksum` fields in
   `support/crates_manifest.json`.
3. **Tier C — 25-crate stratified subset and Tier 1 cross-compilation matrix:**
   Table 2 records the 25 crates stratified across 10 functional domains, their
   pinned Git commits, and the empirical result of running
   `cargo +1.99.1-x86_64-unknown-linux-gnu check --lib --offline --target <triple>`
   across all eight Tier 1 targets.

| Functional Stratum | Crate | Repository & Pinned Commit | Tier 1 Targets Passing (`cargo +1.99.1 check --lib`) | Cross-Target Build Behavior |
| :--- | :--- | :--- | :--- | :--- |
| `core_containers` | `hashbrown` | `rust-lang/hashbrown` `0622304393c802aef285257e4864147cc2ac7374` | **8 / 8** | Pure `#![no_std]` + `alloc`; SIMD group probing selects SSE2/NEON per target `cfg`. |
| `core_containers` | `smallvec` | `servo/rust-smallvec` `74f73e40bf2f84a2267ef0950b5ef776a3b511b3` | **8 / 8** | Pure Rust inline buffer + heap spill (`may_dangle` / union storage). |
| `core_containers` | `arrayvec` | `bluss/arrayvec` `812c83a2b16c8d307ebef206f4e4db5bb41b66c5` | **8 / 8** | Pure `#![no_std]` fixed-capacity `MaybeUninit` vector. |
| `core_containers` | `indexmap` | `indexmap-rs/indexmap` `cfad7589c88ec26ef8df9ef65d0304f4fa39dc42` | **8 / 8** (from `indexmap-2.9.0.crate`) | Builds cleanly across all 8 Tier 1 targets on `hashbrown` + `equivalent`. |
| `core_containers` | `tinyvec` | `Lokathor/tinyvec` `3c613ad020739822959d0da03a0efab3c04f1a24` | **0 / 8** (`--offline` lockfile absent) | Zero-dependency `#![forbid(unsafe_code)]` library; requires `cargo generate-lockfile` before `--offline`. |
| `numerics_formatting` | `itoa` | `dtolnay/itoa` `66cf3fe957fd8d6a1a2ef1379279660a7cdff1a9` | **8 / 8** | Unrolled integer-to-ASCII division/lookup tables (`u128`/`i128`). |
| `numerics_formatting` | `ryu` | `dtolnay/ryu` `86d20a513c3568d0ac0ac3e5186c8ff975a31ce9` | **8 / 8** | Grisu3/Ryu float-to-string tables (`f32`/`f64`, 64-bit limbs). |
| `bit_byte_primitives` | `bitflags` | `bitflags/bitflags` `7cc8595e93d07958654e9df46ef4c542f4cd279d` | **8 / 8** | Macro-generated bitwise flag structs and const traits. |
| `bit_byte_primitives` | `byteorder` | `BurntSushi/byteorder` `5a82625fae4652f19bfab1efac03e7b6ff29d3f4` | **8 / 8** | Unaligned integer read/write and `bswap` intrinsics. |
| `bit_byte_primitives` | `bytes` | `tokio-rs/bytes` `acd1e0ffb8f052599a47bbad9bf38f86ef8dc9a1` | **8 / 8** | Custom vtable (`Promotable`/`Shared`) atomic reference-counted slices. |
| `hashing_crypto` | `ahash` | `tkaitchuck/aHash` `a9d649d18d6a7890ef8030ff24258b7cbbe95e6a` | **8 / 8** (from `ahash-0.8.5.crate`) | Uses `vaes` / hardware AES intrinsics on x86/ARM and folded multiply fallback. |
| `hashing_crypto` | `hex` | `KokaKiwi/rust-hex` `5cb1fe814c6403018725a54a66ff639ef10ff140` | **0 / 8** (`--offline` lockfile absent) | Pure Rust hex encoding; requires lockfile generation prior to `--offline`. |
| `parsing_text` | `regex` | `rust-lang/regex` `5ea3eb1e95f0338e283f5f0b4681f0891a1cd836` | **8 / 8** | Full `regex` + `regex-automata` + `regex-syntax` + `memchr` + `aho-corasick` workspace. |
| `parsing_text` | `nom` | `rust-bakery/nom` `51c3c4e44fa78a8a09b413419372b97b2cc2a787` | **8 / 8** (from `nom-8.0.0.crate`) | Parser combinator traits and byte/character streaming slices. |
| `parsing_text` | `glob` | `rust-lang/glob` `0639988caf1c0bc4b9a628ff9b0e0bf03d8e66d0` | **8 / 8** | Path pattern matching across Unix and Windows path separators. |
| `serialization` | `serde_json` | `serde-rs/json` `3f17d2c6ea1588bd7b714359522bd94751465275` | **8 / 8** | `serde` + `serde_json` + `itoa` + `ryu` + `memchr`. |
| `serialization` | `toml` | `toml-rs/toml` `e64436850fe15058325f8107867969e320b9f38b` | **0 / 8** (`--offline` workspace dev-deps) | Requires `toml_edit`/`winnow` lockfile resolution. |
| `proc_macro_ast` | `proc-macro2` | `dtolnay/proc-macro2` `ed8a5497669cb249e277f1d96ff87cb15f11b76e` | **8 / 8** | TokenStream bridge and `unicode-ident` lexer. |
| `proc_macro_ast` | `syn` | `dtolnay/syn` `4e508677213155cf73b4072f7a82f73a26cad3f5` | **0 / 8** (`syn-test-suite` dev-dep `build-alert`) | Library target builds when invoked outside the `tests/features` workspace member. |
| `concurrency_sync` | `once_cell` | `matklad/once_cell` `fda60a6c70ebad88b19c5a9763ef0b45dc196a30` | **8 / 8** | Atomic initialization state machine and `UnsafeCell`. |
| `concurrency_sync` | `parking_lot` | `Amanieu/parking_lot` `03d36d62fecbd85ce7cea1babfae23c673f0c6a3` | **8 / 8** | `parking_lot_core` word-lock hash table; selects `futex` on Linux, `ulock`/pthread on Darwin, and `WaitOnAddress`/KeyedEvent (`windows-targets`) on Windows. |
| `async_io_net` | `mio` | `tokio-rs/mio` `b0578c2d166c55b02c18c64bc183ff8191bfba41` | **8 / 8** | Cross-platform OS selector (`epoll` on Linux, `kqueue` on Darwin, `IOCP` via `windows-sys` on Windows). |
| `async_io_net` | `http` | `hyperium/http` `0d7425146ea7bd229596ef41608a19bd72f4bd32` | **8 / 8** | HeaderMap, URI, and status-code state machines (`bytes` + `fnv` + `itoa`). |
| `os_ffi_compression` | `libc` | `rust-lang/libc` `333bf0394a696c4514e0f200fa9fa461487791b8` | **8 / 8** | Platform C ABI struct layouts, constants, and `extern "C"` declarations across all 8 Tier 1 targets. |
| `os_ffi_compression` | `lz4` | `10XGenomics/lz4-rs` `89f932380ac7798d66eb0a9ef5f1a3eb0018a0c2` | **0 / 8** (`lz4-sys` `cc-rs` C build script) | Fails on `x86_64-pc-windows-msvc` with `cc-rs: GNU compiler is not supported for this target` without `CC_x86_64_pc_windows_msvc=clang-cl`. |

### 2. Pinned application set and cross-target FFI library probe

Basis: source + execution

Table 3 specifies the eight real-world application workloads preserved in
`support/applications_and_benchmarks.json`.

| Application ID | Upstream Repository & Pinned Revision | Crate Types | Deterministic Workload & Subsystem Coverage |
| :--- | :--- | :--- | :--- |
| `ripgrep` | `BurntSushi/ripgrep` `4649aa9700619f94cf9c66876e9549d83420e16c` (`14.1.1`) | `bin` | `rg -n --no-ignore 'fn [a-z0-9_]+\(' compiler/` over `rust-lang/rust` `58cf8f9c35b3`: stresses SIMD `memchr`, `aho-corasick`, lazy DFA, and parallel directory walk. |
| `fd` | `sharkdp/fd` `b19136871310b01500b4f09eadd7387b8476be47` (`v10.2.0`) | `bin` | `fd --no-ignore --extension rs . compiler/ library/` over `rust-lang/rust` `58cf8f9c35b3`: stresses work-stealing directory traversal and `globset`/`regex` matching. |
| `rustc-self-compile` | `rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`) | `dylib`, `rlib`, `bin` | `./x.py build --stage 1 library/std compiler/rustc` followed by compiling `serde_json` and `regex` with the stage-1 compiler (78 compiler crates, max DAG depth 23). |
| `tokio-axum-hyper-server` | `tokio-rs/tokio` `9a1b076c0084`, `tokio-rs/axum` `601d775da87c`, `hyperium/hyper` `793af1ed2a3f` | `rlib`, `bin` | In-process 10,000-request HTTP/1.1 + HTTP/2 loopback benchmark across 64 concurrent tasks: stresses `Coroutine` state machines, `Pin`, atomic wakers, and `mio`. |
| `serde-json-workload` | `serde-rs/json` `3f17d2c6ea1588bd7b714359522bd94751465275` | `rlib` | Parse + serialize round-trip over `canada.json` (float-heavy), `citm_catalog.json` (integer/key-heavy), and `twitter.json` (UTF-8 string-heavy). |
| `regex-workload` | `rust-lang/regex` `5ea3eb1e95f0338e283f5f0b4681f0891a1cd836` | `rlib` | `regex` and `regex-automata` compile + search suite exercising PikeVM, bounded backtracker, one-pass DFA, lazy DFA, and SIMD `teddy` prefilters. |
| `image-codec-workload` | `image-rs/image` `aae5fb91a27386801babec31ab07b9a1821e3b03` | `rlib` | PNG, JPEG, and WebP decode + Lanczos3 1024x1024 RGBA8 resample + PNG encode (`flate2` `8ad8fd76828f`, `brotli` `85dbcc34999e`). |
| `ffi-cdylib-and-staticlib` | `rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67` (`support/corpus_harness.py`) | `cdylib`, `staticlib`, `rlib` | `#![no_std]` `verified_crc32c_step` library compiled with `-C opt-level=3 -C panic=abort` and linked into a C99 driver (`main.c`) verifying `crc32c("123456789") == 0xe3069283`. |

Executing the `ffi-cdylib-and-staticlib` workload with
`rustc +1.99.1-x86_64-unknown-linux-gnu` produces two key empirical observations:

1. **Unwinding panic gate on `#![no_std]` `cdylib`/`staticlib`:** Invoking
   `rustc +1.99.1 --crate-type=staticlib --crate-type=cdylib` on a `#![no_std]`
   crate without `-C panic=abort` is rejected by `rustc` with `error: unwinding
   panics are not supported without std` because prebuilt `libcore.rlib` is
   compiled with `panic="unwind"`, requiring `-C panic=abort` when `libstd` is
   not linked.
2. **Cross-target artifact sizes and `staticlib` vs `cdylib` packaging:** On
   `x86_64-unknown-linux-gnu`, linking the C99 driver against `liblib.so`
   (`cdylib`, **5,280 bytes**) or `liblib.a` (`staticlib`, **7,730,098 bytes**,
   which bundles `libcore` and `libcompiler_builtins` archive members) both
   execute and print `crc32c=0xe3069283` (`exit 0`). Table 4 shows the emitted
   object (`.o`), assembly (`.s`), and LLVM IR (`.ll`) sizes across all eight
   Tier 1 targets from `support/corpus_harness.py --suite tier1-smoke`.

| Tier 1 Target Triple | Object Format | `lib.o` (Bytes) | `lib.s` (Bytes) | `lib.ll` (Bytes) | Median Compile Time (`rustc +1.99.1 -O3`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | ELF64 (`EM_X86_64`) | 1,424 | 1,931 | 3,721 | 32.1 ms |
| `x86_64-pc-windows-msvc` | COFF (`IMAGE_FILE_MACHINE_AMD64`) | 1,014 | 1,813 | 3,674 | 31.2 ms |
| `x86_64-pc-windows-gnu` | COFF (`IMAGE_FILE_MACHINE_AMD64`) | 876 | 1,674 | 3,673 | 29.8 ms |
| `aarch64-unknown-linux-gnu` | ELF64 (`EM_AARCH64`) | 1,432 | 1,624 | 3,826 | 34.1 ms |
| `aarch64-apple-darwin` | Mach-O 64 (`CPU_TYPE_ARM64`) | 592 | 1,100 | 3,656 | 32.1 ms |
| `aarch64-pc-windows-msvc` | COFF (`IMAGE_FILE_MACHINE_ARM64`) | 732 | 1,398 | 3,765 | 32.7 ms |
| `i686-unknown-linux-gnu` | ELF32 (`EM_386`) | 1,112 | 2,312 | 3,641 | 30.8 ms |
| `i686-pc-windows-msvc` | COFF (`IMAGE_FILE_MACHINE_I386`) | 791 | 1,761 | 3,589 | 31.2 ms |

### 3. Benchmark suite: `rustc-perf` plus SIMD, unwinding, and concurrency supplements

Basis: source + documentation

`support/applications_and_benchmarks.json` pins `rust-lang/rustc-perf` at commit
`b9d680e5dda9b6d9ff98716e9eed705dad3c105d` (`Cargo.toml` workspace
`rust-version = "1.97.0"`):

1. **Compile-time benchmark suite (`collector/compile-benchmarks`):** 22 Primary
   benchmarks (`bitmaps-3.2.1`, `cargo-0.87.1`, `clap_derive-4.5.32`,
   `cranelift-codegen-0.119.0`, `diesel-2.2.10`, `eza-0.21.2`, `helloworld`,
   `html5ever-0.31.0`, `hyper-1.6.0`, `image-0.25.6`, `libc-0.2.172`,
   `nalgebra-0.33.0`, `regex-automata-0.4.8`, `ripgrep-14.1.1`, `serde-1.0.219`,
   `serde_derive-1.0.219`, `stm32f4-0.15.1`, `syn-2.0.101`,
   `tokio-webpush-simple`, `tuple-stress`, `unify-linearly`, and
   `webrender-2022`) measured across `Check`, `Debug`, and `Opt` profiles under
   full and incremental scenarios.
2. **Runtime benchmark suite (`collector/runtime-benchmarks`):** Driven via
   `benchlib::benchmark::run_benchmark_group`, supplemented in
   `support/applications_and_benchmarks.json` by three domain suites where
   `rustc-perf`'s runtime benchmarks under-sample backend codegen:
   - **SIMD-heavy:** `stdarch-core-arch-kernels` (`library/stdarch/crates/core_arch`
     SSE2/AVX2/AVX-512 and NEON kernels), `portable-simd-f32x8-i32x8`
     (`library/portable-simd` `simd_*` intrinsic lowerings), and
     `byteorder-ahash-simd`.
   - **Unwinding-heavy:** `catch-unwind-drop-ladder` (`library/panic_unwind`
     call stacks of depth 8, 32, and 128 with nested `Drop` guards and
     `extern "C-unwind"` frames exercising `.eh_frame` and Windows SEH
     `.pdata`/`.xdata` unwind tables).
   - **Concurrency-heavy:** `parking-lot-mutex-rwlock-contention` (1, 4, 16, and
     48 threads under `SeqCst`/`AcqRel`/`Acquire`/`Release` atomics) and
     `tokio-mpsc-work-stealing`.

### 4. Measurement conventions and harness interface (`support/corpus_harness.py`)

Basis: source + execution

`support/measurement_conventions.json` and `support/corpus_harness.py` standardize
four experimental requirements across all downstream studies:

1. **Host hardware and isolation metadata:** Every benchmark report must record
   the OS kernel version, CPU model/family/stepping, physical core and NUMA
   topology (`lscpu`), L1d/L1i/L2/L3 cache capacities, active ISA extensions,
   RAM capacity, and whether the host runs under a hypervisor (such as KVM,
   where `cpufreq` sysfs is unexposed) or bare metal (`scaling_governor=performance`,
   `no_turbo=1`). Single-threaded runs must pin to a single NUMA node and
   physical core (`numactl --cpunodebind=0 --membind=0 taskset -c <core>`) with
   ASLR disabled (`setarch $(uname -m) -R`).
2. **Repetition counts and nonparametric statistics:** Compile-time and CLI
   workloads require at least 3 warmup runs followed by $N \ge 30$ timed process
   invocations; in-process microbenchmarks require $M \ge 100$ iterations.
   Reports must record the **median ($p_{50}$)**, **interquartile range
   ($\text{IQR} = p_{75} - p_{25}$)**, **Normalized IQR ($\text{IQR} / p_{50}$)**,
   **median absolute deviation (MAD)**, and a **10,000-resample percentile
   bootstrap 95% confidence interval** on the candidate-to-baseline median
   ratio, gated by a two-sided Mann-Whitney U test ($\alpha = 0.01$) and a
   noise ceiling ($\text{Normalized IQR} < 3.0\%$).
3. **Section-level binary size accounting:** Size comparisons must report both
   total stripped binary size and section-decomposed sizes via `llvm-size -A`
   (from `llvm-tools-preview` `23.1.1`), separating executable code (`.text`),
   read-only data (`.rodata` / `.rdata`), initialized data (`.data`), unwind
   tables (`.eh_frame` + `.eh_frame_hdr` / `.pdata` + `.xdata`), and debug
   sections (`.debug_*`).
4. **Drop-in compiler and per-function hook interface:**
   `support/corpus_harness.py` accepts `--rustc <cmd>`, `--suite`, `--reps`,
   `--crate-flags-json <file>` (injecting per-crate `rustc` flags via
   `RUSTC_WRAPPER`), and `--fn-filter <spec>` (exporting `ANNEAL_FN_FILTER` for
   per-function routing between verified and fallback backends).

## Boundaries

- **Cross-target C-compiler (`cc-rs`) build scripts (`unsupported` without target
  C SDKs):** Pure-Rust crates in the stratified corpus compile across all eight
  Tier 1 targets out of the box using `rust-std-1.99.1-<target>`, but `-sys`
  crates that compile bundled C sources via `cc-rs` (`lz4-sys`, `zstd-sys`,
  `bzip2-sys`) require a target-specific C compiler (`CC_<target>`) and target
  libc/SDK headers.
- **Full 10,000-crate Crater execution (`not examined` in this baseline
  setup):** `support/crates_manifest.json` pins the top 100 crates with `.crate`
  SHA-256 digests and the 1,129-crate lockfile closure; executing full-ecosystem
  Crater runs belongs to the dedicated ecosystem testing track (`Q4`).

## Evidence

- **Primary upstream repositories and commits:**
  - `rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`).
  - `rust-lang/rustc-perf` `b9d680e5dda9b6d9ff98716e9eed705dad3c105d`
    (`Cargo.toml:1-25`, `collector/compile-benchmarks/README.md`,
    `collector/runtime-benchmarks/README.md`).
  - Application and stratified crate commits listed in Tables 2 and 3.
- **Preserved support artifacts:**
  - `support/crates_manifest.json` — top 100 crates by recent downloads with
    verified `.crate` SHA-256 hashes, 25-crate stratified subset with Tier 1
    check results, and 1,129-package `Cargo.lock` dependency closure with
    SHA-256 checksums.
  - `support/applications_and_benchmarks.json` — pinned application commits,
    workloads, `ffi-cdylib-and-staticlib` empirical results across all 8 Tier 1
    targets, `rustc-perf` benchmark inventory, and SIMD/unwinding/concurrency
    benchmark specifications.
  - `support/measurement_conventions.json` — host hardware schema, isolation
    rules, statistical estimators, and section-size accounting definitions.
  - `support/corpus_harness.py` — standalone executable harness for validating
    manifests and running cross-target Tier 1 smoke/benchmark suites with any
    `rustc`-compatible binary.

## Revalidation

Run the preserved harness to validate all corpus manifests and execute the
eight-target Tier 1 compilation and size probe:

```console
python3 reports/rustc-experimental-corpora-and-harness-conventions/support/corpus_harness.py --suite manifest-check
python3 reports/rustc-experimental-corpora-and-harness-conventions/support/corpus_harness.py --suite tier1-smoke --reps 3
```
