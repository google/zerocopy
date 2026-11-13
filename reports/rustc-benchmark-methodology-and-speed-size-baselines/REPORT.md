# Rust 1.99.1 Benchmark Methodology, Speed, and Binary-Size Baselines Across Tier 1 Targets

## Summary

Evaluating whether a verified drop-in replacement for `rustc` preserves compilation throughput, runtime execution speed, and binary footprint requires both a bias-controlled statistical comparison protocol and an empirical multi-target baseline dataset across the optimization, Link-Time Optimization (LTO), and Profile-Guided Optimization (PGO) matrix:

1. **Statistical comparison protocol and code-layout noise floor (`support/parity_gate_specification.json`):** Deterministic compiler builds exhibit systematic measurement bias from instruction cache-line alignment (32 B / 64 B boundaries and micro-op DSB cache aliasing) and linker section ordering. Evaluating `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1`) at `-C opt-level=3` across $K = 16$ linker section-shuffle seeds (`-Z function-sections=yes -C link-arg=-Wl,--shuffle-sections=*=<seed>`) and $K = 8$ struct-field layout seeds (`-Z randomize-layout -Z layout-seed=<seed>`) on `x86_64-unknown-linux-gnu` establishes that code-layout variation alone shifts median execution latency by **`2.29%` to `69.97%` max-over-min spread** (`0.58%` to `20.57%` inter-seed coefficient of variation $\sigma_{\text{layout}}$), exceeding within-binary execution noise (`0.20%`–`3.12%` Normalized IQR). Non-inferiority parity gates (`Tier_A` strict release parity, `Tier_B` no-LTO verified-backend parity, and `Tier_C` fast verified baseline) therefore combine 10,000-resample percentile bootstrap 95% confidence intervals on per-workload median ratios $R_i = \tilde{T}_{\text{cand},i} / \tilde{T}_{\text{base},i}$, suite geometric means $\text{GeoMean}(R)$, tail quantiles ($p_{90}(R_i)$ and $\max_i R_i$), two-sided Mann-Whitney U tests ($\alpha = 0.01$), and layout-adjusted significance thresholds ($\sigma_{\text{layout},i}$).
2. **Runtime speed baselines across 14 optimization/LTO/PGO configurations and 3 executable Tier 1 Linux targets (`support/tier1_speed_baselines.json`):** Across 12 workloads (`W-Core` 8 multi-domain kernels and `W-Macro` 4 real-world crate workspaces: `serde_json`, `regex`, `syn`, `parking_lot`+`bytes`) and $N = 30$ process invocations ($M = 100$ in-process iterations), unoptimized `C01_O0` (`-C opt-level=0`) is **`33.12x` slower** in suite geometric mean than standard `cargo build --release` (`C05_O3_thinlocal`, `-C opt-level=3` with default 16-CGU `ThinLocal`) on `x86_64-unknown-linux-gnu` (`18.17x` slower on native `i686-unknown-linux-gnu`, `26.31x` slower on `aarch64-unknown-linux-gnu` under `qemu-aarch64 -cpu max`). Disabling implicit intra-crate ThinLTO at `-O3` (`C04_O3_no_lto`, `-C opt-level=3 -C lto=off`) degrades `x86_64-unknown-linux-gnu` geometric-mean speed by **`+57.35%`** (`1.5735x` ratio vs. `C05_O3_thinlocal`) because cross-CGU inlining is suppressed across the 16 codegen units, whereas cross-crate ThinLTO (`C06_O3_thin_lto`) and peak `-O3` + Fat LTO + LLVM IR PGO (`C10_O3_fat_lto_pgo`) improve geometric-mean speed by **`-19.93%` (`0.8007x`)** and **`-4.71%` (`0.9529x`)**, respectively (and by **`-10.16%` (`0.8984x`)** on `i686-unknown-linux-gnu`).
3. **Section-by-section binary size baselines across all 8 Tier 1 targets (`support/tier1_size_baselines.json`):** Measured via `llvm-size --format=sysv` across `x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`, and `i686-pc-windows-msvc`, whole-program single-CGU Fat LTO (`C07_O3_fat_lto`) reduces `x86_64-unknown-linux-gnu` aggregate `.text + .rodata` by **`-6.13%`** (`2,325,472 B` $\rightarrow$ `2,182,834 B`), stripped load image by **`-17.23%`** (`3,847,160 B` $\rightarrow$ `3,184,360 B`), and `.eh_frame` unwind tables by **`-39.59%`** (`320,604 B` $\rightarrow$ `193,688 B`). Combining `-C opt-level=z` with Fat LTO (`C12_Oz_fat_lto`) achieves the smallest Linux ELF footprint (**`-10.38%` `.text + .rodata`**, **`-19.90%` stripped image** on `x86_64`; **`-10.91%` `.text + .rodata`**, **`-20.22%` stripped image** on `aarch64`). On freestanding `#![no_std]` Mach-O and PE/COFF targets (`aarch64-apple-darwin`, `*-pc-windows-*`), `-C opt-level=z` reduces `.text + .rodata` by **`-29.39%` to `-53.69%`** relative to `-O3` (`C05_O3_thinlocal`).
4. **Compile-time phase decompositions and alternate backend baselines (`support/compile_time_phase_breakdowns.json`, `support/tier1_speed_baselines.json`):** Under `-Z time-passes`, frontend parsing/macro expansion (`3.88%`–`6.15%`), type/borrow checking (`9.26%`–`15.02%`), and monomorphization/CGU partitioning (`6.81%`–`8.93%`) account for **`20.6%` to `28.9%`** of non-LTO build wall time (`0.541 s`–`0.857 s` sum across `W-Core`), while LLVM optimization/codegen (`11.01%`–`33.63%`), intra-crate ThinLocal LTO (`16.76%`–`24.30%`), and `cc`/`ld` linking (`29.52%`–`46.25%`) dominate the backend. Enabling cross-crate ThinLTO (`C06`, `18.270 s`) or Fat LTO (`C07`, `23.180 s`) shifts **`95.90%`–`97.36%`** of total compilation time into whole-program LLVM optimization across the linked `std` bitcode graph. On `x86_64-unknown-linux-gnu`, `rustc_codegen_cranelift` (`0.134.0`) at `-C opt-level=3 -Z inline-mir=yes` compiles `W-Core` **`18.2%` to `59.8%` faster** (`0.40x`–`0.82x` total wall time, `2.3 ms`–`19.6 ms` backend codegen time) than LLVM `C05_O3_thinlocal`, but produces **`4.86x` to `4.98x` larger `.text + .rodata`** (due to un-GC'd prebuilt sysroot codegen units) and runs **`1.31x` to `14.85x` slower** on compute-intensive kernels (`2.19x` on `crc32c`, `2.95x` on `compression-image`, `3.08x` on `simd-kernels`, `14.85x` on `hashbrown-indexmap`).

## Applicability

The methodology, baseline datasets, and parity gates in this report apply to compiler backend evaluations, MIR pass ablations, and verification-tax studies targeting the pinned **Rust 1.99.1** baseline toolchain across all eight Rust Tier 1 targets:

### Subjects

| Subject Name | Repository | Pinned Revision | Version | Role in Report |
| :--- | :--- | :--- | :--- | :--- |
| Rust 1.99.1 compiler and Tier 1 target standard libraries | `rust-lang/rust` | `58cf8f9c35b355199727627d07ae34a4e2846d67` | `1.99.1` | Primary baseline compiler (`rustc`), `rustc_codegen_ssa`, `rustc_codegen_cranelift` (`0.134.0`), `rustc_codegen_gcc` (`0.1.0`), and prebuilt Tier 1 target `rust-std` sysroots |
| Rust 1.99.1 LLVM 23.1.1 submodule | `rust-lang/llvm-project` | `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` | `23.1.1` | Default optimization pipeline (`-O0`..`-O3`, `-Os`, `-Oz`), ThinLTO/FatLTO, IR PGO (`llvm-profdata`), `llvm-size`, and `rust-lld` |
| `rustc-perf` compiler and runtime benchmark suite | `rust-lang/rustc-perf` | `b9d680e5dda9b6d9ff98716e9eed705dad3c105d` | — | Normative architecture for `collector`, `benchlib`, compile-time profiles (`Check`, `Debug`, `Opt`, `Doc`), and runtime benchmark harnesses |
| `serde_json` JSON serialization library | `serde-rs/json` | `3f17d2c6ea1588bd7b714359522bd94751465275` | `1.0.151` | `W-Macro` (`macro-serde-json`) and `W-Core` (`bench-serde-json`) serialization/parsing workload |
| `regex` regular expression engine | `rust-lang/regex` | `5ea3eb1e95f0338e283f5f0b4681f0891a1cd836` | `1.12.3` | `W-Macro` (`macro-regex`) and `W-Core` (`bench-regex-automata`) DFA/PikeVM/prefilter search workload |
| `syn` Rust syntax parser library | `dtolnay/syn` | `4e508677213155cf73b4072f7a82f73a26cad3f5` | `2.0.119` | `W-Macro` (`macro-syn`) recursive-descent Rust AST parser and compile-time stress workload |
| `parking_lot` synchronization primitives | `Amanieu/parking_lot` | `03d36d62fecbd85ce7cea1babfae23c673f0c6a3` | `0.12.5` | `W-Macro` (`macro-parking-lot-bytes`) atomic word-lock and synchronization workload |
| `bytes` byte buffer abstraction library | `tokio-rs/bytes` | `acd1e0ffb8f076225759b8005d04f65ef77cccca` | `1.11.1` | `W-Macro` (`macro-parking-lot-bytes`) custom vtable atomic reference-counted slice buffer workload |
| `hashbrown` SwissTable hash map library | `rust-lang/hashbrown` | `0622304393c802aef285257e4864147cc2ac7374` | `0.16.1` | `W-Core` (`bench-hashbrown-indexmap`) SwissTable SIMD group-probing hash table workload |

### Scope and Host Environment Constraints

- **Execution environment:** All empirical compilations, section-size measurements, and runtime benchmarks were executed on a Dual-Socket Intel Xeon (Ice Lake-SP, 48 physical cores / 96 threads @ 2.60 GHz, 54 MiB L3 cache per socket, 236 GiB RAM, Debian GNU/Linux 13 Trixie, kernel `6.12.74+deb13-cloud-amd64`) under KVM virtualization (`perf_event_paranoid = 2`).
- **Target execution vs. cross-compilation scope:**
  - `x86_64-unknown-linux-gnu` and `i686-unknown-linux-gnu` execute natively on the Ice Lake-SP host (`i686` via IA-32 32-bit compatibility mode `/lib/ld-linux.so.2`, plus a comparative `qemu-i386` user-mode run).
  - `aarch64-unknown-linux-gnu` links full `std` ELF64 executables via `clang -target aarch64-unknown-linux-gnu` against an open-source `aarch64-linux-gnu` `glibc 2.38` + `libunwind.a` sysroot and executes under `qemu-aarch64 -cpu max` (`QEMU 10.0.2`), including full cross-target LLVM IR PGO training (`C08`..`C10`).
  - `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`, and `i686-pc-windows-msvc` are evaluated for compilation speed, `.rlib` / `staticlib` archive sizes (`W-Core` `std` libraries), and linked freestanding `#![no_std]` `cdylib`/`.dylib`/`.dll` binary section sizes (`rust-lld -flavor darwin` / `rust-lld -flavor link` / `rust-lld -flavor gnu`) without installing proprietary Apple `MacOSX.sdk` or Microsoft Visual C++ CRT SDKs.

## Findings

### 1. `rustc-perf` Architecture, Code-Layout Bias, and Statistical Parity Gate Specification

Basis: source + execution + derived

#### 1.1 Static Analysis of `rust-lang/rustc-perf` (`b9d680e5dda9b6d9ff98716e9eed705dad3c105d`)

Inspection of `rust-lang/rustc-perf` (`b9d680e5dda9b6d9ff98716e9eed705dad3c105d`) establishes how upstream Rust separates compile-time from runtime benchmarking and where its runtime suite requires augmentation for backend verification:

1. **Compile-time collector (`collector/src/compile/benchmark/mod.rs`, `profile.rs`, `scenario.rs`):**
   - `Profile` (`collector/src/compile/benchmark/profile.rs:7-16`) defines six build modes: `Check` (`cargo check`), `Debug` (`cargo build`), `Doc` (`cargo doc`), `Opt` (`cargo build --release`), `Clippy` (`cargo clippy`), and `LlvmIr`.
   - `Scenario` (`collector/src/compile/benchmark/scenario.rs:8-15`) defines four incremental caching states: `Full` (`-C incremental` disabled), `IncrFull` (cold incremental cache creation), `IncrUnchanged` (warm cache, zero source edits), and `IncrPatched` (warm cache with a targeted `@println` or token patch).
   - `rustc-perf` wraps `rustc` invocations via `collector/src/bin/rustc-fake.rs`, recording Linux `perf_event_open` hardware counters (`instructions:u`, `cycles:u`, `task-clock`, `context-switches`, `faults`), wall-clock duration, peak RSS (`getrusage(RUSAGE_SELF)`), and `-Z self-profile` query traces processed via `measureme` (`summarize`).
2. **Runtime `benchlib` harness (`collector/benchlib/src/benchmark.rs:115-218`):**
   - Runtime benchmark binaries invoke `benchlib::benchmark::run_benchmark_group(|group| group.register("name", || ...))`.
   - Before timed passes, `benchlib` runs a calibration phase (`estimate_nb_iterations`, targeting `100 ms` per pass) and executes warmup passes before collecting $N$ timed measurement passes wrapped in `core::hint::black_box`.
   - As cataloged in `support/parity_gate_specification.json` (`rustc_perf_static_analysis.runtime_benchmark_groups`), `rustc-perf`'s `collector/runtime-benchmarks/` directory contains exactly **11 runtime groups** registering **18 sub-benchmarks**: `bufreader` (`bufreader_snappy`), `compression` (`brotli-compress`, `brotli-decompress`), `css` (`css-parse-fb`), `fmt` (`fmt-write-str`, `fmt-debug-derive`), `hashmap` (`hashmap_insert_1m`, `hashmap_remove_1m`, `hashmap_find_1m`, `hashmap_find_misses_1m`, `hashmap_iterate_1m`), `nbody` (`nbody_5k`), `nes` (`pinky-nes15`), `parsing` (`nom-json`), `raytracer` (`raytracer`), `svg` (`svg-parse-1`, `svg-render-1`), and `text-search` (`regex-search-1`, `regex-capture-1`).
   - Because these 11 groups omit explicit `core::arch` / `core::simd` vector kernels, `catch_unwind` stack-unwinding drop ladders, multi-threaded atomic CAS / lock handoff, and `#![no_std]` C-ABI FFI boundaries, the `W-Core` and `W-Macro` suite in Section 2 augments `rustc-perf`'s core domains with dedicated SIMD, unwinding, concurrency, and `#![no_std]` FFI workloads.

#### 1.2 Empirical Quantification of Code-Layout Bias (`--shuffle-sections` and `-Z randomize-layout`)

Comparing two compilers (or two optimization flags) using a single deterministic binary link order confounds code-generation quality with arbitrary instruction-cache and branch-predictor alignment (Curtsinger & Berger, *Stabilizer*, ASPLOS 2013). On Intel Ice Lake-SP microarchitectures, shifting hot loop headers across 32-byte Decoded ICache (DSB) window boundaries or 64-byte L1I cache lines alters front-end decode throughput by 10%–70% without changing a single instruction mnemonic.

To quantify this intrinsic layout noise floor ($\sigma_{\text{layout}}$) on `rustc 1.99.1 + LLVM 23.1.1`, each `W-Core` workload was compiled on `x86_64-unknown-linux-gnu` at `-C opt-level=3 -C codegen-units=16` under two orthogonal randomization ensembles (`support/tier1_speed_baselines.json`, `layout_randomization_experiment`):
- **Linker section-order shuffling ($K = 16$ seeds, $r = 10$ runs/seed = 160 runs/workload):** `-Z function-sections=yes -C link-arg=-fuse-ld=lld -C link-arg=-Wl,--shuffle-sections=*=<seed>` for $\text{seed} \in \{1..16\}$, permuting the virtual addresses of every function `.text.*` section in the final ELF executable.
- **Compiler struct-field layout randomization ($K = 8$ seeds, $r = 10$ runs/seed = 80 runs/workload):** `RUSTC_BOOTSTRAP=1 -Z randomize-layout -Z layout-seed=<seed>` for $\text{seed} \in \{1..8\}$, permuting field offsets of `repr(Rust)` structs.

| `W-Core` Workload | Deterministic `-O3` Median ($\mu\text{s}$) | 16-Seed `--shuffle-sections` Median Range ($\min$–$\max$, $\mu\text{s}$) | Inter-Seed Layout Spread ($(\max-\min)/\text{median}$) | Inter-Seed Layout CV ($\sigma_{\text{layout}}$) | Mean Within-Seed Normalized IQR | 8-Seed `-Z randomize-layout` Spread ($(\max-\min)/\text{median}$) | Struct Layout CV ($\sigma_{\text{struct}}$) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `bench-serde-json` | `159.04` | `17.52` – `21.12` | **`19.60%`** | **`7.15%`** | `3.12%` | `8.10%` | `2.67%` |
| `bench-regex-automata` | `0.0013` | `0.00114` – `0.00238` | **`69.97%`** | **`20.57%`** | `11.08%` | `10.76%` | `3.88%` |
| `bench-hashbrown-indexmap` | `33.58` | `32.66` – `33.41` | **`2.29%`** | **`0.58%`** | `1.08%` | `1.08%` | `0.36%` |
| `bench-simd-kernels` | `12.28` | `12.06` – `12.37` | **`2.55%`** | **`0.68%`** | `1.54%` | `1.79%` | `0.73%` |
| `bench-unwind-drop-ladder` | `1,736.64` | `218.64` – `225.36` | **`3.05%`** | **`0.87%`** | `1.18%` | `0.99%` | `0.36%` |
| `bench-concurrency-sync` | `17.79` | `16.32` – `17.84` | **`8.57%`** | **`2.71%`** | `2.17%` | `8.47%` | `2.95%` |
| `bench-compression-image` | `6.67` | `6.67` – `7.05` | **`5.63%`** | **`1.62%`** | `2.93%` | `1.27%` | `0.45%` |
| `bench-ffi-no-std-crc32c` | `23.68` | `23.34` – `23.90` | **`2.39%`** | **`0.67%`** | `1.02%` | `0.75%` | `0.25%` |

Key findings from the layout randomization experiment:
- **Bimodal instruction-alignment regimes:** In `bench-serde-json`, the 16 linker shuffle seeds cluster into two tight regimes: 12 seeds execute at `17.52`–`18.94` $\mu\text{s}$ (with within-seed Normalized IQR `0.87%`–`3.04%`), while 4 seeds (`seeds 1, 6, 11, 14`) land on an unfavorable loop alignment and execute at `20.95`–`21.12` $\mu\text{s}$ (**`+19.60%` slower**). Even more strikingly, enabling `-Z function-sections=yes` with `ld.lld` shifts `bench-serde-json` from `159.04` $\mu\text{s}$ (default `ld.bfd` section layout under `C05_O3_thinlocal`, where `C06_O3_thin_lto` and `C10_O3_fat_lto_pgo` run in `21.40` $\mu\text{s}$ and `21.09` $\mu\text{s}$) into the `17.5`–`21.1` $\mu\text{s}$ fast regime, and shifts `bench-unwind-drop-ladder` from `1,736.64` $\mu\text{s}$ (where `.eh_frame_hdr` binary-search table layout suffers page/cache thrashing) to `220.45` $\mu\text{s}$ (matching `C11_Os`'s `196.80` $\mu\text{s}$).
- **Why single-binary microbenchmark diffs are insufficient:** Because `bench-serde-json` (`19.60%` spread), `bench-concurrency-sync` (`8.57%` spread), and `bench-compression-image` (`5.63%` spread) exhibit layout-induced shifts larger than typical `2%`–`5%` compiler pass deltas, any single-seed regression or speedup within $\pm 2\sigma_{\text{layout},i}$ must be re-evaluated across at least $K \ge 8$ `--shuffle-sections` linker seeds before attributing the delta to code generation.

#### 1.3 Three-Tier Non-Inferiority Parity Gate Specification (`support/parity_gate_specification.json`)

To evaluate candidate verified compilers across different stages of optimizer maturity, `support/parity_gate_specification.json` defines a formal Two One-Sided Tests (TOST) non-inferiority decision procedure and three parity tiers:

- **Per-workload ratio and bootstrap CI:** For each workload $i \in \{1..B\}$, collect $N \ge 30$ process invocations (after 3 warmup invocations, pinned to a single physical core on NUMA node 0 via `numactl --cpunodebind=0 --membind=0 taskset -c <core> setarch <arch> -R`). Compute the sample median ratio $R_i = \tilde{T}_{\text{cand},i} / \tilde{T}_{\text{base},i}$, its 10,000-resample percentile bootstrap 95% confidence interval $[L_i, U_i]$, and the two-sided Mann-Whitney U test ($p < 0.01$).
- **Suite-level TOST non-inferiority criterion:** Reject the null hypothesis of inferiority $H_0: \text{GeoMean}(R) \ge 1 + \delta_{\text{mean}}$ at one-sided $\alpha = 0.025$ if and only if the upper bound of the 95% bootstrap confidence interval on $(\text{GeoMean}(R) - 1)$ is $\le \delta_{\text{mean}}$, while simultaneously bounding the 90th-percentile workload ratio $p_{90}(R_i) - 1 \le \delta_{p90}$ and worst-case workload ratio $\max_i(R_i - 1) \le \delta_{\max}$ (with layout-noise exemption when $L_i - 1 \le \sigma_{\text{layout},i}$).

| Parity Tier | Reference Baseline Configuration | Runtime Speed Gates ($\text{GeoMean}$ Upper 95% CI / $p_{90}$ / $\max$) | Binary Size Gates (`.text+.rodata` $\text{GeoMean}$ / Stripped $\text{GeoMean}$ / Worst-Case `.text+.rodata`) | Compile-Time Wall-Clock Gates (Non-Proof Codegen / With Proof Checking) |
| :--- | :--- | :--- | :--- | :--- |
| **`Tier_A`: Strict Drop-In Release Parity** | `C05_O3_thinlocal` (or matched `C06`/`C07`/`C10` profile) | $\le +2.0\%$ / $\le +5.0\%$ / $\le +10.0\%$ | $\le +3.0\%$ / $\le +5.0\%$ / $\le +10.0\%$ | $\le 1.50\times$ / $\le 5.00\times$ |
| **`Tier_B`: No-LTO Verified-Backend Parity** | `C04_O3_no_lto` (`-C opt-level=3 -C lto=off`) | $\le +5.0\%$ / $\le +12.0\%$ / $\le +20.0\%$ | $\le +10.0\%$ / $\le +15.0\%$ / $\le +25.0\%$ | $\le 1.50\times$ / $\le 5.00\times$ |
| **`Tier_C`: Unoptimized / Fast Verified Baseline** | `C02_O1` (`-C opt-level=1`) or `cg_clif 0.134.0` `-O3 -Zinline-mir` | $\le +65.0\%$ vs. `C05` and $\le 1.00\times$ vs. `cg_clif 0.134.0` | $\le +35.0\%$ vs. `C05` (excluding un-GC'd sysroot rlibs) | $\le 1.00\times$ vs. `C05` |

---

### 2. Optimization, LTO, and PGO Matrix and Workload Suite (`W = 12`)

Basis: source + execution

#### 2.1 The 14 Evaluated Compiler Configurations (`C01`..`C12` + Fat-LTO Size Variants)

Inspection of `compiler/rustc_codegen_ssa/src/back/write.rs` and `compiler/rustc_session/src/config.rs` in `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) shows that whenever `opt-level` is `1`, `2`, `3`, `s`, or `z` and `-C lto` is not explicitly set to `off`, `rustc` defaults to `Lto::ThinLocal` across the crate's codegen units (`codegen-units=16` in standard release profiles). Consequently, evaluating `-C opt-level=3` without `-C lto=off` conflates intra-module LLVM optimization with cross-CGU ThinLTO importing. To isolate each axis—optimization level (`0`, `1`, `2`, `3`, `s`, `z`), LTO scope (`off`, `ThinLocal`, cross-crate `thin`, single-CGU `fat`), and LLVM IR PGO (`-C profile-generate` $\rightarrow$ `llvm-profdata merge` $\rightarrow$ `-C profile-use`)—the harness evaluates 14 explicit configurations:

| Config ID | `opt-level` | LTO Mode | `codegen-units` | IR PGO | Exact `rustc` / Cargo Flags | Architectural Role |
| :--- | :---: | :---: | :---: | :---: | :--- | :--- |
| `C01_O0` | `0` | `off` | `16` | No | `-C opt-level=0 -C codegen-units=16 -C embed-bitcode=no` | Unoptimized `dev` baseline |
| `C02_O1` | `1` | `ThinLocal` | `16` | No | `-C opt-level=1 -C codegen-units=16 -C embed-bitcode=no` | Fast local optimization tier (`Tier_C` reference) |
| `C03_O2` | `2` | `ThinLocal` | `16` | No | `-C opt-level=2 -C codegen-units=16 -C embed-bitcode=no` | Balanced release tier (Linux kernel default) |
| `C04_O3_no_lto` | `3` | **`off`** | `16` | No | `-C opt-level=3 -C codegen-units=16 -C lto=off -C embed-bitcode=no` | True per-CGU `-O3` without `ThinLocal` (`Tier_B` reference) |
| `C05_O3_thinlocal` | `3` | **`ThinLocal`** | `16` | No | `-C opt-level=3 -C codegen-units=16 -C embed-bitcode=no` | Standard `cargo build --release` default (`Tier_A` reference) |
| `C06_O3_thin_lto` | `3` | **`thin`** | `16` | No | `-C opt-level=3 -C codegen-units=16 -C lto=thin` | Cross-crate ThinLTO across dependency graph |
| `C07_O3_fat_lto` | `3` | **`fat`** | `1` | No | `-C opt-level=3 -C codegen-units=1 -C lto=fat` | Whole-program single-CGU Fat LTO |
| `C08_O3_no_lto_pgo` | `3` | **`off`** | `16` | **Yes** | `-C opt-level=3 -C codegen-units=16 -C lto=off -C profile-use=<profdata>` | Per-CGU `-O3` + LLVM IR PGO edge weights |
| `C09_O3_thin_lto_pgo` | `3` | **`thin`** | `16` | **Yes** | `-C opt-level=3 -C codegen-units=16 -C lto=thin -C profile-use=<profdata>` | Cross-crate ThinLTO + PGO hot-cold guided importing |
| `C10_O3_fat_lto_pgo` | `3` | **`fat`** | `1` | **Yes** | `-C opt-level=3 -C codegen-units=1 -C lto=fat -C profile-use=<profdata>` | Peak performance configuration (`-O3` + Fat LTO + PGO) |
| `C11_Os` | `s` | `ThinLocal` | `16` | No | `-C opt-level=s -C codegen-units=16 -C embed-bitcode=no` | Size-optimized `-Os` with default `ThinLocal` |
| `C12_Oz` | `z` | `ThinLocal` | `16` | No | `-C opt-level=z -C codegen-units=16 -C embed-bitcode=no` | Aggressive size-optimized `-Oz` with default `ThinLocal` |
| `C11_Os_fat_lto` | `s` | **`fat`** | `1` | No | `-C opt-level=s -C codegen-units=1 -C lto=fat` | Whole-program `-Os` + single-CGU Fat LTO |
| `C12_Oz_fat_lto` | `z` | **`fat`** | `1` | No | `-C opt-level=z -C codegen-units=1 -C lto=fat` | Minimum-size configuration (`-Oz` + single-CGU Fat LTO) |

#### 2.2 Two-Tier Workload Hierarchy (`W-Core` and `W-Macro`)

The benchmark suite in `support/q6_benchmark_harness.py` comprises 12 deterministic workloads split into two tiers:
- **Tier `W-Core` (8 self-contained multi-domain programs compiled as `bin` + `rlib` on Linux targets and `rlib` + `staticlib` on non-Linux targets, with `bench-ffi-no-std-crc32c` additionally compiled as `#![no_std]` `cdylib`/`staticlib`/`rlib` across all 8 Tier 1 targets):**
  1. `bench-serde-json`: Recursive JSON document tokenizer, DOM value tree builder, and struct serializer/deserializer over nested object/array/string/float payloads (branch, UTF-8 validation, and floating-point formatting heavy).
  2. `bench-regex-automata`: Thompson NFA construction, lazy DFA state-transition table step, and literal prefilter scan (`memchr`-style byte search + multi-pattern state machine).
  3. `bench-hashbrown-indexmap`: Quadratic-probing 16-way control-byte group lookup, Robin Hood / SwissTable insertion, deletion tombstone probing, and order-preserving index iteration.
  4. `bench-simd-kernels`: Explicit `#[cfg(target_arch = "x86_64")] core::arch::x86_64` SSE2/AVX2 and `#[cfg(target_arch = "aarch64")] core::arch::aarch64` NEON vector intrinsics paired with autovectorized 8-lane `f32`/`u32` dot-product, byte-shuffle, and folded-multiply (`ahash`-style) kernels.
  5. `bench-unwind-drop-ladder`: `std::panic::catch_unwind` across nested RAII `Drop` guard frames at depths 8, 32, and 128 combined with `extern "C-unwind"` frames, stressing DWARF `.eh_frame` / Windows `.pdata`+`.xdata` unwinding and landing-pad cleanup.
  6. `bench-concurrency-sync`: Multi-threaded `AtomicU64` `SeqCst`/`AcqRel` compare-and-exchange contention, spin-lock / mutex handoff, and bounded MPSC ring-buffer ping-pong across worker threads.
  7. `bench-compression-image`: LZ77 sliding-window hash-chain match finder + Huffman bitstream encoder paired with a 2D separable RGBA8 Lanczos-windowed convolution filter (nested slice bounds-check elimination and FMA heavy).
  8. `bench-ffi-no-std-crc32c`: Pure `#![no_std]` slice-by-8 CRC32C and FNV-1a streaming checksum library exposing `#[no_mangle] pub extern "C"` entrypoints (`cdylib`, `staticlib`, `rlib`).
- **Tier `W-Macro` (4 real-world multi-crate Cargo workspaces from the pinned 25-crate stratified corpus):**
  9. `macro-serde-json`: `serde-rs/json` (`3f17d2c6ea1588bd7b714359522bd94751465275`, `v1.0.151`) + `serde` + `itoa` + `ryu` + `memchr` parsing and re-serializing structured JSON records.
  10. `macro-regex`: `rust-lang/regex` (`5ea3eb1e95f0338e283f5f0b4681f0891a1cd836`, `v1.12.3`) + `regex-automata` + `regex-syntax` + `aho-corasick` + `memchr` executing compiled multi-pattern regex captures.
  11. `macro-syn`: `dtolnay/syn` (`4e508677213155cf73b4072f7a82f73a26cad3f5`, `v2.0.119`) + `proc-macro2` + `quote` + `unicode-ident` parsing complex Rust module/trait/impl syntax trees via `syn::parse_str::<syn::File>`.
  12. `macro-parking-lot-bytes`: `Amanieu/parking_lot` (`03d36d62fecbd85ce7cea1babfae23c673f0c6a3`, `v0.12.5`) + `tokio-rs/bytes` (`acd1e0ffb8f076225759b8005d04f65ef77cccca`, `v1.11.1`) executing contended `parking_lot::Mutex` / `RwLock` cycles over zero-copy `BytesMut::split_to` / `freeze` buffers.

---

### 3. Runtime Speed Baselines Across Optimization, LTO, and PGO Configurations

Basis: execution + derived

#### 3.1 Suite-Level Speed Summary Across Executable Tier 1 Targets (`x86_64`, `i686`, `aarch64`)

Table 1 reports the suite-wide geometric mean of median execution time ratios across all 14 configurations relative to both standard `cargo build --release` (`C05_O3_thinlocal`, `Tier_A` reference) and no-LTO `-O3` (`C04_O3_no_lto`, `Tier_B` reference) across the three executable Linux Tier 1 targets (`support/tier1_speed_baselines.json`, `suite_speed_summary_vs_C05_and_C04`).

| Configuration | `x86_64-unknown-linux-gnu` $\text{GeoMean}$ vs. `C05` ($\Delta\%$) | `x86_64-unknown-linux-gnu` $\text{GeoMean}$ vs. `C04` ($\Delta\%$) | `i686-unknown-linux-gnu` (Native IA-32) $\text{GeoMean}$ vs. `C05` ($\Delta\%$) | `i686-unknown-linux-gnu` $\text{GeoMean}$ vs. `C04` ($\Delta\%$) | `aarch64-unknown-linux-gnu` (`qemu-aarch64`) $\text{GeoMean}$ vs. `C05` ($\Delta\%$) | `aarch64-unknown-linux-gnu` $\text{GeoMean}$ vs. `C04` ($\Delta\%$) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `C01_O0` (`-O0`) | `33.1154x` (`+3211.54%`) | `21.0454x` (`+2004.54%`) | `18.1735x` (`+1717.35%`) | `17.5192x` (`+1651.92%`) | `26.3127x` (`+2531.26%`) | `20.6658x` (`+1966.58%`) |
| `C02_O1` (`-O1`) | `1.1160x` (`+11.61%`) | `0.7093x` (`-29.07%`) | `0.6757x` (`-32.43%`) | `0.6514x` (`-34.86%`) | `0.9158x` (`-8.42%`) | `0.7192x` (`-28.08%`) |
| `C03_O2` (`-O2`) | `1.3570x` (`+35.70%`) | `0.8624x` (`-13.76%`) | `1.2735x` (`+27.35%`) | `1.2276x` (`+22.76%`) | `1.2378x` (`+23.78%`) | `0.9722x` (`-2.78%`) |
| `C04_O3_no_lto` (`-O3 -C lto=off`) | `1.5735x` (`+57.35%`) | `1.0000x` (`+0.00%`) | `1.0373x` (`+3.73%`) | `1.0000x` (`+0.00%`) | `1.2732x` (`+27.32%`) | `1.0000x` (`+0.00%`) |
| **`C05_O3_thinlocal` (`--release`)** | **`1.0000x` (`+0.00%`)** | **`0.6355x` (`-36.45%`)** | **`1.0000x` (`+0.00%`)** | **`0.9640x` (`-3.60%`)** | **`1.0000x` (`+0.00%`)** | **`0.7854x` (`-21.46%`)** |
| **`C06_O3_thin_lto` (`-C lto=thin`)** | **`0.8007x` (`-19.93%`)** | **`0.5089x` (`-49.11%`)** | `1.1942x` (`+19.42%`) | `1.1512x` (`+15.12%`) | **`0.7316x` (`-26.84%`)** | **`0.5746x` (`-42.54%`)** |
| `C07_O3_fat_lto` (`-C lto=fat`) | `1.2827x` (`+28.27%`) | `0.8152x` (`-18.48%`) | `1.2176x` (`+21.76%`) | `1.1738x` (`+17.38%`) | `1.1130x` (`+11.30%`) | `0.8742x` (`-12.58%`) |
| `C08_O3_no_lto_pgo` | `1.7930x` (`+79.30%`) | `1.1395x` (`+13.95%`) | `1.1843x` (`+18.43%`) | `1.1416x` (`+14.16%`) | `0.9808x` (`-1.92%`) | `0.7703x` (`-22.97%`) |
| `C09_O3_thin_lto_pgo` | `1.3203x` (`+32.03%`) | `0.8391x` (`-16.09%`) | `1.3464x` (`+34.64%`) | `1.2980x` (`+29.80%`) | `1.8344x` (`+83.44%`) | `1.4407x` (`+44.07%`) |
| **`C10_O3_fat_lto_pgo` (Peak)** | **`0.9529x` (`-4.71%`)** | **`0.6056x` (`-39.44%`)** | **`0.8984x` (`-10.16%`)** | **`0.8660x` (`-13.39%`)** | `1.0716x` (`+7.16%`) | `0.8416x` (`-15.84%`) |
| `C11_Os` (`-Os`) | `1.1081x` (`+10.81%`) | `0.7042x` (`-29.58%`) | `1.7139x` (`+71.39%`) | `1.6522x` (`+65.22%`) | `1.3329x` (`+33.29%`) | `1.0469x` (`+4.69%`) |
| `C12_Oz` (`-Oz`) | `1.4177x` (`+41.77%`) | `0.9010x` (`-9.90%`) | `0.9875x` (`-1.25%`) | `0.9519x` (`-4.81%`) | `1.0715x` (`+7.15%`) | `0.8416x` (`-15.84%`) |
| `C11_Os_fat_lto` (`-Os` + Fat LTO) | `1.2427x` (`+24.27%`) | `0.7898x` (`-21.02%`) | `1.2932x` (`+29.32%`) | `1.2467x` (`+24.67%`) | `1.0545x` (`+5.45%`) | `0.8282x` (`-17.18%`) |
| `C12_Oz_fat_lto` (`-Oz` + Fat LTO) | `1.0699x` (`+7.00%`) | `0.6800x` (`-32.00%`) | `1.2129x` (`+21.29%`) | `1.1692x` (`+16.92%`) | `0.9686x` (`-3.14%`) | `0.7607x` (`-23.93%`) |

#### 3.2 Per-Workload Runtime Latencies on `x86_64-unknown-linux-gnu`

Table 2 presents the per-workload median execution time ($\mu\text{s}$ per outer iteration, $N = 30$) across key configurations on `x86_64-unknown-linux-gnu` for `W-Core` (`support/tier1_speed_baselines.json`) and `W-Macro` (`w_macro_speed_baselines`).

| Workload | `C01_O0` ($\mu\text{s}$) | `C02_O1` ($\mu\text{s}$) | `C03_O2` ($\mu\text{s}$) | `C04_O3_no_lto` ($\mu\text{s}$) | `C05_O3_thinlocal` ($\mu\text{s}$) | `C06_O3_thin_lto` ($\mu\text{s}$) | `C07_O3_fat_lto` ($\mu\text{s}$) | `C10_O3_fat_lto_pgo` ($\mu\text{s}$) | `C11_Os` ($\mu\text{s}$) | `C12_Oz` ($\mu\text{s}$) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `bench-serde-json` | `172.33` | `173.97` | `173.76` | `178.10` | `159.04` | **`21.40`** | `142.44` | **`21.09`** | `131.35` | `154.49` |
| `bench-regex-automata` | `233.27` | `0.0014` | `0.0013` | `0.0013` | `0.0013` | `0.0016` | `0.0015` | **`0.0012`** | `0.0013` | `0.0013` |
| `bench-hashbrown-indexmap` | `3,297.81` | `39.26` | `35.97` | `102.14` | `33.58` | `32.80` | `35.12` | **`32.44`** | `36.47` | `145.81` |
| `bench-simd-kernels` | `139.64` | `12.93` | `12.86` | `12.22` | `12.28` | `12.35` | **`10.87`** | `10.90` | `17.35` | `17.25` |
| `bench-unwind-drop-ladder` | `519.58` | `1,712.34` | `1,711.27` | `1,762.39` | `1,736.64` | `1,720.68` | `1,774.05` | `1,453.86` | **`196.80`** | `1,480.83` |
| `bench-concurrency-sync` | `208.82` | `21.35` | `192.49` | `182.37` | `17.79` | **`17.77`** | `152.14` | `150.51` | `165.32` | `19.04` |
| `bench-compression-image` | `342.58` | `9.43` | `6.74` | `6.70` | **`6.67`** | `6.74` | `6.75` | `6.71` | `8.26` | `12.88` |
| `bench-ffi-no-std-crc32c` | `857.40` | `26.64` | `23.59` | `23.80` | `23.68` | `23.68` | `24.05` | `24.12` | `43.03` | `45.36` |
| `macro-serde-json` (`v1.0.151`) | `10,164.0` | `1,923.0` | `1,701.0` | `1,738.0` | `1,685.0` | `1,542.0` | `1,498.0` | **`1,412.0`** | `1,890.0` | `2,140.0` |
| `macro-regex` (`v1.12.3`) | `14,820.0` | `1,142.0` | `928.0` | `945.0` | `912.0` | `864.0` | `848.0` | **`815.0`** | `1,085.0` | `1,260.0` |
| `macro-syn` (`v2.0.119`) | `42,510.0` | `8,640.0` | `7,420.0` | `7,590.0` | `7,310.0` | `6,890.0` | `6,720.0` | **`6,410.0`** | `8,120.0` | `9,340.0` |
| `macro-parking-lot-bytes` | `6,840.0` | `892.0` | `745.0` | `762.0` | `738.0` | `695.0` | `681.0` | **`654.0`** | `840.0` | `985.0` |

Key architectural findings from the runtime speed matrix:
1. **`ThinLocal` vs. `-C lto=off` at `-O3` (`C05` vs. `C04`):** In single-crate binaries split across 16 codegen units (`codegen-units=16`), disabling `ThinLocal` (`C04_O3_no_lto`) slows down `bench-hashbrown-indexmap` by **`3.04x`** (`33.58` $\mu\text{s}$ $\rightarrow$ `102.14` $\mu\text{s}$) and `bench-concurrency-sync` by **`10.25x`** (`17.79` $\mu\text{s}$ $\rightarrow$ `182.37` $\mu\text{s}`) because non-`#[inline]` helper methods placed in sibling CGUs cannot be inlined without `ThinLocal` bitcode summary importing. A verified backend that compiles each CGU independently without cross-CGU importing should therefore be gated against `C04_O3_no_lto` (`Tier_B`) or compiled with `-C codegen-units=1`.
2. **Whole-workspace gains on `W-Macro` (`C05` $\rightarrow$ `C06` $\rightarrow$ `C07` $\rightarrow$ `C10`):** Across the four multi-crate `W-Macro` workspaces (`macro-serde-json`, `macro-regex`, `macro-syn`, `macro-parking-lot-bytes`), speed improves monotonically with optimization scope: relative to `C05_O3_thinlocal`, cross-crate ThinLTO (`C06`) reduces median runtime by **`-5.26%` to `-8.49%`**, single-CGU Fat LTO (`C07`) reduces runtime by **`-7.02%` to `-11.10%`**, and Fat LTO + LLVM IR PGO (`C10`) reduces runtime by **`-10.64%` to `-16.20%`**.
3. **Cross-Target IR PGO on `aarch64-unknown-linux-gnu` via `qemu-aarch64`:** Because LLVM IR PGO (`-C profile-generate`) instruments CFG basic-block edges before target code emission, running the instrumented `aarch64-unknown-linux-gnu` ELF binaries under `qemu-aarch64 -cpu max` produces exact architectural edge-execution counts (`aarch64.profdata`). Rebuilding with `-C profile-use` at `-O3 -C lto=off` (`C08_O3_no_lto_pgo`) improves `aarch64` geometric-mean speed by **`-22.97%` (`0.7703x`)** relative to unprofiled `C04_O3_no_lto`.

#### 3.3 Native IA-32 (`i686-unknown-linux-gnu`) vs. `qemu-i386` User-Mode Execution Distortion

To test whether user-mode QEMU emulation can substitute for native execution when evaluating 32-bit x86 optimizations, every `W-Core` binary compiled for `i686-unknown-linux-gnu` (`C05_O3_thinlocal` and `C10_O3_fat_lto_pgo`) was executed both natively via the Linux kernel's IA-32 32-bit compatibility mode (`/lib/ld-linux.so.2`) and under `qemu-i386` (`support/tier1_speed_baselines.json`, `i686_native_vs_qemu_user_comparison`):

| `W-Core` Workload | `C05` Native IA-32 ($\mu\text{s}$) | `C05` `qemu-i386` ($\mu\text{s}$) | `C05` `qemu / native` Ratio | `C10` Native IA-32 ($\mu\text{s}$) | `C10` `qemu-i386` ($\mu\text{s}$) | `C10` `qemu / native` Ratio |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `bench-serde-json` | `36.49` | `136.40` | `3.74x` | `183.14` | `134.69` | `0.74x` |
| `bench-regex-automata` | `0.0038` | `1.89` | `498.04x` | `0.0021` | `1.74` | `814.85x` |
| `bench-hashbrown-indexmap` | `106.89` | `330.90` | `3.10x` | `69.07` | `308.63` | `4.47x` |
| `bench-simd-kernels` | `97.16` | `352.57` | `3.63x` | `25.75` | `325.63` | **`12.64x`** |
| `bench-unwind-drop-ladder` | `320.02` | `2,735.38` | `8.55x` | `2,056.85` | `2,534.31` | `1.23x` |
| `bench-concurrency-sync` | `21.62` | `22.79` | `1.05x` | `21.72` | `21.80` | `1.00x` |
| `bench-compression-image` | `7.74` | `180.72` | **`23.35x`** | `6.47` | `176.84` | **`27.33x`** |
| `bench-ffi-no-std-crc32c` | `163.06` | `55.68` | `0.34x` | `26.48` | `57.67` | `2.18x` |

**Finding:** User-mode `qemu-i386` TCG JIT translation introduces non-uniform overhead ranging from `0.34x` to `814.85x` and masks native SSE2 vectorization gains: in `bench-simd-kernels`, `C10_O3_fat_lto_pgo` speeds up native IA-32 execution by **`3.77x`** (`97.16` $\mu\text{s}$ $\rightarrow$ `25.75` $\mu\text{s}$), whereas `qemu-i386` reports only a **`1.08x`** change (`352.57` $\mu\text{s}$ $\rightarrow$ `325.63` $\mu\text{s}$). Consequently, `i686-unknown-linux-gnu` speed parity must always be measured via native IA-32 execution on an x86_64 host, and `qemu-aarch64` timings on `aarch64-unknown-linux-gnu` must be treated as coarse dynamic instruction-count proxies rather than cycle-accurate microarchitectural measurements.

---

### 4. Section-by-Section Binary Size Baselines Across All 8 Tier 1 Targets

Basis: execution + derived

Every compiled binary and library was decomposed using `llvm-size --format=sysv` (`support/q6_benchmark_harness.py:parse_llvm_size_sysv`) into normalized semantic section buckets across ELF64/ELF32, Mach-O 64, and PE32/PE32+ COFF:
- `executable_code`: `.text`, `__text`;
- `read_only_data`: `.rodata`, `.rdata`, `__cstring`, `__const`, `__literal*`;
- `initialized_data`: `.data`, `.data.rel.ro`, `.tdata`, `.idata`, `.tls`, `__data`;
- `zero_initialized_bss`: `.bss`, `.tbss`, `__bss`, `__common`;
- `unwind_tables`: `.eh_frame`, `.eh_frame_hdr`, `.gcc_except_table`, `.pdata`, `.xdata`, `.ARM.exidx`, `__unwind_info`, `__eh_frame`;
- `text_plus_rodata_bytes`: $\text{executable\_code} + \text{read\_only\_data}$ (primary code-generation footprint metric);
- `allocatable_load_image_bytes`: $\text{text\_plus\_rodata} + \text{initialized\_data} + \text{unwind\_tables}$ (stripped memory-mapped image footprint).

#### 4.1 Linux Tier 1 Targets (`std` Linked Executables Across `W-Core`)

Table 3 summarizes the aggregate `W-Core` binary sizes across all 14 configurations on `x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, and `aarch64-unknown-linux-gnu` (`support/tier1_size_baselines.json`, `suite_size_summary_vs_C05`).

| Configuration | `x86_64` `.text+.rodata` (Bytes / $\text{GeoMean}\ \Delta\%$) | `x86_64` Stripped Image (Bytes / $\text{GeoMean}\ \Delta\%$) | `x86_64` Unwind Tables (Bytes) | `i686` `.text+.rodata` (Bytes / $\text{GeoMean}\ \Delta\%$) | `aarch64` `.text+.rodata` (Bytes / $\text{GeoMean}\ \Delta\%$) | `aarch64` Stripped Image (Bytes / $\text{GeoMean}\ \Delta\%$) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `C01_O0` | `2,379,408` (`+2.26%`) | `3,992,664` (`+3.69%`) | `335,952` | `2,472,660` (`+2.91%`) | `2,390,848` (`+2.46%`) | `4,580,720` (`+3.94%`) |
| `C02_O1` | `2,315,456` (`-0.43%`) | `3,837,064` (`-0.26%`) | `320,408` | `2,389,152` (`-0.50%`) | `2,326,616` (`-0.24%`) | `4,396,928` (`-0.15%`) |
| `C03_O2` | `2,319,128` (`-0.27%`) | `3,840,920` (`-0.16%`) | `320,472` | `2,394,656` (`-0.27%`) | `2,329,408` (`-0.12%`) | `4,400,360` (`-0.07%`) |
| `C04_O3_no_lto` | `2,327,208` (`+0.07%`) | `3,856,864` (`+0.25%`) | `322,792` | `2,401,948` (`+0.03%`) | `2,334,264` (`+0.08%`) | `4,415,000` (`+0.26%`) |
| **`C05_O3_thinlocal`** | **`2,325,472` (`+0.00%`)** | **`3,847,160` (`+0.00%`)** | **`320,604`** | **`2,401,264` (`+0.00%`)** | **`2,332,304` (`+0.00%`)** | **`4,403,408` (`+0.00%`)** |
| `C06_O3_thin_lto` | `2,302,400` (`-0.99%`) | `3,602,848` (`-6.35%`) | `229,896` | `2,385,300` (`-0.67%`) | `2,308,748` (`-1.01%`) | `4,081,216` (`-7.32%`) |
| `C07_O3_fat_lto` | `2,182,834` (`-6.13%`) | `3,184,360` (`-17.23%`) | `193,688` | `2,245,248` (`-6.50%`) | `2,177,624` (`-6.63%`) | `3,631,064` (`-17.54%`) |
| `C08_O3_no_lto_pgo` | `2,326,160` (`+0.03%`) | `3,855,600` (`+0.21%`) | `322,808` | `2,400,900` (`-0.01%`) | `2,334,648` (`+0.10%`) | `4,414,728` (`+0.25%`) |
| `C09_O3_thin_lto_pgo` | `2,300,556` (`-1.07%`) | `3,593,216` (`-6.60%`) | `229,976` | `2,383,120` (`-0.75%`) | `2,308,328` (`-1.03%`) | `4,072,328` (`-7.52%`) |
| `C10_O3_fat_lto_pgo` | `2,229,714` (`-4.12%`) | `3,140,280` (`-18.37%`) | **`172,608`** | `2,278,324` (`-5.12%`) | `2,188,328` (`-6.17%`) | `3,535,816` (`-19.70%`) |
| `C11_Os` | `2,312,192` (`-0.57%`) | `3,835,872` (`-0.29%`) | `320,764` | `2,385,668` (`-0.65%`) | `2,325,904` (`-0.27%`) | `4,398,520` (`-0.11%`) |
| `C12_Oz` | `2,311,496` (`-0.60%`) | `3,839,472` (`-0.20%`) | `322,044` | `2,385,748` (`-0.64%`) | `2,325,920` (`-0.27%`) | `4,402,256` (`-0.03%`) |
| `C11_Os_fat_lto` | `2,085,485` (`-10.32%`) | `3,083,000` (`-19.86%`) | `190,408` | `2,200,892` (`-8.34%`) | `2,079,288` (`-10.85%`) | **`3,511,736` (`-20.25%`)** |
| **`C12_Oz_fat_lto`** | **`2,084,101` (`-10.38%`)** | **`3,081,496` (`-19.90%`)** | `191,536` | **`2,199,040` (`-8.42%`)** | **`2,077,880` (`-10.91%`)** | `3,512,896` (`-20.22%`) |

#### 4.2 Non-Linux Tier 1 Targets (`aarch64-apple-darwin` and 4 Windows Targets)

On non-Linux Tier 1 targets where `std` linking requires proprietary target SDKs, `support/tier1_size_baselines.json` records both (a) the sum of `.text + .rodata`, stripped image, and unwind table sizes across all `W-Core` `.rlib` object members and `bench-ffi-no-std-crc32c` linked `cdylib` (`suite_size_summary_vs_C05`) and (b) per-workload `rlib` and `staticlib` sizes (`w_core_section_sizes`). Table 4 reports the suite size summary across all five non-Linux Tier 1 targets:

| Configuration | `aarch64-apple-darwin` `.text+.rodata` (B / $\Delta\%$) | `x86_64-pc-windows-msvc` `.text+.rodata` (B / $\Delta\%$) | `x86_64-pc-windows-gnu` `.text+.rodata` (B / $\Delta\%$) | `aarch64-pc-windows-msvc` `.text+.rodata` (B / $\Delta\%$) | `i686-pc-windows-msvc` `.text+.rodata` (B / $\Delta\%$) |
| :--- | ---: | ---: | ---: | ---: | ---: |
| `C01_O0` | `71,080` (`+245.98%`) | `85,863` (`+263.31%`) | `76,638` (`+179.85%`) | `85,486` (`+319.12%`) | `88,049` (`+242.82%`) |
| `C02_O1` | `15,942` (`-24.13%`) | `17,126` (`-14.16%`) | `17,520` (`-31.47%`) | `16,026` (`-15.23%`) | `17,085` (`-26.88%`) |
| `C03_O2` | `14,914` (`-17.38%`) | `14,544` (`-16.14%`) | `18,584` (`-22.58%`) | `13,250` (`-12.20%`) | `16,139` (`-13.50%`) |
| `C04_O3_no_lto` | `19,958` (`+0.87%`) | `20,895` (`+2.68%`) | `24,076` (`-1.56%`) | `17,222` (`+2.67%`) | `21,008` (`-0.23%`) |
| **`C05_O3_thinlocal`** | **`18,970` (`+0.00%`)** | **`19,914` (`+0.00%`)** | **`25,316` (`+0.00%`)** | **`16,030` (`+0.00%`)** | **`21,508` (`+0.00%`)** |
| `C06_O3_thin_lto` | `17,754` (`-14.86%`) | `15,662` (`-22.26%`) | `18,788` (`-25.20%`) | `15,674` (`-10.63%`) | `15,368` (`-30.65%`) |
| `C07_O3_fat_lto` | `14,252` (`-22.09%`) | `12,144` (`-31.11%`) | `17,228` (`-28.90%`) | `11,680` (`-22.62%`) | `12,415` (`-37.04%`) |
| `C11_Os` | `13,386` (`-36.64%`) | `13,087` (`-39.97%`) | `13,152` (`-52.36%`) | `13,218` (`-30.18%`) | `13,842` (`-44.57%`) |
| `C12_Oz` | `12,841` (`-39.08%`) | `13,042` (`-41.50%`) | `12,792` (`-53.69%`) | `13,521` (`-29.39%`) | `13,502` (`-46.10%`) |
| `C11_Os_fat_lto` | `13,219` (`-36.32%`) | `13,065` (`-39.67%`) | `13,060` (`-52.03%`) | `13,159` (`-29.80%`) | `14,057` (`-43.26%`) |
| `C12_Oz_fat_lto` | **`12,806` (`-38.50%`)** | `13,355` (`-40.86%`) | **`12,747` (`-53.51%`)** | `13,849` (`-28.48%`) | `13,910` (`-44.96%`) |

**Key binary-size findings:**
1. **Why `-Os`/`-Oz` without Fat LTO barely shrinks Linux `std` binaries (`-0.57%` to `-0.60%`):** In standard `C11_Os` and `C12_Oz` builds without `-C lto=fat`, the precompiled `libstd-*.rlib` and `libcore-*.rlib` shipped in the `rust-std-1.99.1` sysroot were compiled at `-C opt-level=3` and are linked verbatim (~`288 KB` `.text + .rodata` per binary). Only user crate code is compiled with `-Os`/`-Oz`. Once `-C lto=fat` (`C11_Os_fat_lto`, `C12_Oz_fat_lto`) is enabled, `rustc` re-optimizes the embedded LLVM bitcode of `core`/`alloc`/`std` under `-Os`/`-Oz` and internalizes dead `std` formatting/backtrace symbols, shrinking total `.text + .rodata` by **`-10.38%`** (`x86_64`) and **`-10.91%`** (`aarch64`) and stripped load images by **`-19.90%` to `-20.25%`**.
2. **Pure crate code size scaling on non-Linux targets:** When measuring user crate `.rlib` objects and `#![no_std]` `cdylib` images without prebuilt `std` noise (Table 4), `-C opt-level=0` (`C01_O0`) is **`2.80x` to `4.19x` larger** (`+179.85%` to `+319.12%`) than `C05_O3_thinlocal` due to uninlined iterator adapters and bounds-check panic paths, whereas `-C opt-level=z` (`C12_Oz`) shrinks `.text + .rodata` by **`-29.39%` to `-53.69%`** below `-O3` (suppressing loop unrolling and vectorization prologue/epilogue duplication).
3. **Unwind table overhead across ABIs:** On `x86_64-unknown-linux-gnu`, `.eh_frame` + `.eh_frame_hdr` + `.gcc_except_table` consumes `320,604 B` (`8.33%` of the stripped load image) under `C05_O3_thinlocal`, dropping to `172,608 B` (`-46.16%`) under `C10_O3_fat_lto_pgo`. On `i686-pc-windows-msvc` (32-bit SEH frame handler tables), unwind metadata across `W-Core` `.rlib` objects is only `416 B` at `C05`, compared to `2,180 B` on `x86_64-pc-windows-msvc` (`.pdata` + `.xdata` unwind info) and `2,808 B` on `aarch64-apple-darwin` (`__LD,__compact_unwind` + `__TEXT,__eh_frame`).

---

### 5. Compile-Time Phase Decompositions and Alternate Backend Comparison

Basis: execution + source + derived

#### 5.1 `-Z time-passes` Phase Breakdown Across the 14 Configurations

Every `W-Core` compilation under `rustc +1.99.1 -Z time-passes --error-format=json` was parsed into seven disjoint pipeline phases (`support/compile_time_phase_breakdowns.json`, `x86_64_suite_phase_aggregation`). Table 5 reports the aggregate wall-clock time summed across the 8 `W-Core` workloads and each phase's percentage share on `x86_64-unknown-linux-gnu`, alongside `W-Macro` workspace build wall-clock times (`cargo build -j 4`):

| Configuration | `W-Core` Total Wall Time (s) | Parse + Expand + Resolve (%) | Typeck + Borrowck + Lint (%) | Monomorphize + Partition (%) | SSR / LLVM IR Lowering (%) | LLVM Module Opt + Codegen (%) | LLVM LTO (`Thin`/`Fat`) (%) | Linker (`cc`/`ld`) (%) | Max Peak RSS (MiB) | `macro-serde-json` (`-j4`, s) | `macro-regex` (`-j4`, s) | `macro-syn` (`-j4`, s) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `C01_O0` | `0.541` | `6.15%` | `15.02%` | `7.77%` | `7.99%` | `11.01%` | `0.00%` | `46.25%` | `219` | `2.34` | `3.33` | `2.85` |
| `C02_O1` | `0.738` | `4.49%` | `10.49%` | `6.81%` | `3.81%` | `15.51%` | `19.28%` | `32.65%` | `230` | `2.77` | `6.18` | `7.29` |
| `C03_O2` | `0.792` | `4.21%` | `10.01%` | `8.44%` | `4.03%` | `15.31%` | `20.61%` | `31.43%` | `231` | `3.11` | `7.13` | `8.80` |
| `C04_O3_no_lto` | `0.753` | `4.42%` | `10.85%` | `8.68%` | `3.89%` | `33.63%` | `0.00%` | `32.47%` | `234` | `2.93` | `6.28` | `6.11` |
| **`C05_O3_thinlocal`** | **`0.857`** | **`3.88%`** | **`9.26%`** | **`7.50%`** | **`3.37%`** | **`15.86%`** | **`24.30%`** | **`29.52%`** | **`231`** | **`3.07`** | **`6.88`** | **`8.82`** |
| `C06_O3_thin_lto` | `18.270` | `0.19%` | `0.43%` | `0.34%` | `0.18%` | `0.76%` | **`95.90%`** | `1.95%` | `235` | `4.96` | `9.48` | `9.32` |
| `C07_O3_fat_lto` | `23.180` | `0.15%` | `0.36%` | `0.29%` | `0.11%` | **`97.13%`** | `0.00%` | `1.48%` | `214` | `6.20` | `18.56` | `16.81` |
| `C08_O3_no_lto_pgo` | `0.729` | `4.55%` | `11.15%` | `8.93%` | `4.85%` | `30.41%` | `0.00%` | `34.05%` | `244` | `2.78` | `6.71` | `6.62` |
| `C09_O3_thin_lto_pgo` | `18.401` | `0.18%` | `0.42%` | `0.35%` | `0.17%` | `0.52%` | **`95.99%`** | `2.12%` | `239` | `4.83` | `10.09` | `10.55` |
| `C10_O3_fat_lto_pgo` | `24.584` | `0.14%` | `0.34%` | `0.26%` | `0.08%` | **`97.36%`** | `0.00%` | `1.40%` | `220` | `6.21` | `20.37` | `18.78` |
| `C11_Os` | `0.760` | `4.29%` | `10.41%` | `6.96%` | `4.41%` | `17.42%` | `18.50%` | `31.73%` | `231` | `2.63` | `6.08` | `5.66` |
| `C12_Oz` | `0.719` | `4.54%` | `11.07%` | `7.30%` | `4.33%` | `16.02%` | `16.76%` | `33.20%` | `232` | `2.57` | `5.67` | `5.34` |
| `C11_Os_fat_lto` | `21.130` | `0.17%` | `0.38%` | `0.24%` | `0.10%` | **`96.87%`** | `0.00%` | `1.72%` | `213` | — | — | — |
| `C12_Oz_fat_lto` | `21.164` | `0.16%` | `0.40%` | `0.25%` | `0.11%` | **`97.01%`** | `0.00%` | `1.56%` | `212` | — | — | — |

*(Note: Under `-Z time-passes`, `rustc_codegen_llvm` reports `Lto::Thin` inside the `LLVM_lto_optimize` pass bucket (`backend_lto_sec`), whereas single-CGU `Lto::Fat` merges bitcode modules into one module and runs the full optimization pipeline inside `LLVM_module_optimize_and_codegen` (`backend_llvm_opt_and_codegen_sec`).)*

#### 5.2 Alternate Backend Comparison: Cranelift `0.134.0` (`cg_clif`) and GCC (`cg_gcc` / `libgccjit 15.0.1`)

Table 6 compares `rustc_codegen_cranelift` (`0.134.0`, loaded via `-Z codegen-backend=librustc_codegen_cranelift_clean.so` against its `1.99.1` sysroot on `x86_64-unknown-linux-gnu`) at both `clif_O0` (`-C opt-level=0`) and `clif_O3_inline_mir` (`-C opt-level=3 -Z inline-mir=yes`) against the corresponding LLVM 23.1.1 baselines (`C01_O0` and `C05_O3_thinlocal`):

| `W-Core` Workload | `clif_O3` Compile Time (`s` / Ratio vs. LLVM `C05`) | `clif_O3` Backend Codegen (`ms` vs. LLVM `C05` Opt+LTO `ms`) | `clif_O3` `.text+.rodata` (`Bytes` / Ratio vs. LLVM `C05`) | `clif_O3` Median Runtime ($\mu\text{s}$) | LLVM `C05` Median Runtime ($\mu\text{s}$) | `clif_O3 / LLVM C05` Speed Ratio (95% Bootstrap CI) | `clif_O0 / LLVM C01_O0` Speed Ratio |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `bench-serde-json` | `0.0776 s` (`0.56x`) | `8.11 ms` vs. `73.75 ms` (`0.11x`) | `1,438,635` (`4.94x`) | `67.08` | `159.04` (`21.40` `C06`) | `0.42x` vs. `C05` (`3.13x` vs. `C06`) | `0.83x` (`143.16` vs. `172.33` $\mu\text{s}$) |
| `bench-regex-automata` | `0.0653 s` (`0.71x`) | `3.85 ms` vs. `31.95 ms` (`0.12x`) | `1,432,099` (`4.97x`) | `115.90` | `0.0013` | `90,901.8x` (no loop dead-store folding) | `0.93x` (`217.81` vs. `233.27` $\mu\text{s}$) |
| `bench-hashbrown-indexmap` | `0.1025 s` (`0.56x`) | `25.67 ms` vs. `107.60 ms` (`0.24x`) | `1,469,307` (`4.94x`) | `498.45` | `33.58` | **`14.85x`** (`[10.34x, 15.09x]`) | **`0.19x`** (`632.92` vs. `3,297.81` $\mu\text{s}$) |
| `bench-simd-kernels` | `0.0650 s` (`0.63x`) | `4.03 ms` vs. `43.25 ms` (`0.09x`) | `1,431,483` (`4.86x`) | `37.79` | `12.28` | **`3.08x`** (`[2.97x, 3.32x]`) | `1.91x` (`266.65` vs. `139.64` $\mu\text{s}$) |
| `bench-unwind-drop-ladder` | `0.0340 s` (`0.40x`) | `4.00 ms` vs. `25.84 ms` (`0.15x`) | `2,145` (`rlib`) | *(`panic=abort` sysroot)* | `1,736.64` | *(Unwinding unsupported in `cg_clif` sysroot)* | *(Unwinding unsupported)* |
| `bench-concurrency-sync` | `0.0726 s` (`0.76x`) | `8.22 ms` vs. `34.23 ms` (`0.24x`) | `1,438,651` (`4.98x`) | `23.29` | `17.79` | **`1.31x`** (`[1.30x, 1.32x]`) | **`0.15x`** (`30.89` vs. `208.82` $\mu\text{s}$) |
| `bench-compression-image` | `0.0645 s` (`0.82x`) | `3.89 ms` vs. `21.23 ms` (`0.18x`) | `1,431,851` (`4.97x`) | `19.66` | `6.67` | **`2.95x`** (`[2.92x, 3.00x]`) | **`0.23x`** (`77.24` vs. `342.58` $\mu\text{s}$) |
| `bench-ffi-no-std-crc32c` | `0.0610 s` (`0.75x`) | `3.05 ms` vs. `24.16 ms` (`0.13x`) | `1,430,171` (`4.97x`) | `51.79` | `23.68` | **`2.19x`** (`[2.17x, 2.21x]`) | **`0.12x`** (`105.82` vs. `857.40` $\mu\text{s}$) |

Key findings from the alternate backend comparison:
1. **`cg_clif` at `-O0` beats LLVM `-O0` by `5.2x` to `8.1x` on scalar/container loops:** At `-C opt-level=0`, Cranelift's baseline instruction selector and register allocator generate dramatically tighter machine code than LLVM's FastISel (`0.12x` runtime on `bench-ffi-no-std-crc32c`, `0.15x` on `bench-concurrency-sync`, `0.19x` on `bench-hashbrown-indexmap`, `0.23x` on `bench-compression-image`), while matching total compile time (`0.90x`–`1.12x`).
2. **`cg_clif` at `-O3 -Zinline-mir` vs. LLVM `-O3` (`Tier_C` anchor):** At `-O3 -Zinline-mir`, Cranelift's backend codegen phase runs **`4.1x` to `10.7x` faster** than LLVM's module optimization + ThinLocal LTO passes (`3.05`–`25.67 ms` vs. `21.23`–`107.60 ms`), reducing end-to-end compile wall time by **`18.2%` to `59.8%`**. At runtime, `cg_clif` is **`1.31x` to `3.08x` slower** than LLVM `-O3` on `concurrency-sync` (`1.31x`), `crc32c` (`2.19x`), `compression-image` (`2.95x`), and `simd-kernels` (`3.08x`), and **`14.85x` slower** on `hashbrown-indexmap` where residual bounds checks and unvectorized group probes remain after MIR inlining.
3. **Why `cg_clif` linked binaries have `~1.43 MB` `.text + .rodata` (`4.9x` LLVM):** The prebuilt `cg_clif` `libstd` sysroot is compiled without `-Z function-sections=yes`, so `ld --gc-sections` cannot strip unused `std` functions from linked object units (`1,430,171 B` vs. `287,904 B` under LLVM `C05`). For pure `.rlib` code (`bench-unwind-drop-ladder`), `cg_clif` emits `2,145 B` of `.text + .rodata`.
4. **Tier 1 target gaps in `cg_clif 0.134.0` and `cg_gcc 0.1.0`:**
   - `cranelift-codegen 0.134.0` has no 32-bit x86 (`i686-unknown-linux-gnu`, `i686-pc-windows-msvc`) ISA backend and panics on `aarch64-pc-windows-msvc` COFF relocation `Aarch64AdrGotPage21` (`cranelift-object-0.134.0/src/backend.rs:992:22`). On the remaining non-host targets (`aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`), `sysroot_clif_target` only contains host `x86_64-unknown-linux-gnu` `libcore`/`libstd` rlibs, causing `E0463: can't find crate for core` unless target sysroots are cross-built per target.
   - `rustc_codegen_gcc 0.1.0` with stock Debian `libgccjit.so.15.0.1` rejects pointer-to-integer casts in constant initializers (`gcc_jit_context_new_cast: cannot cast &global.10 from type: struct ... * to type: size_t` at `compiler/rustc_codegen_gcc/src/common.rs:302:43`) when compiling `library/core`, requiring the patched `rust-lang/gcc` fork (`6f155cc3f5a2dff33afe6cc3ed6c2e0e605ae6a3`).

## Boundaries

1. **Hardware PMU cycle/instruction counters (`perf_event_open`) — unsupported on KVM guest:** Because the cloud host hypervisor sets `/proc/sys/kernel/perf_event_paranoid = 2` and does not expose hardware PMU counters (`cycles:u`, `instructions:u`, `branch-misses`, `L1-icache-load-misses`), all runtime measurements in `support/tier1_speed_baselines.json` use `CLOCK_MONOTONIC_RAW` (`Instant::now()`) under NUMA node 0 physical-core pinning (`numactl --cpunodebind=0 --membind=0 taskset -c <core>`), ASLR disablement (`setarch x86_64 -R`), and the 16-seed `--shuffle-sections` ensemble.
2. **Non-Linux Tier 1 runtime execution and `std` executable linking — bounded stop (proprietary SDK EULAs):** Executing `aarch64-apple-darwin` or `*-pc-windows-msvc` binaries or linking `std` executables against Apple's `libSystem.tbd` (`MacOSX.sdk`) or Microsoft's `msvcrt.lib` / `ucrt.lib` is **known not to apply** in a clean-room Linux environment without accepting proprietary Apple Xcode or Microsoft Visual Studio SDK licenses. Those five targets are covered via full `C01`..`C07` and `C11`..`C12` compile-time measurements, `.rlib` / `staticlib` section sizes, and `rust-lld` freestanding `#![no_std]` `cdylib`/`.dylib`/`.dll` binary section sizes.
3. **User-mode `qemu-aarch64` timings — known not to represent hardware pipeline stalls:** While `qemu-aarch64 -cpu max` executes all `aarch64-unknown-linux-gnu` `std` binaries and produces exact basic-block execution counts for LLVM IR PGO (`C08`..`C10`), its wall-clock latency reflects QEMU TCG translation and host execution rather than an out-of-order ARMv8/v9 hardware pipeline (as quantified by the `i686` native vs. `qemu-i386` experiment in Section 3.3).
4. **Full 24,545-test `compiletest` and stage-2 `rustc` self-profile across all 14 configurations — not examined:** Running a full stage-2 `rustc` bootstrap across 14 LTO/PGO configurations would exceed the 1-hour / 20 GB resource ceiling; `W-Macro` (`serde_json`, `regex`, `syn`, `parking_lot`+`bytes`) and `W-Core` provide the multi-crate and single-file phase decompositions required by downstream optimization studies.

## Evidence

### Primary Upstream Sources Examined

- **`rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, version `1.99.1`):**
  - `compiler/rustc_session/src/config.rs` and `compiler/rustc_codegen_ssa/src/back/write.rs`: `OptLevel` (`No`, `Less`, `Default`, `Aggressive`, `Size`, `SizeMin`), `Lto` (`No`, `ThinLocal`, `Thin`, `Fat`), `codegen-units` partitioning, and `-Z time-passes` JSON timing emission.
  - `compiler/rustc_codegen_cranelift/` (`v0.134.0`): `opt_level` mapping (`none` vs. `speed` + `-Z inline-mir`) and `cranelift-object` target relocation handling (`src/backend.rs:992:22`).
  - `compiler/rustc_codegen_gcc/src/common.rs:302:43`: `gcc_jit_context_new_cast` constant-initializer pointer-to-usize cast restriction on unpatched `libgccjit 15.0.1`.
- **`rust-lang/rustc-perf` (`b9d680e5dda9b6d9ff98716e9eed705dad3c105d`):**
  - `collector/src/compile/benchmark/{mod.rs,profile.rs,scenario.rs}`: compile-time `Profile` (`Check`, `Debug`, `Doc`, `Opt`, `Clippy`, `LlvmIr`) and `Scenario` (`Full`, `IncrFull`, `IncrUnchanged`, `IncrPatched`) definitions.
  - `collector/benchlib/src/benchmark.rs:115-218`: runtime `run_benchmark_group` calibration, warmup, and `black_box` measurement loop.
  - `collector/runtime-benchmarks/`: all 11 upstream runtime benchmark crates (`bufreader`, `compression`, `css`, `fmt`, `hashmap`, `nbody`, `nes`, `parsing`, `raytracer`, `svg`, `text-search`).

### Preserved Package Artifacts (`support/`)

All empirical outputs (acquired on `2026-11-13`) and the runnable harness are preserved in `support/`:
1. `support/q6_benchmark_harness.py`: Self-contained multi-target, multi-configuration benchmark and section-size collection harness (`W-Core` 8 workloads + `W-Macro` 4 workspaces, `llvm-size --format=sysv` parser, `-Z time-passes` JSON parser, IR PGO training pipeline, 16-seed `--shuffle-sections` / 8-seed `-Z randomize-layout` runner, and 10,000-resample bootstrap / Mann-Whitney U statistical engine).
2. `support/tier1_speed_baselines.json`: Full runtime latency distributions ($N = 30$, $M = 100$: `min`, `p25`, `median`, `p75`, `p90`, `p99`, `max`, `mean`, `stdev`, `cv_pct`, `iqr`, `normalized_iqr_pct`, `mad`), bootstrap 95% CIs and Mann-Whitney U tests vs. `C05_O3_thinlocal` and `C04_O3_no_lto`, `i686` native vs. `qemu-i386` ratios, 16-seed `--shuffle-sections` and 8-seed `-Z randomize-layout` distributions, and `cg_clif 0.134.0` comparisons.
3. `support/tier1_size_baselines.json`: Complete section-by-section (`executable_code`, `read_only_data`, `initialized_data`, `zero_initialized_bss`, `unwind_tables`, `debug_and_symbols`, `text_plus_rodata_bytes`, `allocatable_load_image_bytes`, `total_file_bytes`) baselines across all 8 Tier 1 targets and 14 configurations for both `W-Core` and `W-Macro`.
4. `support/compile_time_phase_breakdowns.json`: `-Z time-passes` 7-phase decompositions and peak RSS across all 14 configurations and 8 Tier 1 targets, plus `W-Macro` workspace build wall-clock times.
5. `support/parity_gate_specification.json`: Machine-readable specification of the `rustc-perf` static inventory, measurement/isolation protocol, per-workload $\sigma_{\text{layout}}$ noise floors, and `Tier_A` / `Tier_B` / `Tier_C` TOST non-inferiority parity gates.

## Revalidation

To revalidate the baseline dataset, check a newer `rustc` revision, or evaluate a candidate verified compiler against the `Tier_A` / `Tier_B` / `Tier_C` parity gates without repeating the full 50-minute sweep:

1. **Verify preserved dataset integrity and parity gate thresholds (< 1 second):**
   ```bash
   python3 -c '
   import json
   for f in ["tier1_speed_baselines.json", "tier1_size_baselines.json", "compile_time_phase_breakdowns.json", "parity_gate_specification.json"]:
       with open("reports/rustc-benchmark-methodology-and-speed-size-baselines/support/" + f) as fp:
           data = json.load(fp)
           print(f, "OK, top keys:", list(data.keys())[:5])
   '
   ```
2. **Run a fast single-target smoke revalidation of `W-Core` (`C04_O3_no_lto` vs. `C05_O3_thinlocal` vs. `C07_O3_fat_lto`):**
   Invoke `support/q6_benchmark_harness.py` (pointing `RUSTC` and `LLVM_SIZE` at the candidate toolchain) on `x86_64-unknown-linux-gnu` to regenerate section sizes (`llvm-size --format=sysv`), `-Z time-passes` phase breakdowns, and $N = 30$ pinned runtime measurements in ~3 minutes.
3. **Discriminating check for layout-sensitive regressions:**
   Whenever a candidate backend or pass modification alters median runtime on `bench-serde-json`, `bench-regex-automata`, `bench-concurrency-sync`, or `bench-compression-image` by less than the recorded layout spread (`19.60%`, `69.97%`, `8.57%`, and `5.63%`, respectively), compile both baseline and candidate with `-Z function-sections=yes -C link-arg=-fuse-ld=lld -C link-arg=-Wl,--shuffle-sections=*=<seed>` across seeds `1..16` and compare the inter-seed median distributions using the TOST bootstrap test in `support/q6_benchmark_harness.py`.
