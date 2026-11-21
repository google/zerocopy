# Generated-Code Performance, Microarchitectural Quality, Footprint, Stack, and Rigorous Statistical Benchmarking in `rustc`

## Summary

Evaluating whether a verified Rust compiler—or a modified MIR/LLVM optimization pipeline—matches upstream `rustc` on generated-code quality requires unambiguous, orthogonal metrics across six physical dimensions rather than single-seed wall-clock medians alone. Direct source inspection of `rust-lang/rust` (`412be32a6a189d9a28922beee178bc0abee9d492`), `rust-lang/llvm-project` (`08ec928a5bd1866f4008c8ad216166ca685fd380`), and `rust-lang/rustc-perf` (`15d95905429e577d5a710b17c49e04b4451c263b`), paired with live execution across `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`) and `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1`) preserved in `support/generated_code_metrics_specimen.json`, establishes the following findings and measurement laws:

1. **Latency quantiles, async coroutine state-machine footprint, and unwind cost (`Section 1`):** Steady-state medians conceal tail preemption, async allocation elision, and exception-handling cliffs. On a `16 KiB` streaming scan at `-C opt-level=2` / `-C opt-level=z` (`19,294 ns` median, `0.7909 GiB/s`, `3.0618 cycles/byte` at `2.60 GHz`), `p99` rises to `22,940`–`29,833 ns` (`1.19x`–`1.55x` median) and `p99.9` reaches `36,527`–`41,588 ns`. In `async fn` lowering (`compiler/rustc_mir_transform/src/coroutine/layout.rs`), scoping a `[u8; 1024]` local before `.await` shrinks `size_of_val(&fut)` by **`32.1x`** (`1,027 B` $\rightarrow$ `32 B`) across all optimization levels (`-O0` through `-Oz`), and two sequential `1,024 B` `.await` scopes overlap into `1,048 B` rather than `2,048 B`. Meanwhile, polling a 4-deep `Box::pin` coroutine speeds up **`170.4x`** from `-O0` (`214.34 ns`) to `-O3` (`1.258 ns`) via heap-to-stack allocation elision, whereas `-Os` (`20.59 ns`) and `-Oz` (`32.63 ns`) retain heap allocation under tightened CGSCC inline budgets (`50` and `5`). Even with a silent no-op panic hook (`std::panic::set_hook(Box::new(|_| {}))`), DWARF stack unwinding (`catch_unwind`) is **`375.6x` slower** than `Result::Err` at call depth `4` (`4,381.16 ns` vs. `11.66 ns` at `-O3`) and **`118.6x` slower** at call depth `32` (`19,927.75 ns` vs. `168.03 ns`).
2. **Microarchitectural dynamic counters, SIMD target-CPU cliffs, spill density, and MIR vs. LLVM `Assert` survival (`Section 2`):** Isolating kernel-only dynamic execution via `valgrind --tool=cachegrind --cache-sim=yes --branch-sim=yes` removes `~120,000` dynamic-loader (`ld-linux.so`) instructions and shows `-O0` $\rightarrow$ `-O3` cuts dynamic instructions (`Ir`) by **`-72.27%`** (`3,002,496` $\rightarrow$ `832,656`), data reads (`Dr`) by **`-87.04%`**, and data writes (`Dw`) by **`-90.18%`**, while `-Oz` achieves the lowest instruction-cache miss count (`I1mr = 20` vs. `90` at `-O0` and `29` at `-O3`) by shrinking static kernel instructions to `358` (`-27.5%` vs. `-O3`). Moving from `-C target-cpu=x86-64` (SSE2 baseline, no hardware FMA) to `-C target-cpu=x86-64-v3` (AVX2 + FMA) accelerates `f32::mul_add` dot-products by **`9.0x`** (`2,807.46 ns` $\rightarrow$ `312.16 ns`) and eliminates **`16,384` dynamic indirect branches (`Bi`: `18,448` $\rightarrow$ `2,064`)** because IEEE-754 single-rounding `mul_add` lowers to `vfmadd231ps ymm` instead of `fmaf@PLT` `libm` calls; `-C target-cpu=x86-64-v4` (AVX-512) further accelerates integer `u32` MAC by **`3.24x`** natively (`305.76 ns` $\rightarrow$ `94.34 ns`) while triggering `SIGILL` (`returncode = -4`) in Valgrind `3.25.1`'s VEX lifter. Across `google/zerocopy` (`0d0e0196aa4c95f7ccc1292a49b07a33011be371`, `4,301` optimized MIR bodies) and 6 canonical indexing/division kernels, `rustc`'s 221-line `SsaRangePropagation` pass (`compiler/rustc_mir_transform/src/ssa_range_prop.rs:1-221`) propagates only singleton equality ranges (`start == end`) and `bool` `otherwise` arms—leaving `15` `TerminatorKind::Assert` checks in `zerocopy` and `4 / 6` canonical idioms (`a[k & 0xff]`, `s[i % s.len()]`, `for k in 0..s.len()`, `if d != 0 { x / d }`) to be eliminated downstream by LLVM `-O2` (`0` surviving panic calls).
3. **Process startup, `SHT_RELR` packed relative relocations, and dual-layer heap telemetry (`Section 3`):** Enabling `-Wl,-z,pack-relative-relocs` (`SHT_RELR`) on a PIE `std` binary eliminates all `883` `R_X86_64_RELATIVE` entries from `.rela.dyn` (`22,776 B` $\rightarrow$ `1,584 B`), compressing `21,192 B` of `Elf64_Rela` records into a **`240 B` `.relr.dyn` bitmap (`-98.87%`)** and reducing median `fork + execve + wait4` cold startup latency by **`-24.81%`** (`3,124.66 µs` $\rightarrow$ `2,349.35 µs`; `p99`: `5,939.88 µs` $\rightarrow$ `4,065.98 µs`). Combining an atomic `#[global_allocator]` wrapper (`598` `alloc` calls, `302` `realloc` calls, `88,344 B` peak live Rust heap) with `valgrind --tool=dhat` (`137,068 B` whole-process `malloc` volume including `48,724 B` pre-`main` runtime setup, `142,440 B` heap reads, `142,677 B` heap writes) isolates both pre-`main` runtime overhead and **`16,964 B` of zero-read dead heap allocations**.
4. **Exact static-to-dynamic stack-bound law via `-Z emit-stack-sizes` (`Section 4`):** LLVM's `AsmPrinter::emitStackSizeSection` (`llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp:1698-1722`) emits `<uint64_le func_addr, ULEB128 stack_size>` pairs that (a) silently omit functions with variable-sized stack objects (`FrameInfo.hasVarSizedObjects()`), (b) omit prebuilt sysroot `STT_FUNC` symbols compiled without `-Z emit-stack-sizes` (`606 / 651` functions in a default `std` link), (c) exclude the `8 B` return address pushed by each caller `callq` on `x86-64`, and (d) exclude up to `128 B` of leaf-function System V ABI red-zone usage below `%rsp`. Consequently, naively summing `.stack_sizes` along a 4-deep `-O3` call chain (`544 B`) **under-approximates actual runtime stack consumption by `152 B` (`-21.8%`)**, whereas accounting for `callq` return pushes and leaf red-zone displacement (`544 B + 3 × 8 B + 128 B = 696 B`, or `672 B + 3 × 8 B = 696 B` under `-C no-redzone=yes`) matches live runtime stack-painting watermarks (**`696 B`**) to the **exact byte** across `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz`.
5. **Binary section attribution ladder and hardware energy accounting (`Section 5`):** Across an 11-step binary-diet progression, `-Z debuginfo-compression=zstd` shrinks `.debug_*` sections by **`-78.70%`** (`4,516,798 B` $\rightarrow$ `961,917 B`) without losing DWARF fidelity; `-C opt-level=z -C lto=fat -C codegen-units=1 -C panic=abort -Z location-detail=none -Z fmt-debug=none -C strip=symbols` with `--gc-sections --icf=all -z pack-relative-relocs` reduces total ELF file size by **`-94.31%`** (`5,197,080 B` $\rightarrow$ `295,512 B`); and a `#![no_std]` `-C force-unwind-tables=no` build reaches **`4,712 B`** (`242 B` `.text`). On cloud KVM guests, Linux exposes `/sys/bus/event_source/devices/power` (`type = 11`, `event = config:0-7`) with empty `events/` and denies unprivileged RAPL `energy-pkg`/`energy-ram` reads (`EACCES`, `errno = 13`) to block power side channels, requiring bare-metal `CAP_PERFMON` collection for Joule and Energy-Delay Product ($\text{EDP} = E \cdot T$) parity gates.
6. **3D Pareto hypervolume pruning and layout-randomized hierarchical TOST benchmarking (`Section 6`):** Evaluating (`Compile Time`, `Code Size`, `Runtime Speed`) jointly in 3D space reveals that 4 of the 14 canonical configurations in `rustc-benchmark-methodology-and-speed-size-baselines` (`C03_O2`, `C04_O3_no_lto`, `C07_O3_fat_lto`, and `C08_O3_no_lto_pgo`) are strictly dominated on all three axes ($HV = 0.550014$). In a live $K = 10$ seed $\times$ $R = 12$ invocation `ld.lld --shuffle-sections=*=<seed>` A/A null experiment (`rustc 1.99.1 -O3` seeds `1..10` vs. identical `-O3` seeds `101..110`), **naive single-seed Mann-Whitney U ($\alpha = 0.01$) produces false-positive regressions/speedups on `27%` to `63%` of seed pairs** (with pairwise seed shifts up to `69.16%`), whereas a two-level hierarchical bootstrap over `(seed, invocation)` paired with Two One-Sided Tests (`TOST`) and Holm-Bonferroni / Benjamini-Hochberg multiplicity control achieves **`0%` family-wise false positives** on the A/A null (`p_adj >= 0.630`) while cleanly isolating true `-C target-cpu=x86-64-v3` effects (`-88.18%` Hodges-Lehmann shift on `f32_dot_fma`, `-57.65%` on `u32_autovec_mac`, and a `+6.96%` GPR spill-scheduling regression on `reg_pressure_spills`, all at `BH q <= 0.0017`).

## Applicability

### Examined Subjects and Their Roles

| Subject | Repository | Pinned Revision | Version | Role in This Report |
| :--- | :--- | :--- | :--- | :--- |
| Rust compiler upstream source snapshot | `rust-lang/rust` | `412be32a6a189d9a28922beee178bc0abee9d492` | `1.102.0-dev` | Primary source authority for `-Z emit-stack-sizes`, `-C no-redzone`, `-Z location-detail`, `SsaRangePropagation`, MIR optimization pass ordering, and coroutine layout |
| Rust nightly compiler toolchain | `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `1.102.0-nightly` | Live execution compiler (bundled LLVM `23.1.5`) for `-Z emit-stack-sizes`, `-Z dump-mir`, `-Z debuginfo-compression=zstd`, `-Z location-detail=none`, and microarchitectural/footprint specimens |
| Rust 1.99.1 release compiler toolchain | `rust-lang/rust` | `58cf8f9c35b355199727627d07ae34a4e2846d67` | `1.99.1` | Stable release baseline (bundled LLVM `23.1.1`) for cross-version latency/Cachegrind checks, 14-profile 3D Pareto synthesis, and the 240-run `--shuffle-sections` hierarchical TOST study |
| Rust LLVM submodule snapshot | `rust-lang/llvm-project` | `08ec928a5bd1866f4008c8ad216166ca685fd380` | `23.1.x` | Primary source authority for `AsmPrinter::emitStackSizeSection` (`AsmPrinter.cpp:1698-1722`) and ELF `.stack_sizes` emission |
| Rust 1.99.1 LLVM 23.1.1 submodule | `rust-lang/llvm-project` | `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` | `23.1.1` | Bundled codegen/LTO/lld toolchain for `rustc 1.99.1` |
| `rustc-perf` benchmark collector and suite | `rust-lang/rustc-perf` | `15d95905429e577d5a710b17c49e04b4451c263b` | — | Upstream benchmark harness (`collector/src/artifact_stats.rs`, `collector/src/runtime/mod.rs`) contrasted against layout-randomized hierarchical protocols |
| `zerocopy` crate | `google/zerocopy` | `0d0e0196aa4c95f7ccc1292a49b07a33011be371` | `0.9.0-alpha` | Real-world `4,688`-body (`4,301` post-const-prune) crate evaluated for MIR `TerminatorKind::Assert` and `SsaRangePropagation` survival |

### Scope, Host Environment, and Relationship to Companion Corpus Packages

- **Host and execution environment:** All live measurements in `support/generated_code_metrics_specimen.json` were acquired on `x86_64-unknown-linux-gnu` running on an Intel Xeon Ice Lake-SP processor (`2.60 GHz` nominal base frequency, `SSE4.2` + `AVX2` + `FMA` + `BMI2` + `AVX-512` `F/BW/DQ/VL/VNNI/VBMI2`, Linux kernel `7.1.6-1rodete1-amd64` under KVM virtualization with `/proc/sys/kernel/perf_event_paranoid = 2`, `valgrind 3.25.1`, and toolchain-bundled `llvm-size`, `llvm-objdump`, `llvm-readelf`, and `ld.lld`).
- **Cross-version scope (`1.99.1` vs. `1.102.0-nightly`):** Stable flags (`-C opt-level=0..3/s/z`, `-C target-cpu=*`, `-C lto=*`, `-C panic=abort`, `-C strip=symbols`, `-C no-redzone=yes`, `-C force-unwind-tables=no`, and linker flags `-Wl,--gc-sections,--icf=all,-z,pack-relative-relocs,--shuffle-sections`) behave identically across `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), as verified by matched latency, Cachegrind `Ir`/`Dr`/`Dw` (`832,656 / 156,400 / 72,416` on both compilers at `-O3`), and static instruction counts (`494` and `569`). Unstable `-Z` flags (`-Z emit-stack-sizes`, `-Z dump-mir`, `-Z debuginfo-compression=zstd`, `-Z location-detail=none`, `-Z fmt-debug=none`) require nightly or `RUSTC_BOOTSTRAP=1`.
- **Relationship to companion corpus reports:**
  - `reports/rustc-benchmark-methodology-and-speed-size-baselines/` establishes the 14-configuration (`C01_O0`..`C12_Oz_fat_lto`) speed, `.text + .rodata`, and `-Z time-passes` baselines across `W-Core` (8 kernels), `W-Macro` (4 multi-crate workspaces), and all 8 Tier 1 targets. Section 6.1 of the present report computes the exact 3D Pareto frontier and hypervolume over that 14-configuration baseline without duplicating its per-target tables, while Sections 1–6 extend the methodology to tail quantiles, async coroutines, `catch_unwind`, PMU/Cachegrind/disassembly quality metrics, `SHT_RELR` startup cost, `DHAT` heap telemetry, `.stack_sizes` static call-graph verification, energy accounting, and formal A/A vs. A/B hierarchical equivalence testing.
  - `reports/rustc-size-optimized-compilation-parity-and-transformations/` documents how `-Os`/`-Oz` map to `OptimizationLevel::O2` plus `optsize`/`minsize`, `InlineCost` thresholds (`50` and `5`), and target-dependent `MachineOutliner`. Sections 1.2, 2.2, and 5.1 below connect those pass thresholds directly to async poll heap-allocation retention, L1I cache-miss reduction, and full-binary debuginfo/relocation/unwind stripping.
  - `reports/rust-stack-discipline-probes-red-zones-and-overflow/` documents prologue stack probes (`4096 B` x86 vs. `1024 B` AArch64 residual) and OS guard-page handlers; Section 4 below builds the complementary compile-time `.stack_sizes` binary decoder and static call-graph max-stack prover.

---

## Findings

### 1. Taxonomy of Execution Speed, Throughput, Tail-Latency, Async, and Unwind Metrics

Basis: source + execution + derived

Single-number runtime summaries (such as mean or median wall-clock duration) collapse distinct execution regimes that compiler transformations affect asymmetrically. A complete runtime speed evaluation separates four orthogonal measurement classes:

1. **Cold-start (first-invocation) vs. warm steady-state latency:** First-invocation latency in a freshly spawned process includes demand-paging minor page faults across `.text` and `.rodata`, L1I/L2/LLC instruction cache fills, ITLB/DTLB misses, and cold branch-target buffer (BTB) / TAGE predictor states. Warm steady-state latency measures throughput once working-set pages are resident and loop branch predictors have converged.
2. **Latency quantiles and tail dispersion (`median`, `IQR`, `Normalized IQR`, `p90`, `p95`, `p99`, `p99.9`, `max`):** Because OS timer ticks, vCPU hypervisor exits, and allocator slow paths induce right-skewed heavy tails without shifting the median, non-parametric dispersion ($\text{Normalized IQR} = (\text{p75} - \text{p25}) / \text{median}$) characterizes core execution stability while `p99` and `p99.9` capture tail amplification (such as alignment faults, page-crossing SIMD loads, or unamortized `realloc` spikes).
3. **Domain-normalized throughput (`ops/s`, `GiB/s`, and `cycles/byte`):** Converting raw duration $T$ over payload size $B$ bytes at nominal clock frequency $f_{\text{nom}}$ into $\text{cycles/byte} = (T \cdot f_{\text{nom}}) / B$ relates software speed directly to hardware issue-width and L1D load-port ceilings (for instance, `0.5`–`1.0 cycles/byte` for scalar byte loops vs. `< 0.15 cycles/byte` for 256-bit AVX2 loops).
4. **Control-plane state-machine and exceptional-path metrics:** Coroutine `Future` byte size (`core::mem::size_of_val(&fut)`), per-completion `Future::poll` latency, and `Result<T, E>` vs. `catch_unwind` stack-unwinding latency.

#### 1.1 Empirical Cold vs. Warm Latency Quantiles and Throughput (`16 KiB` Request Scan)

Table 1 reports measurements from `support/generated_code_metrics_specimen.json` (`experiment_1_latency_async_unwind`) for `process_request_16k` (a streaming 64-bit FNV-1a hash and structural delimiter counter over a `16,384 B` buffer), comparing `32` fresh-process first-call latencies against `2,000` warm in-process invocations across `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):

| Profile | Cold 1st-Call Median (`ns`) | Warm Median (`ns`) | Warm `IQR` (`ns` / `Norm IQR %`) | Warm `p90` (`ns`) | Warm `p95` (`ns`) | Warm `p99` (`ns`) | Warm `p99.9` (`ns`) | Throughput (`ops/s` / `GiB/s`) | `cycles/byte` (`@ 2.60 GHz`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `nightly_O0` | `69,036.5` | `68,568.5` | `1,565.8` (`2.28%`) | `78,903.0` | `87,158.1` | `100,406.4` | `115,841.4` | `14,584 / 0.2225` | `10.8812` |
| `nightly_O1` | `22,349.0` | `22,156.0` | `34.0` (`0.15%`) | `22,252.8` | `24,294.3` | `28,502.8` | `36,492.4` | `45,135 / 0.6887` | `3.5160` |
| `nightly_O2` | `19,455.5` | `19,294.0` | `1.0` (`0.01%`) | `20,514.7` | `22,437.0` | `29,832.9` | `41,588.3` | `51,830 / 0.7909` | `3.0618` |
| `nightly_O3` | `19,437.5` | `19,839.0` | `1,872.3` (`9.44%`) | `23,204.6` | `25,712.6` | `37,506.7` | `106,995.7` | `50,406 / 0.7691` | `3.1483` |
| `nightly_Os` | `19,542.0` | `19,294.0` | `1.0` (`0.01%`) | `23,210.0` | `23,693.4` | `33,975.7` | `42,968.7` | `51,830 / 0.7909` | `3.0618` |
| `nightly_Oz` | `19,431.5` | `19,294.0` | `2.0` (`0.01%`) | `19,297.0` | `19,800.1` | `22,939.6` | `36,526.6` | `51,830 / 0.7909` | `3.0618` |
| `r1991_O3` | `19,450.5` | `19,293.0` | `2.0` (`0.01%`) | `19,298.0` | `21,161.5` | `22,663.8` | `32,308.3` | `51,832 / 0.7909` | `3.0616` |
| `r1991_Oz` | `19,442.5` | `19,295.0` | `4.0` (`0.02%`) | `19,851.1` | `20,049.1` | `23,426.4` | `38,122.9` | `51,827 / 0.7908` | `3.0620` |

Two structural lessons emerge from Table 1:
- **Serial dependency chains pin throughput to `~3.06 cycles/byte` across `-O2`, `-O3`, `-Os`, and `-Oz`:** Because 64-bit FNV-1a (`h = (h ^ b) * 0x100000001b3`) carries a loop-carried 3-cycle integer `imul r64` latency dependency per byte on Ice Lake-SP (`LoadLatency` hidden behind out-of-order prefetch, `imul` throughput `1/cycle` but latency `3 cycles`), neither loop unrolling at `-O3` nor unroll suppression at `-Oz` alters the critical recurrence (`19,293`–`19,295 ns` = `3.062 cycles/byte` across `1.99.1` and `1.102.0-nightly`).
- **Why `IQR` and `p99` must accompany `median`:** During `nightly_O3`'s 2,000-request window, background host vCPU scheduling jitter lifted `IQR` to `1,872.3 ns` (`9.44%`) and `p99.9` to `106,995.7 ns`, whereas `nightly_O2` (`IQR = 1.0 ns`) and `r1991_O3` (`IQR = 2.0 ns`) experienced almost zero preemption. Reporting a sample `mean` without `Normalized IQR` and `p99` conflates transient hypervisor preemption with compiler code-generation regressions.

#### 1.2 Async Coroutine State-Machine Footprint (`size_of_val(&fut)`) and Poll Latency

In `rust-lang/rust` (`412be32a6a189d9a28922beee178bc0abee9d492`), `coroutine::StateTransform` (`compiler/rustc_mir_transform/src/lib.rs:668`, `compiler/rustc_mir_transform/src/coroutine/layout.rs`) lowers `async fn` bodies into state-machine structs during the `Runtime(Initial)` MIR transition—**before** backend optimization level selection. Only locals whose MIR liveness spans a `Yield` terminator (`Poll::Pending` suspension point) are saved as coroutine fields, and non-conflicting locals live across disjoint suspension points share storage slots via conflict-graph coloring:

| Async Coroutine / Error Benchmark | `-O0` (`nightly` / `1.99.1`) | `-O1` | `-O2` | `-O3` (`nightly` / `1.99.1`) | `-Os` | `-Oz` (`nightly` / `1.99.1`) | Governing Compiler Mechanism |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| `size_of_val(&fut_live_across_await_1k)` (`B`) | `1,027` / `1,027` | `1,027` | `1,027` | `1,027` / `1,027` | `1,027` | `1,027` / `1,027` | `[u8; 1024]` + `2 × 1 B` `YieldOnce` + `1 B` discriminant (`align = 1`) |
| `size_of_val(&fut_scoped_before_await_1k)` (`B`) | **`32` / `32`** | **`32`** | **`32`** | **`32` / `32`** | **`32`** | **`32` / `32`** | Block-scoped `[u8; 1024]` dies before `.await`; excluded from state machine (**`-96.9%`**) |
| `size_of_val(&fut_disjoint_two_branches_1k)` (`B`) | **`1,048` / `1,048`** | **`1,048`** | **`1,048`** | **`1,048` / `1,048`** | **`1,048`** | **`1,048` / `1,048`** | Two sequential `[u8; 1024]` `.await` scopes share overlapping variant storage (`1,048 B` vs. `2,048+ B`) |
| `size_of_val(&fut_nested_depth4)` (`B`) | `144` / `144` | `144` | `144` | `144` / `144` | `144` | `144` / `144` | 4-level nested `async fn` composition (`[u64; 8]` leaf state + discriminants) |
| `Box::pin(fut_nested_depth4)` complete poll (`ns`) | `214.34` / `436.88` | `20.11` | **`1.667`** | **`1.258` / `1.518`** | `20.59` | `32.63` / `33.94` | `-O2`/`-O3` inline `poll` + elide `Box::pin` `malloc`/`free`; `-Os`/`-Oz` retain heap alloc (`26x` slower) |
| `result_ladder` (`Err`, depth `4` / depth `32`, `ns`) | `50.26` / `598.21` | `11.35` / `154.09` | `15.82` / `226.40` | **`11.66` / `168.03`** | `11.61` / `179.83` | `14.25` / `211.87` | Scalar discriminant compare + register `ret` + inline `DropGuard` (`~5.25 ns/frame` at `-O3`) |
| `catch_unwind` (`panic_any`, depth `4` / `32`, `ns`) | `5,498` / `19,659` | `4,415` / `24,777` | `6,097` / `21,010` | **`4,381` / `19,928`** | `4,493` / `18,914` | `4,688` / `19,125` | `_Unwind_RaiseException` 2-phase `.eh_frame_hdr` + `.gcc_except_table` walk (`~623 ns/frame`) |
| **`catch_unwind / Result::Err` slowdown ratio (`d=4 / d=32`)** | `109.4x / 32.9x` | `389.1x / 160.8x` | `385.4x / 92.8x` | **`375.6x / 118.6x`** | `387.1x / 105.2x` | `329.0x / 90.3x` | Pure DWARF unwinder table walk (silent panic hook installed to exclude `stderr` I/O) |

Key implications for verified code generation:
1. **Coroutine `size_of_val` parity is governed at MIR, while `poll` speed is governed by CGSCC inlining and allocation elision:** Because `size_of_val(&fut)` (`1,027 B`, `32 B`, `1,048 B`, `144 B`) is invariant from `-O0` to `-Oz` on both `1.99.1` and `1.102.0-nightly`, any backend consuming post-`StateTransform` `Runtime(PostCleanup)` MIR inherits upstream coroutine memory layout automatically. However, achieving `-O2`/`-O3` async poll speed (`1.26`–`1.67 ns` vs. `20.59`–`32.63 ns` at `-Os`/`-Oz`) requires inlining `Future::poll` across nested state machines so `InstCombine` can prove the `Box::pin` allocation never escapes and elide the `__rust_alloc` / `__rust_dealloc` pair.
2. **Benchmarking `catch_unwind` requires silencing `std`'s panic hook:** By default, `panic_any` invokes `std`'s default panic hook (`stderr` mutex lock + formatting + `write(2)` syscall) *before* entering `libgcc_s`'s `_Unwind_RaiseException`. Installing `std::panic::set_hook(Box::new(|_| {}))` isolates the true generated-code unwind cost: binary search over `.eh_frame_hdr`, DWARF Call Frame Information (CFI) register restoration per frame in `.eh_frame`, and Language-Specific Data Area (LSDA) landing-pad dispatch in `.gcc_except_table` (`~4.38 µs` base + `~486 ns` per additional stack frame at `-O3`).

---

### 2. Microarchitectural Code-Quality Metrics: PMU, Cachegrind, SIMD, Spills, and Bounds Checks

Basis: source + execution + derived

Wall-clock timing cannot tell *why* generated machine code is slow or whether two backends achieve similar speed for fragile accidental reasons. Microarchitectural evaluation decomposes code quality into dynamic pipeline/hierarchy metrics and static instruction-stream metrics.

#### 2.1 Hardware PMU (`perf_event_open` Syscall `298`), Software Counters, and TMA Level 1

In Linux on `x86-64`, `rustc-perf` and low-overhead profilers invoke syscall `298` (`__NR_perf_event_open`) passing `struct perf_event_attr` with `exclude_kernel = 1` (bit `5`) and `exclude_hv = 1` (bit `6`) to count strictly user-space (`:u`) retirements and stalls:
- **Core hardware PMU ratios:** Instructions Per Cycle $\text{IPC} = \text{instructions:u} / \text{cycles:u}$, dynamic instruction count (`instructions:u`), branch misprediction rate $\text{branch-misses:u} / \text{branches:u}$, and L1D / LLC miss rates.
- **Intel Top-Down Microarchitecture Analysis (`TMA` Level 1):** On Ice Lake / Sapphire Rapids P-cores (`IssueWidth = 6` pipeline slots/cycle, `PERF_METRICS` MSR `0x329` paired with fixed counter `3` `TOPDOWN.SLOTS` raw config `0x0400`), pipeline issue slots partition into four exhaustive fractions summing to `1.0`:
  $$\text{Retiring} = \frac{\text{UOPS\_ISSUED.RETIRED\_SLOTS}}{\text{TOPDOWN.SLOTS}}, \qquad \text{Bad Speculation} = \frac{\text{UOPS\_ISSUED.ANY} - \text{UOPS\_RETIRED.RETIRE\_SLOTS} + 6 \cdot \text{INT\_MISC.RECOVERY\_CYCLES}}{\text{TOPDOWN.SLOTS}}$$
  $$\text{Frontend Bound} = \frac{\text{IDQ\_UOPS\_NOT\_DELIVERED.CORE}}{\text{TOPDOWN.SLOTS}}, \qquad \text{Backend Bound} = 1 - (\text{Retiring} + \text{Bad Speculation} + \text{Frontend Bound})$$
  Compiler optimizations shift bottlenecks across TMA quadrants in diagnostic ways: poor loop alignment or instruction bloat inflates **Frontend Bound** (DSB-to-MITE switches and L1I misses); unpromoted `dyn Trait` calls or unpredicted bounds checks inflate **Bad Speculation**; register-allocator spills and unvectorized scalar chains inflate **Backend Bound** (Core Bound / Memory Bound) while inflating `Retiring` slot counts without improving runtime.
- **Live KVM hypervisor probe (`support/generated_code_metrics_specimen.json`, `pmu_and_rapl_host_probe`):** Probing syscall `298` directly on the cloud KVM host (`/proc/sys/kernel/perf_event_paranoid = 2`) establishes an exact operational boundary:
  - All `PERF_TYPE_HARDWARE` (`type = 0`: `HW_CPU_CYCLES`, `HW_INSTRUCTIONS`, `HW_CACHE_REFERENCES`, `HW_CACHE_MISSES`, `HW_BRANCH_INSTRUCTIONS`, `HW_BRANCH_MISSES`) and raw `TOPDOWN.SLOTS` (`type = 4, config = 0x0400`) fail closed with **`errno = 2` (`ENOENT`)** when the guest hypervisor disables virtual PMU (`vPMU`) passthrough.
  - All six `PERF_TYPE_SOFTWARE` counters (`type = 1`: `SW_CPU_CLOCK`, `SW_TASK_CLOCK`, `SW_PAGE_FAULTS`, `SW_CONTEXT_SWITCHES`, `SW_PAGE_FAULTS_MIN`, `SW_PAGE_FAULTS_MAJ`) succeed (`errno = 0`) even at `perf_event_paranoid = 2`. Crucially, however, setting `exclude_kernel = 1` causes `SW_PAGE_FAULTS_MIN` and `SW_CONTEXT_SWITCHES` to read `0` because page-fault exception handlers (`exc_page_fault`) and scheduler context switches (`__schedule`) retire inside ring 0; software fault/switch counters must therefore be opened with `exclude_kernel = 0` while hardware cycle/instruction counters retain `exclude_kernel = 1, exclude_hv = 1`.

#### 2.2 Kernel-Isolated `Cachegrind` Dynamic Profiles and Static `llvm-objdump` Code-Quality Metrics

When hardware PMU counters are masked in cloud/CI containers, `valgrind --tool=cachegrind --cache-sim=yes --branch-sim=yes` provides deterministic, zero-variance dynamic instruction (`Ir`), L1I/LLi (`I1mr`, `ILmr`), data read/write (`Dr`, `D1mr`, `DLmr`, `Dw`, `D1mw`, `DLmw`), conditional branch (`Bc`, `Bcm`), and indirect branch (`Bi`, `Bim`) counts. Two methodological rules are mandatory:
1. **Explicit `--cache-sim=yes`:** Modern Valgrind (`3.20+`, including `3.25.1`) defaults to `--cache-sim=no`, emitting only `Ir` unless `--cache-sim=yes --branch-sim=yes` are passed explicitly.
2. **Symbol-level `fn=` filtering (`parse_cachegrind_out`):** Whole-process `summary:` lines include `~120,000` `Ir` and `~4,500` `Bcm` from glibc's dynamic linker (`_dl_start`, symbol hash lookup) before `main`. Summing `cg.out` records strictly across target `#[no_mangle]` kernel symbols isolates exact compiler-generated dynamic execution.

Table 2 combines the kernel-isolated `Cachegrind` dynamic profiles, native per-suite execution latency, and static `llvm-objdump -d -M intel` code-quality metrics across 8 optimization and `target-cpu` configurations on `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, cross-checked against `rustc 1.99.1` `58cf8f9c35b355199727627d07ae34a4e2846d67`):

| Profile (`CGU=1`) | Native Suite Median (`ms`) | Dynamic `Ir` (Kernels Only) | Dynamic `Dr` / `Dw` | `I1mr` / `Bcm` / `Bi` (`Bim`) | Static Insns / BBs | Stack Spills (`All` / `20-GPR` per `100` Insns) | SIMD Mix (`ScalarFP` / `XMM` / `YMM` / `FMA`) | Direct / Indirect Calls (`% Direct`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `O0_x86_64` | `3.897` | `3,002,496` | `1,206,384 / 737,744` | `90 / 62 / 2,048 (2,048)` | `1,039 / 123` | **`56.50` / `77.59`** | `3 / 34 / 0 / 0` | `49 / 25` (`66.2%`) |
| `O1_x86_64` | `1.232` | `914,576` | `185,104 / 72,464` | `26 / 126 / 18,448 (2,053)` | `475 / 35` | `21.05 / 37.76` | `3 / 26 / 0 / 0` | `6 / 5` (`54.6%`) |
| `O2_x86_64` | `0.979` | `832,656` | `156,400 / 72,416` | `28 / 143 / 18,448 (2,053)` | `491 / 38` | `19.35 / 36.04` | `3 / 63 / 0 / 0` | `6 / 5` (`54.6%`) |
| `O3_x86_64` | `0.990` | `832,656` | `156,400 / 72,416` | `29 / 134 / 18,448 (2,053)` | `494 / 39` | `19.23 / 36.04` | `3 / 63 / 0 / 0` | `6 / 5` (`54.6%`) |
| `Os_x86_64` | `1.194` | `869,280` | `180,976 / 72,432` | `24 / 137 / 18,448 (2,053)` | `392 / 29` | `23.72 / 36.60` | `3 / 26 / 0 / 0` | `6 / 5` (`54.6%`) |
| `Oz_x86_64` | `1.237` | `913,984` | `178,816 / 76,400` | **`20` / `83`** / `18,448 (2,053)` | **`358 / 28`** | `20.11` / **`30.86`** | `3 / 26 / 0 / 0` | `6 / 5` (`54.6%`) |
| **`O3_x86_64_v3`** | **`0.695`** | **`721,536`** | **`129,728 / 43,696`** | `32 / 156` / **`2,064` (`2,049`)** | `569 / 55` | **`15.29`** / `40.10` | `5 / 33` / **`29` / `3`** | **`6 / 1` (`85.7%`)** |
| **`O3_x86_64_v4`** | **`0.694`** | *(Valgrind `SIGILL`)* | *(Valgrind `SIGILL`)* | *(EVEX `0x62` unsupported)* | `569 / 55` | `15.29 / 40.10` | `5 / 33 / 29 / 3` | `6 / 1` (`85.7%`) |

*(Cross-version verification: `rustc 1.99.1` at `O3_x86_64` and `O3_x86_64_v3` produces bit-identical dynamic instruction and memory counts—`Ir = 832,656`, `Dr = 156,400`, `Dw = 72,416` at `x86-64`, and `Ir = 721,536`, `Dr = 129,728`, `Dw = 43,696` at `x86-64-v3`—and identical static instruction/SIMD/spill counts `494` and `569`.)*

Four high-leverage microarchitectural insights follow directly from Table 2 and per-kernel breakdowns:
1. **Why `-C target-cpu=x86-64-v3` eliminates `16,384` indirect branches and accelerates `f32::mul_add` by `9.0x`:** Rust's `f32::mul_add(a, b, c)` guarantees IEEE-754 fused multiply-add with a *single* rounding step. Because the default `x86_64-unknown-linux-gnu` baseline target (`-C target-cpu=x86-64`, `x86-64-v1`) assumes only SSE2 and lacks hardware `FMA3`, LLVM cannot lower `f32::mul_add` to `mulps + addps` (which double-rounds!); instead, at `-O1`..`-Oz`, it emits `call fmaf@PLT` into `libm` (`16` outer reps $\times$ `1,024` elements = `16,384` PLT indirect jumps `jmp qword ptr [rip + fmaf@GOTPCREL]`, accounting for the exact jump from `Bi = 2,064` to `Bi = 18,448`!). Enabling `-C target-cpu=x86-64-v3` unlocks hardware `FMA` + `AVX2`, collapsing all `1,024` calls per pass into 8-wide 256-bit `vfmadd231ps ymm` instructions (`3` static FMA vector ops, `0` PLT calls) and slashing `kernel_f32_dot_fma` runtime from `2,807.46 ns` to **`312.16 ns`** (`344.65 ns` on `1.99.1`).
2. **SIMD vector width progression (`x86-64` $\rightarrow$ `x86-64-v3` $\rightarrow$ `x86-64-v4`) and Valgrind's EVEX ceiling:** On `kernel_u32_autovec_mac` (`1,024`-element `u32` multiply-accumulate + shift-xor), `-O0` runs in `8,344.56 ns` (scalar GPR loop), `-O1` runs in `1,176.90 ns`, `-O2`/`-O3` (`x86-64`) autovectorize with 128-bit SSE2/SSE4.1 (`63` `XMM` instructions vs. `26` at `-O1`/`-Os`/`-Oz`) to reach **`304.11`–`305.76 ns`** (`27.3x` faster than `-O0`), `O3_x86_64_v3` (`29` 256-bit `YMM` instructions) reaches **`159.82 ns`** (`93.72 ns` on `1.99.1`), and `O3_x86_64_v4` (`AVX-512VL` EVEX 256/512-bit encoding) reaches **`94.34 ns`**. Because Valgrind `3.25.1`'s VEX `amd64->IR` lifter aborts with `SIGILL` (`returncode = -4`) on `0x62`-prefixed EVEX instructions, dynamic simulation of `x86-64-v4` / `icelake-server` binaries requires Intel SDE (`sde64`) or bare-metal PMU rather than Cachegrind/DHAT.
3. **Register-allocation spill/reload density (`spills_per_100_insns`):** Counting non-`lea` stack-frame memory operands (`[rsp + disp]` / `[rbp - disp]`) per 100 static instructions cleanly separates unoptimized stack-slot codegen (`56.50` across all kernels, `77.59` in the 20-live-variable `kernel_reg_pressure_spills`) from greedy/RAGreedy register allocation (`19.23` across all kernels, `36.04` in `kernel_reg_pressure_spills` at `-O2`/`-O3`, matching dynamic `Dw` dropping **`10.19x`** from `737,744` at `-O0` to `72,416` at `-O3` and `43,696` at `x86-64-v3`). Notice a subtle secondary effect: on GPR-only `kernel_reg_pressure_spills`, `-C target-cpu=x86-64-v3` increases stack memory operands from `71` (`36.04%`) to `79` (`40.10%`), slowing that specific kernel by **`+6.69%`** (`1,814.00 ns` $\rightarrow$ `1,935.29 ns`; confirmed statistically at `p < 0.0001` in Section 6.2).
4. **Indirect-call devirtualization limits on alternating slice elements:** In `kernel_dyn_dispatch_and_memops`, iterating `stages[i & 1].step(state)` over a local `[&dyn OpStage; 2]` array retains `1` indirect vtable `call qword ptr [rax + 24]` per loop iteration (`Bi = 2,048`, `Bim = 2,048` — a **`99.3%`–`100.0%` indirect branch misprediction rate** under Cachegrind's single-target BTB simulator because the target alternates between `MulStage::step` and `XorStage::step` on every iteration!), whereas `d_slice.copy_from_slice(s_slice)` lowers inline without external `memcpy@PLT` calls at `-O1`..`-O3` (`memcpy_memset_calls = 0`).

#### 2.3 Surviving Bounds-Check / `Assert` Density: MIR `SsaRangePropagation` vs. LLVM `-O2`

A central question for verified Rust compilation is how many runtime safety checks (`TerminatorKind::Assert` for slice bounds, arithmetic overflow, and division/remainder by zero) `rustc`'s own MIR optimizer (`-Z mir-opt-level=2`) discharges versus how many depend on LLVM's middle-end (`EarlyCSE`, `GVN`, `CorrelatedValuePropagation`, `IndVarSimplify`).

Direct source inspection of `compiler/rustc_mir_transform/src/ssa_range_prop.rs:1-221` and `compiler/rustc_mir_transform/src/lib.rs:754-771` in `rust-lang/rust` (`412be32a6a189d9a28922beee178bc0abee9d492`) reveals three exact structural boundaries in `SsaRangePropagation`:
1. **Singleton-equality `WrappingRange` only (`ssa_range_prop.rs:101-114`):** `RangeSet::try_as_constant` folds an SSA `Place` to a `ConstOperand` *only* when `range.start == range.end`. It never derives relational interval inequalities (`i < len`) from arithmetic or bitwise operations.
2. **Operand rewrite without terminator replacement (`ssa_range_prop.rs:161-177`):** When `GVN` (`lib.rs:755`) unifies an `if i < s.len()` branch condition and a subsequent slice `Assert` condition into the same boolean local `_3`, `SsaRangePropagation` (`lib.rs:759`) rewrites `_3` inside `Assert(copy _3, true)` to `const true`, leaving the `TerminatorKind::Assert` intact until `SimplifyConstCondition::AfterConstProp` (`lib.rs:764`) and `SimplifyCfg::Final` (`lib.rs:771`) fold `Assert(const true, true)` into `Goto`.
3. **Boolean-only `otherwise` arm (`ssa_range_prop.rs:204-218`):** On `TerminatorKind::SwitchInt`, `SsaRangePropagation` records a range on the `otherwise` branch *only* when `place.ty(...).ty.is_bool()`. For `if d != 0 { x / d }` (`d: u32`), `SwitchInt(copy d) -> [0: bb_else, otherwise: bb_then]` records **no** non-zero range `[1, u32::MAX]` on `bb_then` (`FIXME: The range for the otherwise target be extend to more types`), so `Eq(copy d, 0)` inside `x / d` cannot fold at MIR!

Table 3 presents both (a) the 6 canonical slice/division kernels from `support/generated_code_metrics_specimen.json` (`mir_vs_llvm_assert_survival`) and (b) the full crate-wide MIR `Assert` lifecycle across `google/zerocopy` (`0d0e0196aa4c95f7ccc1292a49b07a33011be371`, compiled with `rustc 1.102.0-nightly` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` at `-C opt-level=2 -Z mir-opt-level=2`):

| Subject / Kernel | `PostCleanup` (`SimplifyCfg-pre-opt`) `Assert`s | After `SsaRangePropagation` `Assert`s | Final MIR (`SimplifyCfg-final`) `Assert`s | LLVM `-O2` IR Surviving Panic Calls | Mechanism Explaining MIR Survival vs. LLVM Elimination |
| :--- | ---: | ---: | ---: | ---: | :--- |
| `idx_const_in_bounds` (`a[7]` on `&[u32; 16]`) | `1` | `1` | **`0`** | **`0`** | `DataflowConstProp` evaluates `Lt(7, 16) -> true`; `SimplifyConstCondition` folds `Assert` |
| `idx_slice_guard` (`if i < s.len() { s[i] }`) | `1` | `1` *(operand `true`)* | **`0`** | **`0`** | `GVN` merges `Lt(i, len)` + `SsaRangeProp` sets `[1, 1]` + `SimplifyConstCondition` folds |
| `idx_bitmask_256` (`a[k & 0xff]` on `&[u8; 256]`) | `1` | `1` | **`1`** | **`0`** | MIR lacks bitwise `computeKnownBits`; LLVM `InstCombine` proves `(k & 255) < 256` |
| `idx_rem_nonempty` (`if !s.is_empty() { s[i % s.len()] }`) | `2` | `2` | **`1`** | **`0`** | MIR folds `!(len == 0)` (`2 -> 1`), but cannot prove `(i % len) < len`; LLVM `CVP` proves `urem < d` |
| `idx_for_iter_sum` (`for k in 0..s.len() { s[k] }`) | `1` | `1` | **`1`** | **`0`** | MIR lacks loop SCEV induction-variable bounds; LLVM `IndVarSimplify` eliminates check |
| `checked_div_guard` (`if d != 0 { x / d }`, `d: u32`) | `1` | `1` | **`1`** | **`0`** | `ssa_range_prop.rs:206` skips non-`bool` `SwitchInt` `otherwise` arm; LLVM `GVN`/`CVP` proves `d != 0` |
| **`google/zerocopy` (`4,688` $\rightarrow$ `4,301` MIR bodies)** | **`19`** (`4` bounds, `4` ovf, `7` div/rem, `4` other) | **`15`** (`4` bounds, `0` ovf, `7` div/rem, `4` other) | **`15`** (`4` bounds, `0` ovf, `7` div/rem, `4` other) | *(Lowered to LLVM)* | `4` const/overflow bodies pruned (`4,688 -> 4,301`); `15` `Assert`s (`4` bounds + `7` div/rem + `4` other) handed to LLVM |

---

### 3. Process Startup, Dynamic Relocations (`RELA` vs. `RELR`), and Runtime Heap Footprint

Basis: execution + derived

#### 3.1 Cold Process Startup (`execve`) and Packed Relative Relocations (`SHT_RELR`)

Default Rust Linux executables compile as Position-Independent Executables (`PIE`, `-C relocation-model=pic`) so the kernel can randomize their load base under ASLR. Every initialized pointer inside `.data.rel.ro`—including every trait-object vtable pointer (drop-in-place, size, align, and method pointers) and static function-pointer table—requires dynamic base-address relocation by `ld-linux-x86-64.so.2` before `main` executes. Under traditional SysV `DT_RELA` (`.rela.dyn`), each `R_X86_64_RELATIVE` entry occupies **`24 bytes`** (`Elf64_Rela`: `8 B` `r_offset` + `8 B` `r_info` + `8 B` `r_addend`). Passing `-C link-arg=-Wl,-z,pack-relative-relocs` to `ld.lld` encodes relative relocations into `SHT_RELR` (`.relr.dyn`), where one `8 B` base address word is followed by `63`-slot bitmaps (`1 bit` per contiguous `8 B` pointer slot!).

Table 4 reports the relocation section sizes, `llvm-readelf -r` relocation counts, and `N = 80` cold `fork + execve + wait4` startup latencies from `support/generated_code_metrics_specimen.json` (`experiment_3_startup_relocations_and_heap.startup_and_relocations`) on a binary containing `std` plus a `256`-entry function-pointer table in `.data.rel.ro`:

| Binary Variant | `R_X86_64_RELATIVE` Count | `GLOB_DAT` / `JUMP_SLOT` | `.rela.dyn` (`Bytes`) | `.relr.dyn` (`Bytes`) | `.data.rel.ro` (`Bytes`) | Total File (`Bytes`) | Startup Median (`µs`) | Startup `p90` / `p99` (`µs`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `std_pie_default_rela` (`-O3`, default `RELA`) | **`883`** | `66` / `2` | **`22,776`** | `0` | `9,312` | `4,639,032` | `3,124.66` | `4,605.64` / `5,939.88` |
| `std_pie_packed_relr` (`-O3 -Wl,-z,pack-relative-relocs`) | **`0`** *(in `.relr.dyn`)* | `66` / `2` | **`1,584`** | **`240`** | `9,312` | `4,618,208` | **`2,349.35`** (`-24.8%`) | **`3,666.28` / `4,065.98`** (`-31.5%`) |
| `nostd_libc_minimal` (`#![no_std] _exit(0)` + `RELR`) | `0` *(in `.relr.dyn`)* | `6` / `1` | `144` | `24` | `0` | **`6,072`** | `2,852.66` | `3,725.98` / `6,220.07` |

Key findings:
- **`98.87%` relative-relocation compression:** Packing `883` `R_X86_64_RELATIVE` records replaces `883 × 24 = 21,192 B` of `.rela.dyn` with **`240 B`** of `.relr.dyn` (`0.27 bytes/relocation`), shrinking total relocation tables by **`-92.00%`** (`22,776 B` $\rightarrow$ `1,824 B`) and speeding up dynamic-linker startup by **`-24.81%`** at median (`-31.55%` at `p99`) because `glibc` processes `63` contiguous pointer slots per `64`-bit bitmap word without reading `24 B` `Elf64_Rela` structs from L1D/L2 cache.
- **Startup floor attribution:** Comparing `nostd_libc_minimal` (`_exit(0)` with zero `std::rt::lang_start` initialization) against `std_pie_packed_relr` shows that `~2.0`–`2.3 ms` on this host comes from Linux kernel `fork` + `execve` VMA teardown/creation + `ld-linux-x86-64.so.2` mapping `libc.so.6`, while Rust's `std::rt::init` (`SIGSEGV` altstack `mmap` + `stdio`/`env` guards) adds `< 300 µs` once `RELR` is enabled.

#### 3.2 Dual-Layer Runtime Heap and Allocator Telemetry (`GlobalAlloc` + `Valgrind DHAT`)

Measuring memory footprint via OS peak RSS (`VmHWM` / `getrusage(ru_maxrss)`) alone has `4 KiB`–`2 MiB` page granularity and never frees reclaimed arena pages back to the OS watermark. Rigorous allocator benchmarking combines two complementary instrumentation layers (`experiment_3_startup_relocations_and_heap.heap_allocator_profiles`):
1. **In-process atomic `#[global_allocator]` wrapper (`CountingAlloc`):** Intercepts `GlobalAlloc::{alloc, dealloc, realloc}` with `Ordering::Relaxed` + `fetch_max` (`~3`–`5 ns` per call, `< 1%` runtime perturbation), isolating exact Rust-level post-`main` `alloc_calls`, `realloc_calls`, `total_bytes_allocated`, `peak_live_bytes`, and `end_live_bytes`.
2. **Whole-process binary instrumentation via `valgrind --tool=dhat`:** Intercepts `libc` `malloc`/`calloc`/`realloc`/`free` across *both* `std::rt::init` C/Rust startup and user code, additionally tracking **every memory load (`rb`) and store (`wb`) to every heap block** to detect write-only / zero-read wasted allocations!

| Metric | `CountingAlloc` (`-O0` / `-O2` / `-O3` / `-Oz`) | `Valgrind DHAT` (`-O0` / `-O3` / `-Oz`) | What the Difference Quantifies |
| :--- | ---: | ---: | :--- |
| Total allocation calls / blocks | `598` `alloc` + `302` `realloc` (`900` ops) | `921` blocks (`tbk`) | **`21` blocks** allocated by C/`std::rt::init` outside `main` window |
| Cumulative bytes allocated | `88,344 B` | `137,068 B` (`tb`) | `DHAT` counts full `realloc` copy-allocations + `std` startup buffers (`+48,724 B`) |
| Peak live heap (`t-gmax`) | **`88,344 B`** | **`88,896 B`** (`601` live blocks) | **`552 B`** of live `std` runtime heap (`thread_info` / `altstack` metadata) at peak |
| Unfreed live heap at exit (`t-end`) | **`0 B`** (`598` `dealloc` == `598` `alloc`) | **`548 B`** (`eb`) | Zero user leaks; `548 B` intentionally retained by `std` until `_exit` |
| Dynamic heap reads / writes (`rb` / `wb`) | *(Not observable in `GlobalAlloc`)* | `144,467 / 142,842` (`-O0`) $\rightarrow$ **`142,440 / 142,677` (`-O3`)** | `-O2`/`-O3` eliminate **`2,027 B`** of redundant heap reads (`BTreeMap`/slice temp loads) |
| **Zero-read wasted heap bytes (`rb == 0`)** | *(Not observable in `GlobalAlloc`)* | **`16,964 B`** (`16,384 B` `unread_scratch` + `580 B` init) | Exact detection of dead heap allocations written once (`memset`) and never read |
| Kernel Peak Resident Set (`VmHWM`) | `2,340 KiB` (`-O0`) / `2,204 KiB` (`-O2`) / `2,220 KiB` (`-Oz`) | — | Coarse `4 KiB`-paged RSS (`~25x` larger than `88.9 KiB` live heap due to shared `libc.so` pages) |

---

### 4. Static and Dynamic Stack-Usage Verification (`-Z emit-stack-sizes` Binary Law)

Basis: source + execution + derived

#### 4.1 Source Mechanics of `-Z emit-stack-sizes` in `rustc` and LLVM

Tracing `-Z emit-stack-sizes` through `rust-lang/rust` (`412be32a6a189d9a28922beee178bc0abee9d492`) and `rust-lang/llvm-project` (`08ec928a5bd1866f4008c8ad216166ca685fd380`) establishes the exact contract of ELF `.stack_sizes` metadata:
1. `compiler/rustc_session/src/options.rs:2611` defines `emit_stack_sizes: bool` (`UNTRACKED`, default `false`), which `compiler/rustc_codegen_llvm/src/back/write.rs:208, 279` and `owned_target_machine.rs:31, 58` pass into `PassWrapper.cpp:360, 437` (`Options.EmitStackSizeSection = EmitStackSizeSection`).
2. During machine-code emission, `AsmPrinter::emitStackSizeSection` (`llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp:1698-1722`) executes for each `MachineFunction`:
   ```cpp
   const MachineFrameInfo &FrameInfo = MF.getFrameInfo();
   // Don't emit functions with dynamic stack allocations.
   if (FrameInfo.hasVarSizedObjects())
     return;
   ...
   uint64_t StackSize = FrameInfo.getStackSize() + FrameInfo.getUnsafeStackSize();
   OutStreamer->emitSymbolValue(FunctionSymbol, TM.getProgramPointerSize());
   OutStreamer->emitULEB128IntValue(StackSize);
   ```
3. Each `.stack_sizes` section carries `SHF_LINK_ORDER` referencing its parent `.text` (or `.text.<sym>` under `-Z function-sections=yes`), so `ld.lld --gc-sections` discards `.stack_sizes` records for dead-stripped functions. Each surviving record is an unpadded binary pair `<uint64_le relocated_fn_vaddr, ULEB128 frame_bytes>`.

#### 4.2 Four Soundness Pitfalls and the Exact x86-64 Call-Graph Stack Equation

Inspection of `AsmPrinter.cpp:1709-1719` paired with our pure-Python ELF64 `.stack_sizes` + disassembly analyzer (`parse_elf64_stack_sizes_and_symbols` and `compute_call_graph_max_stack`, verified with `0` mismatches against `llvm-readelf --stack-sizes`) exposes **four soundness hazards** that any static stack-bound verifier must handle:

1. **Silent omission of dynamic `alloca` functions (`hasVarSizedObjects()`):** Line `1709` returns early without emitting any sentinel record when a function contains variable-sized stack objects (`alloca` or inline assembly dynamic stack adjustments).
2. **Uninstrumented prebuilt sysroot functions:** In a standard `std` executable (`experiment_4_stack_sizes_static_and_dynamic`), `.symtab` defines `651` `STT_FUNC` symbols at `-O3`, of which only `39` user-crate monomorphizations appear in `.stack_sizes`; **`606` prebuilt `libstd`/`libcore` functions are absent** unless `core`/`std` are compiled from source with `-Z emit-stack-sizes`. Consequently, a sound analyzer must verify that *every* `STT_FUNC` reachable from the root entrypoint appears in `.stack_sizes` and that no reachable block contains an unresolved indirect `call` or SCC recursion cycle.
3. **Exclusion of caller-pushed return addresses on `x86-64` (`+8 B` per call edge):** On `x86-64`, `MachineFrameInfo::getStackSize()` records `subq $N, %rsp` plus `8 B` per `pushq` callee-saved register, **excluding** the `8 B` return address pushed onto the stack by the caller's `callq` instruction (which is why a frame doing `pushq %rax` to realign `RSP % 16 == 0` reports `8 B` in `.stack_sizes`, consuming `8 + 8 = 16 B` per call).
4. **Exclusion of leaf-function System V ABI red-zone displacements (`0..128 B` below `%rsp`):** On `x86_64-unknown-linux-gnu` without `-C no-redzone=yes` (`compiler/rustc_session/src/options.rs:2390`, `compiler/rustc_codegen_llvm/src/declare.rs:78`), leaf functions address up to `128 B` at `[rsp - d]` ($1 \le d \le 128$) *without* decrementing `%rsp`, so `FrameInfo.getStackSize()` excludes those `d` bytes!

Therefore, for an acyclic direct call path $P = (f_0 \to f_1 \to \dots \to f_k)$ on `x86-64` (measured from `%rsp` immediately after `f_0` is entered, excluding `f_0`'s own incoming return address), the **exact worst-case stack consumption** is:
$$\text{MaxStack}(f_0) = \sum_{j=0}^{k} S_{\text{section}}(f_j) \;+\; 8 \cdot k \;+\; R_{\text{redzone}}(f_k)$$
where $S_{\text{section}}(f_j)$ is the ULEB128 value in `.stack_sizes`, $8 \cdot k$ accounts for the $k$ internal `callq` return-address pushes, and $R_{\text{redzone}}(f_k) = \max_{[{\tt rsp}-d] \in f_k} d \in [0, 128]$ is the leaf red-zone depth.

#### 4.3 Empirical Verification Against Runtime Stack-Painting Watermarks

Table 5 validates this exact equation across `-O0`, `-O1`, `-O2`, `-O3`, `-Os`, `-Oz`, and `-O3 -C no-redzone=yes` on `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), comparing static `.stack_sizes` values against live runtime canary painting (`0xA5` painted across `16 KiB` below `%rsp` on a pre-faulted `2 MiB` thread stack):

| Profile | `stack_slot_coloring` `.stack_sizes` / Painted (`B`) | `stack_leaf_redzone` `.stack_sizes` + RedZone (`B`) | `stack_async_poll` `.stack_sizes` + RedZone (`B`) | 4-Deep Chain Naive `.stack_sizes` Sum (`B`) | Exact Formula $\sum S + 8k + R_{\text{leaf}}$ (`B`) | Live Runtime Painted Chain Watermark (`B`) | Naive Error vs. Exact Formula Error |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| `O0_default_redzone` | **`1,608`** / `1,552` | `328 + 0 = 328` | `280 + 0 = 280` | `928` | `1,064` *(incl. cold `Range::next`)* | `992` | `-64 B` (naive) vs. **`+72 B` safe over-bound** |
| `O1_default_redzone` | **`568`** / `576` | `88 + 120 = 208` | `136 + 128 = 264` | `560` | **`560 + 24 + 120 = 704`** | **`704`** | **`-144 B` (`-20.5%` unsound)** vs. **`0 B` exact** |
| `O2_default_redzone` | **`568`** / `576` | `72 + 128 = 200` | `136 + 128 = 264` | `544` | **`544 + 24 + 128 = 696`** | **`696`** | **`-152 B` (`-21.8%` unsound)** vs. **`0 B` exact** |
| `O3_default_redzone` | **`568`** / `576` | **`72 + 128 = 200`** | `136 + 128 = 264` | **`544`** | **`544 + 24 + 128 = 696`** | **`696`** | **`-152 B` (`-21.8%` unsound)** vs. **`0 B` exact** |
| `O3_no_redzone` (`-C no-redzone=yes`) | `568` / `576` | **`200 + 0 = 200`** | `264 + 0 = 264` | **`672`** | **`672 + 24 + 0 = 696`** | **`696`** | `-24 B` (`callq` pushes only) vs. **`0 B` exact** |
| `Os_default_redzone` | `568` / `576` | `232 + 0 = 232` | `136 + 0 = 136` | `752` | `752 + 24 + 0 = 776` (`784` incl. entry `callq`) | `784` | `-32 B` vs. **`0 B` exact (incl. entry `callq`)** |
| `Oz_default_redzone` | **`392`** / `520` (`392+128`) | `72 + 0` (`rbp` leaf) | **`56`** | `592` | `592 + 24 + 128 = 744` | **`744`** | `-152 B` vs. **`0 B` exact** |

Notice three crystal-clear empirical proofs in Table 5:
1. **`O3_default_redzone` vs. `O3_no_redzone` proves the `128 B` red-zone shift:** Passing `-C no-redzone=yes` leaves total hardware stack usage completely unchanged (`696 B` painted watermark in both builds!), while shifting exactly `128 B` from unrecorded leaf red-zone accesses into `.stack_sizes` (`72 B` $\rightarrow$ `200 B` on `stack_leaf_redzone`; `136 B` $\rightarrow$ `264 B` on `stack_chain_leaf` and `stack_async_poll_entry`; naive sum `544 B` $\rightarrow$ `672 B`), leaving only the `3 × 8 = 24 B` `callq` return addresses outside `.stack_sizes`!
2. **Stack-slot coloring (`StackColoring` + MIR storage markers) compresses sequential local buffers by `-64.7%` to `-75.6%`:** In `stack_slot_coloring_sequential` (three sequential non-overlapping `[u8; 512]` scopes = `1,536 B` raw locals), `-O0` allocates disjoint slots (`1,608 B` frame), whereas `-O1`..`-Os` coalesce all three scopes into a single `512 B` slot (`568 B` frame), and `-Oz` further places `128 B` in the leaf red zone (`392 B` `.stack_sizes` + `128 B` red zone = `520 B` painted!).
3. **Why `-O0` static bound (`1,064 B`) exceeds painted watermark (`992 B`) by `+72 B`:** At `-O0`, `0..32` invokes uninlined `<Range<usize> as Iterator>::next` $\rightarrow$ `RangeIteratorImpl::spec_next` $\rightarrow$ `Step::forward_unchecked` $\rightarrow$ `u32::unchecked_add::precondition_check` (an untaken debug UB-check branch whose `72 B` leaf frame is statically reachable in the CFG but never entered dynamically on valid inputs—illustrating a sound conservative static upper bound!).

---

### 5. Binary Footprint Attribution Ladder, Debug/Unwind Overhead, and Energy Accounting

Basis: execution + source + derived

#### 5.1 11-Step Binary Footprint Attribution Ladder

File size (`stat().st_size`), memory-mapped `PT_LOAD` image size, `.text + .rodata`, unwind metadata, and DWARF `.debug_*` sections measure fundamentally different deployment costs (disk/network transfer vs. instruction cache pressure vs. per-process unshared RAM). Table 6 decomposes all 11 steps of `experiment_5_binary_footprint_ladder` (`rustc 1.102.0-nightly` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` + `ld.lld`):

| Step & Configuration | Total File (`Bytes`) | `.text` (`Bytes`) | `.rodata` (`Bytes`) | `.data.rel.ro` (`Bytes`) | Unwind Total (`.eh_frame` + `hdr` + `LSDA`) | Reloc Sections (`.rela` + `.relr`) | `.debug_*` Sections (`Bytes`) | Cumulative File $\Delta\%$ vs. Step `01` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `01_dev_O0_debug2` (`-O0 -C debuginfo=2`) | `5,197,080` | `306,707` | `32,084` | `11,560` | `50,964` (`29,528 + 6,908 + 14,528`) | `25,368` | `4,596,717` | `+0.00%` |
| `02_rel_O3_debug2` (`-O3 -C debuginfo=2`) | `4,993,464` | `255,347` | `22,492` | `9,312` | `40,444` (`22,272 + 4,572 + 13,600`) | `22,824` | `4,516,798` | `-3.92%` |
| **`03_rel_O3_debug2_zstd`** (`+ -Z debuginfo-compression=zstd`) | **`1,438,584`** | `255,347` | `22,492` | `9,312` | `40,444` | `22,824` | **`961,917`** (`-78.7%`) | **`-72.32%`** |
| `04_rel_O3_default` (`-O3`, no user debuginfo) | `4,639,008` | `255,347` | `22,492` | `9,312` | `40,444` | `22,824` | `4,162,554` *(prebuilt `std`)* | `-10.74%` |
| `05_rel_Oz_default` (`-Oz`, default `ThinLocal`) | `4,644,560` | `253,555` | `22,652` | `9,408` | `42,260` | `22,968` | `4,162,554` | `-10.63%` |
| `06_rel_Oz_fatlto` (`-Oz -C lto=fat -C codegen-units=1`) | `1,966,840` | `235,296` | `21,227` | `8,112` | **`25,124`** (`18,124 + 3,652 + 3,348`) | `14,904` | `1,572,284` | `-62.15%` |
| `07_rel_Oz_fatlto_abort` (`+ -C panic=abort`) | `1,954,504` | `233,136` | `20,987` | `8,088` | `24,124` (`17,556 + 3,524 + 3,044`) | `14,808` | `1,566,604` | `-62.39%` |
| `08_rel_Oz_fatlto_abort_gc_icf` (`+ --gc-sections --icf=all -z pack-relative-relocs`) | `1,939,568` | `231,856` | `20,987` | `8,088` | `23,516` (`17,084 + 3,388 + 3,044`) | **`1,632`** (`-89.0%`) | `1,566,604` | `-62.68%` |
| `09_rel_Oz_fatlto_abort_noloc_nofmt` (`+ -Z location-detail=none -Z fmt-debug=none`) | `1,939,056` | `231,856` | `20,675` | `7,896` | `23,516` | `1,624` | `1,566,604` | `-62.69%` |
| **`10_rel_Oz_stripped_final`** (`+ -C strip=symbols`) | **`295,512`** | **`231,856`** | **`20,675`** | **`7,896`** | **`23,516`** | **`1,624`** | **`0`** | **`-94.31%`** |
| **`11_nostd_abort_force_no_uwtable_stripped`** (`#![no_std] -C force-unwind-tables=no`) | **`4,712`** | **`242`** | **`0`** | `0` | **`92`** (`72 B` CRT stub) | `168` | **`0`** | **`-99.91%`** |

Critical attribution takeaways:
- **Prebuilt `libstd` debug sections dominate unstripped `release` file sizes (`4.16 MB` / `89.7%`):** In `04_rel_O3_default`, even with `-C debuginfo=0` on user code, the prebuilt `libstd` rlib linked from the rustup toolchain embeds `4,162,554 B` of DWARF debug info (`89.7%` of the `4.64 MB` file!). Never use raw unstripped file bytes to judge codegen bloat! Furthermore, when debuginfo must be retained for production crash symbolication, `-Z debuginfo-compression=zstd` (`SHF_COMPRESSED` `ELFCOMPRESS_ZSTD`, `compiler/rustc_codegen_llvm/src/back/write.rs:230-238`) shrinks `.debug_*` by **`-78.70%`** (`4.52 MB` $\rightarrow$ `0.96 MB`).
- **Fat LTO slashes `.gcc_except_table` LSDA by `-75.38%` (`13,600 B` $\rightarrow$ `3,348 B`):** Internalizing and dead-stripping unused `std` formatting/backtrace landing pads under `-C lto=fat -C codegen-units=1` removes three-quarters of LSDA exception-dispatch tables, while `--icf=all` (Identical Code Folding in `ld.lld`) merges binary-identical read-only functions beyond LLVM's per-module `MergeFunctions` (`-1,280 B` `.text`, `-608 B` `.eh_frame`), and `-z pack-relative-relocs` cuts dynamic relocations from `14,808 B` to `1,632 B` (`-88.98%`).

#### 5.2 Hardware Energy Accounting (`RAPL`), `EDP`, and Cloud Virtualization Boundaries

Execution time $T$ and dynamic instruction count `Ir` are imperfect proxies for energy $E$ (Joules) because wide 256/512-bit SIMD units, DRAM cache misses, and unthrottled spin loops draw higher instantaneous package and DRAM power $P(t)$ despite retiring fewer instructions or running in less wall time:
- **Primary energy & efficiency metrics:**
  1. **Energy per operation ($J / \text{op}$):** Measured on bare-metal Intel/AMD Linux hosts via the kernel `power` PMU (`/sys/bus/event_source/devices/power`, `pmu_type = 11`, `format/event = config:0-7`: `energy-pkg` `config = 0x01` reading `MSR_PKG_ENERGY_STATUS` `0x611`, `energy-cores` `0x02`, `energy-ram` `0x03` reading `MSR_DRAM_ENERGY_STATUS` `0x619`, `energy-psys` `0x05`, scaled by unit $2^{-32}\text{ J} \approx 2.3283 \times 10^{-10}\text{ J}$ or `/sys/class/powercap/intel-rapl:0/energy_uj`). Note that RAPL MSRs are **socket-scoped** (not per-thread!), so bare-metal energy benchmarks must run on an otherwise idle socket pinned via `numactl --cpunodebind=0 --membind=0` over windows $\ge 200\text{ ms}$ (well above the `~1 ms` RAPL MSR update period) and subtract measured idle background socket power $P_{\text{idle}} \cdot T$.
  2. **Energy-Delay Product ($\text{EDP} = E \cdot T = \bar{P} \cdot T^2$, in $\text{J}\cdot\text{s}$) and $\text{ED}^2\text{P} = E \cdot T^2$:** Under constant-power scaling ($\bar{P}_{\text{cand}} \approx \bar{P}_{\text{base}}$), a `9.0x` latency reduction (such as `O3_x86_64` $\rightarrow$ `O3_x86_64_v3` on `f32_dot_fma`) reduces energy $E$ by `~8–9x` and $\text{EDP}$ by **`~75–81x`** even if AVX2 raises core dynamic capacitance by `10–15%`. Conversely, if aggressive `-O3` loop unrolling speeds up a memory-bound loop by `2%` while raising DRAM/L2 traffic and package power by `8%`, $E$ worsens (`+5.8%`) and $\text{EDP}$ regresses (`+3.7%`).
- **Live KVM virtualization boundary (`pmu_and_rapl_host_probe.rapl_power_pmu`):** On our Ice Lake-SP KVM guest, `/sys/bus/event_source/devices/power` registers `pmu_type = 11` with `format/event = config:0-7`, but `events/` and `/sys/class/powercap/` are empty and `perf_event_open(type=11, config=0x01..0x03)` returns **`errno = 13` (`EACCES`)** (enforced both by hypervisor MSR filtering and Linux's `CVE-2020-8694` PLATYPUS side-channel mitigation requiring `CAP_PERFMON` / `CAP_SYS_ADMIN`).

---

### 6. 3D Pareto Frontier (`Compile Time` $\times$ `Code Size` $\times$ `Speed`) and Hierarchical Statistical Benchmarking

Basis: execution + derived

#### 6.1 Dominated-Configuration Pruning and Exact 3D Pareto Hypervolume

Compiler configurations trade off three competing minimization objectives: **clean compile wall time** $C$ (`seconds`), **code footprint** $S$ (`.text + .rodata` bytes), and **runtime execution latency** $T$ (seconds or suite geometric-mean ratio). Configuration $b$ **strictly Pareto-dominates** $a$ ($b \prec a$) iff $C_b \le C_a$, $S_b \le S_a$, and $T_b \le T_a$ with at least one strict inequality. To compare entire compiler backends or pass pipelines via a single scalar monotonic indicator, normalize $(C, S, T)$ linearly onto $[0, 1]^3$ and compute the **exact 3D dominated hypervolume** $HV(\mathcal{P}, \mathbf{r})$ bounded by nadir reference point $\mathbf{r} = (1, 1, 1)$ via $z$-slice 2D skyline integration (`exact_3d_hypervolume_min`), together with each frontier point $p$'s **exclusive hypervolume contribution** $\Delta HV(p) = HV(\mathcal{P}, \mathbf{r}) - HV(\mathcal{P} \setminus \{p\}, \mathbf{r})$.

Applying 3D Pareto analysis (`experiment_6_pareto_3d_and_shuffle_tost.pareto_3d`) to both the 14-configuration `W-Core` matrix from `rustc-benchmark-methodology-and-speed-size-baselines` ($HV = 0.550014$) and our 8-configuration microarchitecture matrix ($HV = 0.253872$) yields sharp structural pruning:

| Dataset | Non-Dominated 3D Pareto Frontier Configurations (with Top Exclusive $\Delta HV$) | Strictly 3D-Dominated Configurations (`Dominators` that beat them on *all 3* of Compile Time, Code Size, and Speed!) |
| :--- | :--- | :--- |
| **`W-Core` 14-Profile Matrix** (`rustc 1.99.1`, $HV = 0.550014$) | `C12_Oz` (`ΔHV = 0.001335`), `C12_Oz_fat_lto` (`0.001056`), `C06_O3_thin_lto` (`0.000961`), `C05_O3_thinlocal` (`0.000915`), `C11_Os_fat_lto` (`0.000689`), `C09_O3_thin_lto_pgo` (`0.000473`), `C01_O0` (`0.000099`), `C11_Os` (`0.000054`), `C10_O3_fat_lto_pgo` (`0.000029`), `C02_O1` (`0.000003`) | **`C03_O2`** (`0.792 s, 2.319 MB, 1.357x` — strictly beaten on all 3 axes by `C02_O1` *and* `C11_Os`!), **`C04_O3_no_lto`** (`0.753 s, 2.327 MB, 1.574x` — beaten by `C02_O1` and `C12_Oz`!), **`C07_O3_fat_lto`** (`23.18 s, 2.183 MB, 1.283x` — beaten by `C11_Os_fat_lto` and `C12_Oz_fat_lto`!), **`C08_O3_no_lto_pgo`** (beaten by `C12_Oz`!) |
| **Live 8-Profile Microarch Suite** (`1.102.0-nightly`, `CGU=1`, $HV = 0.253872$) | `Oz_x86_64` (`ΔHV = 0.028428`, smallest `291.56 KiB`), `O0_x86_64` (`0.014549`, fastest build `0.129 s`), `O2_x86_64` (`0.001226`), `O3_x86_64_v4_avx512` (`0.000194`, fastest runtime `0.6935 ms`), `Os_x86_64` (`0.000190`) | **`O1_x86_64`** (beaten by `Os_x86_64` on compile time, size, and speed), **`O3_x86_64`** (beaten by `O2_x86_64` within `1%` layout noise), **`O3_x86_64_v3_avx2`** (marginally dominated by `O3_x86_64_v4_avx512`: `294.53` vs. `295.46 KiB`, `0.6935` vs. `0.6949 ms`) |

Notice why **`C04_O3_no_lto`** (`-O3 -C codegen-units=16 -C lto=off`) is strictly 3D-dominated: splitting a crate into 16 CGUs without `ThinLocal` cross-CGU importing pays `-O3`'s per-module compile-time and code-size cost while losing intra-crate inlining (`+57.35%` slower than `C05_O3_thinlocal`).

#### 6.2 Hierarchical Layout-Randomized Statistical Protocol (`--shuffle-sections` + Bootstrap + TOST)

In `rust-lang/rustc-perf` (`15d95905429e577d5a710b17c49e04b4451c263b`, `collector/src/runtime/mod.rs:30`, `DEFAULT_RUNTIME_ITERATIONS = 5`), comparing two single-link deterministic binaries treats $R$ invocations of *one* binary layout as independent samples of compiler code quality. In reality, runtime observations $Y_{a,k,r}$ for compiler arm $a \in \{\text{base}, \text{cand}\}$, linker layout seed $k \in \{1..K\}$, and process invocation $r \in \{1..R\}$ obey a **two-level hierarchical random-effects model**:
$$Y_{a,k,r} = \mu_a + \eta_{a,k} + \varepsilon_{a,k,r}, \qquad \eta_{a,k} \sim \mathcal{D}_{\text{layout}}(0, \sigma^2_{\text{seed}}), \quad \varepsilon_{a,k,r} \sim \mathcal{D}_{\text{run}}(0, \sigma^2_{\text{run}})$$
Increasing invocations $R$ shrinks only $\sigma^2_{\text{run}} / R$ while leaving the layout variance $\sigma^2_{\text{seed}} / K$ untouched! Whenever the intraclass correlation $\text{ICC} = \sigma^2_{\text{seed}} / (\sigma^2_{\text{seed}} + \sigma^2_{\text{run}}) > 0$, a naive single-seed Mann-Whitney U test ($K = 1, R \ge 12$) converges to **100% false-positive probability** as $R \to \infty$ whenever two deterministic builds happen to land on different 32-byte DSB / 64-byte L1I cache alignments.

To eliminate layout confounding and test *equivalence* (not merely failure to reject difference), the rigorous comparison protocol implemented in `probe_generated_code_metrics.py` (`hierarchical_comparison`) executes five steps:
1. **Multi-seed linker section shuffling:** Compile both baseline and candidate with `-Z function-sections=yes -C link-arg=-fuse-ld=lld -C link-arg=-Wl,--shuffle-sections=*=<seed>` across $K \ge 10$ seeds (`16..32` recommended for high-ICC kernels) and $R \ge 12$ pinned process invocations per seed.
2. **Seed-level aggregation and Hodges-Lehmann shift:** Compute each seed's median $\tilde{Y}_{a,k} = \text{median}_r(Y_{a,k,r})$, the inter-seed median ratio $\hat{\rho} = \text{median}_k(\tilde{Y}_{\text{cand},k}) / \text{median}_k(\tilde{Y}_{\text{base},k})$, and the non-parametric **Hodges-Lehmann shift estimator** $\hat{\Delta}_{\text{HL}} = \text{median}_{k, k'}(\tilde{Y}_{\text{cand},k'} - \tilde{Y}_{\text{base},k})$.
3. **Two-level hierarchical bootstrap ($B \ge 4,000$ resamples):** In each bootstrap replicate $b$, sample $K$ seeds *with replacement* from each arm and $R$ invocations *with replacement* within each sampled seed, forming the empirical distribution $\{\hat{\rho}^{*(b)}\}_{b=1}^B$, the 90% confidence interval $[L_{90}, U_{90}]$ (for $\alpha = 0.05$ TOST), and the 95% confidence interval $[L_{95}, U_{95}]$.
4. **Two One-Sided Tests (`TOST`) for equivalence and non-inferiority:** Given equivalence margin $\delta$ (e.g., $\delta = 0.05$ for $\pm 5\%$ parity):
   - **Equivalence** ($H_0: \rho \le 1 - \delta \text{ or } \rho \ge 1 + \delta$ vs. $H_1: 1 - \delta < \rho < 1 + \delta$) holds at level $\alpha = 0.05$ iff $[L_{90}, U_{90}] \subseteq [1 - \delta, 1 + \delta]$ ($p_{\text{TOST}} = \max(p_{\text{low}}, p_{\text{high}}) < 0.05$).
   - **Non-inferiority** ($H_0: \rho \ge 1 + \delta$ vs. $H_1: \rho < 1 + \delta$) holds at one-sided $\alpha = 0.025$ iff $U_{95} \le 1 + \delta$.
5. **Multi-workload multiplicity control:** Across $M$ kernels/workloads, adjust two-sided hierarchical $p$-values via **Holm-Bonferroni** ($p_{(i)}^{\text{Holm}} = \max_{j \le i} \min(1, (M - j + 1) p_{(j)})$, controlling the Family-Wise Error Rate $\text{FWER} \le \alpha$ for release gates) and **Benjamini-Hochberg** ($q_{(i)}^{\text{BH}} = \min_{j \ge i} \min(1, \frac{M}{j} p_{(j)})$, controlling the False Discovery Rate $\text{FDR}$ for diagnostic optimization triage).

#### 6.3 Live Empirical Proof: 240-Run A/A Null Control vs. A/B Target-CPU Study (`rustc 1.99.1`)

Table 7 reports the live $K = 10$ seed $\times$ $R = 12$ invocation (`120` runs/arm) experiment on `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67` + `ld.lld`), contrasting:
- **A/A Null Study:** Identical `-C opt-level=3 -C target-cpu=x86-64` flags with disjoint linker seeds (`1..10` vs. `101..110`), where the true codegen difference is **identically zero**;
- **A/B Target-CPU Study:** `-C target-cpu=x86-64` vs. `-C target-cpu=x86-64-v3` across seeds `1..10`:

| Study & Metric | Naive Single-Seed MWU False/Raw Reject Rate (`p < 0.01` over `100` Seed Pairs) | Max Pairwise Seed Shift (`%`) | Hierarchical Median Ratio $\hat{\rho}$ (Hodges-Lehmann $\Delta\%$) | Hierarchical 90% Bootstrap CI (`TOST` $\pm 5\%$) | `TOST` $\pm 5\%$ Equiv / Non-Inf? | Holm-Bonferroni $p_{\text{adj}}$ / BH $q$ |
| :--- | ---: | ---: | ---: | ---: | :---: | ---: |
| **A/A Null:** `total_suite_ms` | `4.0%` | `23.58%` | `0.9985x` (`+0.21%`) | `[0.9559, 1.0734]` | No / No (`p=0.131`) | *(Suite aggregate)* |
| **A/A Null:** `f32_dot_fma` | **`35.0%` *(false alarm!)*** | `11.38%` | `1.0185x` (`+2.71%`) | `[0.9990, 1.0558]` | No / No (`p=0.077`) | **`0.630` / `0.630`** *(0 false pos)* |
| **A/A Null:** `u32_autovec_mac` | **`27.0%` *(false alarm!)*** | `47.11%` | `0.9971x` (`-0.16%`) | `[0.9767, 1.2343]` | No / No (`p=0.143`) | **`1.000` / `0.804`** *(0 false pos)* |
| **A/A Null:** `reg_pressure_spills` | **`32.0%` *(false alarm!)*** | `31.91%` | `1.0051x` (`+1.08%`) | `[0.9919, 1.2092]` | No / No (`p=0.170`) | **`1.000` / `0.671`** *(0 false pos)* |
| **A/A Null:** `bounds_and_iter` | **`28.0%` *(false alarm!)*** | `8.37%` | **`1.0003x` (`+0.10%`)** | **`[0.9908, 1.0273]`** | **Yes / Yes (`p=0.008`)** | **`1.000` / `0.804`** *(0 false pos)* |
| **A/A Null:** `dyn_dispatch_and_memops` | **`63.0%` *(false alarm!)*** | **`69.16%`** | `1.1199x` (`+8.83%`) | `[0.9315, 1.2431]` | No / No (`p=0.608`) | **`1.000` / `0.671`** *(0 false pos)* |
| **A/B (`v3` vs `v1`):** `total_suite_ms` | `100.0%` | `50.13%` | **`0.6567x` (`-33.89%`)** | **`[0.6244, 0.7136]`** | No / **Yes (`p<0.001`)** | *(Suite speedup)* |
| **A/B (`v3` vs `v1`):** `f32_dot_fma` | `100.0%` | `89.62%` | **`0.1085x` (`-88.18%`)** | **`[0.1067, 0.1148]`** | No / **Yes (`p<0.001`)** | **`0.0000` / `0.0000`** *(True AVX2+FMA win)* |
| **A/B (`v3` vs `v1`):** `u32_autovec_mac` | `33.0%` | `70.84%` | **`0.4242x` (`-57.65%`)** | **`[0.3022, 0.5500]`** | No / **Yes (`p<0.001`)** | **`0.0030` / `0.0017`** *(True AVX2 win)* |
| **A/B (`v3` vs `v1`):** `reg_pressure_spills` | `64.0%` | `48.95%` | **`1.0683x` (`+6.96%`)** | **`[1.0473, 1.1050]`** | No / **No (`p=0.923`)** | **`0.0000` / `0.0000`** *(True spill regression!)* |
| **A/B (`v3` vs `v1`):** `bounds_and_iter` | `1.0%` | `3.24%` | **`0.9983x` (`-0.19%`)** | **`[0.9872, 1.0064]`** | **Yes / Yes (`p<0.001`)** | `0.9140` / `0.6295` *(Proved equivalent)* |
| **A/B (`v3` vs `v1`):** `dyn_dispatch_and_memops` | `64.0%` | `71.85%` | `1.1779x` (`+10.49%`) | `[0.8517, 1.2457]` | No / No (`p=0.681`) | `0.9140` / `0.5713` *(Layout noise only)* |

Table 7 demonstrates why both components of the hierarchical TOST protocol are indispensable:
1. **Elimination of `27%`–`63%` single-seed false alarms:** Under identical `-O3` codegen, comparing two single-seed binaries with Mann-Whitney U at $\alpha = 0.01$ falsely declares a statistically significant difference on **`63.0%`** of seed pairs in `dyn_dispatch_and_memops` (`69.16%` max shift) and **`27.0%`–`35.0%`** across the other four kernels! The two-level hierarchical bootstrap + Holm-Bonferroni / BH procedure produces **zero false positives across all 5 kernels** (`p_adj >= 0.630`).
2. **Distinguishing proved equivalence (`TOST` pass) from under-powered layout noise (`TOST` withhold):** On `bounds_and_iter`, $K = 10$ seeds already prove strict $\pm 5\%$ equivalence (`90% CI = [0.9908, 1.0273]`, $p_{\text{TOST}} = 0.00775$ on A/A; `[0.9872, 1.0064]`, $p_{\text{TOST}} < 0.0001$ on A/B). On high-layout-variance `dyn_dispatch_and_memops`, `TOST` rightly *refuses* to certify $\pm 5\%$ equivalence at $K = 10$ (`90% CI = [0.9315, 1.2431]`), signaling that either $K$ must be increased ($K \ge 32$) or the parity margin widened to $\pm 2 \sigma_{\text{layout}}$.
3. **Simultaneous high power on real regressions and speedups:** In the A/B study, the exact same test cleanly certifies both the `-88.18%` FMA/AVX2 speedup (`f32_dot_fma`, `p_adj < 0.0001`), the `-57.65%` integer AVX2 speedup (`u32_autovec_mac`, `p_adj = 0.0030`), *and* the genuine **`+6.96%` (`1.0683x`)** `reg_pressure_spills` slowdown (`p_adj < 0.0001`) caused by the extra `8` stack spill operations (`71` $\rightarrow$ `79`) observed statically in Table 2!

---

## Boundaries

1. **Hardware PMU (`PERF_TYPE_HARDWARE` / `TMA` Level 1) and Intel RAPL MSRs on KVM guests — `unsupported` in virtualized guest environment:** As verified by syscall `298` probes in `support/generated_code_metrics_specimen.json`, the cloud KVM hypervisor masks hardware PMU counters (`errno = 2`, `ENOENT`) and blocks unprivileged RAPL power counters (`errno = 13`, `EACCES`, empty `/sys/class/powercap`). Exact `IPC`, `TOPDOWN.SLOTS`, and Joule measurements require bare-metal Linux hosts with `perf_event_paranoid <= 1` (or `CAP_PERFMON`).
2. **Valgrind `3.25.1` (`Cachegrind` / `DHAT`) on `x86-64-v4` (`AVX-512` EVEX) — `unsupported` by tool:** Valgrind `3.25.1`'s VEX `amd64->IR` translator terminates with `SIGILL` (`returncode = -4`) on EVEX-encoded AVX-512 instructions (`O3_x86_64_v4_avx512`), even when the underlying Ice Lake-SP CPU executes them natively (`0.6935 ms`).
3. **Static `.stack_sizes` bounds in the presence of recursion, indirect calls, dynamic `alloca`, or uninstrumented `libstd` — `known not to apply` without whole-graph closure:** Because `AsmPrinter::emitStackSizeSection` (`AsmPrinter.cpp:1709`) silently omits functions where `FrameInfo.hasVarSizedObjects()` is true and prebuilt rustup `libstd` rlibs lack `.stack_sizes` (`606 / 651` `STT_FUNC` symbols missing in a default `std` build), static call-graph stack bounds are sound **only** over call subgraphs where every reachable `STT_FUNC` is verified present in `.stack_sizes` (requiring `#![no_std]` or `-Z build-std` with `-Z emit-stack-sizes`), indirect call targets are resolved or bounded, and recursion cycles are absent.
4. **Post-link binary optimizers (`llvm-bolt` / Propeller) and non-`x86-64` dynamic `Cachegrind`/`RELR` measurements — `not examined` in live probe:** While `rustc-benchmark-methodology-and-speed-size-baselines` covers `aarch64` and `i686` speed/section baselines, the live `Cachegrind`, `DHAT`, `SHT_RELR`, and `.stack_sizes` runtime-painting probes in `support/probe_generated_code_metrics.py` were executed on `x86_64-unknown-linux-gnu`; post-link `BOLT` layout optimization on top of `FatLTO+PGO` was not examined.

---

## Evidence

### Primary Upstream Sources Examined

- **`rust-lang/rust` (`412be32a6a189d9a28922beee178bc0abee9d492`):**
  - `compiler/rustc_session/src/options.rs:2390, 2611, 2742, 2910`: `-C no-redzone`, `-Z emit-stack-sizes`, `-Z location-detail`, and `-Z randomize-layout` option definitions.
  - `compiler/rustc_codegen_llvm/src/back/write.rs:208, 230-238, 279`, `compiler/rustc_codegen_llvm/src/back/owned_target_machine.rs:31, 58`, `compiler/rustc_codegen_llvm/src/declare.rs:78`, and `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:360, 437`: plumbing of `EmitStackSizeSection`, `DebugInfoCompression::Zstd`, and `noredzone` into LLVM `TargetMachine`.
  - `compiler/rustc_mir_transform/src/lib.rs:668, 754-771` and `compiler/rustc_mir_transform/src/ssa_range_prop.rs:1-221`: `coroutine::StateTransform` phase placement, `GVN` $\rightarrow$ `SsaRangePropagation` $\rightarrow$ `DataflowConstProp` $\rightarrow$ `SimplifyConstCondition` ordering, singleton `WrappingRange` equality constraint (`lines 101-114`), and `is_bool()` `SwitchInt` `otherwise` restriction (`lines 204-218`).
- **`rust-lang/llvm-project` (`08ec928a5bd1866f4008c8ad216166ca685fd380`):**
  - `llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp:1698-1722`: `AsmPrinter::emitStackSizeSection`, `FrameInfo.hasVarSizedObjects()` early return (`line 1709`), and `<pointer, ULEB128>` emission (`lines 1718-1719`).
- **`rust-lang/rustc-perf` (`15d95905429e577d5a710b17c49e04b4451c263b`):**
  - `collector/src/artifact_stats.rs:1-75` and `collector/src/runtime/mod.rs:1-70`: ELF/`.rlib` section/symbol size extraction (`ArtifactStats`) and `DEFAULT_RUNTIME_ITERATIONS = 5` single-binary runtime harness.
- **Executed Toolchains and Subject Crate (`2026-11-21`):**
  - `rustc 1.102.0-nightly` (`rust-lang/rust` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`), `rustc 1.99.1` (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `google/zerocopy` (`0d0e0196aa4c95f7ccc1292a49b07a33011be371`).

### Preserved Package Artifacts (`support/`)

1. `support/probe_generated_code_metrics.py`: Standalone, linear-`O(N)` Python 3.10+ measurement suite executing entirely inside `tempfile.TemporaryDirectory` across `rustc +nightly` and `rustc +1.99.1`. Contains the syscall `298` `perf_event_open` + RAPL sysfs prober, pure-Python ELF64 `.stack_sizes` ULEB128 + `.symtab` parser, static call-graph + leaf red-zone stack calculator, Intel-syntax `llvm-objdump` spill/SIMD/call-site analyzer, kernel-isolating `Cachegrind` and `DHAT` parsers, exact 3D Pareto hypervolume engine, and two-level hierarchical bootstrap + `TOST` + Holm-Bonferroni / Benjamini-Hochberg statistical engine.
2. `support/generated_code_metrics_specimen.json` (`153,312 bytes`, SHA-256 `7a888510907cbcfe4017d32cd44863c193c6670b594e27f74454f83ac2c43e47`, acquired `2026-11-21` in `52.72 s`): Complete machine-readable empirical dataset backing Tables 1–7.

---

## Revalidation

1. **Instant structural and invariant audit of preserved specimen (`< 1 second`):**
   ```bash
   python3 -c '
   import json
   d = json.load(open("reports/rustc-generated-code-performance-footprint-microarch-and-rigorous-benchmarking/support/generated_code_metrics_specimen.json"))
   s_o3 = d["experiment_4_stack_sizes_static_and_dynamic"]["O3_default_redzone"]
   assert s_o3["call_graph_chain_d1_bound"]["max_call_tree_bytes_excl_entry_retaddr"] == s_o3["runtime_painted_watermarks"]["runtime_painted_chain_d1_bytes"] == 696
   aa = d["experiment_6_pareto_3d_and_shuffle_tost"]["hierarchical_shuffle_sections_study"]["aa_null_disjoint_seeds_O3_vs_O3"]
   assert min(aa["holm_bonferroni_p"].values()) >= 0.05
   print("Specimen invariants verified OK; keys:", list(d.keys()))
   '
   ```
2. **Fast 5-second smoke probe of PMU/RAPL capabilities and MIR `SsaRangePropagation` vs. LLVM `-O2` `Assert` survival on a newer toolchain:**
   ```bash
   python3 -B reports/rustc-generated-code-performance-footprint-microarch-and-rigorous-benchmarking/support/probe_generated_code_metrics.py --quick
   ```
3. **Full 55-second regeneration of all 6 empirical experiments (`Cachegrind`, `DHAT`, `.stack_sizes`, 11-step footprint ladder, and 240-run `--shuffle-sections` TOST study):**
   ```bash
   python3 -B reports/rustc-generated-code-performance-footprint-microarch-and-rigorous-benchmarking/support/probe_generated_code_metrics.py --output /tmp/revalidated_metrics.json
   ```
   A passing run establishes whether the target toolchain and host preserve coroutine size compression, SIMD/spill codegen ratios, `SHT_RELR` relocation packing, exact `.stack_sizes` + `callq` + red-zone stack accounting, and hierarchical TOST statistical parity.
