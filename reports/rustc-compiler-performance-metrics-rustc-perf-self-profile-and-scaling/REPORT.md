# Compiler Performance Metrics, `rustc-perf` Architecture, `measureme` Self-Profiling, Parallel Scaling, and Verification-Tax Accounting

## Summary

Comparing compile-time throughput, memory footprint, incremental caching efficiency, and formal verification overhead across `rustc` revisions or between an unverified `rustc` and a certifying/verified drop-in replacement requires exact metric definitions grounded in compiler instrumentation and operating-system accounting:

1. **`rustc-perf` suite, interposition protocol, and summary-statistic asymmetry (`rust-lang/rustc-perf@15d95905429e577d5a710b17c49e04b4451c263b`):** Upstream `rustc-perf` evaluates **`69` compile-time benchmark directories** (`50` library, `19` binary) partitioned into **`21` `Primary`** real-world crates, **`39` `Secondary`** synthetic stress/next-solver/Polonius benchmarks, and **`9` `Stable`** long-horizon release-tracking crates across **`6` `Profile` variants** (`Check`, `Debug`, `Doc`, `DocJson`, `Opt`, `Clippy`—with `LlvmIr` migrated out of `Profile` into the 15-tool `Profiler` enum) and **`4` `Scenario` variants** (`Full`, `IncrFull`, `IncrUnchanged`, `IncrPatched`). `rustc-fake` interposes between Cargo and `rustc` in two phases (`--skip-this-rustc` for unmeasured dependency preparation vs. `--wrap-rustc-with <PerfTool>` with `EXPECT_ONLY_WRAPPED_RUSTC=1` for the target leaf crate), recording **`28` typed `Metric` keys** (`14` execution/PMU/OS counters + `14` `size:*` artifact/IR/doc byte metrics). Crucially, `site/src/comparison.rs` and `site/frontend/src/pages/compare/data.ts` compute PR headline means as the **filtered arithmetic mean of percentage changes** $\frac{1}{|S|} \sum_{i \in S} \frac{B_i - A_i}{A_i}$ restricted to cases exceeding a 30-commit historical interquartile fence $Q_3 + 3.0(Q_3 - Q_1)$ (default `0.2%`), which is asymmetric under $A \leftrightarrow B$ inversion and subject to threshold-selection bias; cross-compiler non-inferiority gates must instead pair `rustc-perf` per-case noise fences with the **unfiltered suite geometric mean of ratios** $\exp\!\left(\frac{1}{N}\sum_{i=1}^N \ln(B_i / A_i)\right)$.
2. **Deterministic instruction and cache accounting (`perf_event_open` syscall `298` vs. `valgrind --tool=cachegrind`):** On `x86_64` Linux with `/proc/sys/kernel/perf_event_paranoid = 2`, setting `exclude_kernel = 1` and `exclude_hv = 1` in `perf_event_attr` satisfies unprivileged kernel admission without `CAP_PERFMON`: all **7 `PERF_TYPE_SOFTWARE` counters** (`task-clock:u`, `cpu-clock:u`, `page-faults:u`, `minor-faults:u`, `major-faults:u`, `context-switches:u`, `cpu-migrations:u`) succeed (`fd >= 0`), whereas on virtualized cloud guests that omit architectural vPMU exposure, `PERF_TYPE_HARDWARE` counters (`instructions:u`, `cycles:u`, `branch-misses:u`, `cache-misses:u`) return `ENOENT` (`errno = 2`, distinct from privilege denial `EACCES` `errno = 13`). On such hosts, `valgrind --tool=cachegrind --cache-sim=yes --branch-sim=yes` with `MALLOC_CONF="dirty_decay_ms:0,muzzy_decay_ms:0"` and ASLR disabled (`setarch x86_64 -R`) simulates all 13 instruction/cache/branch events (`Ir`, `I1mr`, `ILmr`, `Dr`, `D1mr`, `DLmr`, `Dw`, `D1mw`, `DLmw`, `Bc`, `Bcm`, `Bi`, `Bim`) and composite cycle estimate $\text{CEst} = \text{Ir} + 10\,\text{Bm} + 10\,\text{L1m} + 100\,\text{LLm}$, reducing run-to-run coefficient of variation from **`3.51%`–`33.05%` (wall-clock)** down to **`0.0375%`–`0.0834%` (multi-CGU `Ir`)** and **`0.0034%` (`34.4 ppm`, single-CGU `-C codegen-units=1` `Ir`)** at a `234x`–`359x` wall-time simulation cost (`~15x`–`25x` with `--cache-sim=no --branch-sim=no`).
3. **Internal phase attribution, `measureme` v9 `.mm_profdata` binary wire format, and fast `-O0` backends (`TPDE`, `Cranelift`, `FastISel`):** `rustc` exposes coarse pass timings via `-Z time-passes -Z time-passes-format=json` (`stderr` lines `time: {"pass":"...","time":<sec>,"rss_start":<bytes>,"rss_end":<bytes>}`) and fine-grained query/LLVM/incremental traces via `-Z self-profile=<dir>`, which writes a single paged `measureme 12.0.3` (`CURRENT_FILE_FORMAT_VERSION = 9`) `.mm_profdata` binary container (`MMPD` header + 5-byte-framed `Events`, `StringData`, and `StringIndex` pages; 32-byte `RawEvent` records with 48-bit timestamps/integers; `0xFE`-prefixed UTF-8 substring DAGs; and bulk post-session `DepNodeIndex -> Addr` virtual string mappings). Live decoding across all four `Scenario`s shows `IncrUnchanged` cutting wall time by **`44.4%` (`98.86 ms` $\rightarrow$ `54.95 ms`)** on `rustc 1.99.1` by skipping all `5,431` `LLVM Pass` events and satisfying `23,574` query cache hits + `864` `IncrementalLoadResult` reads. Upstream `rust-lang/rust@412be32a6a189d9a28922beee178bc0abee9d492` also integrates `src/tpde` (`rust-lang/tpde@050927ee81dc11a9e599fa2524ff0eef16daf51a`) behind `-Z llvm-tpde={try,only}`, intercepting `LLVMRustWriteOutputFile` via `PassPluginLibraryInfo::PreCodeGenCallback` to compile `x86_64`/`aarch64` ELF modules in a single pass (`10x`–`20x` faster than LLVM `-O0`) with per-CGU fallback to LLVM under `try`.
4. **Cargo pipelined critical-path latency (`time-to-.rmeta`) and parallel scaling:** Single-crate `wall-time` overstates multi-crate workspace latency because `rustc_metadata::fs::encode_and_write_metadata` emits `.rmeta` and fires `--json=artifacts` (`{"$message_type":"artifact","emit":"metadata"}`) before LLVM optimization and object emission begin. Across a 4-crate dependency chain (`stage_a -> stage_b -> stage_c -> stage_d`) at `--release -j 4`, each crate emits `.rmeta` at **`16.8%`–`19.4%`** of its total compilation time (`41.05`–`49.95 ms` vs. `241.31`–`257.23 ms`), yielding a **`2.173x` (`rustc 1.99.1`) / `2.164x` (`rustc 1.102.0-nightly`)** end-to-end pipelining speedup (`451.19 ms` measured DAG wall time vs. `980.34 ms` sequential sum). Within a single crate, `-C codegen-units=16` accelerates `-O3 -C lto=off` codegen by **`2.675x`–`2.696x`** (`+28.1%`–`+28.5%` peak RSS), while `-Z threads=8` reaches **`1.297x`** check-mode speedup on `1.102.0-nightly` (`+42.9%` RSS) coordinated through `rustc_data_structures::jobserver::Proxy`.
5. **Memory footprint, `DHAT` heap churn, pathological scaling, and verification-tax taxonomy:** Isolated `wait4(2)` `ru_maxrss` and `valgrind --tool=dhat` (`heap` and `copy` modes) show that moving from `Check` (`--emit=metadata`) to `Opt` (`-C opt-level=2`) increases total dynamic heap allocations **`2.75x`–`2.83x`** (`23.83 MB` $\rightarrow$ `65.61 MB` on `1.99.1`; `22.24 MB` $\rightarrow$ `63.02 MB` on `1.102.0-nightly`) and triples the heap churn ratio `Total / At-t-gmax` from **`1.36x`–`1.40x` to `3.00x`–`3.41x`** (`llvm::ScheduleDAGSDNodes::BuildSchedUnits` + `trait_impls_of_provider`). Controlled Cachegrind sweeps isolate marginal instruction scaling exponents $\alpha$ ($\Delta\text{Ir}(N) \propto N^\alpha$) across five pathological axes, peaking in `match` exhaustiveness arity ($\alpha = 1.301$ overall, `2.09` for $N = 8 \to 16$) and single-function CFG size ($\alpha = 1.221$, reaching `4.81B Ir` / `795.3 ms` at `1,024` branches). Section 6.2 synthesizes a 10-metric formal verification performance taxonomy ($T_{\text{cert-gen}}$, $T_{\text{check}}$, $T_{\text{crit-verif}}$, $B_{\text{cert}}/S_{\text{MIR}}$, $|V_{\text{DAG}}|$ vs. $|V_{\text{tree}}|$, $M_{\text{check}}$, $H_{\text{proof}}$, $\tau_{\text{norm}}$, $\text{SLOC}_{\text{TCB}}$, and $W_{\text{trusted}}$) that keeps compiler-side and proof-checker costs orthogonal and directly comparable.

## Applicability

### Examined Subjects and Roles

| Subject | Repository | Pinned Revision | Version / Role |
| :--- | :--- | :--- | :--- |
| Rust compiler upstream snapshot | `rust-lang/rust` | `412be32a6a189d9a28922beee178bc0abee9d492` | Primary source authority for `SelfProfiler`, `-Z time-passes`, `jobserver`, `.rmeta` artifact notifications, `CodeStats`, and `-Z llvm-tpde` integration (`2026-11-18`) |
| Rust 1.102.0-nightly toolchain | `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Live-executed nightly compiler (`2026-11-11`, bundled LLVM `23.1.5`, `x86_64-unknown-linux-gnu`) |
| Rust 1.99.1 release toolchain | `rust-lang/rust` | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Live-executed stable baseline compiler (`2026-10-13`, bundled LLVM `23.1.1`, `x86_64-unknown-linux-gnu`) |
| `rustc-perf` collector, DB, and site | `rust-lang/rustc-perf` | `15d95905429e577d5a710b17c49e04b4451c263b` | Primary source authority for compile-time benchmark corpus, `Profile`, `Scenario`, `Metric`, `Profiler`, `rustc-fake`, and PR triage math |
| `measureme` / `decodeme` / `analyzeme` | `rust-lang/measureme` | `5ac839c602b59eee9c908b3b35b6d6c0cd1c42f7` | Version `12.0.3` (pinned in `rust-lang/rust` `Cargo.lock`); normative binary wire format (`v9`) for `.mm_profdata` |
| `TPDE` and `TPDE-LLVM` backend | `rust-lang/tpde` | `050927ee81dc11a9e599fa2524ff0eef16daf51a` | `src/tpde` submodule at `412be32a6a189d9a28922beee178bc0abee9d492`; single-pass x86-64/AArch64 ELF code generator |
| Rust LLVM 23.1 fork (upstream snapshot) | `rust-lang/llvm-project` | `08ec928a5bd1866f4008c8ad216166ca685fd380` | `src/llvm-project` submodule at `412be32a6a189d9a28922beee178bc0abee9d492` |
| Rust 1.99.1 LLVM 23.1.1 fork | `rust-lang/llvm-project` | `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` | `src/llvm-project` submodule in `rustc 1.99.1` |
| Cargo package manager | `rust-lang/cargo` | `f93c676e3e7ab1aee08dc95d869700f6b99a1a20` | `src/tools/cargo` submodule; pipelined unit-graph scheduler consuming `--json=artifacts` |
| Lean 4 v4.34.1 kernel checker | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | Reference proof-checking kernel (`v4.34.1`) for verification-specific performance metrics in Section 6.2 |

### Relationship to Companion Corpus Packages and Host Environment

- **Cross-report boundary:** Companion package `rustc-benchmark-methodology-and-speed-size-baselines` establishes runtime execution speed and linked binary section-size baselines (`W-Core` and `W-Macro` across 14 `-O0`..`-Oz`/LTO/PGO configurations and 8 Tier 1 targets) on `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and an earlier `rustc-perf` snapshot. This report covers the orthogonal **compiler-execution and verification-pipeline performance plane**: the updated `rustc-perf` collector/database/triage architecture at `15d95905429e577d5a710b17c49e04b4451c263b`, `perf_event_open` vs. `Cachegrind` deterministic instruction accounting, `measureme` v9 `.mm_profdata` binary decoding, Cargo `time-to-.rmeta` pipelining, `DHAT` heap churn, asymptotic stress scaling, and certifying/verified-compiler cost accounting (connecting directly to `anneal-verification-pipeline-profiling-and-content-addressed-caching`, `anneal-mirwp-proof-scaling-normalization-and-f1-checker-overhead`, and `rustc-surgical-edit-mir-invalidation-and-early-cutoff-blast-radius`).
- **Host execution environment (`support/compiler_perf_specimen.json`):** Live measurements were acquired on `2026-11-21` on an `x86_64-unknown-linux-gnu` Dual-Socket Intel Xeon (Ice Lake-SP, 48 physical cores / 96 logical CPUs @ 2.60 GHz, `32 KiB` 8-way L1I, `48 KiB` 12-way L1D, `56 MiB` 14-way LL cache, Linux kernel `7.1.6`, KVM hypervisor with `/proc/sys/kernel/perf_event_paranoid = 2`, and `valgrind-3.25.1`).
- **Version-shared vs. version-specific behavior:** `measureme` v9 wire layout, `--json=artifacts` metadata notifications, `perf_event_open` / `Cachegrind` / `DHAT` mechanics, and Cargo pipelining apply identically across `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and `412be32a6a189d9a28922beee178bc0abee9d492` (with `RUSTC_BOOTSTRAP=1` required on `1.99.1` to unlock `-Z` flags). By contrast, `-Z llvm-tpde` (`src/tpde`) and the `Profile::DocJson` / `Profiler::LlvmIr` split in `rustc-perf@15d95905429e577d5a710b17c49e04b4451c263b` are post-`1.99.1` additions.

## Findings

### 1. `rustc-perf` Collector, Benchmark Corpus, Profiles, Scenarios, Metrics, and Triage Math

`Basis: source (rust-lang/rustc-perf@15d95905429e577d5a710b17c49e04b4451c263b)`

#### 1.1 Compile-Time Benchmark Corpus Composition (`69` Benchmarks Across `3` Categories)

Inspection of `collector/src/benchmark_set/compile_benchmarks.rs:1-77`, `collector/src/benchmark_set/mod.rs:280-453`, `collector/src/compile/benchmark/category.rs:7-31`, and all `perf-config.json` manifests under `collector/compile-benchmarks/*` (`70` `perf-config.json` files total: `69` top-level benchmark manifests plus `1` nested fixture file `collector/compile-benchmarks/tt-muncher/quote-1.0.17-modified/perf-config.json`) establishes an exact **69-benchmark** compile-time corpus (`50` `"artifact": "library"` and `19` `"artifact": "binary"`):

| `Category` (`category.rs:7-11`) | Count | DB Representation (`category.rs:25-31`) | Operational Role & Complete Member Inventory (`compile_benchmarks.rs:6-77`) |
| :--- | ---: | :--- | :--- |
| **`Primary`** | **`21`** | `(supports_stable: false, category: "primary")` | **Modern real-world crates** weighting `3x` in PR regression triage: `bitmaps-3.2.1`, `cargo-0.87.1`, `clap_derive-4.5.32`, `cranelift-codegen-0.119.0`, `diesel-2.2.10`, `eza-0.21.2`, `helloworld`, `html5ever-0.31.0`, `hyper-1.6.0`, `image-0.25.6`, `libc-0.2.172`, `nalgebra-0.33.0`, `regex-automata-0.4.8`, `ripgrep-14.1.1`, `serde-1.0.219`, `serde_derive-1.0.219`, `stm32f4-0.15.1`, `syn-2.0.101`, `tokio-1.53.1`, `typenum-1.18.0`, `unicode-normalization-0.1.24`. |
| **`Secondary`** | **`39`** | `(supports_stable: false, category: "secondary")` | **Synthetic stress microbenchmarks and solver/borrowck ablations:**<ul><li>*Next-generation trait solver (`8` `-Znext-solver` variants):* `bitmaps-3.2.1-new-solver`, `deeply-nested-multi-new-solver`, `diesel-2.2.10-new-solver`, `html5ever-0.31.0-new-solver`, `nalgebra-0.33.0-new-solver`, `serde-1.0.219-new-solver`, `syn-2.0.101-new-solver`, `typenum-1.18.0-new-solver`, `wg-grammar-new-solver` (`9` total `-new-solver` crates).</li><li>*Polonius / NLL borrow-checker stress (`3` `-nll` variants):* `clap_derive-4.5.32-nll`, `ripgrep-14.1.1-nll`, `serde-1.0.219-nll`.</li><li>*Micro-stress & pathological regressions (`27` crates):* `await-call-tree`, `coercions`, `ctfe-stress-5`, `deep-vector`, `deeply-nested-multi`, `deref-sidebar-stress`, `derive`, `enum-stress`, `externs`, `helloworld-tiny`, `include-blob`, `issue-46449`, `issue-58319`, `issue-88862`, `large-workspace`, `many-assoc-items`, `projection-caching`, `regression-31157`, `ripgrep-14.1.1-tiny`, `token-stream-stress`, `tt-muncher`, `tuple-stress`, `ucd`, `unify-linearly`, `unused-warnings`, `wf-projection-stress-65510`, `wg-grammar`.</li></ul> |
| **`Stable`** | **`9`** | `(supports_stable: true, category: "primary")` | **Frozen historical crates** compilable across multi-year stable Rust releases (`1.x.0`) for the public release-over-release dashboard (`site/src/request_handlers/dashboard.rs:88-93`): `cargo`, `encoding`, `futures`, `html5ever`, `inflate`, `piston-image`, `regex`, `syn`, `tokio-webpush-simple`. |

On `x86_64-unknown-linux-gnu` (`collector/src/benchmark_set/mod.rs:364-441`), master/try CI splits the 69 compile-time benchmarks across two disjoint collector machines (`Set 0`: `9` `Stable` + `17` non-stable + the `11` runtime benchmark groups + `rustc` bootstrap self-timing; `Set 1`: `43` non-stable), whereas `aarch64-unknown-linux-gnu` (`mod.rs:442-446`) runs all `69` in a single `BenchmarkSet`. Each `BenchmarkConfig` (`collector/src/compile/benchmark/mod.rs:55-92`) defaults to `runs = 3` iterations (`default_runs()`, line `29`), `artifact = Library`, and optional `excluded_profiles`, `excluded_scenarios`, `touch_file`, `package`, and `frontend_threads` overrides.

#### 1.2 `Profile`, `Scenario`, `CodegenBackend`, and `FrontendThreads` Axes

Every compile-time measurement cell in `rustc-perf` (`CompileTestCase`) is indexed by the 6-tuple `(benchmark, profile, scenario, backend, target, frontend_threads)`:

1. **`Profile` (`collector/src/compile/benchmark/profile.rs:10-23`):** Contains **exact `6` variants** at `15d95905429e577d5a710b17c49e04b4451c263b`:
   - `Check`: `cargo rustc --profile check` (`--emit=dep-info,metadata`).
   - `Debug`: `cargo rustc` (`dev` profile, `-C opt-level=0`).
   - `Opt`: `cargo rustc --release` (`release` profile, `-C opt-level=3`).
   - `Doc`: `cargo rustdoc` (HTML documentation generation).
   - `DocJson`: `cargo rustdoc -Zunstable-options --output-format=json -- --document-private-items --document-hidden-items` (`collector/src/compile/execute/mod.rs:451-455, 490-495`, stressing `rustdoc` JSON serialization for `cargo-semver-checks`).
   - `Clippy`: `cargo rustc --profile check` with `RUSTC` redirected to `clippy-fake` (`clippy-driver`) and `RUSTFLAGS+=" -Wclippy::all"` on the leaf crate (`execute/mod.rs:437-448, 481-488`).
   - *(Version delta note:* `LlvmIr` is **not** a `Profile` variant at `15d95905429e577d5a710b17c49e04b4451c263b`; LLVM IR emission `--emit=llvm-ir=./llvm-ir -Cno-prepopulate-passes -Cpasses=name-anon-globals` lives exclusively in `Profiler::LlvmIr` at `collector/src/compile/execute/profiler.rs:33, 443-447` and `rustc-fake.rs:400-408`.)
2. **`Scenario` (`collector/src/compile/benchmark/scenario.rs:5-10`, mapped to `database::Scenario` in `bencher.rs:177-185`):**
   - `Full` $\mapsto$ `database::Scenario::Empty`: `-C incremental` disabled (`CARGO_INCREMENTAL=0`).
   - `IncrFull` $\mapsto$ `database::Scenario::IncrementalEmpty`: Cold creation of `-C incremental=<cwd>/incremental-state` (`execute/mod.rs:540-545`).
   - `IncrUnchanged` $\mapsto$ `database::Scenario::IncrementalFresh`: Warm incremental cache rebuild after touching `touch_file` (or all `.rs` files under the manifest parent) with zero source changes.
   - `IncrPatched` $\mapsto$ `database::Scenario::IncrementalPatch(PatchName)`: Warm incremental rebuild after applying each `NNN-<name>.patch` file in `collector/compile-benchmarks/<bench>/` sorted by numeric index (`patch.rs:28-74`).
3. **`CodegenBackend` (`codegen_backend.rs:4-7`) and `Target` (`target.rs:8-16`):** `Llvm` (default) vs. `Cranelift` (`-Zcodegen-backend=cranelift`), across `X86_64UnknownLinuxGnu`, `AArch64UnknownLinuxGnu`, and `Custom(TargetName)`.
4. **`FrontendThreads` (`frontend_threads.rs:4`):** `NonZeroU32` passed via `RUSTC_THREAD_COUNT=<N>` to `rustc-fake`, which appends `-Zthreads=<N>` (`rustc-fake.rs:79-84`).

#### 1.3 Complete `28`-Metric `database::metric::Metric` Schema and `15`-Tool `Profiler` Suite

`database/src/metric.rs:8-112` defines the exhaustive **`28`-variant `Metric` enum** stored in PostgreSQL/SQLite (`Stats` in `collector/src/compile/execute/mod.rs:829-857`):

| Metric Class | Wire / DB Key (`Metric::as_str`) | Source / Producer | Unit & Exact Meaning |
| :--- | :--- | :--- | :--- |
| **Hardware PMU** | `instructions:u` | `perf stat -x;` / Windows ETW `InstructionRetired` | Retired userspace instructions (primary deterministic CI triage signal). |
| **Hardware PMU** | `cycles`, `cycles:u` | `perf stat` / Windows ETW `TotalCycles` | Total / userspace core clock cycles (frequency-scaling sensitive). |
| **Hardware PMU** | `branch-misses`, `cache-misses` | `perf stat -e branch-misses,cache-misses` | Hardware branch-predictor mispredictions and LLC misses. |
| **OS CPU Clocks** | `task-clock`, `task-clock:u`, `cpu-clock`, `cpu-clock:u` | `perf stat` / ETW | Aggregated kernel+user or user-only CPU time across threads (`ms` in `perf stat`). |
| **Wall Latency** | `wall-time` | `rustc-fake` `Instant::now().elapsed()` (`rustc-fake.rs:139-143, 550-554`) | End-to-end leaf `rustc` wall-clock seconds (`$sec.$nanos`). |
| **Memory & OS** | `max-rss` | `libc::getrusage(RUSAGE_CHILDREN).ru_maxrss` (`rustc-fake.rs:530-541`) | Peak resident set size of wrapped child (`KiB` on Linux). |
| **Memory & OS** | `faults`, `faults:u`, `context-switches` | `perf stat -e faults,context-switches` | Page faults (minor + major) and voluntary + involuntary context switches. |
| **CGU Estimates** | `size:codegen_unit_size_estimate`, `size:cgu_instructions` | `-Zself-profile` `ArtifactSize` events (`profiling.rs:365`) | `rustc` pre-codegen MIR CGU size estimate vs. actual emitted LLVM IR instruction count. |
| **Binary / Codegen** | `size:linked_artifact`, `size:object_file`, `size:crate_metadata`, `size:dwo_file`, `size:assembly_file`, `size:llvm_bitcode`, `size:llvm_ir` | `-Zself-profile` `ArtifactSize` events (`execute/mod.rs:681-687`) | Total bytes written to final `.rlib`/bin, `.rcgu.o` objects, `.rmeta`, split DWARF `.dwo`, `.s`, `.bc`, and `.ll`. |
| **Incremental Disk** | `size:dep_graph`, `size:query_cache`, `size:work_product_index` | `-Zself-profile` `ArtifactSize` events | Bytes written to incremental `dep-graph.bin`, `query-cache.bin`, and `work-products.bin`. |
| **Rustdoc Output** | `size:doc_bytes`, `size:doc_files_count` | `store_documentation_size_into_stats` (`execute/mod.rs:667-679`) | Total byte size and file count of `target/doc` under `Profile::Doc`. |

Separately from `Metric` time-series benchmarking (`Bencher::{PerfStat, PerfStatSelfProfile, XperfStat, XperfStatSelfProfile}`), `collector` provides **`15` diagnostic `Profiler` modes** (`collector/src/compile/execute/profiler.rs:18-34`): `SelfProfile` (`summarize`, `flamegraph`, `crox`), `PerfRecord` (`perf record --call-graph=dwarf --freq=299`), `Oprofile`, `Samply`, `Cachegrind`, `Callgrind`, `Dhat`, `DhatCopy`, `Massif` (`--alloc-fn=__rdl_alloc`), `Bytehound`, `Eprintln` (filtering `$message_type` JSON lines), `LlvmLines` (`cargo llvm-lines`), `MonoItems` (`-Zprint-mono-items` partitioned per CGU), `DepGraph` (`-Zdump-dep-graph -Zquery-dep-graph`), and `LlvmIr`. In addition, `collector/src/artifact_stats.rs:21-165` parses ELF/archive `.rcgu.o` members via `object`, normalizing `.text._RNv...` subsections into `.text` and stripping `.cold`/`.warm`, v0 `[hash]`, legacy `::h<hex>`, and `.llvm.<hash>` suffixes so per-symbol code-size diffs match across LTO/PGO builds.

#### 1.4 `rustc-fake` Two-Phase Interposition and Self-Profile Timing Isolation

`collector` isolates leaf-crate compilation from upstream dependency builds without patching Cargo (`collector/src/compile/execute/mod.rs:289-553`, `collector/src/bin/rustc-fake.rs:20-147`):

1. **Preparation pass (`needs_final = false`):** `Benchmark::prepare` (`benchmark/mod.rs:414-446`) runs `cargo rustc -p <pkgid> ... -- --skip-this-rustc` across profiles concurrently under a shared `jobserver::Client`. Dependency crates invoke `rustc-fake` without `--skip-this-rustc`, so `rustc-fake` sets `RUSTC_FORCE_INCR_COMP_ARTIFACT_HEADER="rustc-perf"` and `RUSTC_FORCE_RUSTC_VERSION="rustc-perf"` (eliminating `StableCrateId` commit-hash entropy across compiler revisions), appends `-Adeprecated -Aunknown-lints -Zincremental-verify-ich`, and `exec`s `RUSTC_REAL`. When Cargo reaches the leaf crate, it passes `--skip-this-rustc`, causing `rustc-fake` to exit `0` immediately (`rustc-fake.rs:434-436`).
2. **Measurement pass (`needs_final = true`):** `CargoProcess::run_rustc` touches `touch_file`, exports `EXPECT_ONLY_WRAPPED_RUSTC=1` (causing `rustc-fake` to abort with exit code `1` if Cargo unexpectedly recompiles any unwrapped dependency, `rustc-fake.rs:438-448`), restricts hybrid Intel (`/sys/devices/cpu_core/cpus`) and ARM (`cpu_capacity >= 0.9 * max`) CPUs to P-cores via `taskset --cpu-list` (`execute/mod.rs:150-301`), and passes `--wrap-rustc-with <PerfTool>` after `--`.
3. **First-collection `PerfStatSelfProfile` contamination guard (`bencher.rs:132-206`):** Enabling `-Zself-profile` distorts instruction counts, wall time, and RSS. `BenchProcessor` therefore runs iteration `0` under `PerfStatSelfProfile`, uploads the Snappy-framed `.mm_profdata.sz` trace to S3/local storage (`self_profile.rs:319-327`), and **discards all timing and counter metrics from that run** via `res.0.stats.retain(|key, _| key.starts_with("size:"))` (`bencher.rs:205`), before re-running the `N = 3` timed iterations under pure `PerfStat` (`setarch <ARCH> -R`).

#### 1.5 `site/` Triage Significance Math vs. Suite Geometric-Mean Parity Gates

Inspection of `site/src/comparison.rs:346-513, 1232-1443` and `site/frontend/src/pages/compare/data.ts:86-136` reveals three exact formulas that govern `perf.rust-lang.org` PR triage—and a critical statistical pitfall when repurposing them for full-compiler comparisons:

1. **30-commit historical IQR significance threshold (`comparison.rs:1190, 1238-1308, 1347`):** For each `CompileTestCase`, `HistoricalData` fetches the preceding $K = 30$ master commits, computes the $29$ adjacent absolute relative deltas $d_t = |x_t - x_{t+1}| / x_t$, and defines the per-case noise barrier:
   $$\tau_{\text{sig}} = Q_3(d) + 3.0 \cdot \bigl(Q_3(d) - Q_1(d)\bigr)$$
   falling back to `DEFAULT_SIGNIFICANCE_THRESHOLD = 0.002` (`0.2%`) when fewer than 30 prior commits exist.
2. **Dual-factor `Magnitude` and relevance filter (`comparison.rs:357-376, 1384-1437`):** A change $\Delta = |B - A| / A$ is `is_significant()` iff $\Delta \ge \tau_{\text{sig}}$. Its `Magnitude` (`1 = VerySmall` .. `5 = VeryLarge`) averages the integer rank of $\Delta / \tau_{\text{sig}}$ (cutoffs `1.5x`, `3.0x`, `6.0x`, `12.0x`) with the integer rank of absolute percent change $100\Delta / \nu_m$ (cutoffs `0.2%`, `1.0%`, `2.0%`, `5.0%`), where the metric noise factor is $\nu_m = 1.0$ for `instructions:u` and $\nu_m = 2.0$ for all other 27 metrics (`is_typically_noisy()`). A test case is `is_relevant()` iff `is_significant() && magnitude >= Magnitude::Small` (and $\Delta \ge 0.0001$). A commit triggers `deserves_attention_icount` (`comparison.rs:593-608`) iff `primary` has a `>= Medium` change, `secondary` has a `>= Large` change, or `3 * primary.num_changes() + secondary.num_changes() >= 9`.
3. **Why `rustc-perf` headline means differ from suite geometric means:** Both `ArtifactComparisonSummary::arithmetic_mean` (`comparison.rs:501-513`) and `computeSummary` (`data.ts:127-128`) compute the **arithmetic mean of relative changes over `is_relevant()` cases only** (while `aggregations.vue:31-36` also displays $\frac{\sum B_i - \sum A_i}{\sum A_i}$, weighting long benchmarks disproportionately). Filtering by `is_relevant()` is ideal for catching localized PR regressions on incremental compiler commits, where $>98\%$ of test cases are unchanged (`0%`). However, when comparing two distinct compilers or backends (where nearly every crate shifts), arithmetic means of $(B_i - A_i)/A_i$ violate inversion symmetry (e.g., one `2.0x` slowdown `+100%` and one `0.5x` speedup `-50%` yield an arithmetic mean of **`+25.0%`** rather than net parity) and censoring sub-threshold improvements introduces selection bias. Cross-compiler parity evaluations must therefore report the **unfiltered suite geometric mean of ratios**:
   $$\text{GeoMean}(B / A) = \exp\!\left(\frac{1}{N} \sum_{i=1}^{N} \ln\!\left(\frac{B_i}{A_i}\right)\right), \qquad \Delta_{\text{geo}}\% = \bigl(\text{GeoMean}(B / A) - 1\bigr) \times 100\%$$
   paired with tail quantiles ($p_{90}$, $\max$) as specified in `rustc-benchmark-methodology-and-speed-size-baselines`.

---

### 2. Deterministic Instruction, Cache, and Syscall Accounting (`perf_event_open` vs. `Cachegrind`)

`Basis: source + execution + derived (support/probe_compiler_perf_metrics.py, support/compiler_perf_specimen.json)`

#### 2.1 `perf_event_open` Syscall `298` Privilege Semantics Under `perf_event_paranoid = 2`

On `x86_64` Linux, `syscall(298, &attr, pid, cpu, group_fd, flags)` (`__NR_perf_event_open = 298`) configures per-process performance counters via `struct perf_event_attr` (`136` bytes). To profile an external `rustc` invocation across all spawned Rayon / LLVM codegen worker threads without root privileges (`CAP_PERFMON`) when `/proc/sys/kernel/perf_event_paranoid == 2`, the caller forks a synchronized child, attaches `perf_event_open` from the parent to `pid = child_pid, cpu = -1` with bitfield flags:

$$\text{flags} = \underbrace{2^0}_{\text{disabled}} \;\mid\; \underbrace{2^1}_{\text{inherit}} \;\mid\; \underbrace{2^5}_{\text{exclude\_kernel}} \;\mid\; \underbrace{2^6}_{\text{exclude\_hv}} \;\mid\; \underbrace{2^{12}}_{\text{enable\_on\_exec}} = \texttt{0x1063}$$

and unblocks the child's `execve` over a pipe (`support/probe_compiler_perf_metrics.py:189-243`). Probing all 13 hardware and software event configurations on the Ice Lake-SP KVM host (`perf_event_paranoid = 2`) establishes a sharp two-regime kernel behavior:

- **Privilege gate passed (`errno != EACCES`):** Omitting `exclude_kernel = 1` at `perf_event_paranoid = 2` fails immediately with `EACCES` (`errno = 13`). With `0x1063`, the kernel accepts unprivileged userspace attachment.
- **Software counters succeed (`fd >= 0`, `errno = 0`) while unvirtualized KVM PMU counters fail with `ENOENT` (`errno = 2`):** All 7 `PERF_TYPE_SOFTWARE` (`type = 1`) counters—`cpu-clock:u`, `task-clock:u`, `page-faults:u`, `context-switches:u`, `cpu-migrations:u`, `minor-faults:u`, and `major-faults:u`—open cleanly and aggregate across child threads via `inherit = 1`. Conversely, all 6 `PERF_TYPE_HARDWARE` (`type = 0`) counters (`instructions:u`, `cycles:u`, `cache-references:u`, `cache-misses:u`, `branches:u`, `branch-misses:u`) return `ENOENT` (`No such file or directory`) because the cloud hypervisor masks architectural PMU CPUID leaf `0x0a`. On bare-metal runners (including upstream `rustc-perf` collectors) or KVM guests booted with `-cpu host,pmu=on`, the identical `0x1063` syscall returns hardware `instructions:u` directly.

#### 2.2 Valgrind `Cachegrind` 13-Event Simulation and `CEst` Cycle Estimation Formula

When hardware PMUs are unavailable (or when kernel/page-table/ASLR address jitter must be eliminated), `valgrind --tool=cachegrind --cache-sim=yes --branch-sim=yes` translates guest `x86_64` basic blocks through LibVEX and simulates a two-level inclusive/non-inclusive cache hierarchy (`I1`, `D1`, `LL`, auto-detected from host CPUID unless overridden via `--I1`/`--D1`/`--LL`) plus a bimodal + global-history indirect branch predictor:

- **13 raw `Cachegrind` events:**
  - *Instruction fetch:* `Ir` (instructions executed), `I1mr` (L1I read misses), `ILmr` (last-level instruction read misses).
  - *Data reads:* `Dr` (memory data reads), `D1mr` (L1D read misses), `DLmr` (LL data read misses).
  - *Data writes:* `Dw` (memory data writes), `D1mw` (L1D write misses), `DLmw` (LL data write misses).
  - *Branches:* `Bc` (conditional branches executed), `Bcm` (conditional branch mispredictions), `Bi` (indirect branches/jumps executed), `Bim` (indirect branch mispredictions).
- **Composite miss aggregates and classic `CEst` cycle estimate:** Defining total L1 misses $\text{L1m} = \text{I1mr} + \text{D1mr} + \text{D1mw}$, total last-level cache misses $\text{LLm} = \text{ILmr} + \text{DLmr} + \text{DLmw}$, and total branch mispredictions $\text{Bm} = \text{Bcm} + \text{Bim}$, the standard Valgrind Callgrind/Cachegrind synthetic cycle-cost estimator weights L1 misses and branch flushes at `10` cycles and last-level misses at `100` cycles:
  $$\text{CEst} = \text{Ir} + 10 \cdot \text{Bm} + 10 \cdot \text{L1m} + 100 \cdot \text{LLm}$$
- **Eliminating jemalloc background purge variance:** `rustc` links `tikv-jemalloc` on `x86_64-unknown-linux-gnu`, which uses wall-clock decay timers (`dirty_decay_ms`, `muzzy_decay_ms`, defaulting to `10,000 ms`) to `madvise(MADV_FREE / MADV_DONTNEED)` unused pages. Because Valgrind slows wall-clock execution by `200x`–`360x`, a native `100 ms` compilation crosses jemalloc's `10 s` wall-clock decay threshold mid-run under Valgrind, injecting non-deterministic `Ir` noise unless `MALLOC_CONF="dirty_decay_ms:0,muzzy_decay_ms:0"` is set (`rustc-fake.rs:285-290`). For human-readable diffs, `collector/src/utils/cachegrind.rs:37-95` collapses all `/jemalloc/` frames into `<all-jemalloc-files>:<all-jemalloc-functions>`, demangles Rust v0 symbols, normalizes `/rustc/<sha>/` and `.llvm.<hash>` suffixes via `cg_diff`, and renders percentages via `cg_annotate --show-percs=yes`.

#### 2.3 Empirical Variance Comparison Across `rustc 1.99.1` and `rustc 1.102.0-nightly`

Table 1 summarizes `Probe 1` (`support/compiler_perf_specimen.json`, `probe_1_determinism_perf_and_cachegrind`) compiling the 146-line `perf_subject` crate (`VmState` bytecode interpreter, generic `HashFold` trait, and `DenseMatrix<4,4>` / `DenseMatrix<8,8>` multiplication at `-C opt-level=2`) under `setarch x86_64 -R` and `MALLOC_CONF="dirty_decay_ms:0,muzzy_decay_ms:0"`:

| Metric / Observable | `rustc 1.99.1` (`58cf8f9c35b3`) | `rustc 1.102.0-nightly` (`3ef0c22cdb86`) | Determinism / Engineering Interpretation |
| :--- | ---: | ---: | :--- |
| Native wall-clock median (`N = 5`, `ms`) | `108.643 ms` | `174.135 ms` | Subject to OS scheduling, turbo-boost, and transient host load. |
| **Native wall-clock CV (`%`)** | **`3.5106%`** | **`33.0547%`** | High jitter (`3.5%`–`33.1%`) masks `< 2%` compiler pass improvements. |
| `perf_event_open` `task-clock:u` median (`ms`) | `114.223 ms` | `153.509 ms` | Excludes off-CPU sleep time; `task-clock / wall > 1` reflects CGU threads. |
| **`perf_event_open` `task-clock:u` CV (`%`)** | **`4.2628%`** | **`15.5371%`** | Better than wall time under preemption, still noisy from cache/frequency state. |
| `perf_event_open` `minor-faults:u` (`N = 5` CV) | `5,194` (`0.1084%`) | `5,599` (`0.8841%`) | `0` major faults; `~5.2k`–`5.6k` minor anonymous/mmap page faults per invocation. |
| `wait4(2)` isolated `max-rss` median (`KiB`) | `162,432 KiB` | `137,344 KiB` | Nightly reduces peak RSS by **`-15.4%`** (`-25.1 MiB`) on identical source. |
| `Cachegrind` `Ir` median (`N = 3`, multi-CGU) | `288,643,124` | `287,890,152` | Nightly executes **`-0.261%`** fewer instructions (`-752,972 Ir`) than `1.99.1`. |
| **`Cachegrind` `Ir` CV (`%`, multi-CGU `-O2`)** | **`0.0834%`** (`1,646 ppm`) | **`0.0375%`** (`676 ppm`) | **`42x`–`881x` lower variance** than native wall-clock; residual `<0.09%` is CGU thread-lock serialization. |
| **`Cachegrind` `Ir` CV (`%`, single-CGU `cgu=1`)** | **`0.0034%`** (`68.7 ppm`) | — | Eliminating multi-CGU worker threads (`-C codegen-units=1`) drops `Ir` CV to **`34.4 ppm`** (`[26,774,928, 26,773,088, 26,774,052]`). |
| `Cachegrind` `I1mr` / `ILmr` (run 0) | `4,206,507` / `196,906` | `4,266,123` / `200,152` | High L1I miss rate (`14.57` / `1k Ir`) characteristic of large compiler instruction footprints (`librustc_driver` + `libLLVM`). |
| `Cachegrind` `Dr` / `D1mr` / `DLmr` (run 0) | `77.47M` / `1.93M` / `141.7k` | `77.14M` / `1.95M` / `140.4k` | Pointer-chasing across AST/HIR/Ty interners and LLVM IR `Use` lists. |
| `Cachegrind` `Dw` / `D1mw` / `DLmw` (run 0) | `40.91M` / `868.1k` / `263.3k` | `40.50M` / `895.4k` / `260.5k` | Arena bump allocation and bitcode/object buffer emission. |
| `Cachegrind` `Bc` / `Bcm` / `Bi` / `Bim` (run 0) | `49.41M` / `3.99M` / `1.81M` / `554.4k` | `48.98M` / `4.02M` / `1.80M` / `555.1k` | **`8.88%`–`9.02%` branch mispredict rate** (`30.6%` on indirect `Bi` query/pass vtables). |
| `Cachegrind` `CEst` median & CV (`%`) | `464,353,704` (`0.3090%`) | `464,844,756` (`0.2907%`) | `CEst / Ir = 1.609`–`1.615` effective simulated cycles per instruction. |
| Full `Cachegrind` slowdown vs. native wall | `358.98x` | `234.06x` | Use `--cache-sim=no --branch-sim=no` (`rustc-fake.rs:292-293`) when only `Ir` is needed (`~15x`–`25x`). |

---

### 3. Internal Phase Attribution, `measureme` v9 Wire Format, IR Volume, and Fast `-O0` Backends

`Basis: source + execution + derived (rust-lang/rust@412be32a6a189d9a28922beee178bc0abee9d492, rust-lang/measureme@5ac839c602b59eee9c908b3b35b6d6c0cd1c42f7, rust-lang/tpde@050927ee81dc11a9e599fa2524ff0eef16daf51a, support/compiler_perf_specimen.json)`

#### 3.1 `-Z time-passes` JSON Schema vs. `--json=timings` and Live Phase Decompositions

`rustc` provides two distinct JSON timing streams on `stderr` that tools must not conflate:

1. **Detailed pass hierarchy (`-Z time-passes -Z time-passes-format=json`, `compiler/rustc_data_structures/src/profiling.rs:861-903`, `compiler/rustc_session/src/options.rs:3035-3038`):** Every `VerboseTimingGuard` drop emits an unbuffered `stderr` line prefixed by literal `"time: "`:
   ```text
   time: {"pass":"type_check_crate","time":0.009745,"rss_start":81264640,"rss_end":86507520}
   ```
   where `"time"` is `Duration::as_secs_f64()` and `"rss_start"` / `"rss_end"` are **instantaneous** resident bytes read from `/proc/self/statm` field `1` multiplied by `sysconf(_SC_PAGESIZE)` (`profiling.rs:991-1000`, `K32GetProcessMemoryInfo` `WorkingSetSize` on Windows, `proc_pidinfo` `pti_resident_size` on macOS). In default `Text` mode (`TimePassesFormat::Text`), `print_time_passes_entry` **silently elides** any pass with `dur.as_millis() <= 5` and zero RSS delta (`profiling.rs:906-922`), whereas `TimePassesFormat::Json` emits **all** `79`–`126` verbose activities unconditionally.
2. **Cargo section markers (`-Z unstable-options --json=timings --error-format=json`, `compiler/rustc_errors/src/json.rs:120-131`):** Emits standard JSON diagnostic lines (`{"$message_type":"section_timing","name":"codegen"|"link","event":"start"|"end","timestamp":<integer>}`) consumed by `cargo build --timings` to split each bar into frontend (start $\rightarrow$ `codegen:start`), backend codegen (`codegen:start` $\rightarrow$ `codegen:end`), and linking (`link:start` $\rightarrow$ `link:end`).

Table 2 reports key `-Z time-passes -Z time-passes-format=json` phases from `Probe 2` on `perf_subject`:

| Pass / Metric (`ms` unless noted) | `1.99.1` `Check` | `1.99.1` `Debug_O0` | `1.99.1` `Opt_O3` | `1.102.0-nightly` `Check` | `1.102.0-nightly` `Debug_O0` | `1.102.0-nightly` `Opt_O3` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| Emitted JSON pass records (`pass_count`) | `116` | `125` | `126` | `79` | `88` | `89` |
| `parse_crate` | `0.430` | `0.560` | `0.425` | `0.554` | `0.551` | `0.538` |
| `macro_expand_crate` | `2.300` | `2.364` | `2.275` | `2.315` | `2.332` | `2.459` |
| `late_resolve_crate` | `1.315` | `1.384` | `1.324` | `1.729` | `1.758` | `1.744` |
| `type_check_crate` | `9.678` | `9.638` | `9.420` | `9.745` | `9.846` | `9.719` |
| `MIR_borrow_checking` *(consolidated in `1.102.0`)* | `4.301` | `5.345` | `5.123` | *(per-body query)* | *(per-body query)* | *(per-body query)* |
| `monomorphization_collector_graph_walk` | — | `3.880` | `2.332` | — | `3.428` | `1.913` |
| `codegen_crate` (MIR $\rightarrow$ LLVM IR lowering) | `0.019` | `3.668` | `3.308` | `0.019` | `4.098` | `3.353` |
| `LLVM_passes` + `finish_ongoing_codegen` | `0.037` | `14.956` | **`70.998`** | `0.036` | `14.697` | **`80.991`** |
| `total` (`rustc` internal driver span) / Process wall | `31.28` / `39.36` | `48.16` / `55.68` | `94.83` / `103.07` | `30.80` / `43.60` | `47.95` / `57.01` | `104.65` / `117.52` |
| Peak `rss_end` (`MiB`) / `wait4` `max_rss` (`KiB`) | `132.35` / `135,220` | `157.12` / `163,432` | `157.19` / `164,020` | `111.11` / `113,340` | `131.20` / `138,048` | `135.66` / `141,356` |

*(Note the `1.99.1` $\rightarrow$ `1.102.0-nightly` schema shift: `pass_count` drops from `116`–`126` to `79`–`89` because batch wrapper passes such as `MIR_borrow_checking` were removed in favor of on-demand query execution—demonstrating why automated pass parsers must handle absent pass names gracefully and rely on `-Z self-profile` for stable query-level attribution.)*

#### 3.2 `SelfProfiler` Architecture and `EventFilter` Bitmask (`profiling.rs:104-156, 591-773`)

`SelfProfiler` wraps `measureme::Profiler` and gates overhead via a `u16` `EventFilter` bitmask stored inline inside `SelfProfilerRef` (`profiling.rs:106-135, 205-224`) so disabled checks compile to a single inlined bit-test jumping over an `#[inline(never)] #[cold]` slow path:

- **`DEFAULT` (`-Z self-profile=<dir>`):** Enables 7 bitflags: `GENERIC_ACTIVITIES` (`1<<0`), `QUERY_PROVIDERS` (`1<<1`), `QUERY_BLOCKED` (`1<<3`), `INCR_CACHE_LOADS` (`1<<4`), `INCR_RESULT_HASHING` (`1<<8`), `ARTIFACT_SIZES` (`1<<9`), and **`QUERY_CACHE_HIT_COUNTS` (`1<<10`)**.
- **Aggregated hit counters vs. per-hit instant events (`profiling.rs:420-446, 521-542, 597-608`):** Recording an instant event on every in-memory query cache hit (`query-cache-hit`, `1<<2`) slows compilation **`3x`–`5x`**. Instead, `DEFAULT` enables `query-cache-hit-count` (`1<<10`), incrementing `RwLock<Vec<AtomicU64>>` indexed by `QueryInvocationId(u32)` (`DepNodeIndex`) with `Ordering::Relaxed` and flushing only non-zero `QueryCacheHitCount` integer events once at session teardown (`store_query_cache_hits`).
- **Optional high-detail filters:** `args` (`query-keys` `1<<5` | `function-args` `1<<6`), `llvm` (`1<<7`, hooking `LLVMRustSelfProfileBeforePassCallback` in `PassWrapper.cpp:585-590` to emit `"LLVM Pass"` intervals), `all`, and `none`.
- **7-digit zero-padded PID filename (`profiling.rs:631-636`):** Output stems are formatted as `{crate_name}-{pid:07}.mm_profdata` because unpadded variable-length PID strings in heap/environment allocations measurably shift heap addresses and cache-line alignment when ASLR is disabled.

#### 3.3 Exact `measureme 12.0.3` (`v9`) `.mm_profdata` Binary Wire Specification

Direct source audit of `rust-lang/measureme@5ac839c602b59eee9c908b3b35b6d6c0cd1c42f7` (`file_header.rs`, `serialization.rs`, `raw_event.rs`, `stringtable.rs`, `event_id.rs`, `decodeme/src/stringtable.rs`, and `analyzeme/src/analysis.rs`) and our clean-room decoder (`support/probe_compiler_perf_metrics.py:251-428`) establish the complete byte-level specification:

1. **Outer paged container (`file_header.rs:8-20`, `serialization.rs:18-63`):**
   - Bytes `0..8`: Top-level header `b"MMPD"` (`4` bytes) + `CURRENT_FILE_FORMAT_VERSION = 9u32` (`4` bytes little-endian: `\x09\x00\x00\x00`).
   - Bytes `8..EOF`: Contiguous sequence of unaligned pages (`MAX_PAGE_SIZE = 262,144` B, `MIN_PAGE_SIZE = 131,072` B):
     ```text
     [ page_tag : u8 (0 = Events, 1 = StringData, 2 = StringIndex) ]
     [ page_size : u32 LE                                          ]
     [ page_payload : [u8; page_size]                              ]
     ```
   - Concatenating payloads of identical `page_tag` reconstructs three logical byte streams, each starting with its own 8-byte stream header: `b"MMES" + 9u32` (`Events`), `b"MMSD" + 9u32` (`StringData`), and `b"MMSI" + 9u32` (`StringIndex`).
2. **32-byte little-endian `RawEvent` (`raw_event.rs:10-126`):** After the 8-byte `MMES` header, `Events` holds $N_{\text{ev}} = (\text{len} - 8) / 32$ packed records:
   ```text
   Offset  Size  Type      Field & Bit Packing
   0..8    8 B   u64 LE    event_kind (StringId: "Query", "GenericActivity", "LLVM Pass", ...)
   8..16   8 B   u64 LE    event_id   (EventId = StringId; virtual DepNodeIndex or concrete DAG id)
   16..20  4 B   u32 LE    thread_id
   20..24  4 B   u32 LE    payload1_lower  (bits 0..31 of val1)
   24..28  4 B   u32 LE    payload2_lower  (bits 0..31 of val2)
   28..32  4 B   u32 LE    payloads_upper  (bits 16..31 = val1[32..47]; bits 0..15 = val2[32..47])
   ```
   Unpacking the two 48-bit unsigned integers `val1 = payload1_lower | ((payloads_upper & 0xFFFF_0000) << 16)` and `val2 = payload2_lower | ((payloads_upper & 0x0000_FFFF) << 32)`:
   - `val2 == 0xFFFF_FFFF_FFFF` (`INSTANT_MARKER`): **Instant event** at timestamp `val1` ns (`QueryCacheHit`).
   - `val2 == 0xFFFF_FFFF_FFFE` (`INTEGER_MARKER`): **Integer event** with scalar count/size `val1` (`ArtifactSize`, `QueryCacheHitCount`).
   - `val2 <= 0xFFFF_FFFF_FFFD` (`MAX_INTERVAL_VALUE`, ~78.1 hours in ns): **Interval event** spanning `[val1, val2]` ns; because intervals are written when `TimingGuard` drops, **children precede their enclosing parent** in the `MMES` stream.
3. **UTF-8 DAG StringTable (`MMSD` + `MMSI`, `stringtable.rs:117-195`, `event_id.rs:19`):**
   - `StringId` namespace partition: `0 ..= 100,000,000` (`MAX_USER_VIRTUAL_STRING_ID`, used for `DepNodeIndex` virtual query IDs), `100,000_001` (`METADATA_STRING_ID`, JSON object `{"start_time", "process_id", "cmd", "counter"}`), `100,000_002` (`INVALID`), and `>= 100,000_003` (`FIRST_REGULAR_STRING_ID`).
   - Crucial offset invariant: `StringTableBuilder::new` writes the 8-byte `MMSD` header through `data_sink`, advancing `data_sink.addr` from `0` to `8`. Consequently, both `addr = regular_id - 100_000_003` and the `16`-byte `[virtual_id: u64 LE, addr: u64 LE]` records in `MMSI[8..]` index **directly into the `MMSD` buffer with its 8-byte header retained** (`addr >= 8`).
   - Each string entry at `MMSD[addr..]` is a sequence of components terminated by `0xFF` (illegal in UTF-8): any byte `< 0xFE` begins a literal UTF-8 slice running until the next `0xFE` or `0xFF`; byte `0xFE` (`STRING_REF_TAG`) followed by an 8-byte `u64 LE` `StringId` (`9` bytes total) splices the referenced string recursively. Event arguments are separated from `<label>` by ASCII Record Separator `\x1E` (`SEPARATOR_BYTE`).
4. **Single-pass reverse-chronological self-time attribution (`analyzeme/src/analysis.rs:115-289`):** Iterating `MMES` **backwards** (`idx = N_ev - 1` down to `0`) visits every parent interval before its nested children on the same `thread_id`. Maintaining a per-thread interval stack (popping entries whose `[start, end]` does not contain the current event), `perform_analysis` subtracts each child's duration $d = \text{end} - \text{start}$ from its immediate stack parent's `self_time` (and from `incremental_hashing_time` or `incremental_load_time` when the parent has those kinds) and adds $d$ to the current event's `self_time` and `time` (omitting `time` addition for `IncrementalResultHashing` because it already executes inside its enclosing `Query` interval).

Table 3 presents decoded `.mm_profdata` v9 and `-Z incremental-info` metrics across all four `Scenario`s on `perf_subject` (`-C opt-level=2 -C codegen-units=4 -Z self-profile-events=default,args,llvm`):

| `measureme` v9 / Incremental Observable | `1.99.1` `Full` | `1.99.1` `IncrFull` | `1.99.1` `IncrUnchanged` | `1.99.1` `IncrPatched` | `1.102.0` `Full` | `1.102.0` `IncrFull` | `1.102.0` `IncrUnchanged` | `1.102.0` `IncrPatched` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Wall time (`ms`) | `98.86` | `116.36` | **`54.95`** | `89.30` | `104.69` | `122.54` | **`72.14`** | `97.76` |
| `.mm_profdata` total size (`KiB`) | `2,067.3` | `2,951.2` | `808.5` | `1,605.5` | `1,956.4` | `2,818.2` | `842.0` | `1,578.8` |
| `RawEvent` count (`MMES` / `32 B`) | `30,666` | `57,744` | `20,030` | `31,987` | `29,794` | `56,207` | `20,226` | `31,510` |
| `Query` provider executions | `11,833` | `11,705` | **`2,589`** | `6,175` | `11,489` | `11,366` | **`2,884`** | `6,159` |
| Total in-memory `Query` cache hits | `102,002` | `106,076` | `23,574` | `47,177` | `101,303` | `105,299` | `24,884` | `46,201` |
| `LLVM Pass` interval events | `5,431` | `8,377` | **`0`** | `3,952` | `5,187` | `8,142` | **`0`** | `3,952` |
| `IncrementalLoadResult` events / `ms` | `0` / `0.0` | `0` / `0.0` | `864` / `1.77` | `1,026` / `1.36` | `0` / `0.0` | `0` / `0.0` | `876` / `2.00` | `1,034` / `1.70` |
| `IncrementalResultHashing` events / `ms` | `0` / `0.0` | `11,870` / `9.20` | `440` / `0.18` | `526` / `0.28` | `0` / `0.0` | `11,532` / `9.62` | `442` / `0.27` | `523` / `0.41` |
| `DepGraph` nodes / edges (`-Zincremental-info`) | — | `12,135` / `38,920` | `12,114` / `38,899` | `12,225` / `39,668` | — | `11,759` / `38,432` | `11,782` / `38,610` | `11,841` / `39,138` |
| `size:object_file` (`ArtifactSize`, `B`) | `34,352` | `44,048` | **`0`** (100% reused) | **`19,128`** (1/4 CGU) | `34,272` | `43,992` | **`0`** (100% reused) | **`19,136`** (1/4 CGU) |
| `size:dep_graph` / `size:query_cache` (`KiB`) | — | `520.6` / `88.2` | `519.8` / `89.1` | `525.4` / `93.8` | — | `505.8` / `71.0` | `507.0` / `72.4` | `510.2` / `77.1` |

Notice how `IncrPatched` (mutating one constant inside `#[inline(never)] pub fn leaf_checksum`) reduces `LLVM Pass` invocations from `8,377` (`IncrFull`, 4 CGUs) to `3,952` and reduces emitted `size:object_file` bytes from `44,048 B` (`19,128 + 12,376 + 7,104 + 5,440 B` across the 4 `.o` modules) to **exact `19,128 B`**—recompiling only the single dirty CGU containing `leaf_checksum` while reusing the other 3 `.o` modules from the incremental session cache!

#### 3.4 Fast `-O0` Backend Alternatives: LLVM `FastISel`, `Cranelift`, and `TPDE-LLVM` (`-Z llvm-tpde`)

For rapid edit-compile-test and proof-iteration cycles, `rust-lang/rust@412be32a6a189d9a28922beee178bc0abee9d492` supports three unoptimized/debug codegen paths with sharply different throughput, target coverage, and IR boundaries:

1. **LLVM `-O0` (`FastISel` + `SelectionDAG` fallback):** Default backend across all targets. At `-C opt-level=0`, LLVM uses `FastISel` for straight-line instructions, but falls back to full `SelectionDAG` graph construction on unsupported terminators—most notably `SwitchInt` (`match` dispatch tables, documented at `compiler/rustc_codegen_ssa/src/mir/block.rs:522`, where `rustc` lowers binary switches to `br i1` specifically to stay on `FastISel`).
2. **Cranelift (`rustc_codegen_cranelift`, `-Z codegen-backend=cranelift`):** Replaces `rustc_codegen_llvm` entirely at the `rustc_codegen_ssa` MIR-lowering boundary. Avoids building LLVM IR (`libLLVM.so` is never invoked), accelerating backend codegen `4.1x`–`10.7x` over LLVM `-O3` (`18%`–`60%` total compile-time reduction) and generating `5.2x`–`8.1x` faster `-O0` loop code than LLVM `FastISel`, at the cost of `panic=abort`-only unwinding in its standard sysroot and narrower target support (`x86_64`, `aarch64`, `s390x`, `riscv64`).
3. **Newly integrated `TPDE-LLVM` single-pass plugin (`src/tpde` @ `050927ee81dc11a9e599fa2524ff0eef16daf51a`, `-Z llvm-tpde`):**
   - *Wiring (`tpde_ffi.rs:52-125`, `PassWrapper.cpp:500-538`, `tpde-plugin.cpp:13-42`):* Unlike Cranelift, `-Z llvm-tpde` (`-Z llvm-tpde=try` default or `-Z llvm-tpde=only`) **keeps `rustc_codegen_llvm`'s full MIR-to-LLVM-IR lowering intact**. `TpdeWrapper` `dlopen`s `<sysroot>/lib/rustlib/<host>/lib/libtpde-plugin.so` and passes `llvmGetPassPluginInfo` into `LLVMRustWriteOutputFile`. Before constructing LLVM's `PassManager`, `PassWrapper.cpp:527` invokes `plugin.PreCodeGenCallback(*unwrap(M), *unwrap(Target), FileType, BOS)`, calling `tpde_llvm::LLVMCompiler::compile_to_elf(mod, buf)`.
   - *Compile-time and code-quality profile (`docs/tpde-llvm/main.md:3`):** Single-pass linear-scan compilation from LLVM IR directly to ELF `.o` runs **`10x`–`20x` faster** than LLVM's `-O0` backend with comparable `-O0` execution speed and `+10%`–`30%` larger `.text` size.
   - *Constraints and fallback subtlety (`diagnostics.rs:125-136`, `llvm.rs:2413-2456`, `main.md:22-77`):* Rejected with hard diagnostics when LTO (`-C lto=thin|fat`) or split debuginfo (`packed`/`unpacked`) is enabled, and warns at `opt-level > 1`. Bootstrap requires locally built shared LLVM (`llvm.link-shared = true`) and currently sets `-DTPDE_ENABLE_EH=OFF`. Targets are restricted to `x86-64-v1` and `AArch64 (ARMv8.1)` Linux ELF Small-PIC; integers `> i128`, inline assembly, `<N x i1> shufflevector`, vector `getelementptr`, and non-SysV/AAPCS calling conventions fail `compile_to_elf` and—under `LlvmTpde::Try`—fall back seamlessly per CGU to LLVM's backend. Crucially, `compile_to_elf` mutates `llvm::Module` in place (expanding constant expressions inside functions into instruction sequences and rewriting TLS globals to `llvm.threadlocal.address`) *prior* to returning `false` on unsupported constructs (`main.md:22`), so any LLVM fallback path compiles the TPDE-mutated `llvm::Module`.

---

### 4. Cargo Pipelined Compilation Critical-Path Latency (`time-to-.rmeta`) and Parallel Scaling

`Basis: source + execution + derived (compiler/rustc_metadata/src/fs.rs, compiler/rustc_data_structures/src/jobserver.rs, support/compiler_perf_specimen.json)`

#### 4.1 Why Single-Crate `wall-time` Misses Cargo Pipelining (`time-to-.rmeta`)

In a multi-crate Cargo workspace (`rust-lang/cargo@f93c676e3e7ab1aee08dc95d869700f6b99a1a20`), compiling library crate $u$ with `--emit=dep-info,metadata,link` executes frontend analysis and `.rmeta` serialization **before** LLVM optimization and object codegen finish:

1. `encode_and_write_metadata` (`compiler/rustc_metadata/src/fs.rs:60-112`) serializes crate metadata to a temporary file, atomically moves it into `lib<u>.rmeta` via `non_durable_rename` (unlinking any existing destination first on Linux so `ext4`/`btrfs` `auto_da_alloc` heuristics do not trigger a synchronous `fsync` stall, `fs.rs:119-130`), and—when Cargo passes `--json=artifacts`—immediately prints to `stderr` (`fs.rs:101-103`, `json.rs:112-118`):
   ```json
   {"$message_type":"artifact","artifact":".../libstage_a.rmeta","emit":"metadata"}
   ```
2. Cargo's unit-graph scheduler reads that newline-delimited JSON notification at elapsed time $t_{\text{rmeta}}(u)$ and **immediately spawns downstream `rustc` processes** for every dependent crate $v \in \text{succ}(u)$ while crate $u$'s own `rustc` process continues running LLVM module optimization, ThinLocal LTO, and `.rlib` archiving for the remaining $t_{\text{total}}(u) - t_{\text{rmeta}}(u)$.

Consequently, along any dependency chain $u_1 \to u_2 \to \dots \to u_K$ scheduled on $\ge K$ cores, the **unlimited-core pipelined critical-path latency** is governed by $t_{\text{rmeta}}$ on all interior nodes and $t_{\text{total}}$ only on the final sink $u_K$:

$$T_{\text{crit}}(u_1 \to \dots \to u_K) = \sum_{i=1}^{K-1} t_{\text{rmeta}}(u_i) + t_{\text{total}}(u_K) \;\;\ll\;\; T_{\text{seq}} = \sum_{i=1}^{K} t_{\text{total}}(u_i)$$

Defining the metadata-emission fraction $\eta_i = t_{\text{rmeta}}(u_i) / t_{\text{total}}(u_i)$, the asymptotic $K$-stage chain speedup approaches $1 / \eta$ as $K$ grows. **Critical implication for compiler and verification benchmarking:** Any pass added *before* `encode_and_write_metadata` (e.g., synchronous HIR/MIR verification blocking `.rmeta` emission) Penalizes the global critical path $\sum t_{\text{rmeta}}$, whereas any pass executed *after* `.rmeta` emission (e.g., backend optimization, asynchronous MIR/machine-code proof checking, or leaf-stage translation validation) runs off the upstream critical path in parallel with downstream crates!

#### 4.2 Empirical 4-Stage Cargo DAG Pipelining Measurements

Table 4 reports `Probe 3` (`cargo_4_stage_dag_pipelining` in `support/compiler_perf_specimen.json`), instrumenting `cargo build --release -j 4` via a monotonic-clock `RUSTC_WRAPPER` across the 4-crate chain `stage_a -> stage_b -> stage_c -> stage_d` (each containing 32 non-inlined generic compute kernels):

| Crate / Summary Metric | `1.99.1` Start (`ms`) | `1.99.1` `.rmeta` Ready (`ms`) | `1.99.1` Exit (`ms`) | `1.99.1` $t_{\text{rmeta}} / t_{\text{total}}$ ($\eta$) | `1.102.0` Start (`ms`) | `1.102.0` `.rmeta` Ready (`ms`) | `1.102.0` Exit (`ms`) | `1.102.0` $t_{\text{rmeta}} / t_{\text{total}}$ ($\eta$) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `stage_a` | `0.00` | `41.05` | `244.15` | `41.05 / 244.15` (**`16.81%`**) | `0.00` | `49.95` | `257.23` | `49.95 / 257.23` (**`19.42%`**) |
| `stage_b` | `67.90` | `109.78` | `311.71` | `41.88 / 243.81` (**`17.18%`**) | `75.03` | `119.52` | `325.57` | `44.49 / 250.54` (**`17.76%`**) |
| `stage_c` | `141.62` | `184.23` | `392.68` | `42.62 / 251.07` (**`16.98%`**) | `145.01` | `190.02` | `399.00` | `45.00 / 253.99` (**`17.72%`**) |
| `stage_d` | `209.88` | `251.62` | `451.19` | `41.74 / 241.31` (**`17.30%`**) | `215.53` | `261.13` | `469.15` | `45.60 / 253.62` (**`17.98%`**) |
| **Non-pipelined sum $\sum t_{\text{total}}$** | — | — | **`980.34 ms`** | `1.000x` | — | — | **`1,015.39 ms`** | `1.000x` |
| **Theoretical $\sum_{i<4} t_{\text{rmeta}} + t_{\text{total},4}$** | — | — | **`366.86 ms`** | (`+27`–`31 ms`/hop Cargo IPC) | — | — | **`393.06 ms`** | (`+25`–`26 ms`/hop Cargo IPC) |
| **Measured pipelined DAG wall** | — | — | **`451.19 ms`** | **`2.173x` speedup** | — | — | **`469.15 ms`** | **`2.164x` speedup** |

Note the `~25`–`31 ms` gap per hop between `rmeta_ready_offset_ms` of crate $i$ and `start_offset_ms` of crate $i+1$ (`41.05 ms` $\rightarrow$ `67.90 ms`): that delta comprises Cargo JSON artifact parsing, unit-fingerprint file writing, Python wrapper `execve` startup, and `librustc_driver.so` dynamic relocation (`~8 ms`). Even on a 4-crate chain, `stage_d` **starts compiling (`209.88 ms`) before `stage_a` finishes (`244.15 ms`)**, cutting workspace build latency more than in half.

#### 4.3 Intra-Crate Parallelism (`-C codegen-units`, `-Z threads`) and Jobserver Token Sharing

Within a single `rustc` invocation, parallelism operates across two distinct subsystems coordinated with Cargo's GNU Make jobserver (`compiler/rustc_data_structures/src/jobserver.rs:14-149`):

1. **Jobserver non-starvation invariant (`jobserver.rs:39-149`):** Every `rustc` process implicitly holds `1` jobserver token granted by Cargo for its lifetime. `jobserver::Proxy` multiplexes that implicit token plus dynamically requested helper-thread tokens across internal worker threads: when `data.used == 0`, `acquire_thread()` hands the implicit process token to the requesting thread without touching the OS pipe; when `data.used >= 1`, `helper.request_token()` asynchronously reads extra byte tokens from `CARGO_MAKEFLAGS` (`--jobserver-auth=R,W`), and `release_thread()` returns tokens to the pipe only when `data.used > 1` (never releasing the last token so `rustc` cannot deadlock). At exit, `drop_helper_thread()` (`jobserver.rs:145-148`) joins the helper thread so no leaked token starves sibling crates.
2. **Backend CGU partitioning vs. parallel frontend (`Probe 3` on a 96-function, 8-module crate):**

| Intra-Crate Parallel Axis | `rustc 1.99.1` Wall Median (`ms`) | `1.99.1` Speedup | `1.99.1` `max-rss` (`KiB`) | `rustc 1.102.0-nightly` Wall Median (`ms`) | `1.102.0` Speedup | `1.102.0` `max-rss` (`KiB`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `-O3 -C lto=off -C codegen-units=1` | `206.72 ms` | `1.000x` | `129,884` | `210.25 ms` | `1.000x` | `115,496` |
| `-O3 -C lto=off -C codegen-units=4` | `92.76 ms` | **`2.229x`** | `152,916` (`+17.7%`) | `98.07 ms` | **`2.144x`** | `130,772` (`+13.2%`) |
| `-O3 -C lto=off -C codegen-units=16` | `77.28 ms` | **`2.675x`** | `166,392` (`+28.1%`) | `78.00 ms` | **`2.696x`** | `148,428` (`+28.5%`) |
| `Check` (`--emit=metadata`) `-Z threads=1` | `38.19 ms` | `1.000x` | `109,724` | `43.15 ms` | `1.000x` | `92,636` |
| `Check` (`--emit=metadata`) `-Z threads=2` | `46.30 ms` | `0.825x` | `203,216` (`+85.2%`) | `48.03 ms` | `0.898x` | `109,628` (`+18.3%`) |
| `Check` (`--emit=metadata`) `-Z threads=4` | `42.90 ms` | `0.890x` | `207,708` (`+89.3%`) | `35.84 ms` | **`1.204x`** | `114,308` (`+23.4%`) |
| `Check` (`--emit=metadata`) `-Z threads=8` | `41.52 ms` | `0.920x` | `224,532` (`+104.6%`) | `33.26 ms` | **`1.297x`** | `132,384` (`+42.9%`) |

Under Amdahl's Law $S(P) = \bigl((1 - p) + p / P\bigr)^{-1}$, the `-O3 -C lto=off` CGU curve (`1.00x` $\to$ `2.23x` $\to$ `2.68x` at $P = 16$) corresponds to an effective parallel backend fraction $p \approx 0.667$ (`66.7%`, bounded by serial frontend analysis, monomorphization collection, and `.rlib` archiving). Conversely, parallel frontend `-Z threads` incurs Rayon pool initialization and `RwLock`/`Mutex` interner contention that outweighs parallel `typeck` gains at `threads=2` (`0.825x`–`0.898x`) on sub-`50 ms` crates, crossing `1.0x` on `1.102.0-nightly` at `threads=4` (`1.204x`) and `threads=8` (`1.297x`) while cutting per-thread stack/arena RSS bloat in half relative to `1.99.1` (`+42.9%` vs. `+104.6%`).

---

### 5. Compiler Memory Footprint, Dynamic Heap Churn (`DHAT`), and Disk Footprint

`Basis: source + execution + derived (support/probe_compiler_perf_metrics.py, support/compiler_perf_specimen.json)`

#### 5.1 Disentangling Peak RSS Metrics (`wait4` `ru_maxrss` vs. `VmHWM` vs. `statm` vs. `jemalloc`)

Four distinct "memory usage" metrics appear across compiler tooling and cannot be compared interchangeably:

1. **Per-child `wait4(pid, &status, 0, &rusage)` `ru_maxrss` (used in `probe_compiler_perf_metrics.py:87-105`):** Kernel-tracked high-water mark (`mm->hiwater_rss` + anonymous/file pages, reported in **`KiB` on Linux** and **bytes on macOS/BSD**) of that specific child process tree. *Critical harness trap:* Calling `getrusage(RUSAGE_CHILDREN)` inside a multi-run benchmark driver (rather than `wait4` per child or spawning a fresh wrapper process per run as `rustc-fake` does at `rustc-fake.rs:535`) returns the **monotonic maximum across all children reaped since the parent started**, silently masking memory improvements whenever an earlier run had higher RSS.
2. **`/proc/<pid>/status` `VmHWM` vs. `/proc/self/statm` resident pages:** `VmHWM` equals the process's own `hiwater_rss`, whereas `-Z time-passes` (`profiling.rs:994`) reads `/proc/self/statm` instantaneous resident pages only at pass entry/exit—missing transient intra-pass spikes (e.g., `Opt_O3` `rss_end` max is `135.66 MiB` vs. `wait4` `ru_maxrss` `138.04 MiB`) and including ~`70`–`90 MiB` of shared `mmap`ped pages from `librustc_driver-*.so` and `libLLVM.so`.
3. **`jemalloc` `stats.allocated` vs. `stats.resident`:** `stats.allocated` tracks live application-requested heap bytes, whereas `stats.resident` includes allocator metadata, size-class internal fragmentation, thread caches (`tcache`), and unpurged dirty/muzzy pages retained until `dirty_decay_ms` expires.
4. **Monotonic `TyCtxt` Arenas (`rustc_arena::DroplessArena` / `TypedArena`):** HIR nodes, `ty::Ty` interned slices, and MIR bodies cached in `TyCtxt` arenas are never freed individually during compilation; they determine the baseline `At t-gmax` plateau until `TyCtxt` drops after codegen dispatch.

#### 5.2 Dynamic Heap Allocation and Copy Churn (`valgrind --tool=dhat` v2)

`Probe 4` (`probe_4_memory_footprint_and_dhat_churn` in `support/compiler_perf_specimen.json`) profiles `perf_subject` under `valgrind --tool=dhat` (`dhatFileVersion = 2`) in both default `heap` mode and `--mode=copy` (`memcpy`/`memmove` interception):

| `DHAT` Heap / Copy Metric | `1.99.1` `Check` (`heap`) | `1.99.1` `Opt_O2` (`heap`) | `1.99.1` `Check` (`copy`) | `1.102.0` `Check` (`heap`) | `1.102.0` `Opt_O2` (`heap`) | `1.102.0` `Check` (`copy`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| End time `te` (instructions) | `55,508,424` | `289,624,814` | `55,506,707` | `57,632,729` | `291,666,415` | `57,635,755` |
| Peak heap timestamp `tg` (instrs) | `54,491,919` (`98.2%`) | `159,846,975` (`55.2%`) | — | `56,591,325` (`98.2%`) | `87,560,945` (`30.0%`) | — |
| **`Total bytes` allocated / copied** | **`23,834,075 B`** | **`65,613,255 B`** | `4,328,329 B` | **`22,239,417 B`** | **`63,019,716 B`** | `5,328,643 B` |
| **`Total blocks` (`malloc`/`copy` calls)** | `44,363` | `145,653` | `19,973` | `42,242` | `142,002` | `26,283` |
| **`At t-gmax bytes` (live peak heap)** | **`17,553,645 B`** | **`21,863,771 B`** | — | **`15,838,362 B`** | **`18,466,315 B`** | — |
| `At t-gmax blocks` | `15,009` | `24,213` | — | `15,170` | `22,721` | — |
| `At t-end bytes` / `blocks` (unfreed at exit) | `359,277 B` / `275` | `359,877 B` / `282` | — | `352,630 B` / `282` | `353,230 B` / `289` | — |
| Heap `total_bytes_read` / `written` | `22.36 MB` / `11.54 MB` | `165.24 MB` / `51.26 MB` | — | `23.34 MB` / `11.42 MB` | `165.17 MB` / `50.69 MB` | — |
| **Heap churn ratio (`Total / At t-gmax`)** | **`1.358x`** | **`3.001x`** | — | **`1.404x`** | **`3.413x`** | — |
| Mean allocation / copy size (`B`) | `537.25 B` | `450.48 B` | `216.71 B` | `526.48 B` | `443.79 B` | `202.74 B` |

Key findings from the `DHAT` call-stack attribution:
1. **Arena retention in `Check` (`1.36x`–`1.40x` churn, `tg = 98.2%` of `te`) vs. transient C++ DAG churn in `Opt` (`3.00x`–`3.41x` churn):** In `Check` mode, `73.7%` (`17.55 / 23.83 MB`) of all allocated bytes remain live until `98.2%` of execution (`TyCtxt` drop), dominated by `trait_impls_of_provider` (`773`–`816 KB` across `55`–`56` blocks), `MetadataDecodeContext::decode_syntax_context` (`618 KB` on `1.99.1`), and `CtxtInterners::new` `RawTableInner` (`590 KB` single table on `1.102.0-nightly`). When LLVM `-O2` codegen runs, live peak heap grows by only `+2.6`–`+4.3 MB` (`18.47`–`21.86 MB`), while cumulative allocations jump by **`+40.8`–`+41.8 MB`** (`~100,000` short-lived C++ allocations led by `llvm::ScheduleDAGSDNodes::BuildSchedUnits()` at `1.04 MB` / `68`–`69` blocks, `0 B` live at `t-gmax`).
2. **Large stack/context `memmove`s in `--mode=copy`:** `Check` performs `19,973`–`26,283` non-trivial `memcpy`/`memmove` calls (`4.33`–`5.33 MB`), with the two single largest `memmove`s (`121.7 KB` on `1.99.1`, `124.4 KB` on `1.102.0-nightly`) occurring when moving `GlobalCtxt` (`TyCtxt::create_global_ctxt`) into its `OnceLock` slot during compiler initialization!

#### 5.3 IR Volume (`-Z print-type-sizes`, `-Z print-mono-items`) and Disk Artifact Breakdown

On `perf_subject` (`27` monomorphized items on `1.99.1`, `25` on `1.102.0-nightly`; `153` MIR basic blocks across `~3,000` MIR lines; `7` optimized LLVM IR `define`s across `1,077`–`1,080` `.ll` lines; largest layout `DenseMatrix<8, 8>` = `512 B`, `VmState` = `160 B`), on-disk artifacts partition into:
- **Standard outputs (`1.102.0-nightly` `-O2`):** `.rlib` = `48,800 B` (`51,480 B` on `1.99.1`), `.o` = `27,696 B`, `.rmeta` = `19,188 B`, `.bc` = `19,084 B`, `.d` = `708 B`, textual `.mir` = `101,634 B`, textual `.ll` = `128,575 B`.
- **Incremental session directory (`incr/` at `cgu=4`, `894.1 KiB` total on `1.102.0-nightly`):** `dep-graph.bin` = **`522,441 B` (`57.1%`)**, `query-cache.bin` = `78,920 B` (`8.6%`), 4 cached CGU objects `*.o` = `43,992 B` (`4.8%`), 4 pre-LTO bitcode modules `*.pre-lto.bc` = `28,556 B` (`3.1%`), `metadata.rmeta` = `17,083 B`, `work-products.bin` = `413 B`, and `thin-lto-past-keys.bin` = `268 B`. Because `dep-graph.bin` dominates incremental disk I/O (`12.6`–`13.1 ms` `incr_comp_encode_dep_graph_finish` self-time even on `IncrUnchanged`), any verification cache stored alongside `-C incremental` should content-address per-item obligation digests rather than inflating `DepGraph` node arity.

---

### 6. Asymptotic Pathological Scaling and Certifying/Verified-Compiler Metrics Taxonomy

`Basis: execution + derived + source (support/compiler_perf_specimen.json, companion corpus synthesis)`

#### 6.1 Empirical Pathological Scaling Sweeps (`Probe 5`)

Because an empty `pub fn noop() {}` crate already executes a fixed baseline of $\text{Ir}_0 = 16,337,204$ instructions in `Check` (`--emit=metadata`) and $\text{Ir}_0 = 21,646,472$ instructions in `Opt` (`-C opt-level=2 -C codegen-units=1`) to initialize `TyCtxt` and load `libstd`/`libcore` `.rmeta` headers, fitting scaling exponents to raw $\text{Ir}(N)$ underestimates superlinearity on small-to-medium inputs. Subtracting $\text{Ir}_0$ isolates **marginal instructions $\Delta\text{Ir}(N) = \text{Ir}(N) - \text{Ir}_0$** across five pathological axes on `rustc 1.99.1`:

| Pathological Stress Dimension (Mode) | Swept Parameter $N$ | Source Bytes | Native Wall (`ms`) | `max-rss` (`KiB`) | Total `Ir` | Marginal $\Delta\text{Ir} = \text{Ir} - \text{Ir}_0$ | Marginal $\Delta\text{Ir} / N$ | Fitted $\alpha$ ($\Delta\text{Ir} \propto N^\alpha$) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **1. Associated-type projection depth** (`Wrap<...<Base>>`, `Check`) | `8` $\to$ `16` $\to$ `32` $\to$ `64` | `454` $\to$ `1,126` | `22.08` $\to$ `26.72` | `109,820` $\to$ `108,248` | `22.30M` $\to$ `50.62M` | `5.97M` $\to$ `8.14M` $\to$ `14.41M` $\to$ `34.29M` | `745.9k` $\to$ `450.3k` $\to$ **`535.7k`** | `0.839` (`1.250` for $N=32\to 64$) |
| **2. `match` exhaustiveness diagonal matrix** ($N$-tuple `bool`, `Check`) | `4` $\to$ `8` $\to$ `12` $\to$ `16` | `295` $\to$ `1,502` | `20.51` $\to$ `26.57` | `98,232` $\to$ `98,580` | `18.33M` $\to$ `29.07M` | `1.99M` $\to$ `3.45M` $\to$ `6.70M` $\to$ **`12.73M`** | `498.0k` $\to$ `431.6k` $\to$ `558.1k` $\to$ **`795.7k`** | **`1.301`** (**`1.884`** for $N=8\to 16$) |
| **3. Generic monomorphization fanout** (`generic_pipeline::<S_i>`, `Opt`) | `16` $\to$ `64` $\to$ `256` | `1,673` $\to$ `24,374` | `42.77` $\to$ `241.02` | `128,068` $\to$ `138,248` | `98.43M` $\to$ **`1,178.39M`** | `76.78M` $\to$ `326.30M` $\to$ **`1,156.74M`** | `4.80M` $\to$ `5.10M` $\to$ `4.52M` | **`0.978`** (strictly $O(N)$) |
| **4. Single-function CFG branches** (`giant_cfg` `if/else` chain, `Opt`) | `64` $\to$ `256` $\to$ `1,024` | `6,646` $\to$ `109,336` | `49.93` $\to$ **`795.32`** | `128,476` $\to$ `138,888` | `183.86M` $\to$ **`4,809.73M`** | `162.21M` $\to$ `784.03M` $\to$ **`4,788.09M`** | `2.53M` $\to$ `3.06M` $\to$ **`4.68M`** | **`1.221`** (**`1.306`** for $N=256\to 1024$) |
| **5. Declarative `macro_rules!` TT-muncher** (recursive `$($tail:tt)*`, `Check`) | `16` $\to$ `32` $\to$ `64` $\to$ `112` | `223` $\to$ `415` | `19.97` $\to$ `22.15` | `103,624` $\to$ `101,948` | `19.30M` $\to$ `33.42M` | `2.96M` $\to$ `4.86M` $\to$ `9.21M` $\to$ **`17.08M`** | `185.2k` $\to$ `144.0k` $\to$ **`152.5k`** | `0.899` (`1.104` for $N=64\to 112$) |

Diagnostic takeaways for compiler and verifier scaling:
- **Linear inter-procedural monomorphization vs. superlinear intra-procedural CFGs:** Compiling `256` independent monomorphized functions (`monomorphization_fanout`) executes `1.18B Ir` at a nearly constant `4.52M`–`5.10M Ir` per instance ($\alpha = 0.978$). Packing `1,024` sequential diamonds into **one** function (`single_fn_cfg_branches`) inflates marginal per-branch cost by **`+84.6%`** (`2.53M` $\to$ `4.68M Ir/branch`, reaching `4.81B Ir` / `795.3 ms`, $\alpha = 1.306$ at the upper step) as MIR dataflow bitsets and LLVM dominance/register-allocation passes scale superlinearly in basic-block count $B$.
- **Exhaustiveness matrix specialization:** Diagonal wildcard-bool matrices (`match_exhaustiveness_arity`) transition from linear setup overhead at $N \le 8$ (`431.6k Ir/col`) to nearly quadratic growth between $N = 8$ and $N = 16$ (`3.45M` $\to$ `12.73M` $\Delta\text{Ir}$, $\alpha_{8\to 16} = 1.884$) as pattern usefulness specialization splits submatrices.

#### 6.2 Formal Verification and Certifying-Compiler Performance Taxonomy (`10` Orthogonal Metrics)

When evaluating a verified compiler (proof-producing / certifying `rustc`, translation validator, or deductive MIR verifier such as Anneal) against unverified `rustc`, collapsing total elapsed time into a single "slowdown multiplier" confounds **fixed TCB startup overhead**, **per-function untrusted certificate synthesis**, **trusted kernel proof checking**, and **Cargo pipelining behavior**. Every benchmark comparison between verified and unverified compilation must report the following **10 orthogonal verification performance metrics**:

| ID | Metric Symbol & Name | Exact Formula / Operational Definition | Canonical Units & Normalization Denominator | Empirical Anchor & Failure Cliff (Corpus Cross-Reference) |
| :--- | :--- | :--- | :--- | :--- |
| **V1** | **$T_{\text{floor}}$: Fixed Per-Invocation Verification Floor** | Latency of an empty / 1-block verified crate (`nop`), decomposed into driver relocation, lockfile/manifest SHA-256 hashing, header parsing, and TCB environment load. | `ms` (wall and `task-clock:u`) | Uncached source-spawned checker floor is `9,224 ms` (`95.7%` of `scalar` `9,635 ms`); native compiled inspector + precompiled `.olean`s cut floor $>10\times$ (`anneal-verification-pipeline-profiling-and-content-addressed-caching`). |
| **V2** | **$T_{\text{cert-gen}}$ & $\rho_{\text{gen}}$: Certificate / VC Generation Latency** | Untrusted time spent extracting MIR/IR, running abstract interpretation / pass witnesses, and emitting proof scripts or binary certificates; $\rho_{\text{gen}} = T_{\text{cert-gen}} / T_{\text{compile-base}}$. | `ms` and dimensionless ratio $\rho_{\text{gen}}$ | Pure `Runtime(PostCleanup)` MIR extraction + rendering is `0.304 ms` on `apply_endianness` vs. `359.6 ms` whole-crate `tcx.analysis(())`; witness synthesis scales superlinearly if uncompacted. |
| **V3** | **$T_{\text{check}}$ & $\rho_{\text{check}}$: Trusted Proof-Checker / Kernel Replay Time** | Time inside the trusted checker (`lean -j1 -DElab.async=false -Ddebug.skipKernelTC=false` + from-scratch `Kernel.Environment.replay`, or standalone C/Rust proof-certificate validator); $\rho_{\text{check}} = T_{\text{check}} / T_{\text{compile-base}}$. | `ms`, `Ir` (`Cachegrind`), and ratio $\rho_{\text{check}}$ | Report **both** synchronous single-core audit time (`-DElab.async=false -j1`) and parallel elaboration time (`-DElab.async=true -jT`, `2.37x`–`2.58x` faster with byte-identical `.olean` SHA-256). |
| **V4** | **$T_{\text{crit-verif}}$: Pipelined DAG Verification Critical-Path Latency** | Workspace wall time when `.rmeta` is emitted at $t_{\text{rmeta}}$ and $T_{\text{cert-gen}} + T_{\text{check}}$ runs asynchronously alongside downstream Cargo crates (blocking only final `bin`/artifact seal). | `ms` and DAG speedup $T_{\text{seq-verif}} / T_{\text{crit-verif}}$ | Because $\eta = t_{\text{rmeta}} / t_{\text{total}} \approx 0.17\text{--}0.19$ (Section 4.2), decoupling MIR/codegen proof checking from `.rmeta` emission hides up to $(K-1)$ crate-checks off the critical path. |
| **V5** | **$B_{\text{cert}}$: Certificate Byte Density** | Serialized byte size of generated proof terms / `.olean`s / binary translation-validation witnesses, normalized by MIR statements ($B_{\text{cert}} / S_{\text{MIR}}$), machine instructions ($B_{\text{cert}} / I_{\text{mach}}$), and object bytes ($B_{\text{cert}} / B_{\text{obj}}$). | `B / MIR stmt`, `B / mach insn`, and ratio $B_{\text{cert}} / B_{\text{obj}}$ | At $K = 32$ symbolic 128-bit ops, compacting storage markers + dead locals (`R0_RawPostCleanup` $\to$ `R3_MinLocalCompact`) shrinks `.olean` size `2.71x` (`238,176 B` $\to$ `87,832 B`). |
| **V6** | **$|V_{\text{DAG}}|$, $|V_{\text{tree}}|$, & $D_{\text{rec}}$: Proof-Term Sharing and Recursion Depth** | Unique kernel `Expr` DAG nodes $|V_{\text{DAG}}|$, unfolded tree size $|V_{\text{tree}}|$ (sharing ratio $|V_{\text{tree}}| / |V_{\text{DAG}}|$), and maximum kernel WHNF/typechecker recursion depth $D_{\text{rec}}$. | Node counts and depth vs. hard kernel limit (`maxRecDepth = 512`) | `.olean` bytes track $|V_{\text{DAG}}|$, **not** $|V_{\text{tree}}|$: `.nop` lowering (`R1_F1_1b_Nop`) shrinks $|V_{\text{DAG}}|$ (`5,100` $\to$ `3,753`) while inflating $|V_{\text{tree}}|$ (`517,943` $\to$ `579,377`) and hitting `maxRecDepth = 512` (`anneal-mirwp-proof-scaling-normalization-and-f1-checker-overhead`). |
| **V7** | **$M_{\text{check}}$: Peak Checker RSS & Memory Amplification** | Isolated `wait4(2)` `ru_maxrss` (and `DHAT` `At t-gmax`) of the trusted proof checker, plus ratio $M_{\text{check}} / M_{\text{rustc}}$. | `KiB` / `MiB` and ratio $M_{\text{check}} / M_{\text{rustc}}$ | Uncompacted symbolic MIR verification reaches `308`–`671 MB` RSS (`2.2x`–`4.8x` `rustc`'s `138`–`164 MB` RSS), dropping `1.72x` (`179.2 MB`) under dead-local compaction. |
| **V8** | **$H_{\text{proof}}$ & $\beta_{\text{edit}}$: Incremental Proof-Cache Hit Rate & Blast Radius** | Fraction of function obligations satisfied from content-addressed proof cache ($H_{\text{proof}} = N_{\text{hit}} / N_{\text{total}}$) and invalidated fraction $\beta_{\text{edit}} = N_{\text{recheck}} / N_{\text{total}}$ across canonical edit classes (`E1` comment shift, `E2` private leaf, `E3` `#[inline]` helper, `E4` internal `const`, `E5` EOF item append). | Dimensionless `[0, 1]` per edit class | Span-stripped `DefPath`-keyed `PostCleanup` MIR + transitive `Const::Unevaluated` cone achieves **`H_proof = 100%` (`0` invalidations)** on `E1`/`E5` and **`1 / 1,105` (`99.91%` hit rate)** on `serde_json` `E2`/`E3`, vs. `27` symbol diffs post-ThinLTO (`rustc-surgical-edit-mir-invalidation-and-early-cutoff-blast-radius`). |
| **V9** | **$\tau_{\text{norm}}$: Normalization / Pass-Transport Tax** | Ratio $\tau_{\text{norm}} = (T_{\text{transport}} + T_{\text{check-norm}}) / T_{\text{check-raw}}$ when simplifying IR before proving functional/safety VCs. Net speedup requires $\tau_{\text{norm}} < 1 \iff T_{\text{transport}} < T_{\text{check-raw}} - T_{\text{check-norm}}$. | Dimensionless ratio (`< 1.0` = net win, `> 1.0` = net loss) | Naive $O(S \times L)$ kernel `rfl` transport takes `2,882 ms` at $K = 32$, wiping out `2,697 ms` of `R3_MinLocalCompact` proof savings ($\tau_{\text{norm}} = 1.05\times$); requires $O(S)$ indexed or compiled-certificate transport. |
| **V10** | **$\text{TCB}$ & $W_{\text{trusted}}$: Trusted Computing Base & Waiver Surface** | Audited TCB source lines ($\text{SLOC}_{\text{TCB}}$ split into `vetted` vs. `candidate`), stripped TCB binary bytes ($B_{\text{TCB-bin}}$), and trusted waiver density $W_{\text{trusted}} / N_{\text{fn}}$ (`#[anneal::trusted]`, `asm!`, unverified FFI). | `SLOC`, `Bytes`, and waived-function fraction | Prevents trading compile-time speed for silent TCB bloat (e.g., moving unverified optimization passes inside the TCB instead of emitting checkable certificates). |

*(Comparison gate integration:* The compile-time non-inferiority gates in `rustc-benchmark-methodology-and-speed-size-baselines`—$\text{GeoMean}(T_{\text{cand}} / T_{\text{base}}) \le 1.50\times$ without proof checking and $\le 5.00\times$ with end-to-end proof checking—map directly onto $(T_{\text{compile-cand}} + T_{\text{cert-gen}}) / T_{\text{compile-base}} \le 1.50$ and $(T_{\text{compile-cand}} + T_{\text{cert-gen}} + T_{\text{check}}) / T_{\text{compile-base}} \le 5.00$, evaluated under both single-crate `Full` and multi-crate pipelined $T_{\text{crit-verif}}$.)*

## Boundaries

1. **Hardware PMU counters (`instructions:u`, `cycles:u`, `branch-misses:u`) on unvirtualized-PMU KVM guests — unsupported by guest hypervisor:** Although `perf_event_open` with `exclude_kernel = 1, exclude_hv = 1` (`0x1063`) passes Linux's `perf_event_paranoid = 2` permission check without `CAP_PERFMON`, the KVM virtual CPU on the measurement host does not expose architectural PMU counters (`errno = ENOENT`). Hardware PMU behavior is therefore established from `rustc-perf` primary source plus kernel syscall probing (`SW_*` counters succeeding, `HW_*` returning `ENOENT`), while deterministic instruction, cache, and branch counts are measured via `valgrind --tool=cachegrind`.
2. **Live execution of `-Z llvm-tpde` (`libtpde-plugin.so`) — not examined in prebuilt `rustup` toolchains:** Standard `rustup` distributions (`1.99.1` and `1.102.0-nightly`) ship with `llvm.tpde = false` (`bootstrap.example.toml:110`) because `llvm::Tpde` (`src/bootstrap/src/core/build_steps/llvm.rs:2413-2420`) currently panics unless built from source against a locally compiled `llvm.link-shared = true` tree. TPDE's integration seam, ABI constraints, and `10x`–`20x` `-O0` codegen profile are documented from `rust-lang/rust@412be32a6a189d9a28922beee178bc0abee9d492` and `rust-lang/tpde@050927ee81dc11a9e599fa2524ff0eef16daf51a` source and upstream documentation.
3. **Windows ETW (`xperf.exe` / `tracelog.exe`) and macOS `proc_pidinfo` live runs — not examined:** `rustc-fake`'s Windows `XperfStat` / `etw_parser.rs` (`InstructionRetired,TotalCycles:CSWITCH`) and macOS `PROC_PIDTASKINFO` RSS paths are documented from source inspection only; all live executions ran on `x86_64-unknown-linux-gnu`.
4. **Full 69-crate `rustc-perf` suite execution under `Cachegrind` — bounded stop:** Running all `69 benchmarks x 6 profiles x 4 scenarios` under `Cachegrind` (`234x`–`359x` slowdown) would require hundreds of CPU-hours; `support/probe_compiler_perf_metrics.py` instead provides fast, self-contained synthetic probes (`~2.5 minutes` end-to-end) covering every instrumentation interface, wire format, pipelining seam, and scaling law.

## Evidence

### Primary Upstream Sources Inspected

- **`rust-lang/rustc-perf` (`15d95905429e577d5a710b17c49e04b4451c263b`):**
  - `collector/src/benchmark_set/{compile_benchmarks.rs:1-77, mod.rs:232-542}` and `collector/compile-benchmarks/*/perf-config.json`: exact 69-benchmark inventory (`21` `Primary`, `39` `Secondary`, `9` `Stable`; `50` `library`, `19` `binary`) and `Set 0` / `Set 1` target sharding.
  - `collector/src/compile/benchmark/{category.rs:7-50, profile.rs:10-69, scenario.rs:5-32, patch.rs:28-74, target.rs:8-60, codegen_backend.rs:4-25, frontend_threads.rs:4-36, mod.rs:29-450}`: `Profile` (`Check`, `Debug`, `Doc`, `DocJson`, `Opt`, `Clippy`), `Scenario`, and `BenchmarkConfig`.
  - `database/src/metric.rs:8-113`: all `28` `Metric` enum variants and wire names.
  - `collector/src/bin/rustc-fake.rs:20-558` and `collector/src/compile/execute/{mod.rs:33-923, bencher.rs:35-283, profiler.rs:18-460}`: `rustc-fake` determinism env, `--skip-this-rustc`, `EXPECT_ONLY_WRAPPED_RUSTC`, hybrid P-core `taskset`, `15` `Profiler` tools, and `PerfStatSelfProfile` `size:*`-only metric retention.
  - `collector/src/artifact_stats.rs:21-258` and `collector/src/utils/cachegrind.rs:12-116`: `.rlib`/ELF symbol demangling/suffix stripping and `Cachegrind` jemalloc frame collapsing.
  - `site/src/{comparison.rs:346-710, 1190-1560, average.rs:7-79, github/comparison_summary.rs:262-369, request_handlers/dashboard.rs:88-229}` and `site/frontend/src/pages/compare/{data.ts:25-136, compile/aggregations.vue:31-58}`: 30-commit `Q3 + 3*IQR` threshold, `2.0x` noisy-metric factor, `deserves_attention_icount`, and arithmetic-mean summary formulas.
- **`rust-lang/rust` (`412be32a6a189d9a28922beee178bc0abee9d492`, plus live execution of `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_data_structures/src/profiling.rs:104-1007`: `EventFilter` bitmask, `SelfProfiler`, `QueryCacheHitCount` `AtomicU64` vector, `{crate}-{pid:07}.mm_profdata` naming, `JsonTimePassesEntry`, and `/proc/self/statm` RSS sampling.
  - `compiler/rustc_data_structures/src/jobserver.rs:14-149`: `jobserver::Proxy` single-token retention and helper-thread teardown.
  - `compiler/rustc_metadata/src/fs.rs:60-130` and `compiler/rustc_errors/src/json.rs:112-131`: `non_durable_rename`, `--json=artifacts` `"emit":"metadata"`, and `--json=timings` `section_timing` records.
  - `compiler/rustc_session/src/{code_stats.rs:18-175, options.rs:2897, 3035-3045}`: `-Z print-type-sizes`, `-Z time-passes-format`, and `-Z llvm-tpde`.
  - `compiler/rustc_codegen_llvm/src/{llvm/tpde_ffi.rs:1-126, back/llvm_backend.rs:212-235, diagnostics.rs:125-138}`, `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:500-595`, and `src/bootstrap/src/core/build_steps/llvm.rs:2307-2491`: TPDE dynamic loading, `PreCodeGenCallback` bypass, and bootstrap CMake flags.
- **`rust-lang/measureme` (`5ac839c602b59eee9c908b3b35b6d6c0cd1c42f7`, version `12.0.3`):**
  - `measureme/src/{file_header.rs:8-94, serialization.rs:18-235, raw_event.rs:10-195, stringtable.rs:77-329, profiler.rs:26-180, event_id.rs:19-97}`, `decodeme/src/{lib.rs:100-175, stringtable.rs:35-190}`, and `analyzeme/src/analysis.rs:115-366`: `v9` `.mm_profdata` binary container, `RawEvent` 48-bit packing, UTF-8 DAG string table, and reverse-stack self-time analysis.
- **`rust-lang/tpde` (`050927ee81dc11a9e599fa2524ff0eef16daf51a`):**
  - `tpde-llvm/tools/tpde-plugin.cpp:13-42` and `docs/tpde-llvm/main.md:1-77`: `llvmGetPassPluginInfo` callback, supported x86-64/AArch64 ELF subset, and in-place `llvm::Module` constant-expression/TLS rewriting.

### Preserved Package Artifacts (`support/`)

1. `support/probe_compiler_perf_metrics.py`: Standalone, standard-library-only Python 3.11+ measurement and decoding harness executing inside `tempfile.TemporaryDirectory()` (`perf_event_open` syscall `298`, `wait4(2)` isolated `rusage`, `Cachegrind` 13-event + `CEst` parser, pure-Python `measureme` v9 `.mm_profdata` binary decoder, `-Z time-passes` JSON parser, 4-stage Cargo pipelining `RUSTC_WRAPPER`, `-Z threads` / `-C codegen-units` scaling sweeps, `DHAT` v2 JSON analyzer, and 5-axis asymptotic stress sweeps, with automatic path sanitization).
2. `support/compiler_perf_specimen.json` (`105,810` bytes, acquired `2026-11-21`): Complete machine-readable dataset generated by running `support/probe_compiler_perf_metrics.py` against `rustc +1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rustc +nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).

## Revalidation

1. **Validate preserved specimen integrity and key invariants (< 1 second, zero external tools required):**
   ```bash
   python3 -c '
   import json
   d = json.load(open("reports/rustc-compiler-performance-metrics-rustc-perf-self-profile-and-scaling/support/compiler_perf_specimen.json"))
   assert d["schema"] == "rustc-compiler-perf-metrics-specimen/1"
   for tc in ("stable_1_99_1", "nightly_1_102_0"):
       cg = d["probe_1_determinism_perf_and_cachegrind"]["toolchains"][tc]["cachegrind_3_runs"]
       sp = d["probe_2_internal_phases_and_self_profile"][tc]["self_profile_scenarios"]
       pp = d["probe_3_cargo_pipelining_and_parallel_scaling"][tc]["cargo_4_stage_dag_pipelining"]
       assert cg["Ir_cv_pct"] < 0.1, cg
       assert sp["Full"]["format_version"] == 9 and sp["IncrUnchanged"]["event_kind_counts"].get("LLVM Pass", 0) == 0
       assert pp["pipelining_speedup_vs_sequential_sum"] > 2.0, pp
   print("Specimen invariants verified:", list(d["toolchains"].keys()))
   '
   ```
2. **Re-execute the full live 5-probe suite against newer `rustc` toolchains (~2.5 minutes on a multi-core Linux host with `rustup` and `valgrind`):**
   ```bash
   python3 -B reports/rustc-compiler-performance-metrics-rustc-perf-self-profile-and-scaling/support/probe_compiler_perf_metrics.py \
     --stable-selector +stable \
     --nightly-selector +nightly \
     --out /tmp/revalidated_compiler_perf_specimen.json
   ```
3. **Targeted upstream source drift checks (< 5 seconds):**
   - Check whether `measureme` incremented `CURRENT_FILE_FORMAT_VERSION` past `9`: inspect `measureme/src/file_header.rs:8` in the version pinned by `rust-lang/rust` `Cargo.lock`.
   - Check whether `rustc-perf` added `Profile`, `Scenario`, or `Metric` variants: diff `collector/src/compile/benchmark/{profile.rs,scenario.rs}` and `database/src/metric.rs` in `rust-lang/rustc-perf` against `15d95905429e577d5a710b17c49e04b4451c263b`.
   - Check whether `-Z llvm-tpde` graduated from local-shared-LLVM-only (`llvm.rs:2413-2420`) to default CI/dist sysroots: check `bootstrap.example.toml` (`llvm.tpde`) and `compiler/rustc_codegen_llvm/src/llvm/tpde_ffi.rs`.
