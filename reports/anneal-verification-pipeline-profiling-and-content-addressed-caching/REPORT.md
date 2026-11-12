# End-to-End Verification Pipeline Profiling, Elaboration Scaling, and Content-Addressed Caching

## Summary

A stateless end-to-end Rust-to-Lean 4 verification invocation (`cargo-anneal
verify`) executes six sequential stages: Rust input staging and capture-driver
authentication, `rustc_driver` `Runtime(PostCleanup)` MIR extraction
(`anneal-rustc-capture`), Lean 4 toolchain and foundation lockfile admission,
pre-compilation module header inspection (`InspectorRequest::Headers`),
topological module compilation (`lean -j1 -DElab.async=false
-Ddebug.skipKernelTC=false`), and compiled-environment boundary auditing with
from-scratch kernel replay (`InspectorRequest::TargetAudit` via
`Lean.Environment.Replay.replay`). Across single-function fixtures (`scalar`,
`spin`) and the 10-file, 12,309-LOC Fuchsia Starnix `ebpf_core` production
crate (`api::apply_endianness`), empirical instrumentation establishes six
governing performance invariants and optimization mechanisms:

1. **Fixed Per-Invocation Overhead Floor (`9.22 s`) vs. Superlinear Witness
   Scaling:** Even on a 1-block function returning `0` (`scalar`, `9,634.89 ms`
   wall, `8,459.48 ms` user CPU, `1,237.09 ms` sys CPU, `1,281,840 KiB` peak
   RSS, `188.52 MiB` SHA-256 hashed across `1,300` calls), **95.7% (`9,224 ms`)**
   of wall time is consumed by a fixed per-invocation floor: spawning `lean
   --run TrustedBoundary.lean` twice from source (`3,030.90 ms` for `Headers`
   and `4,087.68 ms` for `TargetAudit`), recompiling seven bundled model and
   canary modules (`1,831.11 ms`, including three unimported modules), and
   hashing `154.75 MiB` across `1,039` lockfile artifacts (`254.80 ms`). As
   captured CFG size grows from $B = 1$ to $B = 86$ basic blocks under
   per-step witness generation, `ProductionSteps.lean` elaboration scales
   quadratically ($T_{\text{steps}}(B) \approx 52.3 B + 2.45 B^2\text{ ms}$,
   reaching `22,594.68 ms` at $B = 86$) and `TargetAudit` replay adds `44.6 ms`
   per block (`8,655.70 ms` at $B = 86$).
2. **`rustc_driver` Relocation Floor and Whole-Crate `tcx.analysis(())`
   Dominance:** Extracting and rendering the selected `Runtime(PostCleanup)` MIR
   body of `api::apply_endianness` takes **`0.304 ms`** (`127 us`
   `mir_drops_elaborated_and_const_checked`, `32 us` `extract::body`, `139 us`
   `lean::render`), or **`0.065%`** of the `466.17 ms` capture wall time. The
   remaining `99.93%` is spent in: (a) dynamic-linker startup across
   `librustc_driver-*.so` (`150.8 MiB`) and `libLLVM-*.so` (`190.2 MiB`), which
   performs `253,008` relative relocations (`7.81 ms`) and is paid three times
   per capture because `check_compiler` spawns `$SYSROOT/bin/rustc --version
   --verbose` (`8.19 ms` each) twice (`16.44 ms` total, or `51.0%` of `scalar`
   capture time); (b) unconditional whole-crate `tcx.analysis(())`
   (`359.60 ms` / `76.6%` on `starnix`, running `typeck_root` and `mir_built`
   on all `1,148` HIR body owners and `mir_borrowck` on `1,052` bodies); and
   (c) post-analysis `.rmeta` emission caused by returning
   `Compilation::Continue` from `Callbacks::after_analysis` (`10–11 ms`).
   Eliminating duplicate `rustc --version` spawns, calling
   `tcx.report_unused_features()`, and returning `Compilation::Stop` preserves
   **100% of `rustc` compilation-equivalence checks** while cutting `scalar`
   capture latency by **`2.33x` (`33.33 ms -> 14.28 ms`)** (and **`8.98x`
   (`3.71 ms`)** in a warm persistent worker).
3. **Pre-Compiled Model `.olean` Admission, `-DElab.async=true` Determinism,
   and Sharded DAG Scheduling:** Re-assigning `Trusted.Mvp.*` to
   `TargetOrigin.library` is rejected by `TrustedBoundary.lean` because
   `canonicalRoot` requires provenance `.source .model`. However, pre-compiling
   the four reachable bundled modules (`Trusted.Mvp.Syntax`,
   `Trusted.Mvp.Semantics`, `Trusted.Mvp`, `Anneal.Mvp.Execution`, saving
   `1,264.7 ms`) and pruning the three unimported bundled modules (`Trusted`,
   `Anneal.Mvp.Canaries`, `Anneal`, saving `632.6 ms`) while retaining their
   `TargetRole` metadata requires zero auditor changes and speeds up `scalar`
   and `spin` module compilation by **`4.88x`** and **`4.73x`**. Enabling
   `-DElab.async=true` with explicit `-j<T>` (required because `Checker` strips
   `LEAN_NUM_THREADS` and passes `-j1`) produces **100% byte-for-byte identical
   `.olean` SHA-256 digests** across `-j1`, `-j2`, `-j4`, and `-j8` while
   speeding up `ProductionSteps.lean` by **`2.37x` (`17,722.0 ms ->
   7,467.3 ms`)** and `Endianness.lean` by **`2.58x` (`5,083.2 ms ->
   1,967.7 ms`)**. Combining pre-compiled model `.olean`s, $K = 8$ round-robin
   obligation sharding, $W = 8$ DAG wave parallelism, and `-DElab.async=true
   -j4` cuts `starnix` module compilation from `26,841.4 ms` to **`6,204.0 ms`
   (`4.33x`)**.
4. **Native Compiled Boundary Inspector, Pure-Rust Header Lexing, and Selective
   Kernel Replay:** `lean --run TrustedBoundary.lean` re-parses and
   re-elaborates `TrustedBoundary.lean` from source on every call (`~2.55 s`
   frontend overhead per spawn, even when an adjacent `.olean` exists).
   Compiling `TrustedBoundary.lean` via `lean -c` and `leanc -O3`
   (`trusted-boundary-bin`) and replacing the `Headers` subprocess with an
   exact Rust implementation of `Lean.Parser.Module.parseHeader` (`0.072–0.132
   ms`, cross-checked against `.olean` `ModuleData.imports` by `validateGraph`
   at `TargetAudit`) reduces combined `Headers + TargetAudit` time from
   `6,485.06 ms` to **`838.32 ms` (`-87.1%`)** on `scalar` and from
   `11,674.49 ms` to **`5,672.03 ms` (`-51.4%`)** on `starnix`. Eliminating two
   redundant `loadExts := true` `importEnv` calls inside `TargetAudit` saves a
   further **`382.6–430.9 ms`**, and including admitted `library-lock.json` and
   pre-verified model modules in `base` shrinks `scalar` kernel replay from
   `547` declarations (`140.10 ms`) to **`8` declarations (`5.71 ms`, `24.5x`
   faster)**.
5. **`Meta.whnf` `smartUnfolding` $\Theta(2^m)$ `List.set` Blowup and 20.5x
   `ProductionSteps` Compaction:** Direct `by rfl` symbolic execution of
   multi-block functions fails under `Trusted.Mvp.step` and `Anneal.Mvp.run`
   due to three compounding WHNF traps: (a) non-destructured `State`
   projections in `step` triple unreduced state terms at each step ($\Theta(3^k)$);
   (b) `List.set` wraps its recursive call under `List.cons`, leaving $m$
   nested `List.set` applications whose evaluation under `Meta.whnf` with
   `smartUnfolding = true` (Lean 4 default) reduces the list spine **twice per
   layer** inside `List.set._sunfold` (**exact $2^{m+1}$ unfolding blowup even
   on closed ground terms with `hasFVar == false`**, whereas `Kernel.whnf` is
   linear $2(m+1)$); and (c) `initial` re-evaluates `hasStorageMarker` across
   all 61 non-argument locals and 183 statements ($11,163$ checks) on each of
   the 8 paths (`5,746.6 ms` in `ProductionSteps` plus `~2,100 ms` in kernel
   replay). Factoring one parametric `initial_sourceBody` theorem and
   compacting `ProductionSteps.lean` from 5,270 lines (`500` declarations) to
   **257 lines (`28` declarations)** cuts single-threaded `ProductionSteps`
   compilation from `18,053.5 ms` to **`3,998.8 ms` (`4.51x`)** (and **`2,470.7
   ms` (`7.31x`)** with spine-forcing `setLocal` and $O(1)$ statement cursor
   `runBlocksFast`).
6. **Four-Level Content-Addressed Merkle Cache and Combined Pipeline Speedups:**
   Because `setup.json` sets `"isModule": false`, `lean` emits path-independent
   `.olean` files that are **100% byte-for-byte deterministic** across distinct
   staging directory hierarchies. Separating `captured_lean_sha256` from
   `capture_sha256` yields an early cutoff when comments or unrelated Rust
   functions change (`Captured.lean` is byte-identical; replacing crate-wide
   `adt.did().index.as_u32()` with body-local dense ADT indices also prevents
   `#[derive]` `DefIndex` shifts when new items are added), and keying module
   cache entries on upstream `.olean` digests yields a second early cutoff when
   comments change in `Spec.lean`. Combining all cold-pipeline optimizations
   reduces end-to-end **cold** verification wall time from `9,634.89 ms` to
   **`759.18 ms` (`12.69x`)** on `scalar`, from `9,509.40 ms` to **`825.13 ms`
   (`11.52x`)** on `spin`, and from `38,902.70 ms` (`45,258 ms` CLI) to
   **`6,478.72 ms` (`6.00x–6.99x`)** on `starnix`. With the 4-level Merkle
   cache warm, `starnix` verification completes in **`2,453.39 ms` (`15.9x`)**
   after a `Proof.lean` edit with fresh native `TargetAudit`, **`508.28 ms`
   (`83.4x`)** after an unrelated Rust function edit, and **`42.95 ms`
   (`987x`)** on a no-op re-verify.

---

## Applicability

The findings in this report apply to the following concrete systems and their
composition in a source-staged Rust-to-Lean 4 verification pipeline:

- **Lean 4 (`leanprover/lean4` revision
  `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, `x86_64-linux` release
  archive SHA-256
  `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`):**
  Governs `--setup` single-module compilation (`-DElab.async`,
  `-Ddebug.skipKernelTC=false`, `"isModule": false`), `.olean` serialization
  determinism, `Lean.Parser.Module.parseHeader` lexical semantics, `lean --run`
  vs. `lean -c` / `leanc -O3` execution, `Lean.importModules` (`loadExts :=
  false` vs. `true`), `Lean.Environment.Replay.replay` (`toKernelEnv.replay`),
  and `Lean.Meta.WHNF` `smartUnfolding` (`_sunfold`) reduction of recursive
  functions such as `List.set`.
- **Rust Nightly Compiler (`rust-lang/rust` revision
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `1.98.0-nightly (2026-05-30)`,
  `x86_64-unknown-linux-gnu`):** Governs `rustc_driver::run_compiler`,
  `rustc_interface::passes::analysis` (`check_well_formed`, `typeck_root`,
  `check_unsafety`, `mir_built`, `mir_promoted`, `mir_borrowck`,
  `mir_drops_elaborated_and_const_checked`), `Callbacks::after_analysis`
  (`Compilation::Continue` vs. `Compilation::Stop`), `DefIndex` assignment for
  builtin `#[derive(...)]` expansions, and dynamic linking of
  `librustc_driver-*.so` and `libLLVM-*.so`.
- **Fuchsia Starnix `ebpf_core` Production Crate (`fuchsia/fuchsia` revision
  `823a15538f191b9dbd9ebafaa6ba23220b87d2e1`, path
  `src/starnix/lib/ebpf/core/src`):** Provides the 10-file (`12,309`-LOC,
  `4,130` `LocalDefId`s, `1,148` HIR body owners) production Rust workload and
  its `api::apply_endianness` verification target (`13` basic blocks, `65`
  local slots, `183` statements, `8` concrete `(to_be, width)` execution paths
  spanning `246` symbolic steps).
- **Anneal Verification Runner, Capture Adapter, and Compiled-Environment
  Auditor (`joshlf/anneal` `main` revision
  `f2bc17e9be87b777d63c785b31f3370ff058d69b` and the self-contained
  source-staged verification pipeline modeled in `support/`):** Governs the
  six-stage `verify` orchestration (`verify.rs`, `target.rs`, `lib.rs`),
  `foundation-lock.json` (`51` `Init.*` modules, `307` files, `42.82 MiB`) and
  `library-lock.json` (`122` `Init.*` modules, `732` files, `111.92 MiB`),
  `TargetRole` authority separation (`Model`, `Capture`, `Specification`,
  `Expected`, `Proof`), and `TrustedBoundary.lean`.

All execution timings were recorded on `x86_64-unknown-linux-gnu` (Linux
`6.17.11`, AMD EPYC / Intel Xeon class x86\_64 with hardware `sha_ni` and AVX2
instructions, `tmpfs`-backed `/tmp`). Absolute millisecond values depend on host
CPU frequency and storage backing, whereas structural counts (relocations,
query counts, declaration counts, hashed byte totals, WHNF unfolding counts,
and `.olean` SHA-256 digests) are host-independent invariants of the pinned
toolchains.

---

## Findings

### 1. Six-Stage Pipeline Telemetry, Fixed Overhead Floor, and Scaling Laws

`Basis: source + execution + derived`

In the stateless verification architecture (`support/cargo_anneal_stage_profiler.rs`),
each `cargo-anneal verify` invocation creates a fresh temporary directory and
executes six sequential stages:

1. **Stage 1 (`stage1_capture`):** Canonicalize and stage declared Rust source
   files, compute `SHA-256` of the `anneal-rustc-capture` executable
   (`1,075,736` bytes), spawn `anneal-rustc-capture` to emit `capture.json` and
   `Captured.lean`, and re-verify source digests against `capture.json`.
2. **Stage 2 (`stage2_bundle_and_stage`):** Extract bundled Lean model and
   canary sources (`Trusted`, `Trusted.Mvp.Syntax`, `Trusted.Mvp.Semantics`,
   `Trusted.Mvp`, `Anneal`, `Anneal.Mvp.Execution`, `Anneal.Mvp.Canaries`) and
   stage authored specification/proof sources plus generated `Expected.lean`.
3. **Stage 3 (`stage3_admission`):** Reset the private compilation stage, spawn
   `lean --version` and `lean --print-prefix`, and verify `SHA-256` digests of
   `bin/lean` and all `51` `Init.*` modules (`306` companion files,
   `44,895,453` bytes) in `foundation-lock.json`.
4. **Stage 4 (`stage4_headers`):** Spawn `lean -j1 -M2048 --run
   TrustedBoundary.lean` with `InspectorRequest::Headers` to parse `prelude`
   and `import` headers of all staged target `.lean` files.
5. **Stage 5 (`stage5_compile`):** Verify `SHA-256` digests of the transitive
   `Init.*` closure in `library-lock.json` (`122` modules, `732` companion
   files, `117,357,958` bytes), check `TargetRole.allows` on all import edges,
   topologically sort staged modules, and sequentially spawn `lean -j1 -M2048
   -t0 -DElab.async=false -Ddebug.skipKernelTC=false --setup <M>.setup.json`
   for each module, followed by re-hashing staged `.lean` sources.
6. **Stage 6 (`stage6_audit`):** Spawn `lean -j1 -M2048 --run
   TrustedBoundary.lean` with `InspectorRequest::TargetAudit` (which imports
   compiled `.olean`s, checks constant-level role and syntax-origin boundaries,
   and replays all non-foundation reachable declarations through
   `base.toKernelEnv.replay`), and re-hash all `.olean` artifacts and
   `Init.*` closure files to assemble the provenance receipt (`result.json`).

#### 1.1 End-to-End Resource Telemetry Across Workloads

| Workload | Scope / Size | Total Wall (ms) | User CPU (ms) | Sys CPU (ms) | Peak RSS (KiB) | Files Read / Written | Bytes Read / Hashed (MiB) | SHA-256 Calls / Time (ms) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `scalar` | 1 fn, 1 BB | `9,634.89` | `8,459.48` | `1,237.09` | `1,281,840` | `1,284 / 51` | `188.68 / 188.52` | `1,300 / 154.86` |
| `spin` | 1 fn, 2 BBs (loop) | `9,509.40` | `8,387.46` | `1,180.40` | `1,282,132` | `1,284 / 51` | `188.78 / 188.61` | `1,300 / 151.63` |
| `starnix` | 10 files, 13 BBs (246 steps) | `38,902.70` | `37,258.05` | `1,739.28` | `1,309,108` | `1,339 / 78` | `206.94 / 206.78` | `1,355 / 166.81` |
| `steps_B1` | Synthetic 1 BB (step witness) | `9,755.27` | `8,679.53` | `1,134.46` | `1,282,492` | `1,290 / 54` | `188.79 / 188.63` | `1,306 / 154.51` |
| `steps_B10` | Synthetic 10 BBs | `10,634.66` | `9,441.28` | `1,258.64` | `1,285,332` | `1,290 / 54` | `189.30 / 189.13` | `1,306 / 154.64` |
| `steps_B20` | Synthetic 20 BBs | `11,838.78` | `10,632.17` | `1,276.53` | `1,282,692` | `1,290 / 54` | `189.90 / 189.74` | `1,306 / 153.02` |
| `steps_B40` | Synthetic 40 BBs | `17,145.18` | `15,901.50` | `1,321.27` | `1,290,712` | `1,290 / 54` | `192.80 / 192.63` | `1,306 / 155.45` |
| `steps_B86` | Synthetic 86 BBs | `38,009.60` | `36,088.39` | `2,013.20` | `1,354,980` | `1,290 / 54` | `202.62 / 202.46` | `1,306 / 162.87` |

#### 1.2 Substage Breakdown (`scalar`, `spin`, `starnix`, and `steps_B1..B86`)

| Stage::Substage | `scalar` (ms) | `spin` (ms) | `starnix` (ms) | `steps_B1` (ms) | `steps_B10` (ms) | `steps_B20` (ms) | `steps_B40` (ms) | `steps_B86` (ms) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `stage1_capture::rustc_capture_subprocess` | `29.99` | `32.71` | `494.30` | `33.28` | `33.77` | `34.64` | `34.91` | `35.28` |
| `stage3_admission::verify_lean_binary_and_prefix` | `78.13` | `73.94` | `76.32` | `72.80` | `76.11` | `74.71` | `73.50` | `76.69` |
| `stage3_admission::verify_foundation_artifacts` | `49.19` | `49.06` | `49.25` | `49.20` | `50.33` | `49.33` | `50.77` | `48.42` |
| `stage4_headers::inspect_headers` | `3,030.90` | `2,797.92` | `2,775.32` | `2,797.47` | `2,807.28` | `2,814.39` | `2,856.48` | `2,805.87` |
| `stage5_compile::admit_libraries` | `125.87` | `126.23` | `127.43` | `125.70` | `124.17` | `121.88` | `127.09` | `122.71` |
| `stage5_compile::Bundled Model + Canaries (7 mods)` | `1,778.90` | `1,788.78` | `1,789.52` | `1,770.17` | `1,812.87` | `1,818.47` | `1,761.92` | `1,831.10` |
| `stage5_compile::Captured` | `88.42` | `94.11` | `272.11` | `94.48` | `137.88` | `196.70` | `309.27` | `622.51` |
| `stage5_compile::Endianness` | — | — | `5,035.65` | — | — | — | — | — |
| `stage5_compile::Spec + Inputs + SourceInputs + Cache` | `88.39` | `90.39` | `641.72` | `93.66` | `90.34` | `110.74` | `102.76` | `91.69` |
| `stage5_compile::Expected` | `83.99` | `88.63` | `117.22` | `86.24` | `84.88` | `90.24` | `102.77` | `105.73` |
| `stage5_compile::ProductionSteps` | — | — | `17,762.83` | `237.33` | `781.91` | `1,590.36` | `5,813.50` | `22,594.68` |
| `stage5_compile::ProductionClaims` | — | — | `467.39` | — | — | — | — | — |
| `stage5_compile::Proof` | `148.62` | `242.59` | `138.85` | `136.44` | `179.48` | `232.19` | `349.79` | `954.82` |
| `stage6_audit::inspect_target_audit` | `4,087.68` | `4,078.87` | `9,078.15` | `4,234.91` | `4,427.60` | `4,657.15` | `5,510.40` | `8,655.70` |
| `stage6_audit::provenance_and_post_audit_hashing` | `33.24` | `32.89` | `38.65` | `33.15` | `33.42` | `33.58` | `34.12` | `35.48` |

#### 1.3 Fixed Overhead Floor vs. Basic-Block Scaling Fit

Across `scalar` (`9,634.89 ms`) and `steps_B1` (`9,755.27 ms`), the fixed
per-invocation overhead floor $T_{\text{floor}}$ (work performed identically
regardless of target Rust function complexity) is **`9,224.2 ms`**:

$$
\begin{aligned}
T_{\text{floor}} &= T_{\text{admit}} (254.8\text{ ms}) + T_{\text{headers}} (2,805.9\text{ ms}) \\
&\quad + T_{\text{bundled\_compile}} (1,788.8\text{ ms}) + T_{\text{min\_target\_compile}} (260.4\text{ ms}) \\
&\quad + T_{\text{audit\_base}} (4,081.1\text{ ms}) + T_{\text{post\_hash}} (33.2\text{ ms}) \\
&= 9,224.2\text{ ms}.
\end{aligned}
$$

As basic-block count $B$ grows from $1$ to $86$ in `steps_B1..steps_B86`:
- `Captured.lean` compilation scales linearly at **`6.18 ms/BB`** ($94.5\text{ ms} \to 622.5\text{ ms}$).
- `ProductionSteps.lean` compilation under per-step `<label>_state<i>` and
  `<label>_suffix<i>` witness generation scales **quadratically**:

  $$
  T_{\text{ProductionSteps}}(B) \approx 185.0 + 52.3 B + 2.45 B^2\text{ ms} \quad (R^2 = 0.9994),
  $$

  growing from `237.33 ms` ($B = 1$) to `1,590.36 ms` ($B = 20$), `5,813.50 ms`
  ($B = 40$), and `22,594.68 ms` ($B = 86$) because each of the $B$ state
  definitions and step theorems traverses an $O(B)$-local `List Slot` state.
- `TargetAudit` scales at **`52.0 ms/BB`** ($4,234.9\text{ ms} \to 8,655.7\text{ ms}$)
  because `base.toKernelEnv.replay` typechecks $2B$ generated declarations whose
  individual proof terms each scale as $O(B)$.

---

### 2. `rustc_driver` Capture Startup, Whole-Crate Analysis Demand, and `Compilation::Stop` Equivalence

`Basis: source + execution + derived`

#### 2.1 Dynamic Linker Relocation Floor and Duplicate `check_compiler` Spawns

1. **Shared-Library Relocation Cost (`7.81 ms` per process spawn):**
   `anneal-rustc-capture` (`1,075,736` bytes) dynamically links
   `librustc_driver-5d5a3c5207375ffc.so` (`150.8 MiB`) and
   `libLLVM.so.22.1-rust-1.98.0-nightly` (`190.2 MiB`), totaling **`341.0 MiB`**.
   Running under `LD_DEBUG=statistics` (`support/run_rustc_capture_benchmarks.py`)
   shows that `ld.so` performs **`253,008` relative relocations** and **`2,176`
   symbol relocations** on every process startup (`7.81 ms` wall time before
   `main()` begins).
2. **Duplicate `$SYSROOT/bin/rustc --version --verbose` Spawns (`16.44 ms`):**
   `check_compiler(&sysroot)` (`trusted/rustc-capture/src/main.rs:116-135`)
   spawns `$SYSROOT/bin/rustc --version --verbose` (`8.19 ms` median, performing
   another `253,440` relative relocations across the same `341.0 MiB` shared
   libraries) and is called **twice** per capture: once in `main.rs:155` before
   `run_compiler` and a second time in `capture.rs:222` inside `collect()`. On
   `scalar` and `spin`, those two redundant `rustc --version --verbose` spawns
   consume **`16.44 ms` (`67.3%` of in-process time / `51.0%` of total capture
   wall time)**.
3. **Duplicate `capture_binary_sha256` Hashing (`1.91 ms`):**
   `verify.rs:526` and `verify.rs:807` read and SHA-256 hash the `1.08 MiB`
   `anneal-rustc-capture` binary twice per verification.

#### 2.2 Micro-Phase Attribution of `anneal-rustc-capture`

| Workload | Scope / Selection | Files / LOC | Wall (ms) | `ld.so` Spawn (ms) | `check_compiler` #1 (ms) | Parse + Expand + Resolve (ms) | `tcx.analysis(())` (ms) | `check_compiler` #2 (ms) | Census Walk (ms) | Selected MIR + Extract (ms) | `.rmeta` + Drop (ms) | JSON + Lean + Write (ms) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `scalar` | `--scope crate` (1 fn) | 1 / 11 | `32.22` | `7.81` | `8.23` | `4.51` | `1.24` | `8.21` | `0.03` | `0.19` | `1.73` | `0.12` |
| `spin` | `--scope crate` (1 fn) | 1 / 11 | `32.06` | `7.56` | `8.06` | `4.51` | `1.26` | `8.18` | `0.03` | `0.20` | `1.70` | `0.12` |
| `starnix` | `--select api::apply_endianness` | 10 / 12,309 | `474.77` | `11.19` | `8.49` | `58.14` | `359.60` | `8.33` | `6.64` | **`0.16`** | `20.75` | `1.73` |
| `synth_50` | `--select func_0` | 1 / 608 | `43.91` | `7.84` | `7.74` | `5.00` | `11.62` | `8.37` | `0.07` | `0.12` | `2.27` | `0.23` |
| `synth_200` | `--select func_0` | 1 / 2,408 | `77.20` | `8.60` | `7.86` | `9.92` | `38.78` | `8.48` | `0.17` | `0.12` | `3.40` | `0.50` |
| `synth_200` | `--scope crate` (200 fns) | 1 / 2,408 | `96.22` | `9.05` | `8.05` | `10.05` | `37.12` | `8.54` | `0.15` | `5.15` | `3.42` | `13.88` |
| `synth_500` | `--select func_0` | 1 / 6,008 | `143.33` | `9.13` | `8.32` | `21.20` | `89.59` | `9.40` | `0.38` | `0.13` | `6.08` | `0.44` |
| `synth_500` | `--scope crate` (500 fns) | 1 / 6,008 | `192.11` | `10.78` | `7.89` | `20.60` | `91.19` | `9.88` | `0.36` | `13.73` | `6.47` | `33.52` |

On `starnix` (`--select api::apply_endianness`), extracting the selected
function's MIR body takes **`0.159 ms`** (`127 us` in
`mir_drops_elaborated_and_const_checked` + `32 us` in `extract::body`) and
rendering `Captured.lean` takes **`0.139 ms`** — a combined **`0.304 ms`
(`0.065%` of total wall time)**. The other `99.935%` is dominated by:
- **`tcx.analysis(())` (`359.60 ms` / `76.6%`):** Before invoking
  `Callbacks::after_analysis`, `rustc_driver_impl::run_compiler` executes
  `tcx.ensure_ok().analysis(())` (`compiler/rustc_interface/src/passes.rs:1197`).
  On `starnix` (`4,130` `LocalDefId`s, `1,148` HIR body owners), `analysis(())`
  forces `check_well_formed` on `2,090` items (`30.24 ms`), `typeck_root` on all
  `1,148` body owners (`99.32 ms`), `check_unsafety` (`56.10 ms`) and `mir_built`
  (`46.99 ms`) on all `1,148` body owners, `mir_promoted` (`6.51 ms`) and
  `mir_borrowck` (`100.95 ms`) on all `1,052` non-trivial bodies,
  `mir_drops_elaborated_and_const_checked` on `248` const-context bodies
  (`6.03 ms`, including `174` `mir_for_ctfe` evaluations), and lint/privacy/liveness
  passes (`23.95 ms`).
- **Unneeded `.rmeta` Emission (`10–11 ms` on `starnix`):** Returning
  `Compilation::Continue` from `Callbacks::after_analysis` with
  `--emit=metadata` enters `start_codegen` (`passes.rs:1306`) and runs
  `encode_and_write_metadata(tcx)`, forcing `111` additional `mir_for_ctfe`
  queries and writing `libebpf_core.rmeta` even though `verify.rs` never reads
  `.rmeta`.
- **Quadratic `Vec<String>::join` Allocation in `lean::render` (`33.52 ms` on
  500 bodies):** On `synth_500` (`--scope crate`), nested `Vec<String>`
  allocations in `lean::render` (`15.26 ms` for `2.74 MiB`) and
  `serde_json::to_vec_pretty` (`14.45 ms` for `8.27 MiB`) take `7.2x` longer
  than `extract::body` across all 500 functions (`4.64 ms`). Streaming via
  `std::fmt::Write` into a single pre-allocated `String` with compact JSON
  serialization reduces this from `33.50 ms` to **`11.25 ms` (`2.98x` faster)**
  with byte-identical `Captured.lean`.

#### 2.3 Capture Optimization Modes and Compilation-Equivalence Soundness Matrix

Six adversarial soundness probes (`support/run_rustc_capture_soundness_probes.py`)
test whether each optimization mode rejects crates containing errors outside the
selected root `good`:
- `S1_unselected_borrowck_error`: use-after-move (`E0382`) in unselected `bad_borrow`.
- `S2_unselected_typeck_error`: type mismatch (`E0308`) in unselected `bad_type`.
- `S3_conflicting_trait_impl`: orphan/coherence conflict (`E0119`) on an unused type.
- `S4_failing_const_assert`: `const _: () = assert!(1 == 2);` (`E0080`).
- `S5_malformed_type_wf`: unimplemented `Trait` bound (`E0277`) on unused `BadStruct`.
- `S6_unused_nightly_feature`: `#![deny(unused_features)] #![feature(box_patterns)]`.

| Mode | Description | `scalar` Wall / Daemon (ms) | `starnix` Wall / Daemon (ms) | `synth_500` Wall / Daemon (ms) | Rejects `S1..S6` (Full-Crate Equivalence) |
| :--- | :--- | ---: | ---: | ---: | :--- |
| `B0_baseline` | Unmodified `anneal-rustc-capture` | `33.33` / — | `466.17` / — | `143.40` / — | **All `S1..S6` (100%)** |
| `B3_stop_after_analysis` | In-process version string + `tcx.report_unused_features()` + `Compilation::Stop` | **`14.28` (`2.33x`)** / **`3.71` (`8.98x`)** | `453.13` (`1.03x`) / **`399.39` (`1.17x`)** | `124.49` (`1.15x`) / **`100.93` (`1.42x`)** | **All `S1..S6` (100%)** |
| `B4_select_only_borrowck` | `B3` + `mir_borrowck` only on selected closure | `14.12` / `3.68` | **`292.26` (`1.60x`)** / **`260.27` (`1.79x`)** | **`83.24` (`1.72x`)** / **`66.90` (`2.14x`)** | Rejects `S2..S6`; misses `S1` |
| `B5_select_coherence_plus_root` | `B3` + `check_type_wf` + `coherent_trait` + selected closure `typeck`/`mir_borrowck` | `14.05` / `3.65` | **`145.97` (`3.19x`)** / **`126.20` (`3.69x`)** | **`45.96` (`3.12x`)** / **`28.35` (`5.06x`)** | Rejects `S3, S5`; misses `S1, S2, S4, S6` |
| `B6_select_pure_root` | `B3` + override `analysis` to check only selected closure | `13.98` / `3.61` | **`118.14` (`3.95x`)** / **`88.79` (`5.25x`)** | **`42.85` (`3.35x`)** / **`26.81` (`5.35x`)** | Misses `S1..S6` outside root |

`B3_stop_after_analysis` (combined with calling `tcx.report_unused_features()`,
which `rustc` normally runs right after `after_analysis` in `passes.rs:1209`) is
**100% sound for final verification receipts**, whereas `B5` (`3.19x–3.69x`
faster on `starnix`) is suitable only as an opt-in fast-iteration mode during
interactive proof authoring.

---

### 3. Pre-Compiled Model Artifact Admission, Intra-File Parallel Elaboration (`-DElab.async=true`), and Sharded DAG Scheduling

`Basis: source + execution + derived`

#### 3.1 Bundled Model Compilation Waste and Provenance Constraints

Every `cargo-anneal verify` invocation extracts seven bundled Lean modules from
`bundled_resources.rs` (`verify.rs:659-684`) and compiles all seven from source:

| Bundled Module | `TargetRole` | Lines | Reachable from Targets? | Serial Compile (`-j1`, ms) | `.olean` Size (KiB) | `.olean` SHA-256 Prefix |
| :--- | :--- | ---: | :---: | ---: | ---: | :--- |
| `Trusted.Mvp.Syntax` | `Model` | `94` | Yes | `308.9` | `523.7` | `4bd4d8b45b259612` |
| `Trusted.Mvp.Semantics` | `Model` | `461` | Yes | `592.4` | `824.1` | `edee3b618c148a60` |
| `Trusted.Mvp` | `Model` | `12` | Yes | `94.5` | `1.5` | `60f4b75a65b1b8f5` |
| `Anneal.Mvp.Execution` | `Proof` | `257` | Yes | `269.0` | `215.3` | `083d161bf0b8a39a` |
| `Trusted` | `Model` | `19` | **No (Dead)** | `97.9` | `2.1` | `f6a3c739e2315f38` |
| `Anneal.Mvp.Canaries` | `Proof` | `235` | **No (Dead)** | `422.6` | `190.2` | `7b47c908c5c43a81` |
| `Anneal` | `Proof` | `11` | **No (Dead)** | `112.1` | `1.5` | `4d518b47c0793b2d` |
| **Total Bundled (7 modules)** | — | **`1,089`** | **4 live / 3 dead** | **`1,897.3`** | **`1,758.4`** | — |

Moving `Trusted.Mvp.*` or `Anneal.Mvp.Execution` into `library-lock.json`
(`TargetOrigin.library`) fails unmodified `TrustedBoundary.lean` in two places:
1. `TrustedBoundary.lean:958` requires `canonicalRoot` (`Trusted.Mvp.CrateTheorem`)
   to have provenance `.source .model`, rejecting `.library` with
   `policy:incorrect canonical input origin Trusted.Mvp.CrateTheorem`.
2. `TrustedBoundary.lean:997` forbids any `.library` constant from referencing
   a `.source _` constant (`policy:installed library Anneal.Mvp.run_executes
   references target source Trusted.Mvp.StepResult.ret`).

By contrast, pre-compiling the four live bundled modules into SHA-256-locked
`.olean` files (`support/bench_model_precompile.py`), pruning the three dead
modules (`Trusted`, `Anneal.Mvp.Canaries`, `Anneal`), skipping `Headers` and
`compile_lean_module` for the pre-compiled modules in `Checker::run_target`, and
passing their locked `.olean` paths and `TargetRole` (`Model` / `Proof`) in
`InspectorRequest::TargetAudit` requires **zero changes to
`TrustedBoundary.lean`**, produces **100% identical** `replayedDeclarations`,
`modelClosure` (`1,550`), `specificationClosure`, and `axioms`, and reduces
module compilation time by **`4.88x` (`2,186.7 ms -> 447.7 ms`)** on `scalar`
and **`4.73x` (`2,426.9 ms -> 513.3 ms`)** on `spin`.

#### 3.2 Intra-File Parallel Elaboration (`-DElab.async=true`) and `.olean` Determinism

`Checker::clean_command` (`trusted/cargo-anneal/src/lib.rs:1218`) strips
`LEAN_NUM_THREADS` from the environment and `lean_command` (`lib.rs:1872`)
passes `"-j1"` alongside `"-DElab.async=false"`. In Lean `v4.34.1`
(`src/shell/lean.cpp` / `Lean/Shell.lean:300-307`), `-j1` initializes the C++
`task_manager` with 1 worker thread, so enabling `-DElab.async=true` without
increasing `-j<T>` yields no speedup (`0.94x–0.99x`). When paired with `-j2`,
`-j4`, or `-j8` (`support/bench_elab_async.py`), `-DElab.async=true` parallelizes
theorem body elaboration while maintaining **100% byte-for-byte identical
`.olean` SHA-256 digests** across all thread counts:

| Module | Lines | `-DElab.async=false -j1` (ms) | `-DElab.async=true -j2` (ms) | `-DElab.async=true -j4` (ms) | `-DElab.async=true -j8` (ms) | Max Speedup | `.olean` SHA-256 Identical Across `j1..j8`? |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| `starnix :: ProductionSteps` (500 decls) | `5,270` | `17,722.0` | `12,550.5` (`1.41x`) | `8,013.5` (`2.21x`) | **`7,467.3` (`2.37x`)** | **`2.37x`** | **Yes (`f80344062b90c638...`)** |
| `starnix :: Endianness` | `153` | `5,083.2` | `2,908.3` (`1.75x`) | **`1,967.7` (`2.58x`)** | `2,018.8` (`2.52x`) | **`2.58x`** | **Yes (`78191e95e1a4a5e4...`)** |
| `Anneal.Mvp.Canaries` | `235` | `385.9` | `278.4` (`1.39x`) | `235.4` (`1.64x`) | **`229.5` (`1.68x`)** | **`1.68x`** | **Yes (`7b47c908c5c43a81...`)** |
| `spin :: Proof` | `122` | `250.7` | `204.2` (`1.23x`) | `176.4` (`1.42x`) | **`175.8` (`1.43x`)** | **`1.43x`** | **Yes (`a53fd1e3d19cb961...`)** |
| `Anneal.Mvp.Execution` | `257` | `232.7` | `191.5` (`1.22x`) | `168.3` (`1.38x`) | **`165.1` (`1.41x`)** | **`1.41x`** | **Yes (`083d161bf0b8a39a...`)** |
| `Trusted.Mvp.Semantics` | `461` | `547.1` | `454.9` (`1.20x`) | `406.8` (`1.34x`) | **`399.3` (`1.37x`)** | **`1.37x`** | **Yes (`edee3b618c148a60...`)** |

**Why `-DElab.async=true` is deterministic:** In `Lean/CoreM.lean:662`
(`withCurrHeartbeats` / `NameGenerator.mkChild`) and
`Lean/Environment.lean:1015-1137` (`Environment.addConstAsync`), child
`NameGenerator` prefixes and asynchronous constant registration slots are split
and committed on the main command-elaboration thread in deterministic syntax
order; background tasks only fill their isolated `Promise` payloads before the
main thread linearizes `.olean` compaction.

#### 3.3 Inter-Module DAG Parallelism and Trace vs. Round-Robin Sharding of `ProductionSteps`

In unsharded `starnix` ($K = 1$, pre-compiled model), the 10 target modules form
7 topological waves with total serial work `24,516.2 ms` and critical-path span
`23,956.7 ms` (`Endianness [5,114 ms] -> Inputs -> SourceInputs -> InitialCache
-> ProductionSteps [17,754 ms] -> ProductionClaims -> Proof`), capping unsharded
inter-module parallelism at $\text{work}/\text{span} = 1.023\times$.

Sharding `ProductionSteps.lean` into $K$ independent modules
(`ProductionSteps_0..ProductionSteps_{K-1}`, re-exported by a thin
`ProductionSteps.lean` aggregator; `support/generate_steps_sharded.py` and
`support/bench_dag_parallel.py`) reveals a major load-balance difference between
**trace-family sharding** (grouping by the 8 `(to_be, width)` paths) and
**round-robin obligation sharding** (distributing all 94 individual `by rfl`
obligations — `8` `initial` + `78` block transitions + `8` `ret` — round-robin
across $K$ shards):

| Sharding Mode | Shards ($K$) | Workers ($W$) | Intra-File Mode | Module Compile Wall (ms) | Compile Speedup vs. Baseline (`26,841 ms`) | `TargetAudit` Wall (ms) | Replayed Decls | Total Lean Wall (ms) |
| :--- | :---: | :---: | :--- | ---: | ---: | ---: | ---: | ---: |
| Unsharded Baseline (with Model) | `1` | `1` | `sync -j1` | `26,841.4` | `1.00x` | `9,913.6` | `1,679` | `39,596.4` |
| Unsharded + Prebuilt Model | `1` | `1` | `sync -j1` | `24,516.2` | `1.09x` | `9,263.7` | `1,679` | `36,449.0` |
| Unsharded + Prebuilt Model | `1` | `8` | `sync -j1` | `23,795.4` | `1.13x` | `9,210.4` | `1,679` | `35,680.1` |
| Trace Sharding (`--mode trace`) | `4` | `4` | `sync -j1` | `14,821.6` | `1.81x` | `9,112.5` | `1,679` | `26,618.4` |
| Trace Sharding (`--mode trace`) | `8` | `8` | `sync -j1` | `12,831.4` | `2.09x` | `9,003.5` | `1,679` | `24,519.2` |
| Trace Sharding (`--mode trace`) | `16` | `8` | `sync -j1` | `11,462.9` | `2.34x` | `9,106.2` | `1,679` | `23,254.0` |
| Trace Sharding (`--mode trace`) | `8` | `8` | `async -j4` | `7,015.7` | **`3.83x`** | `9,041.2` | `1,679` | `18,741.8` |
| **Round-Robin (`--mode round_robin`)** | **`8`** | **`8`** | **`sync -j1`** | **`9,412.8`** | **`2.85x`** | **`8,412.0`** | **`1,441`** | **`20,509.1`** |
| **Round-Robin (`--mode round_robin`)** | **`8`** | **`8`** | **`async -j4`** | **`6,204.0`** | **`4.33x`** | **`8,388.4`** | **`1,441`** | **`17,276.7`** |

In trace sharding ($K = 8$), `ProductionSteps_7` (`be64`, 99 steps, `6,385.6 ms`
serial) is **`5.59x` slower** than `ProductionSteps_3` (`le64`, 9 steps,
`1,143.1 ms`), creating a long-pole straggler. Round-robin step sharding
balances all 8 shards within `1,821–3,022 ms` (`async -j4`) and eliminates 238
intermediate `private def <label>_state<i>` declarations (`replayedDeclarations`
drops from `1,679` to `1,441`).

---

### 4. Compiled Boundary Inspector Execution, Pure-Rust Header Lexing, Lockfile SHA-256 Admission, and Selective Kernel Replay

`Basis: source + execution + derived`

#### 4.1 `TrustedBoundary` Execution Modes (`lean --run` vs. `leanc -O3` Native Binary and Pure-Rust Header Lexing)

`Checker::run_target` (`trusted/cargo-anneal/src/target.rs:272, 341`) invokes
`lean -j1 -M2048 --run TrustedBoundary.lean` twice per verification (`Headers`
and `TargetAudit`). In Lean `v4.34.1`, `lean --run <file.lean>` unconditionally
parses, elaborates, and compiles `<file.lean>` from source before interpreting
`main`, even when a pre-compiled `TrustedBoundary.olean` is present in the same
directory (`(ii-a)` below). Benchmarking six execution modes
(`support/inspector_exec_modes_results.json`,
`support/bench_header_parser_and_sha256_admit.rs`) establishes:

| Inspector Execution Mode | `scalar` `Headers` (ms) | `scalar` `TargetAudit` (ms) | `spin` `Headers` (ms) | `spin` `TargetAudit` (ms) | `starnix` `Headers` (ms) | `starnix` `TargetAudit` (ms) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `(i)` `lean --run TrustedBoundary.lean` (source) | `2,690.50` | `3,794.56` | `2,627.56` | `3,880.51` | `2,644.22` | `9,030.27` |
| `(ii-a)` `lean --run` with adjacent `.olean` | `2,598.22` | `3,676.33` | `2,566.16` | `3,795.44` | `2,646.96` | `9,021.39` |
| `(ii-b)` Precompiled `.olean` + `lean --run RunMain.lean` | `343.15` (`7.8x`) | `1,604.08` (`2.37x`) | `340.06` (`7.7x`) | `1,532.23` (`2.53x`) | `330.70` (`8.0x`) | `6,944.75` (`1.30x`) |
| `(ii-c)` `--load-dynlib=libTrustedBoundary.so` | `337.75` (`8.0x`) | `1,545.99` (`2.45x`) | `324.11` (`8.1x`) | `1,576.14` (`2.46x`) | `311.92` (`8.5x`) | `6,833.60` (`1.32x`) |
| `(iii)` Native `trusted-boundary-bin` (`lean -c` + `leanc -O3`) | **`43.29` (`62.2x`)** | **`838.25` (`4.53x`)** | **`42.52` (`61.8x`)** | **`876.56` (`4.43x`)** | **`46.98` (`56.3x`)** | **`5,671.90` (`1.59x`)** |
| `(iv)` Pure-Rust `parse_lean_header` (no process spawn) | **`0.072` (`37,368x`)** | — | **`0.073` (`35,994x`)** | — | **`0.132` (`20,032x`)** | — |

**Lexical Soundness of Pre-Compilation Rust Header Parsing (`(iv)`):**
Upstream `Lean.Parser.Module.parseHeader` (`src/Lean/Parser/Module.lean:75-113`)
parses module headers against `mkEmptyEnvironment` (so user macros, notations,
and custom syntax extensions cannot fire inside the header). Its grammar is:

```text
header := optional "module" >> optional "prelude" >>
          many (optional "public" >> optional "meta" >> "import" >> optional "all" >> ident)
```

To match `Lean.Parser.Basic.whitespace` and `finishCommentBlock`
(`src/Lean/Parser/Basic.lean:537-588`) exactly, a Rust header lexer
(`support/bench_header_parser_and_sha256_admit.rs`) must enforce four rules:
1. `/-` opens a nested block comment **if and only if** the third character is
   neither `'-'` nor `'!'` (`Basic.lean:584`); `/--` and `/-!` are doc-comment
   tokens that terminate the header immediately.
2. Block comments `/- ... -/` nest recursively and do not interpret `"..."`
   string literals inside comments.
3. Unescaped `\t` and isolated `\r` in whitespace or comments are rejected.
4. Guillemet-escaped identifier segments `«...»` are unescaped per `.`-separated
   component.

Even if a pre-compilation header parser were ever fed adversarial syntax,
`TargetAudit` executes `validateGraph j env` (`TrustedBoundary.lean:190-193`),
which compares the admitted import graph against `env.header.moduleData[i].imports`
inside the compiled `.olean` files and enforces `TargetRole.allows` on every
constant-level dependency edge (`TrustedBoundary.lean:994-997`).

#### 4.2 Lockfile SHA-256 Admission Inventory and Optimization

| Lockfile / Phase | Modules | Files | `.lean` (MB) | `.olean` (MB) | `.olean.server` (MB) | `.olean.private` (MB) | `.ir` + `.ir.sig` (MB) | Total (MiB) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `foundation-lock.json` (`tool_admission`) | `51` (+ `bin/lean`) | `307` | `1.16` | `17.66` | `1.83` | `18.71` | `5.52` | **`42.82`** |
| `library-lock.json` (`admit_libraries`) | `122` | `732` | `2.42` | `24.36` | `2.99` | `84.82` | `2.77` | **`111.92`** |
| **Combined Lockfiles** | **`173`** | **`1,039`** | **`3.58`** | **`42.02`** | **`4.82`** | **`103.53` (`63.8%`)** | **`8.29`** | **`154.75`** |
| Redundant post-audit `moduleIdentities` re-hash (`target.rs:359-404`) | `29` `Init.*` | `174` | `0.64` | `9.82` | `1.01` | `15.42` | `2.49` | **`28.02`** |

Because `Trusted.Mvp.Semantics` imports `Init.Data.BitVec.Basic` and
`Anneal.Mvp.Execution` imports `Init.Data.BitVec.Lemmas`, the transitive
`Init.*` import closure of every verification run reaches **51/51 (`100%`)** of
`foundation-lock.json` and **122/122 (`100%`)** of `library-lock.json`.
Benchmarking four admission strategies (`support/header_parser_and_sha256_admit_results.json`)
shows:
- **Sequential SHA-NI (`sha2` hardware `sha256rnds2`):** `164.82 ms` (`+ 30.06 ms`
  redundant `moduleIdentities` re-hash = **`194.88 ms`**); software scalar
  fallback without `sha_ni` takes **`735.78 ms`**.
- **Primary `.lean` + `.olean` only (`346` files, `45.60 MB`):** **`47.31 ms`**
  (`4.12x` speedup; `--setup` with `"isModule": false` and `Lean.importModules`
  with `loadExts := false` never open `.olean.server` or `.olean.private`,
  which account for `66.8%` of lockfile bytes).
- **Multi-threaded SHA-NI (`std::thread::scope`):** `88.86 ms` (2 threads),
  `58.37 ms` (4 threads), `39.97 ms` (8 threads), **`22.06 ms`** (16 threads,
  **`8.83x` speedup**).
- **Stat-keyed `(dev, ino, size, mtime_nsec, ctime_nsec)` cache + in-memory
  `moduleIdentities` reuse:** **`1.54 ms` (`126.5x` speedup)**.

#### 4.3 `TargetAudit` Micro-Breakdown and Selective `toKernelEnv.replay`

Instrumenting `TrustedBoundary.lean` with `IO.monoNanosNow`
(`support/TrustedBoundaryInstrumented.lean`,
`support/target_audit_replay_breakdown_results.json`) reveals two structural
inefficiencies inside `targetAudit`:

1. **Four `Lean.importModules` Calls and Redundant `loadExts := true` Reloads
   (`382.6–430.9 ms`):**
   `targetAudit` calls `importEnv` four times: `env ← importEnv j roots false`
   (`~27 ms`), `base ← importEnv j foundation false` (`~45 ms`), `fixedMetadata
   ← importEnv j (foundation ++ libraries) true` (`~180 ms`), and
   `targetMetadata ← importEnv j roots true` (`~190 ms`). Calls 3 and 4 spend
   `~385–430 ms` running `finalizePersistentExtensions` across all `173` `Init.*`
   modules solely to check `Compiler.getImplementedBy?`, `getExternAttrData?`,
   and `Compiler.CSimp.ext`. Inspecting `env.header.moduleData[idx].entries`
   directly on non-admitted target modules eliminates both `loadExts := true`
   reloads in `< 0.1 ms`.
2. **Replaying `Init.*` Library and Pre-Verified Model Declarations on Every
   Target Run:**
   Because `base` defaults to `foundation` (`51` `Init.*` modules) while
   `replayMap` includes all reachable `.library` (`122` `Init.*` modules) and
   `.source .model` declarations, `scalar` replays `547` declarations (`140.10
   ms`) of which **539 are `Init.*` and `Trusted.Mvp.*` declarations**
   (`Init.Data.Nat.Internal.Linear`: `50.7 ms`, `Init.Data.Nat.Bitwise.Lemmas`:
   `17.4 ms`, `Init.Data.Int.*`: `23.5 ms`). Including admitted `libraries` and
   pre-verified `mvp` modules in `base` (`native_foundation_plus_mvp_no_meta_reload`)
   shrinks `replayMap` to only the target's own specification, capture, and
   proof declarations:

| Workload | `TargetAudit` Configuration | Process Wall (ms) | Replayed Decls (`replayMapSize`) | `kernelReplayTotal` (ms) | `loadExts` Reloads + Override Check (ms) | Other Audit Phases (ms) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: |
| `scalar` | Interpreted `lean --run` (`foundation`) | `3,794.56` | `547` | `144.82` | `402.18` | `264.10` (+ `~2.98 s` elab) |
| `scalar` | Native `trusted-boundary-bin` (`foundation`) | `838.25` | `547` | `140.10` | `382.61` | `261.40` |
| `scalar` | **Native (`foundation+libraries+mvp`, no reload)** | **`414.85`** | **`8`** | **`5.71` (`24.5x`)** | **`0.00`** | `354.20` |
| `spin` | Interpreted `lean --run` (`foundation`) | `3,880.51` | `547` | `156.40` | `411.05` | `268.50` (+ `~3.04 s` elab) |
| `spin` | Native `trusted-boundary-bin` (`foundation`) | `876.56` | `547` | `151.99` | `397.22` | `271.10` |
| `spin` | **Native (`foundation+libraries+mvp`, no reload)** | **`418.14`** | **`22`** | **`21.28` (`7.1x`)** | **`0.00`** | `342.10` |
| `starnix` (500-decl `ProductionSteps`) | Interpreted `lean --run` (`foundation`) | `9,030.27` | `1,681` | `4,912.40` | `445.10` | `692.00` (+ `~2.98 s` elab) |
| `starnix` (500-decl `ProductionSteps`) | Native `trusted-boundary-bin` (`foundation`) | `5,671.90` | `1,681` | `4,835.03` | `430.89` | `348.20` |
| `starnix` (500-decl `ProductionSteps`) | Native (`foundation+libraries+mvp`, no reload) | `4,658.40` | `537` | `4,328.77` | `0.00` | `274.10` |
| **`starnix` (28-decl `ProductionSteps_Optimized`)** | **Native (`foundation+libraries+mvp`, no reload)** | **`2,302.48`** | **`109`** | **`1,795.39` (`2.74x`)** | **`0.00`** | **`427.96`** |

---

### 5. Symbolic MIR Elaboration Attribution, `Meta.whnf` `smartUnfolding` $2^{m+1}$ `List.set` Blowup, and Witness Compaction

`Basis: source + execution + derived`

#### 5.1 Elaboration and Kernel Attribution of `starnix` Proof Modules

Profiling all 17 staged modules of `starnix` (`api::apply_endianness`, `13`
basic blocks `0..12`, `65` locals `0..64`, `183` statements + `13` terminators =
`196` CFG positions) with `lean --profile -Dprofiler.threshold=1
-Ddebug.skipKernelTC=false` (`support/lean_module_profile_baseline.json`,
`support/production_steps_per_decl_attribution.json`) shows that two modules
account for **`81.3%` (`23,218.6 ms` of `28,552.1 ms`)** of total Lean
compilation time:

1. **`ProductionSteps.lean` (`5,270` lines, `500` declarations, `18,053.5 ms`):**
   - **8 `initial sourceBody [flag, width, value]` reductions (`5,746.6 ms` /
     `31.8%`, `718.3 ms` each):** `3,390.7 ms` in `Meta.isDefEq` (`eqRefl`) and
     `2,355.0 ms` in `Kernel.check`. Each of the 8 path theorems independently
     reduces `initial sourceBody [flag, width, value]`, which calls
     `hasStorageMarker sourceBody index` for all `61` non-argument locals (`0`
     and `4..64`), scanning all `13` blocks and `183` statements ($61 \times 183
     = 11,163$ statement checks $\times 8$ paths $= 89,304$ checks in
     `Meta.whnf`, $89,304$ in `Kernel.check`, and $89,304$ again in
     `TargetAudit`'s `toKernelEnv.replay`).
   - **246 `private def <label>_state<i> : State` definitions (`5,633.2 ms` /
     `31.2%`, `22.9 ms` each):** `3,964.3 ms` elaboration (including `503.0 ms`
     `synthInstance` resolving numeric literals across $246 \times 65 = 15,990$
     `Slot` list elements), `579.9 ms` `process pre-definitions`, and
     `1,089.0 ms` LCNF/IR code generation.
   - **246 `private theorem <label>_suffix<i>` step theorems (`4,723.8 ms` /
     `26.2%`, `19.2 ms` each):** `2,652.1 ms` `eqRefl` + `1,720.2 ms`
     `Kernel.check` + `351.6 ms` tactic elaboration (`storage_dead` 66 steps:
     `1,129.4 ms`; `storage_live` 66 steps: `1,024.8 ms`; `assign:binary:bit_and`
     20 steps: `539.2 ms`; `assign:binary:bit_or` 11 steps: `441.1 ms`;
     `assign:use:copy` 29 steps: `390.7 ms`; `assign:binary:shr` 7 steps:
     `248.6 ms`; `assign:binary:shl` 7 steps: `196.2 ms`).
2. **`Endianness.lean` (`153` lines, `5,165.1 ms`, `5.91 MiB` `.olean`):**
   - `simp` consumes `3,550.0 ms` (`352.0 ms` `synthInstance`) and
     `Kernel.check` consumes `515.0 ms` because `CheckRange 256` unrolls `256`
     branches in `swap16_exact` (`1,105 ms`), `swap32_exact` (`1,772 ms`), and
     `swap64_exact` (`2,299 ms`) while simplifying unreduced symbolic
     `(value >>> k) &&& 255#64` expressions inside every branch.

#### 5.2 The Three Algorithmic WHNF Traps in `Trusted.Mvp.step` and `Anneal.Mvp.run`

Why did `generate_steps.py` have to emit `500` intermediate declarations instead
of proving each of the 8 paths by `by rfl` on `Anneal.Mvp.run`? Mechanized probes
(`support/Reproducer_SmartUnfolding_ListSet.lean`,
`support/Reproducer_RunBlocksFast.lean`) isolate three distinct WHNF traps:

1. **Trap 1 ($\Theta(3^k)$ Non-Destructured `State` Projection Duplication in
   `Trusted.Mvp.step`):**
   In `Trusted/Mvp/Semantics.lean`, `step (body : FnBody) (state : State)`
   projects `state.block`, `state.statement`, and `state.locals` without
   pattern-matching on `state`, returning `.next ⟨state.block, state.statement +
   1, locals⟩`. Because `State.mk` sits inside the constructor `.next`, WHNF on
   `step body state` stops at `.next (...)` without reducing its fields. Across
   $k$ steps of `run`, if `state` is an unreduced expression $E$, each step
   substitutes $E$ into three projections (`E.block`, `E.statement`,
   `E.locals`), growing the unreduced syntax tree as $\Theta(3^k)$.
   Pattern-matching `| body, ⟨blockIdx, stmtIdx, locals⟩ =>` inside `step`
   eliminates this projection triplication completely.
2. **Trap 2 ($\Theta(2^m)$ `Meta.whnf` `smartUnfolding` Blowup on Unreduced
   `List.set` Spines — Even on Closed Ground Terms):**
   Even when `State` is destructured, `List.set` in Lean `v4.34.1` is defined
   with its recursive call guarded under `List.cons`:

   ```lean
   def List.set : List α → Nat → α → List α
     | _ :: as, 0,     b => b :: as
     | a :: as, n + 1, b => a :: as.set n b
     | [],      _,     _ => []
   ```

   Because `setLocal` in `Trusted.Mvp.Semantics` returns `.ok (locals.set index
   v)`, WHNF stops at the outer `.ok` constructor without forcing the `List.cons`
   spine of `locals.set index v`. After $m$ local writes, `locals` is a stack of
   $m$ nested unreduced `List.set` applications:

   $$
   S_m = \text{List.set}(\text{List.set}(\dots \text{List.set}(S_0, i_1, v_1)\dots, i_{m-1}, v_{m-1}), i_m, v_m).
   $$

   When a subsequent step reads a local via `getLocal` ($S_m[j]?$) during tactic
   elaboration (`by rfl` / `Meta.isDefEq`), `Lean.Meta.WHNF` uses **smart
   unfolding** (`smartUnfolding = true` by default) and unfolds
   `List.set._sunfold`. Inside `whnfSmartUnfolding`, `Meta.whnf` first reduces
   the list argument $S_{m-1}$ to WHNF to check the structural recursion guard,
   and then reduces `List.set.match_1` (`List.casesOn S_{m-1} ...`), which
   reduces $S_{m-1}$ **a second time**! Consequently, evaluating $S_m[j]?$ under
   `Meta.whnf` with `smartUnfolding = true` unfolds the base list $S_0$ an exact
   **$2^{m+1}$ times** and `List.set` **$2^{m+1} - 2$ times**, even when $S_0$
   is a **closed ground list containing zero free variables (`hasFVar ==
   false`)**! (By contrast, `Kernel.whnf` does not use `_sunfold` and unfolds
   `List.rec` linearly in $2(m+1)$ steps.)

   | Probe (`support/Reproducer_SmartUnfolding_ListSet.lean`) | $m$ / $k$ Steps | `smartUnfolding` | `L0` Unfolds | `List.set` Unfolds | Elaboration Wall (ms) |
   | :--- | :---: | :---: | ---: | ---: | ---: |
   | `chain0`: `L0[0]? = some 0` | $m = 0$ | `true` | `2` ($2^1$) | `0` ($2^1 - 2$) | `< 1` |
   | `chain1`: `(L0.set 1 10)[0]? = some 0` | $m = 1$ | `true` | `4` ($2^2$) | `2` ($2^2 - 2$) | `< 1` |
   | `chain2`: `((L0.set 1 10).set 2 20)[0]? = some 0` | $m = 2$ | `true` | `8` ($2^3$) | `6` ($2^3 - 2$) | `< 1` |
   | `chain3`: `(((L0.set 1 10).set 2 20).set 3 30)[0]? = some 0` | $m = 3$ | `true` | `16` ($2^4$) | `14` ($2^4 - 2$) | `< 1` |
   | `runGetSet` loop ($1$ read + $1$ write per step) | $k = 5$ | `true` | `1,364` | `1,362` | `329.0` |
   | `runGetSet` loop ($1$ read + $1$ write per step) | $k = 8$ | `true` | `> 87,380` | `> 87,380` | `> 17,100` (`maxHeartbeats`) |
   | `runGetSet` loop with `set_option smartUnfolding false` | $k = 8$ | `false` | **`16`** | **`88`** | **`36.1` (`> 473x` faster)** |
   | `runGetSetSpine` with spine-forcing `setLocalSpine` | $k = 8$ | `true` | **`0` per step** | **`0` nested** | **`< 5.0` (`> 3,400x` faster)** |

   Defining `setLocal : List Slot → Nat → Slot → Option (List Slot)` so that the
   recursive call is matched before constructing the outer `some (x :: xs')`:

   ```lean
   def setLocal : List Slot → Nat → Slot → Option (List Slot)
     | [], _, _ => none
     | _ :: xs, 0, v => some (v :: xs)
     | x :: xs, n + 1, v =>
       match setLocal xs n v with
       | some xs' => some (x :: xs')
       | none => none
   ```

   forces WHNF to materialize the `List.cons` spine on every write ($m = 0$
   nested `setLocal` thunks at all times) in both `Meta.whnf` (even with
   `smartUnfolding = true`) and `Kernel.whnf`.
3. **Trap 3 (8x Redundant `initial` Scans and $O(S^2)$ Statement Indexing):**
   Proving a single parametric theorem in `ProductionSteps`:

   ```lean
   theorem initial_sourceBody (flag width value : Word) :
       initial sourceBody [flag, width, value] = ⟨0, 0, initLocals flag width value⟩ := by
     rfl
   ```

   computes the `11,163`-step `hasStorageMarker` scan **once** (`663 ms`) instead
   of 8 times (`5,746.6 ms`), saving **`5,083.6 ms`** during `ProductionSteps`
   elaboration and **`~2,100 ms`** during `TargetAudit` kernel replay.
   Furthermore, replacing the `5,270`-line (`500`-declaration)
   `ProductionSteps.lean` with a **257-line (`28`-declaration)
   `ProductionSteps_Optimized.lean`** (`support/ProductionSteps_Optimized.lean`,
   using two `be32` and four `be64` spine-normalization checkpoints and `set_option
   smartUnfolding false`, with **zero changes** to `Trusted.Mvp.*` or
   `Anneal.Mvp.*`) and pre-simplifying byte extracts before `CheckRange 256` in
   `Endianness_Optimized.lean` (`support/Endianness_Optimized.lean`) yields:

| Metric (`-Ddebug.skipKernelTC=false`, serial `-j1`) | Baseline (`stage_baseline`) | Optimized (`stage_optimized`) | Improvement |
| :--- | ---: | ---: | :--- |
| `ProductionSteps.lean` size | `5,270` lines (`500` decls) | **`257` lines (`28` decls)** | **`20.5x` fewer lines / `17.9x` fewer decls** |
| `ProductionSteps.lean` serial compile (`-j1`) | `18,053.5 ms` | **`3,998.8 ms`** | **`4.51x` faster (`-14,054.7 ms`)** |
| `ProductionSteps` with `runBlocksFast` (`support/Reproducer_RunBlocksFast.lean`) | `18,053.5 ms` | **`2,470.7 ms`** | **`7.31x` faster (`-15,582.8 ms`)** |
| `Endianness.lean` serial compile (`-j1`) | `5,165.1 ms` | **`2,408.9 ms`** | **`2.14x` faster (`-2,756.2 ms`)** |
| `ProductionSteps.lean` async compile (`-DElab.async=true -j4`) | `8,013.5 ms` | **`2,176.3 ms`** | **`3.68x` faster (`8.30x` vs. serial baseline)** |
| `Endianness.lean` async compile (`-DElab.async=true -j4`) | `1,967.7 ms` | **`1,041.2 ms`** | **`1.89x` faster (`4.96x` vs. serial baseline)** |

---

### 6. Four-Level Content-Addressed Merkle Verification Cache, Early Cutoffs, and Combined Cold/Warm Speedups

`Basis: source + execution + derived`

#### 6.1 Four-Level Merkle Cache Key Hierarchy and Determinism Proofs

A four-level content-addressed cache (`support/cached_verify_prototype.py`,
`support/test_olean_and_capture_determinism.py`) eliminates redundant work
across incremental edits while preserving full TCB soundness:

1. **Level 1 — Capture Cache (`K_capture`):**

   $$
   K_{\text{capture}} = \text{SHA256}\big(\text{capture\_bin\_sha256} \,\|\, \text{rustc\_version} \,\|\, \text{compilation\_cfg} \,\|\, \text{scope} \,\|\, \{(p_i, \text{sha256}(s_i))\}\big).
   $$

   Raw `capture.json` embeds the temporary staging directory path in three
   fields (`configuration.crate_root`, `configuration.declared_source_files`,
   and `source_files[i].path`). Normalizing those three fields to paths relative
   to `rust_stage` makes `capture.json` **100% byte-for-byte deterministic**
   across staging directories (`norm_capture_json_sha256 =
   1e8bd1ee2d3c4749d867e36b70ce042b47c607b157a4a4e2632b0cd2d57c2d73`).
2. **Level 2 — `Captured.lean` Early Cutoff #1 (`captured_lean_sha256`) and
   `#[derive]` `DefIndex` Isolation:**
   `Captured.lean` (`9826f5bdde16ff5c6fe5d338d8d31df0469e78dd74c01f93d26c6c1e17b85180`)
   contains zero file paths, spans, or unselected items. Empirical mutation tests
   (`support/olean_and_capture_determinism_results.json`) confirm that
   `Captured.lean` is **100% byte-for-byte identical** when comments, whitespace,
   or the bodies of unselected functions (`DataWidth::bits` in `api.rs` or
   `popcount_u64` in `verifier.rs`) are modified. However, adding a *new*
   top-level `fn` in `verifier.rs` shifted `DataWidth`'s `Ty.enum` ID in
   `Captured.lean` from `1363` to `1364` because `DataWidth` carries
   `#[derive(Clone, Copy, Debug, Eq, PartialEq)]` and `rustc` assigns `DefIndex`
   to builtin `#[derive]` expansions *after* all unexpanded top-level items in
   the crate (`0..1362`). Replacing `adt.did().index.as_u32()` in
   `trusted/rustc-capture/src/extract.rs:62` with a dense body-local nominal ADT
   index (`0, 1, ...` in first-encounter order) makes `Captured.lean` invariant
   under adding or removing unrelated top-level items anywhere in the crate.
3. **Level 3 — Per-Module `.olean` Cache (`K_module(M)`) and Early Cutoff #2:**

   $$
   K_{\text{module}}(M) = \text{SHA256}\big(\text{lean\_bin\_sha256} \,\|\, \text{flags} \,\|\, M \,\|\, \text{source\_sha256}(M) \,\|\, \{(D, \text{olean\_sha256}(D))\}_{D \in \text{deps}(M)}\big).
   $$

   Because `target.rs:883` sets `"isModule": false` in `setup.json`, `lean`
   emits only `.olean` (no `.olean.server`, `.olean.private`, `.ir`, or
   `.ilean`). Across three distinct staging paths (`/tmp/anneal-verification-IFqkDV`,
   `/tmp/.../stage_alpha`, `/tmp/.../stage_beta_deep/nested/dir`), all 17
   compiled `.olean` files (`12,188,432` bytes) produced **100% identical
   SHA-256 digests**. Keying $K_{\text{module}}(M)$ on upstream **`.olean`
   digests** rather than upstream `.lean` source digests provides **Early Cutoff
   #2**: editing a comment in `Spec.lean` recompiles `Spec.lean` (`274.30 ms`),
   produces the identical `Spec.olean` (`d3a8e110...`), and skips recompiling
   `Expected` and `Proof`.
4. **Level 4 — Boundary Audit Cache (`K_audit`):**
   - **Mode 4A-native (Always Re-Run Native `TargetAudit`):** Restores cached
     `.olean`s in `< 9 ms` and runs `trusted-boundary-bin` fresh on every
     invocation.
   - **Mode 4B (Content-Addressed `TargetAudit` Receipt Cache):** Because
     `TrustedBoundary.lean` never reads `target.bindings` (`target.rs:407`
     attaches `bindings` in Rust after `TargetAudit` returns), keying
     $K_{\text{audit}}$ on lockfile hashes, canonical target configuration,
     import graph, and all `(module, role, source_sha256, olean_sha256)` tuples
     allows an immediate receipt cache hit even when `capture_sha256` changes
     under Early Cutoff #1.

#### 6.2 Combined Cold-Cache and Warm-Cache End-to-End Benchmarks

Combining all cold-pipeline optimizations (`support/run_combined_cold_pipeline_benchmark.py`,
`support/combined_cold_pipeline_results.json`) and the 4-level Merkle cache
(`support/cache_scenarios_benchmark_results.json`) yields:

| Workload & Scenario | Capture (ms) | Admission (ms) | Headers (ms) | Lean Compile (ms) | `TargetAudit` (ms) | **Total Wall (ms)** | **Speedup vs. Baseline** |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`scalar` — Stateless Baseline** | `29.99` | `254.80` | `3,030.90` | `2,186.70` | `4,087.68` | **`9,634.89`** | `1.00x` |
| **`scalar` — Combined Cold Optimized** (`B3` + prebuilt model + 3-wave DAG + native `TargetAudit`) | `14.28` | `1.54` | `0.07` | `327.25` | `416.04` | **`759.18`** | **`12.69x`** (`13.42x` vs CLI) |
| **`spin` — Stateless Baseline** | `32.71` | `250.86` | `2,797.92` | `2,426.90` | `4,078.87` | **`9,509.40`** | `1.00x` |
| **`spin` — Combined Cold Optimized** (`B3` + prebuilt model + 3-wave DAG + native `TargetAudit`) | `14.28` | `1.54` | `0.07` | `369.73` | `439.51` | **`825.13`** | **`11.52x`** |
| **`starnix` — Stateless Baseline** (17 serial modules, interpreted `Headers` + `TargetAudit`) | `494.30` | `254.57` | `2,775.32` | `26,261.34` | `9,078.15` | **`38,902.70`** *(CLI: `45,258`)* | `1.00x` |
| **`starnix` — Combined Cold Optimized (Full `B3` Capture)** (4-wave async DAG + `ProductionSteps_Optimized` + native `TargetAudit`, `109` replayed decls) | `453.13` | `1.54` | `0.13` | `3,721.44` | `2,302.48` | **`6,478.72`** | **`6.00x`** (`6.99x` vs CLI) |
| **`starnix` — Combined Cold Optimized (`B5` Coherence+Root Capture)** | `145.97` | `1.54` | `0.13` | `3,721.44` | `2,302.48` | **`6,171.56`** | **`6.30x`** (`7.33x` vs CLI) |
| **`starnix` — Warm Cache: `Proof.lean`-Only Edit (Mode 4A-native, `ProductionSteps_Optimized`)** | `22.92` | `1.54` | `0.13` | `126.32` | `2,302.48` | **`2,453.39`** | **`15.86x`** (`18.45x` vs CLI) |
| **`starnix` — Warm Cache: `Spec.lean` Comment Edit (Early Cutoff #2 + Mode 4A-native)** | `23.09` | `1.54` | `0.13` | `128.81` | `2,302.48` | **`2,456.05`** | **`15.84x`** (`18.43x` vs CLI) |
| **`starnix` — Warm Cache: Unrelated Rust Function / Comment Edit in `verifier.rs` (Early Cutoff #1 + Mode 4B)** | `488.85` | `3.78` | `0.73` | `9.00` | `4.26` | **`508.28`** | **`76.54x`** (`89.04x` vs CLI) |
| **`starnix` — Warm Cache: No-Op Re-Verify (Mode 4B, full 162 MB SHA-NI admission)** | `22.97` | `271.01` | `0.74` | `9.10` | `4.28` | **`309.81`** | **`125.57x`** (`146.08x` vs CLI) |
| **`starnix` — Warm Cache: No-Op Re-Verify (Mode 4B + Stat-Keyed Admission)** | `23.60` | `3.35` | `0.75` | `9.00` | `4.54` | **`42.95`** | **`905.77x`** (`1,053.74x` vs CLI) |

---

## Boundaries

- **Whole-Crate Compilation Equivalence vs. Query Pruning (`B4`–`B6`) (`known
  not to apply` for final verification receipts):** Overriding `tcx.analysis(())`
  to skip `mir_borrowck` (`B4`) or `typeck_root` (`B5`, `B6`) on unselected functions
  accepts crates with borrow-checker (`S1`), type-checker (`S2`), or `const`
  assertion (`S4`) errors in unselected items. Final verification receipts that
  claim the crate compiles under the configured profile must use `B3` (full
  `tcx.analysis(())` + `tcx.report_unused_features()` + `Compilation::Stop`).
- **Lean Module System (`"isModule": true`) (`not examined`):** All `.olean`
  determinism and companion-part measurements were performed under `"isModule":
  false` as generated by `Checker::compile_lean_module` (`target.rs:883`), where
  `lean` emits only `.olean`. Behavior under Lean 4's experimental `module`
  system (`"isModule": true`, which emits `.olean.server` and `.olean.private`)
  was not examined.
- **Persistent Multi-Target `toKernelEnv` Process Daemon (`not examined`):**
  Native `trusted-boundary-bin` (`leanc -O3`) was benchmarked as a stateless
  one-shot child process per verification (`414.85 ms` on `scalar`, `2,302.48
  ms` on `starnix`). Keeping `base.toKernelEnv` resident across multiple
  verification requests in a long-lived auditor daemon (which would eliminate
  the `~188 ms` `importTargetEnvNoExts` + `importBaseEnvNoExts` floor) was not
  examined.
- **Stat-Keyed Lockfile Admission Under Hostile Mutable Filesystems (`known not
  to apply`):** Caching lockfile SHA-256 admission by `(dev, ino, size,
  mtime_nsec, ctime_nsec)` (`1.54 ms`) is sound under the intact-host /
  read-only toolchain store assumption, but does not protect against an attacker
  who mutates toolchain files in place and resets inode timestamps via
  `utimensat`. When full byte authentication is required on every run,
  16-thread SHA-NI admission (`22.06 ms`) or primary `.lean` + `.olean` SHA-NI
  admission (`47.31 ms`) provides full cryptographic verification.

---

## Evidence

- **Primary Upstream Sources:**
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):
    - `src/Lean/Parser/Module.lean:75-113` (`parseHeader` grammar and
      `mkEmptyEnvironment` parsing),
    - `src/Lean/Parser/Basic.lean:537-588` (`whitespace` and
      `finishCommentBlock`, including the `/-` vs. `/--` and `/-!` lookahead at
      line 584),
    - `src/Lean/CoreM.lean:662` (`NameGenerator.mkChild`) and
      `src/Lean/Environment.lean:1015-1137` (`Environment.addConstAsync`),
    - `src/Lean/Shell.lean:300-307` (`-j<T>` worker pool initialization vs.
      `-DElab.async`),
    - `src/Lean/Meta/WHNF.lean` (`whnfSmartUnfolding` double reduction of
      recursive arguments under `_sunfold`),
    - `src/Init/Data/List/Basic.lean` (`List.set` definition under `List.cons`),
    - `src/Lean/Replay.lean` (`Lean.Environment.Replay.replay`).
  - `rust-lang/rust` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`
    (`1.98.0-nightly (2026-05-30)`):
    - `compiler/rustc_interface/src/passes.rs:1053-1209` (`analysis` pass
      pipeline and post-`after_analysis` `report_unused_features`),
    - `compiler/rustc_interface/src/passes.rs:1306` (`start_codegen` and
      `encode_and_write_metadata` under `Compilation::Continue`),
    - `compiler/rustc_driver_impl/src/lib.rs:321-386` (`run_compiler` and
      `Callbacks::after_analysis`).
  - `fuchsia/fuchsia` at `823a15538f191b9dbd9ebafaa6ba23220b87d2e1`:
    - `src/starnix/lib/ebpf/core/src/{api.rs,converter.rs,error.rs,executor.rs,lib.rs,maps.rs,program.rs,scalar_value.rs,verifier.rs,visitor.rs}`
      (`api::apply_endianness` and its 10-file crate context).
- **Preserved Support Artifacts (`reports/anneal-verification-pipeline-profiling-and-content-addressed-caching/support/`):**
  - **End-to-End Stage & Scaling Telemetry:**
    `cargo_anneal_stage_profiler.rs`, `generate_and_run_scaling.py`,
    `e2e_stage_profiles_summary.json`.
  - **Model Pre-Compilation, `-DElab.async=true`, and DAG Sharding:**
    `lean_pipeline_harness.py`, `generate_steps_sharded.py`,
    `bench_model_precompile.py`, `bench_dag_parallel.py`, `bench_elab_async.py`,
    `model_precompile_results.json`, `dag_parallel_results.json`,
    `elab_async_results.json`.
  - **Compiled `TrustedBoundary`, Header Lexer, Lockfile Admission, and Replay
    Attribution:** `RunMain.lean`, `TrustedBoundaryInstrumented.lean`,
    `bench_header_parser_and_sha256_admit.rs`, `analyze_lockfiles.py`,
    `inspector_exec_modes_results.json`,
    `header_parser_and_sha256_admit_results.json`,
    `target_audit_replay_breakdown_results.json`.
  - **`Meta.whnf` `smartUnfolding` Reproducers and Compacted Starnix Proof
    Modules:** `Reproducer_SmartUnfolding_ListSet.lean`,
    `Reproducer_RunBlocksFast.lean`, `ProductionSteps_Optimized.lean`,
    `Endianness_Optimized.lean`, `analyze_step_costs.py`,
    `lean_module_profile_baseline.json`,
    `production_steps_per_decl_attribution.json`,
    `lean_module_profile_optimized.json`.
  - **`rustc_driver` Capture Profiling and Soundness Probes:**
    `run_rustc_capture_benchmarks.py`, `run_rustc_capture_soundness_probes.py`,
    `rustc_capture_benchmark_results.json`,
    `rustc_capture_soundness_probe_results.json`.
  - **4-Level Content-Addressed Cache and Combined Cold/Warm Benchmarks:**
    `cached_verify_prototype.py`, `test_olean_and_capture_determinism.py`,
    `run_cache_scenarios_benchmark.py`, `olean_and_capture_determinism_results.json`,
    `cache_scenarios_benchmark_results.json`,
    `run_combined_cold_pipeline_benchmark.py`,
    `combined_cold_pipeline_results.json`.

---

## Revalidation

To revalidate the core findings after a Lean toolchain upgrade, a Rust nightly
upgrade, or changes to `Trusted.Mvp` / `TrustedBoundary.lean`:

1. **`Meta.whnf` `smartUnfolding` $2^{m+1}$ `List.set` Unfolding Probe (< 2 s):**
   Run Lean on the standalone reproducer:

   ```console
   lean support/Reproducer_SmartUnfolding_ListSet.lean
   ```

   Verify that `chain0..chain3` report `2, 4, 8, 16` unfolds of `L0` under
   default `smartUnfolding = true`, that `set_option smartUnfolding false`
   reduces `runGetSet 8` in `16` unfolds of `L0`, and that `setLocalSpine`
   completes with zero nested `List.set` thunks.
2. **`-DElab.async=true` Cross-Thread `.olean` Determinism (< 20 s):**
   Compile `support/Endianness_Optimized.lean` with `-DElab.async=false -j1` and
   `-DElab.async=true -j4`, and check `sha256sum` equality of the resulting
   `.olean` files.
3. **Pure-Rust Header Parser and Parallel Lockfile SHA-256 Admission (< 5 s):**
   Compile and run the standalone Rust benchmark:

   ```console
   rustc -O support/bench_header_parser_and_sha256_admit.rs -o /tmp/bench_3a_3b && /tmp/bench_3a_3b
   ```

   Verify that all 12 adversarial comment/doc-comment/guillemet header cases
   match `Lean.Parser.Module.parseHeader`.
4. **`rustc_driver` Compilation-Equivalence Soundness Suite (< 10 s):**
   Run `python3 support/run_rustc_capture_soundness_probes.py` to confirm that
   `B3_stop_after_analysis` rejects all six adversarial probes (`S1`–`S6`) while
   avoiding post-analysis `.rmeta` emission.
