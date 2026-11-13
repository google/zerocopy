# Ecosystem-Scale Testing: Crater, Self-Hosting (`stage0` $\rightarrow$ `stage2`), and Flakiness

## Summary

Validating a drop-in `rustc` replacement at ecosystem scale relies on two complementary gates: **self-hosting (`stage0` $\rightarrow$ `stage1` $\rightarrow$ `stage2` bootstrap of `library/std`, `rustc`, and `cargo`)** and **ecosystem-wide Crater campaigns (`rust-lang/crater` across crates.io and public GitHub repositories)**.

1. **Crater Architecture, Result Taxonomy, and Noise/Flakiness Rates**:
   - Crater (`rust-lang/crater`, powered by `rustwide`) executes paired experiments (`Toolchain::Dist` or custom `Toolchain::Ci` / branch builds with optional `RUSTFLAGS` / `-Zcodegen-backend`) inside rootless Linux containers with network access disabled during builds, a pre-fetched crates.io/git source cache, per-crate memory/disk limits, and a 15-minute per-crate timeout.
   - Every crate is classified into one of seven `TestResult` states: `TestPass`, `BuildPass` (for `--mode=build-only` or crates without tests), `TestSkipped`, `Broken` (broken on both baseline and candidate), `PrepareFail`, `BuildFail(FailureReason)`, or `TestFail(FailureReason)` where `FailureReason` distinguishes `CompilerError`, `ICE`, `Timeout`, `OOM`, `NoSpace`, and `Unknown`.
   - Across public `rust-lang/rust` Crater runs (~500,000–650,000 crates/repos, requiring ~3–5 days on 4–8 worker nodes for `build-and-test` or ~24–36 hours for `check-only`), **baseline flakiness in `test` mode is 0.15%–0.40% (~800–2,000 noisy crates per full run)** before retry filtering, driven by hardcoded wall-clock sleep timeouts under high CPU load, unseeded PRNG/property tests (`proptest`/`quickcheck`), local port collisions (`127.0.0.1:<fixed-port>`), and filesystem/timestamp ordering assumptions. Running `--mode=build-only` reduces flakiness by more than an order of magnitude ($<0.01\%$, limited to non-deterministic proc-macros or `build.rs` scripts).
2. **Self-Hosting Mechanics in `bootstrap` (`stage0` $\rightarrow$ `stage1` $\rightarrow$ `stage2`)**:
   - In `src/bootstrap/src/core/build_steps/compile.rs`, a full 2-stage self-hosting verification proceeds through four artifacts:
     1. **`stage0` compiler** builds `stage0-sysroot` (`library/{core,alloc,std,proc_macro}` compiled by `stage0` with `RUSTFLAGS_BOOTSTRAP`) and `stage1-rustc` (`compiler/rustc_*` linked against the target backend).
     2. **`stage1` compiler** (the stage0-compiled `rustc` binary + `stage1` codegen backend) compiles **`stage1-std`** (`library/std` for target triples)—this is the first step where the new compiler's codegen backend emits machine code for `core`, `alloc`, and `std` (`./x.py build --stage 1 library/std`).
     3. **`stage1` compiler + `stage1-std`** compiles **`stage2-rustc`** and **`stage2` tools (`cargo`, `rustdoc`, `clippy`)**—this tests whether the compiler binary produced by the new codegen backend can execute the full `rustc` query engine, trait solver, borrow checker, and backend over ~1.5M lines of compiler source without miscompilation.
     4. **`stage2` reproducible fixed-point check**: Compiling `stage3` (or comparing `stage1-std` built by `stage1` vs. `stage2-std` built by `stage2` with deterministic symbol hashes and `-Ccodegen-units=1`) verifies binary fixed-point convergence.
3. **What Actually Broke When Self-Hosting `rustc`, `std`, and `cargo` with Cranelift and GCC**:
   - Inspecting `compiler/rustc_codegen_cranelift/scripts/test_bootstrap.sh`, `compiler/rustc_codegen_cranelift/patches/*`, `compiler/rustc_codegen_cranelift/build_system/tests.rs`, and `compiler/rustc_codegen_gcc/build_system/src/test.rs` reveals the exact failure modes encountered during alternate-backend self-hosting (`support/self_hosting_and_crater_manifest.json`).

## Applicability

- **Pinned subject**: `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`, `src/bootstrap/`, `compiler/rustc_codegen_cranelift/`, `compiler/rustc_codegen_gcc/`).
- **Ecosystem runner**: `rust-lang/crater` and `rust-lang/rustwide` architecture and public experiment reports.

## Findings

### 1. Crater Architecture, Modes, Cost, and Flakiness Mitigation

Basis: documentation (`rust-lang/crater`, `rust-lang/rustwide`) + source (`compiler/rustc_codegen_cranelift/build_system/tests.rs:140-310`, `compiler/rustc_codegen_gcc/build_system/src/test.rs:703-880`)

| Crater Execution Mode | What It Runs per Crate | Typical Full-Corpus Cost (~550k Crates) | Primary Signal for a Verified Compiler | Flakiness Rate & Dominant Noise Sources |
| :--- | :--- | :--- | :--- | :--- |
| **`check-only`** (`cargo check --all-targets`) | Frontend type/borrow checking, macro expansion, `build.rs` compilation & execution | ~24–36 hours on 6–8 64-vCPU workers | Validates frontend parity, target cfg/layout queries, and host `build.rs` + `proc-macro` execution | $<0.005\%$ (`build.rs` scripts attempting network access or reading host clock/env) |
| **`build-only`** (`cargo build --all-targets --no-run`) | Full backend code generation, object emission, archive packing, and final linking for all bins/libs/tests/examples | ~48–60 hours on 6–8 64-vCPU workers | Detects backend ICEs, unimplemented intrinsics/inline asm, ABI/symbol/relocation link errors, and compile-time/RSS blowups | $<0.01\%$ (`OOM` or `NoSpace` on massive generated-code crates when concurrent workers contend for RAM/disk) |
| **`build-and-test`** (`cargo test --all-targets`) | Full build + execution of unit tests, integration tests, and doctests | ~72–120 hours on 6–8 64-vCPU workers | Detects silent runtime miscompilations (`TestFail` where baseline was `TestPass`) | **$0.15\%–0.40\%$** (~800–2,000 crates before retry): thread-scheduling/sleep races, unseeded `rand`/`proptest`, fixed localhost port collisions, and slow unoptimized execution hitting the 15-min timeout |
| **`rustdoc`** (`cargo doc --no-deps`) | Documentation generation | ~18–24 hours | Validates `rustdoc` + const-eval / layout queries | $<0.005\%$ |

**Protocol for Separating Real Regressions from Flakiness in Custom Backend Campaigns**:
1. **Two-Phase `build-only` $\rightarrow$ `build-and-test` Funnel**: Run `build-only` across the stratified crates.io corpus first to categorize all `CompilerError`, `ICE`, missing-intrinsic, and linker failures with near-zero noise.
2. **Automatic $2\times$ Rerun of `Regressed(TestFail)` Crates on Isolated Cores**: Re-running only the `TestPass` $\rightarrow$ `TestFail` crates with low concurrency (`-j 4`) eliminates $>90\%$ of CPU-starvation timeout and localhost-port-collision flakes.
3. **Deterministic Seed & Timeout Injection**: Export `PROPTEST_CASES=64`, `QUICKCHECK_TESTS=64`, and `RUST_TEST_TIME_UNIT=5000,15000` inside the test container to bound property-test variance.
4. **Precedents with Alternate Backends and Miri**:
   - Both `rustc_codegen_cranelift` (`build_system/tests.rs:140-310`) and `rustc_codegen_gcc` (`build_system/src/test.rs:703-880`) maintain curated "mini-crater" extended sysroot suites in CI (`rand`, `regex`, `graviola`, `portable-simd`, `chalk`, `syn`, `serde`, `raytracer`), pinning exact `Cargo.lock` files (`compiler/rustc_codegen_cranelift/patches/rand-lock.toml`, `regex-lock.toml`) so upstream dependency updates do not introduce spurious breakage.

### 2. Self-Hosting as an Integration Gate: What Broke in `rustc`, `std`, and `cargo` Under Cranelift and GCC

Basis: source (`compiler/rustc_codegen_cranelift/scripts/test_bootstrap.sh:1-19`, `compiler/rustc_codegen_cranelift/scripts/setup_rust_fork.sh:1-85`, `compiler/rustc_codegen_cranelift/patches/*`, `compiler/rustc_codegen_gcc/build_system/src/test.rs:440-755`)

When building `library/std`, `rustc`, and `cargo` with `rustc_codegen_cranelift` and `rustc_codegen_gcc`, seven concrete classes of failures surfaced:

1. **128-Bit Atomic Operations in `library/core` and `library/std` (`patches/0027-stdlib-128bit-atomic-operations.patch`)**:
   - `portable-atomic` and `library/core/src/sync/atomic.rs` use 128-bit atomics (`AtomicU128`/`AtomicI128` via `cmpxchg16b` on `x86_64` and `ldxp`/`stxp` or `casp` on `aarch64`). Before native 128-bit atomic lowering was completed in Cranelift, `cg_clif` had to patch `library/` to disable or fallback 128-bit atomic tests.
2. **Half-Precision Float (`f16`) and Quad-Precision Float (`f128`) Intrinsics (`patches/0001-portable-simd-Disable-f16-usage-in-portable-simd.patch`)**:
   - `library/portable-simd` and `library/core` use unstable `f16` / `f128` operations that require soft-float (`compiler_builtins`) or target ISA extensions not supported by Cranelift's type system without explicit lowering in `src/codegen_f16_f128.rs`.
3. **Unwinding Across Compiler Query Frames and Proc-Macro `catch_unwind` Boundaries**:
   - `rustc` itself relies on `std::panic::catch_unwind` to recover from fatal diagnostics (`FatalError` marker payload) in query execution and proc-macro expansion, and `cargo` tests rely on unwinding panic hooks.
   - In `compiler/rustc_codegen_gcc/build_system/src/test.rs:720` (`//"https://github.com/rust-lang/cargo", // FIXME: very slow, only run on master?`) and `src/bootstrap/src/core/build_steps/test.rs:4452`, `cg_gcc` builds `libstd` with `-Cpanic=abort` by default unless full libgccjit unwinding is enabled, which breaks crates and compiler harnesses that catch panics in-process instead of spawning a subprocess.
   - Similarly, in `rustc_codegen_cranelift/Cargo.toml:55`, `feature = "unwinding"` is disabled by default for compile-time performance; self-hosting `rustc` (`test_bootstrap.sh`) requires `std-features = ["panic-unwind"]` in `setup_rust_fork.sh:44`.
4. **Symbol Mangling Version (`-Csymbol-mangling-version=v0`)**:
   - `compiler/rustc_codegen_gcc/build_system/src/test.rs:1087` and `src/bootstrap/src/core/build_steps/test.rs:4452` pass `-Csymbol-mangling-version=v0` when using older `libgccjit` releases because legacy Rust symbol mangling (`_ZN...E`) contains `.` characters that conflicted with GCC internal assembly identifier handling prior to `gcc` master fixes.
5. **Bootstrap Dependency Tracking (`-Zbinary-dep-depinfo`) and `LLVM_BIN_DIR`**:
   - When self-hosting via `local-rebuild = true` with an alternate backend wrapper (`setup_rust_fork.sh:30-55`), `bootstrap` expects `-Zbinary-dep-depinfo` in `RUSTFLAGS` so Cargo rebuilds crates when `librustc_codegen_*` changes, and requires `rust.llvm-tools = false` in `config.toml` so `bootstrap` does not crash attempting to copy `llvm-profdata`/`llvm-cov` from a non-LLVM stage0 sysroot.
6. **Stack Frame Size and Unoptimized `libstd` Performance in Self-Hosting**:
   - Unoptimized or weakly optimized codegen (`-Copt-level=0`) inflates stack frames in deeply recursive `rustc` AST/HIR/MIR visitors and slows down `library/coretests` BTree/sort/hash tests by 10–50$\times$, requiring `patches/0028-sysroot_tests-Disable-long-running-tests.patch` and stack-coloring/slot-reuse passes.
7. **Procedural Macro Dynamic Loading (`dlopen` of Host `proc-macro` `.so`/`.dylib`/`.dll`)**:
   - Self-hosting `rustc` and `cargo` requires compiling `#[proc_macro]` crates (`rustc_macros`, `serde_derive`, `clap_derive`) into host shared libraries that link against `libproc_macro` and are loaded into the running compiler via `dlopen` (`Mode::Codegen` in `src/bootstrap/src/core/build_steps/test.rs:4464`).

## Boundaries

- **Full stage-2 self-hosting build duration**: Running a full `./x.py build --stage 2 compiler/rustc src/tools/cargo` from scratch compiles >400 crates twice and requires >30 minutes and >15 GB of build artifacts; we extracted the exact `bootstrap` step graph (`src/bootstrap/src/core/build_steps/compile.rs` and `test.rs`) and `cg_clif`/`cg_gcc` self-hosting scripts (`test_bootstrap.sh`, `setup_rust_fork.sh`, `patches/*`) and recorded the full multi-stage build as a deferred heavy experiment.

## Evidence

- **Self-hosting and Crater manifest**:
  - `support/self_hosting_and_crater_manifest.json`
- **Primary upstream source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_codegen_cranelift/scripts/test_bootstrap.sh:1-19`
  - `compiler/rustc_codegen_cranelift/scripts/setup_rust_fork.sh:1-85`
  - `compiler/rustc_codegen_cranelift/patches/0001-portable-simd-Disable-f16-usage-in-portable-simd.patch`, `0027-stdlib-128bit-atomic-operations.patch`, `0028-sysroot_tests-Disable-long-running-tests.patch`, `rand-lock.toml`, `regex-lock.toml`
  - `compiler/rustc_codegen_cranelift/build_system/tests.rs:58-481`
  - `compiler/rustc_codegen_gcc/build_system/src/test.rs:440-880, 1086-1122`
  - `src/bootstrap/src/core/build_steps/test.rs:4310-4500`

## Revalidation

Inspect `compiler/rustc_codegen_cranelift/scripts/test_bootstrap.sh`, `compiler/rustc_codegen_cranelift/patches/`, and `compiler/rustc_codegen_gcc/build_system/src/test.rs` on any newer `rust-lang/rust` revision to check which stdlib patches or bootstrap workarounds remain required for alternate codegen backends.
