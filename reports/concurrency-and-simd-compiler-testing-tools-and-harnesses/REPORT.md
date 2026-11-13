# Concurrency and SIMD Compiler Testing Tools and Harnesses

## Summary

Testing concurrency/weak-memory code generation and SIMD intrinsic lowering in a new `rustc` backend requires separating **library-level schedule exploration tools** (`loom`, `shuttle`, `GenMC`, `C11Tester`) from **IR/interpreter weak-memory and race detectors** (`Miri` with `-Zmiri-many-seeds` and `-Zmiri-track-weak-memory-loads`) and **instruction-level hardware/ISA validators** (`herdtools7` over emitted assembly and `stdarch`'s `intrinsic-test` differential C++/Rust harness).

1. **Crucial Architectural Distinction — Library-Level Interception vs. Backend Instruction Testing**:
   - **`loom` (`0.7.2`) and `shuttle` (`0.9.5`) do NOT test how a compiler backend lowers `core::sync::atomic::Atomic*` instructions**. Both require target code to replace `std::sync::atomic` / `std::thread` imports with `loom::sync::atomic` or `shuttle::sync::atomic` (`loom-0.7.2/src/rt/atomic.rs:1-931`, `loom-0.7.2/src/model.rs:11-140`), intercepting every atomic load/store/RMW in a single-threaded user-space coroutine scheduler (`generator` / `context`) to explore C11 modification-order graphs (CDSChecker dynamic partial-order reduction in `loom`, randomized/PCT/DFS scheduling in `shuttle`). When compiled with a new backend, `loom` and `shuttle` test suites serve as complex coroutine/stack-switching/closure stress tests for the backend, **not** as validators of the backend's emitted `ldar`/`stlr`/`dmb` or `lock cmpxchg` instructions.
   - **Validating a new backend's actual atomic and fence machine-code lowering** requires:
     1. **Static/Symbolic Litmus Extraction to `herd7` (`herdtools7` 7.58)**: Translating the backend's emitted x86_64/i686/AArch64 assembly sequences for each `(AtomicOrdering, RMW/Load/Store/Fence)` pattern into `.litmus` tests and checking them against `x86tso.cat` and `aarch64.cat` (`weak-memory-concurrency-models-hardware-mappings-and-optimizations` and `tier1-atomics-and-fences-instruction-lowering`),
     2. **ThreadSanitizer (`-Zsanitizer=thread`) / C11Tester Instrumentation**: Running concurrent stress tests compiled with TSan instrumentation or hardware watchpoints on native weak-memory (`aarch64`) and TSO (`x86_64`) hardware, and
     3. **`Miri` Weak-Memory & Race Oracle (`-Zmiri-many-seeds=0..N`)**: Validating that the concurrent Rust test cases themselves are free of data races and hold under C11 weak-memory store-buffering (`support/release_acquire_store_buffering_probe.rs`, verified across 16 seeds in **0.42s** / **26.25 ms/seed** in `support/miri_multiseed_and_simd_summary.json`).
2. **SIMD Differential Validation via `stdarch`'s `intrinsic-test` (`library/stdarch/crates/intrinsic-test/`)**:
   - In `rustc 1.99.1`, `library/stdarch/crates/intrinsic-test/src/common/mod.rs:34-131` (`gen_c.rs`, `gen_rust.rs`, `x86/mod.rs`, `arm/mod.rs`) parses vendor intrinsic specifications (Intel XML and Arm ACLE JSON) and automatically generates:
     - Chunked C++ reference programs (`c_programs/wrapper_<i>.c`) compiled by `--cppcompiler` (`clang++` or `g++`), and
     - Matching Rust test crates (`rust_programs/mod_<i>/src/lib.rs`) compiled by the Rust toolchain/backend under test,
     calling each intrinsic across **`PASSES = 20` deterministic input vector combinations** (`mod.rs:36`) and comparing every output lane bit-for-bit (or within ULP tolerances) natively or under `--runner` (`qemu-aarch64` / `Intel SDE`).

## Applicability

- **Pinned subjects**:
  - `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`, `library/stdarch/crates/intrinsic-test/`).
  - `loom` `0.7.2` (`tokio-rs/loom`).
  - `shuttle` `0.9.5` / `shuttle-engine` `0.1.3` (`awslabs/shuttle`).
  - `Miri` @ `5c543b0b8c73c7b72bc8284ced4fb22ead15734d` (`1.101.0-nightly`).
- **Extends**:
  - `rust-atomics-weak-memory-and-aliasing-operational-models`
  - `weak-memory-concurrency-models-hardware-mappings-and-optimizations`
  - `tier1-atomics-and-fences-instruction-lowering`
  - `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`

## Findings

### 1. Concurrency Testing Tools: Mechanism, Backend Integration, and Bug Classes

Basis: source (`loom-0.7.2/src/model.rs:1-278`, `loom-0.7.2/src/rt/atomic.rs:1-931`, `loom-0.7.2/src/rt/vv.rs:1-86`, `shuttle-0.9.5/src/lib.rs:1-320`) + execution (`support/miri_multiseed_and_simd_summary.json`)

| Tool | Interception Level | Scheduling & Memory Model Algorithm | How It Runs Against a New `rustc` Backend | What It Actually Finds When Testing a Backend |
| :--- | :--- | :--- | :--- | :--- |
| **`loom` (`0.7.2`)** | Source-level API replacement (`loom::sync::atomic`, `loom::thread`, `loom::cell::UnsafeCell`) | Exhaustive DPOR over C11 release/acquire vector clocks (`src/rt/vv.rs`, `src/rt/atomic.rs`) bounded by `max_threads = 5`, `max_branches = 1000`, `preemption_bound` (`src/model.rs:11-43`) | Compiles as standard Rust crates with `RUSTFLAGS="-Zcodegen-backend=<backend>" cargo test` | Finds algorithm bugs in lock-free Rust data structures; for the **backend**, stresses stackful coroutine switching (`generator`), TLS, and closure ABI, **not** native atomic instruction emission. |
| **`shuttle` (`0.9.5`)** | Source-level API replacement (`shuttle::sync`, `shuttle::thread`, `shuttle::future`) | Randomized, Probabilistic Concurrency Testing (`pct.rs`), and Portfolio schedulers (`max_steps`, seed replay in `tests/basic/replay.rs`) | Compiles with `RUSTFLAGS="-Zcodegen-backend=<backend>" cargo test` | Scales to 100+ threads/tasks where exhaustive DPOR explodes; stresses backend async state-machine and coroutine codegen. |
| **`Miri` (`-Zmiri-many-seeds`)** | Direct MIR interpretation (`rustc_const_eval::interpret` + `miri` machine hooks) | Vector-clock data-race detector (`-Zmiri-disable-data-race-detector` to toggle) + C11 weak-memory load buffer (`-Zmiri-track-weak-memory-loads`) + randomized preemption (`-Zmiri-preemption-rate`, `-Zmiri-many-seeds=0..N`) | Runs directly on unmodified `std::sync::atomic` and `std::thread` Rust source (`26.25 ms/seed` measured across 16 seeds on `release_acquire_store_buffering_probe.rs`) | Reference oracle for whether a concurrent Rust test case has UB/data races or can exhibit weak-memory behaviors (e.g., store buffering `r1 == 0 && r2 == 0` under `Release`/`Acquire`) before running compiled binaries on hardware. |
| **`ThreadSanitizer` (`-Zsanitizer=thread`) & `C11Tester`** | Compiler IR load/store/atomic pass (`__tsan_read*`, `__tsan_write*`, `__tsan_atomic*`) | Dynamic happens-before vector clocks (TSan) or C11 modification-order history sampling (`C11Tester` via `LD_PRELOAD` / LLVM pass) | Requires the backend to emit `__tsan_*` instrumentation calls (supported in `rustc_codegen_llvm`; unsupported in `cg_clif` and `cg_gcc`) | Detects data races in unmodified multi-threaded Rust + C FFI binaries at runtime. |
| **`GenMC`** | LLVM IR interpreter / model checker | Stateless Model Checking (SMC) over RC11 / IMM execution graphs with optimal DPOR | Operates on LLVM bitcode (`.ll`/`.bc`); cannot directly consume non-LLVM backend output unless lifted to IMM/BIR | Exhaustively verifies lock-free C/Rust kernels at the IR level against RC11/IMM. |
| **`herd7` (`herdtools7` 7.58)** | Machine assembly / `.litmus` | Axiomatic saturation over `x86tso.cat`, `aarch64.cat`, `riscv.cat`, and `c11.cat` | Extracts the backend's emitted x86/AArch64 instruction sequences for atomic operations into `.litmus` files and runs `herd7` | **Directly validates backend atomic & fence instruction selection** (e.g., catching a backend that lowers `Ordering::SeqCst` load + `Ordering::Acquire` load without restoring trailing-sync or `ldar`/`dmb` invariants on AArch64). |

### 2. SIMD Testing via `stdarch` `intrinsic-test` and Co-Execution Oracles

Basis: source (`library/stdarch/crates/intrinsic-test/src/main.rs:1-35`, `src/common/cli.rs:1-72`, `src/common/mod.rs:1-131`, `src/common/gen_rust.rs:1-340`, `src/common/gen_c.rs:1-53`, `src/x86/mod.rs:1-237`, `src/arm/mod.rs:1-319`) + `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`

1. **Architecture of `library/stdarch/crates/intrinsic-test`**:
   - Invoked via `cargo run --bin intrinsic-test -- <input.xml|input.json> --cppcompiler <clang++> --runner "<emulator>" --target <triple> [--linker <linker>] [--skip <file>]` (`src/common/cli.rs:11-72`).
   - Supports two vendor specification frontends:
     - **x86 / x86_64 (`src/x86/xml_parser.rs`)**: Parses Intel's `data-latest.xml` intrinsic specification.
     - **ARM / AArch64 (`src/arm/json_parser.rs`)**: Parses Arm's ACLE `intrinsics.json` specification (NEON, SVE, SVE2, CRC32, Crypto).
   - **Code Generation & Execution Pipeline (`src/common/mod.rs:54-131`)**:
     1. Partitions the filtered intrinsics into `ncores` parallel chunks (`manual_chunk`, `lines 126-131`).
     2. Generates `c_programs/wrapper_<i>.c` containing `extern "C"` wrapper functions that invoke each C/C++ clang/gcc header intrinsic (`<immintrin.h>` or `<arm_neon.h>` / `<arm_sve.h>`).
     3. Generates a Cargo workspace in `rust_programs/` with subcrates `mod_<i>` whose `build.rs` compiles `wrapper_<i>.c` via the `cc` crate and whose `src/lib.rs` invokes both the Rust `core::arch` intrinsic and the C++ `extern "C"` wrapper across **`PASSES = 20`** deterministic input arrays (`src/common/values.rs:1-361`, covering `0`, `-0.0`, `NaN`, `Inf`, `MIN`, `MAX`, alternating bitmasks, and PRNG lanes), asserting lane-by-lane equality.
     4. Executes the linked test binary natively or via `--runner` (`qemu-aarch64` or `Intel SDE`).
2. **Running `intrinsic-test` Against an Alternate or Verified Backend**:
   - Because `intrinsic-test` invokes `cargo run` inside `rust_programs/` (`src/main.rs`), setting `RUSTFLAGS="-Zcodegen-backend=<path-to-backend>"` (or `RUSTC="/path/to/verified-rustc"`) tests the new backend's lowering of every `core::arch` SIMD intrinsic directly against `clang++` + `qemu-aarch64` / native `x86_64` hardware.
   - As established in `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`, this C++-oracle pipeline can be strengthened into a **three-way co-execution oracle** by pairing (1) kernel-checked Lean 4 bitvector theorems generated from the vendor XML/JSON specs, (2) the verified compiler's emitted machine code, and (3) native `x86_64` / `qemu-aarch64 -cpu max` execution.

### 3. Assembling an End-to-End Concurrency and SIMD Verification Campaign for a New Backend

Basis: synthesis of Findings 1 and 2

To qualify a new backend's concurrency and SIMD lowering without blind spots:
1. **Stage 1 — Axiomatic Assembly Audit (`herd7`)**: Extract emitted instruction templates for all atomic `Ordering`s (`Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst`), RMWs (`fetch_add`, `compare_exchange`, `swap`), and `fence`/`compiler_fence` across `x86_64`, `i686`, and `aarch64`, and verify them against `x86tso.cat` and `aarch64.cat` under `herd7`.
2. **Stage 2 — Multi-Seed Operational Pre-Check (`Miri`)**: Run concurrent test suites under `miri -Zmiri-many-seeds=0..64` (`~1.7s` for 64 seeds) to ensure the test suite itself is race-free and exercises weak-memory read-from edges.
3. **Stage 3 — Native Weak-Memory Hardware Stress (`aarch64` + `x86_64`)**: Execute multi-threaded litmus and lock-free stress suites (`crossbeam`, `tokio`, `parking_lot`, `std::sync`) compiled by the new backend on native `aarch64` hardware (not `qemu-aarch64` on x86, which masks weak-memory ordering bugs behind host x86 TSO).
4. **Stage 4 — Exhaustive SIMD Intrinsic Differential Suite (`intrinsic-test` + Lean 4 Co-Execution)**: Run `library/stdarch/crates/intrinsic-test` with `RUSTC=<new-compiler>` across `x86_64` (SSE2/SSSE3/SSE4.1/AVX/AVX2/AVX-512) and `aarch64` (`qemu-aarch64 -cpu max` for NEON/CRC/Crypto/SVE).

## Boundaries

- **Intel SDE licensing**: Testing AVX-512 or APX instructions that are not present on the host `x86_64` CPU requires either `qemu-x86_64 -cpu max` (open-source GPLv2) or Intel Software Development Emulator (`Intel SDE`), which is gated by a proprietary Intel click-through license and was therefore not installed or executed.
- **Library-level model checkers (`loom`, `shuttle`) do not validate machine-code atomics**: As documented in Finding 1, passing `loom` or `shuttle` test suites under a new backend validates coroutine/closure compilation, not atomic instruction selection or memory fence placement.

## Evidence

- **Miri 16-seed weak-memory probe and summary**:
  - `support/release_acquire_store_buffering_probe.rs` and `support/miri_multiseed_and_simd_summary.json` (`16` seeds executed in `0.42s`, `rc=0`).
- **Co-execution SIMD verification cross-reference**:
  - `reports/vendor-intrinsic-specifications-stdarch-verification-and-lean-generation/support/coexecution_results.json` (`360/360` bit-exact matches across Lean 4.34.1, `x86_64` SSE2, and `qemu-aarch64` NEON).
- **Primary upstream source citations**:
  - `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`: `library/stdarch/crates/intrinsic-test/src/{main.rs,common/cli.rs,common/mod.rs,common/gen_rust.rs,common/gen_c.rs,common/values.rs,x86/mod.rs,arm/mod.rs}`
  - `loom` `0.7.2`: `src/model.rs:1-278`, `src/rt/atomic.rs:1-931`, `src/rt/vv.rs:1-86`, `src/rt/scheduler.rs:1-161`
  - `shuttle` `0.9.5`: `src/lib.rs:1-320`, `tests/basic/{pct.rs,dfs.rs,replay.rs,atomic.rs}`

## Revalidation

Run `cargo +nightly-2026-09-30 miri run -Zmiri-many-seeds=0..16 support/release_acquire_store_buffering_probe.rs` to re-verify Miri weak-memory schedule exploration, and run `cargo run --manifest-path library/stdarch/crates/intrinsic-test/Cargo.toml -- --help` in `rust-lang/rust` to inspect the SIMD differential test generator CLI.
