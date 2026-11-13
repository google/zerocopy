# Candidate Optimizers: LLVM, Cranelift, and GCC Backend Comparison for a Derivation-Emitting Rust Compiler

## Summary

Comparing `rustc_codegen_llvm` (LLVM `23.1.1`), `rustc_codegen_cranelift` (`Cranelift 0.121` in `rustc 1.99.1`), and `rustc_codegen_gcc` / `GCC 14.2.0` across runtime performance, code size, compile time, Tier 1 target coverage, differential correctness (`#[custom_mir]`), and proof-certificate instrumentability establishes:

1. **Runtime Speed, Code Size, and Compile Time (`support/optimizer_speed_size_matrix.csv`):**
   - **Runtime Speed (`x86_64-unknown-linux-gnu`, $B=30$ paired blocks across 5 compute kernels):** `rustc_llvm -O3` executes the benchmark suite in **`2.045 ms`** (`clang-19 -O3`: `1.861 ms`, `0.910x`). `rustc_llvm -O2` takes `4.660 ms` (`2.279x`), whereas **`rustc_cranelift -O2`/`-O3` takes `24.425 ms` (`11.945x` slower than `rustc_llvm -O3`)** and `gcc-14 -O3` on the unvectorized scalar-loop C translation takes `20.750 ms` (`10.148x`). At `-O0`, `rustc_cranelift -O0` (`45.280 ms`) is **24.5% faster at runtime** than `rustc_llvm -O0` (`59.969 ms`).
   - **Code Size (`.text` section bytes of the 5 kernels):** `rustc_llvm -Os` (`684 B` on `x86_64`, `768 B` on `aarch64`, `1,068 B` on `i686`) and `-Oz` (`688 B` on `x86_64`) achieve the smallest code size—**3.70x smaller** than `rustc_cranelift -O3` (`2,530 B` on `x86_64`, `2,487 B` on `aarch64`) and **1.55x smaller** than `gcc-14 -Os` (`1,062 B` on `x86_64`).
   - **Compile Time:** `rustc_cranelift -O3` compiles the workload in **`64.68 ms` on `x86_64`** and **`35.00 ms` on `aarch64`** (**42.7% faster** than `rustc_llvm -O3` at `112.86 ms` on `x86_64` and **40.7% faster** than `rustc_llvm -O3` at `59.05 ms` on `aarch64`).
2. **Tier 1 Target Coverage Gaps (`support/optimizer_speed_size_matrix.csv`, `support/instrumentability_metrics.json`):**
   - `rustc_codegen_llvm` supports **8/8 (100%)** Tier 1 targets.
   - `rustc_codegen_cranelift` supports **4/8 (50%)** Tier 1 targets (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, and partial `x86_64-pc-windows-gnu` without unwinding); it **completely lacks a 32-bit x86 (`i686-*`) backend** (`error: Cranelift doesn't support i686-unknown-linux-gnu`) and lacks Windows MSVC SEH unwinding (`*-pc-windows-msvc`).
   - `rustc_codegen_gcc` supports ELF/MinGW targets where `libgccjit.so` is built for the target triple, but **lacks `*-pc-windows-msvc` ABI support** (`3/8` Tier 1 targets use MSVC ABI).
3. **Architectural Instrumentability for Proof-Generating Compilation (`support/instrumentability_metrics.json`):**
   - **Cranelift (`~185k` SLOC, `20,035` LOC in `compiler/rustc_codegen_cranelift`)** is by far the cleanest architecture for **verified lowering and register allocation**: its mid-end (`opts.isle`) and instruction selectors (`x64/lower.isle`, `aarch64/lower.isle`) are declarative term-rewriting rules over acyclic e-graphs (`AEGraph`, verified in external projects via `VeriISLE` and `Crocus`), and `regalloc2` already ships a production symbolic SSA dataflow checker (`regalloc2::checker`). However, Cranelift lacks loop vectorization, SLP vectorization, interprocedural SROA/GVN, and `i686`/MSVC target support.
   - **LLVM 23 (`~3.82M` SLOC, `42,276` LOC in `compiler/rustc_codegen_llvm`, 193-pass `-O3` pipeline)** is required for performance/size parity and full 8/8 Tier 1 target support, and provides `PassInstrumentationCallbacks` plus external SMT validators (`Alive2`, `llubi`), but mutates imperative C++ pointer graphs in place across 124 distinct pass classes.
   - **GCC 14 (`~5.40M` SLOC, `25,361` LOC in `compiler/rustc_codegen_gcc`, 268 GIMPLE+RTL passes)** has the largest TCB, C-macro-heavy GIMPLE/RTL mutation APIs, and the weakest formal verification ecosystem (limited to GIMPLE subset checking in `smtgcc`).

## Applicability

- **Extends:** `verified-and-validated-compiler-optimization-precedents`, `rustc-llvm-free-sysroot-cranelift-gcc-and-host-tools-audit`
- **Subjects and Scope:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), specifically `compiler/rustc_codegen_ssa` (`36,396` LOC), `compiler/rustc_codegen_llvm` (`42,276` LOC), `compiler/rustc_codegen_cranelift` (`20,035` LOC), and `compiler/rustc_codegen_gcc` (`25,361` LOC).
  - `rust-lang/llvm-project` `23.1.1-rust-1.99.1-stable` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
  - Host `x86_64-linux-gnu-gcc` `14.2.0` and `clang-19` `19.1.7`.

## Findings

### 1. Head-to-Head Performance, Code Size, and Compile-Time Matrix

**Basis: execution (`support/run_backend_comparison.py`, `support/optimizer_speed_size_matrix.csv`).**

Across the 5-workload benchmark suite (`wl1_crc32c`, `wl2_fnv1a64`, `wl3_chacha_quarter_rounds`, `wl4_binary_search_sum`, `wl5_matmul_8x8`):

| Backend Configuration | Target | Status | Compile Time (ms) | Kernel `.text` Size (B) | Runtime Median ($B=30$, ms) | Runtime Ratio vs. `rustc_llvm -O3` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| `rustc_llvm -O0` | `x86_64-unknown-linux-gnu` | `OK` | `63.34` | `5,796` | `59.969` | `29.33x` |
| `rustc_llvm -O2` | `x86_64-unknown-linux-gnu` | `OK` | `94.50` | `1,411` | `4.660` | `2.28x` |
| **`rustc_llvm -O3`** | `x86_64-unknown-linux-gnu` | `OK` | `112.86` | `2,215` | **`2.045`** | **`1.00x`** |
| `rustc_llvm -Os` | `x86_64-unknown-linux-gnu` | `OK` | `93.17` | **`684`** | `2.295` | `1.12x` |
| `rustc_llvm -Oz` | `x86_64-unknown-linux-gnu` | `OK` | `89.32` | `688` | `2.205` | `1.08x` |
| `rustc_cranelift -O0` | `x86_64-unknown-linux-gnu` | `OK` | `66.65` | `8,594` | `45.280` | `22.14x` |
| `rustc_cranelift -O2` (`speed`) | `x86_64-unknown-linux-gnu` | `OK` | `64.91` | `2,530` | `24.425` | `11.95x` |
| `rustc_cranelift -O3` (`speed`) | `x86_64-unknown-linux-gnu` | `OK` | `64.68` | `2,530` | `24.476` | `11.97x` |
| `rustc_cranelift -Os` (`speed_and_size`) | `x86_64-unknown-linux-gnu` | `OK` | `67.55` | `5,541` | `38.613` | `18.88x` |
| `gcc-14 -O0` (C kernel proxy) | `x86_64-unknown-linux-gnu` | `OK` | `46.06` | `1,997` | `72.913` | `35.66x` |
| `gcc-14 -O2` (C kernel proxy) | `x86_64-unknown-linux-gnu` | `OK` | `75.16` | `1,414` | `20.586` | `10.07x` |
| `gcc-14 -O3` (C kernel proxy) | `x86_64-unknown-linux-gnu` | `OK` | `110.70` | `2,699` | `20.750` | `10.15x` |
| `gcc-14 -Os` (C kernel proxy) | `x86_64-unknown-linux-gnu` | `OK` | `69.42` | `1,062` | `20.663` | `10.11x` |
| `clang-19 -O3` (C kernel proxy) | `x86_64-unknown-linux-gnu` | `OK` | `107.78` | `3,015` | `1.861` | `0.91x` |
| `rustc_llvm -O0` | `aarch64-unknown-linux-gnu` | `OK` | `36.07` | `6,011` | — | — |
| `rustc_llvm -O3` | `aarch64-unknown-linux-gnu` | `OK` | `59.05` | `1,420` | — | — |
| `rustc_llvm -Os` | `aarch64-unknown-linux-gnu` | `OK` | `48.52` | `768` | — | — |
| `rustc_cranelift -O0` | `aarch64-unknown-linux-gnu` | `OK` | `36.33` | `8,290` | — | — |
| `rustc_cranelift -O3` | `aarch64-unknown-linux-gnu` | `OK` | `35.00` | `2,487` | — | — |
| `rustc_llvm -O3` | `i686-unknown-linux-gnu` | `OK` | `55.42` | `2,111` | — | — |
| `rustc_cranelift -O3` | `i686-unknown-linux-gnu` | **`UNSUPPORTED`** | `33.78` | `0` | — | — |

**Why LLVM `-O3` Outperforms Cranelift `-O2`/`-O3` by `11.95x` on Compute Kernels:**
1. **Complete Loop Unrolling + Constant/Algebraic Folding (`wl1_crc32c` and `wl5_matmul_8x8`):** LLVM unrolls the inner 8-bit CRC32C polynomial loop and the $8 \times 8 \times 8$ matrix multiplication loops, vectorizing `wl5_matmul_8x8` and `wl3_chacha_quarter_rounds` into 128-bit SSE2 / 256-bit AVX2 SIMD instructions. Cranelift performs no loop unrolling and no auto-vectorization.
2. **Identical `-O2` and `-O3` Mapping in `rustc_codegen_cranelift`:** In `compiler/rustc_codegen_cranelift/src/config.rs`, both `-C opt-level=2` and `-C opt-level=3` map to Cranelift's `OptLevel::Speed`, producing identical `2,530 B` `.text` output.

---

### 2. Quantitative Instrumentability & Proof-Certificate Comparison

**Basis: source + execution (`support/instrumentability_metrics.json`).**

| Metric / Dimension | LLVM `23.1.1` (`rustc_codegen_llvm`) | Cranelift `0.121` (`rustc_codegen_cranelift`) | GCC `14.2` (`rustc_codegen_gcc` / `libgccjit`) |
| :--- | :--- | :--- | :--- |
| **`rustc` Codegen Crate Size** | `69` files, `42,276` LOC (`+36,396` LOC in `rustc_codegen_ssa`) | `64` files, `20,035` LOC | `62` files, `25,361` LOC |
| **Optimizer + Backend SLOC** | `~3,820,000` C++/TableGen SLOC | `~185,000` Rust + ISLE SLOC | `~5,400,000` C/C++/md SLOC |
| **IR Hierarchy** | `LLVM IR` $\to$ `SelectionDAG` / `GlobalISel` $\to$ `MachineInstr` $\to$ `MCInst` | `CLIF SSA` (block params) $\to$ `AEGraph` $\to$ `VCode` (`RegAlloc2`) $\to$ `MachBuffer` | `GENERIC` $\to$ `GIMPLE` (High/Low/SSA) $\to$ `RTL` $\to$ Assembly |
| **Pass Count (`-O3`)** | `193` pass invocations (`124` distinct pass classes) | `11` phases (`egraph` pass combines GVN, LICM, and `opts.isle` in a single pass!) | `268` passes (`~185` GIMPLE + `~83` RTL passes) |
| **IR Mutation Surface** | Imperative pointer mutation (`replaceAllUsesWith`, `IRBuilder`, `MemorySSAUpdater`) | Scoped pure functional e-class union in `egraph.rs` + generated pure pattern matchers from `*.isle` | In-place C union/tree pointer mutation (`gsi_replace`, `validate_change`) |
| **Built-In Verification / Checkers** | `VerifierPass` (structural SSA/dominance/types only) | `cranelift_codegen::verifier` + **`regalloc2::checker` (symbolic SSA equivalence checker for register allocation!)** | `verify_gimple_in_cfg`, `verify_ssa`, `verify_rtl_sharing` (structural only) |
| **Transformation Tracing Hooks** | `PassInstrumentationCallbacks` (`BeforePass` / `AfterPass`), `-opt-bisect-limit` | Per-phase CLIF serialization + ISLE rule-firing trace hooks | `gcc-plugin` `PASS_EXECUTION` events + `-fdump-tree-all` |
| **Proof & TV Precedents** | **Alive2** (Z3 IR-to-IR & AArch64 asm TV), **Crellvm** (Coq hint emission), **Vellvm** (Coq ITrees), **llubi** | **VeriISLE** & **Crocus** (SMT verification of ISLE rules), **regalloc2 checker** | **smtgcc** (GIMPLE subset TV), **seL4 graph-refine** (ARMv7 `-O2` binary lifting) |

---

### 3. Five-Way Differential Testing (`#[custom_mir]` Across LLVM, Cranelift, and Miri)

**Basis: execution (`support/instrumentability_metrics.json`, `support/run_backend_comparison.py`).**

Running our 250-seed pseudo-random `#[custom_mir(dialect = "runtime", phase = "optimized")]` differential stress test (exercising `Checked(a + y)` overflow tuples, dynamic shift masking `z & 63`, 64-bit wrapping multiplication, bitwise XOR, and unsigned `>=` comparison) across all 5 execution engines produced bit-identical FNV-1a output hashes:
- `rustc_llvm -O0`: `HASH=e76bb4b9df0a322f` (`5.640 ms`)
- `rustc_llvm -O3`: `HASH=e76bb4b9df0a322f` (`5.455 ms`)
- `rustc_cranelift -O0`: `HASH=e76bb4b9df0a322f` (`5.481 ms`)
- `rustc_cranelift -O2`: `HASH=e76bb4b9df0a322f` (`5.473 ms`)
- `Miri 0.1.0` (`nightly-2026-09-30`): `HASH=e76bb4b9df0a322f` (`98.192 ms`)

Combined with the `compiletest` backend sweep (`rustc-compiletest-bootstrap-and-alternate-backend-test-mechanics`), where `assembly-llvm` passed `422/422`, `codegen-units` passed `46/46`, `qemu-i386` passed `69/69`, and `Cranelift` passed `78/82` `ui/numbers-arithmetic/` tests (failing only on inline-assembly and LLVM-specific diagnostic tests), this confirms that Cranelift can serve as a fast (`-O0` / dev-build) differential reference and architectural template for verified ISLE lowering + `regalloc2` checking, while an LLVM-derived or middle-end-verified pipeline is mandatory for `-O3`/`-Os` performance/size parity and 8/8 Tier 1 target coverage.

## Boundaries

1. **No Live `libgccjit.so` Execution on Host:** While `compiler/rustc_codegen_gcc` (`25,361` LOC) is present in the `rustc 1.99.1` tree, a pre-built patched `libgccjit.so` matching `rustc_codegen_gcc`'s custom entry points is not installed in `/usr/lib`; GCC's optimizer (`gcc 14.2.0`) was therefore benchmarked directly on the semantically matched C kernel translation (`o8_workload.c`).
2. **Cranelift 32-Bit x86 and MSVC Unwinding (`unsupported`):** `cranelift-codegen` has no `i686` instruction selector (`isa/x86` was removed upstream in favor of `isa/x64`), blocking `i686-unknown-linux-gnu`, `i686-pc-windows-gnu`, and `i686-pc-windows-msvc`.

## Evidence

- **`rustc 1.99.1` Codegen Backends (`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_codegen_llvm/` (`69` files, `42,276` LOC).
  - `compiler/rustc_codegen_cranelift/` (`64` files, `20,035` LOC; `src/config.rs`, `src/base.rs`, `src/abi/`).
  - `compiler/rustc_codegen_gcc/` (`62` files, `25,361` LOC; `src/back/`, `build_system/src/fuzz/reduce.rs`).
- **Preserved Package Support Artifacts (`support/`):**
  - [`support/run_backend_comparison.py`](support/run_backend_comparison.py): Reproducible multi-backend benchmark, cross-compilation, and 250-seed `#[custom_mir]` differential harness.
  - [`support/optimizer_speed_size_matrix.csv`](support/optimizer_speed_size_matrix.csv): Measured compile times, `.text` sizes, and $B=30$ runtime medians across `rustc_llvm`, `rustc_cranelift`, `gcc-14`, and `clang-19`.
  - [`support/instrumentability_metrics.json`](support/instrumentability_metrics.json): Codebase size, pass counts, IR mutation APIs, verification precedents, and 250-seed differential results.

## Revalidation

```bash
python3 support/run_backend_comparison.py
```
Verify that all 5 engines in `custom_mir_250_seed_differential_campaign` emit `HASH=e76bb4b9df0a322f` and that `optimizer_speed_size_matrix.csv` reproduces the speed and `.text` size ratios within $\pm 5\%$.
