# Compiler Differential Testing, Fuzzing, Reduction, and Bug-Finding Records

## Summary

Building a high-yield differential-testing and fuzzing pipeline for a verified `rustc` replacement combines UB-free program generators (`rustlantis` for arbitrary MIR, `RustSmith` for safe surface Rust, `abi-cafe` for cross-ABI calling conventions, and `yarpgen`/`Csmith` for loop/vectorization stress), reference semantic oracles (`Miri` under Tree/Stacked Borrows, `MiniRust`, and cross-backend execution across `LLVM -O0`/`-O3`, `Cranelift`, and `GCC`), and syntax/MIR-aware test-case reducers (`compiler/rustc_codegen_gcc/build_system/src/fuzz/reduce.rs`, `treereduce`, `cvise`, and `llvm-reduce`).

1. **In-Tree Differential Fuzzing and Custom MIR Reduction in `rustc 1.99.1`**:
   - `compiler/rustc_codegen_gcc/build_system/src/fuzz.rs:1-345` embeds a complete differential testing harness that invokes `rustlantis` (`generate <seed>`) to synthesize deterministic, UB-free `#![feature(custom_mir, core_intrinsics)]` programs (`#[custom_mir(dialect = "runtime", phase = "initial")]`), compiles each program across multiple backends/flags (`-Copt-level=0..3`, `-Zcodegen-backend=...`), compares runtime state hashes (`dump_var`), and validates UB-freedom via Miri.
   - `compiler/rustc_codegen_gcc/build_system/src/fuzz/reduce.rs:1-370` implements a domain-specific 7-pass reducer for `#[custom_mir]` reproducers (`remove_dump_var` $\rightarrow$ `remove_fn_calls` $\rightarrow$ `remove_fns` $\rightarrow$ `remove_dup_assign` $\rightarrow$ `match_to_goto` $\rightarrow$ `block_abort` $\rightarrow$ `remove_block` $\rightarrow$ `linearize_cf`) that reduces multi-hundred-line MIR control-flow graphs in seconds before any generic token/tree reducer runs.
2. **Empirical Throughput Across LLVM, Cranelift, and Miri Oracles**:
   - On `x86_64-unknown-linux-gnu` (`support/differential_probe_results.json`), compiling and executing a 50-iteration `#[custom_mir]` + wrapping/checked arithmetic differential batch (`support/custom_mir_differential_probe.rs`) takes **57.1 ms compile + 5.9 ms run** under `LLVM -O0`, **66.3 ms compile + 5.9 ms run** under `LLVM -O3`, **58.3 ms compile + 5.8 ms run** under `Cranelift -O0`, **57.5 ms compile + 6.0 ms run** under `Cranelift -O2`, and **143.6 ms total** under `Miri` (`1.101.0-nightly` `5c543b0b8c73c7b72bc8284ced4fb22ead15734d`), all producing the identical FNV-1a state digest `HASH=a7c3711295530c84` (~**15–17 programs/sec/core** for compiled backends and **7.0 programs/sec/core** when gated by Miri).
3. **Lessons from Empirical Bug-Finding in Verified and Production Compilers**:
   - **Yang et al. (PLDI 2011, Csmith on CompCert 1.6–1.8)** and **Marcozzi et al. / Fonenant et al.**: The only defects Csmith found in CompCert lay outside the mechanized middle-end proof boundary—specifically in the unverified front-end parser/elaborator (`cparser` bitfield/signedness lowering) and unverified back-end assembly printer/target-feature macros—whereas zero miscompilations were found in the Coq-verified `Clight`-to-`Asm` passes.
   - This directly parallels our corpus findings in `minirust-source-lowering-miri-differential-and-open-contract-boundaries` and `anneal-vacuity-mutation-oracles-and-verification-scaling`: differential testing must concentrate on **unverified boundary seams** (frontend HIR/THIR $\rightarrow$ MIR lowering, ABI marshaling (`abi-cafe`), inline assembly, linker/relocation emission, and specification translation vacuity) in addition to end-to-end random MIR execution.

## Applicability

- **Pinned subjects**:
  - `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`, `tests/crashes` with 179 ICE reproducers, `compiler/rustc_codegen_gcc/build_system/src/fuzz.rs`, `compiler/rustc_codegen_cranelift/build_system/abi_cafe.rs`).
  - `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly` with `rustc-codegen-cranelift-preview`).
  - `Miri` @ `5c543b0b8c73c7b72bc8284ced4fb22ead15734d` (`1.101.0-nightly`).
  - `minirust/minirust` @ `24c9dfceab29a2eb1f3bc55c92b02ef7e8e9d733`.
- **Extends**:
  - `minirust-source-lowering-miri-differential-and-open-contract-boundaries` (MiniRust vs. Miri operational semantics and open contract boundaries).
  - `anneal-vacuity-mutation-oracles-and-verification-scaling` (specification vacuity, mutation oracles, and negative attribution).

## Findings

### 1. Program Generators, Fuzzers, and UB-Freedom Techniques

Basis: source (`compiler/rustc_codegen_gcc/build_system/src/fuzz.rs:1-345`, `compiler/rustc_codegen_cranelift/build_system/abi_cafe.rs:1-125`, `compiler/rustc_codegen_cranelift/scripts/abi-cafe-rules.toml:1-75`, `tests/crashes/`) + literature

| Tool / Generator | Input Layer | How It Guarantees UB-Freedom | Target Bug Classes & Historical Yield in `rustc` / `LLVM` / Alternate Backends |
| :--- | :--- | :--- | :--- |
| **`rustlantis`** (`difftests` / `fuzz.rs`) | Custom Initial Runtime MIR (`#[custom_mir(dialect = "runtime", phase = "initial")]`) | Uses acyclic/bounded-loop stack-slot dominance tracking, explicit `Checked(...)` arithmetic, initialized locals before read, and post-generation Miri validation | Miscompilations in `mir-opt` passes (`GVN`, `JumpThreading`, `CopyProp`, `DestinationPropagation`, `SROA`), LLVM instruction selection (`i128` shifts/divisions, aggregate ABI), Cranelift `codegen_i128` / `peephole`, and `libgccjit` switch/overflow lowering (>70 bugs filed across `rustc`, LLVM, Cranelift, and `cg_gcc`). |
| **`RustSmith`** | Surface Safe Rust AST | Generates type-correct, borrow-checked safe Rust (`#![forbid(unsafe_code)]`) with fuel-bounded recursion/loops and wrapping arithmetic | Frontend-to-MIR lowering discrepancies, drop-elaboration order, closure captures, and LLVM optimization bugs triggered by idiomatic ownership patterns. |
| **`abi-cafe`** (`build_system/abi_cafe.rs`) | Paired caller/callee crates across ABIs (`Rust`, `C`, `cdecl`, `stdcall`, `fastcall`, `vectorcall`, `sysv64`, `win64`, `efiapi`) | Deterministic structural type generators (nested structs, unions, transparent wrappers, `i128`, floats, SIMD vectors, by-val vs. indirect `PassMode`) | Calling-convention mismatches between `rustc_codegen_llvm`, `rustc_codegen_cranelift`, `rustc_codegen_gcc`, and host C compilers (`clang`/`gcc`/`cl.exe`). Directly integrated into both `cg_clif` (`./y.sh abi-cafe`) and `cg_gcc` (`--abi-tests`). |
| **`icemaker` / `glacier` / `tests/crashes`** | Mutated `tests/ui` corpus + LLM/grammar combinations + arbitrary `-Z`/`-C` flag combinations | Targets compiler crashes (`exit 101`, `SIGSEGV`, assertion failures) where runtime UB of the compiled binary is irrelevant | Internal Compiler Errors (ICEs) across trait solver, const-eval, MIR borrowck, polymorphization, and backend codegen. `tests/crashes` in `rustc 1.99.1` tracks **179 active ICE reproducers** automatically tested on every CI run to detect when an ICE is fixed. |
| **`Csmith` / `yarpgen`** (via C FFI or `c2rust`) | Random UB-free C99/C++17 scalar, struct, loop, and vector kernels | Static abstract interpretation (`Csmith` range/pointer analysis) or construction-by-invariant (`yarpgen` loop data-dependence graphs) | Deep middle-end loop vectorization, alias analysis (`noalias`), scalar evolution (`SCEV`), and instruction-combine miscompilations in LLVM and GCC. |

### 2. Test-Case Reducers Across Rust, MIR, and LLVM IR

Basis: source (`compiler/rustc_codegen_gcc/build_system/src/fuzz/reduce.rs:1-370`) + documentation

1. **Custom MIR Structural Reducer (`compiler/rustc_codegen_gcc/build_system/src/fuzz/reduce.rs:1-370`)**:
   - Specifically designed for `rustlantis` `#[custom_mir]` reproducers where generic line/token reducers break basic-block terminators or variable declarations:
     1. `remove_dump_var` (`lines 19-68`): Binary-searches which `dump_var(...)` calls actually diverge between the two compilers and deletes all agreeing `dump_var` calls, caching the diverging stdout/stderr signature in `ResultCache`.
     2. `remove_fn_calls` (`lines 125-171`): Replaces `Call(place = fnX(...), ReturnTo(bb), ...)` with `place = 0; Goto(bb)`.
     3. `remove_fns` (`lines 173-208`): Deletes entire unreachable `fn fnX(...)` definitions.
     4. `remove_dup_assign` (`lines 210-241`): Removes redundant assignments within basic blocks.
     5. `match_to_goto` (`lines 243-271`): Collapses `match place { ... => bb }` multi-target switches into unconditional `Goto(bb)`.
     6. `block_abort` & `remove_block` (`lines 273-325`): Replaces unreachable tail subgraphs with `Terminator()` and prunes dead basic blocks.
     7. `linearize_cf` (`lines 327-335`): Sorts and folds linear chains of `Goto` blocks.
2. **Surface Rust AST Reducers (`treereduce-rust` and `cargo-minimize`)**:
   - `treereduce` parses Rust source with `tree-sitter-rust` and performs hierarchical delta-debugging on AST nodes (replacing expressions with `loop {}` or `todo!()`, deleting items/fields/impls) while preserving syntactic validity on every probe, achieving 5–10$\times$ fewer compiler invocations than token-level C-Reduce.
   - `cargo-minimize` reduces multi-file/multi-crate Cargo workspaces by inlining modules (`cargo-modules` / `rust-analyzer`), dead-code pruning, and hierarchical item deletion.
3. **Token-Level and IR-Level Reducers (`cvise` / `creduce` and `llvm-reduce`)**:
   - `cvise` (parallel Python port of C-Reduce's Clang/token passes) remains the final pass for minimizing arbitrary syntax or macro-heavy ICEs after `treereduce` reaches a local fixed point.
   - `llvm-reduce` operates directly on `.ll`/`.bc` bitcode to isolate backend LLVM instruction-selection or pass miscompilations independently of `rustc`.

### 3. Oracles and Differential Pipeline Architecture

Basis: execution (`support/differential_probe_results.json`, `support/custom_mir_differential_probe.rs`) + `minirust-source-lowering-miri-differential-and-open-contract-boundaries` + `anneal-vacuity-mutation-oracles-and-verification-scaling`

| Oracle Tier | Invocation & Cost (`x86_64` Host) | What It Validates | Blind Spots / Boundaries |
| :--- | :--- | :--- | :--- |
| **Tier 1: Operational Reference Interpreter (`Miri`)** | `miri --sysroot ~/.cache/miri` (~`143.6 ms` per 50-iter `custom_mir` batch; `~7.0` progs/sec/core) | Exact MIR operational semantics, Stacked/Tree Borrows pointer provenance (`-Zmiri-tree-borrows`), uninitialized memory reads, alignment, and integer/pointer cast rules | Cannot execute target machine assembly (`asm!`), target-specific hardware bugs, or linker/object relocations; rejects int-to-ptr casts under `-Zmiri-strict-provenance`. |
| **Tier 2: Multi-Backend Execution (`LLVM -O0`/`-O3` vs. `Cranelift` vs. `GCC`)** | `rustc -Copt-level={0,3}` vs. `-Zcodegen-backend=cranelift` (~`57–66 ms` compile + `5.9 ms` run; `~16` progs/sec/core) | End-to-end MIR lowering, instruction selection, register allocation, stack frame layout, calling conventions (`abi-cafe`), and runtime output equivalence | Shared bugs in upstream `rustc` frontend or pre-codegen `mir-opt` passes affect all backends identically unless `-Zmir-opt-level=0` is compared against `-Zmir-opt-level=4`. |
| **Tier 3: Formal Spec & Mutation Oracles (`MiniRust` / `Anneal` Canary & Mutant Suites)** | Mechanized Lean 4 / Coq evaluation + mutation testing (see `anneal-vacuity-mutation-oracles-and-verification-scaling`) | Detects precondition unsatisfiability (vacuity) and under-specified contracts at the formal theorem boundary | Requires mechanized lowering from surface/MIR test cases into the formal IR. |

### 4. Empirical Records from Verified Compilers and Systems

Basis: primary literature (Yang et al., PLDI 2011; Fonseca et al., EuroSys 2017; Marcozzi et al., OOPSLA 2019)

1. **CompCert Under Csmith (Yang et al., PLDI 2011, *"Finding and Understanding Bugs in C Compilers"*)**:
   - Across $>325$ bugs found in GCC and LLVM, Csmith found **only 11 bugs in CompCert 1.6–1.8**, and **every single bug lay in unverified code**:
     - Unverified front-end (`cparser` / `Cil` elaboration of bitfields, unsigned-preserving conversions, and `sizeof` expressions) before the initial `Clight` semantics;
     - Unverified back-end assembly pretty-printing and target hardware register-alignment assumptions after the final `Asm` abstract syntax.
   - Zero miscompilation bugs were found inside the Coq-verified middle-end passes (`Clight` $\rightarrow$ `Csharpminor` $\rightarrow$ `Cminor` $\rightarrow$ `RTL` $\rightarrow$ `LTL` $\rightarrow$ `Linear` $\rightarrow$ `Mach` $\rightarrow$ `Asm`).
2. **Implications for a Verified Drop-In `rustc` Replacement**:
   - If the verified compiler reuses an unverified frontend or emits textual assembly/object files through an unverified serializer, differential fuzzing must specifically target:
     1. **Frontend-to-Verified-IR translation** (`HIR`/`THIR` $\rightarrow$ `MIR` via `RustSmith` + `Miri`),
     2. **Cross-ABI boundary shims** (`abi-cafe` pairing verified-compiler objects against `rustc_codegen_llvm` and `clang` objects),
     3. **Binary/relocation emission** (direct ELF/COFF/Mach-O encoding vs. `llvm-mc`), and
     4. **Middle-end pass isolation** (`rustlantis` comparing `-Zmir-opt-level=0` under `Miri` against full verified compilation).

## Boundaries

- **Multi-hour fuzzing campaigns**: In this investigation we executed a deterministic 50-iteration `#[custom_mir]` + arithmetic differential probe across `LLVM -O0`, `LLVM -O3`, `Cranelift -O0`, `Cranelift -O2`, and `Miri` to measure per-stage latency and verify output agreement. Multi-hour `rustlantis` and `abi-cafe` fuzzing sweeps ($>10^5$ seeds) are specified for continuous execution on dedicated fuzzing runners.

## Evidence

- **Differential probe and measured throughput**:
  - `support/custom_mir_differential_probe.rs` and `support/differential_probe_results.json` (`HASH=a7c3711295530c84` across all 5 configurations: `LLVM -O0`, `LLVM -O3`, `Cranelift -O0`, `Cranelift -O2`, and `Miri`).
- **Primary upstream source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_codegen_gcc/build_system/src/fuzz.rs:1-345` (`rustlantis` differential fuzzer integration)
  - `compiler/rustc_codegen_gcc/build_system/src/fuzz/reduce.rs:1-370` (7-pass `#[custom_mir]` reducer)
  - `compiler/rustc_codegen_cranelift/build_system/abi_cafe.rs:1-125` and `scripts/abi-cafe-rules.toml:1-75`
  - `tests/crashes/` (179 active ICE regression tests)

## Revalidation

Compile and run `support/custom_mir_differential_probe.rs` across `rustc -Copt-level=0`, `rustc -Copt-level=3`, `rustc -Zcodegen-backend=cranelift`, and `miri` to verify `HASH=a7c3711295530c84` and benchmark per-invocation differential throughput.
