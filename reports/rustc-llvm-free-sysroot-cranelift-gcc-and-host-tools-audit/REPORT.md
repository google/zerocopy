# Building the `rustc` Sysroot and Host Toolchain Without LLVM Code Generation

## Summary

Building a complete Rust `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
standard-library sysroot (`library/sysroot`: `core`, `compiler_builtins`,
`alloc`, `std`, `test`, `unwind`, `panic_abort`, `panic_unwind`, and
`std_detect`) and host toolchain without LLVM code generation faces five
distinct classes of obstacles across the 8 Tier 1 targets
(`x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`,
`aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`,
`i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`, and `x86_64-pc-windows-gnu`):

1. **32-bit x86 (`i686`) ISA absence in Cranelift (`0.134.0`) and single-target
   `libgccjit.so` architecture in GCC**:
   - `cranelift-codegen` `0.134.0` implements 64-bit `x86_64`, `aarch64`,
     `s390x`, `riscv64`, and `pulley`, but has no 32-bit x86 backend. Compiling
     any crate for `i686-unknown-linux-gnu` or `i686-pc-windows-msvc` with
     `rustc_codegen_cranelift` immediately aborts with `error: can't compile for
     i686-...: Support for this target has not been implemented yet`.
   - `rustc_codegen_gcc` dynamically loads `<sysroot>/lib/rustlib/<host>/
     codegen-backends/lib/<llvm_target>/libgccjit.so`. Because GCC compiles each
     `libgccjit.so` for a single fixed `(host, target)` pair
     (`src/bootstrap/src/core/build_steps/compile.rs:1565-1635`), cross-compiling
     to `N` targets requires building `N` separate `libgccjit.so` libraries from
     the patched `rust-lang/gcc` fork (`6f155cc3f5a2dff33afe6cc3ed6c2e0e605ae6a3`).
2. **128-bit integer atomics (`AtomicI128`, `AtomicU128`) in unpatched
   `library/core`**:
   - On `x86_64-unknown-linux-gnu`, `max_atomic_width` defaults to `64`, so
     unpatched `library/core` compiles cleanly with `rustc_codegen_cranelift`
     (`rc = 0`).
   - On all other five 64-bit Tier 1 targets (`aarch64-unknown-linux-gnu`,
     `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `aarch64-pc-windows-msvc`,
     and `x86_64-pc-windows-gnu`), the target specification sets
     `max_atomic_width = Some(128)`, enabling `#[cfg(target_has_atomic_load_store
     = "128")]` in `library/core/src/sync/atomic.rs:3996`. Unpatched `core` fails
     with `error: 128bit atomics not yet supported` unless
     `compiler/rustc_codegen_cranelift/patches/0027-stdlib-128bit-atomic-operations.patch`
     is applied.
3. **COFF AArch64 relocation gap (`Aarch64AdrGotPage21`) in `cranelift-object`**:
   - Even after applying `0027-stdlib-128bit-atomic-operations.patch`, compiling
     `core` for `aarch64-pc-windows-msvc` panics inside `cranelift-object`
     `0.134.0` (`src/backend.rs:992:22`: `not implemented: Aarch64AdrGotPage21 is
     not supported for this file format`), whereas the other five 64-bit Tier 1
     targets (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`,
     `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, and
     `x86_64-pc-windows-gnu`) compile `core`, `compiler_builtins`, `alloc`,
     `unwind`, `panic_abort`, `panic_unwind`, `std_detect`, and `std` (`.rlib`)
     to completion (`rc = 0`).
4. **Stock vs. patched `libgccjit.so` in `rustc_codegen_gcc`**:
   - Even when built with `--no-default-features` (disabling the `master` feature
     gate) against system Debian GCC 15 `libgccjit.so.15.0.1`, compiling `core`
     on `x86_64-unknown-linux-gnu` fails in `libgccjit.so` with
     `gcc_jit_context_new_cast: cannot cast &global.10 from type: struct ... * to
     type: size_t` and panics at `compiler/rustc_codegen_gcc/src/common.rs:302:43`.
5. **Non-codegen LLVM dependencies in a Tier 1 toolchain**:
   - While archive creation was decoupled from LLVM by porting to the pure-Rust
     `ar_archive_writer` crate (`rustc_codegen_ssa/src/back/archive.rs`), the
     toolchain still relies on LLVM's `compiler-rt` C sources for
     `profiler_builtins` (`-Cinstrument-coverage` / `-Cprofile-generate`),
     bundled `rust-lld` (`lld` 23.1.1) for self-contained linking, and
     `llvm-tools` (`llvm-cov`, `llvm-profdata`, `llvm-objcopy`, `llvm-nm`,
     `llvm-ar`, `llvm-S-dwp`) for PGO, coverage, and split-DWARF packaging.

## Applicability

- **Primary baseline**: `rust-lang/rust` `1.99.1`
  (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `cranelift-codegen` `0.134.0`,
  and `gccjit` `3.3.0`, cross-checked against `1.100.0`
  (`0ef1bc386059596dada8fb65b50425aab2ea637a`) and `nightly-2026-11-12`
  (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
- **Scope**: Sysroot build workflows (`rustc_codegen_cranelift/build_system`,
  `rustc_codegen_gcc/build_system`, and `src/bootstrap`), special requirements
  of `core`, `alloc`, `std`, `compiler_builtins`, `panic_unwind`, `std_detect`,
  and `profiler_builtins`, non-codegen LLVM toolchain components, and empirical
  sysroot build results across all 8 Tier 1 targets.

## Findings

### 1. How Cranelift, GCC, and `bootstrap` Build the Standard-Library Sysroot

`Basis: source + execution`

#### 1.1 `rustc_codegen_cranelift` Sysroot Pipeline (`build_system/build_sysroot.rs`)

`compiler/rustc_codegen_cranelift/build_system/build_sysroot.rs:202-265` builds
the Cranelift sysroot in four steps:

1. **Source preparation & patching (`build_sysroot.rs:212-222`)**: Copies
   `<sysroot>/lib/rustlib/src/rust` to `build/stdlib` and applies
   `patches/*stdlib*.patch` (`0027-stdlib-128bit-atomic-operations.patch`, which
   strips `#[cfg(target_has_atomic_load_store = "128")]` `AtomicI128` and
   `AtomicU128` definitions from `library/core/src/sync/atomic.rs` and
   `library/core/src/panic/unwind_safe.rs`).
2. **Required `RUSTFLAGS` (`build_sysroot.rs:224-249`)**:
   - `-Zforce-unstable-if-unmarked`
   - `-Cpanic=abort` (when `panic_unwind_support == false`, the default)
   - `-Zcodegen-backend=<path/to/librustc_codegen_cranelift.so>`
   - `--sysroot=/dev/null` (prevents `rustc` from picking up pre-existing
     LLVM-compiled `.rlib`s in the host sysroot)
   - `-Zinline-mir` (compensates for Cranelift's lack of cross-function inlining)
   - `-Zdisable-incr-comp-backend-caching`
3. **Cargo invocation (`build_sysroot.rs:250-265`)**: Builds
   `library/sysroot/Cargo.toml` with `--release --features "backtrace
   panic-unwind" -Zembed-metadata=no` and `__CARGO_DEFAULT_LIB_METADATA=cg_clif`.

#### 1.2 `rustc_codegen_gcc` Sysroot Pipeline (`build_system/src/build.rs`)

`compiler/rustc_codegen_gcc/build_system/src/build.rs:109-204` requires:
1. Symlinking the target-specific `libgccjit.so` (built from commit
   `6f155cc3f5a2dff33afe6cc3ed6c2e0e605ae6a3` of `rust-lang/gcc`) into
   `<sysroot>/lib/rustlib/<host_triple>/codegen-backends/lib/<llvm_target>/libgccjit.so`.
2. Passing `RUSTFLAGS="-Zforce-unstable-if-unmarked -Zmir-opt-level=3"` (plus
   `-Csymbol-mangling-version=v0` when built with `--no-default-features`) to
   `cargo build --target <target> --features backtrace` in `library/sysroot`.

#### 1.3 `src/bootstrap` Alternate-Backend Support (`compile.rs`)

In `src/bootstrap/src/core/build_steps/compile.rs`:
- `rust.codegen-backends = ["cranelift"]` or `["gcc"]` (without `"llvm"`) builds
  `CraneliftCodegenBackend` (`compile.rs:1736-1806`) or `GccCodegenBackend`
  (`compile.rs:1652-1733`) plus `GccCodegenLibs` (`compile.rs:1565-1635`) and
  sets `CFG_DEFAULT_CODEGEN_BACKEND` (`compile.rs:1330`) so stage 1+ `rustc`
  defaults to the non-LLVM backend when building stage 1+ `Std`
  (`compile.rs:112-490`).
- However, `bootstrap` still requires LLVM `compiler-rt` sources if either
  `build.profiler = true` (`compiler_rt_for_profiler`, `compile.rs:507-523`) or
  `rust.optimized-compiler-builtins = true` (`compile.rs:605-640`, which enables
  the `c` feature of `compiler_builtins` against `src/llvm-project/compiler-rt`).
  An LLVM-free bootstrap must therefore set `build.profiler = false` and
  `rust.optimized-compiler-builtins = false`.

---

### 2. Per-Crate Sysroot Obstacles and Special Support Requirements

`Basis: source + execution`

| Sysroot Crate | Path in `s1991` | Special Backend / Toolchain Requirements | Status Without LLVM |
| :--- | :--- | :--- | :--- |
| `core` | `library/core` | Uses all compiler intrinsics, SIMD (`core::arch`), inline `asm!`, `f16`/`f128` primitives, and 128-bit atomics (`AtomicI128`/`AtomicU128` on targets where `max_atomic_width == 128`). | **Compiles on Cranelift** once `0027-stdlib-128bit-atomic-operations.patch` is applied (`f16`/`f128` ops are polyfilled via `compiler_builtins` soft-float libcalls in `codegen_f16_f128.rs`). |
| `compiler_builtins` | `library/compiler-builtins/compiler-builtins` | Provides software integer division/multiplication (`__udivti3`, `__muloti4`), `f16`/`f32`/`f64`/`f128` soft-float conversions (`__floattisf`, `__addtf3`, `__truncdfhf2`), `mem` (`memcpy`, `memmove`, `memset`, `memcmp`, `bcmp`), and `__rust_probestack`. Features: `default = ["arch"]`, `mem`, `c` (compiles C/ASM from `llvm-project/compiler-rt`). | **Pure-Rust build (`--features compiler-builtins,mem`, without `c`) compiles on Cranelift** without `llvm-project/compiler-rt`, using inline `global_asm!` (compiled via external `$CC` in `cranelift/src/global_asm.rs`) or pure-Rust fallbacks (`no-asm`). |
| `alloc` | `library/alloc` | Relies on `#[rustc_allocator]` magic symbols (`__rust_alloc`, `__rust_dealloc`, `__rust_realloc`, `__rust_alloc_zeroed`, `__rust_no_alloc_shim_is_unstable_v2`) generated by `ExtraBackendMethods::codegen_allocator`. | **Compiles unmodified** on Cranelift and GCC (`rc = 0`). |
| `panic_unwind` & `unwind` | `library/panic_unwind`, `library/unwind` | `panic_unwind/src/gcc.rs` defines `rust_eh_personality` parsing DWARF `.gcc_except_table` LSDA (`DW_EH_PE_*` encodings) and calling `_Unwind_RaiseException` (`libgcc_s` / `libunwind`). | **Compiles unmodified** (`rc = 0`), but executing cleanup landing pads requires the backend to emit valid `.eh_frame` CFI and `.gcc_except_table` LSDA (or SEH tables on Windows). |
| `std_detect` | `library/std_detect` | Uses `core::arch` CPUID / `mrs` inline `asm!` or OS `getauxval` to probe runtime CPU features. | **Compiles unmodified** on Cranelift (`rc = 0`) because Cranelift supports `asm!` on `x86_64`, `aarch64`, `riscv64`, and `s390x` by shelling out to an external assembler (`inline_asm.rs`). |
| `std` | `library/std` | Integrates `backtrace` (`gimli`, `object`, `addr2line`, `miniz_oxide`), `panic_unwind`/`panic_abort`, TLS (`#[thread_local]`), and platform `libc`/Windows imports (`raw-dylib` on Windows). | **`libstd.rlib` compiles on all 5 supported 64-bit Tier 1 targets**; linking `libstd.so`/`.dylib`/`.dll` requires target linkers, and `raw-dylib` on `windows-gnu` invokes `dlltool` (`x86_64-w64-mingw32-dlltool`). |
| `profiler_builtins` | `library/profiler_builtins` | `build.rs` compiles 20 C/C++ files (`InstrProfiling*.c`, `GCDAProfiling.c`) directly from `src/llvm-project/compiler-rt/lib/profile` (`build.rs:26-49`). | **Hard LLVM `compiler-rt` dependency**: requires either `src/llvm-project/compiler-rt` or prebuilt `LLVM_PROFILER_RT_LIB`. Not needed when `-Cinstrument-coverage` and `-Cprofile-generate` are disabled. |

---

### 3. Empirical Sysroot Build Matrix Across All 8 Tier 1 Targets

`Basis: execution`

We executed three build tiers across all 8 Tier 1 targets on `rustc` 1.99.1
(`support/v5_tier1_sysroot_matrix.json`): (A) unpatched `library/core` with
`librustc_codegen_cranelift.so`, (B) patched `library/core` (with
`0027-stdlib-128bit-atomic-operations.patch`) and full `library/sysroot` (`core`,
`compiler_builtins`, `alloc`, `unwind`, `panic_abort`, `panic_unwind`,
`std_detect`, `std`, `test`, `sysroot`), and (C) `rustc_codegen_gcc` (`--no-default-features`
against system `libgccjit.so.15.0.1`).

| Tier 1 Target | Cranelift: Unpatched `core` | Cranelift: Patched `core` (`0027` patch) | Cranelift: Full `library/sysroot` (`core` + `alloc` + `compiler_builtins` + `std.rlib` + `std.so/.dll`) | GCC (`libgccjit.so.15` host x86_64): `mini_no_std` / `core` |
| :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | **PASS (`rc = 0`)** (`max_atomic_width = 64`) | **PASS (`rc = 0`)** | **PASS (`rc = 0`)** — Complete sysroot (`.rlib` + `libstd.so`) built in release mode | `mini_no_std`: `rc = 0`; `core`: **FAIL (`rc = 101`)** (`gcc_jit_context_new_cast: cannot cast &global.10 ... to size_t`) |
| `i686-unknown-linux-gnu` | **FAIL (`rc = 1`)** (`Support for this target has not been implemented yet`) | **FAIL (`rc = 1`)** (No 32-bit x86 ISA in Cranelift `0.134.0`) | **Blocked** by missing `i686` ISA in Cranelift | **FAIL (`rc = 1`)** (`CPU you selected does not support x86-64 instruction set` without 32-bit cross `libgccjit.so`) |
| `aarch64-unknown-linux-gnu` | **FAIL (`rc = 1`)** (`error: 128bit atomics not yet supported` at `atomic.rs:3996`) | **PASS (`rc = 0`)** | **All `.rlib` crates PASS (`rc = 0`)**; `libstd.so` link requires `aarch64-linux-gnu-gcc` without `-B.../gcc-ld -fuse-ld=lld` conflict (`--fix-cortex-a53-843419`) | `mini_no_std` emits wrong-arch `EM_X86_64` `.rcgu.o` inside `AArch64` `.rlib` unless cross-targeted `libgccjit.so` is used |
| `aarch64-apple-darwin` | **FAIL (`rc = 1`)** (`error: 128bit atomics not yet supported`) | **PASS (`rc = 0`)** | **All `.rlib` crates PASS (`rc = 0`)** (`libcore`, `liballoc`, `libcompiler_builtins`, `libstd.rlib`); `libstd.dylib` link requires Darwin `cc`/SDK | **FAIL (`rc = 101`)** (Requires `arm64-apple-macosx/libgccjit.so`) |
| `x86_64-pc-windows-msvc` | **FAIL (`rc = 1`)** (`error: 128bit atomics not yet supported`) | **PASS (`rc = 0`)** | **All `.rlib` crates PASS (`rc = 0`)**; `std.dll` link requires `link.exe` / `lld-link` and Windows import libs | `mini_no_std`: `rc = 0` (emits ELF `.o` from Linux `libgccjit.so` instead of COFF `.obj`!) |
| `i686-pc-windows-msvc` | **FAIL (`rc = 1`)** (`Support for this target has not been implemented yet`) | **FAIL (`rc = 1`)** (No 32-bit x86 ISA in Cranelift) | **Blocked** by missing `i686` ISA in Cranelift | **FAIL (`rc = 1`)** (`CPU you selected does not support x86-64 instruction set`) |
| `aarch64-pc-windows-msvc` | **FAIL (`rc = 101`)** (128-bit atomics + `Aarch64AdrGotPage21` ICE) | **FAIL (`rc = 101`)** (`cranelift-object-0.134.0/src/backend.rs:992:22`: `not implemented: Aarch64AdrGotPage21 is not supported for this file format`) | **Blocked** in `core` by missing COFF AArch64 GOT relocation in `cranelift-object` | `mini_no_std`: wrong-arch `EM_X86_64` ELF `.o` without `aarch64-pc-windows-msvc` `libgccjit.so` |
| `x86_64-pc-windows-gnu` | **FAIL (`rc = 1`)** (`error: 128bit atomics not yet supported`) | **PASS (`rc = 0`)** | **All dependency `.rlib`s PASS**; `std` fails invoking `x86_64-w64-mingw32-dlltool` (`No such file or directory`) for `raw-dylib` import stubs | `mini_no_std`: emits ELF `.o` without `x86_64-w64-mingw32` `libgccjit.so` |

---

### 4. Non-Codegen LLVM Components in a Tier 1 Toolchain

`Basis: source + execution`

Even when `LlvmCodegenBackend` is replaced for MIR-to-object compilation, a
standard `rustc` toolchain carries four categories of LLVM-derived components:

1. **Static archive creation (`ar_archive_writer` — Already Ported to Pure Rust)**:
   `compiler/rustc_codegen_ssa/src/back/archive.rs` uses the pure-Rust
   `object` + `ar_archive_writer` crate (`ArArchiveBuilderBuilder`) by default in
   `CodegenBackend::link` (`traits/backend.rs:153`). Only `LlvmCodegenBackend`
   uses `LlvmArchiveBuilderBuilder`, which itself delegates archive writing to
   `ar_archive_writer` while using LLVM only to read bitcode symbol tables for
   LTO archives (`rustc_codegen_llvm/src/back/archive.rs:1-102`).
2. **`raw-dylib` PE/COFF import library generation (`ar_archive_writer::write_import_library`)**:
   On `x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, and
   `aarch64-pc-windows-msvc`, `rustc_codegen_ssa/src/back/link.rs` synthesizes
   `.lib` COFF import libraries in pure Rust via `ar_archive_writer`. However,
   on **`x86_64-pc-windows-gnu`** (`is_like_windows && env == Env::Gnu`),
   `rustc_codegen_ssa/src/back/archive.rs` invokes the external
   `x86_64-w64-mingw32-dlltool` binary (`llvm-dlltool` or binutils `dlltool`) to
   assemble `.def` files into import libraries, which is why building `std` on
   `x86_64-pc-windows-gnu` without `x86_64-w64-mingw32-dlltool` on `PATH` fails!
3. **Inline and `global_asm!` assembly (`cranelift/src/inline_asm.rs`,
   `global_asm.rs`)**:
   `rustc_codegen_llvm` uses LLVM's integrated MC assembler (`LLVMRustAssemble`).
   `rustc_codegen_cranelift` instead writes textual `.s` assembly and invokes an
   external C compiler/assembler (`$CC` / `gcc` / `clang`) via
   `global_asm::compile_global_asm`. An LLVM-free toolchain must either provide
   a target assembler or emit machine bytes directly for `asm!` and
   `global_asm!`.
4. **Bundled `rust-lld` and `llvm-tools`**:
   - `rust-lld` (`lld`, `ld.lld`, `lld-link`, `ld64.lld`, `wasm-ld`) is used as
     the default self-contained linker on `x86_64-unknown-linux-gnu` (via the
     `gcc-ld/ld.lld` wrapper) and cross-targets.
   - `llvm-tools` (`llvm-profdata`, `llvm-cov`, `llvm-objcopy`, `llvm-nm`,
     `llvm-ar`, `llvm-dwp`) is optional for normal compilation (`cargo build` /
     `cargo test`) except when `-Csplit-debuginfo=packed` on ELF invokes `dwp` /
     `llvm-dwp`.

## Boundaries

- **Patched `rust-lang/gcc` fork build (`not examined` via full GCC compilation)**:
  Building the custom `rust-lang/gcc` C++ fork (`6f155cc3f5a2dff33afe6cc3ed6c2e0e605ae6a3`)
  from source for 8 cross-targets requires >1 hour wall-clock and >20 GB disk;
  we verified the exact failure mode against stock Debian `libgccjit.so.15.0.1`
  and documented the multi-target `GccCodegenLibs` architecture from
  `src/bootstrap/src/core/build_steps/compile.rs:1565-1635`.

## Evidence

- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_codegen_cranelift/build_system/build_sysroot.rs:1-265`
  - `compiler/rustc_codegen_cranelift/patches/0027-stdlib-128bit-atomic-operations.patch:1-87`
  - `compiler/rustc_codegen_cranelift/src/compiler_builtins.rs:1-180`
  - `compiler/rustc_codegen_gcc/build_system/src/build.rs:109-252` and
    `compiler/rustc_codegen_gcc/libgccjit.version:1`
  - `src/bootstrap/src/core/build_steps/compile.rs:502-668, 1565-1850`
  - `library/compiler-builtins/compiler-builtins/Cargo.toml:1-62`
  - `library/profiler_builtins/build.rs:1-80`
- **Support artifacts**:
  - `support/v5_tier1_sysroot_matrix.json`: Complete empirical build logs and
    exit codes across all 8 Tier 1 targets for unpatched `core`, patched `core`,
    full `library/sysroot` under Cranelift, and `core` under `rustc_codegen_gcc`.

## Revalidation

To revalidate Tier 1 sysroot compilation without LLVM on a newer `rustc`
revision:

1. Build `compiler/rustc_codegen_cranelift` with `RUSTC_BOOTSTRAP=1 cargo build
   --release`.
2. Apply `compiler/rustc_codegen_cranelift/patches/0027-stdlib-128bit-atomic-operations.patch`
   to a scratch copy of `library/` and run `cargo build --release --target
   <triple> --manifest-path library/sysroot/Cargo.toml --features "backtrace
   panic-unwind"` with `RUSTFLAGS="-Zforce-unstable-if-unmarked -Cpanic=abort
   -Zcodegen-backend=<path/to/librustc_codegen_cranelift.so> --sysroot=/dev/null
   -Zinline-mir"`.
