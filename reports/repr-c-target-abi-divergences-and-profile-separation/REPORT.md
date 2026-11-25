# Target-Specific `#[repr(C)]` ABI Divergences, Late-2026 ZST/HVA Fixes, and Layout-vs.-ABI Profile Separation

## Summary

Using `#[repr(C)]` as both Rust's stable field-order layout attribute and its external C calling-convention contract causes silent platform ABI mismatches whenever C psABIs depend on non-`align_of` field placement, zero-sized struct conventions, or toolchain C/C++ differences. Primary-source inspection of `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` paired with cross-target `clang-19` (`19.1.7`) and `gcc`/`g++` (`15.2.0`) probes establishes:

1. **AIX `f64` and Win32 `u64` layout-vs.-ABI splits:** On `powerpc64-ibm-aix`, `clang-19` places `struct Struct { double a1; uint8_t a2; }` at **`size=16, _Alignof=4`**, `struct Floats { double a; uint8_t b; double c; }` at `size=24`, and `struct LaterF64 { uint8_t b; double a; }` at **`size=12, _Alignof=4`**, because AIX's Power alignment rule increases aggregate `sizeof` / natural alignment to 8 when `double` is the *first* member while reporting `_Alignof=4` and keeping non-first `double` members 4-byte aligned, whereas `rustc` (`f64:32:64`) lays out `Struct` as `size=12, align=4`, `Floats` as `size=20, align=4`, and `LaterF64` as `size=12, align=4`. On `i686-pc-windows-msvc`, both `rustc` and `clang-19` give `struct Win32U64 { u32, u64 }` `size=16, align=8` (`_Alignof = 8`), even though MSVC 32-bit stack alignment guarantees only `4` bytes unless forced via `alignas`.
2. **Divergent empty-struct (`Empty {}`) conventions across Linux `i686` and Windows `x86_64`:**
   - On `i686-unknown-linux-gnu`, `clang-19` (C & C++), `gcc -m32` (C), and `g++ -m32` (C++) all return `struct Empty {}` via an invisible `sret` pointer popped by callee `ret $4`, while disagreeing on parameter slots (`gcc -m32` C, `clang-19` C, and `clang++-19` C++ pass `Empty` in `0` bytes; `g++ -m32` C++ shifts the next argument to `[esp+8]`); meanwhile `rustc` lowers both arguments and returns of `#[repr(C)] struct CZero {}` to `PassMode::Ignore` (`void ()` / no parameter).
   - On `x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu`, `PR #156112` (`9025bde4556c4c91f7730a9691cb25adbe61a4c8`) propagates `repr_c` onto `LayoutData` and routes `#[repr(C)]` ZSTs (including `[i32; 0]` and `#[repr(transparent)]` wrappers over `CZero`) through `make_indirect_from_ignore()` (`ptr align 1` argument, `ptr sret([0 x i8])` return) while keeping `()` and `#[repr(Rust)]` ZSTs as `Ignore`; by contrast, `clang-19 --target=x86_64-pc-windows-msvc` passes/returns `Empty {}` as `i32` in C mode and `i8` in C++ mode (`sizeof == 1`).
3. **Late-2026 `"trivial ABI"`, AArch64 `_Bool`/HVA, and `#[repr(C)]` enum discriminant fixes:**
   - `PR #157973` (`3bcfbadbc0011903cab2731a9087a5536f6c3aaf`) rewrites `core::primitive::fn` ABI-compatibility guarantees around `"trivial ABI"`, normatively excluding `#[repr(C)]` 1-ZSTs and zero-length arrays of non-trivial-ABI elements (such as `[CZero; 0]`).
   - `PR #159317` (`ad0c9dce27a22416b65946bc0010edaf22ac6c83`) removes global `zeroext`+`noundef` assumptions on `bool` FFI returns (`extern "C" fn(bool) -> bool` on `aarch64-unknown-linux-gnu` emits `define i1 @ret_bool(i1 %x)` without `zeroext`), restricting unconditional `bool` extension to rustic ABIs.
   - `PR #161394` (`e82904d34bad7e1c26d8001a343cc71c07b989e6`) switches Arm, AArch64, and PowerPC64 `is_homogeneous_aggregate` vector checks from aggregate total size to `unit.size.bits() == 64 || 128` (`#[repr(C)] struct HVA { a: F64x2, b: F64x2 }` lowers to `[2 x <2 x double>]` on `aarch64-unknown-linux-gnu`).
   - `PR #147017` (`b40a20f16df44bb6016dc6b18d0c2e6e96200483`) documents eager `isize` evaluation via `ReprOptions::discr_type()` before layout and tightens `repr_c_enums_larger_than_int` bounds checking.
4. **Architectural pressure to separate layout from C ABI profiles:** Upstream language/RFC proposals seek to decouple predictable declaration-ordered Rust layout (free of C toolchain quirks and usable as an internal deterministic representation) from explicit OS/toolchain C ABI profiles, constrained by Rust's requirement not to silently alter the ABI of existing `#[repr(C)]` definitions across editions or macro boundaries.

## Applicability

- **Examined subjects (`REPORT.json`):** `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, incorporating merged commits `PR #156112`, `PR #157973`, `PR #159317`, `PR #161394`, and `PR #147017`), `rust-lang/reference@956d1bd03d2a8934fc5041ecb04b33e55159c655`, `clang-19` (`19.1.7`), and `gcc`/`g++` (`Debian 15.2.0-14`, `15.2.0`).
- **Execution scope:** Cross-target `rustc` metadata/IR probes ran locally for `powerpc64-ibm-aix`, `i686-pc-windows-msvc`, `i686-unknown-linux-gnu`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `x86_64-unknown-linux-gnu`, and `aarch64-unknown-linux-gnu`. C/C++ comparisons ran with `clang-19`/`clang++-19` (cross-targeting `powerpc64-ibm-aix`, `i686-pc-windows-msvc`, `i686-unknown-linux-gnu`, `x86_64-pc-windows-msvc`) and native Debian `gcc`/`g++` `-m32`/`-m64`. Proprietary Microsoft `cl.exe` and IBM XL C/`ibm-clang` binaries were not executed.
- **Relation to existing corpus packages:** Complements without duplicating [`repr-c-layout-algebra-dst-tails-and-enum-tags`](../repr-c-layout-algebra-dst-tails-and-enum-tags/REPORT.md) (`#[repr(C, Int)]` vs. `#[repr(Int)]` enum layouts and C-enum tag widths), [`rust-cpp-ffi-abi-soundness-improper-ctypes-setjmp-errno-and-init-array`](../rust-cpp-ffi-abi-soundness-improper-ctypes-setjmp-errno-and-init-array/REPORT.md) (`improper_ctypes` blind spots and x86-64 empty-struct C vs. C++ layout mismatch), [`tier1-calling-conventions-fnabi-and-llvm-lowering`](../tier1-calling-conventions-fnabi-and-llvm-lowering/REPORT.md) (baseline 8-target psABI conventions), and [`abi-cross-testing-matrix-rustc-llvm-cranelift-gcc-clang`](../abi-cross-testing-matrix-rustc-llvm-cranelift-gcc-clang/REPORT.md) (x86-64 differential matrix).

## Findings

### 1. Target-Specific `#[repr(C)]` Data-Layout vs. C ABI Divergences

**Basis:** `source` (`3ef0c22cd`, `PR #156112`) + `execution` (`support/probe_repr_c_target_divergences.py`)

| Construct & Target | `rustc` (`3ef0c22cd`) | C / C++ Oracle (`clang-19` / `gcc` / `g++`) | Root Mechanism & Divergence |
| :--- | :--- | :--- | :--- |
| `Struct { a1: f64, a2: u8 }` (`powerpc64-ibm-aix`) | `size=12, align=4` | `clang-19` C: `size=16, _Alignof=4` | AIX C raises aggregate `sizeof` / natural alignment to 8 when `double` is the *first* member (`Floats { f64, u8, f64 }` is `24B` in `clang-19` vs. `20B` in `rustc`) while still reporting `_Alignof=4`, whereas `LaterF64 { u8, f64 }` is `size=12, _Alignof=4` in both `clang-19` and `rustc` (`powerpc64_ibm_aix.rs` sets `f64:32:64`). |
| `Win32U64 { a: u32, b: u64 }` (`i686-pc-windows-msvc`) | `size=16, align=8` | `clang-19` C: `size=16, _Alignof=8` | Layout matches MSVC `_Alignof`, but Win32 ABI only guarantees 4-byte stack alignment (`rustc` splits stack alignment vs. struct alignment rather than splitting `align_of::<u64>()`). |
| `Empty {}` (`i686-unknown-linux-gnu`) | `ret` -> `void ()`; `arg` -> ignored (`i32 %x`) | `gcc -m32` & `clang-19` C: `sret` (`ret $4`), `0B` arg<br>`clang++-19`: `sret` (`ret $4`), `0B` arg<br>`g++ -m32`: `sret` (`ret $4`), `4B` stack arg | Four-way mismatch: `rustc` ignores both arg and return; all four C/C++ compilers emit hidden `sret` return (`ret $4`); `g++ -m32` uniquely pushes 4 bytes for the empty argument (`movl 8(%esp), %eax`), whereas `clang++-19`, `clang-19`, and `gcc -m32` elide the arg (`movl 4(%esp), %eax`). |
| `Empty {}` (`x86_64-pc-windows-{msvc,gnu}`) | `repr(C) Empty` / `CArr0([i32; 0])` / `WrapCZero`: `ptr align 1 %_1` + `sret([0 x i8])`<br>`()` / `RZero` / `WrapUnit`: `Ignore` | `clang-19` C: `i32` return & `i32` arg<br>`clang++-19` C++: `i8` return & `i8` arg | `x86_win64.rs:52-66` (`PR #156112`) calls `arg.make_indirect_from_ignore()` whenever `arg.is_ignore() && arg.layout.is_repr_c()`. |

Note specifically how `PR #156112` (`9025bde455`) propagates `repr_c` onto `LayoutData`: `LayoutCalculator` sets `repr_c: true` for `#[repr(C)]` types, arrays of `repr_c` elements (`[CZero; 0]`), and `#[repr(transparent)]` wrappers containing any `repr_c` field (`WrapCZero`), ensuring `x86_win64.rs` treats `[CZero; 0]` and `WrapCZero` identically to `CZero` while leaving `()`, `[u8; 0]`, `#[repr(Rust)] struct RZero`, and `WrapUnit(())` ignored.

### 2. Late-2026 Semantic Clarifications and `FnAbi` Fixes (`#157973`, `#159317`, `#161394`, `#147017`)

**Basis:** `normative` (`rust-lang/rust` `core::primitive::fn`) + `source` + `execution`

1. **`"trivial ABI"` excludes `#[repr(C)]` ZSTs (`PR #157973`, `3bcfbadbc0`):** In `library/core/src/primitive_docs.rs:1832-1850`, function-pointer ABI compatibility replaces the blanket *"any two types with size 0 and alignment 1 are ABI-compatible"* rule with **"trivial ABI"**, which requires `size == 0`, `align == 1`, and being one of: a `#[repr(Rust)]` ADT (even with modifiers like `packed`), a tuple, a `#[repr(transparent)]` ADT whose *all* fields have trivial ABI, an array (even length `0`) whose *element* type has trivial ABI, `!`, or a function/closure item. `#[repr(C)]` 1-ZSTs (and arrays `[CZero; 0]`) do **not** have trivial ABI, matching `x86_win64.rs`'s indirect ZST passing.
2. **AArch64 `_Bool` FFI Return Masking (`PR #159317`, `ad0c9dce27`):** Prior to `ad0c9dce27`, `rustc_ty_utils::abi::arg_attrs_for_rust_scalar` attached `ArgExtension::Zext` + `NoUndef` to *every* `bool` scalar across all calling conventions, allowing LLVM callers on AArch64 to compare full 32-bit `w0` (`cmp w0, #0`) even when a C ABI permits upper bits `[8..31]` of a returned `_Bool` to hold garbage. `PR #159317` removes `scalar.is_bool()` from `arg_attrs_for_rust_scalar`, moves `extend_bool` exclusively into `adjust_for_rust_abi` (`callconv/mod.rs`), and lowers `extern "C" fn(bool) -> bool` on `aarch64-unknown-linux-gnu` to `define i1 @ret_bool(i1 %x)` (unextended, forcing callers to mask `tst w0, #0x1` / `and`).
3. **Homogeneous Vector Aggregates (`PR #161394`, `e82904d34b`):** In `compiler/rustc_target/src/callconv/{aarch64.rs, arm.rs, powerpc64.rs}` and `rustc_monomorphize/src/mono_checks/abi_check.rs`, `is_homogeneous_aggregate` previously checked `size.bits() == 64 || 128` (total aggregate size instead of lane-vector `unit.size`), rejecting multi-vector aggregates (`HVA { a: F64x2, b: F64x2 }`, 256 bits) from SIMD register passing (`q0`/`q1`). Checking `unit.size.bits() == 64 || 128` (`[2 x <2 x double>] @ret_hva([2 x <2 x double>] %0)` verified live on `3ef0c22cd`) restores AAPCS64 HVA lowering.
4. **`#[repr(C)]` Enum `isize` Eager Evaluation (`PR #147017`, `b40a20f16d`):** Before target C-`enum` width selection, `ReprOptions::discr_type()` defaults bare `#[repr(C)]` discriminants to `IntegerType::Pointer(true)` (`isize`), evaluating discriminant expressions on pointer-width integer ranges and diagnosing >32-bit values (`BigEnum { A = i64::MAX }`) with future-incompatibility lint `repr_c_enums_larger_than_int`.

### 3. Architectural Tension: Declaration-Ordered Layout vs. C ABI Profiles

**Basis:** `source` (`rustc_abi`) + `documentation` (public Rust RFC proposals)

Because `ReprFlags::IS_C` sets both `FIELD_ORDER_UNOPTIMIZABLE` (fixing field order and padding rules) and `ABI_UNOPTIMIZABLE` (triggering `#[repr(C)]` ZST indirection on Win64, preventing single-field scalar unboxing in `FnAbi`, and binding the type to platform C struct rules like AIX first-field `double` or Win32 `u64`), `#[repr(C)]` conflates two orthogonal needs:

1. **Predictable in-memory layout without C FFI quirks:** Users needing deterministic declaration order for wire protocols, IPC shared memory, or unsafe field projection cannot opt out of C ABI struct overhead (`ABI_UNOPTIMIZABLE` / Win64 empty-struct indirection / platform `f64` quirks). Unmerged design proposals (such as RFC #3845 `repr(ordered_fields)`, RFC #3718 relaxing transitive `aligned`-in-`packed` restrictions, RFC #3806 alignment attributes, and RFC #3470 `crABI`) explore separating a target-independent ordered field layout from C ABI profiles without breaking backward compatibility of `#[repr(C)]`.
2. **Retroactive evolution limits (`#[repr(C)]`, macros, editions):** Changing what `#[repr(C)]` or default C ABI emits across Rust editions faces a structural barrier: structs and `extern "C"` declarations cross crate boundaries with differing editions, and `macro_rules!` / procedural-macro token hygiene (`Span`) complicates inferring which edition owns an item's ABI contract—pushing profile selection toward explicit ABI strings (e.g., `"C"`, `"sysv64"`, `"win64"`), target triples, or opt-in target modifiers rather than silent edition-gated shifts of `#[repr(C)]`.

## Boundaries

- **Proprietary MSVC `cl.exe` and IBM AIX XL C / Open XL (`not examined`):** Windows and AIX C/C++ behavior was observed via `clang-19` / `clang++-19` cross-targeting (`--target=powerpc64-ibm-aix`, `--target=i686-pc-windows-msvc`, `--target=x86_64-pc-windows-msvc`), not proprietary vendor toolchains (note MSVC `cl.exe` in strict C mode rejects empty `struct {}` altogether with `C2016`, whereas Clang/GCC accept it as an extension).
- **Pre-`PR #159317` / Pre-`PR #161394` live `aarch64` IR execution (`unsupported` locally without `core`):** Installed stable toolchains `1.96.0` and `1.100.0` lack prebuilt `aarch64-unknown-linux-gnu` `core` and disallow `#![no_core]` (`E0554`), so pre-fix vs. post-fix AArch64 comparison rests on source diffs (`ad0c9dce27`, `e82904d34b`) plus live `3ef0c22cd` IR output.
- **Unmerged RFCs (`unknown` stabilization):** RFCs #3845, #3718, #3806, #3470, and #3659 are unmerged proposals and carry no normative status in `rust-lang/reference@956d1bd0`.

## Evidence

- **Primary compiler sources (`rust-lang/rust`):**
  - `compiler/rustc_target/src/callconv/x86_win64.rs:52-66` and `PR #156112` (`9025bde4556c4c91f7730a9691cb25adbe61a4c8`) — `make_indirect_from_ignore()` for `arg.layout.is_repr_c()`.
  - `library/core/src/primitive_docs.rs:1832-1850` (`PR #157973`, `3bcfbadbc0011903cab2731a9087a5536f6c3aaf`) — `"trivial ABI"` specification.
  - `compiler/rustc_target/src/callconv/mod.rs:751-771` and `compiler/rustc_ty_utils/src/abi.rs:329-338` (`PR #159317`, `ad0c9dce27a22416b65946bc0010edaf22ac6c83`) — AArch64 `_Bool` FFI return fix.
  - `compiler/rustc_target/src/callconv/{aarch64.rs:35-38, arm.rs:26-29, powerpc64.rs:36-39}` and `compiler/rustc_monomorphize/src/mono_checks/abi_check.rs:65-75` (`PR #161394`, `e82904d34bad7e1c26d8001a343cc71c07b989e6`) — HVA `unit.size` fix.
  - `compiler/rustc_abi/src/lib.rs:154-156` and `compiler/rustc_hir_analysis/src/collect.rs:605-675` (`PR #147017`, `b40a20f16df44bb6016dc6b18d0c2e6e96200483`) — `discr_type()` and `repr_c_enums_larger_than_int`.
  - `compiler/rustc_target/src/spec/targets/powerpc64_ibm_aix.rs` (`f64:32:64`).
- **Observed execution receipts (`2026-11-25`, reproducible via `support/probe_repr_c_target_divergences.py`):**
  - AIX `Struct` / `Floats` / `LaterF64`: `clang-19` `size = 16 / 24 / 12` with `_Alignof = 4` on `Struct` and `LaterF64`; `rustc` `size = 12 / 20 / 12` with `align = 4` (exact `#[rustc_dump_layout]` vs. LLVM IR constant returns).
  - `i686` `Empty {}`: `gcc -m32` C & `clang-19` C & `clang++-19` C++ `movl 4(%esp), %eax` (`0B` arg) + `ret $4` (`sret`); `g++ -m32` C++ `movl 8(%esp), %eax` (`4B` arg) + `ret $4`; `rustc` `define i32 @arg_c_empty(i32 %x)` & `define void @ret_c_empty()`.
  - `Win64` ZSTs: `rustc` `define void @ret_c_empty(ptr sret([0 x i8]) align 1 %_0)` vs. `define void @ret_rust_zst()`; `clang-19` C `define i32 @ret_empty()`; `clang++-19` C++ `define i8 @"?ret_empty@@YA?AUEmpty@@XZ"()`.
  - AArch64 `3ef0c22cd`: `define i1 @ret_bool(i1 %x)` and `define [2 x <2 x double>] @ret_hva([2 x <2 x double>] %0)`.

## Revalidation

Run the standalone revalidation script from this report package directory (requires `rustc +nightly` with `#![feature(no_core, rustc_attrs, repr_simd)]`, `clang-19`/`clang++-19`, and `gcc`/`g++` with 32-bit `-m32` multilib):

```bash
python3 support/probe_repr_c_target_divergences.py
```

Verify whether `rustc --target=powerpc64-ibm-aix` still reports `Size(12 bytes)` / `Size(20 bytes)` for `Struct` / `Floats` against `clang-19`'s `16` / `24`, whether `i686` `Empty {}` still diverges from C/C++ `sret`, and whether `x86_64-pc-windows-msvc` continues passing `#[repr(C)]` ZSTs indirectly via `ptr` / `sret`.
