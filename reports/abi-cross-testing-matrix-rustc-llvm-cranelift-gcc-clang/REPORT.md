# Cross-Compiler ABI Testing Matrix: `rustc` (LLVM and Cranelift), Clang, and GCC Across Tier 1 Targets

## Summary

Executing a 16-pair live caller $\times$ callee cross-compiler differential harness (`rustc_llvm 1.99.1`, `rustc_cranelift`, `clang-19`, and `gcc-14`) on `x86_64-unknown-linux-gnu` alongside an 8-target LLVM IR & assembly calling-convention verification sweep across all Tier 1 targets establishes:

1. **100% Live Execution Parity Across All 16 Caller $\times$ Callee Pairs on SysV `x86_64` (`support/abi_cross_test_matrix.csv`):**
   - All $4 \times 4 = 16$ caller $\times$ callee combinations (`rustc_llvm`, `rustc_cranelift`, `clang-19`, `gcc-14`) pass **10/10 (`160/160` total link-and-run checks)** on `x86_64-unknown-linux-gnu`, covering scalar sign/zero extension (`u8`, `i16`, `u32`, `i64`, `f32`, `f64`), 128-bit integers (`u128` / `i128` split across `%rdi:%rsi`, `%rdx:%rcx`, and `%rax:%rdx`), two-eightbyte `INTEGER` structs (`PairI64`), $>16\text{-byte}$ `MEMORY` structs returned via hidden `sret` pointer (`BigStruct24`), 4-float aggregates (`HfaF32x4` packed into two `SSE` `<2 x float>` / `double` registers `%xmm0:%xmm1`), mixed integer+float eightbytes (`MixedIntFloat`: `{ u32, f32 }` coerced into a single 64-bit `INTEGER` eightbyte in `%rdi`), `#[repr(C, packed)]` unaligned structs crossing an eightbyte boundary (`PackedCross8` passed via stack `byval`), 16-byte aligned structs (`Aligned16Struct`), and 10-argument stack spill offsets.
2. **Five Verified Cross-Compiler ABI Representation & Lowering Divergences (`support/known_abi_incompatibilities.json`):**
   - **`ABI-01` (`f128` / `__float128` on `x86_64-pc-windows-gnu` MinGW):** `rustc 1.99.1` lowers `extern "C" fn(f128) -> f128` on `x86_64-pc-windows-gnu` to indirect pass-by-pointer and hidden `sret` return (`define void @edge_f128(ptr sret([16 x i8]) align 16 %_0, ptr align 16 %x)`), whereas `clang-19 -target x86_64-pc-windows-gnu` passes and returns `__float128` directly in `XMM0` (`define dso_local fp128 @edge_f128(fp128 noundef returned %0)`). Calling between `rustc` and `clang` with `f128` on MinGW corrupts `RCX` (treating an `XMM0` value as a return pointer) and crashes immediately.
   - **`ABI-02` (`HfaF32x4` Coercion Type in SysV `x86_64` LLVM IR):** On `x86_64-unknown-linux-gnu`, `rustc 1.99.1` lowers a 4-`f32` struct to `{ double, double }` (`%xmm0`, `%xmm1`), whereas `clang-19` lowers it to `<2 x float>, <2 x float>` (`%xmm0`, `%xmm1`). While both occupy the low 64 bits of `%xmm0` and `%xmm1` at the machine-register level (passing live execution), IR-level LTO or CFI signature matching (`-Z sanitizer=cfi`) sees distinct LLVM function types.
   - **`ABI-03` (`u128` / `__int128` Parameter Representation in SysV `x86_64` and `AAPCS64` LLVM IR):** `rustc 1.99.1` emits scalar `i128 noundef %x` in LLVM IR, whereas `clang-19` splits `__int128` in front-end IR into `(i64 noundef %0, i64 noundef %1)`. Both lower to identical register pairs (`%rdi:%rsi` on SysV `x86_64`, even-aligned `x0:x1` on `AAPCS64`). On `x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu`, both `rustc 1.99.1` and `clang-19` pass 128-bit integers indirectly by pointer (`ptr align 16`) and return via `XMM0` (reflecting the Rust 1.78 / LLVM 18 Win64 `i128` fix).
   - **`ABI-04` (`#[repr(C, packed)]` Structs Crossing Eightbyte Boundaries Across ISAs):** `PackedCross8` (`10` bytes: `u8`, unaligned `u64`, `u8`) is passed on the stack via `byval([10 x i8])` on `x86_64-unknown-linux-gnu` and `i686-*`, by indirect pointer (`ptr align 1`) on `x86_64-pc-windows-*`, and in two 64-bit general-purpose registers (`[2 x i64]`) on `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, and `aarch64-pc-windows-msvc`.
   - **`ABI-05` (`Zero-Sized Types` in `#[repr(C)]` Structs Across C vs. C++ Callers):** `WithZst { a: u32, z: (), b: u32 }` has size `8` in Rust and GNU C (`struct {}`), packing into a single `i64` register on `x86_64` and `aarch64` (`byval([8 x i8])` on `i686`), whereas standard C++ gives an empty struct field size `1` (plus `3` bytes padding, total size `12` bytes), causing an ABI layout mismatch unless `[[no_unique_address]]` is used in C++.

## Applicability

- **Extends:** `tier1-calling-conventions-fnabi-and-llvm-lowering`, `rustc-layout-computation-target-datalayouts-and-parametricity`
- **Subjects and Scope:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), specifically `compiler/rustc_target/src/callconv/{x86_64.rs, x86_win64.rs, x86.rs, aarch64.rs}` and `compiler/rustc_codegen_cranelift/src/abi/`.
  - `clang-19` (`19.1.7`) and `x86_64-linux-gnu-gcc` (`14.2.0`).
  - All 8 Tier 1 targets: `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `i686-pc-windows-msvc`, `aarch64-apple-darwin`, and `aarch64-pc-windows-msvc`.

## Findings

### 1. Live Cross-Compiler Caller $\times$ Callee Matrix (`x86_64-unknown-linux-gnu`)

**Basis: execution (`support/run_abi_cross_tests.py`, `support/abi_cross_test_matrix.csv`).**

| Caller Compiler | Callee Compiler | Mode | Signatures Tested | Passed | Failed | Verified Edge Cases |
| :--- | :--- | :--- | :---: | :---: | :---: | :--- |
| `rustc_llvm 1.99.1` | `rustc_llvm 1.99.1` | Live execution | `10` | `10` | `0` | `u128`/`i128`, `sret`, `HFA`, mixed int/float, `packed`, `align(16)`, stack spill |
| `rustc_llvm 1.99.1` | `rustc_cranelift` | Live execution | `10` | `10` | `0` | Full ABI compatibility between LLVM and Cranelift object files |
| `rustc_llvm 1.99.1` | `clang-19` | Live execution | `10` | `10` | `0` | `{ double, double }` vs. `<2 x float>` HFA register compatibility |
| `rustc_llvm 1.99.1` | `gcc-14` | Live execution | `10` | `10` | `0` | `__int128` register-pair splitting (`%rdi:%rsi`, `%rdx:%rcx`) |
| `rustc_cranelift` | `rustc_llvm 1.99.1` | Live execution | `10` | `10` | `0` | Cranelift caller $\to$ LLVM callee across all 10 ABI classes |
| `rustc_cranelift` | `rustc_cranelift` | Live execution | `10` | `10` | `0` | Cranelift self-consistency |
| `rustc_cranelift` | `clang-19` | Live execution | `10` | `10` | `0` | Cranelift caller $\to$ Clang callee |
| `rustc_cranelift` | `gcc-14` | Live execution | `10` | `10` | `0` | Cranelift caller $\to$ GCC callee |
| `clang-19` | `rustc_llvm 1.99.1` | Live execution | `10` | `10` | `0` | Clang caller $\to$ `rustc_llvm` callee |
| `clang-19` | `rustc_cranelift` | Live execution | `10` | `10` | `0` | Clang caller $\to$ `rustc_cranelift` callee |
| `clang-19` | `clang-19` | Live execution | `10` | `10` | `0` | Clang self-consistency |
| `clang-19` | `gcc-14` | Live execution | `10` | `10` | `0` | Clang caller $\to$ GCC callee |
| `gcc-14` | `rustc_llvm 1.99.1` | Live execution | `10` | `10` | `0` | GCC caller $\to$ `rustc_llvm` callee |
| `gcc-14` | `rustc_cranelift` | Live execution | `10` | `10` | `0` | GCC caller $\to$ `rustc_cranelift` callee |
| `gcc-14` | `clang-19` | Live execution | `10` | `10` | `0` | GCC caller $\to$ Clang callee |
| `gcc-14` | `gcc-14` | Live execution | `10` | `10` | `0` | GCC self-consistency |

---

### 2. Cross-Target Calling-Convention Lowering Across All 8 Tier 1 Targets

**Basis: execution + source (`support/known_abi_incompatibilities.json`, `compiler/rustc_target/src/callconv/`).**

| Edge Signature | `x86_64-unknown-linux-gnu` (SysV64) | `aarch64-{linux,darwin,msvc}` (AAPCS64) | `x86_64-pc-windows-{msvc,gnu}` (Win64) | `i686-{linux,msvc}` (cdecl / x86-32) |
| :--- | :--- | :--- | :--- | :--- |
| **`edge_u128(u128) -> u128`** | `i128 %x` $\to$ `%rdi:%rsi`, ret `%rax:%rdx` (Clang IR: `i64, i64`) | `i128 %x` $\to$ `x0:x1`, ret `x0:x1` | Arg: `ptr align 16 %x` (indirect in `%rcx`), Ret: `<16 x i8>` in `%xmm0` | Arg: `i128` on stack, Ret: hidden `sret` or `%eax:%edx:...` (`i128`) |
| **`edge_f16(f16) -> f16`** | `half %x` in `%xmm0` | `half %x` in `h0` (`v0`) | `half %x` in `%xmm0` | `half %x` (`__gnu_f2h_ieee` / `xmm0` with SSE2) |
| **`edge_f128(f128) -> f128`** | `fp128 %x` in `%xmm0` | `fp128 %x` in `q0` (`v0`) | **`rustc`:** `ptr sret([16 x i8])`, `ptr align 16 %x`<br>**`clang` (MinGW):** `fp128 %0` in `%xmm0` (**MISMATCH!**) | `fp128 %x` on stack / `xmm0` |
| **`edge_hfa(HfaF32x4) -> HfaF32x4`** | **`rustc`:** `{ double, double }` (`%xmm0:%xmm1`)<br>**`clang`:** `<2 x float>, <2 x float>` | `[4 x float]` in `s0, s1, s2, s3` (true 4-register HFA!) | `ptr sret([16 x i8])`, `ptr %v` (Win64 x86_64 has no HFA for `extern "C"`) | `ptr sret([16 x i8])`, `ptr byval([16 x i8])` |
| **`edge_packed(PackedCross8) -> u64`** | `ptr byval([10 x i8])` on stack (unaligned field crosses 8B boundary) | `[2 x i64] %0` in `x0, x1` (AAPCS64 passes composite $\le 16\text{B}$ in 2 GP regs regardless of internal packing!) | `ptr align 1 %p` (indirect pointer in `%rcx`; size $10 \notin \{1,2,4,8\}$) | `ptr byval([10 x i8])` on stack |
| **`edge_with_zst(WithZst) -> u32`** | `i64 %0` in `%rdi` (ZST `()` field elided) | `i64 %0` in `x0` | `i64 %0` in `%rcx` | `ptr byval([8 x i8])` on stack |

**Critical Takeaway for a Verified `rustc` Replacement:**
A verified `FnAbi` computation cannot treat `extern "C"` struct classification as a simple size threshold:
1. On **SysV `x86_64`** (`compiler/rustc_target/src/callconv/x86_64.rs`), any field whose offset is not a multiple of its natural alignment (`#[repr(C, packed)]` `q1: u64` at byte offset `1` in `PackedCross8`) forces the entire aggregate into the `MEMORY` class (`byval` on the stack), whereas on **AAPCS64** (`compiler/rustc_target/src/callconv/aarch64.rs`), any non-HFA composite $\le 16$ bytes is unconditionally loaded into `[2 x i64]` registers (`x0, x1`) regardless of internal field alignment.
2. On **`x86_64-pc-windows-gnu`**, `rustc`'s `x86_win64.rs` currently applies MSVC's indirect-pointer rule to `f128`, diverging from GCC/Clang's MinGW ABI which passes `__float128` in `XMM0`.

## Boundaries

1. **Proprietary MSVC `cl.exe` and Apple Xcode Clang Execution (`unsupported` without EULA SDKs):** Cross-target verification on `*-pc-windows-msvc` and `aarch64-apple-darwin` was performed by comparing `rustc 1.99.1 --target <triple> --emit=llvm-ir,asm` against `clang-19 -target <triple> -S -emit-llvm` without downloading EULA-gated Microsoft Visual C++ or Apple macOS SDK sysroots.
2. **Cranelift `i686` Target Absence:** `rustc_codegen_cranelift` rejects `i686-unknown-linux-gnu` and `i686-pc-windows-msvc` at target initialization time.

## Evidence

- **`rustc 1.99.1` ABI Classification Source (`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_target/src/callconv/x86_64.rs` (SysV64 eightbyte classification, unaligned field `Memory` fallback, `SSE` pair coalescing into `double`).
  - `compiler/rustc_target/src/callconv/x86_win64.rs` (Win64 `1/2/4/8`-byte power-of-two integer register rule, `i128` and `f128` pointer indirection).
  - `compiler/rustc_target/src/callconv/aarch64.rs` (AAPCS64 HFA/HVA detection and $\le 16$-byte `[2 x i64]` register block passing).
- **Preserved Package Support Artifacts (`support/`):**
  - [`support/run_abi_cross_tests.py`](support/run_abi_cross_tests.py): Reproducible 16-pair live caller $\times$ callee harness and 8-target IR signature extractor.
  - [`support/abi_cross_test_matrix.csv`](support/abi_cross_test_matrix.csv): Complete 24-row test matrix across live execution and cross-target verification.
  - [`support/known_abi_incompatibilities.json`](support/known_abi_incompatibilities.json): Exact LLVM IR signatures per Tier 1 target and catalog of 5 cross-compiler ABI divergences.

## Revalidation

```bash
python3 support/run_abi_cross_tests.py
```
Verify that all 16 live caller $\times$ callee pairs print `ALL_10_ABI_TESTS_PASSED` and check `support/known_abi_incompatibilities.json` for any changes in `@edge_f128` or `@edge_u128` lowering when upgrading `rustc` or LLVM.
