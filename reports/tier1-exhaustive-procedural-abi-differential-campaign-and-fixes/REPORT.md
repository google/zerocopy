# Exhaustive Tier 1 Procedural ABI Differential Campaign and Cross-Compiler Divergence Resolution

## Summary

Executing a procedural 256-signature-per-target calling-convention campaign (`2,048` total target-signature compilations across the 8 Tier 1 targets and `1,674` cross-compiler LLVM IR & assembly comparisons against `clang-19` `19.1.7`, paired with live caller $\times$ callee execution across `rustc_llvm 1.99.1`, `rustc_codegen_cranelift`, `clang-19`, and `gcc 15.2.0` on native `x86_64-unknown-linux-gnu`, native IA-32 / `qemu-i386` `i686-unknown-linux-gnu`, and `qemu-aarch64` `aarch64-unknown-linux-gnu` in [`support/run_8target_abi_campaign.py`](support/run_8target_abi_campaign.py) and [`support/tier1_abi_campaign_results.json`](support/tier1_abi_campaign_results.json)) establishes seven concrete calling-convention divergences, compiler bugs, and backend rules:

1. **`ABI-01` — Live Crash Mismatch on `x86_64-pc-windows-gnu` (`f128` / `__float128` Return & Argument Passing):**
   - In `compiler/rustc_target/src/callconv/x86_win64.rs:30-39`, `compute_abi_info` special-cases `Primitive::Int(Integer::I128, _)` return values to `Reg::opaque_vector(Size::from_bits(128))` (`<16 x i8>` in `%xmm0`), but falls through to `else if a.layout.size.bytes() > 8 { a.make_indirect(); }` for `Primitive::Float(Float::F128)`.
   - Consequently, `rustc 1.99.1` lowers `extern "C" fn(f128) -> f128` (`@f1_f128_id` and `@f1_f128_pair`) on `x86_64-pc-windows-gnu` to indirect `ptr sret([16 x i8]) align 16` in `%rcx` and `ptr align 16` in `%rdx`, whereas `clang-19 --target=x86_64-w64-mingw32` lowers `f128` to `define dso_local fp128 @f1_f128_id(fp128 %0)` in `%xmm0`.
2. **`ABI-02` — SysV `x86_64` Eightbyte Coercion Type Differences (`f16` and `f32` Aggregates):**
   - Across `129` of `218` C-equivalent signatures on `x86_64-unknown-linux-gnu`, `rustc 1.99.1` and `clang-19` emit different LLVM IR types that lower to the same physical registers (`%xmm0`, `%xmm1`): `rustc` coerces `F16Pair { a: f16, b: f16 }` (`4` bytes) to `float` (`Reg::f32()`) vs. Clang's `<2 x half>`, `F16F32` and `HfaF16x4` (`8` bytes) to `double` vs. Clang's `<4 x half>`, and `HfaF32x4` (`16` bytes) to `{ double, double }` vs. Clang's `<2 x float>, <2 x float>`.
3. **`ABI-03` — Newly Discovered Live Runtime Mismatch on SysV `x86_64` When `u128` Straddles the 6th GPR (`%r9` Backfilling):**
   - Consider `extern "C" fn(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, x: u128, after: u64) -> u64` (`@f2_u128_straddle_gpr5_scalar` / `@abi_straddle_u128_after`), where the first 5 parameters consume `%rdi, %rsi, %rdx, %rcx, %r8`, leaving exactly `1` available GPR (`%r9`, `int_regs == 1`).
   - Because `x: u128` requires `2` GPRs (`needed_int = 2`), it spills to the stack at `8(%rsp), 16(%rsp)`.
   - In **`rustc_llvm 1.99.1` (`LLVM 23.1.1`)** and **`gcc 15.2.0`**, `%r9` remains available (`int_regs` stays `1` in `compiler/rustc_target/src/callconv/x86_64.rs:210-224`), so the 7th parameter `after: u64` (or a 1-eightbyte struct `Single64(u64)`) is passed in **`%r9`** (`xorq %r9, %rdi`), and live execution returns the expected `0x42424242`.
   - In **`clang-19` (`LLVM 19.1.7`)** and **`rustc_codegen_cranelift` (`0.1.0`)**, spilling `i128` when `1` GPR remains marks all integer registers as exhausted, placing `after` on the stack at **`24(%rsp)`** (`0x20(%rbp)` in Cranelift)! Calling a `clang-19` or `rustc_codegen_cranelift` callee from a `rustc_llvm 1.99.1` caller silently reads garbage from `24(%rsp)` (`STRADDLE_AFTER=0x3` instead of `0x42424242`).
4. **`ABI-04` — Packed Unaligned Structs (`#[repr(C, packed(1..4))]`) Crossing Eightbyte Boundaries:**
   - `Packed1Cross8`, `Packed2Cross8`, and `Packed4Cross8` contain a `u64` field at an offset not aligned to 8 bytes. On `x86_64-unknown-linux-gnu` and `i686-*`, `x86_64.rs:64` forces the aggregate to `Memory` (`byval` on stack); on `x86_64-pc-windows-*`, size $\notin \{1, 2, 4, 8\}$ forces `Indirect` (`ptr align 1` in `%rcx`); on all three `aarch64-*` targets, `aarch64.rs:149-155` classifies any non-HFA composite $\le 16\text{ B}$ into `[2 x i64]` (`x0, x1`) regardless of internal field alignment (verified live under `qemu-aarch64`).
5. **`ABI-05` — AArch64 Sub-Target Divergences (`AAPCS` Linux vs. `DarwinPCS` macOS vs. `Win64` Windows ARM64):**
   - `fn(u32, u128)`: Linux and Windows ARM64 even-align `u128` to `x2:x3` (skipping `x1`), whereas Darwin passes `u128` in `x1:x2`. Conversely, for `#[repr(C, align(16))] struct Align16Pair(u64, u64)` (`unadjusted_abi_align = 8`, `abi_align = 16`), `aarch64.rs:140-154` uses `unadjusted_abi_align` on Linux `AAPCS` (`[2 x i64]` in `x1, x2`) and `align.abi` on Darwin/WinARM64 (`i128` in `x2, x3`).
   - Stack packing (`@f5_darwin_tight_stack_pack`): After `x0..x7` are exhausted, Darwin packs `u8, u16, u32, u8, u64` on the stack at natural 1/2/4/8-byte offsets (`[sp]`, `[sp, #2]`, `[sp, #4]`, `[sp, #8]`, `[sp, #16]`) with caller `signext`/`zeroext`, whereas Linux and Windows ARM64 allocate 8-byte slots per argument.
   - `VaList` (`library/core/src/ffi/va_list.rs:41-229`, stabilized in Rust 1.99.0 via `VaList::next_arg`): Linux `aarch64` uses a 32-byte `VaListInner { stack, gr_top, vr_top, gr_offs, vr_offs }` struct; Linux `x86_64` uses a 24-byte `#[rustc_pass_indirectly_in_non_rustic_abis]` `VaListInner { gp_offset, fp_offset, overflow_arg_area, reg_save_area }`; and Darwin `aarch64`, Windows (`x64`, `x86`, `arm64`), and `i686` Linux use a flat `*const c_void` pointer.
6. **`ABI-06` — `#[repr(simd)]` Target-Feature Gates and Array-Backed HVA Mismatch on AArch64:**
   - In `extern "Rust"`, `BackendRepr::SimdVector` is unconditionally passed via `PassMode::Indirect { on_stack: false }` so callers and callees with differing `-C target-feature` flags never disagree on vector register width.
   - In `extern "C"`, `rustc 1.99.1` rejects `SimdF32x8` (`256-bit`) on `x86_64`/`i686` unless `#[target_feature(enable = "avx")]` is present, and rejects `SimdF32x8` on `aarch64-*` unconditionally (`error: this function definition uses SIMD vector type SimdF32x8 which is not currently supported with the chosen ABI`).
   - For `#[repr(C)] struct HvaSimd2 { a: SimdF32x4, b: SimdF32x4 }` (`32` bytes), `clang-19 --target=aarch64-unknown-linux-gnu` classifies `struct HvaSimd2` (`2 x __attribute__((vector_size(16)))`) as a 2-element Homogeneous Short-Vector Aggregate (`[2 x <4 x float>]` in `q0, q1`), whereas `rustc 1.99.1` classifies `HvaSimd2` as a 32-byte non-homogeneous memory aggregate (`ptr %v`, `sret` in `x8`) because `SimdF32x4([f32; 4])` uses an array field inside `#[repr(simd)]`.
7. **`ABI-07` & `ABI-08` — `extern "rust-cold"` `SIGSEGV` ICE on `i686-unknown-linux-gnu` and Cranelift C-Variadic Callee Rejection:**
   - **`ABI-07` (`rustc 1.99.1` LLVM `23.1.1` `SIGSEGV` on `i686-unknown-linux-gnu`):** `compiler/rustc_target/src/spec/abi_map.rs:104-105` maps `ExternAbi::RustCold` to `CanonAbi::Rust` only when `self.os == OsKind::Windows`, leaving 32-bit `i686-unknown-linux-gnu` as `CanonAbi::RustCold`. Then `compiler/rustc_codegen_llvm/src/abi.rs:723` lowers `CanonAbi::RustCold => llvm::PreserveMost` (`preserve_mostcc`) without checking `Arch::X86_64 | Arch::AArch64` (unlike `CanonAbi::RustPreserveNone` on lines `724-727`). Because LLVM's 32-bit x86 backend does not support `CallingConv::PreserveMost`, compiling any `extern "rust-cold" fn` on `i686-unknown-linux-gnu` crashes `rustc 1.99.1` with `SIGSEGV` (`rc = -11`) inside `libLLVM.so` (`FPPassManager::runOnFunction`).
   - **`ABI-08` (`rustc_codegen_cranelift` C-Variadic Definition Rejection):** Cranelift compiles calls to C-variadic functions but aborts with `error: Defining variadic functions is not yet supported by Cranelift` when compiling a C-variadic callee (`extern "C" fn(n: u32, mut ap: ...)`).

## Applicability

- **Extends:** `abi-cross-testing-matrix-rustc-llvm-cranelift-gcc-clang`, `tier1-calling-conventions-fnabi-and-llvm-lowering`, `target-features-implications-detection-and-abi-effects`
- **Subjects Examined:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, for `rustc_codegen_cranelift`);
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`);
  - `clang-19` (`19.1.7`) and `gcc` (`15.2.0`);
  - `qemu-i386` and `qemu-aarch64` (`11.1.2`) plus native `x86_64` and IA-32 execution on Intel Xeon Ice Lake-SP.

## Findings

### 1. Per-Target Procedural Campaign Summary (`256` Signatures $\times$ `8` Targets = `2,048` Checks)

`Basis: execution (support/run_8target_abi_campaign.py, support/tier1_abi_campaign_results.json)`

| Tier 1 Target | Procedural Signatures Compiled (`rustc 1.99.1`) | LLVM IR Definitions Emitted (`-Zmerge-functions=disabled`) | C-Equivalent Signatures Compared (`clang-19`) | Exact Normalized LLVM IR Matches | Register-Compatible IR Coercion Differences | True Calling-Convention Mismatches |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `x86_64-unknown-linux-gnu` | `256` | `256` | `218` | `89` | `129` | `0` (plus `ABI-03` live `%r9` straddle vs Clang 19) |
| `aarch64-unknown-linux-gnu` | `256` | `256` | `222` | `150` | `72` | `0` (plus `ABI-06` array-backed `HvaSimd2`) |
| `i686-unknown-linux-gnu` | `256` | `256` | `179` | `52` | `127` | `0` (plus `ABI-07` `rust-cold` `SIGSEGV`) |
| `x86_64-pc-windows-msvc` | `256` | `256` | `216` | `72` | `144` | `0` |
| `x86_64-pc-windows-gnu` | `256` | `256` | `218` | `73` | `143` | **`2` (`ABI-01`: `f1_f128_id`, `f1_f128_pair`)** |
| `i686-pc-windows-msvc` | `256` | `256` | `179` | `19` | `160` | `0` |
| `aarch64-apple-darwin` | `256` | `256` | `222` | `148` | `74` | `0` |
| `aarch64-pc-windows-msvc` | `256` | `256` | `220` | `147` | `73` | `0` |
| **Total** | **`2,048`** | **`2,048`** | **`1,674`** | **`750`** | **`922`** | **`2` + `ABI-03`, `ABI-06`, `ABI-07`, `ABI-08`** |

---

### 2. Live Execution Verification Across Native `x86_64`, `i686`, and `qemu-aarch64`

`Basis: execution (support/tier1_abi_campaign_results.json)`

| Execution Environment | Caller $\to$ Callee Pair | Standard ABI Suite (`f16`, `u128`, `HFA4`, `PackedCross8`, `Big24`, `VaList`) | `ABI-03` 6th-GPR `u128` Straddle (`abi_straddle_u128_after`) | Observed Machine-Code Behavior |
| :--- | :--- | :---: | :---: | :--- |
| `x86_64-unknown-linux-gnu` (Native) | `rustc_llvm 1.99.1` $\to$ `rustc_llvm 1.99.1` | **PASS (`6/6`)** | **PASS (`0x42424242`)** | `u128` spills to `8(%rsp), 16(%rsp)`; 7th arg `after` passed in `%r9` |
| `x86_64-unknown-linux-gnu` (Native) | `rustc_llvm 1.99.1` $\to$ `gcc 15.2.0` | **PASS (`6/6`)** | **PASS (`0x42424242`)** | GCC 15.2.0 backfills `%r9` for `after`, matching `rustc 1.99.1` / LLVM 23 |
| `x86_64-unknown-linux-gnu` (Native) | `rustc_llvm 1.99.1` $\to$ `clang-19` (`19.1.7`) | **PASS (`6/6`)** | **MISMATCH (`0x3` vs `0x42424242`)** | Clang 19 burns `%r9` when `i128` spills, reading `after` from `24(%rsp)` |
| `x86_64-unknown-linux-gnu` (Native) | `rustc_llvm 1.99.1` $\to$ `rustc_cranelift` | **PASS (`5/5`, no varargs def)** | **MISMATCH (`0x3` vs `0x42424242`)** | Cranelift burns `%r9` when `i128` spills, reading `after` from `0x20(%rbp)` |
| `i686-unknown-linux-gnu` (Native IA-32 + `qemu-i386`) | `rustc_llvm 1.99.1` $\to$ `clang-19` | **PASS (`exit 0` on both)** | N/A (`i686` stack args) | Verifies `cdecl` hidden `sret` (`retl $4`), `fastcall` (`%ecx, %edx`), and `stdcall` callee-pop |
| `aarch64-unknown-linux-gnu` (`qemu-aarch64 -cpu max`) | `rustc_llvm 1.99.1` $\to$ `clang-19` | **PASS (`exit 0`)** | N/A (even-reg `x6:x7` or stack) | Verifies `u128` even-pair `x2:x3` (skipping `x1`), 4-float HFA (`s0..s3`) vs 5-float indirect cliff, `Packed1Cross8` in `x0, x1`, and `sret` in `x8` (`XR`) with all 8 GPRs `x0..x7` live |

---

### 3. Exact `rustc_target` and Backend Patch Specifications for `ABI-01`..`ABI-08`

`Basis: source + derived (compiler/rustc_target/src/callconv/, compiler/rustc_target/src/spec/abi_map.rs, compiler/rustc_codegen_llvm/src/abi.rs)`

1. **Fixing `ABI-01` (`f128` on `x86_64-pc-windows-gnu` in `compiler/rustc_target/src/callconv/x86_win64.rs:30-40`):**
   - Replace the `I128`-only return check with a check that also returns `F128` in `xmm0` (`Reg::f128()` / `Reg::opaque_vector(Size::from_bits(128))`) on non-MSVC Windows x64 targets (`!cx.target_spec().is_like_msvc`).
2. **Fixing `ABI-03` (`u128` 6th-GPR straddling in `rustc_codegen_cranelift` and verified `MiniMach`):**
   - When lowering `FnAbi` on System V AMD64 (`x86_64`), a 16-byte `ScalarInt(16)` (`u128`/`i128`) parameter requires `2` available GPRs (`int_avail >= 2`). When `int_avail == 1` (`%r9` free), `u128` must be assigned to stack slots `[rsp + offset]` **without** decrementing `int_avail`, leaving `%r9` available for a subsequent 8-byte integer or 1-eightbyte `INTEGER` aggregate parameter.
3. **Fixing `ABI-06` (`#[repr(simd)]` in `LayoutData::homogeneous_aggregate` for AArch64 and `vectorcall`):**
   - Treat 64-bit and 128-bit `BackendRepr::SimdVector` structs as homogeneous vector units (`RegKind::Vector`) even when defined via an single array field `#[repr(simd)] struct V([T; N])`, matching Clang's `__attribute__((vector_size(16)))` HVA classification.
4. **Fixing `ABI-07` (`extern "rust-cold"` `SIGSEGV` on 32-bit `i686` in `compiler/rustc_target/src/spec/abi_map.rs:104-105` and `compiler/rustc_codegen_llvm/src/abi.rs:723`):**
   - Restrict `CanonAbi::RustCold => llvm::PreserveMost` to `(Arch::X86_64 | Arch::AArch64)` when `os != OsKind::Windows`, falling back to `CanonAbi::Rust` (`llvm::CCallConv`) on 32-bit `Arch::X86` (`i686`), matching `CanonAbi::RustPreserveNone` on lines `724-727`.

## Boundaries

- **Proprietary MSVC `cl.exe` and Apple Xcode SDK Linker (`not examined` live):** Windows (`*-pc-windows-msvc`) and macOS (`aarch64-apple-darwin`) targets were evaluated via `rustc 1.99.1 --emit=llvm-ir,asm` vs. `clang-19 --target=<triple> -S -emit-llvm`.
- **Unstable Scalable Vectors (`SVE` / `RVV`) (`unsupported` in `rustc_target::callconv`):** Both `x86_win64.rs:28` and `x86_win32.rs:113` panic with `"scalable vectors are unsupported"` unless target-specific scalable vector rules apply.

## Evidence

- **Primary Upstream Sources (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_target/src/callconv/x86_win64.rs:12-66` (`f128` vs `i128` return rule and ZST indirect pointer rule).
  - `compiler/rustc_target/src/callconv/x86_64.rs:175-270` (`int_regs` / `sse_regs` depletion and `u128` straddling behavior).
  - `compiler/rustc_target/src/callconv/aarch64.rs:19-201` (`AbiKind::{AAPCS, DarwinPCS, Win64}`, `is_homogeneous_aggregate`, and `unadjusted_abi_align`).
  - `compiler/rustc_target/src/callconv/x86.rs:138-246` and `x86_win32.rs:1-136` (`fill_inregs`, `extern "Rust"` `<4 x i8>` SSE2 float return workaround, and `byval` alignment).
  - `compiler/rustc_target/src/spec/abi_map.rs:96-120` and `compiler/rustc_codegen_llvm/src/abi.rs:720-762` (`CanonAbi::RustCold` `preserve_mostcc` lowering bug on 32-bit `i686`).
  - `library/core/src/ffi/va_list.rs:41-229` (`VaListInner` representations across AArch64 Linux, SysV x86_64, and pointer-based targets).
- **Preserved Support Artifacts:**
  - [`support/run_8target_abi_campaign.py`](support/run_8target_abi_campaign.py): Procedural 256-signature-per-target generator, cross-compiler IR comparator, and live execution runner.
  - [`support/tier1_abi_campaign_results.json`](support/tier1_abi_campaign_results.json): Complete per-target comparison statistics, live execution results, and catalog of `ABI-01`..`ABI-08`.

## Revalidation

```bash
python3 reports/tier1-exhaustive-procedural-abi-differential-campaign-and-fixes/support/run_8target_abi_campaign.py
```

Verify that all `2,048` procedural target-signature pairs compile cleanly across the 8 Tier 1 targets and inspect `support/tier1_abi_campaign_results.json` for `per_target_summary` and `live_execution_verification`.
