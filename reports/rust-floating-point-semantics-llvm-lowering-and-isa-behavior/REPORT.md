# End-to-End Rust Floating-Point Semantics: RFC 3514, LLVM 23.1.1 Lowering, Tier 1 ISA NaN Behavior, and Platform Libcalls

## Summary

Floating-point semantics in **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1` at
`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) are governed by **RFC 3514**
(`rust-lang/rfcs` `7677feddd580f356f780cb7123aeda6a3708275a`,
`text/3514-float-semantics.md`), which combines strict IEEE 754-2008 arithmetic
for non-NaN values with structured non-determinism for NaN sign/payload bits and
controlled relaxation for algebraic/fast-math intrinsics and transcendental
functions:

1. **Four-choice NaN lattice and bitwise exemptions (RFC 3514):**
   For `+`, `-` (binary), `*`, `/`, `%`, `mul_add`, `sqrt`, and float `as`
   casts, any NaN output has a non-deterministic sign bit (`0` or `1`) and a
   quiet bit + payload chosen non-deterministically from four sets:
   (a) **Preferred NaN** (`quiet = 1`, payload `= 0`: `0x7fc0_0000` /
   `0xffc0_0000` for `f32`), (b) **Quieting NaN propagation** (`quiet = 1`,
   payload copied from any NaN input), (c) **Unchanged NaN propagation**
   (`quiet` and payload copied unchanged from any NaN input—so an operation can
   return a signaling NaN *if and only if* at least one input is a signaling
   NaN), and (d) **Target-specific extra payloads** (empty on x86, x86_64,
   AArch64, and RISC-V). Unary `-`, `abs`, and `copysign` are strictly
   **bitwise** operations (`compiler/rustc_const_eval/src/interpret/operator.rs:L471`)
   that never quiet signaling NaNs or alter payload bits.
2. **Empirical NaN payload and ABI divergences across CTFE, Miri, Cranelift, and
   Tier 1 ISAs (`support/s8_float_probe.rs`):**
   - **`0.0f32 / 0.0f32` sign divergence:** Rust 1.99.1 CTFE
     (`Machine::generate_nan` in `compiler/rustc_const_eval/src/interpret/machine.rs:L294`)
     and AArch64 hardware (`fdiv`) return positive preferred QNaN `0x7fc0_0000`,
     whereas `x86_64` and `i686` hardware (`divss` / x87 `fdiv`) and Cranelift
     on `x86_64` return negative QNaN `0xffc0_0000`, and Miri returns
     `0x7fc0_0000` under seed `0` and `0xffc0_0000` under `-Zmiri-seed=1`.
   - **Optimization-dependent two-NaN propagation (`qnan1 + qnan2` vs.
     `qnan2 + qnan1`):** For `qnan1 = 0x7fc0_0001` and `qnan2 = 0x7fc0_0002`,
     `-O0` on `x86_64` and `aarch64` returns `(0x7fc0_0001, 0x7fc0_0002)`
     (propagating the first operand), whereas at `-O3` LLVM CSE/GVN merges
     commutative `fadd(qnan2, qnan1)` with `fadd(qnan1, qnan2)`, yielding
     `(0x7fc0_0002, 0x7fc0_0002)` on `x86_64` and `(0x7fc0_0001, 0x7fc0_0001)`
     on `aarch64`.
   - **32-bit `i686` `extern "Rust"` (SSE2) vs. `extern "C"` (x87 `st(0)`)
     signaling NaN hazard:** Because `i686-unknown-linux-gnu` and
     `i686-pc-windows-msvc` set `base.rustc_abi = Some(RustcAbi::X86Sse2)`
     (`compiler/rustc_target/src/callconv/x86.rs:L210-L246`), `extern "Rust"`
     returns `f32`/`f64` in SSE2 `xmm0` (`Reg::opaque_vector`)—or integer `eax`
     when `-C target-feature=-sse2` is passed—preserving a signaling NaN
     (`0x7f80_0001`) bit-for-bit. By contrast, `extern "C"` on `i686` returns
     floats in x87 `st(0)` (`flds` / `fstps`), which hardware-quiets
     `0x7f80_0001` to **`0x7fc0_0001`** at `-O0`, whereas at `-O3` LLVM promotes
     non-exported `extern "C"` functions to `internal fastcc` (`%xmm0`),
     changing the returned bit pattern back to **`0x7f80_0001`**!
3. **LLVM 23.1.1 intrinsic lowering, `minimum`/`maximum` workarounds, and
   8-target libcall matrix (`support/s8_libcalls.rs`):**
   - `fadd_fast`..`frem_fast` call `LLVMRustSetFastMath` (`I->setFast(true)`,
     enabling all 7 LLVM fast-math flags including `nnan` and `ninf`, which
     yields `poison` on NaN/Inf). By contrast, `fadd_algebraic`..`frem_algebraic`
     call `LLVMRustSetAlgebraicMath`
     (`compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp:L623-L630`), enabling
     only `reassoc`, `contract`, `arcp`, and `nsz` so NaN/Inf inputs never
     produce `poison`.
   - In `rustc 1.99.1` (`compiler/rustc_codegen_llvm/src/intrinsic.rs:L119-L219`),
     `minimum_number_nsz_f*` / `maximum_number_nsz_f*` (`f32::min` / `f32::max`)
     lower to `llvm.minimumnum` / `llvm.maximumnum` with the `nsz` flag (enabled
     for LLVM $\ge 22.0.0$), whereas `minimumf64`, `maximumf64`, `minimumf128`,
     and `maximumf128` are **commented out** in `call_simple_intrinsic` (`L121-L131`)
     due to upstream LLVM miscompilations (`llvm/llvm-project#139380`, `#139381`,
     `#140445`) and instead use software fallback expansion in `core`.

## Applicability

These findings apply to **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`), **LLVM 23.1.1**
(`rust-lang/llvm-project` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), **RFC
3514** (`rust-lang/rfcs` `7677feddd580f356f780cb7123aeda6a3708275a`), **Miri
0.1.0** (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`), and
**`rustc_codegen_cranelift`** (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`)
across all eight Tier 1 targets (`x86_64-unknown-linux-gnu`,
`aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-apple-darwin`,
`x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`,
and `i686-pc-windows-msvc`).

## Findings

### 1. Rust Floating-Point Rules (RFC 3514, `rustc_apfloat`, and CTFE/Miri)

Basis: normative (`text/3514-float-semantics.md:L47-L155`) + source
(`compiler/rustc_apfloat/src/ieee.rs`,
`compiler/rustc_const_eval/src/interpret/{operator.rs,intrinsics.rs,machine.rs,cast.rs}`,
`src/tools/miri/src/math.rs`)

1. **Bitwise vs. arithmetic float operations:**
   - **Bitwise operations (`-x`, `abs`, `copysign`):** Operate purely on the
     sign bit without inspecting or modifying the exponent, quiet bit, or
     mantissa (`operator.rs:L471`: `// No NaN adjustment here, '-' is a bitwise
     operation!`). Passing a signaling NaN `0x7f80_0001` to `-x` deterministically
     yields `0xff80_0001` in CTFE, Miri, Cranelift, and all Tier 1 targets.
   - **Arithmetic and cast operations (`+`, `-`, `*`, `/`, `%`, `mul_add`,
     `sqrt`, `as`):** Round according to IEEE 754-2008 `roundTiesToEven` (except
     float-to-integer `as` casts, which truncate toward zero and saturate to
     `INT::MIN` / `INT::MAX`, or `0` on NaN; `cast.rs:L415-L455`). Whenever the
     result is NaN, `InterpCx::adjust_nan` (`eval_context.rs:L641`) calls
     `M::generate_nan(self, inputs)`:
     - In **CTFE (`CompileTimeMachine`)**, `generate_nan` (`machine.rs:L294`)
       always returns `F2::NAN` (the positive preferred quiet NaN:
       `0x7fc0_0000` for `f32`, `0x7ff8_0000_0000_0000` for `f64`).
     - In **Miri (`MiriMachine`)**, `generate_nan` (`src/tools/miri/src/math.rs`)
       randomly picks among the RFC 3514 allowed set (random sign, preferred
       NaN, quieted input NaN payload, or unchanged signaling input NaN
       payload).
2. **`mul_add` (`fmaf*`) vs. `fmuladdf*` and transcendental ULP non-determinism:**
   - `f32::mul_add` / `f64::mul_add` calls `sym::fmaf32` / `sym::fmaf64`, which
     computes `(a * b) + c` with a **single** rounding step (`llvm.fma`).
   - `sym::fmuladdf32` / `sym::fmuladdf64` (`llvm.fmuladd`) non-deterministically
     chooses between fused `fma(a, b, c)` and unfused `(a * b) + c`
     (`intrinsics.rs:L34-L35`, `M::float_fuse_mul_add`).
   - For transcendental intrinsics (`sin`, `cos`, `exp`, `exp2`, `log`, `log2`,
     `log10`, `pow`), Miri applies a random $\pm 4\text{ ULP}$ perturbation
     (`apply_random_float_error_ulp(this, res, 4)` in
     `src/tools/miri/src/math.rs:L573`) and clamps the output to the C23 Annex
     F.10 domain range (`[-1, 1]` for `sin`/`cos`, `[0, +\infty)` for
     `exp`/`exp2`; `math.rs:L187-L230`), while returning exact C23 Annex F.10
     fixed values at special arguments (`math.rs:L232-L535`).

---

### 2. LLVM 23.1.1 Lowering: Fast-Math Flags, `min`/`max` vs. `minimum`/`maximum`, and Float-to-Int Casts

Basis: source (`compiler/rustc_codegen_llvm/src/{intrinsic.rs,builder.rs}`,
`compiler/rustc_codegen_ssa/src/mir/{intrinsic.rs,rvalue.rs}`,
`compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp:L606-L652`)

| Rust Construct / Intrinsic | LLVM 23.1.1 Lowering in `rustc 1.99.1` | Fast-Math Flags / Poison Semantics |
| :--- | :--- | :--- |
| `+`, `-`, `*`, `/`, `%` (`BinOp`) | `fadd`, `fsub`, `fmul`, `fdiv`, `frem` | None (strict IEEE 754 + LLVM NaN rules). |
| `fadd_fast`, `fsub_fast`, `fmul_fast`, `fdiv_fast`, `frem_fast` (`unsafe`) | `fadd fast`, `fsub fast`, `fmul fast`, `fdiv fast`, `frem fast` (`RustWrapper.cpp:L609`) | Sets all 7 flags (`nnan ninf nsz arcp contract afn reassoc`). **NaN or $\pm\infty$ inputs/outputs produce `poison`!** |
| `fadd_algebraic`, `fsub_algebraic`, `fmul_algebraic`, `fdiv_algebraic`, `frem_algebraic` (safe) | `fadd reassoc contract arcp nsz`, etc. (`RustWrapper.cpp:L623`) | Sets **only** `reassoc`, `contract`, `arcp`, `nsz`. Does **not** set `nnan`, `ninf`, or `afn`; NaN/Inf inputs never produce `poison`. |
| `f32::min` / `f64::min` (`minimum_number_nsz_f*`) | `call nsz float @llvm.minimumnum.f32(float, float)` (`intrinsic.rs:L194-L219`) | IEEE 754-2019 `minimumNumber` with `nsz`: returns the non-NaN argument if one argument is NaN (quiet **or** signaling!), and non-deterministically orders `-0.0` vs. `+0.0`. |
| `f32::max` / `f64::max` (`maximum_number_nsz_f*`) | `call nsz float @llvm.maximumnum.f32(float, float)` (`intrinsic.rs:L194-L219`) | IEEE 754-2019 `maximumNumber` with `nsz`. |
| `f32::minimum` / `f32::maximum` (`minimumf16`, `minimumf32`, `maximumf16`, `maximumf32`) | `call float @llvm.minimum.f32` / `@llvm.maximum.f32` (`intrinsic.rs:L119-L127`) | IEEE 754-2019 `minimum` / `maximum`: propagates NaN if **either** input is NaN, and orders `-0.0 < +0.0`. |
| `f64::minimum` / `f64::maximum` (`minimumf64`, `minimumf128`) | **Commented out** in `intrinsic.rs:L121-L131` (`FIXME: llvm-project#{139380,139381,140445}`) | Falls back to explicit comparison + NaN check + signed-zero check in `core::num::f64`. |
| `x as i32` / `x as u32` (`CastKind::FloatToInt`) | `bx.cast_float_to_int(signed, x, ty)` (`builder.rs:L1030-L1095`) | Emits `@llvm.fptosi.sat` / `@llvm.fptoui.sat` (saturates to `[MIN, MAX]` and maps `NaN -> 0`; never UB). |
| `float_to_int_unchecked(x)` (`unsafe`) | `bx.fptosi(x, ty)` / `bx.fptoui(x, ty)` (`mir/intrinsic.rs:L352-L375`) | Raw LLVM `fptosi` / `fptoui`: out-of-range values (after truncation toward zero) or `NaN`/`±Inf` produce **`poison`**! |

---

### 3. Empirical Multi-ISA and Multi-Backend NaN & ABI Measurements

Basis: execution (`support/s8_float_probe.rs`, `support/s8_float_results.json`)

Table 2 records the bit patterns (`u32` hex) observed by running
`support/s8_float_probe.rs` across `rustc 1.99.1` CTFE, `x86_64`, `aarch64`
(`qemu-aarch64`), `i686` (`qemu-i386`, both baseline SSE2 and
`-C target-feature=-sse2`), Cranelift (`-Zcodegen-backend=cranelift`), and Miri
(`seed=0` and `seed=1`). Inputs are `qnan1 = 0x7fc0_0001`,
`qnan2 = 0x7fc0_0002`, and `snan = 0x7f80_0001`.

| Execution Environment | `0.0 / 0.0` | `qnan1 + qnan2` | `qnan2 + qnan1` | `snan + 1.0` | `-snan` | `qnan1.min(1.0)` | `snan.min(1.0)` | `extern "Rust" fn(snan)` | `extern "C" fn(snan)` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`rustc 1.99.1` CTFE (`const`)** | `0x7fc00000` | `0x7fc00000` | `0x7fc00000` | `0x7fc00000` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | `0x7f800001` |
| **`x86_64-unknown-linux-gnu` (`-O0`)** | `0xffc00000` | `0x7fc00001` | `0x7fc00002` | `0x7fc00001` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | `0x7f800001` |
| **`x86_64-unknown-linux-gnu` (`-O3`)** | `0xffc00000` | `0x7fc00002` | `0x7fc00002` | `0x7fc00001` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | `0x7f800001` |
| **`aarch64-unknown-linux-gnu` (`-O0`)** | `0x7fc00000` | `0x7fc00001` | `0x7fc00002` | `0x7fc00001` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | `0x7f800001` |
| **`aarch64-unknown-linux-gnu` (`-O3`)** | `0x7fc00000` | `0x7fc00001` | `0x7fc00001` | `0x7fc00001` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | `0x7f800001` |
| **`i686-unknown-linux-gnu` (`-O0`, SSE2)** | `0xffc00000` | `0x7fc00002` | `0x7fc00002` | `0x7fc00001` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | **`0x7fc00001`** |
| **`i686-unknown-linux-gnu` (`-O3`, SSE2)** | `0xffc00000` | `0x7fc00002` | `0x7fc00002` | `0x7fc00001` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | **`0x7f800001`** |
| **`i686` (`-C target-feature=-sse2`, `-O0`/`-O3`)** | `0xffc00000` | `0x7fc00002` | `0x7fc00002` | `0x7fc00001` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | **`0x7fc00001`** |
| **Cranelift `x86_64` (`-O0` & `-O3`)** | `0xffc00000` | `0x7fc00001` | `0x7fc00002` | `0x7fc00001` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | `0x7f800001` |
| **Miri (`seed = 0`)** | `0x7fc00000` | `0x7fc00002` | `0xffc00000` | `0x7fc00001` | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | `0x7f800001` |
| **Miri (`-Zmiri-seed=1`)** | `0xffc00000` | `0x7fc00002` | `0xffc00000` | **`0x7f800001`** | `0xff800001` | `0x3f800000` | `0x3f800000` | `0x7f800001` | `0x7f800001` |

**Why `extern "Rust"` vs. `extern "C"` differs on `i686` (`x86.rs:L210-L246`):**
In `compiler/rustc_target/src/callconv/x86.rs:L215-L244`, `compute_rust_abi_info`
explicitly avoids returning floats in x87 `st(0)` on `extern "Rust"` functions:
- When `cx.target_spec().rustc_abi == Some(RustcAbi::X86Sse2)` (the default on
  `i686-unknown-linux-gnu` and `i686-pc-windows-msvc`), single-scalar floats
  $\le 128$ bits are cast to `Reg::opaque_vector(size)` and returned in `%xmm0`
  (`movd 0x10(%esp), %xmm0`), preserving signaling NaNs bit-for-bit.
- When `-C target-feature=-sse2` disables SSE2, `compute_rust_abi_info` falls
  back to `L236-L242`: floats $\le 32$ bits (`f16`, `f32`) are returned in
  integer register `%eax`, and `f64`/`f128` are returned indirectly via sret
  pointer—still avoiding x87 `st(0)`!
- By contrast, `extern "C"` on `i686` is bound by the system C ABI to return
  `f32`/`f64` in x87 `st(0)` (`flds` / `fstps`), which hardware-quiets
  `0x7f80_0001` to `0x7fc0_0001` at `-O0` (or whenever the symbol is exported
  with `#[no_mangle]`), whereas at `-O3` on an internal `extern "C"` function
  LLVM promotes the calling convention to `fastcc` (`%xmm0`), eliminating the
  `flds` instruction and returning `0x7f80_0001`.

---

### 4. Platform Libcall Lowering Across All Eight Tier 1 Targets

Basis: execution (`support/s8_libcalls.rs`, `llvm-nm -u` across all 8 Tier 1
targets)

Table 3 shows the exact external symbol calls emitted by `rustc 1.99.1` (`-O3`)
for `f16`, `f32`, `f64`, and `f128` operations across all eight Tier 1 targets.

| Operation | `x86_64` / `i686` Linux & MinGW | `aarch64` Linux & macOS | `x86_64` MSVC | `aarch64` MSVC | `i686` MSVC |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `f16` $\leftrightarrow$ `f32` / `f64` | `__extendhfsf2`, `__truncsfhf2`, `__truncdfhf2` (`compiler_builtins`) | **Hardware `fcvt`** (0 libcalls) | `__extendhfsf2`, `__truncsfhf2`, `__truncdfhf2` | **Hardware `fcvt`** (0 libcalls) | `___extendhfsf2`, `___truncsfhf2`, `___truncdfhf2` |
| `f32::mul_add` / `f64::mul_add` (`fma`) | `fmaf`, `fma` (`libm`, unless `+fma` enabled) | **Hardware `fmadd`** (0 libcalls) | `fmaf`, `fma` | **Hardware `fmadd`** (0 libcalls) | `_fmaf`, `_fma` |
| `f32 % f32` / `f64 % f64` (`frem`) | `fmodf`, `fmod` (`libm`) | `fmodf`, `fmod` | `fmodf`, `fmod` | `fmodf`, `fmod` | `_fmod` (`f32` promoted to `f64`!) |
| `powif32` / `powif64` (`powi`) | `__powisf2`, `__powidf2` (`compiler_builtins`) | `__powisf2`, `__powidf2` | `powf`, `pow` (CRT via `sitofp`) | `powf`, `pow` (CRT via `sitofp`) | `_pow` (CRT via `sitofp`) |
| `f32` / `f64` $\leftrightarrow$ `u128` | `__fixunssfti`, `__fixunsdfti`, `__floatuntisf`, `__floatuntidf` | `__fixunssfti`, `__fixunsdfti`, `__floatuntisf`, `__floatuntidf` | `__fixunssfti`, `__fixunsdfti`, `__floatuntisf`, `__floatuntidf` | `__fixunssfti`, `__fixunsdfti`, `__floatuntisf`, `__floatuntidf` | `___fixunssfti`, `___fixunsdfti`, `___floatuntisf`, `___floatuntidf` |
| `f128` `+`, `*`, `/` | `__addtf3`, `__multf3`, `__divtf3` | `__addtf3`, `__multf3`, `__divtf3` | `__addtf3`, `__multf3`, `__divtf3` | `__addtf3`, `__multf3`, `__divtf3` | `___addtf3`, `___multf3`, `___divtf3` |
| `f128` `%` and `fmaf128` | `fmodf128`, `fmaf128` | `fmodl`, `fmal` | `fmodl`, `fmal` | `fmodl`, `fmal` | `_fmodl`, `_fmal` |

## Boundaries

- **Non-default floating-point control environments (`known not to apply` / UB):**
  Modifying hardware rounding modes or enabling flush-to-zero (FTZ/DAZ),
  default-NaN mode (`FPCR.DN` on AArch64), or trapping exceptions without
  restoring them before leaving inline assembly is Undefined Behavior under RFC
  3514 (`text/3514-float-semantics.md:L136-L155`).
- **Unstable `f128` `frem` / `fmaf128` on Darwin and Windows (`known upstream
  defect`):** On `aarch64-apple-darwin` and `*-pc-windows-msvc`, LLVM lowers
  `f128` `frem` and `llvm.fma.f128` to `fmodl` and `fmal`, which take 64-bit
  `long double` on those platforms rather than 128-bit IEEE binary128.

## Evidence

- **Primary upstream sources:**
  - `rust-lang/rfcs` @ `7677feddd580f356f780cb7123aeda6a3708275a`:
    `text/3514-float-semantics.md:L1-L323`.
  - `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`:
    - `compiler/rustc_apfloat/src/ieee.rs`
    - `compiler/rustc_const_eval/src/interpret/{operator.rs:L69-L95, eval_context.rs:L641, machine.rs:L294-L322, intrinsics.rs:L31-L60, L570-L610}`
    - `src/tools/miri/src/math.rs:L70-L583`
    - `compiler/rustc_codegen_llvm/src/{intrinsic.rs:L66-L219, builder.rs:L590-L605}`
    - `compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp:L606-L652`
    - `compiler/rustc_target/src/callconv/x86.rs:L210-L246`
- **Preserved support artifacts:**
  - [`support/s8_float_probe.rs`](support/s8_float_probe.rs)
  - [`support/s8_libcalls.rs`](support/s8_libcalls.rs)
  - [`support/s8_float_results.json`](support/s8_float_results.json)

## Revalidation

To rerun the multi-ISA floating-point NaN and ABI probe and libcall check:

```bash
SYSROOT=$(rustc +1.99.1-x86_64-unknown-linux-gnu --print sysroot)
LLD="$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld"
for target in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu i686-unknown-linux-gnu; do
  RUSTC_BOOTSTRAP=1 rustc +1.99.1-x86_64-unknown-linux-gnu -A warnings --edition 2021 \
    --target "$target" -C opt-level=0 -C panic=abort -C linker="$LLD" -C linker-flavor=ld.lld \
    reports/rust-floating-point-semantics-llvm-lowering-and-isa-behavior/support/s8_float_probe.rs \
    -o "/tmp/s8_${target}"
done
/tmp/s8_x86_64-unknown-linux-gnu
qemu-aarch64 /tmp/s8_aarch64-unknown-linux-gnu
qemu-i386 /tmp/s8_i686-unknown-linux-gnu
```
