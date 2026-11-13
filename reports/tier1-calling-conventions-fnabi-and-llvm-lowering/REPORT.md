# Tier 1 Calling Conventions: From Normative psABIs Through `rustc` `FnAbi` to LLVM Register and Stack Lowering

## Summary

A drop-in verified replacement for `rustc` must agree bit-for-bit with `rustc` `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) and LLVM `23.1.1`
(`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) on every function call boundary—not only for
FFI `extern "C"` signatures governed by platform psABIs, but also for `extern "Rust"`,
`extern "rust-call"`, `extern "rust-cold"`, `#[track_caller]`, and target-specific ABI strings
when crates compiled by the verified compiler link against standard-library `.rlib`s or
C/C++ objects.

Calling-convention lowering in `rustc` is a two-stage pipeline:
1. **Stage 1 (`rustc_ty_utils::abi::fn_abi_new_uncached` + `rustc_target::callconv`):**
   Computes `FnAbi<'tcx, Ty<'tcx>>`, assigning each argument and return value a `PassMode`:
   `Ignore` (zero-sized types), `Direct(ArgAttributes)`, `Pair(ArgAttributes, ArgAttributes)`,
   `Cast { pad_i32: bool, cast: CastTarget }`, or `Indirect { attrs, meta_attrs, on_stack }`.
   - For **`extern "Rust"`** (and `"rust-call"`, `"rust-cold"`), `fn_abi_adjust_for_abi` in
     `compiler/rustc_ty_utils/src/abi.rs:539-735` **bypasses target psABI classification** and
     applies a uniform target-independent rule before only consulting the target for indirect
     attributes:
     - `BackendRepr::Scalar(s)` $\to$ `PassMode::Direct` (with `RegKind::Float` scalar floats
       wrapped on 32-bit `i686` as `<4 x i8>` / `<8 x i8>` in SSE2 `xmm0` to avoid x87 `st(0)`
       signaling-NaN quietening!).
     - `BackendRepr::ScalarPair(a, b)` $\to$ `PassMode::Pair` (covering `(T, U)`, `&[T]`,
       `&str`, `&dyn Trait`, `Result<u64, u64>`, and `Option<NonNull<T>>`).
     - `BackendRepr::SimdVector` and all `BackendRepr::Memory` aggregates (even 8-byte
       `#[repr(C)] struct S(u32, u32)` if not `Scalar`/`ScalarPair`, or any aggregate $> 2$
       scalars / $> 16$ bytes) $\to$ `PassMode::Indirect { on_stack: false }` (passed by
       pointer to caller-owned temporary with `noalias readonly align N dereferenceable(S) dead_on_return`,
       **never** `byval`!).
   - For **non-Rust ABIs (`extern "C"`, `"system"`, `"sysv64"`, `"win64"`, `"stdcall"`, `"fastcall"`, `"thiscall"`, `"vectorcall"`, `"aapcs"`):**
     `fn_abi_adjust_for_abi` delegates to `rustc_target::callconv::<arch>::compute_abi_info`,
     which encodes the platform psABI into `PassMode::Direct`, `PassMode::Cast`, or
     `PassMode::Indirect { on_stack: true | false }`.
2. **Stage 2 (`rustc_codegen_llvm::abi` $\to$ LLVM SelectionDAG / GlobalISel):**
   Translates `FnAbi` into LLVM IR parameter types, attributes (`sret([N x i8])`, `byval([N x i8])`,
   `inreg`, `signext`, `zeroext`, `returned`), and LLVM `CallingConv::ID` (`ccc`, `x86_64_sysvcc`,
   `win64cc`, `x86_stdcallcc`, `x86_fastcallcc`, `x86_thiscallcc`, `x86_vectorcallcc`,
   `preserve_mostcc`), which LLVM's TableGen rules (`X86CallingConv.td`,
   `AArch64CallingConvention.td`) lower to physical registers and stack slots.

All 29 signature families compiled at `-O0` and `-O3` (`--emit=llvm-ir,asm`) across all 8
Tier 1 targets (`214` target-signature pairs) are preserved in
`support/calling_conv_corpus.rs`, `support/calling_conv_rules_and_goldens.json`, and
`support/goldens/{O0,O3}/*.s`.

## Applicability

- **Primary subjects:** `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
  and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
- **Targets covered:** All 8 Tier 1 targets:
  - `x86_64-unknown-linux-gnu` (System V AMD64 psABI 1.0)
  - `x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu` (Microsoft x64 calling convention +
    MinGW GCC divergences)
  - `i686-unknown-linux-gnu` (System V i386 psABI 1.1) and `i686-pc-windows-msvc` (Microsoft
    32-bit x86 `cdecl`, `stdcall`, `fastcall`, `thiscall`, `vectorcall`)
  - `aarch64-unknown-linux-gnu` (Arm AAPCS64 2025Q1), `aarch64-apple-darwin` (Apple ARM64 ABI),
    and `aarch64-pc-windows-msvc` (Microsoft ARM64 ABI)
- **Relationship to prior reports:** Extends
  `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`,
  `configured-rust-capture-fnabi-placement-and-formality-specr-boundaries`,
  `rustc-codegen-backend-abi-intrinsics-and-rv64gc-cross-compilation`, and
  `zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics` with the complete
  8-target `FnAbi` $\to$ LLVM IR $\to$ physical register/stack assignment rules and golden
  assembly corpus.

## Findings

### 1. Normative psABI Specifications and Register Partitioning Across the 8 Tier 1 Targets

Basis: normative + source (`llvm/lib/Target/X86/X86CallingConv.td`, `llvm/lib/Target/AArch64/AArch64CallingConvention.td`)

| Target / Convention | Normative Specification | Integer / Pointer Arg Regs | FP / Vector Arg Regs | Return Regs (Int / FP-Vec) | Indirect Result (`sret`) Reg | Callee-Saved Regs | Stack Alignment & Shadow Space |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` (`"C"`, `"sysv64"`) | System V AMD64 psABI v1.0 | `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9` (6) | `xmm0`..`xmm7` (`ymm0`..`7` / `zmm0`..`7`) (8) | `rax`, `rdx` / `xmm0`, `xmm1` | `rdi` (consumes 1st GPR; returned in `rax`) | `rbx`, `rbp`, `r12`..`r15` | 16B aligned before `call`; 128B red zone; 0B shadow |
| `x86_64-pc-windows-{msvc,gnu}` (`"C"`, `"win64"`) | Microsoft x64 Software Conventions | `rcx`, `rdx`, `r8`, `r9` (4 positional slots shared with FP) | `xmm0`..`xmm3` (4 positional slots shared with Int) | `rax` / `xmm0` (`<16 x i8>` in `xmm0` for `i128` return!) | `rcx` (consumes slot 0; returned in `rax`) | `rbx`, `rbp`, `rdi`, `rsi`, `r12`..`r15`, `xmm6`..`xmm15` | 16B aligned; no red zone; **32B shadow space** (`[rsp+8..rsp+40]`) allocated by caller |
| `i686-unknown-linux-gnu` (`"C"` / `cdecl`) | System V i386 psABI v1.1 | Stack (`[esp+4]`, ...) (`inreg` uses `eax`, `edx`, `ecx`) | Stack (`xmm0`..`xmm2` for `SimdVector` in `"C"`) | `eax`, `edx` / `st(0)` (`extern "C"` scalar FP) or `xmm0` (`extern "Rust"` `<4/8 x i8>`) | `[esp+4]` (`ret $4` pops hidden `sret` pointer!) | `ebx`, `esi`, `edi`, `ebp` | 16B aligned before `call` |
| `i686-pc-windows-msvc` (`"C"` / `cdecl`) | Microsoft x86 `cdecl` | Stack (`[esp+4]`, ...) | Stack (`xmm0`..`xmm2` for `SimdVector` in `"C"`) | `eax`, `edx` (includes ≤8B structs!) / `st(0)` | `[esp+4]` (caller cleans stack; plain `ret`) | `ebx`, `esi`, `edi`, `ebp` | 4B ABI minimum (16B frame align for SSE) |
| `aarch64-unknown-linux-gnu` (`"C"`, `"aapcs"`) | Arm AAPCS64 (2025Q1) | `x0`..`x7` (8) | `v0`..`v7` (`s0`..`s7` / `d0`..`d7` / `q0`..`q7`) (8) | `x0`, `x1` / `v0`..`v3` (up to 4-elem HFA/HVA) | **`x8`** (`XR`, does **not** consume `x0`..`x7`!) | `x19`..`x28`, `x29`(FP), `x30`(LR), `d8`..`d15` (low 64b) | 16B aligned at all times (SP mod 16 = 0); no red zone |
| `aarch64-apple-darwin` (`"C"`) | Apple ARM64 Function Calling Conventions | `x0`..`x7` (8) | `v0`..`v7` (8) | `x0`, `x1` / `v0`..`v3` | **`x8`** | `x19`..`x28`, `x29`, `x30`, `d8`..`d15` (`x18` reserved by OS) | 16B aligned; 128B red zone; stack args tightly packed (`signext`/`zeroext` `<32b`!) |
| `aarch64-pc-windows-msvc` (`"C"`) | Microsoft ARM64 ABI | `x0`..`x7` (8) | `v0`..`v7` (8) | `x0`, `x1` / `v0`..`v3` | **`x8`** (for non-C++ / C POD; `x0`/`x1` for C++ non-trivial) | `x19`..`x28`, `x29`, `x30`, `d8`..`d15` (`x18` = TEB pointer) | 16B aligned; 16B red zone; variadic calls pass all args in GPRs/stack (no FP regs) |

### 2. `rustc` Stage 1 (`FnAbi`) Rules Across All Accepted ABI Strings

Basis: source (`compiler/rustc_ty_utils/src/abi.rs:440-735`, `compiler/rustc_target/src/callconv/*.rs`) + execution (`support/calling_conv_rules_and_goldens.json`)

#### 2.1 `extern "Rust"`, `extern "rust-call"`, `extern "rust-cold"`, and `#[track_caller]`

1. **`extern "Rust"` (`compiler/rustc_ty_utils/src/abi.rs:621-720`):**
   - **Zero-sized types (`layout.is_zst()`):** Always `PassMode::Ignore` (omitted from LLVM IR
     signature unless raw pointer / reference).
   - **`#[repr(transparent)]` wrappers:** Because layout computation preserves the single
     non-ZST field's `BackendRepr` (`Scalar`, `ScalarPair`, or `SimdVector`), transparent
     wrappers (`NonZero<T>`, `Wrapping<T>`, `MaybeUninit<Scalar>`, user `#[repr(transparent)]`)
     have identical `PassMode` to their inner type in both `extern "Rust"` and `extern "C"`
     (with one exception on `x86_64` SysV C ABI if a transparent wrapper carries an explicit
     `#[repr(align(16))]` that pushes a 16-byte struct's alignment above 8 bytes).
   - **Scalars (`BackendRepr::Scalar`):** `PassMode::Direct(attrs)`. Narrow integers (`i8`,
     `u8`, `i16`, `u16`, `bool`) get `signext`/`zeroext` attributes according to the target's
     C ABI extension rule (`abi::adjust_for_cabi`), and `noundef` / `range(...)` / `nonnull`
     attributes from scalar validity ranges.
   - **32-bit x86 (`i686`) `extern "Rust"` float return workaround (`callconv/x86.rs:108-127`):**
     On `i686-unknown-linux-gnu` and `i686-pc-windows-msvc` (when `+sse2` is enabled),
     `extern "Rust"` casts `f32` return values to `CastTarget` `<4 x i8>` (`define noundef <4 x i8> @cc_rust_f32(float noundef %x, float noundef %y)`)
     and `f64` return values to `<8 x i8>`, returned in `%xmm0` via `movd %xmm0, %eax` / SSE
     registers rather than x87 `fld` + `st(0)`! This prevents x87 `fld` from converting
     signaling NaNs (`sNaN`) into quiet NaNs (`qNaN`) and avoids 80-bit excess precision on return.
   - **Scalar pairs (`BackendRepr::ScalarPair`):** `PassMode::Pair(a0, a1)`. Lowered to two
     separate LLVM arguments (`%p.0, %p.1`) on call and a two-element LLVM struct return
     `{ T0, T1 }` when ≤ 2 registers (`rax, rdx` on `x86_64` SysV and Win64; `x0, x1` on
     `aarch64`; indirect `sret([16 x i8])` on 32-bit `i686` when the pair is two 64-bit
     integers `(u64, u64)` = 16 bytes, or `{ i32, i32 }` in `eax, edx` when `(u32, u32)` /
     `&[T]` = 8 bytes!).
   - **SIMD vectors (`BackendRepr::SimdVector`) in `extern "Rust"` (`abi.rs:647-656`):**
     In `extern "Rust"`, SIMD vector arguments (`__m128`, `f32x4`, `float32x4_t`) are **always**
     passed and returned via `PassMode::Indirect { on_stack: false }` (`sret([16 x i8])` and
     `ptr noalias nofree noundef readonly align 16 captures(none) dead_on_return dereferenceable(16) %v`)!
     `rustc` deliberately avoids passing SIMD vectors in vector registers in `extern "Rust"` so
     that callers without `+avx` / `+avx512f` can safely call `#[target_feature(enable = "avx2")]`
     Rust functions without an ABI mismatch.
   - **Memory aggregates (`BackendRepr::Memory`, ≥3 scalars or non-ScalarPair structs):**
     Always `PassMode::Indirect { on_stack: false }` (passed by pointer in a GPR / stack slot
     without `byval`, and returned via `sret`).
2. **`#[track_caller]` (`abi.rs:587-604`):**
   - Appends an implicit final argument of type `&'static core::panic::Location<'static>` with
     `PassMode::Direct` (`ptr noalias nofree noundef readonly align 8 dereferenceable(24)` on
     64-bit targets; `align 4 dereferenceable(16)` on 32-bit `i686`).
   - Only allowed on `"Rust"`, `"rust-call"`, and `"rust-cold"` ABIs.
3. **`extern "rust-call"` (`abi.rs:555-585`):**
   - Takes `(receiver, tuple_of_args)` and flattens the tuple fields into individual arguments
     in `FnAbi::args`, then applies the standard `extern "Rust"` `PassMode` rules to each
     flattened argument. For example, `extern "rust-call" fn(Env(u64), (u32, u64)) -> u64`
     lowers to `define noundef i64 @cc_rust_call(i64 noundef %0, i32 noundef %1, i64 noundef %2)`
     on 64-bit targets (`rdi, esi, rdx` on SysV; `rcx, edx, r8` on Win64; `x0, w1, x2` on
     AArch64).
4. **`extern "rust-cold"` (`rustc_codegen_llvm/src/abi.rs:604-621`):**
   - Uses identical `FnAbi` `PassMode`s to `extern "Rust"`, but sets LLVM calling convention
     `preserve_mostcc` (`llvm::CallingConv::PreserveMost`) on targets where LLVM supports
     `preserve_mostcc` without frame-pointer/unwind bugs:
     - Emits `preserve_mostcc` on `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, and
       `aarch64-apple-darwin` (where the callee saves almost all GPRs—`r15..r11, r9..rdi` on
       x86-64; `x15..x9, x7..x1` on AArch64—keeping cold panic/error call sites in the caller
       free of register spills).
     - Falls back to default `ccc` on Windows (`x86_64-pc-windows-*`, `aarch64-pc-windows-msvc`)
       and 32-bit `i686` (`abi.rs:610-619`).
5. **`-unwind` ABI variants (`"C-unwind"`, `"system-unwind"`, `"stdcall-unwind"`, etc.):**
   - Identical parameter and return `PassMode`s and LLVM `CallingConv` to their non-`-unwind`
     counterparts. The only difference is in `rustc_codegen_ssa::mir::block`: a call to a
     non-`-unwind` foreign ABI (`extern "C"`) emits the LLVM `nounwind` attribute on the call
     site or wraps a body that can unwind in a landingpad/cleanuppad abort guard
     (`core::panicking::panic_cannot_unwind`), whereas `"C-unwind"` permits unwinding across the
     ABI boundary via DWARF `.eh_frame` or Windows SEH `.pdata`/`.xdata`.

#### 2.2 Platform C and Specialty ABIs (`rustc_target::callconv`)

| Target & ABI | Aggregate Classification Rule (`classify_ret` / `classify_arg`) | `u128` / `i128` Rule | `f16` / `f128` Rule | Vector (`SimdVector`) Rule in `"C"` / `"vectorcall"` |
| :--- | :--- | :--- | :--- | :--- |
| **`x86_64-unknown-linux-gnu`** (`"C"`, `"sysv64"`) (`callconv/x86_64.rs:29-270`) | Eightbyte classification (`Int`, `Sse`, `SseUp`, `Memory`): >16B or unaligned field $\to$ `Indirect { on_stack: true }` (`byval([N x i8])` for args, `sret` for ret). ≤16B classified into 1 or 2 eightbytes (`i64`, `double`, `{ i64, i64 }`, `{ i64, double }`, `<4 x float>`). | `Direct` `i128`: passed in two GPRs (need **not** be even/odd aligned: `cc_u128(i32, u128)` uses `edi` then `rsi, rdx`!), returned in `rax, rdx`. | `f16` $\to$ `half` in `xmm0`; `f128` $\to$ `fp128` in `xmm0`. | 128b in `xmm0..7` (requires `+sse`); 256b in `ymm0..7` (requires `+avx`); 512b in `zmm0..7` (requires `+avx512f`). Without feature, `rustc` emits ABI error/warning! |
| **`x86_64-pc-windows-msvc`** & **`-gnu`** (`"C"`, `"win64"`) (`callconv/x86_win64.rs:1-70`) | Only sizes **1, 2, 4, or 8 bytes** (`i8`, `i16`, `i32`, `i64`) are `Cast` to integer GPRs (`rcx, rdx, r8, r9`, returned in `rax`). **All other sizes** (including 12B, 16B `Struct16B`, `Hfa4F32`, `Mixed16B`) are `Indirect { on_stack: false }` (passed by pointer in GPR/stack, returned via `sret` in `rcx`). | Args: `Indirect { on_stack: false, align: 16 }` (pointer in `rcx`/`rdx`). Return: `Cast` to `<16 x i8>` in `xmm0` (`vmovaps` / `movaps`)! | `f16` $\to$ `half` in `xmm0`. `f128`: on **`msvc`**, `Indirect` (`sret([16 x i8])` and pointer arg, because MSVC `long double` is 64-bit); on **`windows-gnu`**, `fp128` (`xmm0` return, pointer arg). | 128b `<4 x float>` in `"C"` passed by pointer (`Indirect`), returned in `xmm0`. In `"vectorcall"` (`x86_vectorcallcc`), up to 6 vector/HFA args passed in `xmm0..xmm5` and returned in `xmm0..xmm3`! |
| **`i686-unknown-linux-gnu`** (`"C"`) (`callconv/x86.rs:1-246`) | **All** structs/unions (even 8-byte `Struct8B` and `Hfa2F32`!) are returned via `Indirect` `sret` (`[esp+4]`, callee executes `retl $4`!) and passed via `Indirect { on_stack: true }` (`byval([N x i8]) align 4` on stack). | `Direct` `i128`: passed as four 32-bit stack slots, returned in `eax, edx, ecx, ebx` (or stack). | `f16` $\to$ `half` on stack / `xmm0`; `f128` $\to$ `fp128` on stack / `xmm0`. | 128b `<4 x float>` in `"C"` passed in `xmm0..xmm2` and returned in `xmm0`. |
| **`i686-pc-windows-msvc`** (`"C"`, `"stdcall"`, `"fastcall"`, `"thiscall"`, `"vectorcall"`) (`callconv/x86_win32.rs:1-90`) | Structs of size **1, 2, 4, or 8 bytes** (including `Struct8B` and `Hfa2F32`) are returned in `eax` / `eax:edx` (`Cast` `i64`); structs >8B use `sret` (caller pops `sret` in `cdecl`; callee pops in `stdcall`/`fastcall`/`thiscall`/`vectorcall`). Args use `byval` on stack (except 16B-aligned types, which pass by pointer (`on_stack: false`) because Win32 stack is only 4B aligned!). | `Direct` `i128`. Overaligned 16B structs (`Overaligned16B`) are passed by **pointer** (`Indirect { on_stack: false }`), not `byval`! | `f16` $\to$ `half`; `f128` $\to$ `fp128`. | `"fastcall"` puts first two ≤32b int args in `ecx, edx` (`inreg`); `"thiscall"` puts first ≤32b int/ptr arg in `ecx`; `"vectorcall"` puts first two int args in `ecx, edx` (`inreg`) and up to 6 vector/HFA args in `xmm0..xmm5`. |
| **`aarch64-unknown-linux-gnu`**, **`aarch64-apple-darwin`**, **`aarch64-pc-windows-msvc`** (`"C"`, `"aapcs"`) (`callconv/aarch64.rs:1-245`) | **HFA / HVA (`is_homogeneous_aggregate`):** 1..4 elements of identical float (`f16`, `f32`, `f64`, `f128`) or 64b/128b Neon vector type $\to$ `Cast` to `[N x float/double/<4 x float>]`, passed in `v0`..`v7` and returned in `v0`..`v3` (`Hfa2F32` $\to$ `[2 x float]` in `s0, s1`; `Hfa4F32` $\to$ `[4 x float]` in `s0..s3`; `Hfa5F32` has 5 elements > 4 $\to$ `Indirect`!). Non-HFA structs ≤16B $\to$ `Cast` to `i64` or `[2 x i64]` (or `i128` if 16B-aligned on Darwin/Win64), passed in `x0`..`x7` (even-aligned `x2, x3` for 16B-aligned `i128` on Linux AAPCS64!), returned in `x0, x1`. Structs >16B $\to$ `Indirect { on_stack: false }` (caller allocates temporary, passes pointer in `x0`..`x7`; `sret` in **`x8`**!). | `Direct` `i128` in `x0, x1` (`ret`). For `cc_u128(i32, u128)`: on **Linux** & **Windows**, 16B-aligned `i128` skips `x1` and uses even-aligned **`x2, x3`**; on **Apple Darwin** (`AbiVariant::Darwin`), `i128` has 16B alignment in memory (`TargetDataLayout`) but Darwin's ARM64 ABI does **not** even-align `i128` in registers, passing it in **`x1, x2`**! | `f16` $\to$ `half` in `h0`; `f128` $\to$ `fp128` in `q0`. | 128b Neon vector `<4 x float>` in `q0..q7` (requires `+neon`). Note that in Rust `1.99.1`, `#[repr(C)] struct Hva2([f32x4; 2])` using `#[repr(simd)] struct f32x4([f32; 4])` (array-backed SIMD) is classified by `is_homogeneous_aggregate` as non-HVA (>16B `Indirect`) unless the element is a primitive target vector or float. |

### 3. Key Cross-Target Divergences Verified in the Assembly Golden Corpus

Basis: execution (`support/calling_conv_rules_and_goldens.json`, `support/goldens/O3/*.s`)

1. **Apple Darwin vs. Linux/Windows AArch64 Narrow Integer Extension and Stack Packing (`cc_narrow_int`):**
   - On `aarch64-apple-darwin`, `cc_narrow_int(i8, u8, i16, u16) -> i8` emits LLVM `signext`/`zeroext`
     on all narrow parameters and return values (`define noundef signext i8 @cc_narrow_int(i8 noundef signext %a, i8 noundef zeroext %b, i16 noundef signext %c, i16 noundef zeroext %d)`),
     so the caller extends narrow integers to 32 bits and the callee executes `add w8, w1, w0; add w8, w8, w2; add w8, w8, w3; sxtb w0, w8; ret`.
     When spilled to the stack, Apple ARM64 packs `i8`/`i16`/`i32` arguments at their natural
     1/2/4-byte alignment rather than 8-byte slots.
   - On `aarch64-unknown-linux-gnu` and `aarch64-pc-windows-msvc` (standard AAPCS64), narrow
     parameters have **no** `signext`/`zeroext` in LLVM IR (`define noundef i8 @cc_narrow_int(i8 noundef %a, i8 noundef %b, i16 noundef %c, i16 noundef %d)`),
     requiring the **callee** to extend before 32-bit arithmetic (`and w8, w1, #0xff; add w8, w8, w0, sxtb; add w8, w8, w2, sxth; and w9, w3, #0xffff; add w0, w8, w9; ret`),
     and stack arguments each occupy an 8-byte slot.
2. **AArch64 `u128` and 16-Byte-Aligned Struct Register Alignment (`cc_u128`, `cc_overaligned_16b`):**
   - For `extern "C" fn cc_u128(_dummy: i32, x: u128) -> u128`:
     - `aarch64-unknown-linux-gnu` and `aarch64-pc-windows-msvc`: `x` is passed in **`x2, x3`**
       (`x1` is skipped to satisfy AAPCS64's even-register-pair alignment rule for 16-byte
       composite/integer types: `adds x0, x2, #1; adcs x1, x3, xzr; ret`).
     - `aarch64-apple-darwin`: `x` is passed in **`x1, x2`** (`adds x0, x1, #1; adcs x1, x2, xzr; ret`)
       for `u128`, whereas `#[repr(C, align(16))] struct Overaligned16B(u64, u64)` (lowered by
       `callconv/aarch64.rs` to `Reg::i128()` cast) is passed in `x2, x3` (`add x0, x2, x3; ret`).
3. **Variadic Calls (`cc_variadic_caller`):**
   - **`x86_64-unknown-linux-gnu` (SysV):** Passes `sink` in `rdi`, `a` (`i32`) in `esi`, `c`
     (`i8 signext`) in `edx`, `b` (`f64`) in `xmm0`, and sets **`movb $1, %al`** (the count of
     vector registers used, `0..8`) before `jmpq *%rdi`.
   - **`x86_64-pc-windows-{msvc,gnu}` (Win64):** Passes `sink` in `rcx`, `a` in `edx`, and
     duplicates `b` (`f64`) in **both** `xmm2` and `r8` (`movq %xmm2, %r8`), with `c` in `r9d`.
   - **`aarch64-unknown-linux-gnu` (AAPCS64):** Passes `sink` in `x0`, `a` in `w1`, `b` in `d0`,
     and `c` in `w2` (same as non-variadic!).
   - **`aarch64-apple-darwin` (Apple ARM64):** All variadic (`...`) arguments are passed on the
     **stack** (`str w3, [sp, #8]; str d0, [sp]; br x0`), never in `x1..x7` or `v0..v7`!
   - **`aarch64-pc-windows-msvc` (Windows ARM64):** Floating-point registers are disabled for
     variadic functions; `b` (`f64`) is moved into GPR **`x2`** (`fmov x2, d0`) while `a` is in
     `w1` and `c` is in `w3`!

## Boundaries

- **Non-Tier-1 architectures (`riscv64gc`, `s390x`, `powerpc64`, `loongarch64`, `wasm32`):**
  Source rules in `compiler/rustc_target/src/callconv/` were indexed, but the 29-signature
  `-O0`/`-O3` assembly golden matrix in `support/` is scoped to the 8 Tier 1 targets.
- **`extern "C"` scalable vector (`SVE`) passing on AArch64:** Governed by AAPCS64 SVE supplement
  (`z0..z7`, `p0..p3`) and gated by `Target::features_for_correct_scalable_vector_abi` (`Some("sve")`);
  not included in the stable 8-target golden corpus because SVE types remain nightly-only.

## Evidence

- **Primary upstream sources (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_ty_utils/src/abi.rs:440-735` — `fn_abi_new_uncached`, `fn_abi_adjust_for_abi`
    (`extern "Rust"`, `"rust-call"`, `#[track_caller]`, ZST `PassMode::Ignore`, SIMD vector
    indirect rule).
  - `compiler/rustc_target/src/callconv/mod.rs:1-956` — `PassMode`, `ArgAttributes`, `CastTarget`,
    `Reg`, and `FnAbi`.
  - `compiler/rustc_target/src/callconv/x86_64.rs:1-270`, `x86_win64.rs:1-70`, `x86.rs:1-246`,
    `x86_win32.rs:1-90`, `aarch64.rs:1-245` — target-specific psABI classifiers.
  - `compiler/rustc_codegen_llvm/src/abi.rs:132-650` — `FnAbi` to LLVM IR type, attribute, and
    `CallingConv` lowering.
- **Primary upstream sources (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - `llvm/lib/Target/X86/X86CallingConv.td:1-1250` — SysV64, Win64, i386 cdecl/stdcall/fastcall/thiscall/vectorcall, and `preserve_mostcc` register allocation rules.
  - `llvm/lib/Target/AArch64/AArch64CallingConvention.td:1-850` — AAPCS64, Darwin ARM64, Win64
    ARM64, and `preserve_mostcc` register allocation rules.
- **Preserved support artifacts:**
  - `support/calling_conv_corpus.rs` — 29-function `#![no_std]` signature corpus covering
    `extern "Rust"` (scalars, `f32`, pairs, slices, triples, 128-bit SIMD vectors), `extern "rust-call"`,
    `extern "rust-cold"`, `#[track_caller]`, `extern "C"`, `extern "C-unwind"`, variadic calls,
    ZSTs + `#[repr(transparent)]`, narrow integers, 8B/16B/24B/overaligned structs, mixed
    int-float structs, 2/4/5-element HFAs, 2-element HVAs, `u128`, `f16`/`f128`, 9+9 register
    exhaustion (`cc_many_args`), and target-specific ABIs (`sysv64`, `win64`, `stdcall`,
    `fastcall`, `thiscall`, `vectorcall`).
  - `support/calling_conv_rules_and_goldens.json` — machine-readable LLVM IR signatures and
    extracted `-O0` and `-O3` assembly instructions for every signature across all 8 Tier 1 targets.
  - `support/goldens/O0/*.s` and `support/goldens/O3/*.s` — full assembly goldens for all 8 targets.

## Revalidation

To revalidate the calling-convention golden corpus on any `rustc` revision:

```bash
for tgt in x86_64-unknown-linux-gnu x86_64-pc-windows-msvc x86_64-pc-windows-gnu \
           i686-unknown-linux-gnu i686-pc-windows-msvc \
           aarch64-unknown-linux-gnu aarch64-apple-darwin aarch64-pc-windows-msvc; do
  RUSTC_BOOTSTRAP=1 rustc +1.99.1 --edition=2021 --crate-type=rlib -Copt-level=3 \
    --emit=llvm-ir,asm --target "$tgt" \
    reports/tier1-calling-conventions-fnabi-and-llvm-lowering/support/calling_conv_corpus.rs \
    --out-dir /tmp/cc_reval_"$tgt"
done
```

Compare the emitted `define ... @cc_*` lines and `.s` function bodies against
`support/calling_conv_rules_and_goldens.json`.
