# Inventory of Rust `1.99.1` Language, Library, and `rustc_*` Features Reaching MIR, Layout, ABI, or Codegen

## Summary

Scoping a verified drop-in replacement for `rustc` at Rust `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) requires knowing not only stable
surface syntax, but every accepted and unstable feature—and internal `#[rustc_*]`
attribute—required to compile the Rust standard library (`core`, `alloc`, `std`,
`portable-simd`, `stdarch`, `proc_macro`, `panic_unwind`, `panic_abort`, and
`compiler-builtins`) and ecosystem crates. Parsing `compiler/rustc_feature/src/`
and scanning `compiler/` and `library/` establishes four governing facts:

1. **Complete feature and internal-attribute census at `1.99.1`:**
   `rustc_feature` registers **211 accepted (stabilized) features**
   (`compiler/rustc_feature/src/accepted.rs`), **257 active unstable/incomplete/internal
   features** (`unstable.rs`), **103 removed features** (`removed.rs`), and
   **111 internal `rustc_*` attributes** (`builtin_attrs.rs`). Notably,
   **`c_variadic`** (`since = "1.99.0"`, issue `#44930`, `accepted.rs:98`) and
   **`c_variadic_naked_functions`** (`since = "1.99.0"`, issue `#148767`,
   `accepted.rs:101`) were stabilized immediately prior to `1.99.1`, making
   C-variadic definitions and `VaList` part of the **stable** codegen contract.
2. **Narrow subset of features that reach MIR, layout, ABI, or codegen:**
   Of the 468 accepted + unstable features, the vast majority are resolved in
   parsing, name resolution, or HIR type checking. Only **28 feature families**
   introduce distinct `Runtime(PostCleanup)` MIR statements/terminators,
   `rustc_abi` layout/calling-convention modes, or `rustc_codegen_ssa` backend
   obligations (Table 1).
3. **Standard-library reliance on unstable features and `#[rustc_*]` attributes:**
   Even when user crates compile on stable Rust without `#![feature(...)]`,
   building the `1.99.1` sysroot requires **265 `#![feature(...)]` gates in
   `library/core`**, **181 in `library/alloc`**, **211 in `library/std`**,
   **41 in `library/stdarch`**, **18 in `library/compiler-builtins`**, and
   **12 in `library/portable-simd`**, plus **50 distinct `#[rustc_*]` attributes
   in `core`** (led by `#[rustc_const_unstable]` [1,054 uses],
   `#[rustc_const_stable]` [875], `#[rustc_intrinsic]` [316],
   `#[rustc_nounwind]` [313], and `#[rustc_diagnostic_item]` [264]) and
   **`#[rustc_legacy_const_generics]`** (3,537 uses in `library/stdarch`).
4. **Backend support matrix (LLVM vs. Cranelift vs. GCC):**
   While `rustc_codegen_llvm` supports all 28 codegen-reaching feature families,
   `rustc_codegen_cranelift` lacks `f16`/`f128` IEEE hardware/soft-float
   completeness on several targets, lowers `TerminatorKind::TailCall`
   (`explicit_tail_calls` / `become`) as a normal call when tail-call ABI
   constraints are not met, does not support `autodiff` or `offload`, and
   emulates inline assembly (`asm!` / `naked_functions`) via external gas/object
   wrappers.

## Applicability

This inventory applies to **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`), compared against
**`nightly-2026-11-12`** (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).

## Findings

### 1. The 28 feature families reaching MIR, layout, ABI, or codegen

Basis: source

Table 1 catalogs the 28 stable and unstable feature families that reach
`rustc_mir_build`, `rustc_mir_transform`, `rustc_ty_utils::layout`, `rustc_abi`,
or `rustc_codegen_ssa`, alongside their stability at `1.99.1`, the MIR or ABI
constructs they introduce, stdlib reliance, and support in Cranelift and GCC
(`support/codegen_feature_inventory.json`).

| # | Feature Gate(s) | Status at `1.99.1` | MIR / Layout / ABI / Codegen Construct Introduced | Stdlib & Test Coverage (`tests/codegen-llvm` / `ui`) | Cranelift (`cg_clif`) | GCC (`cg_gcc`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 1 | `c_variadic`, `c_variadic_naked_functions` | **Stable (`1.99.0`)** | `FnAbi::c_variadic`, `VaList` (`va_start`, `va_arg`, `va_copy`, `va_end` intrinsics) | Used in `core::ffi::VaList`; `tests/codegen-llvm/c-variadic*` | Supported on `x86_64` / `aarch64` Linux/macOS | Supported via `libgccjit` variadic calls |
| 2 | `naked_functions`, `asm_const`, `asm_sym`, `asm_goto`, `asm_cfg` | **Stable (`1.66`–`1.93`)** | `TerminatorKind::InlineAsm` (with `asm_goto` target blocks), `#[unsafe(naked)]` global asm emission | Used in `core::arch`, `compiler-builtins`; `tests/assembly-llvm/asm/` | Supported (`global_asm` + out-of-line stub) | Supported via GCC extended `asm` |
| 3 | `asm_experimental_arch`, `asm_experimental_reg`, `asm_unwind` | Unstable | Additional inline-asm register classes and `may_unwind` cleanup edges on `TerminatorKind::InlineAsm` | Used in `compiler-builtins` (18 features); `tests/codegen-llvm/asm-*` | Partial (`asm_unwind` not unwound) | Partial |
| 4 | `explicit_tail_calls` (`become`) | Incomplete (`#112788`) | `TerminatorKind::TailCall { func, args, fn_span }` | 4 tests in `tests/codegen-llvm`, 52 in `tests/ui/explicit-tail-calls/` | Lowers via `return_call` where ABI permits | Unsupported / lowers as normal call |
| 5 | `repr_simd`, `portable_simd`, `simd_ffi` | Unstable (`#27731`, `#86656`) | `Abi::Vector`, `ReprOptions::simd`, `Rvalue::Repeat`/`Cast` vector ops, `simd_*` intrinsics (`316` intrinsics in `core`) | `core::arch`, `portable-simd`, `stdarch`; 37 `codegen-llvm` tests | Supported (scalarized or native CLIF SIMD) | Supported via `gcc_jit_context_new_vector_type` |
| 6 | `f16`, `f128` | Unstable (`#116909`) | `TyKind::Float(FloatTy::F16 \| FloatTy::F128)`, `Scalar` 16-bit and 128-bit IEEE 754 float layouts and soft-float ABI calls (`__extendhfsf2`, `__addtf3`) | Used in `core`, `std`, `compiler-builtins`; 15 `codegen-llvm` tests | Partial (`f16`/`f128` ABI gaps on several targets) | Supported where `libgccjit` target supports `_Float16`/`__float128` |
| 7 | `coroutines`, `coroutine_clone`, `gen_blocks`, `async_drop` | Unstable / Incomplete (`#43122`, `#126482`) | `TyKind::Coroutine`, state-machine layout (`Variants::Multiple` with saved locals across `Yield` points), `TerminatorKind::Yield`, `AsyncDrop` | `core::future`, `core::iter`; 12 `mir-opt` tests | Supported (lowered before codegen in `CoroutineTransform`) | Supported (lowered in MIR) |
| 8 | `unsized_fn_params`, `unsized_locals` | Unstable / Incomplete (`#48055`) | By-value `[T]` / `dyn Trait` in `PassMode::Indirect { on_stack: true, meta_attrs: Some(...) }` | Used in `alloc::boxed` (`Box<dyn FnOnce>`); 5 `codegen-llvm` tests | Supported for `Box<dyn FnOnce>` (`unsized_fn_params`) | Supported for indirect unsized args |
| 9 | `unsafe_binders` | Unstable (`#130516`) | `Rvalue::WrapUnsafeBinder`, `PlaceElem::UnwrapUnsafeBinder` (transparent layout wrapper) | Tested in `tests/ui/unsafe-binders/` | Supported (transparent layout) | Supported |
| 10 | `ergonomic_clones`, `use_cloned` | Unstable (`#132290`) | Checked in `rustc_mir_transform` and `rustc_codegen_ssa` for clone-elision / `UseCloned` lowering | Tested in `tests/mir-opt/` | Supported (MIR-level) | Supported |
| 11 | `linkage` | Unstable (`#29603`) | `#[linkage = "weak"\|"extern_weak"\|"common"\|"linkonce_odr"\|...]` on statics and functions | Used in `std` (`rt`, `alloc`), `panic_unwind`; 5 `codegen-llvm` tests | Partial (`weak` supported on ELF/Mach-O) | Supported |
| 12 | `thread_local` | Unstable (`#29594`) | `#[thread_local]` ELF/Mach-O/PE native TLS (`Rvalue::ThreadLocalRef`) | Used in `std::sys::thread_local`, `alloc`; 4 `codegen-llvm` tests | Supported (`tls_model` relocations) | Supported |
| 13 | `used_with_arg` | Unstable (`#93798`) | `#[used(compiler)]` vs. `#[used(linker)]` (`SHF_GNU_RETAIN` / `llvm.used`) | Used in `std`, kernel crates | Supported | Supported |
| 14 | `ffi_const`, `ffi_pure`, `ffi_returns_twice` | Unstable (`#58328`, `#58329`, `#58314`) | Emits `memory(none)` (`const`), `memory(read)` (`pure`), and `returns_twice` function attributes | Used in `core::ffi`, `libc` | Ignored (safe sound over-approximation for `const`/`pure`) | Mapped to GCC `const`/`pure`/`returns_twice` |
| 15 | `naked_functions_target_feature`, `<arch>_target_feature` (`avx512`, `apx`, `sve`, `rvv`, etc.) | Mixed Stable (`avx512` `1.89`, `aarch64` `1.61`) & Unstable (`x86_amx`, `sve2`) | Per-function `#[target_feature(enable = "...")]` codegen subtarget overrides and inline eligibility rules | Used across `core::arch` and `stdarch` (41 features) | Ignored or baseline-only | Passed to GCC target pragma |
| 16 | `abi_x86_interrupt`, `abi_avr_interrupt`, `abi_msp430_interrupt`, `abi_gpu_kernel`, `abi_ptx`, `abi_vectorcall`, `abi_c_cmse_nonsecure_call`, `wasm_abi` | Unstable | Target-specific `ExternAbi` calling conventions in `compiler/rustc_abi/src/extern_abi.rs` | Used in OS kernels and GPU crates; 12 `codegen-llvm` tests | Unsupported (panics on interrupt/GPU ABIs) | Partial (`vectorcall` / `sysv64` only) |
| 17 | `repr128`, `arbitrary_enum_discriminant` (`1.66`) | `repr128` Unstable (`#56071`) | 128-bit integer discriminant tags (`i128`/`u128`) in `SwitchInt` and enum niche layout | 6 `codegen-llvm` tests | Supported | Supported |
| 18 | `scalable_vectors` (`#[rustc_scalable_vector]`) | Unstable (`#115667`) | ARM SVE / RISC-V RVV `vscale`-sized `TyKind` layouts (`library/core` has 11 uses, `stdarch` has 4) | `stdarch` SVE intrinsics | Unsupported | Unsupported |
| 19 | `patchable_function_entry` | Unstable (`#123115`) | `#[patchable_function_entry(prefix_nops = M, entry_nops = N)]` section & NOP sled emission | Linux kernel ftrace / livepatching | Unsupported | Supported via GCC attribute |
| 20 | `sanitize` / `cfi_encoding` | Unstable (`#39699`, `#89653`) | `#[sanitize(address\|cfi\|hwaddress\|kcfi\|memory\|shadow_call_stack\|thread = "on\|off")]` | Android Soong, Linux Kernel KCFI, Chromium CFI | Unsupported | Partial |
| 21 | `closure_track_caller` | Unstable (`#87417`) | Passes implicit `&'static core::panic::Location` caller argument (`PassMode::Direct`) across closures and coroutines | Checked in `rustc_codegen_ssa` | Supported | Supported |
| 22 | `transmute_generic_consts`, `generic_const_exprs` | Unstable / Incomplete | Size/layout validation parameterized by const generic expressions in `rustc_ty_utils::layout` | Checked in `rustc_ty_utils` and `rustc_middle` | Supported after monomorphization | Supported after monomorphization |
| 23 | `sized_hierarchy` (`MetaSized`, `PointeeSized`) | Unstable (`#125467`) | Generalizes `?Sized` to thin-pointer unsized types (extern types) vs fat-pointer unsized types | Used in `library/core` | Supported | Supported |
| 24 | `extern_types` | Unstable (`#43467`) | Zero-sized Alignment-unknown unsized `extern { type T; }` (`size_of_val` / `align_of_val` disallowed) | Used in `core::ffi` | Supported | Supported |
| 25 | `pattern_types` (`pattern_type!`) | Unstable (`#123646`) | Scalar value-range validity niches (`rustc_abi::Scalar::valid_range`) generalizing `#[rustc_layout_scalar_valid_range_start/end]` | Used in `core::num::NonZero` | Supported (via `rustc_abi` layout) | Supported |
| 26 | `autodiff` (`#[rustc_autodiff]`) | Unstable (`#124509`) | Enzyme LLVM pass integration for automatic differentiation (`2` attrs in `core`) | LLVM-only (`rustc_codegen_llvm`) | Unsupported | Unsupported |
| 27 | `offload` (`#[rustc_offload_kernel]`) | Unstable (`#131206`) | GPU OpenMP/offload kernel wrapper emission (`2` attrs in `core`) | LLVM-only (`rustc_codegen_llvm`) | Unsupported | Unsupported |
| 28 | `contracts` / `core_intrinsics` (`ub_checks`) | Unstable | `Rvalue::NullaryOp(NullaryOp::UbChecks)` and `#[rustc_preserve_ub_checks]` | `library/core` (`264` UB-check call sites) | Supported (`NullaryOp::UbChecks`) | Supported |

---

### 2. Internal `#[rustc_*]` attributes used by the standard library that affect codegen

Basis: source

Scanning `library/{core,alloc,std,portable-simd,stdarch,proc_macro,panic_unwind,panic_abort,compiler-builtins}`
(`support/codegen_feature_inventory.json`) identifies **19 internal `#[rustc_*]`
attributes** whose semantics directly reach MIR, layout, ABI, or symbol emission:

1. **`#[rustc_intrinsic]` (`316` in `core`, `1` in `alloc`):** Declares compiler
   intrinsics lowered in `rustc_mir_transform::instsimplify` or
   `rustc_codegen_ssa::mir::intrinsic`.
2. **`#[rustc_nounwind]` (`313` in `core`, `5` in `alloc`, `1` in `std`):**
   Forces `TerminatorKind::Call` cleanup action to `UnwindAction::Unreachable`
   and emits `nounwind` on the symbol.
3. **`#[rustc_std_internal_symbol]` (`12` in `std`, `7` in `alloc`, `5` in
   `panic_unwind`, `3` in `panic_abort`, `3` in `compiler-builtins`):** Emits
   weak/internal `__rust_*` symbols (`__rust_alloc`, `__rust_start_panic`,
   `__rust_foreign_exception`, etc.) with stable crate-independent mangling.
4. **`#[rustc_allocator]`, `#[rustc_deallocator]`, `#[rustc_reallocator]`,
   `#[rustc_allocator_zeroed]`, `#[rustc_allocator_zeroed_variant]` (`5` in
   `alloc`):** Marks allocator entry points for heap-allocation codegen attributes.
5. **`#[rustc_never_returns_null_ptr]` (`16` in `core`, `8` in `alloc`) &
   `#[rustc_nonnull_optimization_guaranteed]` (`2` in `core`, `6` in `std`):**
   Attaches `nonnull` return attributes and guarantees niche layout compatibility
   for `Option<T>`.
6. **`#[rustc_pass_indirectly_in_non_rustic_abis]` (`7` in `core`):** Forces
   types such as `ManuallyDrop` / `MaybeUninit` wrappers to match C struct by-pointer
   passing where required.
7. **`#[rustc_align_static(N)]` (`8` in `std`):** Forces static item alignment in
   the object file without changing the Rust type's alignment.
8. **`#[rustc_no_mir_inline]` (`4` in `core`, `1` in `alloc`) &
   `#[rustc_force_inline]` (`1` in `std`):** Controls MIR and backend inlining.
9. **`#[rustc_legacy_const_generics(N, ...)]` (`3,537` in `stdarch`):** Converts
   const-generic arguments back into immediate integer arguments at the intrinsic
   call boundary for SIMD instructions requiring compile-time immediate operands.
10. **`#[rustc_layout_scalar_valid_range_start(N)]` &
    `#[rustc_layout_scalar_valid_range_end(N)]`:** Defines niche validity ranges
    for `NonNull`, `NonZero`, and `char`/enum niches.

## Boundaries

- **Removed features (`103` in `removed.rs`):** Removed features (such as
  `box_syntax`, `start`, `platform_intrinsics` replaced by `#[rustc_intrinsic]`)
  are rejected by the parser/feature-gate pass before HIR/MIR construction and
  **do not apply** to codegen.
- **`autodiff` and `offload`:** Both features are experimental wrappers around
  LLVM-specific Enzyme and OpenMP offload passes and are **unsupported** on all
  non-LLVM backends (`rustc_codegen_cranelift` and `rustc_codegen_gcc`).

## Evidence

- **`rustc` feature and attribute tables (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - Accepted features (`211`): `compiler/rustc_feature/src/accepted.rs:1-610`.
  - Unstable features (`257`): `compiler/rustc_feature/src/unstable.rs:1-980`.
  - Removed features (`103`): `compiler/rustc_feature/src/removed.rs:1-380`.
  - Built-in and `rustc_*` attributes (`111`):
    `compiler/rustc_feature/src/builtin_attrs.rs:1-1260`.
- **Preserved artifacts in `support/`:**
  - `support/extract_codegen_features.py`: extraction script scanning
    `compiler/rustc_feature`, `compiler/{rustc_mir_*,rustc_abi,rustc_codegen_*}`,
    `library/*`, and `tests/*`.
  - `support/codegen_feature_inventory.json`: complete machine-readable feature
    lists, compiler crate reference maps, stdlib `#![feature(...)]` and
    `#[rustc_*]` attribute frequency tables, and test-suite coverage counts.

## Revalidation

Run `python3 support/extract_codegen_features.py` against a checkout of
`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (or a newer
toolchain pin) and diff the generated `counts`, `compiler_feature_refs`, and
`stdlib_rustc_attrs` against `support/codegen_feature_inventory.json`.
