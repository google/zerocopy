# Multi-Target, Multi-Release `rustc` ABI Drift Matrix and Release-Fingerprinted `FnAbi` Classification

## Summary

Compiling a self-contained `#![no_core]` procedural ABI suite across **`9` targets** (`x86_64-{unknown-linux-gnu,apple-darwin,pc-windows-msvc,pc-windows-gnu}`, `aarch64-{unknown-linux-gnu,apple-darwin,pc-windows-msvc}`, `i686-{unknown-linux-gnu,pc-windows-msvc}`) and **`3` `rustc` releases** (`1.99.1`, `1.100.0`, `1.102.0-nightly`) at `-C opt-level=0`—yielding **`2,499` compiled function instances** (`833` paired functions per release transition)—refutes any assumption of `100.0%` cross-release ABI invariance on `x86_64`, `aarch64`, or `i686` and isolates four distinct compiler mechanisms driving cross-release ABI and symbol drift:

1. **All `9 / 9` Targets Experience True Cross-Release ABI or Linker-Symbol Drift (`78 / 833` = `9.36%` IR-Level Drift; `55 / 833` = `6.60%` Binary/Linker-Visible Breaks):**
   - **`1.99.1 -> 1.100.0` (`30 / 833` = `3.60%` IR and binary breaks across `6 / 9` targets):** All `5` tested `<= 128`-bit `extern "Rust"` `#[repr(simd)]` types (`SimdF32x2`, `SimdF32x4`, `SimdI32x4`, `SimdU8x16`, `SimdF64x2`) flipped from indirect pointer + `sret` (`void (ptr sret([N x i8]) align N, ptr align N)`) to direct vector-register passing (`<2 x float>`, `<4 x float>`, `<4 x i32>`, `<16 x i8>`, `<2 x double>`) on all `6` `x86` and `x86_64` targets (`rust-lang/rust` commit `429c1c18ca616ec5a097019c6071dc8ca75585be`, merged in `498b89dd40af107a23c13a009345a0dea224248c`), while all `3` `aarch64` targets and all `256`/`512`-bit `extern "Rust"` SIMD types remained `sret`.
   - **`1.100.0 -> 1.102.0-nightly` (`48 / 833` = `5.76%` IR drifts across `9 / 9` targets; `25 / 833` = `3.00%` binary/linker breaks + `23 / 833` = `2.76%` IR-only symbol-decoration migrations):**
     1. *`aarch64` `#[repr(simd)]` NEON catch-up (`15` binary breaks across all `3` `aarch64` targets):* `rust-lang/rust` commit `a654a240456566a313e53698f42c70ad7366676d` (merged in `e3c3417ff6499548c5ab52767489ab262f9a2ac0`) enabled the same `<= 128`-bit `sret -> direct vector` transition for non-softfloat `AArch64`, proving that `rustc` ABI optimizations roll out asynchronously across architectures (`1.100.0` is a staggered x86-vs-aarch64 divergence release).
     2. *Windows `x86_64` `extern "C"` non-`#[repr(C)]` ZST break (`6` binary breaks across `x86_64-pc-windows-{msvc,gnu}`):* `rust-lang/rust` commit `916dda0c26e7736748e2ef8233f1fd1477e1be1e` added `LayoutData.repr_c` and restricted Win64 indirect ZST passing to `#[repr(C)]` ZSTs, switching `()`, `ZstStruct`, and `ZstSingleEnum` under `extern "C"` from `void (ptr align 1)` to `void ()`—a live `extern "C"` calling-convention change that shifts subsequent parameter registers (`rcx`/`rdx`/`r8`/`r9`).
     3. *MSVC calling-convention symbol byte-count migration (`27` IR symbol shifts across `6` `x86`/`x86_64` targets: `3` `i686-pc-windows-msvc` `stdcall`/`fastcall`/`system` `@12`/`@20` + `24` `x86`/`x86_64` `vectorcall` `@@20`/`@@24`/`@@32`/`@@112`):* `rust-lang/rust` commit `d11b3f4d61c50f4149ea34a89302cf24a0c52b86` (merged in `62746359572280748adec7b4add65f0a1c26d1a9`) moved `\x01`-prefixed decoration upstream from LLVM MC into `rustc_codegen_llvm::declare::declare_rust_fn` using pre-lowering Rust `FnAbi` layouts. Direct `llvm-nm` inspection of compiled `.o` files proves that **`23 / 27` preserve identical `.o` linker symbols**, whereas **`4 / 27` (`abi_vec_hfa4` on all `4` `x86_64` targets, including Linux ELF and macOS Mach-O) are genuine `.o` linker-symbol breaks: `abi_vec_hfa4@@16` -> `abi_vec_hfa4@@24`**.
2. **`#![no_core]` at `-C opt-level=0` Eliminates Alias Collapse and Sysroot Gaps, While Exposing a Real Nightly ICE:** Compiling `#![no_core]` at `-C opt-level=0` compiles `27 / 27` target-release pairs cleanly without installing cross-target `libcore` `.rlib`s, avoids LLVM `MergeFunctions` `unnamed_addr alias` hiding, and yields `0 / 833` optimization-attribute-only churn across both transitions. However, `rustc 1.102.0-nightly` triggers a delayed-bug ICE (`error performing operation: fully_perform` at `compiler/rustc_trait_selection/src/traits/query/type_op/custom.rs:199:26`) on `#![no_core]` `&'static [u8]` (which compiles cleanly on `1.99.1` and `1.100.0`), requiring `*const [u8]` for portable fat-pointer probing.
3. **Cross-Target Asymmetries and Version-Pinned `FnAbi` Classification:** Real LLVM IR across the `9` targets exhibits sharp convention- and target-dependent splits (`i686` `extern "Rust"` `<4 x i8> (float)` vs. `extern "C"` `float (float)` x87 return; `u128` three-way split across `i128`, Win64 `<16 x i8> (ptr align 16)`, and `i686` `extern "Rust"` `sret`; `HfaF32x4` four-way split across AAPCS64 `[4 x float]`, SysV64 `{ double, double }`, Win64 `sret + ptr`, and `i686` `sret + byval`). Any formally verified Lean `FnAbi` classifier therefore **must** be explicitly parameterized by an immutable `CompilerAbiEpoch` pin (failing closed on unknown `rustc` releases), carry `LayoutData.repr_c` and per-function `#[target_feature]` flags, and fingerprint **both** canonical `FnAbi` pass modes and final linker-visible decorated symbol names.

## Applicability

This report examines cross-release and cross-target procedural ABI lowering across three concrete `rust-lang/rust` compiler releases and interprets those findings against the compiler-version-pinning and MIR AST boundary of `joshlf/anneal`:

- **Examined compilers (`rust-lang/rust`, executed natively on host `x86_64-unknown-linux-gnu` on `2026-11-20`):**
  - `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, commit date `2026-10-13`, bundled `LLVM 23.1.1`).
  - `rustc 1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`, commit date `2026-11-09`, bundled `LLVM 23.1.5`).
  - `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, commit date `2026-11-11`, bundled `LLVM 23.1.5`).
- **Examined verification architecture (`joshlf/anneal`):**
  - `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/rustc-capture/src/driver.rs`, compiler-version pinning check; `trusted/lean/Trusted/MirAst.lean`, structural `MirTy` and `Runtime(PostCleanup)` MIR AST).
- **Target matrix (`9` targets × `3` releases = `27` compilation cells, `2,499` emitted function definitions):**
  - `x86_64` (`4` targets, `96` functions each = `384` per release): `x86_64-unknown-linux-gnu`, `x86_64-apple-darwin`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`.
  - `aarch64` (`3` targets, `87` functions each = `261` per release): `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `aarch64-pc-windows-msvc`.
  - `i686` (`2` targets, `94` functions each = `188` per release): `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`.
- **Invocation conditions:** All primary LLVM IR matrix runs use `RUSTC_BOOTSTRAP=1 RUSTC_ICE=0 rustc +<toolchain> --target <target> -C opt-level=0 -C debuginfo=0 --emit=llvm-ir` on a single `#![crate_type = "lib"]` `#![no_core]` translation unit (`support/e2_6_9target_3release_abi_matrix.py`). Companion object-file linker-symbol verification uses the identical flags with `--emit=obj` followed by `llvm-nm --defined-only -g`.
- **Relationship to prior corpus reports:** `rustc-release-abi-drift-binary-validation-cfg-alignment-and-surviving-bounds-checks` previously measured cross-release drift only on `x86_64-unknown-linux-gnu` at `-C opt-level=2` and explicitly marked `i686` and `aarch64` cross-release drift as not examined because cross-target standard libraries were absent for `1.100.0` and `1.102.0-nightly`. This report resolves that boundary across all `9` targets via `#![no_core]`, disambiguates IR-level symbol migrations from `.o`-level linker breaks, and pins every observed drift to its exact `rust-lang/rust` source commit. Claims about releases outside `{1.99.1, 1.100.0, 1.102.0-nightly}` are not inferred by continuity; each release must be probed directly via the revalidation suite.

## Findings

### 1. Self-Contained `#![no_core]` `-C opt-level=0` Matrix Design and the `1.102.0-nightly` `fully_perform` ICE

`Basis: execution + source (support/e2_6_9target_3release_abi_matrix.py, support/e2_6_9target_3release_abi_matrix.json, live rustc +1.99.1/+1.100.0/+nightly reproducer)`

Cross-target, multi-release ABI differential testing faces two practical failure modes when executed on standard `libcore`-linked Rust crates at `-C opt-level=2`:

1. **Missing Cross-Target Sysroot `.rlib`s:** Installing `rust-std` components for every `(target, release)` pair is brittle across pinned stable and nightly toolchains. Declaring `#![no_core]` with the five minimal language-item traits (`PointeeSized`, `MetaSized`, `Sized`, `Copy`, and `unsafe auto trait Freeze`) and enabling `#![feature(no_core, lang_items, repr_simd, auto_traits, abi_vectorcall)]` under `RUSTC_BOOTSTRAP=1` lets `rustc` execute full type-checking, layout computation (`rustc_abi`), calling-convention classification (`rustc_target::callconv`), LLVM IR generation (`rustc_codegen_llvm`), and native object emission (`--emit=obj`) for all `9` targets across all `3` releases (`27 / 27` cells succeed) using only the host `rustc` binary.
2. **LLVM `MergeFunctions` Alias Hiding and Optimization-Attribute Noise:** At `-C opt-level=2`, LLVM's `MergeFunctions` pass collapses structurally identical lowered functions into `unnamed_addr alias` definitions (for example, `139–140` of `256` symbols in `rustc-release-abi-drift-binary-validation-cfg-alignment-and-surviving-bounds-checks` collapsed to aliases), and LLVM's function-attribute inference emits version-sensitive optimization attributes (`captures(none)` vs. `nocapture`, `dead_on_unwind`, `dead_on_return`, `initializes(...)`, `dereferenceable(...)`). Compiling at `-C opt-level=0 -C debuginfo=0` suppresses `MergeFunctions` completely—every source function emits an independent `define` header—and reduces optimization-attribute-only churn (`opt_attr_only_churn_*` in `support/e2_6_9target_3release_abi_matrix.json`) to **`0 / 833` pairs in both release transitions**.

#### Suite Composition (`99` Source Functions -> `96` `x86_64`, `87` `aarch64`, `94` `i686` Emitted Definitions)

The single-file `#![no_core]` suite defines `99` `#[no_mangle]` probe functions spanning four orthogonal ABI axes:

| Probe Group | Source Fns | Target Gating (`#[cfg]`) | Covered ABI Constructs |
| :--- | ---: | :--- | :--- |
| **Base `extern "Rust"` types** | `41` | All `9` targets (`41` each) | Scalars (`()`, `bool`, `u8`, `i16`, `u32`, `i64`, `usize`, `u128`, `i128`, `f32`, `f64`), ZST struct/enum (`ZstStruct`, `ZstSingleEnum`), `#[repr(transparent)]` (`TransU64`, `TransWithZst`), `#[repr(C)]` aggregates (`PairU64`, `TripleU64`, `Sub8Bytes`, `PackedU16U64`, `Align16U64`), HFAs (`HfaF32x2`–`HfaF32x5`, `HfaF64x2`), mixed int/float (`MixedIntFloat`, `MixedFloatInt`, `MixedU64F64`), `repr(Rust)` struct (`RustPair`), enums (`TagU8Enum`, `NicheRefEnum<'static>`, `NicheResultU64`), wide pointer (`*const [u8]`), and `8` `#[repr(simd)]` types (`64`-bit through `512`-bit). |
| **Base `extern "C"` types** | `38` | All `9` targets (`38` each) | All `41` base types except the `3` `256`/`512`-bit SIMD types (`SimdF32x8`, `SimdI64x4`, `SimdF32x16`), which require explicit target features under `extern "C"`. |
| **Feature-gated wide SIMD `extern "C"`** | `3` | `target_arch = "x86_64"` (`+3` on `x86_64`) | `abi_c_avx_simd_f32x8` (`avx`), `abi_c_avx_simd_i64x4` (`avx`), `abi_c_avx512_simd_f32x16` (`avx512f`). |
| **Multi-arg & cross-platform conventions** | `8` | All `9` targets (`8` each) | Register exhaustion (`abi_rust_many_gpr8`, `abi_c_many_gpr8`, `abi_c_many_fp9`), odd-slot `u128` alignment (`abi_c_odd_i128_align`, `abi_rust_odd_i128_align`), `extern "C-unwind"` (`abi_c_unwind_pair`), `extern "system"` (`abi_system_u64_f32`), and `extern "efiapi"` (`abi_efiapi_pair`). |
| **x86 / x86_64-specific conventions** | `9` | `4` `vectorcall` (`x86` \| `x86_64`), `2` `sysv64`/`win64` (`x86_64`), `3` `fastcall`/`stdcall`/`thiscall` (`x86`) | `abi_vec_f32x4`, `abi_vec_hfa4`, `abi_vec_f32x8` (`avx`), `abi_vec_many6_simd` (7 SIMD args exhausting `xmm0`–`xmm5`); `abi_sysv64_hfa2`, `abi_win64_hfa2`; `abi_fastcall_i686`, `abi_stdcall_i686`, `abi_thiscall_i686`. |
| **Total emitted per release** | **`99`** | `96 × 4` + `87 × 3` + `94 × 2` = **`833`** | **`833 × 3` releases = `2,499` compiled function instances (`100%` `ok: true`).** |

#### Normalization Discipline (`abi_shape` vs. `full_header`)

For each LLVM `define` line, `normalize_llvm_def_header` computes two distinct canonical strings:
- **`full_header`:** Strips `unnamed_addr`, attribute-group tags (`#0`), metadata (`!guid`), and SSA `%var` names while keeping the exact raw symbol name (`@raw_sym`) and every inline parameter/return attribute.
- **`abi_shape`:** Retains the exact calling convention (`x86_vectorcallcc`, `win64cc`, `x86_64_sysvcc`, `x86_stdcallcc`, `x86_fastcallcc`, `x86_thiscallcc`, or default C), return type, `sret(...)`, `byval(...)`, `inreg`, `align N`, parameter LLVM types, and any MSVC `@N`/`@@N` symbol suffix—while stripping `16` pure optimization attributes (`noundef`, `nofree`, `nosync`, `noalias`, `nonnull`, `readonly`, `writeonly`, `writable`, `returned`, `dead_on_unwind`, `dead_on_return`, `captures(...)`, `nocapture`, `initializes(...)`, `dereferenceable[_or_null](...)`, `range(...)`). A difference in `abi_shape` therefore reflects either a machine-level calling-convention/layout change or an IR symbol-decoration change, never optimization-metadata churn.

#### Live `rustc 1.102.0-nightly` `#![no_core]` ICE on `&'static [u8]`

When probing wide-pointer ABI lowering in `#![no_core]` with the minimal five-trait header above (`PointeeSized`, `MetaSized`, `Sized`, `Copy`, `Freeze`), declaring `pub fn abi_rust_slice_ref(x: &'static [u8]) -> &'static [u8] { x }` compiles with exit code `0` on both `rustc 1.99.1` and `rustc 1.100.0`, but **crashes `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) with exit code `101` (`RUSTC_ICE=0`)**:

```text
note: no errors encountered even though delayed bugs were created
note: those delayed bugs will now be shown as internal compiler errors
error: internal compiler error: error performing operation: fully_perform
  --> ice.rs:10:77
   |
10 | ...&'static [u8]) -> &'static [u8] { x }
   |                                      ^
note: delayed at /rustc-dev/3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1/compiler/rustc_trait_selection/src/traits/query/type_op/custom.rs:199:26 - disabled backtrace
```

Replacing `&'static [u8]` with raw fat pointer `*const [u8]` (`abi_rust_fat_slice_ptr` and `abi_c_fat_slice_ptr`) eliminates the region/trait-selection query path that triggers `fully_perform` in minimal `#![no_core]` environments while preserving the exact two-word `(ptr, usize)` slice-pointer ABI (`{ ptr, i64 } (ptr, i64)` on 64-bit `extern "Rust"`, `{ ptr, i32 } (ptr, i32)` on `i686` `extern "Rust"`). Note that `&'a u64` inside `NicheRefEnum<'static>` (a thin reference) does **not** trigger the ICE on `1.102.0-nightly`; the failure is specific to the unsized slice reference `&'static [u8]` under minimal `#![no_core]`.

### 2. Complete 9-Target × 3-Release ABI Drift Matrix (`78 / 833` IR Drifts; `55 / 833` Binary/Linker Breaks)

`Basis: execution + source (support/e2_6_9target_3release_abi_matrix.json, --emit=obj + llvm-nm verification across all 6 x86/x86_64 targets, rust-lang/rust commits 429c1c18ca616ec5a097019c6071dc8ca75585be, a654a240456566a313e53698f42c70ad7366676d, 916dda0c26e7736748e2ef8233f1fd1477e1be1e, d11b3f4d61c50f4149ea34a89302cf24a0c52b86)`

Across the `833` paired functions per release transition, **`78 / 833` (`9.36%`)** exhibit cumulative IR-level `abi_shape` drift from `rustc 1.99.1` to `rustc 1.102.0-nightly`, and **every single one of the `9` tested targets (`9 / 9`)** experiences genuine binary- or linker-visible ABI breaks (`55 / 833` = `6.60%` cumulative binary/linker breaks plus `23 / 833` = `2.76%` IR-only symbol-decoration migrations):

| Target Triple | Emitted Fns / Release | `1.99.1 -> 1.100.0` Drift (IR = Binary) | `1.100.0 -> 1.102.0-nightly` IR Drift | Cumulative `1.99.1 -> 1.102.0-nightly` IR Drift | Genuine Binary / `.o` Linker Breaks | IR-Only Symbol Migrations (`.o` Identical) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `x86_64-unknown-linux-gnu` | `96` | `5` (`5.21%`) | `4` (`4.17%`) | `9` (`9.38%`) | **`6`** (`5` SIMD + `1` `abi_vec_hfa4@@24`) | `3` (`vectorcall`) |
| `x86_64-apple-darwin` | `96` | `5` (`5.21%`) | `4` (`4.17%`) | `9` (`9.38%`) | **`6`** (`5` SIMD + `1` `abi_vec_hfa4@@24`) | `3` (`vectorcall`) |
| `x86_64-pc-windows-msvc` | `96` | `5` (`5.21%`) | `7` (`7.29%`) | `12` (`12.50%`) | **`9`** (`5` SIMD + `3` Win64 ZST + `1` `abi_vec_hfa4@@24`) | `3` (`vectorcall`) |
| `x86_64-pc-windows-gnu` | `96` | `5` (`5.21%`) | `7` (`7.29%`) | `12` (`12.50%`) | **`9`** (`5` SIMD + `3` Win64 ZST + `1` `abi_vec_hfa4@@24`) | `3` (`vectorcall`) |
| `aarch64-unknown-linux-gnu` | `87` | `0` (`0.00%`) | `5` (`5.75%`) | `5` (`5.75%`) | **`5`** (`5` NEON SIMD) | `0` |
| `aarch64-apple-darwin` | `87` | `0` (`0.00%`) | `5` (`5.75%`) | `5` (`5.75%`) | **`5`** (`5` NEON SIMD) | `0` |
| `aarch64-pc-windows-msvc` | `87` | `0` (`0.00%`) | `5` (`5.75%`) | `5` (`5.75%`) | **`5`** (`5` NEON SIMD) | `0` |
| `i686-unknown-linux-gnu` | `94` | `5` (`5.32%`) | `4` (`4.26%`) | `9` (`9.57%`) | **`5`** (`5` SIMD) | `4` (`vectorcall`) |
| `i686-pc-windows-msvc` | `94` | `5` (`5.32%`) | `7` (`7.45%`) | `12` (`12.77%`) | **`5`** (`5` SIMD) | `7` (`4` `vectorcall` + `3` `std`/`fast`/`sys`) |
| **Total (`9` targets)** | **`833`** | **`30` (`3.60%`)** | **`48` (`5.76%`)** | **`78` (`9.36%`)** | **`55` (`6.60%`)** | **`23` (`2.76%`)** |

Zero functions drifted in both transitions (the `30` drifts in `1.99.1 -> 1.100.0` and the `48` drifts in `1.100.0 -> 1.102.0-nightly` are strictly disjoint sets, summing to exactly `78`). Furthermore, `opt_attr_only_churn_1_99_1_to_1_100_0` and `opt_attr_only_churn_1_100_0_to_nightly` are both `{}` (`0` pairs across all `9` targets).

#### Causal Upstream Analysis of All Four Drift Classes

Every single one of the `78` drifts traces directly to one of four discrete commits in `rust-lang/rust`:

| Drift Class | Transition | IR Pairs | Binary / `.o` Breaks | Upstream `rust-lang/rust` Commit & File | Exact Semantic Mechanism |
| :--- | :--- | ---: | ---: | :--- | :--- |
| **D1. x86 / x86_64 `extern "Rust"` SIMD SSE Register Passing** | `1.99.1 -> 1.100.0` | `30` | **`30`** | `429c1c18ca616ec5a097019c6071dc8ca75585be` (merged `498b89dd40af107a23c13a009345a0dea224248c`), `compiler/rustc_target/src/callconv/mod.rs` | On `x86` targets requiring SSE2 (`i686-{linux,win-msvc}`) and non-softfloat `x86_64` (`linux`, `darwin`, `win-msvc`, `win-gnu`), `extern "Rust"` `#[repr(simd)]` types with `size.bits() <= 128` switch from indirect `sret` + `ptr` to direct vector registers (`xmm0`). |
| **D2. AArch64 `extern "Rust"` SIMD NEON Catch-Up** | `1.100.0 -> 1.102.0-nightly` | `15` | **`15`** | `a654a240456566a313e53698f42c70ad7366676d` (merged `e3c3417ff6499548c5ab52767489ab262f9a2ac0`), `compiler/rustc_target/src/callconv/mod.rs:833-839` | Extends the exact same `arg.layout.size.bits() <= 128` register-passing rule to `Arch::AArch64 if spec.rustc_abi != Some(RustcAbi::Softfloat)` (baseline NEON required), flipping the same `5` SIMD types across `aarch64-{linux,darwin,win-msvc}` one release cycle later. |
| **D3. Win64 `extern "C"` Non-`#[repr(C)]` ZST Break** | `1.100.0 -> 1.102.0-nightly` | `6` | **`6`** | `916dda0c26e7736748e2ef8233f1fd1477e1be1e`, `compiler/rustc_abi/src/layout.rs` + `compiler/rustc_target/src/callconv/x86_win64.rs:44-68` | Adds `LayoutData.repr_c: bool` (true for `#[repr(C)]` or `#[repr(transparent)]` wrapping `#[repr(C)]`). Restricts Win64 indirect ZST passing (`make_indirect_from_ignore`) to `layout.is_repr_c()`, changing `()`, `ZstStruct`, and `ZstSingleEnum` in `extern "C"` from `void (ptr align 1)` to `void ()` on both `x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu`. |
| **D4. MSVC Calling-Convention Symbol Byte-Count Decoration** | `1.100.0 -> 1.102.0-nightly` | `27` (`3` `i686` + `24` `vectorcall`) | **`4`** (`abi_vec_hfa4` × `4` `x86_64` targets) | `d11b3f4d61c50f4149ea34a89302cf24a0c52b86` (merged `62746359572280748adec7b4add65f0a1c26d1a9`), `compiler/rustc_codegen_llvm/src/declare.rs:169-185` + `compiler/rustc_codegen_ssa/src/common.rs:179-225` | Moves `\x01`-prefixed `@N`/`@@N` decoration out of LLVM MC into `declare_rust_fn` via `windows_calling_convention_name`, summing `arg.layout.size.bytes().next_multiple_of(pointer_bytes)` on pre-lowering Rust `FnAbi` layouts (decorating `vectorcall` on all x86/x86_64 OSes, and `stdcall`/`fastcall`/`system` on 32-bit Windows). |

#### Complete Exhaustive Drift Catalog (`30` `1.99.1 -> 1.100.0` + `48` `1.100.0 -> 1.102.0-nightly`)

1. **`1.99.1 -> 1.100.0` (`30` pairs — D1 on all `6` `x86` / `x86_64` targets):**
   Every one of the `6` targets (`x86_64-unknown-linux-gnu`, `x86_64-apple-darwin`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`) exhibits the exact same `5` transitions (`5 × 6 = 30`):
   - `abi_rust_simd_f32x2`: `void (ptr sret([8 x i8]) align 8, ptr align 8)` $\rightarrow$ `<2 x float> (<2 x float>)`
   - `abi_rust_simd_f32x4`: `void (ptr sret([16 x i8]) align 16, ptr align 16)` $\rightarrow$ `<4 x float> (<4 x float>)`
   - `abi_rust_simd_f64x2`: `void (ptr sret([16 x i8]) align 16, ptr align 16)` $\rightarrow$ `<2 x double> (<2 x double>)`
   - `abi_rust_simd_i32x4`: `void (ptr sret([16 x i8]) align 16, ptr align 16)` $\rightarrow$ `<4 x i32> (<4 x i32>)`
   - `abi_rust_simd_u8x16`: `void (ptr sret([16 x i8]) align 16, ptr align 16)` $\rightarrow$ `<16 x i8> (<16 x i8>)`
   - *Threshold boundary (`<= 128` bits):* `abi_rust_simd_f32x8` (`256`-bit), `abi_rust_simd_i64x4` (`256`-bit), and `abi_rust_simd_f32x16` (`512`-bit) remained `void (ptr sret([32|64 x i8]) align 32|64, ptr align 32|64)` on all `9` targets across all `3` releases because neither AVX nor AVX-512 is a baseline required target feature.

2. **`1.100.0 -> 1.102.0-nightly` (`48` pairs across all `9` targets):**
   - **D2 (`15` pairs — `3` `aarch64` targets × `5` SIMD types):** `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, and `aarch64-pc-windows-msvc` each undergo the exact `5` transitions listed above (`abi_rust_simd_{f32x2,f32x4,f64x2,i32x4,u8x16}`). Notably, `rustc 1.100.0` sits squarely inside an **asymmetric cross-architecture window** where `extern "Rust"` `SimdF32x4` is passed in registers on `x86_64`/`i686` but via `sret` on `aarch64`.
   - **D3 (`6` pairs — `2` Win64 targets × `3` non-`#[repr(C)]` ZSTs):** On both `x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu`, `abi_c_unit` (`()`), `abi_c_zst_struct` (`ZstStruct`), and `abi_c_zst_enum` (`ZstSingleEnum`) change from `void (ptr align 1)` in `1.99.1`/`1.100.0` to `void ()` in `1.102.0-nightly`. By contrast, all `7` other targets (`x86_64-{linux,darwin}`, all `3` `aarch64`, and both `i686`) already emitted `void ()` in `1.99.1` and `1.100.0`. Because Win64 allocates integer arguments into `rcx`, `rdx`, `r8`, `r9`, eliminating the hidden `ptr align 1` slot shifts every subsequent parameter register by one position for any `extern "C"` function taking a non-`#[repr(C)]` Rust ZST before non-ZST arguments!
   - **D4a (`3` pairs — `i686-pc-windows-msvc` `stdcall` / `fastcall` / `system`):**
     - `abi_fastcall_i686`: `x86_fastcallcc float (i32 inreg, i32 inreg, float, i64)` (sym `abi_fastcall_i686`) $\rightarrow$ `...@20` (sym `\01@abi_fastcall_i686@20`)
     - `abi_stdcall_i686`: `x86_stdcallcc i32 (i32, ptr byval([16 x i8]) align 4)` (sym `abi_stdcall_i686`) $\rightarrow$ `...@20` (sym `\01_abi_stdcall_i686@20`)
     - `abi_system_u64_f32`: `x86_stdcallcc float (i64, float)` (sym `abi_system_u64_f32`) $\rightarrow$ `...@12` (sym `\01_abi_system_u64_f32@12`)
     - Note: `abi_thiscall_i686` (`x86_thiscallcc float (ptr, i32, float)`) did **not** change symbol name (`abi_thiscall_i686` in both releases), and `i686-unknown-linux-gnu` did **not** decorate `stdcall`/`fastcall`/`system`.
   - **D4b (`24` pairs — `6` `x86`/`x86_64` targets × `4` `vectorcall` functions):**
     - On all `4` `x86_64` targets (`unknown-linux-gnu`, `apple-darwin`, `pc-windows-msvc`, `pc-windows-gnu`):
       - `abi_vec_f32x4`: `x86_vectorcallcc <4 x float> (<4 x float>, <4 x float>)` $\rightarrow$ `...@@32` (`\01abi_vec_f32x4@@32`)
       - `abi_vec_f32x8`: `x86_vectorcallcc <8 x float> (<8 x float>)` $\rightarrow$ `...@@32` (`\01abi_vec_f32x8@@32`)
       - `abi_vec_hfa4`: `x86_vectorcallcc void (ptr sret([16 x i8]) align 4, ptr align 4, float)` $\rightarrow$ `...@@24` (`\01abi_vec_hfa4@@24`)
       - `abi_vec_many6_simd`: `x86_vectorcallcc <4 x float> (<4 x float> × 7)` $\rightarrow$ `...@@112` (`\01abi_vec_many6_simd@@112`)
     - On both `i686` targets (`unknown-linux-gnu`, `pc-windows-msvc`): identical `@@32`, `@@32`, `@@112` for the three SIMD functions, and `abi_vec_hfa4` emits `x86_vectorcallcc void (ptr sret([16 x i8]) align 4, ptr byval([16 x i8]) align 4, float)` $\rightarrow$ `...@@20` (`\01abi_vec_hfa4@@20`, where `next_multiple_of(16, 4) + next_multiple_of(4, 4) = 20`).

#### Separating IR-Only Decoration Migration (`23` Pairs) from True `.o` Linker-Symbol Breaks (`4` Pairs)

Compiling the exact same suite with `--emit=obj` on `1.100.0` vs. `1.102.0-nightly` across all `6` `x86`/`x86_64` targets and inspecting global defined symbols via `llvm-nm --defined-only -g` exposes a critical distinction invisible from LLVM IR alone:

| Function | Targets | `1.100.0` LLVM IR Sym | `1.100.0` `.o` Symbol (`llvm-nm`) | `1.102.0-nightly` `.o` Symbol (`llvm-nm`) | Verdict |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `abi_vec_hfa4` | All `4` `x86_64` (`linux`, `darwin`, `win-msvc`, `win-gnu`) | `abi_vec_hfa4` | **`abi_vec_hfa4@@16`** | **`abi_vec_hfa4@@24`** | **GENUINE `.o` LINKER BREAK (`4` pairs)** |
| `abi_vec_hfa4` | Both `i686` (`linux`, `win-msvc`) | `abi_vec_hfa4` | `abi_vec_hfa4@@20` | `abi_vec_hfa4@@20` | IR-only migration (`2` pairs) |
| `abi_vec_f32x4` / `f32x8` / `many6_simd` | All `6` `x86` / `x86_64` | undecorated | `@@32` / `@@32` / `@@112` | `@@32` / `@@32` / `@@112` | IR-only migration (`18` pairs) |
| `abi_fastcall_i686` / `stdcall_i686` / `system_u64_f32` | `i686-pc-windows-msvc` | undecorated | `@...@20` / `_...@20` / `_...@12` | `@...@20` / `_...@20` / `_...@12` | IR-only migration (`3` pairs) |

**Why `abi_vec_hfa4` broke on `x86_64` (`@@16 -> @@24`) but not `i686` (`@@20`):** On `x86_64`, `HfaF32x4` (`16` B) is lowered under `vectorcall` as an indirect `ptr align 4` (not `byval`). In `1.99.1` and `1.100.0`, LLVM MC computed the `@@N` suffix post-lowering from LLVM IR parameter types (excluding `sret`): `sizeof(ptr) + round8(sizeof(float)) = 8 + 8 = 16` (`abi_vec_hfa4@@16`). In `1.102.0-nightly` (`d11b3f4d6`), `rustc_codegen_ssa::common::windows_abi_argument_byte_sum` computes `next_multiple_of(16, 8) + next_multiple_of(4, 8) = 16 + 8 = 24` (`abi_vec_hfa4@@24`) directly from pre-lowering Rust `FnAbi` layouts—fixing the byte count to match MSVC's pre-indirection rule while breaking binary link compatibility against `1.99.1`/`1.100.0` objects on all `4` `x86_64` platforms (including Linux ELF and macOS Mach-O!). On `i686`, `HfaF32x4` was passed via `ptr byval([16 x i8])`, so LLVM MC already summed `16 + 4 = 20`.

### 3. Cross-Target ABI Spotlights Matrix Across All `9` Targets

`Basis: execution (support/e2_6_9target_3release_abi_matrix.json spotlights + live rustc +1.100.0/+nightly LLVM IR extraction across all 9 targets)`

The matrix exposes deep, persistent cross-target and Rust-vs.-C lowering divergences that hold across all `3` releases (except where release drift is explicitly annotated). Grouping the `9` targets into their `5` distinct ABI families—**SysV64** (`x86_64-{unknown-linux-gnu,apple-darwin}`), **Win64** (`x86_64-pc-windows-{msvc,gnu}`), **AAPCS64** (`aarch64-{unknown-linux-gnu,apple-darwin,pc-windows-msvc}`), **i686-Linux** (`i686-unknown-linux-gnu`), and **i686-MSVC** (`i686-pc-windows-msvc`)—yields the complete spotlights comparison below:

| Function (`extern`) | SysV64 (`x86_64-{linux,darwin}`) | Win64 (`x86_64-win-{msvc,gnu}`) | AAPCS64 (`aarch64-{linux,darwin,win}`) | `i686-unknown-linux-gnu` | `i686-pc-windows-msvc` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `abi_rust_f32` (`Rust`) | `float (float)` | `float (float)` | `float (float)` | **`<4 x i8> (float)`** | **`<4 x i8> (float)`** |
| `abi_c_f32` (`C`) | `float (float)` | `float (float)` | `float (float)` | **`float (float)`** | **`float (float)`** |
| `abi_rust_f64` (`Rust`) | `double (double)` | `double (double)` | `double (double)` | **`<8 x i8> (double)`** | **`<8 x i8> (double)`** |
| `abi_c_f64` (`C`) | `double (double)` | `double (double)` | `double (double)` | **`double (double)`** | **`double (double)`** |
| `abi_rust_u128` (`Rust`) | `i128 (i128)` | `i128 (i128)` | `i128 (i128)` | **`void (ptr sret([16 x i8]) align 16, i128)`** | **`void (ptr sret([16 x i8]) align 16, i128)`** |
| `abi_c_u128` (`C`) | `i128 (i128)` | **`<16 x i8> (ptr align 16)`** | `i128 (i128)` | `i128 (i128)` | `i128 (i128)` |
| `abi_rust_hfa_f32x4` (`Rust`) | `void (ptr sret([16 x i8]) align 4, ptr align 4)` | `void (ptr sret([16 x i8]) align 4, ptr align 4)` | `void (ptr sret([16 x i8]) align 4, ptr align 4)` | `void (ptr sret([16 x i8]) align 4, ptr align 4)` | `void (ptr sret([16 x i8]) align 4, ptr align 4)` |
| `abi_c_hfa_f32x4` (`C`) | **`{ double, double } ({ double, double })`** | **`void (ptr sret([16 x i8]) align 4, ptr align 4)`** | **`[4 x float] ([4 x float])`** | **`void (ptr sret([16 x i8]) align 4, ptr byval([16 x i8]) align 4)`** | **`void (ptr sret([16 x i8]) align 4, ptr byval([16 x i8]) align 4)`** |
| `abi_rust_simd_f32x4` (`Rust`) | `1.99.1`: `sret + ptr` -> `1.100.0+`: **`<4 x float> (<4 x float>)`** | `1.99.1`: `sret + ptr` -> `1.100.0+`: **`<4 x float> (<4 x float>)`** | `1.99.1`/`1.100.0`: `sret + ptr` -> `1.102`: **`<4 x float> (<4 x float>)`** | `1.99.1`: `sret + ptr` -> `1.100.0+`: **`<4 x float> (<4 x float>)`** | `1.99.1`: `sret + ptr` -> `1.100.0+`: **`<4 x float> (<4 x float>)`** |
| `abi_c_simd_f32x4` (`C`) | `<4 x float> (<4 x float>)` | `<4 x float> (<4 x float>)` | `<4 x float> (<4 x float>)` | `<4 x float> (<4 x float>)` | `<4 x float> (<4 x float>)` |
| `abi_rust_simd_f32x8` (`Rust`) | `void (ptr sret([32 x i8]) align 32, ptr align 32)` | `void (ptr sret([32 x i8]) align 32, ptr align 32)` | `void (ptr sret([32 x i8]) align 32, ptr align 32)` | `void (ptr sret([32 x i8]) align 32, ptr align 32)` | `void (ptr sret([32 x i8]) align 32, ptr align 32)` |
| `abi_vec_f32x4` (`vectorcall`) | `x86_vectorcallcc <4 x float> (<4 x float>, <4 x float>)` (`@@32` IR in `1.102`) | same (`@@32` IR in `1.102`) | *(not compiled)* | same (`@@32` IR in `1.102`) | same (`@@32` IR in `1.102`) |
| `abi_vec_hfa4` (`vectorcall`) | `x86_vectorcallcc void (ptr sret([16 x i8]) align 4, ptr align 4, float)` (`.o` **`@@16 -> @@24`**) | same (`.o` **`@@16 -> @@24`**) | *(not compiled)* | `... ptr byval([16 x i8]) align 4, float` (`.o` `@@20`) | `... ptr byval([16 x i8]) align 4, float` (`.o` `@@20`) |

Companion verified cross-target divergences extracted from the same suite further constrain any formal ABI model:

| Companion Probe | SysV64 (`linux`) | Win64 (`msvc`) | AAPCS64 (`linux`) | `i686-linux` | `i686-msvc` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `abi_c_unit` (`()`) | `void ()` | **`void (ptr align 1)` -> `void ()` (`1.102`)** | `void ()` | `void ()` | `void ()` |
| `abi_rust_fat_slice_ptr` (`*const [u8]`) | `{ ptr, i64 } (ptr, i64)` | `{ ptr, i64 } (ptr, i64)` | `{ ptr, i64 } (ptr, i64)` | `{ ptr, i32 } (ptr, i32)` | `{ ptr, i32 } (ptr, i32)` |
| `abi_c_fat_slice_ptr` (`*const [u8]`) | `{ i64, i64 } ({ i64, i64 })` | `void (ptr sret([16 x i8]) align 8, ptr align 8)` | `[2 x i64] ([2 x i64])` | `void (ptr sret([8 x i8]) align 4, ptr byval([8 x i8]) align 4)` | **`i64 (ptr byval([8 x i8]) align 4)`** |
| `abi_c_pair_u64` (`PairU64`) | `{ i64, i64 } ({ i64, i64 })` | `void (ptr sret([16 x i8]) align 8, ptr align 8)` | `[2 x i64] ([2 x i64])` | `void (ptr sret([16 x i8]) align 4, ptr byval([16 x i8]) align 4)` | `void (ptr sret([16 x i8]) align 8, ptr byval([16 x i8]) align 4)` |
| `abi_c_mixed_int_float` (`(u32, f32)`) | `i64 (i64)` | `i64 (i64)` | `i64 (i64)` | `void (ptr sret([8 x i8]) align 4, ptr byval([8 x i8]) align 4)` | **`i64 (ptr byval([8 x i8]) align 4)`** |
| `abi_efiapi_pair` (`efiapi`) | **`win64cc { i64, i64 } (i64, { i64, i64 }, double)`** | **`win64cc void (ptr sret([16 x i8]) align 8, i64, ptr align 8, double)`** | `[2 x i64] (i64, [2 x i64], double)` | `void (ptr sret([16 x i8]) align 4, i64, ptr byval([16 x i8]) align 4, double)` | `void (ptr sret([16 x i8]) align 8, i64, ptr byval([16 x i8]) align 4, double)` |
| `abi_c_avx_simd_f32x8` (`avx`) | `<8 x float> (<8 x float>)` | `<8 x float> (<8 x float>)` | *(x86_64 only)* | *(x86_64 only)* | *(x86_64 only)* |
| `abi_c_avx512_simd_f32x16` (`avx512f`) | `<16 x float> (<16 x float>)` | `<16 x float> (<16 x float>)` | *(x86_64 only)* | *(x86_64 only)* | *(x86_64 only)* |

Four cross-target architectural insights emerge directly from these tables:

1. **x87 `st(0)` NaN-Preservation Avoidance on `i686` (`extern "Rust"` vs. `extern "C"`):** On both `i686-unknown-linux-gnu` and `i686-pc-windows-msvc`, `extern "C"` returns `f32`/`f64` as LLVM `float`/`double` (which lowers to x87 `st(0)` and can quiet signaling NaNs or introduce 80-bit rounding transitions), whereas `extern "Rust"` casts the return value to `<4 x i8>` / `<8 x i8>` (integer/vector bit-preserving return) while keeping the incoming argument as `float`/`double`! Any model assuming `f32 -> f32` has symmetric parameter/return lowering on 32-bit x86 is immediately falsified.
2. **Three-Way `u128` Split (With `i686` Inversion and Win64 `<16 x i8>` Return):** On `x86_64-pc-windows-{msvc,gnu}`, `extern "C"` `u128` is **not** `{ i64, i64 }` and **not** `i128`—it passes indirectly via `ptr align 16` and returns in `xmm0` via `<16 x i8>` (`<16 x i8> (ptr align 16)`), whereas `extern "Rust"` `u128` on the exact same Windows targets lowers to `i128 (i128)`. Conversely, on `i686`, `extern "Rust"` returns `u128` via hidden `ptr sret([16 x i8]) align 16` while passing the input as direct `i128`, whereas `extern "C"` lowers to `i128 (i128)`.
3. **Four-Way `HfaF32x4` Split in `extern "C"` vs. Universal `sret` in `extern "Rust"`:** Under `extern "C"`, the `16`-byte homogeneous 4-float aggregate `HfaF32x4` lowers to four completely different LLVM IR shapes across the `5` ABI families: `[4 x float]` on AAPCS64 (`s0`–`s3`), **`{ double, double }`** on SysV64 (because `rustc`'s `x86_64` ABI classifier represents each `SSE`-class eightbyte as `Reg::f64()`, packing two `f32`s per `double` in `xmm0`/`xmm1` rather than emitting `{ <2 x float>, <2 x float> }`), `void (ptr sret([16 x i8]) align 4, ptr align 4)` on Win64, and `void (ptr sret([16 x i8]) align 4, ptr byval([16 x i8]) align 4)` on `i686`. Under `extern "Rust"`, all `9` targets agree on `void (ptr sret([16 x i8]) align 4, ptr align 4)`.
4. **OS-Sensitive `i686` 8-Byte Returns and `efiapi` Target Interaction:** On `i686-pc-windows-msvc`, 8-byte `extern "C"` structs (`*const [u8]`, `MixedIntFloat`) return in `eax:edx` (`i64 (ptr byval([8 x i8]) align 4)`), whereas `i686-unknown-linux-gnu` returns them via hidden `sret` (`void (ptr sret([8 x i8]) align 4, ptr byval([8 x i8]) align 4)`). Notice also that `i686-pc-windows-msvc` aligns `PairU64` (`u64, u64`) `sret` to `align 8` (natural 8-byte `u64` alignment on MSVC) versus `align 4` on `i686-unknown-linux-gnu` (SysV i386 4-byte `u64` ABI alignment), AND that `abi_efiapi_pair` uses `win64cc` with `{ i64, i64 }` on `x86_64-unknown-linux-gnu` versus `win64cc` with `sret + ptr` on `x86_64-pc-windows-msvc`—demonstrating that `efiapi` lowering cannot be modeled independently of the target triple's OS!

### 4. Design Requirements for a Version-Pinned, Release-Fingerprinted Lean `FnAbi` Classifier

`Basis: derived + source (joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613 trusted/rustc-capture/src/driver.rs:24,45-47 and trusted/lean/Trusted/MirAst.lean, combined with Sections 1–3)`

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/rustc-capture/src/driver.rs:24,45-47` already enforces an exact fail-closed compiler-version guard (`if rustc_interface::util::rustc_version_str() != Some(COMPILER_VERSION) { early_dcx.early_fatal(...); }`) against its pinned `rustc` commit (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), while `trusted/lean/Trusted/MirAst.lean` carries explicit `.unsupported` fail-closed variants for unmodeled MIR constructs. Extending a verified compiler or binary-correspondence backend from `Runtime(PostCleanup)` MIR down to machine calling conventions (`FnAbi` -> physical registers/stack slots and linker symbols) requires **five strict architectural invariants** dictated directly by the empirical drift matrix above:

1. **Explicit `CompilerAbiEpoch` Parameterization (Never an Unversioned Target Classifier):**
   Because `1.99.1 -> 1.100.0` broke `30` x86/x86_64 `extern "Rust"` SIMD signatures while leaving `aarch64` unchanged, and `1.100.0 -> 1.102.0-nightly` broke `15` `aarch64` SIMD signatures, `6` Win64 `extern "C"` ZST signatures, and `4` `x86_64` `vectorcall` `.o` linker symbols, a Lean `FnAbi` classifier of type `TargetSpec -> FnSig -> FnAbi` is **unsound across `rustc` releases**. The classifier signature must be explicitly indexed by a pinned release epoch:
   ```text
   classifyFnAbi :
     (epoch    : CompilerAbiEpoch)    -- pinned 40-hex rustc commit SHA + ABI rule flags
     (target   : TargetAbiSpec)       -- arch, os, env, pointer_width, rustc_abi, base_features
     (fnFeats  : List TargetFeature)  -- per-function #[target_feature] (e.g., avx, avx512f)
     (conv     : CanonAbi)            -- Rust, C, CUnwind, System, EfiApi, SysV64, Win64, Vectorcall, ...
     (sig      : List LayoutDesc × LayoutDesc)
     -> Except AbiUnsupported (FnAbi × LinkerSymbolRule)
   ```
   Unrecognized compiler SHAs must return `.error .unknownCompilerEpoch` fail-closed (never silently falling back to a previous epoch's rules). Inside `CompilerAbiEpoch`, the four observed rule toggles map cleanly to explicit version-indexed boolean flags (`rustSimdRegX86Le128`, `rustSimdRegAArch64Le128`, `win64IndirectZstRequiresReprC`, `msvcByteCountPreLowering`).
2. **Mandatory Layout Metadata (`repr_c : Bool`, `is_simd : Bool`, `backend_repr`, `unadjusted_align`):**
   Commit `916dda0c` proves that byte size, alignment, and field list alone **cannot** determine Win64 `extern "C"` ABI lowering for ZSTs: `struct ZstStruct;` (`repr_c = false`, lowered to `PassMode::Ignore`) and `#[repr(C)] struct CZst;` (`repr_c = true`, lowered to `PassMode::Indirect`) have identical size (`0`), alignment (`1`), and empty field lists! Similarly, `#[repr(transparent)]` wrapping a `#[repr(C)]` ZST inherits `repr_c = true`, and `#[repr(simd)]` types require `is_simd = true` alongside element type and lane count to separate `SimdF32x4` (`<4 x float>`) from `HfaF32x4` (`[4 x float]` / `{ double, double }` / `sret`). The MIR-to-ABI bridge must therefore export `LayoutData.repr_c` and `BackendRepr::SimdVector` explicitly from `rustc_abi`, never reconstructing them heuristically from struct fields.
3. **Pre-Lowering Rust Layouts for Linker-Symbol Decoration:**
   Commit `d11b3f4d6` proves that `vectorcall` (`@@N` on all `x86`/`x86_64` OSes including Linux ELF and macOS Mach-O) and 32-bit Windows `stdcall`/`fastcall`/`system` (`@N`) byte counts in `1.102.0-nightly+` depend on **original pre-lowering Rust argument layouts** (`arg.layout.size.bytes().next_multiple_of(pointer_bytes)`), NOT post-lowering indirect pointer sizes (`abi_vec_hfa4`: `24` vs. `16` on `x86_64`). A Lean `FnAbi` model that discards original argument sizes after marking an argument `PassMode::Indirect` cannot compute `LinkerSymbolRule` accurately.
4. **Two-Layer Cross-Release ABI Fingerprint (Canonical `FnAbi` Tuple + Final Linker Symbol):**
   Neither LLVM IR headers alone nor compiled `.o` symbol tables alone provide a sound cross-release ABI fingerprint:
   - *LLVM IR alone* flags **`23 / 833` false-positive binary breaks** (`1.100.0 -> 1.102.0-nightly` IR-only `\01...@N`/`@@N` migrations whose `.o` symbols are bit-for-bit identical) and depends on compiler-internal lowering artifacts such as `MergeFunctions` aliases at `-O2`.
   - *Object `.o` symbol tables alone* miss **`51 / 833` true binary calling-convention breaks** (`45` SIMD register flips + `6` Win64 ZST register shifts) whose linker symbol names never changed.
   - A complete, zero-false-negative fingerprint for cross-crate `.rlib` / verified-object compatibility must hash the pair `(canonical_fn_abi_tuple, final_linker_symbol)`, where `canonical_fn_abi_tuple` encodes `(compiler_sha, target_triple, conv, ret_pass_mode_and_cast, arg_pass_modes_and_casts)` and `final_linker_symbol` is the post-decoration object-file symbol name (`llvm-nm` ground truth).
5. **Fail-Closed Upgrade Gate on Every `rustc` Pin Bump:**
   Whenever a verified toolchain advances its pinned `rustc` commit (analogous to bumping `COMPILER_VERSION` in `trusted/rustc-capture/src/driver.rs`), CI must execute the `9`-target `#![no_core]` matrix at `-C opt-level=0` for **both** `--emit=llvm-ir` and `--emit=obj` (`llvm-nm`), diffing every `(target, fn)` pair against the Lean `classifyFnAbi` oracle for the new `CompilerAbiEpoch`. Any single mismatch across any of the `833+` pairs blocks promotion until the Lean epoch table and its correspondence proof are updated.

## Boundaries

1. **Non-x86 / Non-AArch64 Architectures (`not examined`):** The `9`-target matrix covers `x86_64`, `aarch64`, and `i686` across Linux, macOS, Windows MSVC, and Windows GNU. Other targets (`riscv64`, `s390x`, `powerpc64`, `wasm32`, `arm`, `aarch64_be`, `arm64ec`, and softfloat targets such as `aarch64-unknown-none-softfloat` or `x86_64-unknown-none`) were not compiled in this matrix; upstream commit logs between `1.99.1` and `1.102.0-nightly` show separate SPARC and PowerPC `Complex` ABI changes and `aarch64_be` unit-array layout fixes that are not exercised here.
2. **`#[repr(C)]` ZST Execution on Win64 (`not examined` dynamically; `source`-verified only):** All three ZSTs in the compiled matrix (`()`, `ZstStruct`, `ZstSingleEnum`) are non-`#[repr(C)]`. Retention of indirect `ptr align 1` passing on Win64 for `#[repr(C)]` ZST structs and `#[repr(transparent)]` wrappers around `#[repr(C)]` ZSTs in `1.102.0-nightly` is established directly from `rust-lang/rust` commit `916dda0c26e7736748e2ef8233f1fd1477e1be1e` (`compiler/rustc_abi/src/layout.rs:505-507` and `compiler/rustc_target/src/callconv/x86_win64.rs:52-68`), not executed as a fourth ZST probe in `support/e2_6_9target_3release_abi_matrix.json`.
3. **Excluded Calling Conventions and Scalar Types (`not examined`):** C-variadic functions (`extern "C" fn(..., ...)`), `extern "rust-call"`, `extern "C-cmse-nonsecure-call"`, interrupt/GPU conventions, `#[track_caller]` implicit caller-location arguments, `f16` / `f128` / `x87_f80` scalars, and `#[repr(C, packed)]` aggregates passed under `vectorcall` were not included in the `99`-function probe suite.
4. **LLVM Backend Physical Register Assignment (`not examined`):** Primary measurements stop at `-C opt-level=0` LLVM IR (`--emit=llvm-ir`) and compiled object symbol tables (`--emit=obj` + `llvm-nm`). Although LLVM IR `abi_shape` plus `.o` symbols fully capture `rustc`'s `rustc_target::callconv` and `declare_rust_fn` decisions, they do not directly verify LLVM `SelectionDAG`/`GlobalISel` register-assignment faithfulness (e.g., whether LLVM lowers `<4 x i8>` on `i686` identically across `LLVM 23.1.1` vs. `LLVM 23.1.5` in generated machine code).
5. **Optimization-Level Attribute Churn (`known not to apply` at `-O2`/`-O3`):** Observing `0 / 833` optimization-attribute-only diffs across `1.99.1 -> 1.100.0 -> 1.102.0-nightly` holds strictly at `-C opt-level=0`. Higher optimization levels (`-C opt-level=2`/`3`) invoke LLVM function-attribute inference and `MergeFunctions`, reintroducing alias folding and attribute churn (`captures(...)`, `dead_on_unwind`, `initializes(...)`) not present in this `-O0` dataset.
6. **Root Cause of the `1.102.0-nightly` `#![no_core]` `fully_perform` ICE (`unknown`):** Execution confirms the exact ICE location (`compiler/rustc_trait_selection/src/traits/query/type_op/custom.rs:199:26`), exit code (`101`), affected type (`&'static [u8]` under minimal five-trait `#![no_core]`), and unaffected releases (`1.99.1`, `1.100.0`), but determining which missing optional lang item or trait-solver query caused the delayed bug without a debug-backtrace build of `rustc` remains `unknown`.
7. **Generalization Beyond Examined Releases (`known not to apply`):** Zero drift on an architecture in one release step (`aarch64` had `0 / 87` drifts in `1.99.1 -> 1.100.0`) does not imply stability in the next release (`aarch64` jumped to `5 / 87` breaks in `1.100.0 -> 1.102.0-nightly`). Cross-release ABI stability cannot be extrapolated across untested `rustc` commits.

## Evidence

| Artifact / Upstream Source | Immutable Pin / Coordinates | Evidence Role & What It Establishes |
| :--- | :--- | :--- |
| `support/e2_6_9target_3release_abi_matrix.py` | Preserved in package (`support/`) | **Execution script:** Self-contained `#![no_core]` `99`-function Rust ABI probe generator, `9`-target × `3`-release `rustc -C opt-level=0 --emit=llvm-ir` driver, and `normalize_llvm_def_header` extractor. |
| `support/e2_6_9target_3release_abi_matrix.json` | Preserved in package (`support/`), observed `2026-11-20` | **Execution data:** Complete `2,499`-instance compile status, exact `rustc -vV` metadata, all `30` `1.99.1 -> 1.100.0` drift records, all `48` `1.100.0 -> 1.102.0-nightly` drift records, `0` opt-attr-only churn counters, and full `9`-target × `3`-release `spotlights` dictionary (`13` spotlight functions). |
| `rust-lang/rust` (`1.99.1`) | `58cf8f9c35b355199727627d07ae34a4e2846d67` (`LLVM 23.1.1`) | **Execution subject:** Baseline compiler (`833` emitted functions across `9` targets; clean exit `0` on `#![no_core]` `&'static [u8]`). |
| `rust-lang/rust` (`1.100.0`) | `0ef1bc386059596dada8fb65b50425aab2ea637a` (`LLVM 23.1.5`) | **Execution subject:** Intermediate release (`30 / 833` x86/x86_64 SIMD breaks; `0 / 261` on `aarch64`; clean exit `0` on `#![no_core]` `&'static [u8]`; `--emit=obj` + `llvm-nm` `.o` symbol baseline). |
| `rust-lang/rust` (`1.102.0-nightly`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`LLVM 23.1.5`) | **Execution subject:** Nightly compiler (`48 / 833` IR drifts vs. `1.100.0`; `25 / 833` binary/linker breaks; `fully_perform` ICE at `compiler/rustc_trait_selection/src/traits/query/type_op/custom.rs:199:26` on `#![no_core]` `&'static [u8]`). |
| `rust-lang/rust` D1 commit | `429c1c18ca616ec5a097019c6071dc8ca75585be` (merge `498b89dd40af107a23c13a009345a0dea224248c`), `compiler/rustc_target/src/callconv/mod.rs` | **Source:** Enables `<= 128`-bit `extern "Rust"` SIMD register passing on SSE2-requiring `x86` and non-softfloat `x86_64` targets. |
| `rust-lang/rust` D2 commit | `a654a240456566a313e53698f42c70ad7366676d` (merge `e3c3417ff6499548c5ab52767489ab262f9a2ac0`), `compiler/rustc_target/src/callconv/mod.rs:833-839` | **Source:** Extends `<= 128`-bit `extern "Rust"` SIMD register passing to non-softfloat `Arch::AArch64` (baseline NEON). |
| `rust-lang/rust` D3 commit | `916dda0c26e7736748e2ef8233f1fd1477e1be1e`, `compiler/rustc_abi/src/layout.rs:198-525` & `compiler/rustc_target/src/callconv/x86_win64.rs:44-68` | **Source:** Adds `LayoutData.repr_c` and restricts Win64 indirect ZST passing to `#[repr(C)]` ZSTs (making `()` and `repr(Rust)` ZSTs `PassMode::Ignore`). |
| `rust-lang/rust` D4 commit | `d11b3f4d61c50f4149ea34a89302cf24a0c52b86` (merge `62746359572280748adec7b4add65f0a1c26d1a9`), `compiler/rustc_codegen_llvm/src/declare.rs:169-185` & `compiler/rustc_codegen_ssa/src/common.rs:179-225` | **Source:** Moves `\x01`-prefixed MSVC symbol byte-count decoration into `declare_rust_fn` using `windows_calling_convention_name` over pre-lowering `ArgAbi` layouts. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/rustc-capture/src/driver.rs:24,45-47` & `trusted/lean/Trusted/MirAst.lean` | **Source:** Existing fail-closed compiler-version pinning pattern (`COMPILER_VERSION` pinned to `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and structural `MirAst` fail-closed design informing Section 4. |
| Companion `.o` `llvm-nm` probe | Executed `2026-11-20` on `rustc +1.100.0` vs. `+nightly` (`--emit=obj -C opt-level=0`, all `6` `x86`/`x86_64` targets) | **Execution:** Separates the `4` genuine `.o` linker-symbol breaks (`abi_vec_hfa4@@16 -> abi_vec_hfa4@@24` on all `4` `x86_64` targets) from the `23` `.o`-invariant IR-only decoration migrations. |

## Revalidation

1. **Re-run the full `9`-target × `3`-release LLVM IR differential matrix (takes ~5–10 seconds with `1.99.1`, `1.100.0`, and `nightly` installed via `rustup`, no cross-target `rust-std` components required):**
   ```bash
   python3 support/e2_6_9target_3release_abi_matrix.py --out /tmp/abi_matrix_check.json
   diff -u support/e2_6_9target_3release_abi_matrix.json /tmp/abi_matrix_check.json
   ```
   To evaluate a newer `rustc` release (e.g., `1.101.0` or a newer `nightly`), append `(label, "+<toolchain>")` to `TOOLCHAINS` and check whether `true_abi_drift_*` introduces any unmodeled `(target, fn)` pair.
2. **Disambiguate IR symbol migrations from `.o` linker-symbol breaks (`--emit=obj` + `llvm-nm`):**
   Extract `suite_src` from `support/e2_6_9target_3release_abi_matrix.py` (`build_rust_suite()[0]`) into `/tmp/abi_suite.rs`, compile with:
   ```bash
   for tc in +1.100.0 +nightly; do
     for tgt in x86_64-unknown-linux-gnu x86_64-apple-darwin x86_64-pc-windows-msvc x86_64-pc-windows-gnu i686-unknown-linux-gnu i686-pc-windows-msvc; do
       RUSTC_BOOTSTRAP=1 RUSTC_ICE=0 rustc "$tc" --target "$tgt" -C opt-level=0 --emit=obj /tmp/abi_suite.rs -o "/tmp/${tc}_${tgt}.o"
       llvm-nm --defined-only -g "/tmp/${tc}_${tgt}.o" | grep -E 'abi_(vec|stdcall|fastcall|system)_'
     done
   done
   ```
   Confirm `abi_vec_hfa4@@16` (`1.100.0`) vs. `abi_vec_hfa4@@24` (`1.102.0-nightly`) across all `4` `x86_64` targets and identical `.o` symbols on the remaining `23` decorated pairs.
3. **Check whether the `#![no_core]` `&'static [u8]` `fully_perform` ICE persists on newer nightlies:**
   Compile a minimal file containing `#![crate_type = "lib"] #![feature(no_core, lang_items, auto_traits)] #![no_core]`, the five lang-item traits (`pointee_sized`, `meta_sized`, `sized`, `copy`, `freeze`), and `#[no_mangle] pub fn p(x: &'static [u8]) -> &'static [u8] { x }` with `RUSTC_BOOTSTRAP=1 RUSTC_ICE=0 rustc +<toolchain> --target x86_64-unknown-linux-gnu -C opt-level=0 --emit=llvm-ir`.
4. **Source-level ABI drift pre-check on any candidate `rustc` upgrade (`OLD_SHA..NEW_SHA`):**
   Diff the four upstream ABI-controlling directories in `rust-lang/rust` before updating a Lean `CompilerAbiEpoch`:
   ```bash
   git log --oneline <OLD_SHA>..<NEW_SHA> -- \
     compiler/rustc_target/src/callconv/ \
     compiler/rustc_abi/src/layout.rs \
     compiler/rustc_codegen_llvm/src/declare.rs \
     compiler/rustc_codegen_ssa/src/common.rs
   ```
