# `rustc` Core SIMD Intrinsics: `simd_masked_load` Alignment Polarity, `{-1, 0}` Mask Non-Confluence, `simd_bitmask` Endian Reversal, `simd_as` vs. `simd_cast`, and the `#![forbid(unsafe_code)]` MCP#838 MIR Validator ICE

## Summary

Rust's core SIMD intrinsics (`core::intrinsics::simd`) and `#[repr(simd)]` aggregates enforce five operational and compiler-pipeline invariants that routinely violate scalar Rust intuition and must be encoded explicitly in any sound MIR semantics, translation validator, or LLVM lowering model:

1. **Unconditional Base-Pointer `SimdAlign` vs. Per-Active-Lane Dereferenceability in `simd_masked_load` / `simd_masked_store`:** In `rustc_const_eval` (`simd.rs:674–678, 839–852` at `342d74463`), `lean-miri` (`IntrinsicSimd.lean:157–167, 444–445`), and `rustc_codegen_llvm` (`intrinsic.rs:2619–2630, 2711–2715`), `ptr` is checked against `SimdAlign` (`Unaligned = 1`, `Element = align_of::<T>()`, `Vector = align_of::<Simd<T, N>>()`) **unconditionally before inspecting any mask lane**, and LLVM attaches an unconditional `align N` call-site attribute to `Argument(0)` of `@llvm.masked.load` / `@llvm.masked.store`. Consequently, under an all-zero mask `[0; 4]`, `null()` passes `SimdAlign::Vector` (`0 % 16 == 0`), `without_provenance(1)` passes `SimdAlign::Unaligned` (`1 % 1 == 0`) yet triggers immediate Miri/LLVM alignment UB (`rc = 1`) under `SimdAlign::Element` (`1 % 4 != 0`), and `without_provenance(8)` under `SimdAlign::Vector` on `U32x4` triggers UB on `x86_64` (`align_of::<U32x4>() == 16`, `rc = 1`) while **passing** on `s390x` (`v128:64` datalayout yields `align_of::<U32x4>() == 8`, `rc = 0`). Conversely, once base alignment holds, lane memory addresses use wrapping offset arithmetic (`ptr.wrapping_offset(elem_size * i)`) and dereference memory **strictly** on active `!0` lanes, permitting partial-allocation `[u32; 2]` tail loads (`mask = [-1, -1, 0, 0] -> [10, 20, 99, 99]`) while faulting on any active out-of-bounds lane (`mask = [-1, -1, -1, 0]`).
2. **Non-`{0, -1}` Mask-Lane UB (`+1` Divergence Across Backends & Consumers, Plus an `-O0` IR Reading Trap):** `rustc_const_eval::simd_element_to_bool` (`simd.rs:873–885` at `342d74463`; `889–901` at `14210df0e`) converts every mask lane via signed `to_int(size)` and rejects any value outside `{0, -1}` (`{0, 2^w - 1}`) as immediate UB (`each element of a SIMD mask must be all-0-bits or all-1-bits`). Primary-source inspection across all three `rustc` codegen backends and `core::simd` explains why `{0, 2^w - 1}` is uniquely required—and corrects a common misreading of unoptimized LLVM IR:
   - In `rustc_codegen_llvm`, **both** `simd_masked_load` (`intrinsic.rs:2696`) and `simd_bitmask` (`intrinsic.rs:2405`) lower fixed-width masks through the **same** helper `vector_mask_to_bitmask` (`intrinsic.rs:2072–2084`), which extracts the **MSB** via two unoptimized instructions (`%1 = lshr <N x iW> %0, splat (iW W-1)` followed by `%2 = trunc <N x iW> %1 to <N x i1>`) that LLVM InstCombine folds at `-O` into `%1 = icmp slt <N x iW> %0, zeroinitializer`. Reading the `-O0` `trunc <8 x i32> %1 to <8 x i1>` line without its producer `%1 = lshr` falsely suggests raw LSB truncation, whereas native `x86_64` execution confirms `simd_bitmask(I32x8([1, 0, -1, 0, 0, 0, 0, 0]))` returns `0x04` (MSB: `+1 -> 0`, `-1 -> 1`) and `simd_masked_load` with `[1, 0, 0, 0]` returns passthrough `[99, 99, 99, 99]`.
   - Genuine **MSB vs. LSB vs. nonzero vs. bitwise** non-confluence on `+1` occurs across real consumers: `core::simd::Mask::to_array` (`masks.rs:186–189`) extracts the **LSB** (`simd_cast::<_, i8> & 1`, returning `[1, 0, 1, 0, 0, 0, 0, 0]` on native `x86_64` for the identical `[1, 0, -1, ...]` vector); `rustc_codegen_llvm` scalable-vector `simd_select` (`intrinsic.rs:2375`) emits bare `trunc` (**LSB**); `rustc_codegen_cranelift` mixes **MSB** (`simd_bitmask`, `ushr_imm_u(..., bits - 1)`, `simd.rs:942–943`) with **nonzero** (`simd_masked_load`, `brif(mask_lane, ...)`, `simd.rs:1137`); and `rustc_codegen_gcc` mixes **MSB** (`simd_bitmask`, `simd.rs:812–813`) with **nonzero** (`simd_masked_load`, `ComparisonOp::NotEquals(mask, zero)`, `simd.rs:1630`). As mechanized in `bit_uniform_implies_canonical`, `{0, 2^w - 1}` is the **unique** fixed point on which MSB, LSB, nonzero, and bitwise selection agree.
3. **Target-Endian Bit Reversal in `simd_bitmask` (`bitcast <N x i1> to iN`) and Evolution of `x86_64` vs. `s390x` Vector ABI:** Because LLVM defines `bitcast <N x i1> to iN` in target endian order (`e-...` LSB-first on `x86_64`, `E-...` MSB-first on `s390x`), lane `i` maps to bit `i` on little-endian targets and bit `N - 1 - i` on big-endian targets (`simd_bitmask_index`, `simd.rs:856–863`). Live `#![no_core]` strict-provenance Miri execution on `U32x8([!0, 0, !0, 0, 0, 0, 0, 0])` yields `0x05` (`5`) on `x86_64-unknown-linux-gnu` and `0xa0` (`160`) on `s390x-unknown-linux-gnu`, while `simd_select_bitmask(simd_bitmask(m), yes, no)` round-trips identically on both targets. Native `-O` assembly confirms hardware sign-bit packing into opposite bit orders (`packssdw`/`packsswb`/`pmovmskb` on `x86_64` vs. `chsi`/`ipm`/`risbg`/`rosbg` on `s390x`). Between `rustc 1.98.0-nightly` (`14210df0e`) and `rustc 1.102.0-nightly` (`3ef0c22cd`) / `main` (`342d74463`), `adjust_for_rust_abi` (`callconv/mod.rs:791–804, 931–933`) replaced unconditional `spec.simd_types_indirect` with `can_pass_simd_directly`, moving `<= 128`-bit SIMD vectors (`F32x4`, `U8x4`) to `PassMode::Direct` (`<4 x float>`, `<4 x i8>`) on non-softfloat `x86_64` and `aarch64`, while leaving `256`-bit `I32x8` indirect on `x86_64` and **all** SIMD vectors indirect (`sret([4 x i8]) align 4`, `ptr align 8 %x`) on `s390x`.
4. **Total Saturating `simd_as` (`@llvm.fptoui.sat`) vs. Unchecked `simd_cast` (`fptoui` UB/Poison):** On float-to-integer conversions, `simd_as` lowers to `@llvm.fptoui.sat` / `@llvm.fptosi.sat` (`intrinsic.rs:3232–3236`) and `float_to_float_or_int` in `rustc_const_eval` (`simd.rs:531–532`), deterministically mapping `[-5.0, 300.0, NaN, 42.9]` to `[0, 255, 0, 42]` with zero UB. Unchecked `simd_cast` lowers to raw LLVM `fptoui` / `fptosi` (`intrinsic.rs:3230–3231`, returning `poison` out of range) and `float_to_int_checked` in Miri (`simd.rs:534–542`), faulting on both `300.0_f32 -> u8` and `NaN_f32 -> u8` (`rc = 1`) even though native `x86_64` silently returns `[255, 1, 2, 3]` and `[0, 1, 2, 3]`.
5. **Live `#![forbid(unsafe_code)]` MCP#838 MIR Validator ICE (`rc = 101`) Masked by `--emit=metadata`:** Projecting `v.0` on `#[repr(simd)] pub struct U32x4(pub [u32; 4])` inside a crate marked `#![forbid(unsafe_code)]` passes HIR typechecking, borrow checking, and `rustc --crate-type=lib --emit=metadata` (`rc = 0`, matching `cargo check`), then crashes `rustc` during `optimized_mir` (`rc = 101`, even under `-Zmir-opt-level=0`) inside `Validator::run_pass` (`validate.rs:82:25` at `14210df0e`; `validate.rs:81:25` at `3ef0c22cd` and `342d74463`) with `Projecting into SIMD type U32x4 is banned by MCP#838` (`AdtDef::can_project_fields`, `adt.rs:222–226`).
6. **Constructive Lean `v4.34.1` Mechanization (`support/SimdMaskedLoadBitmaskAndMcp838Soundness.lean`):** All five properties and three sharp counterexamples are kernel-checked in `1,440` lines (`499` constants, `18` exported theorems) under `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`, and `0` `._unsafe_rec` constants, using only `{propext, Quot.sound}` and 6 `Init.*` modules within `joshlf/anneal`'s locked Pass-1 foundation (`c131b320e`).

## Applicability

This report characterizes the interaction among seven durable upstream subjects pinned in `REPORT.json`, distinguishing direct live execution from primary-source multi-revision inspection:

| Subject | Pinned Identity | Role in This Investigation | Direct Execution vs. Source Audit |
| :--- | :--- | :--- | :--- |
| `rust` (`main`) | `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (2026-11-22) | Primary source authority for `library/core/src/intrinsics/simd/mod.rs`, `library/portable-simd`, `rustc_const_eval`, `rustc_codegen_{llvm,cranelift,gcc}`, `rustc_mir_transform/src/validate.rs`, `rustc_middle/src/ty/adt.rs`, and `rustc_target/src/callconv/mod.rs`. | Source audit (all files fetched and inspected verbatim at pinned SHA). |
| `rust` (`1.102.0-nightly`) | `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (2026-11-11) | Revision tracking the Rust SIMD ABI shift (`can_pass_simd_directly` in `callconv/mod.rs`), `AdtDef::can_project_fields` refactor, and `validate.rs:81:25` panic site paired with LLVM `23.1.5`. | Source audit (all four core compiler/library files + `callconv/mod.rs` inspected verbatim; no local `1.102.0-nightly` binary installed in this environment). |
| `rust` (`1.98.0-nightly`) | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (2026-05-31) | Installed compiler & Miri runtime (`rustc 1.98.0-nightly`, `miri 0.1.0 (14210df0e2 2026-05-31)`, LLVM `22.1.6`) executing `support/probe_simd_intrinsics_and_mcp838_ice.py` live. | Source audit **plus live execution** (native `x86_64`, strict-provenance Miri SB & TB on `x86_64` LE and `s390x` BE, cross-target LLVM IR at `-Copt-level=0`/`-O`, assembly, and MCP#838 ICE). |
| `anneal` | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Target verification architecture (`trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`, `trusted/lean/Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and vendored `vendor/lean-miri/Miri/Interpreter/IntrinsicSimd.lean`). | Source audit (inspected verbatim at pinned commit). |
| `lean4` (`v4.34.1`) | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | Proof kernel checking `support/SimdMaskedLoadBitmaskAndMcp838Soundness.lean` and verifying `#print axioms` + constant environment metadata. | Live kernel execution (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`). |
| `llvm-project` (`22.1.6`) | `llvm/llvm-project` @ `fc4aad7b5db3fff421df9a9637605b9ca5667881` | LLVM backend embedded in `rustc 1.98.0-nightly` for all observed LLVM IR (`-O0`/`-O`) and `x86_64`/`s390x` assembly outputs in `support/probe_results.json`. | Live execution via `rustc 1.98.0-nightly`. |
| `llvm-project` (`23.1.5`) | `llvm/llvm-project` @ `392dfff97d29b59d77e5cac6d4b6ef2585fe7117` | LLVM backend paired with `rustc 1.102.0-nightly` (`3ef0c22cd`), sharing the identical LLVM IR intrinsics (`@llvm.masked.load`, `@llvm.fptoui.sat`, `bitcast <N x i1> to iN`). | Referenced via `rustc 1.102.0-nightly` codegen source (`intrinsic.rs` emit calls); not executed locally. |

### Shared vs. Version-Specific Behaviors Across Examined `rustc` Revisions

- **Shared identically across `14210df0e` (`1.98.0-nightly`), `3ef0c22cd` (`1.102.0-nightly`), and `342d74463` (`main`):**
  - `SimdAlign::{Unaligned = 0, Element = 1, Vector = 2}` semantics and unconditional `check_simd_ptr_alignment` / LLVM `Argument(0) align N` emission on `simd_masked_load` and `simd_masked_store`.
  - Per-active-lane `wrapping_offset` + `ptr_to_mplace_unaligned` dereferencing (partial-allocation tail loads legal when disabled lanes are `0`).
  - `simd_element_to_bool` strict `{0, -1}` signed `to_int` validity rule and UB message.
  - `rustc_codegen_llvm::vector_mask_to_bitmask` (`lshr (w - 1)` followed by `trunc ... to <N x i1>`, folded to `icmp slt ..., zeroinitializer` by InstCombine) for both `simd_masked_load` and `simd_bitmask`.
  - `simd_bitmask_index` endian reversal (`idx` on `Endian::Little`, `vec_len - 1 - idx` on `Endian::Big`), 64-lane Miri/CTFE ceiling, and `bitcast <N x i1> to iN` lowering.
  - `simd_as` (`@llvm.fptoui.sat` / `float_to_float_or_int`) vs. `simd_cast` (`fptoui` / `float_to_int_checked` UB).
  - MCP#838 MIR validator ICE on `#[repr(simd)]` field projection in `#![forbid(unsafe_code)]` crates.
- **Differing between `14210df0e` (`1.98.0-nightly`) and `3ef0c22cd` (`1.102.0-nightly`) / `342d74463` (`main`):**
  1. **Rust-ABI `<= 128`-bit SIMD calling convention (`compiler/rustc_target/src/callconv/mod.rs`):** At `14210df0e` (`L839–840`), `if spec.simd_types_indirect { arg.make_indirect(); }` passes and returns **all** `#[repr(simd)]` vectors indirectly (`ptr` / `sret`) on both `x86_64` and `s390x`. At `3ef0c22cd` and `342d74463` (`L791–804, 931–933`), `can_pass_simd_directly` passes `<= 128`-bit SIMD vectors directly in registers (`<4 x float>`, `<4 x i8>`) on non-softfloat `x86_64`, non-softfloat `aarch64`, and `x86` (`X86Sse2`), while keeping `> 128`-bit vectors (`I32x8` = 256 bits) indirect on `x86_64` and keeping **all** SIMD vectors indirect (`sret([4 x i8])`, `ptr align 8 %x`) on `s390x` (`_ => false`).
  2. **MCP#838 `validate.rs` panic line and helper factoring:** At `14210df0e`, `Validator::run_pass` fails at `validate.rs:82:25` and `TypeChecker` checks `if adt_def.repr().simd()` inline at `validate.rs:704–711`. At `3ef0c22cd` and `342d74463`, `Validator::run_pass` fails at `validate.rs:81:25` and `TypeChecker` delegates to `if !adt_def.can_project_fields(self.tcx)` (`validate.rs:719–732` calling `compiler/rustc_middle/src/ty/adt.rs:222–226`), extending the identical projection ban to `#[repr(scalable)]` vectors alongside `#[repr(simd)]` and `DynMetadata`.
  3. **Line-number drift in `simd.rs` and `intrinsic.rs`:** Exact line numbers shifted slightly across the three revisions and are recorded per commit in **Findings** and **Evidence**.

**Relationship to Existing Corpus Reports:** Earlier corpus coverage in `core-simd-mask-all-ones-ub-masked-tail-loads-and-lanewise-chunk-algebras` examined `core::simd` mask validity and Pass-1 strip-mining chunk algebras at `rust-lang/rust@8144389c` and `joshlf/anneal@20aa2043` without live Miri or cross-target IR/asm execution. This report extends coverage to `rust-lang/rust@342d74463` / `3ef0c22cd` / `14210df0e` and `joshlf/anneal@c131b320e`, adds live strict-provenance Miri (Stacked Borrows and Tree Borrows) on both `x86_64` (LE) and `s390x` (BE), adds `-O0` vs. `-O` LLVM IR and hardware assembly analysis, documents the `1.98` -> `1.102`/`main` Rust SIMD ABI change, audits `rustc_codegen_cranelift` and `rustc_codegen_gcc` mask lowerings, characterizes the `#![forbid(unsafe_code)]` MCP#838 MIR Validator ICE (including its `--emit=metadata` blind spot), and mechanizes end-to-end refinement and sharpness counterexamples in zero-`Classical.choice` Lean `v4.34.1`.

## Findings

### 1. `simd_masked_load` / `simd_masked_store`: Unconditional Base-Pointer `SimdAlign` vs. Per-Active-Lane Dereferenceability

`Basis: normative + source + execution + derived`

#### 1.1 Intrinsic Specification and Four-Phase Operational Semantics

In `library/core/src/intrinsics/simd/mod.rs` (`342d74463`, lines `408–467`), `SimdAlign`, `simd_masked_load`, and `simd_masked_store` are declared as:

```rust
pub enum SimdAlign {
    /// No alignment requirements on the pointer
    Unaligned = 0,
    /// The pointer must be aligned to the element type of the SIMD vector
    Element = 1,
    /// The pointer must be aligned to the SIMD vector type
    Vector = 2,
}

#[rustc_intrinsic]
#[rustc_nounwind]
pub const unsafe fn simd_masked_load<V, U, T, const ALIGN: SimdAlign>(mask: V, ptr: U, val: T)
-> T;
```

Its `# Safety` contract explicitly separates two requirements (`mod.rs:433–439`):

1. **Unconditional base-pointer alignment:** "`ptr` must be aligned according to the `ALIGN` parameter, see [`SimdAlign`] for details." (No mask qualification.)
2. **Active-lane-only readability:** "Each pointer offset from `ptr` whose corresponding value in `mask` is `!0` must be readable as if by `ptr::read`."
3. **Canonical mask values:** "`mask` must only contain `0` or `!0` values."

In `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` (`342d74463`, lines `663–696` and `839–853`; `14210df0e`, lines `655–688` and `855–869`) and identically in `vendor/lean-miri/Miri/Interpreter/IntrinsicSimd.lean` (`joshlf/anneal@c131b320e`, lines `157–167` and `434–457`), execution proceeds in four ordered phases:

1. **Vector Projection and Length Check (`simd.rs:666–672`):** Project `mask`, `default`, and `dest` as SIMD arrays, read `ptr` as a pointer scalar without dereferencing it, and assert `dest_len == mask_len == default_len`.
2. **Unconditional Base-Pointer Alignment Check (`simd.rs:674–678, 839–852`):** Decode `ALIGN : ty::SimdAlign` and immediately run `check_simd_ptr_alignment(ptr, dest_layout, align)` **before** entering the lane loop:
   - `SimdAlign::Unaligned` returns `interp_ok(())` immediately (effective alignment `1`).
   - `SimdAlign::Element` checks `self.check_ptr_align(ptr, vector_layout.field(self, 0).align)` (element ABI alignment, e.g., `4` bytes for `u32`).
   - `SimdAlign::Vector` checks `self.check_ptr_align(ptr, vector_layout.align)` (vector ABI alignment, which depends on the target's LLVM data layout!).
3. **Mask & Passthrough Immediate Evaluation (`simd.rs:680–685`):** For each lane `i ∈ 0..dest_len`, read `mask[i]` and `default[i]` and validate `mask[i] ∈ {0, -1}` via `simd_element_to_bool`.
4. **Active-Lane-Only Wrapping-Offset Load (`simd.rs:685–694`):** Only when `simd_element_to_bool(mask)?` returns `true` does the interpreter compute `ptr.wrapping_offset(dest.layout.size * i, self)` (wrapping arithmetic, *not* `inbounds` GEP) and read via `self.ptr_to_mplace_unaligned(ptr, dest.layout)`. When `mask[i] == 0`, zero pointer arithmetic and zero memory access occur, and `default[i]` is written to `dest[i]`.

#### 1.2 LLVM IR Lowering: Why Misaligned All-Zero Masks Are LLVM UB

In `compiler/rustc_codegen_llvm/src/intrinsic.rs` (`342d74463`, lines `2619–2630, 2696–2716`; `3ef0c22cd`, lines `2634–2645, 2711–2731`; `14210df0e`, lines `2659–2670, 2736–2761`), `simd_masked_load` lowers to `@llvm.masked.load` with an unconditional call-site alignment attribute on `Argument(0)`:

```rust
fn llvm_alignment<'ll, 'tcx>(
    bx: &mut Builder<'_, 'll, 'tcx>,
    alignment: SimdAlign,
    vector_ty: Ty<'tcx>,
    element_ty: Ty<'tcx>,
) -> u64 {
    match alignment {
        SimdAlign::Unaligned => 1,
        SimdAlign::Element => bx.align_of(element_ty).bytes(),
        SimdAlign::Vector => bx.align_of(vector_ty).bytes(),
    }
}
// ...
let call = bx.call_intrinsic("llvm.masked.load", &[llvm_elem_vec_ty, llvm_pointer],
    &[args[1].immediate(), mask, args[2].immediate()]);
crate::attributes::apply_to_callsite(
    call,
    crate::llvm::AttributePlace::Argument(0),
    &[crate::llvm::CreateAlignmentAttr(bx.llcx, alignment)],
);
```

Live `-O` LLVM IR captured by `support/probe_simd_intrinsics_and_mcp838_ice.py` (`support/probe_results.json`, `rustc 1.98.0-nightly` / LLVM `22.1.6`) confirms the exact attribute across all three `SimdAlign` modes and exposes the target-datalayout dependence of `SimdAlign::Vector`:

| Function | `SimdAlign` | `x86_64-unknown-linux-gnu` (`-O`) | `s390x-unknown-linux-gnu` (`-O`, `v128:64`) |
| :--- | :--- | :--- | :--- |
| `ir_masked_load_unaligned` | `Unaligned` | `@llvm.masked.load.v4i32.p0(ptr align 1 %p, <4 x i1> %2, <4 x i32> %1)` | `@llvm.masked.load.v4i32.p0(ptr align 1 %p, <4 x i1> %2, <4 x i32> %1)` |
| `ir_masked_load_elem` | `Element` | `@llvm.masked.load.v4i32.p0(ptr align 4 %p, <4 x i1> %2, <4 x i32> %1)` | `@llvm.masked.load.v4i32.p0(ptr align 4 %p, <4 x i1> %2, <4 x i32> %1)` |
| `ir_masked_load_vec` | `Vector` | `@llvm.masked.load.v4i32.p0(ptr align 16 %p, <4 x i1> %2, <4 x i32> %1)` | `@llvm.masked.load.v4i32.p0(ptr align 8 %p, <4 x i1> %2, <4 x i32> %1)` |

Because LLVM's `align N` parameter attribute asserts that `ptr` is a multiple of `N` unconditionally on entry to the call—independent of `<4 x i1> %2`—passing a misaligned pointer even with `<4 x i1> zeroinitializer` produces immediate LLVM `poison`/UB (which LLVM optimizers may exploit to assume lower pointer bits are zero).

#### 1.3 Live Miri & Native Sharpness Matrix (Including the `x86_64` vs. `s390x` `SimdAlign::Vector` Split)

Live execution of `support/probe_simd_intrinsics_and_mcp838_ice.py` on `rustc 1.98.0-nightly` (`14210df0e`) under strict-provenance Miri (`-Zmiri-strict-provenance`, both default Stacked Borrows and `-Zmiri-tree-borrows`) versus native `x86_64` `-O` proves every boundary empirically:

| Test Case | Pointer & Allocation | Mask | `SimdAlign` | Miri `x86_64` (SB / TB) | Miri `s390x` (SB / TB) | Native `x86_64` `-O` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| Partial-allocation tail load | `[10u32, 20].as_ptr()` (8 B alloc) | `[-1, -1, 0, 0]` | `Element` (`4`) | **PASS** (`[10, 20, 99, 99]`) | **PASS** (`[10, 20, 99, 99]`) | `rc = 0`: `[10, 20, 99, 99]` |
| Null pointer, all-zero mask | `without_provenance(0)` | `[0, 0, 0, 0]` | `Vector` | **PASS** (`[77, 77, 77, 77]`) | **PASS** (`[77, 77, 77, 77]`) | `rc = 0`: `[77, 77, 77, 77]` |
| Misaligned `1usize`, all-zero | `without_provenance(1)` | `[0, 0, 0, 0]` | `Unaligned` (`1`) | **PASS** (`[55, 55, 55, 55]`) | **PASS** (`[55, 55, 55, 55]`) | `rc = 0`: `[55, 55, 55, 55]` |
| Misaligned `1usize`, all-zero | `without_provenance(1)` | `[0, 0, 0, 0]` | `Element` (`4`) | **UB** (`rc = 1`: `alignment 1, but alignment 4 is required`) | — | `rc = 0`: `[0, 0, 0, 0]` (silent UB) |
| **Target split:** `8usize`, all-zero | `without_provenance(8)` | `[0, 0, 0, 0]` | `Vector` (`16` vs `8`) | **UB** (`rc = 1`: `alignment 8, but alignment 16 is required`) | **PASS** (`rc = 0`, 0 warnings!) | `rc = 0`: `ALIGN_OF_U32X4=16 VAL=[33, 33, 33, 33]` |
| Active OOB lane 2 on len-2 slice | `[10u32, 20].as_ptr()` (8 B alloc) | `[-1, -1, -1, 0]` | `Element` (`4`) | **UB** (`rc = 1`: `attempting to access 4 bytes, but got alloc19+0x8 ... size 8 bytes`) | — | `rc = 0`: `OOB_LANE0_1=[10, 20]` (silent OOB read) |

**Upstream `core::simd` Safety-Doc Gap Preserved at `342d74463`:** In `library/portable-simd/crates/core_simd/src/vector.rs` (`342d74463`, lines `441–464` and `701–719`), `Simd::load_select_ptr` and `Simd::store_select_ptr` delegate directly to `simd_masked_load` / `simd_masked_store` with `{ SimdAlign::Element }`, yet their `# Safety` comments still state only that *"Enabled `ptr` elements must be safe to read as if by `core::ptr::read`"* / *"each enabled element must satisfy the same conditions as `core::ptr::write`"*. That doc contract omits the unconditional `ptr.addr() % align_of::<T>() == 0` precondition enforced by Miri and LLVM even when `enable == Mask::splat(false)`. By contrast, safe `Simd::load_select(slice: &[T], ...)` (`vector.rs:414–419`) is sound even on `&[]` because valid slices always carry an `align_of::<T>()`-aligned base pointer.

---

### 2. Non-`{0, -1}` Mask-Lane UB: MSB vs. LSB vs. Nonzero Non-Confluence Across Backends and the `-O0` IR Reading Trap

`Basis: normative + source + execution + derived`

#### 2.1 `rustc_const_eval` Strict `{0, -1}` Invariant

In `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` (`342d74463`, lines `873–885`; identical at `14210df0e`, lines `889–901`), every mask-consuming SIMD intrinsic (`simd_reduce_any`, `simd_reduce_all`, `simd_select`, `simd_bitmask`, `simd_gather`, `simd_scatter`, `simd_masked_load`, `simd_masked_store`) validates each lane via:

```rust
fn simd_element_to_bool<Prov: Provenance>(elem: ImmTy<'_, Prov>) -> InterpResult<'_, bool> {
    assert!(
        matches!(elem.layout.ty.kind(), ty::Int(_) | ty::Uint(_)),
        "SIMD mask element type must be an integer, but this is `{}`",
        elem.layout.ty
    );
    let val = elem.to_scalar().to_int(elem.layout.size)?;
    interp_ok(match val {
        0 => false,
        -1 => true,
        _ => throw_ub_format!("each element of a SIMD mask must be all-0-bits or all-1-bits"),
    })
}
```

Crucially, `to_int(elem.layout.size)` sign-extends the lane regardless of whether the mask lane's Rust type is signed (`i32`) or unsigned (`u32`), so at bit width $w \ge 2$, the only admitted bit patterns are `0` (`0x00...00`) and `-1` (`2^w - 1`, `0xFF...FF`). Unsigned `+1` (`0x0000_0001`) triggers immediate UB in Miri on both `simd_masked_load` and `simd_bitmask` (`support/probe_results.json`: `rc = 1`, `error: Undefined Behavior: each element of a SIMD mask must be all-0-bits or all-1-bits`).

#### 2.2 Dissecting `rustc_codegen_llvm` (`-O0` vs. `-O`): Resolving the `lshr` + `trunc` Trap

Direct inspection of `compiler/rustc_codegen_llvm/src/intrinsic.rs` across all three pinned commits (`342d74463:2059–2084`, `3ef0c22cd:2075–2100`, `14210df0e:2094–2119`) reveals an important precision point about LLVM IR lowering. Both `simd_bitmask` (`342d74463:2405`) and `simd_masked_load` (`342d74463:2696`) call the **exact same helper** `vector_mask_to_bitmask`:

```rust
/// The rust simd semantics are that each element should either consist of all ones or all zeroes,
/// but this information is not available to llvm. Truncating the vector effectively uses the lowest bit,
/// but codegen for several targets is better if we consider the highest bit by shifting.
fn vector_mask_to_bitmask<'a, 'll, 'tcx>(
    bx: &mut Builder<'a, 'll, 'tcx>,
    i_xn: Value<'ll>,
    in_elem_bitwidth: u64,
    in_len: u64,
) -> Value<'ll> {
    let shift_idx = bx.cx.const_int(bx.type_ix(in_elem_bitwidth), (in_elem_bitwidth - 1) as _);
    let shift_indices = vec![shift_idx; in_len as _];
    let i_xn_msb = bx.lshr(i_xn, bx.const_vector(shift_indices.as_slice()));
    bx.trunc(i_xn_msb, bx.type_vector(bx.type_i1(), in_len))
}
```

Live LLVM IR emitted by `support/probe_simd_intrinsics_and_mcp838_ice.py` (`rustc 1.98.0-nightly` / LLVM `22.1.6`) confirms what happens before and after LLVM InstCombine:

```llvm
; -C opt-level=0 (pre-InstCombine, identical body on x86_64 and s390x):
define i8 @ir_bitmask(ptr align 32 %m) unnamed_addr #0 {
start:
  %0 = load <8 x i32>, ptr %m, align 32
  %1 = lshr <8 x i32> %0, splat (i32 31)
  %2 = trunc <8 x i32> %1 to <8 x i1>
  %_0 = bitcast <8 x i1> %2 to i8
  ret i8 %_0
}

; -O (post-InstCombine folds `trunc (lshr x, 31) to i1` into `icmp slt x, 0`):
define noundef i8 @ir_bitmask(ptr dead_on_return noalias noundef readonly align 32 captures(none) dereferenceable(32) %m) unnamed_addr #0 {
start:
  %0 = load <8 x i32>, ptr %m, align 32
  %1 = icmp slt <8 x i32> %0, zeroinitializer
  %_0 = bitcast <8 x i1> %1 to i8
  ret i8 %_0
}
```

And `ir_masked_load_elem` emits the **identical** two-instruction sequence at `-C opt-level=0` (`%2 = lshr <4 x i32> %0, splat (i32 31)` -> `%3 = trunc <4 x i32> %2 to <4 x i1>`) and the identical `%2 = icmp slt <4 x i32> %0, zeroinitializer` at `-O`.

**Diagnostic Pitfall Avoided:** Filtering unoptimized LLVM IR for lines matching `trunc ` and `bitcast ` (dropping `%1 = lshr <8 x i32> %0, splat (i32 31)`) leaves `%2 = trunc <8 x i32> %1 to <8 x i1>` looking superficially like a raw LSB truncation. Live native execution on `x86_64` proves otherwise: on `I32x8([1, 0, -1, 0, 0, 0, 0, 0])`, LLVM's `simd_bitmask` returns `0x04` (only lane 2 `-1` is set; lane 0 `+1` has MSB `0` and evaluates to `false`), and `simd_masked_load` on `I32x4([1, 0, 0, 0])` returns passthrough `[99, 99, 99, 99]` (`+1 -> false`).

#### 2.3 Where Real MSB vs. LSB vs. Nonzero vs. Bitwise Divergence Occurs in `rust-lang/rust`

Auditing all three `rustc` backends and `library/portable-simd` at `342d74463` exposes the **actual** multi-consumer non-confluence that forces `{0, -1}` to be the unique valid mask domain:

| Consumer / Lowering Site (`rust-lang/rust@342d74463`) | Exact Operation on Width-$w$ Lane $m$ | $m = 0$ | $m = -1$ ($2^w-1$) | Invalid $m = +1$ (`0x0000_0001`) | Invalid $m = \text{INT\_MIN}$ (`0x8000_0000`) |
| :--- | :--- | :---: | :---: | :---: | :---: |
| `rustc_codegen_llvm` fixed-width `vector_mask_to_bitmask` (`intrinsic.rs:2072–2084`, used by `simd_masked_load`, `simd_bitmask`, fixed `simd_select`, `simd_reduce_{all,any}`) | `trunc(lshr(m, w - 1))` $\equiv$ `icmp slt m, 0` (**MSB**) | `false` | `true` | **`false`** (verified live: `0x04`, `[99; 4]`) | **`true`** |
| `rustc_codegen_llvm` scalable `simd_select` (`intrinsic.rs:2375`) & raw LLVM `trunc <N x iW> to <N x i1>` (`intrinsic.rs:2063`) | `bx.trunc(m, <vscale x N x i1>)` (**LSB**) | `false` | `true` | **`true`** | **`false`** |
| `core::simd::Mask::to_array` (`masks.rs:186–189`) | `simd_cast::<_, i8>(m) & 1` (**LSB**) | `false` | `true` | **`true`** (verified live: `[1,0,1,0,0,0,0,0]`) | **`false`** |
| `rustc_codegen_cranelift` `simd_bitmask` (`cranelift/src/intrinsics/simd.rs:942–943`) | `ushr_imm_u(lane, bits - 1)` (**MSB**) | `false` | `true` | **`false`** | **`true`** |
| `rustc_codegen_cranelift` `simd_masked_load` (`cranelift/src/intrinsics/simd.rs:1137`) | `brif(mask_lane, if_enabled, if_disabled)` (**nonzero `!= 0`**) | `false` | `true` | **`true`** | **`true`** |
| `rustc_codegen_gcc` `simd_bitmask` (`gcc/src/intrinsic/simd.rs:812–813`) | `(elem >> (elem_size - 1)) & 1` (**MSB**) | `false` | `true` | **`false`** | **`true`** |
| `rustc_codegen_gcc` `simd_masked_load` (`gcc/src/intrinsic/simd.rs:1630`) | `ComparisonOp::NotEquals(mask, zero)` (**nonzero `!= 0`**) | `false` | `true` | **`true`** | **`true`** |
| Hardware bitwise blend (NEON `vbsl`, SSE `pand`/`pandn`/`por`) | `(m & yes) \| (~m & no)` (**all $w$ bits**) | `no` | `yes` | **Torn bits** (bit 0 from `yes`, bits `1..w-1` from `no`) | **Torn bits** (MSB from `yes`, bits `0..w-2` from `no`) |

**Live Native Divergence Demonstration:** In `support/probe_results.json` (`non_all_ones_plus1_mask_bitmask_ub_and_lsb_contrast`), evaluating the exact same `black_box(I32x8([1, 0, -1, 0, 0, 0, 0, 0]))` vector on native `x86_64` produces `LLVM_BITMASK_MSB=0x04` (lane 0 = `false`, lane 2 = `true`) under `simd_bitmask` while `simd_and(simd_cast::<_, I8x8>(raw), I8x8([1; 8]))` (`Mask::to_array`'s exact lowering) produces `MASK_TO_ARRAY_LSB=[1, 0, 1, 0, 0, 0, 0, 0]` (lane 0 = `true`, lane 2 = `true`). Meanwhile, `rustc_codegen_cranelift` and `rustc_codegen_gcc` diverge **internally between their own `simd_bitmask` (MSB) and `simd_masked_load` (nonzero) implementations** on `+1`!

**Secondary `rustc_codegen_gcc` Observations (`342d74463`):** Direct source audit of `compiler/rustc_codegen_gcc/src/intrinsic/simd.rs` surfaced two additional backend hazards worth tracking for any cross-backend verification effort: (i) `simd_bitmask` (`L809–817`) shifts lane `i`'s MSB left by `i` unconditionally without checking `target.endian` (ignoring big-endian bit reversal), and (ii) `simd_masked_load` under `#[cfg(feature = "master")]` (`L1627–1635`) constructs `then_val = new_array_access(pointer, i)` unconditionally before `bx.select(mask, then_val, else_val)` and leaves `// FIXME: handle the alignment.` (`L1562`), rather than suppressing inactive-lane memory loads.

---

### 3. `simd_bitmask` Endian Reversal (`bitcast <N x i1> to iN`) and `x86_64` vs. `s390x` ABI Evolution

`Basis: normative + source + execution + derived`

#### 3.1 Target-Endian Bit Ordering in MIR, LLVM IR, and Machine Assembly

In `rustc_const_eval/src/interpret/intrinsics/simd.rs` (`342d74463:457–503, 856–863`; `14210df0e:449–495, 872–879`), `simd_bitmask` and `simd_select_bitmask` compute each lane's bit index via:

```rust
fn simd_bitmask_index(idx: u32, vec_len: u32, endianness: Endian) -> u32 {
    assert!(idx < vec_len);
    match endianness {
        Endian::Little => idx,
        Endian::Big => vec_len - 1 - idx, // reverse order of bits
    }
}
```

Why does Rust's `simd_bitmask` reverse bits on big-endian targets? Because `rustc_codegen_llvm` (`intrinsic.rs:2405–2407` at `342d74463`) lowers `simd_bitmask` directly via LLVM's `bitcast <N x i1> %i1xn to iN` (followed by `zext` to `i8`/`i16`/`i32`/`i64` or an unaligned byte-array store). In LLVM's LangRef, `bitcast` between a vector and an integer is defined as storing the vector to memory and loading the integer—meaning element `0` occupies the lowest-addressed bit, which is the **LSB (bit `0`)** under little-endian data layouts (`e-...`) and the **MSB (bit `N - 1`)** under big-endian data layouts (`E-...`). When `N < 8` (e.g., `N = 4`), `bitcast <4 x i1> to i4` followed by `zext i4 to i8` places the 4 bits in bits `0..3` on both endiannesses, with lane `0` at bit `0` on LE and lane `0` at bit `3` (`4 - 1 - 0`) on BE—which is why `core::simd::Mask::to_bitmask` (`masks.rs:308–321`) first resizes `Mask<T, N>` to $M \in \{8, 16, 32, 64\}$ before calling `simd_bitmask` and applying `uM::reverse_bits()` (`fix_endianness()`) on big-endian targets.

**Live Execution Proof (`support/probe_results.json`):**
1. **Cross-Target Strict-Provenance Miri (`Part A`):** On the identical `#![no_core]` binary with `m8 = U32x8([0xffff_ffff, 0, 0xffff_ffff, 0, 0, 0, 0, 0])` (lanes `0` and `2` active):
   - `--target=x86_64-unknown-linux-gnu` (LE, both SB and TB): `simd_bitmask(m8)` returns **`0x05`** (`0b0000_0101`, bits `0` and `2`), and `simd_select_bitmask(bm, [100..107], [200..207])` returns `[100, 201, 102, 203, 204, 205, 206, 207]`.
   - `--target=s390x-unknown-linux-gnu` (BE, both SB and TB): `simd_bitmask(m8)` returns **`0xa0`** (`0b1010_0000`, bits `7 = 8-1-0` and `5 = 8-1-2`), and `simd_select_bitmask(bm, [100..107], [200..207])` **still** returns the exact same `[100, 201, 102, 203, 204, 205, 206, 207]`!
2. **Cross-Target `-O` Hardware Assembly (`Part C`, LLVM `22.1.6`):**
   - `x86_64-unknown-linux-gnu` (`ir_bitmask`):
     ```asm
     movdqa   (%rdi), %xmm0
     packssdw 16(%rdi), %xmm0
     packsswb %xmm0, %xmm0
     pmovmskb %xmm0, %eax
     retq
     ```
     `pmovmskb` directly gathers the sign bit (MSB) of lanes `0..7` into bits `0..7` of `%eax` (LE order) with zero shift instructions—validating the comment in `intrinsic.rs:2066–2068`.
   - `s390x-unknown-linux-gnu` (`ir_bitmask`, `target-cpu=z10`):
     ```asm
     chsi  4(%r2), 0        ; compare lane 1 against 0 (sign test)
     ipm   %r0
     chsi  0(%r2), 0        ; compare lane 0 against 0
     ipm   %r1
     risbg %r1, %r1, 60, 188, 39  ; lane 0 -> bit 60 (later shifted +4 to bit 56 = u8 MSB!)
     rosbg %r1, %r0, 61, 61, 38   ; lane 1 -> bit 61 (later shifted +4 to bit 57)
     ...
     rosbg %r2, %r0, 32, 59, 4    ; pack lanes 0..3 into bits 56..59 (u8 bits 7..4)
     br    %r14
     ```
     On z/Architecture (64-bit big-endian bit numbering where bit `56` is the MSB of the low byte and bit `63` is the LSB), LLVM lowers `bitcast <8 x i1> (icmp slt %0, 0) to i8` by placing lane `0` (`0(%r2)`) at `u8` bit `7` (z/Arch bit `56`) and lane `7` (`28(%r2)`) at `u8` bit `0` (z/Arch bit `63`), confirming `0xa0` at the machine-instruction level.

#### 3.2 `x86_64` vs. `s390x` Rust-ABI SIMD Calling Convention Shift (`1.98` vs. `1.102`/`main`)

Comparing `compiler/rustc_target/src/callconv/mod.rs` across `14210df0e` (`1.98.0-nightly`), `3ef0c22cd` (`1.102.0-nightly`), and `342d74463` (`main`) explains an important ABI boundary for `#[repr(simd)]` functions using the default Rust ABI:

- **In `rustc 1.98.0-nightly` (`14210df0e`, `callconv/mod.rs:839–840`):** `adjust_for_rust_abi` applied `if spec.simd_types_indirect { arg.make_indirect(); }` to every `BackendRepr::SimdVector` parameter and return value. Accordingly, live IR from `rustc 1.98.0-nightly` (`support/probe_results.json`) emits indirect `sret([4 x i8])` and pointer arguments on **both** `x86_64` (`define void @ir_simd_as(ptr ... sret([4 x i8]) align 4 ... %_0, ptr ... align 16 ... %x)`) and `s390x` (`define void @ir_simd_as(ptr ... sret([4 x i8]) align 4 ... %_0, ptr ... align 8 ... %x)`).
- **In `rustc 1.102.0-nightly` (`3ef0c22cd`) and `main` (`342d74463`, `callconv/mod.rs:791–804, 931–933`):** `adjust_for_rust_abi` introduces `can_pass_simd_directly`:
  ```rust
  let can_pass_simd_directly = |arg: &ArgAbi<'_, Ty>| match &spec.arch {
      Arch::X86 if spec.rustc_abi == Some(RustcAbi::X86Sse2) => arg.layout.size.bits() <= 128,
      Arch::X86_64 if spec.rustc_abi != Some(RustcAbi::Softfloat) => arg.layout.size.bits() <= 128,
      Arch::AArch64 if spec.rustc_abi != Some(RustcAbi::Softfloat) => arg.layout.size.bits() <= 128,
      _ => false,
  };
  // ...
  if spec.simd_types_indirect && !can_pass_simd_directly(arg) {
      arg.make_indirect();
  }
  ```
  Consequently, on `1.102.0-nightly` and `main`, `U8x4` (32-bit) and `F32x4` (128-bit) cross Rust-ABI boundaries **directly in registers** on `x86_64` (`define <4 x i8> @ir_simd_as(<4 x float> %x)`), while `I32x8` (256-bit `> 128`) remains indirect (`ptr align 32 %m`) on `x86_64` and **every** `#[repr(simd)]` vector—including 4-byte `U8x4` and 16-byte `F32x4`—remains indirect (`sret([4 x i8]) align 4`, `ptr align 8 %x`) on `s390x` because baseline `s390x` (`z10`) does not mandate the `vector` target feature in `abi_required_features`.

---

### 4. `simd_as` Saturating (`@llvm.fptoui.sat`) vs. `simd_cast` Unchecked (`fptoui` UB/Poison)

`Basis: normative + source + execution`

In `library/core/src/intrinsics/simd/mod.rs` (`342d74463`, lines `220–236`), `simd_cast` and `simd_as` share identical signatures (`pub const unsafe fn simd_{cast,as}<T, U>(x: T) -> U`) and identical integer/float-to-float semantics, diverging **specifically** on float-to-integer conversions:

| Layer | `simd_as::<F32x4, U8x4>` (Saturating) | `simd_cast::<F32x4, U8x4>` (Unchecked) |
| :--- | :--- | :--- |
| `rustc_const_eval` (`342d74463:531–542`) | `self.float_to_float_or_int(&op, dest.layout)?` (total saturation; `NaN -> 0`, `< 0 -> 0`, `> 255 -> 255`) | `self.float_to_int_checked(&op, dest.layout, Round::TowardZero)?.ok_or_else(\|\| err_ub_format!(...))` |
| `rustc_codegen_llvm` (`342d74463:3229–3237`) | `bx.cast_float_to_int(...)` $\to$ `call <4 x i8> @llvm.fptoui.sat.v4i8.v4f32(<4 x float> %0)` | `bx.fptoui(...)` $\to$ `fptoui <4 x float> %0 to <4 x i8>` (LLVM `poison` if out of `[0, 256)` or `NaN`) |
| `lean-miri` (`IntrinsicSimd.lean:210–219`) | `FloatOps.castFloatToInt` (saturating) | `IntrinsicFloat.toIntegerChecked` $\to$ `ub "simd_cast value cannot be represented"` on `none` |
| Live Miri (`support/probe_results.json`, SB & TB) | `[-5.0, 300.0, qNaN, 42.9]` $\to$ **PASS** (`[0, 255, 0, 42]`) | `[300.0, 1.0, 2.0, 3.0]` $\to$ **UB** (`rc = 1`: `300f32 which cannot be represented in target type u8`); `[NaN, 1.0, 2.0, 3.0]` $\to$ **UB** (`rc = 1`: `NaN_f32 which cannot be represented`) |
| Live native `x86_64` `-O` | `[0, 255, 0, 42]` (`rc = 0`) | `300.0 -> [255, 1, 2, 3]`, `NaN -> [0, 1, 2, 3]` (`rc = 0`, silently masking UB!) |

Live `-O` LLVM IR (`support/probe_results.json`) additionally shows that LLVM annotates `declare <4 x i8> @llvm.fptoui.sat.v4i8.v4f32(<4 x float>) #3` with `nocreateundeforpoison speculatable willreturn memory(none)`, proving `simd_as` cannot manufacture `undef` or `poison` from any finite/infinite/NaN float input, whereas `fptoui` in `ir_simd_cast` carries no such guarantee and turns any lane outside `(-1.0, 256.0)` (truncating toward zero) into `poison`.

---

### 5. Live `#![forbid(unsafe_code)]` MCP#838 MIR Validator ICE (`validate.rs`) and the `--emit=metadata` Blind Spot

`Basis: source + execution + derived`

Consider this 7-line crate containing zero `unsafe` code:

```rust
#![forbid(unsafe_code)]
#![feature(repr_simd)]

#[repr(simd)]
pub struct U32x4(pub [u32; 4]);

pub fn safe_proj_ice(v: U32x4) -> [u32; 4] {
    v.0
}
```

**Why It Compiles Past Typechecking and Crashes `rustc` (`rc = 101`):**
1. HIR typechecking and borrow checking treat `U32x4` as an ordinary tuple struct whose field `0` is `pub [u32; 4]`, so `v.0` requires zero `unsafe` and lowers to a MIR place projection `Place { local: _1, projection: [PlaceElem::Field(0, [u32; 4])] }`.
2. During `rustc --crate-type=lib --emit=metadata` (the compilation mode used by `cargo check` for library crates without codegen), `optimized_mir` is never queried for non-generic, non-`#[inline]` items—so **`rustc --crate-type=lib --emit=metadata` exits with `rc = 0`** (`support/probe_results.json`, `part_d...emit_metadata_only`)!
3. During codegen (`rustc --crate-type=lib`, even with `-Zmir-opt-level=0`), `rustc_monomorphize` queries `optimized_mir`, which executes `rustc_mir_transform::validate::Validator::run_pass` (`validate.rs:80–82` at `342d74463`/`3ef0c22cd`; `81–83` at `14210df0e`). Inside `validate_types`:
   - At `14210df0e` (`validate.rs:704–711`), `TypeChecker` directly checks `if adt_def.repr().simd()` and queues `"Projecting into SIMD type {adt_def:?} is banned by MCP#838"`; `Validator::run_pass` aborts via `cfg_checker.fail(location, msg)` (`span_bug!`) at **`validate.rs:82:25`**.
   - At `3ef0c22cd` and `342d74463` (`validate.rs:719–732`), `TypeChecker` checks `if !adt_def.can_project_fields(self.tcx)` (where `AdtDef::can_project_fields` in `compiler/rustc_middle/src/ty/adt.rs:222–226` returns `!self.repr().simd() && !self.repr().scalable() && !tcx.is_lang_item(self.did(), LangItem::DynMetadata)`), and `Validator::run_pass` aborts at **`validate.rs:81:25`**.

**Consequence for MIR Verifiers and `joshlf/anneal` (`c131b320e`):**
- In `joshlf/anneal@c131b320e`, `Trusted.MirAst.MirTy` (`Trusted/MirAst.lean:312–321`) currently lowers all `#[repr(simd)]` ADTs and `Float` types fail-closed to `MirTy.unsupported`, and `Trusted.MirAst.StatementKind` (`L657–662`) lowers `StatementKind::Intrinsic` to `.unsupported`.
- When Anneal or a verified `rustc` capture pipeline is extended to `#[repr(simd)]` types, the MIR syntax/validator layer **must** mirror MCP#838's invariant: user MIR bodies cannot contain `PlaceElem::Field` projections into `#[repr(simd)]` (or `#[repr(scalable)]`) ADTs; lane access in valid `Runtime(PostCleanup)` MIR happens exclusively through SIMD intrinsics (`simd_extract`, `simd_insert`, `simd_masked_load`, etc.) or `transmute`, whereas CTFE/Miri (`rustc_const_eval`'s `project_to_simd` and `lean-miri`'s `IntrinsicSimd.toRead`/`toWrite` at `IntrinsicSimd.lean:62–69`) project field `0` internally **only** inside the interpreter's own intrinsic handlers.

---

### 6. Kernel-Checked Lean `v4.34.1` Formalization (`support/SimdMaskedLoadBitmaskAndMcp838Soundness.lean`)

`Basis: source + execution + derived`

To provide a reusable, machine-checked specification compatible with `joshlf/anneal`'s Pass-1 trusted-boundary rules (`TrustedBoundary.lean:442–596, 1110–1134, 2164`, `foundation-lock.json` at `c131b320e`), `support/SimdMaskedLoadBitmaskAndMcp838Soundness.lean` (`1,440` lines) mechanizes all core invariants and counterexamples directly over `prelude` plus 6 locked `Init.*` modules (`Init.Core`, `Init.NotationExtra`, `Init.Data.List.Basic`, `Init.Data.Nat.Basic`, `Init.Data.Nat.Div.Basic`, `Init.Data.Option.Basic`). All recursive functions over inductive types are marked `noncomputable def` (preventing Lean 4 from emitting `partial` `*._unsafe_rec` helpers, matching `Trusted/MirAst.lean:75–92`), and all `DecidableEq` instances are written structurally without `deriving`.

| Theorem (`Anneal.Simd.MaskedLoadBitmaskMcp838.*`) | Line | What It Proves | Kernel Axioms |
| :--- | ---: | :--- | :--- |
| `simd_masked_load_refines_llvm_masked_load` | 728 | For any $w \ge 2$, `SimdAlign`, target `(elemAlign, vecAlign)`, `baseAddr`, partial `MemMap`, and lane lists, if MIR `evalSimdMaskedLoadMir` succeeds with `.ok out`, then LLVM `evalLlvmMaskedLoad` (with unconditional `Argument(0)` `align` check and `vector_mask_to_bitmask` MSB lowering) succeeds with the exact same `.ok out`. | `[propext]` |
| `simd_masked_load_inactive_lane_frame` | 754 | Modifying or unmapping every address belonging to inactive (`0`) lanes leaves `evalSimdMaskedLoadMir` completely unchanged (formalizing partial-allocation tail-load framing). | `[propext]` |
| `s390x_align8_vector_safe_x86_ub` | 822 | Concrete `baseAddr = 8`, all-zero mask `[0, 0, 0, 0]`, `SimdAlign::Vector` witness: `.ubAlign` when `vecAlign = 16` (`x86_64`) and `.ok [33, 33, 33, 33]` when `vecAlign = 8` (`s390x` `v128:64`). | `[propext]` |
| `maskMsbLshrTrunc_eq_signCmp` | 364 | For every $w \ge 1$ and $m < 2^w$, `((m / 2^(w-1)) % 2 == 1)` equals `(2^(w-1) <= m)`, proving LLVM InstCombine's rewrite of `trunc (lshr x, w-1) to i1` into `icmp slt x, 0`. | `[propext]` |
| `canonical_mask_unifies_msb_and_lsb` | 421 | Under `IsCanonicalMaskLane w m` ($w \ge 2$, $m \in \{0, 2^w - 1\}$), `maskMsbLshrTrunc`, `maskMsbSignCmp`, `maskLsb`, and `maskNonZero` all agree, and `bitwiseSelectAtBit` selects every bit $j < w$ uniformly from `yes` or `no`. | `[propext]` |
| `bit_uniform_implies_canonical` | 486 | Converse uniqueness: if every bit $j < w$ of $m < 2^w$ equals a single boolean $b$, then $m = 2^w - 1$ (if $b$) or $m = 0$ (if $\neg b$). | `[propext]` |
| `bitAt_packBitmask` / `bitmask_le_be_reversal` | 1132 / 1147 | Exact bit-extraction bijection for `packBitmask` under both `.little` (`i`) and `.big` (`len - 1 - i`), proved constructively via zero-carry multiples (LE) and strict upper bounds (BE). | `[propext, Quot.sound]` |
| `simd_bitmask_select_roundtrip_both_endians` | 1212 | For both `e ∈ {.little, .big}` and any canonical mask `ms` ($w \ge 2$), `selectByBitmask e (packBitmask e (ms.map (maskMsbLshrTrunc w))) yes no = selectByBoolList (ms.map maskLsb) yes no`. | `[propext, Quot.sound]` |
| `bitmask_8lane_le_0x05_be_0xa0` | 1233 | Concrete 8-lane witness: `[true, false, true, false, false, false, false, false]` packs to `5` (`0x05`) under `.little` and `160` (`0xa0`) under `.big`. | `∅` (none) |
| `ce1_plus1_mask_diverges_msb_vs_lsb` | 1280 | Constructive counterexample at $w = 32, m = 1$: `¬ IsCanonicalMaskLane 32 1`, `maskMsbLshrTrunc 32 1 = false`, `maskMsbSignCmp 32 1 = false`, `maskLsb 1 = true`, `maskNonZero 1 = true`. | `[propext]` |
| `ce2_all_zero_mask_misaligned_violates_llvm_align_attr` | 1302 | Constructive counterexample at `baseAddr = 1`, `mask = [0, 0, 0, 0]`, `SimdAlign::Element`: both MIR and LLVM fault `.ubAlign`, while `.unaligned` yields `.ok [55; 4]` and `baseAddr = 0` under `.vector` yields `.ok [77; 4]`. | `[propext]` |
| `ce3_unchecked_simd_cast_oob_poison` | 1313 | Constructive counterexample for `u8` (`maxVal = 255`): `300.0` and `NaN` yield `.poisonOrUb` under `evalSimdCastUnsigned` while saturating to `255` and `0` under `evalSimdAsUnsigned`. | `[propext]` |
| `mcp838_forbids_simd_field_projection` | 1432 | `validateMirPlace isUnsafeFn (.adt .reprSimd innerTy) (.field0 rest) = .iceBannedSimdProjection` for every `isUnsafeFn : Bool` (including `false` / `#![forbid(unsafe_code)]`), while ordinary structs project cleanly. | `[propext]` |

**Machine-Checked Constant & Axiom Audit:** Compiled with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`), followed by a reflection walk over all `499` constants registered in the compiled `.olean`: `BAD_CONSTS = 0` (`0` `*._unsafe_rec`, `0` `isPartial`, `0` `isUnsafe`, `0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`).

## Boundaries

To prevent over-generalization, the following negative-space boundaries apply:

- **Not examined:**
  - **Live binary execution of `rustc 1.102.0-nightly` (`3ef0c22cd`, LLVM `23.1.5`), `rustc_codegen_cranelift`, and `rustc_codegen_gcc`:** Only `rustc 1.98.0-nightly` (`14210df0e`, LLVM `22.1.6`) and its bundled Miri (`0.1.0`) were installed and executed on this host. Findings specific to `3ef0c22cd` and `342d74463` (including `can_pass_simd_directly` register passing on `x86_64`, `AdtDef::can_project_fields`, `validate.rs:81:25`, and Cranelift/GCC backend lowerings) are established by direct **source** inspection rather than live execution of those binaries.
  - **Physical `s390x` hardware execution and `qemu-s390x`:** Big-endian `s390x` behavior was verified by live cross-target Miri interpretation (`--target=s390x-unknown-linux-gnu`), live LLVM IR emission (`-Copt-level=0` and `-O`), and live z/Architecture assembly inspection (`--emit=asm`), not execution on physical IBM Z silicon.
  - **Scalable vector types (`#[repr(scalable)]`, SVE/RVV) and `> 64`-lane `simd_bitmask`:** `rustc_const_eval` (`simd.rs:459–464`) explicitly throws an unsupported error for `bitmask_len > 64`, and scalable vector lowering (`intrinsic.rs:2364–2375`) was inspected only at the `simd_select` bare-`trunc` site.
  - **Multi-byte / overlapping `simd_masked_store` write-ordering and Tree Borrows aliasing under overlapping scatter lanes:** Only `simd_masked_load` was empirically probed and mechanized in Lean; `simd_masked_store` and `simd_gather`/`simd_scatter` were inspected in `rustc_const_eval` and `lean-miri` source only.
  - **Floating-point rounding edge cases near `2^n` boundaries (e.g., `255.99998_f32` vs. `256.0_f32` in `float_to_int_checked`) and `-0.0` / signaling NaN payloads:** The Lean model abstracts IEEE-754 inputs into `FloatLaneClass` partitions (`nan`, `negInf`, `posInf`, `negFinite`, `inRange`, `tooLarge`) rather than formalizing full IEEE-754 binary32 rounding.
  - **Direct import of `joshlf/anneal`'s `Trusted.MirSemantics` inside the standalone Lean proof file:** Because `joshlf/anneal@c131b320e` currently lowers all `#[repr(simd)]` ADTs, `Float` scalars, and `StatementKind::Intrinsic` calls to `.unsupported`, `support/SimdMaskedLoadBitmaskAndMcp838Soundness.lean` is a standalone Pass-1-compatible formalization of the SIMD operational model rather than a proof linked against `Trusted.MirSemantics.evalStep`.

- **Unknown:**
  - Whether upstream `rust-lang/rust` will tighten `Simd::load_select_ptr` / `store_select_ptr` `# Safety` documentation to explicitly require unconditional base-pointer alignment, or alter `Simd::load_select_ptr` to check/branch on all-false masks.
  - Whether upstream `rust-lang/rust` will turn safe `#[repr(simd)]` field projection (`v.0`) into a clean HIR/typeck diagnostic rather than a post-`optimized_mir` `Validator` ICE (`MCP#838`), or deprecate `#[repr(simd)]` tuple structs with `pub` fields altogether.

- **Known not to apply:**
  - **LLVM `simd_bitmask` does NOT use bare LSB `trunc` on fixed-width masks:** Claims that `rustc_codegen_llvm` lowers `simd_masked_load` via MSB (`icmp slt 0`) while lowering `simd_bitmask` via LSB (`trunc <8 x i32> to <8 x i1>`) are **false** for `rustc_codegen_llvm` across all three audited commits (`14210df0e`, `3ef0c22cd`, `342d74463`). Both intrinsics call `vector_mask_to_bitmask` (`lshr (w - 1)` then `trunc`, folded to `icmp slt 0` at `-O`). The actual MSB-vs-LSB/nonzero split lies between `rustc_codegen_llvm` / Cranelift `simd_bitmask` / GCC `simd_bitmask` (**MSB**) and `core::simd::Mask::to_array` / scalable `simd_select` (**LSB**) plus Cranelift & GCC `simd_masked_load` (**nonzero**).
  - **`SimdAlign::Vector` alignment is NOT universally `16` bytes for 128-bit vectors:** Live Miri (`rc = 0` on `s390x` vs. `rc = 1` on `x86_64`) and live LLVM IR (`ptr align 8 %p` on `s390x` vs. `ptr align 16 %p` on `x86_64`) prove that `SimdAlign::Vector` is target-datalayout dependent.
  - **`cargo check` / `--emit=metadata` does NOT catch the MCP#838 SIMD field projection ICE:** Live execution proves `--emit=metadata` exits with `rc = 0` on the exact `#![forbid(unsafe_code)]` crate that crashes `--crate-type=lib` with `rc = 101`.
  - **Passing native `x86_64` execution does NOT imply freedom from SIMD UB:** Every single Part B UB case (misaligned all-zero mask, `+1` mask lane, `300.0` / `NaN` `simd_cast`, and active OOB lane 2) exits with `rc = 0` on native `x86_64` `-O` while failing with `rc = 1` under Miri.

- **Unsupported:**
  - `simd_bitmask` / `simd_select_bitmask` on vectors with `bitmask_len > 64` in `rustc_const_eval` (`simd.rs:460–464`) and `lean-miri` (`IntrinsicSimd.lean:171–174`).
  - `#[repr(simd)]` types, floating-point types, and MIR intrinsics in `joshlf/anneal@c131b320e` (`Trusted/MirAst.lean:308–321, 654–662`), which fail closed as `.unsupported`.
  - Passing `#[repr(simd)]` types across `extern "C"` on baseline `s390x-unknown-linux-gnu` without `-C target-feature=+vector` (rejected at compile time by `rustc` with `requires the vector target feature, which is not enabled`).

- **Stronger conclusions NOT established by this evidence:**
  - The standalone Lean refinement theorem `simd_masked_load_refines_llvm_masked_load` models `evalSimdMaskedLoadMir` and `evalLlvmMaskedLoad` over an abstract partial element memory map `MemMap α` without pointer provenance tags, Stacked/Tree Borrows permission trees, or concurrent/atomic byte tearing; it does **not** prove full LLVM backend miscompilation-freedom or Tree Borrows soundness.
  - Passing strict-provenance Miri under `#![no_core]` confirms operational conformance of the intrinsic rules tested in Parts A–B, not absence of bugs in `core::simd` wrapper APIs outside the inspected lines.

## Evidence

All technical evidence in this report was acquired and verified on `2026-11-22`.

### 1. Primary Upstream Source Citations (Pinned 40-Hex Commits)

| Repository & Commit | File Path | Symbol / Line Range | Fact Established |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `library/core/src/intrinsics/simd/mod.rs` | `220–236`, `408–467`, `623–640` | Signatures & `# Safety` docs of `simd_cast`, `simd_as`, `SimdAlign`, `simd_masked_load`, `simd_masked_store`, `simd_bitmask`, `simd_select`. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `library/portable-simd/crates/core_simd/src/masks.rs` | `175–205`, `302–337` | `Mask::to_array` LSB (`& 1`) lowering, `from_simd_unchecked` `assume`, `to_bitmask` BE `fix_endianness()`. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `library/portable-simd/crates/core_simd/src/vector.rs` | `414–464`, `701–719` | `load_select_ptr` / `store_select_ptr` delegating to `{ SimdAlign::Element }` while `# Safety` mentions only enabled lanes. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` | `445–559`, `663–722`, `839–885` | `simd_select_bitmask`, `simd_bitmask` (64-lane limit), `simd_cast` vs `simd_as`, unconditional `check_simd_ptr_alignment` before lane loop, `simd_bitmask_index` LE/BE reversal, `simd_element_to_bool` `{0, -1}` UB. |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` | `437–551`, `655–714`, `855–901` | Identical semantics at locally executed `1.98.0-nightly` (`simd_bitmask_index` at `872–879`, `simd_element_to_bool` at `889–901`). |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_llvm/src/intrinsic.rs` | `2059–2084`, `2364–2438`, `2619–2717`, `3141–3245` | `vector_mask_to_bitmask` (`lshr`+`trunc`), scalable bare `trunc`, `simd_bitmask` `bitcast <N x i1> to iN`, `llvm_alignment`, `CreateAlignmentAttr` on `Argument(0)`, `simd_as` vs `simd_cast`. |
| `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_codegen_llvm/src/intrinsic.rs` | `2075–2100`, `2406–2457`, `2647–2732` | Confirms `vector_mask_to_bitmask` (`lshr`+`trunc`) is unchanged in `1.102.0-nightly`. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_cranelift/src/intrinsics/simd.rs` | `879–884`, `934–949`, `1107–1144` | Cranelift `simd_bitmask` MSB (`ushr_imm_u`) vs. `simd_masked_load` nonzero (`brif`). |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_gcc/src/intrinsic/simd.rs` | `781–845`, `1553–1638` | GCC `simd_bitmask` MSB (`>> (w-1) & 1`, missing BE reversal) vs. `simd_masked_load` nonzero (`NotEquals`, eager array access). |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_target/src/callconv/mod.rs` | `717–840` | `1.98.0-nightly` unconditional `if spec.simd_types_indirect { arg.make_indirect(); }` (`L839–840`). |
| `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` & `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_target/src/callconv/mod.rs` | `771–804`, `915–934` (`342d74463`); `756+` (`3ef0c22cd`) | `can_pass_simd_directly` enabling direct `<= 128`-bit SIMD ABI on `x86_64`/`aarch64`/`x86` while keeping `s390x` indirect. |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/validate.rs` | `80–83`, `704–711` | `1.98.0-nightly` MCP#838 ICE at `validate.rs:82:25` via `if adt_def.repr().simd()`. |
| `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` & `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_mir_transform/src/validate.rs` & `compiler/rustc_middle/src/ty/adt.rs` | `validate.rs:80–82, 718–732`; `adt.rs:222–226` | `1.102.0-nightly` / `main` MCP#838 ICE at `validate.rs:81:25` via `AdtDef::can_project_fields`. |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`, `trusted/lean/Trusted/MirAst.lean`, `vendor/lean-miri/Miri/Interpreter/IntrinsicSimd.lean` | `TrustedBoundary.lean:442–596, 1110–1134, 2164`; `MirAst.lean:75–92, 312–321, 657–662`; `IntrinsicSimd.lean:75–80, 157–174, 210–219, 346–383, 434–461` | Pass-1 `Init.*` lock, `noncomputable` / zero-`._unsafe_rec` policy, fail-closed `.unsupported` SIMD/float/intrinsic boundary in `MirAst`, and `lean-miri` parity with `rustc_const_eval`. |

### 2. Preserved Package Support Artifacts

1. **`support/probe_simd_intrinsics_and_mcp838_ice.py`:** Self-contained Python 3 standard-library probe invoking the installed `rustc` and `miri` binaries directly (using `#![no_core]` Miri so cross-target `x86_64` and `s390x` interpretation executes offline in `< 6` seconds without building a `std` sysroot) and writing structured JSON output.
2. **`support/probe_results.json`:** Verbatim recorded output from running `python3 support/probe_simd_intrinsics_and_mcp838_ice.py` on `2026-11-22` with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / LLVM `22.1.6` / `miri 0.1.0 (14210df0e2 2026-05-31)` on host `x86_64-unknown-linux-gnu`:
   - Part A native stdout: `PARTIAL=[10, 20, 99, 99] NULL_MASKED=[77, 77, 77, 77] UNALIGN1_MASKED=[55, 55, 55, 55] SAT=[0, 255, 0, 42] BITMASK=0x05 ROUNDTRIP=[100, 201, 102, 203, 204, 205, 206, 207]` (`rc = 0`).
   - Part A strict-provenance Miri exit codes (returning `bm as isize` after verifying all 5 assertions): `x86_64` SB = `5` (`0x05`), TB = `5` (`0x05`); `s390x` SB = `160` (`0xa0`), TB = `160` (`0xa0`).
   - Part B 7-case Miri UB matrix (all 7 cases fail with `rc = 1` on `x86_64` SB & TB with exact verbatim UB diagnostics, while `all_masked_align8_vector_align_target_split` passes with `rc = 0` on `s390x` SB & TB, and all 7 exit `rc = 0` on native `x86_64` `-O`).
   - Part C complete LLVM IR (`-Copt-level=0` and `-O`) for `ir_bitmask`, `ir_simd_as`, `ir_simd_cast`, `ir_masked_load_{unaligned,elem,vec}` plus `-O` assembly of `ir_bitmask` on both `x86_64-unknown-linux-gnu` and `s390x-unknown-linux-gnu`.
   - Part D MCP#838 ICE matrix: `--crate-type=lib` (`rc = 101`, `validate.rs:82:25`), `-Zmir-opt-level=0` (`rc = 101`, `validate.rs:82:25`), and `--emit=metadata` (`rc = 0`, 0 errors).
3. **`support/SimdMaskedLoadBitmaskAndMcp838Soundness.lean`:** Self-contained `1,440`-line Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) proof module verified with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`), `#print axioms` (`∅` / `[propext]` / `[propext, Quot.sound]` across all 18 theorems), and `.olean` constant walk (`MODULE_CONSTS_CHECKED=499 BAD_CONSTS=0`).

## Revalidation

Each claim class admits a fast (`< 10`-second), discriminating local check against any newer `rustc`, `LLVM`, `Miri`, or `Lean` release without repeating the full multi-backend audit:

### 1. Re-run the Complete `rustc` / `LLVM` / `Miri` Empirical Suite (`< 6` seconds)

Run the preserved probe script against any nightly `rustc` with the `miri` component installed:

```bash
python3 reports/rustc-simd-masked-load-align-bitmask-endianness-and-mcp838-mir-ice/support/probe_simd_intrinsics_and_mcp838_ice.py --out /tmp/reval_simd.json
```

Inspect the JSON diff against `support/probe_results.json` for five high-signal drift indicators:
- **ABI drift (`part_c...ir_simd_as`):** On `rustc >= 1.102.0-nightly`, `x86_64` switches from `sret([4 x i8])` to direct `define <4 x i8> @ir_simd_as(<4 x float> %x)` while `s390x` retains `sret([4 x i8])`; if `s390x` ever adopts direct passing, `can_pass_simd_directly` in `compiler/rustc_target/src/callconv/mod.rs` changed.
- **Mask lowering drift (`part_c...opt0...ir_bitmask` and `opt2...ir_bitmask`):** Check whether `-Copt-level=0` still emits `lshr ... splat (i32 31)` + `trunc` (MSB) and `-O` still folds it to `icmp slt ..., zeroinitializer`.
- **Target alignment drift (`part_b...all_masked_align8_vector_align_target_split`):** Confirm `miri_x86_64_tb_rc == 1` vs. `miri_s390x_tb_rc == 0` (if `s390x` begins failing, its data layout changed `v128:64`).
- **Bitmask endianness (`part_a...miri_bitmask_hex`):** Confirm `x86_64_le == "0x05"` and `s390x_be == "0xa0"`.
- **MCP#838 ICE status (`part_d`):** If `crate_type_lib.rc` changes from `101` to `1` (normal compiler error) and `emit_metadata_only.rc` changes from `0` to `1`, upstream `rustc` has promoted MCP#838's projection ban from a post-`optimized_mir` `Validator` ICE to a clean HIR/typeck diagnostic.

### 2. Re-check the Lean `v4.34.1` Formalization and Axiom/Constant Footprint (`< 5` seconds)

```bash
export LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1"
"$LEAN_SYSROOT/bin/lean" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  reports/rustc-simd-masked-load-align-bitmask-endianness-and-mcp838-mir-ice/support/SimdMaskedLoadBitmaskAndMcp838Soundness.lean
```

To verify zero `Classical.choice`, zero `sorryAx`, zero `Lean.ofReduceBool`, and zero `._unsafe_rec`/`partial` constants after any Lean toolchain upgrade, compile to a temporary `.olean` with `-R .../support -o /tmp/SimdMaskedLoadBitmaskAndMcp838Soundness.olean`, `#print axioms` on all 18 theorems, and verify `env.header.moduleData[idx].constNames` contains `0` unsafe/partial/`_unsafe_rec` entries.

### 3. Narrow Upstream Source Diffs (When Checking a Newer `rust-lang/rust` Commit)

Diff only these six narrow source regions against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:
1. `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` (`check_simd_ptr_alignment`, `simd_masked_load`, `simd_bitmask_index`, `simd_element_to_bool`, `simd_cast | simd_as`).
2. `compiler/rustc_codegen_llvm/src/intrinsic.rs` (`vector_mask_to_bitmask`, `simd_bitmask`, `llvm_alignment`, `simd_masked_load`, `simd_cast | simd_as`).
3. `compiler/rustc_mir_transform/src/validate.rs` (`Validator::run_pass`, `TypeChecker` `ty::Adt` field projection check) and `compiler/rustc_middle/src/ty/adt.rs` (`AdtDef::can_project_fields`).
4. `compiler/rustc_target/src/callconv/mod.rs` (`can_pass_simd_directly` inside `adjust_for_rust_abi`).
5. `library/portable-simd/crates/core_simd/src/{masks.rs, vector.rs}` (`Mask::to_array`, `Mask::to_bitmask`, `Simd::load_select_ptr`, `Simd::store_select_ptr`).
6. `compiler/rustc_codegen_{cranelift,gcc}/src/intrinsic*/simd.rs` (`simd_bitmask` and `simd_masked_load` mask predicates).
