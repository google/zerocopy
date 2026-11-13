# Inventory of `rustc` 1.99.1 Compiler Intrinsics, Portable SIMD Operations, and `core::arch` LLVM Bindings Across Semantic Sources and Backends

## Summary

A verified drop-in replacement for `rustc` at the pinned **Rust 1.99.1**
baseline (`58cf8f9c35b355199727627d07ae34a4e2846d67`) must account for three
distinct intrinsic surfaces—`#[rustc_intrinsic]` functions in `core` and
`alloc`, portable/scalable `simd_*` intrinsics in `core::intrinsics::simd`, and
external `link_name = "llvm.*"` declarations in `core::arch` (`library/stdarch`).
Auditing all three surfaces across MIR construction, MIR transformations,
compile-time constant evaluation (`rustc_const_eval`), Miri, and the three
in-tree codegen backends (`rustc_codegen_llvm`, `rustc_codegen_cranelift`, and
`rustc_codegen_gcc`) establishes four governing facts:

1. **Complete `#[rustc_intrinsic]` inventory (`317` declarations at `1.99.1`):**
   Rust `1.99.1` declares exactly **317 unique `#[rustc_intrinsic]` functions**
   across five source files: `library/core/src/intrinsics/mod.rs` (`234`),
   `library/core/src/intrinsics/simd/mod.rs` (`75`),
   `library/core/src/intrinsics/simd/scalable.rs` (`5`),
   `library/core/src/intrinsics/gpu.rs` (`2`), and
   `library/alloc/src/intrinsics.rs` (`1`: `write_box_via_move`). Of these 317
   intrinsics, **166 are `safe fn`** and **151 are `unsafe fn`**; **218 are
   `const fn`**; **298 carry `#[rustc_nounwind]`**; and **93 provide a default
   Rust MIR fallback body** (`{ ... }`), leaving **224 bodyless declarations**
   that must be lowered before or during backend codegen.
2. **Five-stage compiler lowering pipeline:** Not all 317 intrinsics reach a
   codegen backend's `IntrinsicCallBuilderMethods::codegen_intrinsic_call`:
   - **Stage 1 — THIR-to-MIR construction (`rustc_mir_build`):**
     `write_via_move` and `write_box_via_move` are lowered directly into
     un-dropped MIR `StatementKind::Assign` statements in
     `compiler/rustc_mir_build/src/builder/expr/into.rs:401-456` and never
     appear as `TerminatorKind::Call` in built MIR.
   - **Stage 2 — Constness remapping (`rustc_mir_transform`):**
     `const_eval_select` is rewritten by `remap_mir_for_const_eval_select`
     (`compiler/rustc_mir_transform/src/lib.rs:240-290, 517, 801`) into a direct
     call to `called_in_const` in `mir_for_ctfe` and `called_at_rt` in
     `optimized_mir`.
   - **Stage 3 — Required `LowerIntrinsics` pass (`rustc_mir_transform`):**
     `compiler/rustc_mir_transform/src/lower_intrinsics.rs:12-346` (`PassPolicy::Required`,
     running even at `-Zmir-opt-level=0`) lowers **28 intrinsics** into native
     MIR terminators, statements, and rvalues (`TerminatorKind::Unreachable`,
     `NonDivergingIntrinsic::Assume`, `NonDivergingIntrinsic::CopyNonOverlapping`,
     `Operand::RuntimeChecks`, `Rvalue::BinaryOp`, `Rvalue::Cast(CastKind::Transmute)`,
     `Rvalue::Discriminant`, `Rvalue::Aggregate(AggregateKind::RawPtr)`, and
     `Rvalue::UnaryOp(UnOp::PtrMetadata)`).
   - **Stage 4 — CTFE / GVN compile-time evaluation (`rustc_const_eval` & `gvn`):**
     **14 compile-time reflection and type-inspection intrinsics** (`type_of`,
     `type_id_vtable`, `type_id_is_signed`, `size_of_type_id`, `type_id_variants`,
     `type_id_fields`, `type_id_field_representing_type`,
     `field_representing_type_actual_type_id`, `field_representing_type_name`,
     `field_representing_type_offset`, `non_exhaustive`, `type_id_generics`,
     `const_allocate`, `const_make_global`) are evaluated exclusively in
     `compiler/rustc_const_eval/src/const_eval/machine.rs:483-760`, while layout
     queries (`size_of`, `align_of`, `needs_drop`, `variant_count`, `offset_of`,
     `field_offset`, `type_name`, `type_id`) are folded by CTFE/GVN or lowered
     in `rustc_codegen_ssa::mir::intrinsic::codegen_intrinsic_call`.
   - **Stage 5 — Backend intrinsic lowering (`rustc_codegen_ssa` + backend):**
     `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs` handles **84 intrinsics**
     generically through `BuilderMethods`, while backend-specific modules
     handle SIMD, atomics, va_list, math, and target hooks (`293 / 317`
     supported in `rustc_codegen_llvm`, `281 / 317` in `rustc_codegen_cranelift`,
     and `210 / 317` in `rustc_codegen_gcc`).
3. **Complete portable `simd_*` lowering and cross-check coverage (`75` intrinsics):**
   All **75 portable SIMD intrinsics** in `library/core/src/intrinsics/simd/mod.rs`
   are implemented in `rustc_codegen_llvm/src/intrinsic.rs:1495-3405`, where 63
   are shared in `rustc_const_eval/src/interpret/intrinsics/simd.rs` and the
   remaining **12 runtime/pointer/gather-scatter intrinsics** are implemented in
   Miri (`src/tools/miri/src/intrinsics/simd.rs`), giving **75 / 75 (100%)
   independent executable reference coverage in Miri + CTFE** and **72 / 75
   (96.0%) in `rustc_codegen_cranelift`** (`compiler/rustc_codegen_cranelift/src/intrinsics/simd.rs`).
4. **The `8,384` `link_name = "llvm.*"` bindings in `core::arch` (`8,115` unique LLVM intrinsics):**
   Scanning `library/stdarch/crates/core_arch/src/` identifies **8,384
   `link_name = "llvm.*"` bindings** across 17 architecture directories
   (`2,394` in `aarch64`, `1,853` in `hexagon`, `1,097` in `arm_shared`, `986`
   in `x86`, `904` in `loongarch64`, `530` in `mips`, `176` in `s390x`, `118` in
   `powerpc`, `101` in `x86_64`, `53` in `amdgpu`, `52` in `wasm32`, `41` in
   `arm`, `41` across `riscv*`, `21` across `loongarch32`/`loongarch_shared`,
   `15` in `nvptx`, `2` in `powerpc64`). Of the **8,115 unique `llvm.*`
   intrinsics**, only **60 (0.74%)** use target-independent LLVM intrinsics
   (`llvm.nearbyint`, `llvm.roundeven`, `llvm.vector.reverse`, `llvm.fptosi.sat`,
   `llvm.fptoui.sat`, `llvm.vector.insert`, `llvm.minimum`, `llvm.maximum`,
   `llvm.smax`, `llvm.umax`, `llvm.smin`, `llvm.umin`, `llvm.prefetch`,
   `llvm.minnum`, `llvm.maxnum`, `llvm.fshr`), whereas **8,055 (99.26%)** bind
   target-specific `llvm.<arch>.*` intrinsics. Miri emulates **225 `llvm.*`
   intrinsics** (`176` x86/x86_64, `15` AArch64/Arm NEON, `8` LoongArch, plus
   variants), and `rustc_codegen_cranelift` emulates **236 `stdarch` `llvm.*`
   intrinsics** (`73` x86/x86_64, `164` AArch64/Arm, `2` s390x/generic).

## Applicability

These findings apply to **Rust 1.99.1** (`rust-lang/rust` commit
`58cf8f9c35b355199727627d07ae34a4e2846d67`), with explicit version-evolution
comparisons against **Rust 1.100.0** (`0ef1bc386059596dada8fb65b50425aab2ea637a`)
and **`nightly-2026-11-12`** (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`). All
counts and lowering classifications were extracted directly from the compiler,
library, and Miri source trees and preserved in
`support/intrinsics_inventory.json`.

## Findings

### 1. Partitioning of the 317 `#[rustc_intrinsic]` declarations in Rust 1.99.1

Basis: source (`library/core/src/intrinsics/`, `library/alloc/src/intrinsics.rs`)

Table 1 breaks down the 317 `#[rustc_intrinsic]` declarations by source file,
safety, constness, fallback-body presence, and lowering stage.

| Source File | Count | `safe fn` | `unsafe fn` | `const fn` | Default MIR Fallback Body (`{ ... }`) | Primary Lowering Stage in `rustc 1.99.1` |
| :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| `library/core/src/intrinsics/mod.rs` | 234 | 164 | 70 | 217 | **93** (`39.7%`) | `rustc_mir_build` (`1`), `remap_mir` (`1`), `LowerIntrinsics` (`28`), CTFE (`14`), `rustc_codegen_ssa` (`84`), backend (`106`) |
| `library/core/src/intrinsics/simd/mod.rs` | 75 | 0 | 75 | 0 | **0** (`0.0%`) | `rustc_codegen_llvm::intrinsic::codegen_simd_intrinsic_call` + CTFE `interpret/intrinsics/simd.rs` + Miri `intrinsics/simd.rs` |
| `library/core/src/intrinsics/simd/scalable.rs` | 5 | 0 | 5 | 0 | **0** (`0.0%`) | `rustc_codegen_llvm::intrinsic` (`sve` / `rvv` scalable vectors: `simd_cast`, `simd_as`, `simd_neg`, `simd_add`, `simd_sub`) |
| `library/core/src/intrinsics/gpu.rs` | 2 | 2 | 0 | 0 | **0** (`0.0%`) | `rustc_codegen_llvm` (` autodiff` & `offload`) |
| `library/alloc/src/intrinsics.rs` | 1 | 0 | 1 | 1 | **0** (`0.0%`) | `rustc_mir_build` (`write_box_via_move`, lowered during THIR-to-MIR construction) |
| **Total (`1.99.1`)** | **317** | **166** | **151** | **218** | **93** | **All 317 accounted for across MIR build, MIR transform, CTFE, and codegen** |

#### 1.1 The 28 intrinsics lowered to native MIR by `LowerIntrinsics`

`compiler/rustc_mir_transform/src/lower_intrinsics.rs:12-346` runs with
`PassPolicy::Required` at the end of the `Runtime(PostCleanup)` phase. A backend
consuming `Runtime(PostCleanup)` or `Runtime(Optimized)` MIR never sees call
terminators for these 28 intrinsics because they have already been replaced by
first-class MIR statements or terminators:

| Intrinsic Name(s) | Count | Target MIR Construct Emitted by `LowerIntrinsics` (`lower_intrinsics.rs`) |
| :--- | ---: | :--- |
| `unreachable` | 1 | `TerminatorKind::Unreachable` (`lines 24-26`) |
| `ub_checks`, `overflow_checks`, `contract_checks` | 3 | `StatementKind::Assign(dest, Rvalue::Use(Operand::RuntimeChecks(op), WithRetag::Yes))` (`lines 27-43`) |
| `forget` | 1 | `StatementKind::Assign(dest, Rvalue::Use(Operand::Constant(Const::zero_sized(unit)), WithRetag::Yes))` (`lines 44-61`) |
| `copy_nonoverlapping` | 1 | `StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping { src, dst, count })` (`lines 62-80`) |
| `assume` | 1 | `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(arg))` (`lines 81-93`) |
| `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `three_way_compare` | 4 | `Rvalue::BinaryOp(BinOp::Add \| Sub \| Mul \| Cmp, (lhs, rhs))` (`lines 94-131`) |
| `unchecked_add`, `unchecked_sub`, `unchecked_mul`, `unchecked_div`, `unchecked_rem`, `unchecked_shl`, `unchecked_shr` | 7 | `Rvalue::BinaryOp(BinOp::AddUnchecked \| SubUnchecked \| MulUnchecked \| Div \| Rem \| ShlUnchecked \| ShrUnchecked, (lhs, rhs))` (`lines 98-131`) |
| `add_with_overflow`, `sub_with_overflow`, `mul_with_overflow` | 3 | `Rvalue::BinaryOp(BinOp::AddWithOverflow \| SubWithOverflow \| MulWithOverflow, (lhs, rhs))` (`lines 132-151`) |
| `read_via_copy` | 1 | `Rvalue::Use(Operand::Copy(*arg), WithRetag::Yes)` (`lines 152-183`; `Unreachable` if target is `None`) |
| `discriminant_value` | 1 | `Rvalue::Discriminant(*arg)` (`lines 185-203`) |
| `offset` | 1 | `Rvalue::BinaryOp(BinOp::Offset, (ptr, delta))` (`lines 204-220`) |
| `slice_get_unchecked` | 1 | `Rvalue::RawPtr` or `Rvalue::Ref` over `place.project_deeper(&[Deref, Index(idx)])` (`lines 221-266`) |
| `transmute`, `transmute_unchecked` | 2 | `Rvalue::Cast(CastKind::Transmute, arg, dst_ty)` (`lines 267-291`) |
| `aggregate_raw_ptr` | 1 | `Rvalue::Aggregate(AggregateKind::RawPtr(pointee_ty, mutbl), [data, meta])` (`lines 292-318`) |
| `ptr_metadata` | 1 | `Rvalue::UnaryOp(UnOp::PtrMetadata, ptr)` (`lines 319-335`) |

In addition, `InstSimplify` (`compiler/rustc_mir_transform/src/instsimplify.rs:273-380`,
enabled when `-Zmir-opt-level > 0`) simplifies:
- `size_of_val::<T>` and `align_of_val::<T>` into `LangItem::SizeOf` /
  `LangItem::AlignOf` constants when `T: Sized` (and `align_of_val::<[T]>` to
  `align_of::<T>()`),
- `raw_eq::<T>(a, b)` into integer `BinOp::Eq(CastKind::Transmute(a), CastKind::Transmute(b))`
  whenever `sizeof(T)` matches a primitive integer (`u8`, `u16`, `u32`, `u64`, `u128`),
- `assert_inhabited::<T>()`, `assert_zero_valid::<T>()`, and
  `assert_mem_uninitialized_valid::<T>()` into `Nop` (when valid) or `TerminatorKind::Unreachable` / panic (when invalid).

#### 1.2 Default MIR fallback bodies (`93` intrinsics) and when backends use them

In `library/core/src/intrinsics/mod.rs` and `library/core/src/intrinsics/fallback.rs`,
**93 `#[rustc_intrinsic]` declarations include a Rust body**. In `rustc_codegen_ssa::mir::block`
(`compiler/rustc_codegen_ssa/src/mir/block.rs:1070-1120`), when a backend's
`codegen_intrinsic_call` returns `Err(Instance)` (indicating the backend opted
not to emit a specialized instruction sequence), `rustc_codegen_ssa` emits a
normal function call to the monomorphized MIR fallback body of that intrinsic!
Notable examples of fallback-backed intrinsics include:
- Wide arithmetic in `fallback.rs`: `carrying_mul_add`, `widening_mul`,
  ` borrowing_sub`, `carrying_add`, `disjoint_bitor`, `funnel_shl`, `funnel_shr`,
  `scmp`, `ucmp`,
- Control and optimization hints that default to identity/false when unlowered:
  `likely(b) -> b`, `unlikely(b) -> b`, `black_box(x) -> x`,
  `is_val_statically_known(_) -> false`, `select_unpredictable(cond, t, f)`,
  `prefetch_read_data`, `prefetch_write_data`, `prefetch_read_instruction`,
  `prefetch_write_instruction`, `cold_path() {}`,
- Checked/saturating wrappers: `saturating_add`, `saturating_sub`, `exact_div`,
  `unchecked_shl`, `unchecked_shr`, `rotate_left`, `rotate_right`, `ctlz`,
  `cttz`, `ctpop`, `bitreverse`, `bswap`.

#### 1.3 Evolution across `1.99.1`, `1.100.0`, and `nightly-2026-11-12`

Comparing `s1991` (`1.99.1`), `s1100` (`1.100.0`), and `n1112`
(`nightly-2026-11-12`) reveals two structural consolidations in `core::intrinsics`:
1. **Polymorphic float math intrinsics (`1.100.0` and `nightly-2026-11-12`):**
   `1.100.0` replaces the 28 width-suffixed transcendental intrinsics
   (`sinf16`/`f32`/`f64`/`f128`, `cosf*`, `expf*`, `exp2f*`, `logf*`, `log2f*`,
   `log10f*`) with 7 generic float intrinsics (`sin<T>`, `cos<T>`, `exp<T>`,
   `exp2<T>`, `log<T>`, `log2<T>`, `log10<T>`). `nightly-2026-11-12` completes
   this migration by replacing the remaining 40 width-suffixed float intrinsics
   (`sqrtf*`, `floorf*`, `ceilf*`, `truncf*`, `roundf*`, `round_ties_even_f*`,
   `fmaf*`, `fmuladdf*`, `powf*`, `powif*`) with generic `sqrt<T>`, `floor<T>`,
   `ceil<T>`, `trunc<T>`, `round<T>`, `round_ties_even<T>`, `fma<T>`,
   `fmuladd<T>`, `powf<T>`, and `powi<T>`.
2. **Compile-time reflection (`type_id_*`):** `1.100.0` and `nightly-2026-11-12`
   expand the experimental `const` reflection intrinsics with
   `type_id_array_len`, `type_id_element_ty`, `type_id_function_ptr`,
   `type_id_points_mutably`, and `type_id_points_to`.

---

### 2. Portable SIMD (`simd_*`) semantics and backend lowering

Basis: source (`library/core/src/intrinsics/simd/mod.rs`, `compiler/rustc_codegen_llvm/src/intrinsic.rs:1495-3405`, `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs`, `src/tools/miri/src/intrinsics/simd.rs`, `compiler/rustc_codegen_cranelift/src/intrinsics/simd.rs`)

Table 2 categorizes all **75 portable `simd_*` intrinsics** in
`library/core/src/intrinsics/simd/mod.rs`, their LLVM IR lowering in
`rustc_codegen_llvm/src/intrinsic.rs`, their CTFE vs. Miri execution engine
implementation, and their `rustc_codegen_cranelift` lowering.

| Category | Count | `simd_*` Intrinsic Names | LLVM 23.1.1 Lowering (`rustc_codegen_llvm/src/intrinsic.rs`) | CTFE (`interpret/intrinsics/simd.rs`) | Miri (`miri/src/intrinsics/simd.rs`) | Cranelift (`cg_clif/src/intrinsics/simd.rs`) |
| :--- | ---: | :--- | :--- | :--- | :--- | :--- |
| Element access & shuffles | 4 | `simd_insert`, `simd_extract`, `simd_shuffle`, `simd_splat` | `insertelement`, `extractelement`, `shufflevector` | 4 / 4 | 4 / 4 (via CTFE) | 4 / 4 |
| Comparisons (mask-producing) | 6 | `simd_eq`, `simd_ne`, `simd_lt`, `simd_le`, `simd_gt`, `simd_ge` | `icmp` / `fcmp` followed by `sext <N x i1> to <N x iM>` (all-ones `-1` or `0` per lane) | 6 / 6 | 6 / 6 (via CTFE) | 6 / 6 |
| Lane-wise binary arithmetic & bitwise | 10 | `simd_add`, `simd_sub`, `simd_mul`, `simd_div`, `simd_rem`, `simd_shl`, `simd_shr`, `simd_and`, `simd_or`, `simd_xor` | `add`/`fadd`, `sub`/`fsub`, `mul`/`fmul`, `udiv`/`sdiv`/`fdiv`, `urem`/`srem`/`frem`, `shl`, `lshr`/`ashr`, `and`, `or`, `xor` (`lines 3250-3264`) | 10 / 10 | 10 / 10 (via CTFE) | 10 / 10 |
| Saturating integer arithmetic | 2 | `simd_saturating_add`, `simd_saturating_sub` | `@llvm.sadd.sat.*`, `@llvm.uadd.sat.*`, `@llvm.ssub.sat.*`, `@llvm.usub.sat.*` (`lines 3379-3403`) | 2 / 2 | 2 / 2 (via CTFE) | 2 / 2 |
| Unary & bit manipulation | 9 | `simd_neg`, `simd_bswap`, `simd_bitreverse`, `simd_ctlz`, `simd_cttz`, `simd_ctpop`, `simd_funnel_shl`, `simd_funnel_shr`, `simd_carryless_mul` | `sub 0, x`/`fneg`, `@llvm.bswap`, `@llvm.bitreverse`, `@llvm.ctlz(..., i1 false)`, `@llvm.cttz(..., i1 false)`, `@llvm.ctpop`, `@llvm.fshl`, `@llvm.fshr`, `@llvm.clmul` (LLVM $\ge 22$, `lines 3280-3356`) | 9 / 9 | 9 / 9 (via CTFE) | 8 / 9 (`simd_carryless_mul` unimplemented) |
| Casts & provenance | 6 | `simd_as`, `simd_cast`, `simd_cast_ptr`, `simd_expose_provenance`, `simd_with_exposed_provenance`, `simd_arith_offset` | `trunc`/`sext`/`zext`, `sitofp`/`uitofp`, `@llvm.fptosi.sat`/`@llvm.fptoui.sat` (`simd_as`), `fptosi`/`fptoui` (`simd_cast`), `bitcast`, `ptrtoint`, `inttoptr`, vector `getelementptr` (`lines 3018-3234, 3358-3377`) | 4 / 6 (`expose_provenance` & `with_exposed_provenance` in Miri) | 6 / 6 | 6 / 6 |
| Mask selection & bitmasks | 3 | `simd_select`, `simd_select_bitmask`, `simd_bitmask` | `trunc <N x iM> to <N x i1>` + `select`; `bitcast <N x i1> to iN` (padded to byte/integer width, endian-reversed on big-endian) | 3 / 3 | 3 / 3 (via CTFE) | 3 / 3 |
| Horizontal reductions | 11 | `simd_reduce_add_ordered`, `simd_reduce_add_unordered`, `simd_reduce_mul_ordered`, `simd_reduce_mul_unordered`, `simd_reduce_min`, `simd_reduce_max`, `simd_reduce_and`, `simd_reduce_or`, `simd_reduce_xor`, `simd_reduce_all`, `simd_reduce_any` | `@llvm.vector.reduce.{add,fadd,mul,fmul,smin,umin,smax,umax,and,or,xor}` (`lines 2865-3016`) | 9 / 11 (`unordered` float reductions in Miri) | 11 / 11 | 11 / 11 |
| Floating-point unary/binary/ternary math | 20 | `simd_fabs`, `simd_fsqrt`, `simd_ffloor`, `simd_fceil`, `simd_ftrunc`, `simd_fround`, `simd_fround_ties_even`, `simd_fsin`, `simd_fcos`, `simd_fexp`, `simd_fexp2`, `simd_flog`, `simd_flog2`, `simd_flog10`, `simd_fma`, `simd_fmuladd`, `simd_fpow`, `simd_fpowi`, `simd_minimum_number_nsz`, `simd_maximum_number_nsz` | `@llvm.{fabs,sqrt,floor,ceil,trunc,round,roundeven,sin,cos,exp,exp2,log,log2,log10,fma,fmuladd,pow,powi,minimum,maximum}` | 16 / 20 (transcendentals in Miri) | 20 / 20 | 18 / 20 (`simd_fpow`, `simd_fpowi` scalarized) |
| Masked memory loads, stores, gather & scatter | 4 | `simd_masked_load`, `simd_masked_store`, `simd_gather`, `simd_scatter` | `@llvm.masked.load`, `@llvm.masked.store`, `@llvm.masked.gather`, `@llvm.masked.scatter` (with LLVM $\ge 22$ `align` parameter attribute on pointer arg, `lines 2630-2863`) | 0 / 4 (rejected in CTFE) | 4 / 4 (`miri/src/intrinsics/simd.rs`) | 4 / 4 (lane-by-lane conditional load/store loop) |

**Key semantic invariants for a verified backend:**
1. **`simd_cast` vs. `simd_as` on float-to-int:** `simd_cast` emits raw LLVM
   `fptosi` / `fptoui` (yielding `poison` on out-of-range or `NaN` lanes),
   whereas `simd_as` calls `bx.cast_float_to_int` (`@llvm.fptosi.sat` /
   `@llvm.fptoui.sat`), clamping `NaN` to `0` and out-of-bounds values to
   `T::MIN` / `T::MAX` (`rustc_codegen_llvm/src/intrinsic.rs:3207-3216`).
2. **Vector mask representation:** Comparison intrinsics (`simd_eq`, etc.) must
   return all-ones (`-1`, i.e. `0xFF..FF`) for `true` and `0` for `false` in the
   signed integer lane width. Conversely, `simd_select` checks only the mask
   element's LSB (`trunc <N x iM> to <N x i1>`) in LLVM, whereas CTFE/Miri
   verifies that mask lanes are strictly `0` or all-ones (`-1`) and throws UB
   otherwise (`interpret/intrinsics/simd.rs:42-60`).
3. **LLVM 22+ `masked.{load,store,gather,scatter}` signature change:** At
   LLVM $\ge 22.0.0$ (including `1.99.1`'s LLVM `23.1.1`), the 4th integer
   alignment parameter was removed from `@llvm.masked.{load,store,gather,scatter}`
   and replaced by an `align(N)` attribute on the pointer argument
   (`rustc_codegen_llvm/src/intrinsic.rs:2676-2692, 2844-2861`).

---

### 3. `core::arch` `link_name = "llvm.*"` inventory and cross-check coverage

Basis: source (`library/stdarch/crates/core_arch/src/`, `src/tools/miri/src/intrinsics/`, `compiler/rustc_codegen_cranelift/src/intrinsics/`, `compiler/rustc_codegen_gcc/src/intrinsic/`)

Table 3 presents the complete census of `link_name = "llvm.*"` external
declarations across `library/stdarch/crates/core_arch/src/` (`8,384` total
declarations, `8,115` unique `llvm.*` intrinsic names) and the number of unique
intrinsics emulated by Miri, Cranelift, and GCC.

| `core_arch` Directory | Total `link_name` Declarations | Unique `llvm.*` Intrinsics | Target-Independent (`llvm.<generic>`) | Target-Specific (`llvm.<arch>.*`) | Miri Shims (`src/tools/miri/src/intrinsics/`) | Cranelift Emulation (`cg_clif/src/intrinsics/`) | GCC Backend Mapping (`cg_gcc/src/intrinsic/`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `aarch64` | 2,394 | 2,229 | 29 | 2,200 | 11 | 58 | 1 |
| `arm_shared` | 1,097 | 1,006 | 8 | 998 | 4 | 106 | 1 |
| `arm` | 41 | 41 | 0 | 41 | 0 | 0 | 0 |
| `x86` | 986 | 982 | 1 | 981 | 173 | 70 | 311 |
| `x86_64` | 101 | 101 | 0 | 101 | 3 | 3 | 42 |
| `hexagon` | 1,853 | 1,853 | 0 | 1,853 | 0 | 0 | 0 |
| `loongarch64` | 904 | 904 | 0 | 904 | 8 | 0 | 0 |
| `loongarch_shared` | 17 | 17 | 0 | 17 | 0 | 0 | 0 |
| `loongarch32` | 4 | 4 | 0 | 4 | 0 | 0 | 0 |
| `mips` | 530 | 530 | 0 | 530 | 0 | 0 | 0 |
| `s390x` | 176 | 176 | 9 | 167 | 0 | 2 | 0 |
| `powerpc` | 118 | 117 | 13 | 104 | 0 | 0 | 1 |
| `powerpc64` | 2 | 2 | 0 | 2 | 0 | 0 | 0 |
| `amdgpu` | 53 | 53 | 0 | 53 | 0 | 0 | 0 |
| `wasm32` | 52 | 52 | 6 | 46 | 0 | 0 | 0 |
| `riscv_shared` | 20 | 20 | 0 | 20 | 0 | 0 | 0 |
| `riscv32` | 12 | 12 | 0 | 12 | 0 | 0 | 0 |
| `riscv64` | 9 | 9 | 0 | 9 | 0 | 0 | 0 |
| `nvptx` | 15 | 15 | 2 | 13 | 0 | 0 | 0 |
| **Total (`stdarch`)** | **8,384** | **8,115** (deduped) | **60** | **8,055** | **198** (`225` total in Miri) | **236** | **356** |

**Why `stdarch` uses fewer `link_name = "llvm.*"` bindings than total vendor intrinsics:**
In `stdarch`, roughly half of all `core::arch` functions are implemented using
portable `simd_*` intrinsics (`simd_add`, `simd_sub`, `simd_mul`, `simd_and`,
`simd_or`, `simd_xor`, `simd_shuffle`, `simd_cast`, `simd_eq`, etc.) rather than
`link_name = "llvm.*"` foreign calls! As a result:
- Every `core::arch` function written in terms of `simd_*` intrinsics works
  **automatically** in Miri, CTFE, `rustc_codegen_cranelift`, and
  `rustc_codegen_gcc` without needing a target-specific `llvm.<arch>.*` shim.
- On `x86` + `x86_64` (`1,087` `link_name` bindings across `1,083` unique
  `llvm.x86.*` intrinsics), Miri implements **176 `llvm.x86.*` shims**
  (`src/tools/miri/src/intrinsics/x86/{mod,sse,sse2,sse3,ssse3,sse41,sse42,avx,avx2,avx512,bmi,aesni,sha,gfni}.rs`),
  covering the non-trivial horizontal, saturating, string-comparison (`pcmpestri` /
  `pcmpistrm`), cryptographic (`aesenc`, `sha256rnds2`, `gf2p8affineqb`), and
  bit-manipulation (`pdep`, `pext`, `bzhi`) operations used by `hashbrown`,
  `memchr`, `regex`, `crc32fast`, and `ring`/`RustCrypto`.
- On `aarch64` + `arm_shared` (`3,491` `link_name` bindings across `3,235`
  unique `llvm.aarch64.*` / `llvm.arm.*` intrinsics, of which `2,018` in
  `aarch64/sve/` and `sve2/` are SVE/SVE2), Miri implements **15 `llvm.aarch64.*`
  shims** (`src/tools/miri/src/intrinsics/aarch64.rs`) and Cranelift emulates
  **164 `llvm.aarch64.*` / generic NEON intrinsics**
  (`compiler/rustc_codegen_cranelift/src/intrinsics/llvm_aarch64.rs`) by
  lowering them to CLIF vector instructions or inline assembly snippets.

## Boundaries

- **Miri and Cranelift are partial cross-check oracles for `llvm.<arch>.*`:**
  While Miri + CTFE provide **100% (75 / 75)** executable reference coverage for
  `core::intrinsics::simd` and **74.1% (235 / 317)** for all `#[rustc_intrinsic]`
  functions, Miri covers **16.3% (`176 / 1,083`)** of `llvm.x86.*` bindings and
  **0.46% (`15 / 3,235`)** of `llvm.aarch64.*` / `llvm.arm.*` bindings. Complete
  verification of `core::arch` therefore requires vendor-specification / ISA-level
  semantics rather than relying solely on Miri shims (see
  `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`).
- **GPU offload and Enzyme autodiff intrinsics (`autodiff`, `offload`,
  `gpu_thread_id`):** These intrinsics exist only as LLVM pass hooks in
  `rustc_codegen_llvm` and are **unsupported** in Miri, Cranelift, and GCC.

## Evidence

- **Primary source files (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `library/core/src/intrinsics/mod.rs:1-4620`, `fallback.rs:1-345`,
    `gpu.rs:1-95`, `simd/mod.rs:1-695`, `simd/scalable.rs:1-85`.
  - `library/alloc/src/intrinsics.rs:1-35`.
  - `compiler/rustc_mir_build/src/builder/expr/into.rs:401-456` (`write_via_move`,
    `write_box_via_move`).
  - `compiler/rustc_mir_transform/src/lib.rs:240-290` (`const_eval_select`),
    `lower_intrinsics.rs:12-346` (`LowerIntrinsics`), `instsimplify.rs:273-380`,
    `gvn.rs:1-2600`.
  - `compiler/rustc_const_eval/src/const_eval/machine.rs:480-760`,
    `interpret/intrinsics.rs:1-1680`, `interpret/intrinsics/atomic.rs:1-175`,
    `interpret/intrinsics/simd.rs:1-1180`.
  - `src/tools/miri/src/intrinsics/{mod,simd,math,aarch64,loongarch}.rs` and
    `src/tools/miri/src/intrinsics/x86/*.rs`.
  - `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:1-780`,
    `compiler/rustc_codegen_llvm/src/intrinsic.rs:1-3406`,
    `compiler/rustc_codegen_cranelift/src/intrinsics/{mod,simd,llvm,llvm_x86,llvm_aarch64}.rs`,
    `compiler/rustc_codegen_gcc/src/intrinsic/{mod,simd,llvm,archs}.rs`.
- **Preserved support artifacts:**
  - `support/intrinsics_inventory.json`: Machine-readable inventory of all 317
    `#[rustc_intrinsic]` items and `8,384` `stdarch` `llvm.*` bindings with
    per-stage and per-backend coverage booleans.
  - `support/probe_intrinsics.py`: Standalone extractor script reproducing
    `support/intrinsics_inventory.json`.

## Revalidation

To revalidate this inventory on a newer `rust-lang/rust` checkout, point
`support/probe_intrinsics.py` at the target worktree and diff the generated
`summary` block against `support/intrinsics_inventory.json`. Specifically check
`version_diffs` for newly added or consolidated `#[rustc_intrinsic]` symbols and
any changes in `LowerIntrinsics` match arms.
