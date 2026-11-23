# Wide-Pointer `ptr::eq` vs. `ptr::addr_eq`, Non-Deterministic `DynMetadata` Vtables, Dynamic Custom-DST `size_of_val`, and `zerocopy::KnownLayout` Arithmetic

## Summary

Comparing wide pointers (`*const [T]`, `*const str`, `*const dyn Trait`, and pointers to custom `?Sized` structs) in Rust involves two distinct operations whose semantics, LLVM lowerings, and Miri behaviors diverge sharply, while dynamic `mem::size_of_val` / `mem::align_of_val` lowering on custom dynamically sized types (DSTs) shares an exact mathematical equivalence with `zerocopy::KnownLayout` / `DstLayout` normalized layout arithmetic modulo the distinction between `usize::MAX` representability and `isize::MAX` allocation validity:

1. **`core::ptr::eq` Compares `(data, meta)` Pairs, Whereas `core::ptr::addr_eq` Compares Thin Addresses Only:**
   - In `library/core/src/ptr/mod.rs` (`277240238554297f93fa9ee3c7643dfa03ccbbb4`), `ptr::eq(a, b)` executes `a == b` (`2515-2517`), which `rustc_codegen_ssa::mir::rvalue::Builder::codegen_wide_ptr_binop` (`rvalue.rs:907-912` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`; `1017-1022` at `27724023`) lowers for `OperandValue::Pair` into `(lhs_addr == rhs_addr) & (lhs_extra == rhs_extra)` (and `a != b` into `|`). Under `-Copt-level=2`, LLVM emits `icmp eq ptr %a.0, %b.0`, `icmp eq <meta_ty> %a.1, %b.1`, and `and i1 %0, %1`.
   - `ptr::addr_eq(p, q)` casts both pointers to `*const ()` before comparing (`(p as *const ()) == (q as *const ())`, `ptr/mod.rs:2539-2541`), stripping pointer metadata and lowering to a single `icmp eq ptr %a.0, %b.0`.
   - Consequently, `ptr::eq(p, q) ==> ptr::addr_eq(p, q)`, while the converse fails whenever slice lengths differ (`SLICE_ADDR_EQ=true`, `SLICE_EQ_DIFF=false`), when a trait object points to an outer wrapper vs. its field (`DYN_ADDR_EQ=true`, `DYN_EQ_DIFF_VTABLE=false`), on trait upcasting coercions (`DYN_EQ_UPCAST=false`), or when Miri duplicates vtables for the same concrete object.

2. **Non-Deterministic `DynMetadata` Vtable Addresses Explain Native-vs.-Miri Divergence and Cross-Type False Positives:**
   - In native LLVM codegen (`rustc_codegen_ssa/src/meth.rs:145-175`, `rustc_codegen_llvm/src/consts.rs:296-345, 909-918`), vtable globals are emitted with `PrivateLinkage` and `UnnamedAddr::Global` and deduplicated within a single codegen unit (CGU) both by `(self_ty, trait_ref)` in `cx.vtables()` and by constant allocation contents `cv` in `const_globals`.
   - Within one CGU, two separate `&Outer -> &dyn Tr` coercions of the same concrete object yield the same vtable pointer (`DYN_EQ_SAME_VTABLE=true`), **and** two distinct concrete `!needs_drop` zero-method marker types `TyA(u8)` and `TyB(u8)` sharing the same union storage address emit identical `[null, 1, 1]` vtables (`VtblEntry::MetadataDropInPlace` lowers to `Pointer::null()` when `!ty.needs_drop(...)` at `compiler/rustc_middle/src/ty/vtable.rs:123-135`) and coalesce onto the same global vtable, yielding a native false positive (`DIFF_TYPES_ADDR_EQ=true`, `DIFF_TYPES_PTR_EQ=true` even at `-O0`!). Conversely, trait upcasting `(&Outer as &dyn SubTr) as &dyn Tr` reuses `dyn SubTr`'s longer vtable prefix on native codegen, causing `DYN_EQ_UPCAST=false` even natively.
   - Under `cargo +nightly miri` (`miri 0.1.0` at `14210df0e`), `InterpCx::get_vtable_ptr` (`compiler/rustc_const_eval/src/interpret/traits.rs:19-36`) passes `instance = None` to `M::get_global_alloc_salt(self, None)`. In Miri (`src/tools/miri/src/machine.rs:60, 2058-2097`), non-functions return `unique = false`, drawing a random salt in `0..32` (`ADDRS_PER_ANON_GLOBAL = 32`) used by `reserve_and_set_vtable_alloc` (`compiler/rustc_middle/src/mir/interpret/mod.rs:500-507`), while Miri's `binary_ptr_op` (`src/tools/miri/src/operator.rs:25-50`) compares `ScalarPair` raw bits lexicographically. Therefore `ptr::eq` on two separate `&Outer -> &dyn Tr` coercions of the same object fails ~96.875% of the time in Miri (`DYN_EQ_SAME_VTABLE=false` in Miri default and in `0/16` seeds `0..15`, and `DIFF_TYPES_PTR_EQ=false`), whereas copied wide pointers (`DYN_EQ_COPIED=true`) and `ptr::addr_eq` (`DYN_ADDR_EQ=true`) are 100% salt-invariant.

3. **Custom-DST `size_and_align_of_dst` Lowers to One Single-Step Bitmask Rounding Using Precomputed Unadjusted Offset:**
   - For `ty::Adt | ty::Tuple` DSTs (`compiler/rustc_codegen_ssa/src/size_of_val.rs:91-182`), `rustc` statically precomputes `unsized_offset_unadjusted = layout.fields.offset(i).bytes()` and `sized_align = layout.align.bytes()`, recursively obtains `(unsized_size, unsized_align)` (for `ty::Dynamic`, loaded with `!invariant.load` and `!range` from vtable slots `1` and `2` at `+8`/`+16` bytes on 64-bit), caps `unsized_align` with `min(unsized_align, packed)` if `#[repr(packed(N))]` is present, sets `full_align = max(sized_align, unsized_align)`, and emits `(unsized_offset_unadjusted + unsized_size + (full_align - 1)) & -full_align` **without** first aligning `unsized_offset_unadjusted` dynamically to `effective_tail_align`.
   - For `Packet<dyn Tr>` (`u8`, static `align=1`, `unsized_offset_unadjusted=1`), LLVM folds `add(1 + size, align - 1)` into **`add nuw i64 %3, %1; sub nsw i64 0, %3; and i64 %4, %5`** (`(align + size) & -align`). For `Header6<dyn Tr>` (`u32, u16, dyn Tr`, `unsized_offset_unadjusted=6`, `sized_align=4`), LLVM emits `llvm.umax.i64(%3, 4)` and computes `(5 + size + full_align) & -full_align`. Both two-step alignment (`alignTo (alignTo offset effTail + tailSize) fullAlign`) and single-step bitmask rounding (`(offset + tailSize + (fullAlign - 1)) & -fullAlign`) are proved mathematically and bit-exact equal in Lean 4 whenever `effTail | tailSize`, `effTail | fullAlign`, and no `w`-bit overflow occurs. All 8 specimen pairs (`U32_3=(16,4)`, `U32_0=(4,4)`, `U8_3=(4,1)`, `DYN_SMALL=(2,1)`, `DYN_BIG=(32,16)`, `H6_U8_3=(12,4)`, `H6_DYN_BIG=(32,16)`, `PACKED2_U32_3=(14,2)`) agree bit-for-bit across native execution, Miri, LLVM IR, and Lean `rfl`.

4. **`zerocopy::KnownLayout` Separates `usize::MAX` Size Overflow from `isize::MAX` Allocation Validity:**
   - In `google/zerocopy` (`0.8.64`, `907b9175` / `e86eb028`), `TrailingSliceLayout::size_for_elems` (`layout.rs:427-491`) checks against `usize::MAX` (`available_bytes = usize::MAX`), while `KnownLayout::is_valid_metadata` (`lib.rs:904-906, 934-960`) validates against `DstLayout::MAX_SIZE = isize::MAX as usize` (`usize::MAX` when `elem_size == 0`, else the largest element count fitting in `isize::MAX`). Live execution confirms `<[u8]>::size_for_metadata(usize::MAX) == Some(18446744073709551615)` while `is_valid_metadata(usize::MAX) == false`, `<[()]>::is_valid_metadata(usize::MAX) == true`, and `<[u32]>::size_for_metadata(usize::MAX) == None`.
   - `DstLayout::for_repr_c_struct` normalizes arbitrary leading layouts plus a trailing slice into `(size_base, size_align, size_phase)` packed in `RoundingAlignAndPhase(align | phase)`. Both the normalization identity `size_base + roundUp(size_phase + elems * elem_size, size_align) == (sizeAndAlignRustc spec tail).1` and checked overflow/validity equivalence are kernel-checked in `support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean` (1,534 LOC, 170 theorems, 137 `noncomputable def`s, 7 types, zero `sorry`, zero `Classical.choice`, zero `._unsafe_rec`, zero `omega`/`bv_decide`/`native_decide`/`partial`).

---

## Applicability

This report documents four tightly coupled compiler, ABI, interpreter, and layout-verification subsystems at their pinned revisions and relates them explicitly:

- **Core pointer equality & LLVM SSA/LLVM backend (`rust-lang/rust@277240238554297f93fa9ee3c7643dfa03ccbbb4` and executed nightly `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly`, LLVM `22.1.6`):**
  - Source findings cover `core::ptr::eq`, `core::ptr::addr_eq`, `core::ptr::DynMetadata`, `rustc_codegen_ssa::mir::rvalue::codegen_wide_ptr_binop`, `rustc_codegen_ssa::size_of_val::size_and_align_of_dst`, `rustc_codegen_ssa::meth::{VirtualIndex, get_vtable}`, `rustc_codegen_llvm::consts::static_addr_of_impl`, `rustc_middle::ty::vtable`, and `rustc_const_eval::interpret::{cast, operator, traits}`.
  - Between the executed nightly (`14210df0e`) and `main` (`27724023`), audited source inspection confirmed identical `codegen_wide_ptr_binop` logic (`Eq` as `icmp eq` + `and`, `Ne` as `icmp ne` + `or`, shifted only by surrounding file line offsets) and identical `size_and_align_of_dst` formulas (with `VirtualIndex::get_usize` dropping its trailing `t` parameter and `spanned_layout_of` replacing `layout_of` on `main`). Empirical LLVM IR and execution behavior apply directly to `x86_64-unknown-linux-gnu` (64-bit little-endian ELF target, `-Copt-level=0` for execution and `-Copt-level=2` for LLVM IR inspection).
- **Miri interpreter (`miri 0.1.0` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, and source at `277240238554297f93fa9ee3c7643dfa03ccbbb4`):**
  - Applies under Miri's default allocation/salt configuration (`ADDRS_PER_ANON_GLOBAL = 32`, RNG-salted vtables and constants, non-GenMC, non-native-lib mode). Behavior on `-Zmiri-seed=0..15` demonstrates that default deterministic seeds do not accidentally defeat Miri's vtable splitting across separate coercions (`0/16` collision rate on two coercions in the tested program).
- **`google/zerocopy` (`907b9175fee081872ec883ca4709e6ad922f8ed0`, crate version `0.8.64`, verified identical under `zerocopy/` against upstream `main` `e86eb0281380bdc278f4b4b3788dc9525ef59035`):**
  - Covers `zerocopy::KnownLayout`, `zerocopy::PointerMetadata`, `zerocopy::DstLayout`, `zerocopy::TrailingSliceLayout`, `RoundingAlignAndPhase`, `max_trailing_bytes`, `size_for_elems`, `validate_cast_and_convert_metadata`, and `is_valid_metadata` compiled directly with `rustc --edition 2021` + `CARGO_PKG_VERSION=0.8.64`.
- **Anneal Trusted MIR specification (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - At `c131b320`, `Trusted.MirAst.MirTy` (`trusted/lean/Trusted/MirAst.lean:312-321`) classifies unsized pointees (`Slice`, `Str`, `Dynamic`) as `.unsupported`, and `Trusted.MirSemantics.evalBinOp` (`trusted/lean/Trusted/MirSemantics.lean:1111-1160`) and `evalUnOp` (`1177-1193`) fail closed with `.error .unsupported` on pointer/metadata operands (`| _, _ => .error .unsupported`). The formalization and empirical bounds in this report define the exact compiler and library semantics required when extending verified MIR models to cover wide pointers, trait object metadata, custom DSTs, or `KnownLayout` contracts.
- **Lean 4 kernel formalization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, `support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean`):**
  - Self-contained core-Lean (`Init` only) formalization under namespace `VerifiedRustc.WidePtrDstKnownLayout`. All theorems establish mathematical identities and separation witnesses for exact idealized definitions matching the audited `rustc` and `zerocopy` expressions (modeling-bridge correspondence between Lean definitions and Rust ASTs is argued by source quotation below, not mechanized via `rustc` AST extraction).

---

## Findings

### 1. Wide-Pointer `ptr::eq` vs. `ptr::addr_eq`: Core Definitions and MIR/LLVM Lowering

`Basis: normative + source + execution (library/core/src/ptr/mod.rs, compiler/rustc_codegen_ssa/src/mir/rvalue.rs, support/probe_wide_ptr_dst_size_of_val.py)`

In `library/core/src/ptr/mod.rs` (`277240238554297f93fa9ee3c7643dfa03ccbbb4`), `core::ptr::eq` and `core::ptr::addr_eq` differ solely in whether pointer metadata survives into equality:

```rust
// library/core/src/ptr/mod.rs:2515-2517
#[stable(feature = "ptr_eq", since = "1.17.0")]
#[inline(always)]
#[must_use = "pointer comparison produces a value"]
#[rustc_diagnostic_item = "ptr_eq"]
#[allow(ambiguous_wide_pointer_comparisons)] // it's actually clear here
pub fn eq<T: PointeeSized>(a: *const T, b: *const T) -> bool {
    a == b
}

// library/core/src/ptr/mod.rs:2539-2541
#[stable(feature = "ptr_addr_eq", since = "1.76.0")]
#[inline(always)]
#[must_use = "pointer comparison produces a value"]
pub fn addr_eq<T: PointeeSized, U: PointeeSized>(p: *const T, q: *const U) -> bool {
    (p as *const ()) == (q as *const ())
}
```

When `a == b` or `a != b` is evaluated on wide pointers (`OperandValue::Pair(addr, extra)` in `compiler/rustc_codegen_ssa/src/mir/rvalue.rs`, dispatched at lines `673-688` at `main` `27724023`), SSA codegen compares **both** the thin data address and the metadata word (`usize` element count for `[T]` / `str`, or `*const VTable` pointer for `dyn Trait`):

```rust
// compiler/rustc_codegen_ssa/src/mir/rvalue.rs:897-917 (at 14210df0e)
// Identical logic at lines 1007-1027 on main (27724023)
fn codegen_wide_ptr_binop(
    &mut self,
    bx: &mut Bx,
    op: mir::BinOp,
    lhs_addr: Bx::Value,
    lhs_extra: Bx::Value,
    rhs_addr: Bx::Value,
    rhs_extra: Bx::Value,
    _input_ty: Ty<'tcx>,
) -> Bx::Value {
    match op {
        mir::BinOp::Eq => {
            let lhs = bx.icmp(IntPredicate::IntEQ, lhs_addr, rhs_addr);
            let rhs = bx.icmp(IntPredicate::IntEQ, lhs_extra, rhs_extra);
            bx.and(lhs, rhs)
        }
        mir::BinOp::Ne => {
            let lhs = bx.icmp(IntPredicate::IntNE, lhs_addr, rhs_addr);
            let rhs = bx.icmp(IntPredicate::IntNE, lhs_extra, rhs_extra);
            bx.or(lhs, rhs)
        }
        ...
```

Conversely, `(p as *const ()) == (q as *const ())` performs a MIR `CastKind::PointerCoercion(PointerCoercion::Unsize | ...)` / thin-cast (`Scalar`), discarding `lhs_extra` and `rhs_extra` before emitting `mir::BinOp::Eq` on thin `*const ()` operands (`codegen_scalar_binop`, single `icmp eq`). Compiling the 5 minimal comparison functions in [`support/probe_wide_ptr_dst_size_of_val.py`](support/probe_wide_ptr_dst_size_of_val.py) with `rustc --edition 2024 -Copt-level=2 --emit=llvm-ir` (`14210df0e`, LLVM `22.1.6`) confirms this exact IR:

```llvm
define noundef zeroext i1 @cmp_dyn_addr_eq(
    ptr noundef readnone captures(address) %a.0,
    ptr noalias noundef readonly align 8 captures(none) dereferenceable(32) %a.1,
    ptr noundef readnone captures(address) %b.0,
    ptr noalias noundef readonly align 8 captures(none) dereferenceable(32) %b.1) unnamed_addr #0 {
start:
  %_0 = icmp eq ptr %a.0, %b.0
  ret i1 %_0
}

define noundef zeroext i1 @cmp_dyn_ptr_eq(
    ptr noundef readnone captures(address) %a.0,
    ptr noalias noundef readonly align 8 captures(address) dereferenceable(32) %a.1,
    ptr noundef readnone captures(address) %b.0,
    ptr noalias noundef readonly align 8 captures(address) dereferenceable(32) %b.1) unnamed_addr #0 {
start:
  %0 = icmp eq ptr %a.0, %b.0
  %1 = icmp eq ptr %a.1, %b.1
  %_0 = and i1 %0, %1
  ret i1 %_0
}

define noundef zeroext i1 @cmp_dyn_ptr_ne(
    ptr noundef readnone captures(address) %a.0,
    ptr noalias noundef readonly align 8 captures(address) dereferenceable(32) %a.1,
    ptr noundef readnone captures(address) %b.0,
    ptr noalias noundef readonly align 8 captures(address) dereferenceable(32) %b.1) unnamed_addr #0 {
start:
  %0 = icmp ne ptr %a.0, %b.0
  %1 = icmp ne ptr %a.1, %b.1
  %_0 = or i1 %0, %1
  ret i1 %_0
}

define noundef zeroext i1 @cmp_slice_addr_eq(
    ptr noundef readnone captures(address) %a.0, i64 noundef %a.1,
    ptr noundef readnone captures(address) %b.0, i64 noundef %b.1) unnamed_addr #0 {
start:
  %_0 = icmp eq ptr %a.0, %b.0
  ret i1 %_0
}

define noundef zeroext i1 @cmp_slice_ptr_eq(
    ptr noundef readnone captures(address) %a.0, i64 noundef %a.1,
    ptr noundef readnone captures(address) %b.0, i64 noundef %b.1) unnamed_addr #0 {
start:
  %0 = icmp eq ptr %a.0, %b.0
  %1 = icmp eq i64 %a.1, %b.1
  %_0 = and i1 %0, %1
  ret i1 %_0
}
```

Notice two telling parameter-capture details emitted by LLVM 22.1.6:
- In `@cmp_dyn_addr_eq`, the vtable pointers `%a.1` and `%b.1` carry `captures(none)` because `ptr::addr_eq` discards them completely, whereas `@cmp_dyn_ptr_eq` and `@cmp_dyn_ptr_ne` mark `%a.1` and `%b.1` with **`captures(address)`** because `icmp eq/ne ptr` observes their pointer bit-patterns.
- `#[allow(ambiguous_wide_pointer_comparisons)]` suppresses the compiler lint on `a == b` (`ptr::eq`), whereas unannotated `a != b` (`cmp_dyn_ptr_ne`) emits `warning: ambiguous wide pointer comparison, the comparison includes metadata which may not be expected` suggesting `!std::ptr::addr_eq(a, b)`.

---

### 2. Why `ptr::eq` on `&dyn Trait` Pointers Diverges Between Native LLVM Execution and Miri

`Basis: documentation + source + execution (library/core/src/ptr/metadata.rs, compiler/rustc_codegen_ssa/src/meth.rs, compiler/rustc_codegen_llvm/src/consts.rs, compiler/rustc_const_eval/src/interpret/{cast.rs, traits.rs}, src/tools/miri/src/{machine.rs, operator.rs}, support/probe_results.json)`

Comparing two `*const dyn Trait` pointers via `ptr::eq` calls `DynMetadata::PartialEq`, which explicitly warns that vtable pointer equality is **neither reflexive across coercions nor injective across types** (`library/core/src/ptr/metadata.rs:155-158` at `27724023`):

> "Note that while this type implements `PartialEq`, comparing vtable pointers is unreliable: pointers to vtables of the same type for the same trait can compare inequal (because vtables are duplicated in multiple codegen units), and pointers to vtables of *different* types/traits can compare equal (since identical vtables can be deduplicated within a codegen unit)."

Live execution of the same binary (`WIDE_PTR_PROBE_RS` in [`support/probe_wide_ptr_dst_size_of_val.py`](support/probe_wide_ptr_dst_size_of_val.py)) under native `rustc` (`-Copt-level=0`) versus `cargo +nightly miri run --offline` (`support/probe_results.json`) produces the exact divergences summarized in Table 1:

| Probe Flag | Expression Under Test | Native (`rustc` `-O0`) | Miri (`cargo +nightly miri`) | Mechanism Responsible |
| :--- | :--- | :--- | :--- | :--- |
| `SLICE_ADDR_EQ` | `ptr::addr_eq(&arr[..2], &arr[..3])` | `true` | `true` | Identical base address; metadata `2 != 3` stripped (`*const ()`). |
| `SLICE_EQ_DIFF` | `ptr::eq(&arr[..2], &arr[..3])` | `false` | `false` | Equal address, unequal slice lengths (`2 != 3`). |
| `SLICE_EQ_SAME` | `ptr::eq(&arr[..3], &arr[..3])` | `true` | `true` | Equal address and deterministic length metadata (`3 == 3`). |
| `SLICE_OFF_ADDR_EQ` | `ptr::addr_eq(&arr[..2], &arr[1..3])` | `false` | `false` | Distinct base addresses (`+0 != +1`). |
| `SLICE_OFF_EQ` | `ptr::eq(&arr[..2], &arr[1..3])` | `false` | `false` | Equal length `2`, unequal base address. |
| `SLICE_THIN_CAST_EQ` | `(&arr[..2] as *const ()) == (&arr[..3] as *const ())` | `true` | `true` | Normative definition of `ptr::addr_eq`. |
| `DYN_ADDR_EQ` | `ptr::addr_eq(to_dyn_a(&obj), &obj.inner as &dyn Tr)` | `true` | `true` | `#[repr(C)] Outer` starts at offset 0 field `inner: Inner`. |
| `DYN_EQ_DIFF_VTABLE` | `ptr::eq(to_dyn_a(&obj), &obj.inner as &dyn Tr)` | `false` | `false` | Same base address, distinct concrete types (`Outer` vs `Inner`, different `size=2` vs `1` and `tag` fn). |
| `DYN_EQ_SAME_VTABLE` | `ptr::eq(to_dyn_a(&obj), to_dyn_b(&obj))` | **`true`** | **`false`** (`0/16` seeds true) | **Single-CGU native cache vs. Miri salted `AllocId`!** |
| `DYN_EQ_COPIED` | `let dp_copy = dp_a; ptr::eq(dp_a, dp_copy)` | `true` | `true` | Copy reproduces identical `(addr, vtable_alloc_id)` scalar pair. |
| `DYN_EQ_UPCAST` | `ptr::eq(to_dyn_a(&obj), upcast_to_dyn(&obj))` | **`false`** | **`false`** | Direct `dyn Tr` vtable vs. `dyn SubTr` prefix reuse (`cast.rs:496-500`) natively / distinct salt in Miri! |
| `DIFF_TYPES_ADDR_EQ` | `ptr::addr_eq(pa: *const dyn Marker /*TyA*/, pb /*TyB*/)` | `true` | `true` | Both fields inside `#[repr(C)] union SameAddrPair` at offset `0`. |
| `DIFF_TYPES_PTR_EQ` | `ptr::eq(pa: *const dyn Marker /*TyA*/, pb /*TyB*/)` | **`true`** | **`false`** | Identical `[null, 1, 1]` vtable allocation coalesced by native `const_globals`; separated by Miri RNG salt! |

Why each divergence occurs follows directly from the upstream source:

1. **Native Single-CGU Caching & Content-Based Deduplication (`DYN_EQ_SAME_VTABLE=true`, `DIFF_TYPES_PTR_EQ=true`):**
   - In `compiler/rustc_codegen_ssa/src/meth.rs:145-175` (`get_vtable`), codegen checks `cx.vtables().borrow().get(&(self_ty, trait_ref))`, ensuring all coercions of the same `(self_ty, trait_ref)` within one CGU reuse the same `Value<'ll>`.
   - Furthermore, on a miss, `get_vtable` resolves `vtable_allocation = tcx.global_alloc(tcx.vtable_allocation((self_ty, trait_ref))).unwrap_memory()` and calls `cx.static_addr_of(vtable_allocation, Some("vtable"))`. In `compiler/rustc_codegen_llvm/src/consts.rs:323-345` (`static_addr_of_impl`), `CodegenCx` interns by **LLVM constant value `cv`** (`self.const_globals.borrow().get(&cv)`), emitting `PrivateLinkage` + `UnnamedAddr::Global` (`313, 316`).
   - Crucially, in `compiler/rustc_middle/src/ty/vtable.rs:123-135` (`vtable_allocation_provider`), when `!ty.needs_drop(...)`, `MetadataDropInPlace` writes a null pointer rather than a per-type drop-glue shim (`Scalar::from_maybe_pointer(Pointer::null(), &tcx)`):
     ```rust
     // compiler/rustc_middle/src/ty/vtable.rs:123-134
     VtblEntry::MetadataDropInPlace => {
         if ty.needs_drop(tcx, ty::TypingEnv::fully_monomorphized()) {
             let instance = ty::Instance::resolve_drop_glue(tcx, ty);
             let fn_alloc_id = tcx.reserve_and_set_fn_alloc(instance, CTFE_ALLOC_SALT);
             let fn_ptr = Pointer::from(fn_alloc_id);
             Scalar::from_pointer(fn_ptr, &tcx)
         } else {
             Scalar::from_maybe_pointer(Pointer::null(), &tcx)
         }
     }
     VtblEntry::MetadataSize => Scalar::from_uint(size, ptr_size),
     VtblEntry::MetadataAlign => Scalar::from_uint(align, ptr_size),
     ```
     Because both `#[repr(C)] struct TyA(u8)` and `#[repr(C)] struct TyB(u8)` satisfy `!needs_drop`, `size = 1`, `align = 1`, and have zero `Marker` trait methods, both produce byte-for-byte identical `[null, 1, 1]` `ConstAllocation` bytes and identical LLVM constant structs `cv`. Consequently `static_addr_of_impl` returns the exact same global variable `gv` from `self.const_globals` even at `-Copt-level=0`, making `DIFF_TYPES_PTR_EQ=true` natively! Across multiple CGUs, `PrivateLinkage` emits duplicate private globals in separate object files, causing the opposite failure (`DYN_EQ_SAME_VTABLE == false` natively in multi-CGU or shared-library builds).

2. **Why `DYN_EQ_UPCAST` Is `false` Even Natively:**
   - In `to_dyn_a(&obj)`, the coercion creates a 4-entry `dyn Tr` vtable `[null, 2, 1, Outer::tag]`.
   - In `upcast_to_dyn(&obj)`, `&obj` is first coerced to `&dyn SubTr`, generating a 5-entry `dyn SubTr` vtable `[null, 2, 1, Outer::tag, Outer::extra]`, and then upcast `&dyn SubTr -> &dyn Tr`.
   - As documented in `compiler/rustc_const_eval/src/interpret/cast.rs:495-501`:
     > `// In this case codegen would keep using the old vtable. We don't want to do`
     > `// that as it has the wrong trait. The reason codegen can do this is that`
     > `// one vtable is a prefix of the other, so we double-check that.`
   - Because SSA codegen keeps the longer `dyn SubTr` vtable allocation pointer (`supertrait_vtable_slot == None`, prefix reuse) rather than replacing it with `dyn Tr`'s standalone 4-entry vtable allocation, `dp_a.1` points to `[null, 2, 1, tag]` while `dp_upcast.1` points to `[null, 2, 1, tag, extra]`, so `ptr::eq(dp_a, dp_upcast)` is deterministically `false` even inside a single CGU at `-O0`!

3. **Why Miri Produces `DYN_EQ_SAME_VTABLE=false` Across Seeds (`0/16` in `0..=15`):**
   - On every `SizeToDyn` or `DynToDyn` coercion (`compiler/rustc_const_eval/src/interpret/cast.rs:457-513`), Miri calls `self.get_vtable_ptr(...)` (`compiler/rustc_const_eval/src/interpret/traits.rs:19-36`):
     ```rust
     // compiler/rustc_const_eval/src/interpret/traits.rs:32-35
     let salt = M::get_global_alloc_salt(self, None);
     let vtable_symbolic_allocation = self.tcx.reserve_and_set_vtable_alloc(ty, dyn_ty, salt);
     let vtable_ptr = self.global_root_pointer(Pointer::from(vtable_symbolic_allocation))?;
     interp_ok(vtable_ptr.into())
     ```
   - `AllocMap::dedup` (`compiler/rustc_middle/src/mir/interpret/mod.rs:425`) keys on `(GlobalAlloc::VTable(ty, dyn_ty), salt)` (`500-507`), whereas CTFE uses constant `CTFE_ALLOC_SALT = 0` (`409`).
   - In Miri (`src/tools/miri/src/machine.rs:60, 2058-2097`), because `instance` is `None`:
     ```rust
     const ADDRS_PER_ANON_GLOBAL: usize = 32;
     ...
     } else {
         // Non-functions are never unique.
         false
     };
     if unique {
         CTFE_ALLOC_SALT
     } else {
         ecx.machine.rng.borrow_mut().random_range(0..ADDRS_PER_ANON_GLOBAL)
     }
     ```
   - Whenever two coercions `to_dyn_a(&obj)` and `to_dyn_b(&obj)` draw different salts $s_1 \neq s_2 \in \{0,\dots,31\}$ (probability $31/32 = 96.875\%$ per independent pair; $0/16$ equal across `-Zmiri-seed=0..15`), Miri assigns distinct `AllocId`s and distinct non-overlapping base addresses (`alloc_addresses.rs:198-221`). Miri's `binary_ptr_op` (`src/tools/miri/src/operator.rs:25-50`) then compares `(lhs_addr_bits, lhs_vptr_bits) == (rhs_addr_bits, rhs_vptr_bits)`, returning `false`. Copying an existing fat pointer (`dp_copy = dp_a`) preserves the exact salted `AllocId`, keeping `DYN_EQ_COPIED=true`.

---

### 3. Dynamic Custom-DST `size_of_val` / `align_of_val` Lowering and Bitmask Equivalence

`Basis: source + execution + Lean kernel proof (compiler/rustc_codegen_ssa/src/{size_of_val.rs, meth.rs}, compiler/rustc_middle/src/ty/vtable.rs, support/probe_wide_ptr_dst_size_of_val.py, support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean)`

In `compiler/rustc_codegen_ssa/src/size_of_val.rs` (`14-185` at `main` `27724023`; `15-184` at `14210df0e`), `size_and_align_of_dst` recursively lowers `size_of_val` / `align_of_val` along the `TyKind` spine:

1. **Trait object tail (`ty::Dynamic`):** Loads `usize` slots from the vtable pointer at `COMMON_VTABLE_ENTRIES_SIZE = 1` (byte offset `+8` on 64-bit) and `COMMON_VTABLE_ENTRIES_ALIGN = 2` (byte offset `+16` on 64-bit) (`vtable.rs:49-51`, `meth.rs:20-42, 105-112`), attaching `!invariant.load` and `!range` metadata (`0..=isize::MAX` for size, `1..=Align::max_for_target` for align; `size_of_val.rs:28-45`).
2. **Slice / `str` tail (`ty::Slice(_) | ty::Str`):** Multiplies element count metadata by `unit.size.bytes()` (`unchecked_sumul`) and returns constant `unit.align.bytes()` (`46-56`).
3. **Custom ADT / tuple DST (`ty::Adt(..) | ty::Tuple(..)`):** Reads statically computed `unsized_offset_unadjusted = layout.fields.offset(i).bytes()` and `sized_align = layout.align.bytes()`, recurses on trailing field `i = layout.fields.count() - 1` to get `(unsized_size, unsized_align)`, optionally caps `unsized_align = min(unsized_align, packed)` if `def.repr().pack == Some(packed)` (`1` directly when `packed == 1`, `icmp ult` + `select` otherwise, `115-128`), computes `full_align = max(sized_align, unsized_align)` (`umax`, statically folded when constant, `132-145`), and computes the final object size via single-step bitmask rounding (`163-180`):
   $$\text{rustc\_size} = \bigl((\text{unsized\_offset\_unadjusted} + \text{unsized\_size}) + (\text{full\_align} - 1)\bigr) \mathbin{\&} (-\text{full\_align})$$

**Subtle Distinction: `layout.fields.offset(i)` Already Aligns Statically Known Slice Tails, Leaving Unaligned Offsets Only for `dyn Trait` (Static Align 1) and `#[repr(packed)]`:**

The `-Copt-level=2` LLVM IR emitted from `LLVM_CUSTOM_DST_IR_RS` (`support/probe_results.json:252-304`) demonstrates four structurally distinct cases:

1. **`Packet<[u32]>` (`header: u8, payload: [u32]`):** `rustc_abi` statically aligns the trailing `[u32]` field (`align=4`), so `unsized_offset_unadjusted = 4` and `sized_align = 4`:
   ```llvm
   define { i64, i64 } @packet_slice_u32_size_align(...) {
   start:
     %0 = shl nuw nsw i64 %p.1, 2
     %1 = add nuw i64 %0, 7        ; (4 + len*4) + (4 - 1) = len*4 + 7
     %_2 = and i64 %1, -4          ; & -4
     ...                           ; align = 4
   ```
   Wait: why is `u32_0` size equal to **`4`** rather than `1`? Because `Packet<[u32]>` has `sized_align = 4`, so `unsized_offset_unadjusted = 4` and `roundUp(4 + 0, 4) = 4`!

2. **`Packet<dyn Tr>` (`header: u8, payload: dyn Tr`):** `dyn Tr` has static alignment `1` in `rustc_abi` (dynamic alignment unknown statically), so `rustc_abi` computes `unsized_offset_unadjusted = 1` and `sized_align = 1`! Notice what LLVM does with `(1 + unsized_size + (unsized_align - 1)) & -unsized_align` — arithmetic cancellation of `1 + (-1)` simplifies the entire expression to **`(align + size) & -align`**:
   ```llvm
   define { i64, i64 } @packet_dyn_size_align(
       ptr noundef nonnull readnone captures(none) %p.0,
       ptr noalias noundef readonly align 8 captures(none) dereferenceable(32) %p.1) unnamed_addr #0 {
   start:
     %0 = getelementptr inbounds nuw i8, ptr %p.1, i64 8
     %1 = load i64, ptr %0, align 8, !range !4, !invariant.load !5
     %2 = getelementptr inbounds nuw i8, ptr %p.1, i64 16
     %3 = load i64, ptr %2, align 8, !range !6, !invariant.load !5
     %4 = add nuw i64 %3, %1       ; align + size  (from 1 + size + (align - 1)!)
     %5 = sub nsw i64 0, %3        ; -align
     %_2 = and i64 %4, %5          ; (align + size) & -align
     %6 = insertvalue { i64, i64 } poison, i64 %_2, 0
     %7 = insertvalue { i64, i64 } %6, i64 %3, 1
     ret { i64, i64 } %7
   }
   ```
   For `DYN_SMALL` (`u8`: `size=1, align=1`), `(1 + 1) & -1 = 2`, returning `(2, 1)`! For `DYN_BIG` (`Big16`: `size=16, align=16`), `(16 + 16) & -16 = 32`, returning `(32, 16)` (because offset `1` plus `15` bytes of inter-field padding equals `16`, plus `16` tail bytes = `32`)!

3. **`Header6<dyn Tr>` (`a: u32, b: u16, payload: dyn Tr`):** Here `unsized_offset_unadjusted = 6` and `sized_align = 4`, so `full_align = umax(align, 4)` and `6 + size + (full_align - 1)` folds to `size + 5 + full_align`:
   ```llvm
   define { i64, i64 } @header6_dyn_size_align(...) {
   start:
     %0 = getelementptr inbounds nuw i8, ptr %p.1, i64 8
     %1 = load i64, ptr %0, align 8, !range !4, !invariant.load !5
     %2 = getelementptr inbounds nuw i8, ptr %p.1, i64 16
     %3 = load i64, ptr %2, align 8, !range !6, !invariant.load !5
     %4 = tail call i64 @llvm.umax.i64(i64 %3, i64 4)
     %5 = add nuw i64 %1, 5
     %6 = add nuw i64 %5, %4
     %7 = sub nsw i64 0, %4
     %_2 = and i64 %6, %7
     ...
   ```
   Evaluating on `Big16` (`size=16, align=16`): `umax(16, 4) = 16`, `((16 + 5 + 16) & -16) = 37 & -16 = 32`, returning `(32, 16)`. Evaluating `Header6<[u8]>` with 3 `u8`s: `umax(1, 4) = 4`, `((6 + 3 + 3) & -4) = (12 & -4) = 12`, returning `(12, 4)`! Note carefully: for **`Header6<[u8]>` with 0 elements**, `rustc` computes `(6 + 0 + 3) & -4 = 8` (and `[u8]` already places `payload` at offset `6`, padded up to multiple of `4` -> `8`), matching `zerocopy`'s `H6_U8_0=Some(8)`!

4. **`Packed2Slice` (`#[repr(C, packed(2))] { header: u8, payload: [u32] }`):** `packed(2)` caps `[u32]`'s alignment to `min(4, 2) = 2` (`size_of_val.rs:124-126`). Thus `unsized_offset_unadjusted = 2`, `full_align = 2`, and `(2 + len*4 + 1) & -2 = 2 + len*4`, which LLVM constant-folds into bit-disjoint shift-or (`shl nuw nsw i64 %p.1, 2; or disjoint i64 %0, 2`), returning `(14, 2)` for `len = 3`!

| DST Specimen | Concrete Tail | Native `(size, align)` | Miri `(size, align)` | Lean `sizeAndAlignRustc` | `zerocopy::DstLayout` (`usize::MAX`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `Packet<[u32]>` | `[u32; 3]` | `(16, 4)` | `(16, 4)` | `(16, 4)` | `Some(16)` |
| `Packet<[u32]>` | `[u32; 0]` | `(4, 4)` | `(4, 4)` | `(4, 4)` | `Some(4)` |
| `Packet<[u8]>` | `[u8; 3]` | `(4, 1)` | `(4, 1)` | `(4, 1)` | `Some(4)` |
| `Packet<dyn Tr>` | `u8` (`1, 1`) | `(2, 1)` | `(2, 1)` | `(2, 1)` | n/a (trait object, non-slice) |
| `Packet<dyn Tr>` | `Big16` (`16, 16`) | `(32, 16)` | `(32, 16)` | `(32, 16)` | n/a (trait object, non-slice) |
| `Header6<[u8]>` | `[u8; 3]` | `(12, 4)` | `(12, 4)` | `(12, 4)` | `Some(12)` (`0` elems: `Some(8)`) |
| `Header6<dyn Tr>` | `Big16` (`16, 16`) | `(32, 16)` | `(32, 16)` | `(32, 16)` | n/a (trait object, non-slice) |
| `Packed2Slice` | `[u32; 3]` | `(14, 2)` | `(14, 2)` | `(14, 2)` | `Some(14)` |

Note a Rust language restriction encountered during live probe authoring (`E0277`): `#[repr(C, packed(2))]` on a **generic** `?Sized` struct `struct PackedDst<T: ?Sized>` is rejected by `rustc` because generic `?Sized` tails might require drop (`align` cannot be statically known safe for `Drop` alignment without `Copy`), whereas concrete `struct Packed2Slice { header: u8, payload: [u32] }` (`payload` has no drop glue) is accepted (`rustc_codegen_ssa/src/size_of_val.rs:116-128` handles this case).

**Why `rustc`'s Single-Step Formula Equals the Two-Step Formula:**
The comment in `size_of_val.rs:149-161` states cleanly why `rustc` avoids aligning `unsized_offset_unadjusted` dynamically before adding `unsized_size`:
1. Since `tail.align | tail.size` and `effTail = min(tail.align, packCap)` divides `tail.align` (all alignments are powers of 2!), we have `effTail | tail.size`. Adding a multiple of `effTail` commutes with `roundUp(_, effTail)`: `roundUp(offset + tail.size, effTail) = roundUp(offset, effTail) + tail.size`.
2. Since `effTail` and `prefixAlign` are powers of two, `effTail | max(prefixAlign, effTail) = fullAlign`. Alignment idempotence for divisible alignments gives `roundUp(roundUp(y, effTail), fullAlign) = roundUp(y, fullAlign)`.
Both steps together prove `sizeAndAlignRustc spec tail = sizeAndAlignTwoStep spec tail` universally (`Theorem sizeAndAlignRustc_eq_twoStep` in Lean).

---

### 4. `google/zerocopy` `KnownLayout` / `DstLayout` Arithmetic and `isize::MAX` Separation

`Basis: source + execution + Lean kernel proof (zerocopy/src/layout.rs, zerocopy/src/lib.rs, zerocopy/src/util/mod.rs, support/probe_wide_ptr_dst_size_of_val.py, support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean)`

In `google/zerocopy` `0.8.64` (`907b9175fee081872ec883ca4709e6ad922f8ed0` / `e86eb0281380bdc278f4b4b3788dc9525ef59035`), `DstLayout::SizeInfo::SliceDst(TrailingSliceLayout)` normalizes *any* nested `repr(C)`/`packed`/`align` leading structure plus a trailing slice `[Elem]` into four integers (`layout.rs:153-207`):
- `offset`: byte offset of the first trailing-slice element;
- `elem_size`: size of one slice element (`0` for ZSTs);
- `size_base`: fixed base bytes already rounded down so `size_align | size_base` (for completed layouts);
- `size_rounding_align_and_phase`: `RoundingAlignAndPhase(align | phase)` packing power-of-two `size_align` (`1 << ((POINTER_WIDTH_BITS - 1) - leading_zeros)`) and remainder `size_phase < size_align` (`layout.rs:65-148`).

For `elems` elements (`trailing_bytes = elems * elem_size`), the mathematical object size is:
$$\text{object\_size}(\text{trailing\_bytes}) = \text{size\_base} + \text{round\_up}(\text{size\_phase} + \text{trailing\_bytes}, \text{size\_align})$$

Two distinct methods enforce **two different upper bounds**:

1. **`KnownLayout::size_for_metadata` -> `TrailingSliceLayout::size_for_elems` (`lib.rs:870-872`, `layout.rs:252-341, 427-491`) enforces `usize::MAX` representability (`available_bytes = usize::MAX`), NOT `isize::MAX`:**
   - First computes `max_trailing_bytes(usize::MAX)`:
     - `rounded_phase = if size_phase == 0 { 0 } else { size_align.get() }`
     - `minimum_size = size_base.checked_add(rounded_phase)?`
     - `extra_bytes = available_bytes.checked_sub(minimum_size)?`
     - `aligned_bytes = round_down(extra_bytes, size_align)` (`util::round_down_to_next_multiple_of_alignment`, computing `extra_bytes & !(size_align - 1)`)
     - `initial_padding = rounded_phase - size_phase` (`< size_align`, bit-disjoint with `aligned_bytes`, so `aligned_bytes | initial_padding == aligned_bytes + initial_padding`)
   - Next checks `trailing_size = elem_size.checked_mul(elems)?` and rejects iff `trailing_size > max_trailing_bytes`. When accepted, computes `trailing_end.wrapping_add(padding_for_elems(elems))`, which cancels `size_base + round_up(size_phase + elems * elem_size, size_align) mod 2^W` without overflow (`layout.rs:360-491`).
   - Crucially (`lib.rs:848-851, 864`): `<[u8]>::size_for_metadata(usize::MAX)` returns `Some(usize::MAX)` (`18446744073709551615`), even though no Rust allocation may exceed `isize::MAX`!

2. **`KnownLayout::is_valid_metadata` -> `maximum_trailing_slice_len` (`lib.rs:904-906, 934-960`) enforces `DstLayout::MAX_SIZE = isize::MAX as usize` (`layout.rs:925`):**
   - For ZST tails (`elem_size == 0`), `MAX_LEN = usize::MAX` (because `mathObjSize t elems` ignores `elems` when `elem_size = 0`).
   - For non-ZST tails (`elem_size > 0`), `MAX_LEN` equals the `elems` returned by `DstLayout::validate_cast_and_convert_metadata(align, isize::MAX, CastType::Prefix)`, which internally calls `trailing.max_trailing_bytes(isize::MAX)` and divides by `elem_size` (`max_elems_for_bytes`, `layout.rs:1790-1835`). Note a subtle edge case visible in Lean theorem `zcIsValidMetadata_iff_le_isizeMax`: `maximum_trailing_slice_len` requires `min_size <= isize::MAX` even for ZST tails (`max_trailing_bytes(isize::MAX)`), ensuring the fixed header itself fits in `isize::MAX`.

Live probe output compiling `zerocopy` `0.8.64` (`probe_results.json:317-337`) verifies every regime:
- `<[u32]>::size_for_metadata(3) == Some(12)` == `mem::size_of_val(&arr[..])` (`ZC_U32_3=Some(12)`, `MEM_U32_3=12`), `size_of_val_raw(NonNull::from(&arr[..])) == Some(12)`.
- `<[u32]>::size_for_metadata(usize::MAX) == None` (`ZC_OVERFLOW=None`), `is_valid_metadata(3) == true`, `is_valid_metadata(usize::MAX) == false`.
- `<[u8]>::size_for_metadata(usize::MAX) == Some(18446744073709551615)` (`ZC_U8_USIZE_MAX`), while `is_valid_metadata(isize::MAX as usize) == true` (`VALID_U8_IMAX`) and `is_valid_metadata((isize::MAX as usize) + 1) == false` (`VALID_U8_OVER`).
- `<[()]>::is_valid_metadata(usize::MAX) == true` (`VALID_ZST_MAX=true`).
- Custom DST `DstLayout::for_repr_c_struct`: `PKT_U32_3=Some(16)`, `PKT_U32_0=Some(4)`, `PKT_U32_MAX=None`, `PKT_U8_3=Some(4)`, `H6_U8_3=Some(12)`, `H6_U8_0=Some(8)`, `PACKED2_U32_3=Some(14)` — 100% identical to native `mem::size_of_val`, Miri, and Lean normalization!

---

### 5. Kernel-Checked Lean 4 Formalization Architecture (`WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean`)

`Basis: execution (Lean kernel check) (support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean, leanprover/lean4 v4.34.1)`

The standalone 1,534-line Lean 4 module `VerifiedRustc.WidePtrDstKnownLayout` in [`support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean`](support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean) compiles with core `Init` only (no Mathlib), `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, and satisfies strict MetaM hygiene: **170 theorems**, **137 `noncomputable def`s**, **7 inductive/structure types**, **`0` `._unsafe_rec` constants**, **`0` `Classical.choice`**, **`0` `sorryAx`**, **`0` `omega`/`bv_decide`/`native_decide`**, **`0` `partial def`**, and **`0` `deriving` clauses** (only `propext` and `Quot.sound` appear in theorem axioms). Notice that in `leanprover/lean4:v4.34.1`, standard core library lemmas `Nat.pow_lt_pow_right`, `Nat.testBit_two_pow_sub_one`, and `BEq.rfl` / `beq_self_eq_true` for `Nat` transitively reference `Classical.choice`; the formalization constructs pure alternatives `pow2_lt_of_lt`, `testBit_two_pow_sub_one_pure`, `Nat.beq`, and `nat_beq_false_of_ne` so the entire file stays 100% constructive modulo `{propext, Quot.sound}`.

Table 2 documents every section, key definitions, and principal theorems verified by the kernel:

| Section | Modeled Subsystem | Principal Definitions | Key Proved Theorems & Separation Witnesses |
| :--- | :--- | :--- | :--- |
| **§1 (L17–349)** | Pure `Nat` power-of-two divisibility & alignment algebra | `isPow2`, `paddingNeeded`, `alignToNat`, `roundUpNat`, `roundDownNat`, `isLeastAlignedGe` | `pow2_lt_of_lt`, `min_pow2_dvd_{left,right}`, `{left,right}_dvd_max_pow2`, `roundUpNat_isLeast`, `roundUpNat_eq_alignToNat`, `roundUpNat_add_of_dvd`, `roundUpNat_idem_of_dvd`, `roundUpNat_eq_self_plus_pad_le` |
| **§2 (L350–508)** | Fixed-width `BitVec w` LLVM bitmask identities | `llvmRoundDownBV`, `llvmAlignUpBV`, `testBit_two_pow_sub_one_pure` | `nat_land_neg_two_pow_eq_roundDown`, `llvmRoundDownBV_eq_roundDownNat`, `llvmAlignUpBV_eq_roundUpNat`, `llvmAlignUpBV_unit_offset` (`(1 + x + (2^k - 1)) &&& (-2^k) = (2^k + x) &&& (-2^k)`), `llvmAlignUpBV_wraps_on_overflow` |
| **§3 (L509–722)** | Wide pointers, `ptr::eq` vs. `ptr::addr_eq`, vtable salt oracles | `PtrMeta`, `WidePtr`, `metaEq`, `ptrEq`, `ptrNe`, `addrEq`, `VtableAllocOracle`, `coerceToDyn`, `sameObjSaltInvariant`, `vtableDivergesOnSalts` | `ptrEq_implies_addrEq`, `ptrNe_eq_not_ptrEq`, `addrEq_eq_ptrEq_on_thin`, `slice_addrEq_not_implies_ptrEq`, `slice_same_len_ptrEq_iff_addrEq`, `addrEq_invariant_under_vtable_salts`, `ptrEq_true_when_salt_invariant`, `ptrEq_false_when_vtable_diverges`, `miri_salted_vtable_model_divergence_witness`, `native_cgu_vtable_dedup_false_positive_witness`, `trait_upcast_vtable_prefix_divergence_witness` |
| **§4 (L723–910)** | Custom DST `size_and_align_of_dst` equivalence & bitmasking | `DstTailMeta`, `CustomDstSpec`, `applyPackCap`, `effectiveTailAlign`, `fullDstAlign`, `sizeAndAlignRustc`, `sizeAndAlignTwoStep`, `sizeAndAlignRustcBV` | `effectiveTailAlign_isPow2`, `effectiveTailAlign_dvd_fullAlign`, `sizeAndAlignRustc_eq_twoStep`, `sizeAndAlignRustc_align_dvd_size`, `sizeAndAlignRustc_size_ge_sum`, `sizeAndAlignRustc_bitmask_eq`, plus all 8 `specimen_*` exact `rfl` checks (`pkt_u32_3`, `pkt_u32_0`, `pkt_u8_3`, `pkt_dyn_small`, `pkt_dyn_big`, `h6_u8_3`, `h6_dyn_big`, `packed2_u32_3`) |
| **§5 (L911–1416)** | `zerocopy` `KnownLayout` checked overflow & `isize::MAX` soundness | `usizeMax`, `isizeMax`, `checkedAddW`, `checkedSubW`, `checkedMulW`, `ZcTrailingSliceLayout`, `zcWellFormed`, `mathObjSize`, `zcMaxTrailingBytes`, `zcSizeForElems`, `zcMaxTrailingSliceLen`, `zcIsValidMetadata` | `isizeMax_lt_usizeMax`, `zcRoundedPhase_eq_roundUp`, `roundUpNat_phase_plus_bytes_le_iff`, `zcMaxTrailingBytes_some_spec`, `zcMaxTrailingBytes_none_spec`, `zcSizeForElems_some_iff`, `zcSizeForElems_none_iff`, `zcIsValidMetadata_iff_le_isizeMax`, `zcIsValidMetadata_implies_sizeForElems_some`, `zc_u8_usize_max_size_some_but_invalid_witness`, `zc_u32_3_and_overflow_witness`, `zc_zst_usize_max_valid_witness`, `zc_custom_dst_specimens` |
| **§6 (L1417–1534)** | Normalized bridge: `rustc` custom DST $\leftrightarrow$ `zerocopy` `DstLayout` | `normalizeCustomDstToZc` (`base = roundDownNat unadjOff fullA`, `phase = unadjOff % fullA`) | `normalizeCustomDstToZc_wellFormed`, `normalizeCustomDstToZc_math_equiv_rustc`, `normalizeCustomDstToZc_zcSizeForElems_eq_rustc`, `normalize_h6_u8_eq_zcH6U8`, `normalize_pkt_u32_eq_zcPktU32`, `normalize_packed2_u32_eq_zcPacked2U32` |

Three proof mechanics inside the Lean formalization deserve highlighting for reuse:
- **Unit-Offset Cancellation (`llvmAlignUpBV_unit_offset`):** Captures LLVM's algebraic rewrite of `Packet<dyn Tr>` (`add(align, size) & -align`): when `unsized_offset_unadjusted = 1` and no `w`-bit wrap occurs (`1 + sz.toNat + (2^k - 1) < 2^w`), `(1 + sz + (2^k - 1)) &&& (-2^k)` equals `((2^k + sz) &&& (-2^k))` identically in `BitVec w.toNat`.
- **Two-Step Equivalence Side Conditions (`sizeAndAlignRustc_eq_twoStep`):** Requires *only* power-of-two `prefixAlign`, power-of-two `tail.align`, power-of-two `packCap` (if `some`), and `tail.align | tail.size`. Under those invariants, `applyPackCap tail.align packCap` divides `tail.align` and therefore divides `tail.size`, allowing `(offset + tail.size)` inside `roundUp` to commute with `alignTo offset effTail`.
- **Exact Separation Between `size_for_elems` and `is_valid_metadata`:** Theorem `zcSizeForElems_some_iff` proves `zcSizeForElems w t elems = some s ↔ mathObjSize t elems ≤ usizeMax w ∧ s = mathObjSize t elems`, whereas `zcIsValidMetadata_iff_le_isizeMax` proves `zcIsValidMetadata w t elems = true ↔ mathObjSize t elems ≤ isizeMax w`, paired with concrete 64-bit counterexample `zc_u8_usize_max_size_some_but_invalid_witness` where `size_for_elems` returns `some (2^64 - 1)` while `is_valid_metadata` returns `false`.

---

## Boundaries

The following negative space defines where the findings, probe results, and Lean proofs **do not** apply:

1. **Multi-CGU, LTO, and Function Pointer Comparisons (partially not examined / known not to guarantee equality):**
   - `SLICE_*` / `DYN_*` probes executed inside one compilation unit (`rustc --edition 2024`). Multi-CGU native builds, Fat/Thin LTO across crates, dynamically loaded DSOs (`dlopen`), or identical-code-folding (ICF) passes across distinct types with non-trivial methods were **not executed** natively here; upstream documentation in `library/core/src/ptr/metadata.rs:155-158` explicitly warns that vtables for the same `(T, dyn Trait)` *can* compare unequal across CGUs.
   - Similarly, `core::ptr::fn_addr_eq` / function pointer identity (`library/core/src/ptr/mod.rs:2543+`, `machine.rs:2062-2086`) has its own separate non-uniqueness rule in Miri (`is_generic || can_be_inlined`, preserving monotonic identity for non-inline backtrace frames) and was **not parameterized** inside `VtableAllocOracle`.

2. **Target Bit Widths, Pointer Authentication, and Nested-Packed Generic DSTs (unsupported / not examined):**
   - Executed Rust/LLVM/Miri measurements target `x86_64-unknown-linux-gnu` (64-bit, `usize = u64`, `isize::MAX = 2^63 - 1`) only; 32-bit, 16-bit, CHERI capability targets, and ARMv8.3 PAC/pointer-signing targets (where vtable or data pointers carry extra metadata or PAC bits) were **not examined**.
   - As verified empirically (`E0277`), generic `#[repr(C, packed(N))] struct Wrapper<T: ?Sized>` is **unsupported** in Rust when fields may need drop; `rustc`'s `packed` cap in `size_of_val.rs:116-128` applies to concrete `?Sized` tail fields lacking drop glue (like `Packed2Slice`) or non-`packed` outer structs containing nested packed structs.
   - `zerocopy::DstLayout` itself does **not** model `dyn Trait` object layout or `DynMetadata` (`KnownLayout::PointerMetadata` only supports `()` and `usize`, `lib.rs:761, 967-975`), so the Section 6 Lean normalization theorem `normalizeCustomDstToZc_math_equiv_rustc` applies specifically to **slice-DST** suffixes `[Elem]`, not trait-object `dyn Trait` tails (whose `(size, align)` are runtime vtable loads rather than affine `elems * elemSize` products).

3. **Unchecked Arithmetic Overflow vs. Soundness Assumption in `rustc` Runtime `size_of_val`:**
   - Theorem `sizeAndAlignRustc_bitmask_eq` requires explicit no-overflow hypotheses (`sum < 2^w` and `sum + (2^k - 1) < 2^w`), reflecting the Rust invariant that valid allocated objects fit in `isize::MAX`. As demonstrated by `llvmAlignUpBV_wraps_on_overflow`, if an unguarded bitmask `(x + (a - 1)) & -a` is invoked on a **raw dangling slice pointer** whose byte size exceeds `2^w - (a - 1)` (possible in safe construction of `*const [T]` via `ptr::slice_from_raw_parts`, though UB to dereference), `BitVec w` modular arithmetic wraps below `x`, whereas `zerocopy::TrailingSliceLayout::size_for_elems` fails closed with `None` (`zcSizeForElems_none_iff`).

4. **Lean Formalization Modeling Scope (model theorems vs. compiler extraction):**
   - `VerifiedRustc.WidePtrDstKnownLayout` proves equivalence over **direct Lean models** (`WidePtr`, `VtableAllocOracle`, `CustomDstSpec`, `ZcTrailingSliceLayout`). No tool automatically extracts MIR/LLVM/Rust ASTs from `rustc` or `google/zerocopy` into Lean, and `google/zerocopy`'s `DstLayout::MAX_SIZE` enforcement inside `KnownLayout::is_valid_metadata` was audited at source and executed on `x86_64`, while full generic trait derives (`#[derive(KnownLayout)]` macro expansion on nested enums/unions) remain outside the slice-layout normalization model.
   - In `joshlf/anneal` (`c131b320`), `Trusted.MirAst` and `Trusted.MirSemantics` currently fail closed with `.unsupported` on slice/trait/wide-pointer operations; connecting `WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean` directly to `Trusted.MirSemantics` remains future semantics-extension work.

---

## Evidence

All source revisions and commit SHAs below were resolved live against upstream repositories on `2026-11-23`.

### 1. Pinned Primary-Source Coordinates

- **`rust-lang/rust` (`main` `277240238554297f93fa9ee3c7643dfa03ccbbb4` & executed nightly `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
  - `library/core/src/ptr/mod.rs` (`27724023`, lines `2510-2541`): `core::ptr::eq` (`a == b`) and `core::ptr::addr_eq` (`(p as *const ()) == (q as *const ())`).
  - `library/core/src/ptr/metadata.rs` (`27724023`, lines `155-246`): `DynMetadata<Dyn>` layout/vtable documentation and `PartialEq` delegating to `ptr::eq::<VTable>`.
  - `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` (`27724023` lines `673-688, 1007-1027`; `14210df0e` lines `897-917`): `codegen_wide_ptr_binop` (`BinOp::Eq` as `icmp eq` + `and`, `BinOp::Ne` as `icmp ne` + `or`).
  - `compiler/rustc_codegen_ssa/src/size_of_val.rs` (`27724023` lines `14-185`; `14210df0e` lines `15-184`): `size_and_align_of_dst` (`ty::Dynamic` vtable loads, `ty::Slice | ty::Str` element product, `ty::Adt | ty::Tuple` packed capping, `max`, and `(full_size + (full_align - 1)) & -full_align`).
  - `compiler/rustc_codegen_ssa/src/meth.rs` (`27724023`, lines `19-42, 105-112, 145-175`): `VirtualIndex::get_usize` (`!invariant.load`) and `get_vtable` single-CGU cache `cx.vtables()`.
  - `compiler/rustc_codegen_llvm/src/consts.rs` (`27724023`, lines `296-345, 909-918`): `static_addr_of_mut` (`PrivateLinkage`, `UnnamedAddr::Global`) and `static_addr_of_impl` (`const_globals` content deduplication).
  - `compiler/rustc_middle/src/ty/vtable.rs` (`27724023`, lines `44-51`): `COMMON_VTABLE_ENTRIES_{DROPINPLACE,SIZE,ALIGN} = 0, 1, 2`.
  - `compiler/rustc_const_eval/src/interpret/traits.rs` (`27724023`, lines `19-36`): `get_vtable_ptr` calling `M::get_global_alloc_salt(self, None)` -> `reserve_and_set_vtable_alloc`.
  - `compiler/rustc_const_eval/src/interpret/cast.rs` (`27724023`, lines `457-506`): trait upcasting `data_a == data_b`, `supertrait_vtable_slot`, and vtable-prefix reuse comment (`495-501`).
  - `compiler/rustc_middle/src/mir/interpret/mod.rs` (`27724023`, lines `409, 425, 461-507`): `CTFE_ALLOC_SALT = 0`, `AllocMap::dedup`, `reserve_and_set_vtable_alloc`.
  - `src/tools/miri/src/machine.rs` (`27724023`, lines `60, 2058-2097`): `ADDRS_PER_ANON_GLOBAL = 32` and `get_global_alloc_salt` returning random salt when `instance == None`.
  - `src/tools/miri/src/alloc_addresses.rs` (`27724023`, lines `46, 108-222`): per-`AllocId` address assignment.
  - `src/tools/miri/src/operator.rs` (`27724023`, lines `13-50`): Miri `binary_ptr_op` comparing `Immediate::ScalarPair` bits lexicographically.
- **`google/zerocopy` (`0.8.64`, `907b9175fee081872ec883ca4709e6ad922f8ed0`, identical under `zerocopy/` vs. `main` `e86eb0281380bdc278f4b4b3788dc9525ef59035`):**
  - `zerocopy/src/layout.rs`: `RoundingAlignAndPhase` (`65-148`), `TrailingSliceLayout` (`153-207`), `max_trailing_bytes` (`252-341`), `padding_for_elems` (`360-415`), `size_for_elems` (`427-491`), `DstLayout::MAX_SIZE` (`925`), `for_slice` (`1098-1121`), `extend` (`1255-1377`), `pad_to_align` (`1395-1495`), `validate_cast_and_convert_metadata` (`1705-1840`).
  - `zerocopy/src/lib.rs`: `KnownLayout` (`748-907`), `size_of_val_raw` (`828-833`), `size_for_metadata` (`870-872`), `is_valid_metadata` (`904-906`), `maximum_trailing_slice_len` (`934-960`), `PointerMetadata` (`964-1079`).
  - `zerocopy/src/util/mod.rs`: `padding_needed_for` (`160-216`), `round_down_to_next_multiple_of_alignment` (`237-255`).
- **`joshlf/anneal` (`main` `c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - `trusted/lean/lean-toolchain` (`leanprover/lean4:v4.34.1`), `trusted/lean/Trusted/MirAst.lean` (`312-321, 400-409, 445-446`), and `trusted/lean/Trusted/MirSemantics.lean` (`550-557, 1111-1193`).

### 2. Preserved Package Artifacts (`support/`)

- [`support/probe_wide_ptr_dst_size_of_val.py`](support/probe_wide_ptr_dst_size_of_val.py): Self-contained Python 3 probe (using only standard library + `tempfile.TemporaryDirectory()`) executing native `rustc`, `cargo +nightly miri run --offline` (default + `-Zmiri-seed=0..15`), `-Copt-level=2 --emit=llvm-ir`, and compiled `zerocopy` (`CARGO_PKG_VERSION=0.8.64`, `--edition 2021`).
- [`support/probe_results.json`](support/probe_results.json): Captured JSON output from running the probe on `x86_64-unknown-linux-gnu` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `LLVM 22.1.6`, `miri 0.1.0 (14210df0e2 2026-05-31)`, `zerocopy 0.8.64 @ 907b9175fee081872ec883ca4709e6ad922f8ed0`) with path redaction (`<tmp>`, `<home>`). All internal assertions passed (`exit 0`).
- [`support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean`](support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean): 1,534-line, 70,328-byte standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel-checked formalization verified with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, zero warnings) and audited via Lean `MetaM` (`thms=170 defs=137 inds=7`, `0` `_unsafe_rec`, `0` `Classical.choice`, `0` `sorryAx`, `0` `ofReduceBool`).

---

## Revalidation

Each claim above admits cheap, standalone revalidation without repeating the full upstream source crawl:

1. **Rerun the Lean 4 Kernel Proof & Hygiene Checks (`< 5 s`):**
   ```bash
   LEAN_FILE=reports/rustc-wide-ptr-eq-vs-addr-eq-vtable-nondet-dst-size-of-val-and-zerocopy-known-layout/support/WidePtrEqDstSizeOfValAndKnownLayoutSoundness.lean
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true "$LEAN_FILE"
   grep -nE "\bsorry\b|\bomega\b|\bbv_decide\b|\bnative_decide\b|\bpartial\b|\bderiving\b|noncomputable section|Classical\.choice" "$LEAN_FILE" || true
   ```
2. **Rerun the Live `rustc` / Miri / LLVM IR / `zerocopy` Empirical Probe (`~15 s`):**
   ```bash
   python3 reports/rustc-wide-ptr-eq-vs-addr-eq-vtable-nondet-dst-size-of-val-and-zerocopy-known-layout/support/probe_wide_ptr_dst_size_of_val.py \
     --zerocopy-dir /path/to/zerocopy \
     --out /tmp/recheck_probe_results.json
   ```
   Pass if all script assertions succeed (`exit 0`), native `DYN_EQ_SAME_VTABLE=true` contrasts with Miri `DYN_EQ_SAME_VTABLE=false`, LLVM IR retains `(icmp eq) & (icmp eq)` on `ptr::eq` vs. single `icmp eq` on `ptr::addr_eq`, and `(size + align) & -align` / `zerocopy` `0.8.64` outputs match `support/probe_results.json`. (Pass without `--zerocopy-dir` to revalidate `rustc`/LLVM/Miri alone when a `zerocopy` checkout is absent.)
3. **Diff Narrow Upstream File Regions Before Relying on Future Toolchains / Crates:**
   - For `ptr::eq` / `ptr::addr_eq` and Miri vtable salting: diff `library/core/src/ptr/{mod.rs, metadata.rs}`, `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` (`codegen_wide_ptr_binop`), `compiler/rustc_const_eval/src/interpret/traits.rs` (`get_vtable_ptr`), and `src/tools/miri/src/machine.rs` (`get_global_alloc_salt`, `ADDRS_PER_ANON_GLOBAL`).
   - For custom-DST `size_of_val`: diff `compiler/rustc_codegen_ssa/src/size_of_val.rs` (`size_and_align_of_dst`) and `compiler/rustc_codegen_llvm/src/consts.rs` (`static_addr_of_impl`).
   - For `zerocopy::KnownLayout`: diff `zerocopy/src/layout.rs` (`max_trailing_bytes`, `size_for_elems`, `DstLayout::MAX_SIZE`, `validate_cast_and_convert_metadata`) and `zerocopy/src/lib.rs` (`KnownLayout::{size_for_metadata, is_valid_metadata}`, `maximum_trailing_slice_len`).
