# `rustc` MIR `UnOp::PtrMetadata`, `AggregateKind::RawPtr`, `GVN` Custom-DST Folding Asymmetry, `FakeForPtrMetadata`, and `BoxDerefTransmute`

## Summary

This report establishes primary-source (`rust-lang/rust`, `rust-lang/reference`, `joshlf/anneal`), empirical (`rustc` MIR/LLVM-IR + `cargo miri` under Stacked Borrows and Tree Borrows), and kernel-checked (`Lean v4.34.1`) ground truth for how `rustc` lowers, optimizes, interprets, and compiles wide-pointer metadata creation, extraction, bounds checking, struct-tail field projection, and `Box` dereference coercion:

1. **Intrinsic lowering (`LowerIntrinsics`) and canonical `AggregateKind::RawPtr` / `UnOp::PtrMetadata` representations (`lower_intrinsics.rs`, `lower_slice_len.rs`, `instsimplify.rs`, `validate.rs`, `ty/sty.rs`):** Both `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and `rust-lang/rust` HEAD (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) lower `core::intrinsics::aggregate_raw_ptr` and `ptr_metadata` in the `Required` pass `LowerIntrinsics` (`Runtime(Initial) -> Runtime(PostCleanup)`) into `Rvalue::Aggregate(AggregateKind::RawPtr(*pointee_ty, *mutability), [data, meta])` and `Rvalue::UnaryOp(UnOp::PtrMetadata, ptr)`, while `LowerSliceLenCalls` (`mir-opt-level >= 1`) converts direct `<[T]>::len` calls into `UnOp::PtrMetadata` (empirically increasing `ptr_metadata_ops` from `1` to `2` in `probe_a_array_to_slice` and `probe_c_nested_struct_unsize_ref` between `-Zmir-opt-level=0` and `=1`). Metadata type resolution (`ty/sty.rs`: `ptr_metadata_ty_or_tail`) recursively follows `tcx.struct_tail_raw` to yield `()` for sized/`Foreign`/empty-tail ADTs, `usize` for `[T]`/`str`, and `DynMetadata<dyn Trait>` for `ty::Dynamic`. When `meta_ty.is_unit()`, `InstSimplify` (`instsimplify.rs`) collapses `Aggregate(RawPtr(pointee, mut), [p, ()])` into `Cast(PtrToPtr, p, *const/*mut pointee)` (empirically reducing `raw_ptr_aggregates` from `1` to `0` and raising `ptr_to_ptr_casts` from `0` to `1` in `probe_d_from_raw_parts_roundtrip`). Notably, `MirValidator` (`validate.rs`) requires operand 0 of `AggregateKind::RawPtr` to be a sized raw pointer matching target mutability, yet explicitly enforces operand 1's type only for slices (`usize`) and sized types (`()`), leaving `str`, `dyn Trait`, and struct-tail custom DSTs (`ty::Adt`) unvalidated in MIR validation.
2. **`GVN` `UnOp::PtrMetadata` and `AggregateKind::RawPtr` folding asymmetry (`gvn.rs`):** `GVN` is *not* uniformly unable to fold custom-DST metadata; rather, it exhibits a sharp structural split:
   - `GVN::simplify_aggregate(AggregateKind::RawPtr)` unconditionally constructs `Value::RawPtr { pointer, metadata }` after peeling sized `PtrToPtr` casts on operand 0, and `GVN::simplify_unary(UnOp::PtrMetadata)` returns `metadata` for *any* `Value::RawPtr`—including nested struct-tail custom DSTs (`probe_d` folds `ptr::metadata(from_raw_parts::<Wrapper<[u8]>>(without_provenance(1), 9))` to `const 9_usize`).
   - By contrast, for `CastKind::PointerCoercion(Unsize)` (`GVN::simplify_unary`), `rustc` guards constant folding on direct top-level `ty::Array(_, len)` -> `ty::Slice(..)` (`probe_a` folds `ptr::metadata`, `s.len()`, and the bounds check to `const 4_usize`), leaving struct-tail custom-DST unsizes such as `&Wrapper<[u8; 3]> -> &Wrapper<[u8]>` (`probe_c_nested_struct_unsize_ref`, `probe_c_nested_struct_unsize_box`, `probe_e_fake_for_ptr_metadata_and_mut_raw_parts`) completely unfolded across `-Zmir-opt-level=0..2` and `GVN.after.mir`.
   - Furthermore, the peeling loop in `GVN::simplify_unary` crosses `Value::Address { base: AddressBase::Deref(reborrowed), projection }` **only if `projection.is_empty()`**, blocking `&raw const (fake) (((*wu).1: Inner<[u8]>).1: [u8])` even when `wu` originates from a constant-length unsize or `RawPtr` aggregate. Mechanized theorem `peelProj_unsound_without_live_ref_side_condition` proves that blindly relaxing the empty-projection guard on arbitrary raw pointers would silently delete `OffsetMode::Inbounds` UB at nonzero field offsets, whereas `extGvnUnsizeSimplify_sound` proves recursive struct-tail unsize folding (`Wrap_1<...Wrap_k<[T; N]>...>`) sound with zero preconditions on tail dereferenceability.
3. **Raw `ptr::metadata` memory independence vs. `OffsetMode::Inbounds` nonzero field projection vs. `FakeForPtrMetadata` (`operator.rs`, `interpret/place.rs`, `projection.rs`, `step.rs`, `as_place.rs`):** Direct `ptr::metadata(raw_wide_ptr)` operates purely on the `ScalarPair.1` metadata lane without reading heap bytes or checking data-pointer provenance, alignment, nullness, or allocation liveness. Differential `cargo miri` execution (`0.1.0 (14210df0e)` under both Stacked Borrows and `-Zmiri-tree-borrows`) confirms `PASS` (`rc = 0`) on null raw slices (`len = 42`), unaligned no-provenance `Wrapper<[u8]>` (`0x1[noalloc]`, `len = 99`), freed `Box<[u8]>` and `Box<dyn Summarize>` raw pointers (`DynMetadata` returning `(16, 8)`), and oversized raw `[u64]` (`len = usize::MAX`), whereas reborrowing `&*p` on any of those triggers immediate UB (`rc = 1`). Even for raw pointers, however, `&raw const (*p).inner.tail` (`l12`) fails both Stacked Borrows and Tree Borrows (`attempting to offset pointer by 2 bytes, but got 0x2[noalloc] which is a dangling pointer`) because MIR place projection invokes `OffsetMode::Inbounds` for `offset > 0` before yielding the inner slice. Simultaneously, MIR construction (`as_place.rs`) emits `&raw const (fake) ...` (`RawPtrKind::FakeForPtrMetadata`) for bounds checks on `&mut [T]` or projected slice places; Miri (`step.rs`) omits borrow-tag retagging when `kind.is_fake()`, allowing overlapping `&mut` calls inside slice indexing expressions (`s[mutate_slice(s)]`, `wu.inner.tail[mutate_wrap(wu)]`) in both Stacked Borrows and Tree Borrows (`l06`). Meanwhile, between `14210df0e` and `fde8dfd638`, CTFE/Miri's `UnOp::PtrMetadata` handler (`operator.rs`) added `self.deref_pointer(val)?`, which enforces full dereference validity for `&T`/`Box<T>`, validates `vtable` identity for raw `*const dyn Trait`, and explicitly performs no data check (`// Nothing to check`) for raw `[T]`/`str`/`Foreign`.
4. **`Box` deref elaboration (`Unique -> NonNull -> Transmute` vs. `BoxRaw -> BoxDerefTransmute`) and `rustc_codegen_ssa` layout/codegen (`elaborate_box_derefs.rs`, `interpret/cast.rs`, `mir/rvalue.rs`, `mir/place.rs`, `size_of_val.rs`):** In `rustc 1.98.0-nightly (14210df0e)`, `Box<T, A>` wraps `Unique<T>`, and `ElaborateBoxDerefs` emits a two-field projection plus generic `CastKind::Transmute` to `*const T`—empirically confirmed to exit `rc = 0` in Miri (`l14a_198_raw_box_deref_unaligned_transmute_gap`) when taking `&raw const (*b)` on an unaligned local `Box<Wrapper<[u8]>>`, whereas `&(*b)` (`l14b`) fails with alignment UB (`required 2 byte alignment but found 1`). At `rust-lang/rust` HEAD (`fde8dfd638`), `Box<T, A>` wraps `BoxRaw<T>`, `ElaborateBoxDerefs` emits one field projection plus `CastKind::BoxDerefTransmute`, and CTFE/Miri (`cast.rs:206-214`) reconstructs `Ty::new_box(*self.tcx, pointee_ty)` and calls `self.deref_pointer(&ptr)?` so `&raw const (*b)` catches unaligned/dangling `Box` UB immediately while `rustc_codegen_ssa` compiles `BoxDerefTransmute` via `codegen_transmute_operand` identically to `CastKind::Transmute`. During SSA codegen, `size_and_align_of_dst` and `PlaceRef::project_field` omit intermediate `.align_to(unsized_align)` on trailing fields while emitting dynamic offset rounding `(2 + len + 1) & -2` at `-C opt-level=0` for intermediate non-zero-offset custom-DST fields (`Inner<[u8]>` at offset `2` inside `Wrapper<[u8]>`). Lean theorem `sizeAndAlign_adjustedOffset_equiv_and_tail_inbounds` formally proves this algebraic alignment-absorption identity over arbitrary power-of-two alignments.
5. **Anneal (`joshlf/anneal@c131b320e`) trusted boundary:** `Trusted.MirAst` declares `UnOp.ptrMetadata` and `MirTy.rawPtr`, and `vendor/lean-miri` implements `UnOp.PtrMetadata` and `RawPtrKind.FakeForPtrMetadata`, yet `Trusted.MirAst.MirTy` lacks `array`/`slice`/`dynTrait`/`adt`, `Trusted.MirAst.Rvalue` lacks `Cast` and `AggregateKind::RawPtr`, `Trusted.MirSemantics.evalUnOp` rejects `.ptrMetadata` with `.error .unsupported`, and `trusted/rustc-capture/src/driver.rs` pins `1.98.0-nightly` (`f8a08b688`) with zero MIR extraction yet active—leaving wide pointers fail-closed.

---

## Applicability

This report documents the interaction and comparison among five immutable subjects recorded in `REPORT.json`:

1. **Live executed toolchain (`rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)`, LLVM `22.1.6`, `miri 0.1.0 (14210df0e2 2026-05-31)`, host `x86_64-unknown-linux-gnu`):** All empirical MIR dumps (`-Zdump-mir=all`, `--emit=mir -Zmir-opt-level=0..2`), LLVM IR (`--emit=llvm-ir` at `-C opt-level=0` and `-C opt-level=2`), native `-C opt-level=2` binary executions, CTFE evaluations, and `15/15` Miri differential litmus tests (Stacked Borrows and `-Zmiri-tree-borrows`) were executed directly against this toolchain (`2026-11-23`) using `--edition=2024` and `#![feature(core_intrinsics, ptr_metadata)]`. Installed `rustc-src` and `rust-src` trees at exact commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` were inspected directly alongside live execution.
2. **Upstream compiler source comparison (`rust-lang/rust` HEAD `fde8dfd638478da758f93f0e8d9b74d7907f0c9e`):** Direct source inspection of `compiler/rustc_{mir_transform,middle,mir_build,const_eval,codegen_ssa}` and `library/{core,alloc}` at `fde8dfd638` establishes which behaviors are shared verbatim with `14210df0e` (`LowerIntrinsics`, `LowerSliceLenCalls`, `InstSimplify`, `GVN` custom-DST/array asymmetry, `FakeForPtrMetadata`, `OffsetMode::Inbounds`, `rustc_codegen_ssa` `ScalarPair` and `size_of_val` codegen) and which evolved between `14210df0e` and `fde8dfd638` (`BoxRaw<T>` + `CastKind::BoxDerefTransmute`, and `UnOp::PtrMetadata` calling `self.deref_pointer(val)?` in CTFE/Miri).
3. **Normative language specification (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** Interprets wide pointer layout, valid wide-pointer metadata/vtable validity (`r[undefined.validity.wide]`), alignment rules (`r[undefined.misaligned.ptr]`), `Struct` unsized coercion (`r[coerce.unsized]`), and pointer-to-pointer casts against the compiler's MIR/CTFE/codegen implementation.
4. **Anneal verification boundary (`joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Maps `rustc` MIR semantics onto Anneal's TCB AST (`Trusted/MirAst.lean`), executable semantics (`Trusted/MirSemantics.lean`), correspondence proofs (`correspondence/Anneal/MirCorrespondenceBase.lean`, `trusted/correspondence/Trusted/Correspondence.lean`), vendored Lean-Miri (`vendor/lean-miri`), and pinned compiler driver (`trusted/rustc-capture/src/driver.rs`).
5. **Kernel-checked formalization (`leanprover/lean4` `v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`):** `support/MirPtrMetadataGvnCustomDstAndRawPtrSoundness.lean` (`1,832` lines, `49` proved theorems) mechanizes both the `v198LegacyTransmute` (`14210df0e`) and `vHeadBoxDerefTransmute` (`fde8dfd638`) semantic profiles over unbounded natural-number addresses, alignments, and recursive custom-DST pointees.

Where a claim applies strictly to one compiler revision or configuration (`14210df0e` vs. `fde8dfd638`, `-C opt-level=0` vs. `-C opt-level=2`, `-Zmir-opt-level=0..2`, Stacked Borrows vs. Tree Borrows, or raw pointer vs. `&T`/`Box<T>`), that qualification is preserved explicitly in each section. This report focuses specifically on `UnOp::PtrMetadata`, `AggregateKind::RawPtr`, `GVN` metadata folding, `FakeForPtrMetadata`, `BoxDerefTransmute`, and `PlaceRef::project_field` / `size_of_val` offset-rounding; it complements (and avoids duplicating) general `Unsize` field-sorting and `rustc_ty_utils::layout` coverage.

---

## Findings

### 1. Intrinsics, MIR Typing Rules, `LowerSliceLenCalls`, and `InstSimplify` Collapse

**Basis:** source (`rust-lang/rust@fde8dfd638`: `compiler/rustc_mir_transform/src/{lower_intrinsics.rs:315-358, lower_slice_len.rs:1-65, instsimplify.rs:168-182, validate.rs:1115-1155, 1261-1267}`, `compiler/rustc_middle/src/ty/sty.rs:1765-1865`; identical semantics at `rust-lang/rust@14210df0e`: `lower_intrinsics.rs:291-334`, `lower_slice_len.rs:1-67`, `instsimplify.rs:171-185`, `validate.rs:1097-1137, 1243-1249`, `ty/sty.rs:1733-1830`, `library/core/src/ptr/metadata.rs:27-173`) + execution (`rustc 1.98.0-nightly` MIR dumps on `probe_a..probe_e`).

#### Intrinsic Surface and `ptr_metadata_ty_or_tail` Typing

In `library/core/src/ptr/metadata.rs:100-140`, public pointer decomposition and reconstruction functions wrap two compiler intrinsics (`#[rustc_intrinsic]`):

- `core::ptr::metadata<T: ?Sized>(ptr: *const T) -> <T as Pointee>::Metadata` invokes `core::intrinsics::ptr_metadata(ptr)`.
- `core::ptr::from_raw_parts<T: ?Sized>(data_pointer: *const impl Thin, metadata: <T as Pointee>::Metadata) -> *const T` (and `from_raw_parts_mut`) invokes `core::intrinsics::aggregate_raw_ptr(data_pointer, metadata)`. Note that the `DynMetadata<Dyn>` struct (`metadata.rs:152-200`) holds `*const VTable` (`PhantomData<Dyn>`, `NonNull<VTable>` internally at `14210df0e`/`fde8dfd638`) and exposes `size_of(self) -> usize` and `align_of(self) -> usize` which forward to `vtable_size` and `vtable_align` intrinsics lowered directly by codegen.

At the type level (`compiler/rustc_middle/src/ty/sty.rs:1765-1865` at `fde8dfd638`; `L1733-1830` at `14210df0e`), `Ty::ptr_metadata_ty_or_tail` walks `self.tcx.struct_tail_raw(...)` (peeling nested `ty::Adt` wrappers to their unsized tail field) and maps the resolved tail to its metadata type:

| Tail `TyKind` | `Pointee::Metadata` Type | Representation Class | Validated by `validate.rs` (`AggregateKind::RawPtr`)? |
| :--- | :--- | :--- | :--- |
| `Sized`, `ty::Foreign(_)`, unit `ty::Tuple([])` | `()` (`unit`) | ZST (discarded in `ScalarPair` / collapsed by `InstSimplify`) | Yes (`is_sized`: requires `meta_ty.is_unit()`) |
| `ty::Slice(_)` | `usize` | Scalar integer element count | Yes (`meta_ty == tcx.types.usize`) |
| `ty::Str` | `usize` | Scalar integer byte count | No (falls outside `is_slice` / `is_sized` checks in `validate.rs:1143-1151`) |
| `ty::Dynamic(..)` | `DynMetadata<tail>` (`LangItem::DynMetadata`) | Thin `NonNull<VTable>` pointer | No (falls outside `is_slice` / `is_sized` checks in `validate.rs:1143-1151`) |
| `ty::Adt(..., tail)` (custom-DST struct tail) | Recursive metadata of `struct_tail_raw(tail)` | `usize` or `DynMetadata` matching tail | No (`pointee_ty` is neither `is_slice()` nor `is_sized()` in `validate.rs:1143-1151`) |
| `ty::Param` / `ty::Alias` (unmonomorphized generic tail) | `<tail as Pointee>::Metadata` projection (`Ok`/`Err` wrapped by `pointee_metadata_ty_or_projection`) | Deferred trait projection | Deferred until monomorphization |

#### MIR Pipeline Transformations (`LowerIntrinsics` -> `LowerSliceLenCalls` -> `InstSimplify`)

1. **`LowerIntrinsics` (`PassPolicy::Required`, `Runtime(Initial) -> Runtime(PostCleanup)`):**
   - On `sym::aggregate_raw_ptr(data, meta)` (`fde8dfd638` `lower_intrinsics.rs:315-341`), extracts `ty::RawPtr(pointee_ty, mutability)` from `generic_args.type_at(0)` and emits `Rvalue::Aggregate(Box::new(AggregateKind::RawPtr(*pointee_ty, *mutability)), [data.node, meta.node])` plus `TerminatorKind::goto(target)`. Because `PassPolicy::Required` runs unconditionally even at `-Zmir-opt-level=0`, live `probe_d` `LowerIntrinsics.after.mir` immediately shows:
     ```text
     _61 = ();
     _56 = *const u32 from (move _57, move _61);
     goto -> bb19;
     ```
   - On `sym::ptr_metadata(ptr)` (`fde8dfd638` `lower_intrinsics.rs:342-358`), emits `Rvalue::UnaryOp(UnOp::PtrMetadata, ptr.node)` plus `TerminatorKind::goto(target)`. Importantly, calls *through wrapper functions* (`std::ptr::metadata::<[u32]>` or `std::ptr::from_raw_parts::<[u32], ()>`) stay as `TerminatorKind::Call` across `LowerIntrinsics` until cross-crate `Inline` (`-C opt-level=2`) exposes their inner intrinsic bodies—explaining why `probe_d` exhibits `AggregateKind::RawPtr` on the direct `core::intrinsics::aggregate_raw_ptr` call already at `-Zmir-opt-level=0` while `from_raw_parts` only becomes `AggregateKind::RawPtr` after `Inline` at `-C opt-level=2`.
2. **`validate.rs` checks on `AggregateKind::RawPtr` and `UnOp::PtrMetadata` (`fde8dfd638` `validate.rs:1115-1155, 1261-1267`):**
   - `AggregateKind::RawPtr` is forbidden before `MirPhase::Runtime(_)` (`validate.rs:1118-1122`: pre-`LowerIntrinsics` analysis phases reject raw pointer aggregates).
   - It must have exactly 2 operands (`[data, metadata]`); operand 0 must be `ty::RawPtr(in_pointee, in_mut)` where `in_mut == target_mut` and `in_pointee.is_sized(...)` (annotated with a `// FIXME(Thin): require in_pointee to be Thin`).
   - Operand 1 (`meta_ty`) is checked only when `target_pointee` is `ty::Slice(_)` (`meta_ty == usize`) or `target_pointee.is_sized(...)` (`meta_ty.is_unit()`), leaving `str` and `dyn Trait` unchecked at MIR validation time (`validate.rs:1148-1154`).
   - `UnOp::PtrMetadata` requires operand type `ty::RawPtr | ty::Ref` (`validate.rs:1243-1249` in `14210df0e`, `L1261-1267` in `fde8dfd638`)—never directly accepting a `Box<T>` before `ElaborateBoxDerefs`.
3. **`LowerSliceLenCalls` (`mir-opt-level >= 1`, `lower_slice_len.rs:1-65`):**
   Rewrites any `Call` terminator to `tcx.lang_items().slice_len_fn()` with `CallSource::Normal` and `target: Some(bb)` into `Assign(destination, Rvalue::UnaryOp(UnOp::PtrMetadata, arg))` + `TerminatorKind::goto(bb)`. In `probe_a_array_to_slice`, comparing `LowerIntrinsics.after.mir` vs. `LowerSliceLenCalls.after.mir` isolates this exact rewrite in `bb1`:
   ```text
   // LowerIntrinsics.after.mir:
   _7 = core::slice::<impl [u32]>::len(move _8) -> [return: bb2, unwind continue];
   // LowerSliceLenCalls.after.mir:
   _7 = PtrMetadata(move _8);
   goto -> bb2;
   ```
   And identically in `probe_c_nested_struct_unsize_ref`, replacing `core::slice::<impl [u8]>::len(move _10)` with `_9 = PtrMetadata(move _10); goto -> bb2;`. Across `-Zmir-opt-level=0 -> 1`, `slice_len_calls` drops `1 -> 0` and `ptr_metadata_ops` increments `1 -> 2` in both functions.
4. **`InstSimplify` thin `RawPtr` collapse (`fde8dfd638` `instsimplify.rs:168-182`):**
   When `Rvalue::Aggregate(kind, fields)` has `kind = AggregateKind::RawPtr(pointee, mutability)` and `meta_ty = fields[FieldIdx::ONE].ty(...)` satisfies `meta_ty.is_unit()`, `InstSimplify` rewrites the aggregate in place to `Rvalue::Cast(CastKind::PtrToPtr, fields[0], Ty::new_ptr(tcx, pointee, mutability))`. Empirically verified in `probe_d_from_raw_parts_roundtrip`: `_56 = *const u32 from (move _57, move _61)` at `LowerIntrinsics.after.mir` transforms immediately into `_56 = move _57 as *const u32 (PtrToPtr)` in `InstSimplify-before-inline.after.mir`, causing `raw_ptr_aggregates` to drop `1 -> 0` and `ptr_to_ptr_casts` to rise `0 -> 1` between `-Zmir-opt-level=0` and `-Zmir-opt-level=1`.

---

### 2. `GVN` `UnOp::PtrMetadata` and `AggregateKind::RawPtr` Constant-Folding Asymmetry

**Basis:** source (`rust-lang/rust@fde8dfd638` `gvn.rs:1248-1380, 1607-1664`; identical at `14210df0e` `gvn.rs:1242-1375`) + execution (`rustc 1.98.0-nightly` MIR sweep & `GVN.after.mir` across `probe_a`, `probe_b`, `probe_c_ref`, `probe_c_box`, `probe_d`, `probe_e`) + derived (Lean theorems `stockGvn_folding_asymmetry`, `stockGvnPeel_preserves_meta_and_valid`, `extGvnUnsizeSimplify_sound`, `peelProj_unsound_without_live_ref_side_condition`).

#### Exact Value-Numbering Pipeline in `rustc_mir_transform/src/gvn.rs`

`GVN` evaluates rvalues symbolically through `simplify_aggregate`, `simplify_cast`, and `simplify_unary`:

1. **`simplify_aggregate` on `AggregateKind::RawPtr` (`gvn.rs:1248-1270`):**
   - Loops over operand 0 (`pointer`), peeling any `Value::Cast { kind: CastKind::PtrToPtr, value: cast_value }` whose source is a `Sized` raw pointer (`from_pointee_ty.is_sized(...)`) of identical `Mutability` (`from_mtbl == output_mtbl`).
   - Returns **`Some(self.insert(ty, Value::RawPtr { pointer, metadata }))`** regardless of whether `ty`'s pointee is `[T]`, `dyn Trait`, or a multi-level custom-DST struct `Wrapper<[u8]>`.
2. **`simplify_cast` on `CastKind::PtrToPtr` (`gvn.rs:1607-1618`):**
   - When casting `Value::RawPtr { pointer, .. }` back to a thin `*const/*mut T` where `to_pointee_ty.is_sized(...)` and mutability matches (`from_mtbl == to_mtbl`), `GVN` strips the metadata lane and returns **`Some(pointer)`**.
   - `CastKind::BoxDerefTransmute` is intentionally excluded from `simplify_cast` (`gvn.rs:1638-1664`), preserving UB checks in CTFE/Miri.
3. **`simplify_unary` on `UnOp::PtrMetadata` (`gvn.rs:1309-1379`):**
   Executes a two-stage pass:
   - **Stage A (Peeling loop, `gvn.rs:1311-1349`):** Repeatedly replaces `arg_index` when matching:
     1. `Value::Cast { kind: CastKind::PtrToPtr, value: inner }` **if `self.pointers_have_same_metadata(self.ty(inner), arg_ty)`** (accepts `*const Wrapper<[u8]>` <-> `*mut Wrapper<[u8]>` and generic tails, rejects wide-to-thin casts).
     2. `Value::Cast { kind: PointerCoercion(Unsize), value: from }` **if `from` derefs to `ty::Array(_, len)` AND `arg_index` derefs to `ty::Slice(..)`** -> immediately returns `const len: usize`.
     3. `Value::Address { base: AddressBase::Deref(reborrowed), projection }` **if `projection.is_empty()`**.
   - **Stage B (Top-level value match, `gvn.rs:1356-1379`):**
     1. `(UnOp::PtrMetadata, Value::RawPtr { metadata, .. }) => return Some(metadata)`.
     2. `(UnOp::PtrMetadata, Value::Cast { kind: PointerCoercion(Unsize), value: inner })` **if `arg_ty` derefs directly to `ty::Slice(..)` AND `self.ty(inner)` derefs directly to `ty::Array(_, len)`** -> returns `const len: usize`.

#### Empirical Demonstration of the Three-Way Custom-DST Asymmetry

Live `GVN.after.mir` and `-Zmir-opt-level=0..2` dumps confirm all three consequences of lines `1248-1379` in `probe_a..probe_e`:

| Construct Examined in `GVN.after.mir` (`-C opt-level=2`) | Symbolic Value Entering `simplify_unary(PtrMetadata)` | Result in `rustc 1.98.0-nightly` `GVN.after.mir` | Structural Reason in `gvn.rs` |
| :--- | :--- | :--- | :--- |
| **`probe_a`: `&[u32; 4] -> &[u32]` (`ptr::metadata(s)`, `s.len()`, `s[2]`)** | `Cast(Unsize, &[u32; 4])` directly typed `ty::Slice` | **ALL 3 folded to `const 4_usize`** (bounds check `_12 = const true`) | Matches `ty::Array` / `ty::Slice` at top level (`gvn.rs:1331-1336`) |
| **`probe_c_ref`: `&Wrapper<[u8; 3]> -> &Wrapper<[u8]>` (`ptr::metadata(u)`)** | `Cast(Unsize, &Wrapper<[u8; 3]>)` (`ty::Adt`) | **UNFOLDED:** `_4 = PtrMetadata(copy _2)` (`runtime-optimized` keeps `PtrMetadata`) | Top-level pointee is `ty::Adt(Wrapper)`, not `ty::Slice`! |
| **`probe_c_ref`: `u.inner.tail.len()` and `u.inner.tail[2]`** | `Address { base: Deref(_2), projection: [Field(1), Field(1)] }` | **UNFOLDED:** `_9 = PtrMetadata(copy _10)` and `_14 = PtrMetadata(copy _13)` | Non-empty `projection` stops peeling loop at `gvn.rs:1341`! |
| **`probe_d`: `from_raw_parts::<[u32]>(s_data, s_meta)` then `(&*s_rebuilt)[3]`** | `Address { Deref(_11) }` with `projection = []` over `Value::RawPtr { meta: 4 }` | **FOLDED:** `_17 = const 4_usize; _18 = const true;` | Empty `projection` peels `Deref(_11)` to `Value::RawPtr` -> `const 4_usize`! |
| **`probe_d`: `ptr::metadata(from_raw_parts::<Wrapper<[u8]>>(without_prov(1), 9))`** | Constant-folded `Indirect` alloc or `Value::RawPtr { meta: 9 }` | **FOLDED:** `_68 = const 9_usize`! | Custom-DST `Value::RawPtr { metadata }` returns `Some(metadata)` at `gvn.rs:1365`! |
| **`probe_e`: `(*rebuilt).inner.tail[2]` on `*mut Wrapper<[u8]> from (data, meta)`** | `Address { Deref(_11), projection: [Field(1), Field(1)] }` over `Value::RawPtr` | **UNFOLDED:** `_16 = PtrMetadata(copy _15)` even though `_11 = *mut Wrapper<[u8]> from (...)` | Non-empty `[Field(1), Field(1)]` blocks peeling at `gvn.rs:1341` (and `meta` itself came from unfolded `Unsize`)! |

Crucially, `probe_c_nested_struct_unsize_box` proves LLVM `-C opt-level=2` eventually constant-folds the emitted LLVM IR (`store i64 3, ptr %_0`), *after* MIR GVN fails—meaning MIR-level passes (`ConstProp`, bounds-check elimination, and MIR-based static analyzers) still see uneliminated `PtrMetadata` panicking assertions in `runtime-optimized.after.mir` for every struct-tail custom DST!

#### Soundness Conditions for Extending `GVN` to Nested Struct-Tail Wrappers and Field Projections

Lean theorems `stockGvn_folding_asymmetry`, `extGvnUnsizeSimplify_sound`, and `peelProj_unsound_without_live_ref_side_condition` establish two sharp formal boundaries:

1. **Unconditional soundness of recursive struct-tail `Unsize` folding (`extGvnUnsizeSimplify_sound`):** For *any* ADT wrapper chain `Wrap_1<...Wrap_k<[T; N]>...> -> Wrap_1<...Wrap_k<[T]>...>` related by `PointerCoercion::Unsize` (matching prefix fields and parallel tail unsizing via `unsizeRel`), because `Unsize` preserves `ptr_metadata_ty` down `tcx.struct_tail_raw`, `extGvnUnsizeSimplify` collapsing `(PtrMetadata, Cast(Unsize, inner))` to `const N_usize` preserves semantics cleanly across both `v198LegacyTransmute` and `vHeadBoxDerefTransmute`. Why? Because `Unsize` on `&T`/`Box<T>`/`*const T` materializes `N_usize` eagerly at cast time into the metadata register without touching the data pointer—zero field offset arithmetic is bypassed.
2. **Negative boundary against unconditionally dropping `projection.is_empty()` (`peelProj_unsound_without_live_ref_side_condition`):** Unlike bare `(*p)` (offset `0`), peeling a non-empty field projection chain `[Field(idx, byteOffset > 0), ...]` from `&raw const (*p).inner.tail` in `GVN` **is UNSOUND for arbitrary raw pointers** under Miri / `const_eval`! Specifically, if `p` is a dangling/no-provenance raw pointer `(0x2[noalloc], len = 3)` (`litmus l12`), MIR evaluation of `&raw const (*p).inner.tail` executes `OffsetMode::Inbounds` pointer arithmetic at `offset = 2` and **triggers UB** (`danglingInboundsOffset`), whereas folding `PtrMetadata(&raw const (fake) (*p).inner.tail)` to `const 3_usize` and DCE-eliminating `_15 = &raw const ...` would silently erase that UB, violating `PassPolicy::Required` / UB preservation. Peeling non-empty field projections past `PtrMetadata` is sound *only* when the base place is statically known to be dereferenceable and non-dangling for at least `field_offset` bytes (e.g., `base` is an active reference `&T`/`&mut T`, `Box<T>`, or an unaliased stack local).

---

### 3. Raw `ptr::metadata` Memory Independence, `OffsetMode::Inbounds`, `FakeForPtrMetadata`, and Miri Differential Matrix

**Basis:** normative (`rust-lang/reference@c9cc32825` `behavior-considered-undefined.md:L82, L154`, `type-layout.md:L68`) + source (`rust-lang/rust@14210df0e`: `rustc_const_eval/src/interpret/{operator.rs:487-501, place.rs:466-520, projection.rs:83,200, step.rs:257}`, `rustc_mir_build/src/builder/expr/as_place.rs:688-720`; deltas at `rust-lang/rust@fde8dfd638`: `operator.rs:499-514`, `place.rs:468-538`, `step.rs` / `as_place.rs:706`) + execution (`miri 0.1.0 (14210df0e)` Stacked Borrows & Tree Borrows across `15/15` litmus tests) + derived (`MirPtrMetadataGvnCustomDstAndRawPtrSoundness` Theorems `1`–`6`).

#### How `rustc_const_eval` / Miri Separates Metadata Inspection from Reference & Field Validity

Between `rustc 1.98.0-nightly (14210df0e)` and `rust-lang/rust` HEAD (`fde8dfd638`), `eval_rvalue_into_place` / `unary_op(UnOp::PtrMetadata, val)` evolved from direct `val.to_scalar_and_meta()` reading (`14210df0e` `operator.rs:487-501`) to invoking `self.deref_pointer(val)?; // validity check` (`fde8dfd638` `operator.rs:499-514`), mirroring Lean-Miri's `ScalarOps.lean:138-149`. Inspecting `deref_pointer` (`fde8dfd638` `place.rs:468-538`) reveals a strict 3-way split matching `rust-lang/reference` `r[undefined.validity.wide]`:

- **Safe references & `Box<T>` (`ptr_ty.is_ref() || ptr_ty.is_box()`):** `deref_pointer` checks (i) non-null, (ii) `size_and_align_of_val` (`dyn Trait` vtable validity & overflow), (iii) `check_ptr_access(..., Dereferenceable)`, and (iv) `check_ptr_align`. Note: in `14210df0e`, passing an already-constructed `Box` raw deref did *not* reach `deref_pointer` due to `CastKind::Transmute`, which `fde8dfd638` fixed via `BoxDerefTransmute` (Section 4).
- **Raw `dyn Trait` pointers (`ty::RawPtr` with `ty::Dynamic` tail):** `deref_pointer` extracts the vtable pointer and executes `self.get_ptr_vtable_ty(vtable, Some(data))?`—forged stack vtables fail immediately even on `*const dyn Trait`, matching `r[undefined.validity.wide]` and live Miri `l13`.
- **Raw slices, `str`, and custom-DST wrappers over slices (`ty::RawPtr` with `ty::Slice | ty::Str | ty::Foreign` tail):** `place.rs:528-530` executes **`// Nothing to check`** (`read_immediate` ensures initialization of the two scalar lanes). No null check, no provenance check, no allocation liveness check, no bounds check, and no alignment check are ever performed on the thin data pointer lane!

Lean Theorems `fromRawParts_after_decompose_exact`, `decompose_after_fromRawParts_exact`, and `ptrMetadata_dangling_uninit_data_independent` prove exact round-trip preservation `from_raw_parts(to_thin_data(p), ptr::metadata(p)) == p` (including address AND provenance) and strict data/heap invariance for raw wide pointers.

#### `FakeForPtrMetadata` Borrow-Tag Immunity vs. Nonzero `OffsetMode::Inbounds` Projection UB

Why does `s[mutate_slice(s)]` or `wu.inner.tail[mutate_wrap(wu)]` (`l06`, `probe_e`) avoid Stacked Borrows / Tree Borrows aliasing UB even when taking `&mut` inside the index expression evaluates the length *before* the mutating argument runs?

- In `compiler/rustc_mir_build/src/builder/expr/as_place.rs:688-720`, `len_of_slice_or_array` avoids `FakeForPtrMetadata` when `place` is a direct `[Deref]` of a trivially `Copy` local (`&[T]` or `*const [T]`, e.g., `probe_a`'s `_11 = PtrMetadata(copy _2)`), emitting **`Rvalue::RawPtr(RawPtrKind::FakeForPtrMetadata, place)`** (`&raw const (fake) ...`) whenever the slice place carries non-copy reborrow sensitivity (`&mut [T]` as in `l06`) or field projections (`((*_2).1: Inner<[u8]>).1: [u8]` as in `probe_c_ref` and `probe_e`).
- Borrowck classifies `FakeForPtrMetadata` as `(Shallow(Some(ArtificialField::ArrayLength)), Read(ReadKind::Copy))`.
- Miri (`interpret/step.rs:257`) explicitly checks `if !kind.is_fake()` before reborrowing/retagging, leaving `&mut` uniqueness intact across the interleaving call (`fakeForPtrMetadata_preserves_meta_without_mut_conflict`).

Crucially, however, `&raw const (*p).inner.tail` STILL evaluates the field `Place` projection: if `p: *const Wrapper<[u8]>` holds a no-provenance address `0x2[noalloc]` (`l12`), evaluating `.inner` (`offset = 2 > 0`) runs `OffsetMode::Inbounds` pointer arithmetic (`projection.rs:200`) and fails Miri immediately with `in-bounds pointer arithmetic failed: attempting to offset pointer by 2 bytes, but got 0x2[noalloc] which is a dangling pointer (it has no provenance)`, whereas `ptr::metadata(p)` on that exact same pointer passes!

#### Complete 15-Case Miri Differential Matrix (`0.1.0 (14210df0e)` Stacked Borrows vs. `-Zmiri-tree-borrows`)

| Litmus ID | Case Description | SB (`rc=0`/`UB`) | TB (`rc=0`/`UB`) | Observed Diagnostic (`miri 0.1.0 (14210df0e)`) |
| :--- | :--- | :---: | :---: | :--- |
| `l01` | `ptr::metadata` on null `*const [u32]` (`len = 42`) | `PASS` | `PASS` | `None` (`rc = 0`, matches `l01` in Lean) |
| `l02` | `ptr::metadata` on dangling `0x1` `*const Wrapper<[u8]>` (`len = 99`) | `PASS` | `PASS` | `None` (`rc = 0`) |
| `l03` | `ptr::metadata` on freed `Box<[u8]>` raw pointer (`len = 4`) | `PASS` | `PASS` | `None` (`rc = 0`) |
| `l04` | `ptr::metadata` + `DynMetadata::{size_of, align_of}` on freed `dyn` | `PASS` | `PASS` | `None` (`(16, 8)`, `rc = 0`) |
| `l05` | `ptr::metadata` on oversized `*const [u64]` (`len = usize::MAX`) | `PASS` | `PASS` | `None` (`rc = 0`) |
| `l06` | `FakeForPtrMetadata` bounds check overlapping `&mut` call (`[u32]` & `Wrapper`) | `PASS` | `PASS` | `None` (`rc = 0`) |
| `l07` | `from_raw_parts_mut::<Wrapper<[u8]>>` mutable write round-trip | `PASS` | `PASS` | `None` (`[1, 77, 3]`, `rc = 0`) |
| `l08` | CTFE `const` `ptr::metadata` on null raw slice & unsized `Wrapper` | `PASS` | `PASS` | `None` (`(5, 3)`, `rc = 0`) |
| `l09` | Reborrow `&*p` on null `*const [u32]` | `UB` | `UB` | `constructing invalid value of type &[u32]: encountered a null reference` |
| `l10` | Reborrow `&*p` on freed `Box<[u8]>` | `UB` | `UB` | `constructing invalid value of type &[u8]: encountered a dangling reference (use-after-free)` |
| `l11` | Reborrow `&*p` on unaligned `0x1[noalloc]` `*const Wrapper<[u8]>` | `UB` | `UB` | `constructing invalid value of type &Wrapper<[u8]>: encountered a dangling reference (0x1[noalloc] has no provenance)` |
| `l12` | `&raw const (*p).inner.tail` on dangling `0x2[noalloc]` `*const Wrapper<[u8]>` | `UB` | `UB` | `in-bounds pointer arithmetic failed: attempting to offset pointer by 2 bytes, but got 0x2[noalloc] which is a dangling pointer (it has no provenance)` |
| `l13` | `from_raw_parts::<dyn Summarize>` with stack `[usize; 4]` forged vtable | `UB` | `UB` | `constructing invalid value of type *const dyn Summarize: encountered ...[alloc...], but expected a vtable pointer` |
| `l14a` | **`1.98` gap:** `&raw const (*b)` on unaligned `Box<Wrapper<[u8]>>` slot | **`PASS`** | **`PASS`** | **`None` (`rc = 0`, silently elides alignment UB in `14210df0e`)** |
| `l14b` | Ref deref `&(*b)` on same unaligned `Box<Wrapper<[u8]>>` slot | `UB` | `UB` | `constructing invalid value of type &Wrapper<[u8]>: encountered an unaligned reference (required 2 byte alignment but found 1)` |

---

### 4. `Box<Wrapper<[u8]>>` Deref Lowering (`BoxDerefTransmute`), `ScalarPair` Representation, and `PlaceRef::project_field` LLVM IR

**Basis:** source (`14210df0e`: `library/alloc/src/boxed.rs:234-237`, `elaborate_box_derefs.rs:29-80`, `rustc_codegen_ssa/src/{size_of_val.rs:15-184, mir/{place.rs:166-260, rvalue.rs:166-260,536-745, operand.rs:745-865}}`; `fde8dfd638`: `boxed.rs:238-241, 308-311`, `elaborate_box_derefs.rs:60-68, 126-138`, `validate.rs:1404, 1435-1444`, `interpret/cast.rs:206-214`, `rustc_codegen_ssa/src/{size_of_val.rs:15-180, mir/{place.rs:175-258, rvalue.rs:254-257,410-422,618-620,725-734,807-842}}`) + execution (`rustc 1.98.0-nightly` `ElaborateBoxDerefs.after.mir`, `l14a` MIR, and O0/O2 LLVM IR on `probe_a..probe_e`) + derived (`boxDeref_unaligned_legacy198_elides_vs_head_catches`, `sizeAndAlignOfDst_pow2_and_dvd`, `sizeAndAlign_adjustedOffset_equiv_and_tail_inbounds`, `ssa_codegen_scalarPair_roundtrip`).

#### Cross-Version Evolution: `Unique -> Transmute` (`14210df0e`) vs. `BoxRaw -> BoxDerefTransmute` (`fde8dfd638`)

Live `rustc 1.98.0-nightly (14210df0e)` MIR dumps of `probe_c_nested_struct_unsize_box` and `l14a` (`ElaborateBoxDerefs.after.mir`) directly confirm how `14210df0e` lowers `Box<Wrapper<[u8]>>` dereferences:

```text
// rustc 1.98.0-nightly (14210df0e) ElaborateBoxDerefs on Box<Wrapper<[u8]>>:
_15 = copy ((_2.0: std::ptr::Unique<Wrapper<[u8]>>).0: std::ptr::NonNull<Wrapper<[u8]>>) as *const Wrapper<[u8]> (Transmute);
_6 = &(*_15);
_5 = &raw const (*_6);
```

And in `l14a`, `&raw const (*b)` lowers directly to:

```text
_31 = copy ((_3.0: std::ptr::Unique<Wrapper<[u8]>>).0: std::ptr::NonNull<Wrapper<[u8]>>) as *const Wrapper<[u8]> (Transmute);
_18 = std::ptr::metadata::<Wrapper<[u8]>>(copy _31) -> [return: bb8, unwind: bb13];
```

Because `NonNull<Wrapper<[u8]>>` only enforces non-nullity and `CastKind::Transmute` only checks size equality and raw-pointer validity (without calling `deref_pointer`), `l14a` passes both Stacked Borrows and Tree Borrows in `miri 0.1.0 (14210df0e)` even though `b`'s backing pointer is at an odd address (`align = 1` vs. required `align = 2` for `Wrapper<[u8]>`).

At `rust-lang/rust` HEAD (`fde8dfd638`):
- `library/alloc/src/boxed.rs:238-241, 308-311` replaces `Unique<T>` with `struct BoxRaw<T: ?Sized> { pointer: NonNull<T>, _marker: PhantomData<T> }`, and `ElaborateBoxDerefs` (`elaborate_box_derefs.rs:60-68`) projects a single field (`FieldIdx::ZERO` -> `BoxRaw<T>`) and emits **`CastKind::BoxDerefTransmute`** (`validate.rs:1435-1444` checks both operands are `Sized` and the target is a raw pointer).
- In `rustc_const_eval/src/interpret/cast.rs:206-214`, `CastKind::BoxDerefTransmute` transmutes the immediate `BoxRaw` pointer to `Ty::new_box(*self.tcx, pointee_ty)` and calls `self.deref_pointer(&ptr)?`, preserving null, dereferenceability, and alignment checks on `&raw const (*b)`.
- Meanwhile `rustc_codegen_ssa/src/mir/rvalue.rs:618-620` routes `CastKind::Transmute | CastKind::BoxDerefTransmute | CastKind::Subtype` identically through `self.codegen_transmute_operand`, lowering `ScalarPair -> ScalarPair` register pairs with zero runtime instructions.

#### `rustc_codegen_ssa` `ScalarPair` Representation and `PlaceRef::project_field` / `size_of_val` IR

1. **`UnOp::PtrMetadata` (`rvalue.rs:725-734` at `fde8dfd638`):** Loads operand `op`; if `operand.layout.fields.count() > 1`, returns `OperandValue::Immediate(Scalar(operand.pointer_parts().1))`; otherwise emits `ZeroSized` (`()`).
2. **`AggregateKind::RawPtr` (`rvalue.rs:254-257, 807-842` at `fde8dfd638`):** Explicitly excluded from the memory-write aggregate fast path (`!matches!(**kind, AggregateKind::RawPtr(..))`) and lowered unconditionally via `codegen_rvalue_operand` (`OperandRefBuilder`), which packs `data` into scalar lane `0` (`offset 0`) and `meta` into lane `1` for wide pointers (`{ ptr, i64 }` for slices/`Wrapper<[u8]>` and `{ ptr, ptr }` for `dyn Summarize`), while building a thin `Immediate` for unit-metadata targets (`ssa_codegen_scalarPair_roundtrip`).
3. **`PlaceRef::project_field` (`place.rs:175-258`) and `size_and_align_of_dst` (`size_of_val.rs:15-180`):**
   - For sized fields, direct `[T]`/`str` fields, or fields at `offset = 0`, `project_field` skips dynamic offset calculation.
   - For non-zero-offset custom-DST subfields like `Inner<[u8]>` at unadjusted byte offset `2` inside `#[repr(C)] Wrapper<T>` (`head: u8` at `0..1`, `1` byte padding, `inner: Inner<T>` starting at `2`), `project_field` calls `size_and_align_of_dst(bx, field_ty, meta)` at `-C opt-level=0`, emitting exact `(2 + meta * 1 + 1) & -2` arithmetic before loading `&wrapper + 2 + 2` for `tail`:
     ```llvm
     %3 = mul nuw nsw i64 %rebuilt.1, 1
     %4 = add i64 2, %3
     %5 = add i64 %4, 1
     %6 = and i64 %5, -2
     %7 = getelementptr inbounds i8, ptr %rebuilt.0, i64 2
     %_10.0 = getelementptr inbounds i8, ptr %7, i64 2
     ```
   - `probe_b` LLVM O0 IR likewise confirms `vtable` global emission (`@vtable.1` containing `size = 16 = \10`, `align = 8 = \08`, and `&Concrete::score` at byte offset `24`), and in MIR (`GVN.after.mir`) `DynMetadata::{size_of, align_of}` inline to `vtable_size(copy _12)` / `vtable_align(copy _12)` with `_4 = PtrMetadata(copy _2)` preserved on `&Concrete -> &dyn Summarize` (`store i64 16`, `store i64 8` at `-C opt-level=2`).
   - Theorem `sizeAndAlign_adjustedOffset_equiv_and_tail_inbounds` formally proves `size_of_val.rs:148-160`'s elision identity: whenever `uAlign ∣ uSize` and `uAlign ∣ fullAlign` (guaranteed for all power-of-two layouts by `sizeAndAlignOfDst_pow2_and_dvd`), `alignUp (alignUp off uAlign + uSize) fullAlign = alignUp (off + uSize) fullAlign` and the aligned tail fits strictly inside `[0, fullSize]` (`Wrapper<[u8]>` at `len = 3` reduces to `(size = 8, align = 2)` by `rfl`, matching LLVM O2's `alloca [8 x i8], align 8`).

---

### 5. `joshlf/anneal` MIR Correspondence & TCB Ingestion Boundary (`c131b320e`)

**Basis:** source (`joshlf/anneal@c131b320e`: `trusted/lean/Trusted/MirAst.lean:312-321, 443-446, 620-628`, `trusted/lean/Trusted/MirSemantics.lean:1177-1193`, `trusted/correspondence/Trusted/Correspondence.lean:914-917, 1492-1505`, `correspondence/Anneal/MirCorrespondenceBase.lean:1819-1823`, `vendor/lean-miri/Miri/{MIR/{Operators.lean:23, Syntax.lean:119}, Interpreter/{ScalarOps.lean:138-149, PointerPlaceMachine.lean:134-142, Aggregate.lean:49, Cast.lean:282,385-397, Rvalue.lean:101}}`, `trusted/rustc-capture/src/driver.rs:25, 75-84`).

At `joshlf/anneal@c131b320e`, wide-pointer metadata support splits cleanly across the vendored reference interpreter vs. Anneal's TCB kernel semantics:

| Layer in `joshlf/anneal@c131b320e` | Support for `PtrMetadata`, `RawPtr`, `FakeForPtrMetadata`, `BoxDerefTransmute`, Custom DSTs | Exact Boundary Behavior |
| :--- | :--- | :--- |
| `vendor/lean-miri` | Implements `UnOp.PtrMetadata`, `RawPtrKind.FakeForPtrMetadata`, `AggregateKind.RawPtr`, `BoxDerefTransmute` (`Cast.lean`), and `derefValidity` (`ScalarOps.lean:138-149` matching `HEAD` `deref_pointer`) | Models upstream `HEAD` interpreter rules (`rawPtr` returns metadata after vtable check, skips slice/str data checks) |
| `trusted/correspondence` & `correspondence/Anneal` | `toMiriUnOp .ptrMetadata = .PtrMetadata`; `toMiriRvalue (.addressOf ...) = .RawPtr ...`; `evalRefUnOp_eq` (`MirCorrespondenceBase.lean:1819`) checks scalar `PtrMetadata` fails identically | Translates syntax variant `.ptrMetadata`, while `.addressOf` rejects to `.unsupported` in Day-1 proofs (`MirCorrespondenceProof.lean:1252`) |
| `trusted/lean/Trusted/MirAst.lean` | Declares `UnOp.ptrMetadata`, `MirTy.rawPtr`, `MirTy.ref`, `Rvalue.addressOf` | **Lacks** `MirTy.{array, slice, dynTrait, adt}`, `RawPtrKind`, `CastKind` (`Unsize`, `PtrToPtr`, `BoxDerefTransmute`), `AggregateKind::RawPtr` -> collapses to `.unsupported` |
| `trusted/lean/Trusted/MirSemantics.lean` | `evalUnOp` handles `.not`/`.neg` on `.bool`/`.scalar` only | Rejects `.ptrMetadata` at line `1193` with `.error .unsupported`; `Provenance`/wide `ScalarPair` not yet in `Val` |
| `trusted/rustc-capture/src/driver.rs` | Pins `1.98.0-nightly (f8a08b688 2026-05-30)`; calls `run_compiler` & `after_analysis` callback | No MIR extraction emitted yet; any future capture pipeline targeting `1.98` must explicitly account for `1.98`'s `CastKind::Transmute` box-deref UB-elision bug (`l14a`) vs. `HEAD`'s `BoxDerefTransmute` |

---

## Boundaries

- **not examined:** `dyn*` / `CoerceUnsized` user-defined smart pointers (`Rc<T>`, `Arc<T>`, `Pin<P>`) and non-`Global` custom `Box<T, A>` allocators (`A: Allocator` where `!ty_is_box_global`, which `place.rs:473` does not treat as a built-in `Box`); behavior was examined only for `&T`, `&mut T`, `*const T`, `*mut T`, and `Box<T, Global>`.
- **not examined:** `-Zmir-opt-level=3` / `4` experimental passes beyond `GVN` (specifically cross-crate `Inline` thresholds at `-Zinline-mir-threshold` overrides when compiling `std::ptr::metadata` with `-C opt-level=0`).
- **unknown:** Live runtime execution on a toolchain compiled at exact upstream `rust-lang/rust` HEAD (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) was not performed because the execution host carries `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)`. Consequently, `CastKind::BoxDerefTransmute` (`l14a` becoming UB at `HEAD`) and `UnOp::PtrMetadata`'s `deref_pointer` call in `operator.rs:499-514` are established from primary-source inspection of `fde8dfd638` (`source`) and Lean formalization (`derived`), not live execution of a `fde8dfd638` binary.
- **known not to apply:** `GVN` constant folding of `PtrMetadata(Unsize(...))` does **not** apply to struct-tail custom DSTs (`&Wrapper<[u8; 3]> -> &Wrapper<[u8]>`), trait objects (`&Concrete -> &dyn Summarize`, whose metadata is a vtable pointer rather than a slice length), or non-empty field projections (`&raw const (fake) (*wu).inner.tail`). Conversely, `AggregateKind::RawPtr` folding in `GVN` *does* apply to custom DSTs when constructed via `from_raw_parts` with an empty deref chain (`probe_d`).
- **known not to apply:** Unaligned-`Box` raw-deref UB elision (`l14a`: `&raw const (*b)` returning `rc = 0` in Miri `14210df0e`) does **not** carry over to `rust-lang/rust` HEAD (`fde8dfd638`), where `CastKind::BoxDerefTransmute` invokes `self.deref_pointer(&ptr)?` (`cast.rs:212`).
- **unsupported:** In `joshlf/anneal@c131b320e`, executable `MirSemantics.evalUnOp` does not support `.ptrMetadata` (returns `.error .unsupported`), and `MirAst` cannot represent `Array`/`Slice`/`Dynamic`/custom-DST structs, `CastKind::{Unsize, PtrToPtr, BoxDerefTransmute}`, or `AggregateKind::RawPtr`. In `rustc_mir_transform/src/validate.rs:1143-1151`, `AggregateKind::RawPtr` validation does not validate operand 1's type for `ty::Str`, `ty::Dynamic`, or struct-tail custom DST (`ty::Adt`) targets.

---

## Evidence

### 1. Upstream Source & Specification Anchors

| Subject | Commit / Version | File Path & Symbols / Line Ranges | Role in Report |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `compiler/rustc_mir_transform/src/lower_intrinsics.rs:315-358` (`aggregate_raw_ptr`, `ptr_metadata`) | `source` |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `compiler/rustc_mir_transform/src/lower_slice_len.rs:1-65` (`LowerSliceLenCalls`) | `source` |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `compiler/rustc_mir_transform/src/instsimplify.rs:168-182` (`RawPtr` unit collapse) | `source` |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `compiler/rustc_mir_transform/src/gvn.rs:1248-1380, 1607-1664` (`simplify_aggregate`, `simplify_unary`, `simplify_cast`) | `source` |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `compiler/rustc_mir_transform/src/{elaborate_box_derefs.rs:60-68, 126-138, validate.rs:1115-1155, 1261-1267, 1404, 1435-1444}` | `source` |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `compiler/rustc_middle/src/{mir/syntax.rs:193,1528,1625, ty/sty.rs:1765-1865}` (`PtrMetadata`, `FakeForPtrMetadata`, `BoxDerefTransmute`, `ptr_metadata_ty_or_tail`) | `source` |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `compiler/rustc_mir_build/src/builder/expr/as_place.rs:669-745` (`FakeForPtrMetadata`, `len_of_slice_or_array`) | `source` |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `compiler/rustc_const_eval/src/interpret/{operator.rs:499-514, place.rs:468-538, cast.rs:206-214}` (`deref_pointer`, `BoxDerefTransmute`) | `source` |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `compiler/rustc_codegen_ssa/src/{size_of_val.rs:15-180, mir/{place.rs:175-258, rvalue.rs:254-257, 618-620, 725-734, 807-842}}` | `source` |
| `rust-lang/rust` | `fde8dfd638478da758f93f0e8d9b74d7907f0c9e` | `library/core/src/ptr/metadata.rs:27-173`, `library/alloc/src/boxed.rs:238-241, 308-311` (`BoxRaw`) | `source` |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Installed `rustc-src`/`src` (`operator.rs:487-501`, `elaborate_box_derefs.rs:29-80, 127`, `boxed.rs:234-237`, `projection.rs:200`, `step.rs:257`, `gvn.rs:1242-1375`, `validate.rs:1097-1137, 1243-1249`, `rvalue.rs:166-260,536-745`) | `source` |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `src/behavior-considered-undefined.md:L82, L154` (`r[undefined.misaligned.ptr]`, `r[undefined.validity.wide]`), `src/type-layout.md:L68` (`r[layout.pointer.unsized]`), `src/type-coercions.md` | `normative` |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/{MirAst.lean:312-321,443-446,620-628, MirSemantics.lean:1177-1193}`, `trusted/correspondence/Trusted/Correspondence.lean:914-917,1492-1505`, `correspondence/Anneal/MirCorrespondenceBase.lean:1819-1823`, `vendor/lean-miri/Miri/...`, `trusted/rustc-capture/src/driver.rs:25,75-84` | `source` |

### 2. Package Support Material and Exact Checksums

| Artifact Path (Relative to Package) | Description | Size | SHA-256 |
| :--- | :--- | ---: | :--- |
| `support/probe_ptr_metadata_gvn_custom_dst_and_rawptr.py` | Self-contained `rustc` MIR/LLVM-IR + `miri` (Stacked Borrows & Tree Borrows) differential harness running `probe_a..probe_e`, `-Zmir-opt-level=0..2`, `-Zdump-mir=all`, LLVM O0/O2 IR, and the 15-case litmus matrix (`0` leaked host paths). | `891` LOC / `30,430` B | `e6d06b6a6d214a4b8f7582b563ccb3997f74ce555e4618f71cd5dda6555132f5` |
| `support/ptr_metadata_gvn_custom_dst_probe_results.json` | Sanitized, reproducible JSON capture (`2026-11-23`) from `rustc 1.98.0-nightly (14210df0e)` and `miri 0.1.0 (14210df0e)`: verbatim outputs, MIR pass progression (`built` through `runtime-optimized`), LLVM O0/O2 IR (`@vtable.*`, alignment rounding), and `15/15` SB/TB litmus verdicts. | `695` LOC / `258,598` B | `0d2caa5d303770b78374492e20dc5c8f7b80c7d0b1e043e736b88b74e1826845` |
| `support/MirPtrMetadataGvnCustomDstAndRawPtrSoundness.lean` | Standalone, dependency-free Lean `v4.34.1` formalization (`49` theorems, `725` module constants, `0` `sorry`, `0` `Classical.choice`, `0` `omega`/`bv_decide`/`native_decide`, `0` `._unsafe_rec`, `0` `partial` defs). | `1,832` LOC / `83,986` B | `4dc853c7fb2dbba9d15c98643c6ee662b9201bfc73841c0cfecfef94f99f12b0` |

### 3. Recorded Live Execution and Lean Verification Transcript (`2026-11-23`)

1. **Differential `rustc` + `miri` execution (`python3 support/probe_ptr_metadata_gvn_custom_dst_and_rawptr.py` -> exit code `0`):**
   - `rustc -vV`: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `host: x86_64-unknown-linux-gnu`, `LLVM version: 22.1.6`.
   - `cargo miri --version`: `miri 0.1.0 (14210df0e2 2026-05-31)`.
   - Native `-C opt-level=2`, Miri Stacked Borrows, and Miri `-Zmiri-tree-borrows` all produced identical deterministic JSON output across `probe_a..probe_e`:
     `{"A":[4,4,30],"B":[16,8,42],"C_REF":[3,9,513,3,103],"C_BOX":[3,5,77,22],"D":[40,42,9,103,17,9,8,true],"E":[42,999,22,77]}`.
   - MIR opt sweep (`-Zmir-opt-level=0 -> 1 -> 2` at `-C opt-level=0`):
     - `probe_a_array_to_slice`: `slice_len_calls: 1 -> 0 -> 0`; `ptr_metadata_ops: 1 -> 2 -> 0`; `const_4_usize: false -> false -> true`.
     - `probe_c_nested_struct_unsize_ref`: `slice_len_calls: 1 -> 0 -> 0`; `ptr_metadata_ops: 1 -> 2 -> 2`; `const_3_usize: false -> false -> false`.
     - `probe_d_from_raw_parts_roundtrip`: `raw_ptr_aggregates: 1 -> 0 -> 0`; `ptr_to_ptr_casts: 0 -> 1 -> 1` (confirming `InstSimplify` unit collapse of `aggregate_raw_ptr(data, ())`).
   - Full `-Zdump-mir=all` (`-C opt-level=2`): `probe_d` exhibits `_68 = const 9_usize` (custom-DST `RawPtr` constant-folded by `GVN`), while `probe_c_ref`, `probe_c_box`, and `probe_e` retain unfolded `PtrMetadata(copy ...)` on struct-tail `Unsize` and `&raw const (fake) (((*_2).1: Inner<[u8]>).1: [u8])` in `GVN.after.mir` and `runtime-optimized.after.mir`.
   - Miri differential litmus suite: `15/15` Stacked Borrows and `15/15` Tree Borrows cases matched expectations, with exact UB diagnostics recorded in `support/ptr_metadata_gvn_custom_dst_probe_results.json`.
2. **Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel check and purity audit (`2026-11-23`):**
   - `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/MirPtrMetadataGvnCustomDstAndRawPtrSoundness.lean` -> **exit code `0`**, zero errors, zero warnings.
   - Isolated `.olean` build + environment scan over all `725` generated constants and `#print axioms` on all `49` proved theorems -> **exit code `0`**: `UNSAFE_REC=0`, `UNSAFE_OR_PARTIAL_DEF=0`, `MOD_AXIOMS=0`; axiom usage per theorem is strictly bounded by `∅`, `[propext]`, or `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorryAx`, zero `Lean.ofReduceBool`/`Lean.trustCompiler`).

### 4. Mechanized Theorem Inventory (`support/MirPtrMetadataGvnCustomDstAndRawPtrSoundness.lean`)

| Theorem Identifier | Formalized Claim | Axioms Used |
| :--- | :--- | :--- |
| `alignUp_add_mul_absorb`, `pow2_le_dvd`, `pow2_max_both_dvd` | Algebraic alignment-absorption identity `alignUp (alignUp off uAlign + uSize) fAlign = alignUp (off + uSize) fAlign` for power-of-two alignments (`size_of_val.rs:148-160`). | `[propext]` |
| `sizeAndAlignOfDst_pow2_and_dvd`, `sizeAndAlign_adjustedOffset_equiv_and_tail_inbounds` | Dynamic alignment is always `2^e` dividing total `size_of_val`, and `PlaceRef::project_field`'s aligned tail `[adjustedOffset, adjustedOffset + uSize]` lies within `[0, fullSize]`. | `[propext]` |
| `fromRawParts_after_decompose_exact`, `decompose_after_fromRawParts_exact` | Exact `(data, meta)` bijection and provenance preservation under `from_raw_parts(to_thin_data(p), ptr::metadata(p))` across slices, `dyn Trait`, and custom-DST wrappers. | `[propext]` |
| `ptrMetadata_dangling_uninit_data_independent` | Invariance of raw `evalPtrMetadata` across allocation freeing, null/odd data addresses, and target `isizeMax` across both `14210df0e` and `fde8dfd638` profiles. | `[propext]` |
| `dangling_rawPtr_metadata_passes_while_nonzero_field_and_ref_fail` | Sharp separation between passing `ptr::metadata` (`l02`), failing `OffsetMode::Inbounds` field projection at offset `2` (`l12`), and failing safe reference validity (`l11`). | `[propext]` |
| `boxDeref_unaligned_legacy198_elides_vs_head_catches` | Cross-version separation proving `&raw const (*b)` on unaligned `Box<Wrapper<[u8]>>` passes `v198LegacyTransmute` (`l14a`) and faults under `vHeadBoxDerefTransmute` (`BoxDerefTransmute`) & `&(*b)` (`l14b`). | `[propext]` |
| `fakeForPtrMetadata_preserves_meta_without_mut_conflict` | `FakeForPtrMetadata` extracts exact slice metadata across live `&mut` references without consuming mutable borrow permission (`l06`). | `[propext]` |
| `stockGvn_folding_asymmetry`, `extGvnUnsizeSimplify_sound` | Stock `GVN` folds `[T; N] -> [T]` and custom-DST `RawPtr` aggregates yet leaves struct-tail `Unsize` & non-empty projections unfolded; recursive wrapper `Unsize` folding `extGvnUnsizeSimplify` is proved sound. | `[propext]` / `[propext, Quot.sound]` |
| `peelProj_unsound_without_live_ref_side_condition` | Proves unconditional removal of `projection.is_empty()` in `GVN` is unsound for dangling raw pointers because it deletes `OffsetMode::Inbounds` UB (`l12`). | `[propext]` |
| `ssa_codegen_scalarPair_roundtrip`, `specimen_probe_*`, `specimen_litmus_matrix_exact` | `rustc_codegen_ssa` `ScalarPair` round-trip and concrete kernel reductions (`rfl`) matching `probe_a..probe_e`, `Wrapper<[u8]>` (`size=8, align=2` at `len=3`), and Miri `l01..l14b`. | `∅` / `[propext]` |

---

## Revalidation

Use the following fast checks to revalidate any claim against a newer `rustc` nightly, `Miri`, `joshlf/anneal` commit, or `Lean` release:

### 1. Re-run the Standalone `rustc` + `Miri` Probe & Check Version Transitions (`l14a`, `probe_c`, `GVN`)

From this package directory (ensuring `rustc` nightly and prebuilt `cargo-miri` sysroot are in `PATH`):

```bash
python3 support/probe_ptr_metadata_gvn_custom_dst_and_rawptr.py \
  --out /tmp/reval_ptr_metadata_probe.json
```

Compare `/tmp/reval_ptr_metadata_probe.json` against `support/ptr_metadata_gvn_custom_dst_probe_results.json`:

1. **`CastKind::BoxDerefTransmute` landing check (`l14a` & `probe_c_nested_struct_unsize_box`):** On a toolchain synced at or past `fde8dfd638`:
   - `probe_c_nested_struct_unsize_box` `ElaborateBoxDerefs.after.mir` shifts from `Unique`/`NonNull` + `(Transmute)` (`transmutes: 5`) to `BoxRaw` + `(BoxDerefTransmute)` (`box_deref_transmutes >= 1`).
   - `l14a_198_raw_box_deref_unaligned_transmute_gap` will transition from `PASS` (`rc = 0`) to `UB` (via `CastKind::BoxDerefTransmute` calling `self.deref_pointer(&ptr)?` -> alignment error at `place.rs:509-515`) in both Stacked Borrows and Tree Borrows once `CastKind::BoxDerefTransmute` is active.
2. **`GVN` custom-DST folding evolution (`probe_c_nested_struct_unsize_ref` & `probe_e`):** If `rustc`'s `gvn.rs` learns to peel nested struct tails in `simplify_unary`, `probe_c_nested_struct_unsize_ref` at `mir_opt_level_2` will drop `ptr_metadata_ops` (`2 -> 0`) and set `const_3_usize = true`, and `probe_d` will gain `*const Wrapper<[u8]>` folding in `GVN.after.mir`.

### 2. Re-verify the Kernel-Checked Lean `v4.34.1` Formalization

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/MirPtrMetadataGvnCustomDstAndRawPtrSoundness.lean
```

Confirm exit code `0`, and grep comments-stripped source to confirm zero occurrences of `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, `deriving`, `_unsafe_rec`, or `axiom `.

### 3. Upstream Source Diff Check (`rust-lang/rust` & `joshlf/anneal`)

If moving to a newer `rust-lang/rust` commit `<NEW_SHA>`, diff only the exact files controlling these behaviors:

```bash
git diff fde8dfd638478da758f93f0e8d9b74d7907f0c9e <NEW_SHA> -- \
  compiler/rustc_mir_transform/src/{lower_intrinsics,lower_slice_len,instsimplify,gvn,elaborate_box_derefs,validate}.rs \
  compiler/rustc_const_eval/src/interpret/{operator,cast,place,projection,step}.rs \
  compiler/rustc_codegen_ssa/src/{size_of_val,mir/{place,rvalue}}.rs \
  library/core/src/ptr/metadata.rs \
  library/alloc/src/boxed.rs
```

For `joshlf/anneal`, diff `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` and `trusted/rustc-capture/src/driver.rs` against `c131b320eeeb26ef692e5afd5ec8db49ee518613` to detect whether wide-pointer types (`Array`, `Slice`, `Dynamic`, ADT tails), `CastKind::BoxDerefTransmute`, or `.ptrMetadata` execution enter the TCB AST/semantics.
