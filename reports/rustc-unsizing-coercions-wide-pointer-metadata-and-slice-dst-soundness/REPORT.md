# Rustc Unsizing Coercions, Wide Pointer Metadata, PtrMetadata Folding, and Dynamic DST Layout Soundness

## Summary

Across `rustc`, `core::ptr`, Miri (`rustc_const_eval::interpret`), SSA codegen (`rustc_codegen_ssa`), and `joshlf/anneal`, unsizing coercions (`CastKind::PointerCoercion(PointerCoercion::Unsize, _)`) and wide-pointer metadata operations (`UnOp::PtrMetadata`, `AggregateKind::RawPtr`, `size_of_val_raw`, `align_of_val_raw`) obey seven load-bearing invariants:

1. **Runtime MIR separates pointer reinterpretation, raw-parts aggregation, and metadata projection into distinct typed primitives.** After borrow-checking cleanup (`CleanupPostBorrowck`) lowers borrowck-only `PointerCoercion::{ArrayToPointer, MutToConstPointer}` to `CastKind::PtrToPtr` and `LowerIntrinsics` (`compiler/rustc_mir_transform/src/lower_intrinsics.rs:291-334`) lowers `core::intrinsics::aggregate_raw_ptr` and `core::intrinsics::ptr_metadata`, `MirPhase::Runtime(RuntimePhase::PostCleanup)` retains three wide-pointer primitives: `Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize, _), src, dst_ty)` for thin-to-wide, wide-to-wide, and `CoerceUnsized` wrapper coercions; `Rvalue::Aggregate(AggregateKind::RawPtr(pointee_ty, mutability), [data, meta])` for raw pointer assembly; and `Rvalue::UnaryOp(UnOp::PtrMetadata, ptr)` (often paired with `Rvalue::RawPtr(RawPtrKind::FakeForPtrMetadata, place)` for slice bounds checks) for pure metadata extraction without pointee dereference (`compiler/rustc_middle/src/mir/syntax.rs:186-192,1499-1515,1610-1617`).
2. **`PtrMetadata` peephole folding over `Unsize` and `RawPtr` aggregates lives in `GVN` (`-Zmir-opt-level >= 2`), not `InstSimplify`, and exhibits a concrete custom-DST blind spot.** In both `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, `LowerSliceLenCalls` (`lower_slice_len.rs:11-62`, `-Zmir-opt-level >= 1`) rewrites `<[T]>::len` calls into `UnOp::PtrMetadata`, while `InstSimplify` (`instsimplify.rs:172-184,275-321`, `-Zmir-opt-level >= 1`) rewrites thin `Aggregate(RawPtr, [p, ()])` into `Cast(PtrToPtr, p)` and folds `size_of_val::<Sized>`, `align_of_val::<Sized>`, and `align_of_val::<[T]>` into `SizeOf`/`AlignOf` constants. Actual `UnOp::PtrMetadata` folding resides in `GVN::simplify_unary` (`gvn.rs:1291-1375`, `-Zmir-opt-level >= 2`), which folds `PtrMetadata(RawPtr { metadata, .. }) -> metadata` and `PtrMetadata(Unsize(&[T; N] -> &[T])) -> const N`. Because `GVN::simplify_unary` guards its `Unsize` rule on `ty::Slice(..)` (`gvn.rs:1328,1367`) and peels `AddressBase::Deref` only when `projection.is_empty()` (`gvn.rs:1335`), `rustc` leaves `PtrMetadata` **unfolded** at `-Zmir-opt-level=2` on custom slice-tail structs (`&DstWrap<[u32; 4]> -> &DstWrap<[u32]>`), even for adjacent statements and slice-tail bounds checks (`s03_dst_wrap_slice_tail`).
3. **Wide pointers use `BackendRepr::ScalarPair(data_ptr, metadata)`, whereas standalone `DynMetadata<Dyn>` uses `FieldsShape::Aggregate`.** In `compiler/rustc_ty_utils/src/layout.rs:421-487`, `Ref` and `RawPtr` normalize `<Pointee as Pointee>::Metadata`: if the metadata layout is `is_1zst()` (`()` for `Sized` and `extern` types), the pointer has `BackendRepr::Scalar(data_ptr)` (`8` bytes on 64-bit targets); otherwise it has `BackendRepr::ScalarPair(data_ptr, metadata)` (`16` bytes on 64-bit targets), with non-null `valid_range.start = 1` on `DynMetadata`'s vtable pointer. Because `DynMetadata<Dyn>` has `FieldsShape::Primitive` inside a wide pointer's metadata slot versus `FieldsShape::Aggregate` as a standalone struct, `DynMetadata::vtable_ptr` (`library/core/src/ptr/metadata.rs:173-185`) must extract the pointer via `mem::transmute` rather than field projection to avoid codegen ICEs. Every compiler-generated vtable begins with `TyCtxt::COMMON_VTABLE_ENTRIES = &[MetadataDropInPlace, MetadataSize, MetadataAlign]` at word indices `0, 1, 2` (`compiler/rustc_middle/src/ty/vtable.rs:45-52`).
4. **In-place struct-tail unsizing depends on `StructKind::MaybeUnsized` freezing prefix field order and excluding the tail from field sorting.** In `compiler/rustc_ty_utils/src/layout.rs:687-761`, `maybe_unsized` is `true` if and only if an ADT is a non-empty `struct` whose last field is not statically `Sized` in the struct definition's generic identity environment. When `maybe_unsized` holds (`StructKind::MaybeUnsized`), `LayoutCalculator::univariant` (`compiler/rustc_abi/src/layout.rs:285-289,1112-1118`) disables end-biased niche layout and restricts alignment-descending field reordering strictly to `fields[..fields.len() - 1]`. Empirically, `DstWrap<T: ?Sized> { tag: u8, header: u16, tail: T }` places `(header, tag)` at byte offsets `(0, 2)` across `u8`, `[u32; 4]`, `u64`, `AlignedPayload` (`align = 16`), and `dyn SubTrait`, whereas an otherwise identical `SizedWrap<T> { tag: u8, header: u16, tail: T }` (without `?Sized`, hence `StructKind::AlwaysSized`) hoists `tail: u64` to offset `0` and shifts `(header, tag)` to `(8, 10)`. Furthermore, `#[repr(packed(P))]` structs forbid unsized tails that may need drop (`E0277`, preventing unaligned `&mut T` in `drop_in_place`), requiring `ManuallyDrop<T>` to activate dynamic `min(vtable_align, pack)` capping (`eval_context.rs:468-472`, `size_of_val.rs:115-127`).
5. **CTFE/Miri validates `size_of_val_raw <= isize::MAX` and vtable provenance eagerly, whereas SSA codegen assumes those preconditions via `mul nuw nsw` and bitmask rounding.** Upstream `compiler/rustc_codegen_ssa/src/base.rs` no longer contains a separate `unsize_thin_ptr` helper; thin-to-wide and wide-to-wide pointer coercions share `unsize_ptr(bx, src, src_ty, dst_ty, old_info: Option<Bx::Value>)` (`base.rs:223-266`), which delegates to `TyCtxt::struct_lockstep_tails_for_codegen` (`ty/util.rs:321-373`) so nested wrappers `Foo<Foo<T>> -> Foo<dyn Trait>` generate vtables for `Foo<T>` rather than `T`. For `size_of_val_raw`, Miri (`eval_context.rs:432-518`) enforces `elem_size.saturating_mul(len) <= isize::MAX` (`InvalidMeta::SliceTooBig`), vtable trait/allocation authenticity, and `(unsized_offset_unadjusted.align_to(unsized_align) + unsized_size).align_to(full_align) <= isize::MAX` (`InvalidMeta::TooBig`), licensing codegen (`size_of_val.rs:53,162-179`) to emit unchecked `bx.unchecked_sumul` (`mul nuw nsw i64`) and `(size + (align - 1)) & -align` without overflow branches.
6. **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` parses `UnOp.ptrMetadata` in `Trusted.MirAst` and maps it in `Trusted.Correspondence`, while failing closed with `FaultKind.unsupported` in `Trusted.MirSemantics`.** In `trusted/lean/Trusted/MirAst.lean:308-321,445-446,612-628`, `UnOp.ptrMetadata` is present, `MirTy` lowers `Array`, `Slice`, `Str`, `Dynamic`, and structs to `MirTy.unsupported`, and `Rvalue` lowers `Cast` and `AggregateKind::RawPtr` to `Rvalue.unsupported`. In `trusted/lean/Trusted/MirSemantics.lean:1007-1019,1177-1193`, `evalPrimitiveOperand` rejects non-primitive pointer operands with `.error .unsupported`, and `evalUnOp` handles only `.not` and `.neg` (`| _, _ => .error .unsupported`). Meanwhile, `vendor/lean-miri` (`Miri/Interpreter/{Cast,DynamicLayout,ScalarOps}.lean`) already mechanizes `unsizeInto`, `sizeAndAlignFromMeta`, and `UnOp.PtrMetadata`, providing the exact reference oracle for a six-part Pass 1/Pass 2 TCB extension.
7. **Empirical and Lean `v4.34.1` verification confirm all layout, peephole, and UB boundaries.** `support/probe_unsizing_and_ptr_metadata.py` compiles 10 specimens across `-Zmir-opt-level=0..2`, runs native layout checks, and executes 12 `miri -Zmiri-tree-borrows` litmus tests (`5/5` valid cases pass including `&[(); usize::MAX]` and `#[repr(packed(2))]` `dyn` DSTs; `7/7` UB cases caught across `SliceTooBig`, $2^{64}$ modular-wraparound `len = 2^{62} + 1`, struct-prefix `TooBig`, forged vtables, wrong-trait vtable transmutes, and misaligned/null ZST slice references). `support/UnsizingWidePointerSoundness.lean` (`396` kernel declarations, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`) mechanizes prefix-offset invariance, `PtrMetadata` peephole folding soundness, dynamic-static span containment within `isize::MAX`, and three concrete sharpness counterexamples.

## Applicability

The findings in this report govern the four pinned upstream subjects recorded in `REPORT.json`:

- **Executed nightly compiler, `core` library, and Miri toolchain (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):** `rustc 1.98.0-nightly (2026-05-31)` with LLVM `22.1.6` and `miri 0.1.0 (14210df0e2 2026-05-31)` on `x86_64-unknown-linux-gnu` (`64`-bit pointers, `usize::MAX = 2^{64} - 1`, `isize::MAX = 2^{63} - 1`). All empirical MIR dumps (`-Zmir-opt-level=0`, `1`, `2`), LLVM IR dumps, native binary outputs, `core` library line citations, and Miri `-Zmiri-tree-borrows` diagnostics were obtained directly from this revision.
- **Cross-checked upstream compiler source (`rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`):** Inspected side-by-side against `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` across all audited compiler and `core` modules to isolate any post-`14210df0e` implementation changes:
  - *Shared across both revisions:* `UnOp::PtrMetadata` and `CastKind::PointerCoercion(PointerCoercion::Unsize, _)` invariants (`syntax.rs`); `LowerIntrinsics`, `LowerSliceLenCalls`, `InstSimplify::{simplify_ptr_aggregate, simplify_size_or_align_of_val}`, and `GVN::simplify_unary` (including the `ty::Slice` guard on `Unsize` folding); `BackendRepr::ScalarPair` fat-pointer layout (`rustc_ty_utils/src/layout.rs`); `StructKind::MaybeUnsized` prefix-only field sorting (`rustc_abi/src/layout.rs`); `COMMON_VTABLE_ENTRIES` (`ty/vtable.rs`); `unsize_ptr`, `coerce_unsized_into`, and `size_and_align_of_dst` (`rustc_codegen_ssa`); and `size_and_align_from_meta` (`eval_context.rs`).
  - *Specific to `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (and `8144389c895da997dbdecaa635e41d6a50be6ffd`):* In `compiler/rustc_const_eval/src/interpret/cast.rs`, copying unchanged sibling fields of a `CoerceUnsized` struct inside `unsize_into` switched from `self.copy_op(&src_field, &dst_field)?` (`14210df0e2:L492`) to `self.copy_op_no_validate(&src_field, &dst_field, /* allow_transmute */ false)?` (`c7d5ba59d8:L568-571`), deferring validity checking to the caller's single post-cast validation step. Additionally, `LayoutCalculator::univariant` / `univariant_biased` (`14210df0e2:L266,1094`) was renamed `layout_of_univariant` / `univariant_biased` (`c7d5ba59d8:L273,596`) with identical `StructKind::MaybeUnsized` exclusion logic (`end = fields.len() - 1`).
- **Anneal verification stack (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Directly characterizes `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/correspondence/Trusted/Correspondence.lean`, `trusted/audit/TrustedBoundary.lean`, and vendored `vendor/lean-miri` (pinned to upstream `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`). Note that Anneal enforces `Program.pointerWidthBits == 64` and `deinitMovedPlace = true` (`MirSemantics.lean:67-70,901-905`).
- **Proof assistant kernel (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Checks `support/UnsizingWidePointerSoundness.lean` in standalone single-file mode using only `Init` (`propext` only; zero `Classical.choice`, `Quot.sound`, `sorryAx`, or `Lean.ofReduceBool`).

Feature-gate scope: array-to-slice unsizing (`&[T; N] -> &[T]`), concrete-to-`dyn Trait` unsizing, trait upcasting (`&dyn SubTrait -> &dyn SuperTrait`, stabilized in Rust 1.86), custom struct-tail DST unsizing (`&Struct<[T; N]> -> &Struct<[T]>` and `&Struct<Concrete> -> &Struct<dyn Trait>`), `mem::size_of_val`, and `mem::align_of_val` are stable Rust features. Direct user-surface access to `ptr::Pointee`, `ptr::DynMetadata`, `ptr::metadata`, `ptr::from_raw_parts`, `mem::size_of_val_raw`, `mem::align_of_val_raw`, `marker::Unsize`, `ops::CoerceUnsized`, and `ops::DispatchFromDyn` requires nightly feature gates (`#![feature(ptr_metadata, layout_for_ptr, unsize, coerce_unsized, dispatch_from_dyn)]`), though `core` itself uses these intrinsics internally to implement stable `<[T]>::len`, `slice::from_raw_parts`, `Box`/`Rc`/`Arc` coercions, and `size_of_val`.

## Findings

### 1. MIR Syntax, Trait Hierarchy (`Pointee`, `Unsize`, `CoerceUnsized`, `DispatchFromDyn`), and `MirPhase::Runtime` Invariants

```text
Basis: source (compiler/rustc_middle/src/mir/syntax.rs, ty/adjustment.rs; library/core/src/{ptr/metadata.rs, ops/unsize.rs, marker.rs, mem/mod.rs})
```

#### 1.1 Four Language-Item Traits Governing Wide Pointers and Coercions

In `library/core` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), wide-pointer metadata and unsizing coercions are anchored by four `#[lang = "..."]` traits:

1. **`Pointee` (`#[lang = "pointee_trait"]`, `library/core/src/ptr/metadata.rs:56-68`):** Compiler-implemented for every `T: PointeeSized` (`#[rustc_deny_explicit_impl]`), defining `#[lang = "metadata_type"] type Metadata: fmt::Debug + Copy + Send + Sync + Ord + Hash + Unpin + Freeze;` (deliberately omitting `'static` because `DynMetadata<dyn Trait + 'a>` carries `'a`). Compiler normalization assigns:
   - `()` (`Thin` alias `Pointee<Metadata = ()>`, `metadata.rs:85`) for all `Sized` types and `extern` (`ty::Foreign`) types;
   - `usize` (element count for `[T]`; UTF-8 byte count for `str`);
   - `DynMetadata<Self>` (`#[lang = "dyn_metadata"]`, `metadata.rs:158-162`, wrapping `NonNull<VTable>` + `PhantomData<Dyn>`) for `dyn Trait`;
   - `<Tail as Pointee>::Metadata` recursively for any struct or tuple whose last field is `Tail: ?Sized`.
2. **`Unsize<T>` (`#[lang = "unsize"]`, `library/core/src/marker.rs:232-237`):** Compiler-implemented (`#[rustc_deny_explicit_impl]`) marker describing pointee types whose representation can be reinterpreted **in-place behind a pointer without moving or mutating pointee bytes**:
   - `[T; N]: Unsize<[T]>` for any `Sized` element type `T` and compile-time length `N: usize`;
   - `T: Unsize<dyn Trait + AutoTraits... + 'a>` when `T: Sized + Trait + AutoTraits... + 'a` and `Trait` is dyn-compatible;
   - `(dyn TraitA + AutoA... + 'a): Unsize<dyn TraitB + AutoB... + 'b>` when `TraitB` is a supertrait of `TraitA` (or `TraitA == TraitB`, or principal trait is dropped leaving only auto traits), `AutoB ⊆ AutoA`, and `'a: 'b` (`marker.rs:208-212`);
   - `Foo<..., T1..Tn, ...>: Unsize<Foo<..., U1..Un, ...>>` for structs when **only the last field** mentions `T1..Tn`, all earlier fields and generic parameters are identical, and `LastField<T1..Tn>: Unsize<LastField<U1..Un>>` (`marker.rs:213-219`).
3. **`CoerceUnsized<T>` (`#[lang = "coerce_unsized"]`, `library/core/src/ops/unsize.rs:35-70`):** User-implementable trait for **by-value pointer/wrapper coercions** (`&'b mut T -> &'a mut U | &'a U | *mut U | *const U`, `&'b T -> &'a U | *const U`, `*mut T -> *mut U | *const U`, `*const T -> *const U` when `T: Unsize<U>`, plus custom structs such as `Box`, `Rc`, `Arc`, `NonNull`, `Cell`, `CustomPtr`, and `TaggedPtr`). Unlike `Unsize` (which requires identical in-memory prefix offsets of an unsized pointee), `CoerceUnsized` on `Wrap<T> -> Wrap<U>` requires `Wrap<T>: Sized` and `Wrap<U>: Sized` and permits arbitrary unchanged or `1-ZST` sibling fields alongside **at most one** non-phantom coerced field (`CustomCoerceUnsized::Struct(FieldIdx)` in `compiler/rustc_middle/src/ty/adjustment.rs:217-229`).
4. **`DispatchFromDyn<T>` (`#[lang = "dispatch_from_dyn"]`, `library/core/src/ops/unsize.rs:118-134`):** Stricter companion to `CoerceUnsized` for dyn-compatible method receivers (`self: Rc<Self>`, `self: CustomPtr<'_, Self>`). Beyond `CoerceUnsized`, `DispatchFromDyn` requires `Self` to be a non-`#[repr(packed)]`, non-`#[repr(C)]` struct whose **only** non-`1-ZST` field is the coerced pointer (`unsize.rs:93-103`), guaranteeing that the wrapper has the exact same `Scalar`/`ScalarPair` representation as a raw pointer (`base.rs:253-255`: `offset == 0` and `src_layout.size == src_f.size`) so dynamic dispatch can swap the receiver's data pointer without reconstructing multi-field memory aggregates.

#### 1.2 Runtime MIR Constructs and Post-Borrowck Invariants

In `compiler/rustc_middle/src/mir/syntax.rs` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`; corresponding lines in `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` noted alongside):

- **`CastKind::PointerCoercion(PointerCoercion, CoercionSource)` (`syntax.rs:1508`, `c7d5ba59d8:L1519`):** Of the six `PointerCoercion` variants in `compiler/rustc_middle/src/ty/adjustment.rs:11-40` (`ReifyFnPointer`, `UnsafeFnPointer`, `ClosureFnPointer`, `MutToConstPointer`, `ArrayToPointer`, `Unsize`), `ArrayToPointer` (`*const [T; N] -> *const T`) and `MutToConstPointer` (`*mut T -> *const T`) are **forbidden** starting in `AnalysisPhase::PostCleanup` and throughout all `MirPhase::Runtime` dialects (`syntax.rs:110-112,1502-1507`), having been lowered to `CastKind::PtrToPtr`. `PointerCoercion::Unsize` remains in runtime MIR and intentionally stores **only** the source operand and target type `Ty<'tcx>`, delegating lockstep structural tail traversal to CTFE/Miri and codegen (`adjustment.rs:34-38`).
- **`UnOp::PtrMetadata` (`syntax.rs:1616`, `c7d5ba59d8:L1627`):**
  ```rust
  pub enum UnOp {
      Not,
      Neg,
      /// Extracts the metadata from a pointer (or reference).
      /// For example, this will give a `()` from `*const i32`, a `usize` from
      /// `&mut [u8]`, or a `ptr::DynMetadata<dyn Foo>` (internally a pointer)
      /// from a `*mut dyn Foo`.
      /// Allowed only in [`MirPhase::Runtime`]; earlier it's an intrinsic.
      PtrMetadata,
  }
  ```
- **`RawPtrKind::FakeForPtrMetadata` (`syntax.rs:191`, `c7d5ba59d8:L191`):** Emitted by MIR building for slice length queries and bounds checks (`_11 = &raw const (fake) ((*_2).2: [u32]); _12 = PtrMetadata(copy _11);`). Operational semantics treats it identically to raw address-of without incurring a Stacked/Tree Borrows retag (`syntax.rs:187-190`), so reading slice length through an existing place never invalidates active borrows of slice elements.
- **`AggregateKind::RawPtr(Ty<'tcx>, Mutability)` (`lower_intrinsics.rs:301`):** Produced when `LowerIntrinsics` lowers `core::intrinsics::aggregate_raw_ptr(data, meta)` (the backing intrinsic of `ptr::from_raw_parts` and `ptr::from_raw_parts_mut`, `metadata.rs:116-134`) into a two-field MIR aggregate `[data_pointer, metadata]`.

---

### 2. Three-Tier MIR Lowering and Peephole Folding (`LowerIntrinsics`, `LowerSliceLenCalls`, `InstSimplify`, and `GVN`)

```text
Basis: source (compiler/rustc_mir_transform/src/{lib.rs, lower_intrinsics.rs, lower_slice_len.rs, instsimplify.rs, gvn.rs}) + execution (support/probe_unsizing_and_ptr_metadata.py, support/unsizing_probe_results.json)
```

#### 2.1 Exact Division of Labor Across MIR Passes

Inspection of `compiler/rustc_mir_transform/src/` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (and `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) establishes that wide-pointer simplifications are partitioned across **four distinct MIR passes** gated at three optimization levels:

1. **`LowerIntrinsics` (`lower_intrinsics.rs:291-334`, unconditional in `run_runtime_cleanup_passes` at `-Zmir-opt-level >= 0`, `lib.rs:653-658`):**
   - Rewrites `sym::aggregate_raw_ptr(data, meta)` calls into `StatementKind::Assign(*destination, Rvalue::Aggregate(Box::new(AggregateKind::RawPtr(*pointee_ty, *mutability)), [data.node, meta.node]))` + `TerminatorKind::Goto`.
   - Rewrites `sym::ptr_metadata(ptr)` calls into `StatementKind::Assign(*destination, Rvalue::UnaryOp(UnOp::PtrMetadata, ptr.node))` + `TerminatorKind::Goto`.
   - Does **not** lower `sym::size_of_val` or `sym::align_of_val`; those remain `TerminatorKind::Call` intrinsics in `Runtime(PostCleanup)` MIR so `InstSimplify` can inspect them after inlining (`instsimplify.rs:270-271`).
2. **`LowerSliceLenCalls` (`lower_slice_len.rs:10-62`, enabled when `mir_opt_level > 0`, running first in `run_optimization_passes` before inlining, `lib.rs:700-702`):**
   - Matches `TerminatorKind::Call` targeting `tcx.lang_items().slice_len_fn()` (`<[T]>::len`) and replaces the call with `*destination = Rvalue::UnaryOp(UnOp::PtrMetadata, arg.node.clone())` followed by `Goto { target }`.
3. **`InstSimplify` (`instsimplify.rs:15-69`, enabled when `mir_opt_level > 0` — both `BeforeInline` and `AfterSimplifyCfg`):**
   - `simplify_ptr_aggregate` (`instsimplify.rs:172-184`): When `Rvalue::Aggregate(AggregateKind::RawPtr(pointee_ty, mutability), fields)` has `fields.raw[1].ty(...).is_unit()`, rewrites the aggregate to `Rvalue::Cast(CastKind::PtrToPtr, data, Ty::new_ptr(tcx, *pointee_ty, *mutability))`.
   - `simplify_size_or_align_of_val` (`instsimplify.rs:275-321`): Matches `TerminatorKind::Call` to `sym::size_of_val` or `sym::align_of_val`:
     * If `generic_ty.is_sized(tcx, typing_env)`, replaces **both** `size_of_val::<T>` and `align_of_val::<T>` with `Operand::unevaluated_constant` referencing `LangItem::SizeOf` / `LangItem::AlignOf` (note: folding `size_of_val::<Sized>(ptr)` discards `ptr` without reading metadata or checking dereferenceability, matching `mem::size_of_val_raw`'s safety contract at `mem/mod.rs:416`: *"If `T` is `Sized`, this function is always safe to call"*).
     * If `lang_item == LangItem::AlignOf` and `*generic_ty.kind() == ty::Slice(elem_ty)`, replaces `align_of_val::<[T]>` with `LangItem::AlignOf` instantiated at `elem_ty` (since slice element types are `Sized` and slice alignment is independent of length).
     * Leaves `size_of_val::<[T]>`, `size_of_val::<CustomDst>`, `align_of_val::<CustomDst>`, and both intrinsics on `dyn Trait` untouched.
   - Notably, `InstSimplify` contains **zero** `UnOp::PtrMetadata` folding rules.
4. **`GVN` (`gvn.rs:1291-1375`, enabled at `-Zmir-opt-level >= 2`):**
   `GVN::simplify_unary` performs value-numbering simplification on `UnOp::PtrMetadata`:
   - Peels metadata-preserving `Value::Cast { kind: CastKind::PtrToPtr, value: inner }` whenever `self.pointers_have_same_metadata(self.ty(inner), arg_ty)` (`gvn.rs:1315-1319`), guarding against metadata-erasing casts such as `*const [T] -> *const T`.
   - Peels unprojected reborrows `Value::Address { base: AddressBase::Deref(reborrowed), projection, .. }` **only if `projection.is_empty()`** (`gvn.rs:1334-1338`).
   - Folds `(UnOp::PtrMetadata, Value::RawPtr { metadata, .. }) => return Some(metadata)` (`gvn.rs:1359`), collapsing `ptr::metadata(ptr::from_raw_parts(data, meta))` directly to `meta`.
   - Folds array-to-slice unsizing (`gvn.rs:1322-1331,1361-1371`):
     ```rust
     Value::Cast {
         kind: CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _),
         value: from,
     } if let Some(from) = self.ty(from).builtin_deref(true)
         && let ty::Array(_, len) = from.kind()
         && let Some(to) = self.ty(arg_index).builtin_deref(true)
         && let ty::Slice(..) = to.kind() =>
     {
         return Some(self.insert_constant(Const::Ty(self.tcx.types.usize, *len)));
     }
     ```
   - Additionally, when the **entire** source pointer operand is compile-time constant (e.g., `&static_arr`), `GVN::eval_to_const` (`gvn.rs:758-766`) allocates a temporary stack place and invokes CTFE `self.ecx.unsize_into(src, ty, &dest)`.

#### 2.2 Empirical Sweep Across `-Zmir-opt-level=0..2` and the Custom-DST `GVN` Blind Spot

Executing `support/probe_unsizing_and_ptr_metadata.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` yields the following exact MIR construct counts per function (`support/unsizing_probe_results.json`):

| Specimen function | MIR opt `0` (`PtrMeta` / `Unsize` / `RawAgg` / `SizeVal` / `AlignVal`) | MIR opt `1` (`PtrMeta` / `Unsize` / `RawAgg` / `SizeVal` / `AlignVal`) | MIR opt `2` (`PtrMeta` / `Unsize` / `RawAgg` / `SizeVal` / `AlignVal`) | Key transition verified |
| :--- | :---: | :---: | :---: | :--- |
| `s01_array_to_slice_len` | `0 / 1 / 0 / 0 / 0` (`1` `::len` call) | `1 / 1 / 0 / 0 / 0` (`0` `::len` calls) | `0 / 1 / 0 / 0 / 0` (`_0 = const 4_usize`) | Opt 1: `LowerSliceLenCalls`; Opt 2: `GVN` folds `PtrMetadata(Unsize)` to `4_usize` |
| `s02_zst_slice_max_len` | `0 / 0 / 0 / 1 / 1` | `0 / 0 / 0 / 1 / 1` | `0 / 0 / 0 / 1 / 1` | Wrapper calls `ptr::from_raw_parts` / `mem::size_of_val` stay uninlined under `-Copt-level=0` |
| `s03_dst_wrap_slice_tail` | `2 / 1 / 0 / 1 / 1` | `2 / 1 / 0 / 1 / 1` | **`2 / 1 / 0 / 1 / 1`** (`const_4_usize = false`) | **Custom-DST blind spot:** `GVN` fails to fold `PtrMetadata` on `&DstWrap<[u32; 4]> -> &DstWrap<[u32]>` |
| `s04_nested_2level_dst_wrap` | `1 / 1 / 0 / 1 / 1` | `1 / 1 / 0 / 1 / 1` | `1 / 1 / 0 / 1 / 1` | 2-level nested `OuterWrap<DstWrap<[u32; 3]>>` keeps dynamic `PtrMetadata` bounds check |
| `s05_dyn_supertrait_upcast` | `0 / 5 / 0 / 0 / 0` | `0 / 3 / 0 / 0 / 0` | `0 / 3 / 0 / 0 / 0` | Concrete->`dyn SubTrait` + `dyn SubTrait`->`dyn BaseA` + `dyn SubTrait`->`dyn BaseB` (2 redundant reborrow casts simplified) |
| `s06_dst_wrap_dyn_tail` | `0 / 3 / 0 / 1 / 1` | `0 / 1 / 0 / 1 / 1` | `0 / 1 / 0 / 1 / 1` | `DstWrap<AlignedPayload> -> DstWrap<dyn SubTrait>` single surviving `Unsize` |
| `s07_custom_coerce_unsized` | `0 / 2 / 0 / 0 / 0` | `0 / 2 / 0 / 0 / 0` | `0 / 2 / 0 / 0 / 0` | `CustomPtr<[u32; 4]> -> CustomPtr<[u32]>` (`ScalarPair`) and `TaggedPtr<AlignedPayload> -> TaggedPtr<dyn SubTrait>` (`Memory`) |
| `s08_from_raw_parts_roundtrip` | `2 / 0 / 4 / 0 / 0` (`2` `PtrToPtr`) | `2 / 0 / 2 / 0 / 0` (`3` `PtrToPtr`) | `1 / 0 / 2 / 0 / 0` (`1` `PtrToPtr`) | Opt 1: `InstSimplify` folds thin `aggregate_raw_ptr(p, ()) -> PtrToPtr`; Opt 2: `GVN` folds `PtrMetadata(RawPtr)` |
| `s09_size_and_align_peephole` | `0 / 0 / 0 / 3 / 3` | `0 / 0 / 0 / 2 / 1` | `0 / 0 / 0 / 2 / 1` (`const_4_usize = true`) | Opt 1: `InstSimplify` folds `size_of_val::<u64>`, `align_of_val::<u64>`, and `align_of_val::<[u32]>`; keeps `[u32]` size and `DstWrap` size/align |
| `s10_packed_dst_wrap` | `0 / 1 / 0 / 1 / 1` | `0 / 1 / 0 / 1 / 1` | `0 / 1 / 0 / 1 / 1` | `#[repr(packed(2))] PackedDst<ManuallyDrop<AlignedPayload>> -> *const PackedDst<dyn SubTrait>` |

Comparing the emitted `-Zmir-opt-level=2` MIR for `s01_array_to_slice_len` against `s03_dst_wrap_slice_tail` (`unsizing_probe_results.json:348-349`) exposes the exact structural limitation in `GVN`:

```rust
// s01_array_to_slice_len at -Zmir-opt-level=2: folded to const 4_usize
bb0: {
    _2 = copy _1 as &[u32] (PointerCoercion(Unsize, Implicit));
    _0 = const 4_usize;
    return;
}

// s03_dst_wrap_slice_tail at -Zmir-opt-level=2: BOTH PtrMetadata ops remain unfolded!
bb0: {
    _2 = copy _1 as &DstWrap<[u32]> (PointerCoercion(Unsize, Implicit));
    _3 = PtrMetadata(copy _2);
    _5 = &raw const (*_2);
    _4 = std::intrinsics::size_of_val::<DstWrap<[u32]>>(move _5) -> [return: bb1, unwind unreachable];
}
...
bb2: {
    _8 = copy ((*_2).1: u16);
    _9 = copy ((*_2).0: u8);
    _11 = &raw const (fake) ((*_2).2: [u32]);
    _12 = PtrMetadata(copy _11);
    _13 = Lt(const 3_usize, copy _12);
    assert(move _13, "index out of bounds: the length is {} but the index is {}", move _12, const 3_usize) -> [success: bb3, unwind continue];
}
```

Two distinct guards in `GVN::simplify_unary` block folding in `s03_dst_wrap_slice_tail`:
1. In `bb0`, `_3 = PtrMetadata(copy _2)` inspects `_2: &DstWrap<[u32]>`, whose pointee is `ty::Adt(DstWrap, [Slice(u32)])` rather than `ty::Slice(..)`, failing `gvn.rs:1328,1367`. Replacing `from.kind()` / `to.kind()` with `tcx.struct_lockstep_tails_for_codegen(from, to, typing_env)` (proved sound in Theorem 2 of `support/UnsizingWidePointerSoundness.lean`) folds `_3` directly to `const 4_usize`.
2. In `bb2`, `_11 = &raw const (fake) ((*_2).2: [u32])` projects the unsized tail field `Field(2, [u32])`, failing `projection.is_empty()` at `gvn.rs:1335`. Because projecting a struct's unsized tail field preserves wide-pointer metadata identically (`PointerPlaceMachine` / `place.rs`), peeling tail-field projections whose pointee has identical metadata (`pointers_have_same_metadata`) would also eliminate the redundant bounds check `Lt(const 3_usize, copy _12)` at MIR level prior to LLVM IR lowering.

---

### 3. Wide Pointer `ScalarPair` ABI, `DynMetadata` Transmute Workaround, and VTable Header Layout

```text
Basis: source (compiler/rustc_ty_utils/src/layout.rs, compiler/rustc_middle/src/ty/vtable.rs, library/core/src/ptr/metadata.rs) + execution (support/unsizing_probe_results.json)
```

#### 3.1 `Scalar` vs. `ScalarPair` Pointer Layout and the `DynMetadata` Dual-Shape Hazard

In `compiler/rustc_ty_utils/src/layout.rs:413-487` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `layout_of_uncached` computes the layout of `ty::Ref(_, pointee, _)` and `ty::RawPtr(pointee, _)`:

1. `data_ptr` is initialized as `scalar_unit(Pointer(AddressSpace::ZERO))`, with `valid_range.start = 1` (non-null niche) for `ty::Ref` (unless `pointee` is uninhabited).
2. If `pointee.is_sized(tcx, cx.typing_env)` holds, `rustc` immediately returns `LayoutData::scalar(cx, data_ptr)` (`BackendRepr::Scalar`, `8` bytes, `align = 8` on 64-bit targets).
3. Otherwise, `rustc` normalizes `Ty::new_projection(tcx, metadata_def_id, [pointee])` (`<Pointee as Pointee>::Metadata`, `layout.rs:421-456`):
   - If `metadata_layout.is_1zst()` (which occurs for `extern` types `ty::Foreign(..)`, where `Metadata = ()`), the pointer is **still thin** (`LayoutData::scalar(cx, data_ptr)`, `layout.rs:457-459,470-472`).
   - Otherwise `metadata_layout.backend_repr` must be `BackendRepr::Scalar(metadata)`, and `rustc` returns `LayoutData::scalar_pair(cx, data_ptr, metadata)` (`BackendRepr::ScalarPair`, `16` bytes, `align = 8` on 64-bit targets, field `0` = `data_ptr` at offset `0`, field `1` = `metadata` at offset `8`).
   - When `metadata_def_id` is absent (early bootstrap fallback, `layout.rs:467-482`), `tcx.struct_tail_for_codegen(pointee, cx.typing_env)` classifies the leaf tail directly: `ty::Foreign(..)` -> thin scalar; `ty::Slice(_) | ty::Str` -> unsigned pointer-sized integer (`usize`, full `0..=usize::MAX` valid range); `ty::Dynamic(..)` -> `Pointer(AddressSpace::ZERO)` with `valid_range.start = 1` (non-null vtable pointer).
   - Meanwhile, the unsized pointee types `ty::Dynamic(_, _)` and `ty::Foreign(..)` themselves receive `LayoutData::unit(cx, /* sized = */ false)` (`size = 0`, **`align = 1`**, `BackendRepr::Memory { sized: false }`, `layout.rs:516-519`).

A subtle compiler-internal representation mismatch occurs on `DynMetadata<Dyn>` (`library/core/src/ptr/metadata.rs:158-185`): as a standalone Rust struct (`struct DynMetadata<Dyn> { _vtable_ptr: NonNull<VTable>, _phantom: PhantomData<Dyn> }`), `DynMetadata` has `FieldsShape::Arbitrary` (`Aggregate`), whereas inside field `1` of a wide pointer `LayoutData::scalar_pair` gives the metadata slot `FieldsShape::Primitive`. Attempting a MIR field projection `meta._vtable_ptr` on extracted metadata causes codegen ICEs, so `core` extracts the raw vtable pointer via `mem::transmute::<Self, *const VTable>(self)` (`metadata.rs:181-185`) and queries size and alignment via `core::intrinsics::vtable_size` and `core::intrinsics::vtable_align` (`metadata.rs:189-202`).

#### 3.2 Canonical VTable Header and Supertrait `TraitVPtr` Upcasting

In `compiler/rustc_middle/src/ty/vtable.rs:31-108`, every monomorphic vtable allocation (`vtable_allocation_provider`) is an array of `VtblEntry<'tcx>` whose fixed 3-word header is:

```rust
pub const COMMON_VTABLE_ENTRIES: &'tcx [VtblEntry<'tcx>] =
    &[VtblEntry::MetadataDropInPlace, VtblEntry::MetadataSize, VtblEntry::MetadataAlign];

pub const COMMON_VTABLE_ENTRIES_DROPINPLACE: usize = 0; // byte offset 0  on 64-bit
pub const COMMON_VTABLE_ENTRIES_SIZE: usize = 1;        // byte offset 8  on 64-bit
pub const COMMON_VTABLE_ENTRIES_ALIGN: usize = 2;       // byte offset 16 on 64-bit
```

Following slots `0..3` come method pointers (`VtblEntry::Method(Instance)`), `VtblEntry::Vacant` slots (for methods with unsatisfied `where Self: Sized` bounds), and embedded supertrait vtable pointers `VtblEntry::TraitVPtr(TraitRef)` used for multi-trait upcasting:

- **Primary-prefix supertrait upcast (`vptr_entry_idx == None`, `base.rs:208-210`, `cast.rs:427-433`):** When `SubTrait: BaseA + BaseB` places `BaseA`'s entries as an exact prefix of `SubTrait`'s vtable (`&vtable_entries[..vtable_entries_b.len()] == vtable_entries_b`), SSA codegen reuses `old_info` with **zero memory loads**, while CTFE/Miri (`cast.rs:428-437`) asserts the prefix property and substitutes the canonical `get_vtable_ptr(ty, data_b)` symbolic vtable so Miri's strict trait-tag check on `DynMetadata` (`m10_ub_wrong_trait_vtable_transmute`) remains exact!
- **Non-prefix secondary supertrait upcast (`vptr_entry_idx == Some(entry_idx)`, `base.rs:202-207`, `cast.rs:405-426`):** When upcasting `&dyn SubTrait -> &dyn BaseB`, codegen computes `vtable_byte_offset = entry_idx * ptr_size.bytes()` and loads the secondary vtable pointer directly from `old_info` (`load_vtable(bx, old_info, bx.type_ptr(), vtable_byte_offset, source, true)`), leaving the data pointer unchanged.
- Empirically (`s05_dyn_supertrait_upcast` and `s06_dst_wrap_dyn_tail` on `#[repr(align(16))] struct AlignedPayload([u64; 3])`, `size = 32`, `align = 16`): `s05_dyn_upcast = [32, 16, 32, 16, 303, 101, 202, true]`, confirming that `DynMetadata::size_of() == 32` and `align_of() == 16` match across `dyn SubTrait` and `dyn BaseB`, all three dispatched methods return `(303, 101, 202)`, the data pointer address is bit-identical (`raw_sub == raw_b`), and the secondary supertrait vtable pointer is distinct (`vptr_sub != vptr_b`). Note also the critical caveat documented at `metadata.rs:190-192`: for a custom DST `&DstWrap<dyn SubTrait>` (`s06_dst_dyn = [32, 16, 48, 16, 9]`), `DynMetadata::size_of()` returns **`32`** (the size of the `AlignedPayload` tail alone!), whereas `size_of_val_raw` on `*const DstWrap<dyn SubTrait>` returns **`48`** (`16`-byte aligned prefix + `32`-byte tail).

---

### 4. `StructKind::MaybeUnsized` Prefix-Field Offset Invariance vs. `AlwaysSized` Reordering and `#[repr(packed)]` DST Rules

```text
Basis: source (compiler/rustc_ty_utils/src/layout.rs:687-761, compiler/rustc_abi/src/layout.rs:266-297,535-548,1094-1328) + execution (support/unsizing_probe_results.json)
```

#### 4.1 How `rustc` Prevents `repr(Rust)` Field Reordering From Corrupting `Unsize`

Because `PointerCoercion::Unsize` reinterprets `&Struct<T>` as `&Struct<U>` **in-place** without copying memory (`unsize_into_ptr` only attaches metadata to the existing pointer), `Struct<T>` and `Struct<U>` must place every prefix field `0 .. n - 2` at the exact same byte offset—even under `repr(Rust)`'s default alignment-descending and niche-optimizing field reordering! `rustc` enforces this through a three-part mechanism:

1. **Generic-definition `maybe_unsized` classification (`compiler/rustc_ty_utils/src/layout.rs:687-706`):**
   ```rust
   let maybe_unsized = def.is_struct()
       && def.non_enum_variant().tail_opt().is_some_and(|last_field| {
           let typing_env = ty::TypingEnv::post_analysis(tcx, def.did());
           !tcx.type_of(last_field.did)
               .instantiate_identity()
               .skip_norm_wip()
               .is_sized(tcx, typing_env)
       });
   ```
   Crucially, `maybe_unsized` inspects `last_field` in **`def`'s uninstantiated identity environment** (`instantiate_identity()`), **not** the monomorphized `args`! Consequently, `DstWrap<u64>` (`struct DstWrap<T: ?Sized>`) is classified as `StructKind::MaybeUnsized` even though `u64` is `Sized`, whereas `SizedWrap<u64>` (`struct SizedWrap<T>`) is classified as `StructKind::AlwaysSized`.
2. **Tail exclusion from sorting, randomization, and end-biased niche retries (`compiler/rustc_abi/src/layout.rs:285-289,1112-1118` at `14210df0e2`; `L292-296,609-615` at `c7d5ba59d8`):**
   - In `univariant`, `if !matches!(kind, StructKind::MaybeUnsized)` suppresses the second `NicheBias::End` pass (`"otherwise we could end up with different layouts for Foo<Type> and Foo<dyn Trait> which would break unsizing"`).
   - In `univariant_biased`:
     ```rust
     let end = if let StructKind::MaybeUnsized = kind { fields.len() - 1 } else { fields.len() };
     let optimizing = &mut in_memory_order.raw[..end];
     let fields_excluding_tail = &fields.raw[..end];
     ```
     Both `optimizing.sort_by_key(...)`, `-Z randomize-layout` seed computation (`field_seed`), `max_field_align`, and `largest_niche_size` operate exclusively on `fields[..fields.len() - 1]`. The tail field `fields.len() - 1` stays last in `in_memory_order`!
   - Furthermore, debug-assertion builds of `rustc` execute a built-in self-audit (`rustc_ty_utils/src/layout.rs:713-761`) replacing the sized tail with `[u8]` (`align = 1`) and asserting `sized_fields == unsized_fields` and `sized_tail >= unsized_tail`.
3. **Empirical verification (`DstWrap<T: ?Sized>` vs. `SizedWrap<T>` in `unsizing_probe_results.json:421-469`):**
   Both structs declare identical fields `{ tag: u8, header: u16, tail: T }`:

   | Monomorphized type | `StructKind` | `offset(header: u16)` | `offset(tag: u8)` | `offset(tail)` | `size` | `align` |
   | :--- | :--- | ---: | ---: | ---: | ---: | ---: |
   | `DstWrap<u8>` | `MaybeUnsized` | `0` | `2` | `3` | `4` | `2` |
   | `DstWrap<[u32; 4]>` | `MaybeUnsized` | `0` | `2` | `4` | `20` | `4` |
   | `DstWrap<u64>` | `MaybeUnsized` | `0` | `2` | `8` | `16` | `8` |
   | `DstWrap<AlignedPayload>` | `MaybeUnsized` | `0` | `2` | `16` | `48` | `16` |
   | `&DstWrap<dyn SubTrait>` (runtime) | `MaybeUnsized` | `0` | `2` | `16` | `48` (dyn) | `16` (dyn) |
   | `SizedWrap<u8>` | `AlwaysSized` | `0` | `2` | `3` | `4` | `2` |
   | **`SizedWrap<u64>`** | **`AlwaysSized`** | **`8`** | **`10`** | **`0`** | **`16`** | **`8`** |

   Observe both halves of this invariant: inside `DstWrap`, `repr(Rust)` **still** reorders the prefix (`header: u16` moves before `tag: u8` to `(0, 2)`), while `tail` remains pinned after byte `3` (`alignUp(3, align(T)) = 3, 4, 8, 16`). In `SizedWrap<u64>`, omitting `?Sized` unlocks full-struct sorting, hoisting `tail: u64` to offset `0` and shifting `(header, tag)` to `(8, 10)`—demonstrating why `Unsize` is forbidden on `SizedWrap` and why Counterexample 2 (`ce2_non_tail_field_reordering_breaks_coerce_unsized`) is tight.

#### 4.2 `#[repr(packed(P))]` Unsized Tails Require Non-Drop Wrappers (`ManuallyDrop<T>`)

Compiling `#[repr(packed(2))] struct PackedDst<T: ?Sized> { tag: u8, tail: T }` directly in `rustc 1.98.0-nightly` fails with `E0277`:
> `note: the last field of a packed struct may only have a dynamically sized type if it does not need drop to be run`

Because `drop_in_place::<dyn Trait>` dispatches through vtable slot `0` expecting a naturally aligned `*mut Concrete`, dropping a misaligned `dyn Trait` tail inside a packed struct would cause immediate alignment UB. Wrapping the tail in `mem::ManuallyDrop<T>` (`#[repr(transparent)]`, guaranteed no-drop) satisfies `E0277` and exercises `rustc`'s dynamic packed-DST layout path (`eval_context.rs:468-472`, `size_of_val.rs:115-127`): for `PackedDst<AlignedPayload>` (`tag: u8` at `0`, `AlignedPayload` of `size = 32, align = 16` capped to `min(16, 2) = 2` at `alignUp(1, 2) = 2`), both native execution (`s10_packed = [34, 2, 90]`) and Miri (`m04_valid_packed2_dyn_dst_size_align`) confirm `size_of_val_raw == 34` and `align_of_val_raw == 2`.

---

### 5. CTFE/Miri (`unsize_into`, `size_and_align_from_meta`) vs. Codegen (`unsize_ptr`, `coerce_unsized_into`, `size_and_align_of_dst`)

```text
Basis: source (compiler/rustc_const_eval/src/interpret/{cast.rs, eval_context.rs, operator.rs, intrinsics.rs}, compiler/rustc_codegen_ssa/src/{base.rs, size_of_val.rs, mir/rvalue.rs}, compiler/rustc_middle/src/ty/util.rs) + execution (support/unsizing_probe_results.json)
```

#### 5.1 Lockstep Tail Peeling and Unification of `unsize_ptr` / `coerce_unsized_into`

Both Miri (`cast.rs:374-375`) and SSA codegen (`base.rs:168-169`) resolve pointee unsizing targets via `TyCtxt::struct_lockstep_tails_for_codegen` (`compiler/rustc_middle/src/ty/util.rs:321-373`) rather than independent `struct_tail_for_codegen` calls:
- Given `(Foo<Foo<T>>, Foo<dyn Trait>)`, `struct_lockstep_tails_raw` peels outer structs/tuples **only while both types share the same `AdtDef` (or tuple arity)**, stopping at `(Foo<T>, dyn Trait)` so `get_vtable_ptr` / `meth::get_vtable` builds the vtable for `Foo<T>` rather than `T` (`util.rs:315-316`).
- In `compiler/rustc_codegen_ssa/src/base.rs` (at both `14210df0e2:L223-315` and `c7d5ba59d8:L221-313`), historical `unsize_thin_ptr` has been eliminated in favor of unified `unsize_ptr(bx, src, src_ty, dst_ty, old_info: Option<Bx::Value>) -> (Bx::Value, Bx::Value)`:
  - When `dest.layout` has `BackendRepr::ScalarPair` (a wide reference, wide raw pointer, or `DispatchFromDyn`-compatible single-pointer wrapper such as `Box`/`NonNull`/`CustomPtr`), `mir/rvalue.rs:55-60,449-455` extracts `(lldata, llextra) = operand.val.pointer_parts()` (`llextra == None` iff `type_is_sized(a)`, asserted at `base.rs:235`) and calls `unsize_ptr` directly in SSA registers.
  - When `dest.layout` is a multi-field `CoerceUnsized` struct (`BackendRepr::Memory`, such as `TaggedPtr<T>` with `{ epoch: u32, raw: *const T }`, `16` bytes thin -> `24` bytes wide in `unsizing_probe_results.json:418-419`), `mir/rvalue.rs:63-66` delegates to `base::coerce_unsized_into` (`base.rs:270-315`), which skips `is_zst()` fields, `typed_place_copy`s unchanged fields (`epoch`), and recurses into the unique coerced pointer field (`raw`).

#### 5.2 Dynamic `size_of_val_raw` / `align_of_val_raw` Algebraic Identity and `isize::MAX` UB Preconditions

Comparing CTFE/Miri (`eval_context.rs:432-518`) against SSA codegen (`size_of_val.rs:15-184`) reveals an exact producer-consumer contract between UB checks and unchecked LLVM arithmetic:

1. **Slices (`[T]` and `str`):**
   - *Miri (`eval_context.rs:501-512`):* Computes `size = elem.size.bytes().saturating_mul(len)` (relying on `max_size_of_val() == isize::MAX < u64::MAX`) and throws **`InvalidMeta(InvalidMetaKind::SliceTooBig)`** if `size > isize::MAX`. For ZST elements (`elem.size == 0`), `0 * usize::MAX == 0 <= isize::MAX` succeeds cleanly (`m02_valid_zst_slice_usize_max`).
   - *Codegen (`size_of_val.rs:46-56`):* Emits `bx.unchecked_sumul(info.unwrap(), bx.const_usize(unit.size.bytes()))`—lowering to LLVM **`mul nuw nsw i64 %len, <elem_size>`** (`unchecked_sumul_nuw_nsw_present = true` in `unsizing_probe_results.json:346`), which produces LLVM `poison` if `len * elem_size > isize::MAX`!
2. **Trait objects (`dyn Trait`):**
   - *Miri (`eval_context.rs:495-499`, `traits.rs:38-47`):* Verifies that metadata is a genuine compiler-allocated vtable pointer for `Some(expected_trait)` (`get_ptr_vtable_ty`) and reads `(layout.size, layout.align.abi)` of the underlying sized concrete type. Furthermore, Miri's value-validity visitor enforces vtable authenticity and trait identity **immediately when a `*const dyn Trait` is constructed** (even before `size_of_val_raw` is called, as demonstrated by `m09` and `m10`).
   - *Codegen (`size_of_val.rs:28-45`):* Loads slot `1` (`size`) with LLVM `!range ![0, isize::MAX + 1)` metadata and slot `2` (`align`) with `!range ![1, max_align + 1)` metadata.
3. **Custom DST structs and tuples (`ty::Adt | ty::Tuple`):**
   Let `o = layout.fields.offset(last)` be the **unadjusted** tail offset (computed against `[T]`'s static element align or `dyn Trait`'s placeholder align `1`), `a_s = layout.align.abi` the static struct align, and `(s_u, a_u_raw)` the recursive dynamic size and alignment of the tail field. After capping `a_u = min(a_u_raw, pack)` if `#[repr(packed(pack))]` is present, `full_align = max(a_s, a_u)`.
   - *Miri (`eval_context.rs:480-493`)* computes `adjusted = o.align_to(a_u)` and `full_size = (adjusted + s_u).align_to(full_align)`, asserts `full_size == (o + s_u).align_to(full_align)` (which holds because `a_u` is a power of two dividing both `s_u` and `full_align`), and throws **`InvalidMeta(InvalidMetaKind::TooBig)`** if `full_size > isize::MAX`.
   - *Codegen (`size_of_val.rs:148-180`)* skips the intermediate `align_to(a_u)` and emits the bitmask round-up `((o + s_u) + (full_align - 1)) & -full_align` (`dst_align_bitmask_roundup_present = true` in `unsizing_probe_results.json:347`) with **no** overflow check—relying strictly on Miri's `full_size <= isize::MAX` safety precondition (`mem/mod.rs:419-420,429-430`).

#### 5.3 12-Case `Miri` (`-Zmiri-tree-borrows`) Litmus Matrix

All 12 litmus cases in `support/probe_unsizing_and_ptr_metadata.py` matched expected outcomes (`12/12`, `unsizing_probe_results.json:471-574`):

| Case ID | Scenario | Outcome | Recorded Miri diagnostic / invariant verified |
| :--- | :--- | :---: | :--- |
| `m01_valid_array_to_slice_and_raw_parts` | `&[u32; 4] -> &[u32] -> to_raw_parts -> from_raw_parts -> size_of_val_raw` | `PASS` | `size == 16`, `align == 4`, element `[2] == 30` |
| `m02_valid_zst_slice_usize_max` | `from_raw_parts::<[()]>(dangling, usize::MAX)` + `&*raw` + `size_of_val_raw` | `PASS` | `metadata == 2^{64}-1`, `size == 0 <= isize::MAX`, `align == 1` |
| `m03_valid_nested_dst_wrap_slice_and_dyn` | `DstWrap<[u32; 4]> -> &DstWrap<[u32]>` & `DstWrap<AlignedPayload> -> &DstWrap<dyn SubTrait>` + upcast `&dyn BaseB` | `PASS` | Dynamic `size_of_val_raw` (`20`, `48`) & `align_of_val_raw` (`4`, `16`) match static concrete layouts |
| `m04_valid_packed2_dyn_dst_size_align` | `#[repr(packed(2))] PackedDst<ManuallyDrop<AlignedPayload>> -> *const PackedDst<dyn SubTrait>` | `PASS` | `align_of_val_raw == 2` (`min(16, 2)`), `size_of_val_raw == 34` (`alignUp(1, 2) + 32`) |
| `m05_valid_zero_len_dangling_slice_size_of_val_raw` | `from_raw_parts::<[u64]>(without_provenance(8), 0)` + `size_of_val_raw` | `PASS` | `size_of_val_raw` uses `imm_ptr_to_mplace` without dereferencing (`intrinsics.rs:299-301`) |
| `m06_ub_slice_size_of_val_raw_isize_overflow` | `*const [u32]` with `len = (isize::MAX / 4) + 1` (`len * 4 == 2^{63}`) | `UB` | `invalid metadata in wide pointer: slice is bigger than largest supported object` |
| `m07_ub_slice_size_of_val_raw_u64_wrap_boundary` | `*const [u32]` with `len = 2^{62} + 1` (`(len * 4) mod 2^{64} == 4`) | `UB` | `invalid metadata in wide pointer: slice is bigger than largest supported object` (witnesses Lean `ce1`) |
| `m08_ub_struct_tail_prefix_pushes_over_isize_max` | `*const DstWrap<[u8]>` with `len = isize::MAX - 1` (`[u8]` alone passes, struct overflows) | `UB` | `invalid metadata in wide pointer: total size is bigger than largest supported object` (witnesses Lean `ce3`) |
| `m09_ub_forged_non_vtable_dyn_metadata` | `DynMetadata<dyn SubTrait>` forged via `transmute` from stack `[usize; 8]` array | `UB` | `constructing invalid value of type *const dyn SubTrait: encountered ..., but expected a vtable pointer` |
| `m10_ub_wrong_trait_vtable_transmute` | `DynMetadata<dyn UnrelatedTrait>` transmuted to `DynMetadata<dyn SubTrait>` | `UB` | `constructing invalid value of type *const dyn SubTrait: wrong trait in wide pointer vtable: expected SubTrait, but encountered UnrelatedTrait` |
| `m11_ub_misaligned_zst_slice_reference` | `&*from_raw_parts::<[ZeroSizedAlign8]>(without_provenance(4), 0)` | `UB` | `constructing invalid value of type &[ZeroSizedAlign8]: encountered an unaligned reference (required 8 byte alignment but found 4)` |
| `m12_ub_null_zst_slice_reference` | `&*from_raw_parts::<[()]>(null(), 0)` | `UB` | `constructing invalid value of type &[()]: encountered a null reference` |

---

### 6. `joshlf/anneal` Representation Audit and Exact TCB Extension Contract

```text
Basis: source (joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613: trusted/lean/Trusted/{MirAst.lean, MirSemantics.lean}, trusted/correspondence/Trusted/Correspondence.lean, vendor/lean-miri/Miri/Interpreter/{Cast.lean, DynamicLayout.lean, ScalarOps.lean}) + derived
```

#### 6.1 Current State in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`

Direct audit of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` reveals an intentional split between syntax/correspondence plumbing and Pass 1 operational semantics:

1. **`Trusted.MirAst` (`trusted/lean/Trusted/MirAst.lean`):**
   - `UnOp` (`L445-446`) **already declares** `| not | neg | ptrMetadata` 1-to-1 with `rustc_middle::mir::UnOp`.
   - `MirTy` (`L312-321`) includes `| ref (mutability : Mutability) (pointee : MirTy)` and `| rawPtr (mutability : Mutability) (pointee : MirTy)`, while routing `Array`, `Slice`, `Str`, `Dynamic`, and structs/ADTs (other than fieldless enums) to `| unsupported` (`L308-311`).
   - `ProjectionElem` (`L472-475`) includes `| deref` and `| field (fieldIdx : FieldIdx) (ty : MirTy)` while routing `Index`, `ConstantIndex`, and `Subslice` to `| unsupported`.
   - `Rvalue` (`L620-628`) includes `| unaryOp (op : UnOp) (opnd : Operand)`, `| ref`, and `| addressOf`, while routing `Cast` (including `PointerCoercion::Unsize`) and non-tuple `Aggregate` (including `AggregateKind::RawPtr`) to `| unsupported` (`L612-618`).
2. **`Trusted.MirSemantics` (`trusted/lean/Trusted/MirSemantics.lean`):**
   - `Rvalue.unaryOp` (`L1262-1268`) evaluates `opnd` through `evalPrimitiveOperand` (`L1007-1019`), which checks `isPrimitiveReadableTy ty`—Currently `true` only for `.bool`, `.int`, and admitted scalar-tagged `.enum` (rejecting `.ref` and `.rawPtr` immediately with `.error .unsupported`!).
   - Even if `evalUnOp` (`L1177-1193`) were called directly, its match handles only `(.not, .bool _)`, `(.not, .scalar _)`, and `(.neg, .scalar _)`, falling through on `.ptrMetadata` to `| _, _ => .error .unsupported` (`L1193`).
   - Thus every body containing `UnOp.ptrMetadata`, `PointerCoercion::Unsize`, or wide pointers currently steps deterministically to `FaultKind.unsupported`, falsifying `WellFormed`.
3. **`Trusted.Correspondence` and `vendor/lean-miri`:**
   - `Trusted.Correspondence.toMiriUnOp` (`trusted/correspondence/Trusted/Correspondence.lean:914-917`) already maps `| .ptrMetadata => .PtrMetadata`.
   - `vendor/lean-miri` already contains full reference mechanizations of `ScalarOps.unary` on `.PtrMetadata` (`Miri/Interpreter/ScalarOps.lean:138-149`), `Cast.cast` / `unsizeInto` / `unsizeIntoPointer` (`Miri/Interpreter/Cast.lean:241-315`, including `takePendingMoveDeinit` staging for `deinitMovedPlace = true`), and fuel-bounded `DynamicLayout.sizeAndAlignFromMeta` (`Miri/Interpreter/DynamicLayout.lean:40-86`).

#### 6.2 Six-Part TCB Extension Contract for Slice DSTs, `dyn Trait`, and Custom Tail DSTs

To discharge verification obligations over `&[T]`, `&mut [T]`, `*const [T]`, `dyn Trait`, and nested custom DSTs (`Wrapper<[T; N]> -> Wrapper<[T]>` and `Wrapper<Concrete> -> Wrapper<dyn Trait>`) in `joshlf/anneal` without weakening `TrustedBoundary.lean`:

1. **`Trusted.MirAst` Type & Rvalue Extension:**
   - Extend `MirTy` with `.array (elem : MirTy) (len : Nat)`, `.slice (elem : MirTy)`, `.str`, `.dynTrait (traitId : Nat) (autoTraits : List Nat)`, `.dynMetadata (traitId : Nat) (autoTraits : List Nat)`, and `.structAdt (def : StructTy)` carrying pre-computed `maybeUnsized : Bool`, `packedAlign : Option Nat`, `prefixOffsets : List Nat`, and `fields : List MirTy` (verified against `rustc`'s `TyAndLayout` by `anneal-rustc-capture`).
   - Extend `Rvalue` with `.unsizeCast (opnd : Operand) (dstTy : MirTy)`, `.ptrToPtrCast (opnd : Operand) (dstTy : MirTy)`, and `.rawPtrAggregate (mutability : Mutability) (pointee : MirTy) (data meta : Operand)`.
   - Extend `ProjectionElem` with `.index (localId : LocalId)`, `.constantIndex (offset : Nat) (minLen : Nat) (fromEnd : Bool)`, and `.subslice (fromIdx toIdx : Nat) (fromEnd : Bool)`.
   - Add `RawPtrKind` (or preserve `.addressOf` without retag) so `FakeForPtrMetadata` never triggers borrow-tag invalidation when Tree Borrows is enabled.
2. **Runtime Value Representation (`Val` in `Trusted.MirSemantics`):**
   - Represent pointers uniformly as `Val.ptr (addr : BitVec 64) (prov : Option AllocId) (meta : PtrMeta)` where `PtrMeta := .thin | .sliceLen (n : BitVec 64) | .vtable (vtId : VTableId)` (matching `BackendRepr::Scalar` when `meta = .thin` and `BackendRepr::ScalarPair` otherwise), and represent `DynMetadata` values as `Val.dynMeta (vtId : VTableId)`.
   - Extend `Program` with a read-only `vtables : List VTableDesc` table (`implTy : MirTy`, `principalTrait : Option Nat`, `autoTraits : List Nat`, `sizeBytes : Nat`, `alignBytes : Nat`, `dropCallee : Option DefId`, `entries : List VtblSlot`), checked by `BodyStaticAdmitted` / `ProgramStaticAdmitted` to satisfy `isSized implTy`, `sizeBytes == staticSize implTy <= 2^63 - 1`, `isPow2 alignBytes`, and `sizeBytes % alignBytes == 0`.
3. **Operational Rules for `UnOp.ptrMetadata` and `Rvalue.rawPtrAggregate` (`Trusted.MirSemantics`):**
   - Admit `.ref` and `.rawPtr` in `isPrimitiveReadableTy` (keeping reference non-null, alignment, and vtable-authenticity validity checks on `evalPrimitiveOperand` matching `Miri.Interpreter.ScalarOps.unary:140` `derefValidity`).
   - In `evalUnOp .ptrMetadata (.ptr _ _ meta)`:
     * `.thin` -> `.ok .unit` (recall `MirSemantics` represents inhabited `()` as `Val.unit`, corresponding to `lean-miri`'s zero-sized `Immediate.uninit` at `unitLayout` in `ScalarOps.lean:146-148`—`Trusted.Correspondence` must relate `Val.unit` at `MirTy.unit` to `(Immediate.uninit, unitLayout)`!).
     * `.sliceLen n` -> `.ok (.scalar ⟨.isize, false, bvZeroExtend 128 n⟩)`.
     * `.vtable vtId` -> `.ok (.dynMeta vtId)`.
   - Note on `deinitMovedPlace = true`: references `&T`, raw pointers `*const T` / `*mut T`, and `DynMetadata` are `Copy` (`Operand::Copy` in MIR), whereas moving `&mut [T]` or `Box<[T]>` via `Operand.move` deinitializes the moved 16-byte local slot in `evalOperandToSlot` (`MirSemantics.lean:961-972`), matching `Cast.lean:294-298` (`immediate` source path). For multi-field `CoerceUnsized` structs in memory (`TaggedPtr`), `evalRvalue` must buffer into a temporary before move-deinitializing the source place (`Cast.lean:299-310`) and validate the whole destination **once** after copying unchanged sibling fields (`copy_op_no_validate`, `c7d5ba59d8` `cast.rs:568-571`).
4. **Operational Rules for `Rvalue.unsizeCast` (`PointerCoercion::Unsize`):**
   - Implement `structLockstepTails srcPointee dstPointee` (`ty/util.rs:341-373`) by structural recursion on `MirTy` (carrying `noncomputable` so `TrustedBoundary.validateRepoConstant` sees zero `partial` / `._unsafe_rec` helpers!).
   - Dispatch leaf pairs: `(.array elem n, .slice elem')` -> attach `.sliceLen n`; `(concrete, .dynTrait ..)` -> look up authenticated `vtId` in `Program.vtables`; `(.dynTrait .., .dynTrait ..)` -> verify source `vtId` and resolve target supertrait `vtId` via `TraitVPtr` slot or prefix identity.
5. **Intrinsic Semantics for `size_of_val` / `align_of_val` and `vtable_size` / `vtable_align`:**
   - Implement `sizeAndAlignFromMeta` over `MirTy` and `PtrMeta` enforcing `<= 2^63 - 1` (`isize::MAX` on 64-bit) at **both** the `.slice` arm (`FaultKind.undefined` on `elemSize * len > 2^63 - 1`) and the `.structAdt` arm (`FaultKind.undefined` on `alignUp (alignUp tailOffUnadjusted tailAlign + tailSize) fullAlign > 2^63 - 1`, applying `min(tailAlign, pack)` when `packedAlign = some pack`).
6. **Pass 2 Correspondence Obligations (`Trusted.Correspondence`):**
   - Prove lockstep simulation against `Miri.Interpreter.ScalarOps.unary`, `Miri.Interpreter.Cast.cast`, and `Miri.Interpreter.DynamicLayout.sizeAndAlignFromMeta` across both the `.ok` pole and the `FaultKind.undefined` pole (`InvalidMeta(SliceTooBig)`, `InvalidMeta(TooBig)`, invalid vtable pointer, misaligned/null wide reference).

---

### 7. Kernel-Checked `Lean v4.34.1` Mechanization and Sharpness Counterexamples

```text
Basis: execution + derived (support/UnsizingWidePointerSoundness.lean checked by Lean v4.34.1 kernel)
```

`support/UnsizingWidePointerSoundness.lean` (`1,076` LOC, `396` kernel declarations) mechanizes the core type, layout, metadata-folding, and dynamic-size soundness theory in standalone `Lean v4.34.1` under Anneal's strict `TrustedBoundary` discipline (`noncomputable` structural recursion throughout, primitive `Bool` `match` elimination avoiding `Nat.decLe` WHNF blowup on $2^{63}$ bounds, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`):

1. **Prefix-Field Offset and Pointer-Projection Invariance (`prefix_field_offset_invariant_under_tail_unsizing`, `prefix_field_projection_commutes_with_unsize`, `nested_slice_tail_prefix_offsets_invariant`):**
   Models `repr(Rust)` alignment-descending insertion sort (`sortFieldsDescAlign`) over `prefixFields : List FieldSpec` (`maybeUnsizedFieldOffset`) versus full-struct sorting over `prefixFields ++ [tail]` (`alwaysSizedFieldOffset`). Proves that for all `i < prefixFields.length` and arbitrary `tailSrc, tailDst : DstTy`, `maybeUnsizedFieldOffset prefixFields tailSrc i = maybeUnsizedFieldOffset prefixFields tailDst i`, that `projectPrefixField` commutes with `unsizePtr`, and that arbitrary paths through two-level nested slice-tail wrappers (`OuterWrap<DstWrap<[T; N]>> -> OuterWrap<DstWrap<[T]>>`) preserve exact byte offsets from the outer pointer base.
2. **`PtrMetadata` Peephole & Generalized Lockstep-Tail Folding Soundness (`ptrMetadata_peephole_folding_sound`):**
   Defines `MirPtrExpr` covering local pointers, `rawPtrAggregate`, `&*` `reborrowDeref`, metadata-preserving `ptrToPtrSameMeta`, `unsizeArrayToSlice`, and `unsizeLockstepStructSlice` (via `structLockstepTails`). Proves by structural induction that whenever `foldPtrMetadataStatic e = some foldedMeta` and `evalMirPtrExpr e = some runtimePtr`, `evalPtrMetadata runtimePtr = foldedMeta`—certifying both `rustc`'s existing `GVN::simplify_unary` rewrites and the lockstep-tail extension that closes `s03_dst_wrap_slice_tail`'s folding gap.
3. **Dynamic Layout Exactness, `<= isizeMax` Bound, and Allocation Span Containment (`sizeOfValChecked_le_isizeMax`, `validUnsize_thin_matches_static_layout`, `validUnsize_sizeAndAlignChecked_eq`, `unsized_span_contained_in_source_allocation`):**
   Defines the inductive `ValidUnsize` relation covering `arrayToSlice` (including ZST slices), `sizedToDyn`, `dynUpcast`, and arbitrarily nested `structTail`. Proves that:
   - Every successful `sizeOfValChecked vtEnv isizeMax ty ptrMeta = some sz` satisfies `sz ≤ isizeMax`;
   - Every thin-source `ValidUnsize` derivation preserves exact `(staticSize srcTy, staticAlign srcTy)` across arbitrary struct-tail nesting;
   - Whenever `staticSize srcTy ≤ isizeMax` and `SpanInBounds alloc p.prov p.addr (staticSize srcTy)`, `sizeOfValChecked` and `alignOfValChecked` on `unsizePtr p metaOut` succeed with `some (staticSize srcTy)` and `some (staticAlign srcTy)`, and the unsized wide pointer's dynamic span remains strictly within `alloc`.
   - Kernel-reduced `concrete_specimens_kernel_verified` confirms `&[(); 2^{64} - 1] -> some (0, 1)`, `DstWrap<[u32]> (len = 4) -> some (20, 4)`, and `OuterWrap<DstWrap<[u32]>> (len = 3) -> some (32, 8)` via `rfl`, matching `unsizing_probe_results.json` bit-for-bit.
4. **Three Kernel-Checked Sharpness Counterexamples:**
   - **`ce1_unchecked_slice_byte_size_overflow_unsound`:** At `elemSize = 4`, `forgedLen = 2^{62} + 1`, and `allocBytes = 8` on 64-bit (`isizeMax64 = 2^{63} - 1`), unchecked modular arithmetic `uncheckedWrappingByteSize64 0 forgedLen 4` wraps modulo $2^{64}$ to `4 ≤ allocBytes`, falsely admitting a slice whose valid index `victimIdx = 2 < forgedLen` accesses bytes `[8, 12)` past `allocBytes = 8`, whereas `sizeOfValChecked` returns `none` (matching Miri `m07`).
   - **`ce2_non_tail_field_reordering_breaks_coerce_unsized`:** On `{ tag: u8, header: u16, tail: T }`, full-struct `alwaysSizedFieldOffset` places `header` at `some 8` for `T = u64` versus `some 0` for `T = dyn Trait` (`some 8 ≠ some 0`), corrupting prefix field projections across `Unsize`, whereas `maybeUnsizedFieldOffset` preserves `header = some 0` and `tag = some 2` (matching `SizedWrap<u64>` vs. `DstWrap<u64>`).
   - **`ce3_prefix_plus_valid_slice_overflows_isizeMax`:** At `edgeLen = 2^{63} - 2` (`isizeMax64 - 1`), `sizeOfValChecked` accepts `[u8]` (`= some 9223372036854775806`) while rejecting `DstWrap<[u8]>` (`= none`) because `3 + (2^{63} - 2) = 2^{63} + 1 > 2^{63} - 1` (matching Miri `m08`).

## Boundaries

- **`extern type` (`ty::Foreign`) unsized tails — unsupported in `size_of_val_raw` / `align_of_val_raw` and unmodeled in Lean:** While `<Foreign as Pointee>::Metadata = ()` makes pointers to `extern` types thin (`rustc_ty_utils/src/layout.rs:457-459,470-472`), calling `size_of_val_raw` or `align_of_val_raw` on an `extern` type (or a struct with an `extern` tail) returns `err_unsup_format!("extern type does not have known layout")` in CTFE/Miri (`intrinsics.rs:304`, `eval_context.rs:460-462,514`) and emits an unconditional `LangItem::PanicNounwind` abort call in SSA codegen (`size_of_val.rs:57-89`).
- **`DynMetadata` pointer equality (`PartialEq` / `Eq`) across codegen units and dynamic libraries — known not to apply as type/trait identity:** Although `DynMetadata<Dyn>` implements `PartialEq` by comparing `vtable_ptr()` addresses (`library/core/src/ptr/metadata.rs:240-245`), `metadata.rs:154-157` explicitly warns that identical `(Concrete, Trait)` pairs can have **distinct** vtable addresses across multiple codegen units or `cdylib`s, and distinct types/traits can share a deduplicated vtable address within a codegen unit. Verifiers must never treat `PtrMetadata(p) == PtrMetadata(q)` on `dyn Trait` as necessary or sufficient for concrete-type equality.
- **Custom `GVN` folding of `PtrMetadata` on `dyn Trait` vtables — known not to apply to non-const sources in MIR:** Unlike slice unsizing (where length `N` is a monomorphic `usize` constant in `[T; N]`), concrete-to-`dyn` unsizing produces a symbolic `AllocId` vtable pointer that cannot be materialized as a scalar integer constant in generic/polymorphic MIR (`gvn.rs:758-766` folds `Unsize` to `dyn Trait` only when the entire source pointer evaluates to a CTFE constant).
- **16-bit and 32-bit target `isize::MAX` bounds — not examined empirically:** Empirical execution in `support/probe_unsizing_and_ptr_metadata.py` ran on 64-bit `x86_64-unknown-linux-gnu` (`isize::MAX = 2^{63} - 1`), matching `joshlf/anneal`'s `pointerWidthBits == 64` gate (`MirAst.lean:901-905`). The mechanized theorems in `support/UnsizingWidePointerSoundness.lean` parameterize `isizeMax : Nat` abstractly and hold for any pointer width, while `ce1` and `ce3` instantiate concrete 64-bit bounds.
- **Experimental `arbitrary_self_types` / `derive_smart_pointer` ergonomics and `PatternKind` (`ty::Pat`) unsizing — not examined empirically:** Source paths for `ty::Pat` inside `cast.rs:469-474` and `base.rs:232,278-284` were inspected statically (noting that `ty::util::struct_lockstep_tails_raw:349-370` peels `Adt` and `Tuple` without a `ty::Pat` arm, unlike `struct_tail_raw:299-302`), and were not exercised in the empirical specimen suite.

## Evidence

### Primary-Source Coordinates

All repository revisions were resolved to full 40-hex commit hashes:

| Subject repository & commit | File path & line range | Symbol / construct inspected |
| :--- | :--- | :--- |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) | `compiler/rustc_middle/src/mir/syntax.rs:110-112,186-192,1499-1515,1610-1617` (`c7d5ba59d8:L110-112,186-192,1510-1526,1621-1628`) | `RuntimePhase::PostCleanup`, `RawPtrKind::FakeForPtrMetadata`, `CastKind::PointerCoercion`, `UnOp::PtrMetadata` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_middle/src/ty/adjustment.rs:11-40,217-229` | `PointerCoercion::Unsize`, `CoerceUnsizedInfo`, `CustomCoerceUnsized::Struct` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_middle/src/ty/util.rs:229-373` | `type_has_metadata`, `struct_tail_raw`, `struct_lockstep_tails_for_codegen` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_middle/src/ty/vtable.rs:31-108` | `VtblEntry`, `COMMON_VTABLE_ENTRIES` (`DROPINPLACE=0, SIZE=1, ALIGN=2`), `vtable_allocation_provider` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) | `compiler/rustc_mir_transform/src/lower_intrinsics.rs:291-334` | Lowering `sym::aggregate_raw_ptr` -> `AggregateKind::RawPtr` and `sym::ptr_metadata` -> `UnOp::PtrMetadata` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) | `compiler/rustc_mir_transform/src/lower_slice_len.rs:10-62` | `LowerSliceLenCalls` rewriting `<[T]>::len` -> `UnOp::PtrMetadata` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) | `compiler/rustc_mir_transform/src/instsimplify.rs:172-184,275-321` (`c7d5ba59d8:L170-182,272-318`) | `simplify_ptr_aggregate` and `simplify_size_or_align_of_val` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) | `compiler/rustc_mir_transform/src/gvn.rs:655-666,758-766,1291-1375` | `GVN::simplify_unary` (`UnOp::PtrMetadata` over `RawPtr` & `Slice` `Unsize`) and `eval_to_const` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) | `compiler/rustc_const_eval/src/interpret/cast.rs:365-516` (`c7d5ba59d8:L433-588`) | `unsize_into_ptr`, `unsize_into` (`copy_op` vs. `copy_op_no_validate` delta) |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) | `compiler/rustc_const_eval/src/interpret/{eval_context.rs:432-518, operator.rs:487-501, intrinsics.rs:298-313, traits.rs:38-47}` | `size_and_align_from_meta`, `UnOp::PtrMetadata` eval, `size_of_val`/`align_of_val` intrinsics, `get_vtable_size_and_align` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) | `compiler/rustc_codegen_ssa/src/{base.rs:161-315, size_of_val.rs:15-184, mir/rvalue.rs:48-66,449-455,616-625}` | `unsized_info`, `unsize_ptr`, `coerce_unsized_into`, `size_and_align_of_dst` (`unchecked_sumul` + bitmask padding) |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) | `compiler/rustc_ty_utils/src/layout.rs:421-519,687-761` & `compiler/rustc_abi/src/layout.rs:266-297,535-548,1094-1328` (`c7d5ba59d8:L273-304,555-565,596-830`) | `ScalarPair` fat-pointer layout, `maybe_unsized`, `StructKind::MaybeUnsized` prefix-only field sorting & debug self-check |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `library/core/src/{ptr/metadata.rs:56-267, mem/mod.rs:401-459,548-598, ops/unsize.rs:35-134, marker.rs:208-237}` | `Pointee`, `Thin`, `metadata`, `from_raw_parts`, `DynMetadata::vtable_ptr` transmute, `size_of_val_raw`, `align_of_val_raw`, `CoerceUnsized`, `DispatchFromDyn`, `Unsize` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/{MirAst.lean:308-321,445-446,472-475,612-628, MirSemantics.lean:1007-1019,1177-1193,1262-1268}` | `UnOp.ptrMetadata`, fail-closed `MirTy.unsupported` / `Rvalue.unsupported` / `evalPrimitiveOperand` / `evalUnOp` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/correspondence/Trusted/Correspondence.lean:914-917`, `trusted/audit/TrustedBoundary.lean:73-104`, `vendor/lean-miri/Miri/Interpreter/{Cast.lean:241-315, DynamicLayout.lean:40-86, ScalarOps.lean:138-149}` | `toMiriUnOp`, `TrustedBoundary` partial/`_unsafe_rec` prohibition, vendored `lean-miri` reference semantics (pinned to `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`) |

### Package Support Artifacts (Observed `2026-11-21`)

- `support/probe_unsizing_and_ptr_metadata.py`: Standalone Python 3 stdlib harness compiling 10 Rust unsizing/metadata specimens across `-Zmir-opt-level=0,1,2` (`--emit=mir,llvm-ir`), executing native layout/offset/vtable assertions, building a hermetic `-Zalways-encode-mir` `core` + `compiler_builtins` sysroot in a temporary directory, and running 12 `miri -Zmiri-tree-borrows` litmus cases.
- `support/unsizing_probe_results.json`: Captured, path-scrubbed JSON output from `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0`.
- `support/UnsizingWidePointerSoundness.lean`: Standalone `Lean v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) kernel-checked mechanization (`396` declarations; `#print axioms` shows `[propext]` on propositional equality/conjunction theorems and zero axioms on `ce2_non_tail_field_reordering_breaks_coerce_unsized`; `0` `sorryAx`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `Lean.ofReduceBool`, `0` `partial`, `0` `._unsafe_rec`).

## Revalidation

1. **Re-run the empirical `rustc` (`-Zmir-opt-level=0..2`) + native + `Miri` (`-Zmiri-tree-borrows`) suite (~20 seconds, completely offline):**
   ```bash
   python3 reports/rustc-unsizing-coercions-wide-pointer-metadata-and-slice-dst-soundness/support/probe_unsizing_and_ptr_metadata.py \
     --out /tmp/recheck_unsizing_probe.json
   diff -u \
     reports/rustc-unsizing-coercions-wide-pointer-metadata-and-slice-dst-soundness/support/unsizing_probe_results.json \
     /tmp/recheck_unsizing_probe.json
   rm -f /tmp/recheck_unsizing_probe.json
   ```
   A clean exit (`12/12 Miri cases matched, 3 MIR opt levels`) re-establishes all MIR pass transitions, `DstWrap` vs. `SizedWrap` field-offset measurements, LLVM `mul nuw nsw` emission, and Miri UB boundaries on the active toolchain. If a future `rustc` generalizes `GVN::simplify_unary` to use `struct_lockstep_tails_for_codegen`, `mir_opt_level_2.s03_dst_wrap_slice_tail.ptr_metadata_ops` will drop from `2` to `1` (or `0` if tail-field projections are also peeled) and `const_4_usize` will flip from `false` to `true`.

2. **Re-verify the `Lean v4.34.1` mechanization under strict kernel checking (~3 seconds):**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-unsizing-coercions-wide-pointer-metadata-and-slice-dst-soundness/support/UnsizingWidePointerSoundness.lean
   ```

3. **Targeted upstream source checks when updating `rust-lang/rust` or `joshlf/anneal` pins:**
   - Diff `compiler/rustc_mir_transform/src/{lower_intrinsics.rs, lower_slice_len.rs, instsimplify.rs, gvn.rs}` around `UnOp::PtrMetadata` and `AggregateKind::RawPtr` to check whether `PtrMetadata` folding moved passes or gained struct-tail support.
   - Diff `compiler/rustc_abi/src/layout.rs` (`StructKind::MaybeUnsized`, `end = fields.len() - 1`) and `compiler/rustc_ty_utils/src/layout.rs` (`maybe_unsized` and `ScalarPair` pointer layout) to verify prefix-offset invariance.
   - Diff `trusted/lean/Trusted/{MirAst.lean, MirSemantics.lean}` in `joshlf/anneal` around `UnOp.ptrMetadata` and `MirTy` to check whether wide-pointer execution has transitioned from `.error .unsupported` to modeled semantics.
