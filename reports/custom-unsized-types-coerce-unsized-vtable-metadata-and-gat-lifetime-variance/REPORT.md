# Custom Unsized Types, CoerceUnsized, Vtable Metadata, and GAT Lifetime Variance

## Summary

Rust's custom dynamically sized types (DSTs), smart-pointer unsizing (`CoerceUnsized` and `DispatchFromDyn`), trait-object upcasting, zero-copy slice-DST casting (`KnownLayout` and `SplitAt`), and Generic Associated Types (GATs) concentrate layout, ABI, and subtyping invariants in compiler-enforced traits and normalization ordering:

1. **Pointee Classification and Composite `DynMetadata` Pitfalls:** Under `Pointee: PointeeSized`, every `?Sized` pointee inherits `<Self as Pointee>::Metadata` recursively from its unsized tail (`()` for `Sized` and `extern type`, `usize` for `[T]`/`str`, and `DynMetadata<dyn Trait>` for trait objects). `DynMetadata<Dyn>` exhibits dual layout magic (`FieldsShape::Primitive` inside wide pointers vs. `FieldsShape::Aggregate` standalone, requiring `transmute` in `DynMetadata::vtable_ptr`), and `metadata(ptr).size_of()` reads *only* the erased tail's vtable size slot—excluding prefix fields and alignment padding on composite structs like `(Header, dyn Trait)`, which require `mem::size_of_val_raw`.
2. **Asymmetry Between `CoerceUnsized` and `DispatchFromDyn`:** `CoerceUnsized` allows `#[repr(C)]` structs and arbitrary unchanged non-`PhantomData` fields, comparing fields by syntactic equality (`a == b`) before normalization to avoid constraining opaque types and recording `CustomCoerceUnsized::Struct(i)`. `DispatchFromDyn` enforces raw-pointer ABI compatibility: it forbids `#[repr(C)]` and `#[repr(packed)]`, demands identical `&`/`*` mutability, and rejects unchanged non-`PhantomData` fields unless they satisfy `layout.is_1zst() && !ty_a.has_non_region_param()`. For `Pin<Ptr>`, both traits additionally require `Ptr: PinSafePointer`.
3. **Hybrid Vtable Layout and Upcasting as Coercion:** In `rustc_middle`, `VtblEntry<'tcx>` places a three-word header (`MetadataDropInPlace`, `MetadataSize`, `MetadataAlign`) before post-order trait entries (`Method`, `Vacant`, `TraitVPtr`). The first-supertrait `PrefixSet` shares the header prefix (zero-cost identity upcasts), whereas secondary supertraits receive embedded `TraitVPtr` slots pointing to distinct supertrait vtables. Because non-prefix upcasts load and swap the wide pointer's metadata word at runtime, trait upcasting (`&dyn Sub -> &dyn Super`) is a *coercion*, not subtyping—blocking `Vec<Box<dyn Sub>>` to `Vec<Box<dyn Super>>`.
4. **`zerocopy` Slice-DST Algebra (`DstLayout` and `TrailingSliceLayout`):** `zerocopy` models slice DSTs via `size_base + round_up(size_phase + elems * elem_size, size_align)`, packing `(size_align, size_phase)` bijectively into `RoundingAlignAndPhase = align | phase`. Packed wrappers (`#[repr(C, packed(2))]` over an `align(4)` slice DST) decouple `DstLayout::align` from `size_align` and decouple `offset % size_align` from `size_phase`. Suffix casts validate `(addr + bytes_len) % align == 0` because completed-layout object sizes are multiples of `align`; `dyn Trait` and `extern type` remain excluded from `KnownLayout`.
5. **Pre-Normalization GAT Invariance and MIR Lifetime Erasure:** During `rustc` variance inference, every argument to an unnormalized alias (`<T as Trait>::Assoc<'a>`) is unconditionally **invariant** via `add_constraints_from_invariant_args`, regardless of concrete `&'a U` impls. Normalization recovers concrete field covariance only after instantiation, whereas `dyn Trait<T> + 'a` is covariant in `'a` and invariant in trait/projection args. Post-borrowck MIR erases all regions (including GAT lifetimes and `for<'a>` HRTBs), leaving concrete MIR verifiers with explicit `PointerCoercion::Unsize` casts while requiring polymorphic specs to model unnormalized GATs as opaque families.

---

## Applicability

This report synthesizes normative specifications, compiler and standard-library sources, zero-copy layout math, and formal type-safety literature across six durable subjects:

- **`rust-lang/rust` (`ec65cd52bba13d491ff65c9d218b39753755c84a`):** Covers `library/core/src/{marker,pin}.rs`, `library/core/src/ptr/metadata.rs`, `library/core/src/ops/unsize.rs`, `compiler/rustc_middle/src/ty/vtable.rs`, and `compiler/rustc_hir_analysis/src/{coherence/builtin,variance/constraints}.rs`.
- **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** Covers `src/{dynamically-sized-types,type-coercions,subtyping}.md`.
- **`rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`):** Covers RFCs `0982` (DST coercion), `1598` (GATs), `2580` (`ptr_metadata`), and `3324` (`dyn` upcasting).
- **`google/zerocopy` (`1962a9c0e3eda8a3a58387f61c70ddd2c396b118`):** Covers `zerocopy/src/{lib,layout,split_at}.rs`.
- **Peer-reviewed PL literature:** Jung et al., *RustBelt* (`10.1145/3158154`, POPL 2018), and Chakravarty et al., *Associated Types with Class* (`10.1145/1040305.1040306`, POPL 2005).

**Stability and cross-corpus scope:** GATs (Rust 1.65) and trait upcasting coercions (Rust 1.86) are stable; `Pointee` (`ptr_metadata`), `Unsize` (`unsize`), `CoerceUnsized` (`coerce_unsized`), `DispatchFromDyn` (`dispatch_from_dyn`), `#[derive(CoercePointee)]` (`derive_coerce_pointee`), `PinSafePointer` (`pin_coerce_unsized_trait`), and `MetaSized`/`PointeeSized` (`sized_hierarchy`) remain nightly-gated at `ec65cd52bba1` while backing stable coercion and dynamic-dispatch lowering. Prior reports cover thin/wide pointer provenance (`rust-raw-pointer-validity-provenance-and-wide-metadata`), `#[repr(C)]` aggregate layout (`rust-aggregate-dst-and-target-layout-guarantees`), coinductive `KnownLayout` trait policies (`rust-unsafe-traits-coinduction-gats-and-safety-invariants`), and cross-DSO vtable deduplication/ICF (`cross-dso-dynamic-linking-vtable-uniqueness-and-open-world-lto-contracts`).

---

## Findings

### 1. Custom DST Taxonomy, `Pointee::Metadata`, and Composite `DynMetadata` Layout

**Basis:** normative (`rust-lang/reference` `src/dynamically-sized-types.md:1-44`, RFC 2580) + source (`library/core/src/marker.rs:159-193`, `library/core/src/ptr/metadata.rs:56-212`, `zerocopy/src/lib.rs:1134-1165`) + derived.

Under `library/core/src/marker.rs:159-193`, Rust organizes size constraints into three compiler-implemented marker traits (`#[rustc_deny_explicit_impl]`, `#[rustc_coinductive]`): `Sized: MetaSized` (compile-time constant size, `()` metadata), `MetaSized: PointeeSized` (runtime size computable from pointer metadata alone via `size_of_val_raw`), and `PointeeSized` (top bound permitting `extern type`).

In `library/core/src/ptr/metadata.rs:56-68`, `Pointee: PointeeSized` defines `type Metadata: fmt::Debug + Copy + Send + Sync + Ord + Hash + Unpin + Freeze` (omitting `'static` because `DynMetadata<dyn Trait + 'a>` carries `'a` via `PhantomData<Dyn>`). Metadata is determined solely by a type's unsized tail (`src/dynamically-sized-types.md:10-30`, `metadata.rs:24-29`):

| Pointee Form | `MetaSized`? | `<T as Pointee>::Metadata` | 64-Bit Ptr Width | Key Representation Invariants |
| :--- | :--- | :--- | :--- | :--- |
| `T: Sized` | Yes | `()` | `8` B (thin) | Zero-sized metadata (`Thin = Pointee<Metadata = ()> + PointeeSized`). |
| `extern type E` | **No** | `()` | `8` B (thin) | `E: Thin`, yet `mem::size_of_val_raw` is unsupported; opaque external size. |
| `[T]` / `str` | Yes | `usize` | `16` B (wide) | Element count for `[T]` (`len * size_of::<T>()` bytes); byte count for `str`. |
| `dyn Trait + 'a` | Yes | `DynMetadata<dyn Trait + 'a>` | `16` B (wide) | Non-null `NonNull<VTable>` pointing to immutable compiler vtable allocation. |
| Custom `struct S<U: ?Sized>` | Matches `U` | `<U as Pointee>::Metadata` | Matches `U` | Prefix fields must be `Sized`; metadata governs only tail field `U`. |

Three implementation pitfalls govern wide-pointer metadata handling:

1. **`DynMetadata` Layout Duality (`metadata.rs:173-186`):** Inside a wide pointer (`*const dyn Trait`), `rustc_middle` overrides `DynMetadata<Dyn>` to `FieldsShape::Primitive` rather than `FieldsShape::Aggregate`. Standalone `DynMetadata<Dyn>` values remain aggregates wrapping `NonNull<VTable>` and `PhantomData<Dyn>`, so projecting fields directly triggered codegen ICEs; `DynMetadata::vtable_ptr` therefore extracts the raw pointer via `mem::transmute::<Self, *const VTable>(self)`.
2. **Composite Tail Size Mismatch (`metadata.rs:188-196`):** Calling `ptr::metadata(p).size_of()` on a composite DST struct like `#[repr(C)] struct Frame { hdr: u32, payload: dyn Send }` invokes `intrinsics::vtable_size(...)` for `dyn Send` alone—**excluding** `u32`, inter-field padding, and trailing alignment rounding. Callers must use `mem::size_of_val_raw(p)` for total byte size.
3. **Pre-1.79 Slice Metadata Authentication (`google/zerocopy/src/lib.rs:1135-1165`):** Before `*mut [T]::len` stabilized in Rust 1.79, `zerocopy` recovered slice lengths without `ptr_metadata` or dereferencing potentially unaligned/dangling pointers by hashing `*mut [T]` to capture the second `Hasher::write_usize` word (`metadata`) and authenticating it with `ptr::eq(ptr, NonNull::slice_from_raw_parts(data, len).as_ptr())`. Because `ptr::eq` compares both address and metadata, an untrusted `Hash` impl cannot forge bogus metadata.

---

### 2. `Unsize`, `CoerceUnsized`, `DispatchFromDyn`, and `#[derive(CoercePointee)]` Soundness

**Basis:** normative (`rust-lang/reference` `src/type-coercions.md:179-211`, RFC 0982) + source (`library/core/src/ops/unsize.rs:34-137`, `library/core/src/marker.rs:200-238, 1153-1296`, `library/core/src/pin.rs:1813-1972`, `compiler/rustc_hir_analysis/src/coherence/builtin.rs:247-463, 655-888, 1013-1041`) + literature (`RustBelt` `10.1145/3158154`).

`Unsize<U>` (`core_marker.rs:200-238`) is compiler-synthesized for `[T; N] -> [T]`, `T -> dyn Trait + 'a` (`T: Trait + Sized + 'a`), `dyn TraitA + AutoA + 'a -> dyn TraitB + AutoB + 'b` (supertrait/auto-trait/region weakening), and `Struct<.., T_i, ..> -> Struct<.., U_i, ..>` when **only the last field** changes via `Field<T_i>: Unsize<Field<U_i>>`.

In `compiler/rustc_hir_analysis/src/coherence/builtin.rs`, wrapper unsizing (`CoerceUnsized`) and dynamic-dispatch receiver conversion (`DispatchFromDyn`) enforce deliberately asymmetric structural rules:

| Invariant / Check | `CoerceUnsized<T>` (`builtin.rs:655-888`) | `DispatchFromDyn<T>` (`builtin.rs:287-463`) | `#[derive(CoercePointee)]` (`builtin.rs:1013-1041`) |
| :--- | :--- | :--- | :--- |
| **Built-In Ptr/Ref Impls** | `&'b mut -> &'a mut`, `&'b mut -> &'a`, `&'a mut -> *mut/*const`, `&'b -> &'a`, `&'a -> *const`, `*mut -> *mut/*const`, `*const -> *const` | **Same mutability & region only**: `&'a -> &'a`, `&'a mut -> &'a mut`, `*const -> *const`, `*mut -> *mut` (`builtin.rs:343-348`) | Generates `CoerceUnsized` + `DispatchFromDyn` plus `CoercePointeeValidated` |
| **ADT Kind & `#[repr]`** | `struct` only (`def_a == def_b`); **`#[repr(C)]` allowed** | `struct` only (`def_a == def_b`); **forbids `#[repr(C)]` and `#[repr(packed)]`** (`builtin.rs:364-366`) | `struct` only; **requires `#[repr(transparent)]`** (`builtin.rs:1034-1036`), rejects manual impls |
| **Unchanged Fields** | Skips `PhantomData` (normalized) and **all fields with `a == b`** (`builtin.rs:803-814`) | Skips `PhantomData`; unchanged fields (`ty_a == ty_b`) **must satisfy `layout.is_1zst() && !ty_a.has_non_region_param()`** (`builtin.rs:391-411`) | Non-empty; ZST fields may not reference generic parameters unless `PhantomData` (`marker.rs:1259-1260`) |
| **Changed Field Obligation** | Exactly `1` diff field (`CustomCoerceUnsized::Struct(i)`), requiring `Field_a: CoerceUnsized<Field_b>` | Exactly `1` diff field, requiring `Field_a: DispatchFromDyn<Field_b>` (`builtin.rs:425-433`) | Single non-ZST field must be a std pointer (`&`, `*`, `NonNull`, `Box`, `Rc`, `Arc`) or `CoercePointee` wrapper |
| **Soundness Rationale** | Value coercion rebuilds the struct by converting field `i` and copying siblings | Vtable shims pass `Wrapper<dyn Tr>` at call ABI **as if `#[repr(transparent)]` around a raw pointer** (`builtin.rs:322-330`) | Prevents custom receivers from violating ABI-transparency or ZST erasure invariants |

Three critical soundness defenses emerge from `builtin.rs` and `pin.rs`:
1. **Syntactic `a == b` Without Normalization (`builtin.rs:803-814`):** `coerce_unsized_info` skips normalization and variance checks on unchanged fields (`if a == b`) because coercion checking runs inside bodies where opaque `impl Trait` types must not be prematurely constrained.
2. **Blocking Parameterized 1-ZSTs in `DispatchFromDyn` (`builtin.rs:391-403`):** Even when a sibling field is a 1-aligned ZST (`layout.is_1zst()`), `builtin.rs:399` forbids type parameters (`!ty_a.has_non_region_param()`), preventing user wrappers from smuggling arbitrary ZST proof tokens or capability witnesses (`RustBelt` `10.1145/3158154`) across type-erased `dyn` dispatch.
3. **`Pin<Ptr>` and `PinSafePointer` (`library/core/src/pin.rs:1813-1972`):** Generic `impl<Ptr: Deref, U> CoerceUnsized<Pin<U>> for Pin<Ptr>` would be unsound if `Ptr` moved its referent during `deref_mut`, altered target addresses, wrapped in an `Unpin` adapter, or treated `&Ptr` in `Clone`/`Debug` as proof of unpinned ownership (as `Arc::get_mut` does). `core::pin` therefore gates `Pin`'s `CoerceUnsized` and `DispatchFromDyn` impls on `unsafe trait PinSafePointer: Deref + Sized` (`pin.rs:1834-1899`), paired with coherence restrictions blocking malicious downstream `DerefMut` impls on `Pin<LocalType>` (`pin.rs:1953-1958`).

---

### 3. Vtable Memory Representation and RFC 3324 Trait-Upcasting Conversion

**Basis:** source (`compiler/rustc_middle/src/ty/vtable.rs:12-156`) + documentation (`rust-lang/rfcs` `text/3324-dyn-upcasting.md:89-180`) + normative (`rust-lang/reference` `src/type-coercions.md:193-197`) + execution.

In `compiler/rustc_middle/src/ty/vtable.rs:12-51`, each vtable allocation is an array of pointer-sized `VtblEntry<'tcx>` words: `MetadataDropInPlace` (slot `0`, null pointer when `!ty.needs_drop`), `MetadataSize` (slot `1`), `MetadataAlign` (slot `2`), `Vacant` (uninitialized padding slot for `where Self: Sized` non-dispatchable methods, skipped at `vtable.rs:135`), `Method(Instance<'tcx>)`, and `TraitVPtr(TraitRef<'tcx>)`.

When `vtable_allocation_provider` constructs the static read-only `Allocation` for `(ty, poly_trait_ref)` (`vtable.rs:84-156`), it erases and anonymizes regions (`tcx.erase_and_anonymize_regions`, line `92`), asserts `layout.is_sized()` (line `106`), and follows RFC 3324's hybrid post-order algorithm (`RFC 3324` lines 107–111):
- Define `PrefixSet(Tr)` as `Tr` followed recursively by each trait's **first** supertrait.
- Deduplicate the supertrait DAG into a post-order traversal; for every `TraitRef`, emit its `Method`/`Vacant` slots, and **if `TraitRef ∉ PrefixSet(Tr)`**, emit `TraitVPtr(TraitRef)` pointing to the separate supertrait vtable `tcx.vtable_allocation((ty, Some(super_trait_ref)))` (`vtable.rs:142-147`).

On a diamond hierarchy (`trait A { fn foo_a; }`, `trait B: A { fn foo_b; }`, `trait C: A { fn foo_c; }`, `trait D: B + C { fn foo_d; }`):
- `PrefixSet(D) = {D, B, A}`: slots `0..5` of `<S as D>` (`[DropInPlace, Size, Align, A::foo_a, B::foo_b]`) match `<S as B>` identically, so `*const dyn D -> *const dyn B` leaves the metadata word unchanged.
- `C ∉ PrefixSet(D)`: `<S as D>` emits `C::foo_c` (slot `5`), `TraitVPtr(<S as C>)` (slot `6`), and `D::foo_d` (slot `7`). Upcasting `*const dyn D -> *const dyn C` keeps the data pointer and provenance intact while **loading slot `6`** to replace `DynMetadata<dyn D>` with `DynMetadata<dyn C>`.

Because non-prefix upcasting mutates the wide-pointer metadata representation at runtime rather than reinterpreting unchanged bits, **trait upcasting is a coercion, not subtyping** (`RFC 3324` line 95): `Box<dyn D>` coerces to `Box<dyn C>`, whereas `Vec<Box<dyn D>>` cannot coerce to `Vec<Box<dyn C>>` and `&mut Box<dyn D>` cannot coerce to `&mut Box<dyn C>`. Furthermore, because safe code may upcast `*const dyn Trait` raw pointers (`RFC 3324` lines 158–160), raw pointers exposed to safe upcasts must carry genuine `Trait` vtable metadata rather than dummy integers.

---

### 4. `zerocopy` Slice-DST Layout Algebra and Cast Metadata Synthesis

**Basis:** source (`google/zerocopy@1962a9c0e3eda8a3a58387f61c70ddd2c396b118` `zerocopy/src/lib.rs:746-1077`, `zerocopy/src/layout.rs:34-546, 1560-1853`, `zerocopy/src/split_at.rs:15-104, 324-337`) + execution + derived.

To cast arbitrary byte slices `&[u8]` / `&mut [u8]` to slice DSTs without nightly `ptr_metadata`, `google/zerocopy` emits a compile-time `const LAYOUT: DstLayout` for every `KnownLayout` type (`zerocopy/src/layout.rs:34-50`), storing `align: NonZeroUsize`, `size_info: SizeInfo` (`Sized { size } | SliceDst(TrailingSliceLayout)`), and `statically_shallow_unpadded: bool`.

#### 4.1 `RoundingAlignAndPhase` and the Normalized Object-Size Law
`TrailingSliceLayout` (`layout.rs:153-207`) compresses nested `#[repr(C)]`, `#[repr(transparent)]`, and `#[repr(packed(N))]` slice-DST structures into four numbers: `(offset, elem_size, size_base, size_rounding_align_and_phase)`. `RoundingAlignAndPhase` (`layout.rs:65-148`) packs a power-of-two `size_align` and `size_phase ∈ 0..size_align` into one `NonZeroUsize` via `align | phase`, decoding `align = 1 << ((POINTER_WIDTH_BITS - 1) - encoded.leading_zeros())` and `phase = encoded ^ align`. For `elems >= 0` trailing elements, total object size satisfies:

$$\text{object\_size}(\text{elems}) = \text{size\_base} + \operatorname{round\_up}(\text{size\_phase} + \text{elems} \cdot \text{elem\_size},\ \text{size\_align})$$

Two layout subtleties (`layout.rs:196-206`) invalidate naive approximations:
- **`size_align > DstLayout::align` and `size_phase != offset % size_align`:** Wrapping `#[repr(C, align(4))] struct Inner { tag: u8, tail: [u8] }` (`align=4, offset=1, size_base=0, size_align=4, size_phase=1`) inside `#[repr(C, packed(2))] struct Outer { hdr: u16, inner: Inner }` reduces overall alignment to `DstLayout::align = 2` while preserving `Inner`'s internal 4-byte rounding (`size_align = 4`, `size_phase = 1`, `size_base = 2`, `offset = 3`). Thus `offset % 4 = 3 != 1 = size_phase`, and `object_size(0..=3) = 6`, `object_size(4) = 10`.

#### 4.2 Prefix/Suffix Cast Inversion and `SplitAt` Overlap Rules
`DstLayout::validate_cast_and_convert_metadata(addr, bytes_len, cast_type)` (`layout.rs:1705-1853`) validates slice casts in $O(1)$ arithmetic:
1. **ZST Panic Guard (`layout.rs:1743-1746`):** Trailing zero-sized elements (`elem_size == 0`) trigger an immediate `const_panic!` before inspecting `addr`/`bytes_len`, avoiding ambiguous infinite element counts.
2. **Endpoint Alignment (`layout.rs:1757-1780`):** Prefix casts check `addr % align == 0`; suffix casts check `(addr + bytes_len) % align == 0`. Under completed layouts, `object_size(elems)` is always a multiple of `align`, so end-alignment implies start-address alignment `(addr + bytes_len - object_size) % align == 0`.
3. **Closed-Form Capacity & Remainder (`layout.rs:252-341, 1791-1834`):** Let `rounded_phase = 0` if `size_phase == 0` else `size_align`, and `minimum_size = size_base + rounded_phase`. When `bytes_len >= minimum_size`, `aligned_bytes = round_down(bytes_len - minimum_size, size_align)` and `initial_padding = rounded_phase - size_phase < size_align` combine disjointly via bitwise OR to give `max_slice_bytes = aligned_bytes | initial_padding`, yielding `elems = max_slice_bytes / elem_size`. When `elem_size` does not divide `size_align` (e.g., `[u8; 3]` in `4` bytes), `unused_bytes = max_slice_bytes % elem_size` leaves `1` unconsumed byte outside `self_bytes = 3`.
4. **`SplitAt` Padding Overlap (`split_at.rs:15-104, 324-337`):** Because `padding_for_elems(l_len)` (`layout.rs:360-415`) varies modulo `size_align`, splitting `&mut Packet` at `l_len` overlaps the left object's trailing padding with `&mut [Packet::Elem]` unless `T: IntoBytes` (`via_into_bytes`), statically unpadded (`via_no_dynamic_padding`), or dynamically verified (`via_runtime_check`); packed structs wrap `Elem` in `Unalign<...>`.

---

### 5. GAT Lifetime Variance, Normalization Ordering, and Higher-Ranked Bounds

**Basis:** source (`compiler/rustc_hir_analysis/src/variance/constraints.rs:181-328`) + normative (`rust-lang/reference` `src/subtyping.md:1-113`, RFC 1598 `text/1598-generic_associated_types.md:108-315`) + literature (`10.1145/1040305.1040306`) + derived.

Generic Associated Types (RFC 1598) enable zero-copy lending views (`trait BufferSource { type View<'a> where Self: 'a; }`). Unlike Haskell type families (`10.1145/1040305.1040306`), Rust GATs interact with **lifetime subtyping variance** (`'long: 'short`).

Inspecting `ConstraintContext::add_constraints_from_ty` (`compiler/rustc_hir_analysis/src/variance/constraints.rs:208-328`) establishes how `rustc` computes variance for aliases and trait objects:
- **Unnormalized GAT Projections (`ty::Projection | ty::Inherent | ty::Opaque`, lines 263–272):** Immediately invoke `add_constraints_from_invariant_args(current, args, variance)` (lines `182-202`), forcing **invariance** on *every* lifetime, type, and const argument passed to `<T as Trait>::Assoc<'a>`. Consequently, a generic struct `struct ViewHolder<'a, B: BufferSource>(B::View<'a>)` is permanently invariant in `'a` (and `B`), even if every in-scope impl defines `type View<'a> = &'a [u8]`, because a sound crate-level signature must hold against downstream impls defining `type View<'a> = &'a mut &'a [u8]` or `fn(&'a u8)`.
- **Free Aliases (`ty::Free`, lines 274–277):** Expand eagerly via `expand_free_alias_tys` before constraining fields, preserving concrete variance.
- **Trait Objects (`ty::Dynamic`, lines 279–301):** `dyn Trait<T> + 'a` is **covariant** in its region bound `'a` (line `281`), **invariant** in `data.principal()` trait arguments (lines `283-289`), and **invariant** in all `data.projection_bounds()` (`Assoc<'b> = Term`, lines `291-300`).

At concrete call sites (after substituting concrete `B = SliceBuf`), type checking normalizes `<SliceBuf as BufferSource>::View<'a>` to `&'a [u8]` *before* subtyping, restoring covariance in `'a` directly on the normalized type—while `ViewHolder<'a, SliceBuf>` itself stays invariant in `'a` because ADT variance is fixed once per `struct` declaration!

Combining GATs with Higher-Ranked Trait Bounds (`for<'a> B: BufferSource<View<'a> = &'a [u8]>`, `RFC 1598` lines 203–218) triggers two additional constraints:
1. **Implied `where Self: 'a` Bounds:** Returning `&'a Self` from `type View<'a>` requires `where Self: 'a` on the trait's GAT declaration. Under `for<'a> B: BufferSource`, `rustc` skolemizes `'a` to a universal `ty::Placeholder`, requiring `B: 'static` unless the `Self: 'a` bound is satisfied locally via implied bounds on a borrowing method signature (`fn view<'a>(&'a self) -> Self::View<'a>`).
2. **Higher-Ranked Subtyping (`src/subtyping.md:21-37`):** Just as `for<'a> fn(&'a i32) -> &'a i32` is a subtype of `fn(&'static i32) -> &'static i32`, a higher-ranked trait object `dyn for<'a> Fn(&'a i32) -> &'a i32` subtypes `dyn Fn(&'static i32) -> &'static i32`. However, when an unnormalized GAT mentions a bound lifetime inside `for<'a> F: FnOnce(T::Item<'a>)`, late normalization can prevent region inference from finding covariant relaxations.

---

### 6. MIR Lowering, Region Erasure, and Formal Verification Obligations

**Basis:** source (`compiler/rustc_middle/src/ty/vtable.rs:84-156`, `compiler/rustc_hir_analysis/src/coherence/builtin.rs:846-848`) + literature (`RustBelt` `10.1145/3158154`) + execution + derived.

In post-cleanup MIR, `rustc` erases all lifetimes and HRTB binders (`tcx.erase_and_anonymize_regions`) and represents coercions explicitly via `Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), operand, target_ty)`. A sound Rust verifier must discharge four obligations across these features:

1. **Coercion Drill-Down (`CustomCoerceUnsized::Struct(i)`):** Project field `i`, coerce it recursively (`&`/`*` -> `Unsize`), and preserve all sibling fields (including allocators permitted by `CoerceUnsized`) byte-for-byte with provenance intact.
2. **Vtable Construction & Upcast Transitions:** `T -> dyn Tr` attaches a read-only `Allocation` matching `T`'s drop glue, `size`, and `align`; `dyn Sub -> dyn Super` either leaves metadata invariant (`Super ∈ PrefixSet(Sub)`) or loads slot `TraitVPtr(Super)` from the source vtable.
3. **Byte-Cast Slice-DST Certificates:** Validate `(addr + (bytes_len if Suffix else 0)) % align == 0`, `object_size(elems) <= bytes_len`, and `object_size(elems) <= isize::MAX` before materializing `&Dst` / `&mut Dst`.
4. **GAT Region Erasure Soundness:** Erasing `'a` in monomorphized MIR is sound precisely because borrowck + GAT `where Self: 'a` WF + pre-normalization invariance (`constraints.rs:263-272`) prevent unsound lifetime shrinking upstream (`RustBelt` `10.1145/3158154`). Pre-monomorphization verifiers reasoning generically over `T: Trait` must treat unnormalized `T::Assoc` as an uninterpreted type family indexed by erased arguments.

#### Executable Verification Model (`RoundingAlignAndPhase`, Slice-DST Casts, and RFC 3324 Vtables)
Executing the Python 3 reference model below verified `143` `RoundingAlignAndPhase` round-trips, **77,760** `(align, size_align, size_phase, size_base, elem_size, bytes_len, cast_type)` combinations against a brute-force oracle, the packed-wrapper witness (`object_size(0)=6`, `object_size(3)=6`, `object_size(4)=10`), and RFC 3324 diamond vtables (`8` entries for `<S as D>` with `TraitVPtr(<S as C>)` at index `6`):

```python
def rap_new(align: int, phase: int) -> int:
    assert align > 0 and (align & (align - 1)) == 0 and 0 <= phase < align
    return align | phase

def rap_components(encoded: int, width: int = 64) -> tuple[int, int]:
    shift = (width - 1) - (width - encoded.bit_length())
    align = 1 << shift
    return align, encoded ^ align

def validate_cast(align: int, size_base: int, rap: int, elem_size: int,
                  addr: int, bytes_len: int, suffix: bool):
    if (addr + (bytes_len if suffix else 0)) % align != 0:
        return None
    sa, sp = rap_components(rap)
    r_phase = 0 if sp == 0 else sa
    min_sz = size_base + r_phase
    if min_sz > bytes_len:
        return None
    aligned = (bytes_len - min_sz) & ~(sa - 1)
    max_slice = aligned | (r_phase - sp)
    elems = max_slice // elem_size
    unused = max_slice % elem_size
    max_rounded = (bytes_len - size_base) & ~(sa - 1)
    self_bytes = size_base + (max_rounded - (unused & ~(sa - 1)))
    return elems, (bytes_len - self_bytes if suffix else self_bytes)
```

---

## Boundaries

- **unsupported:** Manual implementations of `Pointee`, `Sized`, `MetaSized`, `PointeeSized`, and `Unsize` are **unsupported** (`#[rustc_deny_explicit_impl]`, `metadata.rs:57`, `marker.rs:153,172,189,234`). Arbitrary non-auto multi-supertrait objects (`dyn SuperA + SuperB`) are **unsupported** (`RFC 3324` lines 12, 84). In `google/zerocopy`, `KnownLayout` and `DstLayout` are **unsupported** for `dyn Trait` and `extern type` tails (`SizeInfo` supports only `Sized` and `SliceDst`).
- **known not to apply:** Covariance of `&'a T` is **known not to apply** to unnormalized GAT projections `<T as Trait>::Assoc<'a>` inside `rustc` ADT variance inference (`constraints.rs:263-272`). `DynMetadata::size_of` is **known not to apply** as full-object byte size on composite structs ending in `dyn Trait` (`metadata.rs:191-193`); `DynMetadata::eq` is **known not to apply** as a type-identity check due to CGU duplication and ICF (`metadata.rs:155-158`); and `offset % size_align == size_phase` is **known not to apply** to `#[repr(C, packed(N))]` wrappers around higher-alignment slice DSTs (`layout.rs:196-206`).
- **unknown:** The final Rust Abstract Machine validity invariant for `*const dyn Trait` with forged/dummy vtable metadata when never dereferenced, passed to `size_of_val_raw`, or upcast (`RFC 3324` lines 156–163) remains **unknown**.
- **not examined:** Experimental `dyn*` pointer-sized existentials, `ty::View` (`constraints.rs:325-326`), `ty::UnsafeBinder` variance (`constraints.rs:311-314`), and `#[repr(Rust)]` field-reordering heuristics for custom DST tails were **not examined**.

---

## Evidence

Verified on `2026-11-20`:

| Subject | Immutable Identity | Inspected Paths & Anchors | Claims Grounded |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `ec65cd52bba13d491ff65c9d218b39753755c84a` | `library/core/src/ptr/metadata.rs:56-268`; `library/core/src/marker.rs:145-238,1153-1296`; `library/core/src/ops/unsize.rs:34-137`; `library/core/src/pin.rs:1813-1972`; `compiler/rustc_middle/src/ty/vtable.rs:12-156`; `compiler/rustc_hir_analysis/src/coherence/builtin.rs:247-463,655-888,1013-1041`; `compiler/rustc_hir_analysis/src/variance/constraints.rs:181-328` | `Pointee`/`DynMetadata` duality & size pitfall; `Sized: MetaSized: PointeeSized`; `CoerceUnsized` vs `DispatchFromDyn` vs `CoercePointee`; `PinSafePointer`; `VtblEntry`; `add_constraints_from_invariant_args` |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `src/dynamically-sized-types.md:1-44`; `src/type-coercions.md:179-211`; `src/subtyping.md:1-113` | Recursive tail metadata, unsized coercions, HRTB subtyping |
| `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | `text/1598-generic_associated_types.md:108-315`; `text/2580-ptr-meta.md:60-250`; `text/3324-dyn-upcasting.md:89-200` | GAT HRTB equality, `Pointee`, RFC 3324 `TraitVPtr` post-order layout |
| `google/zerocopy` | `1962a9c0e3eda8a3a58387f61c70ddd2c396b118` | `zerocopy/src/lib.rs:746-1165`; `zerocopy/src/layout.rs:34-546,1560-1853`; `zerocopy/src/split_at.rs:15-104,324-337` | `KnownLayout`, `Hash`+`ptr::eq` extraction, `RoundingAlignAndPhase`, `TrailingSliceLayout`, `SplitAt` overlap |
| PL papers | DOI `10.1145/3158154`; DOI `10.1145/1040305.1040306` | Jung et al. (*RustBelt*, POPL 2018); Chakravarty et al. (POPL 2005) | Semantic wrapper soundness & ZST tokens; associated-type normalization |
| Algebraic Probe | Python 3 stdlib (`2026-11-20`) | Inline script in **Findings §6** | `PROBE_A PASS: rap_roundtrips=143, dst_cast_oracle_cases=77760, packed_outer_size0=6, d_vtable_len=8` |

---

## Revalidation

Run the following self-contained check (`< 1 s`, Python 3.10+ stdlib only) to verify upstream invariants and re-execute the packed-DST & `RoundingAlignAndPhase` probe:

```bash
RUST_SHA="ec65cd52bba13d491ff65c9d218b39753755c84a"
ZC_SHA="1962a9c0e3eda8a3a58387f61c70ddd2c396b118"
curl --http1.1 -fsSL "https://raw.githubusercontent.com/rust-lang/rust/${RUST_SHA}/compiler/rustc_hir_analysis/src/variance/constraints.rs" | grep -n -A 8 "Projection"
curl --http1.1 -fsSL "https://raw.githubusercontent.com/rust-lang/rust/${RUST_SHA}/compiler/rustc_middle/src/ty/vtable.rs" | grep -n -A 6 "pub enum VtblEntry"
curl --http1.1 -fsSL "https://raw.githubusercontent.com/google/zerocopy/${ZC_SHA}/zerocopy/src/layout.rs" | grep -n -A 10 "pub(crate) struct RoundingAlignAndPhase"

python3 - <<'PY'
def round_up(n, a): return (n + a - 1) & ~(a - 1)
def rap_comp(enc):
    s = 63 - (64 - enc.bit_length())
    a = 1 << s
    return a, enc ^ a
for a in (1, 2, 4, 8, 16):
    for p in range(a):
        assert rap_comp(a | p) == (a, p)
sa, sp = rap_comp(4 | 1)
assert [2 + round_up(sp + e, sa) for e in (0, 3, 4)] == [6, 6, 10]
print("Revalidation OK")
PY
```
