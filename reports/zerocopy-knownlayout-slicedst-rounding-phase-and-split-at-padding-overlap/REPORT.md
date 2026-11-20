# KnownLayout Slice-DST Rounding-Phase Algebra, split_at Trailing-Padding Overlap, Zero-Element Suffix Alignment, and Lean 4 Mechanization

## Summary

Verifying zero-copy parsing and in-place splitting over Rust slice dynamically sized types (DSTs) requires replacing fixed scalar byte widths with a parametric affine rounding algebra over trailing-element count `elems : usize`. Primary-source inspection of `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, contrasted with `312cb70a655ab25936fefb4d1b8c1787c782876e`), `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`), `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) establishes four core invariants:

1. **Affine `TrailingSliceLayout` and `RoundingAlignAndPhase` (`zerocopy/src/layout.rs`):** Every valid `#[repr(C)]` slice DST normalizes to `(offset, elem_size, size_base, size_rounding_align_and_phase)`, where `RoundingAlignAndPhase` packs power-of-two `size_align` and `size_phase < size_align` into `NonZeroUsize` (`align | phase`), yielding exact size `size_base + round_up(size_phase + elems * elem_size, size_align)` without division. Wrapping a higher-alignment DST inside `#[repr(packed)]` (`Packed<Inner<[u8]>>`) drops `obj_align` to `1` while retaining `size_align = 4`, so `T: Unaligned` does **not** guarantee zero trailing padding.
2. **`PtrInner::split_at_unchecked` Trailing-Padding Overlap (`zerocopy/src/pointer/inner.rs`, `split_at.rs`):** Splitting at `l_len < total_len` places `left`'s trailing padding directly atop `right`'s starting bytes (`[base + offset + l_len * elem_size, base + size_for_elems(l_len))`), causing Tree Borrows (`10.1145/3735592`) and Stacked Borrows (`10.1145/3371109`) UB under `&mut` or `!Freeze` interior mutation unless guarded by `via_immutable`, `via_into_bytes`, `via_no_dynamic_padding`, or `via_runtime_check`.
3. **Metadata Non-Injectivity and Zero-Element Suffix Alignment (`zerocopy/src/ref.rs`):** Dynamic trailing padding collapses distinct counts (`1` and `8` both give `16` bytes on `Frame`), while `from_suffix_with_elems(src, 0)` on an unaligned end address (`base + 13` for `[AU64]`) must still reject misalignment and return the whole unsplit `source` (fixed in `ec133ce4...` after `312cb70a...` returned a truncated split subslice).
4. **Closed-Form `DstLayoutAlgebra` in 3-Axiom `prelude` Lean 4:** Replacing `lean-miri`'s recursive `DynamicLayout.sizeAndAlignFromMeta` traversal with closed-form `TrailingSliceLayout` evaluation yields an `@Nat.rec`-free `prelude` Lean `v4.34.1` module (`Anneal.DstLayoutAlgebra`) admissible under `joshlf/anneal`'s strict `TrustedBoundary.lean` non-TCB envelope.

## Applicability

This report examines and connects six software repositories, three peer-reviewed formalization papers, and one execution probe environment:

1. **`google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897` vs. `312cb70a655ab25936fefb4d1b8c1787c782876e`):** Applies to `KnownLayout` (`zerocopy/src/lib.rs`), `DstLayout`/`TrailingSliceLayout`/`RoundingAlignAndPhase`/`CastFrom` (`zerocopy/src/layout.rs`), `PtrInner` (`zerocopy/src/pointer/inner.rs`), `SplitAt`/`Split` (`zerocopy/src/split_at.rs`), and `Ref::from_*_with_elems` (`zerocopy/src/ref.rs`). Revision `312cb70a655a...` exhibits pre-validation-before-split `CastError::into_src()` truncation; `ec133ce4d799...` merges pull request 3924 preserving whole `source`.
2. **Operational Semantics (`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):** Covers `DynamicLayout.sizeAndAlignFromMeta` (`Miri/Interpreter/DynamicLayout.lean`), `TypedRetag` (`Miri/Interpreter/TypedRetag.lean`), `RuntimeTargetDataLayout` (`Miri/ABI/RuntimeLayout.lean`), `mem::size_of_val` (`core/src/mem/mod.rs`), and `rustc_ty_utils/src/layout.rs`, grounded in Stacked Borrows (`10.1145/3371109`), Tree Borrows (`10.1145/3735592`), and RefinedRust (`10.1145/3656422`).
3. **Lean 4 Non-TCB Verification Envelope (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`):** Non-TCB `theory/` modules under `trusted/audit/TrustedBoundary.lean:L442–596` and `trusted/lean/foundation-lock.json` must start with `prelude`, import only the 51 locked `Init.*` modules (which omit `Init.Data.Nat.Log2`) plus `Trusted.*`/`Anneal.*`, avoid infix `/`, `%`, `&&&`, `|||`, `^^^`, `<<<`, `>>>`, avoid banned tactics (`sorry`, `axiom`, `omega`, `native_decide`, `bv_decide`, `grind`), use only `{propext, Quot.sound, Classical.choice}`, and satisfy Statement-Origin Separation.
4. **Relationship to Existing Corpus Reports:** Extends `zerocopy-byte-apis-cross-target-layout-and-packet-certificates` (fixed-width packet layout checks), `zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics` (`Ptr` validity invariants and `KnownLayout` trait signatures), and `vst-floyd-withspacer-field-at-and-selector-vprop-entailment` (sized struct padding spacers) to parametric slice-DST rounding, padding-overlap aliasing, and zero-element suffix alignment.

## Findings

### 1. `RoundingAlignAndPhase` Bit-Packing, Nested `#[repr(packed)]` Rounding Retention, and Modular Cancellation

Basis: normative (`rust-lang/rust` Reference layout rules cited in `layout.rs:L897–900, L1265–1291`) + source (`google/zerocopy@ec133ce4...`: `zerocopy/src/lib.rs:L746–958`, `zerocopy/src/layout.rs:L34–775, L1085–1558`, `zerocopy/src/util/mod.rs:L156–260`) + execution (`probe_pkg1.py`) + derived

`KnownLayout` (`lib.rs:L746–905`) associates each type with `LAYOUT: DstLayout { align: NonZeroUsize, size_info: SizeInfo, statically_shallow_unpadded: bool }` (`layout.rs:L34–50`). For slice DSTs, `SizeInfo::SliceDst(TrailingSliceLayout)` stores `(offset, elem_size, size_base, size_rounding_align_and_phase)` (`L153–207`):

1. **Lossless `NonZeroUsize` Bit-Packing (`layout.rs:L65–148`):** `RoundingAlignAndPhase(NonZeroUsize)` encodes power-of-two `align` (`2^k`) and `phase < align` via `align | phase` (`L91`). Because `align` contributes only bit `k` and `phase` occupies bits `< k`, their bits are disjoint (`align | phase == align + phase > 0`). Decoding uses `shift = (POINTER_WIDTH_BITS - 1) - (self.0.get().leading_zeros() as usize)`, `align = 1usize << shift`, and `phase = self.0.get() ^ align` (`L119–129`). Exhaustive evaluation over all `65,535` nonzero 16-bit integers confirms a collision-free bijection (`probe_pkg1.py`).
2. **Affine Size Law and Nested `#[repr(packed)]` Retention (`layout.rs:L190–206, L1153–1495`):** For `elems` trailing elements, object size over the nonnegative integers is (`L193`):
   $$\mathsf{objectSize}(L, \text{elems}) = L.\text{size\_base} + \mathsf{roundUp}\!\big(L.\text{size\_phase} + \text{elems} \cdot L.\text{elem\_size},\; L.\text{size\_align}\big)$$
   `DstLayout::for_repr_c_struct` (`L1153–1197`) threads `extend` (`L1231–1377`, clamping field alignment via `min(field.align, max_align)` and shifting both `offset` and `size_base` by `off` when extending with a `SliceDst` at `L1342–1365`) followed by `pad_to_align` (`L1405–1495`):
   - When `size_align < self.align` (`L1432–1473`), outer alignment dominates: `fixed = round_up(size_base, size_align) + size_phase`, producing `new_phase = fixed & (self.align - 1)` and `new_base = round_down(fixed, self.align)` with outer `self.align`. On `OddHeader` (`#[repr(C, align(8))] struct OddHeader { header: [u8; 7], body: [u8] }`, `ref.rs:L1573–1576`), this yields `offset = 7, elem_size = 1, size_base = 0, size_align = 8, size_phase = 7`, giving sizes `(8, 8, 16)` for `elems = (0, 1, 2)`.
   - When `size_align >= self.align` (`L1473–1486`), `pad_to_align` pads only `size_base` to `self.align` and **preserves the larger inner `(size_align, size_phase)`**. Wrapping `#[repr(C)] struct Inner<T: ?Sized> { prefix: u32, tail: T }` inside `#[repr(C, packed)] struct Packed<T: ?Sized> { prefix: u8, tail: ManuallyDrop<T> }` (`split_at.rs:L1104–1123`) produces `obj_align = 1, offset = 5, elem_size = 1, size_base = 5, size_align = 4, size_phase = 0`. Thus `offset % size_align = 1 != size_phase = 0` and `size_align = 4 > obj_align = 1`: `Packed<Inner<[u8]>>` has alignment `1` yet at `elems = 1` occupies `9` bytes with `3` bytes of dynamic inner padding `[6, 9)` (`probe_pkg1.py`).
3. **Division-Free Overflow Bounding and Modular Cancellation (`layout.rs:L252–546`):**
   - `max_trailing_bytes(available_bytes)` (`L252–341`) computes `rounded_phase = if size_phase == 0 { 0 } else { size_align }`, checks `minimum_size = size_base + rounded_phase <= available_bytes`, aligns down `aligned_bytes = round_down(available_bytes - minimum_size, size_align)`, and returns `aligned_bytes | (rounded_phase - size_phase)`.
   - `padding_for_elems(elems)` (`L360–415`) cancels `trailing_bytes = elems * elem_size` modulo $2^W$ (`usize::MAX + 1`) because every power-of-two `size_align` divides $2^W$: reducing `elem_remainder = elem_size & size_mask` and `trailing_remainder = elems.wrapping_mul(elem_remainder) & size_mask` (`L379–390`), it computes `padding_needed_for(size_phase.wrapping_add(trailing_remainder), size_align)` (`util/mod.rs:L156–209`: `!(len.wrapping_sub(1)) & mask`) and adds `(size_base + size_phase - offset)` modulo $2^W$ (`L411–414`). `size_for_elems` (`L427–491`) checks `elems * elem_size <= max_trailing_bytes(usize::MAX)` and adds `padding_for_elems(elems)` onto `offset.wrapping_add(trailing_size)`.
4. **Sufficiency vs. Incompleteness of `has_same_size_sequence` (`layout.rs:L565–642, L2080–2214`):**
   `CastFrom::project` checks whether `dst_meta = offset_delta_elems + src_meta * (src.elem_size / dst.elem_size)` preserves object size for all `src_meta` by calling `dst.advance(offset_delta_elems * dst.elem_size, src.elem_size)` (`L678–774`) and `src.has_same_size_sequence(shifted_dst)` (`L2080–2094`). `has_same_size_sequence(L1, L2)` checks equal `elem_size`, equal representable `size_for_elems(0)`, and either `(elem_size % max(a1, a2) == 0)` or `(a1 == a2 && p1 == p2)`. While sound (`L551–552`), it is strictly incomplete: `L1 = (offset=1, elem_size=2, size_base=0, size_align=4, size_phase=1)` and `L2 = (offset=2, elem_size=2, size_base=0, size_align=4, size_phase=2)` produce identical sizes `4 * (n // 2 + 1)` for all `n >= 0` (`probe_pkg1.py`, `n in 0..1024`) because `gcd(2, 4) = 2` maps residues `{1, 3}` and `{2, 0}` into the same rounding buckets, yet `has_same_size_sequence(L1, L2)` returns `false`.

### 2. `PtrInner::split_at_unchecked` Trailing-Padding Overlap and `Split<T>` Aliasing Discipline

Basis: normative (Tree Borrows `10.1145/3735592`; Stacked Borrows `10.1145/3371109`) + source (`google/zerocopy@ec133ce4...`: `zerocopy/src/pointer/inner.rs:L218–442`, `zerocopy/src/split_at.rs:L125–1095, L1104–1277`, `zerocopy/src/layout.rs:L1532–1558`; `proofs-rs/lean-miri@c92d1d97...`: `Miri/Interpreter/TypedRetag.lean:L114–171`) + execution (`probe_pkg1.py`) + derived

Given `PtrInner<'a, T>` (`T: SplitAt + KnownLayout<PointerMetadata = usize>`) with `meta = N` over `[base, base + size_for_elems(N))`, `PtrInner::split_at_unchecked(l_len)` (`pointer/inner.rs:L308–335`) produces `left = self.with_meta(l_len)` (`[base, base + size_for_elems(l_len))`) and `right = self.trailing_slice().slice_unchecked(l_len..N)` (`[base + offset + l_len * elem_size, base + offset + N * elem_size)`). Whenever `padding_for_elems(l_len) > 0` and `l_len < N` (with `elem_size > 0`), `left`'s trailing padding overlaps `right`'s leading bytes (`L304–305, L332–333`) over:

$$\mathsf{Overlap}(L, l_{\text{len}}, N) = \big[\,\text{base} + \text{offset} + l_{\text{len}} \cdot \text{elem\_size},\; \min(\text{base} + \mathsf{objectSize}(L, l_{\text{len}}),\; \text{base} + \text{offset} + N \cdot \text{elem\_size})\,\big)$$

On `Inner<[u8]>` (`#[repr(C)] struct Inner<T: ?Sized> { prefix: u32, tail: T }`, `align = 4, offset = 4, elem_size = 1`), splitting an 8-byte buffer (`N = 4`) at `l_len = 1` gives `left = [0, 8)` (`padding = 3`) and `right = [5, 8)` (`overlap = [5, 8)`). Forming concurrent `&mut left` and `&mut right` creates two `Reserved` Tree Borrows tags (`10.1145/3735592`, `TypedRetag.lean:L130–171`) over byte `5`; writing `right[0]` activates `right` and transitions `left` to `Disabled` on byte `5`, causing immediate UB on subsequent `left` writes or protected reborrows. Even `&T` shared references trigger UB if `T` permits interior mutation (`!Freeze`, e.g., `UnsafeCell<[u8]>`) over the overlapped padding bytes (`split_at.rs:L654–659, L1031–1034`).

`Split<T>` (`split_at.rs:L338–1095`) restricts reference extraction to four witness paths:
- **`via_immutable` (`L429, L964`):** Requires `T: Immutable` and `Aliasing = Shared`, allowing read-only shared overlap without runtime checks.
- **`via_into_bytes` (`L478, L749, L976`):** Requires `T: IntoBytes`, guaranteeing zero static or dynamic padding across all lengths; works for `&T` and `&mut T`, but rejects types with static inter-field padding (e.g., `(u8, [u16])` at `L515–520`).
- **`via_no_dynamic_padding` (`L571, L846, L989`):** Asserts `!T::LAYOUT.requires_dynamic_padding()` at compile time (`layout.rs:L1532–1558`: `size_for_elems(0) == Some(offset)` AND `elem_size % size_align == 0`). Admits static inter-field padding when every trailing length has zero trailing padding, replacing deprecated `via_unaligned` (`L487–496`).
- **`via_runtime_check` (`L643, L897, L1025`):** Dynamically verifies `trailing_slice_layout::<T>().padding_for_elems(l_len.get()) == 0`, admitting disjoint split indices on dynamically padded types (e.g., `Packed<Inner<[u8]>>` at `l_len = 0, 4` while rejecting `l_len = 1, 2, 3`, `L1235–1240`) and returning `Err(self)` otherwise.

### 3. Endpoint Alignment Divisibility, Metadata Non-Injectivity, and Zero-Element Suffix Casts

Basis: source (`google/zerocopy@ec133ce4...`: `zerocopy/src/layout.rs:L1560–1852`, `zerocopy/src/ref.rs:L835–985, L1563–1619, L1824–1875`, `zerocopy/src/error.rs:L258–451`; `google/zerocopy@312cb70a...`: `zerocopy/src/ref.rs:L835–960`) + execution (`probe_pkg1.py`) + derived

1. **Zero-Element Suffix Alignment (`layout.rs:L1645–1781`, `ref.rs:L1862–1875`):** `validate_cast_and_convert_metadata(addr, bytes_len, cast_type)` checks `(addr + offset) % self.align.get() == 0` (`offset = 0` for `Prefix`, `offset = bytes_len` for `Suffix`) *before* inspecting `size_info`. Because every completed instance size `size` (including `0`) satisfies `self.align | size`, `(addr + bytes_len - size) % align == 0 ↔ (addr + bytes_len) % align == 0`. Hence `Ref::<&mut [u8], [AU64]>::from_suffix_with_elems(&mut buf[..13], 0)` at odd end address `base + 13` still demands `8`-byte alignment and returns `Err(CastError::Alignment)`, even though `size_for_metadata(0) == Some(0)` (`ref.rs:L1865–1874`).
2. **Pre-Split Validation and Whole-Source Error Recovery (`312cb70a655a...` vs. `ec133ce4d799...`, `ref.rs:L835–985`):** Before pull request 3924 (`312cb70a655a...`), `Ref::from_prefix_with_elems` and `Ref::from_suffix_with_elems` split `source` before calling `from_bytes_with_elems`. On alignment failure, `CastError::Alignment(err)` held only the truncated subslice (`err.into_src().len() == 0` for `from_suffix_with_elems(..., 0)`!), permanently losing the rest of `&mut [u8]`. At `ec133ce4d799...`, both constructors first run `Ptr::from_ref(source.deref()).try_cast_into::<T, BecauseImmutable>(CastType::Prefix | Suffix, Some(count))` (`L840–845, L943–948`) and restore the original unsplit `source` on failure via `e.with_src(()).with_src(source)` (`error.rs:L275, L448`). Note that when `source` is *both* too short and misaligned for `from_prefix_with_elems`, checking `try_cast_into` up front shifts the returned variant from `Size` (split-first) to `Alignment` (matching `Ref::from_prefix`).
3. **Ambiguous Size-to-Metadata Inverse (`ref.rs:L1563–1619`):** Because trailing padding maps multiple element counts to the same byte size (`Frame` maps `1` and `8` elements to `16` bytes; `OddHeader` maps `0` and `1` elements to `8` bytes), `Ref<B, T>` must carry explicit `meta: MetadataOf<T>` rather than reconstructing it from `B::len()`, whereas `from_bytes` picks the largest count (`metadata_for_exact_size`, `layout.rs:L1576–1598`).

### 4. `lean-miri` `DynamicLayout` Correspondence and Closed-Form `DstLayoutAlgebra` in Lean 4

Basis: source (`proofs-rs/lean-miri@c92d1d97...`: `Miri/ABI/RuntimeLayout.lean:L45–268`, `Miri/Interpreter/DynamicLayout.lean:L10–112`; `joshlf/anneal@c131b320...`: `trusted/audit/TrustedBoundary.lean:L442–596`, `trusted/lean/foundation-lock.json`) + execution (`probe_pkg1.py`) + derived

In `proofs-rs/lean-miri`, `DynamicLayout.sizeAndAlignFromMeta` (`DynamicLayout.lean:L40–85`) traverses unsized structs recursively under explicit `fuel`: `.slice | .str` computes `elem.layout.size * len` bounded by `maxSizeOfVal` (`L76–84`), and `.adt | .tuple` (`L49–71`) clamps nested `tailAlign` by `packedAlign` (`L61–62`), computes `fullAlign = sizedAlign.max tailAlign`, asserts `alignTo (alignTo offset tailAlign + tailSize) fullAlign == alignTo (offset + tailSize) fullAlign` (`L66–69`), and matches `zerocopy`'s flattened `TrailingSliceLayout` byte-for-byte across nested `Packed<Inner<[u8]>>` (`probe_pkg1.py`, `n in 0..33`).

In `joshlf/anneal@c131b320...`, `theory/` modules cannot import `vendor/lean-miri` or `Init.Data.Nat.Log2` (omitted from `foundation-lock.json`'s 51 `Init.*` modules) and must adhere to `allowedTheorySyntaxKinds` (`TrustedBoundary.lean:L442–596`: no `/`, `%`, `&&&`, `|||`, `^^^`, `<<<` syntax; no `omega`, `native_decide`, `sorry`, `axiom`, `partial`). Scanning bits structurally via `highestBitPow2Aux` removes `Nat.log2`, yielding a closed-form Pass-1 `prelude` Lean `v4.34.1` algebra:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic

namespace Anneal.DstLayoutAlgebra

def highestBitPow2Aux (encoded : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 =>
    let pow := Nat.shiftLeft 1 (k + 1)
    match Nat.ble pow encoded with
    | true  => pow
    | false => highestBitPow2Aux encoded k

/-- Decode `RoundingAlignAndPhase` (`zerocopy/src/layout.rs:104-130`) without `Nat.log2`. -/
def rapDecode (wordBits encoded : Nat) : Nat × Nat :=
  let align := highestBitPow2Aux encoded (wordBits - 1)
  (align, Nat.xor encoded align)

def rapEncode (align phase : Nat) : Nat :=
  Nat.lor align phase

structure TrailingSliceLayout where
  offset    : Nat
  elemSize  : Nat
  sizeBase  : Nat
  sizeAlign : Nat
  sizePhase : Nat
  objAlign  : Nat

def roundUpPow2 (x align : Nat) : Nat :=
  let rem := Nat.mod x align
  match Nat.beq rem 0 with
  | true  => x
  | false => x + (align - rem)

/-- Closed-form object size (`zerocopy/src/layout.rs:193`). -/
def dstObjectSize (L : TrailingSliceLayout) (elems : Nat) : Nat :=
  L.sizeBase + roundUpPow2 (L.sizePhase + elems * L.elemSize) L.sizeAlign

/-- Trailing padding after `elems` elements (`zerocopy/src/layout.rs:360-415`). -/
def dstTrailingPadding (L : TrailingSliceLayout) (elems : Nat) : Nat :=
  dstObjectSize L elems - (L.offset + elems * L.elemSize)

/-- Disjointness predicate guarding `&mut` / `!Immutable` `split_at` (`split_at.rs:1025-1042`). -/
def splitAtDisjointSafe (L : TrailingSliceLayout) (lLen : Nat) : Bool :=
  Nat.beq (dstTrailingPadding L lLen) 0

/-- Sufficient `has_same_size_sequence` condition (`layout.rs:565-642`). -/
def hasSameSizeSeq (L1 L2 : TrailingSliceLayout) : Bool :=
  Nat.beq L1.elemSize L2.elemSize &&
  Nat.beq (dstObjectSize L1 0) (dstObjectSize L2 0) &&
  ((Nat.beq (Nat.mod L1.elemSize L1.sizeAlign) 0 &&
    Nat.beq (Nat.mod L1.elemSize L2.sizeAlign) 0) ||
   (Nat.beq L1.sizeAlign L2.sizeAlign && Nat.beq L1.sizePhase L2.sizePhase))

/-- Prefix/suffix cast validity enforcing zero-element endpoint alignment (`ref.rs:835-985`). -/
def validDstRefCast (isSuffix : Bool) (ptrAddr availBytes : Nat)
    (L : TrailingSliceLayout) (elems : Nat) : Bool :=
  let endpoint := match isSuffix with
    | true  => ptrAddr + availBytes
    | false => ptrAddr
  Nat.beq (Nat.mod endpoint L.objAlign) 0 &&
  Nat.ble (dstObjectSize L elems) availBytes

def packedInnerLayout : TrailingSliceLayout :=
  ⟨5, 1, 5, 4, 0, 1⟩

theorem rap_roundtrip_13 :
    rapDecode 64 (rapEncode 8 5) = (8, 5) := rfl

theorem packed_inner_pad_at_1 :
    dstObjectSize packedInnerLayout 1 = 9 ∧
    dstTrailingPadding packedInnerLayout 1 = 3 ∧
    splitAtDisjointSafe packedInnerLayout 1 = false :=
  ⟨rfl, rfl, rfl⟩

theorem zero_elem_odd_suffix_rejected :
    validDstRefCast true 0 13 ⟨0, 8, 0, 8, 0, 8⟩ 0 = false := rfl

theorem zero_elem_aligned_suffix_ok :
    validDstRefCast true 0 8 ⟨0, 8, 0, 8, 0, 8⟩ 0 = true := rfl

end Anneal.DstLayoutAlgebra
```

Transfer into `joshlf/anneal@c131b320...`: `Trusted.*` only needs wide-pointer `SliceDst` metadata storage, a correspondence-checked `dstSizeOfVal` hook (anchored against `DynamicLayout.lean`), and pre-short-circuit `AlignedRef` enforcement even at `size == 0`, while all `RoundingAlignAndPhase`, `splitAtDisjointSafe`, and `hasSameSizeSeq` proofs stay cleanly in non-TCB `theory/` with $O(1)$ closed-form kernel evaluation.

## Boundaries

- **not examined**: `dyn Trait` vtable metadata (`DynMetadata` and `vtableSizeAndAlign` in `DynamicLayout.lean:L72–75`), `zerocopy-derive` macro expansion details, and live Lean `v4.34.1` compilation latency under `anneal-audit` (only static adherence to `TrustedBoundary.lean` was checked).
- **unknown**: Whether future `rustc` releases preserve layout stability for generic types that transitively nest `#[repr(align)]` inside `#[repr(packed)]` (`layout.rs:L1135–1143`), and tight completeness bounds for general affine sequence equivalence beyond `has_same_size_sequence` (`layout.rs:L565–642`).
- **known not to apply**:
  - `DstLayout::for_repr_c_struct` and `TrailingSliceLayout` formulas do **not** apply to `#[repr(Rust)]` structs (`layout.rs:L1126–1128`).
  - `T: Unaligned` (`obj_align == 1`) does **not** guarantee zero dynamic padding when `#[repr(packed)]` wraps an inner aligned slice DST (`Packed<Inner<[u8]>>` at `split_at.rs:L1221–1251`).
  - `Split::via_immutable` (`split_at.rs:L429`) does **not** permit `&mut` or `!Immutable` (`UnsafeCell`/`Cell`) concurrent split halves to overlap on trailing padding.
  - `DstLayout::validate_cast_and_convert_metadata` panics on zero-sized trailing slice elements (`elem_size == 0`, `layout.rs:L1743–1746`, `ref.rs:L799–815`).
- **unsupported**: In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` and `Trusted.MirSemantics` fail closed (`FaultKind.unsupported`) on slices, `#[repr(C)]` slice DSTs, wide-pointer metadata, `ProjectionElem.deref`, and non-empty `CallerMemory` (`MirAst.lean:L308–321`, `MirSemantics.lean:L803`).

## Evidence

### Primary Repositories, Commits, Files, and Peer-Reviewed Sources

| Subject | Exact Identity | Inspected Paths & Anchors |
| :--- | :--- | :--- |
| **zerocopy (post-fix)** | `google/zerocopy` @ `ec133ce4d7993775413d852f91c9e3eb2a2a0897` | `zerocopy/src/lib.rs` (`L746–976` `KnownLayout`, `PointerMetadata`); `zerocopy/src/layout.rs` (`L34–775`, `L861–1852`, `L2080–2300`); `zerocopy/src/pointer/inner.rs` (`L218–442`, `L570–650`); `zerocopy/src/split_at.rs` (`L125–1095`, `L1104–1277`, `L1328–1353`); `zerocopy/src/ref.rs` (`L835–985`, `L1024–1133`, `L1563–1619`, `L1824–1875`); `zerocopy/src/error.rs` (`L258–280`, `L429–450`); `zerocopy/src/util/mod.rs` (`L156–260`) |
| **zerocopy (pre-fix)** | `google/zerocopy` @ `312cb70a655ab25936fefb4d1b8c1787c782876e` | `zerocopy/src/ref.rs` (`L835–960` before pull request 3924) |
| **lean-miri** | `proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` | `Miri/ABI/RuntimeLayout.lean` (`L45–268`); `Miri/Interpreter/DynamicLayout.lean` (`L10–112`); `Miri/Interpreter/TypedRetag.lean` (`L114–171`) |
| **Rust & std** | `rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd` | `library/core/src/mem/mod.rs` (`L405–517`); `compiler/rustc_ty_utils/src/layout.rs` (`L495–547`) |
| **Anneal & Lean 4** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `trusted/audit/TrustedBoundary.lean` (`L442–596`); `trusted/lean/foundation-lock.json`; `trusted/lean/Trusted/MirAst.lean` (`L308–321`); `trusted/lean/Trusted/MirSemantics.lean` (`L803`) |
| **Literature** | PLDI 2025 (`10.1145/3735592`); POPL 2020 (`10.1145/3371109`); PLDI 2024 (`10.1145/3656422`) | Villani et al. (Tree Borrows); Jung et al. (Stacked Borrows); Gäher et al. (RefinedRust) |

### Executable Probe (`CPython 3.13.15`, `x86_64`, `2026-11-20`)

```python
M64 = (1 << 64) - 1
def pad_for(n, a): return (~((n - 1) & M64) & M64) & (a - 1)
def rd_dn(n, a): return n & (~(a - 1))
def rd_up(n, a): return n if (n & (a - 1)) == 0 else n + (a - (n & (a - 1)))
def rap_enc(a, p): return a | p
def rap_dec(e, w=64):
    s = (w - 1) - (w - e.bit_length())
    return (1 << s), e ^ (1 << s)

def mk_trailing(off, esz, base, enc): return (off, esz, base, enc)
def max_tb(tr, avail):
    _, _, sb, enc = tr; a, ph = rap_dec(enc)
    rp = 0 if ph == 0 else a
    if sb + rp > avail: return None
    return rd_dn(avail - (sb + rp), a) | (rp - ph)

def pad_elems(tr, elems):
    off, esz, sb, enc = tr; a, ph = rap_dec(enc); mask = a - 1
    rp = pad_for((ph + ((elems & M64) * (esz & mask) & mask)) & M64, a)
    return (sb + ph - off + rp) & M64

def sz_elems(tr, elems):
    mt = max_tb(tr, M64); ts = elems * tr[1]
    if mt is None or ts > mt: return None
    return ((tr[0] + ts) & M64) + pad_elems(tr, elems) & M64

def same_seq(t1, t2):
    if t1[1] != t2[1]: return False
    s0, o0 = sz_elems(t1, 0), sz_elems(t2, 0)
    if s0 is None or s0 != o0: return False
    a1, p1 = rap_dec(t1[3]); a2, p2 = rap_dec(t2[3])
    return (t1[1] % max(a1, a2) == 0) or (a1 == a2 and p1 == p2)

def ext_dst(acc, fld, packed=None):
    sa, sz, _ = acc; fa, fsz, ftr = fld
    fa = min(fa, packed if packed else (1 << 63))
    off = sz + pad_for(sz, fa); na = max(sa, fa)
    if ftr is None: return (na, off + fsz, None)
    return (na, None, (off + ftr[0], ftr[1], off + ftr[2], ftr[3]))

def pad_dst(lay):
    al, sz, tr = lay
    if tr is None: return (al, sz + pad_for(sz, al), None)
    off, esz, sb, enc = tr; sa, sp = rap_dec(enc)
    if sa < al:
        fx = sb + pad_for(sb, sa) + sp
        return (al, None, (off, esz, rd_dn(fx, al), rap_enc(al, fx & (al - 1))))
    return (al, None, (off, esz, sb + pad_for(sb, al), enc))

def repr_c(flds, ralign=None, packed=None):
    cur = (ralign or 1, 0, None)
    for f in flds: cur = ext_dst(cur, f, packed)
    return pad_dst(cur)

seen = {rap_dec(e, 16) for e in range(1, 1 << 16)}
assert len(seen) == 65535 and all(rap_enc(a, p) == e for e in range(1, 1 << 16) for a, p in [rap_dec(e, 16)])

sl_u8 = (1, None, (0, 1, 0, rap_enc(1, 0)))
inner = repr_c([(4, 4, None), sl_u8])
pk_in = repr_c([(1, 1, None), inner], packed=1)
pa, pp = rap_dec(pk_in[2][3])
assert (pk_in[0], pk_in[2][0], pk_in[2][2], pa, pp) == (1, 5, 5, 4, 0)
assert all(sz_elems(pk_in[2], n) == 1 + rd_up(4 + n, 4) and pad_elems(pk_in[2], n) == sz_elems(pk_in[2], n) - (5 + n) for n in range(33))

frame = repr_c([(1, 8, None), sl_u8], ralign=8)[2]
odd = repr_c([(1, 7, None), sl_u8], ralign=8)[2]
assert sz_elems(frame, 1) == sz_elems(frame, 8) == 16 and sz_elems(odd, 0) == sz_elems(odd, 1) == 8

l1, l2 = (1, 2, 0, rap_enc(4, 1)), (2, 2, 0, rap_enc(4, 2))
same_ok = all(sz_elems(l1, n) == sz_elems(l2, n) for n in range(1024))
assert same_ok and not same_seq(l1, l2)

ov_lo, ov_hi = inner[2][0] + 1 * inner[2][1], min(sz_elems(inner[2], 1), inner[2][0] + 4 * inner[2][1])
assert (ov_lo, ov_hi) == (5, 8) and pad_elems(inner[2], 1) == 3
perms = {i: ["Reserved", "Reserved"] for i in range(8)}
perms[5] = ["Disabled", "Active"]
tb_dis = [i for i, v in perms.items() if v[0] == "Disabled"]

def cast_check(align, tr, addr, blen, suf, elems):
    ep = addr + blen if suf else addr
    if ep % align != 0: return ("Err", "Alignment", blen)
    sz = sz_elems(tr, elems)
    if sz is None or sz > blen: return ("Err", "Size", blen)
    return ("Ok", elems, blen - sz if suf else sz)

au64_sl = (0, 8, 0, rap_enc(8, 0))
post_z = cast_check(8, au64_sl, 0, 13, True, 0)
ok_z = cast_check(8, au64_sl, 0, 8, True, 0)
assert post_z == ("Err", "Alignment", 13) and ok_z == ("Ok", 0, 8) and tb_dis == [5]
print("PROBE_SLICEDST_OK", {"rap_16bit": len(seen), "pk_inner": (pk_in[0], pk_in[2][0], pk_in[2][2], pa, pp), "pk_sz1_pad1": (sz_elems(pk_in[2], 1), pad_elems(pk_in[2], 1)), "frame_1_8": (sz_elems(frame, 1), sz_elems(frame, 8)), "odd_0_1": (sz_elems(odd, 0), sz_elems(odd, 1)), "same_seq_gap": (same_ok, same_seq(l1, l2)), "overlap": (ov_lo, ov_hi, ov_hi - ov_lo), "tb_disabled": tb_dis, "suf0_pre_post_len": (0, post_z[2]), "suf0_ok8": ok_z})
```

Observed output (`2026-11-20`, `CPython 3.13.15`): `PROBE_SLICEDST_OK {'rap_16bit': 65535, 'pk_inner': (1, 5, 5, 4, 0), 'pk_sz1_pad1': (9, 3), 'frame_1_8': (16, 16), 'odd_0_1': (8, 8), 'same_seq_gap': (True, False), 'overlap': (5, 8, 3), 'tb_disabled': [5], 'suf0_pre_post_len': (0, 13), 'suf0_ok8': ('Ok', 0, 8)}`.

## Revalidation

1. **`zerocopy` layout and `SplitAt` check:** Diff `zerocopy/src/{layout.rs, pointer/inner.rs, split_at.rs, ref.rs}` at a newer `google/zerocopy` commit against `ec133ce4d7993775413d852f91c9e3eb2a2a0897` to confirm whether `TrailingSliceLayout`, `has_same_size_sequence`, `Split::via_runtime_check`, or `Ref::from_*_with_elems` changed semantics.
2. **`lean-miri` `DynamicLayout` check:** Diff `Miri/Interpreter/DynamicLayout.lean` in `proofs-rs/lean-miri` against `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` for `packedAlign` or `codegenSize` updates.
3. **Anneal and Lean kernel check:** Inspect `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` for slice-DST support, and compile `Anneal.DstLayoutAlgebra` under Lean `v4.34.1` (`--trust=0`) plus Anneal's boundary auditor to verify `{propext, Quot.sound, Classical.choice}` closure.
4. **Executable probe:** Run the Python 3 script in **Evidence** (`python3` $\ge 3.10$) and confirm `PROBE_SLICEDST_OK` prints with exit code `0`.
