-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
module
prelude
public import Init.NotationExtra
public import Trusted.MirAst
public import Trusted.MirSemantics.Enum

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Target Data Layout and Type Layouts (`Trusted.MirSemantics.Layout`)

Byte order (`TargetEndian`), the profile-v1 target byte order
(`profileTargetEndian`), the size and alignment of a sized type
(`LayoutData`), and the layouts of the Day-1 local types (`layoutOfTy`).

$M_{\text{anneal}}$ uses these definitions when it moves a local into memory
(`forceAllocation`) and when it encodes or decodes a value as bytes
(`Trusted.MirSemantics.Bytes`). They are semantic choices of
$M_{\text{anneal}}$, so they live outside `Trusted.MirAst*`, which the
independent reference evaluator $M_{\text{ref}}$ may import.
-/

/-- Byte order of multi-byte integers in memory, corresponding to
`rustc_abi::Endian` (`compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum Endian {
>     Little,
>     Big,
> }" -/
inductive TargetEndian where
  | little
  | big

/-- Byte order of the MIR semantic profile version 1
(`Program.mirProfileVersion = 1`).

`Program` does not record the target's byte order. Profile version 1 has no
operation that reinterprets the bytes of a value at another type (no
transmutes, pointer casts, unions, or partial reads), so byte order cannot
affect any `Behavior`. Profile version 1 therefore fixes big-endian order,
which matches the data layout that `Trusted.Correspondence` passes to
`lean-miri` (`Miri.ABI.RuntimeTargetDataLayout.default`). A profile that can
observe byte order must take it from the captured target data layout. -/
noncomputable def profileTargetEndian : TargetEndian := .big

/-- Byte order of the MIR semantic profile version 2
(`Program.mirProfileVersion = 2`).

Profile version 2 can observe byte order: raw pointers load and store
multi-byte integers from caller-supplied bytes (`loadIndirectV2`,
`storeIndirectV2`), and pointer and slice metadata occupy memory. The capture
adapter admits only 64-bit little-endian targets (`checked_target_profile`
in `trusted/rustc-capture/src/capture.rs` refuses every other data layout),
so profile version 2 fixes little-endian order to match the captured
target. -/
noncomputable def profileV2TargetEndian : TargetEndian := .little

/-- Size and alignment of a sized type, corresponding to the `size` and
`align` fields of `rustc_abi::LayoutData` (`compiler/rustc_abi/src/lib.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct LayoutData<FieldIdx: Idx, VariantIdx: Idx> {
>     ...
>     pub align: AbiAlign,
>     ...
>     pub size: Size,
>     ..."

- `size`: size in bytes.
- `alignLog2`: base-2 logarithm of the ABI alignment in bytes (`rustc_abi`'s
  `Align` stores the same exponent, `pow2`).

Every Day-1 local type is sized, and the value of a local is decoded from its
type (`Trusted.MirSemantics.decodeVal`), so `LayoutData` records only the two
fields that allocation, bounds checks, and alignment checks read. -/
structure LayoutData where
  size : Nat
  alignLog2 : Nat

/-- Layout of an integer of width `w` with natural alignment (alignment equal
to size).

`rustc` takes integer alignment from the target data layout
(`Integer::align` in `compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "I8 => dl.i8_align,
>  I16 => dl.i16_align,
>  I32 => dl.i32_align,
>  I64 => dl.i64_align,
>  I128 => dl.i128_align,"

Profile version 1 uses natural alignment for every width, as the LLVM data
layouts of 64-bit `x86_64`, `aarch64`, and `powerpc64` targets specify
(`i64:64-i128:128`). $M_{\text{ref}}$ makes different choices:
`lean-miri`'s `RuntimeTargetDataLayout.default` gives `i64` and `i128` 4-byte
alignment, and `Trusted.Correspondence` gives every local layout alignment 1
(`Align.ONE`). As with byte order, no profile-version-1 operation can observe
alignment: every place is the start of a stack allocation created with the
place's own layout.

Profile v2 does observe alignment (dereferences, `refValidInMem`, and
`ValidEntryArgsV2`). The capture adapter therefore refuses any target whose
`i8_align` through `i128_align` differ from these natural alignments
(`checked_target_alignments` in `trusted/rustc-capture/src/capture.rs`). -/
noncomputable def intLayout (w : IntWidth) : LayoutData :=
  match w with
  | .i8 => ⟨1, 0⟩
  | .i16 => ⟨2, 1⟩
  | .i32 => ⟨4, 2⟩
  | .i64 | .isize => ⟨8, 3⟩
  | .i128 => ⟨16, 4⟩

/-- Layout of the overflow pair `(T, bool)` for an integer `T` of width `w`
(`.tuple [.int w s, .bool]`): the integer at offset `0`, the `bool` at offset
`w.byteSize`, and padding up to the integer's alignment, so the size is
`2 * w.byteSize` (`2`, `4`, `8`, `16`, or `32` bytes) and the alignment is the
integer's.

`rustc` lays out the pair as a `BackendRepr::ScalarPair` whose second scalar
starts at the first scalar's size rounded up to the second scalar's alignment
(`LayoutData::scalar_pair` in `compiler/rustc_abi/src/layout/simple.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "let b_align = b.default_align(dl).abi;
> let align = a.default_align(dl).abi.max(b_align).max(dl.aggregate_align);
> let b_offset = a.size(dl).align_to(b_align);
> let size = (b_offset + b.size(dl)).align_to(align);"

A `bool` has alignment 1, so the `bool` starts at `w.byteSize` and the size
rounds `w.byteSize + 1` up to the integer's (natural) alignment. -/
noncomputable def overflowPairLayout (w : IntWidth) : LayoutData :=
  ⟨2 * (intLayout w).size, (intLayout w).alignLog2⟩

/-- Layout of a Day-1 local type, or `none` for a type outside the Day-1
fragment.

- `.bool`: one byte with alignment 1.
- `.int w _`: `intLayout w`.
- `.char`: four bytes with alignment 4, like `u32`.
- `.ordering`: one byte with alignment 1, like its `#[repr(i8)]` tag.
- `.unit`, `.never`, and 1-variant `.zeroSized` enums: zero bytes with
  alignment 1 (`()` and `!` are zero-sized with alignment 1, and a
  1-variant fieldless enum has `Variants::Single` with no tag).
- `.scalar tagW _` enums: the layout of the tag integer (a fieldless enum with
  `TagEncoding::Direct` stores only its tag).
- Overflow pairs `.tuple [.int w s, .bool]`: `overflowPairLayout w`.

An enum that `enumAdmitted` rejects is outside the Day-1 fragment and has no
layout, so every memory access at its type fails closed with `.unsupported`.
-/
noncomputable def layoutOfTy : MirTy → Option LayoutData
  | .bool => some ⟨1, 0⟩
  | .int w _ => some (intLayout w)
  | .char => some ⟨4, 2⟩
  | .ordering => some ⟨1, 0⟩
  | .unit | .never => some ⟨0, 0⟩
  | .enum ety =>
    if !enumAdmitted ety then
      none
    else
      match ety.tagRepr with
      | .zeroSized => some ⟨0, 0⟩
      | .scalar tagW _ => some (intLayout tagW)
  | .tuple [.int w _, .bool] => some (overflowPairLayout w)
  | _ => none

/-- Layout of a Profile v2 local or pointee type (`layoutOfTy` extended with
64-bit thin pointers `⟨8, 3⟩`, 64-bit wide slice pointers `⟨16, 3⟩`, and
`RangeTo<usize>` / `RangeFrom<usize>` `⟨8, 3⟩`). Returns `none` for unsized
`.slice` directly and unsupported aggregates.

The Rust Reference (`src/type-layout.md:60-70`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`) guarantees the thin-pointer case
and only describes the wide-pointer size in a non-binding note:

> "Pointers and references have the same layout. Mutability of the pointer or
> reference does not change the layout.
>
> Pointers to sized types have the same size and alignment as `usize`.
> ...
> [!NOTE]
>
> Though you should not rely on this, all pointers to <abbr
> title="Dynamically Sized Types">DSTs</abbr> are currently twice the size of
> the size of `usize` and have the same alignment."

The capture adapter admits only 64-bit targets, so `usize` is `⟨8, 3⟩`. The
wide `⟨16, 3⟩` layout is rustc's `(ptr, meta)` scalar pair, with slice
metadata a pointer-sized integer
(`compiler/rustc_ty_utils/src/layout.rs:410-412,473,485-486`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "// Potentially-wide pointers.
> ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => {
>     let mut data_ptr = scalar_unit(Pointer(AddressSpace::ZERO));
> ...
> ty::Slice(_) | ty::Str => scalar_unit(Int(dl.ptr_sized_integer(), false)),
> ...
> // Effectively a (ptr, meta) tuple.
> tcx.mk_layout(LayoutData::scalar_pair(cx, data_ptr, metadata))"

`RangeTo<usize>` and `RangeFrom<usize>` are `repr(Rust)` structs with one
`usize` field. The Reference does not guarantee their layout (it requires only
that the struct alignment be at least that of the field), so `⟨8, 3⟩` is
rustc's univariant layout of a single-field struct, not a Reference
guarantee. -/
noncomputable def layoutOfTyV2 (ty : MirTy) : Option LayoutData :=
  match layoutOfTy ty with
  | some l => some l
  | none =>
    match ty with
    | .rawPtr _ pt | .ref _ pt =>
      if isUnsizedTy pt then some ⟨16, 3⟩ else some ⟨8, 3⟩
    | .rangeTo (.int .isize false) | .rangeFrom (.int .isize false) => some ⟨8, 3⟩
    | _ => none

end Trusted.MirSemantics

end
