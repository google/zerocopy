-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Trusted.MirAst
import Trusted.MirSemantics.Enum

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
place's own layout. -/
noncomputable def intLayout (w : IntWidth) : LayoutData :=
  match w with
  | .i8 => ⟨1, 0⟩
  | .i16 => ⟨2, 1⟩
  | .i32 => ⟨4, 2⟩
  | .i64 | .isize => ⟨8, 3⟩
  | .i128 => ⟨16, 4⟩

/-- Layout of a Day-1 local type, or `none` for a type outside the Day-1
fragment.

- `.bool`: one byte with alignment 1.
- `.int w _`: `intLayout w`.
- `.unit`, `.never`, and 1-variant `.zeroSized` enums: zero bytes with
  alignment 1 (`()` and `!` are zero-sized with alignment 1, and a
  1-variant fieldless enum has `Variants::Single` with no tag).
- `.scalar tagW _` enums: the layout of the tag integer (a fieldless enum with
  `TagEncoding::Direct` stores only its tag).

An enum that `enumAdmitted` rejects is outside the Day-1 fragment and has no
layout, so every memory access at its type fails closed with `.unsupported`.
-/
noncomputable def layoutOfTy : MirTy → Option LayoutData
  | .bool => some ⟨1, 0⟩
  | .int w _ => some (intLayout w)
  | .unit | .never => some ⟨0, 0⟩
  | .enum ety =>
    if !enumAdmitted ety then
      none
    else
      match ety.tagRepr with
      | .zeroSized => some ⟨0, 0⟩
      | .scalar tagW _ => some (intLayout tagW)
  | _ => none

end Trusted.MirSemantics
