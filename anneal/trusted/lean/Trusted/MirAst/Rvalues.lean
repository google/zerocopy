-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_ast
module
prelude
public import Init.NotationExtra
public import Trusted.MirAst.Types
public import Trusted.MirAst.Places

@[expose] public section

namespace Trusted.MirAst

/-!
# MIR Operators and Rvalues (`Trusted.MirAst.Rvalues`)

Binary operators, unary operators, and right-hand-side expressions for captured
`Runtime(PostCleanup)` MIR.
-/

/-- MIR binary operators (`rustc_middle::mir::BinOp` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum BinOp {
>     Add, AddUnchecked, AddWithOverflow,
>     Sub, SubUnchecked, SubWithOverflow,
>     Mul, MulUnchecked, MulWithOverflow,
>     Div, Rem,
>     BitXor, BitAnd, BitOr,
>     Shl, ShlUnchecked, Shr, ShrUnchecked,
>     Eq, Lt, Le, Ne, Ge, Gt,
>     Cmp, Offset,
> }"

Every variant in `BinOp` corresponds 1-to-1 with the same-named variant in
`rustc_middle::mir::BinOp`. Upstream documents `BinOp::Cmp` as follows:

> "The `<=>` operator (three-way comparison, like `Ord::cmp`)
>
> This is supported only on the integer types and `char`, always returning
> [`LangItem::OrderingEnum`] (aka [`std::cmp::Ordering`])."

and `BinOp::AddWithOverflow` as follows:

> "Like `Add`, but returns `(T, bool)` of both the wrapped result
> and a bool indicating whether it overflowed." -/
inductive BinOp where
  | add | addUnchecked | addWithOverflow
  | sub | subUnchecked | subWithOverflow
  | mul | mulUnchecked | mulWithOverflow
  | div | rem
  | bitXor | bitAnd | bitOr
  | shl | shlUnchecked | shr | shrUnchecked
  | eq | lt | le | ne | ge | gt
  | cmp | offset

namespace BinOp

/-- Whether `op` is a bit-shift operator (`.shl`, `.shlUnchecked`, `.shr`, or
`.shrUnchecked`), whose RHS integer width and signedness may differ from its
LHS in MIR (`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "Left and right shift operations accept signed or unsigned integers not
> necessarily of the same type and return a value of the same type as their
> LHS. Like in Rust, the RHS is truncated as needed." -/
noncomputable def isShift : BinOp → Bool
  | .shl | .shlUnchecked | .shr | .shrUnchecked => true
  | _ => false

/-- Whether `op` is an unchecked arithmetic or shift operator that faults with
`FaultKind.undefined` on overflow (`compiler/rustc_middle/src/mir/syntax.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "Like `Add`, but with UB on overflow. (Integers only.)"
> "Like `Shl`, but is UB if the RHS >= LHS::BITS or RHS < 0" -/
noncomputable def isUnchecked : BinOp → Bool
  | .addUnchecked | .subUnchecked | .mulUnchecked
  | .shlUnchecked | .shrUnchecked => true
  | _ => false

/-- Whether `op` is an overflowing arithmetic operator that returns the
wrapped result together with an overflow flag
(`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "Like `Add`, but returns `(T, bool)` of both the wrapped result
> and a bool indicating whether it overflowed." -/
noncomputable def isOverflowing : BinOp → Bool
  | .addWithOverflow | .subWithOverflow | .mulWithOverflow => true
  | _ => false

end BinOp

/-- MIR cast kinds (`rustc_middle::mir::CastKind` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum CastKind {
>     ...
>     PointerExposeProvenance,
>     ...
>     PointerWithExposedProvenance,
>     ...
>     PointerCoercion(PointerCoercion, CoercionSource),
>     IntToInt,
>     FloatToInt,
>     FloatToFloat,
>     IntToFloat,
>     PtrToPtr,
>     FnPtrToPtr,
>     ...
>     Transmute,
>     ...
>     BoxDerefTransmute,
>     ..."

- `.intToInt` corresponds to `CastKind::IntToInt`.
- `.ptrToPtr` corresponds to `CastKind::PtrToPtr` (Profile v2 executes it only
  between raw pointers, never from `*const T` to `*mut T`; see
  `evalPtrToPtrCastV2`). Reference-to-raw
  conversions never take this path
  (`compiler/rustc_middle/src/mir/syntax.rs:1499-1500`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "Note that reference-to-raw-ptr casts are translated into
  > `&raw mut/const *r`, i.e., they are not actually casts."
- `.intToPtr` corresponds to `CastKind::PointerWithExposedProvenance`
  (`compiler/rustc_middle/src/mir/syntax.rs:1496-1498`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "An address-to-pointer cast that picks up an exposed provenance.
  > See the docs on `with_exposed_provenance` for more details."

  Profile v2 executes it only from `usize`, and the result has no provenance
  (see the `.cast .intToPtr` arm of `evalRvalueV2`).
- `.unsize` corresponds to
  `CastKind::PointerCoercion(PointerCoercion::Unsize, _)` (Profile v2;
  `compiler/rustc_middle/src/ty/adjustment.rs`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "Unsize a pointer/reference value, e.g., `&[T; n]` to `&[T]`. Note that
  > the source could be a thin or wide pointer."
- `.unsupported` represents every other `CastKind` variant, causing
  $M_{\text{anneal}}$ to fail closed with `FaultKind.unsupported`. -/
inductive CastKind where
  | intToInt
  | ptrToPtr
  | intToPtr
  | unsize
  | unsupported

/-- MIR unary operators (`rustc_middle::mir::UnOp` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum UnOp { Not, Neg, PtrMetadata }"

Constructors `.not`, `.neg`, and `.ptrMetadata` correspond 1-to-1 with
`UnOp::Not`, `UnOp::Neg`, and `UnOp::PtrMetadata`. -/
inductive UnOp where
  | not | neg | ptrMetadata

/-- A MIR right-hand-side expression (`rustc_middle::mir::Rvalue` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum Rvalue<'tcx> {
>     Use(Operand<'tcx>, WithRetag),
>     Repeat(Operand<'tcx>, ty::Const<'tcx>),
>     Ref(Region<'tcx>, BorrowKind, Place<'tcx>),
>     ThreadLocalRef(DefId),
>     RawPtr(RawPtrKind, Place<'tcx>),
>     Cast(CastKind, Operand<'tcx>, Ty<'tcx>),
>     BinaryOp(BinOp, Box<(Operand<'tcx>, Operand<'tcx>)>),
>     UnaryOp(UnOp, Operand<'tcx>),
>     Discriminant(Place<'tcx>),
>     Aggregate(Box<AggregateKind<'tcx>>, IndexVec<FieldIdx, Operand<'tcx>>),
>     CopyForDeref(Place<'tcx>),
>     WrapUnsafeBinder(Operand<'tcx>, Ty<'tcx>),
>     Reborrow(Ty<'tcx>, Mutability, Place<'tcx>),
> }"

Constructor correspondence:
- `.use op` corresponds to `Rvalue::Use(op, withRetag)` whenever the retag is
  an operational no-op (`compiler/rustc_middle/src/mir/syntax.rs`,
  `rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

  > "Yields the operand unchanged, except for a potential retag."
  > (`Rvalue::Use`)
  >
  > "... and implicitly \"retag\" all references and boxes that it copies ..."
  > (`StatementKind::Assign`)

  A retag is therefore a no-op for `WithRetag::No` and for values that contain
  no references or boxes, which covers every Profile v1 type (`.bool`,
  `.int`, `.unit`, `.never`, and admitted fieldless `.enum`). A retagging
  `Use(_, WithRetag::Yes)` of any other type lowers to `.useRetag`, which
  Profile v2 executes by re-validating the contained references
  (`refsValidInMem`) without modeling Stacked or Tree Borrows tags.
- `.binaryOp op lhs rhs` corresponds to `Rvalue::BinaryOp(op, (lhs, rhs))`.
- `.unaryOp op opnd` corresponds to `Rvalue::UnaryOp(op, opnd)`.
- `.cast kind opnd ty` corresponds to `Rvalue::Cast(kind, opnd, ty)`
  (`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`):

  > "Performs essentially all of the casts that can be performed via `as`."
- `.discriminant place` corresponds to `Rvalue::Discriminant(place)`
  (`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`):

  > "Computes the discriminant of the place, returning it as an integer of type
  > [`discriminant_ty`]. Returns zero for types without discriminant."
  > "Note too that the value of the discriminant is not the same thing as the
  > variant index; use [`discriminant_for_variant`] to convert."
- `.ref mutability place` corresponds to `Rvalue::Ref(_, borrowKind, place)`.
- `.addressOf mutability place` corresponds to `Rvalue::RawPtr(kind, place)`
  for `RawPtrKind::Const` (`.shared`) and `RawPtrKind::Mut` (`.mut`).
- `.fakeAddressOf place` corresponds to
  `Rvalue::RawPtr(RawPtrKind::FakeForPtrMetadata, place)` (Profile v2;
  `compiler/rustc_middle/src/mir/syntax.rs#L180-L192`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "Creates a raw pointer to a place that will only be used to access its
  > metadata, not the data behind the pointer. Note that this limitation is
  > *not* enforced by the validator."
  > "In terms of the operational semantics (i.e., Miri), this is equivalent to
  > `RawPtrKind::Mut`, but will never incur a retag."

  Because the `rustc` validator does not enforce the metadata-only limitation,
  Profile v2 enforces it via `isFakePtrMetadataLocalV2` and
  `bodyFakeAddressOfValidV2`.
- `.aggregateTuple fields` corresponds to
  `Rvalue::Aggregate(AggregateKind::Tuple, fields)`.
- `.aggregateArray elemTy elems` corresponds to
  `Rvalue::Aggregate(AggregateKind::Array(elemTy), elems)` (Profile v2).
- `.repeat_ op elemTy count` corresponds to `Rvalue::Repeat(op, count)`
  (Profile v2).
- `.aggregateRangeTo elemTy endOp` and `.aggregateRangeFrom elemTy startOp`
  correspond to `Rvalue::Aggregate(AggregateKind::Adt, ..)` constructing
  `core::ops::RangeTo { end }` and `core::ops::RangeFrom { start }`
  (Profile v2).
- `.useRetag op` corresponds to a retagging `Use(op, WithRetag::Yes)` of a
  type that is not retag-free.
- `.unsupported` represents all other `Rvalue` variants (`ThreadLocalRef`,
  other `Aggregate`s (including direct fieldless
  enum construction `Rvalue::Aggregate(AggregateKind::Adt, [])`, which is
  intentionally out of scope and lowers fail-closed to `.unsupported` in favor
  of constant and discriminant operations), `CopyForDeref`,
  `WrapUnsafeBinder`, and `Reborrow`).
-/
inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs rhs : Operand)
  | unaryOp (op : UnOp) (opnd : Operand)
  | cast (kind : CastKind) (opnd : Operand) (ty : MirTy)
  | discriminant (place : Place)
  | useRetag (op : Operand)
  | ref (mutability : Mutability) (place : Place)
  | addressOf (mutability : Mutability) (place : Place)
  | fakeAddressOf (place : Place)
  | aggregateTuple (fields : List Operand)
  | aggregateArray (elemTy : MirTy) (elems : List Operand)
  | repeat_ (op : Operand) (elemTy : MirTy) (count : Nat)
  | aggregateRangeTo (elemTy : MirTy) (endOp : Operand)
  | aggregateRangeFrom (elemTy : MirTy) (startOp : Operand)
  | unsupported

end Trusted.MirAst

end
