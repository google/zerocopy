-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_ast
prelude
import Init.NotationExtra
import Trusted.MirAst.Types
import Trusted.MirAst.Places

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
`rustc_middle::mir::BinOp`; upstream `BinOp::Cmp` (three-way `Ordering`
comparison, which returns the `core::cmp::Ordering` ADT) lowers at the enclosing
`Rvalue` level to `Rvalue.unsupported`. -/
inductive BinOp where
  | add | addUnchecked | addWithOverflow
  | sub | subUnchecked | subWithOverflow
  | mul | mulUnchecked | mulWithOverflow
  | div | rem
  | bitXor | bitAnd | bitOr
  | shl | shlUnchecked | shr | shrUnchecked
  | eq | lt | le | ne | ge | gt
  | offset

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

end BinOp

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
  no references or boxes, which covers every type that $M_{\text{anneal}}$
  executes (`.bool`, `.int`, `.unit`, `.never`, and admitted fieldless
  `.enum`). A retagging `Use(_, WithRetag::Yes)` of any other type lowers to
  `.unsupported` until stacked/tree-borrows retagging is modeled.
- `.binaryOp op lhs rhs` corresponds to `Rvalue::BinaryOp(op, (lhs, rhs))`.
- `.unaryOp op opnd` corresponds to `Rvalue::UnaryOp(op, opnd)`.
- `.discriminant place` corresponds to `Rvalue::Discriminant(place)`
  (`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`):

  > "Computes the discriminant of the place, returning it as an integer of type
  > [`discriminant_ty`]. Returns zero for types without discriminant."
  > "Note too that the value of the discriminant is not the same thing as the
  > variant index; use [`discriminant_for_variant`] to convert."
- `.ref mutability place` corresponds to `Rvalue::Ref(_, borrowKind, place)`.
- `.addressOf mutability place` corresponds to `Rvalue::RawPtr(kind, place)`.
- `.aggregateTuple fields` corresponds to
  `Rvalue::Aggregate(AggregateKind::Tuple, fields)`.
- `.unsupported` represents all other `Rvalue` variants (`Repeat`,
  `ThreadLocalRef`, `Cast`, non-tuple `Aggregate` (including direct fieldless
  enum construction `Rvalue::Aggregate(AggregateKind::Adt, [])`, which is
  intentionally out of scope and lowers fail-closed to `.unsupported` in favor
  of constant and discriminant operations), `CopyForDeref`,
  `WrapUnsafeBinder`, `Reborrow`, and a retagging `Use(_, WithRetag::Yes)` of a
  type that contains references or boxes).
-/
inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs rhs : Operand)
  | unaryOp (op : UnOp) (opnd : Operand)
  | discriminant (place : Place)
  | ref (mutability : Mutability) (place : Place)
  | addressOf (mutability : Mutability) (place : Place)
  | aggregateTuple (fields : List Operand)
  | unsupported

end Trusted.MirAst
