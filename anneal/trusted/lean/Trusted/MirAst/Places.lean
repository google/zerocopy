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
public import Init.Data.BitVec.BasicAux
public import Trusted.MirAst.Types

@[expose] public section

namespace Trusted.MirAst

/-!
# MIR Places, Projections, Constants, and Operands (`Trusted.MirAst.Places`)

Place projections, constant literals, and operands for captured
`Runtime(PostCleanup)` MIR.
-/

/-- Place projection elements (`*p`, `p.f`, or unmodeled projection).

Corresponds to `rustc_middle::mir::ProjectionElem` in
`compiler/rustc_middle/src/mir/syntax.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum ProjectionElem<V, T> {
>     Deref,
>     Field(FieldIdx, T),
>     Index(V),
>     ConstantIndex { offset: u64, min_length: u64, from_end: bool },
>     Subslice { from: u64, to: u64, from_end: bool },
>     Downcast(Option<Symbol>, VariantIdx),
>     OpaqueCast(T),
>     UnwrapUnsafeBinder(T),
>     PhantomDeref,
> }"

Constructor correspondence:
- `.deref` corresponds to `ProjectionElem::Deref`.
- `.field fieldIdx ty` corresponds to `ProjectionElem::Field(fieldIdx, ty)`.
- `.constantIndex offset minLength fromEnd` corresponds to
  `ProjectionElem::ConstantIndex { offset, min_length, from_end }` (Profile v2).
- `.unsupported` represents all other `ProjectionElem` variants (`Index`,
  `Subslice`, `Downcast`, `OpaqueCast`, `UnwrapUnsafeBinder`, and
  `PhantomDeref`). -/
inductive ProjectionElem where
  | deref
  | field (fieldIdx : FieldIdx) (ty : MirTy)
  | constantIndex (offset : Nat) (minLength : Nat) (fromEnd : Bool)
  | unsupported

/-- A MIR place (`rustc_middle::mir::Place` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct Place<'tcx> {
>     pub local: Local,
>     pub projection: &'tcx List<PlaceElem<'tcx>>,
> }"

A base local variable (`localId`) plus a list of projections (`projection`)
applied left-to-right. -/
structure Place where
  localId : LocalId
  projection : List ProjectionElem := []

/-- Read-only constant-memory byte (`AllocByte` without pointer provenance,
matching immutable provenance-free `GlobalAlloc::Memory` `.rodata` slices). -/
inductive RodataByte where
  | uninit
  | init (val : UInt8)

/-- Constant literal payload inside `ConstOperand`, corresponding to evaluated
`rustc_middle::mir::ConstValue` (`compiler/rustc_middle/src/mir/consts.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum ConstValue { Scalar(Scalar), ZeroSized, Slice { ... },
> Indirect { ... } }"

- `.scalar bits` corresponds to `ConstValue::Scalar(Scalar::Int(ScalarInt))`
  with raw 128-bit payload `bits`.
- `.zeroSized` corresponds to `ConstValue::ZeroSized`.
- `.rodataBytes bytes` corresponds to provenance-free by-value array constants
  (`ConstValue::Indirect` / multi-byte `Scalar::Int`, Profile v2), per
  `compiler/rustc_middle/src/mir/consts.rs` (`rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
  > "A value not representable by the other variants; needs to be stored
  > in-memory."
- `.rodataRef bytes alignLog2 offsetBytes sliceLen` corresponds to immutable
  `.rodata` references/pointers (`Scalar::Ptr`, `ConstValue::Slice`, or
  dangling aligned non-null zero-size `Scalar::Int` lowered to an empty
  allocation at offset `0` because Profile v2 has no pointer-to-integer
  observation) into a provenance-free `GlobalAlloc::Memory` allocation
  (`compiler/rustc_middle/src/mir/interpret/mod.rs` and `consts.rs`,
  `rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
  > "The alloc ID points to memory."
  > "The allocation storing the slice contents.
  > This always points to the beginning of the allocation." -/
inductive ConstLit where
  | scalar (bits : BitVec 128)
  | zeroSized
  | rodataBytes (bytes : List RodataByte)
  | rodataRef (bytes : List RodataByte) (alignLog2 : Nat)
      (offsetBytes : Nat) (sliceLen : Option Nat)

/-- Typed constant operand carrying `ty : MirTy` and `lit : ConstLit` directly
by value, corresponding to `rustc_middle::mir::ConstOperand` in
`compiler/rustc_middle/src/mir/syntax.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct ConstOperand<'tcx> {
>     pub span: Span,
>     pub user_ty: Option<UserTypeAnnotationIndex>,
>     pub const_: Const<'tcx>,
> }" -/
structure ConstOperand where
  ty : MirTy
  lit : ConstLit

/-- A MIR operand (`copy place`, `move place`, or `const c`).

Corresponds to `rustc_middle::mir::Operand` in
`compiler/rustc_middle/src/mir/syntax.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum Operand<'tcx> {
>     Copy(Place<'tcx>),
>     Move(Place<'tcx>),
>     Constant(Box<ConstOperand<'tcx>>),
>     RuntimeChecks(RuntimeChecks),
> }"

Constructor correspondence:
- `.copy place` corresponds to `Operand::Copy(place)`.
- `.move place` corresponds to `Operand::Move(place)`. Upstream
  `compiler/rustc_middle/src/mir/syntax.rs` (`rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`) notes that `Move` "*may*
  additionally overwrite the place with `uninit` bytes" ("**Needs
  clarification:** ... Currently (both in Miri and codegen) it has no effect at
  all unless it appears in an argument to `Call`"). As a deliberate,
  conservative over-approximation (matching `lean-miri`'s opt-in
  `deinitMovedPlace = true` mode), `Trusted.MirSemantics` unconditionally
  deinitializes non-ZST storage upon evaluating `.move`; this is sound because
  deinitializing causes any subsequent read without re-initialization to fault.
- `.constant c` corresponds strictly to `Operand::Constant(c)`.
- `Operand::RuntimeChecks(RuntimeChecks)` is crate-dependent and evaluated via
  a runtime hook rather than a compile-time constant
  (`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`: "This is not quite a const since
  its value can differ across crates within a single crate graph";
  `vendor/lean-miri/Miri/Interpreter/OperandMachine.lean` evaluates it via
  `h.runtimeChecks`). It is intentionally unmodeled in `MirAst.Operand` and
  must fail closed (be rejected by capture) rather than being folded into a
  `.constant` boolean. -/
inductive Operand where
  | copy (place : Place)
  | move (place : Place)
  | constant (c : ConstOperand)

end Trusted.MirAst

end
