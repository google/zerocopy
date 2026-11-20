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
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic

namespace Trusted.MirAst

/-!
# Anneal MIR Abstract Syntax (`Trusted.MirAst`)

## Human-Comprehension Priority

`Trusted.MirAst` sits in the direct transitive dependency cone of Anneal's
top-level verification obligations (`CrateTheorem`, `UnitTheorem`,
`ProgramVerified`, and `BodyVerified` in `Trusted.MirSemantics`) as well as
the correspondence theorem statements (`CorrespondenceClaim` and
`FaultEquivalenceClaim` in `Trusted.Correspondence`). Human comprehension is
therefore the governing design priority for every declaration in this file:

1. **Direct, self-evident representations:** Every AST type and constructor is
   written in plain, first-order inductive form without clever encodings or
   indirect index indirections, so a human reviewer can see at a glance that the
   syntax means in mathematical terms what it means in intuitive Rust MIR terms.
2. **Explicit fail-closed boundaries (`.unsupported`):** Every syntax category
   with unmodeled `rustc` variants either includes an explicit `.unsupported`
   constructor or documents where unmodeled variants are handled (`Operand`
   relies on capture rejecting `RuntimeChecks`, `BinOp` routes `Cmp` to
   `Rvalue.unsupported`, and `ConstLit` handles non-scalar constants one level
   up), and every comment documents both the modeled and unmodeled upstream
   `rustc_middle::mir` variants.
3. **Pinned upstream citations:** Every modeled AST type and operator
   declaration cites (and, where helpful for auditing, quotes) the
   corresponding `rust-lang/rust` definition at `vendor/lean-miri`'s upstream
   `rustc` commit `8144389c895da997dbdecaa635e41d6a50be6ffd` (and, where
   relevant, `rust-lang/reference` commit
   `a286e1ecb8ce193d50056e4bb042eea9b23876ef`, pinned by
   `rust-lang/rust@8144389c`'s `src/doc/reference` submodule, and
   `anneal-rustc-capture`'s pinned `rustc` commit
   `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`).

## Correspondence with `rustc_middle::mir`

This module defines the trusted abstract syntax tree for post-cleanup runtime
Mid-level Intermediate Representation (`Runtime(PostCleanup)` MIR) extracted by
`anneal-rustc-capture`, corresponding to
`compiler/rustc_middle/src/mir/syntax.rs` and
`compiler/rustc_middle/src/mir/mod.rs` in `rust-lang/rust` at commit
`8144389c895da997dbdecaa635e41d6a50be6ffd`:

> "The lowered representation of a single function."
>
> "The first local is the return value pointer, followed by `arg_count`
> locals for the function arguments, followed by any user-declared
> variables and temporaries."
> (`compiler/rustc_middle/src/mir/mod.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Unlike `rustc_middle::mir` (which interns types into `TyCtxt` as `Ty<'tcx>`)
and `lean-miri` (`Miri.MIR.Syntax`, which indexes a side-table of interned
types via `TyId`), `Trusted.MirAst` carries structural `MirTy` descriptors
directly by value on `Body.locals`, `ConstOperand`, and
`ProjectionElem.field`. This eliminates out-of-bounds `TyId` lookup states
inside $M_{\text{anneal}}$ and allows `Anneal.MirWp` to evaluate operand and
local types structurally without threading a global type table.

## Declaration Modifiers

Every `def` and term-level `abbrev` in `Trusted.MirAst` and
`Trusted.MirSemantics` carries `noncomputable`. For a computable recursive
definition (such as `natListBeq` or `MirTy.beq`), Lean adds a `._unsafe_rec`
compiler helper marked `partial`, and `TrustedBoundary.validateRepoConstant`
rejects every `partial` constant; `noncomputable` stops Lean from adding the
helper. Any non-recursive value definition that calls a `noncomputable` helper
(such as `checkVal` or `BodyStaticAdmitted`) also requires `noncomputable` in
Lean 4 (otherwise compilation fails with `dependsOnNoncomputable`). Because
`TrustedBoundary.inspectNodeKind` forbids `noncomputable section`, each
declaration carries the modifier itself. Remaining non-recursive value
definitions that do not call `noncomputable` helpers, together with
`Prop`-valued definitions, carry `noncomputable` by uniform convention so one
rule covers every definition and adding recursion or a call to a `noncomputable`
helper never requires a modifier change. Type abbreviations such as `DefId`
define types rather than terms and carry no modifier.
-/

/-- Function definition identifier (`rustc_span::def_id::DefId` index in the
captured program unit; `compiler/rustc_span/src/def_id.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct DefId { ... pub index: DefIndex, pub krate: CrateNum, ... }" -/
abbrev DefId := Nat

/-- Local variable slot index (`rustc_middle::mir::Local` in
`compiler/rustc_middle/src/mir/mod.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "rustc_index::newtype_index! { ... pub struct Local { const RETURN_PLACE = 0;
> } }" -/
abbrev LocalId := Nat

/-- Basic-block index (`rustc_middle::mir::BasicBlock` in
`compiler/rustc_middle/src/mir/mod.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "rustc_index::newtype_index! { ... pub struct BasicBlock {
> const START_BLOCK = 0; } }" -/
abbrev BasicBlockId := Nat

/-- Aggregate field index (`rustc_abi::FieldIdx` in
`compiler/rustc_abi/src/layout.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "rustc_index::newtype_index! { ... pub struct FieldIdx {} }" -/
abbrev FieldIdx := Nat

/-- Memory allocation identifier (`rustc_middle::mir::interpret::AllocId` in
`compiler/rustc_middle/src/mir/interpret/mod.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct AllocId(pub NonZero<u64>);" -/
abbrev AllocId := Nat

/-- Integer and pointer-sized scalar widths (`i8`/`u8` through `i128`/`u128`
and target-pointer-sized `isize`/`usize`).

Corresponds to `rustc_ast_ir::IntTy` and `rustc_ast_ir::UintTy` in
`compiler/rustc_ast_ir/src/lib.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and the Rust Reference
(`src/types/numeric.md`, `rust-lang/reference`
`a286e1ecb8ce193d50056e4bb042eea9b23876ef`):

> "pub enum IntTy { Isize, I8, I16, I32, I64, I128, }"
> "pub enum UintTy { Usize, U8, U16, U32, U64, U128, }"
> (`compiler/rustc_ast_ir/src/lib.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)
>
> "The unsigned integer types consist of: ... `u8` ... `u16` ... `u32` ...
> `u64` ... `u128`"
> "The signed two's complement integer types consist of: ... `i8` ... `i16` ...
> `i32` ... `i64` ... `i128`"
> "The `isize` type is a signed two's complement integer type with the same
> number of bits as the platform's pointer type."
> (`src/types/numeric.md`, `rust-lang/reference`
> `a286e1ecb8ce193d50056e4bb042eea9b23876ef`) -/
inductive IntWidth where
  | i8 | i16 | i32 | i64 | i128 | isize

namespace IntWidth

/-- Size in bytes on 64-bit targets (`usize`/`isize` = 8 bytes), matching
`rustc_abi::Integer::size` (`compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "I8 => Size::from_bytes(1), I16 => Size::from_bytes(2),
> I32 => Size::from_bytes(4), I64 => Size::from_bytes(8),
> I128 => Size::from_bytes(16)" -/
noncomputable def byteSize : IntWidth → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 | .isize => 8
  | .i128 => 16

/-- Width in bits (`8`, `16`, `32`, `64`, or `128`). -/
noncomputable def bitWidth (w : IntWidth) : Nat := w.byteSize * 8

end IntWidth

/-- Reference and raw-pointer mutability (`rustc_ast_ir::Mutability` in
`compiler/rustc_ast_ir/src/lib.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum Mutability { ... Not, Mut, }"

- `.shared` corresponds to `Mutability::Not` (`&T`, `*const T`).
- `.mut` corresponds to `Mutability::Mut` (`&mut T`, `*mut T`). -/
inductive Mutability where
  | shared
  | mut

/-- In-memory tag representation of a fieldless Rust enum, corresponding to
`rustc_abi::Variants` (`compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum Variants<FieldIdx: Idx, VariantIdx: Idx> {
>     ...
>     Empty,
>     ...
>     Single {
>         ...
>         index: VariantIdx,
>     },
>     ...
>     Multiple {
>         tag: Scalar,
>         tag_encoding: TagEncoding<VariantIdx>,
>         tag_field: FieldIdx,
>         variants: IndexVec<VariantIdx, VariantLayout<FieldIdx>>,
>     },
> }"

Constructor correspondence:
- `.zeroSized` corresponds to `Variants::Single { index: 0 }` on an inhabited
  1-variant fieldless enum (`Size::ZERO` 0-byte ZST, where no tag bytes are
  stored in memory and `ConstValue::ZeroSized` represents the unique variant).
  Note that `#[repr(C)]` and `#[repr(int)]` 1-variant enums retain an explicit
  tag scalar (`Variants::Multiple` / `.scalar`) rather than `.zeroSized`.
- `.scalar width signed` corresponds to `Variants::Multiple { tag,
  tag_encoding: TagEncoding::Direct, tag_field: 0, .. }` where `tag` has
  primitive integer representation `(width, signed)` (`tag.primitive()` in
  `compiler/rustc_abi/src/lib.rs`). (Uninhabited 0-variant enums
  `Variants::Empty` have no admitted `EnumTagRepr` and are rejected by
  `Trusted.MirSemantics.enumAdmitted`.) -/
inductive EnumTagRepr where
  | zeroSized
  | scalar (width : IntWidth) (signed : Bool)

/-- Structural descriptor for a fieldless Rust enum (`TyKind::Adt(def, _)` with
`def.is_enum()` and zero fields on every variant), carrying its nominal
type-identity key `id`, its `Ty::discriminant_ty` integer representation
`(discrWidth, discrSigned)`, its in-memory tag representation `tagRepr`, and
its declaration-indexed discriminant bit-pattern table `discriminants`.

Corresponds to `rustc_middle::ty::util::Discr`
(`compiler/rustc_middle/src/ty/util.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`), `Ty::discriminant_ty`
(`compiler/rustc_middle/src/ty/sty.rs:1717`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`), and the Rust Reference
(`src/items/enumerations.md`, `rust-lang/reference`
`a286e1ecb8ce193d50056e4bb042eea9b23876ef`):

> "pub struct Discr<'tcx> {
>     /// Bit representation of the discriminant (e.g., `-1i8` is `0xFF_u128`).
>     pub val: u128,
>     pub ty: Ty<'tcx>,
> }"
> (`compiler/rustc_middle/src/ty/util.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)
>
> "Enums without a [primitive representation] have discriminants of type
> `isize`."
> "Enums with a [primitive representation] have discriminants of the type named
> by the representation."
> (`src/items/enumerations.md`, `rust-lang/reference`
> `a286e1ecb8ce193d50056e4bb042eea9b23876ef`)

Each entry `d ∈ discriminants` stores the unsigned bit pattern `Discr.val`
truncated to `discrWidth` (`d < Nat.pow 2 discrWidth.bitWidth`; e.g., `-1i8` is
`255` and `-1isize` on 64-bit targets is `2^64 - 1`).

All five fields (`id` plus the four discriminant and tag layout fields) are
required explicitly (with no defaults) so a producer cannot silently inherit an
`isize` discriminant or tag layout that disagrees with `rustc`. Direct
`Rvalue::Aggregate(AggregateKind::Adt, [])` enum construction is intentionally
out of scope and fails closed as `Rvalue.unsupported` (fieldless enum values
are modeled via constant and `Rvalue.discriminant` operations). -/
structure EnumTy where
  id : Nat
  discrWidth : IntWidth
  discrSigned : Bool
  tagRepr : EnumTagRepr
  discriminants : List Nat

/-- Structural MIR type descriptors carried directly by value in
`Trusted.MirAst`.

Corresponds to monomorphized `rustc_type_ir::TyKind` in
`compiler/rustc_type_ir/src/ty_kind.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum TyKind<I: Interner> { Bool, Char, Int(IntTy), Uint(UintTy),
> Float(FloatTy), Adt(I::AdtDef, I::GenericArgs), Foreign(I::ForeignId),
> Str, Array(I::Ty, Const<I>), Pat(I::Ty, I::Pat), Slice(I::Ty),
> RawPtr(I::Ty, Mutability), Ref(Region<I>, I::Ty, Mutability),
> FnDef(I::FunctionId, ty::Binder<I, I::GenericArgs>),
> FnPtr(ty::Binder<I, FnSigTys<I>>, FnHeader<I>),
> UnsafeBinder(UnsafeBinderInner<I>), Dynamic(...), Closure(...),
> CoroutineClosure(...), Coroutine(...), CoroutineWitness(...), Never,
> Tuple(I::Tys), ... }"

Constructor correspondence:
- `.bool` corresponds to `TyKind::Bool`.
- `.int width true` corresponds to `TyKind::Int(width)` (`i8`, `i16`, `i32`,
  `i64`, `i128`, `isize`).
- `.int width false` corresponds to `TyKind::Uint(width)` (`u8`, `u16`, `u32`,
  `u64`, `u128`, `usize`).
- `.unit` corresponds to the 0-element unit tuple `TyKind::Tuple([])` (`()`).
- `.never` corresponds to the uninhabited never type `TyKind::Never` (`!`).
- `.enum ty` corresponds to a fieldless `TyKind::Adt(def, _)` enum
  (`def.is_enum()` where every variant has zero fields), carrying `ty : EnumTy`
  with its nominal `id`, `Ty::discriminant_ty` `(discrWidth, discrSigned)`,
  in-memory `tagRepr` (`Variants::Single` ZST vs. direct `Variants::Multiple`
  scalar tag), and variant `discriminants` bit patterns.
- `.tuple fields` corresponds to non-empty `TyKind::Tuple(fields)` (empty
  `TyKind::Tuple([])` corresponds to `.unit`).
- `.ref mutability pointee` corresponds to `TyKind::Ref(_, pointee, mutability)`
  (regions are erased at runtime).
- `.rawPtr mutability pointee` corresponds to
  `TyKind::RawPtr(pointee, mutability)`.
- `.unsupported` represents all other `TyKind` variants (`Char`, `Float`,
  non-fieldless-enum `Adt`, `Foreign`, `Str`, `Array`, `Pat`, `Slice`, `FnDef`,
  `FnPtr`, `Dynamic`, `Closure`, `CoroutineClosure`, `Coroutine`, etc.), causing
  $M_{\text{anneal}}$ to fail closed with `FaultKind.unsupported`. -/
inductive MirTy where
  | bool
  | int (width : IntWidth) (signed : Bool)
  | unit
  | never
  | enum (ty : EnumTy)
  | tuple (fields : List MirTy)
  | ref (mutability : Mutability) (pointee : MirTy)
  | rawPtr (mutability : Mutability) (pointee : MirTy)
  | unsupported

/-- Explicit structural equality on `IntWidth` (avoiding `deriving BEq` inside
`Trusted.*` so `TrustedBoundary.lean` sees only pure kernel definitions). -/
noncomputable def IntWidth.beq : IntWidth → IntWidth → Bool
  | .i8, .i8 => true
  | .i16, .i16 => true
  | .i32, .i32 => true
  | .i64, .i64 => true
  | .i128, .i128 => true
  | .isize, .isize => true
  | _, _ => false

/-- Explicit structural equality on `Mutability`. -/
noncomputable def Mutability.beq : Mutability → Mutability → Bool
  | .shared, .shared => true
  | .mut, .mut => true
  | _, _ => false

/-- Elementwise structural equality on `List Nat`. -/
noncomputable def natListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && natListBeq xs ys
  | _, _ => false

/-- Explicit structural equality on `EnumTagRepr`. -/
noncomputable def EnumTagRepr.beq : EnumTagRepr → EnumTagRepr → Bool
  | .zeroSized, .zeroSized => true
  | .scalar w₁ s₁, .scalar w₂ s₂ => IntWidth.beq w₁ w₂ && (s₁ == s₂)
  | _, _ => false

/-- Explicit structural equality on `EnumTy`. -/
noncomputable def EnumTy.beq (a b : EnumTy) : Bool :=
  Nat.beq a.id b.id &&
    IntWidth.beq a.discrWidth b.discrWidth &&
    (a.discrSigned == b.discrSigned) &&
    EnumTagRepr.beq a.tagRepr b.tagRepr &&
    natListBeq a.discriminants b.discriminants

mutual
  /-- Explicit structural equality on `MirTy`. -/
  noncomputable def MirTy.beq : MirTy → MirTy → Bool
    | .bool, .bool => true
    | .int w₁ s₁, .int w₂ s₂ => IntWidth.beq w₁ w₂ && (s₁ == s₂)
    | .unit, .unit => true
    | .never, .never => true
    | .enum ety₁, .enum ety₂ => EnumTy.beq ety₁ ety₂
    | .tuple fs₁, .tuple fs₂ => MirTy.beqList fs₁ fs₂
    | .ref m₁ p₁, .ref m₂ p₂ => Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂
    | .rawPtr m₁ p₁, .rawPtr m₂ p₂ => Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂
    | .unsupported, .unsupported => true
    | _, _ => false

  /-- Elementwise structural equality on `List MirTy`. -/
  noncomputable def MirTy.beqList : List MirTy → List MirTy → Bool
    | [], [] => true
    | x :: xs, y :: ys => MirTy.beq x y && MirTy.beqList xs ys
    | _, _ => false
end

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
- `.unsupported` represents all other `ProjectionElem` variants (`Index`,
  `ConstantIndex`, `Subslice`, `Downcast`, `OpaqueCast`, `UnwrapUnsafeBinder`,
  and `PhantomDeref`). -/
inductive ProjectionElem where
  | deref
  | field (fieldIdx : FieldIdx) (ty : MirTy)
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

/-- Constant literal payload inside `ConstOperand`, corresponding to evaluated
`rustc_middle::mir::ConstValue` (`compiler/rustc_middle/src/mir/consts.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum ConstValue { Scalar(Scalar), ZeroSized, Slice { ... },
> Indirect { ... } }"

- `.scalar bits` corresponds to `ConstValue::Scalar(Scalar::Int(ScalarInt))`
  with raw 128-bit payload `bits`.
- `.zeroSized` corresponds to `ConstValue::ZeroSized`.
- Pointer/slice/indirect constants lower at the enclosing rvalue or statement
  level to `.unsupported`. -/
inductive ConstLit where
  | scalar (bits : BitVec 128)
  | zeroSized

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

/-- A MIR statement inside a basic block (`rustc_middle::mir::StatementKind` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum StatementKind<'tcx> {
>     Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),
>     FakeRead(Box<(FakeReadCause, Place<'tcx>)>),
>     SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },
>     StorageLive(Local),
>     StorageDead(Local),
>     PlaceMention(Box<Place<'tcx>>),
>     AscribeUserType(Box<(Place<'tcx>, UserTypeProjection)>, ty::Variance),
>     Coverage(CoverageKind),
>     Intrinsic(Box<NonDivergingIntrinsic<'tcx>>),
>     ConstEvalCounter,
>     Nop,
>     BackwardIncompatibleDropHint { ... },
> }"

Constructor correspondence:
- `.assign dst rvalue` corresponds to `StatementKind::Assign((dst, rvalue))`.
- `.storageLive localId` corresponds to `StatementKind::StorageLive(localId)`.
- `.storageDead localId` corresponds to `StatementKind::StorageDead(localId)`.
- `.nop` corresponds to `StatementKind::Nop`.
- `.unsupported` represents all other `StatementKind` variants (`FakeRead`,
  `SetDiscriminant`, `PlaceMention`, `AscribeUserType`, `Coverage`, `Intrinsic`,
  `ConstEvalCounter`, and `BackwardIncompatibleDropHint`). -/
inductive StatementKind where
  | assign (dst : Place) (rvalue : Rvalue)
  | storageLive (localId : LocalId)
  | storageDead (localId : LocalId)
  | nop
  | unsupported

/-- Branch table for `TerminatorKind.switchInt`
(`rustc_middle::mir::SwitchTargets` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct SwitchTargets {
>     pub(super) values: SmallVec<[Pu128; 1]>,
>     pub(super) targets: SmallVec<[BasicBlock; 2]>,
> }"

Represented explicitly as `branches : List (BitVec 128 × BasicBlockId)` paired
with the fallback target `otherwise : BasicBlockId` (matching the comment in
`syntax.rs`: `normal: SmallVec<[(Pu128, BasicBlock); 1]>, otherwise:
BasicBlock`). -/
structure SwitchTargets where
  branches : List (BitVec 128 × BasicBlockId)
  otherwise : BasicBlockId

/-- Unwind continuation action on panicking terminators
(`rustc_middle::mir::UnwindAction` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum UnwindAction {
>     Continue,
>     Unreachable,
>     Terminate(UnwindTerminateReason),
>     Cleanup(BasicBlock),
> }" -/
inductive UnwindAction where
  | continue_
  | unreachable
  | terminate
  | cleanup (block : BasicBlockId)

/-- Built-in MIR `Assert` condition kind (`rustc_middle::mir::AssertKind` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum AssertKind<O> {
>     BoundsCheck { len: O, index: O },
>     Overflow(BinOp, O, O),
>     OverflowNeg(O),
>     DivisionByZero(O),
>     RemainderByZero(O),
>     ResumedAfterReturn(CoroutineKind),
>     ResumedAfterPanic(CoroutineKind),
>     ResumedAfterDrop(CoroutineKind),
>     MisalignedPointerDereference { required: O, found: O },
>     NullPointerDereference,
>     NullReferenceConstructed,
>     InvalidEnumConstruction(O),
> }"

Constructor correspondence:
- `.overflow op` corresponds to `AssertKind::Overflow(op, _, _)`.
- `.overflowNeg` corresponds to `AssertKind::OverflowNeg(_)`.
- `.divByZero` corresponds to `AssertKind::DivisionByZero(_)`.
- `.remByZero` corresponds to `AssertKind::RemainderByZero(_)`.
- `.boundsCheck` corresponds to `AssertKind::BoundsCheck { .. }`.
- `.misalignedPtrDeref` corresponds to
  `AssertKind::MisalignedPointerDereference { .. }`.
- `.nullPtrDeref` corresponds to `AssertKind::NullPointerDereference`.
- `.unsupported` represents all other `AssertKind` variants
  (`ResumedAfterReturn`, `ResumedAfterPanic`, `ResumedAfterDrop`,
  `NullReferenceConstructed`, and `InvalidEnumConstruction`), as well as
  `AssertKind::Overflow(BinOp::Cmp, _, _)` whose `BinOp` lowers to
  `.unsupported`. -/
inductive AssertKind where
  | overflow (op : BinOp)
  | overflowNeg
  | divByZero
  | remByZero
  | boundsCheck
  | misalignedPtrDeref
  | nullPtrDeref
  | unsupported

/-- A MIR basic-block terminator (`rustc_middle::mir::TerminatorKind` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum TerminatorKind<'tcx> {
>     Goto { target: BasicBlock, loop_hint_attrs: ThinVec<UnrollAttr> },
>     SwitchInt { discr: Operand<'tcx>, targets: SwitchTargets },
>     UnwindResume,
>     UnwindTerminate(UnwindTerminateReason),
>     Return,
>     Unreachable,
>     Drop { place: Place<'tcx>, target: BasicBlock, unwind: UnwindAction,
>            replace: bool, drop: Option<BasicBlock> },
>     Call { func: Operand<'tcx>, args: Box<[Spanned<Operand<'tcx>>]>,
>            destination: Place<'tcx>, target: Option<BasicBlock>,
>            unwind: UnwindAction, call_source: CallSource, fn_span: Span },
>     TailCall { ... },
>     Assert { cond: Operand<'tcx>, expected: bool,
>              msg: Box<AssertMessage<'tcx>>,
>              target: BasicBlock, unwind: UnwindAction },
>     Yield { ... },
>     CoroutineDrop,
>     FalseEdge { real_target: BasicBlock, imaginary_target: BasicBlock },
>     FalseUnwind { real_target: BasicBlock, unwind: UnwindAction },
>     InlineAsm { ... },
> }"

Constructor correspondence:
- `.goto target` corresponds to `TerminatorKind::Goto { target, .. }`
  (`loop_hint_attrs` are diagnostic/optimization hints with no operational
  effect).
- `.switchInt discr targets` corresponds to
  `TerminatorKind::SwitchInt { discr, targets }`.
- `.return_` corresponds to `TerminatorKind::Return`.
- `.unreachable` corresponds to `TerminatorKind::Unreachable`.
- `.unwindResume` corresponds to `TerminatorKind::UnwindResume`.
- `.assert cond expected msg target unwind` corresponds to
  `TerminatorKind::Assert { cond, expected, msg, target, unwind }`.
- `.call callee args dst target unwind` corresponds to direct `FnDef`
  `TerminatorKind::Call`.
- `.unsupported` represents all other `TerminatorKind` variants
  (`UnwindTerminate`, `Drop`, indirect `Call`, `TailCall`, `Yield`,
  `CoroutineDrop`, `FalseEdge`, `FalseUnwind`, and `InlineAsm`). -/
inductive TerminatorKind where
  | goto (target : BasicBlockId)
  | switchInt (discr : Operand) (targets : SwitchTargets)
  | return_
  | unreachable
  | unwindResume
  | assert (cond : Operand) (expected : Bool) (msg : AssertKind)
      (target : BasicBlockId) (unwind : UnwindAction)
  | call (callee : DefId) (args : List Operand) (dst : Place)
      (target : Option BasicBlockId) (unwind : UnwindAction)
  | unsupported

/-- A MIR basic block (`rustc_middle::mir::BasicBlockData` in
`compiler/rustc_middle/src/mir/mod.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct BasicBlockData<'tcx> {
>     pub statements: Vec<Statement<'tcx>>,
>     pub after_last_stmt_debuginfos: StmtDebugInfos<'tcx>,
>     pub terminator: Option<Terminator<'tcx>>,
>     pub is_cleanup: bool,
> }"

Sequential `statements` followed by a `terminator` and the `cleanup`
(`is_cleanup`) unwind-pad marker. -/
structure BasicBlock where
  statements : List StatementKind
  terminator : TerminatorKind
  cleanup : Bool := false

/-- A MIR function body (`rustc_middle::mir::Body` in
`compiler/rustc_middle/src/mir/mod.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct Body<'tcx> {
>     pub basic_blocks: BasicBlocks<'tcx>,
>     pub phase: MirPhase,
>     pub pass_count: usize,
>     pub source: MirSource<'tcx>,
>     pub source_scopes: IndexVec<SourceScope, SourceScopeData<'tcx>>,
>     pub coroutine: Option<Box<CoroutineInfo<'tcx>>>,
>     pub local_decls: IndexVec<Local, LocalDecl<'tcx>>,
>     pub user_type_annotations: ty::CanonicalUserTypeAnnotations<'tcx>,
>     pub arg_count: usize,
>     pub spread_arg: Option<Local>,
>     ...
> }"

Local slot layout (`compiler/rustc_middle/src/mir/mod.rs`):
- Local `0` (`_0`) is the return place (`locals[0]`).
- Locals `1 .. argumentCount` are the function parameters
  (`locals[1..=argumentCount]`).
- Locals `> argumentCount` are temporaries and user-declared locals.
- `isUnsafe` records whether the function signature has
  `rustc_hir::Safety::Unsafe` (`compiler/rustc_hir/src/hir.rs`, `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`):

  > "pub enum Safety {
  >     ...
  >     #[default]
  >     Unsafe,
  >     Safe,
  > }"

  Only bodies with `isUnsafe = true` may assume a caller-supplied safety
  precondition in `Trusted.MirSemantics.BodyVerified`.
- `identity` records a producer-supplied definition identity string (such as
  `TyCtxt::def_path_str` in `compiler/rustc_middle/src/ty/print/pretty.rs`,
  line 2193, `rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`, which
  is intended for user output rather than guaranteed unique) used to index
  `Trusted.MirSemantics.Specs.safety`. Single-body unit test fixtures that do
  not use `BodyVerified` / `ProgramVerified` may leave the default
  `identity := ""`; `BodyStaticAdmitted` rejects empty `identity` strings and
  `ProgramVerified` enforces pairwise-distinct identities across all bodies in
  `Program.bodies` (failing closed on any collision) so two functions can never
  silently alias in `Specs.safety`.
-/
structure Body where
  argumentCount : Nat
  locals : List MirTy
  basicBlocks : List BasicBlock
  isUnsafe : Bool := false
  identity : String := ""

/-- Capture scope of a `Program`, distinguishing whole-crate verification
(`.crate`, covering every executable body in the compiled crate via
`Trusted.MirSemantics.CrateTheorem`) from selected proof-unit verification
(`.unit`, covering a designated root item and its captured dependencies via
`Trusted.MirSemantics.UnitTheorem`).

Whether a `.crate` capture actually includes every executable body and
reachable callee in the compiled crate is an external obligation of the
capture producer (such as a future `anneal-rustc-capture` emitter), not
checked by the Lean semantics alone. -/
inductive VerificationScope where
  | unit
  | crate

/-- A complete MIR program unit: function bodies indexed by `DefId`, an entry
function `entryDefId`, the captured target's pointer width `pointerWidthBits`,
the MIR semantic profile version `mirProfileVersion`, and the capture scope
`scope`.

1. **Target pointer width (`pointerWidthBits`):**
   `pointerWidthBits` records the target layout that `rustc` used when it
   lowered the program. `rustc` sizes `isize` and `usize` by the target data
   layout's pointer width (`compiler/rustc_middle/src/ty/layout.rs` and
   `compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
   `8144389c895da997dbdecaa635e41d6a50be6ffd`):

   > "ty::IntTy::Isize => cx.data_layout().ptr_sized_integer(),"
   > (`IntegerExt::from_int_ty`)
   >
   > "match self.pointer_offset().bits() { 16 => I16, 32 => I32, 64 => I64, ..."
   > (`TargetDataLayout::ptr_sized_integer`)

   `IntWidth.byteSize` fixes `isize`/`usize` at 8 bytes, so the semantics models
   only 64-bit targets. `Trusted.MirSemantics.initState` and
   `Trusted.Correspondence.initRefState` reject any program whose
   `pointerWidthBits` is not `64` with `FaultKind.unsupported` (`.blocked`).

2. **MIR semantic profile version (`mirProfileVersion`):**
   `mirProfileVersion` pins the contract version of the post-cleanup runtime MIR
   semantic profile shared between `anneal-rustc-capture` (`rust-lang/rust`
   `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `Trusted.MirSemantics`, and
   `Trusted.Correspondence` (`vendor/lean-miri` upstream `rustc` reference
   `8144389c895da997dbdecaa635e41d6a50be6ffd`). Both `initState` and
   `initRefState` fail closed with `FaultKind.unsupported` (`.blocked`)
   whenever `p.mirProfileVersion ≠ 1`.

**Producer obligations:** `Program.pointerWidthBits` and
`Program.mirProfileVersion` carry no defaults so every `Program` literal (both
hand-written canaries and serialized captures) must state the target layout and
profile contract explicitly rather than silently inheriting accepted values.
The remaining Lean field defaults across `Trusted.MirAst` exist solely for
concise hand-written canary literals. Two defaults equal unprojected/non-cleanup
values (`BasicBlock.cleanup := false` and `Place.projection := []`), and
`Program.entryDefId := 0` selects body `0` as the entry point. The remaining
three defaults (`Program.scope := .unit`, `Body.isUnsafe := false`, and
`Body.identity := ""`) fail closed (`scope := .unit` rejects `CrateTheorem` and
admits only the weaker `UnitTheorem` claim, `isUnsafe := false` withholds
caller safety preconditions, and `identity := ""` is rejected by
`BodyStaticAdmitted`). Any serializer or MIR producer (such as
`anneal-rustc-capture`) MUST explicitly populate all of these fields—
`pointerWidthBits` (from the compiled target's data layout),
`mirProfileVersion` (from the capture profile contract), `scope`, `entryDefId`,
`Body.isUnsafe`, `Body.identity`, `BasicBlock.cleanup` (from
`BasicBlockData::is_cleanup`), and `Place.projection` (from
`Place::projection`). Likewise, when `scope = .crate`, completeness of `bodies`
(ensuring every executable body and reachable callee in the crate is included)
is an external producer obligation, not checked by `Trusted.MirSemantics`
alone. -/
structure Program where
  bodies : List Body
  entryDefId : DefId := 0
  pointerWidthBits : Nat
  mirProfileVersion : Nat
  scope : VerificationScope := .unit

end Trusted.MirAst
