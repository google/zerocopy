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
public import Init.Data.Int.Basic

@[expose] public section

namespace Trusted.MirAst

/-!
# MIR Identifiers, Types, and Structural Equality (`Trusted.MirAst.Types`)

Core MIR index aliases (`DefId`, `LocalId`, `BasicBlockId`, `FieldIdx`),
type descriptors (`IntWidth`, `EnumTagRepr`, `EnumTy`, `MirTy`, `Mutability`),
and structural equality functions (`IntWidth.beq`, `MirTy.beq`, etc.). See
`Trusted.MirAst` for the full AST design rationale and modifier conventions.
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
- `.char` corresponds to `TyKind::Char` (a Unicode scalar value).
- `.ordering` corresponds to `TyKind::Adt(def, [])` where `def` is the
  `core::cmp::Ordering` lang item, the result type of `BinOp::Cmp`
  (`library/core/src/cmp.rs`, `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`):

  > "// This is a lang item only so that `BinOp::Cmp` in MIR can return it.
  > // It has no special behavior, but does require that the three variants
  > // `Less`/`Equal`/`Greater` remain `-1_i8`/`0_i8`/`+1_i8` respectively.
  > #[lang = \"Ordering\"]
  > #[repr(i8)]
  > pub enum Ordering {
  >     ...
  >     Less = -1,
  >     ...
  >     Equal = 0,
  >     ...
  >     Greater = 1,
  > }"
- `.enum ty` corresponds to a fieldless `TyKind::Adt(def, _)` enum
  (`def.is_enum()` where every variant has zero fields), carrying `ty : EnumTy`
  with its nominal `id`, `Ty::discriminant_ty` `(discrWidth, discrSigned)`,
  in-memory `tagRepr` (`Variants::Single` ZST vs. direct `Variants::Multiple`
  scalar tag), and variant `discriminants` bit patterns.
- `.tuple fields` corresponds to non-empty `TyKind::Tuple(fields)` (empty
  `TyKind::Tuple([])` corresponds to `.unit`). Only the `(T, bool)` result
  type of `BinOp::{Add,Sub,Mul}WithOverflow` on an integer `T`
  (`.tuple [.int w s, .bool]`) is executable; see
  `Trusted.MirSemantics.isOverflowPairTy`.
- `.ref mutability pointee` corresponds to `TyKind::Ref(_, pointee, mutability)`
  (regions are erased at runtime).
- `.rawPtr mutability pointee` corresponds to
  `TyKind::RawPtr(pointee, mutability)`.
- `.slice elem` corresponds to `TyKind::Slice(elem)`; it is unsized and
  appears only behind `.ref` or `.rawPtr` (Profile v2)
  (`compiler/rustc_type_ir/src/ty_kind.rs:146-147`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "/// The pointee of an array slice. Written as `[T]`.
  > Slice(I::Ty),"
- `.str` corresponds to `TyKind::Str`; it is unsized and appears behind shared
  `.ref` on string slices (`&str`, Profile v2)
  (`compiler/rustc_type_ir/src/ty_kind.rs:131-132`, same pin):

  > "/// The pointee of a string slice. Written as `str`.
  > Str,"
- `.array elem len` corresponds to `TyKind::Array(elem, len)` (Profile v2).
- `.rangeTo elem`, `.rangeFrom elem`, and `.range elem` correspond to the
  `core::ops::RangeTo<elem>`, `core::ops::RangeFrom<elem>`, and
  `core::ops::Range<elem>` `Adt` structs used to index slices (Profile v2)
  (`library/core/src/ops/range.rs:82-89,197-201,281-285`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "pub struct Range<Idx> {
  >     /// The lower bound of the range (inclusive).
  >     ...
  >     pub start: Idx,
  >     /// The upper bound of the range (exclusive).
  >     ...
  >     pub end: Idx,
  > }
  > ...
  > pub struct RangeFrom<Idx> {
  >     /// The lower bound of the range (inclusive).
  >     ...
  >     pub start: Idx,
  > }
  > ...
  > pub struct RangeTo<Idx> {
  >     /// The upper bound of the range (exclusive).
  >     ...
  >     pub end: Idx,
  > }"

  Profile v2 admits only `elem = usize` (`isSupportedV2LocalTy`).
- `.option elem` corresponds to `core::option::Option<elem>` (Profile v2)
  (`library/core/src/option.rs:597-606`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "pub enum Option<T> {
  >     /// No value.
  >     ...
  >     None,
  >     /// Some value of type `T`.
  >     ...
  >     Some(... T),
  > }"
- `.unsupported` represents all other `TyKind` variants (`Float`,
  other non-fieldless-enum `Adt`, `Foreign`, `Pat`, `FnDef`,
  `FnPtr`, `Dynamic`, `Closure`, `CoroutineClosure`, `Coroutine`, etc.), causing
  $M_{\text{anneal}}$ to fail closed with `FaultKind.unsupported`. -/
inductive MirTy where
  | bool
  | int (width : IntWidth) (signed : Bool)
  | unit
  | never
  | char
  | ordering
  | enum (ty : EnumTy)
  | tuple (fields : List MirTy)
  | ref (mutability : Mutability) (pointee : MirTy)
  | rawPtr (mutability : Mutability) (pointee : MirTy)
  | slice (elem : MirTy)
  | str
  | array (elem : MirTy) (len : Nat)
  | vec (elem : MirTy)
  | box (pointee : MirTy)
  | rangeTo (elem : MirTy)
  | rangeFrom (elem : MirTy)
  | range (elem : MirTy)
  | option (elem : MirTy)
  | unsupported

/-- Return `true` when `ty` is an unsized dynamically-sized MIR type
(`.slice _` or `.str`), which may appear behind `.ref` or `.rawPtr` but cannot
be stored directly in a local slot by value. -/
noncomputable def isUnsizedTy : MirTy → Bool
  | .slice _ | .str => true
  | _ => false

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
    | .char, .char => true
    | .ordering, .ordering => true
    | .enum ety₁, .enum ety₂ => EnumTy.beq ety₁ ety₂
    | .tuple fs₁, .tuple fs₂ => MirTy.beqList fs₁ fs₂
    | .ref m₁ p₁, .ref m₂ p₂ => Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂
    | .rawPtr m₁ p₁, .rawPtr m₂ p₂ => Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂
    | .slice e₁, .slice e₂ => MirTy.beq e₁ e₂
    | .str, .str => true
    | .array e₁ n₁, .array e₂ n₂ => Nat.beq n₁ n₂ && MirTy.beq e₁ e₂
    | .vec e₁, .vec e₂ => MirTy.beq e₁ e₂
    | .box p₁, .box p₂ => MirTy.beq p₁ p₂
    | .rangeTo e₁, .rangeTo e₂ => MirTy.beq e₁ e₂
    | .rangeFrom e₁, .rangeFrom e₂ => MirTy.beq e₁ e₂
    | .range e₁, .range e₂ => MirTy.beq e₁ e₂
    | .option e₁, .option e₂ => MirTy.beq e₁ e₂
    | .unsupported, .unsupported => true
    | _, _ => false

  /-- Elementwise structural equality on `List MirTy`. -/
  noncomputable def MirTy.beqList : List MirTy → List MirTy → Bool
    | [], [] => true
    | x :: xs, y :: ys => MirTy.beq x y && MirTy.beqList xs ys
    | _, _ => false
end

end Trusted.MirAst

end
