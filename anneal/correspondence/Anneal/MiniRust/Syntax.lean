-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic

namespace Anneal.MiniRust

/-!
# MiniRust Abstract Syntax, Types, and Values (`Anneal.MiniRust.Syntax`)

Independent, constructive Lean 4 transcription of MiniRust's core abstract
syntax, type descriptors, value domain, and abstract bytes from upstream
`minirust/minirust` commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`:
- `spec/lang/syntax.md`
- `spec/lang/types.md`
- `spec/lang/values.md`
- `spec/lang/representation.md`

This module depends solely on locked `Init.*` primitives (zero `Trusted.*`,
zero `Miri.*`, zero `Classical.choice`).
-/

/-- Allocation identifier (`spec/mem/basic.md`: `pub struct AllocId(Int);`). -/
abbrev AllocId := Nat

/-- Local variable identifier (`spec/lang/syntax.md`: `LocalName`). -/
abbrev LocalName := Nat

/-- Basic block identifier (`spec/lang/syntax.md`: `BbName`). -/
abbrev BbName := Nat

/-- Function identifier (`spec/lang/syntax.md`: `FnName`). -/
abbrev FnName := Nat

/-- Integer signedness (`spec/lang/types.md`: `Signedness`). -/
inductive Signedness where
  | signed
  | unsigned

/-- Explicit structural equality on `Signedness`. -/
def Signedness.beq : Signedness → Signedness → Bool
  | .signed, .signed => true
  | .unsigned, .unsigned => true
  | _, _ => false

/-- Byte size descriptor (`spec/prelude/main.md`: `Size`). -/
structure Size where
  bytes : Nat

/-- Explicit structural equality on `Size`. -/
def Size.beq (a b : Size) : Bool :=
  Nat.beq a.bytes b.bytes

/-- Bit width of `s : Size` (`s.bytes * 8`). -/
def Size.bits (s : Size) : Nat :=
  s.bytes * 8

/-- Alignment in bytes (a power of two; `spec/prelude/main.md`: `Align`). -/
structure Align where
  bytes : Nat

/-- Explicit structural equality on `Align`. -/
def Align.beq (a b : Align) : Bool :=
  Nat.beq a.bytes b.bytes

/-- Whether byte address `addr` is aligned to `a` (`addr % a.bytes == 0`). -/
def Align.isAligned (a : Align) (addr : Nat) : Bool :=
  if Nat.beq a.bytes 0 then false
  else Nat.beq (Nat.mod addr a.bytes) 0

/-- Integer type descriptor (`spec/lang/types.md`: `pub struct IntType`). -/
structure IntType where
  signed : Signedness
  size : Size

/-- Explicit structural equality on `IntType`. -/
def IntType.beq (a b : IntType) : Bool :=
  Signedness.beq a.signed b.signed && Size.beq a.size b.size

/-- Bit width of an integer type (`it.size.bytes * 8`). -/
def IntType.bitWidth (it : IntType) : Nat :=
  it.size.bits

/-- Minimum mathematical integer representable by `it`. -/
def IntType.minVal (it : IntType) : Int :=
  match it.signed with
  | .unsigned => 0
  | .signed =>
    if Nat.beq it.bitWidth 0 then 0
    else Neg.neg (Int.ofNat (Nat.pow 2 (it.bitWidth - 1)))

/-- Exclusive upper bound on mathematical integers representable by `it`
(`2^bits` for unsigned, `2^(bits - 1)` for signed). -/
def IntType.boundVal (it : IntType) : Int :=
  match it.signed with
  | .unsigned => Int.ofNat (Nat.pow 2 it.bitWidth)
  | .signed =>
    if Nat.beq it.bitWidth 0 then 0
    else Int.ofNat (Nat.pow 2 (it.bitWidth - 1))

/-- Check whether mathematical integer `i` lies in the representable range of
`it` (`spec/lang/types.md`: `IntType::can_represent`). -/
def IntType.canRepresent (it : IntType) (i : Int) : Bool :=
  decide (it.minVal ≤ i) && decide (i < it.boundVal)

/-- Euclidean remainder modulo positive `m` (`m > 0`). -/
def intEmodNat (i : Int) (m : Nat) : Nat :=
  match i with
  | .ofNat n => Nat.mod n m
  | .negSucc n =>
    let r := Nat.mod (Nat.succ n) m
    if Nat.beq r 0 then 0 else m - r

/-- Wrap mathematical integer `i` into the representable range of `it` modulo
`2^it.bitWidth` (`spec/lang/types.md`: `IntType::bring_in_bounds`). -/
def IntType.bringInBounds (it : IntType) (i : Int) : Int :=
  let modulus := Nat.pow 2 it.bitWidth
  let u := intEmodNat i modulus
  match it.signed with
  | .unsigned => Int.ofNat u
  | .signed =>
    if Nat.beq it.bitWidth 0 then 0
    else
      let half := Nat.pow 2 (it.bitWidth - 1)
      if Nat.blt u half then Int.ofNat u
      else Int.ofNat u - Int.ofNat modulus

/-- Standard integer types on 64-bit targets. -/
def u8Ty : IntType := ⟨.unsigned, ⟨1⟩⟩
def i8Ty : IntType := ⟨.signed, ⟨1⟩⟩
def u16Ty : IntType := ⟨.unsigned, ⟨2⟩⟩
def i16Ty : IntType := ⟨.signed, ⟨2⟩⟩
def u32Ty : IntType := ⟨.unsigned, ⟨4⟩⟩
def i32Ty : IntType := ⟨.signed, ⟨4⟩⟩
def u64Ty : IntType := ⟨.unsigned, ⟨8⟩⟩
def i64Ty : IntType := ⟨.signed, ⟨8⟩⟩
def u128Ty : IntType := ⟨.unsigned, ⟨16⟩⟩
def i128Ty : IntType := ⟨.signed, ⟨16⟩⟩
def usizeTy : IntType := u64Ty
def isizeTy : IntType := i64Ty

/-- Tag-byte write emitted when encoding an enum variant
(`spec/lang/types.md`: `Variant.tagger`). -/
structure TagWrite where
  offset : Nat
  intTy : IntType
  val : Int

/-- Explicit structural equality on `TagWrite`. -/
def TagWrite.beq (a b : TagWrite) : Bool :=
  Nat.beq a.offset b.offset && IntType.beq a.intTy b.intTy && (a.val == b.val)

/-- Structural equality on `List TagWrite`. -/
def tagWriteListBeq : List TagWrite → List TagWrite → Bool
  | [], [] => true
  | x :: xs, y :: ys => TagWrite.beq x y && tagWriteListBeq xs ys
  | _, _ => false

mutual
  /-- Decision tree decoding an enum's discriminant from memory bytes
  (`spec/lang/types.md`: `pub enum Discriminator`). -/
  inductive Discriminator where
    | known (val : Int)
    | invalid
    | branch (offset : Nat) (valueType : IntType)
        (children : DiscrBranches) (fallback : Discriminator)

  /-- Range-keyed branches `[lo, hi) ↦ child` of `Discriminator.branch`. -/
  inductive DiscrBranches where
    | nil
    | cons (lo hi : Int) (child : Discriminator) (rest : DiscrBranches)
end

mutual
  /-- Explicit structural equality on `Discriminator`. -/
  def Discriminator.beq : Discriminator → Discriminator → Bool
    | .known a, .known b => a == b
    | .invalid, .invalid => true
    | .branch o₁ t₁ c₁ f₁, .branch o₂ t₂ c₂ f₂ =>
      Nat.beq o₁ o₂ && IntType.beq t₁ t₂ &&
        DiscrBranches.beq c₁ c₂ && Discriminator.beq f₁ f₂
    | _, _ => false

  /-- Explicit structural equality on `DiscrBranches`. -/
  def DiscrBranches.beq : DiscrBranches → DiscrBranches → Bool
    | .nil, .nil => true
    | .cons lo₁ hi₁ c₁ r₁, .cons lo₂ hi₂ c₂ r₂ =>
      (lo₁ == lo₂) && (hi₁ == hi₂) &&
        Discriminator.beq c₁ c₂ && DiscrBranches.beq r₁ r₂
    | _, _ => false
end

mutual
  /-- MiniRust type descriptors (`spec/lang/types.md`: `pub enum Type`).
  Rust `char` is lowered to `MrType.int u32Ty` in `Translate.lean`, matching
  upstream MiniRust (`tooling/minimize`). -/
  inductive MrType where
    | int (intTy : IntType)
    | bool
    | tuple (fields : TupleFields) (size : Size) (align : Align)
    | array (elem : MrType) (count : Nat)
    | enum (variants : EnumVariants) (discriminator : Discriminator)
        (discriminantTy : IntType) (size : Size) (align : Align)

  /-- Sized tuple field list `(offset, ty)` (`spec/lang/types.md`). -/
  inductive TupleFields where
    | nil
    | cons (offset : Nat) (ty : MrType) (rest : TupleFields)

  /-- Enum variant table `(discriminant, dataTy, tagger)`. -/
  inductive EnumVariants where
    | nil
    | cons (discriminant : Int) (ty : MrType) (tagger : List TagWrite)
        (rest : EnumVariants)
end

mutual
  /-- Explicit structural equality on `MrType`. -/
  def MrType.beq : MrType → MrType → Bool
    | .int a, .int b => IntType.beq a b
    | .bool, .bool => true
    | .tuple f₁ s₁ a₁, .tuple f₂ s₂ a₂ =>
      TupleFields.beq f₁ f₂ && Size.beq s₁ s₂ && Align.beq a₁ a₂
    | .array e₁ n₁, .array e₂ n₂ => MrType.beq e₁ e₂ && Nat.beq n₁ n₂
    | .enum v₁ d₁ dt₁ s₁ a₁, .enum v₂ d₂ dt₂ s₂ a₂ =>
      EnumVariants.beq v₁ v₂ && Discriminator.beq d₁ d₂ &&
        IntType.beq dt₁ dt₂ && Size.beq s₁ s₂ && Align.beq a₁ a₂
    | _, _ => false

  /-- Explicit structural equality on `TupleFields`. -/
  def TupleFields.beq : TupleFields → TupleFields → Bool
    | .nil, .nil => true
    | .cons o₁ t₁ r₁, .cons o₂ t₂ r₂ =>
      Nat.beq o₁ o₂ && MrType.beq t₁ t₂ && TupleFields.beq r₁ r₂
    | _, _ => false

  /-- Explicit structural equality on `EnumVariants`. -/
  def EnumVariants.beq : EnumVariants → EnumVariants → Bool
    | .nil, .nil => true
    | .cons d₁ t₁ g₁ r₁, .cons d₂ t₂ g₂ r₂ =>
      (d₁ == d₂) && MrType.beq t₁ t₂ && tagWriteListBeq g₁ g₂ &&
        EnumVariants.beq r₁ r₂
    | _, _ => false
end

/-- Size in bytes of a sized `MrType` (`spec/lang/types.md`: `Type::layout`). -/
def MrType.size : MrType → Size
  | .int it => it.size
  | .bool => ⟨1⟩
  | .tuple _ s _ => s
  | .array elem count => ⟨elem.size.bytes * count⟩
  | .enum _ _ _ s _ => s

/-- Alignment in bytes of a sized `MrType` (`spec/lang/types.md`: `Type::align`;
64-bit `INT_MAX_ALIGN = 16`, so every integer width `<= 16` aligns to its byte
size). -/
def MrType.align : MrType → Align
  | .int it => ⟨it.size.bytes⟩
  | .bool => ⟨1⟩
  | .tuple _ _ a => a
  | .array elem _ => elem.align
  | .enum _ _ _ _ a => a

/-- Number of fields in `TupleFields`. -/
def TupleFields.length : TupleFields → Nat
  | .nil => 0
  | .cons _ _ rest => rest.length + 1

/-- Lookup field `idx` in `TupleFields`. -/
def TupleFields.get? : TupleFields → Nat → Option (Nat × MrType)
  | .nil, _ => none
  | .cons off ty _, 0 => some (off, ty)
  | .cons _ _ rest, n + 1 => rest.get? n

/-- Lookup variant by discriminant value in `EnumVariants`. -/
def EnumVariants.find? (discr : Int) :
    EnumVariants → Option (MrType × List TagWrite)
  | .nil => none
  | .cons d ty tagger rest =>
    if d == discr then some (ty, tagger) else rest.find? discr

/-- MiniRust unit type `()` (`spec/lang/types.md`: `unit_ty`). -/
def unitTy : MrType :=
  .tuple .nil ⟨0⟩ ⟨1⟩

/-- Empty payload type of byte size `n` and alignment `a` (all padding bytes),
used as the variant payload of fieldless enums. -/
def emptySizedTy (sz al : Nat) : MrType :=
  .tuple .nil ⟨sz⟩ ⟨al⟩

/-- MiniRust overflow pair type `(T, bool)` matching
`spec/lang/types.md`: `IntType::with_overflow`. -/
def IntType.withOverflow (it : IntType) : MrType :=
  .tuple
    (.cons 0 (.int it) (.cons it.size.bytes .bool .nil))
    ⟨2 * it.size.bytes⟩
    ⟨it.size.bytes⟩

/-- MiniRust representation of `core::cmp::Ordering` (`#[repr(i8)]`:
`Less = -1`, `Equal = 0`, `Greater = 1`). -/
def orderingTy : MrType :=
  let payload := emptySizedTy 1 1
  let lessVal : Int := Neg.neg 1
  let eqVal : Int := 0
  let gtVal : Int := 1
  let variants : EnumVariants :=
    .cons lessVal payload [⟨0, i8Ty, lessVal⟩]
      (.cons eqVal payload [⟨0, i8Ty, eqVal⟩]
        (.cons gtVal payload [⟨0, i8Ty, gtVal⟩] .nil))
  let discr : Discriminator :=
    .branch 0 i8Ty
      (.cons lessVal eqVal (.known lessVal)
        (.cons eqVal gtVal (.known eqVal)
          (.cons gtVal 2 (.known gtVal) .nil)))
      .invalid
  .enum variants discr i8Ty ⟨1⟩ ⟨1⟩

/-- MiniRust uninhabited `!` type (0-variant enum, 0 bytes, align 1). -/
def neverTy : MrType :=
  .enum .nil .invalid i8Ty ⟨0⟩ ⟨1⟩

/-- Abstract byte in MiniRust memory (`spec/mem/prelude.md`: `AbstractByte`). -/
inductive AbstractByte where
  | uninit
  | init (byte : UInt8)

/-- Explicit structural equality on `AbstractByte`. -/
def AbstractByte.beq : AbstractByte → AbstractByte → Bool
  | .uninit, .uninit => true
  | .init a, .init b => a == b
  | _, _ => false

mutual
  /-- MiniRust runtime values (`spec/lang/values.md`: `enum Value`). -/
  inductive MrValue where
    | int (val : Int)
    | bool (val : Bool)
    | tuple (fields : MrValueList)
    | variant (discriminant : Int) (data : MrValue)

  /-- Value list for `MrValue.tuple`. -/
  inductive MrValueList where
    | nil
    | cons (head : MrValue) (tail : MrValueList)
end

/-- Unit value `Value::Tuple([])`. -/
def unitValue : MrValue :=
  .tuple .nil

/-- Length of `MrValueList`. -/
def MrValueList.length : MrValueList → Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1

/-- Constant literals (`spec/lang/syntax.md`: `enum Constant`). -/
inductive MrConstant where
  | int (val : Int)
  | bool (val : Bool)

/-- Integer unary operators (`spec/lang/syntax.md`: `IntUnOp`). -/
inductive IntUnOp where
  | neg
  | bitNot
  | countOnes

/-- Cast operators (`spec/lang/syntax.md`: `CastOp`). -/
inductive CastOp where
  | intToInt (intTy : IntType)
  | transmute (newTy : MrType)

/-- Unary operators (`spec/lang/syntax.md`: `UnOp`). -/
inductive MrUnOp where
  | int (op : IntUnOp)
  | cast (op : CastOp)

/-- Integer binary operators (`spec/lang/syntax.md`: `IntBinOp`). -/
inductive IntBinOp where
  | add | addUnchecked
  | sub | subUnchecked
  | mul | mulUnchecked
  | div | divExact | rem
  | shl | shlUnchecked | shr | shrUnchecked
  | bitAnd | bitOr | bitXor

/-- Overflowing integer binary operators (`spec/lang/syntax.md`:
`IntBinOpWithOverflow`). -/
inductive IntBinOpWithOverflow where
  | add | sub | mul

/-- Relational comparison operators (`spec/lang/syntax.md`: `RelOp`). -/
inductive RelOp where
  | lt | gt | le | ge | eq | ne | cmp

/-- Binary operators (`spec/lang/syntax.md`: `BinOp`). -/
inductive MrBinOp where
  | int (op : IntBinOp)
  | intWithOverflow (op : IntBinOpWithOverflow)
  | rel (op : RelOp)

mutual
  /-- Place expressions (`spec/lang/syntax.md`: `PlaceExpr`). -/
  inductive PlaceExpr where
    | local (name : LocalName)
    | field (root : PlaceExpr) (fieldIdx : Nat)
    | index (root : PlaceExpr) (idx : ValueExpr)
    | downcast (root : PlaceExpr) (discriminant : Int)

  /-- Value expressions (`spec/lang/syntax.md`: `ValueExpr`). -/
  inductive ValueExpr where
    | constant (c : MrConstant) (ty : MrType)
    | tuple (exprs : ValueExprList) (ty : MrType)
    | variant (discriminant : Int) (data : ValueExpr) (enumTy : MrType)
    | getDiscriminant (place : PlaceExpr)
    | load (source : PlaceExpr)
    | unOp (operator : MrUnOp) (operand : ValueExpr)
    | binOp (operator : MrBinOp) (left right : ValueExpr)

  /-- Expression list for `ValueExpr.tuple`. -/
  inductive ValueExprList where
    | nil
    | cons (head : ValueExpr) (tail : ValueExprList)
end

/-- MiniRust basic-block statements (`spec/lang/syntax.md`: `Statement`). -/
inductive MrStatement where
  | assign (destination : PlaceExpr) (source : ValueExpr)
  | placeMention (place : PlaceExpr)
  | setDiscriminant (destination : PlaceExpr) (value : Int)
  | deinit (place : PlaceExpr)
  | storageLive (localId : LocalName)
  | storageDead (localId : LocalName)

/-- MiniRust basic-block terminators (`spec/lang/syntax.md`: `Terminator`),
plus `exitWith` as an explicit non-upstream harness observation terminator used
solely in the synthesized 0-arg, 1-ZST `start` wrapper function to read the
entry function's returned value slot on halt (where upstream `IntrinsicOp::Exit`
halts without returning a value). -/
inductive MrTerminator where
  | goto (target : BbName)
  | switch (value : ValueExpr) (cases : List (Int × BbName))
      (fallback : BbName)
  | unreachable
  | return_
  | exitWith (retLocal : LocalName)

/-- MiniRust basic block (`spec/lang/syntax.md`: `BasicBlock`). -/
structure MrBasicBlock where
  statements : List MrStatement
  terminator : MrTerminator

/-- MiniRust function definition (`spec/lang/syntax.md`: `Function`). -/
structure MrFunction where
  locals : List MrType
  args : List LocalName
  ret : LocalName
  blocks : List MrBasicBlock
  start : BbName

/-- MiniRust program (`spec/lang/syntax.md`: `Program`). -/
structure MrProgram where
  functions : List MrFunction
  start : FnName

end Anneal.MiniRust
