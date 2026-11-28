-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:refinement
module
prelude
public import Init.NotationExtra
public import Init.Data.List.Basic
public import Init.Data.Int.Basic

@[expose] public section

namespace Trusted.CppAst

/-!
# Anneal Rung-0 C11 / Rung-1 C++20 Abstract Syntax (`Trusted.CppAst`)

Tactic-free Ring-0 basic-block CFG representation for C11 functions lowered
from Clang ASTs under SSENF (Single-Side-Effect Normal Form). Every recursive
or helper value definition carries `noncomputable` so Lean 4 emits zero
`._unsafe_rec` or `partial` auxiliary constants.
-/

/-- Fixed-width integer widths admitted by Rung-0 C11 (`8`..`128` bits). -/
inductive CppIntWidth where
  | w8 | w16 | w32 | w64 | w128

/-- Signedness of a C11 integer type (`signed` vs. `unsigned`). -/
inductive Signedness where
  | signed | unsigned

/-- Signed integer overflow policy:
- `isoUB`: ISO C11 §6.5p5 (signed overflow is Undefined Behavior).
- `wrapv`: `-fwrapv` (signed `add`/`sub`/`mul`/`neg` wrap mod 2^W; division by
  zero, `INT_MIN / -1`, and out-of-range shift counts remain Undefined
  Behavior). Under both modes a signed left shift of a negative value or into
  the sign bit is `.unsupported`: undefined in ISO C11 §6.5.7p4, defined in
  C++20. -/
inductive SignedOverflowMode where
  | isoUB
  | wrapv

/-- Translation-unit C11 language policy captured alongside the lowered CFG. -/
structure CppLangPolicy where
  pointerWidthBits : Nat
  charIsSigned     : Bool
  strictAliasing   : Bool
  signedOverflow   : SignedOverflowMode
  exceptionsOff    : Bool
  /-- Byte and bit-field order; only little-endian targets are admitted. -/
  littleEndian     : Bool := true

/-- Calling-convention ABI kind for C/C++ functions. -/
inductive CppAbiKind where
  | c
  | cxxItanium

/-- Structural C11 type descriptors carried directly by value in
`Trusted.CppAst`. `isCharLike` marks `char`/`signed char`/`unsigned char` and
`mayAlias` marks `__attribute__((may_alias))` pointers. Both are reserved for
type-based alias analysis: the semantics admits only programs compiled without
strict aliasing, so neither affects execution yet. `isRestrict` marks
`restrict`-qualified pointers, which are not admitted. -/
inductive CppTy where
  | void
  | bool
  | int (width : CppIntWidth) (sign : Signedness) (isCharLike : Bool)
  | ptr (pointee : CppTy) (isConst : Bool) (isRestrict : Bool) (mayAlias : Bool)
  | array (elem : CppTy) (len : Nat)
  | record (recordId : String)

/-- Field descriptor inside a C11 `struct` or `union` record definition.
Fields are addressed by index (`CppProjElem.field`). `name` is empty exactly
for unnamed bit-fields, whose bits are padding (C11 §6.7.2.1p12). -/
structure CppFieldDecl where
  name       : String
  offsetBits : Nat
  bitWidth   : Option Nat
  ty         : CppTy

/-- Layout-pinned C11 `struct` or `union` record definition. -/
structure CppRecordDef where
  recordId   : String
  isUnion    : Bool
  sizeBytes  : Nat
  alignBytes : Nat
  fields     : List CppFieldDecl

/-- Local variable slot index (`0` = return slot, `1..=K` = parameters). -/
abbrev LocalId := Nat

/-- Basic-block index inside a `CppBody`. -/
abbrev BlockId := Nat

/-- Projection step applied to a base local to form a `CppPlace`. -/
inductive CppProjElem where
  | deref
  | field (recordId : String) (fieldIdx : Nat) (fieldTy : CppTy)
  | index (elemTy : CppTy) (idxLocal : LocalId)
  /-- C/C++ bit-field member (only legal as the last projection). `offsetBits`
  is relative to the start of the enclosing `recordId` object. -/
  | bitfield (recordId : String) (fieldIdx : Nat) (offsetBits : Nat)
             (bitWidth : Nat) (isSigned : Bool)

/-- Memory or local place formed by a base `LocalId` and projection chain. -/
structure CppPlace where
  base  : LocalId
  projs : List CppProjElem

/-- Pure C11 unary operators (side-effect-free after SSENF lowering). -/
inductive CppUnOp where
  | neg
  | bitNot
  | logNot

/-- Pure C11 binary operators (short-circuiting lowered to CFG branches). -/
inductive CppBinOp where
  | add | sub | mul | div | rem
  | shl | shr
  | bitAnd | bitOr | bitXor
  | eq | ne | lt | le | gt | ge

/-- Side-effect-free C11 expressions inside SSENF basic blocks. -/
inductive CppExpr where
  | constInt (width : CppIntWidth) (sign : Signedness) (isCharLike : Bool)
             (val : Int)
  | constBool (val : Bool)
  | nullPtr (ty : CppTy)
  | readPlace (place : CppPlace) (ty : CppTy)
  | addrOf (place : CppPlace) (ptrTy : CppTy)
  | unary (op : CppUnOp) (ty : CppTy) (arg : CppExpr)
  | binary (op : CppBinOp) (resTy : CppTy) (lhs : CppExpr) (rhs : CppExpr)
  | intCast (fromWidth : CppIntWidth) (fromSign : Signedness)
            (toWidth : CppIntWidth) (toSign : Signedness) (toCharLike : Bool)
            (arg : CppExpr)
  | intToBool (arg : CppExpr)
  | boolToInt (width : CppIntWidth) (sign : Signedness) (arg : CppExpr)
  | ptrAdd (elemTy : CppTy) (ptrTy : CppTy) (base : CppExpr) (offset : CppExpr)
  | ptrCast (toPtrTy : CppTy) (arg : CppExpr)
  /-- C++20 `__builtin_bit_cast` (`std::bit_cast`): reinterpret the object
  representation of `arg : fromTy` as `toTy` (equal sizes). -/
  | bitCast (fromTy : CppTy) (toTy : CppTy) (arg : CppExpr)

/-- Single-effect C11 basic-block statement. -/
inductive CppStmt where
  | storageLive (localId : LocalId)
  | storageDead (localId : LocalId)
  | assign (dst : CppPlace) (dstTy : CppTy) (rhs : CppExpr)
  /-- C++ zero-initialization of `dst` (every byte, padding included, is 0). -/
  | zeroInit (dst : CppPlace) (ty : CppTy)

/-- Explicit basic-block CFG terminator (zero hidden control flow in exprs). -/
inductive CppTerminator where
  | goto (target : BlockId)
  | branch (cond : CppExpr) (thenTarget : BlockId) (elseTarget : BlockId)
  | call (callee : String) (args : List CppExpr)
         (dst : Option (CppPlace × CppTy)) (next : BlockId)
  | ret
  | unreachable

/-- Basic block containing straight-line statements and one terminator. -/
structure CppBlock where
  stmts : List CppStmt
  term  : CppTerminator

/-- Local variable declaration inside a `CppBody`. -/
structure CppLocalDecl where
  ty      : CppTy
  isParam : Bool
  /-- The local is a `const`-qualified object; modifying it after its
  initialization is undefined (C11 §6.7.3p6, C++20 [dcl.type.cv]p4). -/
  isConst : Bool := false

/-- Function ABI and type signature. -/
structure CppSignature where
  abi    : CppAbiKind
  params : List CppTy
  ret    : CppTy
  /-- `paramNonNull[i]`: parameter `i` is a C++ reference (`T&`, `T&&`) lowered
  to a pointer that must be non-null with provenance. Missing entries are
  `false`. -/
  paramNonNull : List Bool := []

/-- Lowered C11 function body or external declaration. -/
structure CppBody where
  identity   : String
  isExternal : Bool
  sig        : CppSignature
  locals     : List CppLocalDecl
  blocks     : List CppBlock
  entryBlock : BlockId

/-- Complete or partial lowered C11 translation unit program. -/
structure CppProgram where
  policy     : CppLangPolicy
  isPartial  : Bool
  records    : List CppRecordDef
  bodies     : List CppBody
  entryDefId : Nat

namespace CppIntWidth

/-- Byte size of a fixed-width integer (`1`, `2`, `4`, `8`, or `16`). -/
noncomputable def byteSize : CppIntWidth → Nat
  | .w8   => 1
  | .w16  => 2
  | .w32  => 4
  | .w64  => 8
  | .w128 => 16

/-- Bit width of a fixed-width integer (`8`, `16`, `32`, `64`, or `128`). -/
noncomputable def bitWidth (w : CppIntWidth) : Nat :=
  w.byteSize * 8

/-- Structural equality on `CppIntWidth`. -/
noncomputable def beq : CppIntWidth → CppIntWidth → Bool
  | .w8,   .w8   => true
  | .w16,  .w16  => true
  | .w32,  .w32  => true
  | .w64,  .w64  => true
  | .w128, .w128 => true
  | _,     _     => false

end CppIntWidth

/-- Structural equality on `Signedness`. -/
noncomputable def Signedness.beq : Signedness → Signedness → Bool
  | .signed,   .signed   => true
  | .unsigned, .unsigned => true
  | _,         _         => false

/-- Structural equality on `SignedOverflowMode`. -/
noncomputable def SignedOverflowMode.beq :
    SignedOverflowMode → SignedOverflowMode → Bool
  | .isoUB, .isoUB => true
  | .wrapv, .wrapv => true
  | _,      _      => false

/-- Structural equality on `CppLangPolicy`. -/
noncomputable def CppLangPolicy.beq (a b : CppLangPolicy) : Bool :=
  Nat.beq a.pointerWidthBits b.pointerWidthBits &&
    (a.charIsSigned == b.charIsSigned) &&
    (a.strictAliasing == b.strictAliasing) &&
    SignedOverflowMode.beq a.signedOverflow b.signedOverflow &&
    (a.exceptionsOff == b.exceptionsOff) &&
    (a.littleEndian == b.littleEndian)

/-- Structural equality on `CppAbiKind`. -/
noncomputable def CppAbiKind.beq : CppAbiKind → CppAbiKind → Bool
  | .c,          .c          => true
  | .cxxItanium, .cxxItanium => true
  | _,           _           => false

/-- Structural equality on `CppTy`. -/
noncomputable def CppTy.beq : CppTy → CppTy → Bool
  | .void, .void => true
  | .bool, .bool => true
  | .int w1 s1 c1, .int w2 s2 c2 =>
    CppIntWidth.beq w1 w2 && Signedness.beq s1 s2 && (c1 == c2)
  | .ptr p1 c1 r1 m1, .ptr p2 c2 r2 m2 =>
    CppTy.beq p1 p2 && (c1 == c2) && (r1 == r2) && (m1 == m2)
  | .array e1 n1, .array e2 n2 =>
    Nat.beq n1 n2 && CppTy.beq e1 e2
  | .record id1, .record id2 => id1 == id2
  | _, _ => false

/-- Elementwise structural equality on `List CppTy`. -/
noncomputable def CppTy.beqList : List CppTy → List CppTy → Bool
  | [], [] => true
  | x :: xs, y :: ys => CppTy.beq x y && CppTy.beqList xs ys
  | _, _ => false

/-- Structural equality on `Option Nat`. -/
noncomputable def optNatBeq : Option Nat → Option Nat → Bool
  | none,   none   => true
  | some a, some b => Nat.beq a b
  | _,      _      => false

/-- Structural equality on `CppFieldDecl`. -/
noncomputable def CppFieldDecl.beq (a b : CppFieldDecl) : Bool :=
  (a.name == b.name) && Nat.beq a.offsetBits b.offsetBits &&
    optNatBeq a.bitWidth b.bitWidth && CppTy.beq a.ty b.ty

/-- Elementwise structural equality on `List CppFieldDecl`. -/
noncomputable def CppFieldDecl.beqList :
    List CppFieldDecl → List CppFieldDecl → Bool
  | [], [] => true
  | x :: xs, y :: ys => CppFieldDecl.beq x y && CppFieldDecl.beqList xs ys
  | _, _ => false

/-- Structural equality on `CppRecordDef`. -/
noncomputable def CppRecordDef.beq (a b : CppRecordDef) : Bool :=
  (a.recordId == b.recordId) && (a.isUnion == b.isUnion) &&
    Nat.beq a.sizeBytes b.sizeBytes && Nat.beq a.alignBytes b.alignBytes &&
    CppFieldDecl.beqList a.fields b.fields

/-- Elementwise structural equality on `List CppRecordDef`. -/
noncomputable def CppRecordDef.beqList :
    List CppRecordDef → List CppRecordDef → Bool
  | [], [] => true
  | x :: xs, y :: ys => CppRecordDef.beq x y && CppRecordDef.beqList xs ys
  | _, _ => false

/-- `true` iff no pointer type inside `ty` is `restrict`-qualified. -/
noncomputable def CppTy.noRestrict : CppTy → Bool
  | .ptr p _ r _ => !r && CppTy.noRestrict p
  | .array e _   => CppTy.noRestrict e
  | _            => true

/-- `true` iff no type in `tys` contains a `restrict`-qualified pointer. -/
noncomputable def CppTy.noRestrictList : List CppTy → Bool
  | [] => true
  | t :: ts => CppTy.noRestrict t && CppTy.noRestrictList ts

/-- Structural equality on `CppSignature`. -/
noncomputable def CppSignature.beq (a b : CppSignature) : Bool :=
  CppAbiKind.beq a.abi b.abi &&
    CppTy.beqList a.params b.params &&
    CppTy.beq a.ret b.ret &&
    (a.paramNonNull == b.paramNonNull)

end Trusted.CppAst

end
