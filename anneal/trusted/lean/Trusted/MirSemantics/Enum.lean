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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Ops

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Enum Admission and Value Validation (`Trusted.MirSemantics.Enum`)

Fieldless-enum discriminant rules, value well-formedness (`Val.ty?`,
`checkVal`, `checkArgsMatch`), ZST slot initialization (`liveUninitSlot`), and
pure list/string uniqueness helpers for $M_{\text{anneal}}$.
-/

/-- Check that `x` does not occur in `ys`. -/
noncomputable def natNotElem (x : Nat) : List Nat → Bool
  | [] => true
  | y :: ys => !Nat.beq x y && natNotElem x ys

/-- Check that all elements of a `List Nat` are pairwise distinct. -/
noncomputable def natListPairwiseNe : List Nat → Bool
  | [] => true
  | x :: xs => natNotElem x xs && natListPairwiseNe xs

/-- Pure structural UTF-8 byte equality on `String`, defined over the locked
foundation primitives (`String.toByteArray`, `Array.toList`, and `List.beq`
over `UInt8`) without expanding `foundation-lock.json` to import
`Init.Data.String.Basic` (`String.decEq`). -/
noncomputable def stringBeq (a b : String) : Bool :=
  List.beq a.toByteArray.data.toList b.toByteArray.data.toList

/-- Check whether `s` has no UTF-8 bytes without comparing against `""`. -/
noncomputable def stringIsEmpty (s : String) : Bool :=
  s.toByteArray.data.toList.isEmpty

/-- Three-way comparison outcome for balanced-tree key ordering. -/
inductive ByteCmp where
  | lt
  | eq
  | gt

/-- Compare two `UInt8` bytes without requiring `Decidable` instances outside
the locked foundation imports. -/
noncomputable def byteCmp (x y : UInt8) : ByteCmp :=
  if Nat.blt x.toNat y.toNat then .lt
  else if Nat.blt y.toNat x.toNat then .gt
  else .eq

/-- Lexicographic byte-list comparison (`ByteCmp`). -/
noncomputable def byteListCmp : List UInt8 → List UInt8 → ByteCmp
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match byteCmp x y with
    | .lt => .lt
    | .gt => .gt
    | .eq => byteListCmp xs ys

/-- Compare two byte lists 8 bytes per recursive call so long equal-prefix
identities stay shallow under `maxRecDepth`. -/
noncomputable def byteListCmp8 : List UInt8 → List UInt8 → ByteCmp
  | a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: as,
    b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: bs =>
    match byteCmp a1 b1 with
    | .lt => .lt | .gt => .gt | .eq =>
      match byteCmp a2 b2 with
      | .lt => .lt | .gt => .gt | .eq =>
        match byteCmp a3 b3 with
        | .lt => .lt | .gt => .gt | .eq =>
          match byteCmp a4 b4 with
          | .lt => .lt | .gt => .gt | .eq =>
            match byteCmp a5 b5 with
            | .lt => .lt | .gt => .gt | .eq =>
              match byteCmp a6 b6 with
              | .lt => .lt | .gt => .gt | .eq =>
                match byteCmp a7 b7 with
                | .lt => .lt | .gt => .gt | .eq =>
                  match byteCmp a8 b8 with
                  | .lt => .lt | .gt => .gt | .eq => byteListCmp8 as bs
  | xs, ys => byteListCmp xs ys

/-- Deterministic position-weighted byte checksum over `List UInt8` (unrolled
4 bytes per step). Used purely as a fast comparison pre-key in `IdentityKey`;
any checksum collision falls back to exact `byteListCmp8` comparison. -/
noncomputable def byteListTag (w sum : Nat) : List UInt8 → Nat
  | a1 :: a2 :: a3 :: a4 :: rest =>
    byteListTag (w + 4)
      (sum + w * a1.toNat + (w + 1) * a2.toNat +
        (w + 2) * a3.toNat + (w + 3) * a4.toNat)
      rest
  | a1 :: rest => byteListTag (w + 1) (sum + w * a1.toNat) rest
  | [] => sum

/-- Total comparison key pairing a deterministic checksum tag with the exact
UTF-8 byte sequence. For keys built by `identityKey?` (where
`tag = byteListTag 1 0 bytes`), `k1.bytes = k2.bytes ↔ identityKeyCmp k1 k2 =
.eq`. -/
structure IdentityKey where
  tag : Nat
  bytes : List UInt8

/-- Strict total order comparison over `IdentityKey`: compares `tag` first in
$O(1)$ (`Nat.blt`) and falls back to exact `byteListCmp8` when tags match. -/
noncomputable def identityKeyCmp (a b : IdentityKey) : ByteCmp :=
  if Nat.blt a.tag b.tag then .lt
  else if Nat.blt b.tag a.tag then .gt
  else byteListCmp8 a.bytes b.bytes

/-- Build the canonical `IdentityKey` for a non-empty `identity` string
(`none` on empty string). -/
noncomputable def identityKey? (identity : String) : Option IdentityKey :=
  match identity.toByteArray.data.toList with
  | [] => none
  | bs => some ⟨byteListTag 1 0 bs, bs⟩

/-- Red-Black tree node color for balanced $O(N \log N)$ identity indexing and
uniqueness checking. -/
inductive IdentityRbColor where
  | red
  | black

/-- Balanced Red-Black tree keyed by non-empty `IdentityKey`s with payload
type `α` for $O(\log N)$ uniqueness checking and lookup. -/
inductive IdentityRbTree (α : Type) where
  | empty
  | node :
      IdentityRbColor → IdentityRbTree α → IdentityKey → α →
        IdentityRbTree α → IdentityRbTree α

/-- Okasaki Red-Black rebalance step preserving in-order key sequence. -/
noncomputable def identityRbBalance {α : Type} :
    IdentityRbColor → IdentityRbTree α → IdentityKey → α →
      IdentityRbTree α → IdentityRbTree α
  | .black, .node .red (.node .red a x xv b) y yv c, z, zv, d =>
    .node .red (.node .black a x xv b) y yv (.node .black c z zv d)
  | .black, .node .red a x xv (.node .red b y yv c), z, zv, d =>
    .node .red (.node .black a x xv b) y yv (.node .black c z zv d)
  | .black, a, x, xv, .node .red (.node .red b y yv c) z zv d =>
    .node .red (.node .black a x xv b) y yv (.node .black c z zv d)
  | .black, a, x, xv, .node .red b y yv (.node .red c z zv d) =>
    .node .red (.node .black a x xv b) y yv (.node .black c z zv d)
  | c, a, x, xv, b => .node c a x xv b

/-- Insert `(k, v)` into `t`, returning `none` if an equal key is already
present. -/
noncomputable def identityRbInsertAux {α : Type} (k : IdentityKey) (v : α) :
    IdentityRbTree α → Option (IdentityRbTree α)
  | .empty => some (.node .red .empty k v .empty)
  | .node c l x xv r =>
    match identityKeyCmp k x with
    | .lt =>
      match identityRbInsertAux k v l with
      | none => none
      | some l' => some (identityRbBalance c l' x xv r)
    | .eq => none
    | .gt =>
      match identityRbInsertAux k v r with
      | none => none
      | some r' => some (identityRbBalance c l x xv r')

/-- Balanced insert returning `none` on collision and recoloring the root
black. -/
noncomputable def identityRbInsert {α : Type} (k : IdentityKey) (v : α)
    (t : IdentityRbTree α) : Option (IdentityRbTree α) :=
  match identityRbInsertAux k v t with
  | none => none
  | some .empty => some .empty
  | some (.node _ l x xv r) => some (.node .black l x xv r)

/-- Insert `(identity, v)` into `t`, returning `none` if `identity` is empty
or already present in `t`. -/
noncomputable def identityRbInsertByKey {α : Type} (identity : String)
    (v : α) (t : IdentityRbTree α) : Option (IdentityRbTree α) :=
  match identityKey? identity with
  | none => none
  | some k => identityRbInsert k v t

/-- Bind helper over `Option (IdentityRbTree α)` for chaining insertions. -/
noncomputable def identityRbInsertByKeyOpt {α : Type} (identity : String)
    (v : α) : Option (IdentityRbTree α) → Option (IdentityRbTree α)
  | none => none
  | some t => identityRbInsertByKey identity v t

/-- Single-pass balanced-tree builder unrolled 4 entries per recursive step so
crates with hundreds of items remain well within Lean's default
`maxRecDepth`, returning `none` if any `keyOf item` is empty or duplicated. -/
noncomputable def identityRbBuildAux {α β : Type} (keyOf : β → String)
    (valOf : β → α) : List β → IdentityRbTree α → Option (IdentityRbTree α)
  | [], t => some t
  | [x1], t => identityRbInsertByKey (keyOf x1) (valOf x1) t
  | [x1, x2], t =>
    identityRbInsertByKeyOpt (keyOf x2) (valOf x2)
      (identityRbInsertByKey (keyOf x1) (valOf x1) t)
  | [x1, x2, x3], t =>
    identityRbInsertByKeyOpt (keyOf x3) (valOf x3)
      (identityRbInsertByKeyOpt (keyOf x2) (valOf x2)
        (identityRbInsertByKey (keyOf x1) (valOf x1) t))
  | x1 :: x2 :: x3 :: x4 :: rest, t =>
    match identityRbInsertByKeyOpt (keyOf x4) (valOf x4)
        (identityRbInsertByKeyOpt (keyOf x3) (valOf x3)
          (identityRbInsertByKeyOpt (keyOf x2) (valOf x2)
            (identityRbInsertByKey (keyOf x1) (valOf x1) t))) with
    | none => none
    | some t' => identityRbBuildAux keyOf valOf rest t'

/-- Look up `k` inside an `IdentityRbTree α`. -/
noncomputable def identityRbLookupAux {α : Type} (k : IdentityKey) :
    IdentityRbTree α → Option α
  | .empty => none
  | .node _ l x v r =>
    match identityKeyCmp k x with
    | .lt => identityRbLookupAux k l
    | .eq => some v
    | .gt => identityRbLookupAux k r

/-- Look up the unique payload for `identity` in `t` in $O(\log N)$
comparisons. -/
noncomputable def identityRbLookup {α : Type} (t : IdentityRbTree α)
    (identity : String) : Option α :=
  match identityKey? identity with
  | none => none
  | some k => identityRbLookupAux k t

/-- Single-pass balanced-tree uniqueness check over `Body` identities. -/
noncomputable def bodiesHaveUniqueIdentitiesAux (bs : List Body)
    (t : IdentityRbTree Unit) : Bool :=
  (identityRbBuildAux
    (fun (b : Body) => b.identity) (fun _ => ()) bs t).isSome

/-- Extend or truncate an in-memory scalar enum tag `tagBits` of primitive
representation `(tagW, tagS)` to the enum's discriminant bit width `discrW`,
matching `read_discriminant` (`int_to_int_or_float`) in
`compiler/rustc_const_eval/src/interpret/discriminant.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.Discriminant.readDiscriminant`
(`vendor/lean-miri/Miri/Interpreter/Discriminant.lean`):

> "let discr_val = self.int_to_int_or_float(&tag_val, discr_layout).unwrap();
> let discr_bits = discr_val.to_scalar().to_bits(discr_layout.size)?;" -/
noncomputable def tagBitsToDiscrBits (tagW : IntWidth) (tagS : Bool)
    (discrW : IntWidth) (tagBits : BitVec 128) : BitVec 128 :=
  let extended :=
    if tagS then
      bvOfInt 128 (signExtendBits tagW tagBits)
    else
      truncateBits tagW tagBits
  truncateBits discrW extended

/-- Check that a fieldless enum descriptor `ety : EnumTy` is statically
well-formed:
1. `ety.discriminants` is non-empty and has fewer than $2^{32}$ variants,
   matching `lean-miri`'s `< 2^32` variant-index bound (used on `Niche`
   paths in `vendor/lean-miri/Miri/Interpreter/Discriminant.lean`). In `rustc`,
   `rustc_abi::VariantIdx` (`rustc_index::newtype_index!` in
   `compiler/rustc_abi/src/layout.rs`, with default `max` value `0xFFFF_FF00`
   supplied by `compiler/rustc_index_macros/src/newtype.rs:98`,
   `rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) caps variant
   indices at `0xFFFF_FF00`; the small extra admitted range
   `[0xFFFF_FF01, 2^32)` cannot occur in real `rustc` MIR:

   > "rustc_index::newtype_index! {
   >     ...
   >     pub struct VariantIdx {
   >         /// Equivalent to `VariantIdx(0)`.
   >         const FIRST_VARIANT = 0;
   >     }
   > }"

2. Every entry `d ∈ ety.discriminants` fits unsigned in `ety.discrWidth`
   (`d < Nat.pow 2 ety.discrWidth.bitWidth`, matching `Discr.val` in
   `compiler/rustc_middle/src/ty/util.rs`).
3. All entries in `ety.discriminants` are pairwise distinct, matching the Rust
   Reference (`src/items/enumerations.md`, `rust-lang/reference`
   `a286e1ecb8ce193d50056e4bb042eea9b23876ef`):

   > "It is an error when two variants share the same discriminant."

4. `ety.tagRepr` accurately encodes every declared discriminant:
   - `.zeroSized` requires exactly 1 variant (`Variants::Single { index: 0 }`);
   - `.scalar tagW tagS` requires that truncating each `d` to `tagW` and
     re-extending via `tagBitsToDiscrBits tagW tagS ety.discrWidth` recovers
     `d` losslessly (`TagEncoding::Direct` in `tag_for_variant` /
     `read_discriminant`). -/
noncomputable def enumAdmitted (ety : EnumTy) : Bool :=
  !ety.discriminants.isEmpty &&
    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&
    ety.discriminants.all
      (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) &&
    natListPairwiseNe ety.discriminants &&
    match ety.tagRepr with
    | .zeroSized => Nat.beq ety.discriminants.length 1
    | .scalar tagW tagS =>
      ety.discriminants.all (fun d =>
        let dBits := BitVec.ofNat 128 d
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW dBits) == dBits)

/-- Check whether `ety` is an admitted 0-byte ZST 1-variant fieldless enum
(`Variants::Single { index: 0 }`). -/
noncomputable def isZstEnumTy (ety : EnumTy) : Bool :=
  match ety.tagRepr with
  | .zeroSized => enumAdmitted ety
  | .scalar _ _ => false

/-- Linear search from `idx` for the unique variant index whose declared
discriminant bit pattern equals `discrBits`. -/
noncomputable def findDiscrVariantAux (idx : Nat) (discrBits : BitVec 128) :
    List Nat → Option Nat
  | [] => none
  | d :: ds =>
    if BitVec.ofNat 128 d == discrBits then
      some idx
    else
      findDiscrVariantAux (idx + 1) discrBits ds

/-- Resolve a `discrWidth`-truncated discriminant bit pattern `discrBits` to its
0-based declaration variant index in `ds`, matching
`adt.discriminants(*self.tcx).find(|(_, var)| var.val == discr_bits)` in
`read_discriminant` (`compiler/rustc_const_eval/src/interpret/discriminant.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def findDiscrVariant? (discrBits : BitVec 128)
    (ds : List Nat) : Option Nat :=
  findDiscrVariantAux 0 discrBits ds

/-- Whether `n` is a Unicode scalar value, the values of Rust's `char`
(`src/types/char.md`, `rust-lang/reference`
`a286e1ecb8ce193d50056e4bb042eea9b23876ef`):

> "A value of type `char` is represented as a 32-bit unsigned word in the
> 0x0000 to 0xD7FF or 0xE000 to 0x10FFFF range. It is immediate [undefined
> behavior] to create a `char` that falls outside this range."

This is the check `Miri.Memory.ScalarInt.toChar`
(`vendor/lean-miri/Miri/Memory/ScalarInt.lean`) applies. -/
noncomputable def isUnicodeScalar (n : Nat) : Bool :=
  Nat.ble n 0x10ffff && !(Nat.ble 0xd800 n && Nat.ble n 0xdfff)

/-- The `i8` tag bit pattern of a `core::cmp::Ordering` value: `255` (`-1_i8`)
for `Less`, `0` for `Equal`, and `1` for `Greater`
(`library/core/src/cmp.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "// It has no special behavior, but does require that the three variants
> // `Less`/`Equal`/`Greater` remain `-1_i8`/`0_i8`/`+1_i8` respectively." -/
noncomputable def orderingTagBits : OrderingVal → Nat
  | .less => 255
  | .equal => 0
  | .greater => 1

/-- The `core::cmp::Ordering` value whose `i8` tag bit pattern is `bits`
(`orderingTagBits`), or `none` for any other bit pattern (an invalid tag). -/
noncomputable def orderingOfTagBits (bits : Nat) : Option OrderingVal :=
  if Nat.beq bits 255 then
    some .less
  else if Nat.beq bits 0 then
    some .equal
  else if Nat.beq bits 1 then
    some .greater
  else
    none

/-- Whether `ty` is the `(T, bool)` result type `.tuple [.int w s, .bool]` of
`BinOp::{Add,Sub,Mul}WithOverflow` on an integer `T`
(`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "Like `Add`, but returns `(T, bool)` of both the wrapped result
> and a bool indicating whether it overflowed."

These are the only tuple types that $M_{\text{anneal}}$ executes. -/
noncomputable def isOverflowPairTy : MirTy → Bool
  | .tuple [.int _ _, .bool] => true
  | _ => false

namespace Val

/-- Intrinsic type and well-formedness of a runtime value `Val`: returns
`some ty` iff `v` is a well-formed scalar, boolean, `char`, `Ordering`, unit,
fieldless enum, or overflow-pair value of type `ty`. An overflow pair
`.tuple [.scalar sv, .bool b]` has type `.tuple [.int sv.width sv.signed,
.bool]` (`isOverflowPairTy`); every other tuple has no type. -/
noncomputable def ty? : Val → Option MirTy
  | .scalar sv => if sv.wf then some (.int sv.width sv.signed) else none
  | .bool _ => some .bool
  | .char _ => some .char
  | .ordering _ => some .ordering
  | .unit => some .unit
  | .enumVal ety v =>
    if enumAdmitted ety && Nat.blt v ety.discriminants.length then
      some (.enum ety)
    else
      none
  | .tuple [.scalar sv, .bool _] =>
    if sv.wf then some (.tuple [.int sv.width sv.signed, .bool]) else none
  | _ => none

end Val

/-- Check that runtime value `v` has a well-formed intrinsic type equal to
`ty`. -/
noncomputable def checkVal (v : Val) (ty : MirTy) : Bool :=
  match v.ty? with
  | some vTy => MirTy.beq vTy ty
  | none => false

/-- Check that argument list `vs` matches parameter type list `tys` in length
and element types. -/
noncomputable def checkArgsMatch : List Val → List MirTy → Bool
  | [], [] => true
  | v :: vs, ty :: tys => checkVal v ty && checkArgsMatch vs tys
  | _, _ => false

/-- Check whether `ty` belongs to the supported local-variable type fragment
(`.bool`, `.int`, `.char`, `.ordering`, `.unit`, uninhabited `.never`,
admitted fieldless `.enum`, or an overflow pair `.tuple [.int w s, .bool]`).
The fragment is wider than the name suggests; downstream proof modules refer
to the predicate by this name. -/
noncomputable def isSupportedScalarOrUnitTy : MirTy → Bool
  | .bool | .int _ _ | .char | .ordering | .unit | .never => true
  | .enum ety => enumAdmitted ety
  | .tuple fs => isOverflowPairTy (.tuple fs)
  | _ => false

/-- Initial state of a newly live local slot of type `ty`:
In `rustc_const_eval`
(`compiler/rustc_const_eval/src/interpret/discriminant.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and `lean-miri`
(`Miri/Interpreter/Immediate.lean`, `OperandMachine.lean`, and
`Discriminant.lean`), an inhabited 0-byte ZST (`MirTy.unit` or an admitted
`.zeroSized` 1-variant fieldless enum `Variants::Single { index: 0 }`) requires
zero initialized bytes in memory:

> "Variants::Single { index } => {
>     if op.layout().is_uninhabited() {
>         ...
>         throw_ub!(UninhabitedEnumVariantRead(Some(index)));
>     }
>     ...
>     return interp_ok(index);
> }"

Accordingly, live `.unit` locals start inhabited by `Val.unit` and live
`.zeroSized` fieldless enum locals start inhabited by `Val.enumVal ety 0` (and
`Operand.move` preserves their inhabited ZST value). All other local types
start uninitialized (`.immediate none`). -/
noncomputable def liveUninitSlot : MirTy → LocalSlot
  | .unit => .immediate (some .unit)
  | .enum ety =>
    if isZstEnumTy ety then .immediate (some (.enumVal ety 0))
    else .immediate none
  | _ => .immediate none

/-- Check whether `ty : MirTy` has a primitive-readable
`BackendRepr.Scalar (.Initialized ..)` or `BackendRepr.ScalarPair` layout in
`Miri.Interpreter.MemoryOperand.readImmediate`
(`Miri/Interpreter/MemoryOperand.lean`): `bool`, integers, `char`, and
overflow pairs. Fieldless enums and `Ordering` are not, because their layouts
in $M_{\text{ref}}$ mark the tag scalar `.Union` (see
`Trusted.Correspondence.refEnumLayoutData`). -/
noncomputable def isPrimitiveReadableTy : MirTy → Bool
  | .bool | .int _ _ | .char => true
  | .tuple fs => isOverflowPairTy (.tuple fs)
  | _ => false

/-- Check whether `ty` is an integer-like cast source (an integer, `bool`, or
`char`), the source types that `CastKind::IntToInt` admits in
`compiler/rustc_const_eval/src/interpret/cast.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.Cast.cast`:

> "match sourceKind with
> | .integer _ | .boolean | .character => pure ()
> | _ => invalid \"IntToInt/IntToFloat source type is not integer-like\""
> (`vendor/lean-miri/Miri/Interpreter/Cast.lean`) -/
noncomputable def isIntLikeTy : MirTy → Bool
  | .bool | .int _ _ | .char => true
  | _ => false

/-! ## Profile v2 Value and Type Predicates -/

/- Profile v2 static local and pointee type admission and runtime value checks.
-/

/-- Return `true` when `ty` is a fixed-size data type (scalars, units,
admitted fieldless enums, and nested fixed-size arrays `[T; N]` thereof,
excluding overflow pairs, references, and raw pointers) whose memory layout
and byte representation are modeled in Profile v2. -/
noncomputable def isSupportedV2DataTy : MirTy → Bool
  | .array elem _ => isSupportedV2DataTy elem
  | ty => !isOverflowPairTy ty && isSupportedScalarOrUnitTy ty

/-- Return `true` when `ty` belongs to the Profile v2 structural `PartialEq`
fragment (`bool`, integers, `char`, `()`, `Ordering`, and fixed-size arrays
thereof), excluding user-defined `enum`s whose `PartialEq` impl may be
non-structural (`library/core/src/marker.rs` and `library/core/src/cmp.rs`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "StructuralPartialEq for
>     usize, u8, u16, u32, u64, u128,
>     isize, i8, i16, i32, i64, i128,
>     bool,
>     char,
>     ...
>     (),
>     {T, const N: usize} [T; N],"
> "#[derive_const(Clone, Eq, PartialOrd, Ord, PartialEq)]
> ...
> pub enum Ordering {" -/
noncomputable def isArrayEqElemSupported : MirTy → Bool
  | .bool | .int _ _ | .char | .unit | .ordering => true
  | .array elem _ => isArrayEqElemSupported elem
  | _ => false

/-- Return `true` when `inner` uses `rustc` `TagEncoding::Direct` with fixed
layout (scalar integers and raw pointers; no niche packing inside
`Option<inner>`, and no `#[repr(Rust)]` tuple or range reordering). -/
noncomputable def isNicheFreeOptionPayloadV2 : MirTy → Bool
  | .int _ _ | .rawPtr _ _ => true
  | _ => false

/-- Return `true` when `inner` has a verified `rustc` layout inside
`Option<inner>` (explicit `.unit`/`.bool`/`.ref` niche cases, or niche-free
`TagEncoding::Direct` payloads). -/
noncomputable def isOptionPayloadSupportedV2 (inner : MirTy) : Bool :=
  match inner with
  | .unit | .bool | .ref _ _ => true
  | _ => isNicheFreeOptionPayloadV2 inner

/-- Return `true` when `ty` is a sized Profile v2 pointee or slice-element type
containing no nested references or raw pointers and having a fixed, guaranteed
ABI representation across `rustc` field optimizations, so flat 1-level
`refValidInMem` and `refsStayInCallerMem` remain sound without modeling
`#[repr(Rust)]` field permutation or recursive pointer chasing.

All tuples (`OverflowPair` and general `.tuple`) and `Range`/`RangeTo`/
`RangeFrom` return `false` here (they remain local-only in
`isSupportedV2LocalTy`): `rustc` lays out tuples and `#[repr(Rust)]` structs
via `univariant` (`compiler/rustc_ty_utils/src/layout.rs:571-575` and
`compiler/rustc_abi/src/layout.rs:1111-1120`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), which reorders fields:

> "ty::Tuple(tys) => {
>     ...
>     univariant(tys, kind)?
> }"
> "let optimize_field_order = !repr.inhibit_struct_field_reordering();
> ...
> if optimize_field_order && fields.len() > 1 {"

`library/core/src/ops/range.rs:82,197,281` declares `Range`, `RangeFrom`,
and `RangeTo` without `#[repr(C)]`, so their in-memory layout is also governed
by `univariant`. `.option inner` additionally requires
`isOptionPayloadSupportedV2 inner` so unmodeled nested options such as
`&Option<Option<u8>>` fail closed. -/
noncomputable def isSizedNoRefV2Ty : MirTy → Bool
  | .bool | .int _ _ | .char | .ordering | .unit | .never => true
  | .enum ety => enumAdmitted ety
  | .option inner => isSizedNoRefV2Ty inner && isOptionPayloadSupportedV2 inner
  | .tuple _ | .array _ _ | .ref _ _ | .rawPtr _ _ | .slice _ | .unsupported
  | .str | .rangeTo _ | .rangeFrom _ | .range _ => false

mutual
  /-- Return `true` when `ty` is structurally inhabited in Rust (has at least
  one valid runtime value):
  - `.never`, `.unsupported`, and unsized `.slice` and `.str` have no value
    (`false`);
  - `.enum ety`: inhabited iff `enumAdmitted ety` (which requires
    `!ety.discriminants.isEmpty`);
  - `.array elem n`: `[T; 0]` is inhabited by `Val.array []` even when `T` is
    uninhabited (`[!; 0]`), whereas `[T; n + 1]` requires
    `isInhabitedV2Ty elem`;
  - `.tuple fs`: inhabited iff every field type is inhabited;
  - `.option _`: always inhabited by `None` (`Val.optionVal none`);
  - `.ref _ (.slice _)` and `.ref _ .str`: always inhabited by `&[]` and `""`
    (`len = 0`), whereas a thin reference `.ref _ pt` requires
    `isInhabitedV2Ty pt`;
  - primitives (`.bool`, `.int`, `.char`, `.ordering`, `.unit`), `.rawPtr`, and
    `Range`/`RangeTo`/`RangeFrom` over `usize` are inhabited. -/
  noncomputable def isInhabitedV2Ty : MirTy → Bool
    | .bool | .int _ _ | .char | .ordering | .unit => true
    | .never | .slice _ | .str | .unsupported => false
    | .enum ety => enumAdmitted ety
    | .array elem n => Nat.beq n 0 || isInhabitedV2Ty elem
    | .tuple fs => isInhabitedV2TyList fs
    | .option _ => true
    | .ref _ (.slice _) | .ref _ .str => true
    | .ref _ pt => isInhabitedV2Ty pt
    | .rawPtr _ _ => true
    | .rangeTo (.int .isize false) | .rangeFrom (.int .isize false)
    | .range (.int .isize false) => true
    | .rangeTo _ | .rangeFrom _ | .range _ => false

  noncomputable def isInhabitedV2TyList : List MirTy → Bool
    | [] => true
    | t :: ts => isInhabitedV2Ty t && isInhabitedV2TyList ts
end

/-- Profile v2 sized pointee admission for thin references and raw pointers:
the union of the ref-free sized types handled by the core contracts
(`isSizedNoRefV2Ty`) and the fixed-size array data types
(`isSupportedV2DataTy`). -/
noncomputable def isSupportedV2PointeeTy (pt : MirTy) : Bool :=
  isSizedNoRefV2Ty pt || isSupportedV2DataTy pt

mutual
  /-- Return `true` when `ty` is a valid Profile v2 sized local type
  (scalars, booleans, `char`, `Ordering`, `()`, `!`, admitted fieldless enums,
  fixed-size arrays `[T; N]` of data types, tuples, supported `Option`,
  `Range`/`RangeTo`/`RangeFrom` over `usize`, shared `&str`, and flat
  non-nested pointers or references to ref-free sized, fixed-array, or slice
  pointees).
  Nested references/pointers inside pointees (`&&T`, `*mut &T`, `&[&T]`,
  `[&T; N]`) are rejected fail-closed so `refValidInMem` and
  `refsStayInCallerMem` remain complete without recursive heap reference graphs.

  Overflow-pair pointees and array elements (`&(T, bool)`, `*const (T, bool)`,
  `[(T, bool); N]`) are rejected too.
  The Rust Reference (`src/type-layout.md:94,184`, `rust-lang/reference`
  `ad35aca481751a06afeb23820a672b0f3b11a476`) leaves a tuple's field order
  and size unspecified:

  > "Tuples are laid out according to the [`Rust` representation][`Rust`]."
  > ...
  > "There are no other guarantees of data layout made by this
  > representation."

  `overflowPairLayout` fixes one layout that capture never checks against
  `rustc`, so an overflow pair must stay a non-addressable local. Taking its
  address (`Rvalue.ref`, `Rvalue.addressOf`) or casting to a pointer to it
  (`CastKind.ptrToPtr`) needs a local of a rejected pointer type. -/
  noncomputable def isSupportedV2LocalTy : MirTy → Bool
    | .bool | .int _ _ | .char | .ordering | .unit | .never => true
    | .enum ety => enumAdmitted ety
    | .array elem _ => isSupportedV2DataTy elem
    | .tuple fs => isSupportedV2LocalTyList fs
    | .ref _ (.slice elem) | .rawPtr _ (.slice elem) => isSizedNoRefV2Ty elem
    | .ref .shared .str => true
    | .ref _ pt | .rawPtr _ pt => isSupportedV2PointeeTy pt
    | .rangeTo (.int .isize false) | .rangeFrom (.int .isize false) => true
    | .range (.int .isize false) => true
    | .option inner =>
      isSupportedV2LocalTy inner && isOptionPayloadSupportedV2 inner
    | _ => false

  noncomputable def isSupportedV2LocalTyList : List MirTy → Bool
    | [] => true
    | t :: ts => isSupportedV2LocalTy t && isSupportedV2LocalTyList ts
end

/-- Validate uniform element types across a list of values (used for `[T; N]`
array element checking without requiring `mutual` recursion). -/
noncomputable def checkValUniformV2 (check : Val → Bool) : List Val → Bool
  | [] => true
  | v :: vs => check v && checkValUniformV2 check vs

mutual
  /-- Validate runtime value `v` against Profile v2 static type `ty`, matching
  Profile v1 `checkVal` on scalar/enum/unit types and adding thin pointers,
  wide slice pointers, shared `&str`, fixed-size arrays,
  `Range`/`RangeTo`/`RangeFrom`, `Option`, and general tuples. -/
  noncomputable def checkValV2 : Val → MirTy → Bool
    | .scalar sv, .int w s => checkVal (.scalar sv) (.int w s)
    | .bool b, .bool => checkVal (.bool b) .bool
    | .char c, .char => checkVal (.char c) .char
    | .ordering ord, .ordering => checkVal (.ordering ord) .ordering
    | .unit, .unit => true
    | .enumVal ety v, .enum ety' => checkVal (.enumVal ety v) (.enum ety')
    | .ptr p, .rawPtr _ pt => !isUnsizedTy pt && IntWidth.beq p.width .isize
    | .ptr p, .ref _ pt => !isUnsizedTy pt && IntWidth.beq p.width .isize
    | .slicePtr p _, .rawPtr _ (.slice _) => IntWidth.beq p.width .isize
    | .slicePtr p _, .ref _ (.slice _) => IntWidth.beq p.width .isize
    | .slicePtr p _, .ref .shared .str => IntWidth.beq p.width .isize
    | .rangeTo _, .rangeTo (.int .isize false) => true
    | .rangeFrom _, .rangeFrom (.int .isize false) => true
    | .array vs, .array elem len =>
      Nat.beq vs.length len && checkValUniformV2 (fun v => checkValV2 v elem) vs
    | .range _ _, .range (.int .isize false) => true
    | .optionVal none, .option _ => true
    | .optionVal (some v), .option inner => checkValV2 v inner
    | .tuple vs, .tuple ts => checkValV2List vs ts
    | _, _ => false

  noncomputable def checkValV2List : List Val → List MirTy → Bool
    | [], [] => true
    | v :: vs, t :: ts => checkValV2 v t && checkValV2List vs ts
    | _, _ => false
end

/-- Check that Profile v2 argument list `vs` matches parameter type list `tys`
in length and well-formed runtime value representation. -/
noncomputable def checkArgsMatchV2 : List Val → List MirTy → Bool
  | [], [] => true
  | v :: vs, ty :: tys => checkValV2 v ty && checkArgsMatchV2 vs tys
  | _, _ => false

end Trusted.MirSemantics

end
