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
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Ops

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

/-- Check that `x` does not occur in `ys` under `stringBeq`. -/
noncomputable def stringNotElem (x : String) : List String → Bool
  | [] => true
  | y :: ys => !stringBeq x y && stringNotElem x ys

/-- Check that all strings in a `List String` are pairwise distinct. -/
noncomputable def stringListPairwiseNe : List String → Bool
  | [] => true
  | x :: xs => stringNotElem x xs && stringListPairwiseNe xs

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

namespace Val

/-- Intrinsic type and well-formedness of a runtime value `Val`: returns
`some ty` iff `v` is a well-formed scalar, boolean, unit, or fieldless enum
value of type `ty`. -/
noncomputable def ty? : Val → Option MirTy
  | .scalar sv => if sv.wf then some (.int sv.width sv.signed) else none
  | .bool _ => some .bool
  | .unit => some .unit
  | .enumVal ety v =>
    if enumAdmitted ety && Nat.blt v ety.discriminants.length then
      some (.enum ety)
    else
      none
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
(`.bool`, `.int`, `.unit`, uninhabited `.never`, or admitted fieldless
`.enum`). The fragment is wider than the name suggests; downstream proof
modules refer to the predicate by this name. -/
noncomputable def isSupportedScalarOrUnitTy : MirTy → Bool
  | .bool | .int _ _ | .unit | .never => true
  | .enum ety => enumAdmitted ety
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

/-- Check whether `ty : MirTy` has a primitive-readable `BackendRepr.Scalar`
layout in `Miri.Interpreter.MemoryOperand.readImmediate`
(`Miri/Interpreter/MemoryOperand.lean`). -/
noncomputable def isPrimitiveReadableTy : MirTy → Bool
  | .bool | .int _ _ => true
  | _ => false

end Trusted.MirSemantics
