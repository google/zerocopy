-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
## Reference Arithmetic, Constant, and Branch Equivalence (`vendor/lean-miri`)
-/

section MiriEquiv

open Miri.ABI Miri.Memory Miri.Interpreter

theorem bitVec_zeroExtend_eq {w : Nat} (hw : w ≤ 128) (x : BitVec w) :
    BitVec.zeroExtend 128 x = bvZeroExtend 128 x := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [BitVec.zeroExtend, BitVec.setWidth, bvZeroExtend]
  rw [dite_eq_left hw, BitVec.toNat_setWidth', BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.setWidth'._proof_1 hw x)).symm

theorem bitVec_ofInt_eq (n : Nat) (i : Int) :
    BitVec.ofInt n i = bvOfInt n i := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvOfInt]
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  change (intEmod i (Int.ofNat (HPow.hPow 2 n))).toNat =
    HMod.hMod (intEmod i (Int.ofNat (HPow.hPow 2 n))).toNat (HPow.hPow 2 n)
  exact (Nat.mod_eq_of_lt (BitVec.ofInt._proof_1 n i)).symm

theorem bitVec_signExtend_eq {w : Nat} (v : Nat) (x : BitVec w) :
    BitVec.signExtend v x = bvSignExtend v x := by
  dsimp only [BitVec.signExtend, bvSignExtend]
  rw [bitVec_ofInt_eq]
  rfl

theorem size_truncate_eq (w : IntWidth) (v : BitVec 128) :
    (toMiriSize w).truncate v = .ok (truncateBits w v) := by
  cases w <;> (
    change Except.ok (BitVec.zeroExtend 128 (BitVec.extractLsb _ 0 v)) =
      .ok (truncateBits _ v)
    rw [bitVec_zeroExtend_eq (by decide)]
    rfl)

theorem size_signExtend_eq (w : IntWidth) (v : BitVec 128) :
    (toMiriSize w).signExtend v = .ok (signExtendBits w v) := by
  cases w <;> (
    change Except.ok (BitVec.signExtend 128 (BitVec.extractLsb _ 0 v)).toInt =
      .ok (signExtendBits _ v)
    rw [bitVec_signExtend_eq]
    rfl)

theorem miriScalar_toUInt (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).toUInt (toMiriSize w) = .ok (truncateBits w bits) := by
  have h : (miriScalar w bits).toUInt (toMiriSize w) =
      ((toMiriSize w).truncate bits).mapError ScalarIntError.sizeError := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  rfl

theorem miriScalar_toInt (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).toInt (toMiriSize w) =
      .ok (signExtendBits w (truncateBits w bits)) := by
  have h : (miriScalar w bits).toInt (toMiriSize w) =
      match (toMiriSize w).truncate bits with
      | .ok b =>
        ((toMiriSize w).signExtend b).mapError ScalarIntError.sizeError
      | .error e => .error (.sizeError e) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  dsimp only
  rw [size_signExtend_eq]
  rfl

theorem integerOps_decode_eq (sv : ScalarVal) :
    IntegerOps.decode (miriIntValue sv) = .ok (decodeScalar sv) := by
  cases sv with
  | mk w s bits =>
    have hs : (toMiriIntType w s).signed = s := by cases w <;> cases s <;> rfl
    dsimp only [IntegerOps.decode, miriIntValue, decodeScalar]
    rw [hs]
    cases s with
    | true =>
      change ((miriScalar w bits).toInt (toMiriSize w)).mapError
        IntegerOpError.scalar = _
      rw [miriScalar_toInt]
      rfl
    | false =>
      change bind
        (((miriScalar w bits).toUInt (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun u => pure (Int.ofNat u.toNat)) = _
      rw [miriScalar_toUInt]
      rfl

theorem toMiriIntType_signed (w : IntWidth) (s : Bool) :
    (toMiriIntType w s).signed = s := by
  cases w <;> cases s <;> rfl

theorem toMiriIntType_size (w : IntWidth) (s : Bool) :
    (toMiriIntType w s).size = toMiriSize w := rfl

theorem unary_truncate_signed_eq (w : IntWidth) (resInt : Int) :
    (match bind
        ((ScalarInt.truncateFromInt
          (BitVec.ofInt 128 resInt).toInt (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w true resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k) := by
  rw [bitVec_ofInt_eq]
  change (match bind
      ((ScalarInt.truncateFromInt
        (bvToInt (bvOfInt 128 resInt)) (toMiriSize w)).mapError
        IntegerOpError.scalar)
      (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w true resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k)
  dsimp only [truncateScalar]
  let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
  rw [h_w]
  cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
  | true =>
    cases w <;> (
      dsimp only [ScalarInt.truncateFromInt]
      rw [h_oob]
      rfl)
  | false =>
    have h : (match bind
        ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun x => pure x.1) with
      | .ok sc =>
        (Except.ok (Val.scalar ⟨w, true, sc.data⟩) : Except FaultKind Val)
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported) =
      (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
      | .ok b =>
        match (toMiriSize w).signExtend b with
        | .ok _ => .ok (.scalar ⟨w, true, b⟩)
        | .error _ => .error .unsupported
      | .error _ => .error .unsupported) := by
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    rw [h, bitVec_ofInt_eq, size_truncate_eq]
    dsimp only
    rw [size_signExtend_eq]
    rfl

theorem unary_truncate_unsigned_eq (w : IntWidth) (resInt : Int) :
    (match bind
        ((ScalarInt.truncateFromUInt
          (BitVec.ofInt 128 resInt) (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w false resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k) := by
  rw [bitVec_ofInt_eq]
  dsimp only [truncateScalar]
  let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
  rw [h_raw]
  have h : (match bind
      ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
        IntegerOpError.scalar)
      (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, false, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match (toMiriSize w).truncate raw with
    | .ok b => .ok (.scalar ⟨w, false, b⟩)
    | .error _ => .error .unsupported) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]
  rfl

theorem unary_truncate_eq (w : IntWidth) (s : Bool) (resInt : Int) :
    (match bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped (toMiriIntType w s).size).mapError
            IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt
            (BitVec.ofInt 128 resInt) (toMiriIntType w s).size).mapError
            IntegerOpError.scalar)
        (fun x => pure x.1) with
    | .ok sc =>
      (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported) =
    (match truncateScalar w s resInt with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k) := by
  rw [toMiriIntType_signed, toMiriIntType_size]
  cases s with
  | true => exact unary_truncate_signed_eq w resInt
  | false => exact unary_truncate_unsigned_eq w resInt

/-- Proof-side helper matching `Miri.Interpreter.ScalarOps.unary` over
`Miri.Interpreter.IntegerOps.unary` for scalar and boolean operands. -/
noncomputable def evalRefMiriUnOp (op : Miri.MIR.UnOp) (v : Val) :
    Except FaultKind Val :=
  match op, v with
  | .Not, .bool b => .ok (.bool (!b))
  | _, .scalar sv =>
    match Miri.Interpreter.IntegerOps.unary op (miriIntValue sv) with
    | .ok sc => .ok (.scalar ⟨sv.width, sv.signed, sc.data⟩)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Proof-side shorthand lifting `Trusted.MirAst.UnOp` into
`evalRefMiriUnOp`. -/
noncomputable def evalRefUnOp (op : UnOp) (v : Val) : Except FaultKind Val :=
  evalRefMiriUnOp (toMiriUnOp op) v

theorem evalRefUnOp_eq (op : UnOp) (v : Val) :
    evalRefUnOp op v = evalUnOp op v := by
  cases v with
  | bool b => cases op <;> rfl
  | unit | enumVal _ _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _
  | range _ _ | optionVal _ | tuple _ | array _ | bytes _ | char _ | ordering _ =>
    cases op <;> rfl
  | scalar sv =>
    cases sv with
    | mk w s bits =>
      cases op with
      | not =>
        dsimp only [evalRefUnOp, evalRefMiriUnOp, evalUnOp, toMiriUnOp,
          IntegerOps.unary]
        rw [integerOps_decode_eq]
        exact unary_truncate_eq w s (intNot (decodeScalar ⟨w, s, bits⟩))
      | neg =>
        dsimp only [evalRefUnOp, evalRefMiriUnOp, evalUnOp, toMiriUnOp,
          IntegerOps.unary]
        rw [integerOps_decode_eq]
        change (match
            (let k := fun (result : Int) =>
              bind
                (if (toMiriIntType w s).signed then
                  let wrapped := (BitVec.ofInt 128 result).toInt
                  (ScalarInt.truncateFromInt wrapped
                    (toMiriIntType w s).size).mapError IntegerOpError.scalar
                else
                  (ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
                    (toMiriIntType w s).size).mapError IntegerOpError.scalar)
                (fun x => pure x.1)
            if (toMiriIntType w s).signed then
              bind (pure (Neg.neg (decodeScalar ⟨w, s, bits⟩))) k
            else
              bind (throw (IntegerOpError.invalidUnaryOperator .Neg
                (toMiriIntType w s).signed)) k) with
          | .ok sc =>
            (Except.ok (Val.scalar ⟨w, s, sc.data⟩) : Except FaultKind Val)
          | .error (.undefinedBehavior _) => .error .undefined
          | .error _ => .error .unsupported) =
          if s then
            match truncateScalar w s (Neg.neg (decodeScalar ⟨w, s, bits⟩)) with
            | .ok (res, _) => .ok (.scalar res)
            | .error k => .error k
          else
            .error .unsupported
        let ⟨resInt, h_res⟩ : ∃ x, Neg.neg (decodeScalar ⟨w, s, bits⟩) = x :=
          ⟨_, rfl⟩
        rw [h_res, toMiriIntType_signed, toMiriIntType_size]
        cases s with
        | false => rfl
        | true => exact unary_truncate_signed_eq w resInt
      | ptrMetadata =>
        dsimp only [evalRefUnOp, evalRefMiriUnOp, evalUnOp, toMiriUnOp,
          IntegerOps.unary]
        rw [integerOps_decode_eq]
        rfl

theorem size_signedIntMin_eq (w : IntWidth) :
    (toMiriSize w).signedIntMin = .ok (signedMinInt w) := by
  cases w <;> rfl

theorem bvAnd_eq (x y : BitVec 128) : HAnd.hAnd x y = bvAnd x y := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvAnd]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.and._proof_1 x y)).symm

theorem bvOr_eq (x y : BitVec 128) : HOr.hOr x y = bvOr x y := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvOr]
  rw [BitVec.toNat_or, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.or._proof_1 x y)).symm

theorem bvXor_eq (x y : BitVec 128) : HXor.hXor x y = bvXor x y := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bvXor]
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (BitVec.xor._proof_1 x y)).symm

theorem toMiriBinOp_isUnchecked (op : BinOp) :
    (toMiriBinOp op).isUnchecked = op.isUnchecked := by
  cases op <;> rfl

theorem toMiriBinOp_isOverflowing (op : BinOp) :
    (toMiriBinOp op).isOverflowing = op.isOverflowing := by
  cases op <;> rfl

/-- Proof-side map from Lean's `Ordering` (the `IntegerResult.ordering`
payload of `Miri.Interpreter.IntegerOps`) to `OrderingVal`. -/
noncomputable def refOrderingOfMiri : Ordering → OrderingVal
  | .lt => .less
  | .eq => .equal
  | .gt => .greater

/-- Proof-side map from a `Miri.Interpreter.IntegerOps` result at integer
type `(w, s)` to the corresponding `Val` or `FaultKind`, mirroring
`Miri.Interpreter.ScalarOps.finish` and `ScalarOps.integerError`. -/
noncomputable def refIntResultVal (w : IntWidth) (s : Bool)
    (r : Except IntegerOpError IntegerResult) : Except FaultKind Val :=
  match r with
  | .ok (.scalar sc) => .ok (.scalar ⟨w, s, sc.data⟩)
  | .ok (.withOverflow sc o) =>
    .ok (.tuple [.scalar ⟨w, s, sc.data⟩, .bool o])
  | .ok (.boolean b) => .ok (.bool b)
  | .ok (.ordering o) => .ok (.ordering (refOrderingOfMiri o))
  | .error (.undefinedBehavior _) => .error .undefined
  | .error _ => .error .unsupported

theorem shift_truncate_eq (op : BinOp) (w : IntWidth) (s rs : Bool)
    (resInt r : Int) (overflow : Bool) :
    (refIntResultVal w s (bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped
            (toMiriIntType w s).size).mapError IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriIntType w s).size).mapError IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)))) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (res, _) =>
      if overflow && op.isUnchecked then
        .error .undefined
      else
        .ok (.scalar res)) := by
  rw [toMiriIntType_signed, toMiriIntType_size, bitVec_ofInt_eq,
      toMiriBinOp_isUnchecked]
  cases s with
  | true =>
    change (refIntResultVal w true (bind
        ((ScalarInt.truncateFromInt (bvToInt (bvOfInt 128 resInt))
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)))) =
      (match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (res, _) =>
        if overflow && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar res))
    dsimp only [truncateScalar]
    let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
    rw [h_w]
    cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
    | true =>
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    | false =>
      have h : (refIntResultVal w true (bind
          ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar)
          (fun (value, _) =>
            if overflow && op.isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.shiftOverflow (toMiriBinOp op) r rs))
            else
              pure (IntegerResult.scalar value)))) =
        (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
        | .ok b =>
          match (toMiriSize w).signExtend b with
          | .ok _ =>
            if overflow && op.isUnchecked then
              .error .undefined
            else
              .ok (.scalar ⟨w, true, b⟩)
          | .error _ => .error .unsupported
        | .error _ => .error .unsupported) := by
        cases w <;> (
          dsimp only [ScalarInt.truncateFromInt]
          rw [h_oob]
          cases (overflow && op.isUnchecked) <;> rfl)
      rw [h, bitVec_ofInt_eq, size_truncate_eq]
      dsimp only
      rw [size_signExtend_eq]
      rfl
  | false =>
    change (refIntResultVal w false (bind
        ((ScalarInt.truncateFromUInt (bvOfInt 128 resInt)
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)))) =
      (match truncateScalar w false resInt with
      | .error k => .error k
      | .ok (res, _) =>
        if overflow && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar res))
    dsimp only [truncateScalar]
    let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
    rw [h_raw]
    have h : (refIntResultVal w false (bind
        ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, _) =>
          if overflow && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.shiftOverflow (toMiriBinOp op) r rs))
          else
            pure (IntegerResult.scalar value)))) =
      (match (toMiriSize w).truncate raw with
      | .ok b =>
        if overflow && op.isUnchecked then
          .error .undefined
        else
          .ok (.scalar ⟨w, false, b⟩)
      | .error _ => .error .unsupported) := by
      cases w <;> cases (overflow && op.isUnchecked) <;> rfl
    rw [h, size_truncate_eq]
    rfl

theorem binary_truncate_scalarResult_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (resInt : Int) (hostOverflow ovf : Bool)
    (h_ovf : (toMiriBinOp op).isOverflowing = ovf) :
    (refIntResultVal w s (bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped
            (toMiriIntType w s).size).mapError IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriIntType w s).size).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if (toMiriBinOp op).isOverflowing then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)))) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (val, lossy) =>
      if (hostOverflow || lossy) && op.isUnchecked then
        .error .undefined
      else if ovf then
        .ok (.tuple [.scalar val, .bool (hostOverflow || lossy)])
      else
        .ok (.scalar val)) := by
  rw [toMiriIntType_signed, toMiriIntType_size, bitVec_ofInt_eq, h_ovf,
      toMiriBinOp_isUnchecked]
  cases s with
  | true =>
    change (refIntResultVal w true (bind
        ((ScalarInt.truncateFromInt (bvToInt (bvOfInt 128 resInt))
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if ovf then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)))) =
      (match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        if (hostOverflow || lossy) && op.isUnchecked then
          .error .undefined
        else if ovf then
          .ok (.tuple [.scalar val, .bool (hostOverflow || lossy)])
        else
          .ok (.scalar val))
    dsimp only [truncateScalar]
    let ⟨wrapped, h_w⟩ : ∃ x, bvToInt (bvOfInt 128 resInt) = x := ⟨_, rfl⟩
    rw [h_w]
    cases h_oob : (decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127)) with
    | true =>
      cases w <;> (
        dsimp only [ScalarInt.truncateFromInt]
        rw [h_oob]
        rfl)
    | false =>
      have h : (refIntResultVal w true (bind
          ((ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && op.isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if ovf then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value)))) =
        (match (toMiriSize w).truncate (BitVec.ofInt 128 wrapped) with
        | .ok b =>
          match (toMiriSize w).signExtend b with
          | .ok dec =>
            if (hostOverflow || (dec != wrapped)) && op.isUnchecked then
              .error .undefined
            else if ovf then
              .ok (.tuple [.scalar ⟨w, true, b⟩,
                .bool (hostOverflow || (dec != wrapped))])
            else
              .ok (.scalar ⟨w, true, b⟩)
          | .error _ => .error .unsupported
        | .error _ => .error .unsupported) := by
        cases w <;> (
          dsimp only [ScalarInt.truncateFromInt]
          rw [h_oob]
          change (refIntResultVal _ true
              ((if ((hostOverflow || _) && op.isUnchecked) = true then
              Except.error (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              Except.ok (if ovf then IntegerResult.withOverflow _ _
                else IntegerResult.scalar _)))) =
            if ((hostOverflow || _) && op.isUnchecked) = true then
              Except.error FaultKind.undefined
            else if ovf then
              Except.ok (Val.tuple [Val.scalar ⟨_, true, _⟩, Val.bool _])
            else
              Except.ok (Val.scalar ⟨_, true, _⟩)
          cases ((hostOverflow || _) && op.isUnchecked) <;> cases ovf <;> rfl)
      rw [h, bitVec_ofInt_eq, size_truncate_eq]
      dsimp only
      rw [size_signExtend_eq]
      rfl
  | false =>
    change (refIntResultVal w false (bind
        ((ScalarInt.truncateFromUInt (bvOfInt 128 resInt)
          (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if ovf then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)))) =
      (match truncateScalar w false resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        if (hostOverflow || lossy) && op.isUnchecked then
          .error .undefined
        else if ovf then
          .ok (.tuple [.scalar val, .bool (hostOverflow || lossy)])
        else
          .ok (.scalar val))
    dsimp only [truncateScalar]
    let ⟨raw, h_raw⟩ : ∃ x, bvOfInt 128 resInt = x := ⟨_, rfl⟩
    rw [h_raw]
    have h : (refIntResultVal w false (bind
        ((ScalarInt.truncateFromUInt raw (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && op.isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if ovf then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value)))) =
      (match (toMiriSize w).truncate raw with
      | .ok b =>
        if (hostOverflow || (b != raw)) && op.isUnchecked then
          .error .undefined
        else if ovf then
          .ok (.tuple [.scalar ⟨w, false, b⟩,
            .bool (hostOverflow || (b != raw))])
        else
          .ok (.scalar ⟨w, false, b⟩)
      | .error _ => .error .unsupported) := by
      cases w <;> (
        change (refIntResultVal _ false
            ((if ((hostOverflow || _) && op.isUnchecked) = true then
            Except.error (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            Except.ok (if ovf then IntegerResult.withOverflow _ _
                else IntegerResult.scalar _)))) =
          if ((hostOverflow || _) && op.isUnchecked) = true then
            Except.error FaultKind.undefined
          else if ovf then
            Except.ok (Val.tuple [Val.scalar ⟨_, false, _⟩, Val.bool _])
          else
            Except.ok (Val.scalar ⟨_, false, _⟩)
        cases ((hostOverflow || _) && op.isUnchecked) <;> cases ovf <;> rfl)
    rw [h, size_truncate_eq]
    rfl

theorem toMiriIntType_bne_of_false {w₁ w₂ : IntWidth} {s₁ s₂ : Bool}
    (h : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = false) :
    (toMiriIntType w₁ s₁ != toMiriIntType w₂ s₂) = true := by
  cases w₁ <;> cases w₂ <;> cases s₁ <;> cases s₂ <;>
    first | rfl | nomatch h

theorem eq_of_intWidth_beq_and_signed {w₁ w₂ : IntWidth} {s₁ s₂ : Bool}
    (h : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = true) : w₁ = w₂ ∧ s₁ = s₂ := by
  cases w₁ <;> cases w₂ <;> cases s₁ <;> cases s₂ <;>
    first | exact ⟨rfl, rfl⟩ | nomatch h

theorem toMiriIntType_bne_self (w : IntWidth) (s : Bool) :
    (toMiriIntType w s != toMiriIntType w s) = false := by
  cases w <;> cases s <;> rfl

theorem bitwise_truncate_eq (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    (refIntResultVal w s (bind
        ((ScalarInt.truncateFromUInt bits (toMiriSize w)).mapError
          IntegerOpError.scalar)
        (fun (value, _) => pure (IntegerResult.scalar value)))) =
    .ok (.scalar ⟨w, s, truncateBits w bits⟩) := by
  have h : (refIntResultVal w s (bind
      ((ScalarInt.truncateFromUInt bits (toMiriSize w)).mapError
        IntegerOpError.scalar)
      (fun (value, _) => pure (IntegerResult.scalar value)))) =
    (match (toMiriSize w).truncate bits with
    | .ok b => .ok (.scalar ⟨w, s, b⟩)
    | .error _ => .error .unsupported) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

/-- Proof-side helper matching `Miri.Interpreter.ScalarOps.binary` over
`Miri.Interpreter.IntegerOps.{binary,binaryBool,binaryChar}` for scalar,
boolean, and `char` operands. -/
noncomputable def evalRefMiriBinOp (op : Miri.MIR.BinOp) (lhs rhs : Val) :
    Except FaultKind Val :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    refIntResultVal l.width l.signed
      (Miri.Interpreter.IntegerOps.binary op (miriIntValue l) (miriIntValue r))
  | .bool l, .bool r =>
    match Miri.Interpreter.IntegerOps.binaryBool op l r with
    | .ok (.boolean b) => .ok (.bool b)
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported
  | .char l, .char r =>
    match Miri.Interpreter.IntegerOps.binaryChar op l r with
    | .ok (.boolean b) => .ok (.bool b)
    | .ok (.ordering o) => .ok (.ordering (refOrderingOfMiri o))
    | .ok _ => .error .unsupported
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Proof-side shorthand lifting `Trusted.MirAst.BinOp` into
`evalRefMiriBinOp`. -/
noncomputable def evalRefBinOp (op : BinOp) (lhs rhs : Val) :
    Except FaultKind Val :=
  evalRefMiriBinOp (toMiriBinOp op) lhs rhs

theorem evalShiftOp_eq (op : BinOp) (w₁ w₂ : IntWidth) (s₁ s₂ : Bool)
    (bits₁ bits₂ : BitVec 128) (h_sh : op.isShift = true) :
    evalRefBinOp op (.scalar ⟨w₁, s₁, bits₁⟩) (.scalar ⟨w₂, s₂, bits₂⟩) =
    evalBinOp op (.scalar ⟨w₁, s₁, bits₁⟩) (.scalar ⟨w₂, s₂, bits₂⟩) := by
  have proveShift (op' : BinOp) (resInt rInt : Int) (w : IntWidth) :
      (refIntResultVal w s₁ (bind
          (if (toMiriIntType w s₁).signed then
            let wrapped := (BitVec.ofInt 128 resInt).toInt
            (ScalarInt.truncateFromInt wrapped
              (toMiriIntType w s₁).size).mapError IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
              (toMiriIntType w s₁).size).mapError IntegerOpError.scalar)
          (fun (value, _) =>
            if (intEmod rInt (Int.ofNat w.bitWidth) != rInt) &&
                (toMiriBinOp op').isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.shiftOverflow (toMiriBinOp op') rInt
                  (toMiriIntType w₂ s₂).signed))
            else
              pure (IntegerResult.scalar value)))) =
      (match truncateScalar w s₁ resInt with
      | .error k => .error k
      | .ok (res, _) =>
        if (intEmod rInt (Int.ofNat w.bitWidth) != rInt) && op'.isUnchecked then
          .error .undefined
        else
          .ok (.scalar res)) :=
    shift_truncate_eq op' w s₁ (toMiriIntType w₂ s₂).signed resInt rInt _
  cases op with
  | shl =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp, evalShiftOp,
      toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shl
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .isize
  | shr =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp, evalShiftOp,
      toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shr
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .isize
  | shlUnchecked =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp, evalShiftOp,
      toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shlUnchecked
        (intShiftLeft lInt (intEmod rInt 64).toNat) rInt .isize
  | shrUnchecked =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp, evalShiftOp,
      toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x := ⟨_, rfl⟩
    let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x := ⟨_, rfl⟩
    rw [h_l, h_r]
    cases w₁ with
    | i8 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 8).toNat) rInt .i8
    | i16 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 16).toNat) rInt .i16
    | i32 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 32).toNat) rInt .i32
    | i64 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .i64
    | i128 =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 128).toNat) rInt .i128
    | isize =>
      exact proveShift .shrUnchecked
        (intShiftRight lInt (intEmod rInt 64).toNat) rInt .isize
  | _ => nomatch h_sh

theorem miriIntValue_type_bne_of_false (w₁ w₂ : IntWidth) (s₁ s₂ : Bool)
    (b₁ b₂ : BitVec 128) (h : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = false) :
    ((miriIntValue ⟨w₁, s₁, b₁⟩).type != (miriIntValue ⟨w₂, s₂, b₂⟩).type) =
      true :=
  toMiriIntType_bne_of_false h

theorem miriIntValue_type_bne_self (w : IntWidth) (s : Bool)
    (b₁ b₂ : BitVec 128) :
    ((miriIntValue ⟨w, s, b₁⟩).type != (miriIntValue ⟨w, s, b₂⟩).type) =
      false :=
  toMiriIntType_bne_self w s

theorem miriIntValue_toUInt (w : IntWidth) (s : Bool) (bits : BitVec 128) :
    (miriIntValue ⟨w, s, bits⟩).scalar.toUInt
      (miriIntValue ⟨w, s, bits⟩).type.size =
    .ok (truncateBits w bits) :=
  miriScalar_toUInt w bits

theorem arith_after_rw_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (resInt : Int) :
    (refIntResultVal w s (
      (let hostOverflow := if s then
          decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (resInt ≥ HPow.hPow (2 : Int) 127)
        else
          decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128)
      bind (if s then
          let wrapped := (BitVec.ofInt 128 resInt).toInt
          (ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
            IntegerOpError.scalar
        else
          (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
            (toMiriSize w)).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior
              (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if (toMiriBinOp op).isOverflowing then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else
              IntegerResult.scalar value))))) =
    (match truncateScalar w s resInt with
    | .error k => .error k
    | .ok (val, lossy) =>
      if ((if s then
            decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 127)
          else
            decide (resInt < 0) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 128)) ||
          lossy) && op.isUnchecked then
        .error .undefined
      else if op.isOverflowing then
        .ok (.tuple [.scalar val, .bool ((if s then
            decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 127)
          else
            decide (resInt < 0) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 128)) ||
          lossy)])
      else
        .ok (.scalar val)) := by
  have h := binary_truncate_scalarResult_eq op w s resInt
    (if s then
      decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (resInt ≥ HPow.hPow (2 : Int) 127)
    else
      decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128))
    op.isOverflowing (toMiriBinOp_isOverflowing op)
  rw [toMiriIntType_signed, toMiriIntType_size] at h
  exact h

theorem int_tdiv_eq (a b : Int) : Int.tdiv a b = intTdiv a b := by
  cases a <;> cases b <;> rfl

theorem int_tmod_eq (a b : Int) : Int.tmod a b = intTmod a b := by
  cases a <;> cases b <;> rfl

theorem div_rem_signed_eq (op : BinOp) (w : IntWidth)
    (lInt rInt resInt : Int) :
    (refIntResultVal w true (
      (let jp := fun (_ : PUnit) =>
        let hostOverflow := if true then
            decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (resInt ≥ HPow.hPow (2 : Int) 127)
          else
            decide (resInt < 0) || decide (resInt ≥ HPow.hPow (2 : Int) 128)
        bind (if true then
            let wrapped := (BitVec.ofInt 128 resInt).toInt
            (ScalarInt.truncateFromInt wrapped (toMiriSize w)).mapError
              IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 resInt)
              (toMiriSize w)).mapError IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if (toMiriBinOp op).isOverflowing then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value))
      if lInt == signedMinInt w && rInt == Neg.neg 1 then
        bind (throw (IntegerOpError.undefinedBehavior
          (if toMiriBinOp op == Miri.MIR.BinOp.Div then
            .divisionOverflow
          else
            .remainderOverflow))) jp
      else
        jp PUnit.unit))) =
    (if (false : Bool) then
      .error .undefined
    else if lInt == signedMinInt w && rInt == Neg.neg 1 then
      .error .undefined
    else
      match truncateScalar w true resInt with
      | .error k => .error k
      | .ok (val, lossy) =>
        if ((if true then
              decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
                decide (resInt ≥ HPow.hPow (2 : Int) 127)
            else
              decide (resInt < 0) ||
                decide (resInt ≥ HPow.hPow (2 : Int) 128)) ||
            lossy) && op.isUnchecked then
          .error .undefined
        else if op.isOverflowing then
          .ok (.tuple [.scalar val, .bool ((if true then
              decide (resInt < Neg.neg (HPow.hPow (2 : Int) 127)) ||
                decide (resInt ≥ HPow.hPow (2 : Int) 127)
            else
              decide (resInt < 0) ||
                decide (resInt ≥ HPow.hPow (2 : Int) 128)) ||
            lossy)])
        else
          .ok (.scalar val)) := by
  cases (lInt == signedMinInt w && rInt == Neg.neg 1) with
  | true => rfl
  | false => exact arith_after_rw_eq op w true resInt

theorem arith_full_eq (op : BinOp) (w : IntWidth) (s : Bool) (lInt rInt : Int)
    (h_op : (match op with
      | .add | .sub | .mul | .addUnchecked | .subUnchecked | .mulUnchecked
      | .addWithOverflow | .subWithOverflow | .mulWithOverflow
      | .div | .rem | .offset => true
      | _ => false) = true) :
    (refIntResultVal w s (
      (let jp3 := fun (result : Int) =>
        let hostOverflow := if (toMiriIntType w s).signed then
            decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
              decide (result ≥ HPow.hPow (2 : Int) 127)
          else
            decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
        bind (if (toMiriIntType w s).signed then
            let wrapped := (BitVec.ofInt 128 result).toInt
            (ScalarInt.truncateFromInt wrapped
              (toMiriIntType w s).size).mapError IntegerOpError.scalar
          else
            (ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
              (toMiriIntType w s).size).mapError IntegerOpError.scalar)
          (fun (value, lossy) =>
            if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
              throw (IntegerOpError.undefinedBehavior
                (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if (toMiriBinOp op).isOverflowing then
                IntegerResult.withOverflow value (hostOverflow || lossy)
              else
                IntegerResult.scalar value))
      let jp2 := fun (_ : PUnit) =>
        match toMiriBinOp op with
        | .Add | .AddUnchecked | .AddWithOverflow =>
          bind (pure (lInt + rInt)) jp3
        | .Sub | .SubUnchecked | .SubWithOverflow =>
          bind (pure (lInt - rInt)) jp3
        | .Mul | .MulUnchecked | .MulWithOverflow =>
          bind (pure (lInt * rInt)) jp3
        | .Div => bind (pure (Int.tdiv lInt rInt)) jp3
        | .Rem => bind (pure (Int.tmod lInt rInt)) jp3
        | _ =>
          bind (throw (IntegerOpError.invalidBinaryOperator (toMiriBinOp op)))
            jp3
      let jp1 := fun (_ : PUnit) =>
        if (toMiriIntType w s).signed &&
            (toMiriBinOp op == Miri.MIR.BinOp.Div ||
              toMiriBinOp op == Miri.MIR.BinOp.Rem) then
          bind (((toMiriIntType w s).size.signedIntMin).mapError
              (Function.comp IntegerOpError.scalar ScalarIntError.sizeError))
            (fun min =>
              if lInt == min && rInt == Neg.neg 1 then
                bind (throw (IntegerOpError.undefinedBehavior
                  (if toMiriBinOp op == Miri.MIR.BinOp.Div then
                    .divisionOverflow
                  else
                    .remainderOverflow))) jp2
              else
                jp2 PUnit.unit)
        else
          jp2 PUnit.unit
      if rInt == 0 then
        let jp0 := fun (_ : PUnit) =>
          if toMiriBinOp op == Miri.MIR.BinOp.Rem then
            bind (throw (IntegerOpError.undefinedBehavior .remainderByZero))
              jp1
          else
            jp1 PUnit.unit
        if toMiriBinOp op == Miri.MIR.BinOp.Div then
          bind (throw (IntegerOpError.undefinedBehavior .divisionByZero)) jp0
        else
          jp0 PUnit.unit
      else
        jp1 PUnit.unit))) =
    evalArithOp op w s lInt rInt := by
  rw [toMiriIntType_signed, toMiriIntType_size, size_signedIntMin_eq,
      int_tdiv_eq, int_tmod_eq]
  cases op with
  | add =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .add w false (lInt + rInt)
    | true => exact arith_after_rw_eq .add w true (lInt + rInt)
  | sub =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .sub w false (lInt - rInt)
    | true => exact arith_after_rw_eq .sub w true (lInt - rInt)
  | mul =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .mul w false (lInt * rInt)
    | true => exact arith_after_rw_eq .mul w true (lInt * rInt)
  | addUnchecked =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .addUnchecked w false (lInt + rInt)
    | true => exact arith_after_rw_eq .addUnchecked w true (lInt + rInt)
  | subUnchecked =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .subUnchecked w false (lInt - rInt)
    | true => exact arith_after_rw_eq .subUnchecked w true (lInt - rInt)
  | mulUnchecked =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .mulUnchecked w false (lInt * rInt)
    | true => exact arith_after_rw_eq .mulUnchecked w true (lInt * rInt)
  | addWithOverflow =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .addWithOverflow w false (lInt + rInt)
    | true => exact arith_after_rw_eq .addWithOverflow w true (lInt + rInt)
  | subWithOverflow =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .subWithOverflow w false (lInt - rInt)
    | true => exact arith_after_rw_eq .subWithOverflow w true (lInt - rInt)
  | mulWithOverflow =>
    cases (rInt == 0) <;> cases s with
    | false => exact arith_after_rw_eq .mulWithOverflow w false (lInt * rInt)
    | true => exact arith_after_rw_eq .mulWithOverflow w true (lInt * rInt)
  | offset => cases (rInt == 0) <;> cases s <;> rfl
  | div =>
    dsimp only [evalArithOp]
    cases (rInt == 0) with
    | true => rfl
    | false =>
      cases s with
      | false => exact arith_after_rw_eq .div w false (intTdiv lInt rInt)
      | true => exact div_rem_signed_eq .div w lInt rInt (intTdiv lInt rInt)
  | rem =>
    dsimp only [evalArithOp]
    cases (rInt == 0) with
    | true => rfl
    | false =>
      cases s with
      | false => exact arith_after_rw_eq .rem w false (intTmod lInt rInt)
      | true => exact div_rem_signed_eq .rem w lInt rInt (intTmod lInt rInt)
  | _ => nomatch h_op

theorem evalArithOp_eq (op : BinOp) (w : IntWidth) (s : Bool)
    (bits₁ bits₂ : BitVec 128)
    (h_op : (match op with
      | .add | .sub | .mul | .addUnchecked | .subUnchecked | .mulUnchecked
      | .addWithOverflow | .subWithOverflow | .mulWithOverflow
      | .div | .rem | .offset => true
      | _ => false) = true) :
    evalRefBinOp op (.scalar ⟨w, s, bits₁⟩) (.scalar ⟨w, s, bits₂⟩) =
    evalArithOp op w s (decodeScalar ⟨w, s, bits₁⟩)
      (decodeScalar ⟨w, s, bits₂⟩) := by
  have h_full := arith_full_eq op w s
    (decodeScalar ⟨w, s, bits₁⟩) (decodeScalar ⟨w, s, bits₂⟩) h_op
  cases op with
  | add | sub | mul | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow | div | rem | offset =>
    dsimp only [evalRefBinOp, evalRefMiriBinOp, toMiriBinOp, IntegerOps.binary]
    rw [integerOps_decode_eq, integerOps_decode_eq]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [miriIntValue_type_bne_self]
    exact h_full
  | _ => nomatch h_op

theorem refOrderingOfMiri_compareOfLessAndEq {α : Type} [LT α]
    [deq : DecidableEq α] (x y : α) [dlt : Decidable (x < y)] (l r : Int)
    (h_lt : x < y ↔ l < r) (h_eq : x = y ↔ l = r) :
    refOrderingOfMiri (compareOfLessAndEq x y) = cmpOrderingOfInt l r := by
  dsimp only [compareOfLessAndEq, cmpOrderingOfInt]
  cases dlt with
  | isTrue h =>
    rw [decide_eq_true (h_lt.mp h)]
    rfl
  | isFalse h =>
    rw [decide_eq_false (fun h' => h (h_lt.mpr h'))]
    cases deq x y with
    | isTrue h₂ =>
      rw [decide_eq_true (h_eq.mp h₂)]
      rfl
    | isFalse h₂ =>
      rw [decide_eq_false (fun h' => h₂ (h_eq.mpr h'))]
      rfl

theorem refOrderingOfMiri_compare_int (l r : Int) :
    refOrderingOfMiri (compare l r) = cmpOrderingOfInt l r :=
  refOrderingOfMiri_compareOfLessAndEq l r l r Iff.rfl Iff.rfl

theorem char_lt_iff (l r : Char) :
    l < r ↔ Int.ofNat l.toNat < Int.ofNat r.toNat :=
  Iff.trans Char.lt_def
    (Iff.trans UInt32.lt_iff_toNat_lt Int.ofNat_lt.symm)

theorem char_le_iff (l r : Char) :
    l ≤ r ↔ Int.ofNat l.toNat ≤ Int.ofNat r.toNat :=
  Iff.trans Char.le_def (Iff.trans UInt32.le_iff_toNat_le Int.ofNat_le.symm)

theorem char_eq_iff (l r : Char) :
    l = r ↔ Int.ofNat l.toNat = Int.ofNat r.toNat :=
  Iff.trans Char.toNat_inj.symm Int.ofNat_inj.symm

theorem decide_congr_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : decide p = decide q := by
  cases h_p : decide p with
  | true => exact (decide_eq_true (h.mp (of_decide_eq_true h_p))).symm
  | false =>
    exact (decide_eq_false (fun h_q => absurd (h.mpr h_q)
      (of_decide_eq_false h_p))).symm

theorem refOrderingOfMiri_compare_char (l r : Char) :
    refOrderingOfMiri (compare l r) =
      cmpOrderingOfInt (Int.ofNat l.toNat) (Int.ofNat r.toNat) :=
  refOrderingOfMiri_compareOfLessAndEq l r _ _ (char_lt_iff l r)
    (char_eq_iff l r)

theorem evalCharBinOp_eq (op : BinOp) (l r : Char) :
    evalRefBinOp op (.char l) (.char r) = evalBinOp op (.char l) (.char r) := by
  cases op with
  | eq =>
    change Except.ok (Val.bool (decide (l = r))) =
      Except.ok (Val.bool (decide (Int.ofNat l.toNat = Int.ofNat r.toNat)))
    rw [decide_congr_iff (char_eq_iff l r)]
  | ne =>
    change Except.ok (Val.bool (!decide (l = r))) =
      Except.ok (Val.bool (!decide (Int.ofNat l.toNat = Int.ofNat r.toNat)))
    rw [decide_congr_iff (char_eq_iff l r)]
  | lt =>
    change Except.ok (Val.bool (decide (l < r))) =
      Except.ok (Val.bool (decide (Int.ofNat l.toNat < Int.ofNat r.toNat)))
    rw [decide_congr_iff (char_lt_iff l r)]
  | le =>
    change Except.ok (Val.bool (decide (l ≤ r))) =
      Except.ok (Val.bool (decide (Int.ofNat l.toNat ≤ Int.ofNat r.toNat)))
    rw [decide_congr_iff (char_le_iff l r)]
  | gt =>
    change Except.ok (Val.bool (decide (r < l))) =
      Except.ok (Val.bool (decide (Int.ofNat r.toNat < Int.ofNat l.toNat)))
    rw [decide_congr_iff (char_lt_iff r l)]
  | ge =>
    change Except.ok (Val.bool (decide (r ≤ l))) =
      Except.ok (Val.bool (decide (Int.ofNat r.toNat ≤ Int.ofNat l.toNat)))
    rw [decide_congr_iff (char_le_iff r l)]
  | cmp =>
    change Except.ok (Val.ordering (refOrderingOfMiri (compare l r))) =
      Except.ok (Val.ordering
        (cmpOrderingOfInt (Int.ofNat l.toNat) (Int.ofNat r.toNat)))
    rw [refOrderingOfMiri_compare_char]
  | _ => rfl

theorem evalRefBinOp_eq (op : BinOp) (lhs rhs : Val) :
    evalRefBinOp op lhs rhs = evalBinOp op lhs rhs := by
  cases lhs with
  | unit | enumVal _ _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _
  | range _ _ | optionVal _ | tuple _ | array _ | bytes _ | ordering _ =>
    cases rhs <;> rfl
  | bool l =>
    cases rhs with
    | unit | enumVal _ _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _
    | range _ _ | optionVal _ | tuple _ | array _ | bytes _ | scalar _ | char _ | ordering _ => rfl
    | bool r => cases op <;> cases l <;> cases r <;> rfl
  | char l =>
    cases rhs with
    | unit | enumVal _ _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _
    | range _ _ | optionVal _ | tuple _ | array _ | bytes _ | scalar _ | bool _ | ordering _ => rfl
    | char r => exact evalCharBinOp_eq op l r
  | scalar l =>
    cases rhs with
    | unit | enumVal _ _ | ptr _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _ | rangeTo _ | rangeFrom _
    | range _ _ | optionVal _ | tuple _ | array _ | bytes _ | bool _ | char _ | ordering _ => rfl
    | scalar r =>
      cases l with
      | mk w₁ s₁ bits₁ =>
        cases r with
        | mk w₂ s₂ bits₂ =>
          cases h_sh : op.isShift with
          | true => exact evalShiftOp_eq op w₁ w₂ s₁ s₂ bits₁ bits₂ h_sh
          | false =>
            cases h_ty : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) with
            | false =>
              have h_bne :=
                miriIntValue_type_bne_of_false w₁ w₂ s₁ s₂ bits₁ bits₂ h_ty
              cases op with
              | shl | shr | shlUnchecked | shrUnchecked => nomatch h_sh
              | _ =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty]
                first | rfl | (
                  rw [integerOps_decode_eq, integerOps_decode_eq]
                  let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                    ⟨_, rfl⟩
                  let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₂, s₂, bits₂⟩ = x :=
                    ⟨_, rfl⟩
                  rw [h_l, h_r]
                  dsimp only [bind, Except.bind, pure, Except.pure]
                  rw [h_bne]
                  rfl)
            | true =>
              let ⟨h_w, h_s⟩ := eq_of_intWidth_beq_and_signed h_ty
              subst h_w
              subst h_s
              have h_bne := miriIntValue_type_bne_self w₁ s₁ bits₁ bits₂
              cases op with
              | shl | shr | shlUnchecked | shrUnchecked => nomatch h_sh
              | offset =>
                dsimp only [evalBinOp]
                rw [h_ty]
                have h := evalArithOp_eq .offset w₁ s₁ bits₁ bits₂ rfl
                cases s₁ <;> exact h
              | cmp =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne]
                change Except.ok
                    (Val.ordering (refOrderingOfMiri (compare lInt rInt))) =
                  Except.ok (Val.ordering (cmpOrderingOfInt lInt rInt))
                rw [refOrderingOfMiri_compare_int]
              | eq | ne | lt | le | gt | ge =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne]
                rfl
              | bitAnd =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne, miriIntValue_toUInt, miriIntValue_toUInt]
                dsimp only [Except.mapError, bind, Except.bind]
                rw [bvAnd_eq]
                exact bitwise_truncate_eq w₁ s₁ _
              | bitOr =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne, miriIntValue_toUInt, miriIntValue_toUInt]
                dsimp only [Except.mapError, bind, Except.bind]
                rw [bvOr_eq]
                exact bitwise_truncate_eq w₁ s₁ _
              | bitXor =>
                dsimp only [evalRefBinOp, evalRefMiriBinOp, evalBinOp,
                  toMiriBinOp, IntegerOps.binary]
                rw [h_ty, integerOps_decode_eq, integerOps_decode_eq]
                let ⟨lInt, h_l⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₁⟩ = x :=
                  ⟨_, rfl⟩
                let ⟨rInt, h_r⟩ : ∃ x, decodeScalar ⟨w₁, s₁, bits₂⟩ = x :=
                  ⟨_, rfl⟩
                rw [h_l, h_r]
                dsimp only [bind, Except.bind, pure, Except.pure]
                rw [h_bne, miriIntValue_toUInt, miriIntValue_toUInt]
                dsimp only [Except.mapError, bind, Except.bind]
                rw [bvXor_eq]
                exact bitwise_truncate_eq w₁ s₁ _
              | add =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .add w₁ s₁ bits₁ bits₂ rfl
              | sub =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .sub w₁ s₁ bits₁ bits₂ rfl
              | mul =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .mul w₁ s₁ bits₁ bits₂ rfl
              | addUnchecked =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .addUnchecked w₁ s₁ bits₁ bits₂ rfl
              | subUnchecked =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .subUnchecked w₁ s₁ bits₁ bits₂ rfl
              | mulUnchecked =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .mulUnchecked w₁ s₁ bits₁ bits₂ rfl
              | addWithOverflow =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .addWithOverflow w₁ s₁ bits₁ bits₂ rfl
              | subWithOverflow =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .subWithOverflow w₁ s₁ bits₁ bits₂ rfl
              | mulWithOverflow =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .mulWithOverflow w₁ s₁ bits₁ bits₂ rfl
              | div =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .div w₁ s₁ bits₁ bits₂ rfl
              | rem =>
                dsimp only [evalBinOp]
                rw [h_ty]
                exact evalArithOp_eq .rem w₁ s₁ bits₁ bits₂ rfl

theorem tryFromUInt_eq_truncateFromUInt (value : U128) (size : Size) :
    ScalarInt.tryFromUInt value size =
    bind (ScalarInt.truncateFromUInt value size)
      (fun (result, overflow) =>
        if overflow then pure none else pure (some result)) := rfl

theorem match_truncateFromUInt_eq {α : Type} (w : IntWidth) (raw : BitVec 128)
    (f : BitVec 128 → Bool → α) (d : α) :
    (match ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | .ok (sc, lossy) => f sc.data lossy
    | .error _ => d) =
    f (truncateBits w raw) (truncateBits w raw != raw) := by
  have h : (match ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | .ok (sc, lossy) => f sc.data lossy
    | .error _ => d) =
    (match (toMiriSize w).truncate raw with
    | .ok b => f b (b != raw)
    | .error _ => d) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

theorem match_tryFromUInt_eq {α : Type} (w : IntWidth) (raw : BitVec 128)
    (onSome : BitVec 128 → α) (onNone : α) :
    (match ScalarInt.tryFromUInt raw (toMiriSize w) with
    | .ok (some sc) => onSome sc.data
    | _ => onNone) =
    if truncateBits w raw != raw then onNone
    else onSome (truncateBits w raw) := by
  have h : (match ScalarInt.tryFromUInt raw (toMiriSize w) with
    | .ok (some sc) => onSome sc.data
    | _ => onNone) =
    (match ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | .ok (sc, lossy) => if lossy then onNone else onSome sc.data
    | .error _ => onNone) := by
    rw [tryFromUInt_eq_truncateFromUInt]
    cases ScalarInt.truncateFromUInt raw (toMiriSize w) with
    | error _ => rfl
    | ok pair =>
      let ⟨sc, lossy⟩ := pair
      cases lossy <;> rfl
  rw [h, match_truncateFromUInt_eq w raw
    (fun d lossy => if lossy then onNone else onSome d) onNone]

theorem match_bool_uint8_eq {α : Type} (v : UInt8)
    (onBool : Bool → α) (onInvalidBool onErr : α) :
    (match ((if v == 0 then pure false
        else if v == 1 then pure true
        else throw (ScalarIntError.invalidBool v)) :
        Except ScalarIntError Bool) with
    | .ok b => onBool b
    | .error (.invalidBool _) => onInvalidBool
    | .error _ => onErr) =
    (if v == 0 then onBool false
     else if v == 1 then onBool true
     else onInvalidBool) := by
  cases (v == 0) with
  | true => rfl
  | false => cases (v == 1) <;> rfl

theorem match_tryFromUInt_tryToBool_eq {α : Type} (raw : BitVec 128)
    (onBool : Bool → α) (onInvalidBool onErr : α) :
    (match ScalarInt.tryFromUInt raw (toMiriSize .i8) with
    | .ok (some sc) =>
      match sc.tryToBool with
      | .ok b => onBool b
      | .error (.invalidBool _) => onInvalidBool
      | .error _ => onErr
    | _ => onErr) =
    if truncateBits .i8 raw != raw then
      onErr
    else
      let v := UInt8.ofNat (truncateBits .i8 raw).toNat
      if v == 0 then onBool false
      else if v == 1 then onBool true
      else onInvalidBool := by
  have h1 : (match ScalarInt.tryFromUInt raw (toMiriSize .i8) with
    | .ok (some sc) =>
      match sc.tryToBool with
      | .ok b => onBool b
      | .error (.invalidBool _) => onInvalidBool
      | .error _ => onErr
    | _ => onErr) =
    (match ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | .ok (sc, lossy) =>
      if lossy then onErr
      else
        match sc.tryToBool with
        | .ok b => onBool b
        | .error (.invalidBool _) => onInvalidBool
        | .error _ => onErr
    | .error _ => onErr) := by
    rw [tryFromUInt_eq_truncateFromUInt]
    cases ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | error _ => rfl
    | ok pair =>
      let ⟨sc, lossy⟩ := pair
      cases lossy <;> rfl
  have h2 : (match ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | .ok (sc, lossy) =>
      if lossy then onErr
      else
        match sc.tryToBool with
        | .ok b => onBool b
        | .error (.invalidBool _) => onInvalidBool
        | .error _ => onErr
    | .error _ => onErr) =
    (match ScalarInt.truncateFromUInt raw (toMiriSize .i8) with
    | .ok (sc, lossy) =>
      if lossy then onErr
      else
        match ((let v := UInt8.ofNat sc.data.toNat
          if v == 0 then pure false
          else if v == 1 then pure true
          else throw (ScalarIntError.invalidBool v)) :
          Except ScalarIntError Bool) with
        | .ok b => onBool b
        | .error (.invalidBool _) => onInvalidBool
        | .error _ => onErr
    | .error _ => onErr) := rfl
  rw [h1, h2,
      match_truncateFromUInt_eq .i8 raw
        (fun d lossy =>
          if lossy then onErr
          else
            match ((let v := UInt8.ofNat d.toNat
              if v == 0 then pure false
              else if v == 1 then pure true
              else throw (ScalarIntError.invalidBool v)) :
              Except ScalarIntError Bool) with
            | .ok b => onBool b
            | .error (.invalidBool _) => onInvalidBool
            | .error _ => onErr)
        onErr,
      match_bool_uint8_eq]

end MiriEquiv

end Anneal.MirCorrespondence
