-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.ByteSubLens.Lens
public import Anneal.ByteSubLens.MutSummary

public section
namespace Anneal.ByteSubLens

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

/-!
# End-to-End `&mut Field` MIR Canaries & Fail-Closed Regression Suite
(`ByteSubLens.Canaries`)

Exercises `ByteSubLens` and `MutSummaryCut` end-to-end (`0` `noncomputable`, `0`
`._unsafe_rec`) over unmodified `Trusted.MirSemantics`:

1. **Symbolic `u32` Indirect Load/Store Bridges (`loadIndirect_of_extract4Init`,
   `storeIndirect_u32_eq_byteSubLensPut`):** Connects `ByteSubLens` operations
   on arbitrary `MemoryState`s to `Trusted.MirSemantics.loadIndirect` and
   `Trusted.MirSemantics.storeIndirect`.
2. **Symbolic Callee Realizations & `@[irreducible]` Sealing:**
   - `progMutFieldAddAssignU32` (`*field = (*field).wrapping_add(delta)`):
     `seal_addAssignU32_summaryCut`.
   - `progMutSlotMintIfEmptyU32` (3-block `switchInt` conditional write
     `if *slot == 0 { *slot = cap; 1 } else { 0 }`):
     `seal_slotMintIfEmptyU32_summaryCut`.
3. **5-Call Multi-Slot CNode Chain (`cnodeSummaryChain_certified`):** Evaluates
   5 chained `&mut` method calls across a 24-byte mutable allocation by `rfl`
   without unfolding either callee MIR body, deriving `MirCalleeChainRunsTo` and
   disjoint sibling framing via `execMutSummaryChain_certified_sound`.
4. **Fail-Closed Negative Suite (`overlappingByteLensRefutesFrame`,
   `canary_bytesublens_negative_fail_closed_tests`):** Formal `→ False`
   refutation of frame preservation on overlapping lenses plus 9 single-cause
   boundary rejection checks.
-/

/-! ## 1. Symbolic `u32` Codec & `loadIndirect` / `storeIndirect` Bridges -/

private theorem cn_boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem cn_ite_bool_true {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

private theorem cn_ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

private theorem cn_natEq_of_beq (a b : Nat) (h : Nat.beq a b = true) :
    a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (cn_boolFalseNeTrue h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (cn_boolFalseNeTrue h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

private theorem cn_natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem cn_natAdd_zero_left (a : Nat) : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem cn_natAdd_succ_left (a b : Nat) : (a + 1) + b = (a + b) + 1 := by
  induction b with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem cn_natAdd_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => exact cn_natAdd_zero_left b
  | succ a' ih =>
    exact Eq.trans (cn_natAdd_succ_left a' b) (congrArg Nat.succ ih)

private theorem cn_natAdd_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

/-- Unsigned 32-bit MIR scalar type `.int .i32 false`. -/
@[expose] def u32MirTy : MirTy := .int .i32 false

/-- Computable `u32` scalar `Val` constructor (`0` `noncomputable`). -/
@[expose] def mkU32Val (n : Nat) : Val :=
  .scalar ⟨.i32, false, truncateBitsComp .i32 (BitVec.ofNat 128 n)⟩

private theorem bitVec_toNat_ofNat (w x : Nat) :
    (BitVec.ofNat w x).toNat = Nat.mod x (Nat.pow 2 w) := rfl

private theorem bitVec_eq_of_toNat_eq {n : Nat} {a b : BitVec n}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb => exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

private theorem toNat_truncateBits_i32 (x : BitVec 128) :
    (truncateBits .i32 x).toNat = (bvExtractLsb 31 0 x).toNat := by
  dsimp only [truncateBits, IntWidth.bitWidth, bvZeroExtend]
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le (bvExtractLsb 31 0 x).isLt (Nat.le_of_ble_eq_true rfl))

private theorem natMod_eq_of_lt (a b : Nat) (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem truncateBits_i32_idem (x : BitVec 128) :
    truncateBits .i32 (truncateBits .i32 x) = truncateBits .i32 x := by
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits_i32, toNat_truncateBits_i32]
  dsimp only [bvExtractLsb, bvExtractLsb', Nat.shiftRight]
  rw [toNat_truncateBits_i32]
  dsimp only [bvExtractLsb, bvExtractLsb', Nat.shiftRight]
  rw [bitVec_toNat_ofNat]
  exact natMod_eq_of_lt _ _ (Nat.mod_lt x.toNat (Nat.le_of_ble_eq_true rfl))

private theorem truncateBits_i32_of_lt (v : Nat)
    (hLt : Nat.blt v 4294967296 = true) :
    truncateBits .i32 (BitVec.ofNat 128 v) = BitVec.ofNat 128 v := by
  have hV32 : v < Nat.pow 2 32 := Nat.le_of_ble_eq_true hLt
  have hV128 : v < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hV32 (Nat.le_of_ble_eq_true rfl)
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits_i32]
  dsimp only [bvExtractLsb, bvExtractLsb', Nat.shiftRight]
  rw [bitVec_toNat_ofNat, bitVec_toNat_ofNat,
      natMod_eq_of_lt v _ hV128, natMod_eq_of_lt v _ hV32]

private theorem scalarVal_wf_u32 (bits : BitVec 128)
    (hTrunc : truncateBits .i32 bits = bits) :
    ScalarVal.wf ⟨.i32, false, bits⟩ = true := by
  dsimp only [ScalarVal.wf]
  rw [hTrunc]
  exact beq_self_eq_true bits

private theorem checkVal_u32_of_trunc (bits : BitVec 128)
    (hTrunc : truncateBits .i32 bits = bits) :
    checkVal (.scalar ⟨.i32, false, bits⟩) (.int .i32 false) = true := by
  dsimp only [checkVal, Val.ty?]
  rw [cn_ite_bool_true (scalarVal_wf_u32 bits hTrunc)]
  rfl

private theorem band_false_right (b : Bool) : (b && false) = false := by
  cases b <;> rfl

private theorem evalArithOp_add_u32 (l r : Int) :
    evalArithOp .add .i32 false l r =
      .ok (.scalar ⟨.i32, false, truncateBits .i32 (bvOfInt 128 (l + r))⟩) := by
  dsimp only [evalArithOp, truncateScalar]
  rw [cn_ite_bool_false (rfl : ((false : Bool) && (r == 0)) = false),
      cn_ite_bool_false
        (rfl : ((false : Bool) && false &&
          (l == signedMinInt .i32 && r == Neg.neg 1)) = false),
      cn_ite_bool_false (rfl : (false : Bool) = false)]
  dsimp only
  have hUnchk : ∀ b : Bool, (b && BinOp.isUnchecked .add) = false :=
    band_false_right
  rw [cn_ite_bool_false (hUnchk _),
      cn_ite_bool_false (rfl : BinOp.isOverflowing .add = false)]

private theorem evalBinOp_add_u32 (b1 b2 : BitVec 128) :
    evalBinOp .add (.scalar ⟨.i32, false, b1⟩) (.scalar ⟨.i32, false, b2⟩) =
      .ok (.scalar ⟨.i32, false,
        truncateBits .i32 (bvOfInt 128
          (Int.ofNat (truncateBits .i32 b1).toNat +
            Int.ofNat (truncateBits .i32 b2).toNat))⟩) := by
  dsimp only [evalBinOp, decodeScalar]
  rw [cn_ite_bool_false (rfl : BinOp.isShift .add = false),
      cn_ite_bool_false
        (rfl : (!(IntWidth.beq .i32 .i32 && (false == false))) = false),
      cn_ite_bool_false (rfl : (false : Bool) = false)]
  exact evalArithOp_add_u32 _ _

private theorem evalBinOp_eq_u32 (b1 b2 : BitVec 128) :
    evalBinOp .eq (.scalar ⟨.i32, false, b1⟩) (.scalar ⟨.i32, false, b2⟩) =
      .ok (.bool (Int.ofNat (truncateBits .i32 b1).toNat ==
        Int.ofNat (truncateBits .i32 b2).toNat)) := by
  dsimp only [evalBinOp, decodeScalar]
  rw [cn_ite_bool_false (rfl : BinOp.isShift .eq = false),
      cn_ite_bool_false
        (rfl : (!(IntWidth.beq .i32 .i32 && (false == false))) = false),
      cn_ite_bool_false (rfl : (false : Bool) = false)]
  rfl

private theorem byteStepBound (b acc m : Nat) (hb : b < 256) (hAcc : acc < m) :
    b + 256 * acc < 256 * m := by
  have h1 : b + 1 ≤ 256 := hb
  have h2 : acc + 1 ≤ m := hAcc
  have h3 : 256 * (acc + 1) ≤ 256 * m := Nat.mul_le_mul_left 256 h2
  rw [Nat.mul_add, Nat.mul_one] at h3
  have h4 : (b + 1) + 256 * acc ≤ 256 + 256 * acc :=
    Nat.add_le_add_right h1 (256 * acc)
  rw [cn_natAdd_comm 256 (256 * acc)] at h4
  have h5 : (b + 256 * acc) + 1 = (b + 1) + 256 * acc := by
    rw [cn_natAdd_assoc b 1 (256 * acc), cn_natAdd_comm 1 (256 * acc),
        ← cn_natAdd_assoc b (256 * acc) 1]
  rw [← h5] at h4
  exact Nat.le_trans h4 h3

private theorem decodeUInt_big_4_lt (b3 b2 b1 b0 : UInt8) :
    Nat.blt (decodeUInt .big [b3, b2, b1, b0]) 4294967296 = true := by
  dsimp only [decodeUInt, List.reverse, List.reverseAux, natOfLeBytes]
  have h0 : 0 < 1 := Nat.le_of_ble_eq_true rfl
  have s1 := byteStepBound b3.toNat 0 1 b3.toBitVec.isLt h0
  have s2 :=
    byteStepBound b2.toNat (b3.toNat + 256 * 0) 256 b2.toBitVec.isLt s1
  have s3 := byteStepBound b1.toNat
    (b2.toNat + 256 * (b3.toNat + 256 * 0)) 65536 b1.toBitVec.isLt s2
  have s4 := byteStepBound b0.toNat
    (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 * 0))) 16777216
    b0.toBitVec.isLt s3
  exact Nat.ble_eq_true_of_le s4

/-- Encodes `v : Nat` as 4 big-endian initialized `AllocByte`s (`0`
`noncomputable`, matching `profileTargetEndian = .big`). -/
@[expose] def encodeU32BeSlice (v : Nat) : List AllocByte :=
  List.foldr (fun b acc => AllocByte.init b none :: acc) []
    (encodeUIntComp .big 4 v)

private theorem foldr_init_eq_map (bs : List UInt8) :
    List.foldr (fun b acc => AllocByte.init b none :: acc) [] bs =
      bs.map (fun b => AllocByte.init b none) := by
  induction bs with
  | nil => rfl
  | cons b tl ih => exact congrArg (List.cons (AllocByte.init b none)) ih

/-- Exact length `(encodeU32BeSlice v).length = 4`. -/
theorem encodeU32BeSlice_length (v : Nat) :
    (encodeU32BeSlice v).length = 4 := rfl

/-- Extracts 4 initialized bytes `(b3, b2, b1, b0)` from a 4-byte `AllocByte`
slice, returning `none` if any byte is `.uninit` or length ≠ 4. -/
@[expose] def extract4InitBytes (bs : List AllocByte) :
    Option (UInt8 × UInt8 × UInt8 × UInt8) :=
  match bs with
  | [] => none
  | x3 :: r3 =>
    match x3 with
    | .uninit => none
    | .init b3 _ =>
      match r3 with
      | [] => none
      | x2 :: r2 =>
        match x2 with
        | .uninit => none
        | .init b2 _ =>
          match r2 with
          | [] => none
          | x1 :: r1 =>
            match x1 with
            | .uninit => none
            | .init b1 _ =>
              match r1 with
              | [] => none
              | x0 :: r0 =>
                match x0 with
                | .uninit => none
                | .init b0 _ =>
                  match r0 with
                  | [] => some (b3, b2, b1, b0)
                  | _ :: _ => none

/-- Extracts a single well-formed unsigned 32-bit `Val` argument (`0`
`noncomputable`). -/
@[expose] def extractSingleU32Arg (args : List Val) : Option (BitVec 128) :=
  match args with
  | [] => none
  | a0 :: rest =>
    match rest with
    | _ :: _ => none
    | [] =>
      match a0 with
      | .scalar sv =>
        match sv.width with
        | .i32 =>
          match sv.signed with
          | false =>
            if Nat.beq (truncateBitsComp .i32 sv.bits).toNat sv.bits.toNat then
              some sv.bits
            else none
          | true => none
        | .i8 | .i16 | .i64 | .i128 | .isize => none
      | .ptr _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _
      | .bool _ | .char _ | .ordering _ | .unit
      | .enumVal _ _ | .tuple _ | .bytes _ => none

private theorem extractSingleU32Arg_inv (args : List Val) (dBits : BitVec 128)
    (h : extractSingleU32Arg args = some dBits) :
    args = [.scalar ⟨.i32, false, dBits⟩] ∧ truncateBits .i32 dBits = dBits := by
  cases args with
  | nil => nomatch h
  | cons a0 rest =>
    cases rest with
    | cons _ _ => nomatch h
    | nil =>
      cases a0 with
      | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
      | bool _ | char _ | ordering _ | unit | enumVal _ _
      | tuple _ | bytes _ => nomatch h
      | scalar sv =>
        cases sv with
        | mk w s b =>
          cases w with
          | i8 | i16 | i64 | i128 | isize => nomatch h
          | i32 =>
            cases s with
            | true => nomatch h
            | false =>
              dsimp only [extractSingleU32Arg] at h
              cases hEq : Nat.beq (truncateBitsComp .i32 b).toNat b.toNat with
              | false => rw [cn_ite_bool_false hEq] at h; nomatch h
              | true =>
                rw [cn_ite_bool_true hEq] at h
                injection h with hb
                subst hb
                rw [truncateBitsComp_eq] at hEq
                exact ⟨rfl, bitVec_eq_of_toNat_eq (cn_natEq_of_beq _ _ hEq)⟩

/-- Symbolic bridge: any 4-byte initialized `ByteSubLens` slice loads as the
exact decoded `u32` `Val` under `Trusted.MirSemantics.loadIndirect`. -/
theorem loadIndirect_of_extract4Init (subL : ByteSubLens) (mem : MemoryState)
    (oldSlice : List AllocByte) (b3 b2 b1 b0 : UInt8)
    (hSz : subL.size = 4) (hAl : subL.alignLog2 = 2)
    (hGet : byteSubLensGet subL mem = some oldSlice)
    (hExt : extract4InitBytes oldSlice = some (b3, b2, b1, b0)) :
    loadIndirect mem u32MirTy ⟨subL.allocId, subL.offset⟩ =
      .ok (some (.scalar ⟨.i32, false,
        BitVec.ofNat 128 (decodeUInt .big [b3, b2, b1, b0])⟩)) := by
  have hInit : initBytes? oldSlice = some [b3, b2, b1, b0] ∧
      oldSlice.length = 4 := by
    cases oldSlice with
    | nil => nomatch hExt
    | cons x3 r3 =>
      cases x3 with
      | uninit => nomatch hExt
      | init c3 p3 =>
        cases r3 with
        | nil => nomatch hExt
        | cons x2 r2 =>
          cases x2 with
          | uninit => nomatch hExt
          | init c2 p2 =>
            cases r2 with
            | nil => nomatch hExt
            | cons x1 r1 =>
              cases x1 with
              | uninit => nomatch hExt
              | init c1 p1 =>
                cases r1 with
                | nil => nomatch hExt
                | cons x0 r0 =>
                  cases x0 with
                  | uninit => nomatch hExt
                  | init c0 p0 =>
                    cases r0 with
                    | cons _ _ => nomatch hExt
                    | nil =>
                      injection hExt with hTuple
                      have e3 : c3 = b3 := congrArg Prod.fst hTuple
                      have t1 := congrArg Prod.snd hTuple
                      have e2 : c2 = b2 := congrArg Prod.fst t1
                      have t2 := congrArg Prod.snd t1
                      have e1 : c1 = b1 := congrArg Prod.fst t2
                      have e0 : c0 = b0 := congrArg Prod.snd t2
                      subst e3; subst e2; subst e1; subst e0
                      exact ⟨rfl, rfl⟩
  rw [byteSubLensGet_eq_mir, hSz, hAl] at hGet
  dsimp only [Nat.blt, Nat.ble] at hGet
  cases hFind : findAllocation subL.allocId mem.allocations with
  | none => rw [hFind] at hGet; nomatch hGet
  | some a =>
    rw [hFind] at hGet
    dsimp only at hGet
    cases hMut : mutabilityIsMut a.mutability with
    | false => rw [hMut] at hGet; nomatch hGet
    | true =>
      rw [hMut] at hGet
      dsimp only at hGet
      dsimp only [loadIndirect, u32MirTy, layoutOfTy, intLayout]
      cases hRB : readBytes mem ⟨subL.allocId, subL.offset⟩ 4 2 with
      | error _ => rw [hRB] at hGet; nomatch hGet
      | ok rbs =>
        rw [hRB] at hGet
        injection hGet with hRbs
        subst hRbs
        dsimp only [decodeVal, layoutOfTy, intLayout]
        rw [hInit.2, cn_ite_bool_false (rfl : (!Nat.beq 4 4) = false),
            cn_ite_bool_false (rfl : Nat.beq 4 0 = false), hInit.1]
        dsimp only [profileTargetEndian, evalConstLit]
        have hTrunc := truncateBits_i32_of_lt (decodeUInt .big [b3, b2, b1, b0])
          (decodeUInt_big_4_lt b3 b2 b1 b0)
        rw [hTrunc]
        have hBne : (BitVec.ofNat 128 (decodeUInt .big [b3, b2, b1, b0]) !=
            BitVec.ofNat 128 (decodeUInt .big [b3, b2, b1, b0])) = false := by
          dsimp only [bne]
          rw [beq_self_eq_true]
          rfl
        rw [cn_ite_bool_false hBne]

/-- Symbolic bridge: `Trusted.MirSemantics.storeIndirect` on an aligned 4-byte
`ByteSubLens` matches `byteSubLensPut` of `encodeU32BeSlice bits.toNat`. -/
theorem storeIndirect_u32_eq_byteSubLensPut (subL : ByteSubLens)
    (mem : MemoryState) (bits : BitVec 128)
    (hSz : subL.size = 4) (hAl : subL.alignLog2 = 2)
    (hTrunc : truncateBits .i32 bits = bits)
    (oldSlice : List AllocByte)
    (hGet : byteSubLensGet subL mem = some oldSlice) :
    ∃ memOut : MemoryState,
      storeIndirect mem u32MirTy ⟨subL.allocId, subL.offset⟩
        (.scalar ⟨.i32, false, bits⟩) = .ok memOut ∧
      byteSubLensPut subL mem (encodeU32BeSlice bits.toNat) = some memOut := by
  have hLenSlice : (encodeU32BeSlice bits.toNat).length = subL.size := by
    rw [encodeU32BeSlice_length, hSz]
  cases byteSubLens_put_succeeds_of_get subL mem oldSlice
      (encodeU32BeSlice bits.toNat) hGet hLenSlice with
  | intro memOut hPut =>
    refine ⟨memOut, ?_, hPut⟩
    have hPutMir := hPut
    rw [byteSubLensPut_eq_mir, hSz, hAl] at hPutMir
    dsimp only [encodeU32BeSlice_length, Nat.blt, Nat.ble, Nat.beq,
      Bool.and] at hPutMir
    have hWf : checkVal (.scalar ⟨.i32, false, bits⟩) (.int .i32 false) =
        true := checkVal_u32_of_trunc bits hTrunc
    have hNotWf :
        (!checkVal (.scalar ⟨.i32, false, bits⟩) (.int .i32 false)) = false := by
      rw [hWf]; rfl
    dsimp only [storeIndirect, u32MirTy, layoutOfTy, intLayout, encodeVal]
    rw [cn_ite_bool_false hNotWf]
    dsimp only [profileTargetEndian, IntWidth.byteSize]
    have hEncEq :
        (encodeUInt .big 4 bits.toNat).map (fun b => AllocByte.init b none) =
        encodeU32BeSlice bits.toNat := by
      dsimp only [encodeU32BeSlice]
      rw [foldr_init_eq_map, encodeUIntComp_eq]
    rw [hEncEq]
    cases hW : writeBytes mem ⟨subL.allocId, subL.offset⟩ 2
        (encodeU32BeSlice bits.toNat) with
    | error _ => rw [hW] at hPutMir; nomatch hPutMir
    | ok m' =>
      rw [hW] at hPutMir
      injection hPutMir with hEq
      subst hEq
      rfl

/-! ## 2. Symbolic Callee Realizations & `@[irreducible] MutSummaryCut`s -/

/-- Concrete `&mut Field` MIR program (`0` `noncomputable`):
`*field = (*field).wrapping_add(delta); return *field`. -/
@[expose] def progMutFieldAddAssignU32 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  scope := .unit
  bodies := [{
    argumentCount := 2
    locals := [u32MirTy, u32MirTy, u32MirTy]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)),
        .assign ⟨1, []⟩ (.use (.copy ⟨0, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Computable `MutFieldCallSummary` for `progMutFieldAddAssignU32` (`0`
`noncomputable`). -/
@[expose] def fieldAddAssignSummary : MutFieldCallSummary where
  retTy := u32MirTy
  fieldSize := 4
  alignLog2 := 2
  tempTys := []
  summaryFn := fun oldSlice extraArgs =>
    match extract4InitBytes oldSlice with
    | none => none
    | some (b3, b2, b1, b0) =>
      match extractSingleU32Arg extraArgs with
      | none => none
      | some dBits =>
        let vOld := decodeUIntComp .big [b3, b2, b1, b0]
        let sumBits :=
          truncateBitsComp .i32
            (bvOfIntComp 128 (Int.ofNat (vOld + dBits.toNat)))
        some (encodeU32BeSlice sumBits.toNat, .scalar ⟨.i32, false, sumBits⟩)

/-- Symbolic proof across all `MemoryState`s, all aligned 4-byte `ByteSubLens`
targets, all initialized 4-byte slices, and all `u32` deltas that
`progMutFieldAddAssignU32` realizes `fieldAddAssignSummary` via
`Trusted.MirSemantics.evalStep`. -/
theorem progMutFieldAddAssignU32_realizes_summary :
    CalleeRealizesSummary progMutFieldAddAssignU32 3 fieldAddAssignSummary := by
  intro subL mem oldSlice newSlice extraArgs retVal hSz hAl hGet hSum
  dsimp only [fieldAddAssignSummary] at hSum
  cases hExtB : extract4InitBytes oldSlice with
  | none => rw [hExtB] at hSum; nomatch hSum
  | some quad =>
    rw [hExtB] at hSum
    cases hExtA : extractSingleU32Arg extraArgs with
    | none => rw [hExtA] at hSum; nomatch hSum
    | some dBits =>
      rw [hExtA] at hSum
      cases quad with
      | mk b3 p210 =>
        cases p210 with
        | mk b2 p10 =>
          cases p10 with
          | mk b1 b0 =>
            dsimp only at hSum
            injection hSum with hPair
            rw [decodeUIntComp_eq, truncateBitsComp_eq,
                bvOfIntComp_eq] at hPair
            let vOld := decodeUInt .big [b3, b2, b1, b0]
            let sumBits :=
              truncateBits .i32 (bvOfInt 128 (Int.ofNat (vOld + dBits.toNat)))
            have hNewEq : newSlice = encodeU32BeSlice sumBits.toNat :=
              (congrArg Prod.fst hPair).symm
            have hRetEq : retVal = .scalar ⟨.i32, false, sumBits⟩ :=
              (congrArg Prod.snd hPair).symm
            subst hNewEq; subst hRetEq
            have hArgInv := extractSingleU32Arg_inv extraArgs dBits hExtA
            rw [hArgInv.1]
            have hLoad := loadIndirect_of_extract4Init subL mem oldSlice
              b3 b2 b1 b0 hSz hAl hGet hExtB
            have hTruncOld := truncateBits_i32_of_lt vOld
              (decodeUInt_big_4_lt b3 b2 b1 b0)
            have hOldToNat : (BitVec.ofNat 128 vOld).toNat = vOld := by
              rw [bitVec_toNat_ofNat]
              exact natMod_eq_of_lt vOld _
                (Nat.lt_of_lt_of_le
                  (Nat.le_of_ble_eq_true (decodeUInt_big_4_lt b3 b2 b1 b0))
                  (Nat.le_of_ble_eq_true rfl))
            have hSumTrunc : truncateBits .i32 sumBits = sumBits :=
              truncateBits_i32_idem _
            have hSumWf :
                checkVal (.scalar ⟨.i32, false, sumBits⟩) (.int .i32 false) =
                true := checkVal_u32_of_trunc sumBits hSumTrunc
            have hNotSumWf :
                (!checkVal (.scalar ⟨.i32, false, sumBits⟩)
                  (.int .i32 false)) = false := by
              rw [hSumWf]; rfl
            have hProjEmpty :
                (!List.isEmpty ([] : List ProjectionElem)) = false := rfl
            have hPrimU32 :
                (!isPrimitiveReadableTy (.int .i32 false)) = false := rfl
            cases storeIndirect_u32_eq_byteSubLensPut subL mem sumBits hSz hAl
                hSumTrunc oldSlice hGet with
            | intro memOut hStore =>
              refine ⟨memOut, ?_, hStore.2⟩
              dsimp only [fieldAddAssignSummary, initSuballocCalleeState,
                List.foldr, HAppend.hAppend, Append.append, List.append,
                liveUninitSlotComp]
              rw [mirCalleeRunsTo_succ]
              dsimp only [evalStep, activeFrameBody, attachCallers,
                List.append, HAppend.hAppend, Append.append,
                progMutFieldAddAssignU32, u32MirTy,
                Trusted.MirSemantics.getElem?, evalStatement, evalRvalue,
                evalPrimitiveOperand, evalOperandToSlot]
              rw [cn_ite_bool_false hProjEmpty,
                  cn_ite_bool_false hProjEmpty, cn_ite_bool_false hPrimU32]
              have hLoad' :
                  loadIndirect mem (.int .i32 false)
                    ⟨subL.allocId, subL.offset⟩ =
                  .ok (some (.scalar ⟨.i32, false, BitVec.ofNat 128 vOld⟩)) :=
                hLoad
              rw [hLoad']
              dsimp only
              rw [cn_ite_bool_false hPrimU32]
              dsimp only [Trusted.MirSemantics.getElem?]
              rw [cn_ite_bool_false hProjEmpty]
              dsimp only
              rw [cn_ite_bool_false hPrimU32]
              dsimp only
              rw [evalBinOp_add_u32, hTruncOld, hOldToNat, hArgInv.2]
              have hIntAdd :
                  (Int.ofNat vOld + Int.ofNat dBits.toNat) =
                  Int.ofNat (vOld + dBits.toNat) := rfl
              rw [hIntAdd]
              dsimp only [writePlace, Trusted.MirSemantics.getElem?]
              rw [cn_ite_bool_false hNotSumWf]
              dsimp only [Trusted.MirSemantics.setElem?]
              rw [mirCalleeRunsTo_succ]
              dsimp only [evalStep, activeFrameBody, attachCallers,
                List.append, HAppend.hAppend, Append.append,
                progMutFieldAddAssignU32, u32MirTy,
                Trusted.MirSemantics.getElem?, evalStatement, evalRvalue,
                evalOperandToSlot, writePlace]
              rw [cn_ite_bool_false hProjEmpty, cn_ite_bool_false hProjEmpty]
              dsimp only
              rw [cn_ite_bool_false
                (rfl : (!MirTy.beq (.int .i32 false) (.int .i32 false)) =
                  false)]
              dsimp only
              rw [cn_ite_bool_false hNotSumWf]
              dsimp only [Trusted.MirSemantics.getElem?]
              have hStore1 :
                  storeIndirect mem (.int .i32 false)
                    ⟨subL.allocId, subL.offset⟩
                    (.scalar ⟨.i32, false, sumBits⟩) = .ok memOut := hStore.1
              rw [hStore1]
              dsimp only
              rw [mirCalleeRunsTo_succ]
              exact ⟨rfl, rfl⟩

/-- Sealed `@[irreducible] MutSummaryCut` certificate for
`progMutFieldAddAssignU32`. -/
theorem seal_addAssignU32_summaryCut :
    MutSummaryCut progMutFieldAddAssignU32 3 fieldAddAssignSummary :=
  seal_mutSummaryCut progMutFieldAddAssignU32_realizes_summary

/-- Multi-block branching `&mut slots[i]` MIR program (`0` `noncomputable`):
`if *slot == 0u32 { *slot = cap; return 1u32 } else { return 0u32 }`. -/
@[expose] def progMutSlotMintIfEmptyU32 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  scope := .unit
  bodies := [{
    argumentCount := 2
    locals := [u32MirTy, u32MirTy, u32MirTy, .bool]
    basicBlocks := [
      { statements := [
          .assign ⟨3, []⟩ (.binaryOp .eq (.copy ⟨1, []⟩)
            (.constant ⟨u32MirTy, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator :=
          .switchInt (.move ⟨3, []⟩) ⟨[(BitVec.ofNat 128 0, 2)], 1⟩ },
      { statements := [
          .assign ⟨1, []⟩ (.use (.copy ⟨2, []⟩)),
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32MirTy, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_ },
      { statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32MirTy, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_ }
    ]
  }]

/-- Computable `MutFieldCallSummary` for `progMutSlotMintIfEmptyU32` (`0`
`noncomputable`). -/
@[expose] def slotMintIfEmptySummary : MutFieldCallSummary where
  retTy := u32MirTy
  fieldSize := 4
  alignLog2 := 2
  tempTys := [.bool]
  summaryFn := fun oldSlice extraArgs =>
    match extract4InitBytes oldSlice with
    | none => none
    | some (b3, b2, b1, b0) =>
      match extractSingleU32Arg extraArgs with
      | none => none
      | some capBits =>
        let vOld := decodeUIntComp .big [b3, b2, b1, b0]
        if Nat.beq vOld 0 then
          some (encodeU32BeSlice capBits.toNat, mkU32Val 1)
        else
          some (oldSlice, mkU32Val 0)

/-- Symbolic proof across all `MemoryState`s, all aligned 4-byte `ByteSubLens`
targets, all initialized 4-byte slices, and all `u32` capability values that
`progMutSlotMintIfEmptyU32` realizes `slotMintIfEmptySummary`. -/
theorem progMutSlotMintIfEmptyU32_realizes_summary :
    CalleeRealizesSummary progMutSlotMintIfEmptyU32 5 slotMintIfEmptySummary := by
  intro subL mem oldSlice newSlice extraArgs retVal hSz hAl hGet hSum
  dsimp only [slotMintIfEmptySummary] at hSum
  cases hExtB : extract4InitBytes oldSlice with
  | none => rw [hExtB] at hSum; nomatch hSum
  | some quad =>
    rw [hExtB] at hSum
    cases hExtA : extractSingleU32Arg extraArgs with
    | none => rw [hExtA] at hSum; nomatch hSum
    | some capBits =>
      rw [hExtA] at hSum
      cases quad with
      | mk b3 p210 =>
        cases p210 with
        | mk b2 p10 =>
          cases p10 with
          | mk b1 b0 =>
            dsimp only at hSum
            rw [decodeUIntComp_eq] at hSum
            have hArgInv := extractSingleU32Arg_inv extraArgs capBits hExtA
            rw [hArgInv.1]
            have hLoad := loadIndirect_of_extract4Init subL mem oldSlice
              b3 b2 b1 b0 hSz hAl hGet hExtB
            let vOld := decodeUInt .big [b3, b2, b1, b0]
            have hLoad' :
                loadIndirect mem (.int .i32 false)
                  ⟨subL.allocId, subL.offset⟩ =
                .ok (some (.scalar ⟨.i32, false, BitVec.ofNat 128 vOld⟩)) :=
              hLoad
            have hTruncOld := truncateBits_i32_of_lt vOld
              (decodeUInt_big_4_lt b3 b2 b1 b0)
            have hOldToNat : (BitVec.ofNat 128 vOld).toNat = vOld := by
              rw [bitVec_toNat_ofNat]
              exact natMod_eq_of_lt vOld _
                (Nat.lt_of_lt_of_le
                  (Nat.le_of_ble_eq_true (decodeUInt_big_4_lt b3 b2 b1 b0))
                  (Nat.le_of_ble_eq_true rfl))
            have hIntEqBool :
                (Int.ofNat vOld == Int.ofNat 0) = Nat.beq vOld 0 := by
              cases vOld <;> rfl
            have hProjEmpty :
                (!List.isEmpty ([] : List ProjectionElem)) = false := rfl
            have hPrimU32 :
                (!isPrimitiveReadableTy (.int .i32 false)) = false := rfl
            have hZeroConstBne :
                (truncateBits .i32 (BitVec.ofNat 128 0) !=
                  BitVec.ofNat 128 0) = false := by
              rw [truncateBits_i32_of_lt 0 rfl]; rfl
            cases hZero : Nat.beq vOld 0 with
            | true =>
              rw [cn_ite_bool_true hZero] at hSum
              injection hSum with hPair
              have hNewEq : newSlice = encodeU32BeSlice capBits.toNat :=
                (congrArg Prod.fst hPair).symm
              have hRetEq : retVal = mkU32Val 1 :=
                (congrArg Prod.snd hPair).symm
              rw [hNewEq, hRetEq]
              have hCapWf :
                  checkVal (.scalar ⟨.i32, false, capBits⟩) (.int .i32 false) =
                  true := checkVal_u32_of_trunc capBits hArgInv.2
              have hNotCapWf :
                  (!checkVal (.scalar ⟨.i32, false, capBits⟩)
                    (.int .i32 false)) = false := by
                rw [hCapWf]; rfl
              cases storeIndirect_u32_eq_byteSubLensPut subL mem capBits hSz
                  hAl hArgInv.2 oldSlice hGet with
              | intro memOut hStore =>
                refine ⟨memOut, ?_, hStore.2⟩
                dsimp only [slotMintIfEmptySummary, initSuballocCalleeState,
                  List.foldr, HAppend.hAppend, Append.append, List.append,
                  liveUninitSlotComp]
                rw [mirCalleeRunsTo_succ]
                dsimp only [evalStep, activeFrameBody, attachCallers,
                  progMutSlotMintIfEmptyU32, u32MirTy,
                  Trusted.MirSemantics.getElem?, evalStatement, evalRvalue,
                  evalPrimitiveOperand, evalOperandToSlot, evalConstLit]
                rw [cn_ite_bool_false hProjEmpty,
                    cn_ite_bool_false hProjEmpty, cn_ite_bool_false hPrimU32,
                    hLoad']
                dsimp only
                rw [cn_ite_bool_false hPrimU32]
                dsimp only
                rw [cn_ite_bool_false hZeroConstBne]
                dsimp only
                rw [cn_ite_bool_false hPrimU32]
                dsimp only
                rw [evalBinOp_eq_u32, hTruncOld, hOldToNat,
                    truncateBits_i32_of_lt 0 rfl, truncateBits_i32_of_lt 0 rfl]
                have hZeroToNat : (BitVec.ofNat 128 0).toNat = 0 := rfl
                rw [hZeroToNat, hIntEqBool]
                dsimp only [writePlace, Trusted.MirSemantics.getElem?]
                rw [cn_ite_bool_false
                    (rfl : (!checkVal (.bool (Nat.beq vOld 0)) .bool) = false),
                    hZero]
                dsimp only [Trusted.MirSemantics.setElem?]
                change MirCalleeRunsTo progMutSlotMintIfEmptyU32 memOut
                  (mkU32Val 1) 3
                  { frames := [{
                      defId := 0, blockIdx := 1, stmtIdx := 0,
                      locals := [
                        .immediate none,
                        .indirect ⟨subL.allocId, subL.offset⟩,
                        .immediate (some (.scalar ⟨.i32, false, capBits⟩)),
                        .immediate none
                      ] }]
                    callerMem := ⟨[]⟩
                    mem := mem }
                rw [mirCalleeRunsTo_succ]
                dsimp only [evalStep, activeFrameBody, attachCallers,
                  progMutSlotMintIfEmptyU32, u32MirTy,
                  Trusted.MirSemantics.getElem?, evalStatement, evalRvalue,
                  evalOperandToSlot, writePlace]
                rw [cn_ite_bool_false hProjEmpty, cn_ite_bool_false hProjEmpty]
                dsimp only
                rw [cn_ite_bool_false
                  (rfl : (!MirTy.beq (.int .i32 false) (.int .i32 false)) =
                    false)]
                dsimp only
                rw [cn_ite_bool_false hNotCapWf]
                dsimp only [Trusted.MirSemantics.getElem?]
                have hStore1 :
                    storeIndirect mem (.int .i32 false)
                      ⟨subL.allocId, subL.offset⟩
                      (.scalar ⟨.i32, false, capBits⟩) = .ok memOut := hStore.1
                rw [hStore1]
                dsimp only
                exact ⟨rfl, rfl⟩
            | false =>
              rw [cn_ite_bool_false hZero] at hSum
              injection hSum with hPair
              have hNewEq : newSlice = oldSlice :=
                (congrArg Prod.fst hPair).symm
              have hRetEq : retVal = mkU32Val 0 :=
                (congrArg Prod.snd hPair).symm
              rw [hNewEq, hRetEq]
              refine ⟨mem, ?_, byteSubLens_get_put subL mem oldSlice hGet⟩
              dsimp only [slotMintIfEmptySummary, initSuballocCalleeState,
                List.foldr, HAppend.hAppend, Append.append, List.append,
                liveUninitSlotComp]
              rw [mirCalleeRunsTo_succ]
              dsimp only [evalStep, activeFrameBody, attachCallers,
                List.append, HAppend.hAppend, Append.append,
                progMutSlotMintIfEmptyU32, u32MirTy,
                Trusted.MirSemantics.getElem?, evalStatement, evalRvalue,
                evalPrimitiveOperand, evalOperandToSlot, evalConstLit]
              rw [cn_ite_bool_false hProjEmpty,
                  cn_ite_bool_false hProjEmpty, cn_ite_bool_false hPrimU32,
                  hLoad']
              dsimp only
              rw [cn_ite_bool_false hPrimU32]
              dsimp only
              rw [cn_ite_bool_false hZeroConstBne]
              dsimp only
              rw [cn_ite_bool_false hPrimU32]
              dsimp only
              rw [evalBinOp_eq_u32, hTruncOld, hOldToNat,
                  truncateBits_i32_of_lt 0 rfl, truncateBits_i32_of_lt 0 rfl]
              have hZeroToNat : (BitVec.ofNat 128 0).toNat = 0 := rfl
              rw [hZeroToNat, hIntEqBool]
              dsimp only [writePlace, Trusted.MirSemantics.getElem?]
              rw [cn_ite_bool_false
                  (rfl : (!checkVal (.bool (Nat.beq vOld 0)) .bool) = false),
                  hZero]
              dsimp only [Trusted.MirSemantics.setElem?]
              exact ⟨rfl, rfl⟩

/-- Sealed `@[irreducible] MutSummaryCut` certificate for
`progMutSlotMintIfEmptyU32`. -/
theorem seal_slotMintIfEmptyU32_summaryCut :
    MutSummaryCut progMutSlotMintIfEmptyU32 5 slotMintIfEmptySummary :=
  seal_mutSummaryCut progMutSlotMintIfEmptyU32_realizes_summary

/-! ## 3. 5-Call Multi-Slot CNode Chain (`O(N)` `rfl`, Zero Callee Unfolding) -/

/-- Concrete two-allocation `MemoryState` (`0` `noncomputable`):
- `allocId = 1` (`.shared`, 4 bytes): external read-only config `0xCAFEBABE`;
- `allocId = 2` (`.mut`, 24 bytes): CNode header + 4 capability slots
  `[epoch = 10, activeCount = 0, slots = [0, 77, 0, 99]]`. -/
@[expose] def cnode24Mem0 : MemoryState :=
  { nextAllocId := 3
    allocations := [
      { allocId := 1
        alignLog2 := 2
        mutability := .shared
        bytes := encodeU32BeSlice 0xCAFEBABE
        live := true },
      { allocId := 2
        alignLog2 := 2
        mutability := .mut
        bytes :=
          encodeU32BeSlice 10 ++
          encodeU32BeSlice 0 ++
          encodeU32BeSlice 0 ++
          encodeU32BeSlice 77 ++
          encodeU32BeSlice 0 ++
          encodeU32BeSlice 99
        live := true }
    ] }

/-- Expected post-chain `MemoryState` after minting `501` into `slots[0]`,
attempting `602` on occupied `slots[1]`, minting `703` into `slots[2]`, and
accumulating `activeCount = 2`. -/
@[expose] def cnode24MemExpected : MemoryState :=
  { nextAllocId := 3
    allocations := [
      { allocId := 1
        alignLog2 := 2
        mutability := .shared
        bytes := encodeU32BeSlice 0xCAFEBABE
        live := true },
      { allocId := 2
        alignLog2 := 2
        mutability := .mut
        bytes :=
          encodeU32BeSlice 10 ++
          encodeU32BeSlice 2 ++
          encodeU32BeSlice 501 ++
          encodeU32BeSlice 77 ++
          encodeU32BeSlice 703 ++
          encodeU32BeSlice 99
        live := true }
    ] }

/-- Lens onto `[0..4)` (`epoch`) of `allocId = 2`. -/
@[expose] def cnodeEpochLens : ByteSubLens := ⟨2, 0, 4, 2⟩

/-- Lens onto `[4..8)` (`activeCount`) of `allocId = 2`. -/
@[expose] def cnodeActiveCountLens : ByteSubLens := ⟨2, 4, 4, 2⟩

/-- Lens onto capability slot `i` (`[8 + 4*i .. 12 + 4*i)`) of `allocId = 2`. -/
@[expose] def cnodeSlotLens (i : Nat) : ByteSubLens := ⟨2, 8 + 4 * i, 4, 2⟩

/-- 5-call sequence mixing `progMutSlotMintIfEmptyU32` and
`progMutFieldAddAssignU32` across `slots[0..2]` and `activeCount`. -/
@[expose] def cnodeSummaryChainSpecs : List (Program × Nat × SummaryCallSite) :=
  [ (progMutSlotMintIfEmptyU32, 5,
      ⟨slotMintIfEmptySummary, cnodeSlotLens 0, [mkU32Val 501]⟩),
    (progMutFieldAddAssignU32, 3,
      ⟨fieldAddAssignSummary, cnodeActiveCountLens, [mkU32Val 1]⟩),
    (progMutSlotMintIfEmptyU32, 5,
      ⟨slotMintIfEmptySummary, cnodeSlotLens 1, [mkU32Val 602]⟩),
    (progMutSlotMintIfEmptyU32, 5,
      ⟨slotMintIfEmptySummary, cnodeSlotLens 2, [mkU32Val 703]⟩),
    (progMutFieldAddAssignU32, 3,
      ⟨fieldAddAssignSummary, cnodeActiveCountLens, [mkU32Val 1]⟩) ]

/-- End-to-end 5-call CNode chain theorem: proves step-by-step
`MirCalleeChainRunsTo` over `Trusted.MirSemantics.evalStep` and disjoint
sibling-field preservation (`epoch` `[0..4)` and `slots[3]` `[20..24)`) purely
from sealed `MutSummaryCut`s and `rfl` summary execution (never unfolding
`progMutSlotMintIfEmptyU32` or `progMutFieldAddAssignU32`). -/
theorem cnodeSummaryChain_certified :
    MirCalleeChainRunsTo cnodeSummaryChainSpecs cnode24Mem0 cnode24MemExpected
      [mkU32Val 1, mkU32Val 1, mkU32Val 0, mkU32Val 1, mkU32Val 2] ∧
    byteSubLensGet cnodeEpochLens cnode24MemExpected =
      byteSubLensGet cnodeEpochLens cnode24Mem0 ∧
    byteSubLensGet (cnodeSlotLens 3) cnode24MemExpected =
      byteSubLensGet (cnodeSlotLens 3) cnode24Mem0 := by
  have hAllCuts : AllSitesSummaryCut cnodeSummaryChainSpecs :=
    ⟨seal_slotMintIfEmptyU32_summaryCut,
     seal_addAssignU32_summaryCut,
     seal_slotMintIfEmptyU32_summaryCut,
     seal_slotMintIfEmptyU32_summaryCut,
     seal_addAssignU32_summaryCut,
     True.intro⟩
  have hExecChain :
      execMutSummaryChain
        (List.foldr (fun e acc => e.2.2 :: acc) [] cnodeSummaryChainSpecs)
        cnode24Mem0 =
      some (cnode24MemExpected,
        [mkU32Val 1, mkU32Val 1, mkU32Val 0, mkU32Val 1, mkU32Val 2]) := rfl
  have hChain :=
    execMutSummaryChain_certified_sound cnodeSummaryChainSpecs hAllCuts
      hExecChain
  exact ⟨hChain.1,
    hChain.2 cnodeEpochLens rfl,
    hChain.2 (cnodeSlotLens 3) rfl⟩

/-! ## 4. Fail-Closed Negative Regression Suite -/

private def sliceHeadByteIsZero (opt : Option (List AllocByte)) : Bool :=
  match opt with
  | none => false
  | some xs =>
    match xs with
    | [] => false
    | hd :: _ =>
      match hd with
      | .uninit => false
      | .init b _ => Nat.beq b.toNat 0

/-- Formal refutation (`→ False`, `[]` zero axioms) showing that dropping the
`byteLensDisjoint` side condition from `byteSubLens_get_put_disjoint` is
unsound: writing `0xAABBCCDD` to `[0, 4)` mutates overlapping `[2, 6)`. -/
theorem overlappingByteLensRefutesFrame :
    (∀ m' : MemoryState,
      byteSubLensPut ⟨2, 0, 4, 2⟩ cnode24Mem0
        (encodeU32BeSlice 0xAABBCCDD) = some m' →
      byteSubLensGet ⟨2, 2, 4, 1⟩ m' =
        byteSubLensGet ⟨2, 2, 4, 1⟩ cnode24Mem0) →
    False := by
  intro hBad
  let mOverwritten : MemoryState :=
    { nextAllocId := 3
      allocations := [
        { allocId := 1
          alignLog2 := 2
          mutability := .shared
          bytes := encodeU32BeSlice 0xCAFEBABE
          live := true },
        { allocId := 2
          alignLog2 := 2
          mutability := .mut
          bytes :=
            encodeU32BeSlice 0xAABBCCDD ++
            encodeU32BeSlice 0 ++
            encodeU32BeSlice 0 ++
            encodeU32BeSlice 77 ++
            encodeU32BeSlice 0 ++
            encodeU32BeSlice 99
          live := true }
      ] }
  have hEq := hBad mOverwritten rfl
  have hBool : false = true := congrArg sliceHeadByteIsZero hEq
  exact Bool.noConfusion hBool

@[expose] def deadAllocMem : MemoryState :=
  { nextAllocId := 2
    allocations := [{
      allocId := 1
      alignLog2 := 2
      mutability := .mut
      bytes := encodeU32BeSlice 42
      live := false
    }] }

@[expose] def uninitByteMem : MemoryState :=
  { nextAllocId := 2
    allocations := [{
      allocId := 1
      alignLog2 := 2
      mutability := .mut
      bytes := [.uninit, .init 0 none, .init 0 none, .init 0 none]
      live := true
    }] }

/-- Single-cause fail-closed negative regression suite (`[]` zero axioms):
1. Zero-size `byteSubLensGet` returns `none`;
2. Zero-size `byteSubLensPut` returns `none`;
3. `.shared` (`allocId = 1`) `byteSubLensGet` returns `none`;
4. `.shared` (`allocId = 1`) `byteSubLensPut` returns `none`;
5. Deallocated (`live = false`) `byteSubLensGet` returns `none`;
6. Out-of-bounds (`[22, 26)` on 24-byte `allocId = 2`) `byteSubLensGet` returns
   `none`;
7. Misaligned (`offset = 2`, `alignLog2 = 2`) `byteSubLensGet` returns `none`;
8. Length-mismatched (`3` bytes into a `4`-byte lens) `byteSubLensPut` returns
   `none`;
9. Partially uninitialized slice (`[.uninit, ...]`) is rejected by
   `execMutSummaryCall fieldAddAssignSummary`. -/
theorem canary_bytesublens_negative_fail_closed_tests :
    byteSubLensGet ⟨2, 0, 0, 2⟩ cnode24Mem0 = none ∧
    byteSubLensPut ⟨2, 0, 0, 2⟩ cnode24Mem0 [] = none ∧
    byteSubLensGet ⟨1, 0, 4, 2⟩ cnode24Mem0 = none ∧
    byteSubLensPut ⟨1, 0, 4, 2⟩ cnode24Mem0 (encodeU32BeSlice 1) = none ∧
    byteSubLensGet ⟨1, 0, 4, 2⟩ deadAllocMem = none ∧
    byteSubLensGet ⟨2, 22, 4, 1⟩ cnode24Mem0 = none ∧
    byteSubLensGet ⟨2, 2, 4, 2⟩ cnode24Mem0 = none ∧
    byteSubLensPut ⟨2, 0, 4, 2⟩ cnode24Mem0
      [.init 1 none, .init 2 none, .init 3 none] = none ∧
    execMutSummaryCall fieldAddAssignSummary ⟨1, 0, 4, 2⟩ uninitByteMem
      [mkU32Val 5] = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.ByteSubLens

end
