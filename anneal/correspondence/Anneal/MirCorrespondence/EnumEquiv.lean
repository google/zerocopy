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
import Anneal.MirCorrespondence.Codec
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.ScalarEquiv

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

section MiriEquiv

open Miri.ABI Miri.Memory Miri.Interpreter

theorem intWidth_modulus_pos (w : IntWidth) : 0 < Nat.pow 2 w.bitWidth := by
  cases w <;> decide

theorem intWidth_modulus_le_u128 (w : IntWidth) :
    Nat.pow 2 w.bitWidth ≤ Nat.pow 2 128 := by
  cases w <;> decide

theorem nat_ble_imp_le : ∀ {a b : Nat}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => by cases h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (nat_ble_imp_le h)

theorem nat_lt_of_blt_eq_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  nat_ble_imp_le h

theorem nat_shiftRight_zero (n : Nat) : Nat.shiftRight n 0 = n := rfl

theorem ite_false_eq_true {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

theorem ite_true_eq_true {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

theorem intWidth_lsb_width (w : IntWidth) :
    w.bitWidth - 1 - 0 + 1 = w.bitWidth := by
  cases w <;> decide

theorem toNat_truncateBits (w : IntWidth) (x : BitVec 128) :
    (truncateBits w x).toNat = Nat.mod x.toNat (Nat.pow 2 w.bitWidth) := by
  dsimp only [truncateBits, bvZeroExtend, bvExtractLsb, bvExtractLsb']
  rw [nat_shiftRight_zero, intWidth_lsb_width,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change Nat.mod (Nat.mod x.toNat (Nat.pow 2 w.bitWidth)) (Nat.pow 2 128) =
    Nat.mod x.toNat (Nat.pow 2 w.bitWidth)
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le (Nat.mod_lt x.toNat (intWidth_modulus_pos w))
      (intWidth_modulus_le_u128 w))

theorem truncateBits_eq_ofNat_mod (w : IntWidth) (x : BitVec 128) :
    truncateBits w x =
      BitVec.ofNat 128 (Nat.mod x.toNat (Nat.pow 2 w.bitWidth)) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_truncateBits, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le (Nat.mod_lt x.toNat (intWidth_modulus_pos w))
      (intWidth_modulus_le_u128 w))).symm

theorem truncateBits_idem (w : IntWidth) (x : BitVec 128) :
    truncateBits w (truncateBits w x) = truncateBits w x := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_truncateBits, toNat_truncateBits]
  exact Nat.mod_eq_of_lt (Nat.mod_lt x.toNat (intWidth_modulus_pos w))

theorem truncateBits_eq_of_beq_false {w : IntWidth} {x : BitVec 128}
    (h : (truncateBits w x != x) = false) :
    truncateBits w x = x := by
  have h_beq : (truncateBits w x == x) = true := by
    cases h_eq : (truncateBits w x == x) with
    | true => rfl
    | false =>
      change (!(truncateBits w x == x)) = false at h
      rw [h_eq] at h
      cases h
  exact eq_of_beq h_beq

theorem refNatNotElem_eq (x : Nat) (ys : List Nat) :
    refNatNotElem x ys = natNotElem x ys := by
  induction ys with
  | nil => rfl
  | cons y rest ih =>
    dsimp only [refNatNotElem, natNotElem]
    rw [ih]

theorem refNatListPairwiseNe_eq (xs : List Nat) :
    refNatListPairwiseNe xs = natListPairwiseNe xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [refNatListPairwiseNe, natListPairwiseNe]
    rw [refNatNotElem_eq, ih]

theorem refFindDiscrVariantAux_eq (idx : Nat) (discrBits : BitVec 128)
    (ds : List Nat) :
    refFindDiscrVariantAux idx discrBits ds =
      findDiscrVariantAux idx discrBits ds := by
  induction ds generalizing idx with
  | nil => rfl
  | cons d rest ih =>
    dsimp only [refFindDiscrVariantAux, findDiscrVariantAux]
    rw [ih (idx + 1)]

theorem refFindDiscrVariant?_eq (discrBits : BitVec 128) (ds : List Nat) :
    refFindDiscrVariant? discrBits ds = findDiscrVariant? discrBits ds :=
  refFindDiscrVariantAux_eq 0 discrBits ds

theorem refMiriTagToDiscrBits_eq (tagW : IntWidth) (tagS : Bool)
    (discrW : IntWidth) (tagBits : BitVec 128) :
    refMiriTagToDiscrBits tagW tagS discrW tagBits =
      some (tagBitsToDiscrBits tagW tagS discrW tagBits) := by
  cases tagS with
  | true =>
    change
      (match
          match (toMiriSize tagW).signExtend tagBits with
          | .ok integer => some (BitVec.ofInt 128 integer)
          | .error _ => none
        with
        | some extended =>
          match (toMiriSize discrW).truncate extended with
          | .ok discrBits => some discrBits
          | .error _ => none
        | none => none) =
      some (truncateBits discrW (bvOfInt 128 (signExtendBits tagW tagBits)))
    rw [size_signExtend_eq]
    dsimp only
    rw [bitVec_ofInt_eq, size_truncate_eq]
  | false =>
    change
      (match
          match (toMiriSize tagW).truncate tagBits with
          | .ok trunc => some trunc
          | .error _ => none
        with
        | some extended =>
          match (toMiriSize discrW).truncate extended with
          | .ok discrBits => some discrBits
          | .error _ => none
        | none => none) =
      some (truncateBits discrW (truncateBits tagW tagBits))
    rw [size_truncate_eq]
    dsimp only
    rw [size_truncate_eq]

theorem refEnumDiscrInBounds_eq (w : IntWidth) (d : Nat) :
    (Nat.blt d (Nat.pow 2 128) &&
      match ScalarInt.tryFromUInt (BitVec.ofNat 128 d) (toMiriSize w) with
      | .ok (some _) => true
      | .ok none => false
      | .error _ => false) =
    Nat.blt d (Nat.pow 2 w.bitWidth) := by
  have h_try :
      (match ScalarInt.tryFromUInt (BitVec.ofNat 128 d) (toMiriSize w) with
      | .ok (some _) => true
      | .ok none => false
      | .error _ => false) =
      (if truncateBits w (BitVec.ofNat 128 d) != BitVec.ofNat 128 d then false
       else true) := by
    rw [← @match_tryFromUInt_eq Bool w (BitVec.ofNat 128 d) (fun _ => true) false]
    cases ScalarInt.tryFromUInt (BitVec.ofNat 128 d) (toMiriSize w) with
    | error _ => rfl
    | ok o => cases o <;> rfl
  rw [h_try]
  cases h_u128 : Nat.blt d (Nat.pow 2 128) with
  | false =>
    cases h_mod : Nat.blt d (Nat.pow 2 w.bitWidth) with
    | false => rfl
    | true =>
      have hd_lt : d < Nat.pow 2 128 :=
        Nat.lt_of_lt_of_le (nat_lt_of_blt_eq_true h_mod)
          (intWidth_modulus_le_u128 w)
      have h_true : Nat.blt d (Nat.pow 2 128) = true :=
        Nat.ble_eq_true_of_le hd_lt
      rw [h_true] at h_u128
      cases h_u128
  | true =>
    have hd_u128 : d < Nat.pow 2 128 := nat_lt_of_blt_eq_true h_u128
    have h_btonat : (BitVec.ofNat 128 d).toNat = d := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hd_u128
    cases h_mod : Nat.blt d (Nat.pow 2 w.bitWidth) with
    | true =>
      have hd_mod : d < Nat.pow 2 w.bitWidth := nat_lt_of_blt_eq_true h_mod
      have h_eq : truncateBits w (BitVec.ofNat 128 d) = BitVec.ofNat 128 d := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_truncateBits, h_btonat]
        exact Nat.mod_eq_of_lt hd_mod
      have h_bne :
          (truncateBits w (BitVec.ofNat 128 d) != BitVec.ofNat 128 d) =
            false := by
        rw [h_eq]
        exact bne_self_eq_false (BitVec.ofNat 128 d)
      rw [h_bne]
      rfl
    | false =>
      have h_ne : truncateBits w (BitVec.ofNat 128 d) ≠ BitVec.ofNat 128 d := by
        intro h_eq
        have h_tn : (truncateBits w (BitVec.ofNat 128 d)).toNat =
            (BitVec.ofNat 128 d).toNat := congrArg BitVec.toNat h_eq
        rw [toNat_truncateBits, h_btonat] at h_tn
        have hd_lt : d < Nat.pow 2 w.bitWidth := by
          rw [← h_tn]
          exact Nat.mod_lt d (intWidth_modulus_pos w)
        have h_true : Nat.blt d (Nat.pow 2 w.bitWidth) = true :=
          Nat.ble_eq_true_of_le hd_lt
        rw [h_true] at h_mod
        cases h_mod
      have h_bne :
          (truncateBits w (BitVec.ofNat 128 d) != BitVec.ofNat 128 d) =
            true := by
        cases h_b : (truncateBits w (BitVec.ofNat 128 d) == BitVec.ofNat 128 d)
        · change
            (!(truncateBits w (BitVec.ofNat 128 d) == BitVec.ofNat 128 d)) =
              true
          rw [h_b]
          rfl
        · exact False.elim (h_ne (eq_of_beq h_b))
      rw [h_bne]
      rfl

theorem list_all_congr_eq {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x, f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [List.all]
    rw [h x, ih]

theorem bool_and_congr {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (a₁ && b₁) = (a₂ && b₂) := by
  rw [ha, hb]

theorem refEnumAdmitted_eq (ety : EnumTy) :
    refEnumAdmitted ety = enumAdmitted ety := by
  have h_bnds :
      ety.discriminants.all (fun d =>
        Nat.blt d (Nat.pow 2 128) &&
          match ScalarInt.tryFromUInt (BitVec.ofNat 128 d)
              (toMiriSize ety.discrWidth) with
          | .ok (some _) => true
          | .ok none => false
          | .error _ => false) =
      ety.discriminants.all
        (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) :=
    list_all_congr_eq ety.discriminants _ _
      (refEnumDiscrInBounds_eq ety.discrWidth)
  have h_tag :
      (match ety.tagRepr with
      | .zeroSized => Nat.beq ety.discriminants.length 1
      | .scalar tagW tagS =>
        ety.discriminants.all (fun d =>
          let dBits := BitVec.ofNat 128 d
          match (toMiriSize tagW).truncate dBits with
          | .ok truncTag =>
            match refMiriTagToDiscrBits tagW tagS ety.discrWidth truncTag with
            | some recovered => recovered == dBits
            | none => false
          | .error _ => false)) =
      (match ety.tagRepr with
      | .zeroSized => Nat.beq ety.discriminants.length 1
      | .scalar tagW tagS =>
        ety.discriminants.all (fun d =>
          let dBits := BitVec.ofNat 128 d
          tagBitsToDiscrBits tagW tagS ety.discrWidth
            (truncateBits tagW dBits) == dBits)) := by
    cases ety.tagRepr with
    | zeroSized => rfl
    | scalar tagW tagS =>
      apply list_all_congr_eq
      intro d
      dsimp only
      rw [size_truncate_eq]
      dsimp only
      rw [refMiriTagToDiscrBits_eq]
  exact bool_and_congr
    (bool_and_congr (bool_and_congr rfl h_bnds)
      (refNatListPairwiseNe_eq ety.discriminants))
    h_tag

theorem refIsZstEnumTy_eq (ety : EnumTy) :
    refIsZstEnumTy ety = isZstEnumTy ety := by
  unfold refIsZstEnumTy isZstEnumTy
  cases ety.tagRepr with
  | zeroSized => exact refEnumAdmitted_eq ety
  | scalar _ _ => rfl

theorem refIsSupportedLocalTy_eq (ty : MirTy) :
    refIsSupportedLocalTy ty = isSupportedScalarOrUnitTy ty := by
  cases ty with
  | enum ety => exact refEnumAdmitted_eq ety
  | _ => rfl

theorem refLiveUninitSlot_eq (ty : MirTy) :
    refLiveUninitSlot ty = liveUninitSlot ty := by
  cases ty with
  | enum ety =>
    dsimp only [refLiveUninitSlot, liveUninitSlot]
    rw [refIsZstEnumTy_eq]
  | _ => rfl

theorem fullRange_contains_truncateBits (w : IntWidth) (raw : BitVec 128) :
    match WrappingRange.full (toMiriSize w) with
    | .ok range => range.contains (truncateBits w raw) = true
    | .error _ => False := by
  have h_lt : (truncateBits w raw).toNat < Nat.pow 2 w.bitWidth := by
    rw [toNat_truncateBits]
    exact Nat.mod_lt raw.toNat (intWidth_modulus_pos w)
  cases w <;> (
    dsimp only [toMiriSize, WrappingRange.full, WrappingRange.contains]
    change
      (if (0 : BitVec 128).toNat ≤ (BitVec.ofNat 128 (_ - 1)).toNat then
        decide ((0 : BitVec 128).toNat ≤ (truncateBits _ raw).toNat) &&
          decide ((truncateBits _ raw).toNat ≤ (BitVec.ofNat 128 (_ - 1)).toNat)
      else _) = true
    have h_max : (truncateBits _ raw).toNat ≤ _ - 1 :=
      Nat.le_sub_one_of_lt h_lt
    simp only [BitVec.toNat_ofNat]
    exact decide_eq_true (by
      exact Nat.le_trans h_max (by decide)))

noncomputable def fullRangeOf (w : IntWidth) : WrappingRange :=
  match WrappingRange.full (toMiriSize w) with
  | .ok r => r
  | .error _ => ⟨0, 0⟩

theorem fullRangeOf_contains_truncateBits (w : IntWidth) (raw : BitVec 128) :
    (fullRangeOf w).contains (truncateBits w raw) = true := by
  have h := fullRange_contains_truncateBits w raw
  cases w <;> exact h

theorem findDiscrVariantAux_lt {idx : Nat} {discrBits : BitVec 128}
    {ds : List Nat} {v : Nat}
    (h : findDiscrVariantAux idx discrBits ds = some v) :
    v < idx + ds.length := by
  induction ds generalizing idx with
  | nil => cases h
  | cons d rest ih =>
    dsimp only [findDiscrVariantAux] at h
    cases h_eq : (BitVec.ofNat 128 d == discrBits) <;> rw [h_eq] at h
    · have h_sub := ih h
      dsimp only [List.length]
      have h_arith : idx + 1 + rest.length = idx + (rest.length + 1) :=
        Nat.add_right_comm idx 1 rest.length
      rw [← h_arith]
      exact h_sub
    · injection h with hv
      subst hv
      dsimp only [List.length]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos rest.length)

theorem findDiscrVariant?_lt {discrBits : BitVec 128} {ds : List Nat} {v : Nat}
    (h : findDiscrVariant? discrBits ds = some v) :
    v < ds.length := by
  have h0 := findDiscrVariantAux_lt h
  rw [Nat.zero_add] at h0
  exact h0

private theorem list_get_map_const {α β : Type} (xs : List α) (c : β) (i : Nat)
    (hi : i < (xs.map (fun _ => c)).length) :
    (xs.map (fun _ => c)).get ⟨i, hi⟩ = c := by
  induction xs generalizing i with
  | nil => cases hi
  | cons _ rest ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih j (Nat.lt_of_succ_lt_succ hi)

theorem array_map_inhabited_getElem?_uninhabited (ds : List Nat) (v : Nat)
    (hv : v < ds.length) :
    Option.getD
      ((Array.mk (ds.map (fun _ => refInhabitedVariantLayout)))[v]?.map
        VariantLayout.uninhabited) true = false := by
  dsimp only [Array.size, GetElem?.getElem?, Array.instGetElem?NatLtSize,
    decidableGetElem?, GetElem.getElem, Array.instGetElemNatLtSize,
    Array.getInternal]
  have hv' : v < (ds.map (fun _ => refInhabitedVariantLayout)).length := by
    rw [List.length_map]
    exact hv
  rw [dite_eq_left hv']
  dsimp only [Option.map, Option.getD]
  rw [list_get_map_const ds refInhabitedVariantLayout v hv']
  rfl

theorem truncateFromUInt_eq_miriScalar (w : IntWidth) (raw : BitVec 128) :
    ScalarInt.truncateFromUInt raw (toMiriSize w) =
      .ok (miriScalar w raw, truncateBits w raw != raw) := by
  have h : ScalarInt.truncateFromUInt raw (toMiriSize w) =
      match (toMiriSize w).truncate raw with
      | .ok b => .ok (miriScalar w raw, b != raw)
      | .error e => .error (.sizeError e) := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

theorem miriScalar_data (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).data = truncateBits w bits := by
  have h : (miriScalar w bits).data =
      match (toMiriSize w).truncate bits with
      | .ok b => b
      | .error _ => bits := by
    cases w <;> rfl
  rw [h, size_truncate_eq]

theorem evalRefConstLit_eq (ty : MirTy) (lit : ConstLit) :
    evalRefConstLit ty lit = evalConstLit ty lit := by
  cases ty with
  | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases lit <;> rfl
  | int w s =>
    cases lit with
    | zeroSized => rfl
    | scalar bits =>
      dsimp only [evalRefConstLit, evalConstLit]
      exact @match_tryFromUInt_eq (Except FaultKind Val) w bits
        (fun d => .ok (.scalar ⟨w, s, d⟩)) (.error .unsupported)
  | bool =>
    cases lit with
    | zeroSized => rfl
    | scalar bits =>
      dsimp only [evalRefConstLit, evalConstLit]
      exact @match_tryFromUInt_tryToBool_eq (Except FaultKind Val) bits
        (fun b => .ok (.bool b)) (.error .undefined) (.error .unsupported)
  | enum ety =>
    cases lit with
    | zeroSized =>
      dsimp only [evalRefConstLit, evalConstLit]
      rw [refIsZstEnumTy_eq]
    | scalar bits =>
      dsimp only [evalRefConstLit, evalConstLit]
      cases ety.tagRepr with
      | zeroSized => rfl
      | scalar tagW tagS =>
        dsimp only
        rw [refEnumAdmitted_eq]
        cases enumAdmitted ety with
        | false => rfl
        | true =>
          rw [Bool.not_true, ite_false_eq_true, Bool.false_or]
          rw [tryFromUInt_eq_truncateFromUInt,
              truncateFromUInt_eq_miriScalar tagW bits]
          dsimp only [bind, Except.bind, pure, Except.pure]
          cases h_ov : (truncateBits tagW bits != bits) with
          | true => rfl
          | false =>
            rw [ite_false_eq_true]
            dsimp only
            rw [miriScalar_data, refMiriTagToDiscrBits_eq,
              truncateBits_eq_of_beq_false h_ov]
            dsimp only
            rw [refFindDiscrVariant?_eq]
            cases findDiscrVariant?
                (tagBitsToDiscrBits tagW tagS ety.discrWidth bits)
                ety.discriminants <;> rfl

theorem checkRefVal_int_aux (b : Bool) (vw w : IntWidth) (vs s : Bool) :
    (if (!b) = true then false else IntWidth.beq vw w && (vs == s)) =
    (match if b = true then some (MirTy.int vw vs) else none with
    | some vTy => MirTy.beq vTy (MirTy.int w s)
    | none => false) := by
  cases b <;> rfl

theorem checkRefVal_eq (v : Val) (ty : MirTy) :
    checkRefVal v ty = checkVal v ty := by
  cases v with
  | unit | ptr _ | tuple _ | bytes _ => cases ty <;> rfl
  | bool b => cases ty <;> cases b <;> rfl
  | enumVal ety v =>
    cases ty with
    | enum ety' =>
      dsimp only [checkRefVal, checkVal, Val.ty?, MirTy.beq]
      rw [refEnumAdmitted_eq]
      cases (enumAdmitted ety && Nat.blt v ety.discriminants.length) <;> rfl
    | _ =>
      dsimp only [checkRefVal, checkVal, Val.ty?]
      cases (enumAdmitted ety && Nat.blt v ety.discriminants.length) <;> rfl
  | scalar sv =>
    cases sv with
    | mk vw vs vbits =>
      cases ty with
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
      | unsupported =>
        dsimp only [checkRefVal, checkVal, Val.ty?]
        cases (ScalarVal.wf ⟨vw, vs, vbits⟩) <;> rfl
      | int w s =>
        have h_m :
            (match ScalarInt.tryFromUInt vbits (toMiriSize vw) with
            | .ok (some _) => IntWidth.beq vw w && (vs == s)
            | _ => false) =
            if truncateBits vw vbits != vbits then false
            else IntWidth.beq vw w && (vs == s) :=
          @match_tryFromUInt_eq Bool vw vbits
            (fun _ => IntWidth.beq vw w && (vs == s)) false
        exact h_m.trans
          (checkRefVal_int_aux (truncateBits vw vbits == vbits) vw w vs s)

theorem checkRefArgsMatch_eq (vs : List Val) (tys : List MirTy) :
    checkRefArgsMatch vs tys = checkArgsMatch vs tys := by
  induction vs generalizing tys with
  | nil => cases tys <;> rfl
  | cons v rest ih =>
    cases tys with
    | nil => rfl
    | cons ty tys' =>
      dsimp only [checkRefArgsMatch, checkArgsMatch]
      rw [checkRefVal_eq, ih]

theorem bitVec128_ofNat_toNat (bits : BitVec 128) :
    BitVec.ofNat 128 bits.toNat = bits := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt bits.isLt

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem bvToInt_inj {n : Nat} {u v : BitVec n}
    (h : bvToInt u = bvToInt v) : u = v := by
  dsimp only [bvToInt] at h
  cases hu : decide (2 * u.toNat < Nat.pow 2 n) <;>
    cases hv : decide (2 * v.toNat < Nat.pow 2 n)
  · rw [ite_eq_right (of_decide_eq_false hu),
      ite_eq_right (of_decide_eq_false hv)] at h
    have h_add := congrArg (fun z : Int => z + Int.ofNat (Nat.pow 2 n)) h
    rw [Int.sub_add_cancel, Int.sub_add_cancel] at h_add
    exact BitVec.eq_of_toNat_eq (Int.ofNat.inj h_add)
  · rw [ite_eq_right (of_decide_eq_false hu),
      ite_eq_left (of_decide_eq_true hv)] at h
    have h_add := congrArg (fun z : Int => z + Int.ofNat (Nat.pow 2 n)) h
    rw [Int.sub_add_cancel] at h_add
    change Int.ofNat u.toNat = Int.ofNat (v.toNat + Nat.pow 2 n) at h_add
    have h_nat : u.toNat = v.toNat + Nat.pow 2 n := Int.ofNat.inj h_add
    have h_lt : Nat.pow 2 n < Nat.pow 2 n :=
      Nat.lt_of_le_of_lt (Nat.le_add_left (Nat.pow 2 n) v.toNat)
        (h_nat ▸ u.isLt)
    exact False.elim (Nat.lt_irrefl _ h_lt)
  · rw [ite_eq_left (of_decide_eq_true hu),
      ite_eq_right (of_decide_eq_false hv)] at h
    have h_add := congrArg (fun z : Int => z + Int.ofNat (Nat.pow 2 n)) h
    rw [Int.sub_add_cancel] at h_add
    change Int.ofNat (u.toNat + Nat.pow 2 n) = Int.ofNat v.toNat at h_add
    have h_nat : u.toNat + Nat.pow 2 n = v.toNat := Int.ofNat.inj h_add
    have h_lt : Nat.pow 2 n < Nat.pow 2 n :=
      Nat.lt_of_le_of_lt (Nat.le_add_left (Nat.pow 2 n) u.toNat)
        (h_nat ▸ v.isLt)
    exact False.elim (Nat.lt_irrefl _ h_lt)
  · rw [ite_eq_left (of_decide_eq_true hu),
      ite_eq_left (of_decide_eq_true hv)] at h
    exact BitVec.eq_of_toNat_eq (Int.ofNat.inj h)

private theorem nat_sub_sub_eq_add_sub {a b c : Nat} (hbc : b ≤ c)
    (hca : c ≤ a) : a - (c - b) = (a - c) + b := by
  have h1 : a - (c - b) + (c - b) = a :=
    Nat.sub_add_cancel (Nat.le_trans (Nat.sub_le c b) hca)
  have h2 : (a - c) + b + (c - b) = a := by
    rw [Nat.add_assoc, Nat.add_comm b (c - b), Nat.sub_add_cancel hbc,
      Nat.sub_add_cancel hca]
  exact Nat.add_right_cancel (h1.trans h2.symm)

private theorem bvSignExtend_toNat_mod {n m : Nat} (hn : n ≤ m)
    (u : BitVec n) :
    Nat.mod (bvSignExtend m u).toNat (Nat.pow 2 n) = u.toNat := by
  have h_pow_le : Nat.pow 2 n ≤ Nat.pow 2 m :=
    Nat.pow_le_pow_right (by decide) hn
  have h_pow_mul :
      Nat.pow 2 m = Nat.pow 2 n * Nat.pow 2 (m - n) :=
    (congrArg (Nat.pow 2) (Nat.add_sub_of_le hn).symm).trans
      (Nat.pow_add 2 n (m - n))
  have h_pow_sub_pos : 1 ≤ Nat.pow 2 (m - n) :=
    Nat.one_le_pow (m - n) 2 (by decide)
  have h_sub_eq :
      Nat.pow 2 m - Nat.pow 2 n =
        Nat.pow 2 n * (Nat.pow 2 (m - n) - 1) := by
    have h_m :
        Nat.pow 2 m =
          Nat.pow 2 n * (Nat.pow 2 (m - n) - 1) + Nat.pow 2 n := by
      have h_mul :
          Nat.pow 2 n * (Nat.pow 2 (m - n) - 1) + Nat.pow 2 n =
            Nat.pow 2 n * ((Nat.pow 2 (m - n) - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [h_mul, Nat.sub_add_cancel h_pow_sub_pos]
      exact h_pow_mul
    rw [h_m, Nat.add_sub_cancel]
  dsimp only [bvSignExtend, bvOfInt, bvToInt]
  rw [BitVec.toNat_ofNat]
  cases hu : decide (2 * u.toNat < Nat.pow 2 n) with
  | true =>
    rw [ite_eq_left (of_decide_eq_true hu)]
    dsimp only [intEmod, Int.natAbs, Int.toNat]
    have h_ltm : u.toNat < Nat.pow 2 m := Nat.lt_of_lt_of_le u.isLt h_pow_le
    change Nat.mod (Nat.mod (Nat.mod u.toNat (Nat.pow 2 m)) (Nat.pow 2 m))
      (Nat.pow 2 n) = u.toNat
    rw [nat_mod_eq_of_lt h_ltm, nat_mod_eq_of_lt h_ltm]
    exact nat_mod_eq_of_lt u.isLt
  | false =>
    rw [ite_eq_right (of_decide_eq_false hu)]
    have h_sub_pos : 1 ≤ Nat.pow 2 n - u.toNat :=
      Nat.sub_pos_of_lt u.isLt
    let k := Nat.pow 2 n - u.toNat - 1
    have hk_succ : Nat.succ k = Nat.pow 2 n - u.toNat :=
      Nat.sub_add_cancel h_sub_pos
    have h_int_eq :
        Int.ofNat u.toNat - Int.ofNat (Nat.pow 2 n) = Int.negSucc k := by
      have h_add : Int.negSucc k + Int.ofNat (Nat.pow 2 n) =
          Int.ofNat u.toNat := by
        change Int.subNatNat (Nat.pow 2 n) (Nat.succ k) = Int.ofNat u.toNat
        rw [hk_succ]
        have h_le : Nat.pow 2 n - u.toNat ≤ Nat.pow 2 n := Nat.sub_le _ _
        dsimp only [Int.subNatNat]
        have h_z : (Nat.pow 2 n - u.toNat) - Nat.pow 2 n = 0 :=
          Nat.sub_eq_zero_of_le h_le
        rw [h_z]
        have h_uu : Nat.pow 2 n - (Nat.pow 2 n - u.toNat) = u.toNat :=
          Nat.sub_sub_self (Nat.le_of_lt u.isLt)
        rw [h_uu]
      exact Int.sub_eq_iff_eq_add.mpr h_add.symm
    rw [h_int_eq]
    dsimp only [intEmod, Int.natAbs]
    have hk_lt : k < Nat.pow 2 m := by
      have h1 : k < Nat.succ k := Nat.lt_succ_self k
      rw [hk_succ] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.le_trans (Nat.sub_le _ _) h_pow_le)
    rw [nat_mod_eq_of_lt hk_lt, hk_succ]
    have h_lem : Nat.pow 2 n - u.toNat ≤ Nat.pow 2 m :=
      Nat.le_trans (Nat.sub_le _ _) h_pow_le
    dsimp only [Int.subNatNat]
    rw [Nat.sub_eq_zero_of_le h_lem]
    dsimp only [Int.toNat]
    have h_lt_sub : Nat.pow 2 m - (Nat.pow 2 n - u.toNat) < Nat.pow 2 m :=
      Nat.sub_lt (Nat.pow_pos (by decide)) h_sub_pos
    change Nat.mod
      (Nat.mod (Nat.pow 2 m - (Nat.pow 2 n - u.toNat)) (Nat.pow 2 m))
      (Nat.pow 2 n) = u.toNat
    have hu_le : u.toNat ≤ Nat.pow 2 n := Nat.le_of_lt u.isLt
    rw [nat_mod_eq_of_lt h_lt_sub,
      nat_sub_sub_eq_add_sub hu_le h_pow_le, h_sub_eq]
    exact (Nat.mul_add_mod _ _ _).trans (Nat.mod_eq_of_lt u.isLt)

private theorem signExtendBits_inj (w : IntWidth) (x y : BitVec 128)
    (h : signExtendBits w (truncateBits w x) =
      signExtendBits w (truncateBits w y)) :
    truncateBits w x = truncateBits w y := by
  dsimp only [signExtendBits] at h
  have h_se := bvToInt_inj h
  have hn : w.bitWidth - 1 - 0 + 1 ≤ 128 := by cases w <;> decide
  have h_mod :=
    congrArg
      (fun z : BitVec 128 =>
        Nat.mod z.toNat (Nat.pow 2 (w.bitWidth - 1 - 0 + 1)))
      h_se
  rw [bvSignExtend_toNat_mod hn, bvSignExtend_toNat_mod hn] at h_mod
  have h_low :
      bvExtractLsb (w.bitWidth - 1) 0 (truncateBits w x) =
        bvExtractLsb (w.bitWidth - 1) 0 (truncateBits w y) :=
    BitVec.eq_of_toNat_eq h_mod
  have h_ze := congrArg (bvZeroExtend 128) h_low
  change truncateBits w (truncateBits w x) =
    truncateBits w (truncateBits w y) at h_ze
  rw [truncateBits_idem, truncateBits_idem] at h_ze
  exact h_ze

theorem decodeScalar_beq_eq (w : IntWidth) (s : Bool) (x y : BitVec 128) :
    (decodeScalar ⟨w, s, x⟩ == decodeScalar ⟨w, s, y⟩) =
      (truncateBits w x == truncateBits w y) := by
  cases h_eq : (truncateBits w x == truncateBits w y) with
  | true =>
    have h_t := eq_of_beq h_eq
    dsimp only [decodeScalar]
    rw [h_t]
    exact beq_self_eq_true _
  | false =>
    cases h_d : (decodeScalar ⟨w, s, x⟩ == decodeScalar ⟨w, s, y⟩) with
    | false => rfl
    | true =>
      have h_deq := eq_of_beq h_d
      dsimp only [decodeScalar] at h_deq
      have h_t : truncateBits w x = truncateBits w y := by
        cases s with
        | false =>
          exact BitVec.eq_of_toNat_eq (Int.ofNat.inj h_deq)
        | true =>
          exact signExtendBits_inj w x y h_deq
      rw [h_t, beq_self_eq_true] at h_eq
      cases h_eq

/-! ## Distinct Enum Discriminants and `SimulationInv` Left-Injectivity -/

theorem bool_and_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem natNotElem_ne {x y : Nat} {xs : List Nat} {j : Nat}
    (h_ne : natNotElem x xs = true)
    (h_get : MirSemantics.getElem? xs j = some y) : x ≠ y := by
  induction xs generalizing j with
  | nil => cases h_get
  | cons z rest ih =>
    dsimp only [natNotElem] at h_ne
    let ⟨h_xz, h_rest⟩ := bool_and_split h_ne
    cases j with
    | zero =>
      injection h_get with h_eq
      subst h_eq
      intro h_xy
      subst h_xy
      rw [Nat.beq_refl] at h_xz
      cases h_xz
    | succ k => exact ih h_rest h_get

theorem natListPairwiseNe_inj {xs : List Nat} {i j d : Nat}
    (h_pw : natListPairwiseNe xs = true)
    (hi : MirSemantics.getElem? xs i = some d)
    (hj : MirSemantics.getElem? xs j = some d) : i = j := by
  induction xs generalizing i j with
  | nil => cases hi
  | cons x rest ih =>
    dsimp only [natListPairwiseNe] at h_pw
    let ⟨h_ne, h_rest⟩ := bool_and_split h_pw
    cases i with
    | zero =>
      injection hi with h_x
      subst h_x
      cases j with
      | zero => rfl
      | succ k =>
        exact False.elim (natNotElem_ne h_ne hj rfl)
    | succ i' =>
      cases j with
      | zero =>
        injection hj with h_x
        subst h_x
        exact False.elim (natNotElem_ne h_ne hi rfl)
      | succ j' =>
        exact congrArg Nat.succ (ih h_rest hi hj)

theorem bitVec128_ofNat_inj {a b : Nat}
    (ha : a < Nat.pow 2 128) (hb : b < Nat.pow 2 128)
    (h : BitVec.ofNat 128 a = BitVec.ofNat 128 b) : a = b := by
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
  exact ht

theorem intWidth_pow_le_128 (w : IntWidth) :
    Nat.pow 2 w.bitWidth ≤ Nat.pow 2 128 := by
  cases w <;> decide

theorem enumAdmitted_parts {ety : EnumTy} (h : enumAdmitted ety = true) :
    ety.discriminants.all
        (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) = true ∧
    natListPairwiseNe ety.discriminants = true ∧
    (match ety.tagRepr with
    | .zeroSized => Nat.beq ety.discriminants.length 1
    | .scalar tagW tagS =>
      ety.discriminants.all (fun d =>
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW (BitVec.ofNat 128 d)) ==
            BitVec.ofNat 128 d)) = true := by
  dsimp only [enumAdmitted] at h
  let ⟨h1, h_tag⟩ := bool_and_split h
  let ⟨h2, h_pw⟩ := bool_and_split h1
  let ⟨_, h_bnds⟩ := bool_and_split h2
  exact ⟨h_bnds, h_pw, h_tag⟩

theorem findDiscrVariantAux_of_getElem? {idx v d : Nat} {ds : List Nat}
    (h_bnds : ds.all (fun x => Nat.blt x (Nat.pow 2 128)) = true)
    (h_pw : natListPairwiseNe ds = true)
    (h_get : MirSemantics.getElem? ds v = some d) :
    findDiscrVariantAux idx (BitVec.ofNat 128 d) ds = some (idx + v) := by
  induction ds generalizing idx v with
  | nil => cases h_get
  | cons x rest ih =>
    dsimp only [List.all] at h_bnds
    let ⟨h_x128, h_rest128⟩ := bool_and_split h_bnds
    dsimp only [natListPairwiseNe] at h_pw
    let ⟨h_ne, h_pw_rest⟩ := bool_and_split h_pw
    cases v with
    | zero =>
      injection h_get with h_xd
      subst h_xd
      dsimp only [findDiscrVariantAux]
      rw [beq_self_eq_true, ite_true_eq_true, Nat.add_zero]
    | succ v' =>
      have h_get' : MirSemantics.getElem? rest v' = some d := h_get
      have h_d128_b : Nat.blt d (Nat.pow 2 128) = true :=
        list_all_mirGetElem? (p := fun x => Nat.blt x (Nat.pow 2 128))
          h_rest128 h_get'
      have h_d128 : d < Nat.pow 2 128 := Nat.blt_eq.mp h_d128_b
      have h_x_lt : x < Nat.pow 2 128 := Nat.blt_eq.mp h_x128
      have h_xd_ne : x ≠ d := natNotElem_ne h_ne h_get'
      have h_beq_false : (BitVec.ofNat 128 x == BitVec.ofNat 128 d) = false := by
        cases h_b : (BitVec.ofNat 128 x == BitVec.ofNat 128 d) with
        | false => rfl
        | true =>
          exact False.elim
            (h_xd_ne (bitVec128_ofNat_inj h_x_lt h_d128 (eq_of_beq h_b)))
      dsimp only [findDiscrVariantAux]
      rw [h_beq_false, ite_false_eq_true]
      have h_ih := ih (idx := idx + 1) h_rest128 h_pw_rest h_get'
      have h_ar : idx + 1 + v' = idx + (v' + 1) :=
        Nat.add_right_comm idx 1 v'
      rw [h_ar] at h_ih
      exact h_ih

theorem findDiscrVariant?_of_enumAdmitted {ety : EnumTy} {v d : Nat}
    (h_adm : enumAdmitted ety = true)
    (h_get : MirSemantics.getElem? ety.discriminants v = some d) :
    findDiscrVariant? (BitVec.ofNat 128 d) ety.discriminants = some v := by
  let ⟨h_bnds, h_pw, _⟩ := enumAdmitted_parts h_adm
  have h_128 : ety.discriminants.all (fun x => Nat.blt x (Nat.pow 2 128)) =
      true := by
    have h_le := intWidth_pow_le_128 ety.discrWidth
    have h_aux : ∀ xs : List Nat,
        xs.all (fun x => Nat.blt x (Nat.pow 2 ety.discrWidth.bitWidth)) = true →
        xs.all (fun x => Nat.blt x (Nat.pow 2 128)) = true := by
      intro xs
      induction xs with
      | nil => intro _; rfl
      | cons a rest ih =>
        intro ha
        dsimp only [List.all] at ha
        let ⟨h_a, h_r⟩ := bool_and_split ha
        dsimp only [List.all]
        rw [Nat.blt_eq.mpr (Nat.lt_of_lt_of_le (Nat.blt_eq.mp h_a) h_le),
          ih h_r]
        rfl
    exact h_aux ety.discriminants h_bnds
  have h0 := findDiscrVariantAux_of_getElem? (idx := 0) h_128 h_pw h_get
  rw [Nat.zero_add] at h0
  exact h0

theorem checkVal_eq_true_inv {v : Val} {ty : MirTy}
    (h : checkVal v ty = true) :
    (∃ w s bits, ty = .int w s ∧ v = .scalar ⟨w, s, bits⟩ ∧
      truncateBits w bits = bits) ∨
    (∃ b, ty = .bool ∧ v = .bool b) ∨
    (ty = .unit ∧ v = .unit) ∨
    (∃ ety k, ty = .enum ety ∧ v = .enumVal ety k ∧
      enumAdmitted ety = true ∧ k < ety.discriminants.length) := by
  cases v with
  | scalar sv =>
    cases sv with
    | mk w s bits =>
      dsimp only [checkVal, Val.ty?] at h
      cases h_wf : (ScalarVal.wf ⟨w, s, bits⟩) with
      | false => rw [h_wf] at h; cases h
      | true =>
        rw [h_wf] at h
        have h_ty : MirTy.int w s = ty := MirTy.eq_of_beq h
        exact Or.inl ⟨w, s, bits, h_ty.symm, rfl, eq_of_beq h_wf⟩
  | bool b =>
    dsimp only [checkVal, Val.ty?] at h
    have h_ty : MirTy.bool = ty := MirTy.eq_of_beq h
    exact Or.inr (Or.inl ⟨b, h_ty.symm, rfl⟩)
  | unit =>
    dsimp only [checkVal, Val.ty?] at h
    have h_ty : MirTy.unit = ty := MirTy.eq_of_beq h
    exact Or.inr (Or.inr (Or.inl ⟨h_ty.symm, rfl⟩))
  | enumVal ety k =>
    dsimp only [checkVal, Val.ty?] at h
    cases h_e : (enumAdmitted ety && Nat.blt k ety.discriminants.length) with
    | false => rw [h_e] at h; cases h
    | true =>
      rw [h_e] at h
      have h_ty : MirTy.enum ety = ty := MirTy.eq_of_beq h
      let ⟨h_adm, h_k⟩ := bool_and_split h_e
      exact Or.inr (Or.inr (Or.inr
        ⟨ety, k, h_ty.symm, rfl, h_adm, Nat.blt_eq.mp h_k⟩))
  | ptr _ | tuple _ | bytes _ => cases h

theorem valToMiriImmediate_inj {ty : MirTy} {v₁ v₂ : Val}
    (h₁ : checkVal v₁ ty = true) (h₂ : checkVal v₂ ty = true)
    (h_eq : valToMiriImmediate ty v₁ = valToMiriImmediate ty v₂) :
    v₁ = v₂ := by
  cases checkVal_eq_true_inv h₁ with
  | inl hi₁ =>
    let ⟨w, s, b₁, hty₁, hv₁, htr₁⟩ := hi₁
    subst hty₁; subst hv₁
    cases checkVal_eq_true_inv h₂ with
    | inl hi₂ =>
      let ⟨w₂, s₂, b₂, hty₂, hv₂, htr₂⟩ := hi₂
      injection hty₂ with hw hs; subst hw; subst hs; subst hv₂
      dsimp only [valToMiriImmediate] at h_eq
      injection h_eq with h_sc
      injection h_sc with h_pl
      injection h_pl with h_si
      have h_d := congrArg Miri.Memory.ScalarInt.data h_si
      rw [miriScalar_data, miriScalar_data, htr₁, htr₂] at h_d
      subst h_d
      rfl
    | inr hr =>
      cases hr with
      | inl hb => let ⟨_, hty₂, _⟩ := hb; cases hty₂
      | inr hr2 =>
        cases hr2 with
        | inl hu => cases hu.1
        | inr he => let ⟨_, _, hty₂, _, _, _⟩ := he; cases hty₂
  | inr hr₁ =>
    cases hr₁ with
    | inl hb₁ =>
      let ⟨b₁, hty₁, hv₁⟩ := hb₁
      subst hty₁; subst hv₁
      cases checkVal_eq_true_inv h₂ with
      | inl hi => let ⟨_, _, _, hty₂, _, _⟩ := hi; cases hty₂
      | inr hr =>
        cases hr with
        | inl hb₂ =>
          let ⟨b₂, _, hv₂⟩ := hb₂
          subst hv₂
          cases b₁ <;> cases b₂ <;> first | rfl | cases h_eq
        | inr hr2 =>
          cases hr2 with
          | inl hu => cases hu.1
          | inr he => let ⟨_, _, hty₂, _, _, _⟩ := he; cases hty₂
    | inr hr₁' =>
      cases hr₁' with
      | inl hu₁ =>
        let ⟨hty₁, hv₁⟩ := hu₁
        subst hty₁; subst hv₁
        cases checkVal_eq_true_inv h₂ with
        | inl hi => let ⟨_, _, _, hty₂, _, _⟩ := hi; cases hty₂
        | inr hr =>
          cases hr with
          | inl hb => let ⟨_, hty₂, _⟩ := hb; cases hty₂
          | inr hr2 =>
            cases hr2 with
            | inl hu₂ => rw [hu₂.2]
            | inr he => let ⟨_, _, hty₂, _, _, _⟩ := he; cases hty₂
      | inr he₁ =>
        let ⟨ety, k₁, hty₁, hv₁, h_adm, hk₁⟩ := he₁
        subst hty₁; subst hv₁
        cases checkVal_eq_true_inv h₂ with
        | inl hi => let ⟨_, _, _, hty₂, _, _⟩ := hi; cases hty₂
        | inr hr =>
          cases hr with
          | inl hb => let ⟨_, hty₂, _⟩ := hb; cases hty₂
          | inr hr2 =>
            cases hr2 with
            | inl hu => cases hu.1
            | inr he₂ =>
              let ⟨ety₂, k₂, hty₂, hv₂, _, hk₂⟩ := he₂
              injection hty₂ with h_ety; subst h_ety; subst hv₂
              let ⟨h_bnds, h_pw, h_tag⟩ := enumAdmitted_parts h_adm
              cases h_tr : ety.tagRepr with
              | zeroSized =>
                rw [h_tr] at h_tag
                have h_len1 : ety.discriminants.length = 1 :=
                  Nat.eq_of_beq_eq_true h_tag
                rw [h_len1] at hk₁ hk₂
                cases k₁ with
                | zero =>
                  cases k₂ with
                  | zero => rfl
                  | succ m =>
                    exact False.elim
                      (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hk₂))
                | succ m =>
                  exact False.elim
                    (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hk₁))
              | scalar tagW tagS =>
                rw [h_tr] at h_tag
                let ⟨d₁, hd₁⟩ := mirGetElem?_some_of_lt hk₁
                let ⟨d₂, hd₂⟩ := mirGetElem?_some_of_lt hk₂
                dsimp only [valToMiriImmediate] at h_eq
                rw [h_tr, hd₁, hd₂] at h_eq
                injection h_eq with h_sc
                injection h_sc with h_pl
                injection h_pl with h_si
                have h_d := congrArg Miri.Memory.ScalarInt.data h_si
                rw [miriScalar_data, miriScalar_data] at h_d
                have h_rec₁ :
                    tagBitsToDiscrBits tagW tagS ety.discrWidth
                      (truncateBits tagW (BitVec.ofNat 128 d₁)) =
                      BitVec.ofNat 128 d₁ :=
                  eq_of_beq (list_all_mirGetElem?
                    (p := fun d =>
                      tagBitsToDiscrBits tagW tagS ety.discrWidth
                        (truncateBits tagW (BitVec.ofNat 128 d)) ==
                        BitVec.ofNat 128 d) h_tag hd₁)
                have h_rec₂ :
                    tagBitsToDiscrBits tagW tagS ety.discrWidth
                      (truncateBits tagW (BitVec.ofNat 128 d₂)) =
                      BitVec.ofNat 128 d₂ :=
                  eq_of_beq (list_all_mirGetElem?
                    (p := fun d =>
                      tagBitsToDiscrBits tagW tagS ety.discrWidth
                        (truncateBits tagW (BitVec.ofNat 128 d)) ==
                        BitVec.ofNat 128 d) h_tag hd₂)
                have h_bv_eq : BitVec.ofNat 128 d₁ = BitVec.ofNat 128 d₂ := by
                  rw [← h_rec₁, h_d, h_rec₂]
                have hd₁_128 : d₁ < Nat.pow 2 128 :=
                  Nat.lt_of_lt_of_le
                    (Nat.blt_eq.mp (list_all_mirGetElem?
                      (p := fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth))
                      h_bnds hd₁))
                    (intWidth_pow_le_128 ety.discrWidth)
                have hd₂_128 : d₂ < Nat.pow 2 128 :=
                  Nat.lt_of_lt_of_le
                    (Nat.blt_eq.mp (list_all_mirGetElem?
                      (p := fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth))
                      h_bnds hd₂))
                    (intWidth_pow_le_128 ety.discrWidth)
                have h_nat_eq := bitVec128_ofNat_inj hd₁_128 hd₂_128 h_bv_eq
                subst h_nat_eq
                have hk_eq := natListPairwiseNe_inj h_pw hd₁ hd₂
                subst hk_eq
                rfl

theorem valToMiriImmediate_ne_uninit {ty : MirTy} {v : Val}
    (h_chk : checkVal v ty = true)
    (h_ne_unit : ty ≠ .unit)
    (h_ne_zst : ∀ ety : EnumTy, ty = .enum ety → isZstEnumTy ety = false) :
    valToMiriImmediate ty v ≠ .uninit := by
  intro h_eq
  cases checkVal_eq_true_inv h_chk with
  | inl hi =>
    let ⟨_, _, _, hty, hv, _⟩ := hi
    subst hty; subst hv; cases h_eq
  | inr hr =>
    cases hr with
    | inl hb =>
      let ⟨_, hty, hv⟩ := hb
      subst hty; subst hv; cases h_eq
    | inr hr2 =>
      cases hr2 with
      | inl hu => exact h_ne_unit hu.1
      | inr he =>
        let ⟨ety, k, hty, hv, h_adm, hk⟩ := he
        subst hty; subst hv
        cases h_tr : ety.tagRepr with
        | zeroSized =>
          have h_z := h_ne_zst ety rfl
          dsimp only [isZstEnumTy] at h_z
          rw [h_tr, h_adm] at h_z
          cases h_z
        | scalar tagW tagS =>
          let ⟨d, hd⟩ := mirGetElem?_some_of_lt hk
          dsimp only [valToMiriImmediate] at h_eq
          rw [h_tr, hd] at h_eq
          cases h_eq

theorem slotToMiriLocalValue_inj {ty : MirTy} {s₁ s₂ : LocalSlot}
    (h₁ : SlotMatchesTy ty s₁) (h₂ : SlotMatchesTy ty s₂)
    (h_eq : slotToMiriLocalValue ty s₁ = slotToMiriLocalValue ty s₂) :
    s₁ = s₂ := by
  cases s₁ with
  | dead =>
    cases s₂ with
    | dead => rfl
    | live opt₂ => cases opt₂ <;> cases h_eq
  | live opt₁ =>
    cases s₂ with
    | dead => cases opt₁ <;> cases h_eq
    | live opt₂ =>
      cases opt₁ with
      | none =>
        cases opt₂ with
        | none => rfl
        | some v₂ =>
          injection h_eq with h_op
          injection h_op with h_imm
          exact False.elim (valToMiriImmediate_ne_uninit h₂ h₁.1 h₁.2 h_imm.symm)
      | some v₁ =>
        cases opt₂ with
        | none =>
          injection h_eq with h_op
          injection h_op with h_imm
          exact False.elim (valToMiriImmediate_ne_uninit h₁ h₂.1 h₂.2 h_imm)
        | some v₂ =>
          injection h_eq with h_op
          injection h_op with h_imm
          rw [valToMiriImmediate_inj h₁ h₂ h_imm]

theorem liftLocals_inj (types : List MirTy) {tys : List MirTy}
    {slots₁ slots₂ : List LocalSlot}
    (h₁ : SlotsMatchTys tys slots₁) (h₂ : SlotsMatchTys tys slots₂)
    (h_eq : liftLocals types tys slots₁ = liftLocals types tys slots₂) :
    slots₁ = slots₂ := by
  induction h₁ generalizing slots₂ with
  | nil =>
    cases h₂
    rfl
  | cons hm₁ _ ih =>
    cases h₂ with
    | cons hm₂ h_tl₂ =>
      dsimp only [liftLocals] at h_eq
      injection h_eq with h_hd h_tl
      have h_val := congrArg Miri.Interpreter.LocalState.value h_hd
      dsimp only [refLocalStateOfSlot] at h_val
      rw [slotToMiriLocalValue_inj hm₁ hm₂ h_val, ih h_tl₂ h_tl]

private noncomputable def refDiscrStmtOk (localTys : List MirTy)
    (stmt : RefStatementKind) : Bool :=
  match stmt with
  | .assign dst rv =>
    match rv with
    | .discriminant src =>
      if dst.projection.isEmpty && src.projection.isEmpty then
        match MirSemantics.getElem? localTys src.localId with
        | some srcTy =>
          match srcTy with
          | .enum ety =>
            match MirSemantics.getElem? localTys dst.localId with
            | some dstTy =>
              if refEnumAdmitted ety then
                MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
              else true
            | none => true
          | _ => true
        | none => true
      else true
    | _ => true
  | _ => true

private noncomputable def discrStmtOk (localTys : List MirTy)
    (stmt : StatementKind) : Bool :=
  match stmt with
  | .assign dst rv =>
    match rv with
    | .discriminant src =>
      if dst.projection.isEmpty && src.projection.isEmpty then
        match MirSemantics.getElem? localTys src.localId with
        | some srcTy =>
          match srcTy with
          | .enum ety =>
            match MirSemantics.getElem? localTys dst.localId with
            | some dstTy =>
              if enumAdmitted ety then
                MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
              else true
            | none => true
          | _ => true
        | none => true
      else true
    | _ => true
  | _ => true

private theorem refDiscrStmtOk_eq {ts : List MirTy} {localTys : List MirTy}
    {rstmt : RefStatementKind} {stmt : StatementKind}
    (h_dec : decodeStmt ts rstmt = some stmt) :
    refDiscrStmtOk localTys rstmt = discrStmtOk localTys stmt := by
  cases rstmt with
  | nop => injection h_dec with h; subst h; rfl
  | storageLive _ => injection h_dec with h; subst h; rfl
  | storageDead _ => injection h_dec with h; subst h; rfl
  | unsupported => injection h_dec with h; subst h; rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt] at h_dec
    cases h_d : decodePlace ts rdst with
    | none => rw [h_d] at h_dec; cases h_dec
    | some dst =>
      rw [h_d] at h_dec
      cases h_rv : decodeRvalue ts rrv with
      | none => rw [h_rv] at h_dec; cases h_dec
      | some rv =>
        rw [h_rv] at h_dec
        injection h_dec with h_s
        subst h_s
        cases rrv with
        | discriminant rsrc =>
          dsimp only [decodeRvalue] at h_rv
          cases h_sp : decodePlace ts rsrc with
          | none => rw [h_sp] at h_rv; cases h_rv
          | some src =>
            rw [h_sp] at h_rv
            injection h_rv with h_rv_eq
            subst h_rv_eq
            let ⟨h_did, h_demp⟩ := decodePlace_inv h_d
            let ⟨h_sid, h_semp⟩ := decodePlace_inv h_sp
            dsimp only [refDiscrStmtOk, discrStmtOk]
            rw [h_demp, h_semp, h_did, h_sid]
            cases (dst.projection.isEmpty && src.projection.isEmpty) with
            | false => rfl
            | true =>
              cases MirSemantics.getElem? localTys src.localId with
              | none => rfl
              | some srcTy =>
                cases srcTy with
                | enum ety =>
                  cases MirSemantics.getElem? localTys dst.localId with
                  | none => rfl
                  | some dstTy =>
                    dsimp only
                    rw [refEnumAdmitted_eq]
                | _ => rfl
        | use ro =>
          dsimp only [decodeRvalue] at h_rv
          cases h_o : decodeOperand ts ro with
          | none => rw [h_o] at h_rv; cases h_rv
          | some _ => rw [h_o] at h_rv; injection h_rv with h; subst h; rfl
        | binaryOp _ rl rr =>
          dsimp only [decodeRvalue] at h_rv
          cases h_l : decodeOperand ts rl with
          | none => rw [h_l] at h_rv; cases h_rv
          | some _ =>
            rw [h_l] at h_rv
            cases h_r : decodeOperand ts rr with
            | none => rw [h_r] at h_rv; cases h_rv
            | some _ => rw [h_r] at h_rv; injection h_rv with h; subst h; rfl
        | unaryOp _ ro =>
          dsimp only [decodeRvalue] at h_rv
          cases h_o : decodeOperand ts ro with
          | none => rw [h_o] at h_rv; cases h_rv
          | some _ => rw [h_o] at h_rv; injection h_rv with h; subst h; rfl
        | ref _ rp =>
          dsimp only [decodeRvalue] at h_rv
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h_rv; cases h_rv
          | some _ => rw [h_p] at h_rv; injection h_rv with h; subst h; rfl
        | addressOf _ rp =>
          dsimp only [decodeRvalue] at h_rv
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h_rv; cases h_rv
          | some _ => rw [h_p] at h_rv; injection h_rv with h; subst h; rfl
        | aggregateTuple rops =>
          dsimp only [decodeRvalue] at h_rv
          cases h_os : mapOption (decodeOperand ts) rops with
          | none => rw [h_os] at h_rv; cases h_rv
          | some _ => rw [h_os] at h_rv; injection h_rv with h; subst h; rfl
        | unsupported => injection h_rv with h; subst h; rfl

theorem refDiscriminantTypesValid_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body} (h_dec : decodeBody ts rbody = some body) :
    refDiscriminantTypesValid body.locals rbody = discriminantTypesValid body := by
  dsimp only [decodeBody] at h_dec
  cases h_locs : decodeLocalTys ts rbody.locals with
  | none => rw [h_locs] at h_dec; cases h_dec
  | some locs =>
    rw [h_locs] at h_dec
    cases h_bbs : mapOption (decodeBasicBlock ts) rbody.basicBlocks with
    | none => rw [h_bbs] at h_dec; cases h_dec
    | some bbs =>
      rw [h_bbs] at h_dec
      injection h_dec with h_b
      subst h_b
      change rbody.basicBlocks.all (fun bb =>
          bb.statements.all (refDiscrStmtOk locs)) =
        bbs.all (fun bb => bb.statements.all (discrStmtOk locs))
      have h_all_st : ∀ (rsts : List RefStatementKind)
          (sts : List StatementKind),
          mapOption (decodeStmt ts) rsts = some sts →
          rsts.all (refDiscrStmtOk locs) = sts.all (discrStmtOk locs) := by
        intro rsts
        induction rsts with
        | nil =>
          intro sts hm
          dsimp only [mapOption] at hm
          injection hm with h_n; subst h_n; rfl
        | cons rs rrest ihs =>
          intro sts hm
          dsimp only [mapOption] at hm
          cases h_s : decodeStmt ts rs with
          | none => rw [h_s] at hm; cases hm
          | some s =>
            rw [h_s] at hm
            cases h_rr : mapOption (decodeStmt ts) rrest with
            | none => rw [h_rr] at hm; cases hm
            | some srest =>
              rw [h_rr] at hm
              injection hm with h_c; subst h_c
              dsimp only [List.all]
              rw [refDiscrStmtOk_eq h_s, ihs srest h_rr]
      have h_all_bb : ∀ (rbbs : List RefBasicBlock) (bbs' : List BasicBlock),
          mapOption (decodeBasicBlock ts) rbbs = some bbs' →
          rbbs.all (fun bb => bb.statements.all (refDiscrStmtOk locs)) =
            bbs'.all (fun bb => bb.statements.all (discrStmtOk locs)) := by
        intro rbbs
        induction rbbs with
        | nil =>
          intro bbs' h_m
          dsimp only [mapOption] at h_m
          injection h_m with h_nil; subst h_nil; rfl
        | cons rbb rest ih =>
          intro bbs' h_m
          dsimp only [mapOption] at h_m
          cases h_bb : decodeBasicBlock ts rbb with
          | none => rw [h_bb] at h_m; cases h_m
          | some bb =>
            rw [h_bb] at h_m
            cases h_rest : mapOption (decodeBasicBlock ts) rest with
            | none => rw [h_rest] at h_m; cases h_m
            | some rest' =>
              rw [h_rest] at h_m
              injection h_m with h_cons; subst h_cons
              dsimp only [List.all]
              rw [ih rest' h_rest]
              dsimp only [decodeBasicBlock] at h_bb
              cases h_st : mapOption (decodeStmt ts) rbb.statements with
              | none => rw [h_st] at h_bb; cases h_bb
              | some stmts =>
                rw [h_st] at h_bb
                cases h_tm : decodeTerminator ts rbb.terminator with
                | none => rw [h_tm] at h_bb; cases h_bb
                | some tm =>
                  rw [h_tm] at h_bb
                  injection h_bb with h_bb_eq; subst h_bb_eq
                  rw [h_all_st rbb.statements stmts h_st]
      exact h_all_bb rbody.basicBlocks bbs h_bbs

end MiriEquiv

/-- One-to-one uniqueness of `SimulationInv` (left-injective): any `RefState`
`rs` corresponds to at most one $M_{\text{anneal}}$ `State`. -/
theorem state_unique_of_simulationInv_base :
    StateUniqueOfSimulationInvClaim := by
  intro rp p s₁ s₂ rs h₁ h₂
  let ⟨f₁, rf₁, retTy₁, mem₁, ctrl₁, _, hs₁, _, _, _, _, _, hmiri₁,
    hframe₁⟩ := h₁
  let ⟨f₂, rf₂, retTy₂, mem₂, ctrl₂, _, hs₂, _, _, _, _, _, hmiri₂,
    hframe₂⟩ := h₂
  rw [hmiri₁] at hmiri₂
  dsimp only [mkRefMiriState] at hmiri₂
  have h_stack := congrArg Miri.Interpreter.StepState.stack hmiri₂
  have h_machine := congrArg Miri.Interpreter.StepState.machine hmiri₂
  injection h_stack with h_frames
  injection h_frames with h_list
  injection h_list with h_rf_eq
  subst h_rf_eq
  have h_cm : s₁.callerMem = s₂.callerMem := by
    have h_u := congrArg Miri.Interpreter.MachineHooks.MachineState.user h_machine
    exact congrArg RefUser.callerMem h_u
  let ⟨body₁, rbody₁, hb₁, _, _, _, _, _, _, hsl₁, _, hrf₁⟩ := hframe₁
  let ⟨body₂, rbody₂, hb₂, _, _, _, _, _, _, hsl₂, _, hrf₂⟩ := hframe₂
  have h_rf_eq' := hrf₁.symm.trans hrf₂
  have h_def : f₁.defId = f₂.defId := by
    have h_bi := congrArg Miri.Interpreter.Frame.bodyIdentity h_rf_eq'
    dsimp only [mkRefMiriFrame, Miri.Interpreter.BodyIdentity.ofCanonicalIndex]
      at h_bi
    injection h_bi
  have h_loc := congrArg Miri.Interpreter.Frame.location h_rf_eq'
  dsimp only [mkRefMiriFrame] at h_loc
  injection h_loc with h_mirloc
  injection h_mirloc with h_blk h_stmt
  rw [h_def] at hb₁
  rw [hb₁] at hb₂
  injection hb₂ with h_body_eq
  subst h_body_eq
  have h_locs_arr := congrArg Miri.Interpreter.Frame.locals h_rf_eq'
  dsimp only [mkRefMiriFrame] at h_locs_arr
  injection h_locs_arr with h_lifted
  have h_slots : f₁.locals = f₂.locals :=
    liftLocals_inj rp.types hsl₁ hsl₂ h_lifted
  have h_f : f₁ = f₂ := by
    cases f₁; cases f₂
    dsimp only at h_def h_blk h_stmt h_slots
    rw [h_def, h_blk, h_stmt, h_slots]
  subst h_f
  cases s₁; cases s₂
  dsimp only at hs₁ hs₂ h_cm
  rw [hs₁, hs₂, h_cm]

end Anneal.MirCorrespondence
