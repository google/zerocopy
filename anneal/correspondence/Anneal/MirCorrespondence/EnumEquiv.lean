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

theorem refIsPrimitiveReadableTy_eq (ty : MirTy) :
    refIsPrimitiveReadableTy ty = isPrimitiveReadableTy ty := by
  cases ty <;> rfl

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

private noncomputable def runDirectTagFinal (S : Type) (uninhabited : Bool)
    (v : Nat) : Miri.Interpreter.RvalueM S Nat :=
  let jp := fun (_ : Unit) => (Pure.pure v : Miri.Interpreter.RvalueM S Nat)
  if uninhabited then
    Bind.bind
      (throw (.undefinedBehavior
        (toString "UninhabitedEnumVariantRead(" ++ toString v ++ toString ")")))
      jp
  else
    jp ()

private noncomputable def runDirectTagAfterLookup (S : Type) (ety₀ : EnumTy)
    (optIdx : Option Nat) : Miri.Interpreter.RvalueM S Nat :=
  Bind.bind
    (fun s' => .ok optIdx s' : Miri.Interpreter.RvalueM S (Option Nat))
    (fun opt =>
      match opt with
      | some index =>
        runDirectTagFinal S
          ((refEnumLayoutData ety₀).isVariantUninhabited index) index
      | _ =>
        throw (.undefinedBehavior "InvalidTag(no declared discriminant)"))

private noncomputable def runDirectTagAfterTrunc (S : Type) (ety₀ : EnumTy)
    (truncRes : Except SizeError (BitVec 128)) :
    Miri.Interpreter.RvalueM S Nat :=
  let jp := fun (discrBits : BitVec 128) =>
    runDirectTagAfterLookup S ety₀
      (refFindDiscrVariant? discrBits ety₀.discriminants)
  match truncRes with
  | .ok v => Bind.bind (Pure.pure v) jp
  | .error e => Bind.bind (throw (.invalidProgram (toString e))) jp

private noncomputable def runDirectTagAfterSignExt (S : Type) (ety₀ : EnumTy)
    (discrW : IntWidth) (extRes : Except SizeError Int) :
    Miri.Interpreter.RvalueM S Nat :=
  let jpExt := fun (extended : BitVec 128) =>
    runDirectTagAfterTrunc S ety₀ ((toMiriSize discrW).truncate extended)
  let jpInt := fun (integer : Int) =>
    Bind.bind (Pure.pure (BitVec.ofInt 128 integer)) jpExt
  match extRes with
  | .ok v => Bind.bind (Pure.pure v) jpInt
  | .error e => Bind.bind (throw (.invalidProgram (toString e))) jpInt

private noncomputable def runDirectTagAction (S : Type) (ety₀ : EnumTy)
    (tagW : IntWidth) (tagS : Bool) (discrW : IntWidth)
    (inRange : Bool) (b₀ : BitVec 128) : Miri.Interpreter.RvalueM S Nat :=
  let jpRange := fun (_ : Unit) =>
    let jpExt := fun (extended : BitVec 128) =>
      runDirectTagAfterTrunc S ety₀ ((toMiriSize discrW).truncate extended)
    if tagS then
      let jpInt := fun (integer : Int) =>
        Bind.bind (Pure.pure (BitVec.ofInt 128 integer)) jpExt
      match (toMiriSize tagW).signExtend b₀ with
      | .ok v => Bind.bind (Pure.pure v) jpInt
      | .error e => Bind.bind (throw (.invalidProgram (toString e))) jpInt
    else
      Bind.bind (Pure.pure b₀) jpExt
  if !inRange then
    Bind.bind (throw (.undefinedBehavior "InvalidTag(outside valid range)"))
      jpRange
  else
    jpRange ()

theorem readDiscriminant_enum_scalar_eq (S : Type)
    (ety : EnumTy) (tagW : IntWidth) (tagS : Bool) (raw : BitVec 128) (s : S)
    (h_tr : ety.tagRepr = .scalar tagW tagS) :
    Miri.Interpreter.runRvalue
      (Miri.Interpreter.Discriminant.readDiscriminant
        (refDiscriminantHooks S ety) ()
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW raw))),
          ⟨0, refEnumLayoutData ety⟩⟩) s =
    match findDiscrVariant?
        (tagBitsToDiscrBits tagW tagS ety.discrWidth (truncateBits tagW raw))
        ety.discriminants with
    | some v => (s, .ok v)
    | none =>
      (s, .error (.undefinedBehavior
        "InvalidTag(no declared discriminant)")) := by
  cases ety with
  | mk id discrW discrS tr ds =>
    dsimp only at h_tr
    subst h_tr
    let ety₀ := EnumTy.mk id discrW discrS (.scalar tagW tagS) ds
    have h_step :
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.Discriminant.readDiscriminant
            (refDiscriminantHooks S ety₀) ()
            ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW raw))),
              ⟨0, refEnumLayoutData ety₀⟩⟩) s =
        Miri.Interpreter.runRvalue
          (runDirectTagAction S ety₀ tagW tagS discrW
            ((fullRangeOf tagW).contains (miriScalar tagW raw).data)
            (miriScalar tagW raw).data) s := by
      cases tagW <;> cases tagS <;> cases discrW <;> rfl
    rw [h_step, miriScalar_data, fullRangeOf_contains_truncateBits]
    cases tagS with
    | false =>
      have h₁ :
          Miri.Interpreter.runRvalue
            (runDirectTagAction S ety₀ tagW false discrW true
              (truncateBits tagW raw)) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterTrunc S ety₀
              ((toMiriSize discrW).truncate (truncateBits tagW raw))) s := rfl
      rw [h₁, size_truncate_eq]
      have h₂ :
          Miri.Interpreter.runRvalue
            (runDirectTagAfterTrunc S ety₀
              (.ok (truncateBits discrW (truncateBits tagW raw)))) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterLookup S ety₀
              (refFindDiscrVariant?
                (truncateBits discrW (truncateBits tagW raw)) ds)) s := rfl
      rw [h₂, refFindDiscrVariant?_eq]
      dsimp only [tagBitsToDiscrBits]
      rw [ite_false_eq_true, truncateBits_idem]
      cases h_f : findDiscrVariant?
          (truncateBits discrW (truncateBits tagW raw)) ds with
      | none => rfl
      | some v =>
        have h₃ :
            Miri.Interpreter.runRvalue
              (runDirectTagAfterLookup S ety₀ (some v)) s =
            Miri.Interpreter.runRvalue
              (runDirectTagFinal S
                ((refEnumLayoutData ety₀).isVariantUninhabited v) v) s := rfl
        rw [h₃]
        dsimp only [ety₀, LayoutData.isVariantUninhabited, refEnumLayoutData]
        rw [array_map_inhabited_getElem?_uninhabited ds v
          (findDiscrVariant?_lt h_f)]
        rfl
    | true =>
      have h₁ :
          Miri.Interpreter.runRvalue
            (runDirectTagAction S ety₀ tagW true discrW true
              (truncateBits tagW raw)) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterSignExt S ety₀ discrW
              ((toMiriSize tagW).signExtend (truncateBits tagW raw))) s := rfl
      rw [h₁, size_signExtend_eq]
      have h₂ :
          Miri.Interpreter.runRvalue
            (runDirectTagAfterSignExt S ety₀ discrW
              (.ok (signExtendBits tagW (truncateBits tagW raw)))) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterTrunc S ety₀
              ((toMiriSize discrW).truncate
                (BitVec.ofInt 128
                  (signExtendBits tagW (truncateBits tagW raw))))) s := rfl
      rw [h₂, bitVec_ofInt_eq, size_truncate_eq]
      have h₃ :
          Miri.Interpreter.runRvalue
            (runDirectTagAfterTrunc S ety₀
              (.ok (truncateBits discrW
                (bvOfInt 128
                  (signExtendBits tagW (truncateBits tagW raw)))))) s =
          Miri.Interpreter.runRvalue
            (runDirectTagAfterLookup S ety₀
              (refFindDiscrVariant?
                (truncateBits discrW
                  (bvOfInt 128
                    (signExtendBits tagW (truncateBits tagW raw))))
                ds)) s := rfl
      rw [h₃, refFindDiscrVariant?_eq]
      dsimp only [tagBitsToDiscrBits]
      rw [ite_true_eq_true]
      cases h_f : findDiscrVariant?
          (truncateBits discrW
            (bvOfInt 128 (signExtendBits tagW (truncateBits tagW raw)))) ds with
      | none => rfl
      | some v =>
        have h₄ :
            Miri.Interpreter.runRvalue
              (runDirectTagAfterLookup S ety₀ (some v)) s =
            Miri.Interpreter.runRvalue
              (runDirectTagFinal S
                ((refEnumLayoutData ety₀).isVariantUninhabited v) v) s := rfl
        rw [h₄]
        dsimp only [ety₀, LayoutData.isVariantUninhabited, refEnumLayoutData]
        rw [array_map_inhabited_getElem?_uninhabited ds v
          (findDiscrVariant?_lt h_f)]
        rfl

private theorem match_readDiscr_eq_runRvalue {α : Type}
    (m : Miri.Interpreter.RvalueM Unit Nat)
    (onOk : Nat → α) (onUb onErr : α) :
    (match m () with
    | .ok v _ => onOk v
    | .error (.undefinedBehavior _) _ => onUb
    | .error _ _ => onErr) =
    (match (Miri.Interpreter.runRvalue m ()).2 with
    | .ok v => onOk v
    | .error (.undefinedBehavior _) => onUb
    | .error _ => onErr) := by
  dsimp only [Miri.Interpreter.runRvalue]
  cases m () with
  | ok _ _ => rfl
  | error e _ => cases e <;> rfl

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
      have h_unfold :
          evalRefConstLit (.enum ety) (.scalar bits) =
            match ety.tagRepr with
            | .zeroSized => .error .unsupported
            | .scalar tagW _ =>
              if !refEnumAdmitted ety then
                .error .unsupported
              else
                match ScalarInt.tryFromUInt bits (toMiriSize tagW) with
                | .ok (some sc) =>
                  let op : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
                    ⟨.immediate (.scalar (.fromScalarInt sc)),
                      ⟨0, refEnumLayoutData ety⟩⟩
                  match (Miri.Interpreter.runRvalue
                      (Miri.Interpreter.Discriminant.readDiscriminant
                        (refDiscriminantHooks Unit ety) () op) ()).2 with
                  | .ok v => .ok (.enumVal ety v)
                  | .error (.undefinedBehavior _) => .error .undefined
                  | .error _ => .error .unsupported
                | _ => .error .unsupported := by
        cases ety with
        | mk id dw ds tr discrs =>
          cases tr with
          | zeroSized => rfl
          | scalar tw ts =>
            let ety' : EnumTy := ⟨id, dw, ds, .scalar tw ts, discrs⟩
            dsimp only [evalRefConstLit]
            cases refEnumAdmitted ety' with
            | false => rfl
            | true =>
              rw [Bool.not_true, ite_false_eq_true, ite_false_eq_true]
              cases ScalarInt.tryFromUInt bits (toMiriSize tw) with
              | error _ => rfl
              | ok optSc =>
                cases optSc with
                | none => rfl
                | some sc =>
                  dsimp only
                  exact @match_readDiscr_eq_runRvalue (Except FaultKind Val)
                    (Miri.Interpreter.Discriminant.readDiscriminant
                      (refDiscriminantHooks Unit ety') ()
                      ⟨.immediate (.scalar (.fromScalarInt sc)),
                        ⟨0, refEnumLayoutData ety'⟩⟩)
                    (fun v => .ok (.enumVal ety' v))
                    (.error .undefined)
                    (.error .unsupported)
      rw [h_unfold]
      dsimp only [evalConstLit]
      cases h_tr : ety.tagRepr with
      | zeroSized => rfl
      | scalar tagW tagS =>
        dsimp only
        rw [refEnumAdmitted_eq]
        cases h_adm : enumAdmitted ety with
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
            rw [readDiscriminant_enum_scalar_eq Unit ety tagW tagS bits
              () h_tr]
            rw [truncateBits_eq_of_beq_false h_ov]
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

theorem evalRefSwitchScalarCase_eq (ts : List MirTy)
    (callerMem : CallerMemory) (sv : ScalarVal) (caseBits : BitVec 128)
    (st : Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout
      Unit RefStepMachine) :
    (refTerminatorHooksFor ts callerMem).compareSwitchCase () (.scalar sv)
        caseBits.toNat st =
      (st,
        if truncateBits sv.width caseBits != caseBits then
          .error (faultToStepError .unsupported)
        else
          .ok (truncateBits sv.width sv.bits ==
            truncateBits sv.width caseBits)) := by
  dsimp only [refTerminatorHooksFor]
  rw [bitVec128_ofNat_toNat caseBits]
  apply congrArg (Prod.mk st)
  rw [evalRefConstLit_eq]
  dsimp only [evalConstLit]
  cases h_ov : (truncateBits sv.width caseBits != caseBits) with
  | true => rfl
  | false =>
    rw [ite_false_eq_true, ite_false_eq_true]
    change (match evalRefBinOp .eq (.scalar sv)
          (.scalar ⟨sv.width, sv.signed,
            truncateBits sv.width caseBits⟩) with
      | .ok (.bool eq) => Except.ok eq
      | .error k => .error (faultToStepError k)
      | .ok _ => .error (.unsupported "non-bool SwitchInt Eq result")) = _
    rw [evalRefBinOp_eq]
    dsimp only [evalBinOp]
    have h_w : IntWidth.beq sv.width sv.width = true := by
      cases sv.width <;> rfl
    rw [h_w, beq_self_eq_true]
    change Except.ok (decodeScalar sv ==
        decodeScalar ⟨sv.width, sv.signed, truncateBits sv.width caseBits⟩) = _
    rw [decodeScalar_beq_eq, truncateBits_idem]

theorem evalRefSwitchBoolCase_eq (ts : List MirTy)
    (callerMem : CallerMemory) (b : Bool) (caseBits : BitVec 128)
    (st : Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout
      Unit RefStepMachine) :
    (refTerminatorHooksFor ts callerMem).compareSwitchCase () (.bool b)
        caseBits.toNat st =
      (st,
        match evalConstLit .bool (.scalar caseBits) with
        | .ok (.bool cb) => .ok (b == cb)
        | .error k => .error (faultToStepError k)
        | .ok _ => .error (faultToStepError .unsupported)) := by
  dsimp only [refTerminatorHooksFor]
  rw [bitVec128_ofNat_toNat caseBits]
  apply congrArg (Prod.mk st)
  rw [evalRefConstLit_eq]
  cases evalConstLit .bool (.scalar caseBits) with
  | error k => rfl
  | ok v =>
    cases v with
    | bool cb =>
      change (match evalRefBinOp .eq (.bool b) (.bool cb) with
        | .ok (.bool eq) => Except.ok eq
        | .error k => .error (faultToStepError k)
        | .ok _ => .error (.unsupported "non-bool SwitchInt Eq result")) = _
      rw [evalRefBinOp_eq]
      rfl
    | scalar _ | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => rfl

end MiriEquiv

end Anneal.MirCorrespondence
