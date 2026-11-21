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
import Anneal.MirCorrespondence.EnumEquiv

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# Operand and Rvalue Step Simulation (`Anneal.MirCorrespondence.RvalueStep`)

Proves per-operand and per-rvalue step equivalence between $M_{\text{anneal}}$
and $M_{\text{ref}}$.
-/

private theorem evalRefPlaceOperand_dead (rlocals : List RefLocalState)
    (localId : LocalId) (ty : MirTy) (isMove : Bool)
    (h_get : MirSemantics.getElem? rlocals localId = some ⟨.dead, some ty⟩) :
    evalRefPlaceOperand rlocals localId true isMove = .error .undefined := by
  dsimp only [evalRefPlaceOperand, Bool.not]
  rw [ite_false_eq_true, h_get]
  cases isMove <;> (
    cases ty with
    | enum ety =>
      dsimp only [refLocalLayoutForTy]
      cases refIsZstEnumTy ety <;> rfl
    | _ => rfl)

private theorem evalRefPlaceOperand_live_copy (rlocals : List RefLocalState)
    (localId : LocalId) (optVal : Option Val) (ty : MirTy)
    (h_get : MirSemantics.getElem? rlocals localId =
      some ⟨.live optVal, some ty⟩) :
    evalRefPlaceOperand rlocals localId true false =
      .ok (ty, optVal, rlocals) := by
  dsimp only [evalRefPlaceOperand, Bool.not]
  rw [ite_false_eq_true, h_get]
  cases ty with
  | enum ety =>
    dsimp only [refLocalLayoutForTy]
    cases refIsZstEnumTy ety <;> rfl
  | _ => rfl

private theorem evalRefPlaceOperand_live_move (rlocals : List RefLocalState)
    (localId : LocalId) (optVal : Option Val) (ty : MirTy)
    (h_get : MirSemantics.getElem? rlocals localId =
      some ⟨.live optVal, some ty⟩) :
    evalRefPlaceOperand rlocals localId true true =
      match MirSemantics.setElem? rlocals localId
          ⟨liveUninitSlot ty, some ty⟩ with
      | some rlocals' => .ok (ty, optVal, rlocals')
      | none => .error .unsupported := by
  dsimp only [evalRefPlaceOperand, Bool.not]
  rw [ite_false_eq_true, h_get]
  rw [← refLiveUninitSlot_eq ty]
  cases ty with
  | enum ety =>
    dsimp only [refLocalLayoutForTy, refLiveUninitSlot]
    cases refIsZstEnumTy ety <;> rfl
  | _ => rfl

private theorem toMiriPlace_proj_isEmpty (rp : RefPlace) :
    (toMiriPlace rp).projection.isEmpty = rp.projection.isEmpty := by
  cases rp with | mk _ proj => cases proj <;> rfl

theorem evalRefMiriOperandToSlot_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {rop : RefOperand} {op : Operand}
    (h_dec : decodeOperand ts rop = some op) :
    evalRefMiriOperandToSlot ts (zipRefLocals bodyLocals slots)
        (toMiriOperand rop) =
      mapSlotRes bodyLocals (evalOperandToSlot bodyLocals slots op) := by
  cases rop with
  | copy rp =>
    dsimp only [decodeOperand, optMap] at h_dec
    cases h_pl : decodePlace ts rp with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some p =>
      rw [h_pl] at h_dec
      injection h_dec with h_op
      subst h_op
      let ⟨h_id, h_emp⟩ := decodePlace_inv h_pl
      dsimp only [toMiriOperand, evalRefMiriOperandToSlot, evalOperandToSlot]
      rw [toMiriPlace_proj_isEmpty, h_emp]
      change evalRefPlaceOperand (zipRefLocals bodyLocals slots) rp.localId
          p.projection.isEmpty false = _
      rw [h_id]
      cases p.projection.isEmpty
      · rfl
      · cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
        | none =>
          dsimp only [evalRefPlaceOperand, Bool.not]
          rw [ite_false_eq_true, getElem?_zipRefLocals_none_left h_ty]
          rfl
        | some ty =>
          cases h_sl : MirSemantics.getElem? slots p.localId with
          | none =>
            dsimp only [evalRefPlaceOperand, Bool.not]
            rw [ite_false_eq_true, getElem?_zipRefLocals_none_right h_sl]
            rfl
          | some slot =>
            have h_z := getElem?_zipRefLocals_some h_ty h_sl
            cases slot with
            | dead =>
              rw [evalRefPlaceOperand_dead _ _ _ _ h_z]
              rfl
            | live optVal =>
              rw [evalRefPlaceOperand_live_copy _ _ _ _ h_z]
              rfl
  | move rp =>
    dsimp only [decodeOperand, optMap] at h_dec
    cases h_pl : decodePlace ts rp with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some p =>
      rw [h_pl] at h_dec
      injection h_dec with h_op
      subst h_op
      let ⟨h_id, h_emp⟩ := decodePlace_inv h_pl
      dsimp only [toMiriOperand, evalRefMiriOperandToSlot, evalOperandToSlot]
      rw [toMiriPlace_proj_isEmpty, h_emp]
      change evalRefPlaceOperand (zipRefLocals bodyLocals slots) rp.localId
          p.projection.isEmpty true = _
      rw [h_id]
      cases p.projection.isEmpty
      · rfl
      · cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
        | none =>
          dsimp only [evalRefPlaceOperand, Bool.not]
          rw [ite_false_eq_true, getElem?_zipRefLocals_none_left h_ty]
          rfl
        | some ty =>
          cases h_sl : MirSemantics.getElem? slots p.localId with
          | none =>
            dsimp only [evalRefPlaceOperand, Bool.not]
            rw [ite_false_eq_true, getElem?_zipRefLocals_none_right h_sl]
            rfl
          | some slot =>
            have h_z := getElem?_zipRefLocals_some h_ty h_sl
            cases slot with
            | dead =>
              rw [evalRefPlaceOperand_dead _ _ _ _ h_z]
              rfl
            | live optVal =>
              rw [evalRefPlaceOperand_live_move _ _ _ _ h_z]
              dsimp only
              cases h_set :
                  MirSemantics.setElem? slots p.localId (liveUninitSlot ty) with
              | none =>
                rw [setElem?_zipRefLocals_none h_set]
                rfl
              | some slots' =>
                rw [setElem?_zipRefLocals_some h_ty h_set]
                rfl
  | constant rc =>
    dsimp only [decodeOperand, optMap] at h_dec
    cases h_ty : MirSemantics.getElem? ts rc.ty with
    | none => rw [h_ty] at h_dec; cases h_dec
    | some ty =>
      rw [h_ty] at h_dec
      injection h_dec with h_op
      subst h_op
      cases rc with
      | mk tyId lit =>
        cases lit with
        | scalar bits =>
          dsimp only [toMiriOperand, evalRefMiriOperandToSlot,
            evalOperandToSlot]
          dsimp only at h_ty
          rw [h_ty, bitVec128_ofNat_toNat bits]
          dsimp only
          rw [evalRefConstLit_eq]
          cases evalConstLit ty (.scalar bits) <;> rfl
        | zeroSized =>
          dsimp only [toMiriOperand, evalRefMiriOperandToSlot,
            evalOperandToSlot]
          dsimp only at h_ty
          rw [h_ty]
          dsimp only
          rw [evalRefConstLit_eq]
          cases evalConstLit ty .zeroSized <;> rfl

theorem readRefPrimitiveSlot_eq (ty : MirTy) (optVal : Option Val) :
    readRefPrimitiveSlot ty optVal =
      if !isPrimitiveReadableTy ty then
        .error .unsupported
      else
        match optVal with
        | some v => .ok v
        | none => .error .undefined := by
  dsimp only [readRefPrimitiveSlot]
  rw [refIsPrimitiveReadableTy_eq]
  cases isPrimitiveReadableTy ty <;> rfl

theorem writeRefPlace_eq {bodyLocals : List MirTy} {slots : List LocalSlot}
    {dstLocalId : LocalId} {dstTy : MirTy} {val : Val}
    (h_ty : MirSemantics.getElem? bodyLocals dstLocalId = some dstTy) :
    writeRefPlace (zipRefLocals bodyLocals slots) dstLocalId dstTy val =
      mapSlotsRes bodyLocals (writePlace slots dstLocalId dstTy val) := by
  unfold writeRefPlace writePlace
  rw [checkRefVal_eq]
  cases checkVal val dstTy
  · rfl
  · cases h_sl : MirSemantics.getElem? slots dstLocalId with
    | none =>
      rw [getElem?_zipRefLocals_none_right h_sl]
      rfl
    | some slot =>
      rw [getElem?_zipRefLocals_some h_ty h_sl]
      cases slot with
      | dead => rfl
      | live _ =>
        dsimp only
        cases h_set :
            MirSemantics.setElem? slots dstLocalId (.live (some val)) with
        | none =>
          rw [setElem?_zipRefLocals_none h_set]
          rfl
        | some slots' =>
          rw [setElem?_zipRefLocals_some h_ty h_set]
          rfl

private theorem miriImmToPayload?_roundtrip {α : Type}
    (x : α) :
    miriImmediateToPayload? (payloadToMiriImmediate x) = some x := rfl

private theorem evalRefMiriRvalue_use (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId) (dstSlot : LocalSlot)
    (dstTy : MirTy) (rop : RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some dstTy⟩) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.empty⟩
        (toMiriRvalue (.use rop)) =
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
      | .error k => .error k
      | .ok (srcTy, optVal, rlocals₁) =>
        if !(MirTy.beq srcTy dstTy) then
          .error .unsupported
        else
          match optVal with
          | some v => writeRefPlace rlocals₁ dstId dstTy v
          | none => .error .undefined := by
  have h_arr :
      (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false := rfl
  dsimp only [evalRefMiriRvalue, toMiriRvalue,
    Miri.Interpreter.evalRvalueIntoPlace,
    Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
    Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
    EStateM.pure]
  rw [h_arr, ite_false_eq_true, h_dst]
  dsimp only
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨srcTy, optVal, rlocals₁⟩ := res
    dsimp only
    rw [miriImmToPayload?_roundtrip]
    dsimp only
    cases MirTy.beq srcTy dstTy
    · rfl
    · cases optVal with
      | none => rfl
      | some v =>
        dsimp only
        cases writeRefPlace rlocals₁ dstId dstTy v with
        | error k => cases k <;> rfl
        | ok _ => rfl

private theorem evalRefMiriRvalue_binaryOp (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId) (dstSlot : LocalSlot)
    (dstTy : MirTy) (op : BinOp) (lhs rhs : RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some dstTy⟩) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.empty⟩
        (toMiriRvalue (.binaryOp op lhs rhs)) =
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand lhs) with
      | .error k => .error k
      | .ok (lTy, lOpt, rlocals₁) =>
        match readRefPrimitiveSlot lTy lOpt with
        | .error k => .error k
        | .ok lVal =>
          match evalRefMiriOperandToSlot ts rlocals₁ (toMiriOperand rhs) with
          | .error k => .error k
          | .ok (rTy, rOpt, rlocals₂) =>
            match readRefPrimitiveSlot rTy rOpt with
            | .error k => .error k
            | .ok rVal =>
              match evalRefBinOp op lVal rVal with
              | .error k => .error k
              | .ok v => writeRefPlace rlocals₂ dstId dstTy v := by
  have h_arr :
      (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false := rfl
  have h_step :
      Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.binaryOp op lhs rhs)) ⟨dstId, Array.empty⟩
          rlocals =
        match evalRefMiriOperandToSlot ts rlocals (toMiriOperand lhs) with
        | .error k => .error (faultToStepError k) rlocals
        | .ok (lTy, lOpt, rlocals₁) =>
          match readRefPrimitiveSlot lTy lOpt with
          | .error k => .error (faultToStepError k) rlocals₁
          | .ok lVal =>
            match evalRefMiriOperandToSlot ts rlocals₁ (toMiriOperand rhs) with
            | .error k => .error (faultToStepError k) rlocals₁
            | .ok (rTy, rOpt, rlocals₂) =>
              match readRefPrimitiveSlot rTy rOpt with
              | .error k => .error (faultToStepError k) rlocals₂
              | .ok rVal =>
                match evalRefBinOp op lVal rVal with
                | .error k =>
                  .error (faultToStepError k) rlocals₂
                | .ok v =>
                  match writeRefPlace rlocals₂ dstId dstTy v with
                  | .error k =>
                    .error (faultToStepError k) rlocals₂
                  | .ok locals' => .ok () locals' := by
    dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
      Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
      evalRefBinOp, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
    rw [h_arr, ite_false_eq_true, h_dst]
    dsimp only
    cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand lhs) with
    | error _ => rfl
    | ok resL =>
      let ⟨lTy, lOpt, rlocals₁⟩ := resL
      dsimp only
      rw [miriImmToPayload?_roundtrip]
      dsimp only
      cases readRefPrimitiveSlot lTy lOpt with
      | error _ => rfl
      | ok lVal =>
        dsimp only
        cases evalRefMiriOperandToSlot ts rlocals₁ (toMiriOperand rhs) with
        | error _ => rfl
        | ok resR =>
          let ⟨rTy, rOpt, rlocals₂⟩ := resR
          dsimp only
          rw [miriImmToPayload?_roundtrip]
          dsimp only
          cases readRefPrimitiveSlot rTy rOpt with
          | error _ => rfl
          | ok rVal =>
            dsimp only
            rw [miriImmToPayload?_roundtrip,
              miriImmToPayload?_roundtrip]
            dsimp only
            cases evalRefMiriBinOp (toMiriBinOp op) lVal rVal with
            | error _ => rfl
            | ok v =>
              dsimp only
              rw [miriImmToPayload?_roundtrip]
              rfl
  dsimp only [evalRefMiriRvalue, Miri.Interpreter.runRvalue]
  rw [h_step]
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand lhs) with
  | error k => cases k <;> rfl
  | ok resL =>
    let ⟨lTy, lOpt, rlocals₁⟩ := resL
    dsimp only
    cases readRefPrimitiveSlot lTy lOpt with
    | error k => cases k <;> rfl
    | ok lVal =>
      dsimp only
      cases evalRefMiriOperandToSlot ts rlocals₁ (toMiriOperand rhs) with
      | error k => cases k <;> rfl
      | ok resR =>
        let ⟨rTy, rOpt, rlocals₂⟩ := resR
        dsimp only
        cases readRefPrimitiveSlot rTy rOpt with
        | error k => cases k <;> rfl
        | ok rVal =>
          dsimp only
          cases evalRefBinOp op lVal rVal with
          | error k => cases k <;> rfl
          | ok v =>
            dsimp only
            cases writeRefPlace rlocals₂ dstId dstTy v with
            | error k => cases k <;> rfl
            | ok _ => rfl

private theorem evalRefMiriRvalue_unaryOp (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId) (dstSlot : LocalSlot)
    (dstTy : MirTy) (op : UnOp) (rop : RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some dstTy⟩) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.empty⟩
        (toMiriRvalue (.unaryOp op rop)) =
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
      | .error k => .error k
      | .ok (ty, optVal, rlocals₁) =>
        match readRefPrimitiveSlot ty optVal with
        | .error k => .error k
        | .ok v =>
          match evalRefUnOp op v with
          | .error k => .error k
          | .ok u => writeRefPlace rlocals₁ dstId dstTy u := by
  have h_arr :
      (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false := rfl
  have h_step :
      Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.unaryOp op rop)) ⟨dstId, Array.empty⟩
          rlocals =
        match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
        | .error k => .error (faultToStepError k) rlocals
        | .ok (ty, optVal, rlocals₁) =>
          match readRefPrimitiveSlot ty optVal with
          | .error k => .error (faultToStepError k) rlocals₁
          | .ok v =>
            match evalRefUnOp op v with
            | .error k => .error (faultToStepError k) rlocals₁
            | .ok u =>
              match writeRefPlace rlocals₁ dstId dstTy u with
              | .error k => .error (faultToStepError k) rlocals₁
              | .ok locals' => .ok () locals' := by
    dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
      Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
      evalRefUnOp, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
    rw [h_arr, ite_false_eq_true, h_dst]
    dsimp only
    cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
    | error _ => rfl
    | ok res =>
      let ⟨ty, optVal, rlocals₁⟩ := res
      dsimp only
      rw [miriImmToPayload?_roundtrip]
      dsimp only
      cases readRefPrimitiveSlot ty optVal with
      | error _ => rfl
      | ok v =>
        dsimp only
        rw [miriImmToPayload?_roundtrip]
        dsimp only
        cases evalRefMiriUnOp (toMiriUnOp op) v with
        | error _ => rfl
        | ok u =>
          dsimp only
          rw [miriImmToPayload?_roundtrip]
          rfl
  dsimp only [evalRefMiriRvalue, Miri.Interpreter.runRvalue]
  rw [h_step]
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨ty, optVal, rlocals₁⟩ := res
    dsimp only
    cases readRefPrimitiveSlot ty optVal with
    | error k => cases k <;> rfl
    | ok v =>
      dsimp only
      cases evalRefUnOp op v with
      | error k => cases k <;> rfl
      | ok u =>
        dsimp only
        cases writeRefPlace rlocals₁ dstId dstTy u with
        | error k => cases k <;> rfl
        | ok _ => rfl

private theorem list_all_of_getElem? {α : Type} {xs : List α} {p : α → Bool}
    {i : Nat} {x : α} (h_all : xs.all p = true)
    (h_get : MirSemantics.getElem? xs i = some x) : p x = true := by
  induction xs generalizing i with
  | nil => cases h_get
  | cons y rest ih =>
    dsimp only [List.all] at h_all
    cases hy : p y <;> rw [hy] at h_all
    · cases h_all
    · cases i with
      | zero =>
        injection h_get with h_eq
        subst h_eq
        exact hy
      | succ j =>
        exact ih h_all h_get

private theorem natNotElem_ne_of_getElem? {d : Nat} {xs : List Nat} {i : Nat}
    {x : Nat} (h_not : natNotElem d xs = true)
    (h_get : MirSemantics.getElem? xs i = some x) : d ≠ x := by
  induction xs generalizing i with
  | nil => cases h_get
  | cons y rest ih =>
    dsimp only [natNotElem] at h_not
    cases h_eq : Nat.beq d y <;> rw [h_eq] at h_not
    · cases i with
      | zero =>
        injection h_get with hyx
        subst hyx
        intro h_dx
        subst h_dx
        rw [Nat.beq_refl] at h_eq
        cases h_eq
      | succ j =>
        exact ih h_not h_get
    · cases h_not

private theorem findDiscrVariantAux_of_getElem? {w : IntWidth}
    {ds : List Nat} {idx : Nat} {disc : Nat} (k : Nat)
    (h_all : ds.all (fun d => Nat.blt d (Nat.pow 2 w.bitWidth)) = true)
    (h_pw : natListPairwiseNe ds = true)
    (h_get : MirSemantics.getElem? ds idx = some disc) :
    findDiscrVariantAux k (BitVec.ofNat 128 disc) ds = some (k + idx) := by
  induction ds generalizing k idx with
  | nil => cases h_get
  | cons d rest ih =>
    dsimp only [List.all] at h_all
    cases hd_blt : Nat.blt d (Nat.pow 2 w.bitWidth) <;> rw [hd_blt] at h_all
    · cases h_all
    · dsimp only [natListPairwiseNe] at h_pw
      cases h_not : natNotElem d rest <;> rw [h_not] at h_pw
      · cases h_pw
      · have h_all' :
            rest.all (fun d => Nat.blt d (Nat.pow 2 w.bitWidth)) = true := h_all
        have h_pw' : natListPairwiseNe rest = true := h_pw
        cases idx with
        | zero =>
          injection h_get with h_eq
          subst h_eq
          dsimp only [findDiscrVariantAux]
          have h_self :
              (BitVec.ofNat 128 d == BitVec.ofNat 128 d) = true :=
            beq_self_eq_true _
          rw [h_self]
          rw [Nat.add_zero]
          rfl
        | succ j =>
          dsimp only [MirSemantics.getElem?] at h_get
          have h_ne : d ≠ disc := natNotElem_ne_of_getElem? h_not h_get
          have hd_u128 : d < Nat.pow 2 128 :=
            Nat.lt_of_lt_of_le (nat_lt_of_blt_eq_true hd_blt)
              (intWidth_modulus_le_u128 w)
          have hdisc_blt : Nat.blt disc (Nat.pow 2 w.bitWidth) = true :=
            @list_all_of_getElem? Nat rest
              (fun d => Nat.blt d (Nat.pow 2 w.bitWidth)) j disc h_all' h_get
          have hdisc_u128 : disc < Nat.pow 2 128 :=
            Nat.lt_of_lt_of_le (nat_lt_of_blt_eq_true hdisc_blt)
              (intWidth_modulus_le_u128 w)
          have h_bv_false :
              (BitVec.ofNat 128 d == BitVec.ofNat 128 disc) = false := by
            cases h_b : (BitVec.ofNat 128 d == BitVec.ofNat 128 disc) with
            | false => rfl
            | true =>
              have h_tn := congrArg BitVec.toNat (eq_of_beq h_b)
              rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hd_u128, Nat.mod_eq_of_lt hdisc_u128] at h_tn
              exact False.elim (h_ne h_tn)
          dsimp only [findDiscrVariantAux]
          rw [h_bv_false, ite_false_eq_true]
          rw [ih (k + 1) h_all' h_pw' h_get, Nat.add_right_comm k 1 j,
              Nat.add_assoc]

private theorem findDiscrVariant?_of_getElem? {w : IntWidth}
    {ds : List Nat} {idx : Nat} {disc : Nat}
    (h_all : ds.all (fun d => Nat.blt d (Nat.pow 2 w.bitWidth)) = true)
    (h_pw : natListPairwiseNe ds = true)
    (h_get : MirSemantics.getElem? ds idx = some disc) :
    findDiscrVariant? (BitVec.ofNat 128 disc) ds = some idx := by
  have h := findDiscrVariantAux_of_getElem? 0 h_all h_pw h_get
  rw [Nat.zero_add] at h
  exact h

private theorem enumAdmitted_unpack {ety : EnumTy}
    (h : enumAdmitted ety = true) :
    ety.discriminants.all
        (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) = true ∧
      natListPairwiseNe ety.discriminants = true ∧
      (∀ tagW tagS, ety.tagRepr = .scalar tagW tagS →
        ety.discriminants.all (fun d =>
          let dBits := BitVec.ofNat 128 d
          tagBitsToDiscrBits tagW tagS ety.discrWidth
            (truncateBits tagW dBits) == dBits) = true) := by
  dsimp only [enumAdmitted] at h
  cases h1 : (!ety.discriminants.isEmpty) <;> rw [h1] at h
  · cases h
  · cases h2 : Nat.blt ety.discriminants.length (Nat.pow 2 32) <;> rw [h2] at h
    · cases h
    · cases h3 :
          ety.discriminants.all
            (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) <;>
        rw [h3] at h
      · cases h
      · cases h4 : natListPairwiseNe ety.discriminants <;> rw [h4] at h
        · cases h
        · dsimp only [Bool.and] at h
          refine ⟨rfl, rfl, fun tagW tagS h_tr => ?_⟩
          rw [h_tr] at h
          exact h

private theorem refScalarLayoutData_size (w : IntWidth) (signed : Bool) :
    (refScalarLayoutData w signed).size = toMiriSize w := by
  cases w <;> cases signed <;> rfl

private theorem discriminantForVariant_concrete_ok {ts : List MirTy}
    (tid : TyId) (ety : EnumTy) (variant disc : Nat)
    (s : List RefLocalState)
    (h_ty : MirSemantics.getElem? ts tid = some (.enum ety))
    (h_adm : enumAdmitted ety = true)
    (h_disc : MirSemantics.getElem? ety.discriminants variant = some disc) :
    ((refRvalueHooks ts).discriminantForVariant () tid variant s) =
      .ok ⟨payloadToMiriImmediate
            (.int ety.discrWidth ety.discrSigned,
              some (.scalar ⟨ety.discrWidth, ety.discrSigned,
                truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)),
          ⟨1, refScalarLayoutData ety.discrWidth ety.discrSigned⟩⟩ s := by
  let ⟨h_all, _, _⟩ := enumAdmitted_unpack h_adm
  have hd_blt : Nat.blt disc (Nat.pow 2 ety.discrWidth.bitWidth) = true :=
    @list_all_of_getElem? Nat ety.discriminants
      (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth))
      variant disc h_all h_disc
  have hd_mod : disc < Nat.pow 2 ety.discrWidth.bitWidth :=
    nat_lt_of_blt_eq_true hd_blt
  have hd_u128 : disc < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hd_mod (intWidth_modulus_le_u128 ety.discrWidth)
  have h_trunc_eq :
      truncateBits ety.discrWidth (BitVec.ofNat 128 disc) =
        BitVec.ofNat 128 disc := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_truncateBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd_u128]
    exact Nat.mod_eq_of_lt hd_mod
  have h_bne_false :
      (truncateBits ety.discrWidth (BitVec.ofNat 128 disc) !=
        BitVec.ofNat 128 disc) = false := by
    rw [h_trunc_eq]
    exact bne_self_eq_false _
  have h_from_uint :
      Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
        (BitVec.ofNat 128 disc) (toMiriSize ety.discrWidth) =
      .ok (.fromScalarInt (miriScalar ety.discrWidth
        (BitVec.ofNat 128 disc))) := by
    dsimp only [Miri.Memory.Scalar.fromUInt]
    rw [tryFromUInt_eq_truncateFromUInt,
        truncateFromUInt_eq_miriScalar ety.discrWidth (BitVec.ofNat 128 disc),
        h_bne_false]
    rfl
  dsimp only [refRvalueHooks]
  rw [h_ty]
  dsimp only [Miri.Interpreter.Discriminant.discriminantForVariant,
    refDiscriminantHooks, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
    Nat.beq, ite_true_eq_true]
  rw [h_disc]
  have h_ty_bne : ((1 : Nat) != 1) = false := rfl
  dsimp only
  rw [h_ty_bne, ite_false_eq_true]
  dsimp only [EStateM.bind, EStateM.pure]
  rw [refScalarLayoutData_size, h_from_uint,
      ← miriScalar_data ety.discrWidth (BitVec.ofNat 128 disc)]
  rfl

private theorem discriminantForVariant_concrete_none {ts : List MirTy}
    (tid : TyId) (ety : EnumTy) (variant : Nat)
    (s : List RefLocalState)
    (h_ty : MirSemantics.getElem? ts tid = some (.enum ety))
    (h_none : MirSemantics.getElem? ety.discriminants variant = none) :
    ((refRvalueHooks ts).discriminantForVariant () tid variant s) =
      .error (.invalidProgram "enum variant out of bounds") s := by
  dsimp only [refRvalueHooks]
  rw [h_ty]
  dsimp only [Miri.Interpreter.Discriminant.discriminantForVariant,
    refDiscriminantHooks, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
  rw [h_none]
  rfl

private theorem evalPlaceToOp_enum_dead (tid : TyId) (ety : EnumTy) :
    (Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false)
      (mkSingleLocalMiriFrameWithLayout (slotToMiriLocalValue .dead)
        ⟨tid, refEnumLayoutData ety⟩ false) () ⟨0, Array.empty⟩
      (some ⟨tid, refEnumLayoutData ety⟩)).outcome =
    .error (.stack (.localExpectedLive 0)) := by
  cases ety with
  | mk _ _ _ tr _ => cases tr <;> rfl

private theorem evalPlaceToOp_enum_live (tid : TyId) (ety : EnumTy)
    (optVal : Option Val) :
    (Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false)
      (mkSingleLocalMiriFrameWithLayout (slotToMiriLocalValue (.live optVal))
        ⟨tid, refEnumLayoutData ety⟩ false) () ⟨0, Array.empty⟩
      (some ⟨tid, refEnumLayoutData ety⟩)).outcome =
    .ok ⟨.immediate (payloadToMiriImmediate optVal),
      ⟨tid, refEnumLayoutData ety⟩⟩ := by
  cases ety with
  | mk _ _ _ tr _ => cases tr <;> rfl

private theorem evalRefMiriRvalue_discriminant_eq {ts : List MirTy}
    (rlocals : List RefLocalState) (dstId : LocalId) (dstSlot : LocalSlot)
    (dstTy : MirTy) (rp : RefPlace)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some dstTy⟩)
    (h_tys : ∀ (id : LocalId) (slot : LocalSlot) (ety : EnumTy),
      MirSemantics.getElem? rlocals id = some ⟨slot, some (.enum ety)⟩ →
      ∃ tid, MirSemantics.getElem? ts tid = some (.enum ety)) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.empty⟩
        (toMiriRvalue (.discriminant rp)) =
      if !rp.projection.isEmpty then
        .error .unsupported
      else
        match MirSemantics.getElem? rlocals rp.localId with
        | some ⟨slot, some (.enum ety)⟩ =>
          if !enumAdmitted ety then
            .error .unsupported
          else
            match ety.tagRepr, slot with
            | _, .dead => .error .undefined
            | .zeroSized, .live none =>
              match MirSemantics.getElem? ety.discriminants 0 with
              | some disc =>
                writeRefPlace rlocals dstId dstTy
                  (.scalar ⟨ety.discrWidth, ety.discrSigned,
                    truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
              | none => .error .unsupported
            | .zeroSized, .live (some (.enumVal ety' v)) =>
              if EnumTy.beq ety ety' && Nat.beq v 0 then
                match MirSemantics.getElem? ety.discriminants 0 with
                | some disc =>
                  writeRefPlace rlocals dstId dstTy
                    (.scalar ⟨ety.discrWidth, ety.discrSigned,
                      truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
                | none => .error .unsupported
              else
                .error .unsupported
            | .zeroSized, .live (some _) => .error .unsupported
            | .scalar _ _, .live none => .error .undefined
            | .scalar _ _, .live (some (.enumVal ety' v)) =>
              if EnumTy.beq ety ety' && Nat.blt v ety.discriminants.length then
                match MirSemantics.getElem? ety.discriminants v with
                | some disc =>
                  writeRefPlace rlocals dstId dstTy
                    (.scalar ⟨ety.discrWidth, ety.discrSigned,
                      truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
                | none => .error .unsupported
              else
                .error .unsupported
            | .scalar _ _, .live (some _) => .error .unsupported
        | _ => .error .unsupported := by
  let mapErr : Miri.Interpreter.StepError →
      Except FaultKind (List RefLocalState) :=
    fun err =>
      match err with
      | .undefinedBehavior _ | .stack (.localExpectedLive _) =>
        .error .undefined
      | _ => .error .unsupported
  let finishDiscr : Miri.Interpreter.OpTy (MirTy × Option Val) →
      List RefLocalState → Except FaultKind (List RefLocalState) :=
    fun op s₁ =>
      match (refRvalueHooks ts).readDiscriminant () op s₁ with
      | .error err _ => mapErr err
      | .ok variant s₂ =>
        match (refRvalueHooks ts).discriminantForVariant
            () op.layout.ty variant s₂ with
        | .error err _ => mapErr err
        | .ok discr s₃ =>
          match miriImmediateToPayload? discr.imm with
          | some (_, some v) => writeRefPlace s₃ dstId dstTy v
          | _ => .error .unsupported
  have h_arr :
      (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false := rfl
  have h_unfold :
      evalRefMiriRvalue ts rlocals ⟨dstId, Array.empty⟩
          (toMiriRvalue (.discriminant rp)) =
        match evalRefEnumPlaceToOp ts (toMiriPlace rp) rlocals with
        | .error err _ => mapErr err
        | .ok op s₁ => finishDiscr op s₁ := by
    dsimp only [evalRefMiriRvalue, toMiriRvalue,
      Miri.Interpreter.evalRvalueIntoPlace, refRvalueHooks,
      Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
      EStateM.pure]
    rw [h_arr, ite_false_eq_true, h_dst]
    dsimp only
    cases evalRefEnumPlaceToOp ts (toMiriPlace rp) rlocals with
    | error err s₁ =>
      cases err with | stack se => cases se <;> rfl | _ => rfl
    | ok op s₁ =>
      dsimp only [finishDiscr, refRvalueHooks]
      cases op.op with
      | indirect _ => rfl
      | immediate imm =>
        dsimp only
        cases miriImmediateToPayload? imm with
        | none => rfl
        | some payload =>
          cases payload with
          | mk ty optVal =>
            cases ty with
            | enum ety₁ =>
              dsimp only
              cases encodeRefEnumTagOp ety₁ optVal with
              | error err =>
                cases err with | stack se => cases se <;> rfl | _ => rfl
              | ok miriOp =>
                dsimp only
                cases Miri.Interpreter.Discriminant.readDiscriminant
                    (refDiscriminantHooks (List RefLocalState) ety₁)
                    () miriOp s₁ with
                | error err s₂ =>
                  cases err with | stack se => cases se <;> rfl | _ => rfl
                | ok variant s₂ =>
                  dsimp only
                  cases MirSemantics.getElem? ts op.layout.ty with
                  | none => rfl
                  | some ty₂ =>
                    cases ty₂ with
                    | enum ety₂ =>
                      dsimp only
                      cases Miri.Interpreter.Discriminant.discriminantForVariant
                          (refDiscriminantHooks (List RefLocalState) ety₂)
                          () 0 variant s₂ with
                      | error err s₃ =>
                        cases err with | stack se => cases se <;> rfl | _ => rfl
                      | ok discr s₃ =>
                        dsimp only
                        cases discr.imm with
                        | scalar msc =>
                          dsimp only
                          cases msc.tryToScalarInt with
                          | ok cr =>
                            cases cr with
                            | integer sc =>
                              dsimp only
                              rw [miriImmToPayload?_roundtrip]
                              dsimp only
                              cases writeRefPlace s₃ dstId dstTy
                                  (.scalar ⟨ety₂.discrWidth, ety₂.discrSigned,
                                    sc.data⟩) with
                              | error k => cases k <;> rfl
                              | ok _ => rfl
                            | _ => rfl
                          | error _ => rfl
                        | _ => rfl
                    | _ => rfl
            | _ => rfl
  rw [h_unfold]
  cases rp with
  | mk localId proj =>
    cases proj with
    | cons _ _ => rfl
    | nil =>
      have h_p : toMiriPlace ⟨localId, []⟩ = ⟨localId, Array.empty⟩ := rfl
      rw [h_p]
      dsimp only [List.isEmpty, Bool.not]
      rw [ite_false_eq_true]
      cases h_get : MirSemantics.getElem? rlocals localId with
      | none =>
        have h_op :
            evalRefEnumPlaceToOp ts ⟨localId, Array.empty⟩ rlocals =
              .error (.unsupported "Discriminant on non-enum local")
                rlocals := by
          dsimp only [evalRefEnumPlaceToOp]
          rw [h_arr, ite_false_eq_true, h_get]
        rw [h_op]
      | some rloc =>
        cases rloc with
        | mk slot optTy =>
          cases optTy with
          | none =>
            have h_op :
                evalRefEnumPlaceToOp ts ⟨localId, Array.empty⟩ rlocals =
                  .error (.unsupported "Discriminant on non-enum local")
                    rlocals := by
              dsimp only [evalRefEnumPlaceToOp]
              rw [h_arr, ite_false_eq_true, h_get]
            rw [h_op]
          | some localTy =>
            cases localTy with
            | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _
            | unsupported =>
              have h_op :
                  evalRefEnumPlaceToOp ts ⟨localId, Array.empty⟩ rlocals =
                    .error (.unsupported "Discriminant on non-enum local")
                      rlocals := by
                dsimp only [evalRefEnumPlaceToOp]
                rw [h_arr, ite_false_eq_true, h_get]
              rw [h_op]
            | enum ety =>
              dsimp only
              cases h_adm : enumAdmitted ety with
              | false =>
                dsimp only [Bool.not]
                rw [ite_true_eq_true]
                have h_op :
                    evalRefEnumPlaceToOp ts ⟨localId, Array.empty⟩ rlocals =
                      .error (.unsupported "unadmitted enum in Discriminant")
                        rlocals := by
                  dsimp only [evalRefEnumPlaceToOp]
                  rw [h_arr, ite_false_eq_true, h_get]
                  dsimp only
                  rw [refEnumAdmitted_eq, h_adm]
                  rfl
                rw [h_op]
              | true =>
                dsimp only [Bool.not]
                rw [ite_false_eq_true]
                let ⟨i_ty, h_i_ty⟩ := h_tys localId slot ety h_get
                let ⟨enumTyId, h_idx⟩ := indexOfTy_some_of_getElem? h_i_ty
                have h_tid :
                    MirSemantics.getElem? ts enumTyId = some (.enum ety) :=
                  getElem?_of_indexOfTy h_idx
                cases slot with
                | dead =>
                  have h_op :
                      evalRefEnumPlaceToOp ts ⟨localId, Array.empty⟩ rlocals =
                        .error (.stack (.localExpectedLive 0)) rlocals := by
                    dsimp only [evalRefEnumPlaceToOp]
                    rw [h_arr, ite_false_eq_true, h_get]
                    dsimp only
                    rw [refEnumAdmitted_eq, h_adm]
                    dsimp only [Bool.not]
                    rw [ite_false_eq_true, h_idx]
                    dsimp only
                    rw [evalPlaceToOp_enum_dead enumTyId ety]
                  rw [h_op]
                | live optVal =>
                  let layout : Miri.Interpreter.LocalLayout :=
                    ⟨enumTyId, refEnumLayoutData ety⟩
                  have h_op :
                      evalRefEnumPlaceToOp ts ⟨localId, Array.empty⟩ rlocals =
                        .ok ⟨.immediate (payloadToMiriImmediate
                              (.enum ety, optVal)), layout⟩ rlocals := by
                    dsimp only [evalRefEnumPlaceToOp]
                    rw [h_arr, ite_false_eq_true, h_get]
                    dsimp only
                    rw [refEnumAdmitted_eq, h_adm]
                    dsimp only [Bool.not]
                    rw [ite_false_eq_true, h_idx]
                    dsimp only
                    rw [evalPlaceToOp_enum_live enumTyId ety optVal]
                    rfl
                  rw [h_op]
                  dsimp only [finishDiscr]
                  cases h_tr : ety.tagRepr with
                  | zeroSized =>
                    have h_zst_rd :
                        Miri.Interpreter.Discriminant.readDiscriminant
                          (refDiscriminantHooks (List RefLocalState) ety) ()
                          ⟨.immediate .uninit, ⟨0, refEnumLayoutData ety⟩⟩
                          rlocals =
                        .ok 0 rlocals := by
                      cases ety with
                      | mk id dw ds tr discrs =>
                        dsimp only at h_tr
                        subst h_tr
                        rfl
                    cases optVal with
                    | none =>
                      have h_rd :
                          (refRvalueHooks ts).readDiscriminant ()
                            ⟨.immediate (payloadToMiriImmediate
                              (.enum ety, none)), layout⟩ rlocals =
                          .ok 0 rlocals := by
                        dsimp only [refRvalueHooks, encodeRefEnumTagOp]
                        rw [miriImmToPayload?_roundtrip]
                        dsimp only
                        rw [h_tr]
                        exact h_zst_rd
                      rw [h_rd]
                      dsimp only
                      cases h_d0 :
                          MirSemantics.getElem? ety.discriminants 0 with
                      | none =>
                        rw [discriminantForVariant_concrete_none enumTyId ety 0
                          rlocals h_tid h_d0]
                      | some disc =>
                        rw [discriminantForVariant_concrete_ok enumTyId ety 0
                          disc rlocals h_tid h_adm h_d0]
                        rfl
                    | some val =>
                      cases val with
                      | enumVal ety' v =>
                        dsimp only
                        cases h_chk :
                            (EnumTy.beq ety ety' && Nat.beq v 0) with
                        | false =>
                          have h_rd :
                              (refRvalueHooks ts).readDiscriminant ()
                                ⟨.immediate (payloadToMiriImmediate
                                  (.enum ety, some (.enumVal ety' v))),
                                  layout⟩ rlocals =
                              .error (.unsupported
                                "mismatched ZST enum variant in slot")
                                rlocals := by
                            dsimp only [refRvalueHooks, encodeRefEnumTagOp]
                            rw [miriImmToPayload?_roundtrip]
                            dsimp only
                            rw [h_tr]
                            dsimp only
                            rw [h_chk]
                            rfl
                          rw [h_rd]
                          rfl
                        | true =>
                          have h_rd :
                              (refRvalueHooks ts).readDiscriminant ()
                                ⟨.immediate (payloadToMiriImmediate
                                  (.enum ety, some (.enumVal ety' v))),
                                  layout⟩ rlocals =
                              .ok 0 rlocals := by
                            dsimp only [refRvalueHooks, encodeRefEnumTagOp]
                            rw [miriImmToPayload?_roundtrip]
                            dsimp only
                            rw [h_tr]
                            dsimp only
                            rw [h_chk]
                            exact h_zst_rd
                          rw [h_rd, ite_true_eq_true]
                          dsimp only
                          cases h_d0 :
                              MirSemantics.getElem? ety.discriminants 0 with
                          | none =>
                            rw [discriminantForVariant_concrete_none enumTyId
                              ety 0 rlocals h_tid h_d0]
                          | some disc =>
                            rw [discriminantForVariant_concrete_ok enumTyId ety
                              0 disc rlocals h_tid h_adm h_d0]
                            rfl
                      | _ =>
                        dsimp only [refRvalueHooks, encodeRefEnumTagOp]
                        rw [miriImmToPayload?_roundtrip]
                        dsimp only
                        rw [h_tr]
                  | scalar tagW tagS =>
                    cases optVal with
                    | none =>
                      have h_uninit_ub :
                          (refRvalueHooks ts).readDiscriminant ()
                            ⟨.immediate (payloadToMiriImmediate
                              (.enum ety, none)), layout⟩ rlocals =
                          .error (.undefinedBehavior
                            "InvalidUninitBytes(None)") rlocals := by
                        cases ety with
                        | mk id dw ds tr discrs =>
                          dsimp only at h_tr
                          subst h_tr
                          cases tagW <;> cases tagS <;> rfl
                      rw [h_uninit_ub]
                    | some val =>
                      cases val with
                      | enumVal ety' v =>
                        dsimp only
                        cases h_chk :
                            (EnumTy.beq ety ety' &&
                              Nat.blt v ety.discriminants.length) with
                        | false =>
                          have h_rd :
                              (refRvalueHooks ts).readDiscriminant ()
                                ⟨.immediate (payloadToMiriImmediate
                                  (.enum ety, some (.enumVal ety' v))),
                                  layout⟩ rlocals =
                              .error (.unsupported
                                "mismatched scalar enum variant in slot")
                                rlocals := by
                            dsimp only [refRvalueHooks, encodeRefEnumTagOp]
                            rw [miriImmToPayload?_roundtrip]
                            dsimp only
                            rw [h_tr]
                            dsimp only
                            rw [h_chk]
                            rfl
                          rw [h_rd]
                          rfl
                        | true =>
                          rw [ite_true_eq_true]
                          cases h_dv :
                              MirSemantics.getElem? ety.discriminants v with
                          | none =>
                            have h_rd :
                                (refRvalueHooks ts).readDiscriminant ()
                                  ⟨.immediate (payloadToMiriImmediate
                                    (.enum ety, some (.enumVal ety' v))),
                                    layout⟩ rlocals =
                                .error (.invalidProgram
                                  "missing enum discriminant") rlocals := by
                              dsimp only [refRvalueHooks, encodeRefEnumTagOp]
                              rw [miriImmToPayload?_roundtrip]
                              dsimp only
                              rw [h_tr]
                              dsimp only
                              rw [h_chk, ite_true_eq_true, h_dv]
                            rw [h_rd]
                          | some disc =>
                            have h_rd_eq :
                                (refRvalueHooks ts).readDiscriminant ()
                                  ⟨.immediate (payloadToMiriImmediate
                                    (.enum ety, some (.enumVal ety' v))),
                                    layout⟩ rlocals =
                                match findDiscrVariant?
                                    (tagBitsToDiscrBits tagW tagS
                                      ety.discrWidth
                                      (truncateBits tagW
                                        (BitVec.ofNat 128 disc)))
                                    ety.discriminants with
                                | some idx => .ok idx rlocals
                                | none =>
                                  .error (.undefinedBehavior
                                    "InvalidTag(no declared discriminant)")
                                    rlocals := by
                              have h_rr := readDiscriminant_enum_scalar_eq
                                (List RefLocalState) ety tagW tagS
                                (BitVec.ofNat 128 disc) rlocals h_tr
                              dsimp only [refRvalueHooks, encodeRefEnumTagOp]
                              rw [miriImmToPayload?_roundtrip]
                              dsimp only
                              rw [h_tr]
                              dsimp only
                              rw [h_chk, ite_true_eq_true, h_dv]
                              dsimp only
                              rw [truncateFromUInt_eq_miriScalar tagW
                                (BitVec.ofNat 128 disc)]
                              dsimp only
                              dsimp only [Miri.Interpreter.runRvalue] at h_rr
                              cases h_m :
                                  Miri.Interpreter.Discriminant.readDiscriminant
                                    (refDiscriminantHooks
                                      (List RefLocalState) ety) ()
                                    ⟨.immediate (.scalar (.fromScalarInt
                                        (miriScalar tagW
                                          (BitVec.ofNat 128 disc)))),
                                      ⟨0, refEnumLayoutData ety⟩⟩ rlocals with
                              | ok idx s_out =>
                                rw [h_m] at h_rr
                                dsimp only at h_rr
                                cases h_fv : findDiscrVariant?
                                    (tagBitsToDiscrBits tagW tagS
                                      ety.discrWidth
                                      (truncateBits tagW
                                        (BitVec.ofNat 128 disc)))
                                    ety.discriminants <;>
                                  rw [h_fv] at h_rr
                                · cases h_rr
                                · injection h_rr with hs_eq hok_eq
                                  injection hok_eq with hi_eq
                                  rw [hs_eq, hi_eq]
                              | error err s_out =>
                                rw [h_m] at h_rr
                                dsimp only at h_rr
                                cases h_fv : findDiscrVariant?
                                    (tagBitsToDiscrBits tagW tagS
                                      ety.discrWidth
                                      (truncateBits tagW
                                        (BitVec.ofNat 128 disc)))
                                    ety.discriminants <;>
                                  rw [h_fv] at h_rr
                                · injection h_rr with hs_eq herr_eq
                                  injection herr_eq with he_eq
                                  rw [hs_eq, he_eq]
                                · cases h_rr
                            rw [h_rd_eq]
                            let ⟨h_all, h_pw, h_rt_fn⟩ :=
                              enumAdmitted_unpack h_adm
                            have h_rt_beq :=
                              @list_all_of_getElem? Nat ety.discriminants
                                (fun d =>
                                  let dBits := BitVec.ofNat 128 d
                                  tagBitsToDiscrBits tagW tagS ety.discrWidth
                                    (truncateBits tagW dBits) == dBits)
                                v disc (h_rt_fn tagW tagS h_tr) h_dv
                            dsimp only at h_rt_beq
                            have h_rt_eq :
                                tagBitsToDiscrBits tagW tagS ety.discrWidth
                                  (truncateBits tagW (BitVec.ofNat 128 disc)) =
                                BitVec.ofNat 128 disc := eq_of_beq h_rt_beq
                            have h_find :
                                findDiscrVariant? (BitVec.ofNat 128 disc)
                                  ety.discriminants = some v :=
                              findDiscrVariant?_of_getElem? h_all h_pw h_dv
                            rw [h_rt_eq, h_find]
                            dsimp only
                            rw [discriminantForVariant_concrete_ok enumTyId ety
                              v disc rlocals h_tid h_adm h_dv]
                            rfl
                      | _ =>
                        dsimp only [refRvalueHooks, encodeRefEnumTagOp]
                        rw [miriImmToPayload?_roundtrip]
                        dsimp only
                        rw [h_tr]

private theorem evalRefMiriRvalue_ref (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId) (dstSlot : LocalSlot)
    (dstTy : MirTy) (m : Mutability) (rp : RefPlace)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some dstTy⟩) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.empty⟩
        (toMiriRvalue (.ref m rp)) = .error .unsupported := by
  have h_arr :
      (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false := rfl
  cases m <;> (
    dsimp only [evalRefMiriRvalue, toMiriRvalue,
      Miri.Interpreter.evalRvalueIntoPlace, refRvalueHooks,
      Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
      EStateM.pure]
    rw [h_arr, ite_false_eq_true, h_dst]
    dsimp only
    cases rp with
    | mk srcId srcProj =>
      cases srcProj with
      | cons _ _ => rfl
      | nil =>
        have h_p : toMiriPlace ⟨srcId, []⟩ = ⟨srcId, Array.empty⟩ := rfl
        rw [h_p]
        dsimp only
        rw [h_arr, ite_false_eq_true]
        cases MirSemantics.getElem? rlocals srcId with
        | none => rfl
        | some rloc =>
          cases rloc with
          | mk _ optTy => cases optTy <;> rfl)

private theorem evalRefMiriRvalue_addressOf (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId) (dstSlot : LocalSlot)
    (dstTy : MirTy) (m : Mutability) (rp : RefPlace)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some dstTy⟩) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.empty⟩
        (toMiriRvalue (.addressOf m rp)) = .error .unsupported := by
  have h_arr :
      (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false := rfl
  cases m <;> (
    dsimp only [evalRefMiriRvalue, toMiriRvalue,
      Miri.Interpreter.evalRvalueIntoPlace, refRvalueHooks,
      Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
      EStateM.pure]
    rw [h_arr, ite_false_eq_true, h_dst]
    dsimp only
    cases rp with
    | mk srcId srcProj =>
      cases srcProj with
      | cons _ _ => rfl
      | nil =>
        have h_p : toMiriPlace ⟨srcId, []⟩ = ⟨srcId, Array.empty⟩ := rfl
        rw [h_p]
        dsimp only
        rw [h_arr, ite_false_eq_true]
        cases MirSemantics.getElem? rlocals srcId with
        | none => rfl
        | some rloc =>
          cases rloc with
          | mk _ optTy => cases optTy <;> rfl)

private theorem evalRefMiriRvalue_aggregateTuple (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId) (dstSlot : LocalSlot)
    (dstTy : MirTy) (rops : List RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some dstTy⟩) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.empty⟩
        (toMiriRvalue (.aggregateTuple rops)) = .error .unsupported := by
  have h_arr :
      (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false := rfl
  dsimp only [evalRefMiriRvalue, toMiriRvalue,
    Miri.Interpreter.evalRvalueIntoPlace, refRvalueHooks,
    Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
    EStateM.pure]
  rw [h_arr, ite_false_eq_true, h_dst]

private theorem evalRefMiriRvalue_unsupported (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId) (dstSlot : LocalSlot)
    (dstTy : MirTy)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some dstTy⟩) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.empty⟩
        (toMiriRvalue .unsupported) = .error .unsupported := by
  have h_arr :
      (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false := rfl
  dsimp only [evalRefMiriRvalue, toMiriRvalue,
    Miri.Interpreter.evalRvalueIntoPlace, refRvalueHooks,
    Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
    EStateM.pure]
  rw [h_arr, ite_false_eq_true, h_dst]
  rfl

theorem evalRefMiriRvalue_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot} {rdst : RefPlace} {dst : Place}
    {rrv : RefRvalue} {rv : Rvalue}
    (h_len : slots.length = bodyLocals.length)
    (h_tys : ∀ (id : LocalId) (ty : MirTy),
      MirSemantics.getElem? bodyLocals id = some ty →
      ∃ tid, MirSemantics.getElem? ts tid = some ty)
    (h_pl : decodePlace ts rdst = some dst)
    (h_dec : decodeRvalue ts rrv = some rv) :
    evalRefMiriRvalue ts (zipRefLocals bodyLocals slots) (toMiriPlace rdst)
        (toMiriRvalue rrv) =
      mapSlotsRes bodyLocals
        (if !dst.projection.isEmpty then
          .error .unsupported
        else
          match MirSemantics.getElem? bodyLocals dst.localId with
          | none => .error .unsupported
          | some dstTy =>
            match evalRvalue bodyLocals slots dstTy rv with
            | .error k => .error k
            | .ok (val, localsAfterRval) =>
              writePlace localsAfterRval dst.localId dstTy val) := by
  cases rdst with
  | mk localId proj =>
    let ⟨h_id, h_emp⟩ := decodePlace_inv h_pl
    cases proj with
    | cons _ _ =>
      have h_e : dst.projection.isEmpty = false := h_emp.symm
      rw [h_e]
      rfl
    | nil =>
      have h_e : dst.projection.isEmpty = true := h_emp.symm
      have h_i : dst.localId = localId := h_id.symm
      rw [h_e, h_i]
      dsimp only [Bool.not, ite_false_eq_true]
      have h_tp : toMiriPlace ⟨localId, []⟩ = ⟨localId, Array.empty⟩ := rfl
      rw [h_tp]
      cases h_ty : MirSemantics.getElem? bodyLocals localId with
      | none =>
        have h_arr :
            (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false :=
          rfl
        dsimp only [evalRefMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
          refRvalueHooks, Miri.Interpreter.runRvalue, Bind.bind, Pure.pure,
          EStateM.bind, EStateM.pure]
        rw [h_arr, ite_false_eq_true, getElem?_zipRefLocals_none_left h_ty]
        rfl
      | some dstTy =>
        let ⟨dstSlot, h_sl⟩ := getElem?_some_of_length_eq h_len.symm h_ty
        have h_dst := getElem?_zipRefLocals_some h_ty h_sl
        cases rrv with
        | use rop =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_op : decodeOperand ts rop with
          | none => rw [h_op] at h_dec; cases h_dec
          | some op =>
            rw [h_op] at h_dec
            injection h_dec with h_eq
            subst h_eq
            rw [evalRefMiriRvalue_use ts _ localId dstSlot dstTy rop h_dst]
            dsimp only [evalRvalue]
            rw [evalRefMiriOperandToSlot_eq h_op]
            cases evalOperandToSlot bodyLocals slots op with
            | error _ => rfl
            | ok res =>
              let ⟨srcTy, optVal, slots₁⟩ := res
              dsimp only [mapSlotRes]
              cases MirTy.beq srcTy dstTy
              · rfl
              · cases optVal with
                | none => rfl
                | some v => exact writeRefPlace_eq h_ty
        | binaryOp op lhs rhs =>
          dsimp only [decodeRvalue, optMap2] at h_dec
          cases h_l : decodeOperand ts lhs with
          | none => rw [h_l] at h_dec; cases h_dec
          | some l' =>
            cases h_r : decodeOperand ts rhs with
            | none => rw [h_l, h_r] at h_dec; cases h_dec
            | some r' =>
              rw [h_l, h_r] at h_dec
              injection h_dec with h_eq
              subst h_eq
              rw [evalRefMiriRvalue_binaryOp ts _ localId dstSlot dstTy op lhs
                rhs h_dst]
              dsimp only [evalRvalue]
              rw [evalRefMiriOperandToSlot_eq h_l]
              dsimp only [evalPrimitiveOperand]
              cases evalOperandToSlot bodyLocals slots l' with
              | error _ => rfl
              | ok resL =>
                let ⟨lTy, lOpt, slots₁⟩ := resL
                dsimp only [mapSlotRes]
                rw [readRefPrimitiveSlot_eq]
                cases isPrimitiveReadableTy lTy
                · rfl
                · dsimp only [Bool.not, ite_false_eq_true]
                  cases lOpt with
                  | none => rfl
                  | some lVal =>
                    dsimp only
                    rw [evalRefMiriOperandToSlot_eq h_r]
                    cases evalOperandToSlot bodyLocals slots₁ r' with
                    | error _ => rfl
                    | ok resR =>
                      let ⟨rTy, rOpt, slots₂⟩ := resR
                      dsimp only [mapSlotRes]
                      rw [readRefPrimitiveSlot_eq]
                      cases isPrimitiveReadableTy rTy
                      · rfl
                      · dsimp only [Bool.not, ite_false_eq_true]
                        cases rOpt with
                        | none => rfl
                        | some rVal =>
                          dsimp only
                          rw [evalRefBinOp_eq]
                          cases evalBinOp op lVal rVal with
                          | error _ => rfl
                          | ok v => exact writeRefPlace_eq h_ty
        | unaryOp op rop =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_op : decodeOperand ts rop with
          | none => rw [h_op] at h_dec; cases h_dec
          | some op' =>
            rw [h_op] at h_dec
            injection h_dec with h_eq
            subst h_eq
            rw [evalRefMiriRvalue_unaryOp ts _ localId dstSlot dstTy op rop
              h_dst]
            dsimp only [evalRvalue, evalPrimitiveOperand]
            rw [evalRefMiriOperandToSlot_eq h_op]
            cases evalOperandToSlot bodyLocals slots op' with
            | error _ => rfl
            | ok res =>
              let ⟨ty, optVal, slots₁⟩ := res
              dsimp only [mapSlotRes]
              rw [readRefPrimitiveSlot_eq]
              cases isPrimitiveReadableTy ty
              · rfl
              · dsimp only [Bool.not, ite_false_eq_true]
                cases optVal with
                | none => rfl
                | some v =>
                  dsimp only
                  rw [evalRefUnOp_eq]
                  cases evalUnOp op v with
                  | error _ => rfl
                  | ok u => exact writeRefPlace_eq h_ty
        | discriminant rp =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h_dec; cases h_dec
          | some p =>
            rw [h_p] at h_dec
            injection h_dec with h_eq
            subst h_eq
            let ⟨h_pid, h_pemp⟩ := decodePlace_inv h_p
            have h_zip_tys : ∀ (id : LocalId) (slot : LocalSlot) (ety : EnumTy),
                MirSemantics.getElem? (zipRefLocals bodyLocals slots) id =
                  some ⟨slot, some (.enum ety)⟩ →
                ∃ tid, MirSemantics.getElem? ts tid = some (.enum ety) := by
              intro id slot ety h_get
              cases h_bty : MirSemantics.getElem? bodyLocals id with
              | none =>
                rw [getElem?_zipRefLocals_none_left h_bty] at h_get
                cases h_get
              | some bty =>
                cases h_bsl : MirSemantics.getElem? slots id with
                | none =>
                  rw [getElem?_zipRefLocals_none_right h_bsl] at h_get
                  cases h_get
                | some bsl =>
                  rw [getElem?_zipRefLocals_some h_bty h_bsl] at h_get
                  injection h_get with h_pair
                  injection h_pair with _ h_opt
                  injection h_opt with h_ty_eq
                  subst h_ty_eq
                  exact h_tys id (.enum ety) h_bty
            rw [evalRefMiriRvalue_discriminant_eq _ localId dstSlot dstTy rp
              h_dst h_zip_tys]
            dsimp only [evalRvalue]
            rw [h_pemp, h_pid]
            cases p.projection.isEmpty
            · rfl
            · cases h_pty : MirSemantics.getElem? bodyLocals p.localId with
              | none =>
                rw [getElem?_zipRefLocals_none_left h_pty]
                rfl
              | some ty =>
                cases h_psl : MirSemantics.getElem? slots p.localId with
                | none =>
                  rw [getElem?_zipRefLocals_none_right h_psl]
                  cases ty <;> rfl
                | some slot =>
                  rw [getElem?_zipRefLocals_some h_pty h_psl]
                  cases ty with
                  | enum ety =>
                    dsimp only
                    cases enumAdmitted ety
                    · rfl
                    · cases ety.tagRepr with
                      | zeroSized =>
                        cases slot with
                        | dead => rfl
                        | live opt =>
                          cases opt with
                          | none =>
                            cases MirSemantics.getElem? ety.discriminants 0 with
                            | none => rfl
                            | some disc => exact writeRefPlace_eq h_ty
                          | some val =>
                            cases val with
                            | enumVal ety' v =>
                              dsimp only
                              cases (EnumTy.beq ety ety' && Nat.beq v 0)
                              · rfl
                              · cases MirSemantics.getElem? ety.discriminants 0
                                with
                                | none => rfl
                                | some disc => exact writeRefPlace_eq h_ty
                            | _ => rfl
                      | scalar tagW tagS =>
                        cases slot with
                        | dead => rfl
                        | live opt =>
                          cases opt with
                          | none => rfl
                          | some val =>
                            cases val with
                            | enumVal ety' v =>
                              dsimp only
                              cases (EnumTy.beq ety ety' &&
                                  Nat.blt v ety.discriminants.length)
                              · rfl
                              · cases MirSemantics.getElem? ety.discriminants v
                                with
                                | none => rfl
                                | some disc => exact writeRefPlace_eq h_ty
                            | _ => rfl
                  | _ => rfl
        | ref m rp =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h_dec; cases h_dec
          | some _ =>
            rw [h_p] at h_dec
            injection h_dec with h_eq
            subst h_eq
            exact evalRefMiriRvalue_ref ts _ localId dstSlot dstTy m rp h_dst
        | addressOf m rp =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h_dec; cases h_dec
          | some _ =>
            rw [h_p] at h_dec
            injection h_dec with h_eq
            subst h_eq
            exact evalRefMiriRvalue_addressOf ts _ localId dstSlot dstTy m rp
              h_dst
        | aggregateTuple rops =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_ops : mapOption (decodeOperand ts) rops with
          | none => rw [h_ops] at h_dec; cases h_dec
          | some _ =>
            rw [h_ops] at h_dec
            injection h_dec with h_eq
            subst h_eq
            exact evalRefMiriRvalue_aggregateTuple ts _ localId dstSlot dstTy
              rops h_dst
        | unsupported =>
          injection h_dec with h_eq
          subst h_eq
          exact evalRefMiriRvalue_unsupported ts _ localId dstSlot dstTy h_dst

end Anneal.MirCorrespondence
