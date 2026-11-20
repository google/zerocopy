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
import Anneal.MirCorrespondenceBase

namespace Anneal.MirCorrespondenceProof

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Anneal.MirCorrespondenceBase

/-!
# MIR Correspondence Proofs (`Anneal.MirCorrespondenceProof`)

This module proves Anneal's per-step MIR simulation, end-to-end correspondence
theorems, and Pass 2 non-vacuity canaries (`D6`–`D13`) on top of the codec,
canonicality, and `vendor/lean-miri` scalar/discriminant bridge lemmas in
`Anneal.MirCorrespondenceBase`.
-/

/-- `encodeStmt` maps `.nop` and only `.nop` to `.nop`. -/
theorem encodeStmt_no_dormant_noops : EncodeStmtNoDormantNoopsClaim :=
  encodeStmt_no_dormant_noops_base

/-- `encodeRvalue` maps `.binaryOp` and only `.binaryOp` to `.binaryOp`. -/
theorem encodeRvalue_binaryOp_iff : EncodeRvalueBinaryOpIffClaim :=
  encodeRvalue_binaryOp_iff_base

/-- `encodeRvalue` maps `.unaryOp` and only `.unaryOp` to `.unaryOp`. -/
theorem encodeRvalue_unaryOp_iff : EncodeRvalueUnaryOpIffClaim :=
  encodeRvalue_unaryOp_iff_base

/-- `encodeStmt` maps `.assign` and only `.assign` to `.assign`. -/
theorem encodeStmt_assign_iff : EncodeStmtAssignIffClaim :=
  encodeStmt_assign_iff_base

/-- Unconditional codec round-trip theorem (`decodeProg ∘ encodeProg`). -/
theorem decodeProg_encodeProg : DecodeProgEncodeProgClaim :=
  decodeProg_encodeProg_base

/-- Canonical type-table deduplication theorem for `encodeProg`. -/
theorem encodeProg_types_canonical : EncodeProgTypesCanonicalClaim :=
  encodeProg_types_canonical_base

/-- Left uniqueness of `SimulationInv` (`State` unique given `RefState`). -/
theorem state_unique_of_simulationInv : StateUniqueOfSimulationInvClaim :=
  state_unique_of_simulationInv_base

/-- Right uniqueness of `SimulationInv` (`RefState` unique given `State`). -/
theorem refState_unique_of_simulationInv : RefStateUniqueOfSimulationInvClaim :=
  refState_unique_of_simulationInv_base

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

private theorem readRefPrimitiveSlot_eq (ty : MirTy) (optVal : Option Val) :
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

theorem getElem?_none_of_setElem?_none {α : Type} {xs : List α} {i : Nat}
    {v : α}
    (h : MirSemantics.setElem? xs i v = none) :
    MirSemantics.getElem? xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero => cases h
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_r : MirSemantics.setElem? rest j v with
      | some _ => rw [h_r] at h; cases h
      | none => exact ih h_r

theorem getElem?_some_of_setElem?_some {α : Type} {xs xs' : List α} {i : Nat}
    {v : α}
    (h : MirSemantics.setElem? xs i v = some xs') :
    ∃ x : α, MirSemantics.getElem? xs i = some x := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons x rest ih =>
    cases i with
    | zero => exact ⟨x, rfl⟩
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_r : MirSemantics.setElem? rest j v with
      | none => rw [h_r] at h; cases h
      | some _ => exact ih h_r

private abbrev RefStepState :=
  Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
    RefStepMachine

private abbrev RefMiriFrame :=
  Miri.Interpreter.Frame (Option Val) Miri.Interpreter.LocalLayout Unit

private theorem evalRefStatement_of_ok (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory)
    (stmt : RefStatementKind) (m' : RefStepMachine)
    (h_ev : Miri.Interpreter.Step.evalStatement
        (refStepHooksFor ts callerMem) ()
        (toMiriStatementForDispatch stmt)
        (mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt)) =
      ({ mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt) with
          machine := m' }, .ok ())) :
    evalRefStatement ts rframe callerMem stmt =
      .step {
        frames := [{
          rframe with
          stmtIdx := rframe.stmtIdx + 1
          locals := m'.locals
        }]
        callerMem
      } := by
  let st₀ := mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt)
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock false with
      statements := Array.mk [toMiriStatementForDispatch stmt] }
  let fr : RefMiriFrame :=
    { mkSingleLocalMiriFrame .dead false with
      body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
      location := .mir ⟨0, 0⟩ }
  have h_cf : st₀.stack.currentFrame? = some fr := rfl
  have h_loc : fr.location = .mir ⟨0, 0⟩ := rfl
  have h_bb : fr.body.basicBlocks[0]? = some blk := rfl
  have h_st : blk.statements[0]? = some (toMiriStatementForDispatch stmt) := rfl
  have h_step :
      Miri.Interpreter.Step.step (refStepHooksFor ts callerMem) () st₀ =
        ({ st₀ with
          stack := ⟨Array.mk [{ fr with location := .mir ⟨0, 1⟩ }]⟩
          machine := m' }, .ok true) := by
    unfold Miri.Interpreter.Step.step
    rw [h_cf]; dsimp only
    rw [h_loc]; dsimp only
    rw [h_bb]; dsimp only
    rw [h_st]; dsimp only
    rw [h_ev]; rfl
  unfold evalRefStatement
  rw [h_step]
  rfl

private theorem evalRefStatement_of_err (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory)
    (stmt : RefStatementKind) (st₁ : RefStepState)
    (err : Miri.Interpreter.StepError)
    (h_ev : Miri.Interpreter.Step.evalStatement
        (refStepHooksFor ts callerMem) ()
        (toMiriStatementForDispatch stmt)
        (mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt)) =
      (st₁, .error err)) :
    evalRefStatement ts rframe callerMem stmt =
      match err with
      | .undefinedBehavior _ => .fault .undefined
      | _ => .fault .unsupported := by
  let st₀ := mkRefStmtStepState rframe.locals (toMiriStatementForDispatch stmt)
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock false with
      statements := Array.mk [toMiriStatementForDispatch stmt] }
  let fr : RefMiriFrame :=
    { mkSingleLocalMiriFrame .dead false with
      body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
      location := .mir ⟨0, 0⟩ }
  have h_cf : st₀.stack.currentFrame? = some fr := rfl
  have h_loc : fr.location = .mir ⟨0, 0⟩ := rfl
  have h_bb : fr.body.basicBlocks[0]? = some blk := rfl
  have h_st : blk.statements[0]? = some (toMiriStatementForDispatch stmt) := rfl
  have h_step :
      Miri.Interpreter.Step.step (refStepHooksFor ts callerMem) () st₀ =
        (st₁, .error err) := by
    unfold Miri.Interpreter.Step.step
    rw [h_cf]; dsimp only
    rw [h_loc]; dsimp only
    rw [h_bb]; dsimp only
    rw [h_st]; dsimp only
    rw [h_ev]; rfl
  unfold evalRefStatement
  rw [h_step]
  cases err <;> rfl

private theorem evalRefStatement_storageLive (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (localId : LocalId) :
    evalRefStatement ts rframe callerMem (.storageLive localId) =
      match MirSemantics.getElem? rframe.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? rframe.locals localId
            ⟨liveUninitSlot localTy, some localTy⟩ with
        | some rlocals' =>
          .step {
            frames := [{
              rframe with
              stmtIdx := rframe.stmtIdx + 1
              locals := rlocals'
            }]
            callerMem
          }
        | none => .fault .unsupported
      | _ => .fault .unsupported := by
  have h_sl :
      Miri.Interpreter.Step.evalStatement (refStepHooksFor ts callerMem) ()
          (toMiriStatementForDispatch (.storageLive localId))
          (mkRefStmtStepState rframe.locals
            (toMiriStatementForDispatch (.storageLive localId))) =
        let st₀ := mkRefStmtStepState rframe.locals
          (toMiriStatementForDispatch (.storageLive localId))
        match MirSemantics.getElem? rframe.locals localId with
        | some ⟨_, some localTy⟩ =>
          match MirSemantics.setElem? rframe.locals localId
              ⟨refLiveUninitSlot localTy, some localTy⟩ with
          | some rlocals' =>
            ({ st₀ with machine := { locals := rlocals', terminal := none } },
              .ok ())
          | none =>
            (st₀, .error (.unsupported "storageLive local out of bounds"))
        | _ =>
          (st₀,
            .error (.unsupported "storageLive missing cached layout")) := rfl
  cases h_get : MirSemantics.getElem? rframe.locals localId with
  | none =>
    rw [h_get] at h_sl
    exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sl
  | some rloc =>
    cases rloc with
    | mk slot optTy =>
      cases optTy with
      | none =>
        rw [h_get] at h_sl
        exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sl
      | some localTy =>
        dsimp only
        rw [h_get] at h_sl
        dsimp only at h_sl
        rw [refLiveUninitSlot_eq] at h_sl
        cases h_set : MirSemantics.setElem? rframe.locals localId
            ⟨liveUninitSlot localTy, some localTy⟩ with
        | none =>
          rw [h_set] at h_sl
          exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sl
        | some rlocals' =>
          rw [h_set] at h_sl
          exact evalRefStatement_of_ok ts rframe callerMem _ _ h_sl

private theorem evalRefStatement_storageDead_zero (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (localId : LocalId)
    (h0 : Nat.beq localId 0 = true) :
    evalRefStatement ts rframe callerMem (.storageDead localId) =
      .fault .unsupported := by
  cases localId with
  | zero => rfl
  | succ _ => cases h0

private theorem evalRefStatement_storageDead_nonzero (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (localId : LocalId)
    (h0 : Nat.beq localId 0 = false) :
    evalRefStatement ts rframe callerMem (.storageDead localId) =
      match MirSemantics.getElem? rframe.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? rframe.locals localId
            ⟨.dead, some localTy⟩ with
        | some rlocals' =>
          .step {
            frames := [{
              rframe with
              stmtIdx := rframe.stmtIdx + 1
              locals := rlocals'
            }]
            callerMem
          }
        | none => .fault .unsupported
      | _ => .fault .unsupported := by
  cases localId with
  | zero => cases h0
  | succ n =>
    have h_sd :
        Miri.Interpreter.Step.evalStatement (refStepHooksFor ts callerMem) ()
            (toMiriStatementForDispatch (.storageDead (n + 1)))
            (mkRefStmtStepState rframe.locals
              (toMiriStatementForDispatch (.storageDead (n + 1)))) =
          let st₀ := mkRefStmtStepState rframe.locals
            (toMiriStatementForDispatch (.storageDead (n + 1)))
          match MirSemantics.getElem? rframe.locals (n + 1) with
          | some ⟨_, some localTy⟩ =>
            match MirSemantics.setElem? rframe.locals (n + 1)
                ⟨.dead, some localTy⟩ with
            | some rlocals' =>
              ({ st₀ with machine := { locals := rlocals', terminal := none } },
                .ok ())
            | none =>
              (st₀, .error (.unsupported "storageDead local out of bounds"))
          | _ =>
            (st₀, .error (.unsupported "storageDead missing cached layout")) :=
      rfl
    cases h_get : MirSemantics.getElem? rframe.locals (n + 1) with
    | none =>
      rw [h_get] at h_sd
      exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sd
    | some rloc =>
      cases rloc with
      | mk slot optTy =>
        cases optTy with
        | none =>
          rw [h_get] at h_sd
          exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sd
        | some localTy =>
          dsimp only
          rw [h_get] at h_sd
          dsimp only at h_sd
          cases h_set : MirSemantics.setElem? rframe.locals (n + 1)
              ⟨.dead, some localTy⟩ with
          | none =>
            rw [h_set] at h_sd
            exact evalRefStatement_of_err ts rframe callerMem _ _ _ h_sd
          | some rlocals' =>
            rw [h_set] at h_sd
            exact evalRefStatement_of_ok ts rframe callerMem _ _ h_sd

private theorem evalRefStatement_assign (ts : List MirTy)
    (rframe : RefFrameState) (callerMem : CallerMemory) (dst : RefPlace)
    (rvalue : RefRvalue) :
    evalRefStatement ts rframe callerMem (.assign dst rvalue) =
      match evalRefMiriRvalue ts rframe.locals (toMiriPlace dst)
          (toMiriRvalue rvalue) with
      | .error k => .fault k
      | .ok rlocalsAfterWrite =>
        .step {
          frames := [{
            rframe with
            stmtIdx := rframe.stmtIdx + 1
            locals := rlocalsAfterWrite
          }]
          callerMem
        } := by
  have h_as :
      Miri.Interpreter.Step.evalStatement (refStepHooksFor ts callerMem) ()
          (toMiriStatementForDispatch (.assign dst rvalue))
          (mkRefStmtStepState rframe.locals
            (toMiriStatementForDispatch (.assign dst rvalue))) =
        let st₀ := mkRefStmtStepState rframe.locals
          (toMiriStatementForDispatch (.assign dst rvalue))
        match evalRefMiriRvalue ts rframe.locals (toMiriPlace dst)
            (toMiriRvalue rvalue) with
        | .error k => (st₀, .error (faultToStepError k))
        | .ok rlocalsAfterWrite =>
          ({ st₀ with machine :=
              { locals := rlocalsAfterWrite, terminal := none } },
            .ok ()) := rfl
  cases h_rv : evalRefMiriRvalue ts rframe.locals (toMiriPlace dst)
      (toMiriRvalue rvalue) with
  | error k =>
    rw [h_rv] at h_as
    dsimp only at h_as
    rw [evalRefStatement_of_err ts rframe callerMem _ _ _ h_as]
    cases k <;> rfl
  | ok rlocalsAfterWrite =>
    rw [h_rv] at h_as
    dsimp only at h_as
    exact evalRefStatement_of_ok ts rframe callerMem _ _ h_as

theorem evalRefStatement_eq {ts : List MirTy} {body : Body} {f : FrameState}
    {callerMem : CallerMemory} {rstmt : RefStatementKind} {stmt : StatementKind}
    (h_len : f.locals.length = body.locals.length)
    (h_tys : ∀ (id : LocalId) (ty : MirTy),
      MirSemantics.getElem? body.locals id = some ty →
      ∃ tid, MirSemantics.getElem? ts tid = some ty)
    (h_dec : decodeStmt ts rstmt = some stmt) :
    evalRefStatement ts (liftFrame body.locals f) callerMem rstmt =
      mapStepRes body.locals (evalStatement body f callerMem stmt) := by
  cases rstmt with
  | nop =>
    injection h_dec with h_eq
    subst h_eq
    rfl
  | storageLive localId =>
    injection h_dec with h_eq
    subst h_eq
    rw [evalRefStatement_storageLive]
    dsimp only [evalStatement, liftFrame]
    cases h_ty : MirSemantics.getElem? body.locals localId with
    | none =>
      rw [getElem?_zipRefLocals_none_left h_ty]
      rfl
    | some localTy =>
      let ⟨slot, h_sl⟩ := getElem?_some_of_length_eq h_len.symm h_ty
      rw [getElem?_zipRefLocals_some h_ty h_sl]
      dsimp only
      cases h_set :
          MirSemantics.setElem? f.locals localId (liveUninitSlot localTy) with
      | none =>
        rw [setElem?_zipRefLocals_none h_set]
        rfl
      | some locals' =>
        rw [setElem?_zipRefLocals_some h_ty h_set]
        rfl
  | storageDead localId =>
    injection h_dec with h_eq
    subst h_eq
    dsimp only [evalStatement]
    cases h0 : Nat.beq localId 0
    · rw [evalRefStatement_storageDead_nonzero _ _ _ _ h0]
      dsimp only [liftFrame]
      cases h_set : MirSemantics.setElem? f.locals localId .dead with
      | none =>
        have h_sl_none := getElem?_none_of_setElem?_none h_set
        rw [getElem?_zipRefLocals_none_right h_sl_none]
        rfl
      | some locals' =>
        let ⟨slot, h_sl⟩ := getElem?_some_of_setElem?_some h_set
        let ⟨localTy, h_ty⟩ := getElem?_some_of_length_eq h_len h_sl
        rw [getElem?_zipRefLocals_some h_ty h_sl]
        dsimp only
        rw [setElem?_zipRefLocals_some h_ty h_set]
        rfl
    · rw [evalRefStatement_storageDead_zero _ _ _ _ h0]
      rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt, optMap2] at h_dec
    cases h_pl : decodePlace ts rdst with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some dst =>
      cases h_rv : decodeRvalue ts rrv with
      | none => rw [h_pl, h_rv] at h_dec; cases h_dec
      | some rv =>
        rw [h_pl, h_rv] at h_dec
        injection h_dec with h_eq
        subst h_eq
        rw [evalRefStatement_assign]
        dsimp only [evalStatement, liftFrame]
        rw [evalRefMiriRvalue_eq h_len h_tys h_pl h_rv]
        cases dst.projection.isEmpty
        · rfl
        · dsimp only [Bool.not, ite_false_eq_true]
          cases MirSemantics.getElem? body.locals dst.localId with
          | none => rfl
          | some dstTy =>
            dsimp only
            cases evalRvalue body.locals f.locals dstTy rv with
            | error _ => rfl
            | ok res =>
              cases res with
              | mk val localsAfterRval =>
                dsimp only
                cases writePlace localsAfterRval dst.localId dstTy val <;> rfl
  | unsupported =>
    injection h_dec with h_eq
    subst h_eq
    rfl

private theorem step_term_eq (ts : List MirTy) (callerMem : CallerMemory)
    (rlocals : List RefLocalState) (term : Miri.MIR.Terminator)
    (cleanup : Bool) :
    Miri.Interpreter.Step.step (refStepHooksFor ts callerMem) ()
        (mkRefTermStepState rlocals term cleanup) =
      let r := Miri.Interpreter.ControlFlow.evalTerminator
        (refTerminatorHooksFor ts callerMem) () term
        (mkRefTermStepState rlocals term cleanup)
      (r.1, r.2.map fun _ => true) := rfl

private theorem evalRefTerminator_eq_of_term (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory) :
    evalRefTerminator ts rbb rframe callerMem =
      match Miri.Interpreter.ControlFlow.evalTerminator
          (refTerminatorHooksFor ts callerMem) ()
          (toMiriTerminatorForDispatch rbb.terminator)
          (mkRefTermStepState rframe.locals
            (toMiriTerminatorForDispatch rbb.terminator) rbb.cleanup) with
      | (st', .ok ()) =>
        match st'.machine.terminal with
        | some res => res
        | none =>
          match extractMirLocation? st' with
          | some loc =>
            .step {
              frames := [{
                rframe with
                blockIdx := loc.block
                stmtIdx := loc.statementIndex
                locals := st'.machine.locals
              }]
              callerMem
            }
          | none => .fault .unsupported
      | (_, .error (.undefinedBehavior _)) => .fault .undefined
      | (_, _) => .fault .unsupported := by
  unfold evalRefTerminator
  rw [step_term_eq]
  cases Miri.Interpreter.ControlFlow.evalTerminator
      (refTerminatorHooksFor ts callerMem) ()
      (toMiriTerminatorForDispatch rbb.terminator)
      (mkRefTermStepState rframe.locals
        (toMiriTerminatorForDispatch rbb.terminator) rbb.cleanup) with
  | mk st' res =>
    cases res with
    | ok u => cases u; rfl
    | error e => cases e <;> rfl

private noncomputable def expectedReturnEval (rframe : RefFrameState)
    (callerMem : CallerMemory) :
    Option RefLocalState →
      Miri.Interpreter.StepResult RefStepState Unit
  | some ⟨.live (some retVal), some _⟩ =>
    ({ stack := Miri.Interpreter.Stack.empty
       machine :=
         { locals := rframe.locals
           terminal := some (.done (.returned ⟨retVal, callerMem⟩)) } },
     .ok ())
  | some ⟨.live none, some _⟩ | some ⟨.dead, some _⟩ =>
    ({ stack := Miri.Interpreter.Stack.empty
       machine := { locals := rframe.locals, terminal := none } },
     .error (.undefinedBehavior "uninit or dead return place"))
  | _ =>
    ({ stack := Miri.Interpreter.Stack.empty
       machine := { locals := rframe.locals, terminal := none } },
     .error (.unsupported "missing return place"))

private theorem evalTerminator_return_ref
    (hooks : Miri.Interpreter.TerminatorHooks (Option Val)
      Miri.Interpreter.LocalLayout Unit RefStepMachine Unit Unit Val)
    (st₀ stPop st₁ : RefStepState) (fr frPop : RefMiriFrame)
    (blk : Miri.MIR.BasicBlock)
    (out : Except Miri.Interpreter.StepError Unit)
    (h_cf : st₀.stack.currentFrame? = some fr)
    (h_loc : fr.location = .mir ⟨0, 0⟩)
    (h_bb : fr.body.basicBlocks[0]? = some blk)
    (h_cl_blk : blk.cleanup = false)
    (h_ro : hooks.toControlHooks.returnOperand () st₀ = (st₀, .ok ()))
    (h_pf : hooks.toControlHooks.popFrame () st₀ = (stPop, .ok frPop))
    (h_cp : hooks.toControlHooks.copyReturn () () frPop.returnPlace stPop =
      (st₁, out))
    (h_cl : hooks.toControlHooks.cleanupFrame () false frPop st₁ =
      (st₁, .ok .normal))
    (h_cont : frPop.returnContinuation = .stop false)
    (h_st : st₁.stack = Miri.Interpreter.Stack.empty) :
    Miri.Interpreter.ControlFlow.evalTerminator hooks ()
      (toMiriTerminatorForDispatch .return_) st₀ = (st₁, out) := by
  cases hooks with
  | mk ch _ _ _ _ _ _ _ _ =>
    cases ch with
    | mk _ ro pf cr cf _ =>
      dsimp only at h_ro h_pf h_cp h_cl
      unfold Miri.Interpreter.ControlFlow.evalTerminator
        Miri.Interpreter.ControlFlow.returnFromCurrentFrame
      dsimp only [toMiriTerminatorForDispatch, Id.run, Bind.bind, Pure.pure]
      rw [h_cf]; dsimp only
      rw [h_loc]; dsimp only
      rw [h_bb]; dsimp only
      rw [h_cl_blk]
      have h_bne : (false != false) = false := rfl
      rw [h_bne]
      simp only [Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
        Bool.not_false]
      rw [h_ro]; dsimp only
      rw [h_pf]; dsimp only
      rw [h_cp]; dsimp only
      cases out with
      | error _ => rfl
      | ok u =>
        cases u
        rw [h_cl]; dsimp only
        rw [h_cont]; dsimp only
        rw [h_st]
        rfl

private theorem evalRefTerminator_return_false (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = false) :
    evalRefTerminator ts rbb rframe callerMem =
      match MirSemantics.getElem? rframe.locals 0 with
      | some ⟨.live (some retVal), some _⟩ =>
        .done (.returned ⟨retVal, callerMem⟩)
      | some ⟨.live none, some _⟩ | some ⟨.dead, some _⟩ =>
        .fault .undefined
      | _ => .fault .unsupported := by
  have h_case : ∀ (opt : Option RefLocalState),
      MirSemantics.getElem? rframe.locals 0 = opt →
      evalRefTerminator ts rbb rframe callerMem =
        match opt with
        | some ⟨.live (some retVal), some _⟩ =>
          .done (.returned ⟨retVal, callerMem⟩)
        | some ⟨.live none, some _⟩ | some ⟨.dead, some _⟩ =>
          .fault .undefined
        | _ => .fault .unsupported := by
    intro opt h_get
    rw [evalRefTerminator_eq_of_term, h_rt, h_cl]
    let st₀ := mkRefTermStepState rframe.locals
      (toMiriTerminatorForDispatch .return_) false
    let stPop : RefStepState :=
      { stack := Miri.Interpreter.Stack.empty
        machine := { locals := rframe.locals, terminal := none } }
    let blk : Miri.MIR.BasicBlock :=
      { refDummyMirBlock false with
        terminator := toMiriTerminatorForDispatch .return_ }
    let fr : RefMiriFrame :=
      { mkSingleLocalMiriFrame .dead false with
        body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
        location := .mir ⟨0, 0⟩ }
    have h_cf : st₀.stack.currentFrame? = some fr := rfl
    have h_loc : fr.location = .mir ⟨0, 0⟩ := rfl
    have h_bb : fr.body.basicBlocks[0]? = some blk := rfl
    have h_cp_eq :
        (refTerminatorHooksFor ts callerMem).toControlHooks.copyReturn () ()
          (mkSingleLocalMiriFrame .dead false).returnPlace stPop =
          expectedReturnEval rframe callerMem opt := by
      dsimp only [refTerminatorHooksFor,
        Miri.Interpreter.TerminatorHooks.toControlHooks, stPop]
      rw [h_get]
      cases opt with
      | none => rfl
      | some rloc =>
        cases rloc with
        | mk slot optTy =>
          cases slot with
          | dead => cases optTy <;> rfl
          | live optVal =>
            cases optVal with
            | none => cases optTy <;> rfl
            | some _ => cases optTy <;> rfl
    have h_st_empty :
        (expectedReturnEval rframe callerMem opt).1.stack =
          Miri.Interpreter.Stack.empty := by
      cases opt with
      | none => rfl
      | some rloc =>
        cases rloc with
        | mk slot optTy =>
          cases slot with
          | dead => cases optTy <;> rfl
          | live optVal =>
            cases optVal with
            | none => cases optTy <;> rfl
            | some _ => cases optTy <;> rfl
    have h_eval := evalTerminator_return_ref
      (refTerminatorHooksFor ts callerMem) st₀ stPop
      (expectedReturnEval rframe callerMem opt).1 fr
      (mkSingleLocalMiriFrame .dead false) blk
      (expectedReturnEval rframe callerMem opt).2
      h_cf h_loc h_bb rfl rfl rfl h_cp_eq rfl rfl h_st_empty
    change (match Miri.Interpreter.ControlFlow.evalTerminator
        (refTerminatorHooksFor ts callerMem) ()
        (toMiriTerminatorForDispatch .return_) st₀ with
      | (st', .ok ()) =>
        match st'.machine.terminal with
        | some res => res
        | none =>
          match extractMirLocation? st' with
          | some loc =>
            .step {
              frames := [{
                rframe with
                blockIdx := loc.block
                stmtIdx := loc.statementIndex
                locals := st'.machine.locals
              }]
              callerMem
            }
          | none => .fault .unsupported
      | (_, .error (.undefinedBehavior _)) => .fault .undefined
      | (_, _) => .fault .unsupported) = _
    rw [h_eval]
    cases opt with
    | none => rfl
    | some rloc =>
      cases rloc with
      | mk slot optTy =>
        cases slot with
        | dead => cases optTy <;> rfl
        | live optVal =>
          cases optVal with
          | none => cases optTy <;> rfl
          | some _ => cases optTy <;> rfl
  exact h_case _ rfl

private theorem evalRefTerminator_return_true (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = true) :
    evalRefTerminator ts rbb rframe callerMem = .fault .unsupported := by
  unfold evalRefTerminator
  rw [h_rt, h_cl]
  rfl

private theorem forIn_list_map_congr {α β σ : Type} (l : List α) (init : σ)
    (m : α → β) (f g : β → σ → Id (ForInStep σ))
    (h : ∀ x s, f (m x) s = g (m x) s) :
    forIn (m := Id) (l.map m) init f = forIn (m := Id) (l.map m) init g := by
  induction l generalizing init with
  | nil => rfl
  | cons a tl ih =>
    rw [List.map_cons, List.forIn_cons, List.forIn_cons, h]
    cases g (m a) init with
    | done s => rfl
    | yield s => exact ih s

private theorem evalConstLit_bool_scalar_is_bool (bits : BitVec 128) (v : Val)
    (h : evalConstLit .bool (.scalar bits) = .ok v) :
    ∃ cb : Bool, v = .bool cb := by
  dsimp only [evalConstLit] at h
  cases h1 : (truncateBits .i8 bits != bits) with
  | true => simp [h1] at h
  | false =>
    simp only [h1, Bool.false_eq_true, ite_false] at h
    cases h2 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 0) with
    | true =>
      simp only [h2, ite_true] at h
      injection h with hv
      exact ⟨false, hv.symm⟩
    | false =>
      simp only [h2, Bool.false_eq_true, ite_false] at h
      cases h3 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 1) with
      | true =>
        simp only [h3, ite_true] at h
        injection h with hv
        exact ⟨true, hv.symm⟩
      | false => simp [h3] at h

private theorem evalSwitchBranches_error_eq_unsupported (w : IntWidth)
    (bits : BitVec 128) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) (k : FaultKind)
    (h : evalSwitchBranches w bits otherwise branches = .error k) :
    k = .unsupported := by
  induction branches with
  | nil => dsimp only [evalSwitchBranches] at h; cases h
  | cons hd rest ih =>
    cases hd with
    | mk cb tgt =>
      dsimp only [evalSwitchBranches] at h
      cases h1 : (truncateBits w cb != cb) with
      | true => simp [h1] at h; exact h.symm
      | false =>
        simp only [h1, Bool.false_eq_true, ite_false] at h
        cases h2 : (truncateBits w bits == truncateBits w cb) with
        | true => simp [h2] at h
        | false =>
          simp only [h2, Bool.false_eq_true, ite_false] at h
          exact ih h

private theorem switchInt_forIn_cons {st : RefStepState}
    (cmp : Nat → RefStepState → Miri.Interpreter.StepResult RefStepState Bool)
    (caseBits : BitVec 128) (target otherwise : BasicBlockId)
    (rest : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (((caseBits, target) :: rest).map
        (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
        st, otherwise)
      (fun case __s =>
        have __s := __s.snd
        have state := __s.fst
        have target := __s.snd
        match case with
        | Miri.MIR.SwitchTarget.Case bits block =>
          match cmp bits state with
          | (next, comparison) =>
            have state := next
            match comparison with
            | Except.error error =>
              pure (ForInStep.done
                (some (state, Except.error error), state, target))
            | Except.ok true =>
              have target := block
              pure (ForInStep.done (none, state, target))
            | Except.ok false =>
              pure (ForInStep.yield (none, state, target))) =
    match cmp caseBits.toNat st with
    | (next, Except.error error) =>
      (some (next, Except.error error), next, otherwise)
    | (next, Except.ok true) => (none, next, target)
    | (next, Except.ok false) =>
      forIn (m := Id)
        (rest.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
        ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
          next, otherwise)
        (fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match cmp bits state with
            | (next, comparison) =>
              have state := next
              match comparison with
              | Except.error error =>
                pure (ForInStep.done
                  (some (state, Except.error error), state, target))
              | Except.ok true =>
                have target := block
                pure (ForInStep.done (none, state, target))
              | Except.ok false =>
                pure (ForInStep.yield (none, state, target))) := by
  rw [List.map_cons, List.forIn_cons]
  dsimp only [Bind.bind, Pure.pure, Id.run]
  cases cmp caseBits.toNat st with
  | mk next comparison =>
    cases comparison with
    | error _ => rfl
    | ok flag => cases flag <;> rfl

private theorem switchInt_forIn_scalar {ts : List MirTy}
    {callerMem : CallerMemory}
    (rlocals : List RefLocalState) (mframe : RefMiriFrame)
    (sv : ScalarVal) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
        ({ stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } } : RefStepState),
        otherwise)
      (fun case __s =>
        have __s := __s.snd
        have state := __s.fst
        have target := __s.snd
        match case with
        | Miri.MIR.SwitchTarget.Case bits block =>
          match (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
              (.scalar sv) bits state with
          | (next, comparison) =>
            have state := next
            match comparison with
            | Except.error error =>
              pure (ForInStep.done
                (some (state, Except.error error), state, target))
            | Except.ok true =>
              have target := block
              pure (ForInStep.done (none, state, target))
            | Except.ok false =>
              pure (ForInStep.yield (none, state, target))) =
      match evalSwitchBranches sv.width sv.bits otherwise branches with
      | .error _ =>
        (some ({ stack := ⟨Array.mk [mframe]⟩
                 machine := { locals := rlocals, terminal := none } },
               .error (faultToStepError .unsupported)),
         { stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } },
         otherwise)
      | .ok target =>
        (none,
         { stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } },
         target) := by
  induction branches with
  | nil =>
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest ih =>
    cases hd with
    | mk caseBits target =>
      rw [switchInt_forIn_cons
        (cmp := (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
          (.scalar sv))]
      rw [evalRefSwitchScalarCase_eq]
      dsimp only [evalSwitchBranches]
      cases (truncateBits sv.width caseBits != caseBits) with
      | true => rfl
      | false =>
        cases (truncateBits sv.width sv.bits ==
            truncateBits sv.width caseBits) with
        | false => exact ih
        | true => rfl

private theorem switchInt_forIn_bool {ts : List MirTy}
    {callerMem : CallerMemory}
    (rlocals : List RefLocalState) (mframe : RefMiriFrame)
    (b : Bool) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
        ({ stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } } : RefStepState),
        otherwise)
      (fun case __s =>
        have __s := __s.snd
        have state := __s.fst
        have target := __s.snd
        match case with
        | Miri.MIR.SwitchTarget.Case bits block =>
          match (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
              (.bool b) bits state with
          | (next, comparison) =>
            have state := next
            match comparison with
            | Except.error error =>
              pure (ForInStep.done
                (some (state, Except.error error), state, target))
            | Except.ok true =>
              have target := block
              pure (ForInStep.done (none, state, target))
            | Except.ok false =>
              pure (ForInStep.yield (none, state, target))) =
      match evalBoolSwitchBranches b otherwise branches with
      | .error k =>
        (some ({ stack := ⟨Array.mk [mframe]⟩
                 machine := { locals := rlocals, terminal := none } },
               .error (faultToStepError k)),
         { stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } },
         otherwise)
      | .ok target =>
        (none,
         { stack := ⟨Array.mk [mframe]⟩
           machine := { locals := rlocals, terminal := none } },
         target) := by
  induction branches with
  | nil =>
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest ih =>
    cases hd with
    | mk caseBits target =>
      rw [switchInt_forIn_cons
        (cmp := (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
          (.bool b))]
      rw [evalRefSwitchBoolCase_eq]
      dsimp only [evalBoolSwitchBranches]
      cases h_cl : evalConstLit .bool (.scalar caseBits) with
      | error k => rfl
      | ok v =>
        cases evalConstLit_bool_scalar_is_bool caseBits v h_cl with
        | intro cb h_cb =>
          subst h_cb
          cases cb <;> cases b
          · rfl
          · exact ih
          · exact ih
          · rfl

private theorem evalRefTerminator_switchInt (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (rdiscr : RefOperand) (targets : SwitchTargets)
    (h_rt : rbb.terminator = .switchInt rdiscr targets) :
    evalRefTerminator ts rbb rframe callerMem =
      match evalRefMiriOperandToSlot ts rframe.locals
          (toMiriOperand rdiscr) with
      | .error k => .fault k
      | .ok (ty, optVal, rlocalsAfterDiscr) =>
        match readRefPrimitiveSlot ty optVal with
        | .error k => .fault k
        | .ok discrVal =>
          let targetRes : Except FaultKind BasicBlockId :=
            match discrVal with
            | .scalar sv =>
              evalSwitchBranches sv.width sv.bits targets.otherwise
                targets.branches
            | .bool b =>
              evalBoolSwitchBranches b targets.otherwise targets.branches
            | _ => .error .unsupported
          match targetRes with
          | .error k => .fault k
          | .ok target =>
            .step {
              frames := [{
                rframe with
                blockIdx := target
                stmtIdx := 0
                locals := rlocalsAfterDiscr
              }]
              callerMem
            } := by
  rw [evalRefTerminator_eq_of_term, h_rt]
  let mirTerm : Miri.MIR.Terminator :=
    { sourceInfo := { span := { id := 0 }, scope := 0 }
      kind := .SwitchInt (toMiriOperand rdiscr)
        { cases := Array.mk
            (targets.branches.map (fun b => .Case b.1.toNat b.2))
          otherwise := targets.otherwise } }
  let mframe : RefMiriFrame := {
    mkSingleLocalMiriFrame .dead rbb.cleanup with
    body := {
      refDummyMirBody rbb.cleanup with
      basicBlocks := Array.mk [{ refDummyMirBlock rbb.cleanup with
        terminator := mirTerm }]
    }
    location := .mir ⟨0, 0⟩
  }
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
    toMiriTerminatorForDispatch, refTerminatorHooksFor,
    mkRefTermStepState, mkRefStepStateWith, Id.run, Bind.bind, Pure.pure]
  cases evalRefMiriOperandToSlot ts rframe.locals (toMiriOperand rdiscr) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨ty, optVal, rlocalsAfterDiscr⟩ := res
    dsimp only
    cases readRefPrimitiveSlot ty optVal with
    | error k => cases k <;> rfl
    | ok discrVal =>
      dsimp only
      cases discrVal with
      | scalar sv =>
        dsimp only
        rw [← Array.forIn_toList]
        dsimp only [Array.toList]
        rw [forIn_list_map_congr (g := fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
                (.scalar sv) bits state with
            | (next, comparison) =>
              have state := next
              match comparison with
              | Except.error error =>
                pure (ForInStep.done
                  (some (state, Except.error error), state, target))
              | Except.ok true =>
                have target := block
                pure (ForInStep.done (none, state, target))
              | Except.ok false =>
                pure (ForInStep.yield (none, state, target)))]
        · rw [@switchInt_forIn_scalar ts callerMem rlocalsAfterDiscr
            mframe sv targets.otherwise targets.branches]
          cases h_sw : evalSwitchBranches sv.width sv.bits targets.otherwise
              targets.branches with
          | error k =>
            have h_unsup :=
              evalSwitchBranches_error_eq_unsupported _ _ _ _ _ h_sw
            subst h_unsup
            rfl
          | ok target => rfl
        · intro x s
          cases (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
              (.scalar sv) x.1.toNat s.snd.fst with
          | mk next comparison =>
            cases comparison with
            | error _ => rfl
            | ok flag => cases flag <;> rfl
      | bool b =>
        dsimp only
        rw [← Array.forIn_toList]
        dsimp only [Array.toList]
        rw [forIn_list_map_congr (g := fun case __s =>
          have __s := __s.snd
          have state := __s.fst
          have target := __s.snd
          match case with
          | Miri.MIR.SwitchTarget.Case bits block =>
            match (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
                (.bool b) bits state with
            | (next, comparison) =>
              have state := next
              match comparison with
              | Except.error error =>
                pure (ForInStep.done
                  (some (state, Except.error error), state, target))
              | Except.ok true =>
                have target := block
                pure (ForInStep.done (none, state, target))
              | Except.ok false =>
                pure (ForInStep.yield (none, state, target)))]
        · rw [@switchInt_forIn_bool ts callerMem rlocalsAfterDiscr
            mframe b targets.otherwise targets.branches]
          cases evalBoolSwitchBranches b targets.otherwise targets.branches with
          | error k => cases k <;> rfl
          | ok target => rfl
        · intro x s
          cases (refTerminatorHooksFor ts callerMem).compareSwitchCase ()
              (.bool b) x.1.toNat s.snd.fst with
          | mk next comparison =>
            cases comparison with
            | error _ => rfl
            | ok flag => cases flag <;> rfl
      | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => rfl

theorem evalRefTerminator_eq {ts : List MirTy} {body : Body}
    {rbb : RefBasicBlock}
    {bb : BasicBlock} {f : FrameState} {callerMem : CallerMemory}
    (h_len : f.locals.length = body.locals.length)
    (h_cleanup : rbb.cleanup = bb.cleanup)
    (h_term : decodeTerminator ts rbb.terminator = some bb.terminator) :
    evalRefTerminator ts rbb (liftFrame body.locals f) callerMem =
      mapStepRes body.locals (evalTerminator body bb f callerMem) := by
  cases h_rt : rbb.terminator with
  | goto target =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl
  | switchInt rdiscr targets =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap] at h_term
    cases h_d : decodeOperand ts rdiscr with
    | none => rw [h_d] at h_term; cases h_term
    | some discr =>
      rw [h_d] at h_term
      injection h_term with h_eq
      rw [evalRefTerminator_switchInt _ _ _ _ _ _ h_rt]
      unfold evalTerminator
      rw [← h_eq]
      dsimp only [liftFrame, evalPrimitiveOperand]
      rw [evalRefMiriOperandToSlot_eq h_d]
      cases evalOperandToSlot body.locals f.locals discr with
      | error _ => rfl
      | ok res =>
        let ⟨ty, optVal, localsAfterDiscr⟩ := res
        dsimp only [mapSlotRes]
        rw [readRefPrimitiveSlot_eq]
        cases isPrimitiveReadableTy ty
        · rfl
        · dsimp only [Bool.not, ite_false_eq_true]
          cases optVal with
          | none => rfl
          | some discrVal =>
            dsimp only
            cases discrVal with
            | scalar sv =>
              dsimp only
              cases evalSwitchBranches sv.width sv.bits targets.otherwise
                targets.branches <;> rfl
            | bool b =>
              dsimp only
              cases evalBoolSwitchBranches b targets.otherwise
                targets.branches <;> rfl
            | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => rfl
  | return_ =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    cases h_cl : bb.cleanup
    · rw [evalRefTerminator_return_false _ _ _ _ h_rt (h_cleanup.trans h_cl)]
      unfold evalTerminator
      rw [← h_eq, h_cl]
      dsimp only [liftFrame]
      cases h_sl : MirSemantics.getElem? f.locals 0 with
      | none =>
        rw [getElem?_zipRefLocals_none_right h_sl]
        rfl
      | some s =>
        let ⟨ty₀, h_ty⟩ := getElem?_some_of_length_eq h_len h_sl
        rw [getElem?_zipRefLocals_some h_ty h_sl]
        cases s with
        | dead => rfl
        | live o => cases o <;> rfl
    · rw [evalRefTerminator_return_true _ _ _ _ h_rt (h_cleanup.trans h_cl)]
      unfold evalTerminator
      rw [← h_eq, h_cl]
      rfl
  | unreachable =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl
  | unwindResume =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl
  | assert rcond exp msg t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap] at h_term
    cases h_c : decodeOperand ts rcond with
    | none => rw [h_c] at h_term; cases h_term
    | some c =>
      rw [h_c] at h_term
      injection h_term with h_eq
      unfold evalRefTerminator evalTerminator
      rw [h_rt, ← h_eq]
      rfl
  | call callee rargs rdst t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap2] at h_term
    cases h_a : mapOption (decodeOperand ts) rargs with
    | none => rw [h_a] at h_term; cases h_term
    | some args =>
      cases h_dst : decodePlace ts rdst with
      | none => rw [h_a, h_dst] at h_term; cases h_term
      | some dst =>
        rw [h_a, h_dst] at h_term
        injection h_term with h_eq
        unfold evalRefTerminator evalTerminator
        rw [h_rt, ← h_eq]
        rfl
  | unsupported =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    unfold evalRefTerminator evalTerminator
    rw [h_rt, ← h_eq]
    rfl

theorem evalStatement_step_inv {body : Body} {f : FrameState}
    {callerMem : CallerMemory} {stmt : StatementKind} {s' : State}
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalStatement body f callerMem stmt = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := callerMem } ∧
      f'.defId = f.defId ∧
      f'.locals.length = body.locals.length := by
  cases stmt with
  | nop =>
    injection h_step with h_eq
    refine ⟨{ f with stmtIdx := f.stmtIdx + 1 }, h_eq.symm, rfl, h_len⟩
  | storageLive localId =>
    dsimp only [evalStatement] at h_step
    cases h_ty : MirSemantics.getElem? body.locals localId with
    | none => rw [h_ty] at h_step; cases h_step
    | some localTy =>
      rw [h_ty] at h_step
      dsimp only at h_step
      cases h_set :
          MirSemantics.setElem? f.locals localId (liveUninitSlot localTy) with
      | none => rw [h_set] at h_step; cases h_step
      | some locals' =>
        rw [h_set] at h_step
        injection h_step with h_eq
        refine ⟨{ f with stmtIdx := f.stmtIdx + 1, locals := locals' },
          h_eq.symm, rfl,
          (setElem?_length h_set).trans h_len⟩
  | storageDead localId =>
    dsimp only [evalStatement] at h_step
    cases h0 : Nat.beq localId 0 <;> rw [h0] at h_step
    · cases h_set : MirSemantics.setElem? f.locals localId .dead with
      | none => rw [h_set] at h_step; cases h_step
      | some locals' =>
        rw [h_set] at h_step
        injection h_step with h_eq
        refine ⟨{ f with stmtIdx := f.stmtIdx + 1, locals := locals' },
          h_eq.symm, rfl,
          (setElem?_length h_set).trans h_len⟩
    · cases h_step
  | assign dst rvalue =>
    dsimp only [evalStatement] at h_step
    cases h_emp : dst.projection.isEmpty <;> rw [h_emp] at h_step
    · cases h_step
    · cases h_ty : MirSemantics.getElem? body.locals dst.localId with
      | none => rw [h_ty] at h_step; cases h_step
      | some dstTy =>
        rw [h_ty] at h_step
        dsimp only at h_step
        cases h_rv : evalRvalue body.locals f.locals dstTy rvalue with
        | error _ => rw [h_rv] at h_step; cases h_step
        | ok res =>
          rw [h_rv] at h_step
          cases res with | mk val localsAfterRval =>
          dsimp only at h_step
          cases h_wr : writePlace localsAfterRval dst.localId dstTy val with
          | error _ => rw [h_wr] at h_step; cases h_step
          | ok localsAfterWrite =>
            rw [h_wr] at h_step
            injection h_step with h_eq
            have h_len₁ := (evalRvalue_length h_rv).trans h_len
            have h_len₂ := (writePlace_length h_wr).trans h_len₁
            refine ⟨{ f with
                stmtIdx := f.stmtIdx + 1, locals := localsAfterWrite },
              h_eq.symm, rfl, h_len₂⟩
  | unsupported => cases h_step

theorem evalTerminator_step_inv {body : Body} {bb : BasicBlock}
    {f : FrameState} {callerMem : CallerMemory} {s' : State}
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalTerminator body bb f callerMem = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := callerMem } ∧
      f'.defId = f.defId ∧
      f'.locals.length = body.locals.length := by
  cases bb with | mk stmts term cleanup =>
  cases term with
  | goto target =>
    injection h_step with h_eq
    refine ⟨{ f with blockIdx := target, stmtIdx := 0 }, h_eq.symm, rfl, h_len⟩
  | return_ =>
    dsimp only [evalTerminator] at h_step
    cases cleanup
    · cases h_sl : MirSemantics.getElem? f.locals 0 with
      | none => rw [h_sl] at h_step; cases h_step
      | some s =>
        rw [h_sl] at h_step
        cases s with
        | dead => cases h_step
        | live o => cases o <;> cases h_step
    · cases h_step
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _
  | unsupported =>
    cases h_step
  | switchInt discr targets =>
    dsimp only [evalTerminator] at h_step
    cases h_d : evalPrimitiveOperand body.locals f.locals discr with
    | error _ => rw [h_d] at h_step; cases h_step
    | ok res =>
      rw [h_d] at h_step
      cases res with | mk discrVal localsAfterDiscr =>
      have h_len₁ := (evalPrimitiveOperand_length h_d).trans h_len
      dsimp only at h_step
      cases discrVal with
      | scalar sv =>
        dsimp only at h_step
        cases h_sw : evalSwitchBranches sv.width sv.bits targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_len₁⟩
      | bool b =>
        dsimp only at h_step
        cases h_sw : evalBoolSwitchBranches b targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_len₁⟩
      | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => cases h_step

theorem decodeBasicBlock_inv {ts : List MirTy} {rbb : RefBasicBlock}
    {bb : BasicBlock}
    (h : decodeBasicBlock ts rbb = some bb) :
    mapOption (decodeStmt ts) rbb.statements = some bb.statements ∧
    decodeTerminator ts rbb.terminator = some bb.terminator ∧
    rbb.cleanup = bb.cleanup := by
  dsimp only [decodeBasicBlock, optMap2] at h
  cases h₁ : mapOption (decodeStmt ts) rbb.statements with
  | none => rw [h₁] at h; cases h
  | some stmts =>
    cases h₂ : decodeTerminator ts rbb.terminator with
    | none => rw [h₁, h₂] at h; cases h
    | some term =>
      rw [h₁, h₂] at h
      injection h with h_eq
      rw [← h_eq]
      exact ⟨rfl, rfl, rfl⟩

theorem decodeBody_inv {ts : List MirTy} {rbody : RefBody} {body : Body}
    (h : decodeBody ts rbody = some body) :
    rbody.argumentCount = body.argumentCount ∧
    decodeLocalTys ts rbody.locals = some body.locals ∧
    mapOption (decodeBasicBlock ts) rbody.basicBlocks = some body.basicBlocks ∧
    rbody.isUnsafe = body.isUnsafe ∧
    rbody.identity = body.identity := by
  dsimp only [decodeBody, optMap2] at h
  cases h₁ : decodeLocalTys ts rbody.locals with
  | none => rw [h₁] at h; cases h
  | some locals =>
    cases h₂ : mapOption (decodeBasicBlock ts) rbody.basicBlocks with
    | none => rw [h₁, h₂] at h; cases h
    | some bbs =>
      rw [h₁, h₂] at h
      injection h with h_eq
      rw [← h_eq]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem decodeProg_inv {rp : RefProg} {p : Program}
    (h : decodeProg rp = some p) :
    rp.entryDefId = p.entryDefId ∧
    rp.pointerWidthBits = p.pointerWidthBits ∧
    rp.mirProfileVersion = p.mirProfileVersion ∧
    rp.scope = p.scope ∧
    mapOption (decodeBody rp.types) rp.bodies = some p.bodies := by
  dsimp only [decodeProg, optMap] at h
  cases h_b : mapOption (decodeBody rp.types) rp.bodies with
  | none => rw [h_b] at h; cases h
  | some b' =>
    rw [h_b] at h
    injection h with h_eq
    rw [← h_eq]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem evalStep_step_inv {p : Program} {c : Choice} {s s' : State}
    {f : FrameState} {body : Body}
    (hs : s.frames = [f])
    (h_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalStep p c s = .step s') :
    ∃ f' : FrameState,
      s' = { frames := [f'], callerMem := s.callerMem } ∧
      f'.defId = f.defId ∧
      f'.locals.length = body.locals.length := by
  unfold evalStep at h_step
  rw [hs] at h_step
  dsimp only at h_step
  rw [h_body] at h_step
  dsimp only at h_step
  cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none => rw [h_bb] at h_step; cases h_step
  | some bb =>
    rw [h_bb] at h_step
    dsimp only at h_step
    cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx <;>
      rw [h_st] at h_step
    · dsimp only at h_step
      cases h_end : Nat.beq f.stmtIdx bb.statements.length <;>
        rw [h_end] at h_step
      · cases h_step
      · exact evalTerminator_step_inv h_len h_step
    · exact evalStatement_step_inv h_len h_step

/-- One $M_{\text{ref}}$ step from a simulated state computes exactly the
lifted $M_{\text{anneal}}$ step, with the caller sentinel restored beneath the
top frame. -/
theorem evalRefStep_eq : EvalRefStepEqClaim := by
  intro rp p s rs f rf retTy body h_dec hs hrs hcm h_body h_len hrf h_lt c
  let ⟨_, _, _, _, h_bodies⟩ := decodeProg_inv h_dec
  let ⟨rbody, h_rbody_get, h_rbody_dec⟩ :=
    (mapOption_getElem? h_bodies f.defId).2 body h_body
  let ⟨_, h_locs_dec, h_bbs_dec, _, _⟩ := decodeBody_inv h_rbody_dec
  have h_tys : ∀ (id : LocalId) (ty : MirTy),
      MirSemantics.getElem? body.locals id = some ty →
      ∃ tid, MirSemantics.getElem? rp.types tid = some ty := by
    intro id ty h_get
    let ⟨tid, _, h_tid⟩ := (mapOption_getElem? h_locs_dec id).2 ty h_get
    exact ⟨tid, h_tid⟩
  unfold evalRefStep evalStep
  rw [h_lt, hrs, hs, hrf, hcm]
  dsimp only [liftFrame, callerSentinelFrame]
  rw [h_rbody_get, h_body]
  dsimp only
  cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none =>
    rw [(mapOption_getElem? h_bbs_dec f.blockIdx).1 h_bb]
    rfl
  | some bb =>
    let ⟨rbb, h_rbb_get, h_rbb_dec⟩ :=
      (mapOption_getElem? h_bbs_dec f.blockIdx).2 bb h_bb
    let ⟨h_stmts_dec, h_term_dec, h_cleanup⟩ := decodeBasicBlock_inv h_rbb_dec
    rw [h_rbb_get]
    dsimp only
    cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx with
    | none =>
      rw [(mapOption_getElem? h_stmts_dec f.stmtIdx).1 h_st]
      rw [mapOption_length h_stmts_dec]
      dsimp only
      cases Nat.beq f.stmtIdx bb.statements.length
      · rfl
      · exact congrArg
          (stepResultToRefOutcome (callerSentinelFrame retTy)
            rs.stepsExecuted rs.maxSteps)
          (evalRefTerminator_eq h_len h_cleanup h_term_dec)
    | some stmt =>
      let ⟨rstmt, h_rstmt_get, h_rstmt_dec⟩ :=
        (mapOption_getElem? h_stmts_dec f.stmtIdx).2 stmt h_st
      rw [h_rstmt_get]
      dsimp only
      exact congrArg
        (stepResultToRefOutcome (callerSentinelFrame retTy)
          rs.stepsExecuted rs.maxSteps)
        (evalRefStatement_eq h_len h_tys h_rstmt_dec)

/-! ## Entry Initialization Simulation (`initRefState_sim`) -/

theorem refStmtHasStorageMarker_eq {ts : List MirTy} {localId : LocalId}
    {rstmt : RefStatementKind} {stmt : StatementKind}
    (h : decodeStmt ts rstmt = some stmt) :
    refStmtHasStorageMarker localId rstmt =
      stmtHasStorageMarker localId stmt := by
  cases rstmt with
  | storageLive id =>
    injection h with h_eq; subst h_eq; rfl
  | storageDead id =>
    injection h with h_eq; subst h_eq; rfl
  | nop =>
    injection h with h_eq; subst h_eq; rfl
  | unsupported =>
    injection h with h_eq; subst h_eq; rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt, optMap2] at h
    cases h₁ : decodePlace ts rdst with
    | none => rw [h₁] at h; cases h
    | some dst =>
      cases h₂ : decodeRvalue ts rrv with
      | none => rw [h₁, h₂] at h; cases h
      | some rv =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        rfl

theorem refHasStorageAnnotation_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body}
    (h : decodeBody ts rbody = some body) (localId : LocalId) :
    refHasStorageAnnotation rbody localId =
      hasStorageAnnotation body localId := by
  let ⟨_, _, h_bbs, _, _⟩ := decodeBody_inv h
  unfold refHasStorageAnnotation hasStorageAnnotation
  exact mapOption_any_eq
    (fun _ _ h_bb =>
      mapOption_any_eq (fun _ _ hs => refStmtHasStorageMarker_eq hs)
        (decodeBasicBlock_inv h_bb).1)
    h_bbs

noncomputable def refStmtInBounds (n : Nat) : RefStatementKind → Bool
  | .storageLive id | .storageDead id => Nat.blt id n
  | _ => true

noncomputable def stmtInBounds (n : Nat) : StatementKind → Bool
  | .storageLive id | .storageDead id => Nat.blt id n
  | _ => true

theorem refStmtInBounds_eq {ts : List MirTy} {n : Nat}
    {rstmt : RefStatementKind} {stmt : StatementKind}
    (h : decodeStmt ts rstmt = some stmt) :
    refStmtInBounds n rstmt = stmtInBounds n stmt := by
  cases rstmt with
  | storageLive id => injection h with h_eq; subst h_eq; rfl
  | storageDead id => injection h with h_eq; subst h_eq; rfl
  | nop => injection h with h_eq; subst h_eq; rfl
  | unsupported => injection h with h_eq; subst h_eq; rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt, optMap2] at h
    cases h₁ : decodePlace ts rdst with
    | none => rw [h₁] at h; cases h
    | some dst =>
      cases h₂ : decodeRvalue ts rrv with
      | none => rw [h₁, h₂] at h; cases h
      | some rv =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        rfl

theorem refStorageAnnotationsInBounds_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body}
    (h : decodeBody ts rbody = some body) :
    refStorageAnnotationsInBounds rbody = storageAnnotationsInBounds body := by
  let ⟨_, h_loc, h_bbs, _, _⟩ := decodeBody_inv h
  unfold refStorageAnnotationsInBounds storageAnnotationsInBounds
  rw [mapOption_length h_loc]
  exact mapOption_all_eq
    (fun _ _ h_bb =>
      mapOption_all_eq (fun _ _ hs => refStmtInBounds_eq hs)
        (decodeBasicBlock_inv h_bb).1)
    h_bbs

theorem initLocalsLoop_length (body : Body) (args : List Val) (idx : Nat)
    (tys : List MirTy) :
    (initLocalsLoop body args idx tys).length = tys.length := by
  induction tys generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    dsimp only [initLocalsLoop, List.length_cons]; rw [ih (idx + 1)]

theorem initRefLocalsLoop_eq {ts : List MirTy} {rbody : RefBody} {body : Body}
    (h : decodeBody ts rbody = some body) (args : List Val) (idx : Nat)
    (tys : List MirTy) :
    initRefLocalsLoop rbody args idx tys =
      zipRefLocals tys (initLocalsLoop body args idx tys) := by
  induction tys generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    let ⟨h_arg, _, _, _, _⟩ := decodeBody_inv h
    dsimp only [initRefLocalsLoop, initLocalsLoop, zipRefLocals]
    rw [h_arg, refHasStorageAnnotation_eq h idx, refLiveUninitSlot_eq,
      ih (idx + 1)]
    rfl

theorem getElem?_zero_of_blt {α : Type} {xs : List α} {n : Nat}
    (h : Nat.blt n xs.length = true) :
    ∃ x : α, MirSemantics.getElem? xs 0 = some x := by
  cases xs with
  | nil => cases h
  | cons x _ => exact ⟨x, rfl⟩

theorem initRefState_sim : InitRefStateSimClaim := by
  intro rp p q maxSteps h_dec
  let ⟨h_entry, h_width, h_prof, _, h_bodies⟩ := decodeProg_inv h_dec
  unfold initRefState initState
  rw [h_entry, h_width, h_prof]
  cases Nat.beq p.pointerWidthBits 64
  · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
    intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
  · -- Zeta-reduce the `let`s in both initializers; the remaining
    -- `if (!true) = true` guards reduce definitionally where needed.
    dsimp only
    cases Nat.beq p.mirProfileVersion 1
    · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
      intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
    · cases q.callerMem.allocations.isEmpty
      · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
        intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
      · cases h_b : MirSemantics.getElem? p.bodies p.entryDefId with
        | none =>
          rw [(mapOption_getElem? h_bodies p.entryDefId).1 h_b]
          refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
          intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
        | some body =>
          let ⟨rbody, h_rb_get, h_rb_dec⟩ :=
            (mapOption_getElem? h_bodies p.entryDefId).2 body h_b
          let ⟨h_arg, h_loc_dec, h_bbs_dec, _, _⟩ := decodeBody_inv h_rb_dec
          rw [h_rb_get]
          dsimp only
          rw [h_loc_dec]
          dsimp only
          rw [mapOption_isEmpty h_bbs_dec, h_arg,
            refStorageAnnotationsInBounds_eq h_rb_dec]
          cases body.basicBlocks.isEmpty
          · cases h_blt : Nat.blt body.argumentCount body.locals.length
            · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
              intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
            · cases storageAnnotationsInBounds body
              · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
              · rw [list_all_congr_eq body.locals _ _ refIsSupportedLocalTy_eq]
                cases body.locals.all isSupportedScalarOrUnitTy
                · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                  intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                · rw [checkRefArgsMatch_eq]
                  cases checkArgsMatch q.args
                      ((body.locals.drop 1).take body.argumentCount)
                  · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                    intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                  · let ⟨retTy, h_ret⟩ := getElem?_zero_of_blt h_blt
                    rw [h_ret]
                    dsimp only
                    refine ⟨?_, ?_⟩
                    · intro k hk; cases hk
                    · intro s₀ hs₀
                      injection hs₀ with h_s₀
                      subst h_s₀
                      rw [initRefLocalsLoop_eq h_rb_dec q.args 0 body.locals]
                      have h_entry_ret : entryRetTy? p = some retTy := by
                        dsimp only [entryRetTy?]
                        rw [h_b]
                        exact h_ret
                      refine ⟨_, rfl, ?_, rfl, rfl⟩
                      exact ⟨_, _, retTy, rfl, rfl, rfl, h_entry_ret, rfl,
                        body, h_b,
                        initLocalsLoop_length body q.args 0 body.locals, rfl⟩
          · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
            intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl

/-! ## Multi-Step Reachability and `anneal_corresponds_to_miri` -/

/-- Backward simulation for one step: a running $M_{\text{ref}}$ transition
from a simulated state is matched by an $M_{\text{anneal}}$ transition that
re-establishes `SimulationInv`. -/
theorem sim_of_refStep : SimOfRefStepClaim := by
  intro rp p s rs rs' h_dec h_sim h_rstep
  let ⟨f, rf, retTy, hs, hrs, hcm, hret, hdef, body, hbody, hlen, hrf⟩ := h_sim
  let ⟨c, hc, h_eval⟩ := h_rstep
  cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
  | false =>
    unfold evalRefStep at h_eval
    rw [h_lt] at h_eval
    cases h_eval
  | true =>
    rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_eval
    cases h_es : evalStep p c s with
    | done out =>
      rw [h_es] at h_eval
      cases h_eval
    | fault k =>
      rw [h_es] at h_eval
      cases k <;> cases h_eval
    | step s₁ =>
      let ⟨f₁, hs₁, hdef₁, hlen₁⟩ := evalStep_step_inv hs hbody hlen h_es
      subst hs₁
      rw [h_es] at h_eval
      dsimp only [mapStepRes, stepResultToRefOutcome] at h_eval
      injection h_eval with h_rs'
      subst h_rs'
      have hbody₁ : MirSemantics.getElem? p.bodies f₁.defId = some body := by
        rw [hdef₁]; exact hbody
      exact ⟨_, ⟨c, hc, h_es⟩, f₁, liftFrame body.locals f₁, retTy, rfl, rfl,
        rfl, hret, hdef₁.trans hdef, body, hbody₁, hlen₁, rfl⟩

/-- Backward simulation: every $M_{\text{ref}}$ state reachable from a
simulated state is simulated by a reachable $M_{\text{anneal}}$ state. -/
theorem sim_of_refReaches : SimOfRefReachesClaim := by
  intro rp p s₀ rs₀ rs h_dec h_sim₀ h_reach
  induction h_reach with
  | refl => exact ⟨s₀, Reaches.refl s₀, h_sim₀⟩
  | tail _ h_rstep ih =>
    let ⟨s₂, h_reach₂, h_sim₂⟩ := ih
    let ⟨s₃, h_step, h_sim₃⟩ := sim_of_refStep h_dec h_sim₂ h_rstep
    exact ⟨s₃, Reaches.tail h_reach₂ h_step, h_sim₃⟩

/-- Step-indexed reachability in $M_{\text{anneal}}$: `s₂` is reached from `s₁`
in exactly `n` transitions. -/
inductive ReachesN (p : Program) (s₁ : State) : Nat → State → Prop where
  | refl : ReachesN p s₁ 0 s₁
  | tail {n : Nat} {s₂ s₃ : State} :
      ReachesN p s₁ n s₂ →
      Step p s₂ (.step s₃) →
      ReachesN p s₁ (n + 1) s₃

/-- Step-indexed reachability in $M_{\text{ref}}$: `rs₂` is reached from `rs₁`
in exactly `n` `.running` transitions. -/
inductive RefReachesN (rp : RefProg) (rs₁ : RefState) :
    Nat → RefState → Prop where
  | refl : RefReachesN rp rs₁ 0 rs₁
  | tail {n : Nat} {rs₂ rs₃ : RefState} :
      RefReachesN rp rs₁ n rs₂ →
      RefStep rp rs₂ (.running rs₃) →
      RefReachesN rp rs₁ (n + 1) rs₃

theorem exists_reachesN_of_reaches {p : Program} {s₁ s₂ : State}
    (h : Reaches p s₁ s₂) :
    ∃ n : Nat, ReachesN p s₁ n s₂ := by
  induction h with
  | refl => exact ⟨0, ReachesN.refl⟩
  | tail _ h_step ih =>
    let ⟨n, h_in⟩ := ih
    exact ⟨n + 1, ReachesN.tail h_in h_step⟩

theorem refReaches_of_refReachesN {rp : RefProg} {rs₁ rs₂ : RefState}
    {n : Nat} (h : RefReachesN rp rs₁ n rs₂) :
    RefReaches rp rs₁ rs₂ := by
  induction h with
  | refl => exact RefReaches.refl rs₁
  | tail _ h_step ih => exact RefReaches.tail ih h_step

theorem nat_blt_eq_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

/-- Forward simulation for one step: while the step budget is not exhausted,
an $M_{\text{anneal}}$ transition from a simulated state is matched by one
running $M_{\text{ref}}$ transition that re-establishes `SimulationInv`. -/
theorem refStep_of_step {rp : RefProg} {p : Program} {s s' : State}
    {rs : RefState}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv p s rs)
    (h_step : Step p s (.step s'))
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true) :
    ∃ rs' : RefState,
      RefStep rp rs (.running rs') ∧
      SimulationInv p s' rs' ∧
      rs'.stepsExecuted = rs.stepsExecuted + 1 ∧
      rs'.maxSteps = rs.maxSteps := by
  let ⟨f, rf, retTy, hs, hrs, hcm, hret, hdef, body, hbody, hlen, hrf⟩ := h_sim
  let ⟨c, hc, h_es⟩ := h_step
  have h_ref_eq := evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c
  let ⟨f', hs', hdef', hlen'⟩ := evalStep_step_inv hs hbody hlen h_es
  rw [h_es, hs'] at h_ref_eq
  dsimp only [mapStepRes, stepResultToRefOutcome] at h_ref_eq
  let rs' : RefState := {
    frames := [callerSentinelFrame retTy, liftFrame body.locals f']
    callerMem := s.callerMem
    stepsExecuted := rs.stepsExecuted + 1
    maxSteps := rs.maxSteps
  }
  have h_rstep : RefStep rp rs (.running rs') := ⟨c, hc, h_ref_eq⟩
  have hbody' : MirSemantics.getElem? p.bodies f'.defId = some body := by
    rw [hdef']; exact hbody
  refine ⟨rs', h_rstep, ?_, rfl, rfl⟩
  rw [hs']
  exact ⟨f', liftFrame body.locals f', retTy, rfl, rfl, rfl, hret,
    hdef'.trans hdef, body, hbody', hlen', rfl⟩

/-- Step-indexed forward simulation: an `n`-step $M_{\text{anneal}}$ execution
from a simulated state is matched by an `n`-step $M_{\text{ref}}$ execution
whenever the reference step budget leaves room for `n` more steps. -/
theorem refReachesN_of_reachesN {rp : RefProg} {p : Program} {n : Nat}
    {s₁ s₂ : State} {rs₁ : RefState}
    (h_dec : decodeProg rp = some p)
    (h_in : ReachesN p s₁ n s₂)
    (h_sim₁ : SimulationInv p s₁ rs₁)
    (h_budget : rs₁.stepsExecuted + n ≤ rs₁.maxSteps) :
    ∃ rs₂ : RefState,
      RefReachesN rp rs₁ n rs₂ ∧
      SimulationInv p s₂ rs₂ ∧
      rs₂.stepsExecuted = rs₁.stepsExecuted + n ∧
      rs₂.maxSteps = rs₁.maxSteps := by
  induction h_in with
  | refl =>
    exact ⟨rs₁, RefReachesN.refl, h_sim₁, (Nat.add_zero _).symm, rfl⟩
  | @tail m s_mid s_next h_prev h_step ih =>
    have h_b₁ : rs₁.stepsExecuted + m ≤ rs₁.maxSteps :=
      Nat.le_of_succ_le h_budget
    let ⟨rs₂, h_rreach, h_sim₂, h_steps₂, h_max₂⟩ := ih h_b₁
    have h_lt : Nat.blt rs₂.stepsExecuted rs₂.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      rw [h_steps₂, h_max₂]
      exact h_budget
    let ⟨rs₃, h_rstep, h_sim₃, h_steps₃, h_max₃⟩ :=
      refStep_of_step h_dec h_sim₂ h_step h_lt
    refine ⟨rs₃, RefReachesN.tail h_rreach h_rstep, h_sim₃, ?_, ?_⟩
    · rw [h_steps₃, h_steps₂]
      rfl
    · rw [h_max₃, h_max₂]

/-- UB transfer: if `(p, q)` is well-formed in $M_{\text{anneal}}$, then
`encodeProg p` neither reaches `.ub` nor `.blocked` in $M_{\text{ref}}$ under
any step budget `maxSteps : Nat`. -/
theorem refWellFormed_of_wellFormed : RefWellFormedOfWellFormedClaim := by
  intro p q h_wf
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  let ⟨⟨s₀, h_init, _⟩, h_no_fault⟩ := h_wf
  intro maxSteps
  let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
    (initRefState_sim maxSteps h_dec).2 s₀ h_init
  refine ⟨⟨rs₀, h_rinit, fun _ _ => ⟨0, rfl⟩⟩, ?_, ?_⟩
  · intro h_ub
    unfold RefReachesOutcome at h_ub
    rw [h_rinit] at h_ub
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_ub
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches h_dec h_sim₀ h_rreach
    let ⟨f, rf, _, hs, hrs, hcm, _, _, body, hbody, hlen, hrf⟩ := h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, hs', _, _⟩ := evalStep_step_inv hs hbody hlen h_es
        rw [h_es, hs'] at h_reval
        cases h_reval
      | done out =>
        rw [h_es] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k with
        | unsupported => cases h_reval
        | undefined =>
          apply h_no_fault .undefined
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩
  · intro h_blk
    unfold RefReachesOutcome at h_blk
    rw [h_rinit] at h_blk
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_blk
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches h_dec h_sim₀ h_rreach
    let ⟨f, rf, _, hs, hrs, hcm, _, _, body, hbody, hlen, hrf⟩ := h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, hs', _, _⟩ := evalStep_step_inv hs hbody hlen h_es
        rw [h_es, hs'] at h_reval
        cases h_reval
      | done out =>
        rw [h_es] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k with
        | undefined => cases h_reval
        | unsupported =>
          apply h_no_fault .unsupported
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩

/-- Forward behavior transfer: every terminal behavior of `(p, q)` in
$M_{\text{anneal}}$ is a reference behavior of `encodeProg p` (witnessed by
step budget `n + 1` for an `n`-step execution). -/
theorem refBehavior_of_behavior : RefBehaviorOfBehaviorClaim := by
  intro p q out h_beh
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState p q with
  | error k =>
    rw [h_init] at h_beh
    cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨s_end, h_reach, c, hc, h_es⟩ := h_beh
    let ⟨n, h_in⟩ := exists_reachesN_of_reaches h_reach
    let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
      (initRefState_sim (n + 1) h_dec).2 s₀ h_init
    have h_budget : rs₀.stepsExecuted + n ≤ rs₀.maxSteps := by
      rw [h_steps₀, h_max₀, Nat.zero_add]
      exact Nat.le_succ n
    let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
      refReachesN_of_reachesN h_dec h_in h_sim₀ h_budget
    let ⟨f, rf, _, hs, hrs, hcm, _, _, body, hbody, hlen, hrf⟩ := h_sim_end
    have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
      exact Nat.lt_succ_self n
    have h_reval := evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c
    rw [h_es] at h_reval
    refine ⟨n + 1, ?_⟩
    unfold RefReachesOutcome
    rw [h_rinit]
    exact ⟨rs_end, refReaches_of_refReachesN h_rreach, c, hc, h_reval⟩

/-- Backward behavior transfer: every reference behavior of `encodeProg p` is
a terminal behavior of `(p, q)` in $M_{\text{anneal}}$, so $M_{\text{ref}}$
has no outcomes that $M_{\text{anneal}}$ omits. -/
theorem behavior_of_refBehavior : BehaviorOfRefBehaviorClaim := by
  intro p q out h_ref
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  let ⟨maxSteps, h_out⟩ := h_ref
  unfold RefReachesOutcome at h_out
  unfold Behavior ReachesResult
  cases h_init : initState p q with
  | error k =>
    rw [(initRefState_sim maxSteps h_dec).1 k h_init] at h_out
    cases k <;> cases h_out
  | ok s₀ =>
    let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
      (initRefState_sim maxSteps h_dec).2 s₀ h_init
    rw [h_rinit] at h_out
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_out
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches h_dec h_sim₀ h_rreach
    let ⟨f, rf, _, hs, hrs, hcm, _, _, body, hbody, hlen, hrf⟩ := h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, hs', _, _⟩ := evalStep_step_inv hs hbody hlen h_es
        rw [h_es, hs'] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k <;> cases h_reval
      | done out' =>
        rw [h_es] at h_reval
        dsimp only [mapStepRes, stepResultToRefOutcome] at h_reval
        injection h_reval with h_out_eq
        subst h_out_eq
        exact ⟨s, h_reach, c, hc, h_es⟩

/-- Terminal behaviors coincide exactly in $M_{\text{anneal}}$ and
$M_{\text{ref}}$. -/
theorem behavior_iff_refBehavior : BehaviorIffRefBehaviorClaim :=
  fun p q out =>
    ⟨refBehavior_of_behavior p q out, behavior_of_refBehavior p q out⟩

/-- Total state-lifting function from $M_{\text{anneal}}$ to $M_{\text{ref}}$
at step counters `(0, 0)`. -/
noncomputable def liftState (p : Program) (s : State) : RefState :=
  match s.frames, entryRetTy? p with
  | [f], some retTy =>
    match MirSemantics.getElem? p.bodies f.defId with
    | some body =>
      { frames := [callerSentinelFrame retTy, liftFrame body.locals f]
        callerMem := s.callerMem
        stepsExecuted := 0
        maxSteps := 0 }
    | none =>
      { frames := []
        callerMem := s.callerMem
        stepsExecuted := 0
        maxSteps := 0 }
  | _, _ =>
    { frames := []
      callerMem := s.callerMem
      stepsExecuted := 0
      maxSteps := 0 }

/-- Total state-projection function from $M_{\text{ref}}$ to
$M_{\text{anneal}}$. -/
noncomputable def projectState (rs : RefState) : State :=
  match rs.frames with
  | [_, rf] =>
    { frames := [{
        defId := rf.defId
        blockIdx := rf.blockIdx
        stmtIdx := rf.stmtIdx
        locals := unzipRefSlots rf.locals
      }]
      callerMem := rs.callerMem }
  | _ =>
    { frames := [], callerMem := rs.callerMem }

theorem simulationInv_with_counters {p : Program} {s : State} {rs : RefState}
    (steps max : Nat) (h : SimulationInv p s rs) :
    SimulationInv p s { rs with stepsExecuted := steps, maxSteps := max } := by
  let ⟨f, rf, retTy, hs, hrs, hcm, hret, hdef, hframe⟩ := h
  exact ⟨f, rf, retTy, hs, hrs, hcm, hret, hdef, hframe⟩

theorem simulationInv_of_with_counters {p : Program} {s : State} {rs : RefState}
    {steps max : Nat}
    (h : SimulationInv p s
      { rs with stepsExecuted := steps, maxSteps := max }) :
    SimulationInv p s rs := by
  let ⟨f, rf, retTy, hs, hrs, hcm, hret, hdef, hframe⟩ := h
  exact ⟨f, rf, retTy, hs, hrs, hcm, hret, hdef, hframe⟩

theorem liftState_sim_of_sim {p : Program} {s : State} {rs : RefState}
    (h : SimulationInv p s rs) :
    SimulationInv p s (liftState p s) := by
  let ⟨f, rf, retTy, hs, _, _, hret, hdef, body, hbody, hlen, _⟩ := h
  unfold liftState
  rw [hs, hret]
  dsimp only
  rw [hbody]
  exact ⟨f, liftFrame body.locals f, retTy, hs, rfl, rfl, hret, hdef, body,
    hbody, hlen, rfl⟩

theorem liftState_steps (p : Program) (s : State) :
    (liftState p s).stepsExecuted = 0 ∧ (liftState p s).maxSteps = 0 := by
  unfold liftState
  cases s.frames with
  | nil => exact ⟨rfl, rfl⟩
  | cons f fs =>
    cases fs with
    | cons _ _ => exact ⟨rfl, rfl⟩
    | nil =>
      cases entryRetTy? p with
      | none => exact ⟨rfl, rfl⟩
      | some _ =>
        dsimp only
        cases MirSemantics.getElem? p.bodies f.defId <;> exact ⟨rfl, rfl⟩

theorem liftState_eq_of_sim {p : Program} {s : State} {rs : RefState}
    (h : SimulationInv p s rs) :
    { liftState p s with
      stepsExecuted := rs.stepsExecuted
      maxSteps := rs.maxSteps } = rs :=
  refState_unique_of_simulationInv
    (simulationInv_with_counters rs.stepsExecuted rs.maxSteps
      (liftState_sim_of_sim h))
    h rfl rfl

theorem projectState_sim_of_sim {p : Program} {s : State} {rs : RefState}
    (h : SimulationInv p s rs) :
    projectState rs = s := by
  let ⟨f, rf, retTy, hs, hrs, hcm, _, _, body, _, hlen, hrf⟩ := h
  unfold projectState
  rw [hrs, hrf]
  dsimp only [liftFrame]
  rw [unzipRefSlots_zipRefLocals hlen, hcm]
  cases f
  cases s with | mk frames callerMem =>
  dsimp only at hs
  dsimp only
  rw [hs]

/-- Divergence coincides exactly in $M_{\text{anneal}}$ and $M_{\text{ref}}$:
`(p, q)` has an infinite execution trace in $M_{\text{anneal}}$ if and only if
`encodeProg p` has an infinite running execution trace in $M_{\text{ref}}$. -/
theorem diverges_iff_refDiverges : DivergesIffRefDivergesClaim := by
  intro p q
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  constructor
  · intro h_div
    let ⟨s₀, h_init, trace, h_t0, h_step⟩ := h_div
    let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
      (initRefState_sim 0 h_dec).2 s₀ h_init
    have h_inv : ∀ n : Nat, SimulationInv p (trace n) (liftState p (trace n)) :=
      fun n => by
        induction n with
        | zero =>
          rw [h_t0]
          exact liftState_sim_of_sim h_sim₀
        | succ m ih =>
          have h_sim_m := simulationInv_with_counters m (m + 1) ih
          have h_lt : Nat.blt m (m + 1) = true :=
            nat_blt_eq_true_of_lt (Nat.lt_succ_self m)
          let ⟨_, _, h_sim', _, _⟩ :=
            refStep_of_step h_dec h_sim_m (h_step m) h_lt
          exact liftState_sim_of_sim h_sim'
    refine ⟨rs₀, h_rinit, fun n => liftState p (trace n), ?_, ?_⟩
    · dsimp only
      rw [h_t0]
      exact refState_unique_of_simulationInv (liftState_sim_of_sim h_sim₀)
        h_sim₀ ((liftState_steps p s₀).1.trans h_steps₀.symm)
        ((liftState_steps p s₀).2.trans h_max₀.symm)
    · intro n
      dsimp only
      have h_sim_n := simulationInv_with_counters n (n + 1) (h_inv n)
      have h_lt : Nat.blt n (n + 1) = true :=
        nat_blt_eq_true_of_lt (Nat.lt_succ_self n)
      let ⟨rs', h_rstep, h_sim', h_steps', h_max'⟩ :=
        refStep_of_step h_dec h_sim_n (h_step n) h_lt
      have h_eq := liftState_eq_of_sim h_sim'
      rw [h_steps', h_max'] at h_eq
      rw [h_eq]
      exact h_rstep
  · intro h_rdiv
    let ⟨rs₀, h_rinit, rtrace, h_rt0, h_rstep⟩ := h_rdiv
    cases h_init : initState p q with
    | error k =>
      rw [(initRefState_sim 0 h_dec).1 k h_init] at h_rinit
      cases h_rinit
    | ok s₀ =>
      let ⟨rs₀', h_rinit', h_sim₀, _, _⟩ :=
        (initRefState_sim 0 h_dec).2 s₀ h_init
      rw [h_rinit'] at h_rinit
      injection h_rinit with h_eq
      subst h_eq
      have h_inv : ∀ n : Nat,
          SimulationInv p (projectState (rtrace n)) (rtrace n) := fun n => by
        induction n with
        | zero =>
          rw [h_rt0, projectState_sim_of_sim h_sim₀]
          exact h_sim₀
        | succ m ih =>
          have h_sim_m := simulationInv_with_counters m (m + 1) ih
          let ⟨_, _, h_sim'⟩ := sim_of_refStep h_dec h_sim_m (h_rstep m)
          have h_sim_succ := simulationInv_of_with_counters h_sim'
          rw [projectState_sim_of_sim h_sim_succ]
          exact h_sim_succ
      refine ⟨s₀, h_init, fun n => projectState (rtrace n), ?_, ?_⟩
      · dsimp only
        rw [h_rt0]
        exact projectState_sim_of_sim h_sim₀
      · intro n
        dsimp only
        have h_sim_n := simulationInv_with_counters n (n + 1) (h_inv n)
        let ⟨s', h_step_n, h_sim'⟩ := sim_of_refStep h_dec h_sim_n (h_rstep n)
        rw [projectState_sim_of_sim (simulationInv_of_with_counters h_sim')]
        exact h_step_n

/-- Main end-to-end operational correspondence theorem: for any
`p : Program` and `q : Query`, if `WellFormed p q` holds in
$M_{\text{anneal}}$, then:
1. `RefWellFormed (encodeProg p) q` holds across all step budgets
   `maxSteps : Nat` in the move-deinitializing reference machine
   $M_{\text{ref}}$;
2. `Behavior p q out` holds in $M_{\text{anneal}}$ exactly when
   `RefBehavior (encodeProg p) q out` holds in $M_{\text{ref}}$; and
3. `(p, q)` diverges in $M_{\text{anneal}}$ exactly when `encodeProg p`
   diverges in $M_{\text{ref}}$. -/
theorem anneal_corresponds_to_miri : CorrespondenceClaim :=
  fun p q h_wf =>
    ⟨refWellFormed_of_wellFormed p q h_wf, behavior_iff_refBehavior p q,
      diverges_iff_refDiverges p q⟩

/-- Bidirectional fault-kind correspondence theorem:
fault kinds `.undefined` and `.unsupported` in $M_{\text{anneal}}$ correspond
one-to-one with `.ub` and `.blocked` in $M_{\text{ref}}$
(`faultToRefOutcome k`). -/
theorem reachesResult_fault_iff_refReachesOutcome :
    FaultEquivalenceClaim := by
  intro p q k
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg p
  constructor
  · intro h_res
    unfold ReachesResult at h_res
    cases h_init : initState p q with
    | error k₀ =>
      rw [h_init] at h_res
      injection h_res with h_k
      subst h_k
      refine ⟨0, ?_⟩
      unfold RefReachesOutcome
      rw [(initRefState_sim 0 h_dec).1 k h_init]
    | ok s₀ =>
      rw [h_init] at h_res
      let ⟨s_end, h_reach, c, hc, h_es⟩ := h_res
      let ⟨n, h_in⟩ := exists_reachesN_of_reaches h_reach
      let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
        (initRefState_sim (n + 1) h_dec).2 s₀ h_init
      have h_budget : rs₀.stepsExecuted + n ≤ rs₀.maxSteps := by
        rw [h_steps₀, h_max₀, Nat.zero_add]
        exact Nat.le_succ n
      let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
        refReachesN_of_reachesN h_dec h_in h_sim₀ h_budget
      let ⟨f, rf, _, hs, hrs, hcm, _, _, body, hbody, hlen, hrf⟩ := h_sim_end
      have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
        apply nat_blt_eq_true_of_lt
        rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
        exact Nat.lt_succ_self n
      have h_reval := evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c
      rw [h_es] at h_reval
      refine ⟨n + 1, ?_⟩
      unfold RefReachesOutcome
      rw [h_rinit]
      exact ⟨rs_end, refReaches_of_refReachesN h_rreach, c, hc, h_reval⟩
  · intro h_ex
    let ⟨maxSteps, h_ref⟩ := h_ex
    unfold RefReachesOutcome at h_ref
    cases h_init : initState p q with
    | error k₀ =>
      rw [(initRefState_sim maxSteps h_dec).1 k₀ h_init] at h_ref
      unfold ReachesResult
      rw [h_init]
      cases k₀ <;> cases k <;> cases h_ref <;> rfl
    | ok s₀ =>
      let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
        (initRefState_sim maxSteps h_dec).2 s₀ h_init
      rw [h_rinit] at h_ref
      let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_ref
      let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches h_dec h_sim₀ h_rreach
      let ⟨f, rf, _, hs, hrs, hcm, _, _, body, hbody, hlen, hrf⟩ := h_sim
      cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
      | false =>
        unfold evalRefStep at h_reval
        rw [h_lt] at h_reval
        cases k <;> cases h_reval
      | true =>
        rw [evalRefStep_eq h_dec hs hrs hcm hbody hlen hrf h_lt c] at h_reval
        cases h_es : evalStep p c s with
        | step s' =>
          let ⟨_, hs', _, _⟩ := evalStep_step_inv hs hbody hlen h_es
          rw [h_es, hs'] at h_reval
          cases k <;> cases h_reval
        | done out =>
          rw [h_es] at h_reval
          cases k <;> cases h_reval
        | fault k₀ =>
          rw [h_es] at h_reval
          have hk_eq : k₀ = k := by
            cases k₀ <;> cases k <;> cases h_reval <;> rfl
          subst hk_eq
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩

theorem correspondence_claim_holds : CorrespondenceClaim :=
  anneal_corresponds_to_miri

theorem fault_equivalence_claim_holds : FaultEquivalenceClaim :=
  reachesResult_fault_iff_refReachesOutcome

theorem miri_move_deinit_wiring_claim_holds : MiriMoveDeinitWiringClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K U C O X Host _ cfg limits c state
    rfl
  · intro K U C O X Host _ cfg limits h_true
    refine ⟨?_, ?_⟩ <;>
      change (cfg.deinitMovedPlace || cfg.access.deinitMovedPlace) = true <;>
      rw [h_true] <;> rfl
  · intro Prov Extra State hooks frame state localId known h_false
    dsimp only [Miri.Interpreter.evalOperand]
    rw [h_false]
    rfl
  · intro Prov Extra State hooks frame frame₁ frame₂ state state₁ localId
        known imm layout h_true h_place h_rep
    dsimp only [Miri.Interpreter.evalOperand]
    rw [h_true, h_place]
    dsimp only [Array.isEmpty, Array.size, List.length]
    rw [h_rep]
    rfl
  · intro K U m isMove
    rfl
  · intro P S C E Other Extern FnABI ArgABI h choice place snap
    exact ⟨rfl, rfl⟩

/-! ## Move Deinitialization, Overflow, and Enum Canaries (`D6`–`D13`) -/

open Trusted.Correspondence Anneal.MirWp

/-- `D6` (Use-After-Move UB):
`_2 = move _1; _0 = copy _1; return` deinitializes `_1` on `move _1` and
faults with `.fault .undefined` (`.ub` in $M_{\text{ref}}$) on the subsequent
`copy _1`. -/
theorem canary_D6_use_after_move_ub : CanaryD6UseAfterMoveUbClaim := by
  have h_wp : wpFaultProg progUseAfterMoveD6 2 queryU32_42 .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub, h_excl, _, _, h_nwf⟩ := reaches_fault_and_exclusive_of_wpFault
    progUseAfterMoveD6 queryU32_42 2 .undefined h_wp
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progUseAfterMoveD6 queryU32_42 .undefined).1 h_ub
  exact ⟨h_ub, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf,
    h_ref_ub⟩

/-- `D7a` (`BinaryOp` left-to-right `copy _1` then `move _1` succeeds):
`_0 = BinOp(Add, copy _1, move _1); return` reads `_1` in `lhs`, then reads
and deinitializes `_1` in `rhs`, and returns `84`. -/
theorem canary_D7a_binop_copy_then_move_ok :
    CanaryD7aBinopCopyThenMoveOkClaim := by
  have h_wp : wpProg progBinOpCopyThenMoveD7a 2 queryU32_42
      (fun out => out = .returned ⟨u32Val 84, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, _, out, h_beh, h_eq⟩ := wellFormed_and_spec_of_wp
    progBinOpCopyThenMoveD7a queryU32_42 2 _ h_wp
  subst h_eq
  let ⟨h_rwf, h_rbeh, _⟩ := anneal_corresponds_to_miri
    progBinOpCopyThenMoveD7a queryU32_42 h_sat.1
  exact ⟨h_sat.1, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- `D7b` (`BinaryOp` left-to-right `move _1` then `copy _1` faults with UB):
`_0 = BinOp(Add, move _1, copy _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = copy _1`. -/
theorem canary_D7b_binop_move_then_copy_ub :
    CanaryD7bBinopMoveThenCopyUbClaim := by
  have h_wp :
      wpFaultProg progBinOpMoveThenCopyD7b 1 queryU32_42 .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub, h_excl, _, _, h_nwf⟩ := reaches_fault_and_exclusive_of_wpFault
    progBinOpMoveThenCopyD7b queryU32_42 1 .undefined h_wp
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progBinOpMoveThenCopyD7b queryU32_42 .undefined).1 h_ub
  exact ⟨h_ub, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf,
    h_ref_ub⟩

/-- `D7c` (`BinaryOp` left-to-right `move _1` then `move _1` faults with UB):
`_0 = BinOp(Add, move _1, move _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = move _1`. -/
theorem canary_D7c_binop_move_then_move_ub :
    CanaryD7cBinopMoveThenMoveUbClaim := by
  have h_wp :
      wpFaultProg progBinOpMoveThenMoveD7c 1 queryU32_42 .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub, h_excl, _, _, h_nwf⟩ := reaches_fault_and_exclusive_of_wpFault
    progBinOpMoveThenMoveD7c queryU32_42 1 .undefined h_wp
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progBinOpMoveThenMoveD7c queryU32_42 .undefined).1 h_ub
  exact ⟨h_ub, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf,
    h_ref_ub⟩

/-- `D8` (Self-move `_1 = move _1` preserves initialized value):
`_1 = move _1; _0 = copy _1; return` reads `42` from `_1`, deinitializes `_1`
to `.live none`, and then writes `42` back into `_1`, so the subsequent
`_0 = copy _1` succeeds and returns `42`. -/
theorem canary_D8_self_move_ok : CanaryD8SelfMoveOkClaim := by
  have h_wp : wpProg progSelfMoveD8 3 queryU32_42
      (fun out => out = .returned ⟨u32Val 42, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, _, out, h_beh, h_eq⟩ :=
    wellFormed_and_spec_of_wp progSelfMoveD8 queryU32_42 3 _ h_wp
  subst h_eq
  let ⟨h_rwf, h_rbeh, _⟩ :=
    anneal_corresponds_to_miri progSelfMoveD8 queryU32_42 h_sat.1
  exact ⟨h_sat.1, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- `D9` (Move of 0-Byte ZST `MirTy.unit` Remains Initialized):
`_2 = move _1; _0 = copy _1; return` where `_1 : ()` sets `_1` to
`liveUninitSlot .unit = .live (some .unit)`, so subsequent `_0 = copy _1`
succeeds and returns `.unit`. -/
theorem canary_D9_move_unit_zst_ok : CanaryD9MoveUnitZstOkClaim := by
  have h_wp : wpProg progMoveUnitZstD9 3 queryEmpty
      (fun out => out = .returned ⟨.unit, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, _, out, h_beh, h_eq⟩ :=
    wellFormed_and_spec_of_wp progMoveUnitZstD9 queryEmpty 3 _ h_wp
  subst h_eq
  let ⟨h_rwf, h_rbeh, _⟩ :=
    anneal_corresponds_to_miri progMoveUnitZstD9 queryEmpty h_sat.1
  exact ⟨h_sat.1, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- `D10` (unchecked versus wrapping overflow): on `(u32::MAX, 1)`,
`_0 = AddUnchecked(_1, _2)` (`progAddUncheckedU32`) reaches UB in both
machines, while wrapping `_0 = Add(_1, _2)` (`progAddU32`) returns `0` in both
machines. `encodeRvalue_binaryOp_iff` keeps the codec from exchanging the two
operators, so a semantics or codec that confused them would falsify one half
of this canary. -/
theorem canary_D10_add_unchecked_overflow_ub :
    CanaryD10AddUncheckedOverflowUbClaim := by
  let ⟨⟨h_ub, _, h_nwf⟩, _, h_beh⟩ :=
    canary_negative_ub_add_unchecked_overflow_u32
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progAddUncheckedU32 queryU32MaxPlusOne .undefined).1 h_ub
  exact ⟨h_ub, h_nwf, h_ref_ub, h_beh,
    (behavior_iff_refBehavior progAddU32 queryU32MaxPlusOne _).1 h_beh⟩

/-- `D11` (explicit-repr non-index fieldless enum constant tag decoding,
non-`isize` `u8` `Rvalue.discriminant`, and signed `i8` -> `isize` tag
sign-extension in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D11_enum_discriminant_and_const_ok :
    CanaryD11EnumDiscriminantAndConstOkClaim := by
  let ⟨⟨h_wf₁, h_beh₁⟩, ⟨h_wf₂, h_beh₂⟩⟩ :=
    Anneal.MirWp.canary_positive_enum_explicit_repr_anneal
  let ⟨h_rwf₁, h_rbeh₁, _⟩ :=
    anneal_corresponds_to_miri progEnumExplicitReprU8 queryEmpty h_wf₁
  let ⟨h_rwf₂, h_rbeh₂, _⟩ :=
    anneal_corresponds_to_miri progEnumSignedTagIsize queryEmpty h_wf₂
  exact ⟨h_wf₁, h_beh₁, h_rwf₁, (h_rbeh₁ _).1 h_beh₁,
    h_wf₂, h_beh₂, h_rwf₂, (h_rbeh₂ _).1 h_beh₂⟩

/-- `D12` (1-variant inhabited ZST enum implicit return, non-deinitializing
`Operand.move`, `ConstLit.zeroSized`, and `Variants.Single 0`
`Rvalue.discriminant` in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D12_zst_enum_move_and_discr_ok :
    CanaryD12ZstEnumMoveAndDiscrOkClaim := by
  let ⟨⟨h_wf₁, h_beh₁⟩, ⟨h_wf₂, h_beh₂⟩⟩ :=
    Anneal.MirWp.canary_positive_zst_single_enum_anneal
  let ⟨h_rwf₁, h_rbeh₁, _⟩ :=
    anneal_corresponds_to_miri progZstSingleEnumImplicitRet queryEmpty h_wf₁
  let ⟨h_rwf₂, h_rbeh₂, _⟩ :=
    anneal_corresponds_to_miri progZstSingleEnumMoveAndDiscr queryEmpty h_wf₂
  exact ⟨h_wf₁, h_beh₁, h_rwf₁, (h_rbeh₁ _).1 h_beh₁,
    h_wf₂, h_beh₂, h_rwf₂, (h_rbeh₂ _).1 h_beh₂⟩

/-- `D13` (invalid scalar enum tag `1` on `ReprU8 { A = 10, B = 20 }` and
reading `Rvalue.discriminant` from an uninitialized scalar-tagged enum local
reach UB in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D13_enum_invalid_tag_and_uninit_ub :
    CanaryD13EnumInvalidTagAndUninitUbClaim := by
  let ⟨⟨h_ub₁, h_nunsup₁, h_nwf₁⟩, ⟨h_ub₂, h_nunsup₂, h_nwf₂⟩⟩ :=
    Anneal.MirWp.canary_negative_ub_enum_invalid_tag_and_uninit_anneal
  have h_ref_ub₁ := (reachesResult_fault_iff_refReachesOutcome
    progEnumInvalidTagConstUb queryEmpty .undefined).1 h_ub₁
  have h_ref_ub₂ := (reachesResult_fault_iff_refReachesOutcome
    progEnumUninitDiscrUb queryEmpty .undefined).1 h_ub₂
  exact ⟨h_ub₁, h_nunsup₁, h_nwf₁, h_ref_ub₁,
    h_ub₂, h_nunsup₂, h_nwf₂, h_ref_ub₂⟩

end Anneal.MirCorrespondenceProof
