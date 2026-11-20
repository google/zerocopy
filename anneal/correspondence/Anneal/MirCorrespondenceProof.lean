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
theorems, and Pass 2 non-vacuity canaries (`D6`–`D19`) on top of the codec,
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

private theorem evalRefPlaceOperand_dead (ts : List MirTy)
    (rlocals : List RefLocalState) (localId : LocalId) (ty : MirTy)
    (proj : List Miri.MIR.ProjectionElem) (isMove : Bool)
    (h_get : MirSemantics.getElem? rlocals localId = some ⟨.dead, some ty⟩) :
    evalRefPlaceOperand ts rlocals localId proj isMove =
      .error .undefined := by
  dsimp only [evalRefPlaceOperand]
  rw [h_get]
  cases proj with
  | nil =>
    cases isMove <;> (
      cases ty with
      | enum ety =>
        dsimp only [refLocalLayoutForTy]
        cases refIsZstEnumTy ety <;> rfl
      | _ => rfl)
  | cons e es =>
    cases ty with
    | enum ety =>
      dsimp only [refLocalLayoutForTy]
      cases refIsZstEnumTy ety <;> rfl
    | _ => rfl

private theorem evalRefPlaceOperand_live_copy (ts : List MirTy)
    (rlocals : List RefLocalState) (localId : LocalId) (sv : SlotVal)
    (ty : MirTy)
    (h_get : MirSemantics.getElem? rlocals localId =
      some ⟨.live sv, some ty⟩) :
    evalRefPlaceOperand ts rlocals localId [] false =
      .ok (ty, sv, rlocals) := by
  dsimp only [evalRefPlaceOperand]
  rw [h_get]
  cases ty with
  | enum ety =>
    dsimp only [refLocalLayoutForTy]
    cases refIsZstEnumTy ety <;> rfl
  | _ => rfl

private theorem evalRefPlaceOperand_live_move (ts : List MirTy)
    (rlocals : List RefLocalState) (localId : LocalId) (sv : SlotVal)
    (ty : MirTy)
    (h_get : MirSemantics.getElem? rlocals localId =
      some ⟨.live sv, some ty⟩) :
    evalRefPlaceOperand ts rlocals localId [] true =
      match MirSemantics.setElem? rlocals localId
          ⟨liveUninitSlot ty, some ty⟩ with
      | some rlocals' => .ok (ty, sv, rlocals')
      | none => .error .unsupported := by
  dsimp only [evalRefPlaceOperand]
  rw [h_get]
  rw [← refLiveUninitSlot_eq ty]
  cases ty with
  | enum ety =>
    dsimp only [refLocalLayoutForTy]
    cases refIsZstEnumTy ety <;> rfl
  | _ => rfl

/-- A projected access of a live local reads the whole local through Miri and
then applies the adapter's field projection to its contents. -/
private theorem evalRefPlaceOperand_live_proj (ts : List MirTy)
    (rlocals : List RefLocalState) (localId : LocalId) (sv : SlotVal)
    (ty : MirTy) (e : Miri.MIR.ProjectionElem)
    (es : List Miri.MIR.ProjectionElem) (isMove : Bool)
    (h_get : MirSemantics.getElem? rlocals localId =
      some ⟨.live sv, some ty⟩) :
    evalRefPlaceOperand ts rlocals localId (e :: es) isMove =
      match refProjectTy? ts ty (e :: es), refReadSlotPath? sv (e :: es) with
      | some pty, some psv =>
        if !isMove then
          .ok (pty, psv, rlocals)
        else
          match refWriteSlotPath? sv (e :: es) (refUninitSlotVal pty) with
          | some root' =>
            match MirSemantics.setElem? rlocals localId
                ⟨.live root', some ty⟩ with
            | some rlocals' => .ok (pty, psv, rlocals')
            | none => .error .unsupported
          | none => .error .unsupported
      | _, _ => .error .unsupported := by
  dsimp only [evalRefPlaceOperand]
  rw [h_get]
  cases ty with
  | enum ety =>
    dsimp only [refLocalLayoutForTy]
    cases refIsZstEnumTy ety <;> rfl
  | _ => rfl

private theorem toMiriPlace_proj_isEmpty (rp : RefPlace) :
    (toMiriPlace rp).projection.isEmpty = rp.projection.isEmpty := by
  cases rp with | mk _ proj => cases proj <;> rfl

/-- Place-operand lockstep: evaluating the translated place in the reference
machine agrees with `evalPlaceOperand`, for unprojected and projected copies
and moves alike. -/
private theorem evalRefPlaceOperand_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot} {rp : RefPlace} {p : Place}
    (h_pl : decodePlace ts rp = some p) (isMove : Bool) :
    evalRefPlaceOperand ts (zipRefLocals bodyLocals slots) rp.localId
        (rp.projection.map toMiriProjElem) isMove =
      mapSlotRes bodyLocals (evalPlaceOperand bodyLocals slots p isMove) := by
  let ⟨h_id, h_proj⟩ := decodePlace_proj_inv h_pl
  rw [h_id]
  unfold evalPlaceOperand
  cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
  | none =>
    dsimp only [evalRefPlaceOperand]
    rw [getElem?_zipRefLocals_none_left h_ty]
    rfl
  | some localTy =>
    cases h_sl : MirSemantics.getElem? slots p.localId with
    | none =>
      dsimp only [evalRefPlaceOperand]
      rw [getElem?_zipRefLocals_none_right h_sl]
      rfl
    | some slot =>
      have h_z := getElem?_zipRefLocals_some h_ty h_sl
      cases slot with
      | dead =>
        rw [evalRefPlaceOperand_dead _ _ _ _ _ _ h_z]
        rfl
      | live root =>
        dsimp only
        cases h_rproj : rp.projection with
        | nil =>
          rw [h_rproj] at h_proj
          injection h_proj with h_p
          rw [← h_p]
          cases isMove with
          | false =>
            exact evalRefPlaceOperand_live_copy _ _ _ _ _ h_z
          | true =>
            have h_mv := evalRefPlaceOperand_live_move ts _ _ root _ h_z
            dsimp only [List.map]
            rw [h_mv]
            dsimp only [projectTy?, readSlotPath?, writeSlotPath?,
              liveUninitSlot]
            cases h_set :
                MirSemantics.setElem? slots p.localId
                  (.live (uninitSlotVal localTy)) with
            | none =>
              rw [setElem?_zipRefLocals_none h_set]
              rfl
            | some slots' =>
              rw [setElem?_zipRefLocals_some h_ty h_set]
              rfl
        | cons e es =>
          rw [h_rproj] at h_proj
          have h_map : List.map toMiriProjElem (e :: es) =
              toMiriProjElem e :: List.map toMiriProjElem es := rfl
          rw [h_map, evalRefPlaceOperand_live_proj _ _ _ _ _ _ _ _ h_z,
            ← h_map, refProjectTy?_eq h_proj, refReadSlotPath?_eq h_proj]
          cases projectTy? localTy p.projection with
          | none => rfl
          | some pty =>
            cases readSlotPath? root p.projection with
            | none => rfl
            | some psv =>
              cases isMove with
              | false => rfl
              | true =>
                dsimp only
                rw [refWriteSlotPath?_eq h_proj, refUninitSlotVal_eq]
                cases writeSlotPath? root p.projection (uninitSlotVal pty) with
                | none => rfl
                | some root' =>
                  dsimp only
                  cases h_set :
                      MirSemantics.setElem? slots p.localId (.live root') with
                  | none =>
                    rw [setElem?_zipRefLocals_none h_set]
                    rfl
                  | some slots' =>
                    rw [setElem?_zipRefLocals_some h_ty h_set]
                    rfl

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
      exact evalRefPlaceOperand_eq h_pl false
  | move rp =>
    dsimp only [decodeOperand, optMap] at h_dec
    cases h_pl : decodePlace ts rp with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some p =>
      rw [h_pl] at h_dec
      injection h_dec with h_op
      subst h_op
      exact evalRefPlaceOperand_eq h_pl true
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

private theorem readRefPrimitiveSlot_eq (ty : MirTy) (sv : SlotVal) :
    readRefPrimitiveSlot ty sv =
      if !isPrimitiveReadableTy ty then
        .error .unsupported
      else
        match sv.toVal? with
        | some v => .ok v
        | none => .error .undefined := by
  dsimp only [readRefPrimitiveSlot]
  rw [refIsPrimitiveReadableTy_eq]
  cases isPrimitiveReadableTy ty <;> rfl

private theorem miriImmToPayload?_roundtrip {α : Type}
    (x : α) :
    miriImmediateToPayload? (payloadToMiriImmediate x) = some x := rfl

/-- Reading a live adapter local through Miri returns its contents. -/
private theorem evalPlaceToOp_sized_live (sv : SlotVal) :
    Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false)
        (mkSingleLocalMiriFrame (slotToMiriLocalValue (.live sv)) false) ()
        ⟨0, Array.empty⟩ (some refSizedLocalLayout) =
      ⟨mkSingleLocalMiriFrame (slotToMiriLocalValue (.live sv)) false, (),
        .ok ⟨.immediate (payloadToMiriImmediate sv), refSizedLocalLayout⟩⟩ :=
  rfl

/-- Place-write lockstep: writing through the translated destination in the
reference machine agrees with `writePlace`. -/
theorem writeRefPlace_eq {ts bodyLocals : List MirTy} {slots : List LocalSlot}
    {rproj : List RefProjectionElem} {dst : Place} {localTy dstTy : MirTy}
    {val : Val}
    (h_ty : MirSemantics.getElem? bodyLocals dst.localId = some localTy)
    (h_proj : mapOption (decodeProjElem ts) rproj = some dst.projection) :
    writeRefPlace (zipRefLocals bodyLocals slots)
        ⟨dst.localId, rproj.map toMiriProjElem, dstTy⟩ val =
      mapSlotsRes bodyLocals (writePlace slots dst dstTy val) := by
  unfold writeRefPlace writePlace
  dsimp only
  rw [checkRefVal_eq]
  cases checkVal val dstTy
  · rfl
  · cases h_sl : MirSemantics.getElem? slots dst.localId with
    | none =>
      rw [getElem?_zipRefLocals_none_right h_sl]
      rfl
    | some slot =>
      rw [getElem?_zipRefLocals_some h_ty h_sl]
      cases slot with
      | dead => rfl
      | live root =>
        dsimp only [Bool.not, ite_false_eq_true]
        rw [evalPlaceToOp_sized_live]
        dsimp only
        rw [miriImmToPayload?_roundtrip]
        dsimp only
        rw [refWriteSlotPath?_eq h_proj]
        cases writeSlotPath? root dst.projection val.toSlotVal with
        | none => rfl
        | some root' =>
          dsimp only
          cases h_set :
              MirSemantics.setElem? slots dst.localId (.live root') with
          | none =>
            rw [setElem?_zipRefLocals_none h_set]
            rfl
          | some slots' =>
            rw [setElem?_zipRefLocals_some h_ty h_set]
            rfl

private theorem refProjElemMayAlias_eq {ts : List MirTy}
    {re₁ re₂ : RefProjectionElem} {e₁ e₂ : ProjectionElem}
    (h₁ : decodeProjElem ts re₁ = some e₁)
    (h₂ : decodeProjElem ts re₂ = some e₂) :
    refProjElemMayAlias (toMiriProjElem re₁) (toMiriProjElem re₂) =
      projElemMayAlias e₁ e₂ := by
  cases re₁ with
  | deref =>
    injection h₁ with h₁'
    subst h₁'
    cases re₂ with
    | deref => injection h₂ with h₂'; subst h₂'; rfl
    | unsupported => injection h₂ with h₂'; subst h₂'; rfl
    | field i tid =>
      dsimp only [decodeProjElem, optMap] at h₂
      cases h_t : MirSemantics.getElem? ts tid with
      | none => rw [h_t] at h₂; cases h₂
      | some ty => rw [h_t] at h₂; injection h₂ with h₂'; subst h₂'; rfl
  | unsupported =>
    injection h₁ with h₁'
    subst h₁'
    cases re₂ with
    | deref => injection h₂ with h₂'; subst h₂'; rfl
    | unsupported => injection h₂ with h₂'; subst h₂'; rfl
    | field i tid =>
      dsimp only [decodeProjElem, optMap] at h₂
      cases h_t : MirSemantics.getElem? ts tid with
      | none => rw [h_t] at h₂; cases h₂
      | some ty => rw [h_t] at h₂; injection h₂ with h₂'; subst h₂'; rfl
  | field i tid₁ =>
    dsimp only [decodeProjElem, optMap] at h₁
    cases h_t₁ : MirSemantics.getElem? ts tid₁ with
    | none => rw [h_t₁] at h₁; cases h₁
    | some ty₁ =>
      rw [h_t₁] at h₁
      injection h₁ with h₁'
      subst h₁'
      cases re₂ with
      | deref => injection h₂ with h₂'; subst h₂'; rfl
      | unsupported => injection h₂ with h₂'; subst h₂'; rfl
      | field j tid₂ =>
        dsimp only [decodeProjElem, optMap] at h₂
        cases h_t₂ : MirSemantics.getElem? ts tid₂ with
        | none => rw [h_t₂] at h₂; cases h₂
        | some ty₂ => rw [h_t₂] at h₂; injection h₂ with h₂'; subst h₂'; rfl

private theorem refProjPrefixMayAlias_eq {ts : List MirTy}
    {rp₁ rp₂ : List RefProjectionElem} {p₁ p₂ : List ProjectionElem}
    (h₁ : mapOption (decodeProjElem ts) rp₁ = some p₁)
    (h₂ : mapOption (decodeProjElem ts) rp₂ = some p₂) :
    refProjPrefixMayAlias (rp₁.map toMiriProjElem) (rp₂.map toMiriProjElem) =
      projPrefixMayAlias p₁ p₂ := by
  induction rp₁ generalizing rp₂ p₁ p₂ with
  | nil =>
    injection h₁ with h₁'
    subst h₁'
    rfl
  | cons a as ih =>
    let ⟨a', as', h_a, h_as, h_eq₁⟩ := mapOption_cons_inv h₁
    subst h_eq₁
    cases rp₂ with
    | nil =>
      injection h₂ with h₂'
      subst h₂'
      rfl
    | cons b bs =>
      let ⟨b', bs', h_b, h_bs, h_eq₂⟩ := mapOption_cons_inv h₂
      subst h_eq₂
      dsimp only [List.map, refProjPrefixMayAlias, projPrefixMayAlias]
      rw [refProjElemMayAlias_eq h_a h_b, ih h_as h_bs]

private theorem refPlacesMayOverlap_eq {ts : List MirTy}
    {ra rb : RefPlace} {a b : Place}
    (h_a : decodePlace ts ra = some a)
    (h_b : decodePlace ts rb = some b) :
    refPlacesMayOverlap (toMiriPlace ra) (toMiriPlace rb) =
      placesMayOverlap a b := by
  let ⟨h_ida, h_pa⟩ := decodePlace_proj_inv h_a
  let ⟨h_idb, h_pb⟩ := decodePlace_proj_inv h_b
  dsimp only [refPlacesMayOverlap, placesMayOverlap, toMiriPlace]
  rw [h_ida, h_idb, refProjPrefixMayAlias_eq h_pa h_pb,
    refProjPrefixMayAlias_eq h_pb h_pa]

private theorem refOperandMayOverlapPlace_eq {ts : List MirTy}
    {rdst : RefPlace} {dst : Place} {rop : RefOperand} {op : Operand}
    (h_dst : decodePlace ts rdst = some dst)
    (h_op : decodeOperand ts rop = some op) :
    refOperandMayOverlapPlace (toMiriPlace rdst) (toMiriOperand rop) =
      operandMayOverlapPlace dst op := by
  cases rop with
  | copy rp =>
    dsimp only [decodeOperand, optMap] at h_op
    cases h_p : decodePlace ts rp with
    | none => rw [h_p] at h_op; cases h_op
    | some p =>
      rw [h_p] at h_op
      injection h_op with h_eq
      subst h_eq
      exact refPlacesMayOverlap_eq h_dst h_p
  | move rp =>
    dsimp only [decodeOperand, optMap] at h_op
    cases h_p : decodePlace ts rp with
    | none => rw [h_p] at h_op; cases h_op
    | some p =>
      rw [h_p] at h_op
      injection h_op with h_eq
      subst h_eq
      exact refPlacesMayOverlap_eq h_dst h_p
  | constant rc =>
    dsimp only [decodeOperand, optMap] at h_op
    cases h_t : MirSemantics.getElem? ts rc.ty with
    | none => rw [h_t] at h_op; cases h_op
    | some ty =>
      rw [h_t] at h_op
      injection h_op with h_eq
      subst h_eq
      cases rc with | mk _ lit => cases lit <;> rfl

private theorem refAnyOperandMayOverlapPlace_eq {ts : List MirTy}
    {rdst : RefPlace} {dst : Place} {rops : List RefOperand}
    {ops : List Operand}
    (h_dst : decodePlace ts rdst = some dst)
    (h_ops : mapOption (decodeOperand ts) rops = some ops) :
    refAnyOperandMayOverlapPlace (toMiriPlace rdst) (rops.map toMiriOperand) =
      anyOperandMayOverlapPlace dst ops := by
  induction rops generalizing ops with
  | nil =>
    injection h_ops with h_eq
    subst h_eq
    rfl
  | cons ro ros ih =>
    let ⟨o, os, h_o, h_os, h_eq⟩ := mapOption_cons_inv h_ops
    subst h_eq
    dsimp only [List.map, refAnyOperandMayOverlapPlace,
      anyOperandMayOverlapPlace]
    rw [refOperandMayOverlapPlace_eq h_dst h_o, ih h_os]

private theorem refIsTupleTy_eq (ty : MirTy) :
    refIsTupleTy ty = isTupleTy ty := by
  cases ty <;> rfl

private theorem refAssignHasUnsupportedOverlap_eq {ts : List MirTy}
    {rdst : RefPlace} {dst : Place} (dstTy : MirTy)
    {rrv : RefRvalue} {rv : Rvalue}
    (h_dst : decodePlace ts rdst = some dst)
    (h_rv : decodeRvalue ts rrv = some rv) :
    refAssignHasUnsupportedOverlap (toMiriPlace rdst) dstTy
        (toMiriRvalue rrv) =
      assignHasUnsupportedOverlap dst dstTy rv := by
  cases rrv with
  | use rop =>
    dsimp only [decodeRvalue, optMap] at h_rv
    cases h_op : decodeOperand ts rop with
    | none => rw [h_op] at h_rv; cases h_rv
    | some op =>
      rw [h_op] at h_rv
      injection h_rv with h_eq
      subst h_eq
      dsimp only [toMiriRvalue, refAssignHasUnsupportedOverlap,
        assignHasUnsupportedOverlap]
      rw [refIsTupleTy_eq, refOperandMayOverlapPlace_eq h_dst h_op]
  | aggregateTuple rops =>
    dsimp only [decodeRvalue, optMap] at h_rv
    cases h_ops : mapOption (decodeOperand ts) rops with
    | none => rw [h_ops] at h_rv; cases h_rv
    | some ops =>
      rw [h_ops] at h_rv
      injection h_rv with h_eq
      subst h_eq
      dsimp only [toMiriRvalue, refAssignHasUnsupportedOverlap,
        assignHasUnsupportedOverlap]
      exact refAnyOperandMayOverlapPlace_eq h_dst h_ops
  | binaryOp op lhs rhs =>
    dsimp only [decodeRvalue, optMap2] at h_rv
    cases h_l : decodeOperand ts lhs with
    | none => rw [h_l] at h_rv; cases h_rv
    | some l =>
      cases h_r : decodeOperand ts rhs with
      | none => rw [h_l, h_r] at h_rv; cases h_rv
      | some r =>
        rw [h_l, h_r] at h_rv
        injection h_rv with h_eq
        subst h_eq
        rfl
  | unaryOp op rop =>
    dsimp only [decodeRvalue, optMap] at h_rv
    cases h_o : decodeOperand ts rop with
    | none => rw [h_o] at h_rv; cases h_rv
    | some o =>
      rw [h_o] at h_rv
      injection h_rv with h_eq
      subst h_eq
      rfl
  | discriminant rp =>
    dsimp only [decodeRvalue, optMap] at h_rv
    cases h_p : decodePlace ts rp with
    | none => rw [h_p] at h_rv; cases h_rv
    | some p =>
      rw [h_p] at h_rv
      injection h_rv with h_eq
      subst h_eq
      rfl
  | ref m rp =>
    dsimp only [decodeRvalue, optMap] at h_rv
    cases h_p : decodePlace ts rp with
    | none => rw [h_p] at h_rv; cases h_rv
    | some p =>
      rw [h_p] at h_rv
      injection h_rv with h_eq
      subst h_eq
      cases m <;> rfl
  | addressOf m rp =>
    dsimp only [decodeRvalue, optMap] at h_rv
    cases h_p : decodePlace ts rp with
    | none => rw [h_p] at h_rv; cases h_rv
    | some p =>
      rw [h_p] at h_rv
      injection h_rv with h_eq
      subst h_eq
      cases m <;> rfl
  | cast kind rop tyId =>
    dsimp only [decodeRvalue, optMap2] at h_rv
    cases h_o : decodeOperand ts rop with
    | none => rw [h_o] at h_rv; cases h_rv
    | some o =>
      cases h_t : MirSemantics.getElem? ts tyId with
      | none => rw [h_o, h_t] at h_rv; cases h_rv
      | some ty =>
        rw [h_o, h_t] at h_rv
        injection h_rv with h_eq
        subst h_eq
        rfl
  | unsupported =>
    injection h_rv with h_eq
    subst h_eq
    rfl

private theorem evalRefMiriRvalue_use (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (rop : RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_no_ov : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.use rop)) = false) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.use rop)) =
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
      | .error k => .error k
      | .ok (srcTy, sv, rlocals₁) =>
        if !(MirTy.beq srcTy dstTy) then
          .error .unsupported
        else
          match sv.toVal? with
          | some v => writeRefPlace rlocals₁ ⟨dstId, proj, dstTy⟩ v
          | none => .error .undefined := by
  dsimp only [evalRefMiriRvalue]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no_ov]
  dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
    Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
    Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
    EStateM.pure]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨srcTy, sv, rlocals₁⟩ := res
    dsimp only
    rw [miriImmToPayload?_roundtrip]
    dsimp only
    cases MirTy.beq srcTy dstTy
    · rfl
    · cases sv.toVal? with
      | none => rfl
      | some v =>
        dsimp only
        cases writeRefPlace rlocals₁ ⟨dstId, proj, dstTy⟩ v with
        | error k => cases k <;> rfl
        | ok _ => rfl

private theorem evalRefMiriRvalue_binaryOp (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (op : BinOp) (lhs rhs : RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.binaryOp op lhs rhs)) =
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand lhs) with
      | .error k => .error k
      | .ok (lTy, lSv, rlocals₁) =>
        match readRefPrimitiveSlot lTy lSv with
        | .error k => .error k
        | .ok lVal =>
          match evalRefMiriOperandToSlot ts rlocals₁ (toMiriOperand rhs) with
          | .error k => .error k
          | .ok (rTy, rSv, rlocals₂) =>
            match readRefPrimitiveSlot rTy rSv with
            | .error k => .error k
            | .ok rVal =>
              match evalRefBinOp op lVal rVal with
              | .error k => .error k
              | .ok v => writeRefPlace rlocals₂ ⟨dstId, proj, dstTy⟩ v := by
  have h_step :
      Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.binaryOp op lhs rhs)) ⟨dstId, Array.mk proj⟩
          rlocals =
        match evalRefMiriOperandToSlot ts rlocals (toMiriOperand lhs) with
        | .error k => .error (faultToStepError k) rlocals
        | .ok (lTy, lSv, rlocals₁) =>
          match readRefPrimitiveSlot lTy lSv with
          | .error k => .error (faultToStepError k) rlocals₁
          | .ok lVal =>
            match evalRefMiriOperandToSlot ts rlocals₁ (toMiriOperand rhs) with
            | .error k => .error (faultToStepError k) rlocals₁
            | .ok (rTy, rSv, rlocals₂) =>
              match readRefPrimitiveSlot rTy rSv with
              | .error k => .error (faultToStepError k) rlocals₂
              | .ok rVal =>
                match evalRefBinOp op lVal rVal with
                | .error k =>
                  .error (faultToStepError k) rlocals₂
                | .ok v =>
                  match writeRefPlace rlocals₂ ⟨dstId, proj, dstTy⟩ v with
                  | .error k =>
                    .error (faultToStepError k) rlocals₂
                  | .ok locals' => .ok () locals' := by
    dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
      Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
      evalRefBinOp, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
    rw [h_dst]
    dsimp only
    rw [h_pty]
    dsimp only
    cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand lhs) with
    | error _ => rfl
    | ok resL =>
      let ⟨lTy, lSv, rlocals₁⟩ := resL
      dsimp only
      rw [miriImmToPayload?_roundtrip]
      dsimp only
      cases readRefPrimitiveSlot lTy lSv with
      | error _ => rfl
      | ok lVal =>
        dsimp only
        cases evalRefMiriOperandToSlot ts rlocals₁ (toMiriOperand rhs) with
        | error _ => rfl
        | ok resR =>
          let ⟨rTy, rSv, rlocals₂⟩ := resR
          dsimp only
          rw [miriImmToPayload?_roundtrip]
          dsimp only
          cases readRefPrimitiveSlot rTy rSv with
          | error _ => rfl
          | ok rVal =>
            dsimp only
            rw [miriImmToPayload?_roundtrip,
              miriImmToPayload?_roundtrip]
            dsimp only
            rw [Anneal.MirWp.toVal?_toSlotVal, Anneal.MirWp.toVal?_toSlotVal]
            dsimp only
            cases evalRefMiriBinOp (toMiriBinOp op) lVal rVal with
            | error _ => rfl
            | ok v =>
              dsimp only
              rw [miriImmToPayload?_roundtrip]
              dsimp only
              rw [Anneal.MirWp.toVal?_toSlotVal]
              rfl
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.binaryOp op lhs rhs)) = false := rfl
  dsimp only [evalRefMiriRvalue]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  dsimp only [Miri.Interpreter.runRvalue]
  rw [h_step]
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand lhs) with
  | error k => cases k <;> rfl
  | ok resL =>
    let ⟨lTy, lSv, rlocals₁⟩ := resL
    dsimp only
    cases readRefPrimitiveSlot lTy lSv with
    | error k => cases k <;> rfl
    | ok lVal =>
      dsimp only
      cases evalRefMiriOperandToSlot ts rlocals₁ (toMiriOperand rhs) with
      | error k => cases k <;> rfl
      | ok resR =>
        let ⟨rTy, rSv, rlocals₂⟩ := resR
        dsimp only
        cases readRefPrimitiveSlot rTy rSv with
        | error k => cases k <;> rfl
        | ok rVal =>
          dsimp only
          cases evalRefBinOp op lVal rVal with
          | error k => cases k <;> rfl
          | ok v =>
            dsimp only
            cases writeRefPlace rlocals₂ ⟨dstId, proj, dstTy⟩ v with
            | error k => cases k <;> rfl
            | ok _ => rfl

private theorem evalRefMiriRvalue_unaryOp (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (op : UnOp) (rop : RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.unaryOp op rop)) =
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
      | .error k => .error k
      | .ok (ty, sv, rlocals₁) =>
        match readRefPrimitiveSlot ty sv with
        | .error k => .error k
        | .ok v =>
          match evalRefUnOp op v with
          | .error k => .error k
          | .ok u => writeRefPlace rlocals₁ ⟨dstId, proj, dstTy⟩ u := by
  have h_step :
      Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.unaryOp op rop)) ⟨dstId, Array.mk proj⟩
          rlocals =
        match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
        | .error k => .error (faultToStepError k) rlocals
        | .ok (ty, sv, rlocals₁) =>
          match readRefPrimitiveSlot ty sv with
          | .error k => .error (faultToStepError k) rlocals₁
          | .ok v =>
            match evalRefUnOp op v with
            | .error k => .error (faultToStepError k) rlocals₁
            | .ok u =>
              match writeRefPlace rlocals₁ ⟨dstId, proj, dstTy⟩ u with
              | .error k => .error (faultToStepError k) rlocals₁
              | .ok locals' => .ok () locals' := by
    dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
      Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
      evalRefUnOp, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
    rw [h_dst]
    dsimp only
    rw [h_pty]
    dsimp only
    cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
    | error _ => rfl
    | ok res =>
      let ⟨ty, sv, rlocals₁⟩ := res
      dsimp only
      rw [miriImmToPayload?_roundtrip]
      dsimp only
      cases readRefPrimitiveSlot ty sv with
      | error _ => rfl
      | ok v =>
        dsimp only
        rw [miriImmToPayload?_roundtrip]
        dsimp only
        rw [Anneal.MirWp.toVal?_toSlotVal]
        dsimp only
        cases evalRefMiriUnOp (toMiriUnOp op) v with
        | error _ => rfl
        | ok u =>
          dsimp only
          rw [miriImmToPayload?_roundtrip]
          dsimp only
          rw [Anneal.MirWp.toVal?_toSlotVal]
          rfl
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.unaryOp op rop)) = false := rfl
  dsimp only [evalRefMiriRvalue]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  dsimp only [Miri.Interpreter.runRvalue]
  rw [h_step]
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨ty, sv, rlocals₁⟩ := res
    dsimp only
    cases readRefPrimitiveSlot ty sv with
    | error k => cases k <;> rfl
    | ok v =>
      dsimp only
      cases evalRefUnOp op v with
      | error k => cases k <;> rfl
      | ok u =>
        dsimp only
        cases writeRefPlace rlocals₁ ⟨dstId, proj, dstTy⟩ u with
        | error k => cases k <;> rfl
        | ok _ => rfl

private theorem evalRefMiriRvalue_cast (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (kind : CastKind) (rop : RefOperand)
    (tyId : TyId)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.cast kind rop tyId)) =
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
      | .error k => .error k
      | .ok (srcTy, sv, rlocals₁) =>
        match readRefPrimitiveSlot srcTy sv with
        | .error k => .error k
        | .ok v =>
          match kind with
          | .unsupported => .error .unsupported
          | .intToInt =>
            match MirSemantics.getElem? ts tyId with
            | none => .error .unsupported
            | some castTy =>
              if !(MirTy.beq castTy dstTy) then
                .error .unsupported
              else
                match evalRefMiriIntToIntCast v castTy with
                | .error k => .error k
                | .ok res =>
                  writeRefPlace rlocals₁ ⟨dstId, proj, dstTy⟩ res := by
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.cast kind rop tyId)) = false := rfl
  dsimp only [evalRefMiriRvalue]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
    Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
    Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
    EStateM.pure]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨srcTy, sv, rlocals₁⟩ := res
    dsimp only
    rw [miriImmToPayload?_roundtrip]
    dsimp only
    cases readRefPrimitiveSlot srcTy sv with
    | error k => cases k <;> rfl
    | ok v =>
      dsimp only
      cases kind with
      | unsupported => rfl
      | intToInt =>
        dsimp only [toMiriCastKind]
        cases MirSemantics.getElem? ts tyId with
        | none => rfl
        | some castTy =>
          dsimp only
          cases MirTy.beq castTy dstTy
          · rfl
          · dsimp only [Bool.not, ite_false_eq_true]
            cases evalRefMiriIntToIntCast v castTy with
            | error k => cases k <;> rfl
            | ok res₂ =>
              dsimp only
              cases writeRefPlace rlocals₁ ⟨dstId, proj, dstTy⟩ res₂ with
              | error k => cases k <;> rfl
              | ok _ => rfl

/-- Appending a single tuple-field projection step preserves slot-write
agreement independently of the field type tag carried on `.Field`/`.field`. -/
private theorem refWriteSlotPath?_append_field_eq {ts : List MirTy}
    {rproj : List RefProjectionElem} {proj : List ProjectionElem}
    (h : mapOption (decodeProjElem ts) rproj = some proj)
    (sv new : SlotVal) (idx : Nat) (tyId : TyId) (fieldTy : MirTy) :
    refWriteSlotPath? sv (rproj.map toMiriProjElem ++ [.Field idx tyId]) new =
      writeSlotPath? sv (proj ++ [.field idx fieldTy]) new := by
  induction rproj generalizing proj sv with
  | nil =>
    injection h with h_eq
    subst h_eq
    cases sv with
    | tuple fields =>
      dsimp only [List.map, List.nil_append, refWriteSlotPath?, writeSlotPath?]
      cases MirSemantics.getElem? fields idx <;> rfl
    | _ => rfl
  | cons e es ih =>
    let ⟨e', es', h_e, h_es, h_eq⟩ := mapOption_cons_inv h
    subst h_eq
    cases e with
    | deref =>
      injection h_e with h_e'
      subst h_e'
      cases sv <;> rfl
    | unsupported =>
      injection h_e with h_e'
      subst h_e'
      cases sv <;> rfl
    | field i tid =>
      dsimp only [decodeProjElem, optMap] at h_e
      cases h_t : MirSemantics.getElem? ts tid with
      | none => rw [h_t] at h_e; cases h_e
      | some fty =>
        rw [h_t] at h_e
        injection h_e with h_e'
        subst h_e'
        cases sv with
        | tuple fields =>
          dsimp only [List.map, List.cons_append, toMiriProjElem,
            refWriteSlotPath?, writeSlotPath?]
          cases MirSemantics.getElem? fields i with
          | none => rfl
          | some field =>
            dsimp only
            rw [ih h_es field]
            cases writeSlotPath? field (es' ++ [.field idx fieldTy]) new <;>
              rfl
        | _ => rfl

/-- Writing to an appended tuple field in the reference machine agrees with
`writePlace` on `dst.projection ++ [.field idx fieldTy]`. -/
private theorem writeRefPlace_append_field_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot} {rproj : List RefProjectionElem} {dst : Place}
    {localTy fieldTy : MirTy} {val : Val} (idx : Nat) (tyId : TyId)
    (h_ty : MirSemantics.getElem? bodyLocals dst.localId = some localTy)
    (h_proj : mapOption (decodeProjElem ts) rproj = some dst.projection) :
    writeRefPlace (zipRefLocals bodyLocals slots)
        ⟨dst.localId, rproj.map toMiriProjElem ++ [.Field idx tyId], fieldTy⟩
        val =
      mapSlotsRes bodyLocals
        (writePlace slots
          { dst with projection := dst.projection ++ [.field idx fieldTy] }
          fieldTy val) := by
  unfold writeRefPlace writePlace
  dsimp only
  rw [checkRefVal_eq]
  cases checkVal val fieldTy
  · rfl
  · cases h_sl : MirSemantics.getElem? slots dst.localId with
    | none =>
      rw [getElem?_zipRefLocals_none_right h_sl]
      rfl
    | some slot =>
      rw [getElem?_zipRefLocals_some h_ty h_sl]
      cases slot with
      | dead => rfl
      | live root =>
        dsimp only [Bool.not, ite_false_eq_true]
        rw [evalPlaceToOp_sized_live]
        dsimp only
        rw [miriImmToPayload?_roundtrip]
        dsimp only
        rw [refWriteSlotPath?_append_field_eq h_proj]
        cases writeSlotPath? root (dst.projection ++ [.field idx fieldTy])
            val.toSlotVal with
        | none => rfl
        | some root' =>
          dsimp only
          cases h_set :
              MirSemantics.setElem? slots dst.localId (.live root') with
          | none =>
            rw [setElem?_zipRefLocals_none h_set]
            rfl
          | some slots' =>
            rw [setElem?_zipRefLocals_some h_ty h_set]
            rfl

private def stepErrorToFault : Miri.Interpreter.StepError → FaultKind
  | .undefinedBehavior _ => .undefined
  | .stack (.localExpectedLive _) => .undefined
  | _ => .unsupported

private theorem stepErrorToFault_faultToStepError (k : FaultKind) :
    stepErrorToFault (faultToStepError k) = k := by
  cases k <;> rfl

private theorem getElem?_append_length {α : Type} (xs ys : List α) (y : α) :
    MirSemantics.getElem? (xs ++ y :: ys) xs.length = some y := by
  induction xs with
  | nil => rfl
  | cons _ rest ih => exact ih

private theorem range_zero_size (n : Nat) (h : 0 < 1) :
    (Std.Legacy.Range.mk 0 n 1 h).size = n := by
  dsimp only [Std.Legacy.Range.size]
  simp

private theorem array_getElem?_map_append {α β : Type} (f : α → β)
    (pfx rest : List α) (x : α) :
    (Array.mk ((pfx ++ x :: rest).map f))[pfx.length]? = some (f x) := by
  rw [List.map_append]
  have h_len : (pfx.map f).length = pfx.length := List.length_map f
  rw [← h_len]
  simp

private theorem rvalueM_bind_apply {σ α β : Type}
    (m : Miri.Interpreter.RvalueM σ α)
    (k : α → Miri.Interpreter.RvalueM σ β) (s : σ) :
    (Bind.bind m k) s =
      match m s with
      | .ok a s' => k a s'
      | .error e s' => .error e s' := by
  dsimp only [Bind.bind, EStateM.bind]
  cases m s <;> rfl

private theorem if_bool_true {α : Type} {c : Bool} {a b : α} (h : c = true) :
    (if c = true then a else b) = a := by
  rw [h]; rfl

private theorem if_bool_false {α : Type} {c : Bool} {a b : α} (h : c = false) :
    (if c = true then a else b) = b := by
  rw [h]; exact ite_eq_right (fun hc => Bool.noConfusion hc)

private theorem writeAggregate_tuple_apply {Prov σ Ctx Place : Type}
    (hooks : Miri.Interpreter.AggregateHooks Prov σ Ctx Place)
    (c : Ctx) (ops : Array Miri.MIR.Operand) (dest : Place) (s : σ) :
    let body : Nat → PUnit → Miri.Interpreter.RvalueM σ (ForInStep PUnit) :=
      fun index _ =>
        match ops[index]? with
        | some operand =>
          Bind.bind
            (hooks.projectField c dest
              ((none : Option Miri.MIR.FieldIndex).getD index))
            (fun field =>
              Bind.bind
                (hooks.evalOperandAt c
                  (Miri.Interpreter.OperandPath.aggregate index) operand
                  (some (hooks.placeLayout field)))
                (fun operand =>
                  Bind.bind (hooks.copyOpNoValidate c operand field false)
                    (fun _ => Pure.pure (ForInStep.yield PUnit.unit))))
        | _ =>
          Bind.bind
            (throw
              (Miri.Interpreter.StepError.invalidProgram
                "aggregate operand index"))
            (fun (_ : PUnit) => Pure.pure (ForInStep.yield PUnit.unit))
    Miri.Interpreter.writeAggregate hooks c .Tuple ops dest s =
      match (forIn (List.range' 0 ops.size 1) PUnit.unit body) s with
      | .ok _ s' =>
        (Bind.bind (hooks.writeDiscriminant c 0 dest)
          (fun _ =>
            Bind.bind (hooks.enforceValidity c (hooks.placeLayout dest))
              (fun b => if b then hooks.validate c dest else Pure.pure ()))) s'
      | .error e s' => .error e s' := by
  intro body
  have h_sz : (Std.Legacy.Range.mk 0 ops.size 1 (by decide)).size = ops.size :=
    range_zero_size ops.size (by decide)
  have h_pure : ∀ {α β : Type} (a : α) (k : α → Miri.Interpreter.RvalueM σ β),
      (Bind.bind (Pure.pure a) k) s = k a s := fun _ _ => rfl
  let cont : PUnit → Miri.Interpreter.RvalueM σ Unit :=
    fun _ =>
      Bind.bind (hooks.writeDiscriminant c 0 dest)
        (fun _ =>
          Bind.bind (hooks.enforceValidity c (hooks.placeLayout dest))
            (fun b => if b then hooks.validate c dest else Pure.pure ()))
  have h_eq : Miri.Interpreter.writeAggregate hooks c .Tuple ops dest s =
      (Bind.bind (forIn (List.range' 0 ops.size 1) PUnit.unit body) cont) s := by
    dsimp only [Miri.Interpreter.writeAggregate]
    rw [h_pure]
    dsimp only [Option.isSome, Bool.false_and]
    rw [ite_eq_right (fun h => Bool.noConfusion h)]
    rw [Std.Legacy.Range.forIn_eq_forIn_range', h_sz]
    rfl
  rw [h_eq, rvalueM_bind_apply]
  cases (forIn (List.range' 0 ops.size 1) PUnit.unit body) s <;> rfl

/-- Field-by-field loop lockstep between `Miri.Interpreter.writeAggregate`'s
range loop over `refAggregateHooks` and `writeAggregateTupleFields`. -/
private theorem writeAggregate_loop_eq {ts bodyLocals : List MirTy}
    {rproj : List RefProjectionElem} {dst : Place} {localTy : MirTy}
    (h_ty : MirSemantics.getElem? bodyLocals dst.localId = some localTy)
    (h_proj : mapOption (decodeProjElem ts) rproj = some dst.projection)
    (pfx rops : List RefOperand) (ops : List Operand)
    (pfxTys fieldTys : List MirTy) (slots : List LocalSlot)
    (h_plen : pfxTys.length = pfx.length)
    (h_flen : rops.length = fieldTys.length)
    (h_dec : mapOption (decodeOperand ts) rops = some ops) :
    let allOps : Array Miri.MIR.Operand :=
      Array.mk ((pfx ++ rops).map toMiriOperand)
    let dest : RefDest :=
      ⟨dst.localId, rproj.map toMiriProjElem, .tuple (pfxTys ++ fieldTys)⟩
    let step : Nat → PUnit →
        Miri.Interpreter.RvalueM (List RefLocalState) (ForInStep PUnit) :=
      fun index _ =>
        match allOps[index]? with
        | some operand =>
          Bind.bind
            ((refAggregateHooks ts).projectField () dest
              ((none : Option Miri.MIR.FieldIndex).getD index))
            (fun field =>
              Bind.bind
                ((refAggregateHooks ts).evalOperandAt ()
                  (Miri.Interpreter.OperandPath.aggregate index) operand
                  (some ((refAggregateHooks ts).placeLayout field)))
                (fun operand =>
                  Bind.bind
                    ((refAggregateHooks ts).copyOpNoValidate () operand field
                      false)
                    (fun _ => Pure.pure (ForInStep.yield PUnit.unit))))
        | _ =>
          Bind.bind
            (throw
              (Miri.Interpreter.StepError.invalidProgram
                "aggregate operand index"))
            (fun (_ : PUnit) => Pure.pure (ForInStep.yield PUnit.unit))
    match writeAggregateTupleFields bodyLocals dst pfx.length slots ops
        fieldTys with
    | .ok slots' =>
      forIn (List.range' pfx.length rops.length 1) PUnit.unit step
        (zipRefLocals bodyLocals slots) =
        .ok PUnit.unit (zipRefLocals bodyLocals slots')
    | .error k =>
      ∃ err s_err,
        forIn (List.range' pfx.length rops.length 1) PUnit.unit step
          (zipRefLocals bodyLocals slots) = .error err s_err ∧
        stepErrorToFault err = k := by
  induction rops generalizing pfx ops pfxTys fieldTys slots with
  | nil =>
    injection h_dec with h_ops
    subst h_ops
    cases fieldTys with
    | nil => rfl
    | cons _ _ => cases h_flen
  | cons ro ros ih =>
    let ⟨o, os, h_o, h_os, h_eq⟩ := mapOption_cons_inv h_dec
    subst h_eq
    cases fieldTys with
    | nil => cases h_flen
    | cons ft fts =>
      have h_flen' : ros.length = fts.length := Nat.succ.inj h_flen
      have h_range :
          List.range' pfx.length (ro :: ros).length 1 =
            pfx.length :: List.range' (pfx.length + 1) ros.length 1 := rfl
      have h_step :
          (match (Array.mk ((pfx ++ ro :: ros).map toMiriOperand))[pfx.length]?
            with
            | some operand =>
              Bind.bind
                ((refAggregateHooks ts).projectField ()
                  ⟨dst.localId, rproj.map toMiriProjElem,
                    .tuple (pfxTys ++ ft :: fts)⟩
                  ((none : Option Miri.MIR.FieldIndex).getD pfx.length))
                (fun field =>
                  Bind.bind
                    ((refAggregateHooks ts).evalOperandAt ()
                      (Miri.Interpreter.OperandPath.aggregate pfx.length)
                      operand
                      (some ((refAggregateHooks ts).placeLayout field)))
                    (fun operand =>
                      Bind.bind
                        ((refAggregateHooks ts).copyOpNoValidate () operand
                          field false)
                        (fun _ => Pure.pure (ForInStep.yield PUnit.unit))))
            | _ =>
              Bind.bind
                (throw
                  (Miri.Interpreter.StepError.invalidProgram
                    "aggregate operand index"))
                (fun (_ : PUnit) => Pure.pure (ForInStep.yield PUnit.unit)))
              (zipRefLocals bodyLocals slots) =
            match evalOperandToSlot bodyLocals slots o with
            | .error k =>
              .error (faultToStepError k) (zipRefLocals bodyLocals slots)
            | .ok (srcTy, sv, slots₁) =>
              if !(MirTy.beq srcTy ft) then
                .error (.unsupported "aggregate field type mismatch")
                  (zipRefLocals bodyLocals slots₁)
              else
                match sv.toVal? with
                | none =>
                  .error (.undefinedBehavior "uninit aggregate field operand")
                    (zipRefLocals bodyLocals slots₁)
                | some v =>
                  match writePlace slots₁
                      { dst with
                        projection :=
                          dst.projection ++ [.field pfx.length ft] }
                      ft v with
                  | .error k =>
                    .error (faultToStepError k) (zipRefLocals bodyLocals slots₁)
                  | .ok slots₂ =>
                    .ok (ForInStep.yield PUnit.unit)
                      (zipRefLocals bodyLocals slots₂) := by
        rw [array_getElem?_map_append toMiriOperand pfx ros ro]
        dsimp only [Option.getD, Miri.Interpreter.AggregateHooks.evalOperandAt,
          refAggregateHooks, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
        rw [← h_plen, getElem?_append_length pfxTys fts ft, h_plen]
        dsimp only [EStateM.bind, EStateM.pure]
        rw [evalRefMiriOperandToSlot_eq h_o]
        cases evalOperandToSlot bodyLocals slots o with
        | error _ => rfl
        | ok res =>
          let ⟨srcTy, sv, slots₁⟩ := res
          dsimp only [mapSlotRes]
          rw [miriImmToPayload?_roundtrip]
          dsimp only
          cases MirTy.beq srcTy ft with
          | false => rfl
          | true =>
            rw [ite_eq_right (fun h => Bool.noConfusion h)]
            cases sv.toVal? with
            | none => rfl
            | some v =>
              dsimp only
              rw [writeRefPlace_append_field_eq pfx.length 0 h_ty h_proj]
              cases writePlace slots₁
                  { dst with
                    projection := dst.projection ++ [.field pfx.length ft] }
                  ft v <;> rfl
      dsimp only [writeAggregateTupleFields]
      rw [h_range, List.forIn_cons, rvalueM_bind_apply, h_step]
      cases evalOperandToSlot bodyLocals slots o with
      | error k =>
        exact ⟨faultToStepError k, zipRefLocals bodyLocals slots, rfl,
          stepErrorToFault_faultToStepError k⟩
      | ok res =>
        let ⟨srcTy, sv, slots₁⟩ := res
        dsimp only
        cases MirTy.beq srcTy ft with
        | false =>
          exact ⟨.unsupported "aggregate field type mismatch",
            zipRefLocals bodyLocals slots₁, rfl, rfl⟩
        | true =>
          rw [ite_eq_right (fun h => Bool.noConfusion h)]
          rw [ite_eq_right (fun h => Bool.noConfusion h)]
          cases sv.toVal? with
          | none =>
            exact ⟨.undefinedBehavior "uninit aggregate field operand",
              zipRefLocals bodyLocals slots₁, rfl, rfl⟩
          | some v =>
            dsimp only
            cases writePlace slots₁
                { dst with
                  projection := dst.projection ++ [.field pfx.length ft] }
                ft v with
            | error k =>
              exact ⟨faultToStepError k, zipRefLocals bodyLocals slots₁, rfl,
                stepErrorToFault_faultToStepError k⟩
            | ok slots₂ =>
              dsimp only
              have h_assoc_ops : (pfx ++ [ro]) ++ ros = pfx ++ (ro :: ros) :=
                List.append_assoc pfx [ro] ros
              have h_assoc_tys :
                  (pfxTys ++ [ft]) ++ fts = pfxTys ++ (ft :: fts) :=
                List.append_assoc pfxTys [ft] fts
              have h_len_pfx : (pfx ++ [ro]).length = pfx.length + 1 := by
                rw [List.length_append]
                rfl
              have h_plen' :
                  (pfxTys ++ [ft]).length = (pfx ++ [ro]).length := by
                rw [List.length_append, List.length_append, h_plen]
                rfl
              have h_ih := ih (pfx ++ [ro]) os (pfxTys ++ [ft]) fts slots₂
                h_plen' h_flen' h_os
              dsimp only at h_ih
              rw [h_assoc_ops, h_assoc_tys, h_len_pfx] at h_ih
              exact h_ih

/-- Tuple-aggregate lockstep: evaluating `.aggregateTuple` through
`Miri.Interpreter.evalRvalueIntoPlace` and `Miri.Interpreter.writeAggregate`
agrees with `writeAggregateTuple`. -/
private theorem evalRefMiriRvalue_aggregateTuple_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot} {rproj : List RefProjectionElem} {dst : Place}
    {dstSlot : LocalSlot} {localTy dstTy : MirTy}
    {rops : List RefOperand} {ops : List Operand}
    (h_ty : MirSemantics.getElem? bodyLocals dst.localId = some localTy)
    (h_proj : mapOption (decodeProjElem ts) rproj = some dst.projection)
    (h_dst : MirSemantics.getElem? (zipRefLocals bodyLocals slots) dst.localId =
      some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy (rproj.map toMiriProjElem) = some dstTy)
    (h_ops : mapOption (decodeOperand ts) rops = some ops)
    (h_no_ov : refAssignHasUnsupportedOverlap
      ⟨dst.localId, Array.mk (rproj.map toMiriProjElem)⟩ dstTy
      (toMiriRvalue (.aggregateTuple rops)) = false) :
    evalRefMiriRvalue ts (zipRefLocals bodyLocals slots)
        ⟨dst.localId, Array.mk (rproj.map toMiriProjElem)⟩
        (toMiriRvalue (.aggregateTuple rops)) =
      mapSlotsRes bodyLocals
        (writeAggregateTuple bodyLocals slots dst dstTy ops) := by
  have h_ev_place :
      Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.aggregateTuple rops))
          ⟨dst.localId, Array.mk (rproj.map toMiriProjElem)⟩
          (zipRefLocals bodyLocals slots) =
        (refRvalueHooks ts).writeAggregate () .Tuple
          (Array.mk (rops.map toMiriOperand))
          ⟨dst.localId, rproj.map toMiriProjElem, dstTy⟩
          (zipRefLocals bodyLocals slots) := by
    dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace]
    rw [rvalueM_bind_apply]
    have h_ep :
        (refRvalueHooks ts).evalPlace ()
            ⟨dst.localId, Array.mk (rproj.map toMiriProjElem)⟩ true
            (zipRefLocals bodyLocals slots) =
          .ok ⟨dst.localId, rproj.map toMiriProjElem, dstTy⟩
            (zipRefLocals bodyLocals slots) := by
      dsimp only [refRvalueHooks]
      rw [h_dst]; dsimp only; rw [h_pty]
    rw [h_ep]
  dsimp only [evalRefMiriRvalue]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no_ov]
  rw [ite_eq_right (fun h => Bool.noConfusion h)]
  cases rops with
  | nil =>
    injection h_ops with h_eq
    subst h_eq
    cases dstTy with
    | unit =>
      have h_ev :
          Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
              (toMiriRvalue (.aggregateTuple []))
              ⟨dst.localId, Array.mk (rproj.map toMiriProjElem)⟩
              (zipRefLocals bodyLocals slots) =
            match writePlace slots dst .unit .unit with
            | .error k =>
              .error (faultToStepError k) (zipRefLocals bodyLocals slots)
            | .ok slots' => .ok () (zipRefLocals bodyLocals slots') := by
        rw [h_ev_place]
        have h_v :
            (!Nat.beq (Array.mk ([].map toMiriOperand)).size 0) = false := rfl
        have h_w :
            (refRvalueHooks ts).writeAggregate () .Tuple
                (Array.mk ([].map toMiriOperand))
                ⟨dst.localId, rproj.map toMiriProjElem, .unit⟩
                (zipRefLocals bodyLocals slots) =
              Miri.Interpreter.writeAggregate (refAggregateHooks ts) () .Tuple
                (Array.mk ([].map toMiriOperand))
                ⟨dst.localId, rproj.map toMiriProjElem, .unit⟩
                (zipRefLocals bodyLocals slots) := by
          dsimp only [refRvalueHooks]
          exact if_bool_false h_v
        rw [h_w, writeAggregate_tuple_apply]
        have h_sz0 : (Array.mk ([].map toMiriOperand)).size = 0 := rfl
        rw [h_sz0]
        dsimp only [List.range']
        rw [List.forIn_nil]
        dsimp only [refAggregateHooks, Bind.bind, Pure.pure, EStateM.bind,
          EStateM.pure]
        rw [writeRefPlace_eq h_ty h_proj]
        cases writePlace slots dst .unit .unit <;> rfl
      dsimp only [Miri.Interpreter.runRvalue, writeAggregateTuple]
      rw [h_ev]
      cases writePlace slots dst .unit .unit with
      | error k => cases k <;> rfl
      | ok _ => rfl
    | tuple fieldTys =>
      dsimp only [Miri.Interpreter.runRvalue]
      rw [h_ev_place]
      cases fieldTys <;> rfl
    | _ =>
      dsimp only [Miri.Interpreter.runRvalue]
      rw [h_ev_place]
      rfl
  | cons ro ros =>
    let ⟨o, os, _, _, h_eq⟩ := mapOption_cons_inv h_ops
    subst h_eq
    cases dstTy with
    | tuple fieldTys =>
      cases fieldTys with
      | nil =>
        dsimp only [Miri.Interpreter.runRvalue]
        rw [h_ev_place]
        rfl
      | cons ft fts =>
        have h_len_map :
            (Array.mk ((ro :: ros).map toMiriOperand)).size =
              (ro :: ros).length := List.length_map toMiriOperand
        have h_len_ops : (ro :: ros).length = (o :: os).length :=
          mapOption_length h_ops
        cases h_beq : Nat.beq (o :: os).length (ft :: fts).length with
        | false =>
          have h_ev :
              Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
                  (toMiriRvalue (.aggregateTuple (ro :: ros)))
                  ⟨dst.localId, Array.mk (rproj.map toMiriProjElem)⟩
                  (zipRefLocals bodyLocals slots) =
                .error (.unsupported "tuple aggregate shape mismatch")
                  (zipRefLocals bodyLocals slots) := by
            rw [h_ev_place]
            have h_v :
                (!(!(ft :: fts).isEmpty &&
                  Nat.beq (Array.mk ((ro :: ros).map toMiriOperand)).size
                    (ft :: fts).length)) = true := by
              rw [h_len_map, h_len_ops, h_beq]; rfl
            dsimp only [refRvalueHooks]
            exact if_bool_true h_v
          dsimp only [Miri.Interpreter.runRvalue, writeAggregateTuple]
          rw [h_ev, h_beq]
          rfl
        | true =>
          have h_flen : (ro :: ros).length = (ft :: fts).length := by
            rw [h_len_ops]
            exact Nat.eq_of_beq_eq_true h_beq
          have h_ev :
              Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
                  (toMiriRvalue (.aggregateTuple (ro :: ros)))
                  ⟨dst.localId, Array.mk (rproj.map toMiriProjElem)⟩
                  (zipRefLocals bodyLocals slots) =
                Miri.Interpreter.writeAggregate (refAggregateHooks ts) () .Tuple
                  (Array.mk ((ro :: ros).map toMiriOperand))
                  ⟨dst.localId, rproj.map toMiriProjElem, .tuple (ft :: fts)⟩
                  (zipRefLocals bodyLocals slots) := by
            rw [h_ev_place]
            have h_v :
                (!(!(ft :: fts).isEmpty &&
                  Nat.beq (Array.mk ((ro :: ros).map toMiriOperand)).size
                    (ft :: fts).length)) = false := by
              rw [h_len_map, h_len_ops, h_beq]; rfl
            dsimp only [refRvalueHooks]
            exact if_bool_false h_v
          have h_loop := writeAggregate_loop_eq h_ty h_proj [] (ro :: ros)
            (o :: os) [] (ft :: fts) slots rfl h_flen h_ops
          dsimp only [List.nil_append, List.length_nil] at h_loop
          dsimp only [Miri.Interpreter.runRvalue, writeAggregateTuple]
          rw [h_ev, writeAggregate_tuple_apply, h_len_map, h_beq]
          rw [ite_eq_right (fun h => Bool.noConfusion h)]
          cases h_wf : writeAggregateTupleFields bodyLocals dst 0 slots
              (o :: os) (ft :: fts) with
          | ok slots' =>
            rw [h_wf] at h_loop
            rw [h_loop]
            rfl
          | error k =>
            rw [h_wf] at h_loop
            let ⟨err, s_err, h_err, h_k⟩ := h_loop
            rw [h_err]
            dsimp only
            cases err with
            | undefinedBehavior _ => cases h_k; rfl
            | stack se =>
              cases se <;> (cases h_k; rfl)
            | _ => cases h_k; rfl
    | _ =>
      dsimp only [Miri.Interpreter.runRvalue]
      rw [h_ev_place]
      rfl

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
              SlotVal.scalar ⟨ety.discrWidth, ety.discrSigned,
                truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩),
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
    (sv : SlotVal) :
    (Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false)
      (mkSingleLocalMiriFrameWithLayout (slotToMiriLocalValue (.live sv))
        ⟨tid, refEnumLayoutData ety⟩ false) () ⟨0, Array.empty⟩
      (some ⟨tid, refEnumLayoutData ety⟩)).outcome =
    .ok ⟨.immediate (payloadToMiriImmediate sv),
      ⟨tid, refEnumLayoutData ety⟩⟩ := by
  cases ety with
  | mk _ _ _ tr _ => cases tr <;> rfl

private theorem evalRefMiriRvalue_discriminant_eq {ts : List MirTy}
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (rp : RefPlace)
    (h_dst :
      MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_tys : ∀ (id : LocalId) (slot : LocalSlot) (ety : EnumTy),
      MirSemantics.getElem? rlocals id = some ⟨slot, some (.enum ety)⟩ →
      ∃ tid, MirSemantics.getElem? ts tid = some (.enum ety)) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
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
            | .zeroSized, .live .uninit =>
              match MirSemantics.getElem? ety.discriminants 0 with
              | some disc =>
                writeRefPlace rlocals ⟨dstId, proj, dstTy⟩
                  (.scalar ⟨ety.discrWidth, ety.discrSigned,
                    truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
              | none => .error .unsupported
            | .zeroSized, .live (.enumVal ety' v) =>
              if EnumTy.beq ety ety' && Nat.beq v 0 then
                match MirSemantics.getElem? ety.discriminants 0 with
                | some disc =>
                  writeRefPlace rlocals ⟨dstId, proj, dstTy⟩
                    (.scalar ⟨ety.discrWidth, ety.discrSigned,
                      truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
                | none => .error .unsupported
              else
                .error .unsupported
            | .zeroSized, .live _ => .error .unsupported
            | .scalar _ _, .live .uninit => .error .undefined
            | .scalar _ _, .live (.enumVal ety' v) =>
              if EnumTy.beq ety ety' && Nat.blt v ety.discriminants.length then
                match MirSemantics.getElem? ety.discriminants v with
                | some disc =>
                  writeRefPlace rlocals ⟨dstId, proj, dstTy⟩
                    (.scalar ⟨ety.discrWidth, ety.discrSigned,
                      truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
                | none => .error .unsupported
              else
                .error .unsupported
            | .scalar _ _, .live _ => .error .unsupported
        | _ => .error .unsupported := by
  let mapErr : Miri.Interpreter.StepError →
      Except FaultKind (List RefLocalState) :=
    fun err =>
      match err with
      | .undefinedBehavior _ | .stack (.localExpectedLive _) =>
        .error .undefined
      | _ => .error .unsupported
  let finishDiscr : Miri.Interpreter.OpTy (MirTy × SlotVal) →
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
          | some (_, sv) =>
            match sv.toVal? with
            | some v => writeRefPlace s₃ ⟨dstId, proj, dstTy⟩ v
            | none => .error .unsupported
          | none => .error .unsupported
  have h_arr :
      (!(Array.empty : Array Miri.MIR.ProjectionElem).isEmpty) = false := rfl
  have h_unfold :
      evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
          (toMiriRvalue (.discriminant rp)) =
        match evalRefEnumPlaceToOp ts (toMiriPlace rp) rlocals with
        | .error err _ => mapErr err
        | .ok op s₁ => finishDiscr op s₁ := by
    have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
        (toMiriRvalue (.discriminant rp)) = false := rfl
    dsimp only [evalRefMiriRvalue]
    rw [h_dst]
    dsimp only
    rw [h_pty]
    dsimp only
    rw [h_no]
    dsimp only [toMiriRvalue,
      Miri.Interpreter.evalRvalueIntoPlace, refRvalueHooks,
      Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
      EStateM.pure]
    rw [h_dst]
    dsimp only
    rw [h_pty]
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
          | mk ty sv₁ =>
            cases ty with
            | enum ety₁ =>
              dsimp only
              cases encodeRefEnumTagOp ety₁ sv₁ with
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
                              dsimp only [SlotVal.toVal?]
                              cases writeRefPlace s₃ ⟨dstId, proj, dstTy⟩
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
                | live sv =>
                  let layout : Miri.Interpreter.LocalLayout :=
                    ⟨enumTyId, refEnumLayoutData ety⟩
                  have h_op :
                      evalRefEnumPlaceToOp ts ⟨localId, Array.empty⟩ rlocals =
                        .ok ⟨.immediate (payloadToMiriImmediate
                              (.enum ety, sv)), layout⟩ rlocals := by
                    dsimp only [evalRefEnumPlaceToOp]
                    rw [h_arr, ite_false_eq_true, h_get]
                    dsimp only
                    rw [refEnumAdmitted_eq, h_adm]
                    dsimp only [Bool.not]
                    rw [ite_false_eq_true, h_idx]
                    dsimp only
                    rw [evalPlaceToOp_enum_live enumTyId ety sv]
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
                    cases sv with
                    | uninit =>
                      have h_rd :
                          (refRvalueHooks ts).readDiscriminant ()
                            ⟨.immediate (payloadToMiriImmediate
                              (MirTy.enum ety, SlotVal.uninit)), layout⟩
                            rlocals =
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
                    | enumVal ety' v =>
                        dsimp only
                        cases h_chk :
                            (EnumTy.beq ety ety' && Nat.beq v 0) with
                        | false =>
                          have h_rd :
                              (refRvalueHooks ts).readDiscriminant ()
                                ⟨.immediate (payloadToMiriImmediate
                                  (MirTy.enum ety, SlotVal.enumVal ety' v)),
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
                                  (MirTy.enum ety, SlotVal.enumVal ety' v)),
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
                    cases sv with
                    | uninit =>
                      have h_uninit_ub :
                          (refRvalueHooks ts).readDiscriminant ()
                            ⟨.immediate (payloadToMiriImmediate
                              (MirTy.enum ety, SlotVal.uninit)), layout⟩
                            rlocals =
                          .error (.undefinedBehavior
                            "InvalidUninitBytes(None)") rlocals := by
                        cases ety with
                        | mk id dw ds tr discrs =>
                          dsimp only at h_tr
                          subst h_tr
                          cases tagW <;> cases tagS <;> rfl
                      rw [h_uninit_ub]
                    | enumVal ety' v =>
                        dsimp only
                        cases h_chk :
                            (EnumTy.beq ety ety' &&
                              Nat.blt v ety.discriminants.length) with
                        | false =>
                          have h_rd :
                              (refRvalueHooks ts).readDiscriminant ()
                                ⟨.immediate (payloadToMiriImmediate
                                  (MirTy.enum ety, SlotVal.enumVal ety' v)),
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
                                    (MirTy.enum ety, SlotVal.enumVal ety' v)),
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
                                    (MirTy.enum ety, SlotVal.enumVal ety' v)),
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
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (m : Mutability) (rp : RefPlace)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.ref m rp)) = .error .unsupported := by
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.ref m rp)) = false := by
    cases m <;> rfl
  dsimp only [evalRefMiriRvalue]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  cases m <;> (
    dsimp only [toMiriRvalue, toMiriPlace,
      Miri.Interpreter.evalRvalueIntoPlace, refRvalueHooks,
      Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
      EStateM.pure]
    rw [h_dst]
    dsimp only
    rw [h_pty]
    dsimp only
    cases MirSemantics.getElem? rlocals rp.localId with
    | none => rfl
    | some rloc =>
      cases rloc with
      | mk _ optTy =>
        cases optTy with
        | none => rfl
        | some srcTy =>
          dsimp only
          cases refProjectTy? ts srcTy
              (List.map toMiriProjElem rp.projection) <;> rfl)

private theorem evalRefMiriRvalue_addressOf (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (m : Mutability) (rp : RefPlace)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.addressOf m rp)) = .error .unsupported := by
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.addressOf m rp)) = false := by
    cases m <;> rfl
  dsimp only [evalRefMiriRvalue]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  cases m <;> (
    dsimp only [toMiriRvalue, toMiriPlace,
      Miri.Interpreter.evalRvalueIntoPlace, refRvalueHooks,
      Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
      EStateM.pure]
    rw [h_dst]
    dsimp only
    rw [h_pty]
    dsimp only
    cases MirSemantics.getElem? rlocals rp.localId with
    | none => rfl
    | some rloc =>
      cases rloc with
      | mk _ optTy =>
        cases optTy with
        | none => rfl
        | some srcTy =>
          dsimp only
          cases refProjectTy? ts srcTy
              (List.map toMiriProjElem rp.projection) <;> rfl)

private theorem evalRefMiriRvalue_unsupported (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue .unsupported) = .error .unsupported := by
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue .unsupported) = false := rfl
  dsimp only [evalRefMiriRvalue]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  dsimp only [toMiriRvalue,
    Miri.Interpreter.evalRvalueIntoPlace, refRvalueHooks,
    Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
    EStateM.pure]
  rw [h_dst]
  dsimp only
  rw [h_pty]
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
        (match MirSemantics.getElem? bodyLocals dst.localId with
        | none => .error .unsupported
        | some localTy =>
          match projectTy? localTy dst.projection with
          | none => .error .unsupported
          | some dstTy =>
            if assignHasUnsupportedOverlap dst dstTy rv then
              .error .unsupported
            else
              match rv with
              | .aggregateTuple ops =>
                writeAggregateTuple bodyLocals slots dst dstTy ops
              | _ =>
                match evalRvalue bodyLocals slots dstTy rv with
                | .error k => .error k
                | .ok (val, localsAfterRval) =>
                  writePlace localsAfterRval dst dstTy val) := by
  let ⟨h_id, h_proj⟩ := decodePlace_proj_inv h_pl
  have h_tp : toMiriPlace rdst =
      ⟨dst.localId, Array.mk (rdst.projection.map toMiriProjElem)⟩ := by
    rw [← h_id]
    rfl
  rw [h_tp]
  cases h_ty : MirSemantics.getElem? bodyLocals dst.localId with
  | none =>
    dsimp only [evalRefMiriRvalue]
    rw [getElem?_zipRefLocals_none_left h_ty]
    rfl
  | some localTy =>
    let ⟨dstSlot, h_sl⟩ := getElem?_some_of_length_eq h_len.symm h_ty
    have h_dst := getElem?_zipRefLocals_some h_ty h_sl
    have h_rpt := refProjectTy?_eq h_proj localTy
    dsimp only
    cases h_pt : projectTy? localTy dst.projection with
    | none =>
      rw [h_pt] at h_rpt
      dsimp only [evalRefMiriRvalue]
      rw [h_dst]
      dsimp only
      rw [h_rpt]
      rfl
    | some dstTy =>
      rw [h_pt] at h_rpt
      dsimp only
      have h_ov_eq := refAssignHasUnsupportedOverlap_eq dstTy h_pl h_dec
      rw [h_tp] at h_ov_eq
      cases h_ov : assignHasUnsupportedOverlap dst dstTy rv with
      | true =>
        rw [h_ov] at h_ov_eq
        dsimp only [evalRefMiriRvalue]
        rw [h_dst]
        dsimp only
        rw [h_rpt]
        dsimp only
        rw [h_ov_eq]
        rfl
      | false =>
        rw [h_ov] at h_ov_eq
        rw [ite_eq_right (fun h => Bool.noConfusion h)]
        cases rrv with
        | use rop =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_op : decodeOperand ts rop with
          | none => rw [h_op] at h_dec; cases h_dec
          | some op =>
            rw [h_op] at h_dec
            injection h_dec with h_eq
            subst h_eq
            rw [evalRefMiriRvalue_use ts _ dst.localId _ dstSlot localTy dstTy
              rop h_dst h_rpt h_ov_eq]
            dsimp only [evalRvalue]
            rw [evalRefMiriOperandToSlot_eq h_op]
            cases evalOperandToSlot bodyLocals slots op with
            | error _ => rfl
            | ok res =>
              let ⟨srcTy, sv, slots₁⟩ := res
              dsimp only [mapSlotRes]
              cases MirTy.beq srcTy dstTy
              · rfl
              · cases sv.toVal? with
                | none => rfl
                | some v => exact writeRefPlace_eq h_ty h_proj
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
              rw [evalRefMiriRvalue_binaryOp ts _ dst.localId _ dstSlot localTy
                dstTy op lhs rhs h_dst h_rpt]
              dsimp only [evalRvalue]
              rw [evalRefMiriOperandToSlot_eq h_l]
              dsimp only [evalPrimitiveOperand]
              cases evalOperandToSlot bodyLocals slots l' with
              | error _ => rfl
              | ok resL =>
                let ⟨lTy, lSv, slots₁⟩ := resL
                dsimp only [mapSlotRes]
                rw [readRefPrimitiveSlot_eq]
                cases isPrimitiveReadableTy lTy
                · rfl
                · dsimp only [Bool.not, ite_false_eq_true]
                  cases lSv.toVal? with
                  | none => rfl
                  | some lVal =>
                    dsimp only
                    rw [evalRefMiriOperandToSlot_eq h_r]
                    cases evalOperandToSlot bodyLocals slots₁ r' with
                    | error _ => rfl
                    | ok resR =>
                      let ⟨rTy, rSv, slots₂⟩ := resR
                      dsimp only [mapSlotRes]
                      rw [readRefPrimitiveSlot_eq]
                      cases isPrimitiveReadableTy rTy
                      · rfl
                      · dsimp only [Bool.not, ite_false_eq_true]
                        cases rSv.toVal? with
                        | none => rfl
                        | some rVal =>
                          dsimp only
                          rw [evalRefBinOp_eq]
                          cases evalBinOp op lVal rVal with
                          | error _ => rfl
                          | ok v => exact writeRefPlace_eq h_ty h_proj
        | unaryOp op rop =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_op : decodeOperand ts rop with
          | none => rw [h_op] at h_dec; cases h_dec
          | some op' =>
            rw [h_op] at h_dec
            injection h_dec with h_eq
            subst h_eq
            rw [evalRefMiriRvalue_unaryOp ts _ dst.localId _ dstSlot localTy
              dstTy op rop h_dst h_rpt]
            dsimp only [evalRvalue, evalPrimitiveOperand]
            rw [evalRefMiriOperandToSlot_eq h_op]
            cases evalOperandToSlot bodyLocals slots op' with
            | error _ => rfl
            | ok res =>
              let ⟨ty, sv, slots₁⟩ := res
              dsimp only [mapSlotRes]
              rw [readRefPrimitiveSlot_eq]
              cases isPrimitiveReadableTy ty
              · rfl
              · dsimp only [Bool.not, ite_false_eq_true]
                cases sv.toVal? with
                | none => rfl
                | some v =>
                  dsimp only
                  rw [evalRefUnOp_eq]
                  cases evalUnOp op v with
                  | error _ => rfl
                  | ok u => exact writeRefPlace_eq h_ty h_proj
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
            rw [evalRefMiriRvalue_discriminant_eq _ dst.localId _ dstSlot
              localTy dstTy rp h_dst h_rpt h_zip_tys]
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
                        | live sv =>
                          cases sv with
                          | uninit =>
                            cases MirSemantics.getElem? ety.discriminants 0 with
                            | none => rfl
                            | some disc => exact writeRefPlace_eq h_ty h_proj
                          | enumVal ety' v =>
                            dsimp only
                            cases (EnumTy.beq ety ety' && Nat.beq v 0)
                            · rfl
                            · cases MirSemantics.getElem? ety.discriminants 0
                              with
                              | none => rfl
                              | some disc => exact writeRefPlace_eq h_ty h_proj
                          | _ => rfl
                      | scalar tagW tagS =>
                        cases slot with
                        | dead => rfl
                        | live sv =>
                          cases sv with
                          | uninit => rfl
                          | enumVal ety' v =>
                            dsimp only
                            cases (EnumTy.beq ety ety' &&
                                Nat.blt v ety.discriminants.length)
                            · rfl
                            · cases MirSemantics.getElem? ety.discriminants v
                              with
                              | none => rfl
                              | some disc => exact writeRefPlace_eq h_ty h_proj
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
            exact evalRefMiriRvalue_ref ts _ dst.localId _ dstSlot localTy dstTy
              m rp h_dst h_rpt
        | addressOf m rp =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h_dec; cases h_dec
          | some _ =>
            rw [h_p] at h_dec
            injection h_dec with h_eq
            subst h_eq
            exact evalRefMiriRvalue_addressOf ts _ dst.localId _ dstSlot localTy
              dstTy m rp h_dst h_rpt
        | aggregateTuple rops =>
          dsimp only [decodeRvalue, optMap] at h_dec
          cases h_ops : mapOption (decodeOperand ts) rops with
          | none => rw [h_ops] at h_dec; cases h_dec
          | some ops =>
            rw [h_ops] at h_dec
            injection h_dec with h_eq
            subst h_eq
            exact evalRefMiriRvalue_aggregateTuple_eq h_ty h_proj h_dst h_rpt
              h_ops h_ov_eq
        | cast kind rop tyId =>
          dsimp only [decodeRvalue, optMap2] at h_dec
          cases h_op : decodeOperand ts rop with
          | none => rw [h_op] at h_dec; cases h_dec
          | some op' =>
            cases h_ct : MirSemantics.getElem? ts tyId with
            | none => rw [h_op, h_ct] at h_dec; cases h_dec
            | some castTy =>
              rw [h_op, h_ct] at h_dec
              injection h_dec with h_eq
              subst h_eq
              rw [evalRefMiriRvalue_cast ts _ dst.localId _ dstSlot localTy
                dstTy kind rop tyId h_dst h_rpt]
              dsimp only [evalRvalue, evalPrimitiveOperand]
              rw [evalRefMiriOperandToSlot_eq h_op]
              cases evalOperandToSlot bodyLocals slots op' with
              | error _ => rfl
              | ok res =>
                let ⟨srcTy, sv, slots₁⟩ := res
                dsimp only [mapSlotRes]
                rw [readRefPrimitiveSlot_eq]
                cases isPrimitiveReadableTy srcTy
                · rfl
                · dsimp only [Bool.not, ite_false_eq_true]
                  cases sv.toVal? with
                  | none => rfl
                  | some v =>
                    dsimp only
                    cases kind with
                    | unsupported => rfl
                    | intToInt =>
                      dsimp only
                      rw [h_ct]
                      dsimp only
                      cases MirTy.beq castTy dstTy
                      · rfl
                      · dsimp only [Bool.not, ite_false_eq_true]
                        rw [evalRefMiriIntToIntCast_eq]
                        cases evalIntToIntCast v castTy with
                        | error _ => rfl
                        | ok res₂ => exact writeRefPlace_eq h_ty h_proj
        | unsupported =>
          injection h_dec with h_eq
          subst h_eq
          exact evalRefMiriRvalue_unsupported ts _ dst.localId _ dstSlot localTy
            dstTy h_dst h_rpt

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
  Miri.Interpreter.StepState SlotVal Miri.Interpreter.LocalLayout Unit
    RefStepMachine

private abbrev RefMiriFrame :=
  Miri.Interpreter.Frame SlotVal Miri.Interpreter.LocalLayout Unit

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
        cases MirSemantics.getElem? body.locals dst.localId with
        | none => rfl
        | some localTy =>
          dsimp only
          cases projectTy? localTy dst.projection with
          | none => rfl
          | some dstTy =>
            dsimp only
            cases assignHasUnsupportedOverlap dst dstTy rv with
            | true => rfl
            | false =>
              rw [ite_eq_right (fun h => Bool.noConfusion h)]
              rw [ite_eq_right (fun h => Bool.noConfusion h)]
              cases rv with
              | aggregateTuple ops =>
                dsimp only
                cases writeAggregateTuple body.locals f.locals dst dstTy ops <;>
                  rfl
              | use _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _
              | ref _ _ | addressOf _ _ | cast _ _ _ | unsupported =>
                cases evalRvalue body.locals f.locals dstTy _ with
                | error _ => rfl
                | ok res =>
                  cases res with
                  | mk val localsAfterRval =>
                    dsimp only
                    cases writePlace localsAfterRval dst dstTy val <;> rfl
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
          | none =>
            match Miri.Interpreter.Step.step
                (refStepHooksFor ts callerMem) () st' with
            | (st'', .ok true) =>
              match st''.machine.terminal with
              | some res => res
              | none => .fault .unsupported
            | (_, .error (.undefinedBehavior _)) => .fault .undefined
            | (_, _) => .fault .unsupported
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

/-- Caller frame beneath the entry frame in `mkRefTermStepState`. -/
private noncomputable def refCallerMiriFrame : RefMiriFrame :=
  mkSingleLocalMiriFrame .dead false

/-- Reference state after the entry frame is popped, with terminal outcome
`terminal`. -/
private noncomputable def refPoppedState (rframe : RefFrameState)
    (terminal : Option (StepResult RefState TerminalOut)) : RefStepState :=
  { stack := ⟨Array.mk [refCallerMiriFrame]⟩
    machine := { locals := rframe.locals, terminal := terminal } }

private noncomputable def expectedReturnEval (rframe : RefFrameState)
    (callerMem : CallerMemory) :
    Option RefLocalState →
      Miri.Interpreter.StepResult RefStepState Unit
  | some ⟨.live sv, some _⟩ =>
    match sv.toVal? with
    | some retVal =>
      (refPoppedState rframe (some (.done (.returned ⟨retVal, callerMem⟩))),
        .ok ())
    | none =>
      (refPoppedState rframe none,
        .error (.undefinedBehavior "uninit return place"))
  | some ⟨.dead, some _⟩ =>
    (refPoppedState rframe none,
      .error (.undefinedBehavior "dead return place"))
  | _ =>
    (refPoppedState rframe none,
      .error (.unsupported "missing return place"))

private theorem evalTerminator_return_ref
    (hooks : Miri.Interpreter.TerminatorHooks SlotVal
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
    (h_cont : frPop.returnContinuation = .goto (some 0) .Continue) :
    Miri.Interpreter.ControlFlow.evalTerminator hooks ()
      (toMiriTerminatorForDispatch .return_) st₀ =
      Except.casesOn
        (motive := fun _ => Miri.Interpreter.StepResult RefStepState Unit) out
        (fun e => (st₁, .error e))
        (fun _ => Miri.Interpreter.ControlFlow.returnToBlock (some 0) st₁) := by
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
        rw [h_cont]

private theorem evalRefTerminator_return_false (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = false) :
    evalRefTerminator ts rbb rframe callerMem =
      match MirSemantics.getElem? rframe.locals 0 with
      | some ⟨.live sv, some _⟩ =>
        match sv.toVal? with
        | some retVal => .done (.returned ⟨retVal, callerMem⟩)
        | none => .fault .undefined
      | some ⟨.dead, some _⟩ => .fault .undefined
      | _ => .fault .unsupported := by
  have h_case : ∀ (opt : Option RefLocalState),
      MirSemantics.getElem? rframe.locals 0 = opt →
      evalRefTerminator ts rbb rframe callerMem =
        match opt with
        | some ⟨.live sv, some _⟩ =>
          match sv.toVal? with
          | some retVal => .done (.returned ⟨retVal, callerMem⟩)
          | none => .fault .undefined
        | some ⟨.dead, some _⟩ => .fault .undefined
        | _ => .fault .unsupported := by
    intro opt h_get
    rw [evalRefTerminator_eq_of_term, h_rt, h_cl]
    let st₀ := mkRefTermStepState rframe.locals
      (toMiriTerminatorForDispatch .return_) false
    let stPop : RefStepState := refPoppedState rframe none
    let blk : Miri.MIR.BasicBlock :=
      { refDummyMirBlock false with
        terminator := toMiriTerminatorForDispatch .return_ }
    let fr : RefMiriFrame :=
      { mkSingleLocalMiriFrame .dead false with
        body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
        returnContinuation := .goto (some 0) .Continue
        location := .mir ⟨0, 0⟩ }
    have h_cf : st₀.stack.currentFrame? = some fr := rfl
    have h_loc : fr.location = .mir ⟨0, 0⟩ := rfl
    have h_bb : fr.body.basicBlocks[0]? = some blk := rfl
    have h_pf :
        (refTerminatorHooksFor ts callerMem).toControlHooks.popFrame () st₀ =
          (stPop, .ok fr) := rfl
    have h_cp_eq :
        (refTerminatorHooksFor ts callerMem).toControlHooks.copyReturn () ()
          fr.returnPlace stPop =
          expectedReturnEval rframe callerMem opt := by
      dsimp only [refTerminatorHooksFor, refControlHooksFor, stPop,
        refPoppedState]
      rw [h_get]
      cases opt with
      | none => rfl
      | some rloc =>
        cases rloc with
        | mk slot optTy =>
          cases slot with
          | dead => cases optTy <;> rfl
          | live sv =>
            cases optTy with
            | none => rfl
            | some _ =>
              dsimp only [expectedReturnEval]
              cases sv.toVal? <;> rfl
    have h_cl_eq :
        (refTerminatorHooksFor ts callerMem).toControlHooks.cleanupFrame ()
          false fr (expectedReturnEval rframe callerMem opt).1 =
          ((expectedReturnEval rframe callerMem opt).1, .ok .normal) := rfl
    have h_eval := evalTerminator_return_ref
      (refTerminatorHooksFor ts callerMem) st₀ stPop
      (expectedReturnEval rframe callerMem opt).1 fr fr blk
      (expectedReturnEval rframe callerMem opt).2
      h_cf h_loc h_bb rfl rfl h_pf h_cp_eq h_cl_eq rfl
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
          | none =>
            match Miri.Interpreter.Step.step
                (refStepHooksFor ts callerMem) () st' with
            | (st'', .ok true) =>
              match st''.machine.terminal with
              | some res => res
              | none => .fault .unsupported
            | (_, .error (.undefinedBehavior _)) => .fault .undefined
            | (_, _) => .fault .unsupported
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
        | live sv =>
          cases optTy with
          | none => rfl
          | some _ =>
            dsimp only [expectedReturnEval]
            cases sv.toVal? <;> rfl
  exact h_case _ rfl

private theorem evalRefTerminator_return_true (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = true) :
    evalRefTerminator ts rbb rframe callerMem = .fault .unsupported := by
  unfold evalRefTerminator
  rw [h_rt, h_cl]
  rfl

/-- `UnwindResume` unwinds out of the entry frame from a cleanup block and is
rejected outside one. -/
private theorem evalRefTerminator_unwindResume (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .unwindResume) :
    evalRefTerminator ts rbb rframe callerMem =
      if rbb.cleanup then .done (.unwound callerMem)
      else .fault .unsupported := by
  unfold evalRefTerminator
  rw [h_rt]
  cases rbb.cleanup <;> rfl

/-- The reference check of a translated assert message agrees with
`isOperandFreeAssertKind`. -/
private theorem refIsOperandFreeAssertKind_eq (msg : AssertKind) :
    refIsOperandFreeAssertKind (toMiriAssertKind msg) =
      isOperandFreeAssertKind msg := by
  cases msg with
  | overflow op => cases op <;> rfl
  | _ => rfl

/-- `Assert` lockstep on the reference side: the condition is evaluated like a
`SwitchInt` discriminant; a passing assertion jumps to its target, and a
failing one checks the message and then follows the unwind action. -/
private theorem evalRefTerminator_assert (ts : List MirTy)
    (rbb : RefBasicBlock) (rframe : RefFrameState) (callerMem : CallerMemory)
    (rcond : RefOperand) (expected : Bool) (msg : AssertKind)
    (target : BasicBlockId) (unwind : UnwindAction)
    (h_rt : rbb.terminator = .assert rcond expected msg target unwind) :
    evalRefTerminator ts rbb rframe callerMem =
      match evalRefMiriOperandToSlot ts rframe.locals
          (toMiriOperand rcond) with
      | .error k => .fault k
      | .ok (ty, sv, rlocalsAfterCond) =>
        match readRefPrimitiveSlot ty sv with
        | .error k => .fault k
        | .ok condVal =>
          match condVal with
          | .bool b =>
            if expected == b then
              .step {
                frames := [{
                  rframe with
                  blockIdx := target
                  stmtIdx := 0
                  locals := rlocalsAfterCond
                }]
                callerMem
              }
            else if !isOperandFreeAssertKind msg then
              .fault .unsupported
            else
              UnwindAction.casesOn
                (motive := fun _ => StepResult RefState TerminalOut) unwind
                (.done (.unwound callerMem))
                (.fault .undefined)
                (.fault .unsupported)
                (fun block =>
                  .step {
                    frames := [{
                      rframe with
                      blockIdx := block
                      stmtIdx := 0
                      locals := rlocalsAfterCond
                    }]
                    callerMem
                  })
          | _ => .fault .unsupported := by
  rw [evalRefTerminator_eq_of_term, h_rt]
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
    toMiriTerminatorForDispatch, refTerminatorHooksFor,
    mkRefTermStepState, Id.run, Bind.bind, Pure.pure]
  cases evalRefMiriOperandToSlot ts rframe.locals (toMiriOperand rcond) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨ty, sv, rlocalsAfterCond⟩ := res
    dsimp only
    cases readRefPrimitiveSlot ty sv with
    | error k => cases k <;> rfl
    | ok condVal =>
      dsimp only
      cases condVal with
      | bool b =>
        dsimp only
        rw [refIsOperandFreeAssertKind_eq]
        cases (expected == b)
        · cases isOperandFreeAssertKind msg
          · rfl
          · cases unwind <;> rfl
        · rfl
      | scalar _ | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => rfl

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
    (rlocals : List RefLocalState)
    (stk : Miri.Interpreter.Stack SlotVal Miri.Interpreter.LocalLayout Unit)
    (sv : ScalarVal) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
        ({ stack := stk
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
        (some ({ stack := stk
                 machine := { locals := rlocals, terminal := none } },
               .error (faultToStepError .unsupported)),
         { stack := stk
           machine := { locals := rlocals, terminal := none } },
         otherwise)
      | .ok target =>
        (none,
         { stack := stk
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
    (rlocals : List RefLocalState)
    (stk : Miri.Interpreter.Stack SlotVal Miri.Interpreter.LocalLayout Unit)
    (b : Bool) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
        ({ stack := stk
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
        (some ({ stack := stk
                 machine := { locals := rlocals, terminal := none } },
               .error (faultToStepError k)),
         { stack := stk
           machine := { locals := rlocals, terminal := none } },
         otherwise)
      | .ok target =>
        (none,
         { stack := stk
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
      | .ok (ty, sv, rlocalsAfterDiscr) =>
        match readRefPrimitiveSlot ty sv with
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
    returnContinuation := .goto (some 0) .Continue
    location := .mir ⟨0, 0⟩
  }
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
    toMiriTerminatorForDispatch, refTerminatorHooksFor,
    mkRefTermStepState, Id.run, Bind.bind, Pure.pure]
  cases evalRefMiriOperandToSlot ts rframe.locals (toMiriOperand rdiscr) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨ty, sv₀, rlocalsAfterDiscr⟩ := res
    dsimp only
    cases readRefPrimitiveSlot ty sv₀ with
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
            ⟨Array.mk [mkSingleLocalMiriFrame .dead false, mframe]⟩ sv
            targets.otherwise targets.branches]
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
            ⟨Array.mk [mkSingleLocalMiriFrame .dead false, mframe]⟩ b
            targets.otherwise targets.branches]
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
        let ⟨ty, sv₀, localsAfterDiscr⟩ := res
        dsimp only [mapSlotRes]
        rw [readRefPrimitiveSlot_eq]
        cases isPrimitiveReadableTy ty
        · rfl
        · dsimp only [Bool.not, ite_false_eq_true]
          cases sv₀.toVal? with
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
        | live sv₀ =>
          dsimp only
          cases sv₀.toVal? <;> rfl
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
    rw [evalRefTerminator_unwindResume _ _ _ _ h_rt]
    unfold evalTerminator
    rw [← h_eq, h_cleanup]
    cases bb.cleanup <;> rfl
  | assert rcond exp msg t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap] at h_term
    cases h_c : decodeOperand ts rcond with
    | none => rw [h_c] at h_term; cases h_term
    | some c =>
      rw [h_c] at h_term
      injection h_term with h_eq
      rw [evalRefTerminator_assert _ _ _ _ _ _ _ _ _ h_rt]
      unfold evalTerminator
      rw [← h_eq]
      dsimp only [liftFrame, evalPrimitiveOperand]
      rw [evalRefMiriOperandToSlot_eq h_c]
      cases evalOperandToSlot body.locals f.locals c with
      | error _ => rfl
      | ok res =>
        let ⟨ty, sv₀, localsAfterCond⟩ := res
        dsimp only [mapSlotRes]
        rw [readRefPrimitiveSlot_eq]
        cases isPrimitiveReadableTy ty
        · rfl
        · dsimp only [Bool.not, ite_false_eq_true]
          cases sv₀.toVal? with
          | none => rfl
          | some condVal =>
            dsimp only
            cases condVal with
            | bool b =>
              dsimp only
              cases (exp == b)
              · cases isOperandFreeAssertKind msg
                · rfl
                · cases u <;> rfl
              · rfl
            | scalar _ | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ => rfl
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
    cases h_ty : MirSemantics.getElem? body.locals dst.localId with
    | none => rw [h_ty] at h_step; cases h_step
    | some localTy =>
      rw [h_ty] at h_step
      dsimp only at h_step
      cases h_pt : projectTy? localTy dst.projection with
      | none => rw [h_pt] at h_step; cases h_step
      | some dstTy =>
        rw [h_pt] at h_step
        dsimp only at h_step
        cases h_ov : assignHasUnsupportedOverlap dst dstTy rvalue <;>
            rw [h_ov] at h_step
        · rw [ite_eq_right (fun h => Bool.noConfusion h)] at h_step
          cases rvalue with
          | aggregateTuple ops =>
            dsimp only at h_step
            cases h_wa : writeAggregateTuple body.locals f.locals dst dstTy
                ops with
            | error _ => rw [h_wa] at h_step; cases h_step
            | ok localsAfterWrite =>
              rw [h_wa] at h_step
              injection h_step with h_eq
              have h_len₁ := (writeAggregateTuple_length h_wa).trans h_len
              refine ⟨{ f with
                  stmtIdx := f.stmtIdx + 1, locals := localsAfterWrite },
                h_eq.symm, rfl, h_len₁⟩
          | use _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _
          | ref _ _ | addressOf _ _ | cast _ _ _ | unsupported =>
            cases h_rv : evalRvalue body.locals f.locals dstTy _ with
            | error _ => rw [h_rv] at h_step; cases h_step
            | ok res =>
              rw [h_rv] at h_step
              cases res with | mk val localsAfterRval =>
              dsimp only at h_step
              cases h_wr : writePlace localsAfterRval dst dstTy val with
              | error _ => rw [h_wr] at h_step; cases h_step
              | ok localsAfterWrite =>
                rw [h_wr] at h_step
                injection h_step with h_eq
                have h_len₁ := (evalRvalue_length h_rv).trans h_len
                have h_len₂ := (writePlace_length h_wr).trans h_len₁
                refine ⟨{ f with
                    stmtIdx := f.stmtIdx + 1, locals := localsAfterWrite },
                  h_eq.symm, rfl, h_len₂⟩
        · cases h_step
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
        | live sv₀ =>
          dsimp only at h_step
          cases h_v : sv₀.toVal? <;> rw [h_v] at h_step <;> cases h_step
    · cases h_step
  | unreachable | call _ _ _ _ _ | unsupported =>
    cases h_step
  | unwindResume =>
    dsimp only [evalTerminator] at h_step
    cases cleanup <;> cases h_step
  | assert cond expected msg target unwind =>
    dsimp only [evalTerminator] at h_step
    cases h_d : evalPrimitiveOperand body.locals f.locals cond with
    | error _ => rw [h_d] at h_step; cases h_step
    | ok res =>
      rw [h_d] at h_step
      cases res with | mk condVal localsAfterCond =>
      have h_len₁ := (evalPrimitiveOperand_length h_d).trans h_len
      dsimp only at h_step
      cases condVal with
      | bool b =>
        dsimp only at h_step
        cases h_e : (expected == b) <;> rw [h_e] at h_step
        · cases h_m : isOperandFreeAssertKind msg <;> rw [h_m] at h_step
          · cases h_step
          · cases unwind with
            | cleanup block =>
              injection h_step with h_eq
              refine ⟨_, h_eq.symm, rfl, h_len₁⟩
            | continue_ | unreachable | terminate => cases h_step
        · injection h_step with h_eq
          refine ⟨_, h_eq.symm, rfl, h_len₁⟩
      | scalar _ | unit | enumVal _ _ | tuple _ | ptr _ | bytes _ =>
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

/-! ## Move Deinitialization, Overflow, Enum, Tuple, Cast, and Unwind Canaries
(`D6`–`D18`) -/

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
to `.live .uninit`, and then writes `42` back into `_1`, so the subsequent
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
`liveUninitSlot .unit = .live .unit`, so subsequent `_0 = copy _1`
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

/-- A deterministic terminating run transfers to the reference machine: the
program is well-formed and has the terminal behavior `out` in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$. -/
private theorem positive_ref_of_exec {p : Program} {q : Query} {fuel : Nat}
    {out : TerminalOut}
    (h_exec : execProg p fuel q (fun o => o = out)) :
    WellFormed p q ∧ Behavior p q out ∧
      RefWellFormed (encodeProg p) q ∧ RefBehavior (encodeProg p) q out := by
  let ⟨h_wf, h_beh, _, _⟩ :=
    spec_and_behavior_of_wp_eq (wpProg_of_execProg h_exec)
  let ⟨h_rwf, h_rbeh, _⟩ := anneal_corresponds_to_miri p q h_wf
  exact ⟨h_wf, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- A deterministic faulting run transfers to the reference machine: the
program reaches the fault `expected` (and not `other`), is not well-formed,
and reaches the matching reference outcome. -/
private theorem negative_ref_of_execFault {p : Program} {q : Query}
    {fuel : Nat} {expected other : FaultKind}
    (h_ne : other ≠ expected)
    (h_exec : execFaultProg p fuel q expected) :
    ReachesResult p q (.fault expected) ∧
      ¬ ReachesResult p q (.fault other) ∧
      ¬ WellFormed p q ∧
      (∃ maxSteps,
        RefReachesOutcome (encodeProg p) q maxSteps
          (faultToRefOutcome expected)) := by
  let ⟨h_f, h_nf, h_nwf⟩ := negativeCanary_of_execFault h_ne h_exec
  exact ⟨h_f, h_nf, h_nwf,
    (reachesResult_fault_iff_refReachesOutcome p q expected).1 h_f⟩

/-- `D14` (overflowing operators, sequential moves of single tuple fields, a
tuple aggregate, a field write, and the UB of reading a moved-out field in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D14_overflow_tuple_field_moves :
    CanaryD14OverflowTupleFieldMovesClaim := by
  let ⟨a₁, a₂, a₃, a₄⟩ := positive_ref_of_exec
    (p := progOverflowTupleD14 .addWithOverflow)
    (q := { args := [usizeVal (Nat.pow 2 64 - 1), usizeVal 1] })
    (fuel := 5) (out := .returned ⟨.tuple [usizeVal 0, .bool true], ⟨[]⟩⟩) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := positive_ref_of_exec
    (p := progOverflowTupleD14 .subWithOverflow)
    (q := { args := [usizeVal 0, usizeVal 1] })
    (fuel := 5)
    (out := .returned
      ⟨.tuple [usizeVal (Nat.pow 2 64 - 1), .bool true], ⟨[]⟩⟩) rfl
  let ⟨c₁, c₂, c₃, c₄⟩ := positive_ref_of_exec
    (p := progOverflowTupleD14 .mulWithOverflow)
    (q := { args := [usizeVal (Nat.pow 2 63), usizeVal 2] })
    (fuel := 5) (out := .returned ⟨.tuple [usizeVal 0, .bool true], ⟨[]⟩⟩) rfl
  let ⟨d₁, d₂, d₃, d₄⟩ := positive_ref_of_exec
    (p := progOverflowTupleD14 .addWithOverflow)
    (q := { args := [usizeVal 30, usizeVal 12] })
    (fuel := 5)
    (out := .returned ⟨.tuple [usizeVal 42, .bool false], ⟨[]⟩⟩) rfl
  let ⟨e₁, e₂, e₃, e₄⟩ := positive_ref_of_exec
    (p := progTupleFieldWriteD14) (q := { args := [usizeVal 21] })
    (fuel := 5)
    (out := .returned ⟨.tuple [usizeVal 42, .bool true], ⟨[]⟩⟩) rfl
  let ⟨f₁, f₂, f₃, f₄⟩ := negative_ref_of_execFault
    (p := progTupleFieldUseAfterMoveD14) (q := { args := [usizeVal 21] })
    (fuel := 3) (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, c₁, c₂, c₃, c₄, d₁, d₂, d₃, d₄,
    e₁, e₂, e₃, e₄, f₁, f₂, f₃, f₄⟩

/-- `D15` (`CastKind.intToInt`: signed sign extension, cross-signedness
widening, unsigned zero extension, truncation, `bool` to integer, and the
fail-closed `u8 as bool` and `CastKind.unsupported` cases in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D15_int_to_int_cast : CanaryD15IntToIntCastClaim := by
  let ⟨a₁, a₂, a₃, a₄⟩ := positive_ref_of_exec
    (p := mkCastProg .intToInt i8Ty (.int .i64 true))
    (q := { args := [i8Val 255] }) (fuel := 2)
    (out := .returned ⟨scalarNatVal .i64 true (Nat.pow 2 64 - 1), ⟨[]⟩⟩) rfl
  let ⟨a₁', a₂', a₃', a₄'⟩ := positive_ref_of_exec
    (p := mkCastProg .intToInt i8Ty (.int .i64 false))
    (q := { args := [i8Val 255] }) (fuel := 2)
    (out := .returned ⟨scalarNatVal .i64 false (Nat.pow 2 64 - 1), ⟨[]⟩⟩) rfl
  let ⟨b₁', b₂', b₃', b₄'⟩ := positive_ref_of_exec
    (p := mkCastProg .intToInt u8Ty (.int .i64 true))
    (q := { args := [u8Val 255] }) (fuel := 2)
    (out := .returned ⟨scalarNatVal .i64 true 255, ⟨[]⟩⟩) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := positive_ref_of_exec
    (p := mkCastProg .intToInt u8Ty (.int .i64 false))
    (q := { args := [u8Val 255] }) (fuel := 2)
    (out := .returned ⟨scalarNatVal .i64 false 255, ⟨[]⟩⟩) rfl
  let ⟨c₁, c₂, c₃, c₄⟩ := positive_ref_of_exec
    (p := mkCastProg .intToInt (.int .i64 false) u8Ty)
    (q := { args := [scalarNatVal .i64 false 300] }) (fuel := 2)
    (out := .returned ⟨u8Val 44, ⟨[]⟩⟩) rfl
  let ⟨d₁, d₂, d₃, d₄⟩ := positive_ref_of_exec
    (p := mkCastProg .intToInt .bool (.int .i64 false))
    (q := { args := [.bool true] }) (fuel := 2)
    (out := .returned ⟨scalarNatVal .i64 false 1, ⟨[]⟩⟩) rfl
  let ⟨e₁', e₂', e₃', e₄'⟩ := negative_ref_of_execFault
    (p := mkCastProg .intToInt u8Ty .bool)
    (q := { args := [u8Val 1] })
    (fuel := 1) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨e₁, e₂, e₃, e₄⟩ := negative_ref_of_execFault
    (p := mkCastProg .unsupported u8Ty (.int .i64 false))
    (q := { args := [u8Val 255] })
    (fuel := 1) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, a₃, a₄, a₁', a₂', a₃', a₄', b₁', b₂', b₃', b₄',
    b₁, b₂, b₃, b₄, c₁, c₂, c₃, c₄, d₁, d₂, d₃, d₄, e₁', e₂', e₃', e₄',
    e₁, e₂, e₃, e₄⟩

/-- `D16` (`Assert`: a passing assertion jumps to its target, and a failing
assertion with `unwind continue` unwinds out of the entry function as a
well-formed `.unwound` execution in both $M_{\text{anneal}}$ and
$M_{\text{ref}}$). -/
theorem canary_D16_assert_pass_and_unwind_ok :
    CanaryD16AssertPassAndUnwindContinueClaim := by
  let ⟨a₁, a₂, a₃, a₄⟩ := positive_ref_of_exec
    (p := mkCheckedIncProg (.overflow .add) .continue_ true)
    (q := { args := [usizeVal 41] }) (fuel := 4)
    (out := .returned ⟨usizeVal 42, ⟨[]⟩⟩) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := positive_ref_of_exec
    (p := mkCheckedIncProg (.overflow .add) .continue_ true)
    (q := queryUsizeMax) (fuel := 2) (out := .unwound ⟨[]⟩) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄⟩

/-- `D17` (a failing `Assert` with `unwind unreachable` is UB, and a failing
`Assert` whose message carries operands or whose unwind action is `terminate`
is unsupported, in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D17_assert_unwind_unreachable_ub :
    CanaryD17AssertUnwindUnreachableUbClaim := by
  let ⟨a₁, a₂, a₃, a₄⟩ := negative_ref_of_execFault
    (p := mkCheckedIncProg (.overflow .add) .unreachable true)
    (q := queryUsizeMax)
    (fuel := 2) (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := negative_ref_of_execFault
    (p := mkCheckedIncProg .boundsCheck .continue_ true)
    (q := queryUsizeMax)
    (fuel := 2) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨c₁, c₂, c₃, c₄⟩ := negative_ref_of_execFault
    (p := mkCheckedIncProg (.overflow .add) .terminate true)
    (q := queryUsizeMax)
    (fuel := 2) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, c₁, c₂, c₃, c₄⟩

/-- `D18` (a failing `Assert` with `unwind cleanup` runs the cleanup block,
whose `UnwindResume` unwinds out of the entry function; `UnwindResume` outside
a cleanup block is unsupported, in both $M_{\text{anneal}}$ and
$M_{\text{ref}}$). -/
theorem canary_D18_assert_cleanup_and_resume :
    CanaryD18AssertCleanupAndUnwindResumeClaim := by
  let ⟨a₁, a₂, a₃, a₄⟩ := positive_ref_of_exec
    (p := mkCheckedIncProg (.overflow .add) (.cleanup 2) true)
    (q := queryUsizeMax) (fuel := 4) (out := .unwound ⟨[]⟩) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := negative_ref_of_execFault
    (p := mkCheckedIncProg (.overflow .add) (.cleanup 2) false)
    (q := queryUsizeMax)
    (fuel := 4) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄⟩

/-- `D19` (destination-overlapping tuple aggregates and tuple
self-copy/self-move fail closed with `.fault .unsupported` / `.blocked` in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$, while disjoint sibling-field copies
and empty `.unit` aggregates succeed). -/
theorem canary_D19_tuple_overlap_fail_closed :
    CanaryD19TupleOverlapFailClosedClaim := by
  let qPair : Query := { args := [.tuple [u32Val 10, u32Val 20]] }
  let qTriple : Query := { args := [.tuple [u32Val 1, u32Val 2, u32Val 3]] }
  let qNested : Query :=
    { args := [.tuple [.tuple [u32Val 1, u32Val 2, u32Val 3], u32Val 4]] }
  let ⟨a₁, a₂, a₃, a₄⟩ := negative_ref_of_execFault
    (p := progTupleAggregateAliasD19) (q := qPair)
    (fuel := 1) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := negative_ref_of_execFault
    (p := progTupleAggregateSelfFieldD19) (q := qNested)
    (fuel := 1) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨c₁, c₂, c₃, c₄⟩ := negative_ref_of_execFault
    (p := progTupleSelfUseD19 false) (q := qTriple)
    (fuel := 1) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨d₁, d₂, d₃, d₄⟩ := negative_ref_of_execFault
    (p := progTupleSelfUseD19 true) (q := qTriple)
    (fuel := 1) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨e₁, e₂, e₃, e₄⟩ := negative_ref_of_execFault
    (p := progTupleSubfieldSelfCopyD19) (q := qNested)
    (fuel := 1) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨f₁, f₂, f₃, f₄⟩ := positive_ref_of_exec
    (p := progTupleDisjointFieldAndUnitAggD19) (q := qPair) (fuel := 4)
    (out := .returned ⟨.tuple [u32Val 20, u32Val 20], ⟨[]⟩⟩) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, c₁, c₂, c₃, c₄, d₁, d₂, d₃, d₄,
    e₁, e₂, e₃, e₄, f₁, f₂, f₃, f₄⟩

end Anneal.MirCorrespondenceProof
