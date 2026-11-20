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
theorems, and Pass 2 non-vacuity canaries (`D6`–`D27`) on top of the codec,
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
  dsimp only [evalRefPlaceOperand, refLocalLayoutForTy]
  rw [h_get]
  cases proj with
  | nil =>
    cases isMove <;>
      cases (refIsZeroSizedTy ty && !refIsTypeUninhabited ty) <;> rfl
  | cons _ _ =>
    cases (refIsZeroSizedTy ty && !refIsTypeUninhabited ty) <;> rfl

private theorem evalRefPlaceOperand_live_copy (ts : List MirTy)
    (rlocals : List RefLocalState) (localId : LocalId) (sv : SlotVal)
    (ty : MirTy)
    (h_get : MirSemantics.getElem? rlocals localId =
      some ⟨.live sv, some ty⟩) :
    evalRefPlaceOperand ts rlocals localId [] false =
      .ok (ty, sv, rlocals) := by
  dsimp only [evalRefPlaceOperand, refLocalLayoutForTy]
  rw [h_get]
  dsimp only
  cases (refIsZeroSizedTy ty && !refIsTypeUninhabited ty) <;> rfl

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
  dsimp only [evalRefPlaceOperand, refLocalLayoutForTy]
  rw [h_get, ← refLiveUninitSlot_eq ty]
  dsimp only
  cases (refIsZeroSizedTy ty && !refIsTypeUninhabited ty) <;> rfl

/-- A projected access of a live local reads the whole local through Miri,
resolves projections via `refResolveProjPath`, and reads/updates the subslot. -/
private theorem evalRefPlaceOperand_live_proj (ts : List MirTy)
    (rlocals : List RefLocalState) (localId : LocalId) (sv : SlotVal)
    (ty : MirTy) (e : Miri.MIR.ProjectionElem)
    (es : List Miri.MIR.ProjectionElem) (isMove : Bool)
    (h_get : MirSemantics.getElem? rlocals localId =
      some ⟨.live sv, some ty⟩) :
    evalRefPlaceOperand ts rlocals localId (e :: es) isMove =
      match refProjectTy? ts ty (e :: es) with
      | none => .error .unsupported
      | some pty =>
        match refResolveProjPath ts rlocals (.ty ty) (e :: es) with
        | .error k => .error k
        | .ok resolvedProj =>
          match refReadPlaceSlotPath? (.ty ty) sv resolvedProj with
          | none => .error .unsupported
          | some psv =>
            if !isMove then
              .ok (pty, psv, rlocals)
            else
              match refWritePlaceSlotPath? (.ty ty) sv resolvedProj
                  (refUninitSlotVal pty) with
              | some root' =>
                match MirSemantics.setElem? rlocals localId
                    ⟨.live root', some ty⟩ with
                | some rlocals' => .ok (pty, psv, rlocals')
                | none => .error .unsupported
              | none => .error .unsupported := by
  dsimp only [evalRefPlaceOperand, refLocalLayoutForTy]
  rw [h_get]
  dsimp only
  cases (refIsZeroSizedTy ty && !refIsTypeUninhabited ty) <;> rfl

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
            dsimp only [projectTy?, projectPlaceTy?, resolveProjPath,
              readPlaceSlotPath?, writePlaceSlotPath?, liveUninitSlot]
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
            ← h_map, refProjectTy?_eq h_proj]
          cases projectTy? localTy p.projection with
          | none => rfl
          | some pty =>
            dsimp only
            have h_res := refResolveProjPath_eq (bodyLocals := bodyLocals)
              (slots := slots) h_proj (.ty localTy)
            dsimp only [placeTyToRefPlaceTy] at h_res
            cases h_rp : resolveProjPath bodyLocals slots (.ty localTy)
                p.projection with
            | error k =>
              rw [h_rp] at h_res
              dsimp only
              rw [h_res]
              rfl
            | ok resolvedProj =>
              rw [h_rp] at h_res
              let ⟨resolvedMiriProj, h_rok, _, h_canon⟩ := h_res
              dsimp only
              rw [h_rok]
              dsimp only
              have h_rd := refReadPlaceSlotPath?_eq h_canon (.ty localTy) root
              dsimp only [placeTyToRefPlaceTy] at h_rd
              rw [h_rd]
              cases readPlaceSlotPath? (.ty localTy) root resolvedProj with
              | none => rfl
              | some psv =>
                cases isMove with
                | false => rfl
                | true =>
                  dsimp only
                  have h_wr := refWritePlaceSlotPath?_eq h_canon (.ty localTy)
                    root (uninitSlotVal pty)
                  dsimp only [placeTyToRefPlaceTy] at h_wr
                  rw [refUninitSlotVal_eq, h_wr]
                  cases writePlaceSlotPath? (.ty localTy) root resolvedProj
                      (uninitSlotVal pty) with
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

private noncomputable def writeRefPlaceCommitOpt (rlocals : List RefLocalState)
    (slot : LocalSlot) (dstId : LocalId) (localTy : MirTy)
    (optRoot' : Option SlotVal) : Except FaultKind (List RefLocalState) :=
  match optRoot' with
  | none => .error .unsupported
  | some root' =>
    let frame₀ := mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
    match Miri.Interpreter.placeWriteLocalImmediate
        EStateM.get EStateM.set (pure true)
        (fun _ _ => pure ()) (fun _ _ => pure ())
        0 refSizedLocalLayout (payloadToMiriImmediate root') frame₀ with
    | .ok () frame₁ =>
      match frame₁.getLocal 0,
          MirSemantics.setElem? rlocals dstId ⟨.live root', some localTy⟩ with
      | .ok ⟨.live (.immediate _), _⟩, some rlocals' => .ok rlocals'
      | .ok ⟨.live (.immediate _), _⟩, none => .error .unsupported
      | _, _ => .error .undefined
    | .error _ _ => .error .undefined

/-- Place-write lockstep: writing through a canonicalized destination in the
reference machine agrees with `writePlaceWithLocalTy`. -/
theorem writeRefPlace_eq {bodyLocals : List MirTy} {slots : List LocalSlot}
    {dstId : LocalId} {mps : List Miri.MIR.ProjectionElem}
    {ps : List ProjectionElem} {localTy dstTy : MirTy} {val : Val}
    (h_ty : MirSemantics.getElem? bodyLocals dstId = some localTy)
    (h_canon : CanonProjList mps ps) :
    writeRefPlace (zipRefLocals bodyLocals slots) ⟨dstId, mps, .ty dstTy⟩ val =
      mapSlotsRes bodyLocals
        (writePlaceWithLocalTy localTy slots ⟨dstId, ps⟩ dstTy val) := by
  unfold writeRefPlace writePlaceWithLocalTy
  dsimp only [RefDest.ty?]
  rw [checkRefVal_eq]
  cases checkVal val dstTy with
  | false => rfl
  | true =>
    cases h_sl : MirSemantics.getElem? slots dstId with
    | none =>
      rw [getElem?_zipRefLocals_none_right h_sl]
      rfl
    | some slot =>
      rw [getElem?_zipRefLocals_some h_ty h_sl]
      cases slot with
      | dead => rfl
      | live root =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        rw [evalPlaceToOp_sized_live]
        dsimp only
        rw [miriImmToPayload?_roundtrip]
        dsimp only
        change writeRefPlaceCommitOpt (zipRefLocals bodyLocals slots)
            (.live root) dstId localTy
            (refWritePlaceSlotPath? (.ty localTy) root mps val.toSlotVal) = _
        have h_wr := refWritePlaceSlotPath?_eq h_canon (.ty localTy) root
          val.toSlotVal
        dsimp only [placeTyToRefPlaceTy] at h_wr
        rw [h_wr]
        cases writePlaceSlotPath? (.ty localTy) root ps val.toSlotVal with
        | none => rfl
        | some root' =>
          cases h_set :
              MirSemantics.setElem? slots dstId (.live root') with
          | none =>
            dsimp only [writeRefPlaceCommitOpt]
            rw [h_set, setElem?_zipRefLocals_none h_set]
            rfl
          | some slots' =>
            dsimp only [writeRefPlaceCommitOpt]
            rw [h_set, setElem?_zipRefLocals_some h_ty h_set]
            rfl

private theorem decodeProjElem_cases_inv {ts : List MirTy}
    {re : RefProjectionElem} {e : ProjectionElem}
    (h : decodeProjElem ts re = some e) :
    match re with
    | .deref => e = .deref
    | .field idx tid => ∃ fty, MirSemantics.getElem? ts tid = some fty ∧
        e = .field idx fty
    | .downcast v => e = .downcast v
    | .index idxLocal => e = .index idxLocal
    | .constantIndex o m fe => e = .constantIndex o m fe
    | .unsupported => e = .unsupported := by
  cases re with
  | deref | downcast _ | index _ | constantIndex _ _ _ | unsupported =>
    injection h with h'; exact h'.symm
  | field idx tid =>
    dsimp only [decodeProjElem, optMap] at h
    cases h_t : MirSemantics.getElem? ts tid with
    | none => rw [h_t] at h; cases h
    | some fty =>
      rw [h_t] at h
      injection h with h'
      exact ⟨fty, h_t, h'.symm⟩

private theorem refProjElemMayAlias_eq {ts : List MirTy}
    {re₁ re₂ : RefProjectionElem} {e₁ e₂ : ProjectionElem}
    (h₁ : decodeProjElem ts re₁ = some e₁)
    (h₂ : decodeProjElem ts re₂ = some e₂) :
    refProjElemMayAlias (toMiriProjElem re₁) (toMiriProjElem re₂) =
      projElemMayAlias e₁ e₂ := by
  have hc₁ := decodeProjElem_cases_inv h₁
  have hc₂ := decodeProjElem_cases_inv h₂
  cases re₁ with
  | deref | downcast _ | index _ | unsupported =>
    dsimp only at hc₁; subst hc₁
    cases re₂ with
    | deref | downcast _ | index _ | constantIndex _ _ _ | unsupported =>
      dsimp only at hc₂; subst hc₂; rfl
    | field j tid₂ =>
      let ⟨_, _, he₂⟩ := hc₂; subst he₂; rfl
  | field i tid₁ =>
    let ⟨_, _, he₁⟩ := hc₁; subst he₁
    cases re₂ with
    | deref | downcast _ | index _ | constantIndex _ _ _ | unsupported =>
      dsimp only at hc₂; subst hc₂; rfl
    | field j tid₂ =>
      let ⟨_, _, he₂⟩ := hc₂; subst he₂; rfl
  | constantIndex o₁ m₁ fe₁ =>
    dsimp only at hc₁; subst hc₁
    cases re₂ with
    | deref | downcast _ | index _ | unsupported =>
      dsimp only at hc₂; subst hc₂; cases fe₁ <;> rfl
    | field j tid₂ =>
      let ⟨_, _, he₂⟩ := hc₂; subst he₂; cases fe₁ <;> rfl
    | constantIndex o₂ m₂ fe₂ =>
      dsimp only at hc₂; subst hc₂
      cases fe₁ <;> cases fe₂ <;> rfl

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
      have h_ea := refProjElemMayAlias_eq h_a h_b
      have h_sub := ih h_as h_bs
      have hca := decodeProjElem_cases_inv h_a
      have hcb := decodeProjElem_cases_inv h_b
      cases a with
      | downcast v₁ =>
        dsimp only at hca; subst hca
        cases b with
        | downcast v₂ =>
          dsimp only at hcb; subst hcb
          dsimp only [List.map, toMiriProjElem, refProjPrefixMayAlias,
            projPrefixMayAlias]
          rw [h_sub]
        | deref | index _ | constantIndex _ _ _ | unsupported =>
          dsimp only at hcb; subst hcb; rfl
        | field _ _ =>
          let ⟨_, _, hb⟩ := hcb; subst hb; rfl
      | deref | index _ | constantIndex _ _ _ | unsupported =>
        dsimp only at hca; subst hca
        cases b with
        | downcast _ =>
          dsimp only at hcb; subst hcb; rfl
        | deref | index _ | constantIndex _ _ _ | unsupported =>
          dsimp only at hcb; subst hcb
          dsimp only [List.map, toMiriProjElem, refProjPrefixMayAlias,
            projPrefixMayAlias]
          dsimp only [toMiriProjElem] at h_ea
          rw [h_ea, h_sub]
        | field _ _ =>
          let ⟨_, _, hb⟩ := hcb; subst hb
          dsimp only [List.map, toMiriProjElem, refProjPrefixMayAlias,
            projPrefixMayAlias]
          dsimp only [toMiriProjElem] at h_ea
          rw [h_ea, h_sub]
      | field _ _ =>
        let ⟨_, _, ha⟩ := hca; subst ha
        cases b with
        | downcast _ =>
          dsimp only at hcb; subst hcb; rfl
        | deref | index _ | constantIndex _ _ _ | unsupported =>
          dsimp only at hcb; subst hcb
          dsimp only [List.map, toMiriProjElem, refProjPrefixMayAlias,
            projPrefixMayAlias]
          dsimp only [toMiriProjElem] at h_ea
          rw [h_ea, h_sub]
        | field _ _ =>
          let ⟨_, _, hb⟩ := hcb; subst hb
          dsimp only [List.map, toMiriProjElem, refProjPrefixMayAlias,
            projPrefixMayAlias]
          dsimp only [toMiriProjElem] at h_ea
          rw [h_ea, h_sub]

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

private theorem refMoveOperandMayOverlapPlace_eq {ts : List MirTy}
    {rdst : RefPlace} {dst : Place} {rop : RefOperand} {op : Operand}
    (h_dst : decodePlace ts rdst = some dst)
    (h_op : decodeOperand ts rop = some op) :
    refMoveOperandMayOverlapPlace (toMiriPlace rdst) (toMiriOperand rop) =
      moveOperandMayOverlapPlace dst op := by
  cases rop with
  | copy rp =>
    dsimp only [decodeOperand, optMap] at h_op
    cases h_p : decodePlace ts rp with
    | none => rw [h_p] at h_op; cases h_op
    | some p =>
      rw [h_p] at h_op
      injection h_op with h_eq
      subst h_eq
      rfl
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

private theorem refAnyMoveOperandMayOverlapPlace_eq {ts : List MirTy}
    {rdst : RefPlace} {dst : Place} {rops : List RefOperand}
    {ops : List Operand}
    (h_dst : decodePlace ts rdst = some dst)
    (h_ops : mapOption (decodeOperand ts) rops = some ops) :
    refAnyMoveOperandMayOverlapPlace (toMiriPlace rdst)
        (rops.map toMiriOperand) =
      anyMoveOperandMayOverlapPlace dst ops := by
  induction rops generalizing ops with
  | nil =>
    injection h_ops with h_eq
    subst h_eq
    rfl
  | cons ro ros ih =>
    let ⟨o, os, h_o, h_os, h_eq⟩ := mapOption_cons_inv h_ops
    subst h_eq
    dsimp only [List.map, refAnyMoveOperandMayOverlapPlace,
      anyMoveOperandMayOverlapPlace]
    rw [refMoveOperandMayOverlapPlace_eq h_dst h_o, ih h_os]

private theorem refIsCompoundOverlapProtectedTy_eq (ty : MirTy) :
    refIsCompoundOverlapProtectedTy ty = isCompoundOverlapProtectedTy ty := by
  cases ty <;>
    dsimp only [refIsCompoundOverlapProtectedTy, isCompoundOverlapProtectedTy] <;>
    simp only [refIsZeroSizedTy_eq, refHasEnumPayloadFields_eq]

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
      rw [refIsCompoundOverlapProtectedTy_eq,
        refOperandMayOverlapPlace_eq h_dst h_op]
  | aggregate rkind rops =>
    dsimp only [decodeRvalue, optMap2] at h_rv
    cases h_k : decodeAggregateKind ts rkind with
    | none => rw [h_k] at h_rv; cases h_rv
    | some kind =>
      cases h_ops : mapOption (decodeOperand ts) rops with
      | none => rw [h_k, h_ops] at h_rv; cases h_rv
      | some ops =>
        rw [h_k, h_ops] at h_rv
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
  | repeat_ rop count =>
    dsimp only [decodeRvalue, optMap] at h_rv
    cases h_op : decodeOperand ts rop with
    | none => rw [h_op] at h_rv; cases h_rv
    | some op =>
      rw [h_op] at h_rv
      injection h_rv with h_eq
      subst h_eq
      dsimp only [toMiriRvalue, refAssignHasUnsupportedOverlap,
        assignHasUnsupportedOverlap]
      exact refOperandMayOverlapPlace_eq h_dst h_op
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

private theorem evalRefMiriRvalue_resolve_err (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (mirRv : Miri.MIR.Rvalue) (k : FaultKind)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_no_ov : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      mirRv = false)
    (h_err : refResolveProjPath ts rlocals (.ty localTy) proj = .error k) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩ mirRv = .error k := by
  dsimp only [evalRefMiriRvalue, Array.toList]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no_ov]
  simp only [Bool.false_eq_true, ite_false]
  dsimp only [Miri.Interpreter.evalRvalueIntoPlace, Miri.Interpreter.runRvalue,
    Bind.bind, EStateM.bind, refRvalueHooks, Array.toList]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_err]
  cases k <;> rfl

private theorem evalRefMiriRvalue_use (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj resolvedMiriProj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (rop : RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_no_ov : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.use rop)) = false)
    (h_res : refResolveProjPath ts rlocals (.ty localTy) proj =
      .ok resolvedMiriProj) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.use rop)) =
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
      | .error k => .error k
      | .ok (srcTy, sv, rlocals₁) =>
        if !(MirTy.beq srcTy dstTy) then
          .error .unsupported
        else
          match sv.toVal? with
          | some v =>
            writeRefPlace rlocals₁ ⟨dstId, resolvedMiriProj, .ty dstTy⟩ v
          | none => .error .undefined := by
  dsimp only [evalRefMiriRvalue, Array.toList]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no_ov]
  simp only [Bool.false_eq_true, ite_false]
  dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
    Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
    Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
    EStateM.pure, Array.toList, RefDest.ty?]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_res]
  simp only [Bool.false_eq_true, ite_false]
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨srcTy, sv, rlocals₁⟩ := res
    dsimp only [RefDest.ty?]
    rw [miriImmToPayload?_roundtrip]
    dsimp only
    cases MirTy.beq srcTy dstTy with
    | false => rfl
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases sv.toVal? with
      | none => rfl
      | some v =>
        dsimp only
        cases writeRefPlace rlocals₁ ⟨dstId, resolvedMiriProj, .ty dstTy⟩ v with
        | error k => cases k <;> rfl
        | ok _ => rfl

private theorem evalRefMiriRvalue_binaryOp (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj resolvedMiriProj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (op : BinOp) (lhs rhs : RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_res : refResolveProjPath ts rlocals (.ty localTy) proj =
      .ok resolvedMiriProj) :
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
              | .ok v =>
                writeRefPlace rlocals₂ ⟨dstId, resolvedMiriProj, .ty dstTy⟩
                  v := by
  let rhsStep : EStateM.Result Miri.Interpreter.StepError RefRvalueState Unit :=
    match evalRefMiriOperandToSlot ts rlocals (toMiriOperand lhs) with
    | .error k => .error (faultToStepError k) ⟨rlocals, true, none⟩
    | .ok (lTy, lSv, rlocals₁) =>
      match readRefPrimitiveSlot lTy lSv with
      | .error k => .error (faultToStepError k) ⟨rlocals₁, true, none⟩
      | .ok lVal =>
        match evalRefMiriOperandToSlot ts rlocals₁ (toMiriOperand rhs) with
        | .error k => .error (faultToStepError k) ⟨rlocals₁, true, none⟩
        | .ok (rTy, rSv, rlocals₂) =>
          match readRefPrimitiveSlot rTy rSv with
          | .error k => .error (faultToStepError k) ⟨rlocals₂, true, none⟩
          | .ok rVal =>
            match evalRefBinOp op lVal rVal with
            | .error k =>
              .error (faultToStepError k) ⟨rlocals₂, true, none⟩
            | .ok v =>
              match writeRefPlace rlocals₂
                  ⟨dstId, resolvedMiriProj, .ty dstTy⟩ v with
              | .error k =>
                .error (faultToStepError k) ⟨rlocals₂, true, none⟩
              | .ok locals' => .ok () ⟨locals', true, none⟩
  have h_step :
      Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.binaryOp op lhs rhs)) ⟨dstId, Array.mk proj⟩
          ⟨rlocals, false, none⟩ = rhsStep := by
    dsimp only [rhsStep, toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
      Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
      evalRefBinOp, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
      Array.toList]
    rw [h_dst]
    dsimp only
    rw [h_pty]
    dsimp only
    rw [h_res]
    simp only [Bool.false_eq_true, ite_false]
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
            rw [miriImmToPayload?_roundtrip, miriImmToPayload?_roundtrip]
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
  dsimp only [evalRefMiriRvalue, Array.toList]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  simp only [Bool.false_eq_true, ite_false]
  have h_run :
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.binaryOp op lhs rhs)) ⟨dstId, Array.mk proj⟩)
        ⟨rlocals, false, none⟩ =
      Miri.Interpreter.runRvalue (fun _ => rhsStep) ⟨rlocals, false, none⟩ := by
    dsimp only [Miri.Interpreter.runRvalue]
    exact h_step ▸ rfl
  refine Eq.trans (congrArg
    (fun p : RefRvalueState × Except Miri.Interpreter.StepError Unit =>
      match p with
      | (st', .ok ()) => Except.ok st'.locals
      | (_, .error (.undefinedBehavior _))
      | (_, .error (.stack (.localExpectedLive _))) =>
        Except.error FaultKind.undefined
      | _ => Except.error FaultKind.unsupported) h_run) ?_
  dsimp only [Miri.Interpreter.runRvalue, rhsStep]
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
            cases writeRefPlace rlocals₂ ⟨dstId, resolvedMiriProj, .ty dstTy⟩
                v with
            | error k => cases k <;> rfl
            | ok _ => rfl

private theorem evalRefMiriRvalue_unaryOp (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj resolvedMiriProj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (op : UnOp) (rop : RefOperand)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_res : refResolveProjPath ts rlocals (.ty localTy) proj =
      .ok resolvedMiriProj) :
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
          | .ok u =>
            writeRefPlace rlocals₁ ⟨dstId, resolvedMiriProj, .ty dstTy⟩ u := by
  let rhsStep : EStateM.Result Miri.Interpreter.StepError RefRvalueState Unit :=
    match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
    | .error k => .error (faultToStepError k) ⟨rlocals, true, none⟩
    | .ok (ty, sv, rlocals₁) =>
      match readRefPrimitiveSlot ty sv with
      | .error k => .error (faultToStepError k) ⟨rlocals₁, true, none⟩
      | .ok v =>
        match evalRefUnOp op v with
        | .error k => .error (faultToStepError k) ⟨rlocals₁, true, none⟩
        | .ok u =>
          match writeRefPlace rlocals₁
              ⟨dstId, resolvedMiriProj, .ty dstTy⟩ u with
          | .error k => .error (faultToStepError k) ⟨rlocals₁, true, none⟩
          | .ok locals' => .ok () ⟨locals', true, none⟩
  have h_step :
      Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.unaryOp op rop)) ⟨dstId, Array.mk proj⟩
          ⟨rlocals, false, none⟩ = rhsStep := by
    dsimp only [rhsStep, toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
      Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
      evalRefUnOp, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
      Array.toList]
    rw [h_dst]
    dsimp only
    rw [h_pty]
    dsimp only
    rw [h_res]
    simp only [Bool.false_eq_true, ite_false]
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
  dsimp only [evalRefMiriRvalue, Array.toList]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  simp only [Bool.false_eq_true, ite_false]
  have h_run :
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.unaryOp op rop)) ⟨dstId, Array.mk proj⟩)
        ⟨rlocals, false, none⟩ =
      Miri.Interpreter.runRvalue (fun _ => rhsStep) ⟨rlocals, false, none⟩ := by
    dsimp only [Miri.Interpreter.runRvalue]
    exact h_step ▸ rfl
  refine Eq.trans (congrArg
    (fun p : RefRvalueState × Except Miri.Interpreter.StepError Unit =>
      match p with
      | (st', .ok ()) => Except.ok st'.locals
      | (_, .error (.undefinedBehavior _))
      | (_, .error (.stack (.localExpectedLive _))) =>
        Except.error FaultKind.undefined
      | _ => Except.error FaultKind.unsupported) h_run) ?_
  dsimp only [Miri.Interpreter.runRvalue, rhsStep]
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
        cases writeRefPlace rlocals₁ ⟨dstId, resolvedMiriProj, .ty dstTy⟩ u with
        | error k => cases k <;> rfl
        | ok _ => rfl

private theorem uint64_ofNat_beq_zero_of_lt {n : Nat}
    (h_lt : n < Nat.pow 2 64) :
    (UInt64.ofNat n == (0 : UInt64)) = Nat.beq n 0 := by
  have h_toNat : (UInt64.ofNat n).toNat = n := by
    change (BitVec.ofNat 64 n).toNat = n
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h_lt
  cases h_z : Nat.beq n 0 with
  | true =>
    have h_eq := Nat.eq_of_beq_eq_true h_z
    subst h_eq
    rfl
  | false =>
    cases h_b : (UInt64.ofNat n == (0 : UInt64)) with
    | false => rfl
    | true =>
      have h_eq := congrArg UInt64.toNat (eq_of_beq h_b)
      rw [h_toNat] at h_eq
      change n = 0 at h_eq
      rw [h_eq] at h_z
      cases h_z

private noncomputable def evalRefRepeatExpected (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (resolvedMiriProj : List Miri.MIR.ProjectionElem) (rop : RefOperand)
    (count : Nat) (dstTy : MirTy) : Except FaultKind (List RefLocalState) :=
  match dstTy with
  | .array elemTy len =>
    if !Nat.beq count len || !Nat.blt len (Nat.pow 2 64) then
      .error .unsupported
    else
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
      | .error k => .error k
      | .ok (srcTy, sv, rlocals₁) =>
        if !(MirTy.beq srcTy elemTy) then
          .error .unsupported
        else if Nat.beq count 0 then
          writeRefPlace rlocals₁ ⟨dstId, resolvedMiriProj, .ty dstTy⟩
            (.array elemTy [])
        else
          match sv.toVal? with
          | none => .error .undefined
          | some v =>
            writeRefPlace rlocals₁ ⟨dstId, resolvedMiriProj, .ty dstTy⟩
              (.array elemTy (refReplicateVal count v))
  | _ => .error .unsupported

private theorem ite_rvalueM_apply_true {S A : Type} {b : Bool} (h : b = true)
    (t e : Miri.Interpreter.RvalueM S A) (s : S) :
    (@ite (Miri.Interpreter.RvalueM S A) (b = true) inferInstance t e) s =
      t s := by
  rw [h]; rfl

private theorem ite_rvalueM_apply_false {S A : Type} {b : Bool} (h : b = false)
    (t e : Miri.Interpreter.RvalueM S A) (s : S) :
    (@ite (Miri.Interpreter.RvalueM S A) (b = true) inferInstance t e) s =
      e s := by
  rw [h]; rfl

private theorem writeRepeat_refRepeatHooks (ts : List MirTy)
    (rlocals : List RefLocalState) (elemTy : MirTy) (count : Nat)
    (dst : RefDest) (rop : RefOperand)
    (h_lt : count < Nat.pow 2 64) :
    Miri.Interpreter.writeRepeat (refRepeatHooks ts elemTy count dst) ()
        (toMiriOperand rop) dst ⟨rlocals, none⟩ =
      match evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
      | .error k => .error (faultToStepError k) ⟨rlocals, none⟩
      | .ok (srcTy, sv, rlocals₁) =>
        if !(MirTy.beq srcTy elemTy) then
          .error (.unsupported "repeat operand type mismatch") ⟨rlocals, none⟩
        else if Nat.beq count 0 then
          match writeRefPlace rlocals₁ dst (.array elemTy []) with
          | .error k => .error (faultToStepError k) ⟨rlocals₁, none⟩
          | .ok locals' => .ok () ⟨locals', none⟩
        else
          match sv.toVal? with
          | none =>
            .error (.undefinedBehavior "uninit repeat operand") ⟨rlocals₁, none⟩
          | some v =>
            match writeRefPlace rlocals₁ dst
                (.array elemTy (refReplicateVal count v)) with
            | .error k => .error (faultToStepError k) ⟨rlocals₁, some v⟩
            | .ok locals' => .ok () ⟨locals', some v⟩ := by
  dsimp only [Miri.Interpreter.writeRepeat,
    Miri.Interpreter.AggregateHooks.evalOperandAt, refRepeatHooks,
    Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
  | error _ => rfl
  | ok res =>
    let ⟨srcTy, sv, rlocals₁⟩ := res
    dsimp only
    cases MirTy.beq srcTy elemTy with
    | false => rfl
    | true =>
      have h_sized : refSizedLocalLayout.layout.isSized = true := rfl
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, h_sized]
      dsimp only [EStateM.bind]
      cases h_c0 : Nat.beq count 0 with
      | true =>
        have h_u0_t : (UInt64.ofNat count == (0 : UInt64)) = true :=
          Eq.trans (uint64_ofNat_beq_zero_of_lt h_lt) h_c0
        refine Eq.trans (ite_rvalueM_apply_true h_u0_t _ _ _) ?_
        dsimp only
        cases writeRefPlace rlocals₁ dst (.array elemTy []) <;> rfl
      | false =>
        have h_u0_f : (UInt64.ofNat count == (0 : UInt64)) = false :=
          Eq.trans (uint64_ofNat_beq_zero_of_lt h_lt) h_c0
        refine Eq.trans (ite_rvalueM_apply_false h_u0_f _ _ _) ?_
        dsimp only [EStateM.bind]
        rw [miriImmToPayload?_roundtrip]
        dsimp only
        cases sv.toVal? with
        | none => rfl
        | some v =>
          change (refRepeatHooks ts elemTy count dst).memCopyRepeatedly ()
              ⟨Miri.ABI.Size.ZERO, none⟩ ⟨Miri.ABI.Size.ZERO, none⟩
              refSizedLocalLayout.layout.size (UInt64.ofNat count - 1) true
              ⟨rlocals₁, some v⟩ = _
          dsimp only [refRepeatHooks]
          cases writeRefPlace rlocals₁ dst
              (.array elemTy (refReplicateVal count v)) <;> rfl

private theorem evalRefMiriRvalue_repeat (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj resolvedMiriProj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (rop : RefOperand) (count : Nat)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.repeat_ rop count)) = false)
    (h_res : refResolveProjPath ts rlocals (.ty localTy) proj =
      .ok resolvedMiriProj) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.repeat_ rop count)) =
      evalRefRepeatExpected ts rlocals dstId resolvedMiriProj rop count dstTy := by
  dsimp only [evalRefMiriRvalue, evalRefRepeatExpected, Array.toList]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  simp only [Bool.false_eq_true, ite_false]
  dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
    refRvalueHooks, Miri.Interpreter.runRvalue, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.pure, Array.toList]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_res]
  simp only [Bool.false_eq_true, ite_false]
  cases dstTy with
  | bool | int _ _ | unit | never | adtStruct _ | enum _ | tuple _
  | ref _ _ | rawPtr _ _ | unsupported => rfl
  | array elemTy len =>
    dsimp only
    cases h_cl : Nat.beq count len with
    | false => rfl
    | true =>
      cases h_lt : Nat.blt len (Nat.pow 2 64) with
      | false => rfl
      | true =>
        have h_eq_cl : count = len := Nat.eq_of_beq_eq_true h_cl
        subst h_eq_cl
        simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
        rw [writeRepeat_refRepeatHooks ts rlocals elemTy count
          ⟨dstId, resolvedMiriProj, .ty (.array elemTy count)⟩ rop
          (nat_lt_of_blt_eq_true h_lt)]
        cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
        | error k => cases k <;> rfl
        | ok res =>
          let ⟨srcTy, sv, rlocals₁⟩ := res
          dsimp only
          cases MirTy.beq srcTy elemTy with
          | false => rfl
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            cases Nat.beq count 0 with
            | true =>
              simp only [ite_true]
              cases writeRefPlace rlocals₁
                  ⟨dstId, resolvedMiriProj, .ty (.array elemTy count)⟩
                  (.array elemTy []) with
              | error k => cases k <;> rfl
              | ok _ => rfl
            | false =>
              simp only [Bool.false_eq_true, ite_false]
              cases sv.toVal? with
              | none => rfl
              | some v =>
                dsimp only
                cases writeRefPlace rlocals₁
                    ⟨dstId, resolvedMiriProj, .ty (.array elemTy count)⟩
                    (.array elemTy (refReplicateVal count v)) with
                | error k => cases k <;> rfl
                | ok _ => rfl

private theorem evalRefMiriRvalue_cast (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj resolvedMiriProj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (kind : CastKind) (rop : RefOperand)
    (tyId : TyId)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_res : refResolveProjPath ts rlocals (.ty localTy) proj =
      .ok resolvedMiriProj) :
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
                  writeRefPlace rlocals₁
                    ⟨dstId, resolvedMiriProj, .ty dstTy⟩ res := by
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.cast kind rop tyId)) = false := rfl
  dsimp only [evalRefMiriRvalue, Array.toList]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_no]
  simp only [Bool.false_eq_true, ite_false]
  dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
    Miri.Interpreter.RvalueHooks.evalOperandAt, refRvalueHooks,
    Miri.Interpreter.runRvalue, Bind.bind, Pure.pure, EStateM.bind,
    EStateM.pure, Array.toList]
  rw [h_dst]
  dsimp only
  rw [h_pty]
  dsimp only
  rw [h_res]
  simp only [Bool.false_eq_true, ite_false]
  cases evalRefMiriOperandToSlot ts rlocals (toMiriOperand rop) with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨srcTy, sv, rlocals₁⟩ := res
    dsimp only [RefDest.ty?]
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
          cases MirTy.beq castTy dstTy with
          | false => rfl
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            cases evalRefMiriIntToIntCast v castTy with
            | error k => cases k <;> rfl
            | ok res₂ =>
              dsimp only
              cases writeRefPlace rlocals₁
                  ⟨dstId, resolvedMiriProj, .ty dstTy⟩ res₂ with
              | error k => cases k <;> rfl
              | ok _ => rfl

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

private noncomputable def aggLoopBody {Prov σ Ctx Place : Type}
    (hooks : Miri.Interpreter.AggregateHooks Prov σ Ctx Place)
    (c : Ctx) (ops : Array Miri.MIR.Operand) (variantDest : Place) :
    Nat → PUnit → Miri.Interpreter.RvalueM σ (ForInStep PUnit) :=
  fun index _ =>
    match ops[index]? with
    | some operand =>
      Bind.bind
        (hooks.projectField c variantDest
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

private theorem writeAggregate_nonAdt_apply {Prov σ Ctx Place : Type}
    (hooks : Miri.Interpreter.AggregateHooks Prov σ Ctx Place)
    (c : Ctx) (kind : Miri.MIR.AggregateKind) (ops : Array Miri.MIR.Operand)
    (dest : Place) (s : σ)
    (h_kind : kind = .Tuple ∨ ∃ elemTyId, kind = .Array elemTyId) :
    Miri.Interpreter.writeAggregate hooks c kind ops dest s =
      match (forIn (List.range' 0 ops.size 1) PUnit.unit
          (aggLoopBody hooks c ops dest)) s with
      | .ok _ s' =>
        (Bind.bind (hooks.writeDiscriminant c 0 dest)
          (fun _ =>
            Bind.bind (hooks.enforceValidity c (hooks.placeLayout dest))
              (fun b => if b then hooks.validate c dest else Pure.pure ()))) s'
      | .error e s' => .error e s' := by
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
  have h_eq : Miri.Interpreter.writeAggregate hooks c kind ops dest s =
      (Bind.bind
        (forIn (List.range' 0 ops.size 1) PUnit.unit
          (aggLoopBody hooks c ops dest)) cont) s := by
    cases h_kind with
    | inl hk =>
      subst hk
      dsimp only [Miri.Interpreter.writeAggregate]
      rw [h_pure]
      dsimp only [Option.isSome, Bool.false_and]
      rw [ite_eq_right (fun h => Bool.noConfusion h)]
      rw [Std.Legacy.Range.forIn_eq_forIn_range', h_sz]
      rfl
    | inr h_arr =>
      let ⟨elemTyId, hk⟩ := h_arr
      subst hk
      dsimp only [Miri.Interpreter.writeAggregate]
      rw [h_pure]
      dsimp only [Option.isSome, Bool.false_and]
      rw [ite_eq_right (fun h => Bool.noConfusion h)]
      rw [Std.Legacy.Range.forIn_eq_forIn_range', h_sz]
      rfl
  rw [h_eq, rvalueM_bind_apply]
  cases (forIn (List.range' 0 ops.size 1) PUnit.unit
      (aggLoopBody hooks c ops dest)) s <;> rfl

private theorem writeAggregate_adt_apply {Prov σ Ctx Place : Type}
    (hooks : Miri.Interpreter.AggregateHooks Prov σ Ctx Place)
    (c : Ctx) (tyId : Miri.MIR.TyId) (variant : Miri.MIR.VariantIndex)
    (ops : Array Miri.MIR.Operand) (dest variantDest : Place) (s s₁ : σ)
    (h_dc : hooks.projectDowncast c dest variant s = .ok variantDest s₁) :
    Miri.Interpreter.writeAggregate hooks c
        (.Adt tyId variant Array.empty none none) ops dest s =
      match (forIn (List.range' 0 ops.size 1) PUnit.unit
          (aggLoopBody hooks c ops variantDest)) s₁ with
      | .ok _ s' =>
        (Bind.bind (hooks.writeDiscriminant c variant dest)
          (fun _ =>
            Bind.bind (hooks.enforceValidity c (hooks.placeLayout dest))
              (fun b => if b then hooks.validate c dest else Pure.pure ()))) s'
      | .error e s' => .error e s' := by
  have h_sz : (Std.Legacy.Range.mk 0 ops.size 1 (by decide)).size = ops.size :=
    range_zero_size ops.size (by decide)
  let cont : PUnit → Miri.Interpreter.RvalueM σ Unit :=
    fun _ =>
      Bind.bind (hooks.writeDiscriminant c variant dest)
        (fun _ =>
          Bind.bind (hooks.enforceValidity c (hooks.placeLayout dest))
            (fun b => if b then hooks.validate c dest else Pure.pure ()))
  have h_eq :
      Miri.Interpreter.writeAggregate hooks c
        (.Adt tyId variant Array.empty none none) ops dest s =
      (Bind.bind
        (forIn (List.range' 0 ops.size 1) PUnit.unit
          (aggLoopBody hooks c ops variantDest)) cont) s₁ := by
    dsimp only [Miri.Interpreter.writeAggregate]
    have h_outer : ∀ {α β : Type} (m : Miri.Interpreter.RvalueM σ α)
        (k : α → Miri.Interpreter.RvalueM σ β) (v : α),
        m s = .ok v s₁ → (Bind.bind m k) s = k v s₁ := by
      intro α β m k v hm
      rw [rvalueM_bind_apply, hm]
    have h_pure : ∀ {α β : Type} (a : α) (k : α → Miri.Interpreter.RvalueM σ β),
        (Bind.bind (Pure.pure a) k) s₁ = k a s₁ := fun _ _ => rfl
    rw [h_outer _ _ _ h_dc]
    rw [h_pure]
    dsimp only [Option.isSome, Bool.false_and]
    rw [ite_eq_right (fun h => Bool.noConfusion h)]
    rw [Std.Legacy.Range.forIn_eq_forIn_range', h_sz]
    rfl
  rw [h_eq, rvalueM_bind_apply]
  cases (forIn (List.range' 0 ops.size 1) PUnit.unit
      (aggLoopBody hooks c ops variantDest)) s₁ <;> rfl

/-- Unified field-by-field loop lockstep between
`Miri.Interpreter.writeAggregate`'s range loop over `refAggregateHooks` and
`writeAggregateFields` (shared across `.tuple`, `.adtStruct`, and `.adtEnum`).
-/
private theorem writeAggregate_fields_loop_eq {ts bodyLocals : List MirTy}
    {dstLocal : LocalId} {baseMps : List Miri.MIR.ProjectionElem}
    {basePs : List ProjectionElem} {localTy : MirTy}
    (variantDest : RefDest)
    (h_ty : MirSemantics.getElem? bodyLocals dstLocal = some localTy)
    (h_canon : CanonProjList baseMps basePs)
    (pfx rops : List RefOperand) (ops : List Operand)
    (pfxTys fieldTys : List MirTy) (slots : List LocalSlot)
    (h_plen : pfxTys.length = pfx.length)
    (h_flen : rops.length = fieldTys.length)
    (h_dec : mapOption (decodeOperand ts) rops = some ops)
    (h_pf : ∀ (idx : Nat) (ft : MirTy) (s : RefRvalueState),
      MirSemantics.getElem? (pfxTys ++ fieldTys) idx = some ft →
      (refAggregateHooks ts).projectField () variantDest idx s =
        .ok ⟨dstLocal, baseMps ++ [.Field idx 0], .ty ft⟩ s) :
    let allOps : Array Miri.MIR.Operand :=
      Array.mk ((pfx ++ rops).map toMiriOperand)
    match writeAggregateFields bodyLocals localTy dstLocal basePs pfx.length
        slots ops fieldTys with
    | .ok slots' =>
      forIn (List.range' pfx.length rops.length 1) PUnit.unit
        (aggLoopBody (refAggregateHooks ts) () allOps variantDest)
        ⟨zipRefLocals bodyLocals slots, true, none⟩ =
        .ok PUnit.unit ⟨zipRefLocals bodyLocals slots', true, none⟩
    | .error k =>
      ∃ err s_err,
        forIn (List.range' pfx.length rops.length 1) PUnit.unit
          (aggLoopBody (refAggregateHooks ts) () allOps variantDest)
          ⟨zipRefLocals bodyLocals slots, true, none⟩ = .error err s_err ∧
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
      have h_get_ft :
          MirSemantics.getElem? (pfxTys ++ ft :: fts) pfx.length = some ft := by
        rw [← h_plen]
        exact getElem?_append_length pfxTys fts ft
      have h_canon_ext :
          CanonProjList (baseMps ++ [.Field pfx.length 0])
            (basePs ++ [.field pfx.length ft]) :=
        CanonProjList.append h_canon ⟨rfl, trivial⟩
      have h_step :
          aggLoopBody (refAggregateHooks ts) ()
            (Array.mk ((pfx ++ ro :: ros).map toMiriOperand)) variantDest
            pfx.length PUnit.unit ⟨zipRefLocals bodyLocals slots, true, none⟩ =
          match evalOperandToSlot bodyLocals slots o with
          | .error k =>
            .error (faultToStepError k)
              ⟨zipRefLocals bodyLocals slots, true, none⟩
          | .ok (srcTy, sv, slots₁) =>
            if !(MirTy.beq srcTy ft) then
              .error (.unsupported "aggregate field type mismatch")
                ⟨zipRefLocals bodyLocals slots₁, true, none⟩
            else
              match sv.toVal? with
              | none =>
                .error (.undefinedBehavior "uninit aggregate field operand")
                  ⟨zipRefLocals bodyLocals slots₁, true, none⟩
              | some v =>
                match writePlaceWithLocalTy localTy slots₁
                    ⟨dstLocal, basePs ++ [.field pfx.length ft]⟩ ft v with
                | .error k =>
                  .error (faultToStepError k)
                    ⟨zipRefLocals bodyLocals slots₁, true, none⟩
                | .ok slots₂ =>
                  .ok (ForInStep.yield PUnit.unit)
                    ⟨zipRefLocals bodyLocals slots₂, true, none⟩ := by
        dsimp only [aggLoopBody, Option.getD]
        rw [array_getElem?_map_append toMiriOperand pfx ros ro]
        dsimp only
        rw [rvalueM_bind_apply, h_pf pfx.length ft _ h_get_ft]
        dsimp only [Miri.Interpreter.AggregateHooks.evalOperandAt,
          refAggregateHooks, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
          RefDest.ty?]
        rw [evalRefMiriOperandToSlot_eq h_o]
        cases evalOperandToSlot bodyLocals slots o with
        | error _ => rfl
        | ok res =>
          let ⟨srcTy, sv, slots₁⟩ := res
          dsimp only [mapSlotRes, RefDest.ty?]
          rw [miriImmToPayload?_roundtrip]
          dsimp only
          cases MirTy.beq srcTy ft with
          | false => rfl
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            cases sv.toVal? with
            | none => rfl
            | some v =>
              dsimp only
              rw [writeRefPlace_eq h_ty h_canon_ext]
              cases writePlaceWithLocalTy localTy slots₁
                  ⟨dstLocal, basePs ++ [.field pfx.length ft]⟩ ft v <;> rfl
      dsimp only [writeAggregateFields]
      rw [h_range, List.forIn_cons, rvalueM_bind_apply, h_step]
      cases evalOperandToSlot bodyLocals slots o with
      | error k =>
        exact ⟨faultToStepError k, ⟨zipRefLocals bodyLocals slots, true, none⟩,
          rfl, stepErrorToFault_faultToStepError k⟩
      | ok res =>
        let ⟨srcTy, sv, slots₁⟩ := res
        dsimp only
        cases MirTy.beq srcTy ft with
        | false =>
          exact ⟨.unsupported "aggregate field type mismatch",
            ⟨zipRefLocals bodyLocals slots₁, true, none⟩, rfl, rfl⟩
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          cases sv.toVal? with
          | none =>
            exact ⟨.undefinedBehavior "uninit aggregate field operand",
              ⟨zipRefLocals bodyLocals slots₁, true, none⟩, rfl, rfl⟩
          | some v =>
            dsimp only
            cases writePlaceWithLocalTy localTy slots₁
                ⟨dstLocal, basePs ++ [.field pfx.length ft]⟩ ft v with
            | error k =>
              exact ⟨faultToStepError k,
                ⟨zipRefLocals bodyLocals slots₁, true, none⟩,
                rfl, stepErrorToFault_faultToStepError k⟩
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
              have h_pf' : ∀ (idx : Nat) (ft' : MirTy) (s : RefRvalueState),
                  MirSemantics.getElem? ((pfxTys ++ [ft]) ++ fts) idx =
                    some ft' →
                  (refAggregateHooks ts).projectField () variantDest idx s =
                    .ok ⟨dstLocal, baseMps ++ [.Field idx 0], .ty ft'⟩ s := by
                intro idx ft' s h_g
                rw [h_assoc_tys] at h_g
                exact h_pf idx ft' s h_g
              have h_ih := ih (pfx ++ [ro]) os (pfxTys ++ [ft]) fts slots₂
                h_plen' h_flen' h_os h_pf'
              dsimp only at h_ih
              rw [h_assoc_ops, h_len_pfx] at h_ih
              exact h_ih

/-- Element-by-element loop lockstep between
`Miri.Interpreter.writeAggregate` on `.Array` (`refProjectArrayAggregateElem`)
and `writeAggregateArrayElems`. -/
private theorem writeAggregate_array_loop_eq {ts bodyLocals : List MirTy}
    {dstLocal : LocalId} {baseMps : List Miri.MIR.ProjectionElem}
    {basePs : List ProjectionElem} {localTy elemTy : MirTy} {len : Nat}
    (h_ty : MirSemantics.getElem? bodyLocals dstLocal = some localTy)
    (h_canon : CanonProjList baseMps basePs)
    (h_len_u64 : len < Nat.pow 2 64)
    (pfx rops : List RefOperand) (ops : List Operand) (slots : List LocalSlot)
    (h_sum : pfx.length + rops.length = len)
    (h_dec : mapOption (decodeOperand ts) rops = some ops) :
    let allOps : Array Miri.MIR.Operand :=
      Array.mk ((pfx ++ rops).map toMiriOperand)
    let arrDest : RefDest := ⟨dstLocal, baseMps, .ty (.array elemTy len)⟩
    match writeAggregateArrayElems bodyLocals localTy dstLocal basePs elemTy
        pfx.length slots ops with
    | .ok slots' =>
      forIn (List.range' pfx.length rops.length 1) PUnit.unit
        (aggLoopBody (refAggregateHooks ts) () allOps arrDest)
        ⟨zipRefLocals bodyLocals slots, true, none⟩ =
        .ok PUnit.unit ⟨zipRefLocals bodyLocals slots', true, none⟩
    | .error k =>
      ∃ err s_err,
        forIn (List.range' pfx.length rops.length 1) PUnit.unit
          (aggLoopBody (refAggregateHooks ts) () allOps arrDest)
          ⟨zipRefLocals bodyLocals slots, true, none⟩ = .error err s_err ∧
        stepErrorToFault err = k := by
  induction rops generalizing pfx ops slots with
  | nil =>
    injection h_dec with h_ops
    subst h_ops
    rfl
  | cons ro ros ih =>
    let ⟨o, os, h_o, h_os, h_eq⟩ := mapOption_cons_inv h_dec
    subst h_eq
    have h_idx_lt : pfx.length < len := by
      rw [← h_sum]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos ros.length)
    have h_range :
        List.range' pfx.length (ro :: ros).length 1 =
          pfx.length :: List.range' (pfx.length + 1) ros.length 1 := rfl
    have h_canon_ext :
        CanonProjList
          (baseMps ++ [.ConstantIndex pfx.length (pfx.length + 1) false])
          (basePs ++ [.constantIndex pfx.length (pfx.length + 1) false]) :=
      CanonProjList.append h_canon ⟨⟨rfl, rfl⟩, trivial⟩
    have h_step :
        aggLoopBody (refAggregateHooks ts) ()
          (Array.mk ((pfx ++ ro :: ros).map toMiriOperand))
          ⟨dstLocal, baseMps, .ty (.array elemTy len)⟩
          pfx.length PUnit.unit ⟨zipRefLocals bodyLocals slots, true, none⟩ =
        match evalOperandToSlot bodyLocals slots o with
        | .error k =>
          .error (faultToStepError k)
            ⟨zipRefLocals bodyLocals slots, true, none⟩
        | .ok (srcTy, sv, slots₁) =>
          if !(MirTy.beq srcTy elemTy) then
            .error (.unsupported "aggregate field type mismatch")
              ⟨zipRefLocals bodyLocals slots₁, true, none⟩
          else
            match sv.toVal? with
            | none =>
              .error (.undefinedBehavior "uninit aggregate field operand")
                ⟨zipRefLocals bodyLocals slots₁, true, none⟩
            | some v =>
              match writePlaceWithLocalTy localTy slots₁
                  ⟨dstLocal,
                    basePs ++
                      [.constantIndex pfx.length (pfx.length + 1) false]⟩
                  elemTy v with
              | .error k =>
                .error (faultToStepError k)
                  ⟨zipRefLocals bodyLocals slots₁, true, none⟩
              | .ok slots₂ =>
                .ok (ForInStep.yield PUnit.unit)
                  ⟨zipRefLocals bodyLocals slots₂, true, none⟩ := by
      dsimp only [aggLoopBody, Option.getD]
      rw [array_getElem?_map_append toMiriOperand pfx ros ro]
      dsimp only
      rw [rvalueM_bind_apply]
      dsimp only [Miri.Interpreter.AggregateHooks.evalOperandAt,
        refAggregateHooks, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
      rw [refProjectArrayAggregateElem_eq elemTy h_len_u64 h_idx_lt]
      dsimp only [RefDest.ty?]
      rw [evalRefMiriOperandToSlot_eq h_o]
      cases evalOperandToSlot bodyLocals slots o with
      | error _ => rfl
      | ok res =>
        let ⟨srcTy, sv, slots₁⟩ := res
        dsimp only [mapSlotRes, RefDest.ty?]
        rw [miriImmToPayload?_roundtrip]
        dsimp only
        cases MirTy.beq srcTy elemTy with
        | false => rfl
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          cases sv.toVal? with
          | none => rfl
          | some v =>
            dsimp only
            rw [writeRefPlace_eq h_ty h_canon_ext]
            cases writePlaceWithLocalTy localTy slots₁
                ⟨dstLocal,
                  basePs ++ [.constantIndex pfx.length (pfx.length + 1) false]⟩
                elemTy v <;> rfl
    dsimp only [writeAggregateArrayElems]
    rw [h_range, List.forIn_cons, rvalueM_bind_apply, h_step]
    cases evalOperandToSlot bodyLocals slots o with
    | error k =>
      exact ⟨faultToStepError k, ⟨zipRefLocals bodyLocals slots, true, none⟩,
        rfl, stepErrorToFault_faultToStepError k⟩
    | ok res =>
      let ⟨srcTy, sv, slots₁⟩ := res
      dsimp only
      cases MirTy.beq srcTy elemTy with
      | false =>
        exact ⟨.unsupported "aggregate field type mismatch",
          ⟨zipRefLocals bodyLocals slots₁, true, none⟩, rfl, rfl⟩
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        cases sv.toVal? with
        | none =>
          exact ⟨.undefinedBehavior "uninit aggregate field operand",
            ⟨zipRefLocals bodyLocals slots₁, true, none⟩, rfl, rfl⟩
        | some v =>
          dsimp only
          cases writePlaceWithLocalTy localTy slots₁
              ⟨dstLocal,
                basePs ++ [.constantIndex pfx.length (pfx.length + 1) false]⟩
              elemTy v with
          | error k =>
            exact ⟨faultToStepError k,
              ⟨zipRefLocals bodyLocals slots₁, true, none⟩,
              rfl, stepErrorToFault_faultToStepError k⟩
          | ok slots₂ =>
            dsimp only
            have h_assoc_ops : (pfx ++ [ro]) ++ ros = pfx ++ (ro :: ros) :=
              List.append_assoc pfx [ro] ros
            have h_len_pfx : (pfx ++ [ro]).length = pfx.length + 1 := by
              rw [List.length_append]
              rfl
            have h_sum' : (pfx ++ [ro]).length + ros.length = len := by
              rw [h_len_pfx, Nat.add_assoc, Nat.add_comm 1 ros.length]
              exact h_sum
            have h_ih := ih (pfx ++ [ro]) os slots₂ h_sum' h_os
            dsimp only at h_ih
            rw [h_assoc_ops, h_len_pfx] at h_ih
            exact h_ih

private theorem fieldsForVariant?_some_lt {ety : EnumTy} {v : Nat}
    {fs : List MirTy} (h : fieldsForVariant? ety v = some fs) :
    Nat.blt v ety.discriminants.length = true := by
  dsimp only [fieldsForVariant?] at h
  cases hb : Nat.blt v ety.discriminants.length with
  | false => rw [hb] at h; cases h
  | true => rfl

/-- Aggregate lockstep across `.tuple`, `.adtStruct`, `.adtEnum`, and `.array`:
evaluating `.aggregate rkind rops` via `Miri.Interpreter.evalRvalueIntoPlace`
and `Miri.Interpreter.writeAggregate` agrees with `writeAggregate`. -/
private theorem evalRefMiriRvalue_aggregate_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot} {dstId : LocalId}
    {proj resolvedMiriProj : List Miri.MIR.ProjectionElem}
    {resolvedProj : List ProjectionElem}
    {dstSlot : LocalSlot} {localTy dstTy : MirTy}
    {rkind : RefAggregateKind} {kind : AggregateKind}
    {rops : List RefOperand} {ops : List Operand}
    (h_ty : MirSemantics.getElem? bodyLocals dstId = some localTy)
    (h_dst : MirSemantics.getElem? (zipRefLocals bodyLocals slots) dstId =
      some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_res : refResolveProjPath ts (zipRefLocals bodyLocals slots) (.ty localTy)
      proj = .ok resolvedMiriProj)
    (h_canon : CanonProjList resolvedMiriProj resolvedProj)
    (h_kind : decodeAggregateKind ts rkind = some kind)
    (h_ops : mapOption (decodeOperand ts) rops = some ops)
    (h_no_ov : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.aggregate rkind rops)) = false) :
    evalRefMiriRvalue ts (zipRefLocals bodyLocals slots) ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.aggregate rkind rops)) =
      mapSlotsRes bodyLocals
        (writeAggregate bodyLocals localTy slots ⟨dstId, resolvedProj⟩ dstTy
          kind ops) := by
  let s₀ : RefRvalueState := ⟨zipRefLocals bodyLocals slots, true, none⟩
  let rdest : RefDest := ⟨dstId, resolvedMiriProj, .ty dstTy⟩
  have h_len_map :
      (Array.mk (rops.map toMiriOperand)).size = rops.length :=
    List.length_map toMiriOperand
  have h_len_ops : rops.length = ops.length := mapOption_length h_ops
  have h_ev_place :
      Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.aggregate rkind rops)) ⟨dstId, Array.mk proj⟩
          ⟨zipRefLocals bodyLocals slots, false, none⟩ =
        (refRvalueHooks ts).writeAggregate () (toMiriAggregateKind rkind)
          (Array.mk (rops.map toMiriOperand)) rdest s₀ := by
    dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace]
    rw [rvalueM_bind_apply]
    have h_ep :
        (refRvalueHooks ts).evalPlace () ⟨dstId, Array.mk proj⟩ true
            ⟨zipRefLocals bodyLocals slots, false, none⟩ =
          .ok rdest s₀ := by
      dsimp only [refRvalueHooks, Array.toList, rdest, s₀]
      rw [h_dst]; dsimp only
      rw [h_pty]; dsimp only
      rw [h_res]
      simp only [Bool.false_eq_true, ite_false]
    rw [h_ep]
  dsimp only [evalRefMiriRvalue, Array.toList]
  rw [h_dst]; dsimp only
  rw [h_pty]; dsimp only
  rw [h_no_ov]
  simp only [Bool.false_eq_true, ite_false]
  have h_run :
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (refRvalueHooks ts) ()
          (toMiriRvalue (.aggregate rkind rops)) ⟨dstId, Array.mk proj⟩)
        ⟨zipRefLocals bodyLocals slots, false, none⟩ =
      Miri.Interpreter.runRvalue
        ((refRvalueHooks ts).writeAggregate () (toMiriAggregateKind rkind)
          (Array.mk (rops.map toMiriOperand)) rdest) s₀ := by
    dsimp only [Miri.Interpreter.runRvalue]
    exact h_ev_place ▸ rfl
  refine Eq.trans (congrArg
    (fun p : RefRvalueState × Except Miri.Interpreter.StepError Unit =>
      match p with
      | (st', .ok ()) => Except.ok st'.locals
      | (_, .error (.undefinedBehavior _))
      | (_, .error (.stack (.localExpectedLive _))) =>
        Except.error FaultKind.undefined
      | _ => Except.error FaultKind.unsupported) h_run) ?_
  cases rkind with
  | tuple =>
    injection h_kind with hk
    subst hk
    dsimp only [toMiriAggregateKind, refRvalueHooks, rdest]
    cases dstTy with
    | unit =>
      cases ops with
      | nil =>
        have h_rops_nil : rops = [] := by
          cases rops with
          | nil => rfl
          | cons _ _ => cases h_len_ops
        subst h_rops_nil
        have h_sh :
            refAggregateValidShape ts .Tuple
              (Array.mk (List.map toMiriOperand [])).size
              ⟨dstId, resolvedMiriProj, .ty .unit⟩ = true := rfl
        have h_wa :
            writeAggregate bodyLocals localTy slots ⟨dstId, resolvedProj⟩ .unit
              .tuple [] =
            writePlaceWithLocalTy localTy slots ⟨dstId, resolvedProj⟩ .unit
              .unit := rfl
        rw [h_sh, h_wa]
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        dsimp only [Miri.Interpreter.runRvalue]
        rw [writeAggregate_nonAdt_apply _ _ _ _ _ _ (Or.inl rfl)]
        dsimp only [Array.size, List.map, List.length, List.range']
        rw [List.forIn_nil]
        dsimp only [refAggregateHooks, Bind.bind, Pure.pure, EStateM.bind,
          EStateM.pure, s₀]
        rw [writeRefPlace_eq h_ty h_canon]
        cases writePlaceWithLocalTy localTy slots ⟨dstId, resolvedProj⟩ .unit
            .unit with
        | error k => cases k <;> rfl
        | ok _ => rfl
      | cons o os =>
        have h_sh :
            refAggregateValidShape ts .Tuple
              (Array.mk (rops.map toMiriOperand)).size
              ⟨dstId, resolvedMiriProj, .ty .unit⟩ = false := by
          dsimp only [refAggregateValidShape]
          rw [h_len_map, h_len_ops]
          rfl
        rw [h_sh]
        rfl
    | tuple fieldTys =>
      cases fieldTys with
      | nil => rfl
      | cons ft fts =>
        have h_sh :
            refAggregateValidShape ts .Tuple
              (Array.mk (rops.map toMiriOperand)).size
              ⟨dstId, resolvedMiriProj, .ty (.tuple (ft :: fts))⟩ =
            Nat.beq ops.length (ft :: fts).length := by
          dsimp only [refAggregateValidShape]
          rw [Anneal.MirWp.list_isEmpty_cons, h_len_map, h_len_ops]
          simp only [Bool.not_false, Bool.true_and]
        have h_wa :
            writeAggregate bodyLocals localTy slots ⟨dstId, resolvedProj⟩
              (.tuple (ft :: fts)) .tuple ops =
            if !(Nat.beq ops.length (ft :: fts).length) then
              .error .unsupported
            else
              writeAggregateFields bodyLocals localTy dstId resolvedProj 0 slots
                ops (ft :: fts) := by
          dsimp only [writeAggregate]
          cases Nat.beq ops.length (ft :: fts).length <;> rfl
        rw [h_sh, h_wa]
        cases h_beq : Nat.beq ops.length (ft :: fts).length with
        | false => rfl
        | true =>
          have h_flen : rops.length = (ft :: fts).length :=
            h_len_ops.trans (Nat.eq_of_beq_eq_true h_beq)
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          dsimp only [Miri.Interpreter.runRvalue]
          rw [writeAggregate_nonAdt_apply _ _ _ _ _ _ (Or.inl rfl), h_len_map]
          have h_pf : ∀ (idx : Nat) (ft' : MirTy) (s : RefRvalueState),
              MirSemantics.getElem? ([] ++ ft :: fts) idx = some ft' →
              (refAggregateHooks ts).projectField ()
                ⟨dstId, resolvedMiriProj, .ty (.tuple (ft :: fts))⟩ idx s =
              .ok ⟨dstId, resolvedMiriProj ++ [.Field idx 0], .ty ft'⟩ s := by
            intro idx ft' s h_g
            dsimp only [List.nil_append] at h_g
            dsimp only [refAggregateHooks]
            rw [h_g]
          have h_loop := writeAggregate_fields_loop_eq
            ⟨dstId, resolvedMiriProj, .ty (.tuple (ft :: fts))⟩
            h_ty h_canon [] rops ops [] (ft :: fts) slots rfl h_flen h_ops h_pf
          dsimp only [List.nil_append, List.length_nil] at h_loop
          cases h_wf : writeAggregateFields bodyLocals localTy dstId
              resolvedProj 0 slots ops (ft :: fts) with
          | ok slots' =>
            rw [h_wf] at h_loop
            dsimp only [s₀]
            rw [h_loop]
            dsimp only [refAggregateHooks, Bind.bind, Pure.pure, EStateM.bind,
              EStateM.pure]
            rfl
          | error k =>
            rw [h_wf] at h_loop
            let ⟨err, s_err, h_err, h_k⟩ := h_loop
            dsimp only [s₀]
            rw [h_err]
            cases err with
            | undefinedBehavior _ => cases h_k; rfl
            | stack se => cases se <;> (cases h_k; rfl)
            | _ => cases h_k; rfl
    | _ => rfl
  | adtStruct styId =>
    dsimp only [decodeAggregateKind] at h_kind
    cases h_t : MirSemantics.getElem? ts styId with
    | none => rw [h_t] at h_kind; cases h_kind
    | some mty =>
      rw [h_t] at h_kind
      cases mty with
      | adtStruct sty =>
        injection h_kind with hk
        subst hk
        dsimp only [toMiriAggregateKind, refRvalueHooks, rdest]
        cases dstTy with
        | adtStruct dstSty =>
          have h_sh :
              refAggregateValidShape ts (.Adt styId 0 Array.empty none none)
                (Array.mk (rops.map toMiriOperand)).size
                ⟨dstId, resolvedMiriProj, .ty (.adtStruct dstSty)⟩ =
              (StructTy.beq sty dstSty &&
                Nat.beq ops.length sty.fields.length &&
                areSupportedFieldTys sty.fields &&
                !(isTypeUninhabited (.adtStruct sty))) := by
            dsimp only [refAggregateValidShape]
            rw [h_t]
            dsimp only
            rw [h_len_map, h_len_ops, refAreSupportedFieldTys_eq,
                refIsTypeUninhabited_eq]
            simp only [Nat.beq_refl, Bool.true_and]
          have h_wa :
              writeAggregate bodyLocals localTy slots ⟨dstId, resolvedProj⟩
                (.adtStruct dstSty) (.adtStruct sty) ops =
              if !(StructTy.beq sty dstSty) ||
                  !(Nat.beq ops.length sty.fields.length) ||
                  !(areSupportedFieldTys sty.fields) ||
                  isTypeUninhabited (.adtStruct sty) then
                .error .unsupported
              else if ops.isEmpty then
                writePlaceWithLocalTy localTy slots ⟨dstId, resolvedProj⟩
                  (.adtStruct dstSty) (.structVal sty [])
              else
                writeAggregateFields bodyLocals localTy dstId resolvedProj 0
                  slots ops sty.fields := rfl
          rw [h_sh, h_wa]
          cases h_sb : StructTy.beq sty dstSty with
          | false => rfl
          | true =>
            have h_sty_eq : sty = dstSty :=
              Anneal.MirWp.StructTy.beq_iff.mp h_sb
            subst h_sty_eq
            cases h_ar : Nat.beq ops.length sty.fields.length with
            | false => rfl
            | true =>
              cases areSupportedFieldTys sty.fields with
              | false => rfl
              | true =>
                cases isTypeUninhabited (.adtStruct sty) with
                | true => rfl
                | false =>
                  simp only [Bool.true_and, Bool.not_true, Bool.not_false,
                    Bool.false_or, Bool.false_eq_true, ite_false]
                  dsimp only [Miri.Interpreter.runRvalue]
                  have h_flen : rops.length = sty.fields.length :=
                    h_len_ops.trans (Nat.eq_of_beq_eq_true h_ar)
                  rw [writeAggregate_adt_apply _ _ _ _ _ _
                      ⟨dstId, resolvedMiriProj, .ty (.adtStruct sty)⟩ _ _ rfl,
                      h_len_map]
                  cases h_sf : sty.fields with
                  | nil =>
                    rw [h_sf] at h_flen
                    have h_ops_nil : ops = [] := by
                      cases ops with
                      | nil => rfl
                      | cons _ _ => rw [h_len_ops] at h_flen; cases h_flen
                    subst h_ops_nil
                    have h_rops_nil : rops = [] := by
                      cases rops with
                      | nil => rfl
                      | cons _ _ => cases h_flen
                    subst h_rops_nil
                    have h_emp : ([] : List Operand).isEmpty = true := rfl
                    rw [h_emp]
                    simp only [ite_true]
                    dsimp only [List.length, List.range']
                    rw [List.forIn_nil]
                    dsimp only [refAggregateHooks, Bind.bind, Pure.pure,
                      EStateM.bind, EStateM.pure, s₀]
                    rw [h_sf]
                    have h_sf_emp : ([] : List MirTy).isEmpty = true := rfl
                    rw [h_sf_emp]
                    simp only [ite_true]
                    rw [writeRefPlace_eq h_ty h_canon]
                    cases writePlaceWithLocalTy localTy slots
                        ⟨dstId, resolvedProj⟩ (.adtStruct sty)
                        (.structVal sty []) with
                    | error k => cases k <;> rfl
                    | ok _ => rfl
                  | cons ft fts =>
                    rw [h_sf] at h_flen
                    have h_ops_ne : ops.isEmpty = false := by
                      cases ops with
                      | nil => rw [h_len_ops] at h_flen; cases h_flen
                      | cons _ _ => rfl
                    rw [h_ops_ne]
                    simp only [Bool.false_eq_true, ite_false]
                    have h_pf : ∀ (idx : Nat) (ft' : MirTy) (s : RefRvalueState),
                        MirSemantics.getElem? ([] ++ ft :: fts) idx = some ft' →
                        (refAggregateHooks ts).projectField ()
                          ⟨dstId, resolvedMiriProj, .ty (.adtStruct sty)⟩ idx s =
                        .ok ⟨dstId, resolvedMiriProj ++ [.Field idx 0],
                          .ty ft'⟩ s := by
                      intro idx ft' s h_g
                      dsimp only [List.nil_append] at h_g
                      dsimp only [refAggregateHooks]
                      rw [h_sf, h_g]
                    have h_loop := writeAggregate_fields_loop_eq
                      ⟨dstId, resolvedMiriProj, .ty (.adtStruct sty)⟩
                      h_ty h_canon [] rops ops [] (ft :: fts) slots rfl h_flen
                      h_ops h_pf
                    dsimp only [List.nil_append, List.length_nil] at h_loop
                    cases h_wf : writeAggregateFields bodyLocals localTy dstId
                        resolvedProj 0 slots ops (ft :: fts) with
                    | ok slots' =>
                      rw [h_wf] at h_loop
                      dsimp only [s₀]
                      rw [h_loop]
                      dsimp only [refAggregateHooks, Bind.bind, Pure.pure,
                        EStateM.bind, EStateM.pure]
                      rw [h_sf]
                      rfl
                    | error k =>
                      rw [h_wf] at h_loop
                      let ⟨err, s_err, h_err, h_k⟩ := h_loop
                      dsimp only [s₀]
                      rw [h_err]
                      cases err with
                      | undefinedBehavior _ => cases h_k; rfl
                      | stack se => cases se <;> (cases h_k; rfl)
                      | _ => cases h_k; rfl
        | enum dstEty =>
          have h_sh :
              refAggregateValidShape ts (.Adt styId 0 Array.empty none none)
                (Array.mk (rops.map toMiriOperand)).size
                ⟨dstId, resolvedMiriProj, .ty (.enum dstEty)⟩ = false := by
            dsimp only [refAggregateValidShape]
            rw [h_t]
          rw [h_sh]
          rfl
        | _ => rfl
      | _ => cases h_kind
  | adtEnum etyId variantIdx =>
    dsimp only [decodeAggregateKind] at h_kind
    cases h_t : MirSemantics.getElem? ts etyId with
    | none => rw [h_t] at h_kind; cases h_kind
    | some mty =>
      rw [h_t] at h_kind
      cases mty with
      | enum ety =>
        injection h_kind with hk
        subst hk
        dsimp only [toMiriAggregateKind, refRvalueHooks, rdest]
        cases dstTy with
        | enum dstEty =>
          have h_sh :
              refAggregateValidShape ts
                (.Adt etyId variantIdx Array.empty none none)
                (Array.mk (rops.map toMiriOperand)).size
                ⟨dstId, resolvedMiriProj, .ty (.enum dstEty)⟩ =
              (EnumTy.beq ety dstEty && enumAdmitted ety &&
                match fieldsForVariant? ety variantIdx with
                | some varFieldTys => Nat.beq ops.length varFieldTys.length
                | none => false) := by
            dsimp only [refAggregateValidShape]
            rw [h_t]
            dsimp only
            rw [h_len_map, h_len_ops, refEnumAdmitted_eq,
                refFieldsForVariant?_eq]
            rfl
          have h_wa :
              writeAggregate bodyLocals localTy slots ⟨dstId, resolvedProj⟩
                (.enum dstEty) (.adtEnum ety variantIdx) ops =
              if !(EnumTy.beq ety dstEty) || !(enumAdmitted ety) then
                .error .unsupported
              else
                match fieldsForVariant? ety variantIdx with
                | none => .error .unsupported
                | some varFieldTys =>
                  if !(Nat.beq ops.length varFieldTys.length) then
                    .error .unsupported
                  else
                    match writeAggregateFields bodyLocals localTy dstId
                        (resolvedProj ++ [.downcast variantIdx]) 0 slots ops
                        varFieldTys with
                    | .error k => .error k
                    | .ok locals₁ =>
                      evalSetDiscriminantResolved localTy locals₁
                        ⟨dstId, resolvedProj⟩ (.enum ety) variantIdx := rfl
          rw [h_sh, h_wa]
          cases h_eb : EnumTy.beq ety dstEty with
          | false => rfl
          | true =>
            have h_ety_eq : ety = dstEty :=
              Anneal.MirWp.EnumTy.beq_iff.mp h_eb
            subst h_ety_eq
            cases h_adm : enumAdmitted ety with
            | false => rfl
            | true =>
              simp only [Bool.true_and, Bool.not_true, Bool.false_or,
                Bool.false_eq_true, ite_false]
              cases h_fv : fieldsForVariant? ety variantIdx with
              | none =>
                have h_mn :
                    (match (none : Option (List MirTy)) with
                    | some varFieldTys => Nat.beq ops.length varFieldTys.length
                    | none => false) = false := rfl
                rw [h_mn]
                rfl
              | some varFieldTys =>
                have h_ms :
                    (match some varFieldTys with
                    | some vfs => Nat.beq ops.length vfs.length
                    | none => false) =
                    Nat.beq ops.length varFieldTys.length := rfl
                rw [h_ms]
                dsimp only
                cases h_ar : Nat.beq ops.length varFieldTys.length with
                | false => rfl
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                  dsimp only [Miri.Interpreter.runRvalue]
                  have h_flen : rops.length = varFieldTys.length :=
                    h_len_ops.trans (Nat.eq_of_beq_eq_true h_ar)
                  have h_vlt :
                      Nat.blt variantIdx ety.discriminants.length = true :=
                    fieldsForVariant?_some_lt h_fv
                  let varDest : RefDest :=
                    ⟨dstId, resolvedMiriProj ++ [.Downcast none variantIdx],
                      .variant ety variantIdx⟩
                  have h_dc :
                      (refAggregateHooks ts).projectDowncast ()
                        ⟨dstId, resolvedMiriProj, .ty (.enum ety)⟩ variantIdx
                        s₀ = .ok varDest s₀ := by
                    dsimp only [refAggregateHooks, varDest]
                    rw [refEnumAdmitted_eq, h_adm, h_vlt]
                    rfl
                  rw [writeAggregate_adt_apply _ _ _ _ _ _ varDest _ _ h_dc,
                      h_len_map]
                  have h_canon_dc :
                      CanonProjList
                        (resolvedMiriProj ++ [.Downcast none variantIdx])
                        (resolvedProj ++ [.downcast variantIdx]) :=
                    CanonProjList.append h_canon ⟨rfl, trivial⟩
                  have h_pf : ∀ (idx : Nat) (ft' : MirTy) (s : RefRvalueState),
                      MirSemantics.getElem? ([] ++ varFieldTys) idx =
                        some ft' →
                      (refAggregateHooks ts).projectField () varDest idx s =
                        .ok ⟨dstId,
                          (resolvedMiriProj ++ [.Downcast none variantIdx]) ++
                            [.Field idx 0],
                          .ty ft'⟩ s := by
                    intro idx ft' s h_g
                    dsimp only [List.nil_append] at h_g
                    dsimp only [refAggregateHooks, varDest]
                    rw [refFieldsForVariant?_eq, h_fv]
                    dsimp only
                    rw [h_g]
                  have h_loop := writeAggregate_fields_loop_eq varDest h_ty
                    h_canon_dc [] rops ops [] varFieldTys slots rfl h_flen
                    h_ops h_pf
                  dsimp only [List.nil_append, List.length_nil] at h_loop
                  cases h_wf : writeAggregateFields bodyLocals localTy dstId
                      (resolvedProj ++ [.downcast variantIdx]) 0 slots ops
                      varFieldTys with
                  | error k =>
                    rw [h_wf] at h_loop
                    let ⟨err, s_err, h_err, h_k⟩ := h_loop
                    dsimp only [s₀]
                    rw [h_err]
                    cases err with
                    | undefinedBehavior _ => cases h_k; rfl
                    | stack se => cases se <;> (cases h_k; rfl)
                    | _ => cases h_k; rfl
                  | ok slots₁ =>
                    rw [h_wf] at h_loop
                    dsimp only [s₀]
                    rw [h_loop]
                    dsimp only [refAggregateHooks, Bind.bind, Pure.pure,
                      EStateM.bind, EStateM.pure]
                    rw [evalRefSetDiscriminant_eq variantIdx h_ty h_canon]
                    cases evalSetDiscriminantResolved localTy slots₁
                        ⟨dstId, resolvedProj⟩ (.enum ety) variantIdx with
                    | error k => cases k <;> rfl
                    | ok _ => rfl
        | adtStruct dstSty =>
          have h_sh :
              refAggregateValidShape ts
                (.Adt etyId variantIdx Array.empty none none)
                (Array.mk (rops.map toMiriOperand)).size
                ⟨dstId, resolvedMiriProj, .ty (.adtStruct dstSty)⟩ = false := by
            dsimp only [refAggregateValidShape]
            rw [h_t]
          rw [h_sh]
          rfl
        | _ => rfl
      | _ => cases h_kind
  | array elemTyId =>
    dsimp only [decodeAggregateKind, optMap] at h_kind
    cases h_t : MirSemantics.getElem? ts elemTyId with
    | none => rw [h_t] at h_kind; cases h_kind
    | some elemTy =>
      rw [h_t] at h_kind
      injection h_kind with hk
      subst hk
      dsimp only [toMiriAggregateKind, refRvalueHooks, rdest]
      cases dstTy with
      | array dstElemTy len =>
        have h_sh :
            refAggregateValidShape ts (.Array elemTyId)
              (Array.mk (rops.map toMiriOperand)).size
              ⟨dstId, resolvedMiriProj, .ty (.array dstElemTy len)⟩ =
            (MirTy.beq elemTy dstElemTy && Nat.beq ops.length len &&
              isSupportedScalarOrUnitTy elemTy &&
              Nat.blt len (Nat.pow 2 64)) := by
          dsimp only [refAggregateValidShape]
          rw [h_t]
          dsimp only
          rw [h_len_map, h_len_ops, refIsSupportedLocalTy_eq]
        have h_wagg :
            writeAggregate bodyLocals localTy slots ⟨dstId, resolvedProj⟩
              (.array dstElemTy len) (.array elemTy) ops =
            if !(MirTy.beq elemTy dstElemTy) || !(Nat.beq ops.length len) ||
                !(isSupportedScalarOrUnitTy elemTy) ||
                !(Nat.blt len (Nat.pow 2 64)) then
              .error .unsupported
            else if ops.isEmpty then
              writePlaceWithLocalTy localTy slots ⟨dstId, resolvedProj⟩
                (.array dstElemTy len) (.array elemTy [])
            else
              writeAggregateArrayElems bodyLocals localTy dstId resolvedProj
                elemTy 0 slots ops := rfl
        rw [h_sh, h_wagg]
        cases h_eb : MirTy.beq elemTy dstElemTy with
        | false => rfl
        | true =>
          have h_eeq := MirTy.eq_of_beq h_eb
          subst h_eeq
          cases h_ar : Nat.beq ops.length len with
          | false => rfl
          | true =>
            cases isSupportedScalarOrUnitTy elemTy with
            | false => rfl
            | true =>
              cases h_blt : Nat.blt len (Nat.pow 2 64) with
              | false => rfl
              | true =>
                simp only [Bool.true_and, Bool.not_true, Bool.false_or,
                  Bool.false_eq_true, ite_false]
                dsimp only [Miri.Interpreter.runRvalue]
                have h_len_eq : ops.length = len := Nat.eq_of_beq_eq_true h_ar
                have h_len_u64 : len < Nat.pow 2 64 :=
                  nat_lt_of_blt_eq_true h_blt
                rw [writeAggregate_nonAdt_apply _ _ _ _ _ _
                    (Or.inr ⟨elemTyId, rfl⟩), h_len_map]
                cases ops with
                | nil =>
                  dsimp only [List.length] at h_len_eq
                  subst h_len_eq
                  have h_rops_nil : rops = [] := by
                    cases rops with
                    | nil => rfl
                    | cons _ _ => cases h_len_ops
                  subst h_rops_nil
                  have h_emp : ([] : List Operand).isEmpty = true := rfl
                  rw [h_emp]
                  simp only [ite_true]
                  dsimp only [List.length, List.range']
                  rw [List.forIn_nil]
                  dsimp only [refAggregateHooks, Bind.bind, Pure.pure,
                    EStateM.bind, EStateM.pure, s₀]
                  have h_beq0 : Nat.beq 0 0 = true := rfl
                  rw [h_beq0]
                  simp only [ite_true]
                  rw [writeRefPlace_eq h_ty h_canon]
                  cases writePlaceWithLocalTy localTy slots
                      ⟨dstId, resolvedProj⟩ (.array elemTy 0)
                      (.array elemTy []) with
                  | error k => cases k <;> rfl
                  | ok _ => rfl
                | cons o os =>
                  have h_sum : ([] : List RefOperand).length + rops.length =
                      len := by
                    dsimp only [List.length]
                    rw [Nat.zero_add, h_len_ops, h_len_eq]
                  have h_len_pos : Nat.beq len 0 = false := by
                    rw [← h_len_eq]
                    rfl
                  have h_ne : (o :: os).isEmpty = false := rfl
                  rw [h_ne]
                  simp only [Bool.false_eq_true, ite_false]
                  have h_loop := writeAggregate_array_loop_eq (ts := ts)
                    (elemTy := elemTy) h_ty h_canon
                    h_len_u64 [] rops (o :: os) slots h_sum h_ops
                  dsimp only [List.nil_append, List.length_nil] at h_loop
                  cases h_wa : writeAggregateArrayElems bodyLocals localTy
                      dstId resolvedProj elemTy 0 slots (o :: os) with
                  | ok slots' =>
                    rw [h_wa] at h_loop
                    dsimp only [s₀]
                    rw [h_loop]
                    dsimp only [refAggregateHooks, Bind.bind, Pure.pure,
                      EStateM.bind, EStateM.pure]
                    rw [h_len_pos]
                    rfl
                  | error k =>
                    rw [h_wa] at h_loop
                    let ⟨err, s_err, h_err, h_k⟩ := h_loop
                    dsimp only [s₀]
                    rw [h_err]
                    cases err with
                    | undefinedBehavior _ => cases h_k; rfl
                    | stack se => cases se <;> (cases h_k; rfl)
                    | _ => cases h_k; rfl
      | _ => rfl

private theorem refScalarLayoutData_size (w : IntWidth) (signed : Bool) :
    (refScalarLayoutData w signed).size = toMiriSize w := by
  cases w <;> cases signed <;> rfl

private theorem discriminantForVariant_cached_ok {ts : List MirTy}
    (ety : EnumTy) (variant disc : Nat) (rlocals₁ : List RefLocalState)
    (h_adm : enumAdmitted ety = true)
    (h_disc : MirSemantics.getElem? ety.discriminants variant = some disc) :
    (refRvalueHooks ts).discriminantForVariant () 0 variant
        ⟨rlocals₁, true, some ety⟩ =
      .ok ⟨payloadToMiriImmediate
            (.int ety.discrWidth ety.discrSigned,
              SlotVal.scalar ⟨ety.discrWidth, ety.discrSigned,
                truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩),
          ⟨1, refScalarLayoutData ety.discrWidth ety.discrSigned⟩⟩
        ⟨rlocals₁, true, some ety⟩ := by
  have hd_blt : Nat.blt disc (Nat.pow 2 ety.discrWidth.bitWidth) = true :=
    @list_all_of_getElem? Nat ety.discriminants
      (fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth)) variant disc
      (enumAdmitted_discr_in_bounds h_adm) h_disc
  have hd_mod : disc < (Nat.pow 2 ety.discrWidth.bitWidth) := nat_lt_of_blt_eq_true hd_blt
  have hd_u128 : disc < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hd_mod (intWidth_modulus_le_u128 ety.discrWidth)
  have h_trunc_beq :
      (truncateBits ety.discrWidth (BitVec.ofNat 128 disc) ==
        BitVec.ofNat 128 disc) = true := by
    have h_eq :
        truncateBits ety.discrWidth (BitVec.ofNat 128 disc) =
          BitVec.ofNat 128 disc := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_truncateBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd_u128]
      exact Nat.mod_eq_of_lt hd_mod
    rw [h_eq]
    exact beq_self_eq_true _
  have h_from_uint := scalar_fromUInt_of_truncateBits_beq
    (P := Miri.Memory.Provenance) h_trunc_beq
  have h_eval :
      (refRvalueHooks ts).discriminantForVariant () 0 variant
          ⟨rlocals₁, true, some ety⟩ =
        .ok ⟨payloadToMiriImmediate
              (.int ety.discrWidth ety.discrSigned,
                SlotVal.scalar ⟨ety.discrWidth, ety.discrSigned,
                  (miriScalar ety.discrWidth (BitVec.ofNat 128 disc)).data⟩),
            ⟨1, refScalarLayoutData ety.discrWidth ety.discrSigned⟩⟩
          ⟨rlocals₁, true, some ety⟩ := by
    dsimp only [refRvalueHooks, Nat.beq,
      Miri.Interpreter.Discriminant.discriminantForVariant,
      refDiscriminantHooks, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [h_disc]
    have h_ty_bne : ((1 : Nat) != 1) = false := rfl
    dsimp only
    rw [h_ty_bne]
    simp only [Bool.false_eq_true, ite_false]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [refScalarLayoutData_size, h_from_uint]
    rfl
  rw [h_eval, miriScalar_data]

private theorem discriminantForVariant_cached_none {ts : List MirTy}
    (ety : EnumTy) (variant : Nat) (rlocals₁ : List RefLocalState)
    (h_none : MirSemantics.getElem? ety.discriminants variant = none) :
    (refRvalueHooks ts).discriminantForVariant () 0 variant
        ⟨rlocals₁, true, some ety⟩ =
      .error (.invalidProgram "enum variant out of bounds")
        ⟨rlocals₁, true, some ety⟩ := by
  dsimp only [refRvalueHooks, Nat.beq,
    Miri.Interpreter.Discriminant.discriminantForVariant,
    refDiscriminantHooks, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  rw [h_none]

/-- Discriminant lockstep across `.zeroSized`, `.single`, `.scalar`, and
`.niche` enums (both fieldless and payload, unprojected or projected):
evaluating `Rvalue.discriminant` through `Miri.Interpreter.evalRvalueIntoPlace`
and `Miri.Interpreter.Discriminant.{readDiscriminant, discriminantForVariant}`
agrees with `evalRvalue` + `writePlaceWithLocalTy`. -/
private theorem evalRefMiriRvalue_discriminant_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot} {dstId : LocalId}
    {proj resolvedMiriProj : List Miri.MIR.ProjectionElem}
    {resolvedProj : List ProjectionElem}
    {dstSlot : LocalSlot} {localTy dstTy : MirTy}
    {rp : RefPlace} {p : Place}
    (h_ty : MirSemantics.getElem? bodyLocals dstId = some localTy)
    (h_dst : MirSemantics.getElem? (zipRefLocals bodyLocals slots) dstId =
      some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_res : refResolveProjPath ts (zipRefLocals bodyLocals slots) (.ty localTy)
      proj = .ok resolvedMiriProj)
    (h_canon : CanonProjList resolvedMiriProj resolvedProj)
    (h_p : decodePlace ts rp = some p) :
    evalRefMiriRvalue ts (zipRefLocals bodyLocals slots) ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.discriminant rp)) =
      mapSlotsRes bodyLocals
        (match evalRvalue bodyLocals slots dstTy (.discriminant p) with
        | .error k => .error k
        | .ok (val, locals₁) =>
          writePlaceWithLocalTy localTy locals₁ ⟨dstId, resolvedProj⟩ dstTy
            val) := by
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.discriminant rp)) = false := rfl
  dsimp only [evalRefMiriRvalue, Array.toList, evalRvalue]
  rw [h_dst]; dsimp only
  rw [h_pty]; dsimp only
  rw [h_no]
  simp only [Bool.false_eq_true, ite_false]
  dsimp only [toMiriRvalue, toMiriPlace, Miri.Interpreter.evalRvalueIntoPlace,
    Miri.Interpreter.runRvalue, refRvalueHooks, evalRefEnumPlaceToOp,
    Bind.bind, EStateM.bind, Array.toList]
  rw [h_dst]; dsimp only
  rw [h_pty]; dsimp only
  rw [h_res]
  simp only [Bool.false_eq_true, ite_false]
  rw [evalRefPlaceOperand_eq h_p false]
  cases evalPlaceOperand bodyLocals slots p false with
  | error k =>
    dsimp only [mapSlotRes]
    cases k <;> rfl
  | ok res =>
    let ⟨srcTy, sv, slots₁⟩ := res
    dsimp only [mapSlotRes]
    cases srcTy with
    | enum ety =>
      dsimp only
      rw [refEnumAdmitted_eq]
      cases h_adm : enumAdmitted ety with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        rw [miriImmToPayload?_roundtrip]
        dsimp only
        let s₁ : RefRvalueState :=
          ⟨zipRefLocals bodyLocals slots₁, true, some ety⟩
        have h_rd := readDiscriminant_encodeRefEnumTagOp_stateless ety sv s₁
          (refDiscriminantHooks RefRvalueState ety)
          (refDiscriminantHooks_spec RefRvalueState ety) h_adm
        dsimp only at h_rd
        cases h_enc : encodeRefEnumTagOp ety sv with
        | error err =>
          rw [h_enc] at h_rd
          first | dsimp only [Miri.Interpreter.runRvalue, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw, mapStepExcept] at h_rd | change _
          first | dsimp only [Miri.Interpreter.runRvalue, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw, mapStepExcept] | change _
          rw [← h_rd.2]
          cases err with
          | undefinedBehavior _ => rfl
          | stack se => cases se <;> rfl
          | _ => rfl
        | ok miriOp =>
          rw [h_enc] at h_rd
          first | dsimp only [Miri.Interpreter.runRvalue] at h_rd | change _
          first | dsimp only [Miri.Interpreter.runRvalue] | change _
          cases h_m :
              Miri.Interpreter.Discriminant.readDiscriminant
                (refDiscriminantHooks RefRvalueState ety) () miriOp s₁ with
          | error err s₂ =>
            rw [h_m] at h_rd
            dsimp only [mapStepExcept] at h_rd
            rw [← h_rd.2]
            cases err with
            | undefinedBehavior _ => rfl
            | stack se => cases se <;> rfl
            | _ => rfl
          | ok variant s₂ =>
            rw [h_m] at h_rd
            dsimp only [mapStepExcept] at h_rd
            let ⟨hs₂, hv_eq⟩ := h_rd
            subst hs₂
            rw [← hv_eq]
            dsimp only
            cases h_d : MirSemantics.getElem? ety.discriminants variant with
            | none =>
              have h_dfv := discriminantForVariant_cached_none (ts := ts) ety
                variant (zipRefLocals bodyLocals slots₁) h_d
              dsimp only [refRvalueHooks] at h_dfv
              rw [h_dfv]
              rfl
            | some disc =>
              have h_dfv := discriminantForVariant_cached_ok (ts := ts) ety
                variant disc (zipRefLocals bodyLocals slots₁) h_adm h_d
              dsimp only [refRvalueHooks] at h_dfv
              rw [h_dfv]
              dsimp only
              rw [miriImmToPayload?_roundtrip]
              dsimp only [SlotVal.toVal?]
              rw [writeRefPlace_eq h_ty h_canon]
              cases writePlaceWithLocalTy localTy slots₁ ⟨dstId, resolvedProj⟩
                  dstTy (.scalar ⟨ety.discrWidth, ety.discrSigned,
                    truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩) with
              | error k => cases k <;> rfl
              | ok _ => rfl
    | _ => rfl

private theorem evalRefMiriRvalue_ref (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj resolvedMiriProj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (m : Mutability) (rp : RefPlace)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_res : refResolveProjPath ts rlocals (.ty localTy) proj =
      .ok resolvedMiriProj) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.ref m rp)) = .error .unsupported := by
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.ref m rp)) = false := by
    cases m <;> rfl
  dsimp only [evalRefMiriRvalue, Array.toList]
  rw [h_dst]; dsimp only
  rw [h_pty]; dsimp only
  rw [h_no]
  simp only [Bool.false_eq_true, ite_false]
  cases m <;> (
    dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
      refRvalueHooks, Miri.Interpreter.runRvalue, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, Array.toList]
    rw [h_dst]; dsimp only
    rw [h_pty]; dsimp only
    rw [h_res]; rfl)

private theorem evalRefMiriRvalue_addressOf (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj resolvedMiriProj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy) (m : Mutability) (rp : RefPlace)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_res : refResolveProjPath ts rlocals (.ty localTy) proj =
      .ok resolvedMiriProj) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue (.addressOf m rp)) = .error .unsupported := by
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue (.addressOf m rp)) = false := by
    cases m <;> rfl
  dsimp only [evalRefMiriRvalue, Array.toList]
  rw [h_dst]; dsimp only
  rw [h_pty]; dsimp only
  rw [h_no]
  simp only [Bool.false_eq_true, ite_false]
  cases m <;> (
    dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
      refRvalueHooks, Miri.Interpreter.runRvalue, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, Array.toList]
    rw [h_dst]; dsimp only
    rw [h_pty]; dsimp only
    rw [h_res]; rfl)

private theorem evalRefMiriRvalue_unsupported (ts : List MirTy)
    (rlocals : List RefLocalState) (dstId : LocalId)
    (proj resolvedMiriProj : List Miri.MIR.ProjectionElem) (dstSlot : LocalSlot)
    (localTy dstTy : MirTy)
    (h_dst : MirSemantics.getElem? rlocals dstId = some ⟨dstSlot, some localTy⟩)
    (h_pty : refProjectTy? ts localTy proj = some dstTy)
    (h_res : refResolveProjPath ts rlocals (.ty localTy) proj =
      .ok resolvedMiriProj) :
    evalRefMiriRvalue ts rlocals ⟨dstId, Array.mk proj⟩
        (toMiriRvalue .unsupported) = .error .unsupported := by
  have h_no : refAssignHasUnsupportedOverlap ⟨dstId, Array.mk proj⟩ dstTy
      (toMiriRvalue .unsupported) = false := rfl
  dsimp only [evalRefMiriRvalue, Array.toList]
  rw [h_dst]; dsimp only
  rw [h_pty]; dsimp only
  rw [h_no]
  simp only [Bool.false_eq_true, ite_false]
  dsimp only [toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
    refRvalueHooks, Miri.Interpreter.runRvalue, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.pure, Array.toList]
  rw [h_dst]; dsimp only
  rw [h_pty]; dsimp only
  rw [h_res]; rfl

theorem evalRefMiriRvalue_eq {ts bodyLocals : List MirTy}
    {slots : List LocalSlot} {rdst : RefPlace} {dst : Place}
    {rrv : RefRvalue} {rv : Rvalue}
    (h_len : slots.length = bodyLocals.length)
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
              match resolveProjPath bodyLocals slots (.ty localTy)
                  dst.projection with
              | .error k => .error k
              | .ok resolvedProj =>
                let resolvedDst : Place := ⟨dst.localId, resolvedProj⟩
                match rv with
                | .aggregate kind ops =>
                  writeAggregate bodyLocals localTy slots resolvedDst dstTy
                    kind ops
                | _ =>
                  match evalRvalue bodyLocals slots dstTy rv with
                  | .error k => .error k
                  | .ok (val, localsAfterRval) =>
                    writePlaceWithLocalTy localTy localsAfterRval resolvedDst
                      dstTy val) := by
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
    have h_rpt := refProjectTy?_eq (ty := localTy) h_proj
    dsimp only
    cases h_pt : projectTy? localTy dst.projection with
    | none =>
      rw [h_pt] at h_rpt
      dsimp only [evalRefMiriRvalue, Array.toList]
      rw [h_dst]; dsimp only
      rw [h_rpt]; rfl
    | some dstTy =>
      rw [h_pt] at h_rpt
      dsimp only
      have h_ov_eq := refAssignHasUnsupportedOverlap_eq dstTy h_pl h_dec
      rw [h_tp] at h_ov_eq
      cases h_ov : assignHasUnsupportedOverlap dst dstTy rv with
      | true =>
        rw [h_ov] at h_ov_eq
        dsimp only [evalRefMiriRvalue, Array.toList]
        rw [h_dst]; dsimp only
        rw [h_rpt]; dsimp only
        rw [h_ov_eq]; rfl
      | false =>
        rw [h_ov] at h_ov_eq
        simp only [Bool.false_eq_true, ite_false]
        have h_res_eq := refResolveProjPath_eq (bodyLocals := bodyLocals)
          (slots := slots) h_proj (.ty localTy)
        dsimp only [placeTyToRefPlaceTy] at h_res_eq
        cases h_rp : resolveProjPath bodyLocals slots (.ty localTy)
            dst.projection with
        | error k =>
          rw [h_rp] at h_res_eq
          exact evalRefMiriRvalue_resolve_err ts _ dst.localId _ dstSlot localTy
            dstTy (toMiriRvalue rrv) k h_dst h_rpt h_ov_eq h_res_eq
        | ok resolvedProj =>
          rw [h_rp] at h_res_eq
          let ⟨resolvedMiriProj, h_res, _, h_canon⟩ := h_res_eq
          dsimp only
          cases rrv with
          | use rop =>
            dsimp only [decodeRvalue, optMap] at h_dec
            cases h_op : decodeOperand ts rop with
            | none => rw [h_op] at h_dec; cases h_dec
            | some op =>
              rw [h_op] at h_dec
              injection h_dec with h_eq
              subst h_eq
              rw [evalRefMiriRvalue_use ts _ dst.localId _ resolvedMiriProj
                dstSlot localTy dstTy rop h_dst h_rpt h_ov_eq h_res]
              dsimp only [evalRvalue]
              rw [evalRefMiriOperandToSlot_eq h_op]
              cases evalOperandToSlot bodyLocals slots op with
              | error _ => rfl
              | ok res =>
                let ⟨srcTy, sv, slots₁⟩ := res
                dsimp only [mapSlotRes]
                cases MirTy.beq srcTy dstTy with
                | false => rfl
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                  cases sv.toVal? with
                  | none => rfl
                  | some v => exact writeRefPlace_eq h_ty h_canon
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
                rw [evalRefMiriRvalue_binaryOp ts _ dst.localId _
                  resolvedMiriProj dstSlot localTy dstTy op lhs rhs h_dst h_rpt
                  h_res]
                dsimp only [evalRvalue]
                rw [evalRefMiriOperandToSlot_eq h_l]
                dsimp only [evalPrimitiveOperand]
                cases evalOperandToSlot bodyLocals slots l' with
                | error _ => rfl
                | ok resL =>
                  let ⟨lTy, lSv, slots₁⟩ := resL
                  dsimp only [mapSlotRes]
                  rw [readRefPrimitiveSlot_eq]
                  cases isPrimitiveReadableTy lTy with
                  | false => rfl
                  | true =>
                    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
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
                        cases isPrimitiveReadableTy rTy with
                        | false => rfl
                        | true =>
                          simp only [Bool.not_true, Bool.false_eq_true,
                            ite_false]
                          cases rSv.toVal? with
                          | none => rfl
                          | some rVal =>
                            dsimp only
                            rw [evalRefBinOp_eq]
                            cases evalBinOp op lVal rVal with
                            | error _ => rfl
                            | ok v => exact writeRefPlace_eq h_ty h_canon
          | unaryOp op rop =>
            dsimp only [decodeRvalue, optMap] at h_dec
            cases h_op : decodeOperand ts rop with
            | none => rw [h_op] at h_dec; cases h_dec
            | some op' =>
              rw [h_op] at h_dec
              injection h_dec with h_eq
              subst h_eq
              rw [evalRefMiriRvalue_unaryOp ts _ dst.localId _ resolvedMiriProj
                dstSlot localTy dstTy op rop h_dst h_rpt h_res]
              dsimp only [evalRvalue, evalPrimitiveOperand]
              rw [evalRefMiriOperandToSlot_eq h_op]
              cases evalOperandToSlot bodyLocals slots op' with
              | error _ => rfl
              | ok res =>
                let ⟨ty, sv, slots₁⟩ := res
                dsimp only [mapSlotRes]
                rw [readRefPrimitiveSlot_eq]
                cases isPrimitiveReadableTy ty with
                | false => rfl
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                  cases sv.toVal? with
                  | none => rfl
                  | some v =>
                    dsimp only
                    rw [evalRefUnOp_eq]
                    cases evalUnOp op v with
                    | error _ => rfl
                    | ok u => exact writeRefPlace_eq h_ty h_canon
          | discriminant rp =>
            dsimp only [decodeRvalue, optMap] at h_dec
            cases h_p : decodePlace ts rp with
            | none => rw [h_p] at h_dec; cases h_dec
            | some p =>
              rw [h_p] at h_dec
              injection h_dec with h_eq
              subst h_eq
              exact evalRefMiriRvalue_discriminant_eq h_ty h_dst h_rpt h_res
                h_canon h_p
          | ref m rp =>
            dsimp only [decodeRvalue, optMap] at h_dec
            cases h_p : decodePlace ts rp with
            | none => rw [h_p] at h_dec; cases h_dec
            | some _ =>
              rw [h_p] at h_dec
              injection h_dec with h_eq
              subst h_eq
              exact evalRefMiriRvalue_ref ts _ dst.localId _ resolvedMiriProj
                dstSlot localTy dstTy m rp h_dst h_rpt h_res
          | addressOf m rp =>
            dsimp only [decodeRvalue, optMap] at h_dec
            cases h_p : decodePlace ts rp with
            | none => rw [h_p] at h_dec; cases h_dec
            | some _ =>
              rw [h_p] at h_dec
              injection h_dec with h_eq
              subst h_eq
              exact evalRefMiriRvalue_addressOf ts _ dst.localId _
                resolvedMiriProj dstSlot localTy dstTy m rp h_dst h_rpt h_res
          | aggregate rkind rops =>
            dsimp only [decodeRvalue, optMap2] at h_dec
            cases h_k : decodeAggregateKind ts rkind with
            | none => rw [h_k] at h_dec; cases h_dec
            | some kind =>
              cases h_ops : mapOption (decodeOperand ts) rops with
              | none => rw [h_k, h_ops] at h_dec; cases h_dec
              | some ops =>
                rw [h_k, h_ops] at h_dec
                injection h_dec with h_eq
                subst h_eq
                exact evalRefMiriRvalue_aggregate_eq h_ty h_dst h_rpt h_res
                  h_canon h_k h_ops h_ov_eq
          | repeat_ rop count =>
            dsimp only [decodeRvalue, optMap] at h_dec
            cases h_op : decodeOperand ts rop with
            | none => rw [h_op] at h_dec; cases h_dec
            | some op' =>
              rw [h_op] at h_dec
              injection h_dec with h_eq
              subst h_eq
              rw [evalRefMiriRvalue_repeat ts _ dst.localId _ resolvedMiriProj
                dstSlot localTy dstTy rop count h_dst h_rpt h_ov_eq h_res]
              dsimp only [evalRefRepeatExpected, evalRvalue]
              cases dstTy with
              | bool | int _ _ | unit | never | adtStruct _ | enum _ | tuple _
              | ref _ _ | rawPtr _ _ | unsupported => rfl
              | array elemTy len =>
                dsimp only
                cases (!Nat.beq count len || !Nat.blt len (Nat.pow 2 64)) with
                | true => rfl
                | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  rw [evalRefMiriOperandToSlot_eq h_op]
                  cases evalOperandToSlot bodyLocals slots op' with
                  | error _ => rfl
                  | ok res =>
                    let ⟨srcTy, sv, slots₁⟩ := res
                    dsimp only [mapSlotRes]
                    cases MirTy.beq srcTy elemTy with
                    | false => rfl
                    | true =>
                      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                      cases Nat.beq count 0 with
                      | true =>
                        simp only [ite_true]
                        exact writeRefPlace_eq h_ty h_canon
                      | false =>
                        simp only [Bool.false_eq_true, ite_false]
                        cases sv.toVal? with
                        | none => rfl
                        | some v =>
                          dsimp only
                          rw [refReplicateVal_eq]
                          exact writeRefPlace_eq h_ty h_canon
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
                rw [evalRefMiriRvalue_cast ts _ dst.localId _ resolvedMiriProj
                  dstSlot localTy dstTy kind rop tyId h_dst h_rpt h_res]
                dsimp only [evalRvalue, evalPrimitiveOperand]
                rw [evalRefMiriOperandToSlot_eq h_op]
                cases evalOperandToSlot bodyLocals slots op' with
                | error _ => rfl
                | ok res =>
                  let ⟨srcTy, sv, slots₁⟩ := res
                  dsimp only [mapSlotRes]
                  rw [readRefPrimitiveSlot_eq]
                  cases isPrimitiveReadableTy srcTy with
                  | false => rfl
                  | true =>
                    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
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
                        cases MirTy.beq castTy dstTy with
                        | false => rfl
                        | true =>
                          simp only [Bool.not_true, Bool.false_eq_true,
                            ite_false]
                          rw [evalRefMiriIntToIntCast_eq]
                          cases evalIntToIntCast v castTy with
                          | error _ => rfl
                          | ok res₂ => exact writeRefPlace_eq h_ty h_canon
          | unsupported =>
            injection h_dec with h_eq
            subst h_eq
            exact evalRefMiriRvalue_unsupported ts _ dst.localId _
              resolvedMiriProj dstSlot localTy dstTy h_dst h_rpt h_res

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
  Miri.Interpreter.StepState RefCallProv Miri.Interpreter.LocalLayout Unit
    RefStepMachine

private abbrev RefMiriFrame :=
  Miri.Interpreter.Frame RefCallProv Miri.Interpreter.LocalLayout Unit

private noncomputable def refSentinelMiriFrame : RefMiriFrame :=
  mkSingleLocalMiriFrame
    (.dead : Miri.Interpreter.LocalValue RefCallProv) false

private theorem list_dropLast_append_singleton {α : Type} (xs : List α)
    (x : α) : (xs ++ [x]).dropLast = xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      dsimp only [List.cons_append, List.dropLast]
      rw [← List.cons_append, ih]

private theorem array_back?_append_singleton {α : Type} (xs : List α) (x : α) :
    (Array.mk (xs ++ [x])).back? = some x := by
  dsimp only [Array.back?]
  rw [← Array.getElem?_toList]
  dsimp only [Array.size, Array.toList]
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.getElem?_append_right (Nat.le_refl xs.length), Nat.sub_self]
  rfl

private theorem array_pop_append_singleton {α : Type} (xs : List α) (x : α) :
    (Array.mk (xs ++ [x])).pop = Array.mk xs := by
  apply Array.toList_inj.1
  rw [Array.toList_pop]
  exact list_dropLast_append_singleton xs x

private theorem array_push_mk {α : Type} (xs : List α) (x : α) :
    (Array.mk xs).push x = Array.mk (xs ++ [x]) := by
  apply Array.toList_inj.1
  rw [Array.toList_push]

private theorem array_isEmpty_append_singleton {α : Type} (xs : List α)
    (x : α) : (Array.mk (xs ++ [x])).isEmpty = false := by
  cases xs <;> rfl

private theorem stack_currentFrame?_append (xs : List RefMiriFrame)
    (top : RefMiriFrame) :
    (⟨Array.mk (xs ++ [top])⟩ :
      Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout
        Unit).currentFrame? = some top :=
  array_back?_append_singleton xs top

private theorem stack_currentFrame?_cons_append (x : RefMiriFrame)
    (xs : List RefMiriFrame) (top : RefMiriFrame) :
    (⟨Array.mk (x :: (xs ++ [top]))⟩ :
      Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout
        Unit).currentFrame? = some top := by
  rw [← List.cons_append]
  exact stack_currentFrame?_append (x :: xs) top

private theorem stack_popFrame_append (xs : List RefMiriFrame)
    (top : RefMiriFrame) :
    (⟨Array.mk (xs ++ [top])⟩ :
      Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout
        Unit).popFrame = .ok (⟨Array.mk xs⟩, top) := by
  dsimp only [Miri.Interpreter.Stack.popFrame, bind, Except.bind, pure,
    Except.pure]
  rw [array_back?_append_singleton, array_pop_append_singleton]

private theorem stack_popFrame_cons_append (x : RefMiriFrame)
    (xs : List RefMiriFrame) (top : RefMiriFrame) :
    (⟨Array.mk (x :: (xs ++ [top]))⟩ :
      Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout
        Unit).popFrame = .ok (⟨Array.mk (x :: xs)⟩, top) := by
  rw [← List.cons_append]
  exact stack_popFrame_append (x :: xs) top

private theorem stack_frameIndex_append (xs : List RefMiriFrame)
    (top : RefMiriFrame) :
    (⟨Array.mk (xs ++ [top])⟩ :
      Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout
        Unit).frameIndex = .ok xs.length := by
  dsimp only [Miri.Interpreter.Stack.frameIndex, bind, Except.bind, pure,
    Except.pure]
  rw [array_isEmpty_append_singleton]
  simp only [Bool.false_eq_true, ite_false]
  change Except.ok ((xs ++ [top]).length - 1) = .ok xs.length
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel]

private theorem stack_pushFrame_goto (xs : List RefMiriFrame)
    (top newFrame : RefMiriFrame) (t : Option BasicBlockId)
    (u : Miri.MIR.UnwindAction)
    (h_cont : newFrame.returnContinuation = .goto t u) :
    (⟨Array.mk (xs ++ [top])⟩ :
      Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout
        Unit).pushFrame newFrame =
      .ok ⟨Array.mk ((xs ++ [top]) ++ [newFrame])⟩ := by
  dsimp only [Miri.Interpreter.Stack.pushFrame, bind, Except.bind, pure,
    Except.pure]
  rw [array_isEmpty_append_singleton, h_cont, array_push_mk]
  rfl

private theorem setLocation_append (xs : List RefMiriFrame)
    (top : RefMiriFrame) (m : RefStepMachine)
    (loc : Miri.Interpreter.FrameLocation) :
    Miri.Interpreter.ControlFlow.setLocation
        ({ stack := ⟨Array.mk (xs ++ [top])⟩, machine := m } : RefStepState)
        loc =
      ({ stack := ⟨Array.mk (xs ++ [{ top with location := loc }])⟩
         machine := m }, .ok ()) := by
  dsimp only [Miri.Interpreter.ControlFlow.setLocation]
  rw [stack_currentFrame?_append]
  dsimp only
  rw [array_pop_append_singleton, array_push_mk]

private theorem setLocation_cons_append (x : RefMiriFrame)
    (xs : List RefMiriFrame) (top : RefMiriFrame) (m : RefStepMachine)
    (loc : Miri.Interpreter.FrameLocation) :
    Miri.Interpreter.ControlFlow.setLocation
        ({ stack := ⟨Array.mk (x :: (xs ++ [top]))⟩, machine := m } :
          RefStepState)
        loc =
      ({ stack := ⟨Array.mk ((x :: xs) ++ [{ top with location := loc }])⟩
         machine := m }, .ok ()) := by
  rw [← List.cons_append]
  exact setLocation_append (x :: xs) top m loc

private theorem goToBlock_append (xs : List RefMiriFrame)
    (top : RefMiriFrame) (m : RefStepMachine) (target : BasicBlockId) :
    Miri.Interpreter.ControlFlow.goToBlock target
        ({ stack := ⟨Array.mk (xs ++ [top])⟩, machine := m } : RefStepState) =
      ({ stack := ⟨Array.mk (xs ++ [{ top with location := .mir ⟨target, 0⟩ }])⟩
         machine := m }, .ok ()) :=
  setLocation_append xs top m (.mir ⟨target, 0⟩)

private theorem goToBlock_cons_append (x : RefMiriFrame)
    (xs : List RefMiriFrame) (top : RefMiriFrame) (m : RefStepMachine)
    (target : BasicBlockId) :
    Miri.Interpreter.ControlFlow.goToBlock target
        ({ stack := ⟨Array.mk (x :: (xs ++ [top]))⟩, machine := m } :
          RefStepState) =
      ({ stack :=
           ⟨Array.mk ((x :: xs) ++ [{ top with location := .mir ⟨target, 0⟩ }])⟩
         machine := m }, .ok ()) :=
  setLocation_cons_append x xs top m (.mir ⟨target, 0⟩)

private theorem liftFrames_eq_of_framesSimInv {p : Program}
    {fs : List FrameState} {rfs : List RefFrameState}
    (h : FramesSimInv p fs rfs) :
    liftFrames p fs = rfs := by
  induction fs generalizing rfs with
  | nil =>
    cases rfs with
    | nil => rfl
    | cons _ _ => cases h
  | cons f rest ih =>
    cases rfs with
    | nil => cases h
    | cons rf rrest =>
      let ⟨⟨body, h_body, _, h_rf⟩, h_rest⟩ := h
      dsimp only [liftFrames]
      rw [h_body, ← h_rf, ih h_rest]

private theorem framesSimInv_length_eq {p : Program}
    {fs : List FrameState} {rfs : List RefFrameState}
    (h : FramesSimInv p fs rfs) :
    rfs.length = fs.length := by
  induction fs generalizing rfs with
  | nil =>
    cases rfs with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ rest ih =>
    cases rfs with
    | nil => cases h
    | cons _ rrest =>
      dsimp only [List.length_cons]
      rw [ih h.2]

private theorem list_any_append {α : Type} (p : α → Bool) (xs ys : List α) :
    (xs ++ ys).any p = (xs.any p || ys.any p) := by
  induction xs with
  | nil => simp only [List.nil_append, List.any_nil, Bool.false_or]
  | cons x rest ih =>
    simp only [List.cons_append, List.any_cons, ih, Bool.or_assoc]

private theorem list_any_reverse {α : Type} (p : α → Bool) (xs : List α) :
    xs.reverse.any p = xs.any p := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.reverse_cons, list_any_append, ih, List.any_cons, List.any_cons,
      List.any_nil, Bool.or_false, Bool.or_comm]

private theorem framesSimInv_any_isCallerSentinel {p : Program}
    {fs : List FrameState} {rfs : List RefFrameState}
    (h : FramesSimInv p fs rfs) :
    rfs.reverse.any (fun f => f.isCallerSentinel) = false := by
  rw [list_any_reverse]
  induction fs generalizing rfs with
  | nil =>
    cases rfs with
    | nil => rfl
    | cons _ _ => cases h
  | cons f rest ih =>
    cases rfs with
    | nil => cases h
    | cons rf rrest =>
      let ⟨⟨body, _, _, h_rf⟩, h_rest⟩ := h
      rw [List.any_cons, h_rf]
      dsimp only [liftFrame, Bool.false_or]
      exact ih h_rest

private theorem evalRefStatement_of_ok (rp : RefProg)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) (stmt : RefStatementKind)
    (top' : RefFrameState)
    (h_ev : Miri.Interpreter.Step.evalStatement
        (refStepHooksFor rp callerMem) ()
        (toMiriStatementForDispatch stmt)
        (mkRefStmtStepState rframe rcallers
          (toMiriStatementForDispatch stmt)) =
      ({ mkRefStmtStepState rframe rcallers
            (toMiriStatementForDispatch stmt) with
          machine := { frames := top' :: rcallers } }, .ok ())) :
    evalRefStatement rp rframe rcallers callerMem stmt =
      .step {
        frames := ({
          top' with
          stmtIdx := rframe.stmtIdx + 1
        } :: rcallers).reverse
        callerMem
      } := by
  let st₀ := mkRefStmtStepState rframe rcallers
    (toMiriStatementForDispatch stmt)
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock false with
      statements := Array.mk [toMiriStatementForDispatch stmt] }
  let fr : RefMiriFrame :=
    { mkSingleLocalMiriFrame
        (.dead : Miri.Interpreter.LocalValue RefCallProv) false with
      body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
      location := .mir ⟨0, 0⟩ }
  have h_cf : st₀.stack.currentFrame? = some fr := rfl
  have h_loc : fr.location = .mir ⟨0, 0⟩ := rfl
  have h_bb : fr.body.basicBlocks[0]? = some blk := rfl
  have h_st : blk.statements[0]? = some (toMiriStatementForDispatch stmt) := rfl
  have h_step :
      Miri.Interpreter.Step.step (refStepHooksFor rp callerMem) () st₀ =
        ({ st₀ with
          stack := ⟨Array.mk [{ fr with location := .mir ⟨0, 1⟩ }]⟩
          machine := { frames := top' :: rcallers } }, .ok true) := by
    unfold Miri.Interpreter.Step.step
    rw [h_cf]; dsimp only
    rw [h_loc]; dsimp only
    rw [h_bb]; dsimp only
    rw [h_st]; dsimp only
    rw [h_ev]; rfl
  unfold evalRefStatement
  rw [h_step]
  rfl

private theorem evalRefStatement_of_err (rp : RefProg)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) (stmt : RefStatementKind) (st₁ : RefStepState)
    (err : Miri.Interpreter.StepError)
    (h_ev : Miri.Interpreter.Step.evalStatement
        (refStepHooksFor rp callerMem) ()
        (toMiriStatementForDispatch stmt)
        (mkRefStmtStepState rframe rcallers
          (toMiriStatementForDispatch stmt)) =
      (st₁, .error err)) :
    evalRefStatement rp rframe rcallers callerMem stmt =
      match err with
      | .undefinedBehavior _ => .fault .undefined
      | _ => .fault .unsupported := by
  let st₀ := mkRefStmtStepState rframe rcallers
    (toMiriStatementForDispatch stmt)
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock false with
      statements := Array.mk [toMiriStatementForDispatch stmt] }
  let fr : RefMiriFrame :=
    { mkSingleLocalMiriFrame
        (.dead : Miri.Interpreter.LocalValue RefCallProv) false with
      body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
      location := .mir ⟨0, 0⟩ }
  have h_cf : st₀.stack.currentFrame? = some fr := rfl
  have h_loc : fr.location = .mir ⟨0, 0⟩ := rfl
  have h_bb : fr.body.basicBlocks[0]? = some blk := rfl
  have h_st : blk.statements[0]? = some (toMiriStatementForDispatch stmt) := rfl
  have h_step :
      Miri.Interpreter.Step.step (refStepHooksFor rp callerMem) () st₀ =
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

private theorem evalRefStatement_nop (rp : RefProg)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) :
    evalRefStatement rp rframe rcallers callerMem .nop =
      .step {
        frames := ({ rframe with stmtIdx := rframe.stmtIdx + 1 } ::
          rcallers).reverse
        callerMem
      } :=
  evalRefStatement_of_ok rp rframe rcallers callerMem .nop rframe rfl

private theorem evalRefStatement_unsupported (rp : RefProg)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) :
    evalRefStatement rp rframe rcallers callerMem .unsupported =
      .fault .unsupported :=
  evalRefStatement_of_err rp rframe rcallers callerMem .unsupported _ _ rfl

private theorem evalRefStatement_storageLive (rp : RefProg)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) (localId : LocalId) :
    evalRefStatement rp rframe rcallers callerMem (.storageLive localId) =
      match MirSemantics.getElem? rframe.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? rframe.locals localId
            ⟨liveUninitSlot localTy, some localTy⟩ with
        | some rlocals' =>
          .step {
            frames := ({
              rframe with
              stmtIdx := rframe.stmtIdx + 1
              locals := rlocals'
            } :: rcallers).reverse
            callerMem
          }
        | none => .fault .unsupported
      | _ => .fault .unsupported := by
  have h_sl :
      Miri.Interpreter.Step.evalStatement (refStepHooksFor rp callerMem) ()
          (toMiriStatementForDispatch (.storageLive localId))
          (mkRefStmtStepState rframe rcallers
            (toMiriStatementForDispatch (.storageLive localId))) =
        let st₀ := mkRefStmtStepState rframe rcallers
          (toMiriStatementForDispatch (.storageLive localId))
        match MirSemantics.getElem? rframe.locals localId with
        | some ⟨_, some localTy⟩ =>
          match MirSemantics.setElem? rframe.locals localId
              ⟨refLiveUninitSlot localTy, some localTy⟩ with
          | some rlocals' =>
            ({ st₀ with machine :=
                { frames := { rframe with locals := rlocals' } :: rcallers } },
              .ok ())
          | none =>
            (st₀, .error (.unsupported "storageLive local out of bounds"))
        | _ =>
          (st₀,
            .error (.unsupported "storageLive missing cached layout")) := rfl
  cases h_get : MirSemantics.getElem? rframe.locals localId with
  | none =>
    rw [h_get] at h_sl
    exact evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_sl
  | some rloc =>
    cases rloc with
    | mk slot optTy =>
      cases optTy with
      | none =>
        rw [h_get] at h_sl
        exact evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_sl
      | some localTy =>
        dsimp only
        rw [h_get] at h_sl
        dsimp only at h_sl
        rw [refLiveUninitSlot_eq] at h_sl
        cases h_set : MirSemantics.setElem? rframe.locals localId
            ⟨liveUninitSlot localTy, some localTy⟩ with
        | none =>
          rw [h_set] at h_sl
          exact evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_sl
        | some rlocals' =>
          rw [h_set] at h_sl
          exact evalRefStatement_of_ok rp rframe rcallers callerMem _ _ h_sl

private theorem evalRefStatement_storageDead_zero (rp : RefProg)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) (localId : LocalId)
    (h0 : Nat.beq localId 0 = true) :
    evalRefStatement rp rframe rcallers callerMem (.storageDead localId) =
      .fault .unsupported := by
  cases localId with
  | zero =>
    exact evalRefStatement_of_err rp rframe rcallers callerMem
      (.storageDead 0) _ _ rfl
  | succ _ => cases h0

private theorem evalRefStatement_storageDead_nonzero (rp : RefProg)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) (localId : LocalId)
    (h0 : Nat.beq localId 0 = false) :
    evalRefStatement rp rframe rcallers callerMem (.storageDead localId) =
      match MirSemantics.getElem? rframe.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? rframe.locals localId
            ⟨.dead, some localTy⟩ with
        | some rlocals' =>
          .step {
            frames := ({
              rframe with
              stmtIdx := rframe.stmtIdx + 1
              locals := rlocals'
            } :: rcallers).reverse
            callerMem
          }
        | none => .fault .unsupported
      | _ => .fault .unsupported := by
  cases localId with
  | zero => cases h0
  | succ n =>
    have h_sd :
        Miri.Interpreter.Step.evalStatement (refStepHooksFor rp callerMem) ()
            (toMiriStatementForDispatch (.storageDead (n + 1)))
            (mkRefStmtStepState rframe rcallers
              (toMiriStatementForDispatch (.storageDead (n + 1)))) =
          let st₀ := mkRefStmtStepState rframe rcallers
            (toMiriStatementForDispatch (.storageDead (n + 1)))
          match MirSemantics.getElem? rframe.locals (n + 1) with
          | some ⟨_, some localTy⟩ =>
            match MirSemantics.setElem? rframe.locals (n + 1)
                ⟨.dead, some localTy⟩ with
            | some rlocals' =>
              ({ st₀ with machine :=
                  { frames :=
                      { rframe with locals := rlocals' } :: rcallers } },
                .ok ())
            | none =>
              (st₀, .error (.unsupported "storageDead local out of bounds"))
          | _ =>
            (st₀, .error (.unsupported "storageDead missing cached layout")) :=
      rfl
    cases h_get : MirSemantics.getElem? rframe.locals (n + 1) with
    | none =>
      rw [h_get] at h_sd
      exact evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_sd
    | some rloc =>
      cases rloc with
      | mk slot optTy =>
        cases optTy with
        | none =>
          rw [h_get] at h_sd
          exact evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_sd
        | some localTy =>
          dsimp only
          rw [h_get] at h_sd
          dsimp only at h_sd
          cases h_set : MirSemantics.setElem? rframe.locals (n + 1)
              ⟨.dead, some localTy⟩ with
          | none =>
            rw [h_set] at h_sd
            exact evalRefStatement_of_err rp rframe rcallers callerMem _ _ _
              h_sd
          | some rlocals' =>
            rw [h_set] at h_sd
            exact evalRefStatement_of_ok rp rframe rcallers callerMem _ _ h_sd

private theorem evalRefStatement_assign (rp : RefProg)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) (dst : RefPlace) (rvalue : RefRvalue) :
    evalRefStatement rp rframe rcallers callerMem (.assign dst rvalue) =
      match evalRefMiriRvalue rp.types rframe.locals (toMiriPlace dst)
          (toMiriRvalue rvalue) with
      | .error k => .fault k
      | .ok rlocalsAfterWrite =>
        .step {
          frames := ({
            rframe with
            stmtIdx := rframe.stmtIdx + 1
            locals := rlocalsAfterWrite
          } :: rcallers).reverse
          callerMem
        } := by
  have h_as :
      Miri.Interpreter.Step.evalStatement (refStepHooksFor rp callerMem) ()
          (toMiriStatementForDispatch (.assign dst rvalue))
          (mkRefStmtStepState rframe rcallers
            (toMiriStatementForDispatch (.assign dst rvalue))) =
        let st₀ := mkRefStmtStepState rframe rcallers
          (toMiriStatementForDispatch (.assign dst rvalue))
        match evalRefMiriRvalue rp.types rframe.locals (toMiriPlace dst)
            (toMiriRvalue rvalue) with
        | .error k => (st₀, .error (faultToStepError k))
        | .ok rlocalsAfterWrite =>
          ({ st₀ with machine :=
              { frames :=
                  { rframe with locals := rlocalsAfterWrite } :: rcallers } },
            .ok ()) := rfl
  cases h_rv : evalRefMiriRvalue rp.types rframe.locals (toMiriPlace dst)
      (toMiriRvalue rvalue) with
  | error k =>
    rw [h_rv] at h_as
    dsimp only at h_as
    rw [evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_as]
    cases k <;> rfl
  | ok rlocalsAfterWrite =>
    rw [h_rv] at h_as
    dsimp only at h_as
    exact evalRefStatement_of_ok rp rframe rcallers callerMem _ _ h_as

private theorem evalRefStatement_setDiscriminant (rp : RefProg)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (callerMem : CallerMemory) (rpl : RefPlace) (variantIdx : Nat) :
    evalRefStatement rp rframe rcallers callerMem
        (.setDiscriminant rpl variantIdx) =
      let place := toMiriPlace rpl
      match MirSemantics.getElem? rframe.locals place.localId with
      | some ⟨_, some localTy⟩ =>
        match refProjectTy? rp.types localTy place.projection.toList with
        | none => .fault .unsupported
        | some dstTy =>
          match refResolveProjPath rp.types rframe.locals (.ty localTy)
              place.projection.toList with
          | .error k => .fault k
          | .ok resolvedProj =>
            match evalRefSetDiscriminant rframe.locals
                ⟨place.localId, resolvedProj, .ty dstTy⟩ variantIdx with
            | .error k => .fault k
            | .ok rlocalsAfterWrite =>
              .step {
                frames := ({
                  rframe with
                  stmtIdx := rframe.stmtIdx + 1
                  locals := rlocalsAfterWrite
                } :: rcallers).reverse
                callerMem
              }
      | _ => .fault .unsupported := by
  let stmt := RefStatementKind.setDiscriminant rpl variantIdx
  let st₀ := mkRefStmtStepState rframe rcallers
    (toMiriStatementForDispatch stmt)
  let place := toMiriPlace rpl
  have h_ev :
      Miri.Interpreter.Step.evalStatement (refStepHooksFor rp callerMem) ()
          (toMiriStatementForDispatch stmt) st₀ =
        match MirSemantics.getElem? rframe.locals place.localId with
        | some ⟨_, some localTy⟩ =>
          match refProjectTy? rp.types localTy place.projection.toList with
          | none => (st₀, .error (.unsupported "ill-typed SetDiscriminant place"))
          | some dstTy =>
            match refResolveProjPath rp.types rframe.locals (.ty localTy)
                place.projection.toList with
            | .error k => (st₀, .error (faultToStepError k))
            | .ok resolvedProj =>
              match evalRefSetDiscriminant rframe.locals
                  ⟨place.localId, resolvedProj, .ty dstTy⟩ variantIdx with
              | .error k => (st₀, .error (faultToStepError k))
              | .ok rlocalsAfterWrite =>
                ({ st₀ with machine :=
                    { st₀.machine with frames :=
                        { rframe with locals := rlocalsAfterWrite } ::
                          rcallers } },
                  .ok ())
        | _ => (st₀, .error (.unsupported "missing SetDiscriminant local")) := by
    dsimp only [Miri.Interpreter.Step.evalStatement, toMiriStatementForDispatch,
      refStepHooksFor, mkRefStmtStepState, mkRefStepStateWith, stmt, st₀, place]
    cases MirSemantics.getElem? rframe.locals (toMiriPlace rpl).localId with
    | none => rfl
    | some rloc =>
      cases rloc with
      | mk slot optTy =>
        cases optTy with
        | none => rfl
        | some localTy =>
          dsimp only
          cases refProjectTy? rp.types localTy
              (toMiriPlace rpl).projection.toList with
          | none => rfl
          | some dstTy =>
            dsimp only
            cases refResolveProjPath rp.types rframe.locals (.ty localTy)
                (toMiriPlace rpl).projection.toList with
            | error _ => rfl
            | ok resolvedProj =>
              dsimp only
              cases evalRefSetDiscriminant rframe.locals
                  ⟨(toMiriPlace rpl).localId, resolvedProj, .ty dstTy⟩
                  variantIdx <;> rfl
  first | dsimp only [stmt, place] at h_ev | change _
  first | dsimp only [stmt, place] | change _
  cases h_get : MirSemantics.getElem? rframe.locals (toMiriPlace rpl).localId with
  | none =>
    rw [h_get] at h_ev
    rw [evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_ev]
  | some rloc =>
    cases rloc with
    | mk slot optTy =>
      cases optTy with
      | none =>
        rw [h_get] at h_ev
        rw [evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_ev]
      | some localTy =>
        dsimp only
        rw [h_get] at h_ev
        dsimp only at h_ev
        cases h_pt :
            refProjectTy? rp.types localTy (toMiriPlace rpl).projection.toList with
        | none =>
          rw [h_pt] at h_ev
          rw [evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_ev]
        | some dstTy =>
          dsimp only
          rw [h_pt] at h_ev
          dsimp only at h_ev
          cases h_res : refResolveProjPath rp.types rframe.locals (.ty localTy)
              (toMiriPlace rpl).projection.toList with
          | error k =>
            rw [h_res] at h_ev
            dsimp only at h_ev
            rw [evalRefStatement_of_err rp rframe rcallers callerMem _ _ _ h_ev]
            cases k <;> rfl
          | ok resolvedProj =>
            dsimp only
            rw [h_res] at h_ev
            dsimp only at h_ev
            cases h_sd : evalRefSetDiscriminant rframe.locals
                ⟨(toMiriPlace rpl).localId, resolvedProj, .ty dstTy⟩
                variantIdx with
            | error k =>
              rw [h_sd] at h_ev
              dsimp only at h_ev
              rw [evalRefStatement_of_err rp rframe rcallers callerMem _ _ _
                h_ev]
              cases k <;> rfl
            | ok rlocalsAfterWrite =>
              rw [h_sd] at h_ev
              dsimp only at h_ev
              exact evalRefStatement_of_ok rp rframe rcallers callerMem _ _
                h_ev

theorem evalRefStatement_eq {rp : RefProg} {p : Program} {body : Body}
    {f : FrameState} {callers : List FrameState}
    {rcallers : List RefFrameState} {callerMem : CallerMemory}
    {rstmt : RefStatementKind} {stmt : StatementKind}
    (h_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_len : f.locals.length = body.locals.length)
    (h_callers : FramesSimInv p callers rcallers)
    (h_dec : decodeStmt rp.types rstmt = some stmt) :
    evalRefStatement rp (liftFrame body.locals f) rcallers callerMem rstmt =
      mapStepRes p (evalStatement body f callers callerMem stmt) := by
  have h_lc := liftFrames_eq_of_framesSimInv h_callers
  cases rstmt with
  | nop =>
    injection h_dec with h_eq
    subst h_eq
    rw [evalRefStatement_nop]
    dsimp only [evalStatement, mapStepRes, liftFrames]
    rw [h_body, h_lc]
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
        dsimp only [mapStepRes, liftFrames]
        rw [h_body, h_lc]
        rfl
  | storageDead localId =>
    injection h_dec with h_eq
    subst h_eq
    dsimp only [evalStatement]
    cases h0 : Nat.beq localId 0
    · rw [evalRefStatement_storageDead_nonzero _ _ _ _ _ h0]
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
        simp only [Bool.false_eq_true, ite_false]
        dsimp only [mapStepRes, liftFrames]
        rw [h_body, h_lc]
        rfl
    · rw [evalRefStatement_storageDead_zero _ _ _ _ _ h0]
      rfl
  | setDiscriminant rpl variantIdx =>
    dsimp only [decodeStmt, optMap] at h_dec
    cases h_pl : decodePlace rp.types rpl with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some pl =>
      rw [h_pl] at h_dec
      injection h_dec with h_eq
      subst h_eq
      let ⟨h_id, h_proj⟩ := decodePlace_proj_inv h_pl
      rw [evalRefStatement_setDiscriminant]
      dsimp only [evalStatement, liftFrame, toMiriPlace, Array.toList]
      rw [h_id]
      cases h_ty : MirSemantics.getElem? body.locals pl.localId with
      | none =>
        rw [getElem?_zipRefLocals_none_left h_ty]
        rfl
      | some localTy =>
        let ⟨slot, h_sl⟩ := getElem?_some_of_length_eq h_len.symm h_ty
        rw [getElem?_zipRefLocals_some h_ty h_sl]
        dsimp only
        rw [refProjectTy?_eq h_proj]
        cases projectTy? localTy pl.projection with
        | none => rfl
        | some dstTy =>
          dsimp only
          have h_res_eq := refResolveProjPath_eq (bodyLocals := body.locals)
            (slots := f.locals) h_proj (.ty localTy)
          dsimp only [placeTyToRefPlaceTy] at h_res_eq
          cases h_rp : resolveProjPath body.locals f.locals (.ty localTy)
              pl.projection with
          | error k =>
            rw [h_rp] at h_res_eq
            rw [h_res_eq]
            rfl
          | ok resolvedProj =>
            rw [h_rp] at h_res_eq
            let ⟨resolvedMiriProj, h_res, _, h_canon⟩ := h_res_eq
            rw [h_res]
            dsimp only
            rw [evalRefSetDiscriminant_eq variantIdx h_ty h_canon]
            cases evalSetDiscriminantResolved localTy f.locals
                ⟨pl.localId, resolvedProj⟩ dstTy variantIdx with
            | error _ => rfl
            | ok localsAfterWrite =>
              dsimp only [mapSlotsRes, mapStepRes, liftFrames]
              rw [h_body, h_lc]
              rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt, optMap2] at h_dec
    cases h_pl : decodePlace rp.types rdst with
    | none => rw [h_pl] at h_dec; cases h_dec
    | some dst =>
      cases h_rv : decodeRvalue rp.types rrv with
      | none => rw [h_pl, h_rv] at h_dec; cases h_dec
      | some rv =>
        rw [h_pl, h_rv] at h_dec
        injection h_dec with h_eq
        subst h_eq
        rw [evalRefStatement_assign]
        dsimp only [evalStatement, liftFrame]
        rw [evalRefMiriRvalue_eq h_len h_pl h_rv]
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
              simp only [Bool.false_eq_true, ite_false]
              cases resolveProjPath body.locals f.locals (.ty localTy)
                  dst.projection with
              | error _ => rfl
              | ok resolvedProj =>
                dsimp only
                cases rv with
                | aggregate kind ops =>
                  dsimp only
                  cases writeAggregate body.locals localTy f.locals
                      ⟨dst.localId, resolvedProj⟩ dstTy kind ops with
                  | error _ => rfl
                  | ok localsAfterWrite =>
                    dsimp only [mapSlotsRes, mapStepRes, liftFrames]
                    rw [h_body, h_lc]
                    rfl
                | use _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _
                | ref _ _ | addressOf _ _ | cast _ _ _ | repeat_ _ _
                | unsupported =>
                  cases evalRvalue body.locals f.locals dstTy _ with
                  | error _ => rfl
                  | ok res =>
                    cases res with
                    | mk val localsAfterRval =>
                      dsimp only
                      cases writePlaceWithLocalTy localTy localsAfterRval
                          ⟨dst.localId, resolvedProj⟩ dstTy val with
                      | error _ => rfl
                      | ok localsAfterWrite =>
                        dsimp only [mapSlotsRes, mapStepRes, liftFrames]
                        rw [h_body, h_lc]
                        rfl
  | unsupported =>
    injection h_dec with h_eq
    subst h_eq
    exact evalRefStatement_unsupported rp _ rcallers callerMem

private theorem step_term_eq (rp : RefProg) (callerMem : CallerMemory)
    (rframe : RefFrameState) (rcallers : List RefFrameState)
    (term : Miri.MIR.Terminator) (cleanup : Bool) :
    Miri.Interpreter.Step.step (refStepHooksFor rp callerMem) ()
        (mkRefTermStepState rframe rcallers term cleanup) =
      let r := Miri.Interpreter.ControlFlow.evalTerminator
        (refTerminatorHooksFor rp callerMem) () term
        (mkRefTermStepState rframe rcallers term cleanup)
      (r.1, r.2.map fun _ => true) := by
  let st₀ := mkRefTermStepState rframe rcallers term cleanup
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock cleanup with terminator := term }
  let fr : RefMiriFrame := {
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) cleanup with
    body := { refDummyMirBody cleanup with basicBlocks := Array.mk [blk] }
    bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
      (if rframe.returnCont.isNone then 0 else 1)
    returnContinuation :=
      match rframe.returnCont with
      | none => .goto (some 0) .Continue
      | some c => .goto c.target (toMiriUnwindAction c.unwind)
    location := .mir ⟨0, 1⟩
  }
  let pre := refSentinelMiriFrame :: mkCallerMiriFrames rcallers
  have h_cf : st₀.stack.currentFrame? = some fr :=
    stack_currentFrame?_append pre fr
  unfold Miri.Interpreter.Step.step
  rw [h_cf]
  rfl

private theorem evalRefTerminator_eq_of_term (rp : RefProg)
    (rbb : RefBasicBlock) (rframe : RefFrameState)
    (rcallers : List RefFrameState) (callerMem : CallerMemory) :
    evalRefTerminator rp rbb rframe rcallers callerMem =
      match Miri.Interpreter.ControlFlow.evalTerminator
          (refTerminatorHooksFor rp callerMem) ()
          (toMiriTerminatorForDispatch rbb.terminator)
          (mkRefTermStepState rframe rcallers
            (toMiriTerminatorForDispatch rbb.terminator) rbb.cleanup) with
      | (st', .ok ()) =>
        match st'.machine.terminal with
        | some res => res
        | none =>
          match extractMirLocation? st', st'.machine.frames with
          | some loc, top :: rest =>
            .step {
              frames := ({
                top with
                blockIdx := loc.block
                stmtIdx := loc.statementIndex
              } :: rest).reverse
              callerMem
            }
          | none, _ => drainRefUnwind rp callerMem (rcallers.length + 1) st'
          | _, _ => .fault .unsupported
      | (_, .error (.undefinedBehavior _)) => .fault .undefined
      | (_, _) => .fault .unsupported := by
  unfold evalRefTerminator
  rw [step_term_eq]
  cases Miri.Interpreter.ControlFlow.evalTerminator
      (refTerminatorHooksFor rp callerMem) ()
      (toMiriTerminatorForDispatch rbb.terminator)
      (mkRefTermStepState rframe rcallers
        (toMiriTerminatorForDispatch rbb.terminator) rbb.cleanup) with
  | mk st' res =>
    cases res with
    | ok u => cases u; rfl
    | error e => cases e <;> rfl

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
  | setDiscriminant rpl _ =>
    dsimp only [decodeStmt, optMap] at h
    cases h₁ : decodePlace ts rpl with
    | none => rw [h₁] at h; cases h
    | some _ =>
      rw [h₁] at h
      injection h with h_eq
      subst h_eq
      rfl
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
  | setDiscriminant rpl _ =>
    dsimp only [decodeStmt, optMap] at h
    cases h₁ : decodePlace ts rpl with
    | none => rw [h₁] at h; cases h
    | some _ =>
      rw [h₁] at h
      injection h with h_eq
      subst h_eq
      rfl
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

theorem refBodyEntryAdmitted_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body}
    (h : decodeBody ts rbody = some body) :
    refBodyEntryAdmitted rbody body.locals = bodyEntryAdmitted body := by
  let ⟨h_arg, _, h_bbs, _, _⟩ := decodeBody_inv h
  unfold refBodyEntryAdmitted bodyEntryAdmitted
  rw [mapOption_isEmpty h_bbs, h_arg, refStorageAnnotationsInBounds_eq h,
    list_all_congr_eq body.locals _ _ refIsSupportedLocalTy_eq]

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

private theorem array_size_cons_append_ne_one {α : Type} (x : α) (xs : List α)
    (y : α) : ((Array.mk ((x :: xs) ++ [y])).size == 1) = false := by
  dsimp only [Array.size]
  rw [List.cons_append, List.length_cons, List.length_append,
    List.length_singleton]
  cases xs.length <;> rfl

private theorem setElem?_isSome_of_getElem?_some {α : Type} {xs : List α}
    {i : Nat} {x : α} (h : MirSemantics.getElem? xs i = some x) (y : α) :
    ∃ xs', MirSemantics.setElem? xs i y = some xs' := by
  induction xs generalizing i with
  | nil => cases i <;> cases h
  | cons a rest ih =>
    cases i with
    | zero => exact ⟨y :: rest, rfl⟩
    | succ k =>
      let ⟨rest', h_set⟩ := ih h
      exact ⟨a :: rest', by dsimp only [MirSemantics.setElem?]; rw [h_set]⟩

private theorem refCheckPlaceLive_of_deinitPlace {bodyLocals : List MirTy}
    {slots : List LocalSlot} {dstId : LocalId}
    {mps : List Miri.MIR.ProjectionElem} {ps : List ProjectionElem}
    {localTy dstTy : MirTy}
    (h_ty : MirSemantics.getElem? bodyLocals dstId = some localTy)
    (h_canon : CanonProjList mps ps) :
    refCheckPlaceLive (zipRefLocals bodyLocals slots)
        ⟨dstId, mps, .ty dstTy⟩ =
      match deinitPlaceWithLocalTy localTy slots ⟨dstId, ps⟩ dstTy with
      | .ok _ => .ok ()
      | .error k => .error k := by
  unfold refCheckPlaceLive deinitPlaceWithLocalTy
  dsimp only [RefDest.ty?]
  cases h_sl : MirSemantics.getElem? slots dstId with
  | none =>
    rw [getElem?_zipRefLocals_none_right h_sl]
  | some slot =>
    rw [getElem?_zipRefLocals_some h_ty h_sl]
    cases slot with
    | dead => rfl
    | live root =>
      dsimp only
      rw [evalPlaceToOp_sized_live]
      dsimp only
      rw [miriImmToPayload?_roundtrip]
      dsimp only
      have h_wr := refWritePlaceSlotPath?_eq h_canon (.ty localTy) root
        (refUninitSlotVal dstTy)
      dsimp only [placeTyToRefPlaceTy] at h_wr
      rw [h_wr, refUninitSlotVal_eq]
      cases writePlaceSlotPath? (.ty localTy) root ps
          (uninitSlotVal dstTy) with
      | none => rfl
      | some root' =>
        dsimp only
        let ⟨slots', h_set⟩ :=
          setElem?_isSome_of_getElem?_some h_sl (.live root')
        rw [h_set]

private theorem refDeinitPlace_eq {bodyLocals : List MirTy}
    {slots : List LocalSlot} {dstId : LocalId}
    {mps : List Miri.MIR.ProjectionElem} {ps : List ProjectionElem}
    {localTy dstTy : MirTy}
    (h_ty : MirSemantics.getElem? bodyLocals dstId = some localTy)
    (h_canon : CanonProjList mps ps) :
    refDeinitPlace (zipRefLocals bodyLocals slots)
        ⟨dstId, mps, .ty dstTy⟩ =
      mapSlotsRes bodyLocals
        (deinitPlaceWithLocalTy localTy slots ⟨dstId, ps⟩ dstTy) := by
  unfold refDeinitPlace deinitPlaceWithLocalTy
  dsimp only [RefDest.ty?]
  cases h_sl : MirSemantics.getElem? slots dstId with
  | none =>
    rw [getElem?_zipRefLocals_none_right h_sl]
    rfl
  | some slot =>
    rw [getElem?_zipRefLocals_some h_ty h_sl]
    cases slot with
    | dead => rfl
    | live root =>
      dsimp only
      rw [evalPlaceToOp_sized_live]
      dsimp only
      rw [miriImmToPayload?_roundtrip]
      dsimp only
      change writeRefPlaceCommitOpt (zipRefLocals bodyLocals slots)
          (.live root) dstId localTy
          (refWritePlaceSlotPath? (.ty localTy) root mps
            (refUninitSlotVal dstTy)) = _
      have h_wr := refWritePlaceSlotPath?_eq h_canon (.ty localTy) root
        (refUninitSlotVal dstTy)
      dsimp only [placeTyToRefPlaceTy] at h_wr
      rw [h_wr, refUninitSlotVal_eq]
      cases writePlaceSlotPath? (.ty localTy) root ps
          (uninitSlotVal dstTy) with
      | none => rfl
      | some root' =>
        cases h_set :
            MirSemantics.setElem? slots dstId (.live root') with
        | none =>
          dsimp only [writeRefPlaceCommitOpt]
          rw [h_set, setElem?_zipRefLocals_none h_set]
          rfl
        | some slots' =>
          dsimp only [writeRefPlaceCommitOpt]
          rw [h_set, setElem?_zipRefLocals_some h_ty h_set]
          rfl

private theorem unwindFrame_cleanup (callerMem : CallerMemory) (f : FrameState)
    (callers : List FrameState) (blk : BasicBlockId) :
    unwindFrame callerMem f callers (.cleanup blk) =
      jumpToBlock f callers callerMem blk := by
  cases callers <;> rfl

private theorem unwindFrame_unreachable (callerMem : CallerMemory)
    (f : FrameState) (callers : List FrameState) :
    unwindFrame callerMem f callers .unreachable = .fault .undefined := by
  cases callers <;> rfl

private theorem unwindFrame_terminate (callerMem : CallerMemory)
    (f : FrameState) (callers : List FrameState) :
    unwindFrame callerMem f callers .terminate = .fault .unsupported := by
  cases callers <;> rfl

/-- Draining `.unwinding` frames through `Miri.Interpreter.Step.step`
(`returnFromCurrentFrame` + `unwindToBlock`) matches
`unwindFrame ... .continue_` across arbitrary call-stack depths. -/
private theorem drainRefUnwind_eq {rp : RefProg} {p : Program}
    (callerMem : CallerMemory) (fuel : Nat)
    (f : FrameState) (callers : List FrameState)
    (rf : RefFrameState) (rcallers : List RefFrameState)
    (topBody : Miri.MIR.Body) (span : Miri.MIR.SpanRef)
    (h_f : FrameSimInv p f rf)
    (h_cs : FramesSimInv p callers rcallers)
    (h_fuel : callers.length < fuel) :
    drainRefUnwind rp callerMem fuel
      { stack := ⟨Array.mk
          ((refSentinelMiriFrame :: mkCallerMiriFrames rcallers) ++
            [{ mkRefCallerMiriFrame rf with
               body := topBody
               location := .unwinding span }])⟩
        machine := { frames := rf :: rcallers } } =
      mapStepRes p (unwindFrame callerMem f callers .continue_) := by
  induction callers generalizing fuel f rf rcallers topBody span with
  | nil =>
    cases rcallers with
    | cons _ _ => cases h_cs
    | nil =>
      cases fuel with
      | zero => cases h_fuel
      | succ fuel' =>
        let ⟨body, h_body, _, h_rf⟩ := h_f
        subst h_rf
        cases f with
        | mk defId blockIdx stmtIdx locals returnCont =>
          unfold drainRefUnwind Miri.Interpreter.Step.step
          dsimp only [mkCallerMiriFrames, List.nil_append, List.cons_append]
          cases returnCont <;> rfl
  | cons caller rest ih =>
    cases rcallers with
    | nil => cases h_cs
    | cons rcaller rrest =>
      cases fuel with
      | zero => cases h_fuel
      | succ fuel' =>
        let ⟨body, _, _, h_rf⟩ := h_f
        let ⟨h_c_sim, h_rest_sim⟩ := h_cs
        let ⟨cBody, h_cBody, _, h_rcaller⟩ := h_c_sim
        have h_lrest := liftFrames_eq_of_framesSimInv h_rest_sim
        subst h_rf
        cases f with
        | mk defId blockIdx stmtIdx locals returnCont =>
          let f' : FrameState :=
            ⟨defId, blockIdx, stmtIdx, locals, returnCont⟩
          let pre := refSentinelMiriFrame :: mkCallerMiriFrames (rcaller :: rrest)
          let topFr : RefMiriFrame := {
            mkRefCallerMiriFrame (liftFrame body.locals f') with
            body := topBody
            location := .unwinding span
          }
          have h_cf1 :
              (⟨Array.mk (pre ++ [topFr])⟩ :
                Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout
                  Unit).currentFrame? = some topFr :=
            stack_currentFrame?_append pre topFr
          cases returnCont with
          | none =>
            unfold drainRefUnwind Miri.Interpreter.Step.step
            rw [h_cf1]
            dsimp only [refStepHooksFor,
              Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
              refControlHooksFor, Id.run, Bind.bind, Pure.pure]
            rw [h_cf1]
            dsimp only [topFr]
            rw [array_size_cons_append_ne_one refSentinelMiriFrame _ topFr]
            simp only [bne_self_eq_false, Bool.not_true, Bool.true_and,
              Bool.false_eq_true, ite_false]
            rw [stack_popFrame_append pre topFr]
            dsimp only [topFr, mkRefCallerMiriFrame, liftFrame, f', unwindFrame]
            rfl
          | some cont =>
            have h_pre_eq : pre =
                (refSentinelMiriFrame :: mkCallerMiriFrames rrest) ++
                  [mkRefCallerMiriFrame rcaller] := by
              dsimp only [pre, mkCallerMiriFrames]
              rw [List.cons_append]
            have h_bi10 : (Miri.Interpreter.BodyIdentity.ofCanonicalIndex 1 ==
                Miri.Interpreter.BodyIdentity.ofCanonicalIndex 0) = false := rfl
            cases h_uw : cont.unwind with
            | cleanup blk =>
              let st_fin : RefStepState := {
                stack := ⟨Array.mk
                  ((refSentinelMiriFrame :: mkCallerMiriFrames rrest) ++
                    [{ mkRefCallerMiriFrame rcaller with
                       location := .mir ⟨blk, 0⟩ }])⟩
                machine := { frames := rcaller :: rrest }
              }
              have h_step : Miri.Interpreter.Step.step
                  (refStepHooksFor rp callerMem) ()
                  { stack := ⟨Array.mk (pre ++ [topFr])⟩
                    machine := { frames := liftFrame body.locals f' :: rcaller :: rrest } } =
                  (st_fin, .ok true) := by
                unfold Miri.Interpreter.Step.step
                rw [h_cf1]
                dsimp only [refStepHooksFor,
                  Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
                  refControlHooksFor, Id.run, Bind.bind, Pure.pure]
                rw [h_cf1]
                dsimp only [topFr]
                rw [array_size_cons_append_ne_one refSentinelMiriFrame _ topFr]
                simp only [bne_self_eq_false, Bool.not_true, Bool.true_and,
                  Bool.false_eq_true, ite_false]
                rw [stack_popFrame_append pre topFr]
                dsimp only [topFr, mkRefCallerMiriFrame, liftFrame, f',
                  Option.isNone, Miri.Interpreter.ControlFlow.unwindToBlock,
                  refControlHooksFor, Id.run, Bind.bind, Pure.pure]
                simp only [Bool.false_eq_true, ite_false, ite_true]
                rw [h_bi10]
                dsimp only
                rw [h_pre_eq, h_uw]
                dsimp only [toMiriUnwindAction]
                rw [goToBlock_append]
                rfl
              unfold drainRefUnwind
              rw [h_step]
              dsimp only [unwindFrame, f']
              rw [h_uw, unwindFrame_cleanup]
              dsimp only [st_fin, extractMirLocation?, jumpToBlock,
                mapStepRes, liftFrames]
              rw [stack_currentFrame?_append]
              dsimp only
              rw [h_rcaller, h_cBody, h_lrest]
              rfl
            | unreachable =>
              unfold drainRefUnwind Miri.Interpreter.Step.step
              rw [h_cf1]
              dsimp only [refStepHooksFor,
                Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
                refControlHooksFor, Id.run, Bind.bind, Pure.pure]
              rw [h_cf1]
              dsimp only [topFr]
              rw [array_size_cons_append_ne_one refSentinelMiriFrame _ topFr]
              simp only [bne_self_eq_false, Bool.not_true, Bool.true_and,
                Bool.false_eq_true, ite_false]
              rw [stack_popFrame_append pre topFr]
              dsimp only [topFr, mkRefCallerMiriFrame, liftFrame, f',
                unwindFrame, Option.isNone,
                Miri.Interpreter.ControlFlow.unwindToBlock,
                refControlHooksFor, Id.run, Bind.bind, Pure.pure]
              simp only [Bool.false_eq_true, ite_false, ite_true]
              rw [h_bi10]
              dsimp only
              rw [h_pre_eq, h_uw, unwindFrame_unreachable]
              rfl
            | terminate =>
              unfold drainRefUnwind Miri.Interpreter.Step.step
              rw [h_cf1]
              dsimp only [refStepHooksFor,
                Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
                refControlHooksFor, Id.run, Bind.bind, Pure.pure]
              rw [h_cf1]
              dsimp only [topFr]
              rw [array_size_cons_append_ne_one refSentinelMiriFrame _ topFr]
              simp only [bne_self_eq_false, Bool.not_true, Bool.true_and,
                Bool.false_eq_true, ite_false]
              rw [stack_popFrame_append pre topFr]
              dsimp only [topFr, mkRefCallerMiriFrame, liftFrame, f',
                unwindFrame, Option.isNone,
                Miri.Interpreter.ControlFlow.unwindToBlock,
                refControlHooksFor, Id.run, Bind.bind, Pure.pure]
              simp only [Bool.false_eq_true, ite_false, ite_true]
              rw [h_bi10]
              dsimp only
              rw [h_pre_eq, h_uw]
              dsimp only [toMiriUnwindAction]
              rw [stack_currentFrame?_append]
              dsimp only
              rw [setLocation_append, unwindFrame_terminate]
              rfl
            | continue_ =>
              let st_fin : RefStepState := {
                stack := ⟨Array.mk
                  ((refSentinelMiriFrame :: mkCallerMiriFrames rrest) ++
                    [{ mkRefCallerMiriFrame rcaller with
                       location := .unwinding ⟨0⟩ }])⟩
                machine := { frames := rcaller :: rrest }
              }
              have h_step : Miri.Interpreter.Step.step
                  (refStepHooksFor rp callerMem) ()
                  { stack := ⟨Array.mk (pre ++ [topFr])⟩
                    machine := { frames := liftFrame body.locals f' :: rcaller :: rrest } } =
                  (st_fin, .ok true) := by
                unfold Miri.Interpreter.Step.step
                rw [h_cf1]
                dsimp only [refStepHooksFor,
                  Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
                  refControlHooksFor, Id.run, Bind.bind, Pure.pure]
                rw [h_cf1]
                dsimp only [topFr]
                rw [array_size_cons_append_ne_one refSentinelMiriFrame _ topFr]
                simp only [bne_self_eq_false, Bool.not_true, Bool.true_and,
                  Bool.false_eq_true, ite_false]
                rw [stack_popFrame_append pre topFr]
                dsimp only [topFr, mkRefCallerMiriFrame, liftFrame, f',
                  Option.isNone, Miri.Interpreter.ControlFlow.unwindToBlock,
                  refControlHooksFor, Id.run, Bind.bind, Pure.pure]
                simp only [Bool.false_eq_true, ite_false, ite_true]
                rw [h_bi10]
                dsimp only
                rw [h_pre_eq, h_uw]
                dsimp only [toMiriUnwindAction]
                rw [stack_currentFrame?_append]
                dsimp only
                rw [setLocation_append]
                rfl
              unfold drainRefUnwind
              rw [h_step]
              dsimp only [unwindFrame, f']
              rw [h_uw]
              dsimp only [st_fin, extractMirLocation?]
              rw [stack_currentFrame?_append]
              dsimp only
              exact ih fuel' caller rcaller rrest
                (mkRefCallerMiriFrame rcaller).body ⟨0⟩
                h_c_sim h_rest_sim (Nat.lt_of_succ_lt_succ h_fuel)

private theorem evalRefTerminator_return_true (rp : RefProg)
    (rbb : RefBasicBlock) (rframe : RefFrameState)
    (rcallers : List RefFrameState) (callerMem : CallerMemory)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = true) :
    evalRefTerminator rp rbb rframe rcallers callerMem = .fault .unsupported := by
  rw [evalRefTerminator_eq_of_term, h_rt, h_cl]
  let st₀ := mkRefTermStepState rframe rcallers
    (toMiriTerminatorForDispatch .return_) true
  let pre := refSentinelMiriFrame :: mkCallerMiriFrames rcallers
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock true with terminator := toMiriTerminatorForDispatch .return_ }
  let fr : RefMiriFrame := {
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) true with
    body := { refDummyMirBody true with basicBlocks := Array.mk [blk] }
    bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
      (if rframe.returnCont.isNone then 0 else 1)
    returnContinuation :=
      match rframe.returnCont with
      | none => .goto (some 0) .Continue
      | some c => .goto c.target (toMiriUnwindAction c.unwind)
    location := .mir ⟨0, 1⟩
  }
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
    toMiriTerminatorForDispatch, mkRefTermStepState, Id.run, Bind.bind,
    Pure.pure]
  rw [stack_currentFrame?_append]
  rfl

private theorem returnFromCurrentFrame_false_step {Op : Type}
    {hooks : Miri.Interpreter.ControlHooks RefCallProv
      Miri.Interpreter.LocalLayout Unit RefStepMachine Unit Op}
    {st₀ st₁ : RefStepState} {fr : RefMiriFrame}
    {blk : Miri.MIR.BasicBlock} {val : Op}
    (h_cf : st₀.stack.currentFrame? = some fr)
    (h_loc : fr.location = .mir ⟨0, 1⟩)
    (h_blk : fr.body.basicBlocks[0]? = some blk)
    (h_cl : blk.cleanup = false)
    (h_retOp : hooks.returnOperand () st₀ = (st₀, .ok val))
    (h_pop : hooks.popFrame () st₀ = (st₁, .ok fr)) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks () false st₀ =
      match hooks.copyReturn () val fr.returnPlace st₁ with
      | (st₂, .error e) => (st₂, .error e)
      | (st₂, .ok ()) =>
        match hooks.cleanupFrame () false fr st₂ with
        | (st₃, .error e) => (st₃, .error e)
        | (st₃, .ok .noJump) => (st₃, .ok ())
        | (st₃, .ok .noCleanup) =>
          if !st₃.stack.frames.isEmpty then
            (st₃, .error (.invalidProgram
              "NoCleanup requires empty stack and normal return"))
          else (st₃, .ok ())
        | (st₃, .ok .normal) =>
          match fr.returnContinuation with
          | .goto ret _ => Miri.Interpreter.ControlFlow.returnToBlock ret st₃
          | .stop _ =>
            if !st₃.stack.frames.isEmpty then
              (st₃, .error (.invalidProgram
                "Stop continuation requires normal root return"))
            else (st₃, .ok ()) := by
  cases hooks with
  | mk bodySpan returnOperand popFrame copyReturn cleanupFrame unwindTerminate =>
    dsimp only at h_retOp h_pop
    unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame
    dsimp only [Id.run, Bind.bind, Pure.pure]
    rw [h_cf]
    dsimp only
    rw [h_loc]
    dsimp only
    rw [h_blk]
    dsimp only
    rw [h_cl]
    simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Bool.not_false, ite_true]
    rw [h_retOp]
    dsimp only
    rw [h_pop]
    dsimp only
    cases copyReturn () val fr.returnPlace st₁ with
    | mk st₂ r₂ =>
      cases r₂ with
      | error e => rfl
      | ok u =>
        cases u
        dsimp only
        cases cleanupFrame () false fr st₂ with
        | mk st₃ r₃ =>
          cases r₃ with
          | error e => rfl
          | ok act =>
            cases act with
            | noJump => rfl
            | noCleanup => simp only [Bool.or_false]
            | normal =>
              cases fr.returnContinuation <;> simp only [Bool.false_or]

private theorem evalRefTerminator_return_false {rp : RefProg} {p : Program}
    {body : Body} {rbb : RefBasicBlock} {f : FrameState}
    {callers : List FrameState} {rcallers : List RefFrameState}
    {callerMem : CallerMemory}
    (h_prog : decodeProg rp = some p)
    (h_len : f.locals.length = body.locals.length)
    (h_callers : FramesSimInv p callers rcallers)
    (h_rt : rbb.terminator = .return_) (h_cl : rbb.cleanup = false) :
    evalRefTerminator rp rbb (liftFrame body.locals f) rcallers callerMem =
      mapStepRes p
        (evalTerminator p body
          { statements := [], terminator := .return_, cleanup := false }
          f callers callerMem) := by
  cases f with
  | mk defId blockIdx stmtIdx locals returnCont =>
  let ⟨_, _, _, _, h_bodies⟩ := decodeProg_inv h_prog
  let f : FrameState := ⟨defId, blockIdx, stmtIdx, locals, returnCont⟩
  let rframe := liftFrame body.locals f
  let pre := refSentinelMiriFrame :: mkCallerMiriFrames rcallers
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock false with
      terminator := toMiriTerminatorForDispatch .return_ }
  let mframe : RefMiriFrame := {
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) false with
    body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
    bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
      (if rframe.returnCont.isNone then 0 else 1)
    returnContinuation :=
      match rframe.returnCont with
      | none => .goto (some 0) .Continue
      | some c => .goto c.target (toMiriUnwindAction c.unwind)
    location := .mir ⟨0, 1⟩
  }
  have h_cf0 : (mkRefTermStepState (liftFrame body.locals f) rcallers
      (toMiriTerminatorForDispatch .return_) false).stack.currentFrame? =
      some mframe := by
    dsimp only [mkRefTermStepState, pre, mframe, blk, rframe]
    rw [stack_currentFrame?_append]
    rfl
  have h_blk0' : mframe.body.basicBlocks[0]? = some blk := rfl
  have h_pop : (refControlHooksFor rp callerMem).popFrame ()
      (mkRefTermStepState (liftFrame body.locals f) rcallers
        (toMiriTerminatorForDispatch .return_) false) =
      ({ stack := ⟨Array.mk pre⟩, machine := { frames := rcallers } },
        .ok mframe) := by
    dsimp only [refControlHooksFor,
      mkRefTermStepState, pre, mframe, blk, rframe]
    rw [stack_popFrame_append]
    rfl
  unfold evalTerminator
  dsimp only
  simp only [Bool.false_eq_true, ite_false]
  rw [evalRefTerminator_eq_of_term, h_rt, h_cl]
  have h_kind : (toMiriTerminatorForDispatch .return_).kind = .Return := rfl
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
    refTerminatorHooksFor, Id.run, Bind.bind, Pure.pure]
  rw [h_kind]
  dsimp only
  rw [returnFromCurrentFrame_false_step h_cf0 rfl h_blk0' rfl rfl h_pop]
  dsimp only [refControlHooksFor, mkRefTermStepState, mframe, rframe, f,
    liftFrame, List.head?]
  cases h_sl : MirSemantics.getElem? locals 0 with
  | none =>
    rw [getElem?_zipRefLocals_none_right h_sl]
    rfl
  | some slot =>
    let ⟨ty₀, h_ty₀⟩ := getElem?_some_of_length_eq h_len h_sl
    rw [getElem?_zipRefLocals_some h_ty₀ h_sl]
    cases slot with
    | dead => rfl
    | live sv =>
      dsimp only
      cases sv.toVal? with
      | none => rfl
      | some retVal =>
        dsimp only
        cases returnCont with
        | none =>
          cases callers with
          | nil =>
            cases rcallers with
            | nil => rfl
            | cons _ _ => cases h_callers
          | cons _ _ =>
            cases rcallers with
            | nil => cases h_callers
            | cons _ _ => rfl
        | some cont =>
          cases callers with
          | nil =>
            cases rcallers with
            | nil => rfl
            | cons _ _ => cases h_callers
          | cons caller rest =>
            cases rcallers with
            | nil => cases h_callers
            | cons rcaller rrest =>
              let ⟨⟨cBody, h_cBody, h_clen, h_rcaller⟩, h_rest⟩ := h_callers
              let ⟨rcBody, h_rcBody_get, _⟩ :=
                (mapOption_getElem? h_bodies caller.defId).2 cBody h_cBody
              have h_lrest := liftFrames_eq_of_framesSimInv h_rest
              rw [h_rcaller]
              dsimp only [liftFrame]
              rw [h_rcBody_get, h_cBody]
              dsimp only
              cases h_cty :
                  MirSemantics.getElem? cBody.locals cont.dst.localId with
              | none =>
                rw [getElem?_zipRefLocals_none_left h_cty]
                rfl
              | some localTy =>
                let ⟨cSlot, h_csl⟩ :=
                  getElem?_some_of_length_eq h_clen.symm h_cty
                rw [getElem?_zipRefLocals_some h_cty h_csl]
                dsimp only
                rw [refProjectReturnTy?_eq]
                cases projectTy? localTy cont.dst.projection with
                | none => rfl
                | some dstTy =>
                  dsimp only
                  have h_sr := refResolveStaticReturnProj_eq (.ty localTy)
                    cont.dst.projection
                  dsimp only [placeTyToRefPlaceTy] at h_sr
                  cases h_rs : resolveStaticProjPath (.ty localTy)
                      cont.dst.projection with
                  | error k =>
                    rw [h_rs] at h_sr
                    rw [h_sr]
                    cases k <;> rfl
                  | ok resolvedProj =>
                    rw [h_rs] at h_sr
                    let ⟨resolvedMiriProj, h_rok, h_canon⟩ := h_sr
                    rw [h_rok]
                    dsimp only
                    rw [writeRefPlace_eq h_cty h_canon]
                    cases writePlaceWithLocalTy localTy caller.locals
                        ⟨cont.dst.localId, resolvedProj⟩ dstTy retVal with
                    | error k => cases k <;> rfl
                    | ok callerLocals' =>
                    dsimp only [mapSlotsRes,
                      Miri.Interpreter.ControlFlow.returnToBlock]
                    have h_pre_eq : pre =
                        (refSentinelMiriFrame :: mkCallerMiriFrames rrest) ++
                          [mkRefCallerMiriFrame (liftFrame cBody.locals caller)] := by
                      dsimp only [pre, mkCallerMiriFrames]
                      rw [h_rcaller, List.cons_append]
                    rw [h_pre_eq]
                    simp only [Option.isSome, Bool.false_eq_true, ite_false]
                    cases cont.target with
                    | none => rfl
                    | some nextBb =>
                      dsimp only
                      rw [goToBlock_append]
                      dsimp only [extractMirLocation?, jumpToBlock,
                        mapStepRes, liftFrames]
                      rw [stack_currentFrame?_append, h_cBody, h_lrest]
                      rfl

/-- Multi-frame `UnwindResume`: unwinds out of the current frame from a cleanup
block (draining `.continue_` frames via `drainRefUnwind_eq`) and fails closed
outside one. -/
private theorem evalRefTerminator_unwindResume {rp : RefProg} {p : Program}
    {body : Body} {rbb : RefBasicBlock} {f : FrameState}
    {callers : List FrameState} {rcallers : List RefFrameState}
    {callerMem : CallerMemory}
    (h_f : FrameSimInv p f (liftFrame body.locals f))
    (h_callers : FramesSimInv p callers rcallers)
    (h_rt : rbb.terminator = .unwindResume) :
    evalRefTerminator rp rbb (liftFrame body.locals f) rcallers callerMem =
      if rbb.cleanup then
        mapStepRes p (unwindFrame callerMem f callers .continue_)
      else
        .fault .unsupported := by
  let rframe := liftFrame body.locals f
  let pre := refSentinelMiriFrame :: mkCallerMiriFrames rcallers
  cases h_cl : rbb.cleanup with
  | false =>
    rw [evalRefTerminator_eq_of_term, h_rt, h_cl]
    let blk : Miri.MIR.BasicBlock :=
      { refDummyMirBlock false with
        terminator := toMiriTerminatorForDispatch .unwindResume }
    let fr : RefMiriFrame := {
      mkSingleLocalMiriFrame
        (.dead : Miri.Interpreter.LocalValue RefCallProv) false with
      body := { refDummyMirBody false with basicBlocks := Array.mk [blk] }
      bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
        (if rframe.returnCont.isNone then 0 else 1)
      returnContinuation :=
        match rframe.returnCont with
        | none => .goto (some 0) .Continue
        | some c => .goto c.target (toMiriUnwindAction c.unwind)
      location := .mir ⟨0, 1⟩
    }
    dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
      Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
      toMiriTerminatorForDispatch, mkRefTermStepState, Id.run, Bind.bind,
      Pure.pure]
    rw [stack_currentFrame?_append]
    rfl
  | true =>
    rw [evalRefTerminator_eq_of_term, h_rt, h_cl]
    let blk : Miri.MIR.BasicBlock :=
      { refDummyMirBlock true with
        terminator := toMiriTerminatorForDispatch .unwindResume }
    let fr : RefMiriFrame := {
      mkSingleLocalMiriFrame
        (.dead : Miri.Interpreter.LocalValue RefCallProv) true with
      body := { refDummyMirBody true with basicBlocks := Array.mk [blk] }
      bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
        (if rframe.returnCont.isNone then 0 else 1)
      returnContinuation :=
        match rframe.returnCont with
        | none => .goto (some 0) .Continue
        | some c => .goto c.target (toMiriUnwindAction c.unwind)
      location := .mir ⟨0, 1⟩
    }
    dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
      Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
      toMiriTerminatorForDispatch, refTerminatorHooksFor, refControlHooksFor,
      mkRefTermStepState, Id.run, Bind.bind, Pure.pure]
    rw [stack_currentFrame?_append]
    dsimp only
    have h_blk0 : ∀ (b : Miri.MIR.BasicBlock), (Array.mk [b])[0]? = some b :=
      fun _ => rfl
    rw [h_blk0]
    dsimp only [refDummyMirBlock]
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [array_size_cons_append_ne_one]
    simp only [Bool.not_true, Bool.true_and, Bool.false_eq_true, ite_false,
      ite_true]
    rw [stack_popFrame_append]
    cases f with
    | mk defId blockIdx stmtIdx locals returnCont =>
      dsimp only [rframe, liftFrame, unwindFrame]
      cases callers with
      | nil =>
        cases rcallers with
        | cons _ _ => cases h_callers
        | nil =>
          cases returnCont <;> rfl
      | cons caller rest =>
        cases rcallers with
        | nil => cases h_callers
        | cons rcaller rrest =>
          let ⟨h_c_sim, h_rest⟩ := h_callers
          let ⟨cBody, h_cBody, _, h_rcaller⟩ := h_c_sim
          have h_lrest := liftFrames_eq_of_framesSimInv h_rest
          cases returnCont with
          | none => rfl
          | some cont =>
            dsimp only [Option.isNone,
              Miri.Interpreter.ControlFlow.unwindToBlock,
              refControlHooksFor, Id.run, Bind.bind, Pure.pure]
            simp only [Bool.false_eq_true, ite_false]
            have h_bi10 : (Miri.Interpreter.BodyIdentity.ofCanonicalIndex 1 ==
                Miri.Interpreter.BodyIdentity.ofCanonicalIndex 0) = false := rfl
            rw [h_bi10]
            dsimp only
            have h_pre_eq :
                mkSingleLocalMiriFrame
                    (.dead : Miri.Interpreter.LocalValue RefCallProv) false ::
                  mkCallerMiriFrames (rcaller :: rrest) =
                (refSentinelMiriFrame :: mkCallerMiriFrames rrest) ++
                  [mkRefCallerMiriFrame rcaller] := by
              dsimp only [refSentinelMiriFrame, mkCallerMiriFrames]
              rw [List.cons_append]
            rw [h_pre_eq]
            dsimp only [unwindFrame]
            cases h_uw : cont.unwind with
            | cleanup blk =>
              dsimp only [toMiriUnwindAction]
              rw [goToBlock_append, unwindFrame_cleanup]
              dsimp only [extractMirLocation?, jumpToBlock, mapStepRes,
                liftFrames]
              rw [stack_currentFrame?_append]
              dsimp only
              rw [h_rcaller, h_cBody, h_lrest]
              rfl
            | unreachable =>
              rw [unwindFrame_unreachable]
              rfl
            | terminate =>
              dsimp only [toMiriUnwindAction]
              rw [stack_currentFrame?_append]
              dsimp only
              rw [setLocation_append, unwindFrame_terminate]
              rfl
            | continue_ =>
              dsimp only [toMiriUnwindAction]
              rw [stack_currentFrame?_append]
              dsimp only
              rw [setLocation_append]
              dsimp only [extractMirLocation?]
              rw [stack_currentFrame?_append]
              dsimp only
              have h_len_r : rrest.length = rest.length :=
                framesSimInv_length_eq h_rest
              have h_fuel : rest.length < (rcaller :: rrest).length + 1 := by
                rw [List.length_cons, h_len_r]
                exact Nat.lt_trans (Nat.lt_succ_self rest.length)
                  (Nat.lt_succ_self (rest.length + 1))
              exact drainRefUnwind_eq (rp := rp) callerMem
                ((rcaller :: rrest).length + 1)
                caller rest rcaller rrest (mkRefCallerMiriFrame rcaller).body
                ⟨0⟩ h_c_sim h_rest h_fuel

/-- The reference check of a translated assert message agrees with
`isOperandFreeAssertKind`. -/
private theorem refIsOperandFreeAssertKind_eq (msg : AssertKind) :
    refIsOperandFreeAssertKind (toMiriAssertKind msg) =
      isOperandFreeAssertKind msg := by
  cases msg with
  | overflow op => cases op <;> rfl
  | _ => rfl

/-- Multi-frame `Assert` lockstep on the reference side. -/
private theorem evalRefTerminator_assert {rp : RefProg} {p : Program}
    {body : Body} {rbb : RefBasicBlock} {f : FrameState}
    {callers : List FrameState} {rcallers : List RefFrameState}
    {callerMem : CallerMemory}
    {rcond : RefOperand} {cond : Operand} {expected : Bool}
    {msg : AssertKind} {target : BasicBlockId} {unwind : UnwindAction}
    (h_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_len : f.locals.length = body.locals.length)
    (h_callers : FramesSimInv p callers rcallers)
    (h_c : decodeOperand rp.types rcond = some cond)
    (h_rt : rbb.terminator = .assert rcond expected msg target unwind) :
    evalRefTerminator rp rbb (liftFrame body.locals f) rcallers callerMem =
      mapStepRes p
        (match evalPrimitiveOperand body.locals f.locals cond with
        | .error k => .fault k
        | .ok (condVal, localsAfterCond) =>
          match condVal with
          | .bool b =>
            if expected == b then
              jumpToBlock { f with locals := localsAfterCond } callers
                callerMem target
            else if !isOperandFreeAssertKind msg then
              .fault .unsupported
            else
              unwindFrame callerMem { f with locals := localsAfterCond }
                callers unwind
          | _ => .fault .unsupported) := by
  have h_lcallers := liftFrames_eq_of_framesSimInv h_callers
  let rframe := liftFrame body.locals f
  let pre := refSentinelMiriFrame :: mkCallerMiriFrames rcallers
  let term := toMiriTerminatorForDispatch rbb.terminator
  let blk : Miri.MIR.BasicBlock :=
    { refDummyMirBlock rbb.cleanup with terminator := term }
  let fr : RefMiriFrame := {
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) rbb.cleanup with
    body := { refDummyMirBody rbb.cleanup with basicBlocks := Array.mk [blk] }
    bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
      (if rframe.returnCont.isNone then 0 else 1)
    returnContinuation :=
      match rframe.returnCont with
      | none => .goto (some 0) .Continue
      | some c => .goto c.target (toMiriUnwindAction c.unwind)
    location := .mir ⟨0, 1⟩
  }
  rw [evalRefTerminator_eq_of_term, h_rt]
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
    toMiriTerminatorForDispatch, refTerminatorHooksFor, mkRefTermStepState,
    Id.run, Bind.bind, Pure.pure, evalPrimitiveOperand, rframe, liftFrame]
  rw [evalRefMiriOperandToSlot_eq h_c]
  cases h_op : evalOperandToSlot body.locals f.locals cond with
  | error k => cases k <;> rfl
  | ok res =>
    let ⟨ty, sv, localsAfterCond⟩ := res
    dsimp only [mapSlotRes]
    rw [readRefPrimitiveSlot_eq]
    cases isPrimitiveReadableTy ty with
    | false => rfl
    | true =>
      dsimp only [Bool.not, ite_false_eq_true]
      cases sv.toVal? with
      | none => rfl
      | some condVal =>
        dsimp only
        cases condVal with
        | bool b =>
          dsimp only
          rw [refIsOperandFreeAssertKind_eq]
          cases (expected == b) with
          | true =>
            simp only [Bool.false_and, Bool.false_or, ite_true]
            rw [goToBlock_append]
            dsimp only [extractMirLocation?, jumpToBlock, mapStepRes,
              liftFrames]
            rw [stack_currentFrame?_append, h_body, h_lcallers]
            rfl
          | false =>
            simp only [Bool.false_and, Bool.false_or, Bool.false_eq_true,
              ite_false]
            cases isOperandFreeAssertKind msg with
            | false => rfl
            | true =>
              simp only [Bool.false_eq_true, ite_false]
              dsimp only [Miri.Interpreter.ControlFlow.unwindToBlock,
                refControlHooksFor, Id.run, Bind.bind, Pure.pure]
              cases unwind with
              | cleanup blk' =>
                dsimp only [toMiriUnwindAction]
                rw [goToBlock_append, unwindFrame_cleanup]
                dsimp only [extractMirLocation?, jumpToBlock,
                  mapStepRes, liftFrames]
                rw [stack_currentFrame?_append, h_body, h_lcallers]
                rfl
              | unreachable =>
                rw [unwindFrame_unreachable]
                rfl
              | terminate =>
                dsimp only [toMiriUnwindAction]
                rw [stack_currentFrame?_append]
                dsimp only
                rw [setLocation_append, unwindFrame_terminate]
                rfl
              | continue_ =>
                dsimp only [toMiriUnwindAction]
                rw [stack_currentFrame?_append]
                dsimp only
                rw [setLocation_append]
                dsimp only [extractMirLocation?]
                rw [stack_currentFrame?_append]
                dsimp only
                have h_len' : localsAfterCond.length = body.locals.length :=
                  (evalOperandToSlot_length h_op).trans h_len
                have h_f' : FrameSimInv p { f with locals := localsAfterCond }
                    (liftFrame body.locals { f with locals := localsAfterCond }) :=
                  ⟨body, h_body, h_len', rfl⟩
                have h_len_c : rcallers.length = callers.length :=
                  framesSimInv_length_eq h_callers
                have h_fuel : callers.length < rcallers.length + 1 := by
                  rw [h_len_c]
                  exact Nat.lt_succ_self callers.length
                exact drainRefUnwind_eq callerMem (rcallers.length + 1)
                  { f with locals := localsAfterCond } callers
                  (liftFrame body.locals { f with locals := localsAfterCond })
                  rcallers _ ⟨0⟩ h_f' h_callers h_fuel
        | scalar _ | unit | structVal _ _ | enumVal _ _ _ | tuple _
        | array _ _ | ptr _ | bytes _ => rfl

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

private theorem switchInt_forIn_scalar {rp : RefProg}
    {callerMem : CallerMemory} (m : RefStepMachine)
    (stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit)
    (sv : ScalarVal) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
        ({ stack := stk, machine := m } : RefStepState),
        otherwise)
      (fun case __s =>
        have __s := __s.snd
        have state := __s.fst
        have target := __s.snd
        match case with
        | Miri.MIR.SwitchTarget.Case bits block =>
          match (refTerminatorHooksFor rp callerMem).compareSwitchCase ()
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
        (some ({ stack := stk, machine := m },
               .error (faultToStepError .unsupported)),
         { stack := stk, machine := m },
         otherwise)
      | .ok target =>
        (none, { stack := stk, machine := m }, target) := by
  induction branches with
  | nil =>
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest ih =>
    cases hd with
    | mk caseBits target =>
      rw [switchInt_forIn_cons
        (cmp := (refTerminatorHooksFor rp callerMem).compareSwitchCase ()
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

private theorem switchInt_forIn_bool {rp : RefProg}
    {callerMem : CallerMemory} (m : RefStepMachine)
    (stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit)
    (b : Bool) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    forIn (m := Id)
      (branches.map (fun b => Miri.MIR.SwitchTarget.Case b.1.toNat b.2))
      ((none : Option (Miri.Interpreter.StepResult RefStepState Unit)),
        ({ stack := stk, machine := m } : RefStepState),
        otherwise)
      (fun case __s =>
        have __s := __s.snd
        have state := __s.fst
        have target := __s.snd
        match case with
        | Miri.MIR.SwitchTarget.Case bits block =>
          match (refTerminatorHooksFor rp callerMem).compareSwitchCase ()
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
        (some ({ stack := stk, machine := m },
               .error (faultToStepError k)),
         { stack := stk, machine := m },
         otherwise)
      | .ok target =>
        (none, { stack := stk, machine := m }, target) := by
  induction branches with
  | nil =>
    rw [List.map_nil, List.forIn_nil]
    rfl
  | cons hd rest ih =>
    cases hd with
    | mk caseBits target =>
      rw [switchInt_forIn_cons
        (cmp := (refTerminatorHooksFor rp callerMem).compareSwitchCase ()
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

private theorem evalRefTerminator_switchInt (rp : RefProg)
    (rbb : RefBasicBlock) (rframe : RefFrameState)
    (rcallers : List RefFrameState) (callerMem : CallerMemory)
    (rdiscr : RefOperand) (targets : SwitchTargets)
    (h_rt : rbb.terminator = .switchInt rdiscr targets) :
    evalRefTerminator rp rbb rframe rcallers callerMem =
      match evalRefMiriOperandToSlot rp.types rframe.locals
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
              frames := ({
                rframe with
                blockIdx := target
                stmtIdx := 0
                locals := rlocalsAfterDiscr
              } :: rcallers).reverse
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
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) rbb.cleanup with
    body := {
      refDummyMirBody rbb.cleanup with
      basicBlocks := Array.mk [{ refDummyMirBlock rbb.cleanup with
        terminator := mirTerm }]
    }
    bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
      (if rframe.returnCont.isNone then 0 else 1)
    returnContinuation :=
      match rframe.returnCont with
      | none => .goto (some 0) .Continue
      | some c => .goto c.target (toMiriUnwindAction c.unwind)
    location := .mir ⟨0, 1⟩
  }
  let pre := refSentinelMiriFrame :: mkCallerMiriFrames rcallers
  let stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout
      Unit := ⟨Array.mk (pre ++ [mframe])⟩
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
    toMiriTerminatorForDispatch, refTerminatorHooksFor,
    mkRefTermStepState, Id.run, Bind.bind, Pure.pure]
  cases evalRefMiriOperandToSlot rp.types rframe.locals (toMiriOperand rdiscr) with
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
            match (refTerminatorHooksFor rp callerMem).compareSwitchCase ()
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
        · rw [switchInt_forIn_scalar]
          cases h_sw : evalSwitchBranches sv.width sv.bits targets.otherwise
              targets.branches with
          | error k =>
            have h_unsup :=
              evalSwitchBranches_error_eq_unsupported _ _ _ _ _ h_sw
            subst h_unsup
            rfl
          | ok target =>
            dsimp only
            rw [goToBlock_append]
            dsimp only [extractMirLocation?]
            rw [stack_currentFrame?_append]
        · intro x s
          cases (refTerminatorHooksFor rp callerMem).compareSwitchCase ()
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
            match (refTerminatorHooksFor rp callerMem).compareSwitchCase ()
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
        · rw [switchInt_forIn_bool]
          cases evalBoolSwitchBranches b targets.otherwise targets.branches with
          | error k => cases k <;> rfl
          | ok target =>
            dsimp only
            rw [goToBlock_append]
            dsimp only [extractMirLocation?]
            rw [stack_currentFrame?_append]
        · intro x s
          cases (refTerminatorHooksFor rp callerMem).compareSwitchCase ()
              (.bool b) x.1.toNat s.snd.fst with
          | mk next comparison =>
            cases comparison with
            | error _ => rfl
            | ok flag => cases flag <;> rfl
      | unit | structVal _ _ | enumVal _ _ _ | tuple _ | array _ _
      | ptr _ | bytes _ => rfl

private theorem eStateM_bind_pure {ε σ α β : Type} (a : α)
    (k : α → EStateM ε σ β) (s : σ) :
    EStateM.bind (EStateM.pure a) k s = k a s := rfl

private theorem eStateM_bind_ok {ε σ α β : Type}
    {m : EStateM ε σ α} {a : α} {s s' : σ}
    (h : m s = .ok a s') (k : α → EStateM ε σ β) :
    EStateM.bind m k s = k a s' := by
  dsimp only [EStateM.bind]
  rw [h]

private theorem eStateM_bind_error {ε σ α β : Type}
    {m : EStateM ε σ α} {e : ε} {s s' : σ}
    (h : m s = .error e s') (k : α → EStateM ε σ β) :
    EStateM.bind m k s = .error e s' := by
  dsimp only [EStateM.bind]
  rw [h]

private theorem eStateM_bind_assoc {ε σ α β γ : Type}
    (m : EStateM ε σ α) (f : α → EStateM ε σ β) (g : β → EStateM ε σ γ)
    (s : σ) :
    EStateM.bind (EStateM.bind m f) g s =
      EStateM.bind m (fun a => EStateM.bind (f a) g) s := by
  dsimp only [EStateM.bind]
  cases m s <;> rfl

private theorem eStateM_bind_congr_left {ε σ α β : Type}
    {m₁ m₂ : EStateM ε σ α} {k : α → EStateM ε σ β} {s : σ}
    (h : m₁ s = m₂ s) :
    EStateM.bind m₁ k s = EStateM.bind m₂ k s := by
  dsimp only [EStateM.bind]
  rw [h]

private theorem callM_bind_ok {α β : Type}
    {m : Miri.Interpreter.CallM RefStepState α}
    {k : α → Miri.Interpreter.CallM RefStepState β}
    {s s' : RefStepState} {a : α}
    {rhs : EStateM.Result Miri.Interpreter.StepError RefStepState β}
    (hm : m s = .ok a s') (hk : k a s' = rhs) :
    EStateM.bind m k s = rhs :=
  (eStateM_bind_ok hm k).trans hk

private def localCallAt {A : Type} (xs : Array A) (j : Nat) (msg : String) :
    Miri.Interpreter.CallM RefStepState A :=
  match xs[j]? with
  | none => throw (.invalidProgram msg)
  | some value => pure value

private theorem cleanup_empty_step {α : Type}
    {c : Miri.Interpreter.CallM RefStepState α →
      Miri.Interpreter.CallM RefStepState α}
    {act : Miri.Interpreter.CallM RefStepState α} {s : RefStepState}
    (h_pt : c act s = c (fun _ => act s) s)
    (h_ok : ∀ val s₁, c (fun _ => .ok val s₁) s = .ok val s₁)
    (h_err : ∀ err s₁, c (fun _ => .error err s₁) s = .error err s₁) :
    c act s = act s := by
  rw [h_pt]
  cases act s with
  | ok val s₁ => exact h_ok val s₁
  | error err s₁ => exact h_err err s₁

private theorem congr_bind_ok {ε σ α β γ : Type}
    {f : EStateM.Result ε σ β → γ}
    {m : EStateM ε σ α} {k : α → EStateM ε σ β}
    {s s' : σ} {a : α} {rhs : γ}
    (hm : m s = .ok a s') (hk : f (k a s') = rhs) :
    f (EStateM.bind m k s) = rhs := by
  rw [eStateM_bind_ok hm]
  exact hk

private theorem congr_bind_cleanup_strip {α β γ : Type}
    {f : EStateM.Result Miri.Interpreter.StepError RefStepState β → γ}
    {c : Miri.Interpreter.CallM RefStepState α →
      Miri.Interpreter.CallM RefStepState α}
    {act : Miri.Interpreter.CallM RefStepState α}
    {k : α → Miri.Interpreter.CallM RefStepState β}
    {s : RefStepState} {rhs : γ}
    (h_pt : c act s = c (fun _ => act s) s)
    (h_ok : ∀ val s₁, c (fun _ => .ok val s₁) s = .ok val s₁)
    (h_err : ∀ err s₁, c (fun _ => .error err s₁) s = .error err s₁)
    (h : f (EStateM.bind act k s) = rhs) :
    f (EStateM.bind (c act) k s) = rhs := by
  rw [eStateM_bind_congr_left (cleanup_empty_step h_pt h_ok h_err)]
  exact h

private def callErrToFault : Miri.Interpreter.StepError → FaultKind
  | .undefinedBehavior _ => .undefined
  | _ => .unsupported

private def RefFnArgMatches (fnArg : Miri.Interpreter.FnArg RefCallProv)
    (pair : MirTy × SlotVal) : Prop :=
  extractRefCallArg? fnArg.copyFnArg = some pair ∧
  fnArg.layout = refSizedLocalLayout ∧
  fnArg.copyFnArg.metadata = .none ∧
  (match fnArg with
   | .Copy _ => True
   | .InPlace _ none => True
   | .InPlace _ (some _) => False)

private def RefFnArgsMatch
    (as : List (Miri.Interpreter.FnArg RefCallProv))
    (ps : List (MirTy × SlotVal)) : Prop :=
  @List.rec (Miri.Interpreter.FnArg RefCallProv)
    (fun _ => List (MirTy × SlotVal) → Prop)
    (fun ps =>
      match ps with
      | [] => True
      | _ :: _ => False)
    (fun a _ ih ps =>
      match ps with
      | [] => False
      | p :: ps' => RefFnArgMatches a p ∧ ih ps')
    as ps

private theorem refFnArgsMatch_append
    {as : List (Miri.Interpreter.FnArg RefCallProv)}
    {ps : List (MirTy × SlotVal)}
    {a : Miri.Interpreter.FnArg RefCallProv} {p : MirTy × SlotVal}
    (h_m : RefFnArgsMatch as ps) (h_a : RefFnArgMatches a p) :
    RefFnArgsMatch (as ++ [a]) (ps ++ [p]) := by
  induction as generalizing ps with
  | nil =>
    cases ps with
    | nil => exact ⟨h_a, trivial⟩
    | cons _ _ => cases h_m
  | cons x xs ih =>
    cases ps with
    | nil => cases h_m
    | cons y ys => exact ⟨h_m.1, ih h_m.2⟩

private theorem refFnArgsMatch_length
    {as : List (Miri.Interpreter.FnArg RefCallProv)}
    {ps : List (MirTy × SlotVal)}
    (h : RefFnArgsMatch as ps) : as.length = ps.length := by
  induction as generalizing ps with
  | nil =>
    cases ps with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ xs ih =>
    cases ps with
    | nil => cases h
    | cons _ ys => exact congrArg Nat.succ (ih h.2)

private theorem refFnArgsMatch_map_extract
    {as : List (Miri.Interpreter.FnArg RefCallProv)}
    {ps : List (MirTy × SlotVal)}
    (h : RefFnArgsMatch as ps) :
    mapOption extractRefCallArg? (as.map Miri.Interpreter.FnArg.copyFnArg) =
      some ps := by
  induction as generalizing ps with
  | nil =>
    cases ps with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ps with
    | nil => cases h
    | cons y ys =>
      dsimp only [List.map, mapOption]
      rw [h.1.1, ih h.2]
      rfl

private theorem list_getElem?_append_middle {α : Type} (pre : List α) (x : α)
    (suf : List α) :
    (pre ++ x :: suf)[pre.length]? = some x := by
  induction pre with
  | nil => rfl
  | cons _ rest ih => exact ih

private theorem array_getElem?_mk_eq_list {α : Type} (xs : List α) (i : Nat) :
    (Array.mk xs)[i]? = xs[i]? :=
  (Array.getElem?_toList (xs := Array.mk xs) (i := i)).symm

private theorem list_getElem?_eq_mirGetElem? {α : Type} (xs : List α)
    (i : Nat) : xs[i]? = MirSemantics.getElem? xs i := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

private theorem refFnArgsMatch_getElem?
    {as : List (Miri.Interpreter.FnArg RefCallProv)}
    {ps : List (MirTy × SlotVal)}
    (h : RefFnArgsMatch as ps) :
    ∀ (i : Nat) (p : MirTy × SlotVal),
      ps[i]? = some p →
      ∃ a, as[i]? = some a ∧ RefFnArgMatches a p := by
  induction as generalizing ps with
  | nil =>
    cases ps with
    | nil => intro i _ hi; cases i <;> cases hi
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ps with
    | nil => cases h
    | cons y ys =>
      intro i p hi
      cases i with
      | zero =>
        injection hi with h_eq
        subst h_eq
        exact ⟨x, rfl, h.1⟩
      | succ k => exact ih h.2 k p hi

private theorem array_replicate_getElem?_lt {α : Type} (n : Nat) (x : α)
    (i : Nat) (h : i < n) :
    (Array.replicate n x)[i]? = some x := by
  rw [Array.getElem?_eq_getElem (by rw [Array.size_replicate]; exact h)]
  rw [Array.getElem_replicate]

private theorem nat_succ_beq_self_false (n : Nat) :
    ((n + 1 == n) : Bool) = false :=
  decide_eq_false (Nat.succ_ne_self n)

private theorem nat_range_size_zero_step1 (n : Nat) :
    HDiv.hDiv (n - 0 + 1 - 1) 1 = n := by
  rw [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]

private theorem mirGetElem?_drop {α : Type} (xs : List α) (k i : Nat) :
    MirSemantics.getElem? (xs.drop k) i = MirSemantics.getElem? xs (k + i) := by
  induction k generalizing xs with
  | zero =>
    rw [List.drop_zero, Nat.zero_add]
  | succ m ih =>
    cases xs with
    | nil =>
      rw [List.drop_nil]
      cases i <;> rfl
    | cons x rest =>
      rw [List.drop_succ_cons, ih rest]
      have h_add : m + 1 + i = (m + i) + 1 := by
        rw [Nat.add_assoc, Nat.add_comm 1 i, ← Nat.add_assoc]
      rw [h_add]
      rfl

private theorem list_drop_take_succ_cons {α : Type} (xs : List α)
    (start m : Nat) (x : α)
    (h_get : MirSemantics.getElem? xs (start + 1) = some x) :
    ((xs.drop 1).take (start + (m + 1))).drop start =
      x :: ((xs.drop 1).take (start + (m + 1))).drop (start + 1) := by
  have h_eq : (((xs.drop 1).take (start + (m + 1))).drop start)[0]? = some x := by
    simp only [List.getElem?_drop, Nat.add_zero]
    have h_lt : start < start + (m + 1) :=
      Nat.lt_add_of_pos_right (Nat.succ_pos m)
    rw [List.getElem?_take_of_lt h_lt, List.getElem?_drop, Nat.add_comm 1 start,
      list_getElem?_eq_mirGetElem?]
    exact h_get
  cases h_d : ((xs.drop 1).take (start + (m + 1))).drop start with
  | nil => rw [h_d] at h_eq; cases h_eq
  | cons y ys =>
    rw [h_d] at h_eq
    injection h_eq with h_xy
    subst h_xy
    have h_tail :
        ((xs.drop 1).take (start + (m + 1))).drop (start + 1) = ys := by
      rw [← List.drop_drop, h_d]
      rfl
    rw [h_tail]

private theorem list_drop_take_end_nil {α : Type} (xs : List α) (n : Nat) :
    ((xs.drop 1).take n).drop n = [] := by
  rw [List.drop_eq_nil_iff]
  exact List.length_take_le n (xs.drop 1)

private theorem evalFnCallArgumentAt_eq {rp : RefProg} {body : Body}
    {f : FrameState} {rcallers : List RefFrameState}
    {stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit}
    {ci : Option RefCalleeInit} {rop : RefOperand} {op : Operand}
    (disjoint : Bool) (index : Nat)
    (h_dec : decodeOperand rp.types rop = some op) :
    let st : RefStepState := {
      stack := stk
      machine := { frames := liftFrame body.locals f :: rcallers, calleeInit := ci }
    }
    match evalOperandToSlot body.locals f.locals op with
    | .error k =>
      Miri.Interpreter.Call.evalFnCallArgumentAt (refCallHooks rp) ()
        (toMiriOperand rop) disjoint
        (Miri.Interpreter.OperandPath.argument index) st =
        .error (faultToStepError k) st
    | .ok (ty, sv, locals') =>
      ∃ fnArg : Miri.Interpreter.FnArg RefCallProv,
        Miri.Interpreter.Call.evalFnCallArgumentAt (refCallHooks rp) ()
          (toMiriOperand rop) disjoint
          (Miri.Interpreter.OperandPath.argument index) st =
          .ok fnArg {
            stack := stk
            machine := {
              frames := liftFrame body.locals { f with locals := locals' } :: rcallers
              calleeInit := ci
            }
          } ∧
        RefFnArgMatches fnArg (ty, sv) := by
  intro st
  cases rop with
  | copy rpl =>
    dsimp only [st, toMiriOperand, Miri.Interpreter.Call.evalFnCallArgumentAt,
      bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure,
      refCallHooks, Miri.Interpreter.OperandPath.argument, Array.size,
      List.length, liftFrame]
    have h_op := evalRefMiriOperandToSlot_eq (bodyLocals := body.locals)
      (slots := f.locals) h_dec
    dsimp only [toMiriOperand] at h_op
    rw [h_op]
    cases evalOperandToSlot body.locals f.locals op with
    | error k => rfl
    | ok res =>
      let ⟨ty, sv, locals'⟩ := res
      exact ⟨_, rfl, rfl, rfl, rfl, trivial⟩
  | constant rc =>
    dsimp only [st, toMiriOperand, Miri.Interpreter.Call.evalFnCallArgumentAt,
      bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure,
      refCallHooks, Miri.Interpreter.OperandPath.argument, Array.size,
      List.length, liftFrame]
    have h_op := evalRefMiriOperandToSlot_eq (bodyLocals := body.locals)
      (slots := f.locals) h_dec
    dsimp only [toMiriOperand] at h_op
    rw [h_op]
    cases evalOperandToSlot body.locals f.locals op with
    | error k => rfl
    | ok res =>
      let ⟨ty, sv, locals'⟩ := res
      exact ⟨_, rfl, rfl, rfl, rfl, trivial⟩
  | move rpl =>
    dsimp only [st, toMiriOperand, Miri.Interpreter.Call.evalFnCallArgumentAt,
      Miri.Interpreter.Call.snapshotInPlaceArg,
      bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure,
      refCallHooks, liftFrame]
    have h_op := evalRefMiriOperandToSlot_eq (bodyLocals := body.locals)
      (slots := f.locals) h_dec
    dsimp only [toMiriOperand] at h_op
    rw [h_op]
    cases evalOperandToSlot body.locals f.locals op with
    | error k => rfl
    | ok res =>
      let ⟨ty, sv, locals'⟩ := res
      dsimp only [mapSlotRes]
      cases disjoint with
      | true => exact ⟨_, rfl, rfl, rfl, rfl, trivial⟩
      | false => exact ⟨_, rfl, rfl, rfl, rfl, trivial⟩

private theorem evalCallArgs_forIn_eq {rp : RefProg} {body : Body}
    {rcallers : List RefFrameState}
    {stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit}
    (disjoint : Bool) (allRargs : List RefOperand)
    (stepFn : Nat →
      Array (Miri.Memory.Pointer (Option RefCallProv)) ×
        Array (Miri.Interpreter.FnArg RefCallProv) →
      Miri.Interpreter.CallM RefStepState
        (ForInStep (Array (Miri.Memory.Pointer (Option RefCallProv)) ×
          Array (Miri.Interpreter.FnArg RefCallProv))))
    (h_step : ∀ (index : Nat)
        (acc : Array (Miri.Interpreter.FnArg RefCallProv))
        (arg : Miri.MIR.SpannedOperand) (st : RefStepState),
      (Array.mk (allRargs.map (fun a => (⟨⟨0⟩, toMiriOperand a⟩ :
          Miri.MIR.SpannedOperand))))[index]? = some arg →
      stepFn index ((Array.mk []), acc) st =
        EStateM.bind
          (Miri.Interpreter.Call.evalFnCallArgumentAt (refCallHooks rp) ()
            arg.operand disjoint
            (Miri.Interpreter.OperandPath.argument index))
          (fun fnArg =>
            match fnArg with
            | .InPlace _ (some ⟨.indirect tmpMplace, _⟩) =>
              EStateM.pure (ForInStep.yield ((Array.mk []).push tmpMplace.ptr, acc.push fnArg))
            | .InPlace _ _ =>
              EStateM.pure (ForInStep.yield ((Array.mk []), acc.push fnArg))
            | .Copy _ =>
              EStateM.pure (ForInStep.yield ((Array.mk []), acc.push fnArg))) st)
    (preRargs remRargs : List RefOperand) (remArgs : List Operand)
    (f : FrameState) (acc : Array (Miri.Interpreter.FnArg RefCallProv))
    (accPairs : List (MirTy × SlotVal))
    (h_all : allRargs = preRargs ++ remRargs)
    (h_dec : mapOption (decodeOperand rp.types) remRargs = some remArgs)
    (h_acc : RefFnArgsMatch acc.toList accPairs) :
    let st : RefStepState :=
      { stack := stk, machine := { frames := liftFrame body.locals f :: rcallers } }
    match evalCallArgs body.locals f.locals remArgs with
    | .error k =>
      ∃ st_err,
        forIn (m := Miri.Interpreter.CallM RefStepState)
          (List.range' preRargs.length remRargs.length 1)
          (((Array.mk []) : Array (Miri.Memory.Pointer (Option RefCallProv))), acc)
          stepFn st = .error (faultToStepError k) st_err
    | .ok (remPairs, localsAfter) =>
      ∃ evaluated : Array (Miri.Interpreter.FnArg RefCallProv),
        forIn (m := Miri.Interpreter.CallM RefStepState)
          (List.range' preRargs.length remRargs.length 1)
          (((Array.mk []) : Array (Miri.Memory.Pointer (Option RefCallProv))), acc)
          stepFn st =
          .ok ((Array.mk []), evaluated) {
            stack := stk
            machine := {
              frames := liftFrame body.locals { f with locals := localsAfter } :: rcallers
            }
          } ∧
        RefFnArgsMatch evaluated.toList (accPairs ++ remPairs) := by
  induction remRargs generalizing preRargs remArgs f acc accPairs with
  | nil =>
    dsimp only [mapOption] at h_dec
    injection h_dec with h_rem
    subst h_rem
    dsimp only [List.length, List.range', evalCallArgs]
    rw [List.append_nil]
    refine ⟨acc, ?_, h_acc⟩
    rw [List.forIn_nil]
    rfl
  | cons rop rest ih =>
    dsimp only [mapOption] at h_dec
    cases h_op : decodeOperand rp.types rop with
    | none => rw [h_op] at h_dec; cases h_dec
    | some op =>
      rw [h_op] at h_dec
      cases h_rest : mapOption (decodeOperand rp.types) rest with
      | none => rw [h_rest] at h_dec; cases h_dec
      | some restArgs =>
        rw [h_rest] at h_dec
        injection h_dec with h_rem
        subst h_rem
        dsimp only [List.length, List.range', evalCallArgs]
        rw [List.forIn_cons]
        have h_get :
            (Array.mk (allRargs.map (fun a => (⟨⟨0⟩, toMiriOperand a⟩ :
                Miri.MIR.SpannedOperand))))[preRargs.length]? =
              some ⟨⟨0⟩, toMiriOperand rop⟩ := by
          rw [h_all, List.map_append, List.map_cons, array_getElem?_mk_eq_list]
          have h_len_pre :
              (preRargs.map (fun a => (⟨⟨0⟩, toMiriOperand a⟩ :
                  Miri.MIR.SpannedOperand))).length = preRargs.length :=
            List.length_map _
          rw [← h_len_pre]
          exact list_getElem?_append_middle _ _ _
        dsimp only [bind, Bind.bind, pure, Pure.pure]
        have h_arg := evalFnCallArgumentAt_eq (rp := rp) (body := body)
          (f := f) (rcallers := rcallers) (stk := stk) (ci := none)
          disjoint preRargs.length h_op
        cases h_ev : evalOperandToSlot body.locals f.locals op with
        | error k =>
          rw [h_ev] at h_arg
          have h_step_err :
              stepFn preRargs.length ((Array.mk []), acc)
                { stack := stk, machine := { frames := liftFrame body.locals f :: rcallers } } =
                .error (faultToStepError k)
                  { stack := stk, machine := { frames := liftFrame body.locals f :: rcallers } } := by
            rw [h_step preRargs.length acc ⟨⟨0⟩, toMiriOperand rop⟩ _ h_get]
            exact eStateM_bind_error h_arg _
          exact ⟨_, eStateM_bind_error h_step_err _⟩
        | ok res =>
          let ⟨ty, sv, locals₁⟩ := res
          dsimp only
          rw [h_ev] at h_arg
          let ⟨fnArg, h_fnArg_eq, h_fnArg_m⟩ := h_arg
          have h_yield :
              stepFn preRargs.length ((Array.mk []), acc)
                { stack := stk, machine := { frames := liftFrame body.locals f :: rcallers } } =
                .ok (ForInStep.yield ((Array.mk []), acc.push fnArg)) {
                  stack := stk
                  machine := {
                    frames := liftFrame body.locals { f with locals := locals₁ } :: rcallers
                  }
                } := by
            rw [h_step preRargs.length acc ⟨⟨0⟩, toMiriOperand rop⟩ _ h_get]
            rw [eStateM_bind_ok h_fnArg_eq]
            cases fnArg with
            | Copy _ => rfl
            | InPlace _ snap =>
              cases snap with
              | none => rfl
              | some _ => exact False.elim h_fnArg_m.2.2.2
          have h_all' : allRargs = (preRargs ++ [rop]) ++ rest := by
            rw [List.append_assoc]
            exact h_all
          have h_len' : (preRargs ++ [rop]).length = preRargs.length + 1 := by
            rw [List.length_append, List.length_singleton]
          have h_acc' :
              RefFnArgsMatch (acc.push fnArg).toList (accPairs ++ [(ty, sv)]) := by
            rw [Array.toList_push]
            exact refFnArgsMatch_append h_acc h_fnArg_m
          have h_ih := ih (preRargs ++ [rop]) restArgs { f with locals := locals₁ }
            (acc.push fnArg) (accPairs ++ [(ty, sv)]) h_all' h_rest h_acc'
          rw [h_len'] at h_ih
          cases h_ec : evalCallArgs body.locals locals₁ restArgs with
          | error k =>
            dsimp only
            rw [h_ec] at h_ih
            let ⟨st_err, h_err⟩ := h_ih
            exact ⟨st_err, (eStateM_bind_ok h_yield _).trans h_err⟩
          | ok res₂ =>
            let ⟨tailPairs, locals₂⟩ := res₂
            dsimp only
            rw [h_ec] at h_ih
            let ⟨evaluated, h_ok, h_match⟩ := h_ih
            rw [List.append_assoc] at h_match
            exact ⟨evaluated, (eStateM_bind_ok h_yield _).trans h_ok, h_match⟩

private theorem evalCallArgs_forIn_bind_err {rp : RefProg} {body : Body}
    {f : FrameState} {rcallers : List RefFrameState}
    {stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit}
    {rargs : List RefOperand} {args : List Operand}
    {disjoint : Bool} {k : FaultKind}
    {stepFn : Nat →
      Array (Miri.Memory.Pointer (Option RefCallProv)) ×
        Array (Miri.Interpreter.FnArg RefCallProv) →
      Miri.Interpreter.CallM RefStepState
        (ForInStep (Array (Miri.Memory.Pointer (Option RefCallProv)) ×
          Array (Miri.Interpreter.FnArg RefCallProv)))}
    {β : Type}
    {cont : Array (Miri.Memory.Pointer (Option RefCallProv)) ×
      Array (Miri.Interpreter.FnArg RefCallProv) →
      Miri.Interpreter.CallM RefStepState β}
    (h_step : ∀ (index : Nat)
        (acc : Array (Miri.Interpreter.FnArg RefCallProv))
        (arg : Miri.MIR.SpannedOperand) (st : RefStepState),
      (Array.mk (rargs.map (fun a => (⟨⟨0⟩, toMiriOperand a⟩ :
          Miri.MIR.SpannedOperand))))[index]? = some arg →
      stepFn index ((Array.mk []), acc) st =
        EStateM.bind
          (Miri.Interpreter.Call.evalFnCallArgumentAt (refCallHooks rp) ()
            arg.operand disjoint
            (Miri.Interpreter.OperandPath.argument index))
          (fun fnArg =>
            match fnArg with
            | .InPlace _ (some ⟨.indirect tmpMplace, _⟩) =>
              EStateM.pure (ForInStep.yield ((Array.mk []).push tmpMplace.ptr, acc.push fnArg))
            | .InPlace _ _ =>
              EStateM.pure (ForInStep.yield ((Array.mk []), acc.push fnArg))
            | .Copy _ =>
              EStateM.pure (ForInStep.yield ((Array.mk []), acc.push fnArg))) st)
    (h_dec : mapOption (decodeOperand rp.types) rargs = some args)
    (h_ec : evalCallArgs body.locals f.locals args = .error k) :
    ∃ st_err,
      EStateM.bind
        (forIn (m := Miri.Interpreter.CallM RefStepState)
          (List.range' 0 rargs.length 1)
          (((Array.mk []) : Array (Miri.Memory.Pointer (Option RefCallProv))), (Array.mk []))
          stepFn)
        cont { stack := stk, machine := { frames := liftFrame body.locals f :: rcallers } } =
        .error (faultToStepError k) st_err := by
  have h_loop := evalCallArgs_forIn_eq (rp := rp) (body := body)
    (rcallers := rcallers) (stk := stk) disjoint rargs stepFn h_step
    [] rargs args f (Array.mk []) [] rfl h_dec trivial
  dsimp only [List.length] at h_loop
  rw [h_ec] at h_loop
  let ⟨st_err, h_err⟩ := h_loop
  exact ⟨st_err, eStateM_bind_error h_err cont⟩

private theorem evalCallArgs_forIn_bind_ok {rp : RefProg} {body : Body}
    {f : FrameState} {rcallers : List RefFrameState}
    {stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit}
    {rargs : List RefOperand} {args : List Operand}
    {disjoint : Bool} {argPairs : List (MirTy × SlotVal)}
    {localsAfter : List LocalSlot}
    {stepFn : Nat →
      Array (Miri.Memory.Pointer (Option RefCallProv)) ×
        Array (Miri.Interpreter.FnArg RefCallProv) →
      Miri.Interpreter.CallM RefStepState
        (ForInStep (Array (Miri.Memory.Pointer (Option RefCallProv)) ×
          Array (Miri.Interpreter.FnArg RefCallProv)))}
    {β : Type}
    {cont : Array (Miri.Memory.Pointer (Option RefCallProv)) ×
      Array (Miri.Interpreter.FnArg RefCallProv) →
      Miri.Interpreter.CallM RefStepState β}
    {P : Array (Miri.Interpreter.FnArg RefCallProv) →
      EStateM.Result Miri.Interpreter.StepError RefStepState β → Prop}
    (h_step : ∀ (index : Nat)
        (acc : Array (Miri.Interpreter.FnArg RefCallProv))
        (arg : Miri.MIR.SpannedOperand) (st : RefStepState),
      (Array.mk (rargs.map (fun a => (⟨⟨0⟩, toMiriOperand a⟩ :
          Miri.MIR.SpannedOperand))))[index]? = some arg →
      stepFn index ((Array.mk []), acc) st =
        EStateM.bind
          (Miri.Interpreter.Call.evalFnCallArgumentAt (refCallHooks rp) ()
            arg.operand disjoint
            (Miri.Interpreter.OperandPath.argument index))
          (fun fnArg =>
            match fnArg with
            | .InPlace _ (some ⟨.indirect tmpMplace, _⟩) =>
              EStateM.pure (ForInStep.yield ((Array.mk []).push tmpMplace.ptr, acc.push fnArg))
            | .InPlace _ _ =>
              EStateM.pure (ForInStep.yield ((Array.mk []), acc.push fnArg))
            | .Copy _ =>
              EStateM.pure (ForInStep.yield ((Array.mk []), acc.push fnArg))) st)
    (h_dec : mapOption (decodeOperand rp.types) rargs = some args)
    (h_ec : evalCallArgs body.locals f.locals args = .ok (argPairs, localsAfter))
    (h_cont : ∀ evaluated,
      RefFnArgsMatch evaluated.toList argPairs →
      P evaluated
        (cont ((Array.mk []), evaluated) {
          stack := stk
          machine := {
            frames :=
              liftFrame body.locals { f with locals := localsAfter } :: rcallers
          }
        })) :
    ∃ evaluated : Array (Miri.Interpreter.FnArg RefCallProv),
      P evaluated
        (EStateM.bind
          (forIn (m := Miri.Interpreter.CallM RefStepState)
            (List.range' 0 rargs.length 1)
            (((Array.mk []) : Array (Miri.Memory.Pointer (Option RefCallProv))), (Array.mk []))
            stepFn)
          cont { stack := stk, machine := { frames := liftFrame body.locals f :: rcallers } }) ∧
      RefFnArgsMatch evaluated.toList argPairs := by
  have h_loop := evalCallArgs_forIn_eq (rp := rp) (body := body)
    (rcallers := rcallers) (stk := stk) disjoint rargs stepFn h_step
    [] rargs args f (Array.mk []) [] rfl h_dec trivial
  dsimp only [List.length] at h_loop
  rw [h_ec] at h_loop
  let ⟨evaluated, h_ok, h_m⟩ := h_loop
  rw [List.nil_append] at h_m
  refine ⟨evaluated, ?_, h_m⟩
  rw [eStateM_bind_ok h_ok cont]
  exact h_cont evaluated h_m

private theorem evalCalleeAndArgs_eq {rp : RefProg} {body : Body}
    {f : FrameState} {rcallers : List RefFrameState}
    {stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit}
    {rargs : List RefOperand} {args : List Operand}
    (encodedId : Nat) (dst : Miri.MIR.Place)
    (h_dec : mapOption (decodeOperand rp.types) rargs = some args) :
    let mirArgs : Array Miri.MIR.SpannedOperand :=
      Array.mk (rargs.map (fun a => ⟨⟨0⟩, toMiriOperand a⟩))
    let st : RefStepState :=
      { stack := stk, machine := { frames := liftFrame body.locals f :: rcallers } }
    match evalCallArgs body.locals f.locals args with
    | .error k =>
      ∃ st_err,
        Miri.Interpreter.Call.evalCalleeAndArgs (refCallHooks rp) ()
          (.Constant ⟨⟨0⟩, none, .Val .ZeroSized encodedId⟩) mirArgs dst st =
          .error (faultToStepError k) st_err
    | .ok (argPairs, localsAfter) =>
      let fnInst : Miri.Interpreter.CallInstance :=
        if Nat.beq (Nat.mod encodedId 2) 0 then
          { kind := .Item (Nat.div encodedId 2), args := Array.empty }
        else
          { kind := .Intrinsic (Nat.div encodedId 2), args := Array.empty }
      let fnAbiNat : Nat :=
        match MirSemantics.getElem? rp.bodies (Nat.div encodedId 2) with
        | some rbody => rbody.argumentCount
        | none => 0
      ∃ evaluated : Array (Miri.Interpreter.FnArg RefCallProv),
        Miri.Interpreter.Call.evalCalleeAndArgs (refCallHooks rp) ()
          (.Constant ⟨⟨0⟩, none, .Val .ZeroSized encodedId⟩) mirArgs dst st =
          .ok {
            callee := .Instance fnInst
            args := evaluated
            callerAbi := ()
            fnAbi := some fnAbiNat
            withCallerLocation := false
            tempAllocs := (Array.mk [])
          } {
            stack := stk
            machine := {
              frames :=
                liftFrame body.locals { f with locals := localsAfter } :: rcallers
            }
          } ∧
        RefFnArgsMatch evaluated.toList argPairs := by
  intro mirArgs st
  have h_deinit : (refCallHooks rp).deinitMovedPlace = false := rfl
  have h_evalFn : (refCallHooks rp).evalOperandAt ()
      (Miri.Interpreter.OperandPath.instruction "function")
      (.Constant ⟨⟨0⟩, none, .Val .ZeroSized encodedId⟩) st =
      .ok ⟨.immediate .uninit, { refSizedLocalLayout with ty := encodedId }⟩ st := rfl
  cases h_ec : evalCallArgs body.locals f.locals args with
  | error k =>
    dsimp only
    unfold Miri.Interpreter.Call.evalCalleeAndArgs
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_evalFn, h_deinit]
    simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    dsimp only [Std.Legacy.Range.start, Std.Legacy.Range.size,
      Std.Legacy.Range.step, mirArgs, Array.size]
    rw [List.length_map, nat_range_size_zero_step1]
    refine evalCallArgs_forIn_bind_err
      (disjoint := Miri.Interpreter.Call.moveDefinitelyDisjoint mirArgs dst)
      ?_ h_dec h_ec
    intro index acc arg st' h_get
    dsimp only
    rw [h_get]
    dsimp only
    refine (eStateM_bind_congr_left
      (cleanup_empty_step ?_ ?_ ?_)).trans ?_
    · rfl
    · intro _ _; rfl
    · intro _ _; rfl
    dsimp only [EStateM.bind]
    cases Miri.Interpreter.Call.evalFnCallArgumentAt (refCallHooks rp) ()
        arg.operand (Miri.Interpreter.Call.moveDefinitelyDisjoint mirArgs dst)
        (Miri.Interpreter.OperandPath.argument index) st' with
    | error e s' => rfl
    | ok fnArg s' =>
      cases fnArg with
      | Copy _ => rfl
      | InPlace _ snap =>
        cases snap with
        | none => rfl
        | some op =>
          cases op with
          | mk o _ => cases o <;> rfl
  | ok res =>
    let ⟨argPairs, localsAfter⟩ := res
    dsimp only
    unfold Miri.Interpreter.Call.evalCalleeAndArgs
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_evalFn, h_deinit]
    simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    dsimp only [Std.Legacy.Range.start, Std.Legacy.Range.size,
      Std.Legacy.Range.step, mirArgs, Array.size]
    rw [List.length_map, nat_range_size_zero_step1]
    refine evalCallArgs_forIn_bind_ok
      (disjoint := Miri.Interpreter.Call.moveDefinitelyDisjoint mirArgs dst)
      (P := fun evaluated
        (res : EStateM.Result Miri.Interpreter.StepError RefStepState
          (Miri.Interpreter.EvaluatedCall RefCallProv Unit Unit Nat)) =>
        res = .ok {
          callee := .Instance
            (if Nat.beq (Nat.mod encodedId 2) 0 then
              { kind := .Item (Nat.div encodedId 2), args := Array.empty }
            else
              { kind := .Intrinsic (Nat.div encodedId 2), args := Array.empty })
          args := evaluated
          callerAbi := ()
          fnAbi := some (match MirSemantics.getElem? rp.bodies (Nat.div encodedId 2) with
            | some rbody => rbody.argumentCount
            | none => 0)
          withCallerLocation := false
          tempAllocs := (Array.mk [])
        } {
          stack := stk
          machine := {
            frames :=
              liftFrame body.locals { f with locals := localsAfter } :: rcallers
          }
        })
      ?_ h_dec h_ec ?_
    · intro index acc arg st' h_get
      dsimp only
      rw [h_get]
      dsimp only
      refine (eStateM_bind_congr_left
        (cleanup_empty_step ?_ ?_ ?_)).trans ?_
      · rfl
      · intro _ _; rfl
      · intro _ _; rfl
      dsimp only [EStateM.bind]
      cases Miri.Interpreter.Call.evalFnCallArgumentAt (refCallHooks rp) ()
          arg.operand (Miri.Interpreter.Call.moveDefinitelyDisjoint mirArgs dst)
          (Miri.Interpreter.OperandPath.argument index) st' with
      | error e s' => rfl
      | ok fnArg s' =>
        cases fnArg with
        | Copy _ => rfl
        | InPlace _ snap =>
          cases snap with
          | none => rfl
          | some op =>
            cases op with
            | mk o _ => cases o <;> rfl
    · intro evaluated _
      let st₁ : RefStepState := {
        stack := stk
        machine := {
          frames :=
            liftFrame body.locals { f with locals := localsAfter } :: rcallers
        }
      }
      have h_sig : (refCallHooks rp).functionSignature ()
          { refSizedLocalLayout with ty := encodedId } st₁ = .ok (0, ()) st₁ := rfl
      have h_fk : (refCallHooks rp).functionKind encodedId st₁ =
          .ok (.FnDef encodedId Array.empty) st₁ := rfl
      have h_res : (refCallHooks rp).resolve () encodedId Array.empty st₁ =
          .ok (if Nat.beq (Nat.mod encodedId 2) 0 then
            { kind := .Item (Nat.div encodedId 2), args := Array.empty }
          else
            { kind := .Intrinsic (Nat.div encodedId 2), args := Array.empty }) st₁ := by
        dsimp only [refCallHooks]
        cases Nat.beq (Nat.mod encodedId 2) 0 <;> rfl
      have h_le : decide (0 ≤ evaluated.toList.length) = true :=
        decide_eq_true (Nat.zero_le _)
      refine (cleanup_empty_step ?_ ?_ ?_).trans ?_
      · rfl
      · intro _ _; rfl
      · intro _ _; rfl
      refine callM_bind_ok h_sig ?_
      dsimp only
      rw [h_le]
      refine callM_bind_ok (a := ()) (s' := st₁) rfl ?_
      refine callM_bind_ok h_fk ?_
      dsimp only
      refine callM_bind_ok h_res ?_
      cases Nat.beq (Nat.mod encodedId 2) 0 with
      | true =>
        simp only [ite_true]
        have h_abi : (refCallHooks rp).fnAbiOfInstance ()
            { kind := .Item (Nat.div encodedId 2), args := Array.empty }
            ((evaluated.extract 0 evaluated.toList.length).map (fun arg => arg.layout.ty)) st₁ =
            .ok (match MirSemantics.getElem? rp.bodies (Nat.div encodedId 2) with
              | some rbody => rbody.argumentCount
              | none => 0) st₁ := by
          dsimp only [refCallHooks]
          cases MirSemantics.getElem? rp.bodies (Nat.div encodedId 2) <;> rfl
        refine callM_bind_ok h_abi ?_
        rw [eStateM_bind_pure]
        rfl
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        have h_abi : (refCallHooks rp).fnAbiOfInstance ()
            { kind := .Item (Nat.div encodedId 2), args := Array.empty }
            ((evaluated.extract 0 evaluated.toList.length).map (fun arg => arg.layout.ty)) st₁ =
            .ok (match MirSemantics.getElem? rp.bodies (Nat.div encodedId 2) with
              | some rbody => rbody.argumentCount
              | none => 0) st₁ := by
          dsimp only [refCallHooks]
          cases MirSemantics.getElem? rp.bodies (Nat.div encodedId 2) <;> rfl
        refine callM_bind_ok h_abi ?_
        rw [eStateM_bind_pure]
        rfl

private theorem passArgument_eq {rp : RefProg}
    {stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit}
    {frames : List RefFrameState} {ci : RefCalleeInit}
    {fnArg : Miri.Interpreter.FnArg RefCallProv}
    {argTy : MirTy} {sv : SlotVal}
    (calleeIndex localId : Nat)
    (h_m : RefFnArgMatches fnArg (argTy, sv)) :
    let st : RefStepState :=
      { stack := stk, machine := { frames := frames, calleeInit := some ci } }
    Miri.Interpreter.Call.passArgument (refCallHooks rp) () fnArg () ()
        calleeIndex ⟨localId, Array.empty⟩ 0 false st =
      match MirSemantics.getElem? ci.localTys localId with
      | none => .error (.unsupported "missing callee parameter type") st
      | some paramTy =>
        if !(MirTy.beq argTy paramTy) then
          .error (.unsupported "call argument type mismatch") st
        else
          match sv.toVal? with
          | none => .error (.undefinedBehavior "uninit call argument") st
          | some v =>
            if !checkVal v paramTy then
              .error (.unsupported "invalid call argument value") st
            else
              .ok () {
                stack := stk
                machine := {
                  frames := frames
                  calleeInit := some { ci with argValsRev := v :: ci.argValsRev }
                }
              } := by
  intro st
  let ⟨h_ext, h_lay, h_meta, h_shape⟩ := h_m
  unfold Miri.Interpreter.Call.passArgument
  have h_argLay : (refCallHooks rp).argLayout () = refSizedLocalLayout := rfl
  have h_compat : (refCallHooks rp).checkArgumentCompat () () () st =
      .ok true st := rfl
  have h_sLive : ∀ m,
      (refCallHooks rp).storageLiveDyn () localId m st = .ok () st :=
    fun _ => rfl
  have h_evalPl : (refCallHooks rp).evalPlace () ⟨localId, Array.empty⟩ false st =
      .ok (.frameLocal 0 localId none refSizedLocalLayout
        (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)) st := rfl
  have h_deinit : (refCallHooks rp).deinitMovedPlace = false := rfl
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [h_argLay, h_lay]
  have h_eq0 : (0 == refSizedLocalLayout.ty) = true := rfl
  have h_eqL : (refSizedLocalLayout.layout == refSizedLocalLayout.layout) = true := by
    change (refSizedLocalLayout.layout == refSizedLocalLayout.layout) = true
    exact beq_self_eq_true _
  rw [h_eq0, h_eqL]
  refine callM_bind_ok (a := ()) (s' := st) rfl ?_
  refine callM_bind_ok (a := ()) (s' := st) rfl ?_
  refine callM_bind_ok h_compat ?_
  simp only [ite_true]
  cases fnArg with
  | Copy op =>
    dsimp only [Miri.Interpreter.FnArg.copyFnArg] at h_ext h_meta
    simp only [Bool.not_false, ite_true]
    repeat rw [eStateM_bind_assoc]
    have h_emp : (Array.empty : Array Miri.MIR.ProjectionElem).isEmpty = true := rfl
    have h_mmeta : (!op.metadata.hasMeta || (op.layout.ty == 0)) = true := by
      rw [h_meta]; rfl
    rw [h_emp, h_mmeta]
    refine callM_bind_ok (a := ()) (s' := st) rfl ?_
    refine callM_bind_ok (a := ()) (s' := st) rfl ?_
    refine callM_bind_ok (h_sLive _) ?_
    refine callM_bind_ok h_evalPl ?_
    have h_copy :
        (refCallHooks rp).copyAllowTransmute () op
            (.frameLocal 0 localId none refSizedLocalLayout
              (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)) st =
          match MirSemantics.getElem? ci.localTys localId with
          | none => .error (.unsupported "missing callee parameter type") st
          | some paramTy =>
            if !(MirTy.beq argTy paramTy) then
              .error (.unsupported "call argument type mismatch") st
            else
              match sv.toVal? with
              | none => .error (.undefinedBehavior "uninit call argument") st
              | some v =>
                if !checkVal v paramTy then
                  .error (.unsupported "invalid call argument value") st
                else
                  .ok () {
                    stack := stk
                    machine := {
                      frames := frames
                      calleeInit := some { ci with argValsRev := v :: ci.argValsRev }
                    }
                  } := by
      dsimp only [refCallHooks, st]
      rw [h_ext]
      dsimp only
      cases MirSemantics.getElem? ci.localTys localId with
      | none => rfl
      | some paramTy =>
        dsimp only
        cases MirTy.beq argTy paramTy with
        | false => rfl
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          cases sv.toVal? with
          | none => rfl
          | some v =>
            dsimp only
            rw [checkRefVal_eq]
    cases h_c : MirSemantics.getElem? ci.localTys localId with
    | none =>
      rw [h_c] at h_copy
      first | dsimp only at h_copy | change _
      first | dsimp only | change _
      exact eStateM_bind_error h_copy _
    | some paramTy =>
      rw [h_c] at h_copy
      first | dsimp only at h_copy | change _
      first | dsimp only | change _
      cases h_bt : MirTy.beq argTy paramTy with
      | false =>
        rw [h_bt] at h_copy
        simp only [Bool.not_false, ite_true] at h_copy
        simp only [Bool.not_false, ite_true]
        exact eStateM_bind_error h_copy _
      | true =>
        rw [h_bt] at h_copy
        simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h_copy
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        cases h_sv : sv.toVal? with
        | none =>
          rw [h_sv] at h_copy
          first | dsimp only at h_copy | change _
          first | dsimp only | change _
          exact eStateM_bind_error h_copy _
        | some v =>
          rw [h_sv] at h_copy
          first | dsimp only at h_copy | change _
          first | dsimp only | change _
          cases h_cv : checkVal v paramTy with
          | false =>
            rw [h_cv] at h_copy
            simp only [Bool.not_false, ite_true] at h_copy
            simp only [Bool.not_false, ite_true]
            exact eStateM_bind_error h_copy _
          | true =>
            rw [h_cv] at h_copy
            simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h_copy
            simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            exact eStateM_bind_ok h_copy _
  | InPlace mp snap =>
    cases snap with
    | some _ => exact False.elim h_shape
    | none =>
      dsimp only [Miri.Interpreter.FnArg.copyFnArg] at h_ext h_meta
      simp only [Bool.not_false, ite_true]
      repeat rw [eStateM_bind_assoc]
      have h_emp : (Array.empty : Array Miri.MIR.ProjectionElem).isEmpty = true := rfl
      let op : Miri.Interpreter.OpTy RefCallProv := ⟨.indirect mp.mplace, mp.layout⟩
      have h_mmeta : (!op.metadata.hasMeta || (op.layout.ty == 0)) = true := by
        rw [h_meta]; rfl
      rw [h_emp, h_mmeta]
      refine callM_bind_ok (a := ()) (s' := st) rfl ?_
      refine callM_bind_ok (a := ()) (s' := st) rfl ?_
      refine callM_bind_ok (h_sLive _) ?_
      refine callM_bind_ok h_evalPl ?_
      have h_copy :
          (refCallHooks rp).copyAllowTransmute () op
              (.frameLocal 0 localId none refSizedLocalLayout
                (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)) st =
            match MirSemantics.getElem? ci.localTys localId with
            | none => .error (.unsupported "missing callee parameter type") st
            | some paramTy =>
              if !(MirTy.beq argTy paramTy) then
                .error (.unsupported "call argument type mismatch") st
              else
                match sv.toVal? with
                | none => .error (.undefinedBehavior "uninit call argument") st
                | some v =>
                  if !checkVal v paramTy then
                    .error (.unsupported "invalid call argument value") st
                  else
                    .ok () {
                      stack := stk
                      machine := {
                        frames := frames
                        calleeInit := some { ci with argValsRev := v :: ci.argValsRev }
                      }
                    } := by
        dsimp only [refCallHooks, st]
        rw [h_ext]
        dsimp only
        cases MirSemantics.getElem? ci.localTys localId with
        | none => rfl
        | some paramTy =>
          dsimp only
          cases MirTy.beq argTy paramTy with
          | false => rfl
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            cases sv.toVal? with
            | none => rfl
            | some v =>
              dsimp only
              rw [checkRefVal_eq]
      cases h_c : MirSemantics.getElem? ci.localTys localId with
      | none =>
        rw [h_c] at h_copy
        first | dsimp only at h_copy | change _
        first | dsimp only | change _
        exact eStateM_bind_error h_copy _
      | some paramTy =>
        rw [h_c] at h_copy
        first | dsimp only at h_copy | change _
        first | dsimp only | change _
        cases h_bt : MirTy.beq argTy paramTy with
        | false =>
          rw [h_bt] at h_copy
          simp only [Bool.not_false, ite_true] at h_copy
          simp only [Bool.not_false, ite_true]
          exact eStateM_bind_error h_copy _
        | true =>
          rw [h_bt] at h_copy
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h_copy
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          cases h_sv : sv.toVal? with
          | none =>
            rw [h_sv] at h_copy
            first | dsimp only at h_copy | change _
            first | dsimp only | change _
            exact eStateM_bind_error h_copy _
          | some v =>
            rw [h_sv] at h_copy
            first | dsimp only at h_copy | change _
            first | dsimp only | change _
            cases h_cv : checkVal v paramTy with
            | false =>
              rw [h_cv] at h_copy
              simp only [Bool.not_false, ite_true] at h_copy
              simp only [Bool.not_false, ite_true]
              exact eStateM_bind_error h_copy _
            | true =>
              rw [h_cv] at h_copy
              simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h_copy
              simp only [Bool.not_true, Bool.false_eq_true, ite_false]
              rw [eStateM_bind_ok h_copy]
              rw [h_deinit]
              simp only [Bool.false_eq_true, ite_false]
              dsimp only [extractRefCallArg?, op] at h_ext
              cases h_prov : mp.mplace.ptr.provenance with
              | none => rw [h_prov] at h_ext; cases h_ext
              | some prov =>
                cases prov with
                | dst _ _ => rw [h_prov] at h_ext; cases h_ext
                | arg _ _ => dsimp only [refCallHooks]; rw [h_prov]

private theorem initStackFrame_argsLoop_eq {rp : RefProg}
    {rbody : RefBody} {calleeBody : Body}
    {args : Array (Miri.Interpreter.FnArg RefCallProv)}
    {argPairs : List (MirTy × SlotVal)}
    {pre : List RefMiriFrame} {frames : List RefFrameState}
    (stepFn : Nat → Nat × Nat →
      Miri.Interpreter.CallM RefStepState (ForInStep (Nat × Nat)))
    (h_step : ∀ (start : Nat) (mf : RefMiriFrame) (ci : RefCalleeInit)
      (fnArg : Miri.Interpreter.FnArg RefCallProv),
      start < rbody.argumentCount →
      args[start]? = some fnArg →
      stepFn start (start, start)
        { stack := ⟨Array.mk (pre ++ [mf])⟩
          machine := { frames := frames, calleeInit := some ci } } =
        EStateM.bind
          (Miri.Interpreter.Call.passArgument (refCallHooks rp) () fnArg () ()
            start ⟨start + 1, Array.empty⟩ 0 false)
          (fun _ => EStateM.pure (ForInStep.yield (start + 1, start + 1)))
          { stack := ⟨Array.mk (pre ++ [{ mf with location := .unwinding ⟨0⟩ }])⟩
            machine := { frames := frames, calleeInit := some ci } })
    (h_arg_eq : rbody.argumentCount = calleeBody.argumentCount)
    (h_blt : Nat.blt calleeBody.argumentCount calleeBody.locals.length = true)
    (h_len_pairs : argPairs.length = calleeBody.argumentCount)
    (h_match : RefFnArgsMatch args.toList argPairs)
    (start count : Nat) (mf : RefMiriFrame) (ci : RefCalleeInit)
    (h_sum : start + count = calleeBody.argumentCount)
    (h_ci_tys : ci.localTys = calleeBody.locals) :
    let st : RefStepState := {
      stack := ⟨Array.mk (pre ++ [mf])⟩
      machine := { frames := frames, calleeInit := some ci }
    }
    match validateCallArgs (argPairs.drop start)
        (((calleeBody.locals.drop 1).take calleeBody.argumentCount).drop start) with
    | .error k =>
      ∃ err st_err,
        callErrToFault err = k ∧
        forIn (m := Miri.Interpreter.CallM RefStepState)
          (List.range' start count 1) (start, start) stepFn st =
          .error err st_err
    | .ok tailVals =>
      ∃ mf' : RefMiriFrame,
        forIn (m := Miri.Interpreter.CallM RefStepState)
          (List.range' start count 1) (start, start) stepFn st =
          .ok (calleeBody.argumentCount, calleeBody.argumentCount) {
            stack := ⟨Array.mk (pre ++ [mf'])⟩
            machine := {
              frames := frames
              calleeInit := some { ci with argValsRev := tailVals.reverse ++ ci.argValsRev }
            }
          } := by
  induction count generalizing start mf ci with
  | zero =>
    rw [Nat.add_zero] at h_sum
    subst h_sum
    dsimp only [List.range']
    rw [List.forIn_nil]
    have h_p_nil : argPairs.drop calleeBody.argumentCount = [] := by
      rw [List.drop_eq_nil_iff, h_len_pairs]
      exact Nat.le_refl _
    have h_t_nil :
        ((calleeBody.locals.drop 1).take calleeBody.argumentCount).drop
            calleeBody.argumentCount = [] :=
      list_drop_take_end_nil calleeBody.locals calleeBody.argumentCount
    rw [h_p_nil, h_t_nil]
    exact ⟨mf, rfl⟩
  | succ m ih =>
    have h_lt_arg : start < calleeBody.argumentCount := by
      rw [← h_sum]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos m)
    have h_lt_rarg : start < rbody.argumentCount := by
      rw [h_arg_eq]; exact h_lt_arg
    have h_lt_pairs : start < argPairs.length := by
      rw [h_len_pairs]; exact h_lt_arg
    have h_lt_locs : start + 1 < calleeBody.locals.length := by
      have h_ac_lt : calleeBody.argumentCount < calleeBody.locals.length := by
        rw [← Nat.blt_eq]; exact h_blt
      exact Nat.lt_of_le_of_lt h_lt_arg h_ac_lt
    cases h_ap : argPairs[start]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at h_ap
      exact False.elim (Nat.not_le_of_lt h_lt_pairs h_ap)
    | some pair =>
      let ⟨argTy, sv⟩ := pair
      let ⟨fnArg, h_fn_get, h_fn_m⟩ :=
        refFnArgsMatch_getElem? h_match start (argTy, sv) h_ap
      have h_fn_arr : args[start]? = some fnArg :=
        (Array.getElem?_toList (xs := args) (i := start)).symm.trans h_fn_get
      cases h_pt : MirSemantics.getElem? calleeBody.locals (start + 1) with
      | none =>
        rw [← list_getElem?_eq_mirGetElem?, List.getElem?_eq_none_iff] at h_pt
        exact False.elim (Nat.not_le_of_lt h_lt_locs h_pt)
      | some paramTy =>
        have h_drop_pairs : argPairs.drop start =
            (argTy, sv) :: argPairs.drop (start + 1) := by
          have h_d0 : (argPairs.drop start)[0]? = some (argTy, sv) := by
            rw [List.getElem?_drop, Nat.add_zero]; exact h_ap
          cases h_dp : argPairs.drop start with
          | nil => rw [h_dp] at h_d0; cases h_d0
          | cons y ys =>
            rw [h_dp] at h_d0
            injection h_d0 with h_y
            subst h_y
            have h_tail : argPairs.drop (start + 1) = ys := by
              rw [← List.drop_drop, h_dp]; rfl
            rw [h_tail]
        have h_drop_tys :
            ((calleeBody.locals.drop 1).take calleeBody.argumentCount).drop start =
              paramTy ::
                ((calleeBody.locals.drop 1).take calleeBody.argumentCount).drop
                  (start + 1) := by
          rw [← h_sum]
          exact list_drop_take_succ_cons calleeBody.locals start m paramTy h_pt
        dsimp only [List.range']
        rw [List.forIn_cons]
        dsimp only [bind, Bind.bind, pure, Pure.pure]
        let mf₁ : RefMiriFrame := { mf with location := .unwinding ⟨0⟩ }
        have h_st := h_step start mf ci fnArg h_lt_rarg h_fn_arr
        have h_pass := passArgument_eq (rp := rp)
          (stk := ⟨Array.mk (pre ++ [mf₁])⟩) (frames := frames) (ci := ci)
          start (start + 1) h_fn_m
        rw [h_ci_tys, h_pt] at h_pass
        dsimp only at h_pass
        rw [h_drop_pairs, h_drop_tys]
        dsimp only [validateCallArgs]
        cases h_bt : MirTy.beq argTy paramTy with
        | false =>
          rw [h_bt] at h_pass
          simp only [Bool.not_false, ite_true] at h_pass
          simp only [Bool.not_false, ite_true]
          exact ⟨_, _, rfl, eStateM_bind_error
            (h_st.trans (eStateM_bind_error h_pass _)) _⟩
        | true =>
          rw [h_bt] at h_pass
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h_pass
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          cases h_sv : sv.toVal? with
          | none =>
            rw [h_sv] at h_pass
            first | dsimp only at h_pass | change _
            first | dsimp only | change _
            exact ⟨_, _, rfl, eStateM_bind_error
              (h_st.trans (eStateM_bind_error h_pass _)) _⟩
          | some v =>
            rw [h_sv] at h_pass
            first | dsimp only at h_pass | change _
            first | dsimp only | change _
            cases h_cv : checkVal v paramTy with
            | false =>
              rw [h_cv] at h_pass
              simp only [Bool.not_false, ite_true] at h_pass
              simp only [Bool.not_false, ite_true]
              exact ⟨_, _, rfl, eStateM_bind_error
                (h_st.trans (eStateM_bind_error h_pass _)) _⟩
            | true =>
              rw [h_cv] at h_pass
              simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h_pass
              simp only [Bool.not_true, Bool.false_eq_true, ite_false]
              have h_yield := h_st.trans (eStateM_bind_ok h_pass _)
              rw [← h_ci_tys] at h_yield
              have h_sum' : (start + 1) + m = calleeBody.argumentCount := by
                rw [Nat.add_assoc, Nat.add_comm 1 m, ← Nat.add_assoc]
                exact h_sum
              have h_ih := ih (start + 1) mf₁ { ci with argValsRev := v :: ci.argValsRev }
                h_sum' h_ci_tys
              dsimp only at h_ih
              cases h_vc : validateCallArgs (argPairs.drop (start + 1))
                  (((calleeBody.locals.drop 1).take calleeBody.argumentCount).drop
                    (start + 1)) with
              | error k =>
                rw [h_vc] at h_ih
                dsimp only
                let ⟨err, st_err, h_ek, h_err⟩ := h_ih
                exact ⟨err, st_err, h_ek, (eStateM_bind_ok h_yield _).trans h_err⟩
              | ok vs =>
                rw [h_vc] at h_ih
                dsimp only
                let ⟨mf', h_ok⟩ := h_ih
                refine ⟨mf', ?_⟩
                have h_rev : (v :: vs).reverse ++ ci.argValsRev =
                    vs.reverse ++ (v :: ci.argValsRev) := by
                  rw [List.reverse_cons, List.append_assoc]
                  rfl
                rw [h_rev]
                exact (eStateM_bind_ok h_yield _).trans h_ok

private noncomputable def evalCallPost (rp : RefProg) (callerMem : CallerMemory)
    (rcallers : List RefFrameState) (target : Option BasicBlockId)
    (st₀ : RefStepState)
    (res : EStateM.Result Miri.Interpreter.StepError RefStepState Unit) :
    StepResult RefState TerminalOut :=
  match res with
  | .error (.undefinedBehavior _) _ => .fault .undefined
  | .error _ _ => .fault .unsupported
  | .ok () st' =>
    if target.isSome &&
        st'.stack.frames.size == st₀.stack.frames.size &&
        st'.stack.currentFrame?.map (·.location) ==
          st₀.stack.currentFrame?.map (·.location) then
      .fault .unsupported
    else
      match st'.machine.terminal with
      | some r => r
      | none =>
        match extractMirLocation? st', st'.machine.frames with
        | some loc, top :: rest =>
          .step {
            frames :=
              ({ top with
                 blockIdx := loc.block
                 stmtIdx := loc.statementIndex } :: rest).reverse
            callerMem
          }
        | none, _ => drainRefUnwind rp callerMem (rcallers.length + 1) st'
        | _, _ => .fault .unsupported

private theorem initStackFrame_argsLoop_dispatch {rp : RefProg} {p : Program}
    {rbody : RefBody} {calleeBody : Body}
    {callerMem : CallerMemory} {rcallers : List RefFrameState}
    {target : Option BasicBlockId} {st₀ : RefStepState}
    {args : Array (Miri.Interpreter.FnArg RefCallProv)}
    {argPairs : List (MirTy × SlotVal)}
    {pre : List RefMiriFrame} {mf : RefMiriFrame}
    {frames : List RefFrameState} {ci : RefCalleeInit}
    {stepFn : Nat → Nat × Nat → Miri.Interpreter.CallM RefStepState (ForInStep (Nat × Nat))}
    {k : Nat × Nat → Miri.Interpreter.CallM RefStepState Unit}
    {rhsOk : List Val → StepResult State TerminalOut}
    (h_step : ∀ (start : Nat) (mf' : RefMiriFrame) (ci' : RefCalleeInit)
      (fnArg : Miri.Interpreter.FnArg RefCallProv),
      start < rbody.argumentCount →
      args[start]? = some fnArg →
      stepFn start (start, start)
        { stack := ⟨Array.mk (pre ++ [mf'])⟩
          machine := { frames := frames, calleeInit := some ci' } } =
        EStateM.bind
          (Miri.Interpreter.Call.passArgument (refCallHooks rp) () fnArg () ()
            start ⟨start + 1, Array.empty⟩ 0 false)
          (fun _ => EStateM.pure (ForInStep.yield (start + 1, start + 1)))
          { stack := ⟨Array.mk (pre ++ [{ mf' with location := .unwinding ⟨0⟩ }])⟩
            machine := { frames := frames, calleeInit := some ci' } })
    (h_arg_eq : rbody.argumentCount = calleeBody.argumentCount)
    (h_blt : Nat.blt calleeBody.argumentCount calleeBody.locals.length = true)
    (h_len_pairs : argPairs.length = calleeBody.argumentCount)
    (h_match : RefFnArgsMatch args.toList argPairs)
    (h_ci_tys : ci.localTys = calleeBody.locals)
    (h_ci_rev : ci.argValsRev = [])
    (h_cont : ∀ argVals (mf' : RefMiriFrame),
      validateCallArgs argPairs
          ((calleeBody.locals.drop 1).take calleeBody.argumentCount) = .ok argVals →
      evalCallPost rp callerMem rcallers target st₀
        (k (calleeBody.argumentCount, calleeBody.argumentCount) {
          stack := ⟨Array.mk (pre ++ [mf'])⟩
          machine := {
            frames := frames
            calleeInit := some { ci with argValsRev := argVals.reverse }
          }
        }) = mapStepRes p (rhsOk argVals)) :
    evalCallPost rp callerMem rcallers target st₀
      (EStateM.bind
        (EStateM.bind
          (forIn (m := Miri.Interpreter.CallM RefStepState)
            (List.range' 0 rbody.argumentCount 1) (0, 0) stepFn)
          (fun __s => EStateM.pure (__s.fst, __s.snd)))
        k
        { stack := ⟨Array.mk (pre ++ [mf])⟩
          machine := { frames := frames, calleeInit := some ci } }) =
      Except.casesOn (motive := fun _ => StepResult RefState TerminalOut)
        (validateCallArgs argPairs
          ((calleeBody.locals.drop 1).take calleeBody.argumentCount))
        (fun fk => .fault fk)
        (fun argVals => mapStepRes p (rhsOk argVals)) := by
  have h_loop := initStackFrame_argsLoop_eq (rp := rp) (rbody := rbody)
    (calleeBody := calleeBody) (args := args) (argPairs := argPairs)
    (pre := pre) (frames := frames) stepFn h_step
    h_arg_eq h_blt h_len_pairs h_match 0 calleeBody.argumentCount mf ci
    (Nat.zero_add _) h_ci_tys
  rw [List.drop_zero, List.drop_zero, h_ci_rev] at h_loop
  have h_range : List.range' 0 rbody.argumentCount 1 =
      List.range' 0 calleeBody.argumentCount 1 := by
    rw [h_arg_eq]
  rw [h_range]
  cases h_vc : validateCallArgs argPairs
      ((calleeBody.locals.drop 1).take calleeBody.argumentCount) with
  | error fk =>
    rw [h_vc] at h_loop
    let ⟨err, st_err, h_ek, h_err⟩ := h_loop
    rw [eStateM_bind_error
      (eStateM_bind_error h_err (fun __s => EStateM.pure (__s.fst, __s.snd))),
      ← h_ek]
    cases err <;> rfl
  | ok argVals =>
    rw [h_vc] at h_loop
    let ⟨mf', h_ok⟩ := h_loop
    rw [List.append_nil] at h_ok
    rw [eStateM_bind_ok
      (eStateM_bind_ok h_ok (fun __s => EStateM.pure (__s.fst, __s.snd)))]
    exact h_cont argVals mf' h_vc

private theorem of_bool_true_else {P : Prop} (b : Bool)
    (h_true : b = true → P) (h_false : b = false → P) : P := by
  cases b with
  | true => exact h_true rfl
  | false => exact h_false rfl

private theorem evalRefTerminator_call_overlap {rp : RefProg}
    {rbb : RefBasicBlock} {rframe : RefFrameState}
    {rcallers : List RefFrameState} {callerMem : CallerMemory}
    {func : Miri.MIR.Operand} {margs : Array Miri.MIR.SpannedOperand}
    {mdest : Miri.MIR.Place} {target : Option BasicBlockId}
    {munwind : Miri.MIR.UnwindAction}
    (h_term : toMiriTerminatorForDispatch rbb.terminator = {
      sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Call func margs mdest target munwind .Normal ⟨0⟩
    })
    (h_ov : refAnyMoveOperandMayOverlapPlace mdest
        (margs.toList.map (fun a => a.operand)) = true) :
    evalRefTerminator rp rbb rframe rcallers callerMem = .fault .unsupported := by
  rw [evalRefTerminator_eq_of_term]
  let mirTerm := toMiriTerminatorForDispatch rbb.terminator
  let st₀ := mkRefTermStepState rframe rcallers mirTerm rbb.cleanup
  have h_step :
      Miri.Interpreter.ControlFlow.evalTerminator
        (refTerminatorHooksFor rp callerMem) () mirTerm st₀ =
      (st₀, .error (.unsupported "overlapping move call arg and dest")) := by
    have h_kind : mirTerm.kind =
        .Call func margs mdest target munwind .Normal ⟨0⟩ := by
      dsimp only [mirTerm]
      rw [h_term]
    have h_call :
        (refTerminatorHooksFor rp callerMem).call () mirTerm st₀ =
        (st₀, .error (.unsupported "overlapping move call arg and dest")) := by
      dsimp only [refTerminatorHooksFor]
      rw [h_kind]
      dsimp only
      rw [h_ov]
      rfl
    unfold Miri.Interpreter.ControlFlow.evalTerminator
    rw [h_kind, h_call]
    rfl
  change (match Miri.Interpreter.ControlFlow.evalTerminator
      (refTerminatorHooksFor rp callerMem) () mirTerm st₀ with
    | (st', .ok ()) =>
      match st'.machine.terminal with
      | some res => res
      | none =>
        match extractMirLocation? st', st'.machine.frames with
        | some loc, top :: rest =>
          .step {
            frames :=
              ({ top with
                 blockIdx := loc.block
                 stmtIdx := loc.statementIndex } :: rest).reverse
            callerMem
          }
        | none, _ => drainRefUnwind rp callerMem (rcallers.length + 1) st'
        | _, _ => .fault .unsupported
    | (_, .error (.undefinedBehavior _)) => .fault .undefined
    | (_, _) => .fault .unsupported) = .fault .unsupported
  rw [h_step]

private theorem evalRefTerminator_call_bridge {rp : RefProg}
    {rbb : RefBasicBlock} {rframe : RefFrameState}
    {rcallers : List RefFrameState} {callerMem : CallerMemory}
    {func : Miri.MIR.Operand} {margs : Array Miri.MIR.SpannedOperand}
    {mdest : Miri.MIR.Place} {target : Option BasicBlockId}
    {munwind : Miri.MIR.UnwindAction}
    {rhs : StepResult RefState TerminalOut}
    (h_term : toMiriTerminatorForDispatch rbb.terminator = {
      sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Call func margs mdest target munwind .Normal ⟨0⟩
    })
    (h_noOverlap : refAnyMoveOperandMayOverlapPlace mdest
        (margs.toList.map (fun a => a.operand)) = false)
    (h_post :
      let mirTerm := toMiriTerminatorForDispatch rbb.terminator
      let st₀ := mkRefTermStepState rframe rcallers mirTerm rbb.cleanup
      evalCallPost rp callerMem rcallers target st₀
        (Miri.Interpreter.Call.evalCallTerminator
          (refCallHooks rp) () 2 mirTerm st₀) = rhs) :
    evalRefTerminator rp rbb rframe rcallers callerMem = rhs := by
  rw [evalRefTerminator_eq_of_term]
  let mirTerm := toMiriTerminatorForDispatch rbb.terminator
  let st₀ := mkRefTermStepState rframe rcallers mirTerm rbb.cleanup
  have h_step :
      Miri.Interpreter.ControlFlow.evalTerminator
        (refTerminatorHooksFor rp callerMem) () mirTerm st₀ =
      match Miri.Interpreter.Call.evalCallTerminator
          (refCallHooks rp) () 2 mirTerm st₀ with
      | .error err st' => (st', .error err)
      | .ok () st' =>
        if target.isSome &&
            st'.stack.frames.size == st₀.stack.frames.size &&
            st'.stack.currentFrame?.map (·.location) ==
              st₀.stack.currentFrame?.map (·.location) then
          (st', .error (.invalidProgram "evaluating this call made no progress"))
        else
          (st', .ok ()) := by
    have h_kind : mirTerm.kind =
        .Call func margs mdest target munwind .Normal ⟨0⟩ := by
      dsimp only [mirTerm]
      rw [h_term]
    have h_call :
        (refTerminatorHooksFor rp callerMem).call () mirTerm st₀ =
        Miri.Interpreter.Call.run
          (Miri.Interpreter.Call.evalCallTerminator (refCallHooks rp) () 2 mirTerm)
          st₀ := by
      dsimp only [refTerminatorHooksFor]
      rw [h_kind]
      dsimp only
      rw [h_noOverlap, ite_false_eq_true]
    unfold Miri.Interpreter.ControlFlow.evalTerminator
    rw [h_kind, h_call]
    dsimp only [Miri.Interpreter.Call.run, Id.run, Pure.pure]
    cases Miri.Interpreter.Call.evalCallTerminator
        (refCallHooks rp) () 2 mirTerm st₀ with
    | error err st' => rfl
    | ok u st' =>
      cases u
      rfl
  change (match Miri.Interpreter.ControlFlow.evalTerminator
      (refTerminatorHooksFor rp callerMem) () mirTerm st₀ with
    | (st', .ok ()) =>
      match st'.machine.terminal with
      | some res => res
      | none =>
        match extractMirLocation? st', st'.machine.frames with
        | some loc, top :: rest =>
          .step {
            frames :=
              ({ top with
                 blockIdx := loc.block
                 stmtIdx := loc.statementIndex } :: rest).reverse
            callerMem
          }
        | none, _ => drainRefUnwind rp callerMem (rcallers.length + 1) st'
        | _, _ => .fault .unsupported
    | (_, .error (.undefinedBehavior _)) => .fault .undefined
    | (_, _) => .fault .unsupported) = rhs
  rw [h_step]
  cases h_e : Miri.Interpreter.Call.evalCallTerminator
      (refCallHooks rp) () 2 mirTerm st₀ with
  | error err st' =>
    dsimp only [evalCallPost] at h_post
    rw [h_e] at h_post
    cases err <;> exact h_post
  | ok u st' =>
    cases u
    dsimp only [evalCallPost] at h_post
    rw [h_e] at h_post
    first | dsimp only at h_post | change _
    first | dsimp only | change _
    cases h_np : (target.isSome &&
        st'.stack.frames.size == st₀.stack.frames.size &&
        st'.stack.currentFrame?.map (·.location) ==
          st₀.stack.currentFrame?.map (·.location)) with
    | true =>
      rw [h_np] at h_post
      exact h_post
    | false =>
      rw [h_np] at h_post
      exact h_post

private theorem evalRefTerminator_call_eq {rp : RefProg} {p : Program}
    {body : Body} {rbb : RefBasicBlock} {f : FrameState}
    {callers : List FrameState} {rcallers : List RefFrameState}
    {callerMem : CallerMemory} {callee : DefId}
    {rargs : List RefOperand} {args : List Operand}
    {rdst : RefPlace} {dst : Place}
    {target : Option BasicBlockId} {unwind : UnwindAction}
    (h_dec : decodeProg rp = some p)
    (h_f_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_len : f.locals.length = body.locals.length)
    (h_cs : FramesSimInv p callers rcallers)
    (h_rt : rbb.terminator = .call callee rargs rdst target unwind)
    (h_args : mapOption (decodeOperand rp.types) rargs = some args)
    (h_dst : decodePlace rp.types rdst = some dst) :
    evalRefTerminator rp rbb (liftFrame body.locals f) rcallers callerMem =
      mapStepRes p
        (evalTerminator p body
          { statements := []
            terminator := .call callee args dst target unwind
            cleanup := rbb.cleanup }
          f callers callerMem) := by
  let ⟨h_dst_id, h_dst_proj⟩ := decodePlace_proj_inv h_dst
  let ⟨_, _, _, _, h_bodies⟩ := decodeProg_inv h_dec
  unfold evalTerminator
  dsimp only
  have h_ov_eq :
      refAnyMoveOperandMayOverlapPlace (toMiriPlace rdst)
        ((Array.mk (rargs.map (fun a =>
          (⟨⟨0⟩, toMiriOperand a⟩ : Miri.MIR.SpannedOperand)))).toList.map
          (fun a => a.operand)) =
      anyMoveOperandMayOverlapPlace dst args := by
    dsimp only [Array.toList]
    rw [List.map_map]
    exact refAnyMoveOperandMayOverlapPlace_eq h_dst h_args
  refine of_bool_true_else (anyMoveOperandMayOverlapPlace dst args)
    (fun h_ov => ?_) (fun h_ov_f => ?_)
  · rw [h_ov] at h_ov_eq
    rw [h_ov]
    exact evalRefTerminator_call_overlap (by rw [h_rt]; rfl) h_ov_eq
  rw [h_ov_f] at h_ov_eq
  rw [h_ov_f, ite_false_eq_true]
  refine evalRefTerminator_call_bridge (by rw [h_rt]; rfl) h_ov_eq ?_
  rw [h_rt]
  let mirTerm : Miri.MIR.Terminator :=
    toMiriTerminatorForDispatch (.call callee rargs rdst target unwind)
  let mframe : RefMiriFrame := {
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) rbb.cleanup with
    body := {
      refDummyMirBody rbb.cleanup with
      basicBlocks := Array.mk [{ refDummyMirBlock rbb.cleanup with
        terminator := mirTerm }]
    }
    bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
      (if (liftFrame body.locals f).returnCont.isNone then 0 else 1)
    returnContinuation :=
      match (liftFrame body.locals f).returnCont with
      | none => .goto (some 0) .Continue
      | some c => .goto c.target (toMiriUnwindAction c.unwind)
    location := .mir ⟨0, 1⟩
  }
  let pre : List RefMiriFrame := refSentinelMiriFrame :: mkCallerMiriFrames rcallers
  let stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit :=
    ⟨Array.mk (pre ++ [mframe])⟩
  let st₀ : RefStepState :=
    { stack := stk, machine := { frames := liftFrame body.locals f :: rcallers } }
  change evalCallPost rp callerMem rcallers target st₀
    (Miri.Interpreter.Call.evalCallTerminator (refCallHooks rp) () 2 mirTerm st₀) = _
  unfold Miri.Interpreter.Call.evalCallTerminator
  dsimp only [mirTerm, toMiriTerminatorForDispatch, bind, Bind.bind,
    pure, Pure.pure]
  have h_fi : (refCallHooks rp).frameIndex st₀ = .ok pre.length st₀ := by
    dsimp only [refCallHooks, st₀, stk]
    rw [stack_frameIndex_append]
  have h_gf : (refCallHooks rp).getFrame st₀ = .ok mframe st₀ := by
    dsimp only [refCallHooks, st₀, stk]
    rw [stack_currentFrame?_append]
  rw [eStateM_bind_ok h_fi, eStateM_bind_ok h_gf]
  cases h_ty : MirSemantics.getElem? body.locals dst.localId with
  | none =>
    have h_ep : (refCallHooks rp).evalPlace () (toMiriPlace rdst) false st₀ =
        .error (.unsupported "missing call destination local") st₀ := by
      dsimp only [refCallHooks, st₀, liftFrame, toMiriPlace]
      rw [h_dst_id, getElem?_zipRefLocals_none_left h_ty]
      rfl
    rw [eStateM_bind_error h_ep]
    rfl
  | some localTy =>
    dsimp only
    cases h_sl : MirSemantics.getElem? f.locals dst.localId with
    | none =>
      let ⟨s', hs'⟩ := getElem?_some_of_length_eq h_len.symm h_ty
      rw [h_sl] at hs'
      cases hs'
    | some dstSlot =>
      have h_z := getElem?_zipRefLocals_some h_ty h_sl
      cases h_pt : projectTy? localTy dst.projection with
      | none =>
        dsimp only
        have h_ep : (refCallHooks rp).evalPlace () (toMiriPlace rdst) false st₀ =
            .error (.unsupported "unsupported call destination") st₀ := by
          dsimp only [refCallHooks, st₀, liftFrame, toMiriPlace]
          rw [h_dst_id, h_z]
          dsimp only [Array.toList]
          rw [refProjectTy?_eq h_dst_proj, h_pt]
          rfl
        rw [eStateM_bind_error h_ep]
        rfl
      | some dstTy =>
        dsimp only
        have h_res_eq := refResolveProjPath_eq (bodyLocals := body.locals)
          (slots := f.locals) h_dst_proj (.ty localTy)
        dsimp only [placeTyToRefPlaceTy] at h_res_eq
        cases h_rp : resolveProjPath body.locals f.locals (.ty localTy)
            dst.projection with
        | error k =>
          rw [h_rp] at h_res_eq
          dsimp only
          have h_ep : (refCallHooks rp).evalPlace () (toMiriPlace rdst) false
              st₀ = .error (faultToStepError k) st₀ := by
            dsimp only [refCallHooks, st₀, liftFrame, toMiriPlace]
            simp only [Bool.false_eq_true, ite_false]
            rw [h_dst_id, h_z]
            dsimp only [Array.toList]
            rw [refProjectTy?_eq h_dst_proj, h_pt]
            dsimp only
            rw [h_res_eq]
          rw [eStateM_bind_error h_ep]
          cases k <;> rfl
        | ok resolvedProj =>
        rw [h_rp] at h_res_eq
        let ⟨resolvedMiriProj, h_res_ok, h_mdec, h_canon⟩ := h_res_eq
        dsimp only
        let resolvedDst : Place := ⟨dst.localId, resolvedProj⟩
        let rdest : RefDest := ⟨dst.localId, resolvedMiriProj, .ty dstTy⟩
        let destMplace : Miri.Interpreter.MPlaceTy RefCallProv :=
          ⟨⟨⟨Miri.ABI.Size.ZERO, some (.dst rdest resolvedDst)⟩, .none, none⟩,
            refSizedLocalLayout⟩
        let destPlace : Miri.Interpreter.RuntimeStackPlace RefCallProv :=
          .memory destMplace
        have h_ep : (refCallHooks rp).evalPlace () (toMiriPlace rdst) false st₀ =
            .ok destPlace st₀ := by
          dsimp only [refCallHooks, st₀, liftFrame, toMiriPlace, destPlace,
            destMplace, rdest, resolvedDst]
          simp only [Bool.false_eq_true, ite_false]
          rw [h_dst_id, h_z]
          dsimp only [Array.toList]
          rw [refProjectTy?_eq h_dst_proj, h_pt]
          dsimp only
          rw [h_res_ok]
          dsimp only
          rw [h_mdec]
        rw [eStateM_bind_ok h_ep]
        have h_eca := evalCalleeAndArgs_eq (rp := rp) (body := body)
          (f := f) (rcallers := rcallers) (stk := stk)
          (2 * callee) (toMiriPlace rdst) h_args
        cases h_ec : evalCallArgs body.locals f.locals args with
        | error k =>
          dsimp only
          rw [h_ec] at h_eca
          let ⟨st_err, h_err⟩ := h_eca
          rw [eStateM_bind_error h_err]
          cases k <;> rfl
        | ok res =>
          let ⟨argPairs, localsAfterArgs⟩ := res
          dsimp only
          rw [h_ec] at h_eca
          let ⟨evaluated, h_ev_ok, h_ev_m⟩ := h_eca
          have h_mod : Nat.beq (Nat.mod (2 * callee) 2) 0 = true := by
            change Nat.beq (HMod.hMod (2 * callee) 2) 0 = true
            rw [Nat.mul_mod_right]
            rfl
          have h_div : Nat.div (2 * callee) 2 = callee :=
            Nat.mul_div_right callee (by decide)
          rw [h_mod, h_div] at h_ev_ok
          simp only [ite_true] at h_ev_ok
          rw [eStateM_bind_ok h_ev_ok]
          have h_unw_can : (Option.any (refCallHooks rp).abiCanUnwind
              (some (match MirSemantics.getElem? rp.bodies callee with
                | some rbody => rbody.argumentCount
                | none => 0))) = true := rfl
          rw [h_unw_can]
          simp only [ite_true]
          let st₁ : RefStepState := {
            stack := stk
            machine := {
              frames :=
                liftFrame body.locals { f with locals := localsAfterArgs } :: rcallers
            }
          }
          unfold Miri.Interpreter.Call.initFnCall Miri.Interpreter.Call.initFnCallStep
          dsimp only [bind, Bind.bind, pure, Pure.pure]
          have h_abi_not :
              (Option.any (fun abi => !(refCallHooks rp).abiCanUnwind abi)
                (some (match MirSemantics.getElem? rp.bodies callee with
                  | some rbody => rbody.argumentCount
                  | none => 0))) = false := rfl
          rw [h_abi_not]
          simp only [Bool.false_eq_true, ite_false]
          repeat rw [eStateM_bind_assoc]
          have h_deinit : (refCallHooks rp).deinitMovedPlace = false := rfl
          have h_isrc : (refCallHooks rp).isRustCall () = false := rfl
          rw [eStateM_bind_pure]
          repeat rw [eStateM_bind_assoc]
          refine congr_bind_ok (a := (evaluated, (Array.mk []))) (s' := st₁) rfl ?_
          rw [Array.append_empty]
          repeat rw [eStateM_bind_assoc]
          refine congr_bind_cleanup_strip ?_ ?_ ?_ ?_
          · rfl
          · intro _ _; rfl
          · intro _ _; rfl
          rw [eStateM_bind_assoc]
          have h_ev_size : evaluated.size = argPairs.length :=
            refFnArgsMatch_length h_ev_m
          cases h_cb : MirSemantics.getElem? p.bodies callee with
          | none =>
            have h_rcb := (mapOption_getElem? h_bodies callee).1 h_cb
            have h_find : (refCallHooks rp).findMirOrEvalFn ()
                { kind := .Item callee, args := Array.empty }
                (match MirSemantics.getElem? rp.bodies callee with
                 | some rbody => rbody.argumentCount | none => 0)
                evaluated destPlace target (toMiriUnwindAction unwind) st₁ =
                .error (.unsupported "callee body out of bounds") st₁ := by
              dsimp only [refCallHooks, destPlace, destMplace, rdest,
                RefDest.ty?]
              rw [h_rcb]
            rw [eStateM_bind_error h_find]
            rfl
          | some calleeBody =>
            dsimp only
            let ⟨rbody, h_rcb_get, h_rcb_dec⟩ :=
              (mapOption_getElem? h_bodies callee).2 calleeBody h_cb
            let ⟨h_carg, h_clocs, _, _, _⟩ := decodeBody_inv h_rcb_dec
            cases h_adm : bodyEntryAdmitted calleeBody with
            | false =>
              simp only [Bool.not_false, ite_true]
              have h_find : (refCallHooks rp).findMirOrEvalFn ()
                  { kind := .Item callee, args := Array.empty }
                  (match MirSemantics.getElem? rp.bodies callee with
                   | some rbody => rbody.argumentCount | none => 0)
                  evaluated destPlace target (toMiriUnwindAction unwind) st₁ =
                  .error (.unsupported "callee body not admitted") st₁ := by
                dsimp only [refCallHooks, destPlace, destMplace, rdest,
                  RefDest.ty?]
                rw [h_rcb_get]
                dsimp only
                rw [h_clocs]
                dsimp only
                rw [refBodyEntryAdmitted_eq h_rcb_dec, h_adm]
                rfl
              rw [eStateM_bind_error h_find]
              rfl
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ite_false]
              cases h_arity : Nat.beq argPairs.length calleeBody.argumentCount with
              | false =>
                simp only [Bool.not_false, ite_true]
                have h_find : (refCallHooks rp).findMirOrEvalFn ()
                    { kind := .Item callee, args := Array.empty }
                    (match MirSemantics.getElem? rp.bodies callee with
                     | some rbody => rbody.argumentCount | none => 0)
                    evaluated destPlace target (toMiriUnwindAction unwind) st₁ =
                    .error (.unsupported "call argument count mismatch") st₁ := by
                  dsimp only [refCallHooks, destPlace, destMplace, rdest,
                    RefDest.ty?]
                  rw [h_rcb_get]
                  dsimp only
                  rw [h_clocs]
                  dsimp only
                  rw [refBodyEntryAdmitted_eq h_rcb_dec, h_adm]
                  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                  rw [h_ev_size, h_carg, h_arity]
                  rfl
                rw [eStateM_bind_error h_find]
                rfl
              | true =>
                simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases h_ret : MirSemantics.getElem? calleeBody.locals 0 with
                | none =>
                  dsimp only
                  have h_find : (refCallHooks rp).findMirOrEvalFn ()
                      { kind := .Item callee, args := Array.empty }
                      (match MirSemantics.getElem? rp.bodies callee with
                       | some rbody => rbody.argumentCount | none => 0)
                      evaluated destPlace target (toMiriUnwindAction unwind) st₁ =
                      .error (.unsupported "callee missing return local") st₁ := by
                    dsimp only [refCallHooks, destPlace, destMplace, rdest,
                      RefDest.ty?]
                    rw [h_rcb_get]
                    dsimp only
                    rw [h_clocs]
                    dsimp only
                    rw [refBodyEntryAdmitted_eq h_rcb_dec, h_adm]
                    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                    rw [h_ev_size, h_carg, h_arity]
                    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                    rw [h_ret]
                  rw [eStateM_bind_error h_find]
                  rfl
                | some calleeRetTy =>
                  dsimp only
                  cases h_rty : MirTy.beq calleeRetTy dstTy with
                  | false =>
                    simp only [Bool.not_false, ite_true]
                    have h_find : (refCallHooks rp).findMirOrEvalFn ()
                        { kind := .Item callee, args := Array.empty }
                        (match MirSemantics.getElem? rp.bodies callee with
                         | some rbody => rbody.argumentCount | none => 0)
                        evaluated destPlace target (toMiriUnwindAction unwind) st₁ =
                        .error (.unsupported "call return type mismatch") st₁ := by
                      dsimp only [refCallHooks, destPlace, destMplace, rdest,
                        RefDest.ty?]
                      rw [h_rcb_get]
                      dsimp only
                      rw [h_clocs]
                      dsimp only
                      rw [refBodyEntryAdmitted_eq h_rcb_dec, h_adm]
                      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                      rw [h_ev_size, h_carg, h_arity]
                      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                      rw [h_ret]
                      dsimp only
                      rw [h_rty]
                      rfl
                    rw [eStateM_bind_error h_find]
                    rfl
                  | true =>
                    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                    let mirBody : Miri.MIR.Body := {
                      refDummyMirBody false with
                      argumentCount := rbody.argumentCount
                      spreadArgument := none
                    }
                    let loaded : Miri.Interpreter.LoadedBody := {
                      identity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex 1
                      body := mirBody
                    }
                    have h_find : (refCallHooks rp).findMirOrEvalFn ()
                        { kind := .Item callee, args := Array.empty }
                        (match MirSemantics.getElem? rp.bodies callee with
                         | some rbody => rbody.argumentCount | none => 0)
                        evaluated destPlace target (toMiriUnwindAction unwind) st₁ =
                        .ok (some (loaded,
                          { kind := .Item callee, args := Array.empty })) st₁ := by
                      dsimp only [refCallHooks, destPlace, destMplace, rdest,
                        RefDest.ty?]
                      rw [h_rcb_get]
                      dsimp only
                      rw [h_clocs]
                      dsimp only
                      rw [refBodyEntryAdmitted_eq h_rcb_dec, h_adm]
                      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                      rw [h_ev_size, h_carg, h_arity]
                      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                      rw [h_ret]
                      dsimp only
                      rw [h_rty]
                      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                      dsimp only [loaded, mirBody]
                      rw [h_carg]
                    rw [eStateM_bind_ok h_find]
                    dsimp only
                    rw [h_isrc]
                    simp only [Bool.false_and, Bool.false_eq_true, ite_false]
                    rw [h_rcb_get]
                    dsimp only
                    unfold Miri.Interpreter.Call.initStackFrame
                    dsimp only [bind, Bind.bind, pure, Pure.pure]
                    repeat rw [eStateM_bind_assoc]
                    have h_reqLoc : ∀ i s,
                        (refCallHooks rp).requiresCallerLocation i s = .ok false s :=
                      fun _ _ => rfl
                    have h_var : ∀ a, (refCallHooks rp).abiVariadic a = false :=
                      fun _ => rfl
                    have h_same : ∀ a b, (refCallHooks rp).sameConvention a b = true :=
                      fun _ _ => rfl
                    have h_feat : ∀ i s,
                        (refCallHooks rp).checkTargetFeatures () i s = .ok () s :=
                      fun _ _ => rfl
                    have h_unw : ∀ a, (refCallHooks rp).abiCanUnwind a = true :=
                      fun _ => rfl
                    have h_abi : ∀ s,
                        (refCallHooks rp).fnAbiOfInstance ()
                          { kind := .Item callee, args := Array.empty } (Array.mk []) s =
                          .ok rbody.argumentCount s := by
                      intro s; dsimp only [refCallHooks]; rw [h_rcb_get]
                    rw [eStateM_bind_ok (h_reqLoc _ _)]
                    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
                    repeat rw [eStateM_bind_assoc]
                    rw [eStateM_bind_pure]
                    repeat rw [eStateM_bind_assoc]
                    rw [h_var]
                    simp only [Bool.false_eq_true, ite_false]
                    repeat rw [eStateM_bind_assoc]
                    rw [eStateM_bind_pure]
                    repeat rw [eStateM_bind_assoc]
                    rw [eStateM_bind_ok (h_abi _), h_same, h_var]
                    simp only [ite_true, beq_self_eq_true, Bool.false_and,
                      Bool.false_eq_true, ite_false]
                    repeat rw [eStateM_bind_assoc]
                    rw [eStateM_bind_ok (h_feat _ _), h_unw]
                    simp only [ite_true]
                    have h_pl_op :
                        (refCallHooks rp).placeToOp () destPlace st₁ =
                          match deinitPlaceWithLocalTy localTy localsAfterArgs
                              resolvedDst dstTy with
                          | .ok _ =>
                            .ok ⟨.indirect destMplace.mplace, destMplace.layout⟩
                              st₁
                          | .error k => .error (faultToStepError k) st₁ := by
                      dsimp only [refCallHooks, destPlace, destMplace, st₁,
                        liftFrame]
                      rw [refCheckPlaceLive_of_deinitPlace h_ty h_canon]
                      cases deinitPlaceWithLocalTy localTy localsAfterArgs
                          resolvedDst dstTy <;>
                        rfl
                    repeat rw [eStateM_bind_assoc]
                    cases h_deinit :
                        deinitPlaceWithLocalTy localTy localsAfterArgs
                          resolvedDst dstTy with
                    | error k =>
                      rw [h_deinit] at h_pl_op
                      rw [eStateM_bind_error h_pl_op]
                      cases k <;> rfl
                    | ok localsAfterDeinit =>
                      rw [h_deinit] at h_pl_op
                      rw [eStateM_bind_ok h_pl_op]
                      dsimp only
                      let contMiri : Miri.Interpreter.ReturnContinuation :=
                        .goto target (toMiriUnwindAction unwind)
                      let newMiriFrame : RefMiriFrame :=
                        Miri.Interpreter.Frame.create loaded
                          { kind := .Item callee, args := Array.empty } () contMiri
                          destPlace ⟨0⟩
                          (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)
                      let ci₀ : RefCalleeInit := {
                        defId := callee
                        rbody := rbody
                        localTys := calleeBody.locals
                        argValsRev := []
                        returnCont := ⟨resolvedDst, target, unwind⟩
                      }
                      let stk₂ : Miri.Interpreter.Stack RefCallProv
                          Miri.Interpreter.LocalLayout Unit :=
                        ⟨Array.mk ((pre ++ [mframe]) ++ [newMiriFrame])⟩
                      let st₂ : RefStepState := {
                        stack := stk₂
                        machine := {
                          frames :=
                            liftFrame body.locals { f with locals := localsAfterArgs } ::
                              rcallers
                          calleeInit := some ci₀
                        }
                      }
                      have h_pushRaw :
                          (refCallHooks rp).pushRaw ()
                            { kind := .Item callee, args := Array.empty } loaded
                            destPlace contMiri st₁ = .ok () st₂ := by
                        dsimp only [refCallHooks, destPlace, destMplace, st₁, stk]
                        rw [h_rcb_get]
                        dsimp only
                        rw [h_clocs]
                        dsimp only
                        rw [stack_pushFrame_goto _ _ _ target
                          (toMiriUnwindAction unwind) rfl]
                        dsimp only [st₂, stk₂, newMiriFrame, ci₀, contMiri]
                        cases unwind <;> rfl
                      repeat rw [eStateM_bind_assoc]
                      rw [eStateM_bind_ok h_pushRaw]
                      repeat rw [eStateM_bind_assoc]
                      have h_gf₂ : (refCallHooks rp).getFrame st₂ =
                          .ok newMiriFrame st₂ := by
                        dsimp only [refCallHooks, st₂, stk₂]
                        rw [stack_currentFrame?_append]
                      rw [eStateM_bind_ok h_gf₂]
                      dsimp only [newMiriFrame, Miri.Interpreter.Frame.create]
                      repeat rw [eStateM_bind_assoc]
                      rw [eStateM_bind_pure]
                      let newMiriFrame₁ : RefMiriFrame :=
                        { newMiriFrame with trackCallerArg := none }
                      let st₃ : RefStepState := {
                        stack := ⟨Array.mk ((pre ++ [mframe]) ++ [newMiriFrame₁])⟩
                        machine := st₂.machine
                      }
                      have h_sf₂ : (refCallHooks rp).setFrame newMiriFrame₁ st₂ =
                          .ok () st₃ := by
                        dsimp only [refCallHooks, st₂, stk₂]
                        rw [array_isEmpty_append_singleton,
                          array_pop_append_singleton, array_push_mk]
                        rfl
                      repeat rw [eStateM_bind_assoc]
                      dsimp only [newMiriFrame₁, newMiriFrame,
                        Miri.Interpreter.Frame.create] at h_sf₂
                      rw [eStateM_bind_ok h_sf₂]
                      repeat rw [eStateM_bind_assoc]
                      have h_noncap : (refCallHooks rp).nonCapturingClosure ()
                          { kind := .Item callee, args := Array.empty }
                          rbody.argumentCount st₃ = .ok false st₃ := rfl
                      rw [eStateM_bind_ok h_noncap]
                      repeat rw [eStateM_bind_assoc]
                      have h_abiArgs : (refCallHooks rp).abiArgs rbody.argumentCount =
                          Array.replicate rbody.argumentCount () := rfl
                      rw [h_abiArgs]
                      have h_arity_eq : argPairs.length = calleeBody.argumentCount :=
                        Nat.eq_of_beq_eq_true h_arity
                      have h_req_arity :
                          (evaluated.size + 0 ==
                            (Array.replicate rbody.argumentCount ()).size) = true := by
                        rw [Nat.add_zero, Array.size_replicate, h_ev_size,
                          h_arity_eq, h_carg]
                        exact beq_self_eq_true _
                      rw [h_req_arity]
                      refine congr_bind_ok (a := ()) (s' := st₃) rfl ?_
                      have h_retag : ∀ {α : Type} (act : Miri.Interpreter.CallM RefStepState α),
                          (refCallHooks rp).withRetagMode () .FnEntry act = act :=
                        fun _ => rfl
                      rw [h_retag]
                      rw [eStateM_bind_assoc]
                      dsimp only [loaded, mirBody]
                      rw [Std.Legacy.Range.forIn_eq_forIn_range']
                      dsimp only [Std.Legacy.Range.start, Std.Legacy.Range.size,
                        Std.Legacy.Range.step]
                      rw [nat_range_size_zero_step1]
                      have h_blt :
                          Nat.blt calleeBody.argumentCount calleeBody.locals.length = true := by
                        unfold bodyEntryAdmitted at h_adm
                        cases h_b1 : calleeBody.basicBlocks.isEmpty with
                        | true => rw [h_b1] at h_adm; cases h_adm
                        | false =>
                          rw [h_b1] at h_adm
                          cases h_b2 : Nat.blt calleeBody.argumentCount calleeBody.locals.length with
                          | false => rw [h_b2] at h_adm; cases h_adm
                          | true => rfl
                      refine Eq.trans
                        (initStackFrame_argsLoop_dispatch
                          (rp := rp) (p := p) (rbody := rbody)
                          (calleeBody := calleeBody)
                          (callerMem := callerMem) (rcallers := rcallers)
                          (target := target) (st₀ := st₀)
                          (args := evaluated) (argPairs := argPairs)
                          (pre := pre ++ [mframe]) (mf := newMiriFrame₁)
                          (frames :=
                            liftFrame body.locals
                              { f with locals := localsAfterArgs } :: rcallers)
                          (ci := ci₀)
                          (rhsOk := fun argVals => StepResult.step {
                            frames := {
                              defId := callee
                              blockIdx := 0
                              stmtIdx := 0
                              locals := initLocalsLoop calleeBody argVals 0 calleeBody.locals
                              returnCont := some ⟨resolvedDst, target, unwind⟩
                            } :: { f with locals := localsAfterDeinit } :: callers
                            callerMem := callerMem
                          })
                          ?_ h_carg h_blt h_arity_eq h_ev_m rfl rfl ?_)
                        (by
                          cases validateCallArgs argPairs
                            ((calleeBody.locals.drop 1).take calleeBody.argumentCount) <;>
                            rfl)
                      · intro start mf' ci' fnArg h_lt h_arr
                        dsimp only
                        let stA : RefStepState := {
                          stack := ⟨Array.mk ((pre ++ [mframe]) ++ [mf'])⟩
                          machine := {
                            frames := liftFrame body.locals
                              { f with locals := localsAfterArgs } :: rcallers
                            calleeInit := some ci'
                          }
                        }
                        let stB : RefStepState := {
                          stack := ⟨Array.mk ((pre ++ [mframe]) ++
                            [{ mf' with location := .unwinding ⟨0⟩ }])⟩
                          machine := {
                            frames := liftFrame body.locals
                              { f with locals := localsAfterArgs } :: rcallers
                            calleeInit := some ci'
                          }
                        }
                        have h_ls : (refCallHooks rp).localSpan mirBody (start + 1)
                            stA = .ok ⟨0⟩ stA := rfl
                        rw [eStateM_bind_ok h_ls]
                        refine callM_bind_ok (a := ()) (s' := stB) ?_ ?_
                        · change EStateM.bind (refCallHooks rp).getFrame
                            (fun frame => (refCallHooks rp).setFrame
                              { frame with location := .unwinding ⟨0⟩ }) stA = .ok () stB
                          have h_g : (refCallHooks rp).getFrame stA = .ok mf' stA := by
                            dsimp only [refCallHooks, stA]
                            rw [stack_currentFrame?_append]
                          rw [eStateM_bind_ok h_g]
                          dsimp only [refCallHooks, stA, stB]
                          rw [array_isEmpty_append_singleton,
                            array_pop_append_singleton, array_push_mk]
                          rfl
                        · have h_ll : (refCallHooks rp).localLayout () (start + 1)
                              stB = .ok refSizedLocalLayout stB := rfl
                          rw [eStateM_bind_ok h_ll]
                          simp only [Bool.false_and, Bool.false_eq_true, ite_false]
                          have h_none_ne :
                              ((none : Option Nat) == some (start + 1)) = false := rfl
                          rw [h_none_ne]
                          simp only [Bool.false_eq_true, ite_false]
                          have h_at_rep :
                              (Array.replicate rbody.argumentCount ())[start]? = some () :=
                            array_replicate_getElem?_lt rbody.argumentCount () start h_lt
                          refine callM_bind_ok (a := ()) (s' := stB) ?_ ?_
                          · change localCallAt (Array.replicate rbody.argumentCount ())
                              start "missing callee ABI" stB = .ok () stB
                            dsimp only [localCallAt]
                            rw [h_at_rep]
                            rfl
                          · rw [h_arr]
                            dsimp only
                            rw [eStateM_bind_pure]
                            refine callM_bind_ok (a := ()) (s' := stB) ?_ ?_
                            · change localCallAt (Array.replicate rbody.argumentCount ())
                                start "missing caller ABI" stB = .ok () stB
                              dsimp only [localCallAt]
                              rw [h_at_rep]
                              rfl
                            · rfl
                      · intro argVals mf_end _
                        dsimp only
                        have h_ls0 : ∀ s,
                            (refCallHooks rp).localSpan mirBody 0 s = .ok ⟨0⟩ s :=
                          fun _ => rfl
                        have h_ss_post : ∀ span mf' m,
                            (EStateM.bind (refCallHooks rp).getFrame
                              (fun frame => (refCallHooks rp).setFrame
                                { frame with location := .unwinding span })
                              { stack := ⟨Array.mk ((pre ++ [mframe]) ++ [mf'])⟩
                                machine := m }) =
                              .ok () {
                                stack := ⟨Array.mk ((pre ++ [mframe]) ++
                                  [{ mf' with location := .unwinding span }])⟩
                                machine := m
                              } := by
                          intro span mf' m
                          have h_g : (refCallHooks rp).getFrame
                              { stack := ⟨Array.mk ((pre ++ [mframe]) ++ [mf'])⟩
                                machine := m } =
                              .ok mf'
                                { stack := ⟨Array.mk ((pre ++ [mframe]) ++ [mf'])⟩
                                  machine := m } := by
                            dsimp only [refCallHooks]; rw [stack_currentFrame?_append]
                          rw [eStateM_bind_ok h_g]
                          dsimp only [refCallHooks]
                          rw [array_isEmpty_append_singleton,
                            array_pop_append_singleton, array_push_mk]
                          rfl
                        repeat rw [eStateM_bind_assoc]
                        rw [eStateM_bind_ok (h_ls0 _)]
                        repeat rw [eStateM_bind_assoc]
                        refine congr_bind_ok (h_ss_post ⟨0⟩ mf_end _) ?_
                        repeat rw [eStateM_bind_assoc]
                        have h_retCompat : ∀ s,
                            (refCallHooks rp).checkArgumentCompat ()
                              ((refCallHooks rp).abiReturn rbody.argumentCount)
                              ((refCallHooks rp).abiReturn rbody.argumentCount) s =
                              .ok true s := fun _ => rfl
                        rw [eStateM_bind_ok (h_retCompat _)]
                        rw [ite_eq_left rfl]
                        have h_prot_dst :
                            (refCallHooks rp).protectArgument () destMplace {
                              stack := ⟨Array.mk ((pre ++ [mframe]) ++
                                [{ mf_end with location := .unwinding ⟨0⟩ }])⟩
                              machine := {
                                frames :=
                                  liftFrame body.locals
                                    { f with locals := localsAfterArgs } :: rcallers
                                calleeInit :=
                                  some { ci₀ with argValsRev := argVals.reverse }
                              }
                            } = .ok () {
                              stack := ⟨Array.mk ((pre ++ [mframe]) ++
                                [{ mf_end with location := .unwinding ⟨0⟩ }])⟩
                              machine := {
                                frames :=
                                  liftFrame body.locals
                                    { f with locals := localsAfterDeinit } :: rcallers
                                calleeInit :=
                                  some { ci₀ with argValsRev := argVals.reverse }
                              }
                            } := by
                          dsimp only [refCallHooks, destMplace, rdest, liftFrame]
                          rw [refDeinitPlace_eq h_ty h_canon, h_deinit]
                          rfl
                        repeat rw [eStateM_bind_assoc]
                        rw [eStateM_bind_ok h_prot_dst]
                        repeat rw [eStateM_bind_assoc]
                        refine congr_bind_ok (h_ss_post ⟨0⟩ _ _) ?_
                        repeat rw [eStateM_bind_assoc]
                        rw [eStateM_bind_pure]
                        repeat rw [eStateM_bind_assoc]
                        have h_ceq :
                            (calleeBody.argumentCount ==
                              (Array.replicate rbody.argumentCount ()).size) = true := by
                          rw [Array.size_replicate, h_carg]
                          exact beq_self_eq_true _
                        rw [h_ceq]
                        refine congr_bind_ok (a := ()) (s' := _) rfl ?_
                        have h_not_lt : ¬ (calleeBody.argumentCount < evaluated.size) := by
                          rw [h_ev_size, h_arity_eq]
                          exact Nat.lt_irrefl _
                        rw [ite_eq_right h_not_lt]
                        repeat rw [eStateM_bind_assoc]
                        have h_afi : ∀ s, (refCallHooks rp).afterFrameInit () s = .ok () s :=
                          fun _ => rfl
                        rw [eStateM_bind_ok (h_afi _)]
                        let calleeLocals :=
                          initLocalsLoop calleeBody argVals 0 calleeBody.locals
                        let callerFrame' : FrameState :=
                          { f with locals := localsAfterDeinit }
                        let calleeFrame : FrameState := {
                          defId := callee
                          blockIdx := 0
                          stmtIdx := 0
                          locals := calleeLocals
                          returnCont := some ⟨resolvedDst, target, unwind⟩
                        }
                        let mf_done : RefMiriFrame :=
                          { { { mf_end with location := .unwinding ⟨0⟩ } with
                              location := .unwinding ⟨0⟩ } with
                            location := .mir ⟨0, 0⟩ }
                        let st_done : RefStepState := {
                          stack := ⟨Array.mk ((pre ++ [mframe]) ++ [mf_done])⟩
                          machine := {
                            frames :=
                              liftFrame calleeBody.locals calleeFrame ::
                                liftFrame body.locals callerFrame' :: rcallers
                            calleeInit := none
                          }
                        }
                        have h_pd :
                            (refCallHooks rp).pushDone () {
                              stack := ⟨Array.mk ((pre ++ [mframe]) ++
                                [{ { mf_end with location := .unwinding ⟨0⟩ } with
                                   location := .unwinding ⟨0⟩ }])⟩
                              machine := {
                                frames :=
                                  liftFrame body.locals callerFrame' :: rcallers
                                calleeInit :=
                                  some { ci₀ with argValsRev := argVals.reverse }
                              }
                            } = .ok () st_done := by
                          dsimp only [refCallHooks, ci₀]
                          rw [List.reverse_reverse,
                            initRefLocalsLoop_eq h_rcb_dec argVals 0 calleeBody.locals,
                            goToBlock_append]
                          rfl
                        rw [eStateM_bind_ok h_pd]
                        have h_dealloc :
                            Miri.Interpreter.Call.deallocateTempArgs (refCallHooks rp) ()
                              (Array.mk []) st_done = .ok () st_done := rfl
                        repeat rw [eStateM_bind_assoc]
                        rw [eStateM_bind_ok h_dealloc]
                        repeat rw [eStateM_bind_assoc]
                        rw [eStateM_bind_pure]
                        dsimp only
                        repeat rw [eStateM_bind_assoc]
                        rw [eStateM_bind_pure]
                        have h_fi_done :
                            (refCallHooks rp).frameIndex st_done =
                              .ok (pre.length + 1) st_done := by
                          dsimp only [refCallHooks, st_done]
                          rw [stack_frameIndex_append, List.length_append,
                            List.length_singleton]
                        cases target with
                        | none =>
                          dsimp only [Option.isSome]
                          rw [ite_eq_right Bool.false_ne_true]
                          dsimp only [evalCallPost, EStateM.pure,
                            extractMirLocation?, mapStepRes, liftFrames]
                          rw [h_cb, h_f_body, liftFrames_eq_of_framesSimInv h_cs,
                            stack_currentFrame?_append]
                          rfl
                        | some nextBb =>
                          dsimp only [Option.isSome]
                          rw [ite_eq_left rfl]
                          rw [eStateM_bind_ok h_fi_done]
                          have h_neq : ((pre.length + 1 == pre.length) : Bool) = false :=
                            nat_succ_beq_self_false pre.length
                          rw [h_neq, ite_eq_right Bool.false_ne_true]
                          dsimp only [evalCallPost, EStateM.pure,
                            st_done, st₀, stk, Array.size]
                          simp only [Option.isSome, List.length_append,
                            List.length_singleton, nat_succ_beq_self_false,
                            Bool.true_and, Bool.false_and, Bool.false_eq_true,
                            ite_false]
                          dsimp only [extractMirLocation?, mapStepRes, liftFrames]
                          rw [h_cb, h_f_body, liftFrames_eq_of_framesSimInv h_cs,
                            stack_currentFrame?_append]
                          rfl

private theorem evalRefTerminator_callBuiltin_eq {rp : RefProg} {p : Program}
    {body : Body} {rbb : RefBasicBlock} {f : FrameState}
    {callers : List FrameState} {rcallers : List RefFrameState}
    {callerMem : CallerMemory} {builtin : CoreBuiltin}
    {rargs : List RefOperand} {args : List Operand}
    {rdst : RefPlace} {dst : Place}
    {target : Option BasicBlockId} {unwind : UnwindAction}
    (h_f_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_len : f.locals.length = body.locals.length)
    (h_cs : FramesSimInv p callers rcallers)
    (h_rt : rbb.terminator = .callBuiltin builtin rargs rdst target unwind)
    (h_args : mapOption (decodeOperand rp.types) rargs = some args)
    (h_dst : decodePlace rp.types rdst = some dst) :
    evalRefTerminator rp rbb (liftFrame body.locals f) rcallers callerMem =
      mapStepRes p
        (evalTerminator p body
          { statements := []
            terminator := .callBuiltin builtin args dst target unwind
            cleanup := rbb.cleanup }
          f callers callerMem) := by
  let ⟨h_dst_id, h_dst_proj⟩ := decodePlace_proj_inv h_dst
  unfold evalTerminator
  dsimp only
  have h_ov_eq :
      refAnyMoveOperandMayOverlapPlace (toMiriPlace rdst)
        ((Array.mk (rargs.map (fun a =>
          (⟨⟨0⟩, toMiriOperand a⟩ : Miri.MIR.SpannedOperand)))).toList.map
          (fun a => a.operand)) =
      anyMoveOperandMayOverlapPlace dst args := by
    dsimp only [Array.toList]
    rw [List.map_map]
    exact refAnyMoveOperandMayOverlapPlace_eq h_dst h_args
  refine of_bool_true_else (anyMoveOperandMayOverlapPlace dst args)
    (fun h_ov => ?_) (fun h_ov_f => ?_)
  · rw [h_ov] at h_ov_eq
    rw [h_ov]
    exact evalRefTerminator_call_overlap (by rw [h_rt]; rfl) h_ov_eq
  rw [h_ov_f] at h_ov_eq
  rw [h_ov_f, ite_false_eq_true]
  refine evalRefTerminator_call_bridge (by rw [h_rt]; rfl) h_ov_eq ?_
  rw [h_rt]
  let mirTerm : Miri.MIR.Terminator :=
    toMiriTerminatorForDispatch (.callBuiltin builtin rargs rdst target unwind)
  let mframe : RefMiriFrame := {
    mkSingleLocalMiriFrame
      (.dead : Miri.Interpreter.LocalValue RefCallProv) rbb.cleanup with
    body := {
      refDummyMirBody rbb.cleanup with
      basicBlocks := Array.mk [{ refDummyMirBlock rbb.cleanup with
        terminator := mirTerm }]
    }
    bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex
      (if (liftFrame body.locals f).returnCont.isNone then 0 else 1)
    returnContinuation :=
      match (liftFrame body.locals f).returnCont with
      | none => .goto (some 0) .Continue
      | some c => .goto c.target (toMiriUnwindAction c.unwind)
    location := .mir ⟨0, 1⟩
  }
  let pre : List RefMiriFrame := refSentinelMiriFrame :: mkCallerMiriFrames rcallers
  let stk : Miri.Interpreter.Stack RefCallProv Miri.Interpreter.LocalLayout Unit :=
    ⟨Array.mk (pre ++ [mframe])⟩
  let st₀ : RefStepState :=
    { stack := stk, machine := { frames := liftFrame body.locals f :: rcallers } }
  change evalCallPost rp callerMem rcallers target st₀
    (Miri.Interpreter.Call.evalCallTerminator (refCallHooks rp) () 2 mirTerm st₀) = _
  unfold Miri.Interpreter.Call.evalCallTerminator
  dsimp only [mirTerm, toMiriTerminatorForDispatch, bind, Bind.bind,
    pure, Pure.pure]
  have h_fi : (refCallHooks rp).frameIndex st₀ = .ok pre.length st₀ := by
    dsimp only [refCallHooks, st₀, stk]
    rw [stack_frameIndex_append]
  have h_gf : (refCallHooks rp).getFrame st₀ = .ok mframe st₀ := by
    dsimp only [refCallHooks, st₀, stk]
    rw [stack_currentFrame?_append]
  rw [eStateM_bind_ok h_fi, eStateM_bind_ok h_gf]
  cases h_ty : MirSemantics.getElem? body.locals dst.localId with
  | none =>
    have h_ep : (refCallHooks rp).evalPlace () (toMiriPlace rdst) false st₀ =
        .error (.unsupported "missing call destination local") st₀ := by
      dsimp only [refCallHooks, st₀, liftFrame, toMiriPlace]
      rw [h_dst_id, getElem?_zipRefLocals_none_left h_ty]
      rfl
    rw [eStateM_bind_error h_ep]
    rfl
  | some localTy =>
    dsimp only
    cases h_sl : MirSemantics.getElem? f.locals dst.localId with
    | none =>
      let ⟨s', hs'⟩ := getElem?_some_of_length_eq h_len.symm h_ty
      rw [h_sl] at hs'
      cases hs'
    | some dstSlot =>
      have h_z := getElem?_zipRefLocals_some h_ty h_sl
      cases h_pt : projectTy? localTy dst.projection with
      | none =>
        dsimp only
        have h_ep : (refCallHooks rp).evalPlace () (toMiriPlace rdst) false st₀ =
            .error (.unsupported "unsupported call destination") st₀ := by
          dsimp only [refCallHooks, st₀, liftFrame, toMiriPlace]
          rw [h_dst_id, h_z]
          dsimp only [Array.toList]
          rw [refProjectTy?_eq h_dst_proj, h_pt]
          rfl
        rw [eStateM_bind_error h_ep]
        rfl
      | some dstTy =>
        dsimp only
        have h_res_eq := refResolveProjPath_eq (bodyLocals := body.locals)
          (slots := f.locals) h_dst_proj (.ty localTy)
        dsimp only [placeTyToRefPlaceTy] at h_res_eq
        cases h_rp_dst : resolveProjPath body.locals f.locals (.ty localTy)
            dst.projection with
        | error k =>
          rw [h_rp_dst] at h_res_eq
          dsimp only
          have h_ep : (refCallHooks rp).evalPlace () (toMiriPlace rdst) false
              st₀ = .error (faultToStepError k) st₀ := by
            dsimp only [refCallHooks, st₀, liftFrame, toMiriPlace]
            simp only [Bool.false_eq_true, ite_false]
            rw [h_dst_id, h_z]
            dsimp only [Array.toList]
            rw [refProjectTy?_eq h_dst_proj, h_pt]
            dsimp only
            rw [h_res_eq]
          rw [eStateM_bind_error h_ep]
          cases k <;> rfl
        | ok resolvedProj =>
        rw [h_rp_dst] at h_res_eq
        let ⟨resolvedMiriProj, h_res_ok, h_mdec, h_canon⟩ := h_res_eq
        dsimp only
        let resolvedDst : Place := ⟨dst.localId, resolvedProj⟩
        let rdest : RefDest := ⟨dst.localId, resolvedMiriProj, .ty dstTy⟩
        let destPlace : Miri.Interpreter.RuntimeStackPlace RefCallProv :=
          .memory ⟨⟨⟨Miri.ABI.Size.ZERO, some (.dst rdest resolvedDst)⟩,
              .none, none⟩,
            refSizedLocalLayout⟩
        have h_ep : (refCallHooks rp).evalPlace () (toMiriPlace rdst) false st₀ =
            .ok destPlace st₀ := by
          dsimp only [refCallHooks, st₀, liftFrame, toMiriPlace, destPlace,
            rdest, resolvedDst]
          simp only [Bool.false_eq_true, ite_false]
          rw [h_dst_id, h_z]
          dsimp only [Array.toList]
          rw [refProjectTy?_eq h_dst_proj, h_pt]
          dsimp only
          rw [h_res_ok]
          dsimp only
          rw [h_mdec]
        rw [eStateM_bind_ok h_ep]
        let tag : Nat := coreBuiltinTag builtin
        have h_eca := evalCalleeAndArgs_eq (rp := rp) (body := body)
          (f := f) (rcallers := rcallers) (stk := stk)
          (2 * tag + 1) (toMiriPlace rdst) h_args
        cases h_ec : evalCallArgs body.locals f.locals args with
        | error k =>
          dsimp only
          rw [h_ec] at h_eca
          let ⟨st_err, h_err⟩ := h_eca
          rw [eStateM_bind_error h_err]
          cases k <;> rfl
        | ok res =>
          let ⟨argPairs, localsAfterArgs⟩ := res
          dsimp only
          rw [h_ec] at h_eca
          let ⟨evaluated, h_ev_ok, h_ev_m⟩ := h_eca
          have h_mod : Nat.beq (Nat.mod (2 * tag + 1) 2) 0 = false := by
            dsimp only [tag]
            cases builtin <;> rfl
          have h_div : Nat.div (2 * tag + 1) 2 = tag := by
            dsimp only [tag]
            cases builtin <;> rfl
          rw [h_mod, h_div] at h_ev_ok
          simp only [Bool.false_eq_true, ite_false] at h_ev_ok
          rw [eStateM_bind_ok h_ev_ok]
          have h_unw_can : (Option.any (refCallHooks rp).abiCanUnwind
              (some (match MirSemantics.getElem? rp.bodies tag with
                | some rbody => rbody.argumentCount
                | none => 0))) = true := rfl
          rw [h_unw_can]
          simp only [ite_true]
          let st₁ : RefStepState := {
            stack := stk
            machine := {
              frames :=
                liftFrame body.locals { f with locals := localsAfterArgs } :: rcallers
            }
          }
          unfold Miri.Interpreter.Call.initFnCall Miri.Interpreter.Call.initFnCallStep
          dsimp only [bind, Bind.bind, pure, Pure.pure]
          have h_abi_not :
              (Option.any (fun abi => !(refCallHooks rp).abiCanUnwind abi)
                (some (match MirSemantics.getElem? rp.bodies tag with
                  | some rbody => rbody.argumentCount
                  | none => 0))) = false := rfl
          rw [h_abi_not]
          simp only [Bool.false_eq_true, ite_false]
          repeat rw [eStateM_bind_assoc]
          refine congr_bind_ok (a := ()) (s' := st₁) rfl ?_
          repeat rw [eStateM_bind_assoc]
          refine congr_bind_ok (a := (evaluated, (Array.mk []))) (s' := st₁) rfl ?_
          rw [Array.append_empty]
          repeat rw [eStateM_bind_assoc]
          refine congr_bind_cleanup_strip ?_ ?_ ?_ ?_
          · rfl
          · intro _ _; rfl
          · intro _ _; rfl
          have h_tag_rt : coreBuiltinOfTag? tag = some builtin := by
            cases builtin <;> rfl
          have h_map_ext :
              mapOption extractRefCallArg?
                  (evaluated.map Miri.Interpreter.FnArg.copyFnArg).toList =
                some argPairs := by
            rw [Array.toList_map]
            exact refFnArgsMatch_map_extract h_ev_m
          have h_ci :
              (refCallHooks rp).callIntrinsic ()
                  { kind := .Intrinsic tag, args := Array.empty }
                  (evaluated.map Miri.Interpreter.FnArg.copyFnArg)
                  destPlace target (toMiriUnwindAction unwind) st₁ =
                match readBuiltinArgs builtin argPairs with
                | .error k => .error (faultToStepError k) st₁
                | .ok argVals =>
                  match evalCoreBuiltin builtin dstTy argVals with
                  | .error k => .error (faultToStepError k) st₁
                  | .ok resVal =>
                    match writePlaceWithLocalTy localTy localsAfterArgs
                        resolvedDst dstTy resVal with
                    | .error k => .error (faultToStepError k) st₁
                    | .ok localsAfterWrite =>
                      let st₂ : RefStepState := {
                        stack := stk
                        machine := {
                          frames :=
                            liftFrame body.locals { f with locals := localsAfterWrite } ::
                              rcallers
                        }
                      }
                      match target with
                      | some nextBb =>
                        .ok none {
                          stack := ⟨Array.mk (pre ++ [{ mframe with location := .mir ⟨nextBb, 0⟩ }])⟩
                          machine := st₂.machine
                        }
                      | none => .error (.undefinedBehavior "Unreachable") st₂ := by
            dsimp only [refCallHooks, destPlace, rdest, RefDest.ty?, st₁,
              liftFrame]
            rw [h_tag_rt, h_map_ext]
            dsimp only
            rw [refReadBuiltinArgs_eq]
            cases readBuiltinArgs builtin argPairs with
            | error k => rfl
            | ok argVals =>
              dsimp only
              rw [evalRefCoreBuiltin_eq]
              cases evalCoreBuiltin builtin dstTy argVals with
              | error k => rfl
              | ok resVal =>
                dsimp only
                rw [writeRefPlace_eq h_ty h_canon]
                cases writePlaceWithLocalTy localTy localsAfterArgs
                    resolvedDst dstTy resVal with
                | error k => rfl
                | ok localsAfterWrite =>
                  dsimp only [mapSlotsRes, Miri.Interpreter.ControlFlow.returnToBlock]
                  cases target with
                  | none => rfl
                  | some nextBb =>
                    dsimp only [stk]
                    rw [goToBlock_append]
          cases h_rp : readBuiltinArgs builtin argPairs with
          | error k =>
            rw [h_rp] at h_ci
            first | dsimp only at h_ci | change _
            first | dsimp only | change _
            rw [eStateM_bind_error h_ci]
            cases k <;> rfl
          | ok argVals =>
            rw [h_rp] at h_ci
            first | dsimp only at h_ci | change _
            first | dsimp only | change _
            cases h_eb : evalCoreBuiltin builtin dstTy argVals with
            | error k =>
              rw [h_eb] at h_ci
              first | dsimp only at h_ci | change _
              first | dsimp only | change _
              rw [eStateM_bind_error h_ci]
              cases k <;> rfl
            | ok resVal =>
              rw [h_eb] at h_ci
              first | dsimp only at h_ci | change _
              first | dsimp only | change _
              cases h_wr : writePlaceWithLocalTy localTy localsAfterArgs
                  resolvedDst dstTy resVal with
              | error k =>
                rw [h_wr] at h_ci
                first | dsimp only at h_ci | change _
                first | dsimp only | change _
                rw [eStateM_bind_error h_ci]
                cases k <;> rfl
              | ok localsAfterWrite =>
                rw [h_wr] at h_ci
                first | dsimp only at h_ci | change _
                first | dsimp only | change _
                cases target with
                | none =>
                  first | dsimp only at h_ci | change _
                  first | dsimp only | change _
                  rw [eStateM_bind_error h_ci]
                  rfl
                | some nextBb =>
                  first | dsimp only at h_ci | change _
                  first | dsimp only | change _
                  rw [eStateM_bind_ok h_ci]
                  dsimp only
                  let st_done : RefStepState := {
                    stack := ⟨Array.mk (pre ++ [{ mframe with location := .mir ⟨nextBb, 0⟩ }])⟩
                    machine := {
                      frames :=
                        liftFrame body.locals { f with locals := localsAfterWrite } ::
                          rcallers
                    }
                  }
                  have h_dealloc :
                      Miri.Interpreter.Call.deallocateTempArgs (refCallHooks rp) ()
                        (Array.mk []) st_done = .ok () st_done := rfl
                  rw [eStateM_bind_assoc, eStateM_bind_ok h_dealloc,
                    eStateM_bind_pure]
                  dsimp only
                  rw [eStateM_bind_pure]
                  simp only [Option.isSome, ite_true]
                  have h_fi_done : (refCallHooks rp).frameIndex st_done =
                      .ok pre.length st_done := by
                    dsimp only [refCallHooks, st_done]
                    rw [stack_frameIndex_append]
                  have h_gf_done : (refCallHooks rp).getFrame st_done =
                      .ok { mframe with location := .mir ⟨nextBb, 0⟩ } st_done := by
                    dsimp only [refCallHooks, st_done]
                    rw [stack_currentFrame?_append]
                  rw [eStateM_bind_ok h_fi_done]
                  simp only [beq_self_eq_true, ite_true]
                  rw [eStateM_bind_ok h_gf_done]
                  have h_loc_ne :
                      ((Miri.Interpreter.FrameLocation.mir ⟨nextBb, 0⟩ ==
                        Miri.Interpreter.FrameLocation.mir ⟨0, 1⟩) : Bool) = false := by
                    cases nextBb <;> rfl
                  rw [h_loc_ne, ite_eq_right (fun h => Bool.noConfusion h)]
                  dsimp only [evalCallPost, EStateM.pure, st_done, st₀, stk, mframe]
                  rw [stack_currentFrame?_append, stack_currentFrame?_append]
                  dsimp only [Option.map]
                  have h_opt_loc_ne :
                      ((some (Miri.Interpreter.FrameLocation.mir ⟨nextBb, 0⟩) ==
                        some (Miri.Interpreter.FrameLocation.mir ⟨0, 1⟩)) : Bool) = false := by
                    cases nextBb <;> rfl
                  simp only [h_opt_loc_ne, Bool.and_false, Bool.false_eq_true, ite_false]
                  dsimp only [extractMirLocation?, jumpToBlock, mapStepRes,
                    liftFrames]
                  rw [h_f_body, liftFrames_eq_of_framesSimInv h_cs,
                    stack_currentFrame?_append]
                  rfl

theorem evalRefTerminator_eq {rp : RefProg} {p : Program} {body : Body}
    {rbb : RefBasicBlock} {bb : BasicBlock} {f : FrameState}
    {callers : List FrameState} {rcallers : List RefFrameState}
    {callerMem : CallerMemory}
    (h_dec : decodeProg rp = some p)
    (h_f_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_len : f.locals.length = body.locals.length)
    (h_cs : FramesSimInv p callers rcallers)
    (h_cleanup : rbb.cleanup = bb.cleanup)
    (h_term : decodeTerminator rp.types rbb.terminator = some bb.terminator) :
    evalRefTerminator rp rbb (liftFrame body.locals f) rcallers callerMem =
      mapStepRes p (evalTerminator p body bb f callers callerMem) := by
  have h_f_sim : FrameSimInv p f (liftFrame body.locals f) :=
    ⟨body, h_f_body, h_len, rfl⟩
  cases h_rt : rbb.terminator with
  | goto target =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    rw [evalRefTerminator_eq_of_term, h_rt]
    unfold evalTerminator
    rw [← h_eq]
    dsimp only [Miri.Interpreter.ControlFlow.evalTerminator,
      toMiriTerminatorForDispatch, mkRefTermStepState, jumpToBlock,
      mapStepRes, liftFrames, extractMirLocation?]
    rw [goToBlock_append]
    dsimp only [Id.run, Pure.pure]
    rw [stack_currentFrame?_append, h_f_body,
      liftFrames_eq_of_framesSimInv h_cs]
    rfl
  | switchInt rdiscr targets =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap] at h_term
    cases h_d : decodeOperand rp.types rdiscr with
    | none => rw [h_d] at h_term; cases h_term
    | some discr =>
      rw [h_d] at h_term
      injection h_term with h_eq
      rw [evalRefTerminator_switchInt _ _ _ _ _ _ _ h_rt]
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
                  targets.branches with
              | error _ => rfl
              | ok target =>
                dsimp only [jumpToBlock, mapStepRes, liftFrames, liftFrame]
                rw [h_f_body, liftFrames_eq_of_framesSimInv h_cs]
            | bool b =>
              dsimp only
              cases evalBoolSwitchBranches b targets.otherwise
                  targets.branches with
              | error _ => rfl
              | ok target =>
                dsimp only [jumpToBlock, mapStepRes, liftFrames, liftFrame]
                rw [h_f_body, liftFrames_eq_of_framesSimInv h_cs]
            | unit | structVal _ _ | enumVal _ _ _ | tuple _ | array _ _
            | ptr _ | bytes _ => rfl
  | return_ =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    cases h_cl : bb.cleanup
    · rw [evalRefTerminator_return_false h_dec h_len h_cs h_rt
        (h_cleanup.trans h_cl)]
      unfold evalTerminator
      rw [← h_eq, h_cl]
    · rw [evalRefTerminator_return_true _ _ _ _ _ h_rt (h_cleanup.trans h_cl)]
      unfold evalTerminator
      rw [← h_eq, h_cl]
      rfl
  | unreachable =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    rw [evalRefTerminator_eq_of_term, h_rt]
    unfold evalTerminator
    rw [← h_eq]
    rfl
  | unwindResume =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    rw [evalRefTerminator_unwindResume h_f_sim h_cs h_rt]
    unfold evalTerminator
    rw [← h_eq, h_cleanup]
    cases bb.cleanup <;> rfl
  | assert rcond exp msg t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap] at h_term
    cases h_c : decodeOperand rp.types rcond with
    | none => rw [h_c] at h_term; cases h_term
    | some c =>
      rw [h_c] at h_term
      injection h_term with h_eq
      rw [evalRefTerminator_assert h_f_body h_len h_cs h_c h_rt]
      unfold evalTerminator
      rw [← h_eq]
      rfl
  | call callee rargs rdst t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap2] at h_term
    cases h_a : mapOption (decodeOperand rp.types) rargs with
    | none => rw [h_a] at h_term; cases h_term
    | some args =>
      cases h_dst : decodePlace rp.types rdst with
      | none => rw [h_a, h_dst] at h_term; cases h_term
      | some dst =>
        rw [h_a, h_dst] at h_term
        injection h_term with h_eq
        rw [evalRefTerminator_call_eq h_dec h_f_body h_len h_cs h_rt h_a h_dst]
        unfold evalTerminator
        rw [← h_eq]
  | callBuiltin builtin rargs rdst t u =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap2] at h_term
    cases h_a : mapOption (decodeOperand rp.types) rargs with
    | none => rw [h_a] at h_term; cases h_term
    | some args =>
      cases h_dst : decodePlace rp.types rdst with
      | none => rw [h_a, h_dst] at h_term; cases h_term
      | some dst =>
        rw [h_a, h_dst] at h_term
        injection h_term with h_eq
        rw [evalRefTerminator_callBuiltin_eq h_f_body h_len h_cs h_rt h_a h_dst]
        unfold evalTerminator
        rw [← h_eq]
  | unsupported =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    rw [evalRefTerminator_eq_of_term, h_rt]
    unfold evalTerminator
    rw [← h_eq]
    rfl

theorem evalStatement_step_inv {body : Body} {f : FrameState}
    {callers : List FrameState} {callerMem : CallerMemory}
    {stmt : StatementKind} {s' : State}
    (h_len : f.locals.length = body.locals.length)
    (h_step : evalStatement body f callers callerMem stmt = .step s') :
    ∃ f' : FrameState,
      s' = { frames := f' :: callers, callerMem := callerMem } ∧
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
  | setDiscriminant place variantIdx =>
    dsimp only [evalStatement] at h_step
    cases h_ty : MirSemantics.getElem? body.locals place.localId with
    | none => rw [h_ty] at h_step; cases h_step
    | some localTy =>
      rw [h_ty] at h_step
      dsimp only at h_step
      cases h_pt : projectTy? localTy place.projection with
      | none => rw [h_pt] at h_step; cases h_step
      | some dstTy =>
        rw [h_pt] at h_step
        dsimp only at h_step
        cases h_rp : resolveProjPath body.locals f.locals (.ty localTy)
            place.projection with
        | error _ => rw [h_rp] at h_step; cases h_step
        | ok resolvedProj =>
          rw [h_rp] at h_step
          dsimp only at h_step
          cases h_sd : evalSetDiscriminantResolved localTy f.locals
              ⟨place.localId, resolvedProj⟩ dstTy variantIdx with
          | error _ => rw [h_sd] at h_step; cases h_step
          | ok localsAfterWrite =>
            rw [h_sd] at h_step
            injection h_step with h_eq
            refine ⟨{ f with
                stmtIdx := f.stmtIdx + 1, locals := localsAfterWrite },
              h_eq.symm, rfl,
              (evalSetDiscriminantResolved_length h_sd).trans h_len⟩
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
          cases h_rp : resolveProjPath body.locals f.locals (.ty localTy)
              dst.projection with
          | error _ => rw [h_rp] at h_step; cases h_step
          | ok resolvedProj =>
            rw [h_rp] at h_step
            dsimp only at h_step
            cases rvalue with
            | aggregate kind ops =>
              dsimp only at h_step
              cases h_wa : writeAggregate body.locals localTy f.locals
                  ⟨dst.localId, resolvedProj⟩ dstTy kind ops with
              | error _ => rw [h_wa] at h_step; cases h_step
              | ok localsAfterWrite =>
                rw [h_wa] at h_step
                injection h_step with h_eq
                have h_len₁ := (writeAggregate_length h_wa).trans h_len
                refine ⟨{ f with
                    stmtIdx := f.stmtIdx + 1, locals := localsAfterWrite },
                  h_eq.symm, rfl, h_len₁⟩
            | use _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _
            | ref _ _ | addressOf _ _ | cast _ _ _ | repeat_ _ _
            | unsupported =>
              cases h_rv : evalRvalue body.locals f.locals dstTy _ with
              | error _ => rw [h_rv] at h_step; cases h_step
              | ok res =>
                rw [h_rv] at h_step
                cases res with | mk val localsAfterRval =>
                dsimp only at h_step
                cases h_wr : writePlaceWithLocalTy localTy localsAfterRval
                    ⟨dst.localId, resolvedProj⟩ dstTy val with
                | error _ => rw [h_wr] at h_step; cases h_step
                | ok localsAfterWrite =>
                  rw [h_wr] at h_step
                  injection h_step with h_eq
                  have h_len₁ := (evalRvalue_length h_rv).trans h_len
                  have h_len₂ := (writePlaceWithLocalTy_length h_wr).trans h_len₁
                  refine ⟨{ f with
                      stmtIdx := f.stmtIdx + 1, locals := localsAfterWrite },
                    h_eq.symm, rfl, h_len₂⟩
        · cases h_step
  | unsupported => cases h_step

private theorem framesSimInv_liftFrames {p : Program}
    {fs : List FrameState} {rfs : List RefFrameState}
    (h : FramesSimInv p fs rfs) :
    FramesSimInv p fs (liftFrames p fs) := by
  rw [liftFrames_eq_of_framesSimInv h]
  exact h

theorem unwindFrame_step_inv {p : Program} {callerMem : CallerMemory}
    {f : FrameState} {callers : List FrameState}
    {rf : RefFrameState} {rcallers : List RefFrameState}
    {unwind : UnwindAction} {s' : State}
    (h_f : FrameSimInv p f rf)
    (h_cs : FramesSimInv p callers rcallers)
    (h_step : unwindFrame callerMem f callers unwind = .step s') :
    s'.frames ≠ [] ∧
    s'.callerMem = callerMem ∧
    FramesSimInv p s'.frames (liftFrames p s'.frames) := by
  induction callers generalizing f rf rcallers unwind with
  | nil =>
    cases rcallers with
    | cons _ _ => cases h_cs
    | nil =>
      cases unwind with
      | cleanup block =>
        injection h_step with h_eq
        subst h_eq
        let ⟨body, h_b, h_len, _⟩ := h_f
        refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
        dsimp only [liftFrames]
        rw [h_b]
        exact ⟨⟨body, h_b, h_len, rfl⟩, trivial⟩
      | unreachable | terminate => cases h_step
      | continue_ =>
        dsimp only [unwindFrame] at h_step
        cases h_rc : f.returnCont <;> rw [h_rc] at h_step <;> cases h_step
  | cons caller rest ih =>
    cases rcallers with
    | nil => cases h_cs
    | cons rcaller rrest =>
      cases unwind with
      | cleanup block =>
        injection h_step with h_eq
        subst h_eq
        let ⟨body, h_b, h_len, _⟩ := h_f
        refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
        dsimp only [liftFrames]
        rw [h_b]
        exact ⟨⟨body, h_b, h_len, rfl⟩, framesSimInv_liftFrames h_cs⟩
      | unreachable | terminate => cases h_step
      | continue_ =>
        dsimp only [unwindFrame] at h_step
        cases h_rc : f.returnCont with
        | none => rw [h_rc] at h_step; cases h_step
        | some cont =>
          rw [h_rc] at h_step
          exact ih h_cs.1 h_cs.2 h_step

theorem evalTerminator_step_inv {p : Program} {body : Body} {bb : BasicBlock}
    {f : FrameState} {callers : List FrameState}
    {rcallers : List RefFrameState} {callerMem : CallerMemory} {s' : State}
    (h_f_body : MirSemantics.getElem? p.bodies f.defId = some body)
    (h_len : f.locals.length = body.locals.length)
    (h_cs : FramesSimInv p callers rcallers)
    (h_step : evalTerminator p body bb f callers callerMem = .step s') :
    s'.frames ≠ [] ∧
    s'.callerMem = callerMem ∧
    FramesSimInv p s'.frames (liftFrames p s'.frames) := by
  have h_f_sim : FrameSimInv p f (liftFrame body.locals f) :=
    ⟨body, h_f_body, h_len, rfl⟩
  cases bb with | mk stmts term cleanup =>
  cases term with
  | goto target =>
    injection h_step with h_eq
    subst h_eq
    refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
    dsimp only [liftFrames]
    rw [h_f_body]
    exact ⟨⟨body, h_f_body, h_len, rfl⟩, framesSimInv_liftFrames h_cs⟩
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
          cases h_v : sv₀.toVal? with
          | none => rw [h_v] at h_step; cases h_step
          | some retVal =>
            rw [h_v] at h_step
            dsimp only at h_step
            cases h_rc : f.returnCont with
            | none =>
              rw [h_rc] at h_step
              cases callers <;> cases h_step
            | some cont =>
              rw [h_rc] at h_step
              cases callers with
              | nil => cases h_step
              | cons caller rest =>
                cases rcallers with
                | nil => cases h_cs
                | cons rcaller rrest =>
                  let ⟨callerBody, h_cb, h_clen, _⟩ := h_cs.1
                  dsimp only [Bool.false_eq_true, ite_false] at h_step
                  rw [h_cb] at h_step
                  dsimp only at h_step
                  cases h_ty : MirSemantics.getElem? callerBody.locals cont.dst.localId with
                  | none => rw [h_ty] at h_step; cases h_step
                  | some localTy =>
                    rw [h_ty] at h_step
                    dsimp only at h_step
                    cases h_pt : projectTy? localTy cont.dst.projection with
                    | none => rw [h_pt] at h_step; cases h_step
                    | some dstTy =>
                      rw [h_pt] at h_step
                      dsimp only at h_step
                      cases h_rs : resolveStaticProjPath (.ty localTy)
                          cont.dst.projection with
                      | error _ => rw [h_rs] at h_step; cases h_step
                      | ok resolvedProj =>
                        rw [h_rs] at h_step
                        dsimp only at h_step
                        cases h_wr : writePlaceWithLocalTy localTy caller.locals
                            ⟨cont.dst.localId, resolvedProj⟩ dstTy retVal with
                        | error _ => rw [h_wr] at h_step; cases h_step
                        | ok callerLocals' =>
                          rw [h_wr] at h_step
                          dsimp only at h_step
                          cases h_t : cont.target with
                          | none => rw [h_t] at h_step; cases h_step
                          | some nextBb =>
                            rw [h_t] at h_step
                            injection h_step with h_eq
                            subst h_eq
                            refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
                            dsimp only [liftFrames]
                            rw [h_cb]
                            exact ⟨⟨callerBody, h_cb,
                                (writePlaceWithLocalTy_length h_wr).trans
                                  h_clen,
                                rfl⟩,
                              framesSimInv_liftFrames h_cs.2⟩
    · cases h_step
  | unreachable | unsupported =>
    cases h_step
  | unwindResume =>
    dsimp only [evalTerminator] at h_step
    cases cleanup with
    | false => cases h_step
    | true => exact unwindFrame_step_inv h_f_sim h_cs h_step
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
          · exact unwindFrame_step_inv
              (f := { f with locals := localsAfterCond })
              ⟨body, h_f_body, h_len₁, rfl⟩ h_cs h_step
        · injection h_step with h_eq
          subst h_eq
          refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
          dsimp only [liftFrames]
          rw [h_f_body]
          exact ⟨⟨body, h_f_body, h_len₁, rfl⟩, framesSimInv_liftFrames h_cs⟩
      | scalar _ | unit | structVal _ _ | enumVal _ _ _ | tuple _
      | array _ _ | ptr _ | bytes _ =>
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
          subst h_eq
          refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
          dsimp only [liftFrames]
          rw [h_f_body]
          exact ⟨⟨body, h_f_body, h_len₁, rfl⟩, framesSimInv_liftFrames h_cs⟩
      | bool b =>
        dsimp only at h_step
        cases h_sw : evalBoolSwitchBranches b targets.otherwise
            targets.branches <;>
          rw [h_sw] at h_step
        · cases h_step
        · injection h_step with h_eq
          subst h_eq
          refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
          dsimp only [liftFrames]
          rw [h_f_body]
          exact ⟨⟨body, h_f_body, h_len₁, rfl⟩, framesSimInv_liftFrames h_cs⟩
      | unit | structVal _ _ | enumVal _ _ _ | tuple _ | array _ _
      | ptr _ | bytes _ => cases h_step
  | call callee args dst target unwind =>
    dsimp only [evalTerminator] at h_step
    cases h_ov : anyMoveOperandMayOverlapPlace dst args with
    | true => rw [h_ov] at h_step; cases h_step
    | false =>
      rw [h_ov, ite_false_eq_true] at h_step
      cases h_ty : MirSemantics.getElem? body.locals dst.localId with
      | none => rw [h_ty] at h_step; cases h_step
      | some localTy =>
        rw [h_ty] at h_step; dsimp only at h_step
        cases h_pt : projectTy? localTy dst.projection with
        | none => rw [h_pt] at h_step; cases h_step
        | some dstTy =>
          rw [h_pt] at h_step; dsimp only at h_step
          cases h_rp_dst : resolveProjPath body.locals f.locals (.ty localTy)
              dst.projection with
          | error _ => rw [h_rp_dst] at h_step; cases h_step
          | ok resolvedProj =>
            rw [h_rp_dst] at h_step; dsimp only at h_step
            cases h_ec : evalCallArgs body.locals f.locals args with
            | error _ => rw [h_ec] at h_step; cases h_step
            | ok res =>
              let ⟨argPairs, localsAfterArgs⟩ := res
              rw [h_ec] at h_step; dsimp only at h_step
              have h_len₁ := (evalCallArgs_length h_ec).trans h_len
              cases h_cb : MirSemantics.getElem? p.bodies callee with
              | none => rw [h_cb] at h_step; cases h_step
              | some calleeBody =>
                rw [h_cb] at h_step; dsimp only at h_step
                cases h_adm : bodyEntryAdmitted calleeBody <;>
                  rw [h_adm] at h_step
                · cases h_step
                · dsimp only [Bool.not, ite_false_eq_true] at h_step
                  cases h_ar : Nat.beq argPairs.length calleeBody.argumentCount <;>
                    rw [h_ar] at h_step
                  · cases h_step
                  · dsimp only [Bool.not, ite_false_eq_true] at h_step
                    cases h_ret : MirSemantics.getElem? calleeBody.locals 0 with
                    | none => rw [h_ret] at h_step; cases h_step
                    | some calleeRetTy =>
                      rw [h_ret] at h_step; dsimp only at h_step
                      cases h_rt : MirTy.beq calleeRetTy dstTy <;>
                        rw [h_rt] at h_step
                      · cases h_step
                      · dsimp only [Bool.not, ite_false_eq_true] at h_step
                        cases h_deinit : deinitPlaceWithLocalTy localTy
                            localsAfterArgs ⟨dst.localId, resolvedProj⟩
                            dstTy with
                        | error _ => rw [h_deinit] at h_step; cases h_step
                        | ok localsAfterDeinit =>
                          rw [h_deinit] at h_step; dsimp only at h_step
                          cases h_vc : validateCallArgs argPairs
                              ((calleeBody.locals.drop 1).take
                                calleeBody.argumentCount) with
                          | error _ => rw [h_vc] at h_step; cases h_step
                          | ok argVals =>
                            rw [h_vc] at h_step
                            injection h_step with h_eq
                            subst h_eq
                            refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
                            dsimp only [liftFrames]
                            rw [h_cb, h_f_body]
                            exact ⟨⟨calleeBody, h_cb,
                                initLocalsLoop_length calleeBody argVals 0
                                  calleeBody.locals, rfl⟩,
                              ⟨body, h_f_body,
                                (deinitPlaceWithLocalTy_length h_deinit).trans
                                  h_len₁, rfl⟩,
                              framesSimInv_liftFrames h_cs⟩
  | callBuiltin builtin args dst target unwind =>
    dsimp only [evalTerminator] at h_step
    cases h_ov : anyMoveOperandMayOverlapPlace dst args with
    | true => rw [h_ov] at h_step; cases h_step
    | false =>
      rw [h_ov, ite_false_eq_true] at h_step
      cases h_ty : MirSemantics.getElem? body.locals dst.localId with
      | none => rw [h_ty] at h_step; cases h_step
      | some localTy =>
        rw [h_ty] at h_step; dsimp only at h_step
        cases h_pt : projectTy? localTy dst.projection with
        | none => rw [h_pt] at h_step; cases h_step
        | some dstTy =>
          rw [h_pt] at h_step; dsimp only at h_step
          cases h_rp_dst : resolveProjPath body.locals f.locals (.ty localTy)
              dst.projection with
          | error _ => rw [h_rp_dst] at h_step; cases h_step
          | ok resolvedProj =>
            rw [h_rp_dst] at h_step; dsimp only at h_step
            cases h_ec : evalCallArgs body.locals f.locals args with
            | error _ => rw [h_ec] at h_step; cases h_step
            | ok res =>
              let ⟨argPairs, localsAfterArgs⟩ := res
              rw [h_ec] at h_step; dsimp only at h_step
              have h_len₁ := (evalCallArgs_length h_ec).trans h_len
              cases h_rp : readBuiltinArgs builtin argPairs with
              | error _ => rw [h_rp] at h_step; cases h_step
              | ok argVals =>
                rw [h_rp] at h_step; dsimp only at h_step
                cases h_eb : evalCoreBuiltin builtin dstTy argVals with
                | error _ => rw [h_eb] at h_step; cases h_step
                | ok resVal =>
                  rw [h_eb] at h_step; dsimp only at h_step
                  cases h_wr : writePlaceWithLocalTy localTy localsAfterArgs
                      ⟨dst.localId, resolvedProj⟩ dstTy resVal with
                  | error _ => rw [h_wr] at h_step; cases h_step
                  | ok localsAfterWrite =>
                    rw [h_wr] at h_step; dsimp only at h_step
                    cases target with
                    | none => cases h_step
                    | some nextBb =>
                      injection h_step with h_eq
                      subst h_eq
                      refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
                      dsimp only [liftFrames]
                      rw [h_f_body]
                      exact ⟨⟨body, h_f_body,
                          (writePlaceWithLocalTy_length h_wr).trans h_len₁,
                          rfl⟩,
                        framesSimInv_liftFrames h_cs⟩

theorem evalStep_step_inv {p : Program} {c : Choice} {s s' : State}
    {rfs : List RefFrameState}
    (h_ne : s.frames ≠ [])
    (h_fs : FramesSimInv p s.frames rfs)
    (h_step : evalStep p c s = .step s') :
    s'.frames ≠ [] ∧
    s'.callerMem = s.callerMem ∧
    FramesSimInv p s'.frames (liftFrames p s'.frames) := by
  cases h_sf : s.frames with
  | nil => exact False.elim (h_ne h_sf)
  | cons f callers =>
    rw [h_sf] at h_fs
    cases rfs with
    | nil => cases h_fs
    | cons rf rcallers =>
      let ⟨⟨body, h_body, h_len, _⟩, h_cs⟩ := h_fs
      unfold evalStep at h_step
      rw [h_sf] at h_step
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
          · exact evalTerminator_step_inv h_body h_len h_cs h_step
        · let ⟨f', hs', hdef', hlen'⟩ := evalStatement_step_inv h_len h_step
          subst hs'
          have h_b' : MirSemantics.getElem? p.bodies f'.defId = some body := by
            rw [hdef']; exact h_body
          refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
          dsimp only [liftFrames]
          rw [h_b']
          exact ⟨⟨body, h_b', hlen', rfl⟩, framesSimInv_liftFrames h_cs⟩

private theorem step_invalidBlock_eq (rp : RefProg) (rframe : RefFrameState)
    (rcallers : List RefFrameState) (callerMem : CallerMemory)
    (blockIdx : BasicBlockId) :
    Miri.Interpreter.Step.step (refStepHooksFor rp callerMem) ()
        (mkRefInvalidBlockStepState rframe rcallers blockIdx) =
      (mkRefInvalidBlockStepState rframe rcallers blockIdx,
        .error (.invalidBlock blockIdx)) := by
  unfold Miri.Interpreter.Step.step mkRefInvalidBlockStepState
    mkRefStepStateWith
  cases blockIdx <;> rfl

/-- One $M_{\text{ref}}$ step from a simulated state computes exactly the
lifted $M_{\text{anneal}}$ step, with the caller sentinel restored beneath the
reversed active call stack. -/
theorem evalRefStep_eq : EvalRefStepEqClaim := by
  intro rp p s rs rfs retTy h_dec h_ne hrs hcm h_fs h_lt c
  cases h_sf : s.frames with
  | nil => exact False.elim (h_ne h_sf)
  | cons f callers =>
    rw [h_sf] at h_fs
    cases rfs with
    | nil => cases h_fs
    | cons rf rcallers =>
      let ⟨⟨body, h_body, h_len, hrf⟩, h_cs⟩ := h_fs
      let ⟨_, _, _, _, h_bodies⟩ := decodeProg_inv h_dec
      let ⟨rbody, h_rbody_get, h_rbody_dec⟩ :=
        (mapOption_getElem? h_bodies f.defId).2 body h_body
      let ⟨_, _, h_bbs_dec, _, _⟩ := decodeBody_inv h_rbody_dec
      have h_no_sent :
          (rf :: rcallers).reverse.any (fun fr => fr.isCallerSentinel) = false :=
        framesSimInv_any_isCallerSentinel h_fs
      unfold evalRefStep evalStep
      rw [h_lt, hrs, h_sf, hcm]
      dsimp only [callerSentinelFrame]
      rw [h_no_sent, List.reverse_reverse, hrf]
      dsimp only [liftFrame]
      rw [h_rbody_get, h_body]
      dsimp only
      cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
      | none =>
        rw [(mapOption_getElem? h_bbs_dec f.blockIdx).1 h_bb]
        dsimp only
        rw [step_invalidBlock_eq]
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
              (evalRefTerminator_eq h_dec h_body h_len h_cs h_cleanup h_term_dec)
        | some stmt =>
          let ⟨rstmt, h_rstmt_get, h_rstmt_dec⟩ :=
            (mapOption_getElem? h_stmts_dec f.stmtIdx).2 stmt h_st
          rw [h_rstmt_get]
          dsimp only
          exact congrArg
            (stepResultToRefOutcome (callerSentinelFrame retTy)
              rs.stepsExecuted rs.maxSteps)
            (evalRefStatement_eq h_body h_len h_cs h_rstmt_dec)

/-! ## Entry Initialization Simulation (`initRefState_sim`) -/

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
  · dsimp only
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
          let ⟨h_arg, h_loc_dec, _, _, _⟩ := decodeBody_inv h_rb_dec
          rw [h_rb_get]
          dsimp only
          rw [h_loc_dec]
          dsimp only
          rw [refBodyEntryAdmitted_eq h_rb_dec, h_arg]
          cases h_adm : bodyEntryAdmitted body
          · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
            intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
          · rw [checkRefArgsMatch_eq]
            cases checkArgsMatch q.args
                ((body.locals.drop 1).take body.argumentCount)
            · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
              intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
            · have h_blt : Nat.blt body.argumentCount body.locals.length = true := by
                unfold bodyEntryAdmitted at h_adm
                cases h1 : body.basicBlocks.isEmpty with
                | true => rw [h1] at h_adm; cases h_adm
                | false =>
                  rw [h1] at h_adm
                  cases h2 : Nat.blt body.argumentCount body.locals.length with
                  | false => rw [h2] at h_adm; cases h_adm
                  | true => rfl
              let ⟨retTy, h_ret⟩ := getElem?_zero_of_blt h_blt
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
                exact ⟨[liftFrame body.locals
                    { defId := p.entryDefId, blockIdx := 0, stmtIdx := 0,
                      locals := initLocalsLoop body q.args 0 body.locals,
                      returnCont := none }],
                  retTy, List.cons_ne_nil _ _, rfl, rfl, h_entry_ret,
                  ⟨body, h_b, initLocalsLoop_length body q.args 0 body.locals, rfl⟩,
                  trivial⟩

/-! ## Multi-Step Reachability and `anneal_corresponds_to_miri` -/

/-- Backward simulation for one step: a running $M_{\text{ref}}$ transition
from a simulated state is matched by an $M_{\text{anneal}}$ transition that
re-establishes `SimulationInv`. -/
theorem sim_of_refStep : SimOfRefStepClaim := by
  intro rp p s rs rs' h_dec h_sim h_rstep
  let ⟨rfs, retTy, h_ne, hrs, hcm, hret, h_fs⟩ := h_sim
  let ⟨c, hc, h_eval⟩ := h_rstep
  cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
  | false =>
    unfold evalRefStep at h_eval
    rw [h_lt] at h_eval
    cases h_eval
  | true =>
    rw [evalRefStep_eq h_dec h_ne hrs hcm h_fs h_lt c] at h_eval
    cases h_es : evalStep p c s with
    | done out =>
      rw [h_es] at h_eval
      cases h_eval
    | fault k =>
      rw [h_es] at h_eval
      cases k <;> cases h_eval
    | step s₁ =>
      let ⟨h_ne₁, h_cm₁, h_fs₁⟩ := evalStep_step_inv h_ne h_fs h_es
      rw [h_es] at h_eval
      dsimp only [mapStepRes, stepResultToRefOutcome] at h_eval
      injection h_eval with h_rs'
      subst h_rs'
      exact ⟨s₁, ⟨c, hc, h_es⟩, liftFrames p s₁.frames, retTy, h_ne₁, rfl,
        rfl, hret, h_fs₁⟩

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
  let ⟨rfs, retTy, h_ne, hrs, hcm, hret, h_fs⟩ := h_sim
  let ⟨c, hc, h_es⟩ := h_step
  have h_ref_eq := evalRefStep_eq h_dec h_ne hrs hcm h_fs h_lt c
  let ⟨h_ne', h_cm', h_fs'⟩ := evalStep_step_inv h_ne h_fs h_es
  rw [h_es] at h_ref_eq
  dsimp only [mapStepRes, stepResultToRefOutcome] at h_ref_eq
  let rs' : RefState := {
    frames := callerSentinelFrame retTy :: (liftFrames p s'.frames).reverse
    callerMem := s'.callerMem
    stepsExecuted := rs.stepsExecuted + 1
    maxSteps := rs.maxSteps
  }
  have h_rstep : RefStep rp rs (.running rs') := ⟨c, hc, h_ref_eq⟩
  refine ⟨rs', h_rstep, ?_, rfl, rfl⟩
  exact ⟨liftFrames p s'.frames, retTy, h_ne', rfl, rfl, hret, h_fs'⟩

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
    let ⟨rfs, retTy, h_ne, hrs, hcm, _, h_fs⟩ := h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq h_dec h_ne hrs hcm h_fs h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        rw [h_es] at h_reval
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
    let ⟨rfs, retTy, h_ne, hrs, hcm, _, h_fs⟩ := h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq h_dec h_ne hrs hcm h_fs h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        rw [h_es] at h_reval
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
    let ⟨rfs, retTy, h_ne, hrs, hcm, _, h_fs⟩ := h_sim_end
    have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
      exact Nat.lt_succ_self n
    have h_reval := evalRefStep_eq h_dec h_ne hrs hcm h_fs h_lt c
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
    let ⟨rfs, retTy, h_ne, hrs, hcm, _, h_fs⟩ := h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq h_dec h_ne hrs hcm h_fs h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        rw [h_es] at h_reval
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
  match entryRetTy? p with
  | some retTy =>
    { frames := callerSentinelFrame retTy :: (liftFrames p s.frames).reverse
      callerMem := s.callerMem
      stepsExecuted := 0
      maxSteps := 0 }
  | none =>
    { frames := []
      callerMem := s.callerMem
      stepsExecuted := 0
      maxSteps := 0 }

/-- Total frame-projection function from $M_{\text{ref}}$ to
$M_{\text{anneal}}$. -/
noncomputable def projectFrame (rf : RefFrameState) : FrameState :=
  { defId := rf.defId
    blockIdx := rf.blockIdx
    stmtIdx := rf.stmtIdx
    locals := unzipRefSlots rf.locals
    returnCont := rf.returnCont }

/-- Total state-projection function from $M_{\text{ref}}$ to
$M_{\text{anneal}}$. -/
noncomputable def projectState (rs : RefState) : State :=
  match rs.frames with
  | _ :: activeBottomToTop =>
    { frames := activeBottomToTop.reverse.map projectFrame
      callerMem := rs.callerMem }
  | [] =>
    { frames := [], callerMem := rs.callerMem }

theorem simulationInv_with_counters {p : Program} {s : State} {rs : RefState}
    (steps max : Nat) (h : SimulationInv p s rs) :
    SimulationInv p s { rs with stepsExecuted := steps, maxSteps := max } := by
  let ⟨rfs, retTy, h_ne, hrs, hcm, hret, h_fs⟩ := h
  exact ⟨rfs, retTy, h_ne, hrs, hcm, hret, h_fs⟩

theorem simulationInv_of_with_counters {p : Program} {s : State} {rs : RefState}
    {steps max : Nat}
    (h : SimulationInv p s
      { rs with stepsExecuted := steps, maxSteps := max }) :
    SimulationInv p s rs := by
  let ⟨rfs, retTy, h_ne, hrs, hcm, hret, h_fs⟩ := h
  exact ⟨rfs, retTy, h_ne, hrs, hcm, hret, h_fs⟩

theorem liftState_sim_of_sim {p : Program} {s : State} {rs : RefState}
    (h : SimulationInv p s rs) :
    SimulationInv p s (liftState p s) := by
  let ⟨rfs, retTy, h_ne, _, _, hret, h_fs⟩ := h
  unfold liftState
  rw [hret]
  exact ⟨liftFrames p s.frames, retTy, h_ne, rfl, rfl, hret,
    framesSimInv_liftFrames h_fs⟩

theorem liftState_steps (p : Program) (s : State) :
    (liftState p s).stepsExecuted = 0 ∧ (liftState p s).maxSteps = 0 := by
  unfold liftState
  cases entryRetTy? p <;> exact ⟨rfl, rfl⟩

theorem liftState_eq_of_sim {p : Program} {s : State} {rs : RefState}
    (h : SimulationInv p s rs) :
    { liftState p s with
      stepsExecuted := rs.stepsExecuted
      maxSteps := rs.maxSteps } = rs :=
  refState_unique_of_simulationInv
    (simulationInv_with_counters rs.stepsExecuted rs.maxSteps
      (liftState_sim_of_sim h))
    h rfl rfl

private theorem map_projectFrame_of_framesSimInv {p : Program}
    {fs : List FrameState} {rfs : List RefFrameState}
    (h : FramesSimInv p fs rfs) :
    rfs.map projectFrame = fs := by
  induction fs generalizing rfs with
  | nil =>
    cases rfs with
    | nil => rfl
    | cons _ _ => cases h
  | cons f rest ih =>
    cases rfs with
    | nil => cases h
    | cons rf rrest =>
      let ⟨⟨body, _, h_len, hrf⟩, h_rest⟩ := h
      dsimp only [List.map]
      rw [hrf, ih h_rest]
      dsimp only [projectFrame, liftFrame]
      rw [unzipRefSlots_zipRefLocals h_len]

theorem projectState_sim_of_sim {p : Program} {s : State} {rs : RefState}
    (h : SimulationInv p s rs) :
    projectState rs = s := by
  let ⟨rfs, retTy, _, hrs, hcm, _, h_fs⟩ := h
  unfold projectState
  rw [hrs]
  dsimp only
  rw [List.reverse_reverse, map_projectFrame_of_framesSimInv h_fs, hcm]

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
      let ⟨rfs, retTy, h_ne, hrs, hcm, _, h_fs⟩ := h_sim_end
      have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
        apply nat_blt_eq_true_of_lt
        rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
        exact Nat.lt_succ_self n
      have h_reval := evalRefStep_eq h_dec h_ne hrs hcm h_fs h_lt c
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
      let ⟨rfs, retTy, h_ne, hrs, hcm, _, h_fs⟩ := h_sim
      cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
      | false =>
        unfold evalRefStep at h_reval
        rw [h_lt] at h_reval
        cases k <;> cases h_reval
      | true =>
        rw [evalRefStep_eq h_dec h_ne hrs hcm h_fs h_lt c] at h_reval
        cases h_es : evalStep p c s with
        | step s' =>
          rw [h_es] at h_reval
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

/-! ## Move Deinitialization, Overflow, Enum, Tuple, Cast, Unwind, Call, and
Core-Builtin Canaries (`D6`–`D24`) -/

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

/-- `D20` (direct crate-local call, left-to-right move deinitialization across
call arguments, callee return, and caller destination writeback in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D20_direct_call_and_return :
    CanaryD20DirectCallAndReturnClaim := by
  let q32 : Query := { args := [u32Val 32] }
  let ⟨a₁, a₂, a₃, a₄⟩ := positive_ref_of_exec
    (p := progDirectCallD20) (q := q32) (fuel := 5)
    (out := .returned ⟨u32Val 42, ⟨[]⟩⟩) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := negative_ref_of_execFault
    (p := progCallUseAfterMoveArgD20) (q := q32) (fuel := 1)
    (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄⟩

/-- `D21` (multi-frame panic unwind propagation through caller cleanup, direct
caller propagation, and UB at a non-unwinding call boundary in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D21_multi_frame_unwind : CanaryD21MultiFrameUnwindClaim := by
  let ⟨a₁, a₂, a₃, a₄⟩ := positive_ref_of_exec
    (p := mkMultiFrameUnwindProgD21 (.cleanup 2)) (q := queryUsizeMax)
    (fuel := 7) (out := .unwound ⟨[]⟩) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := positive_ref_of_exec
    (p := mkMultiFrameUnwindProgD21 .continue_) (q := queryUsizeMax)
    (fuel := 5) (out := .unwound ⟨[]⟩) rfl
  let ⟨c₁, c₂, c₃, c₄⟩ := negative_ref_of_execFault
    (p := mkMultiFrameUnwindProgD21 .unreachable) (q := queryUsizeMax)
    (fuel := 5) (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, c₁, c₂, c₃, c₄⟩

/-- `D22` (`TerminatorKind.callBuiltin` across `saturatingSub`,
`saturatingAdd`, `leadingZeros`, `trailingZeros`, `wrappingAdd`, `wrappingShl`,
`overflowingAdd`, `isMultipleOf`, `cmpMin`, and `cmpMax`, plus fail-closed
signed `isMultipleOf`, in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D22_core_builtins : CanaryD22CoreBuiltinsClaim := by
  let u32PairTy : MirTy := .tuple [u32Ty, .bool]
  let i32Ty : MirTy := .int .i32 true
  let pSatSub := mkBinaryBuiltinProgD22 .saturatingSub u32Ty u32Ty u32Ty
  let pSatAdd := mkBinaryBuiltinProgD22 .saturatingAdd i8Ty i8Ty i8Ty
  let pClz := mkUnaryBuiltinProgD22 .leadingZeros u32Ty u32Ty
  let pCtz := mkUnaryBuiltinProgD22 .trailingZeros u32Ty u32Ty
  let pWrapAdd := mkBinaryBuiltinProgD22 .wrappingAdd u32Ty u32Ty u32Ty
  let pWrapShl := mkBinaryBuiltinProgD22 .wrappingShl u32Ty u32Ty u32Ty
  let pOvfAdd := mkBinaryBuiltinProgD22 .overflowingAdd u32PairTy u32Ty u32Ty
  let pMult := mkBinaryBuiltinProgD22 .isMultipleOf .bool u32Ty u32Ty
  let pMultBad := mkBinaryBuiltinProgD22 .isMultipleOf .bool i32Ty i32Ty
  let pMin := mkBinaryBuiltinProgD22 .cmpMin i8Ty i8Ty i8Ty
  let pMax := mkBinaryBuiltinProgD22 .cmpMax i8Ty i8Ty i8Ty
  let ⟨_, a₁, _, a₂⟩ := positive_ref_of_exec
    (p := pSatSub) (q := { args := [u32Val 3, u32Val 10] }) (fuel := 2)
    (out := .returned ⟨u32Val 0, ⟨[]⟩⟩) rfl
  let ⟨_, b₁, _, b₂⟩ := positive_ref_of_exec
    (p := pSatAdd) (q := { args := [i8Val 100, i8Val 50] }) (fuel := 2)
    (out := .returned ⟨i8Val 127, ⟨[]⟩⟩) rfl
  let ⟨_, c₁, _, c₂⟩ := positive_ref_of_exec
    (p := pClz) (q := { args := [u32Val 0] }) (fuel := 2)
    (out := .returned ⟨u32Val 32, ⟨[]⟩⟩) rfl
  let ⟨_, d₁, _, d₂⟩ := positive_ref_of_exec
    (p := pClz) (q := { args := [u32Val 12] }) (fuel := 2)
    (out := .returned ⟨u32Val 28, ⟨[]⟩⟩) rfl
  let ⟨_, e₁, _, e₂⟩ := positive_ref_of_exec
    (p := pCtz) (q := { args := [u32Val 0] }) (fuel := 2)
    (out := .returned ⟨u32Val 32, ⟨[]⟩⟩) rfl
  let ⟨_, f₁, _, f₂⟩ := positive_ref_of_exec
    (p := pCtz) (q := { args := [u32Val 12] }) (fuel := 2)
    (out := .returned ⟨u32Val 2, ⟨[]⟩⟩) rfl
  let ⟨_, g₁, _, g₂⟩ := positive_ref_of_exec
    (p := pWrapAdd) (q := queryU32MaxPlusOne) (fuel := 2)
    (out := .returned ⟨u32Val 0, ⟨[]⟩⟩) rfl
  let ⟨_, h₁, _, h₂⟩ := positive_ref_of_exec
    (p := pWrapShl) (q := { args := [u32Val 1, u32Val 33] }) (fuel := 2)
    (out := .returned ⟨u32Val 2, ⟨[]⟩⟩) rfl
  let ⟨_, i₁, _, i₂⟩ := positive_ref_of_exec
    (p := pOvfAdd) (q := queryU32MaxPlusOne) (fuel := 2)
    (out := .returned ⟨.tuple [u32Val 0, .bool true], ⟨[]⟩⟩) rfl
  let ⟨_, j₁, _, j₂⟩ := positive_ref_of_exec
    (p := pMult) (q := { args := [u32Val 12, u32Val 4] }) (fuel := 2)
    (out := .returned ⟨.bool true, ⟨[]⟩⟩) rfl
  let ⟨_, k₁, _, k₂⟩ := positive_ref_of_exec
    (p := pMult) (q := { args := [u32Val 0, u32Val 0] }) (fuel := 2)
    (out := .returned ⟨.bool true, ⟨[]⟩⟩) rfl
  let ⟨_, l₁, _, l₂⟩ := positive_ref_of_exec
    (p := pMult) (q := { args := [u32Val 5, u32Val 0] }) (fuel := 2)
    (out := .returned ⟨.bool false, ⟨[]⟩⟩) rfl
  let ⟨_, m₁, _, m₂⟩ := positive_ref_of_exec
    (p := pMin) (q := { args := [i8Val 251, i8Val 3] }) (fuel := 2)
    (out := .returned ⟨i8Val 251, ⟨[]⟩⟩) rfl
  let ⟨_, n₁, _, n₂⟩ := positive_ref_of_exec
    (p := pMax) (q := { args := [i8Val 251, i8Val 3] }) (fuel := 2)
    (out := .returned ⟨i8Val 3, ⟨[]⟩⟩) rfl
  let ⟨o₁, _, o₂, o₃⟩ := negative_ref_of_execFault
    (p := pMultBad)
    (q := { args := [scalarNatVal .i32 true 4, scalarNatVal .i32 true 2] })
    (fuel := 1) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, b₁, b₂, c₁, c₂, d₁, d₂, e₁, e₂, f₁, f₂, g₁, g₂, h₁, h₂,
    i₁, i₂, j₁, j₂, k₁, k₂, l₁, l₂, m₁, m₂, n₁, n₂, o₁, o₂, o₃⟩

/-- `D23` (normal return to a `target := none` diverging call continuation for
both direct `.call` and `.callBuiltin` faults with `.fault .undefined` / `.ub`
in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D23_diverging_call_return_ub :
    CanaryD23DivergingCallReturnUbClaim := by
  let ⟨a₁, a₂, a₃, a₄⟩ := negative_ref_of_execFault
    (p := progDivergingCallReturnD23) (q := queryEmpty) (fuel := 3)
    (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := negative_ref_of_execFault
    (p := progDivergingBuiltinD23) (q := queryEmpty) (fuel := 1)
    (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄⟩

/-- `D24` (call-entry destination deinitialization observed as `.undefined` /
`.ub` on unwind cleanup read, fail-closed `.unsupported`/`.blocked` on `.move`
arguments overlapping `dst` for both direct `.call` and `.callBuiltin`, and
positive contrast admitting `.copy` arguments overlapping `dst` in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D24_call_deinit_and_overlap :
    CanaryD24CallDeinitAndOverlapClaim := by
  let q9 : Query := { args := [u32Val 9] }
  let ⟨a₁, a₂, a₃, a₄⟩ := negative_ref_of_execFault
    (p := progCallDeinitUnwindReadD24) (q := queryEmpty) (fuel := 5)
    (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := negative_ref_of_execFault
    (p := progCallMoveOverlapDstD24) (q := q9) (fuel := 1)
    (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨c₁, c₂, c₃, c₄⟩ := negative_ref_of_execFault
    (p := progBuiltinMoveOverlapDstD24) (q := q9) (fuel := 1)
    (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨d₁, d₂, d₃, d₄⟩ := positive_ref_of_exec
    (p := progCallAndBuiltinCopyOverlapDstD24) (q := q9) (fuel := 6)
    (out := .returned ⟨u32Val 10, ⟨[]⟩⟩) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, c₁, c₂, c₃, c₄, d₁, d₂, d₃, d₄⟩

/-- `D25` (non-ZST `U64Range` and ZST `Marker` struct aggregates, sibling field
moves and writes, moved-out field read UB, and fail-closed destination-overlap
struct aggregates in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D25_struct_and_field : CanaryD25StructAndFieldClaim := by
  let r1 : Val := .structVal u64RangeSty [u64Val 10, u64Val 20]
  let r2 : Val := .structVal u64RangeSty [u64Val 5, u64Val 30]
  let rOut : Val := .structVal u64RangeSty [u64Val 16, u64Val 50]
  let ⟨a₁, a₂, a₃, a₄⟩ := positive_ref_of_exec
    (p := progStructAddAndRewriteD25) (q := { args := [r1, r2] }) (fuel := 9)
    (out := .returned ⟨rOut, ⟨[]⟩⟩) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := negative_ref_of_execFault
    (p := progStructFieldUseAfterMoveD25) (q := { args := [r1] }) (fuel := 2)
    (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨c₁, c₂, c₃, c₄⟩ := negative_ref_of_execFault
    (p := progStructOverlapAliasD25) (q := { args := [r1] }) (fuel := 1)
    (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, c₁, c₂, c₃, c₄⟩

/-- `D26` (`Option<u64>` payload enum construction via `Downcast` + `Field` +
`SetDiscriminant` and `.adtEnum` aggregate, niche-encoded `Option<bool>`
construction and `Rvalue.discriminant` decoding, `CoreBuiltin.checkedAdd`, and
Miri Divergence Watch-Outs #2 and #3 in both $M_{\text{anneal}}$ and
$M_{\text{ref}}$). -/
theorem canary_D26_payload_niche_enum_and_checked_arith :
    CanaryD26PayloadNicheEnumAndCheckedArithClaim := by
  let pCheckedAdd := mkBinaryBuiltinProgD22 .checkedAdd optionU64Ty u64Ty u64Ty
  let some42 : Val := .enumVal optionU64EnumTy 1 [u64Val 42]
  let noneU64 : Val := .enumVal optionU64EnumTy 0 []
  let isize10Pair : Val :=
    .tuple [scalarNatVal .isize true 1, scalarNatVal .isize true 0]
  let qOvfU64 : Query := { args := [u64Val (Nat.pow 2 64 - 1), u64Val 1] }
  let ⟨a₁, a₂, a₃, a₄⟩ := positive_ref_of_exec
    (p := progOptionU64SetDiscrDowncastD26) (q := { args := [u64Val 41] })
    (fuel := 5) (out := .returned ⟨some42, ⟨[]⟩⟩) rfl
  let ⟨b₁, b₂, b₃, b₄⟩ := positive_ref_of_exec
    (p := progOptionBoolNicheDiscrD26) (q := { args := [.bool true] })
    (fuel := 7) (out := .returned ⟨isize10Pair, ⟨[]⟩⟩) rfl
  let ⟨c₁, c₂, c₃, c₄⟩ := positive_ref_of_exec
    (p := pCheckedAdd) (q := { args := [u64Val 40, u64Val 2] }) (fuel := 2)
    (out := .returned ⟨some42, ⟨[]⟩⟩) rfl
  let ⟨d₁, d₂, d₃, d₄⟩ := positive_ref_of_exec
    (p := pCheckedAdd) (q := qOvfU64) (fuel := 2)
    (out := .returned ⟨noneU64, ⟨[]⟩⟩) rfl
  let ⟨e₁, e₂, _, e₃⟩ := negative_ref_of_execFault
    (p := progUninitDowncastReadBeforeSetDiscrUbD26) (q := queryEmpty)
    (fuel := 2) (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨f₁, f₂, _, f₃⟩ := negative_ref_of_execFault
    (p := progNicheSetDiscrUntaggedOnUninitUbD26) (q := queryEmpty)
    (fuel := 1) (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨g₁, g₂, g₃, g₄⟩ := positive_ref_of_exec
    (p := progUnitSetDiscrNoopD26) (q := queryEmpty)
    (fuel := 2) (out := .returned ⟨.unit, ⟨[]⟩⟩) rfl
  let ⟨g'₁, g'₂, _, g'₃⟩ := negative_ref_of_execFault
    (p := progUnitSetDiscrBadVariantUbD26) (q := queryEmpty)
    (fuel := 1) (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨h₁, h₂, _, h₃⟩ := negative_ref_of_execFault
    (p := progUninhabitedVariantSetDiscrUbD26) (q := queryEmpty)
    (fuel := 1) (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, c₁, c₂, c₃, c₄, d₁, d₂, d₃, d₄,
    e₁, e₂, e₃, f₁, f₂, f₃, g₁, g₂, g₃, g₄, g'₁, g'₂, g'₃, h₁, h₂, h₃⟩

/-- `D27` (`[u8; 4]` fixed-array aggregate, forward and `fromEnd`
`ConstantIndex`, passing `Assert(.boundsCheck)`, dynamic `Index` read/write
preserving `idxLocal`, dynamic OOB `Index` UB, Miri Divergence Watch-Out #1
`DIV-LM-CONSTANT-INDEX-NAT-SUB-SATURATION`, and `toLeBytes` / `fromLeBytes`
round-tripping in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D27_array_indexing_and_le_bytes :
    CanaryD27ArrayIndexingAndLeBytesClaim := by
  let arr4In : Val := .array u8Ty [u8Val 10, u8Val 20, u8Val 30, u8Val 40]
  let arr4Out : Val := .array u8Ty [u8Val 10, u8Val 20, u8Val 80, u8Val 40]
  let arr3In : Val := .array u8Ty [u8Val 7, u8Val 8, u8Val 9]
  let leArr : Val := .array u8Ty [u8Val 4, u8Val 3, u8Val 2, u8Val 1]
  let u32Word : Val := u32Val 0x01020304
  let pToLe := mkUnaryBuiltinProgD22 .toLeBytes u8Array4Ty u32Ty
  let pFromLe := mkUnaryBuiltinProgD22 .fromLeBytes u32Ty u8Array4Ty
  let ⟨a₁, a₂, a₃, a₄⟩ := positive_ref_of_exec
    (p := progArrayAggregateAndIndexD27) (q := { args := [usizeVal 2] })
    (fuel := 11) (out := .returned ⟨arr4Out, ⟨[]⟩⟩) rfl
  let ⟨b₁, b₂, _, b₃⟩ := negative_ref_of_execFault
    (p := progArrayDynamicIndexOobUbD27)
    (q := { args := [arr4In, usizeVal 4] }) (fuel := 1)
    (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨c₁, c₂, _, c₃⟩ := negative_ref_of_execFault
    (p := progConstIndexFromEndGtMinLenBlockedD27) (q := { args := [arr3In] })
    (fuel := 1) (expected := .unsupported) (other := .undefined)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨d₁, d₂, _, d₃⟩ := negative_ref_of_execFault
    (p := progConstIndexFromEndLtMinLenUbD27) (q := { args := [arr3In] })
    (fuel := 1) (expected := .undefined) (other := .unsupported)
    (fun h => FaultKind.noConfusion h) rfl
  let ⟨e₁, e₂, e₃, e₄⟩ := positive_ref_of_exec
    (p := pToLe) (q := { args := [u32Word] }) (fuel := 2)
    (out := .returned ⟨leArr, ⟨[]⟩⟩) rfl
  let ⟨f₁, f₂, f₃, f₄⟩ := positive_ref_of_exec
    (p := pFromLe) (q := { args := [leArr] }) (fuel := 2)
    (out := .returned ⟨u32Word, ⟨[]⟩⟩) rfl
  exact ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, c₁, c₂, c₃, d₁, d₂, d₃,
    e₁, e₂, e₃, e₄, f₁, f₂, f₃, f₄⟩

end Anneal.MirCorrespondenceProof
