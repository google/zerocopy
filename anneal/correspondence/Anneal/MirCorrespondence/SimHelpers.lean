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

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-! ## One-to-One Simulation Invariant (`SimulationInv`) -/

/-- Project the runtime `LocalSlot` list from a `RefLocalState` list. -/
noncomputable def unzipRefSlots
    (rlocals : List RefLocalState) : List LocalSlot :=
  rlocals.map (·.slot)

theorem unzipRefSlots_zipRefLocals {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    (h_len : slots.length = bodyLocals.length) :
    unzipRefSlots (zipRefLocals bodyLocals slots) = slots := by
  induction bodyLocals generalizing slots with
  | nil =>
    cases slots with
    | nil => rfl
    | cons _ _ => cases h_len
  | cons ty tys ih =>
    cases slots with
    | nil => cases h_len
    | cons s ss =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      exact congrArg (s :: ·) (ih h_len)

/-- One-to-one uniqueness of `SimulationInv` (left-injective): any `RefState`
`rs` corresponds to at most one $M_{\text{anneal}}$ `State`. -/
theorem state_unique_of_simulationInv_base :
    StateUniqueOfSimulationInvClaim := by
  intro p s₁ s₂ rs h₁ h₂
  let ⟨f₁, rf₁, _, hs₁, hrs₁, hcm₁, _, _, body₁, _, hlen₁, hrf₁⟩ := h₁
  let ⟨f₂, rf₂, _, hs₂, hrs₂, hcm₂, _, _, body₂, _, hlen₂, hrf₂⟩ := h₂
  rw [hrs₁] at hrs₂
  injection hrs₂ with _ h_tail
  injection h_tail with h_rf_eq
  subst h_rf_eq
  have h_def : f₁.defId = f₂.defId := by
    have := congrArg RefFrameState.defId (hrf₁.symm.trans hrf₂)
    exact this
  have h_blk : f₁.blockIdx = f₂.blockIdx := by
    have := congrArg RefFrameState.blockIdx (hrf₁.symm.trans hrf₂)
    exact this
  have h_stmt : f₁.stmtIdx = f₂.stmtIdx := by
    have := congrArg RefFrameState.stmtIdx (hrf₁.symm.trans hrf₂)
    exact this
  have h_loc_eq : zipRefLocals body₁.locals f₁.locals =
      zipRefLocals body₂.locals f₂.locals := by
    have := congrArg RefFrameState.locals (hrf₁.symm.trans hrf₂)
    exact this
  have h_slots : f₁.locals = f₂.locals := by
    have h_u := congrArg unzipRefSlots h_loc_eq
    rw [unzipRefSlots_zipRefLocals hlen₁,
      unzipRefSlots_zipRefLocals hlen₂] at h_u
    exact h_u
  have h_f : f₁ = f₂ := by
    cases f₁; cases f₂
    simp only [ FrameState.mk.injEq]
    exact ⟨h_def, h_blk, h_stmt, h_slots⟩
  subst h_f
  cases s₁; cases s₂
  simp only [State.mk.injEq]
  exact ⟨hs₁.trans hs₂.symm, hcm₁.symm.trans hcm₂⟩

/-- One-to-one uniqueness of `SimulationInv` (right-injective at fixed step
counters): any $M_{\text{anneal}}$ `State` `s` and step counters
`(stepsExecuted, maxSteps)` uniquely determine `rs`, including its caller
sentinel frame. -/
theorem refState_unique_of_simulationInv_base :
    RefStateUniqueOfSimulationInvClaim := by
  intro p s rs₁ rs₂ h₁ h₂ h_steps h_max
  let ⟨f₁, rf₁, retTy₁, hs₁, hrs₁, hcm₁, hret₁, _, body₁, hbody₁, _, hrf₁⟩ := h₁
  let ⟨f₂, rf₂, retTy₂, hs₂, hrs₂, hcm₂, hret₂, _, body₂, hbody₂, _, hrf₂⟩ := h₂
  rw [hs₁] at hs₂
  injection hs₂ with h_f_eq
  subst h_f_eq
  rw [hbody₁] at hbody₂
  injection hbody₂ with h_b_eq
  subst h_b_eq
  rw [hret₁] at hret₂
  injection hret₂ with h_ret_eq
  subst h_ret_eq
  subst hrf₁; subst hrf₂
  cases rs₁; cases rs₂
  simp only [RefState.mk.injEq]
  exact ⟨hrs₁.trans hrs₂.symm, hcm₁.trans hcm₂.symm, h_steps, h_max⟩

theorem getElem?_zipRefLocals_some {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot : LocalSlot}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_slot : MirSemantics.getElem? slots i = some slot) :
    MirSemantics.getElem? (zipRefLocals bodyLocals slots) i =
      some ⟨slot, some ty⟩ := by
  induction bodyLocals generalizing slots i with
  | nil => cases h_ty
  | cons t ts ih =>
    cases slots with
    | nil => cases h_slot
    | cons s ss =>
      cases i with
      | zero =>
        injection h_ty with h_t
        injection h_slot with h_s
        subst h_t; subst h_s
        rfl
      | succ j =>
        exact ih h_ty h_slot

theorem getElem?_zipRefLocals_none_left {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} (h_ty : MirSemantics.getElem? bodyLocals i = none) :
    MirSemantics.getElem? (zipRefLocals bodyLocals slots) i = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons t ts ih =>
    cases slots with
    | nil => rfl
    | cons s ss =>
      cases i with
      | zero => cases h_ty
      | succ j => exact ih h_ty

theorem getElem?_zipRefLocals_none_right {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} (h_slot : MirSemantics.getElem? slots i = none) :
    MirSemantics.getElem? (zipRefLocals bodyLocals slots) i = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons t ts ih =>
    cases slots with
    | nil => rfl
    | cons s ss =>
      cases i with
      | zero => cases h_slot
      | succ j => exact ih h_slot

theorem getElem?_some_of_length_eq {α β : Type} {xs : List α} {ys : List β}
    {i : Nat} {x : α}
    (h_len : xs.length = ys.length)
    (h_x : MirSemantics.getElem? xs i = some x) :
    ∃ y : β, MirSemantics.getElem? ys i = some y := by
  induction xs generalizing ys i with
  | nil => cases h_x
  | cons a as ih =>
    cases ys with
    | nil => cases h_len
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      cases i with
      | zero => exact ⟨b, rfl⟩
      | succ j => exact @ih bs j h_len h_x

theorem setElem?_length {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : MirSemantics.setElem? xs i v = some xs') :
    xs'.length = xs.length := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons x rest ih =>
    cases i with
    | zero =>
      injection h with h_eq
      subst h_eq
      rfl
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_rest : MirSemantics.setElem? rest j v with
      | none => rw [h_rest] at h; cases h
      | some rest' =>
        rw [h_rest] at h
        injection h with h_eq
        subst h_eq
        simp only [List.length_cons, ih h_rest]

theorem setElem?_zipRefLocals_some {bodyLocals : List MirTy}
    {slots slots' : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot' : LocalSlot}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_set : MirSemantics.setElem? slots i slot' = some slots') :
    MirSemantics.setElem? (zipRefLocals bodyLocals slots) i ⟨slot', some ty⟩ =
      some (zipRefLocals bodyLocals slots') := by
  induction bodyLocals generalizing slots slots' i with
  | nil => cases h_ty
  | cons t ts ih =>
    cases slots with
    | nil => cases h_set
    | cons s ss =>
      cases i with
      | zero =>
        injection h_ty with h_t
        injection h_set with h_s
        subst h_t; subst h_s
        rfl
      | succ j =>
        dsimp only [MirSemantics.setElem?] at h_set
        cases h_ss : MirSemantics.setElem? ss j slot' with
        | none => rw [h_ss] at h_set; cases h_set
        | some ss' =>
          rw [h_ss] at h_set
          injection h_set with h_s
          subst h_s
          dsimp only [zipRefLocals, MirSemantics.setElem?]
          rw [ih h_ty h_ss]

theorem setElem?_zipRefLocals_none {bodyLocals : List MirTy}
    {slots : List LocalSlot}
    {i : Nat} {rval : RefLocalState} {slot' : LocalSlot}
    (h_set : MirSemantics.setElem? slots i slot' = none) :
    MirSemantics.setElem? (zipRefLocals bodyLocals slots) i rval = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons t ts ih =>
    cases slots with
    | nil => rfl
    | cons s ss =>
      cases i with
      | zero => cases h_set
      | succ j =>
        dsimp only [MirSemantics.setElem?] at h_set
        cases h_ss : MirSemantics.setElem? ss j slot' with
        | some _ => rw [h_ss] at h_set; cases h_set
        | none =>
          dsimp only [zipRefLocals, MirSemantics.setElem?]
          rw [ih h_ss]

theorem evalOperandToSlot_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot}
    {op : Operand} {ty : MirTy} {optVal : Option Val}
    (h : evalOperandToSlot bodyLocals locals op = .ok (ty, optVal, locals')) :
    locals'.length = locals.length := by
  cases op with
  | copy p =>
    dsimp only [evalOperandToSlot] at h
    cases h_emp : p.projection.isEmpty <;> rw [h_emp] at h
    · cases h
    · cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [h_ty] at h; cases h
      | some ty₀ =>
        cases h_sl : MirSemantics.getElem? locals p.localId with
        | none => rw [h_ty, h_sl] at h; cases h
        | some slot =>
        rw [h_ty, h_sl] at h
        cases slot with
        | dead => cases h
        | live opt =>
          injection h with h_tup
          injection h_tup with _ h_rest
          injection h_rest with _ h_loc
          subst h_loc
          rfl
  | move p =>
    dsimp only [evalOperandToSlot] at h
    cases h_emp : p.projection.isEmpty <;> rw [h_emp] at h
    · cases h
    · cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [h_ty] at h; cases h
      | some ty₀ =>
        cases h_sl : MirSemantics.getElem? locals p.localId with
        | none => rw [h_ty, h_sl] at h; cases h
        | some slot =>
        rw [h_ty, h_sl] at h
        cases slot with
        | dead => cases h
        | live opt =>
          dsimp only at h
          cases h_set :
              MirSemantics.setElem? locals p.localId (liveUninitSlot ty₀) <;>
            rw [h_set] at h
          · cases h
          · injection h with h_tup
            injection h_tup with _ h_rest
            injection h_rest with _ h_loc
            subst h_loc
            exact setElem?_length h_set
  | constant c =>
    dsimp only [evalOperandToSlot] at h
    cases h_lit : evalConstLit c.ty c.lit <;> rw [h_lit] at h
    · cases h
    · injection h with h_tup
      injection h_tup with _ h_rest
      injection h_rest with _ h_loc
      subst h_loc
      rfl

theorem evalPrimitiveOperand_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot}
    {opnd : Operand} {v : Val}
    (h : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    locals'.length = locals.length := by
  unfold evalPrimitiveOperand at h
  cases h_op : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [h_op] at h; cases h
  | ok res =>
    let ⟨ty, optVal, l₁⟩ := res
    rw [h_op] at h
    dsimp only at h
    cases h_pr : isPrimitiveReadableTy ty <;> rw [h_pr] at h
    · cases h
    · cases optVal with
      | none => cases h
      | some v₀ =>
        injection h with h_tup
        injection h_tup with _ h_loc
        subst h_loc
        exact evalOperandToSlot_length h_op

theorem evalRvalue_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (h : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    locals'.length = locals.length := by
  cases rv with
  | use opnd =>
    dsimp only [evalRvalue] at h
    cases h_op : evalOperandToSlot bodyLocals locals opnd with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨srcTy, optVal, l₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases h_eq_ty : MirTy.beq srcTy dstTy <;> rw [h_eq_ty] at h
      · cases h
      · cases optVal with
        | none => cases h
        | some v₀ =>
          injection h with h_tup
          injection h_tup with _ h_loc
          subst h_loc
          exact evalOperandToSlot_length h_op
  | binaryOp op lhs rhs =>
    dsimp only [evalRvalue] at h
    cases h_l : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rw [h_l] at h; cases h
    | ok resL =>
      let ⟨lVal, l₁⟩ := resL
      rw [h_l] at h
      dsimp only at h
      cases h_r : evalPrimitiveOperand bodyLocals l₁ rhs with
      | error _ => rw [h_r] at h; cases h
      | ok resR =>
        let ⟨rVal, l₂⟩ := resR
        rw [h_r] at h
        dsimp only at h
        cases h_b : evalBinOp op lVal rVal <;> rw [h_b] at h
        · cases h
        · injection h with h_tup
          injection h_tup with _ h_loc
          subst h_loc
          exact (evalPrimitiveOperand_length h_r).trans
            (evalPrimitiveOperand_length h_l)
  | unaryOp op opnd =>
    dsimp only [evalRvalue] at h
    cases h_op : evalPrimitiveOperand bodyLocals locals opnd with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨v₀, l₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases h_u : evalUnOp op v₀ <;> rw [h_u] at h
      · cases h
      · injection h with h_tup
        injection h_tup with _ h_loc
        subst h_loc
        exact evalPrimitiveOperand_length h_op
  | discriminant place =>
    dsimp only [evalRvalue] at h
    cases h_emp : place.projection.isEmpty <;> rw [h_emp] at h
    · cases h
    · cases h_ty : MirSemantics.getElem? bodyLocals place.localId with
      | none => rw [h_ty] at h; cases h
      | some ty =>
        rw [h_ty] at h
        cases ty with
        | enum ety =>
          cases h_sl : MirSemantics.getElem? locals place.localId with
          | none => rw [h_sl] at h; cases h
          | some slot =>
            rw [h_sl] at h
            dsimp only at h
            cases h_adm : enumAdmitted ety <;> rw [h_adm] at h
            · cases h
            · cases h_tr : ety.tagRepr <;> rw [h_tr] at h
              · cases slot with
                | dead => cases h
                | live opt =>
                  cases opt with
                  | none =>
                    dsimp only at h
                    cases h_d : MirSemantics.getElem? ety.discriminants 0 <;>
                      rw [h_d] at h
                    · cases h
                    · injection h with h_tup
                      injection h_tup with _ h_loc
                      subst h_loc
                      rfl
                  | some val =>
                    cases val with
                    | enumVal ety' v =>
                      dsimp only at h
                      cases h_chk : (EnumTy.beq ety ety' && Nat.beq v 0) <;>
                        rw [h_chk] at h
                      · cases h
                      · cases h_d :
                            MirSemantics.getElem? ety.discriminants 0 <;>
                          rw [h_d] at h
                        · cases h
                        · injection h with h_tup
                          injection h_tup with _ h_loc
                          subst h_loc
                          rfl
                    | _ => cases h
              · cases slot with
                | dead => cases h
                | live opt =>
                  cases opt with
                  | none => cases h
                  | some val =>
                    cases val with
                    | enumVal ety' v =>
                      dsimp only at h
                      cases h_chk :
                        (EnumTy.beq ety ety' &&
                          Nat.blt v ety.discriminants.length) <;>
                        rw [h_chk] at h
                      · cases h
                      · cases h_d :
                            MirSemantics.getElem? ety.discriminants v <;>
                          rw [h_d] at h
                        · cases h
                        · injection h with h_tup
                          injection h_tup with _ h_loc
                          subst h_loc
                          rfl
                    | _ => cases h
        | _ => cases h
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported =>
    cases h

theorem writePlace_length {locals locals' : List LocalSlot}
    {dstLocalId : LocalId} {dstTy : MirTy} {val : Val}
    (h : writePlace locals dstLocalId dstTy val = .ok locals') :
    locals'.length = locals.length := by
  unfold writePlace at h
  cases h_chk : checkVal val dstTy <;> rw [h_chk] at h
  · cases h
  · cases h_get : MirSemantics.getElem? locals dstLocalId with
    | none => rw [h_get] at h; cases h
    | some slot =>
      rw [h_get] at h
      cases slot with
      | dead => cases h
      | live _ =>
        dsimp only at h
        cases h_set :
            MirSemantics.setElem? locals dstLocalId (.live (some val)) <;>
          rw [h_set] at h
        · cases h
        · injection h with h_eq
          subst h_eq
          exact setElem?_length h_set

theorem decodePlace_inv {ts : List MirTy} {rp : RefPlace} {p : Place}
    (h : decodePlace ts rp = some p) :
    rp.localId = p.localId ∧ rp.projection.isEmpty = p.projection.isEmpty := by
  dsimp only [decodePlace] at h
  cases h_proj : mapOption (decodeProjElem ts) rp.projection with
  | none => rw [h_proj] at h; cases h
  | some proj =>
    rw [h_proj] at h
    injection h with h_eq
    subst h_eq
    exact ⟨rfl, mapOption_isEmpty h_proj⟩

noncomputable def mapSlotRes (bodyLocals : List MirTy) :
    Except FaultKind (MirTy × Option Val × List LocalSlot) →
    Except FaultKind (MirTy × Option Val × List RefLocalState)
  | .error k => .error k
  | .ok (ty, optVal, slots') => .ok (ty, optVal, zipRefLocals bodyLocals slots')

noncomputable def mapSlotsRes (bodyLocals : List MirTy) :
    Except FaultKind (List LocalSlot) →
    Except FaultKind (List RefLocalState)
  | .error k => .error k
  | .ok slots' => .ok (zipRefLocals bodyLocals slots')

end Anneal.MirCorrespondence
