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
open Miri.ABI Miri.Memory Miri.Interpreter

/-! ## Section 4: `ValidityVisitor.validatePlace` on `.local` Places -/

theorem refLayoutDataForTy_isSized (ty : MirTy) :
    (refLayoutDataForTy ty).isSized = true := by
  cases ty with
  | unit | never | bool | int _ _ | char | ordering | ref _ _ | rawPtr _ _
  | slice _ | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl
  | tuple fs =>
    cases refLayoutDataForTy_tuple fs with
    | inl h => rw [h]; rfl
    | inr h =>
      let ⟨_, _, _, h_eq⟩ := h
      rw [h_eq]; rfl
  | enum ety =>
    dsimp only [refLayoutDataForTy, refAsEnumTy?, refEnumLayoutData]
    cases ety.tagRepr <;> rfl

theorem wrappingRange_full_contains_truncateBits (w : IntWidth)
    (x : BitVec 128) :
    (refFullWrappingRangeSize (toMiriSize w)).contains (truncateBits w x) =
      true := by
  have h_le : (truncateBits w x).toNat ≤ HPow.hPow 2 w.bitWidth - 1 := by
    have h_lt : (truncateBits w x).toNat < HPow.hPow 2 w.bitWidth := by
      rw [toNat_truncateBits]
      exact Nat.mod_lt x.toNat (intWidth_modulus_pos w)
    exact Nat.le_sub_one_of_lt h_lt
  have hr : refFullWrappingRangeSize (toMiriSize w) =
      ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (HPow.hPow 2 w.bitWidth - 1)⟩ := by
    cases w <;> decide
  have h_and : ∀ {a b : Bool}, a = true → b = true → (a && b) = true := by
    intro a b ha hb; rw [ha, hb]; rfl
  rw [hr]
  cases w <;> (
    dsimp only [Miri.ABI.WrappingRange.contains]
    rw [ite_eq_left (by decide)]
    exact h_and (decide_eq_true (Nat.zero_le _)) (decide_eq_true h_le))

theorem refEnum_isVariantUninhabited_false (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (v : Nat)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_lt : v < ety.discriminants.length) :
    (refEnumLayoutData ety).isVariantUninhabited v = false := by
  dsimp only [refEnumLayoutData]
  rw [h_tr]
  dsimp only [Miri.ABI.LayoutData.isVariantUninhabited]
  have h_get : (Array.mk (ety.discriminants.map
      (fun _ => refInhabitedVariantLayout)))[v]? =
      some refInhabitedVariantLayout := by
    rw [array_getElem?_eq_mirGetElem?, mirGetElem?_map]
    let ⟨d, hd⟩ := mirGetElem?_some_of_lt h_lt
    rw [hd]
    rfl
  rw [h_get]
  rfl

private theorem afterLocalRead_no_race
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (localId : LocalId)
    (h_curr : st.stack.currentFrame? = some frame)
    (h_dr : frame.extra.dataRace = none) :
    Miri.Interpreter.MachineHooks.afterLocalRead localId st = .ok () st := by
  dsimp only [Miri.Interpreter.MachineHooks.afterLocalRead,
    Miri.Interpreter.MachineHooks.currentFrame,
    get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_curr]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_dr]
  rfl

private theorem refBaseCompilerHooks_debugAssertions (types : List MirTy) :
    (refBaseCompilerHooks types).debugAssertions = false := rfl

private theorem refBaseCompilerHooks_validationInProgress (types : List MirTy) :
    (refBaseCompilerHooks types).validationInProgress = (fun st => .ok false st) := rfl

private theorem refBaseCompilerHooks_projection (types : List MirTy) :
    (refBaseCompilerHooks types).projection = (fun _ st => .ok (refProjectionCx types) st) := rfl

private theorem placeToOp_local_immediate (types : List MirTy)
    (c : Choice) (frameIdx : Nat) (localId : LocalId) (ty : MirTy)
    (imm : Immediate Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate imm), some (refLocalLayoutForTy types ty)⟩) :
    Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place c
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types ty⟩ st =
      .ok ⟨.immediate imm, refLocalLayoutForTy types ty⟩ st := by
  have h_op : frame.getLocalOperand localId = .ok (.immediate imm) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]
    rw [h_get]; rfl
  have h_sz : (refLocalLayoutForTy types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    Miri.Interpreter.PlaceMachine.localToOp,
    Miri.Interpreter.PlaceMachine.localToOpCore,
    Miri.Interpreter.PlaceMachine.layoutLocal,
    Miri.Interpreter.MachineHooks.currentFrame]
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    refBaseCompilerHooks_debugAssertions,
    refBaseCompilerHooks_validationInProgress,
    h_fidx, h_curr, h_get, h_op, h_sz,
    bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [afterLocalRead_no_race frame st localId h_curr h_dr]

private theorem validityMemory_readImmediate_imm_scalar
    (types : List MirTy) (ty : MirTy)
    (sc : Scalar Miri.Memory.Provenance) (expected : ExpectedValue)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_prim : (ty = .bool) ∨ (∃ w s, ty = .int w s)) :
    Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
        ⟨.immediate (.scalar sc), refLocalLayoutForTy types ty⟩ expected st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types ty⟩ st := by
  cases h_prim with
  | inl h_b =>
    subst h_b
    cases st with | mk stack machine => rfl
  | inr h_i =>
    let ⟨w, s, h_eq⟩ := h_i
    subst h_eq
    cases st with
    | mk stack machine =>
      cases w <;> cases s <;> rfl

private theorem validityMemory_readImmediate_imm_uninit
    (types : List MirTy) (ty : MirTy) (expected : ExpectedValue)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_prim : (ty = .bool) ∨ (∃ w s, ty = .int w s)) :
    ∃ msg,
      Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
          ⟨.immediate .uninit, refLocalLayoutForTy types ty⟩ expected st =
        .error (.undefinedBehavior msg) st := by
  cases h_prim with
  | inl h_b =>
    subst h_b
    cases st with | mk stack machine => exact ⟨_, rfl⟩
  | inr h_i =>
    let ⟨w, s, h_eq⟩ := h_i
    subst h_eq
    cases st with
    | mk stack machine =>
      cases w <;> cases s <;> exact ⟨_, rfl⟩

private theorem clearPlaceProvenance_imm_no_prov
    (types : List MirTy) (c : Choice) (place : RuntimePlace Miri.Memory.Provenance)
    (imm : Immediate Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
        c place st = .ok ⟨.immediate imm, place.layout⟩ st)
    (h_noprov : imm.hasProvenance = false) :
    Miri.Interpreter.ValidityMemory.clearPlaceProvenance refValidityMemoryEnv
        (refBasePlaceProjectionHooks types).place c
        (fun st => .ok false st) (fun _ _ st => .ok () st) place st =
      .ok () st := by
  dsimp only [Miri.Interpreter.ValidityMemory.clearPlaceProvenance,
    bind, Bind.bind, EStateM.bind]
  rw [h_toOp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_noprov]
  rfl

private theorem scalar_fromBool_toBool (b : Bool) :
    (Scalar.fromBool (Prov := Miri.Memory.Provenance) b).toBool = .ok b := by
  cases b <;> rfl

/-- Shorthand for the bound `ValidityVisitor.Hooks` used by `refCompilerHooks`
and `ExecutionMachine.withValidation`. Kept un-unfolded during `visit` proofs
via projection lemmas below. -/
noncomputable def refValHooks (types : List MirTy) :=
  Miri.Interpreter.TypedMachineBindings.bindValidity
    (refValidityHooks types) refRetagHooks 8

theorem refValHooks_typeName (types : List MirTy) (c : Choice)
    (tyId : TyId) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).typeName c tyId st = .ok "" st := rfl

theorem refValHooks_withGhostValidation (types : List MirTy)
    {A : Type} (act : Miri.Interpreter.ValidityVisitor.M
      (Miri.Interpreter.MachineHooks.State Unit RefUser) A) :
    (refValHooks types).withGhostValidation act = act := rfl

theorem refValHooks_debugAssertions (types : List MirTy) :
    (refValHooks types).debugAssertions = false := rfl

theorem refValHooks_projection (types : List MirTy) :
    (refValHooks types).projection = refBasePlaceProjectionHooks types := rfl

theorem refValHooks_discriminant (types : List MirTy) :
    (refValHooks types).discriminant = refValidityDiscriminantHooks types := rfl

theorem refValHooks_toOp (types : List MirTy) :
    (refValHooks types).toOp =
      Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place := rfl

theorem refValHooks_readImmediate (types : List MirTy) (c : Choice)
    (place : RuntimePlace Miri.Memory.Provenance) (exp : ExpectedValue) :
    (refValHooks types).readImmediate c place exp =
      Bind.bind
        (Miri.Interpreter.placeToOp
          (refBasePlaceProjectionHooks types).place c place)
        (fun op =>
          Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
            op exp) := rfl

theorem refValHooks_clearProvenance (types : List MirTy) (c : Choice)
    (place : RuntimePlace Miri.Memory.Provenance) :
    (refValHooks types).clearProvenance c place =
      Miri.Interpreter.ValidityMemory.clearPlaceProvenance refValidityMemoryEnv
        (refBasePlaceProjectionHooks types).place c
        (fun st => .ok false st) (fun _ _ st => .ok () st) place := rfl

theorem refValHooks_classify (types : List MirTy) (c : Choice)
    (tyId : TyId) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).classify c tyId st =
      match resolveTy types tyId with
      | some .bool => .ok .boolean st
      | some (.int _ _) => .ok .integer st
      | some .char => .ok .character st
      | some .unit => .ok (.aggregate false false false) st
      | some .never => .ok .never st
      | some (.tuple [.int _ _, .bool]) => .ok (.aggregate false false false) st
      | some ty =>
        match refAsEnumTy? ty with
        | some _ => .ok (.aggregate false false true) st
        | none => .error (.invalidProgram "unsupported validity type") st
      | none => .error (.invalidProgram "unsupported validity type") st := rfl

theorem refValHooks_opsemInhabited (types : List MirTy) (c : Choice)
    (tyId : TyId) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).opsemInhabited c tyId st =
      match resolveTy types tyId with
      | some .never => .ok false st
      | some _ => .ok true st
      | none => .error (.invalidProgram "unknown TyId in opsemInhabited") st := rfl

theorem refValHooks_fieldPath (types : List MirTy) (c : Choice)
    (l : LocalLayout) (i : Nat) (tyId : TyId)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).fieldPath c l i tyId st = .ok .enumTag st := rfl

theorem refValHooks_variantPath (types : List MirTy) (c : Choice)
    (l : LocalLayout) (v : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).variantPath c l v st = .ok (.variant "") st := rfl

theorem mem_ite_not_true_eq {α : Type} (a b : α) :
    (if (!true) = true then a else b) = b := rfl

theorem mem_eStateM_bind_pure {ε σ α β : Type} (a : α)
    (f : α → EStateM ε σ β) :
    EStateM.bind (EStateM.pure a) f = f a := rfl

theorem mem_eStateM_bind_ok {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {a : α} {st st' : σ}
    (h : m st = .ok a st') :
    EStateM.bind m f st = f a st' := by
  dsimp only [EStateM.bind]
  rw [h]

theorem mem_eStateM_bind_err {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {e : ε} {st st' : σ}
    (h : m st = .error e st') :
    EStateM.bind m f st = .error e st' := by
  dsimp only [EStateM.bind]
  rw [h]

theorem eStateM_bind_bind_ok {ε σ α β γ : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {g : β → EStateM ε σ γ} {a : α} {st st' : σ}
    (h : m st = .ok a st') :
    EStateM.bind (EStateM.bind m f) g st = EStateM.bind (f a) g st' := by
  dsimp only [EStateM.bind]; rw [h]

theorem eStateM_bind_bind_err {ε σ α β γ : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {g : β → EStateM ε σ γ} {e : ε} {st st' : σ}
    (h : m st = .error e st') :
    EStateM.bind (EStateM.bind m f) g st = .error e st' := by
  dsimp only [EStateM.bind]; rw [h]

theorem mem_refLocalLayoutForTy_ty (types : List MirTy) (ty : MirTy) :
    (refLocalLayoutForTy types ty).ty = tyIdFor types ty := rfl

/-- A local type that $M_{\text{ref}}$ lays out, validates, and reads the
discriminant of through the fieldless enum descriptor `ety` via `refAsEnumTy?`
(`.enum ety` or `core::cmp::Ordering` with `ety = refOrderingEnumTy`). -/
def EnumLike (types : List MirTy) (ty : MirTy) (ety : EnumTy) : Prop :=
  refAsEnumTy? ty = some ety ∧ resolveTy types (tyIdFor types ty) = some ty

theorem mem_refOrderingEnumTy_admitted :
    enumAdmitted refOrderingEnumTy = true := rfl

theorem enumLike_layoutData {ty : MirTy} {ety : EnumTy}
    (h_as : refAsEnumTy? ty = some ety) :
    refLayoutDataForTy ty = refEnumLayoutData ety := by
  cases ty <;> cases h_as <;> rfl

theorem enumLike_layout {types : List MirTy} {ty : MirTy} {ety : EnumTy}
    (h_el : EnumLike types ty ety) :
    refLocalLayoutForTy types ty =
      ⟨tyIdFor types ty, refEnumLayoutData ety⟩ := by
  dsimp only [refLocalLayoutForTy]
  rw [enumLike_layoutData h_el.1]

theorem enumLike_classify {types : List MirTy} {ty : MirTy}
    {ety : EnumTy}
    (h_el : EnumLike types ty ety) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).classify c (tyIdFor types ty) st =
      .ok (.aggregate false false true) st := by
  rw [refValHooks_classify, h_el.2]
  have h_as := h_el.1
  cases ty <;> cases h_as <;> rfl

theorem enumLike_opsemInhabited {types : List MirTy} {ty : MirTy}
    {ety : EnumTy} (h_el : EnumLike types ty ety) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refValHooks types).opsemInhabited c (tyIdFor types ty) st =
      .ok true st := by
  rw [refValHooks_opsemInhabited, h_el.2]
  have h_as := h_el.1
  cases ty <;> cases h_as <;> rfl

theorem enumLike_projectField0 {types : List MirTy} {ty : MirTy}
    {ety : EnumTy} {tagW : IntWidth} {tagS : Bool}
    (h_el : EnumLike types ty ety) (h_tr : ety.tagRepr = .scalar tagW tagS) :
    refProjectFieldLayout types (refLocalLayoutForTy types ty) 0 =
      .ok (refLocalLayoutForTy types (.int tagW tagS)) := by
  dsimp only [refProjectFieldLayout, refLocalLayoutForTy]
  rw [h_el.2]
  have h_as := h_el.1
  cases ty <;> cases h_as <;> dsimp only [refAsEnumTy?] <;> rw [h_tr] <;> rfl

theorem enumLike_projectVariant {types : List MirTy} {ty : MirTy}
    {ety : EnumTy} {variant : Nat}
    (h_el : EnumLike types ty ety) (h_lt : variant < ety.discriminants.length) :
    refProjectVariantLayout types (refLocalLayoutForTy types ty) variant =
      .ok ⟨tyIdFor types ty,
        { refUnitLayoutData with variants := .Single variant }⟩ := by
  have h_blt : Nat.blt variant ety.discriminants.length = true :=
    Nat.ble_eq_true_of_le h_lt
  dsimp only [refProjectVariantLayout, refLocalLayoutForTy]
  rw [h_el.2]
  dsimp only [Option.bind]
  rw [h_el.1]
  dsimp only
  rw [h_blt]
  rfl

private theorem enumLike_discriminantLayout {types : List MirTy} {ty : MirTy}
    {ety : EnumTy} (h_el : EnumLike types ty ety)
    (h_adm : enumAdmitted ety = true) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refDiscriminantLeaves types).discriminantLayout c (tyIdFor types ty) st =
      .ok ⟨tyIdFor types (.int ety.discrWidth ety.discrSigned),
        refScalarLayoutData ety.discrWidth ety.discrSigned⟩ st := by
  have h_ref_adm : refEnumAdmitted ety = true := by
    rw [refEnumAdmitted_eq]; exact h_adm
  dsimp only [refDiscriminantLeaves]
  rw [h_el.2]
  dsimp only [Option.bind]
  rw [h_el.1]
  dsimp only
  rw [h_ref_adm]
  rfl

private theorem enumLike_variantForDiscriminant {types : List MirTy}
    {ty : MirTy}
    {ety : EnumTy} (h_el : EnumLike types ty ety) (c : Choice)
    (bits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (refDiscriminantLeaves types).variantForDiscriminant c (tyIdFor types ty)
        bits st =
      .ok (refFindDiscrVariant? bits ety.discriminants) st := by
  dsimp only [refDiscriminantLeaves]
  rw [h_el.2]
  dsimp only [Option.bind]
  rw [h_el.1]

theorem readDiscriminant_validity_scalar_enum
    (types : List MirTy) (c : Choice) (ty : MirTy) (ety : EnumTy)
    (tagW : IntWidth)
    (tagS : Bool) (variant disc : Nat)
    (op : Miri.Interpreter.Operand Miri.Memory.Provenance)
    (tagOp : OpTy Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_el : EnumLike types ty ety)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_proj :
      Miri.Interpreter.OperandMachine.field (refValidityOperandHooks types) c
        ⟨op, refLocalLayoutForTy types ty⟩ 0 st = .ok tagOp st)
    (h_ri :
      Miri.Interpreter.PlaceMachine.readImmediate
        { refAccessConfig with ghostMode := true, deinitMovedPlace := false }
        tagOp st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (refValidityDiscriminantHooks types) c
        ⟨op, refLocalLayoutForTy types ty⟩ st =
      .ok variant st := by
  let ⟨h_bnds, h_pw, h_tag_all⟩ := enumAdmitted_parts h_adm
  have h_v_lt : variant < ety.discriminants.length :=
    mirGetElem?_lt_of_some h_get_d
  have h_tag_ok : tagBitsToDiscrBits tagW tagS ety.discrWidth
      (truncateBits tagW (BitVec.ofNat 128 disc)) = BitVec.ofNat 128 disc := by
    rw [h_tr] at h_tag_all
    have h_elem := list_all_mirGetElem?
      (p := fun d =>
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW (BitVec.ofNat 128 d)) == BitVec.ofNat 128 d)
      h_tag_all h_get_d
    exact eq_of_beq h_elem
  have h_find : refFindDiscrVariant? (BitVec.ofNat 128 disc) ety.discriminants =
      some variant := by
    rw [refFindDiscrVariant?_eq]
    exact findDiscrVariant?_of_enumAdmitted h_adm h_get_d
  have h_int_w : toMiriSize (intWidthOfMiriInteger (toMiriInteger tagW)) =
      toMiriSize tagW := by
    cases tagW <;> rfl
  have h_signed_eq :
      (refScalarLayoutData (intWidthOfMiriInteger (toMiriInteger tagW)) tagS).backendRepr.isSigned =
        .ok tagS := by
    cases tagW <;> cases tagS <;> rfl
  have h_signed_eq2 :
      (refScalarLayoutData tagW tagS).backendRepr.isSigned = .ok tagS := by
    cases tagW <;> cases tagS <;> rfl
  have h_vr :
      (Miri.ABI.Scalar.Union (value := .Int (toMiriInteger tagW) tagS)).validRange
          RuntimeTargetDataLayout.default =
        .ok (refFullWrappingRangeSize (toMiriSize tagW)) := by
    cases tagW <;> cases tagS <;> rfl
  have h_toBits :
      (miriScalar tagW (BitVec.ofNat 128 disc)).toBits (toMiriSize tagW) =
        .ok (truncateBits tagW (BitVec.ofNat 128 disc)) :=
    miriScalar_toUInt tagW (BitVec.ofNat 128 disc)
  have h_discr_trunc :
      (toMiriSize ety.discrWidth).truncate
        (if tagS then
          BitVec.ofInt 128 (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc)))
        else
          truncateBits tagW (BitVec.ofNat 128 disc)) =
      .ok (BitVec.ofNat 128 disc) := by
    rw [size_truncate_eq]
    have h_eq_td :
        truncateBits ety.discrWidth
          (if tagS then
            BitVec.ofInt 128 (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc)))
          else
            truncateBits tagW (BitVec.ofNat 128 disc)) =
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW (BitVec.ofNat 128 disc)) := by
      cases tagS with
      | false =>
        dsimp only [tagBitsToDiscrBits]
        rw [mem_ite_false_eq, mem_ite_false_eq, truncateBits_idem]
      | true =>
        dsimp only [tagBitsToDiscrBits]
        rw [mem_ite_true_eq, mem_ite_true_eq, bitVec_ofInt_eq]
    rw [h_eq_td, h_tag_ok]
  have h_dl := enumLike_discriminantLayout h_el h_adm c st
  have h_vars : (refLocalLayoutForTy types ty).layout.variants =
      .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct 0
        (ety.discriminants.map (fun _ => refInhabitedVariantLayout)).toArray := by
    rw [enumLike_layout h_el]
    dsimp only [refEnumLayoutData]
    rw [h_tr]
  have h_tl : (refDiscriminantLeaves types).tagLayout c
      (.Union (value := .Int (toMiriInteger tagW) tagS)) st =
      .ok (refLocalLayoutForTy types (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)) st := rfl
  dsimp only [Miri.Interpreter.Discriminant.readDiscriminant,
    refValidityDiscriminantHooks, bind, Bind.bind, EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, h_dl]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_tl]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_proj]
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_ri]
  have h_sz_ne :
      ((refLocalLayoutForTy types (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)).layout.size !=
        (refLocalLayoutForTy types (.int tagW tagS)).layout.size) = false := by
    cases tagW <;> cases tagS <;> rfl
  dsimp only [bind, Bind.bind, EStateM.bind]
  rw [h_sz_ne, mem_ite_false_eq]
  change (EStateM.bind (match (refScalarLayoutData (intWidthOfMiriInteger (toMiriInteger tagW)) tagS).backendRepr.isSigned with
    | .ok v => EStateM.pure v
    | .error _ => EStateM.throw (StepError.invalidProgram "discriminant requires scalar backend representation"))
    (fun _ => EStateM.bind (match (refScalarLayoutData tagW tagS).backendRepr.isSigned with
      | .ok v => EStateM.pure v
      | .error _ => EStateM.throw (StepError.invalidProgram "discriminant requires scalar backend representation"))
      _) st) = .ok variant st
  rw [h_signed_eq, h_signed_eq2]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [bne_self_eq_false, mem_ite_false_eq]
  have h_tb :
      (miriScalar tagW (BitVec.ofNat 128 disc)).toBits
        (refLocalLayoutForTy types
          (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)).layout.size =
      .ok (truncateBits tagW (BitVec.ofNat 128 disc)) := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refScalarLayoutData,
      refBaseLayoutData]
    rw [h_int_w]
    exact h_toBits
  have h_se :
      (refLocalLayoutForTy types
          (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)).layout.size.signExtend
        (truncateBits tagW (BitVec.ofNat 128 disc)) =
      .ok (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc))) := by
    dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refScalarLayoutData,
      refBaseLayoutData]
    rw [h_int_w]
    exact size_signExtend_eq tagW (truncateBits tagW (BitVec.ofNat 128 disc))
  have h_vfd :
      (refDiscriminantLeaves types).variantForDiscriminant c
        (tyIdFor types ty) (BitVec.ofNat 128 disc) st =
      .ok (some variant) st := by
    rw [enumLike_variantForDiscriminant h_el, h_find]
  have h_uninh :
      (refLocalLayoutForTy types ty).layout.isVariantUninhabited variant =
        false := by
    rw [enumLike_layout h_el]
    exact refEnum_isVariantUninhabited_false ety tagW tagS variant h_tr h_v_lt
  change (EStateM.bind
    (EStateM.pure (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar tagW (BitVec.ofNat 128 disc)))) _ st) = .ok variant st
  rw [mem_eStateM_bind_pure]
  change (EStateM.bind
    (EStateM.pure (ScalarIntCastResult.integer
      (miriScalar tagW (BitVec.ofNat 128 disc)))) _ st) = .ok variant st
  rw [mem_eStateM_bind_pure]
  dsimp only
  rw [h_tb]
  change (EStateM.bind
    (EStateM.pure (truncateBits tagW (BitVec.ofNat 128 disc))) _ st) = .ok variant st
  rw [mem_eStateM_bind_pure]
  change (EStateM.bind (match (Miri.ABI.Scalar.Union (value := .Int (toMiriInteger tagW) tagS)).validRange
      RuntimeTargetDataLayout.default with
    | .ok v => EStateM.pure v
    | .error _ => _) _ st) = .ok variant st
  rw [h_vr]
  dsimp only
  rw [mem_eStateM_bind_pure, wrappingRange_full_contains_truncateBits tagW (BitVec.ofNat 128 disc),
    mem_ite_not_true_eq]
  cases tagS with
  | false =>
    rw [mem_ite_false_eq, mem_eStateM_bind_pure]
    rw [mem_ite_false_eq] at h_discr_trunc
    have h_dt :
        (refScalarLayoutData ety.discrWidth ety.discrSigned).size.truncate
          (truncateBits tagW (BitVec.ofNat 128 disc)) =
        .ok (BitVec.ofNat 128 disc) := h_discr_trunc
    rw [h_dt]
    change (EStateM.bind (EStateM.pure (BitVec.ofNat 128 disc)) _ st) = .ok variant st
    rw [mem_eStateM_bind_pure, mem_eStateM_bind_ok h_vfd]
    dsimp only
    rw [mem_eStateM_bind_pure, h_uninh, mem_ite_false_eq]
    rfl
  | true =>
    rw [mem_ite_true_eq, h_se]
    change (EStateM.bind (EStateM.pure (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc)))) _ st) =
      .ok variant st
    rw [mem_eStateM_bind_pure, mem_eStateM_bind_pure]
    rw [mem_ite_true_eq] at h_discr_trunc
    have h_dt :
        (refScalarLayoutData ety.discrWidth ety.discrSigned).size.truncate
          (BitVec.ofInt 128 (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc)))) =
        .ok (BitVec.ofNat 128 disc) := h_discr_trunc
    rw [h_dt]
    change (EStateM.bind (EStateM.pure (BitVec.ofNat 128 disc)) _ st) = .ok variant st
    rw [mem_eStateM_bind_pure, mem_eStateM_bind_ok h_vfd]
    dsimp only
    rw [mem_eStateM_bind_pure, h_uninh, mem_ite_false_eq]
    rfl

theorem refEnumLayoutData_scalar (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) (h_tr : ety.tagRepr = .scalar tagW tagS) :
    refEnumLayoutData ety =
      (let tag : Miri.ABI.Scalar :=
        .Union (value := .Int (toMiriInteger tagW) tagS)
       { refBaseLayoutData (.Scalar tag) (toMiriSize tagW) with
         fields := .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0])
         variants := .Multiple tag .Direct 0
           (Array.mk (ety.discriminants.map (fun _ =>
             refInhabitedVariantLayout))) }) := by
  dsimp only [refEnumLayoutData]
  rw [h_tr]

private theorem readDiscriminant_validity_local_scalar_enum
    (types : List MirTy) (c : Choice) (ty : MirTy) (ety : EnumTy)
    (tagW : IntWidth)
    (tagS : Bool) (variant disc : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_el : EnumLike types ty ety)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (refValidityDiscriminantHooks types) c
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types ty⟩ st =
      .ok variant st := by
  have h_proj :
      Miri.Interpreter.OperandMachine.field (refValidityOperandHooks types) c
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types ty⟩ 0 st =
      .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    dsimp only [Miri.Interpreter.OperandMachine.field, refValidityOperandHooks,
      refBaseCompilerHooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
      EStateM.pure]
    have h_pf : Miri.Interpreter.projectField (refProjectionCx types)
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types ty⟩ 0 =
        .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ := by
      dsimp only [Miri.Interpreter.projectField, refProjectionCx]
      rw [enumLike_projectField0 h_el h_tr]
      rw [enumLike_layout h_el]
      rw [refEnumLayoutData_scalar ety tagW tagS h_tr]
      cases tagW <;> cases tagS <;> rfl
    rw [h_pf]
    rfl
  have h_ri :
      Miri.Interpreter.PlaceMachine.readImmediate
        { refAccessConfig with ghostMode := true, deinitMovedPlace := false }
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    cases st with
    | mk stack machine =>
      cases machine with
      | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
          user pendingMoveDeinit =>
        dsimp only at h_pmd
        subst h_pmd
        cases tagW <;> cases tagS <;> rfl
  exact readDiscriminant_validity_scalar_enum types c ty ety tagW tagS
    variant disc
    _ _ st h_tr h_adm h_el h_get_d h_proj h_ri

private theorem placeToOp_local_field0_enumLike (types : List MirTy)
    (c : Choice) (frameIdx : Nat) (localId : LocalId) (ty : MirTy) (ety : EnumTy)
    (tagW : IntWidth)
    (tagS : Bool) (imm : Immediate Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike types ty ety)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate imm), some (refLocalLayoutForTy types ty)⟩)
    (h_imm_ok : imm = .uninit ∨
      ∃ sc, imm = .scalar sc ∧ sc.size = toMiriSize tagW) :
    Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place c
        ⟨.local frameIdx localId (some Size.ZERO) (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st =
      .ok ⟨.immediate imm, refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
  have h_op : frame.getLocalOperand localId = .ok (.immediate imm) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]
    rw [h_get]; rfl
  have h_sz : (refLocalLayoutForTy types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_off :
      (⟨.immediate imm, refLocalLayoutForTy types ty⟩ :
          OpTy Miri.Memory.Provenance).offset (refProjectionCx types)
        Size.ZERO (refLocalLayoutForTy types (.int tagW tagS)) =
      .ok ⟨.immediate imm, refLocalLayoutForTy types (.int tagW tagS)⟩ := by
    rw [enumLike_layout h_el]
    dsimp only [OpTy.offset, OpTy.offsetWithMeta, refProjectionCx,
      Miri.Interpreter.projectionImmediateOffset, refLocalLayoutForTy,
      refLayoutDataForTy]
    rw [refEnumLayoutData_scalar ety tagW tagS h_tr]
    cases h_imm_ok with
    | inl h_u =>
      subst h_u
      cases tagW <;> cases tagS <;> rfl
    | inr h_s =>
      let ⟨sc, h_eq, _⟩ := h_s
      subst h_eq
      cases tagW <;> cases tagS <;> rfl
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    Miri.Interpreter.PlaceMachine.localToOp,
    Miri.Interpreter.PlaceMachine.localToOpCore,
    Miri.Interpreter.PlaceMachine.layoutLocal,
    Miri.Interpreter.MachineHooks.currentFrame]
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    refBaseCompilerHooks_debugAssertions,
    refBaseCompilerHooks_validationInProgress,
    refBaseCompilerHooks_projection,
    h_fidx, h_curr, h_get, h_op, h_sz,
    bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [afterLocalRead_no_race frame st localId h_curr h_dr]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_off]
  rfl

theorem mem_resolveTy_tyIdFor_int (types : List MirTy) (w : IntWidth)
    (s : Bool) :
    resolveTy types (tyIdFor types (.int w s)) = some (.int w s) := by
  cases w <;> cases s <;> exact resolveTy_tyIdFor_of_aux (h := rfl)

private theorem forIn_empty_array {ε σ α β : Type} (init : β)
    (f : α → β → EStateM ε σ (ForInStep β)) (st : σ) :
    forIn ((Array.mk []) : Array α) init f st = .ok init st := rfl

theorem forIn_singleton_array {ε σ α β : Type} (x : α) (init : β)
    (f : α → β → EStateM ε σ (ForInStep β)) (st : σ) :
    forIn ((Array.mk [x]) : Array α) init f st =
      (match f x init st with
      | .ok (.done b) s => .ok b s
      | .ok (.yield b) s => .ok b s
      | .error e s => .error e s) := by
  have h : forIn ((Array.mk [x]) : Array α) init f = forIn ([x] : List α) init f :=
    (Array.forIn_toList (xs := (Array.mk [x])) (b := init) (f := f)).symm
  rw [h]
  dsimp only [forIn, forIn', List.forIn', List.forIn'.loop,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases f x init st with
  | ok r s => cases r <;> rfl
  | error e s => rfl

private theorem validatePlace_shallow_local_step (types : List MirTy)
    (c : Choice) (place : RuntimePlace Miri.Memory.Provenance)
    (imm : Immediate Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate imm, place.layout⟩ st)
    (h_vis :
      let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess place st = .ok initSess st) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        place false true st = .ok () st := by
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_typeName]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    ite_true, ite_false]
  rw [refValHooks_withGhostValidation, mem_ite_true_eq]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp, h_toOp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [mem_ite_false_eq, h_vis]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [Miri.Interpreter.ValidityVisitor.resetPadding_no_ranges _ _ _ _ rfl]
  rfl

private theorem validatePlace_shallow_local_ub_step (types : List MirTy)
    (c : Choice) (place : RuntimePlace Miri.Memory.Provenance)
    (imm : Immediate Miri.Memory.Provenance)
    (st st' : Miri.Interpreter.MachineHooks.State Unit RefUser) (msg : String)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate imm, place.layout⟩ st)
    (h_vis :
      let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
        path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none
      }
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8
        initSess place st = .error (.undefinedBehavior msg) st') :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooks types) c 8
        place false true st = .error (.undefinedBehavior msg) st' := by
  dsimp only [Miri.Interpreter.ValidityVisitor.validatePlace,
    bind, Bind.bind, EStateM.bind]
  rw [refValHooks_typeName]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    ite_true, ite_false]
  rw [refValHooks_withGhostValidation, mem_ite_true_eq]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp, h_toOp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [mem_ite_false_eq, h_vis]

theorem visit_local_fieldless_enum (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance) (ty : MirTy) (ety : EnumTy)
    (variant : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_ty : place.layout.ty = tyIdFor types ty)
    (h_el : EnumLike types ty ety)
    (h_fields : place.layout.layout.fields = .Arbitrary (Array.mk []) (Array.mk []))
    (h_vars : place.layout.layout.variants = .Single variant)
    (h_rt : session.ctfeMode = none) :
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        session place st = .ok session st := by
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true ==
          .box) =
        false := rfl
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [h_ty, enumLike_classify h_el]
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session
          Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_rt, h_ne_box, mem_ite_false_eq, h_fields, h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [forIn_empty_array]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [enumLike_opsemInhabited h_el]
  rw [refValHooks_debugAssertions]
  cases session with
  | mk path flags mode tracking bytes =>
    cases flags with
    | mk rst md =>
      dsimp only at h_rt
      subst h_rt
      rfl

private theorem visit_local_int_ok (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance) (w : IntWidth) (s : Bool)
    (bits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types (.int w s))
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_db : session.dataBytes = none)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar w bits))),
        refLocalLayoutForTy types (.int w s)⟩ st) :
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        session place st = .ok session st := by
  cases session with
  | mk path flags mode tracking bytes =>
    cases flags with
    | mk rst md =>
      dsimp only at h_db
      subst h_db
      have h_toOp' : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
          c place st = .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar w bits))),
            place.layout⟩ st := by
        rw [h_lay]; exact h_toOp
      have h_ri : (refValHooks types).readImmediate c place .integer st =
          .ok ⟨.scalar (.fromScalarInt (miriScalar w bits)),
            refLocalLayoutForTy types (.int w s)⟩ st := by
        rw [refValHooks_readImmediate]
        dsimp only [bind, Bind.bind, EStateM.bind]
        rw [h_toOp]
        exact validityMemory_readImmediate_imm_scalar types (.int w s)
          (.fromScalarInt (miriScalar w bits)) .integer st (Or.inr ⟨w, s, rfl⟩)
      dsimp only [Miri.Interpreter.ValidityVisitor.visit,
        bind, Bind.bind, EStateM.bind]
      rw [h_lay, mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
      dsimp only
      change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c place .integer) _) _ st) = _
      dsimp only [EStateM.bind]
      rw [h_ri]
      cases rst with
      | false => rfl
      | true =>
        change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c place) _) _ st) = _
        dsimp only [EStateM.bind]
        rw [refValHooks_clearProvenance,
          clearPlaceProvenance_imm_no_prov types c place
            (.scalar (.fromScalarInt (miriScalar w bits))) st h_toOp' rfl]
        rfl

private theorem visit_local_int_uninit_ub (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance) (w : IntWidth) (s : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types (.int w s))
    (h_res : resolveTy types (tyIdFor types (.int w s)) = some (.int w s))
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate .uninit, refLocalLayoutForTy types (.int w s)⟩ st) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          session place st = .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_u⟩ := validityMemory_readImmediate_imm_uninit types (.int w s)
    .integer st (Or.inr ⟨w, s, rfl⟩)
  have h_ri : (refValHooks types).readImmediate c place .integer st =
      .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_toOp]
    exact h_u
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [h_lay, mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c place .integer) _) _ st) = _
  dsimp only [EStateM.bind]
  rw [h_ri]

private theorem visit_local_bool_ok (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance) (b : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types .bool)
    (h_res : resolveTy types (tyIdFor types .bool) = some .bool)
    (h_rst : session.flags.resetProvenanceAndPadding = true)
    (h_db : session.dataBytes = none)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate (.scalar (.fromBool b)),
        refLocalLayoutForTy types .bool⟩ st) :
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        session place st = .ok session st := by
  cases session with
  | mk path flags mode tracking bytes =>
    cases flags with
    | mk rst md =>
      dsimp only at h_rst h_db
      subst h_rst h_db
      have h_toOp' : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
          c place st = .ok ⟨.immediate (.scalar (.fromBool b)), place.layout⟩ st := by
        rw [h_lay]; exact h_toOp
      have h_ri : (refValHooks types).readImmediate c place .boolean st =
          .ok ⟨.scalar (.fromBool b), refLocalLayoutForTy types .bool⟩ st := by
        rw [refValHooks_readImmediate]
        dsimp only [bind, Bind.bind, EStateM.bind]
        rw [h_toOp]
        exact validityMemory_readImmediate_imm_scalar types .bool
          (.fromBool b) .boolean st (Or.inl rfl)
      dsimp only [Miri.Interpreter.ValidityVisitor.visit,
        bind, Bind.bind, EStateM.bind]
      rw [h_lay, mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
      dsimp only
      change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c place .boolean) _) _ st) = _
      dsimp only [EStateM.bind]
      rw [h_ri]
      cases b with
      | false =>
        change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c place) _) _ st) = _
        dsimp only [EStateM.bind]
        rw [refValHooks_clearProvenance,
          clearPlaceProvenance_imm_no_prov types c place (.scalar (.fromBool false)) st
            h_toOp' rfl]
        rfl
      | true =>
        change (EStateM.bind (EStateM.bind ((refValHooks types).clearProvenance c place) _) _ st) = _
        dsimp only [EStateM.bind]
        rw [refValHooks_clearProvenance,
          clearPlaceProvenance_imm_no_prov types c place (.scalar (.fromBool true)) st
            h_toOp' rfl]
        rfl

private theorem visit_local_bool_uninit_ub (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types .bool)
    (h_res : resolveTy types (tyIdFor types .bool) = some .bool)
    (h_toOp : Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate .uninit, refLocalLayoutForTy types .bool⟩ st) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          session place st = .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_u⟩ := validityMemory_readImmediate_imm_uninit types .bool .boolean
    st (Or.inl rfl)
  have h_ri : (refValHooks types).readImmediate c place .boolean st =
      .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_toOp]
    exact h_u
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [h_lay, mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind ((refValHooks types).readImmediate c place .boolean) _) _ st) = _
  dsimp only [EStateM.bind]
  rw [h_ri]

theorem visit_local_never_ub (types : List MirTy) (c : Choice)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types .never)
    (h_res : resolveTy types (tyIdFor types .never) = some .never) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          session place st = .error (.undefinedBehavior msg) st := by
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_lay, mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  exact ⟨_, rfl⟩

private theorem visit_local_scalar_enum_ok (types : List MirTy) (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1) (frameIdx : Nat) (localId : LocalId)
    (ty : MirTy) (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool) (variant disc : Nat)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_el : EnumLike types ty ety)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))))),
        some (refLocalLayoutForTy types ty)⟩) :
    let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        initSess
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types ty⟩ st = .ok initSess st := by
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true ==
          .box) =
        false := rfl
  have h_fields : (refLocalLayoutForTy types ty).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0]) := by
    rw [enumLike_layout h_el]
    rw [refEnumLayoutData_scalar ety tagW tagS h_tr]
  have h_vars : (refLocalLayoutForTy types ty).layout.variants =
      .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct 0
        (ety.discriminants.map (fun _ => refInhabitedVariantLayout)).toArray := by
    rw [enumLike_layout h_el]
    rw [refEnumLayoutData_scalar ety tagW tagS h_tr]
  have h_v_lt : variant < ety.discriminants.length :=
    mirGetElem?_lt_of_some h_get_d
  have h_toOp := placeToOp_local_immediate types c frameIdx localId ty
    (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))))
    frame st h_curr h_fidx h_dr h_get
  have h_ms_sz :
      (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
        (miriScalar tagW (BitVec.ofNat 128 disc))).size = toMiriSize tagW := by
    cases tagW <;> rfl
  have h_toOp_f0 := placeToOp_local_field0_enumLike types c frameIdx localId
    ty ety tagW tagS
    (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))))
    frame st h_el h_tr h_curr h_fidx h_dr h_get (Or.inr ⟨_, rfl, h_ms_sz⟩)
  have h_res_tag :
      resolveTy types (tyIdFor types (.int tagW tagS)) =
        some (.int tagW tagS) :=
    mem_resolveTy_tyIdFor_int types tagW tagS
  have h_pf0 :
      Miri.Interpreter.PlaceDynamic.field (refBasePlaceProjectionHooks types) c
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types ty⟩ 0 st =
      .ok ⟨.local frameIdx localId (some Size.ZERO)
          (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    dsimp only [Miri.Interpreter.PlaceDynamic.field,
      Miri.Interpreter.PlaceDynamic.offsetWithMeta,
      refBasePlaceProjectionHooks,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [enumLike_projectField0 h_el h_tr]
    rw [enumLike_layout h_el, refEnumLayoutData_scalar ety tagW tagS h_tr]
    cases tagW <;> cases tagS <;> rfl
  have h_dc :
      Miri.Interpreter.PlaceDynamic.downcast (refBasePlaceProjectionHooks types) c
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types ty⟩ variant st =
      .ok ⟨.local frameIdx localId (some Size.ZERO)
          (LocalsIdentity.ofAllocationToken 0),
          ⟨tyIdFor types ty,
            { refUnitLayoutData with variants := .Single variant }⟩⟩ st := by
    have h_blt : Nat.blt variant ety.discriminants.length = true :=
      Nat.ble_eq_true_of_le h_v_lt
    dsimp only [Miri.Interpreter.PlaceDynamic.downcast,
      Miri.Interpreter.PlaceDynamic.offsetWithMeta,
      refBasePlaceProjectionHooks,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [enumLike_projectVariant h_el h_v_lt]
    rw [enumLike_layout h_el, refEnumLayoutData_scalar ety tagW tagS h_tr]
    cases tagW <;> cases tagS <;> rfl
  have h_rd_discr := readDiscriminant_validity_local_scalar_enum types c
    ty ety tagW tagS variant disc st h_tr h_adm h_el h_get_d h_pmd
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, enumLike_classify h_el]
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session
          Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, mem_ite_false_eq, h_fields, h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_projection, forIn_singleton_array]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_pf0]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_fuel, visit_local_int_ok types c k _ _ tagW tagS (BitVec.ofNat 128 disc)
    st rfl h_res_tag rfl h_toOp_f0]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_toOp, refValHooks_discriminant, h_toOp]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_rd_discr]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_dc]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_variantPath]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [visit_local_fieldless_enum types c k _ _ ty ety variant st rfl h_el
    rfl rfl rfl]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  have h_inh : (refValHooks types).opsemInhabited c (tyIdFor types ty) st =
      .ok true st := by
    exact enumLike_opsemInhabited h_el c st
  rw [h_inh]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [mem_ite_true_eq, refValHooks_debugAssertions, mem_ite_false_eq]
  rfl

private theorem visit_local_scalar_enum_uninit_ub (types : List MirTy)
    (c : Choice) (fuel k : Nat) (h_fuel : fuel = k + 1) (frameIdx : Nat)
    (localId : LocalId) (ty : MirTy) (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_el : EnumLike types ty ety)
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate .uninit),
        some (refLocalLayoutForTy types ty)⟩) :
    let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none
    }
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          initSess
          ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy types ty⟩ st =
        .error (.undefinedBehavior msg) st := by
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true ==
          .box) =
        false := rfl
  have h_fields : (refLocalLayoutForTy types ty).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0]) := by
    rw [enumLike_layout h_el]
    rw [refEnumLayoutData_scalar ety tagW tagS h_tr]
  have h_toOp_f0 := placeToOp_local_field0_enumLike types c frameIdx localId
    ty ety tagW tagS .uninit frame st h_el h_tr h_curr h_fidx h_dr h_get (Or.inl rfl)
  have h_res_tag :
      resolveTy types (tyIdFor types (.int tagW tagS)) =
        some (.int tagW tagS) :=
    mem_resolveTy_tyIdFor_int types tagW tagS
  have h_pf0 :
      Miri.Interpreter.PlaceDynamic.field (refBasePlaceProjectionHooks types) c
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types ty⟩ 0 st =
      .ok ⟨.local frameIdx localId (some Size.ZERO)
          (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.int tagW tagS)⟩ st := by
    dsimp only [Miri.Interpreter.PlaceDynamic.field,
      Miri.Interpreter.PlaceDynamic.offsetWithMeta,
      refBasePlaceProjectionHooks,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [enumLike_projectField0 h_el h_tr]
    rw [enumLike_layout h_el, refEnumLayoutData_scalar ety tagW tagS h_tr]
    cases tagW <;> cases tagS <;> rfl
  let ⟨msg, h_vis_f0⟩ := visit_local_int_uninit_ub types c k
    { path := (⟨"", (Array.mk [])⟩ : ValidationPath).push .enumTag,
      flags := ⟨true, false || false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
    ⟨.local frameIdx localId (some Size.ZERO) (LocalsIdentity.ofAllocationToken 0),
      refLocalLayoutForTy types (.int tagW tagS)⟩
    tagW tagS st rfl h_res_tag h_toOp_f0
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [mem_refLocalLayoutForTy_ty, enumLike_classify h_el]
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session
          Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, mem_ite_false_eq, h_fields]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_projection, forIn_singleton_array]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_pf0]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_fuel, h_vis_f0]

private theorem validityMemory_readImmediate_imm_char
    (types : List MirTy) (sc : Scalar Miri.Memory.Provenance)
    (expected : ExpectedValue)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
        ⟨.immediate (.scalar sc), refLocalLayoutForTy types .char⟩ expected st =
      .ok ⟨.scalar sc, refLocalLayoutForTy types .char⟩ st := by
  cases st with | mk stack machine => rfl

private theorem validityMemory_readImmediate_imm_uninit_char
    (types : List MirTy) (expected : ExpectedValue)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    ∃ msg,
      Miri.Interpreter.ValidityMemory.readImmediate refValidityMemoryEnv
          ⟨.immediate .uninit, refLocalLayoutForTy types .char⟩ expected st =
        .error (.undefinedBehavior msg) st := by
  cases st with | mk stack machine => exact ⟨_, rfl⟩

private theorem visit_local_char_ok (types : List MirTy) (c : Choice)
    (fuel : Nat)
    (session : Miri.Interpreter.ValidityVisitor.Session
      Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance) (ch : Char)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types .char)
    (h_res : resolveTy types (tyIdFor types .char) = some .char)
    (h_rst : session.flags.resetProvenanceAndPadding = true)
    (h_db : session.dataBytes = none)
    (h_toOp :
      Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st = .ok ⟨.immediate (.scalar (.fromChar ch)),
        refLocalLayoutForTy types .char⟩ st) :
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        session place st = .ok session st := by
  cases session with
  | mk path flags mode tracking bytes =>
    cases flags with
    | mk rst md =>
      dsimp only at h_rst h_db
      subst h_rst h_db
      have h_toOp' :
          Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
            c place st =
            .ok ⟨.immediate (.scalar (.fromChar ch)), place.layout⟩ st := by
        rw [h_lay]; exact h_toOp
      have h_ri : (refValHooks types).readImmediate c place .character st =
          .ok ⟨.scalar (.fromChar ch), refLocalLayoutForTy types .char⟩ st := by
        rw [refValHooks_readImmediate]
        dsimp only [bind, Bind.bind, EStateM.bind]
        rw [h_toOp]
        exact validityMemory_readImmediate_imm_char types
          (.fromChar ch) .character st
      dsimp only [Miri.Interpreter.ValidityVisitor.visit,
        bind, Bind.bind, EStateM.bind]
      rw [h_lay, mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
      dsimp only
      change (EStateM.bind (EStateM.bind
        ((refValHooks types).readImmediate c place .character) _) _ st) = _
      rw [eStateM_bind_bind_ok h_ri]
      change (EStateM.bind (EStateM.bind (EStateM.pure (Scalar.fromChar ch))
        _) _ st) = _
      dsimp only [EStateM.bind, EStateM.pure, bind, Bind.bind, pure, Pure.pure]
      have h_cb :
          (Miri.Interpreter.ValidityVisitor.TypeKind.character == .boolean) =
            false := rfl
      have h_cc :
          (Miri.Interpreter.ValidityVisitor.TypeKind.character == .character) =
            true := rfl
      rw [h_cb, mem_ite_false_eq, h_cc, mem_ite_true_eq, scalar_toChar_fromChar]
      change (EStateM.bind (EStateM.bind
        ((refValHooks types).clearProvenance c place) _) _ st) = _
      dsimp only [EStateM.bind]
      rw [refValHooks_clearProvenance,
        clearPlaceProvenance_imm_no_prov types c place
          (.scalar (.fromChar ch)) st
          h_toOp' rfl]
      rfl

private theorem visit_local_char_uninit_ub (types : List MirTy) (c : Choice)
    (fuel : Nat)
    (session : Miri.Interpreter.ValidityVisitor.Session
      Miri.Memory.Provenance)
    (place : RuntimePlace Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lay : place.layout = refLocalLayoutForTy types .char)
    (h_res : resolveTy types (tyIdFor types .char) = some .char)
    (h_toOp :
      Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place
      c place st =
        .ok ⟨.immediate .uninit, refLocalLayoutForTy types .char⟩ st) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          session place st = .error (.undefinedBehavior msg) st := by
  let ⟨msg, h_u⟩ := validityMemory_readImmediate_imm_uninit_char types
    .character st
  have h_ri : (refValHooks types).readImmediate c place .character st =
      .error (.undefinedBehavior msg) st := by
    rw [refValHooks_readImmediate]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [h_toOp]
    exact h_u
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  rw [h_lay, mem_refLocalLayoutForTy_ty, refValHooks_classify, h_res]
  dsimp only
  change (EStateM.bind (EStateM.bind
    ((refValHooks types).readImmediate c place .character) _) _ st) = _
  dsimp only [EStateM.bind]
  rw [h_ri]

theorem forIn_pair_array {ε σ α β : Type} (x y : α) (init : β)
    (f : α → β → EStateM ε σ (ForInStep β)) (st : σ) :
    forIn ((Array.mk [x, y]) : Array α) init f st =
      (match f x init st with
      | .ok (.done b) s => .ok b s
      | .ok (.yield b) s =>
        (match f y b s with
        | .ok (.done b') s' => .ok b' s'
        | .ok (.yield b') s' => .ok b' s'
        | .error e s' => .error e s')
      | .error e s => .error e s) := by
  have h : forIn ((Array.mk [x, y]) : Array α) init f =
      forIn ([x, y] : List α) init f :=
    (Array.forIn_toList (xs := (Array.mk [x, y])) (b := init) (f := f)).symm
  rw [h]
  dsimp only [forIn, forIn', List.forIn', List.forIn'.loop,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases f x init st with
  | ok r s =>
    cases r with
    | done b => rfl
    | yield b =>
      dsimp only [EStateM.bind]
      cases f y b s with
      | ok r' s' => cases r' <;> rfl
      | error e s' => rfl
  | error e s => rfl

private theorem refProjectFieldLayout_pair0 (types : List MirTy) (w : IntWidth)
    (s : Bool)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    refProjectFieldLayout types
        (refLocalLayoutForTy types (.tuple [.int w s, .bool])) 0 =
      .ok (refLocalLayoutForTy types (.int w s)) := by
  dsimp only [refProjectFieldLayout, refLocalLayoutForTy]
  rw [h_res]
  rfl

private theorem refProjectFieldLayout_pair1 (types : List MirTy) (w : IntWidth)
    (s : Bool)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    refProjectFieldLayout types
        (refLocalLayoutForTy types (.tuple [.int w s, .bool])) 1 =
      .ok (refLocalLayoutForTy types .bool) := by
  dsimp only [refProjectFieldLayout, refLocalLayoutForTy]
  rw [h_res]
  rfl

private theorem pair_offset0 (types : List MirTy) (w : IntWidth) (s : Bool)
    (a b : Scalar Miri.Memory.Provenance) :
    (⟨.immediate (.scalarPair a b),
        refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ :
        OpTy Miri.Memory.Provenance).offset (refProjectionCx types)
      Size.ZERO (refLocalLayoutForTy types (.int w s)) =
    .ok ⟨.immediate (.scalar a), refLocalLayoutForTy types (.int w s)⟩ := by
  cases w <;> rfl

private theorem pair_offset1 (types : List MirTy) (w : IntWidth) (s : Bool)
    (a b : Scalar Miri.Memory.Provenance) :
    (⟨.immediate (.scalarPair a b),
        refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ :
        OpTy Miri.Memory.Provenance).offset (refProjectionCx types)
      (toMiriSize w) (refLocalLayoutForTy types .bool) =
    .ok ⟨.immediate (.scalar b), refLocalLayoutForTy types .bool⟩ := by
  cases w <;> rfl

private theorem pair_offset0_uninit (types : List MirTy) (w : IntWidth)
    (s : Bool) :
    (⟨.immediate .uninit,
        refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ :
        OpTy Miri.Memory.Provenance).offset (refProjectionCx types)
      Size.ZERO (refLocalLayoutForTy types (.int w s)) =
    .ok ⟨.immediate .uninit, refLocalLayoutForTy types (.int w s)⟩ := by
  cases w <;> rfl

private theorem placeToOp_local_offset (types : List MirTy)
    (c : Choice) (frameIdx : Nat) (localId : LocalId) (ty fty : MirTy) (off : Size)
    (imm res : Immediate Miri.Memory.Provenance)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate imm), some (refLocalLayoutForTy types ty)⟩)
    (h_off :
      (⟨.immediate imm, refLocalLayoutForTy types ty⟩ :
          OpTy Miri.Memory.Provenance).offset (refProjectionCx types)
        off (refLocalLayoutForTy types fty) =
      .ok ⟨.immediate res, refLocalLayoutForTy types fty⟩) :
    Miri.Interpreter.placeToOp (refBasePlaceProjectionHooks types).place c
        ⟨.local frameIdx localId (some off) (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types fty⟩ st =
      .ok ⟨.immediate res, refLocalLayoutForTy types fty⟩ st := by
  have h_op : frame.getLocalOperand localId = .ok (.immediate imm) := by
    dsimp only [Miri.Interpreter.Frame.getLocalOperand]
    rw [h_get]; rfl
  have h_sz : (refLocalLayoutForTy types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
    refBasePlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    Miri.Interpreter.PlaceMachine.localToOp,
    Miri.Interpreter.PlaceMachine.localToOpCore,
    Miri.Interpreter.PlaceMachine.layoutLocal,
    Miri.Interpreter.MachineHooks.currentFrame]
  simp only [get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    refBaseCompilerHooks_debugAssertions,
    refBaseCompilerHooks_validationInProgress,
    refBaseCompilerHooks_projection,
    h_fidx, h_curr, h_get, h_op, h_sz,
    bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [afterLocalRead_no_race frame st localId h_curr h_dr]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_off]
  rfl

private theorem placeDynamic_field_local_pair0 (types : List MirTy) (c : Choice)
    (frameIdx : Nat) (localId : LocalId) (w : IntWidth) (s : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    Miri.Interpreter.PlaceDynamic.field (refBasePlaceProjectionHooks types) c
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ 0 st =
      .ok ⟨.local frameIdx localId (some Size.ZERO)
          (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.int w s)⟩ st := by
  dsimp only [Miri.Interpreter.PlaceDynamic.field,
    Miri.Interpreter.PlaceDynamic.offsetWithMeta,
    refBasePlaceProjectionHooks,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refProjectFieldLayout_pair0 types w s h_res]
  cases w <;> rfl

private theorem placeDynamic_field_local_pair1 (types : List MirTy) (c : Choice)
    (frameIdx : Nat) (localId : LocalId) (w : IntWidth) (s : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    Miri.Interpreter.PlaceDynamic.field (refBasePlaceProjectionHooks types) c
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ 1 st =
      .ok ⟨.local frameIdx localId (some (toMiriSize w))
          (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types .bool⟩ st := by
  dsimp only [Miri.Interpreter.PlaceDynamic.field,
    Miri.Interpreter.PlaceDynamic.offsetWithMeta,
    refBasePlaceProjectionHooks,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refProjectFieldLayout_pair1 types w s h_res]
  cases w <;> rfl

private theorem pair_classify (types : List MirTy) (c : Choice) (w : IntWidth)
    (s : Bool) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    (refValHooks types).classify c
      (tyIdFor types (.tuple [.int w s, .bool])) st =
      .ok (.aggregate false false false) st := by
  rw [refValHooks_classify, h_res]

private theorem pair_opsemInhabited (types : List MirTy) (c : Choice)
    (w : IntWidth)
    (s : Bool) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool])) :
    (refValHooks types).opsemInhabited c
      (tyIdFor types (.tuple [.int w s, .bool])) st = .ok true st := by
  rw [refValHooks_opsemInhabited, h_res]

private theorem visit_local_pair_ok (types : List MirTy) (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1) (frameIdx : Nat) (localId : LocalId) (w : IntWidth)
    (s : Bool)
    (bits : BitVec 128) (b : Bool)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool]))
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate (.scalarPair (.fromScalarInt (miriScalar w bits))
          (.fromBool b))),
        some (refLocalLayoutForTy types (.tuple [.int w s, .bool]))⟩) :
    let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
        initSess
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st =
      .ok initSess st := by
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false false ==
          .box) =
        false := rfl
  have h_fields :
      (refLocalLayoutForTy types (.tuple [.int w s, .bool])).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO, toMiriSize w]) (Array.mk [0, 1]) := rfl
  have h_vars :
      (refLocalLayoutForTy types (.tuple [.int w s, .bool])).layout.variants =
      .Single 0 := rfl
  have h_res_int := mem_resolveTy_tyIdFor_int types w s
  have h_res_bool : resolveTy types (tyIdFor types .bool) = some .bool :=
    resolveTy_tyIdFor_of_aux (h := rfl)
  have h_pf0 := placeDynamic_field_local_pair0 types c frameIdx localId w s st h_res
  have h_pf1 := placeDynamic_field_local_pair1 types c frameIdx localId w s st h_res
  have h_toOp_f0 := placeToOp_local_offset types c frameIdx localId
    (.tuple [.int w s, .bool]) (.int w s) Size.ZERO _
    (.scalar (.fromScalarInt (miriScalar w bits))) frame st h_curr h_fidx h_dr h_get
    (pair_offset0 types w s _ _)
  have h_toOp_f1 := placeToOp_local_offset types c frameIdx localId
    (.tuple [.int w s, .bool]) .bool (toMiriSize w) _
    (.scalar (.fromBool b)) frame st h_curr h_fidx h_dr h_get
    (pair_offset1 types w s _ _)
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  simp only [mem_refLocalLayoutForTy_ty, pair_classify types c w s st h_res]
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session
          Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, mem_ite_false_eq, h_fields, h_vars]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_projection, forIn_pair_array]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_pf0]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_fuel, visit_local_int_ok types c k _ _ w s bits st rfl h_res_int rfl
    h_toOp_f0]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_pf1]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [visit_local_bool_ok types c k _ _ b st rfl h_res_bool rfl rfl h_toOp_f1]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  simp only [pair_opsemInhabited types c w s _ h_res, ite_true,
    refValHooks_debugAssertions, Bool.false_eq_true, ite_false]
  rfl

private theorem visit_local_pair_uninit_ub (types : List MirTy) (c : Choice)
    (fuel k : Nat) (h_fuel : fuel = k + 1) (frameIdx : Nat) (localId : LocalId) (w : IntWidth)
    (s : Bool)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy types (tyIdFor types (.tuple [.int w s, .bool])) =
      some (.tuple [.int w s, .bool]))
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate .uninit),
        some (refLocalLayoutForTy types (.tuple [.int w s, .bool]))⟩) :
    let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none
    }
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c (fuel + 1)
          initSess
          ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st =
        .error (.undefinedBehavior msg) st := by
  have h_ne_box :
      (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false false ==
          .box) =
        false := rfl
  have h_fields :
      (refLocalLayoutForTy types (.tuple [.int w s, .bool])).layout.fields =
      .Arbitrary (Array.mk [Size.ZERO, toMiriSize w]) (Array.mk [0, 1]) := rfl
  have h_res_int := mem_resolveTy_tyIdFor_int types w s
  have h_pf0 := placeDynamic_field_local_pair0 types c frameIdx localId w s st h_res
  have h_toOp_f0 := placeToOp_local_offset types c frameIdx localId
    (.tuple [.int w s, .bool]) (.int w s) Size.ZERO _ .uninit frame st
    h_curr h_fidx h_dr h_get (pair_offset0_uninit types w s)
  let ⟨msg, h_vis_f0⟩ := visit_local_int_uninit_ub types c k
    { path := (⟨"", (Array.mk [])⟩ : ValidationPath).push .enumTag,
      flags := ⟨true, false || false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
    ⟨.local frameIdx localId (some Size.ZERO) (LocalsIdentity.ofAllocationToken 0),
      refLocalLayoutForTy types (.int w s)⟩
    w s st rfl h_res_int h_toOp_f0
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.ValidityVisitor.visit,
    bind, Bind.bind, EStateM.bind]
  simp only [mem_refLocalLayoutForTy_ty, pair_classify types c w s st h_res]
  change (match (EStateM.Result.ok none st :
      EStateM.Result StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (Option (Miri.Interpreter.ValidityVisitor.Session
          Miri.Memory.Provenance))) with
    | EStateM.Result.ok a s => _
    | EStateM.Result.error e s => EStateM.Result.error e s) = _
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ne_box, mem_ite_false_eq, h_fields]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_projection, forIn_pair_array]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_pf0]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [refValHooks_fieldPath]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_fuel, h_vis_f0]

theorem isOverflowPairTy_inv {fs : List MirTy}
    (h : isOverflowPairTy (.tuple fs) = true) :
    ∃ w s, fs = [.int w s, .bool] := by
  cases fs with
  | nil => cases h
  | cons f rest =>
    cases f with
    | int w s =>
      cases rest with
      | nil => cases h
      | cons g rest2 =>
        cases g with
        | bool =>
          cases rest2 with
          | nil => exact ⟨w, s, rfl⟩
          | cons _ _ => cases h
        | _ => cases h
    | _ => cases h

/-- Variant index of a `core::cmp::Ordering` value in `refOrderingEnumTy`. -/
noncomputable def orderingVariantIdx : OrderingVal → Nat
  | .less => 0
  | .equal => 1
  | .greater => 2

theorem orderingVariant_getElem? (o : OrderingVal) :
    MirSemantics.getElem? refOrderingEnumTy.discriminants
      (orderingVariantIdx o) = some (orderingTagBits o) := by
  cases o <;> rfl

theorem orderingVariant_enumVariantOfVal (o : OrderingVal) :
    refEnumVariantOfVal? .ordering (.ordering o) =
      some (orderingVariantIdx o) := by
  cases o <;> rfl

theorem orderingVariant_valOfEnumVariant (o : OrderingVal) :
    refValOfEnumVariant? .ordering (orderingVariantIdx o) =
      some (.ordering o) := by
  cases o <;> rfl

theorem valToMiriImmediate_scalar_enumLike {ty : MirTy} {ety : EnumTy}
    {v : Val} {variant disc : Nat} {tagW : IntWidth} {tagS : Bool}
    (h_as : refAsEnumTy? ty = some ety)
    (h_ev : refEnumVariantOfVal? ty v = some variant)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc) :
    valToMiriImmediate ty v =
      .scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))) := by
  cases ty with
  | enum _ =>
    cases h_as
    cases v <;> cases h_ev
    dsimp only [valToMiriImmediate, refAsEnumTy?, refEnumVariantOfVal?]
    rw [h_tr, h_get_d]
  | ordering =>
    cases h_as
    cases v with
    | ordering o =>
      cases o <;> cases h_ev <;> (
        dsimp only [valToMiriImmediate, refAsEnumTy?, refEnumVariantOfVal?]
        rw [h_tr, h_get_d])
    | _ => cases h_ev
  | _ => cases h_as

private theorem visit_local_enumLike_ok (types : List MirTy) (c : Choice)
    (frameIdx : Nat) (localId : LocalId) (ty : MirTy) (ety : EnumTy) (v : Val)
    (variant : Nat)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike types ty ety)
    (h_adm : enumAdmitted ety = true)
    (h_ev : refEnumVariantOfVal? ty v = some variant)
    (h_v_lt : variant < ety.discriminants.length)
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate (valToMiriImmediate ty v)),
        some (refLocalLayoutForTy types ty)⟩) :
    let initSess :
        Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
      path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none
    }
    Miri.Interpreter.ValidityVisitor.visit (refValHooks types) c 8 initSess
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types ty⟩ st = .ok initSess st := by
  cases h_tr : ety.tagRepr with
  | zeroSized =>
    exact visit_local_fieldless_enum types c 7 _ _ ty ety 0 st rfl h_el
      (by rw [enumLike_layout h_el]; dsimp only [refEnumLayoutData]
          rw [h_tr]; rfl)
      (by rw [enumLike_layout h_el]; dsimp only [refEnumLayoutData]
          rw [h_tr]; rfl)
      rfl
  | scalar tagW tagS =>
    let ⟨disc, h_get_d⟩ := mirGetElem?_some_of_lt h_v_lt
    rw [valToMiriImmediate_scalar_enumLike h_el.1 h_ev h_tr h_get_d] at h_get
    exact visit_local_scalar_enum_ok types c 7 6 rfl frameIdx localId ty ety tagW tagS
      variant disc frame st h_tr h_adm h_el h_get_d h_curr h_fidx h_dr h_pmd h_get

/-- `ValidityVisitor.validatePlace` on an initialized Day-1 `.local` holding
`valToMiriImmediate ty v` with `checkVal v ty = true` succeeds without
mutating state. -/
theorem validatePlace_local_ok (types : List MirTy) (c : Choice)
    (frameIdx : Nat) (localId : LocalId) (ty : MirTy) (v : Val)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate (valToMiriImmediate ty v)),
        some (refLocalLayoutForTy types ty)⟩)
    (h_cv : checkVal v ty = true)
    (h_res : resolveTy types (tyIdFor types ty) = some ty) :
    Miri.Interpreter.ValidityVisitor.validatePlace
        (Miri.Interpreter.TypedMachineBindings.bindValidity
          (refValidityHooks types) refRetagHooks 8)
        c 8
        ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy types ty⟩
        false true st = .ok () st := by
  have h_toOp := placeToOp_local_immediate types c frameIdx localId ty
    (valToMiriImmediate ty v) frame st h_curr h_fidx h_dr h_get
  refine validatePlace_shallow_local_step types c _ _ st h_toOp ?_
  cases checkVal_eq_true_inv h_cv with
  | inl h_i =>
    let ⟨w, s, bits, hty, hv, _⟩ := h_i
    subst hty hv
    exact visit_local_int_ok types c 7 _ _ w s bits st rfl h_res rfl h_toOp
  | inr h_rest =>
  cases h_rest with
  | inl h_b =>
    let ⟨b, hty, hv⟩ := h_b
    subst hty hv
    exact visit_local_bool_ok types c 7 _ _ b st rfl h_res rfl rfl h_toOp
  | inr h_rest =>
  cases h_rest with
  | inl h_u =>
    let ⟨hty, hv⟩ := h_u
    subst hty hv
    exact Miri.Interpreter.ValidityVisitor.visit_fieldless
      (refValHooks types) c 7 _ _ st 0
      (by rw [refValHooks_classify]; dsimp only [refLocalLayoutForTy]
          rw [h_res])
      (by rw [refValHooks_opsemInhabited]; dsimp only [refLocalLayoutForTy]
          rw [h_res])
      rfl rfl rfl rfl
  | inr h_rest =>
  cases h_rest with
  | inl h_e =>
    let ⟨ety, variant, hty, hv, h_adm, h_v_lt⟩ := h_e
    subst hty hv
    exact visit_local_enumLike_ok types c frameIdx localId (.enum ety) ety
      (.enumVal ety variant) variant frame st ⟨rfl, h_res⟩ h_adm rfl h_v_lt
      h_curr h_fidx h_dr h_pmd h_get
  | inr h_rest =>
  cases h_rest with
  | inl h_c =>
    let ⟨ch, hty, hv⟩ := h_c
    subst hty hv
    exact visit_local_char_ok types c 7 _ _ ch st rfl h_res rfl rfl h_toOp
  | inr h_rest =>
  cases h_rest with
  | inl h_o =>
    let ⟨o, hty, hv⟩ := h_o
    subst hty hv
    exact visit_local_enumLike_ok types c frameIdx localId .ordering refOrderingEnumTy
      (.ordering o) (orderingVariantIdx o) frame st ⟨rfl, h_res⟩
      mem_refOrderingEnumTy_admitted (orderingVariant_enumVariantOfVal o)
      (mirGetElem?_lt_of_some (orderingVariant_getElem? o))
      h_curr h_fidx h_dr h_pmd h_get
  | inr h_p =>
    let ⟨w, s, bits, b, hty, hv, _⟩ := h_p
    subst hty hv
    exact visit_local_pair_ok types c 7 6 rfl frameIdx localId w s bits b frame st h_res
      h_curr h_fidx h_dr h_get

/-- `ValidityVisitor.validatePlace` on an uninitialized non-ZST Day-1 `.local`
fails with `.undefinedBehavior`. -/
theorem validatePlace_local_uninit_ub (types : List MirTy) (c : Choice)
    (frameIdx : Nat) (localId : LocalId) (ty : MirTy)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_curr : st.stack.currentFrame? = some frame)
    (h_fidx : st.stack.frameIndex = .ok frameIdx)
    (h_dr : frame.extra.dataRace = none)
    (h_get : frame.getLocal localId =
      .ok ⟨.live (.immediate .uninit), some (refLocalLayoutForTy types ty)⟩)
    (h_sm : SlotMatchesTy ty (.immediate none))
    (h_supp : isSupportedScalarOrUnitTy ty = true)
    (h_res : resolveTy types (tyIdFor types ty) = some ty) :
    ∃ msg st',
      Miri.Interpreter.ValidityVisitor.validatePlace
          (Miri.Interpreter.TypedMachineBindings.bindValidity
            (refValidityHooks types) refRetagHooks 8)
          c 8
          ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy types ty⟩
          false true st = .error (.undefinedBehavior msg) st' := by
  have h_toOp := placeToOp_local_immediate types c frameIdx localId ty .uninit frame st
    h_curr h_fidx h_dr h_get
  let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
    path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
    refTracking := none, dataBytes := none
  }
  cases ty with
  | unit => exact False.elim (h_sm.1 rfl)
  | never =>
    let ⟨msg, h_vis⟩ := visit_local_never_ub types c 7 initSess
      ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy types .never⟩ st rfl h_res
    exact ⟨msg, st,
      validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | bool =>
    let ⟨msg, h_vis⟩ := visit_local_bool_uninit_ub types c 7 initSess
      ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy types .bool⟩ st rfl h_res h_toOp
    exact ⟨msg, st,
      validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | int w s =>
    let ⟨msg, h_vis⟩ := visit_local_int_uninit_ub types c 7 initSess
      ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy types (.int w s)⟩ w s st rfl h_res h_toOp
    exact ⟨msg, st,
      validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | char =>
    let ⟨msg, h_vis⟩ := visit_local_char_uninit_ub types c 7 initSess
      ⟨.local frameIdx localId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy types .char⟩ st rfl h_res h_toOp
    exact ⟨msg, st,
      validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | ordering =>
    let ⟨msg, h_vis⟩ := visit_local_scalar_enum_uninit_ub types c 7 6 rfl
      frameIdx localId .ordering refOrderingEnumTy .i8 true frame st rfl ⟨rfl, h_res⟩
      h_curr h_fidx h_dr h_get
    exact ⟨msg, st,
      validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | enum ety =>
    cases h_tr : ety.tagRepr with
    | zeroSized =>
      have h_zst := h_sm.2 ety rfl
      dsimp only [isZstEnumTy] at h_zst
      rw [h_tr] at h_zst
      dsimp only [isSupportedScalarOrUnitTy] at h_supp
      rw [h_supp] at h_zst
      cases h_zst
    | scalar tagW tagS =>
      let ⟨msg, h_vis⟩ := visit_local_scalar_enum_uninit_ub types c 7 6 rfl frameIdx localId
        (.enum ety) ety tagW tagS frame st h_tr ⟨rfl, h_res⟩
        h_curr h_fidx h_dr h_get
      exact ⟨msg, st,
        validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | tuple fs =>
    let ⟨w, s, h_fs⟩ := isOverflowPairTy_inv h_supp
    subst h_fs
    let ⟨msg, h_vis⟩ := visit_local_pair_uninit_ub types c 7 6 rfl frameIdx localId w s
      frame st
      h_res h_curr h_fidx h_dr h_get
    exact ⟨msg, st,
      validatePlace_shallow_local_ub_step types c _ _ st st msg h_toOp h_vis⟩
  | ref _ _ | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _ | range _
  | option _ | unsupported => cases h_supp

end Anneal.MirCorrespondence
