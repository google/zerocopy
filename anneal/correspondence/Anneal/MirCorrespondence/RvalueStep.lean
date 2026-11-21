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
import Anneal.MirCorrespondence.MemRoundTrip

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

/-!
# Operand and Rvalue Step Simulation (`Anneal.MirCorrespondence.RvalueStep`)

Proves per-operand, primitive-read, scalar-operator, discriminant-read,
local-write, and `evalRvalueIntoPlace` step equivalence between
$M_{\text{anneal}}$ (`Trusted.MirSemantics`) and real
`Miri.Interpreter.ExecutionMachine` (`Trusted.Correspondence`) over
`ExecutionMachine.withValidation (refExecutionConfig rp) refLimits`.
-/

/-! ## Section 1: Error Classification, State Builders, and Frame Lemmas -/

/-- Classify a `Miri.Interpreter.StepError` into $M_{\text{anneal}}$'s two fault
poles, matching `evalRefStep`'s error dispatch in
`Trusted/Correspondence/Eval.lean`. -/
def stepErrorFaultKind : Miri.Interpreter.StepError → FaultKind
  | .undefinedBehavior _ => .undefined
  | .stack (.localExpectedLive _) => .undefined
  | _ => .unsupported

/-- Validated `ExecutionMachine.Config` for `rp : RefProg`. -/
noncomputable abbrev refExecCfg (rp : RefProg) :=
  Miri.Interpreter.ExecutionMachine.withValidation
    (refExecutionConfig rp) refLimits

theorem refExecCfg_idempotent (rp : RefProg) :
    Miri.Interpreter.ExecutionMachine.withValidation
      (refExecCfg rp) refLimits = refExecCfg rp := rfl

/-- Immediate encoding of an `Option Val` at type `ty`. -/
noncomputable def optValToMiriImm (ty : MirTy) :
    Option Val → Miri.Interpreter.Immediate Miri.Memory.Provenance
  | none => .uninit
  | some v => valToMiriImmediate ty v

theorem slotToMiriLocalValue_live (ty : MirTy) (optVal : Option Val) :
    slotToMiriLocalValue ty (.immediate optVal) =
      .live (.immediate (optValToMiriImm ty optVal)) := by
  cases optVal <;> rfl

theorem slotToMiriLocalValue_liveUninit (ty : MirTy) :
    slotToMiriLocalValue ty (liveUninitSlot ty) = .live (.immediate .uninit) := by
  cases ty with
  | unit => rfl
  | bool | int _ _ | never | char | ordering | tuple _ | ref _ _ | rawPtr _ _
  | unsupported => rfl
  | enum ety =>
    dsimp only [liveUninitSlot]
    cases h_zst : isZstEnumTy ety with
    | false => rfl
    | true =>
      dsimp only [isZstEnumTy] at h_zst
      cases h_tr : ety.tagRepr with
      | scalar _ _ => rw [h_tr] at h_zst; cases h_zst
      | zeroSized =>
        dsimp only [slotToMiriLocalValue, valToMiriImmediate]
        change LocalValue.live (Operand.immediate
          (match ety.tagRepr with
          | .zeroSized => Immediate.uninit
          | .scalar tagW _ =>
            match MirSemantics.getElem? ety.discriminants 0 with
            | some disc =>
              Immediate.scalar
                (Scalar.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))
            | none => Immediate.uninit)) = _
        rw [h_tr]

theorem refLayoutDataForTy_isUnsized (ty : MirTy) :
    (refLayoutDataForTy ty).backendRepr.isUnsized = false := by
  cases ty with
  | int w s => cases w <;> cases s <;> rfl
  | bool | unit | never | char | ordering | ref _ _ | rawPtr _ _
  | unsupported => rfl
  | enum ety =>
    dsimp only [refLayoutDataForTy, refEnumLayoutData]
    cases ety.tagRepr <;> rfl
  | tuple fs =>
    cases fs with
    | nil => rfl
    | cons f rest =>
      cases rest with
      | nil => cases f <;> rfl
      | cons g rest₂ =>
        cases rest₂ with
        | nil => cases f <;> cases g <;> rfl
        | cons _ _ => cases f <;> cases g <;> rfl

theorem refLayoutDataForTy_isZst_move_deinit (ty : MirTy)
    (optVal : Option Val) (h_sm : SlotMatchesTy ty (.immediate optVal)) :
    (if (refLayoutDataForTy ty).isZst then
        Miri.Interpreter.Operand.immediate (optValToMiriImm ty optVal)
      else Miri.Interpreter.Operand.immediate .uninit) =
      Miri.Interpreter.Operand.immediate .uninit := by
  cases h_z : (refLayoutDataForTy ty).isZst with
  | false => rfl
  | true =>
    cases optVal with
    | none => rfl
    | some v =>
      have h_cv : checkVal v ty = true := h_sm
      cases checkVal_eq_true_inv h_cv with
      | inl hi =>
        let ⟨w, s, _, hty, _, _⟩ := hi
        subst hty
        have h_nz : (refLayoutDataForTy (.int w s)).isZst = false := by
          cases w <;> cases s <;> rfl
        rw [h_nz] at h_z; cases h_z
      | inr h1 =>
        cases h1 with
        | inl hb =>
          let ⟨_, hty, _⟩ := hb
          subst hty
          have h_nz : (refLayoutDataForTy .bool).isZst = false := rfl
          rw [h_nz] at h_z; cases h_z
        | inr h2 =>
          cases h2 with
          | inl hu =>
            let ⟨hty, hv⟩ := hu
            subst hty; subst hv; rfl
          | inr h3 =>
            cases h3 with
            | inl he =>
              let ⟨ety, k, hty, hv, _, _⟩ := he
              subst hty; subst hv
              cases h_tr : ety.tagRepr with
              | zeroSized =>
                have h_imm : optValToMiriImm (.enum ety)
                    (some (.enumVal ety k)) = .uninit := by
                  dsimp only [optValToMiriImm, valToMiriImmediate]
                  rw [h_tr]
                rw [h_imm]; rfl
              | scalar tagW tagS =>
                have h_ld : refLayoutDataForTy (.enum ety) =
                    { refBaseLayoutData
                        (.Scalar (.Union (value := .Int (toMiriInteger tagW) tagS)))
                        (toMiriSize tagW) with
                      fields := .Arbitrary (Array.mk [Size.ZERO]) (Array.mk [0])
                      variants :=
                        .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS))
                          .Direct 0
                          (Array.mk (ety.discriminants.map
                            (fun _ => refInhabitedVariantLayout))) } := by
                  dsimp only [refLayoutDataForTy, refEnumLayoutData]
                  rw [h_tr]
                have h_nz : (refLayoutDataForTy (.enum ety)).isZst = false := by
                  rw [h_ld]; cases tagW <;> rfl
                rw [h_nz] at h_z; cases h_z
            | inr h4 =>
              cases h4 with
              | inl hc =>
                let ⟨_, hty, _⟩ := hc
                subst hty
                have h_nz : (refLayoutDataForTy .char).isZst = false := rfl
                rw [h_nz] at h_z; cases h_z
              | inr h5 =>
                cases h5 with
                | inl ho =>
                  let ⟨_, hty, _⟩ := ho
                  subst hty
                  have h_nz : (refLayoutDataForTy .ordering).isZst = false := rfl
                  rw [h_nz] at h_z; cases h_z
                | inr hp =>
                  let ⟨w, s, _, _, hty, _, _⟩ := hp
                  subst hty
                  have h_nz :
                      (refLayoutDataForTy (.tuple [.int w s, .bool])).isZst =
                        false := by
                    cases w <;> cases s <;> rfl
                  rw [h_nz] at h_z; cases h_z

/-- Shorthand for a single-frame `Miri.Interpreter.Frame` backed by
`liftLocals rp.types bodyLocals slots`. -/
noncomputable abbrev mkSimFrame (rp : RefProg) (defId : DefId) (rbody : RefBody)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (bodyLocals : List MirTy)
    (slots : List LocalSlot) (retPlace : MPlaceTy Miri.Memory.Provenance) :=
  mkRefMiriFrame rp.types defId rbody blockIdx stmtIdx
    (liftLocals rp.types bodyLocals slots) retPlace

/-- Shorthand for a single-frame `Miri.Interpreter.MachineHooks.State` backed by
`mkSimFrame`. -/
noncomputable abbrev mkSimState (rp : RefProg) (defId : DefId) (rbody : RefBody)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (bodyLocals : List MirTy)
    (slots : List LocalSlot) (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :=
  mkRefMiriState
    (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace)
    mem ctrl cm

private theorem eStateM_bind_ok {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {s s₁ : σ} {a : α}
    (h : m s = .ok a s₁) :
    EStateM.bind m f s = f a s₁ := by
  dsimp only [EStateM.bind]; rw [h]

private theorem eStateM_bind_err {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {s s₁ : σ} {e : ε}
    (h : m s = .error e s₁) :
    EStateM.bind m f s = .error e s₁ := by
  dsimp only [EStateM.bind]; rw [h]

private theorem eStateM_bind_pure {ε σ α β : Type} (a : α)
    (f : α → EStateM ε σ β) (s : σ) :
    EStateM.bind (EStateM.pure a) f s = f a s := rfl

private theorem eStateM_bind_assoc {ε σ α β γ : Type} (m : EStateM ε σ α)
    (f : α → EStateM ε σ β) (g : β → EStateM ε σ γ) (s : σ) :
    EStateM.bind (EStateM.bind m f) g s =
      EStateM.bind m (fun a => EStateM.bind (f a) g) s := by
  dsimp only [EStateM.bind]
  cases m s <;> rfl

private theorem eStateM_bind_ite_pure {ε σ α : Type} (b : Bool) (e : ε)
    (k : Unit → EStateM ε σ α) (s : σ) :
    EStateM.bind (if b = true then EStateM.pure () else EStateM.throw e) k s =
      if b = true then k () s else .error e s := by
  cases b <;> rfl

private theorem ite_false_eq {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

private theorem ite_true_eq {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

private theorem ite_not_true_eq {α : Type} (a b : α) :
    (if (!true) = true then a else b) = b := rfl

private theorem ite_not_false_eq {α : Type} (a b : α) :
    (if (!false) = true then a else b) = a := rfl

private theorem array_forIn_empty {ε σ α β : Type}
    (init : β) (f : α → β → EStateM ε σ (ForInStep β)) (st : σ) :
    forIn (Array.empty : Array α) init f st = .ok init st := rfl

private theorem array_forIn_singleton {ε σ α β : Type}
    (x : α) (init : β) (f : α → β → EStateM ε σ (ForInStep β)) (st : σ) :
    forIn (Array.mk [x]) init f st =
      (match f x init st with
      | .ok (.done b) s => .ok b s
      | .ok (.yield b) s => .ok b s
      | .error e s => .error e s) := by
  have h : forIn (Array.mk [x]) init f = forIn ([x] : List α) init f :=
    (Array.forIn_toList (xs := Array.mk [x]) (b := init) (f := f)).symm
  rw [h]
  dsimp only [forIn, forIn', List.forIn', List.forIn'.loop,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases f x init st with
  | ok r s => cases r <;> rfl
  | error e s => rfl

private theorem mirSetElem?_some_of_lt {α : Type} (xs : List α) (i : Nat) (v : α)
    (hi : i < xs.length) :
    ∃ xs', MirSemantics.setElem? xs i v = some xs' := by
  induction xs generalizing i with
  | nil => cases hi
  | cons x rest ih =>
    cases i with
    | zero => exact ⟨v :: rest, rfl⟩
    | succ j =>
      let ⟨rest', h_r⟩ := ih j (Nat.lt_of_succ_lt_succ hi)
      exact ⟨x :: rest', by dsimp only [MirSemantics.setElem?]; rw [h_r]⟩

theorem mkSimFrame_getLocal_some (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance) (id : LocalId)
    (ty : MirTy) (slot : LocalSlot)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot) :
    (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace).getLocal id =
      .ok (refLocalStateOfSlot rp.types ty slot) := by
  have h_lift := getElem?_liftLocals_some rp.types h_ty h_sl
  have h_sz : id < (Array.mk (liftLocals rp.types bodyLocals slots)).size :=
    mirGetElem?_lt_of_some h_lift
  dsimp only [Miri.Interpreter.Frame.getLocal, mkSimFrame, mkRefMiriFrame]
  rw [dite_eq_left h_sz]
  have h_idx : GetElem.getElem (Array.mk (liftLocals rp.types bodyLocals slots)) id h_sz =
      refLocalStateOfSlot rp.types ty slot := by
    have h_opt : (Array.mk (liftLocals rp.types bodyLocals slots))[id]? =
        some (refLocalStateOfSlot rp.types ty slot) := by
      rw [array_getElem?_eq_mirGetElem?]; exact h_lift
    rw [Array.getElem?_eq_getElem h_sz] at h_opt
    injection h_opt
  rw [h_idx]
  rfl

theorem mkSimFrame_getLocal_none_left (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance) (id : LocalId)
    (h_ty : MirSemantics.getElem? bodyLocals id = none) :
    (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace).getLocal id =
      .error (.invalidLocal id (liftLocals rp.types bodyLocals slots).length) := by
  have h_none := getElem?_liftLocals_none_left rp.types (slots := slots) h_ty
  have h_not : ¬ (id < (Array.mk (liftLocals rp.types bodyLocals slots)).size) :=
    Nat.not_lt.mpr (mirGetElem?_ge_of_none h_none)
  dsimp only [Miri.Interpreter.Frame.getLocal, mkSimFrame, mkRefMiriFrame]
  rw [dite_eq_right h_not]
  rfl

theorem mkSimFrame_getLocal_none_right (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance) (id : LocalId)
    (h_sl : MirSemantics.getElem? slots id = none) :
    (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace).getLocal id =
      .error (.invalidLocal id (liftLocals rp.types bodyLocals slots).length) := by
  have h_none := getElem?_liftLocals_none_right rp.types (bodyLocals := bodyLocals) h_sl
  have h_not : ¬ (id < (Array.mk (liftLocals rp.types bodyLocals slots)).size) :=
    Nat.not_lt.mpr (mirGetElem?_ge_of_none h_none)
  dsimp only [Miri.Interpreter.Frame.getLocal, mkSimFrame, mkRefMiriFrame]
  rw [dite_eq_right h_not]
  rfl

theorem mkSimFrame_getLocalOperand_dead (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance) (id : LocalId)
    (ty : MirTy)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead) :
    (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace).getLocalOperand id =
      .error (.localExpectedLive id) := by
  dsimp only [Miri.Interpreter.Frame.getLocalOperand, bind, Bind.bind, Except.bind]
  rw [mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx bodyLocals slots
    retPlace id ty .dead h_ty h_sl]
  rfl

theorem mkSimFrame_getLocalOperand_live (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance) (id : LocalId)
    (ty : MirTy) (optVal : Option Val)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal)) :
    (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace).getLocalOperand id =
      .ok (.immediate (optValToMiriImm ty optVal)) := by
  dsimp only [Miri.Interpreter.Frame.getLocalOperand, bind, Bind.bind, Except.bind]
  rw [mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx bodyLocals slots
    retPlace id ty (.immediate optVal) h_ty h_sl]
  dsimp only [refLocalStateOfSlot]
  rw [slotToMiriLocalValue_live]
  rfl

theorem mkSimFrame_replaceLocalValue_some (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots slots' : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance) (id : LocalId)
    (ty : MirTy) (slot slot' : LocalSlot)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot)
    (h_set : MirSemantics.setElem? slots id slot' = some slots') :
    (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace).replaceLocalValue
        id (slotToMiriLocalValue ty slot') =
      .ok (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots' retPlace) := by
  have h_lift_get :
      MirSemantics.getElem? (liftLocals rp.types bodyLocals slots) id =
        some (refLocalStateOfSlot rp.types ty slot) :=
    getElem?_liftLocals_some rp.types h_ty h_sl
  have h_lt : id < (liftLocals rp.types bodyLocals slots).length :=
    mirGetElem?_lt_of_some h_lift_get
  have h_lift_set :
      MirSemantics.setElem? (liftLocals rp.types bodyLocals slots) id
        (refLocalStateOfSlot rp.types ty slot') =
        some (liftLocals rp.types bodyLocals slots') :=
    setElem?_liftLocals_some rp.types h_ty h_set
  have h_arr_set := array_set_eq_mirSetElem? h_lt h_lift_set
  dsimp only [Miri.Interpreter.Frame.replaceLocalValue, mkSimFrame, mkRefMiriFrame]
  have h_sz : id < (Array.mk (liftLocals rp.types bodyLocals slots)).size := h_lt
  rw [dite_eq_left h_sz]
  have h_idx : GetElem.getElem (Array.mk (liftLocals rp.types bodyLocals slots)) id h_sz =
      refLocalStateOfSlot rp.types ty slot := by
    have h_opt : (Array.mk (liftLocals rp.types bodyLocals slots))[id]? =
        some (refLocalStateOfSlot rp.types ty slot) := by
      rw [array_getElem?_eq_mirGetElem?]; exact h_lift_get
    rw [Array.getElem?_eq_getElem h_sz] at h_opt
    injection h_opt
  rw [h_idx]
  dsimp only [refLocalStateOfSlot]
  change Except.ok ({
    body := toMiriBody rp.types rbody,
    bodyIdentity := BodyIdentity.ofCanonicalIndex defId,
    functionInstance := { kind := .Item defId, args := Array.empty },
    extra := { borrowTracker := none, catchUnwind := none, userRelevance := 255, dataRace := none },
    returnContinuation := ReturnContinuation.stop false,
    returnPlace := RuntimeStackPlace.memory retPlace,
    localsIdentity := LocalsIdentity.ofAllocationToken 0,
    locals := (Array.mk (liftLocals rp.types bodyLocals slots)).set id
      (refLocalStateOfSlot rp.types ty slot') h_sz,
    vaList := Array.empty,
    trackCallerArg := none,
    location := FrameLocation.mir { block := blockIdx, statementIndex := stmtIdx }
  } : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra) = _
  rw [h_arr_set]

theorem mkSimFrame_setLocalOperand_some (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots slots' : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance) (id : LocalId)
    (ty : MirTy) (optVal : Option Val) (optVal' : Option Val)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal))
    (h_set : MirSemantics.setElem? slots id (.immediate optVal') = some slots') :
    (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace).setLocalOperand
        id (.immediate (optValToMiriImm ty optVal')) =
      .ok (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots' retPlace) := by
  dsimp only [Miri.Interpreter.Frame.setLocalOperand, bind, Bind.bind, Except.bind]
  rw [mkSimFrame_getLocalOperand_live rp defId rbody blockIdx stmtIdx bodyLocals slots
    retPlace id ty optVal h_ty h_sl]
  have h_rep := mkSimFrame_replaceLocalValue_some rp defId rbody blockIdx stmtIdx
    bodyLocals slots slots' retPlace id ty (.immediate optVal) (.immediate optVal')
    h_ty h_sl h_set
  rw [slotToMiriLocalValue_live] at h_rep
  exact h_rep

/-! ## Section 2: `OperandMachine` (`localToOp`, `evalPlaceToOp`) -/

private theorem currentFrame_mkSimState (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :
    Miri.Interpreter.MachineHooks.currentFrame
        (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace
          mem ctrl cm) =
      .ok (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace)
        (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace
          mem ctrl cm) := rfl

theorem operandMachine_localToOp_ok (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (known : Option LocalLayout)
    (ty : MirTy) (optVal : Option Val)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal)) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.OperandMachine.localToOp
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
        c id known st =
      .ok ⟨.immediate (optValToMiriImm ty optVal),
        refLocalLayoutForTy rp.types ty⟩ st := by
  intro st
  have h_cf := currentFrame_mkSimState rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_gl := mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty (.immediate optVal) h_ty h_sl
  have h_go := mkSimFrame_getLocalOperand_live rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty optVal h_ty h_sl
  dsimp only [Miri.Interpreter.OperandMachine.localToOp, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_cf, h_gl]
  dsimp only [refLocalStateOfSlot]
  change (EStateM.bind (EStateM.pure _) _ st) = _
  rw [eStateM_bind_pure]
  dsimp only
  rw [eStateM_bind_pure, eStateM_bind_ok h_cf, h_go]
  change (EStateM.bind (EStateM.pure _) _ st) = _
  rw [eStateM_bind_pure]
  have h_un : (refLocalLayoutForTy rp.types ty).layout.backendRepr.isUnsized = false :=
    refLayoutDataForTy_isUnsized ty
  simp only [h_un, Bool.false_eq_true, ite_false]
  rfl

theorem operandMachine_localToOp_dead (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (known : Option LocalLayout)
    (ty : MirTy)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.OperandMachine.localToOp
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
        c id known st =
      .error (.stack (.localExpectedLive id)) st := by
  intro st
  have h_cf := currentFrame_mkSimState rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_gl := mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty .dead h_ty h_sl
  have h_go := mkSimFrame_getLocalOperand_dead rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty h_ty h_sl
  dsimp only [Miri.Interpreter.OperandMachine.localToOp, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_cf, h_gl]
  dsimp only [refLocalStateOfSlot]
  change (EStateM.bind (EStateM.pure _) _ st) = _
  rw [eStateM_bind_pure]
  dsimp only
  rw [eStateM_bind_pure, eStateM_bind_ok h_cf, h_go]
  rfl

theorem operandMachine_localToOp_none (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (known : Option LocalLayout)
    (h_oob : MirSemantics.getElem? bodyLocals id = none ∨
      MirSemantics.getElem? slots id = none) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.OperandMachine.localToOp
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
        c id known st =
      .error (.stack (.invalidLocal id (liftLocals rp.types bodyLocals slots).length)) st := by
  intro st
  have h_cf := currentFrame_mkSimState rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_gl :
      (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace).getLocal id =
        .error (.invalidLocal id (liftLocals rp.types bodyLocals slots).length) := by
    cases h_oob with
    | inl h =>
      exact mkSimFrame_getLocal_none_left rp defId rbody blockIdx
        stmtIdx bodyLocals slots retPlace id h
    | inr h =>
      exact mkSimFrame_getLocal_none_right rp defId rbody blockIdx
        stmtIdx bodyLocals slots retPlace id h
  dsimp only [Miri.Interpreter.OperandMachine.localToOp, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_cf, h_gl]
  rfl

theorem operandMachine_evalPlaceToOp_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (rpl : RefPlace) (pl : Place)
    (known : Option LocalLayout)
    (h_pl : decodePlace rp.types rpl = some pl)
    (h_inv : SlotsMatchTys bodyLocals slots) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    let res := Miri.Interpreter.OperandMachine.evalPlaceToOp
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
      c (toMiriPlace rpl) known st
    match MirSemantics.getElem? bodyLocals pl.localId,
        MirSemantics.getElem? slots pl.localId with
    | some _, some .dead =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = .undefined
    | some ty, some (.immediate optVal) =>
      if !pl.projection.isEmpty then
        ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = .unsupported
      else
        res = .ok ⟨.immediate (optValToMiriImm ty optVal),
          refLocalLayoutForTy rp.types ty⟩ st
    | _, _ =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = .unsupported := by
  intro st res
  let ⟨h_id, h_emp⟩ := decodePlace_inv h_pl
  have h_deinit : (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).deinitMovedPlace = true := rfl
  have h_unfold :
      res =
        EStateM.bind
          (Miri.Interpreter.OperandMachine.localToOp
            (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
            c rpl.localId (if (toMiriPlace rpl).projection.isEmpty then known else none))
          (fun op =>
            EStateM.bind
              (forIn (toMiriPlace rpl).projection op
                (fun elem op =>
                  EStateM.bind
                    (Miri.Interpreter.OperandMachine.project
                      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
                      c op elem)
                    (fun op' => EStateM.pure (ForInStep.yield op'))))
              (fun op =>
                EStateM.bind
                  ((Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).checkPlaceType
                    c (toMiriPlace rpl) op)
                  (fun _ => EStateM.pure op)))
          st := by
    dsimp only [res, Miri.Interpreter.OperandMachine.evalPlaceToOp]
    rw [h_deinit]
    rfl
  rw [h_unfold, h_id]
  cases h_ty : MirSemantics.getElem? bodyLocals pl.localId with
  | none =>
    rw [eStateM_bind_err (operandMachine_localToOp_none rp c defId rbody
      blockIdx stmtIdx bodyLocals slots retPlace mem ctrl cm pl.localId _
      (Or.inl h_ty))]
    exact ⟨_, _, rfl, rfl⟩
  | some ty =>
    cases h_sl : MirSemantics.getElem? slots pl.localId with
    | none =>
      rw [eStateM_bind_err (operandMachine_localToOp_none rp c defId rbody
        blockIdx stmtIdx bodyLocals slots retPlace mem ctrl cm pl.localId _
        (Or.inr h_sl))]
      exact ⟨_, _, rfl, rfl⟩
    | some slot =>
      cases slot with
      | dead =>
        rw [eStateM_bind_err (operandMachine_localToOp_dead rp c defId rbody
          blockIdx stmtIdx bodyLocals slots retPlace mem ctrl cm pl.localId _
          ty h_ty h_sl)]
        exact ⟨_, _, rfl, rfl⟩
      | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
      | immediate optVal =>
        rw [eStateM_bind_ok (operandMachine_localToOp_ok rp c defId rbody
          blockIdx stmtIdx bodyLocals slots retPlace mem ctrl cm pl.localId _
          ty optVal h_ty h_sl)]
        dsimp only
        cases h_pe : pl.projection.isEmpty with
        | true =>
          have h_rpe : rpl.projection.isEmpty = true := h_emp.trans h_pe
          have h_proj_empty : (toMiriPlace rpl).projection = Array.empty := by
            dsimp only [toMiriPlace]; rw [h_rpe]; rfl
          rw [h_proj_empty, ite_not_true_eq]
          dsimp only [EStateM.bind]
          rw [array_forIn_empty]
          rfl
        | false =>
          have h_rpe : rpl.projection.isEmpty = false := h_emp.trans h_pe
          have h_proj_deref : (toMiriPlace rpl).projection = Array.mk [.Deref] := by
            dsimp only [toMiriPlace]; rw [h_rpe]; rfl
          rw [h_proj_deref, ite_not_false_eq]
          dsimp only [EStateM.bind]
          rw [array_forIn_singleton]
          exact ⟨_, _, rfl, rfl⟩

theorem operandMachine_evalOperandAt_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (amem : MemoryState)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (path : Miri.Interpreter.OperandPath)
    (rop : RefOperand) (op : Operand) (tyOk : MirTy → Bool)
    (known : Option LocalLayout)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_op : decodeOperand rp.types rop = some op) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    let res := Miri.Interpreter.OperandMachine.evalOperandAt
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
      c path (toMiriOperand rp.types rop) known st
    match evalOperandToSlot bodyLocals slots amem tyOk op with
    | .error k =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
    | .ok (ty, optVal, slots', _) =>
      res = .ok ⟨.immediate (optValToMiriImm ty optVal),
          refLocalLayoutForTy rp.types ty⟩
        (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots'
          retPlace mem ctrl cm) := by
  intro st res
  cases rop with
  | copy rpl =>
    dsimp only [decodeOperand, optMap] at h_op
    cases h_pl : decodePlace rp.types rpl with
    | none => rw [h_pl] at h_op; cases h_op
    | some pl =>
      rw [h_pl] at h_op; injection h_op with h_eq; subst h_eq
      have h_ev := operandMachine_evalPlaceToOp_eq rp c defId rbody blockIdx
        stmtIdx bodyLocals slots retPlace mem ctrl cm rpl pl known h_pl h_inv
      change (match evalOperandToSlot bodyLocals slots amem tyOk (.copy pl) with
        | .error k => ∃ err st', Miri.Interpreter.OperandMachine.evalPlaceToOp
            (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
            c (toMiriPlace rpl) known st = .error err st' ∧ stepErrorFaultKind err = k
        | .ok (ty, optVal, slots', _) =>
          Miri.Interpreter.OperandMachine.evalPlaceToOp
            (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
            c (toMiriPlace rpl) known st =
            .ok ⟨.immediate (optValToMiriImm ty optVal), refLocalLayoutForTy rp.types ty⟩
              (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots'
                retPlace mem ctrl cm))
      dsimp only [evalOperandToSlot]
      cases h_ty : MirSemantics.getElem? bodyLocals pl.localId with
      | none => rw [h_ty] at h_ev; exact h_ev
      | some ty =>
        cases h_sl : MirSemantics.getElem? slots pl.localId with
        | none => rw [h_ty, h_sl] at h_ev; exact h_ev
        | some slot =>
          rw [h_ty, h_sl] at h_ev
          cases slot with
          | dead => exact h_ev
          | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
          | immediate optVal =>
            cases h_pe : pl.projection.isEmpty with
            | false => rw [h_pe] at h_ev; exact h_ev
            | true => rw [h_pe] at h_ev; exact h_ev
  | move rpl =>
    dsimp only [decodeOperand, optMap] at h_op
    cases h_pl : decodePlace rp.types rpl with
    | none => rw [h_pl] at h_op; cases h_op
    | some pl =>
      rw [h_pl] at h_op; injection h_op with h_eq; subst h_eq
      let ⟨h_id, h_emp⟩ := decodePlace_inv h_pl
      have h_ev := operandMachine_evalPlaceToOp_eq rp c defId rbody blockIdx
        stmtIdx bodyLocals slots retPlace mem ctrl cm rpl pl known h_pl h_inv
      have h_deinit : (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).deinitMovedPlace = true := rfl
      dsimp only [evalOperandToSlot]
      cases h_ty : MirSemantics.getElem? bodyLocals pl.localId with
      | none =>
        rw [h_ty] at h_ev
        let ⟨err, st', h_err, h_fk⟩ := h_ev
        refine ⟨err, st', ?_, h_fk⟩
        dsimp only [res, Miri.Interpreter.OperandMachine.evalOperandAt,
          Miri.Interpreter.OperandMachine.evalOperand, toMiriOperand]
        rw [h_deinit]
        dsimp only [Bool.not, ite_false_eq, bind, Bind.bind, EStateM.bind]
        rw [h_err]
      | some ty =>
        cases h_sl : MirSemantics.getElem? slots pl.localId with
        | none =>
          rw [h_ty, h_sl] at h_ev
          let ⟨err, st', h_err, h_fk⟩ := h_ev
          refine ⟨err, st', ?_, h_fk⟩
          dsimp only [res, Miri.Interpreter.OperandMachine.evalOperandAt,
            Miri.Interpreter.OperandMachine.evalOperand, toMiriOperand]
          rw [h_deinit]
          dsimp only [Bool.not, ite_false_eq, bind, Bind.bind, EStateM.bind]
          rw [h_err]
        | some slot =>
          rw [h_ty, h_sl] at h_ev
          cases slot with
          | dead =>
            let ⟨err, st', h_err, h_fk⟩ := h_ev
            refine ⟨err, st', ?_, h_fk⟩
            dsimp only [res, Miri.Interpreter.OperandMachine.evalOperandAt,
              Miri.Interpreter.OperandMachine.evalOperand, toMiriOperand]
            rw [h_deinit]
            dsimp only [Bool.not, ite_false_eq, bind, Bind.bind, EStateM.bind]
            rw [h_err]
          | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
          | immediate optVal =>
            cases h_pe : pl.projection.isEmpty with
            | false =>
              rw [h_pe] at h_ev
              let ⟨err, st', h_err, h_fk⟩ := h_ev
              refine ⟨err, st', ?_, h_fk⟩
              dsimp only [res, Miri.Interpreter.OperandMachine.evalOperandAt,
                Miri.Interpreter.OperandMachine.evalOperand, toMiriOperand]
              rw [h_deinit]
              dsimp only [Bool.not, ite_false_eq, bind, Bind.bind, EStateM.bind]
              rw [h_err]
            | true =>
              rw [h_pe] at h_ev
              have h_rpe : rpl.projection.isEmpty = true := h_emp.trans h_pe
              have h_proj_empty : (toMiriPlace rpl).projection.isEmpty = true := by
                dsimp only [toMiriPlace]; rw [h_rpe]; rfl
              have h_sm := SlotsMatchTys.getElem? h_inv h_ty h_sl
              have h_deinit_eq :
                  (if (refLocalLayoutForTy rp.types ty).layout.isZst then
                      Miri.Interpreter.Operand.immediate (optValToMiriImm ty optVal)
                    else Miri.Interpreter.Operand.immediate .uninit) =
                    Miri.Interpreter.Operand.immediate .uninit :=
                refLayoutDataForTy_isZst_move_deinit ty optVal h_sm
              let ⟨slots', h_set⟩ := mirSetElem?_some_of_lt slots pl.localId
                (liveUninitSlot ty) (mirGetElem?_lt_of_some h_sl)
              dsimp only
              rw [ite_not_true_eq, h_set]
              have h_rep := mkSimFrame_replaceLocalValue_some rp defId rbody
                blockIdx stmtIdx bodyLocals slots slots' retPlace pl.localId ty
                (.immediate optVal) (liveUninitSlot ty) h_ty h_sl h_set
              rw [slotToMiriLocalValue_liveUninit ty] at h_rep
              have h_cf := currentFrame_mkSimState rp defId rbody blockIdx stmtIdx
                bodyLocals slots retPlace mem ctrl cm
              dsimp only [res, Miri.Interpreter.OperandMachine.evalOperandAt,
                Miri.Interpreter.OperandMachine.evalOperand, toMiriOperand]
              rw [h_deinit]
              dsimp only [Bool.not, ite_false_eq, bind, Bind.bind, pure, Pure.pure]
              rw [eStateM_bind_ok h_ev]
              simp only [h_proj_empty, ite_true]
              dsimp only [toMiriPlace]
              rw [h_id, h_deinit_eq, eStateM_bind_ok h_cf, h_rep]
              rfl
  | constant rc =>
    dsimp only [decodeOperand, optMap] at h_op
    cases h_ty : MirSemantics.getElem? rp.types rc.ty with
    | none => rw [h_ty] at h_op; cases h_op
    | some ty =>
      rw [h_ty] at h_op; injection h_op with h_eq; subst h_eq
      have h_can := canonicalTyId_of_some h_ty
      have h_get_can : MirSemantics.getElem? rp.types (tyIdFor rp.types ty) = some ty := by
        let ⟨idx, h_idx⟩ := indexOfTy_some_of_mirGetElem? h_ty
        dsimp only [tyIdFor]
        rw [h_idx]
        exact (indexOfTy_some_getElem? h_idx).1
      cases rc with
      | mk tyId lit =>
        dsimp only at h_ty h_can
        cases lit with
        | scalar bits =>
          have h_step :
              res =
                refEvalConstOperand rp.types
                  ⟨⟨0⟩, none, .Val (.Scalar (.Int bits.toNat 16))
                    (canonicalTyId rp.types tyId)⟩ st := rfl
          dsimp only [evalOperandToSlot]
          rw [h_step]
          dsimp only [refEvalConstOperand]
          rw [h_can.1, h_get_can, bitVec128_ofNat_toNat bits]
          dsimp only
          rw [evalRefConstLit_eq]
          cases evalConstLit ty (.scalar bits) with
          | error k => cases k <;> exact ⟨_, _, rfl, rfl⟩
          | ok v => rfl
        | zeroSized =>
          have h_step :
              res =
                refEvalConstOperand rp.types
                  ⟨⟨0⟩, none, .Val .ZeroSized (canonicalTyId rp.types tyId)⟩ st := rfl
          dsimp only [evalOperandToSlot]
          rw [h_step]
          dsimp only [refEvalConstOperand]
          rw [h_can.1, h_get_can]
          dsimp only
          rw [evalRefConstLit_eq]
          cases evalConstLit ty .zeroSized with
          | error k => cases k <;> exact ⟨_, _, rfl, rfl⟩
          | ok v => rfl

/-! ## Section 3: Primitive Read (`PlaceMachine.readImmediate`) -/

private theorem readImmediate_imm_int_ok (w : IntWidth) (s : Bool)
    (bits : BitVec 128) (types : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar w bits))),
          refLocalLayoutForTy types (.int w s)⟩ st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar w bits)),
        refLocalLayoutForTy types (.int w s)⟩ st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd
      cases w <;> cases s <;> rfl

private theorem readImmediate_imm_int_uninit (w : IntWidth) (s : Bool)
    (types : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    ∃ msg,
      Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
          ⟨.immediate .uninit, refLocalLayoutForTy types (.int w s)⟩ st =
        .error (.undefinedBehavior msg) st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd
      cases w <;> cases s <;> exact ⟨_, rfl⟩

private theorem readImmediate_imm_bool_ok (b : Bool) (types : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
        ⟨.immediate (.scalar (.fromBool b)),
          refLocalLayoutForTy types .bool⟩ st =
      .ok ⟨.scalar (.fromBool b), refLocalLayoutForTy types .bool⟩ st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd
      rfl

private theorem readImmediate_imm_bool_uninit (types : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    ∃ msg,
      Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
          ⟨.immediate .uninit, refLocalLayoutForTy types .bool⟩ st =
        .error (.undefinedBehavior msg) st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd
      exact ⟨_, rfl⟩

private theorem readImmediate_imm_char_ok (ch : Char) (types : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
        ⟨.immediate (.scalar (.fromChar ch)),
          refLocalLayoutForTy types .char⟩ st =
      .ok ⟨.scalar (.fromChar ch), refLocalLayoutForTy types .char⟩ st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd
      rfl

private theorem readImmediate_imm_char_uninit (types : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    ∃ msg,
      Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
          ⟨.immediate .uninit, refLocalLayoutForTy types .char⟩ st =
        .error (.undefinedBehavior msg) st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd
      exact ⟨_, rfl⟩

private theorem readImmediate_imm_pair_ok (w : IntWidth) (s : Bool)
    (bits : BitVec 128) (b : Bool) (types : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
        ⟨.immediate (.scalarPair (.fromScalarInt (miriScalar w bits))
            (.fromBool b)),
          refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st =
      .ok ⟨.scalarPair (.fromScalarInt (miriScalar w bits)) (.fromBool b),
        refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd
      cases w <;> cases s <;> rfl

private theorem readImmediate_imm_pair_uninit (w : IntWidth) (s : Bool)
    (types : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    ∃ msg,
      Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
          ⟨.immediate .uninit,
            refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st =
        .error (.undefinedBehavior msg) st := by
  cases st with
  | mk stack machine =>
    cases machine with
    | mk memory borrowTracker dataRace threads raceAllocations allocationSpans
        user pendingMoveDeinit =>
      dsimp only at h_pmd; subst h_pmd
      cases w <;> cases s <;> exact ⟨_, rfl⟩

/-- The primitive-readable local types are `bool`, integers, `char`, and
overflow pairs. -/
theorem isPrimitiveReadableTy_cases {ty : MirTy}
    (h : isPrimitiveReadableTy ty = true) :
    ty = .bool ∨ (∃ w s, ty = .int w s) ∨ ty = .char ∨
      (∃ w s, ty = .tuple [.int w s, .bool]) := by
  cases ty with
  | bool => exact Or.inl rfl
  | int w s => exact Or.inr (Or.inl ⟨w, s, rfl⟩)
  | char => exact Or.inr (Or.inr (Or.inl rfl))
  | unit | never | ordering | enum _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases h
  | tuple fs =>
    cases fs with
    | nil => cases h
    | cons f rest =>
      cases rest with
      | nil => cases f <;> cases h
      | cons g rest₂ =>
        cases rest₂ with
        | cons _ _ => cases f <;> cases g <;> cases h
        | nil =>
          cases f with
          | int w s =>
            cases g with
            | bool => exact Or.inr (Or.inr (Or.inr ⟨w, s, rfl⟩))
            | _ => cases h
          | _ => cases h

private theorem readImmediate_imm_nonprim_err (ty : MirTy)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (types : List MirTy)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_np : isPrimitiveReadableTy ty = false) :
    ∃ err st',
      Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
          ⟨.immediate imm, refLocalLayoutForTy types ty⟩ st =
        .error err st' ∧
      stepErrorFaultKind err = .unsupported := by
  cases ty with
  | bool | int _ _ | char => cases h_np
  | unit | never | ordering | ref _ _ | rawPtr _ _ | unsupported =>
    exact ⟨_, _, rfl, rfl⟩
  | tuple fs =>
    cases fs with
    | nil => exact ⟨_, _, rfl, rfl⟩
    | cons f rest =>
      cases rest with
      | nil => cases f <;> exact ⟨_, _, rfl, rfl⟩
      | cons g rest₂ =>
        cases rest₂ with
        | cons _ _ => cases f <;> cases g <;> exact ⟨_, _, rfl, rfl⟩
        | nil =>
          cases f with
          | int w s =>
            cases g with
            | bool => cases h_np
            | _ => exact ⟨_, _, rfl, rfl⟩
          | _ => exact ⟨_, _, rfl, rfl⟩
  | enum ety =>
    cases h_tr : ety.tagRepr with
    | zeroSized =>
      have h_eq :
          Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
              ⟨.immediate imm, refLocalLayoutForTy types (.enum ety)⟩ st =
            .error (refAccessConfig.memoryError .invalidPrimitiveRead)
              { st with machine :=
                  { st.machine with pendingMoveDeinit := false } } := by
        dsimp only [Miri.Interpreter.PlaceMachine.readImmediate,
          localMemoryLayout, refLocalLayoutForTy, refLayoutDataForTy,
          refEnumLayoutData]
        rw [h_tr]; rfl
      exact ⟨_, _, h_eq, rfl⟩
    | scalar tagW tagS =>
      have h_eq :
          Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
              ⟨.immediate imm, refLocalLayoutForTy types (.enum ety)⟩ st =
            .error (refAccessConfig.memoryError .invalidPrimitiveRead)
              { st with machine :=
                  { st.machine with pendingMoveDeinit := false } } := by
        dsimp only [Miri.Interpreter.PlaceMachine.readImmediate,
          localMemoryLayout, refLocalLayoutForTy, refLayoutDataForTy,
          refEnumLayoutData]
        rw [h_tr]
        cases tagW <;> rfl
      exact ⟨_, _, h_eq, rfl⟩

/-- The type of every successfully evaluated operand is interned in
`rp.types` (locals by `h_loc_res`, constants by `decodeOperand`), so its
canonical `TyId` resolves back to it. -/
theorem evalOperandToSlot_res (rp : RefProg) {bodyLocals : List MirTy}
    {slots : List LocalSlot} {amem : MemoryState} {tyOk : MirTy → Bool}
    {rop : RefOperand} {op : Operand} {ty : MirTy} {optVal : Option Val}
    {slots' : List LocalSlot} {amem' : MemoryState}
    (h_op : decodeOperand rp.types rop = some op)
    (h_loc_res : ∀ (id : LocalId) (t : MirTy),
      MirSemantics.getElem? bodyLocals id = some t →
      resolveTy rp.types (tyIdFor rp.types t) = some t)
    (h_es : evalOperandToSlot bodyLocals slots amem tyOk op =
      .ok (ty, optVal, slots', amem')) :
    resolveTy rp.types (tyIdFor rp.types ty) = some ty := by
  have h_local : ∀ (pl : Place) (t : MirTy),
      MirSemantics.getElem? bodyLocals pl.localId = some t → ty = t →
      resolveTy rp.types (tyIdFor rp.types ty) = some ty := by
    intro pl t h_t h_eq
    subst h_eq
    exact h_loc_res pl.localId ty h_t
  cases op with
  | copy pl =>
    dsimp only [evalOperandToSlot] at h_es
    cases h_t : MirSemantics.getElem? bodyLocals pl.localId with
    | none => rw [h_t] at h_es; cases h_es
    | some t =>
      rw [h_t] at h_es
      cases h_s : MirSemantics.getElem? slots pl.localId with
      | none => rw [h_s] at h_es; cases h_es
      | some sl =>
        rw [h_s] at h_es
        cases sl with
        | dead => cases h_es
        | immediate _ =>
          cases h_pe : pl.projection.isEmpty with
          | false => rw [h_pe] at h_es; cases h_es
          | true =>
            rw [h_pe] at h_es
            injection h_es with htup; injection htup with h_teq _
            exact h_local pl t h_t h_teq.symm
        | indirect mp =>
          cases h_pe : pl.projection.isEmpty with
          | false => rw [h_pe] at h_es; cases h_es
          | true =>
            rw [h_pe] at h_es
            dsimp only [Bool.not, ite_false_eq] at h_es
            cases h_ok : tyOk t with
            | false => rw [h_ok] at h_es; cases h_es
            | true =>
              rw [h_ok] at h_es
              dsimp only [Bool.not, ite_false_eq] at h_es
              cases h_ld : loadIndirect amem t mp with
              | error _ => rw [h_ld] at h_es; cases h_es
              | ok _ =>
                rw [h_ld] at h_es
                injection h_es with htup; injection htup with h_teq _
                exact h_local pl t h_t h_teq.symm
  | move pl =>
    dsimp only [evalOperandToSlot] at h_es
    cases h_t : MirSemantics.getElem? bodyLocals pl.localId with
    | none => rw [h_t] at h_es; cases h_es
    | some t =>
      rw [h_t] at h_es
      cases h_s : MirSemantics.getElem? slots pl.localId with
      | none => rw [h_s] at h_es; cases h_es
      | some sl =>
        rw [h_s] at h_es
        cases sl with
        | dead => cases h_es
        | immediate _ =>
          cases h_pe : pl.projection.isEmpty with
          | false => rw [h_pe] at h_es; cases h_es
          | true =>
            rw [h_pe] at h_es
            dsimp only [Bool.not, ite_false_eq] at h_es
            cases h_st : MirSemantics.setElem? slots pl.localId
                (liveUninitSlot t) with
            | none => rw [h_st] at h_es; cases h_es
            | some _ =>
              rw [h_st] at h_es
              injection h_es with htup; injection htup with h_teq _
              exact h_local pl t h_t h_teq.symm
        | indirect mp =>
          cases h_pe : pl.projection.isEmpty with
          | false => rw [h_pe] at h_es; cases h_es
          | true =>
            rw [h_pe] at h_es
            dsimp only [Bool.not, ite_false_eq] at h_es
            cases h_ok : tyOk t with
            | false => rw [h_ok] at h_es; cases h_es
            | true =>
              rw [h_ok] at h_es
              dsimp only [Bool.not, ite_false_eq] at h_es
              cases h_ld : loadIndirect amem t mp with
              | error _ => rw [h_ld] at h_es; cases h_es
              | ok _ =>
                rw [h_ld] at h_es
                dsimp only at h_es
                cases h_di : deinitIndirect amem t mp with
                | error _ => rw [h_di] at h_es; cases h_es
                | ok _ =>
                  rw [h_di] at h_es
                  injection h_es with htup; injection htup with h_teq _
                  exact h_local pl t h_t h_teq.symm
  | constant cst =>
    cases rop with
    | copy rpl =>
      dsimp only [decodeOperand, optMap] at h_op
      cases h_p : decodePlace rp.types rpl with
      | none => rw [h_p] at h_op; cases h_op
      | some _ =>
        rw [h_p] at h_op; injection h_op with h_o; cases h_o
    | move rpl =>
      dsimp only [decodeOperand, optMap] at h_op
      cases h_p : decodePlace rp.types rpl with
      | none => rw [h_p] at h_op; cases h_op
      | some _ =>
        rw [h_p] at h_op; injection h_op with h_o; cases h_o
    | constant rc =>
      dsimp only [decodeOperand, optMap] at h_op
      cases h_t : MirSemantics.getElem? rp.types rc.ty with
      | none => rw [h_t] at h_op; cases h_op
      | some t =>
        rw [h_t] at h_op
        injection h_op with h_oeq
        injection h_oeq with h_ceq
        subst h_ceq
        dsimp only [evalOperandToSlot] at h_es
        cases h_c : evalConstLit t rc.lit with
        | error _ => rw [h_c] at h_es; cases h_es
        | ok _ =>
          rw [h_c] at h_es
          injection h_es with htup; injection htup with h_teq _
          subst h_teq
          exact (resolveTy_tyIdFor_of_mem h_t).2

theorem evalPrimitiveOperand_ref_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (amem : MemoryState)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (path : Miri.Interpreter.OperandPath)
    (rop : RefOperand) (op : Operand) (known : Option LocalLayout)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_op : decodeOperand rp.types rop = some op)
    (h_loc_res : ∀ (id : LocalId) (ty : MirTy),
      MirSemantics.getElem? bodyLocals id = some ty →
      resolveTy rp.types (tyIdFor rp.types ty) = some ty) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    let res := EStateM.bind
      (Miri.Interpreter.OperandMachine.evalOperandAt
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
        c path (toMiriOperand rp.types rop) known)
      (Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig) st
    match evalPrimitiveOperand bodyLocals slots amem op with
    | .error k =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
    | .ok (v, slots', _) =>
      ∃ ty : MirTy,
        checkVal v ty = true ∧
        isPrimitiveReadableTy ty = true ∧
        resolveTy rp.types (tyIdFor rp.types ty) = some ty ∧
        res = .ok ⟨valToMiriImmediate ty v, refLocalLayoutForTy rp.types ty⟩
          (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots'
            retPlace mem ctrl cm) := by
  intro st res
  have h_ev := operandMachine_evalOperandAt_eq rp c defId rbody blockIdx stmtIdx
    bodyLocals slots amem retPlace mem ctrl cm path rop op
    isPrimitiveReadableTy known h_inv h_op
  dsimp only [evalPrimitiveOperand]
  cases h_es : evalOperandToSlot bodyLocals slots amem isPrimitiveReadableTy
      op with
  | error k =>
    rw [h_es] at h_ev
    let ⟨err, st', h_err, h_fk⟩ := h_ev
    dsimp only [res]
    rw [eStateM_bind_err h_err]
    exact ⟨err, st', rfl, h_fk⟩
  | ok tup =>
    let ⟨ty, optVal, slots', _⟩ := tup
    have h_tres := evalOperandToSlot_res rp h_op h_loc_res h_es
    rw [h_es] at h_ev
    dsimp only [res]
    rw [eStateM_bind_ok h_ev]
    let ⟨_, h_sm, _⟩ := evalOperandToSlot_slotsMatchTys h_inv h_es
    cases h_pr : isPrimitiveReadableTy ty with
    | false =>
      dsimp only [Bool.not, ite_true_eq]
      exact readImmediate_imm_nonprim_err ty (optValToMiriImm ty optVal)
        rp.types _ h_pr
    | true =>
      dsimp only [Bool.not, ite_false_eq]
      cases optVal with
      | none =>
        dsimp only
        let st' := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots'
          retPlace mem ctrl cm
        cases isPrimitiveReadableTy_cases h_pr with
        | inl hb =>
          subst hb
          let ⟨_, h_u⟩ := readImmediate_imm_bool_uninit rp.types st' rfl
          exact ⟨_, _, h_u, rfl⟩
        | inr h1 =>
          cases h1 with
          | inl hi =>
            let ⟨w, s, hty⟩ := hi
            subst hty
            let ⟨_, h_u⟩ := readImmediate_imm_int_uninit w s rp.types st' rfl
            exact ⟨_, _, h_u, rfl⟩
          | inr h2 =>
            cases h2 with
            | inl hc =>
              subst hc
              let ⟨_, h_u⟩ := readImmediate_imm_char_uninit rp.types st' rfl
              exact ⟨_, _, h_u, rfl⟩
            | inr hp =>
              let ⟨w, s, hty⟩ := hp
              subst hty
              let ⟨_, h_u⟩ := readImmediate_imm_pair_uninit w s rp.types st' rfl
              exact ⟨_, _, h_u, rfl⟩
      | some v =>
        dsimp only
        let st' := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots'
          retPlace mem ctrl cm
        have h_cv : checkVal v ty = true := h_sm
        cases checkVal_eq_true_inv h_cv with
        | inl hi =>
          let ⟨w, s, bits, hty, hv, _⟩ := hi
          subst hty; subst hv
          exact ⟨.int w s, h_cv, rfl, h_tres,
            readImmediate_imm_int_ok w s bits rp.types st' rfl⟩
        | inr h1 =>
          cases h1 with
          | inl hb =>
            let ⟨b, hty, hv⟩ := hb
            subst hty; subst hv
            exact ⟨.bool, h_cv, rfl, h_tres,
              readImmediate_imm_bool_ok b rp.types st' rfl⟩
          | inr h2 =>
            cases h2 with
            | inl hu => let ⟨hty, _⟩ := hu; subst hty; cases h_pr
            | inr h3 =>
              cases h3 with
              | inl he =>
                let ⟨_, _, hty, _, _, _⟩ := he; subst hty; cases h_pr
              | inr h4 =>
                cases h4 with
                | inl hc =>
                  let ⟨ch, hty, hv⟩ := hc
                  subst hty; subst hv
                  exact ⟨.char, h_cv, rfl, h_tres,
                    readImmediate_imm_char_ok ch rp.types st' rfl⟩
                | inr h5 =>
                  cases h5 with
                  | inl ho => let ⟨_, hty, _⟩ := ho; subst hty; cases h_pr
                  | inr hp =>
                    let ⟨w, s, bits, b, hty, hv, _⟩ := hp
                    subst hty; subst hv
                    exact ⟨_, h_cv, rfl, h_tres,
                      readImmediate_imm_pair_ok w s bits b rp.types st' rfl⟩

/-! ## Section 4: `ScalarOps.binary` and `ScalarOps.unary` -/

private theorem scalarInt_eq_of_data_size (a b : Miri.Memory.ScalarInt)
    (hd : a.data = b.data) (hs : a.size = b.size) : a = b := by
  cases a
  cases b
  dsimp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
  subst hd; subst hs; rfl

private theorem scalarInt_toBits_miriScalar (w : IntWidth) (bits : BitVec 128) :
    (miriScalar w bits).toBits (toMiriSize w) = .ok (truncateBits w bits) :=
  miriScalar_toUInt w bits

private theorem miriScalar_truncateBits (w : IntWidth) (bits : BitVec 128) :
    miriScalar w (truncateBits w bits) = miriScalar w bits := by
  apply scalarInt_eq_of_data_size
  · rw [miriScalar_data, miriScalar_data, truncateBits_idem]
  · cases w <;> rfl

private def integerResultWf (w : IntWidth) :
    Except IntegerOpError IntegerResult → Prop
  | .ok (.scalar sc) => sc = miriScalar w sc.data ∧ truncateBits w sc.data = sc.data
  | .ok (.withOverflow sc _) =>
    sc = miriScalar w sc.data ∧ truncateBits w sc.data = sc.data
  | .ok _ => True
  | .error (.scalar (.invalidBool _)) => False
  | .error (.scalar (.invalidChar _)) => False
  | .error _ => True

private def truncatePairWf (w : IntWidth) :
    Except IntegerOpError (Miri.Memory.ScalarInt × Bool) → Prop
  | .ok (sc, _) => sc = miriScalar w sc.data ∧ truncateBits w sc.data = sc.data
  | .error (.scalar (.invalidBool _)) => False
  | .error (.scalar (.invalidChar _)) => False
  | .error _ => True

private theorem truncateFromUInt_wf (w : IntWidth) (x : BitVec 128) :
    truncatePairWf w ((Miri.Memory.ScalarInt.truncateFromUInt x (toMiriSize w)).mapError
      IntegerOpError.scalar) := by
  rw [truncateFromUInt_eq_miriScalar w x]
  dsimp only [Except.mapError, truncatePairWf]
  rw [miriScalar_data w x]
  exact ⟨(miriScalar_truncateBits w x).symm, truncateBits_idem w x⟩

private theorem truncateFromInt_wf (w : IntWidth) (x : Int) :
    truncatePairWf w ((Miri.Memory.ScalarInt.truncateFromInt x (toMiriSize w)).mapError
      IntegerOpError.scalar) := by
  cases h_oob : (decide (x < Neg.neg (HPow.hPow (2 : Int) (127 : Nat))) ||
      decide (x ≥ HPow.hPow (2 : Int) (127 : Nat))) with
  | true =>
    have h_eq : (Miri.Memory.ScalarInt.truncateFromInt x (toMiriSize w)).mapError
        IntegerOpError.scalar = .error (.scalar (.integerOutsideI128 x)) := by
      cases w <;> (dsimp only [Miri.Memory.ScalarInt.truncateFromInt]; rw [h_oob]; rfl)
    rw [h_eq]; exact True.intro
  | false =>
    have h_eq :
        (Miri.Memory.ScalarInt.truncateFromInt x (toMiriSize w)).mapError
            IntegerOpError.scalar =
          match Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 x) (toMiriSize w) with
          | .ok (sc, _) =>
            match (toMiriSize w).signExtend sc.data with
            | .ok decoded => .ok (sc, decoded != x)
            | .error e => .error (.scalar (.sizeError e))
          | .error e => .error (.scalar e) := by
      cases w <;> (dsimp only [Miri.Memory.ScalarInt.truncateFromInt]; rw [h_oob]; rfl)
    rw [h_eq, truncateFromUInt_eq_miriScalar w (BitVec.ofInt 128 x)]
    dsimp only
    rw [miriScalar_data w (BitVec.ofInt 128 x), size_signExtend_eq]
    dsimp only [truncatePairWf]
    rw [miriScalar_data w (BitVec.ofInt 128 x)]
    exact ⟨(miriScalar_truncateBits w (BitVec.ofInt 128 x)).symm,
      truncateBits_idem w (BitVec.ofInt 128 x)⟩

private theorem truncate_body_wf (w : IntWidth) (s : Bool) (v : Int) :
    truncatePairWf w
      (if (toMiriIntType w s).signed then
        let wrapped := (BitVec.ofInt 128 v).toInt
        (Miri.Memory.ScalarInt.truncateFromInt wrapped (toMiriIntType w s).size).mapError
          IntegerOpError.scalar
      else
        (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 v)
          (toMiriIntType w s).size).mapError IntegerOpError.scalar) := by
  rw [toMiriIntType_signed, toMiriIntType_size]
  cases s with
  | true => exact truncateFromInt_wf w (BitVec.ofInt 128 v).toInt
  | false => exact truncateFromUInt_wf w (BitVec.ofInt 128 v)

private theorem shift_body_wf (op : BinOp) (w₁ w₂ : IntWidth) (s₁ s₂ : Bool)
    (l r : Int) :
    integerResultWf w₁
      (bind (((toMiriIntType w₁ s₁).size.bits).mapError
          (Function.comp IntegerOpError.scalar ScalarIntError.sizeError))
        (fun bits =>
          let amount := HMod.hMod r (Int.ofNat bits.toNat)
          let overflow := amount != r
          let result := match toMiriBinOp op with
            | .Shl | .ShlUnchecked => HShiftLeft.hShiftLeft l amount.toNat
            | _ => HShiftRight.hShiftRight l amount.toNat
          bind
            (if (toMiriIntType w₁ s₁).signed then
              let wrapped := (BitVec.ofInt 128 result).toInt
              (Miri.Memory.ScalarInt.truncateFromInt wrapped
                (toMiriIntType w₁ s₁).size).mapError IntegerOpError.scalar
            else
              (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
                (toMiriIntType w₁ s₁).size).mapError IntegerOpError.scalar)
            (fun (value, _) =>
              if overflow && (toMiriBinOp op).isUnchecked then
                throw (IntegerOpError.undefinedBehavior
                  (.shiftOverflow (toMiriBinOp op) r (toMiriIntType w₂ s₂).signed))
              else
                pure (IntegerResult.scalar value)))) := by
  have h_bits : ∃ bits, (toMiriIntType w₁ s₁).size.bits = .ok bits := by
    cases w₁ <;> exact ⟨_, rfl⟩
  let ⟨bits, hb⟩ := h_bits
  rw [hb]
  have h_tr := truncate_body_wf w₁ s₁
    (match toMiriBinOp op with
     | .Shl | .ShlUnchecked =>
       HShiftLeft.hShiftLeft l (HMod.hMod r (Int.ofNat bits.toNat)).toNat
     | _ =>
       HShiftRight.hShiftRight l (HMod.hMod r (Int.ofNat bits.toNat)).toNat)
  have h_step :
      ∀ (tr : Except IntegerOpError (Miri.Memory.ScalarInt × Bool)),
        truncatePairWf w₁ tr →
        integerResultWf w₁
          (bind tr (fun (value, _) =>
            if ((HMod.hMod r (Int.ofNat bits.toNat) != r) && (toMiriBinOp op).isUnchecked) then
              throw (IntegerOpError.undefinedBehavior
                (.shiftOverflow (toMiriBinOp op) r (toMiriIntType w₂ s₂).signed))
            else
              pure (IntegerResult.scalar value))) := by
    intro tr htr
    cases tr with
    | error e =>
      cases e with
      | scalar se => cases se <;> exact htr
      | _ => exact True.intro
    | ok p =>
      cases ((HMod.hMod r (Int.ofNat bits.toNat) != r) && (toMiriBinOp op).isUnchecked) with
      | true => exact True.intro
      | false => exact htr
  exact h_step _ h_tr

private theorem scalarResult_body_wf (op : BinOp) (w : IntWidth) (s : Bool)
    (result : Int) :
    integerResultWf w
      (let hostOverflow := if (toMiriIntType w s).signed then
          decide (result < Neg.neg (HPow.hPow (2 : Int) (127 : Nat))) ||
            decide (result ≥ HPow.hPow (2 : Int) (127 : Nat))
        else decide (result < 0) ||
          decide (result ≥ HPow.hPow (2 : Int) (128 : Nat))
       bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 result).toInt
          (Miri.Memory.ScalarInt.truncateFromInt wrapped
            (toMiriIntType w s).size).mapError IntegerOpError.scalar
        else
          (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
            (toMiriIntType w s).size).mapError IntegerOpError.scalar)
        (fun (value, lossy) =>
          if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
            throw (IntegerOpError.undefinedBehavior (.arithmeticOverflow (toMiriBinOp op)))
          else
            pure (if (toMiriBinOp op).isOverflowing then
              IntegerResult.withOverflow value (hostOverflow || lossy)
            else IntegerResult.scalar value))) := by
  have h_tr := truncate_body_wf w s result
  have h_step :
      ∀ (tr : Except IntegerOpError (Miri.Memory.ScalarInt × Bool)) (ho : Bool),
        truncatePairWf w tr →
        integerResultWf w
          (bind tr (fun (value, lossy) =>
            if (ho || lossy) && (toMiriBinOp op).isUnchecked then
              throw (IntegerOpError.undefinedBehavior (.arithmeticOverflow (toMiriBinOp op)))
            else
              pure (if (toMiriBinOp op).isOverflowing then
                IntegerResult.withOverflow value (ho || lossy)
              else IntegerResult.scalar value))) := by
    intro tr ho htr
    cases tr with
    | error e =>
      dsimp only [bind, Bind.bind, Except.bind]
      cases e with
      | scalar se => cases se <;> exact htr
      | _ => exact True.intro
    | ok p =>
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
      cases ((ho || p.2) && (toMiriBinOp op).isUnchecked) with
      | true => exact True.intro
      | false =>
        dsimp only [ite_false_eq]
        cases (toMiriBinOp op).isOverflowing with
        | true => exact htr
        | false => exact htr
  exact h_step _ _ h_tr

private theorem arith_body_wf (op : BinOp) (w : IntWidth) (s : Bool) (l r : Int) :
    integerResultWf w
      (let jp2 := fun (_ : PUnit) =>
          bind
            (match toMiriBinOp op with
             | .Add | .AddUnchecked | .AddWithOverflow => pure (l + r)
             | .Sub | .SubUnchecked | .SubWithOverflow => pure (l - r)
             | .Mul | .MulUnchecked | .MulWithOverflow => pure (l * r)
             | .Div => pure (Int.tdiv l r)
             | .Rem => pure (Int.tmod l r)
             | _ => throw (IntegerOpError.invalidBinaryOperator (toMiriBinOp op)))
            (fun result =>
              let hostOverflow := if (toMiriIntType w s).signed then
                  decide (result < Neg.neg (HPow.hPow (2 : Int) (127 : Nat))) || decide (result ≥ HPow.hPow (2 : Int) (127 : Nat))
                else decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) (128 : Nat))
              bind
                (if (toMiriIntType w s).signed then
                  let wrapped := (BitVec.ofInt 128 result).toInt
                  (Miri.Memory.ScalarInt.truncateFromInt wrapped
                    (toMiriIntType w s).size).mapError IntegerOpError.scalar
                else
                  (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
                    (toMiriIntType w s).size).mapError IntegerOpError.scalar)
                (fun (value, lossy) =>
                  if (hostOverflow || lossy) && (toMiriBinOp op).isUnchecked then
                    throw (IntegerOpError.undefinedBehavior (.arithmeticOverflow (toMiriBinOp op)))
                  else
                    pure (if (toMiriBinOp op).isOverflowing then
                      IntegerResult.withOverflow value (hostOverflow || lossy)
                    else IntegerResult.scalar value)))
       let jp1 := fun (_ : PUnit) =>
          if (toMiriIntType w s).signed &&
              (toMiriBinOp op == Miri.MIR.BinOp.Div || toMiriBinOp op == Miri.MIR.BinOp.Rem) then
            bind (((toMiriIntType w s).size.signedIntMin).mapError
                (Function.comp IntegerOpError.scalar ScalarIntError.sizeError))
              (fun min =>
                if l == min && r == Neg.neg (1 : Int) then
                  bind (throw (IntegerOpError.undefinedBehavior
                    (if toMiriBinOp op == Miri.MIR.BinOp.Div then .divisionOverflow
                     else .remainderOverflow)) : Except IntegerOpError PUnit) jp2
                else jp2 PUnit.unit)
          else jp2 PUnit.unit
       if r == 0 then
         let jp0 := fun (_ : PUnit) =>
           if toMiriBinOp op == Miri.MIR.BinOp.Rem then
             bind (throw (IntegerOpError.undefinedBehavior .remainderByZero) :
               Except IntegerOpError PUnit) jp1
           else jp1 PUnit.unit
         if toMiriBinOp op == Miri.MIR.BinOp.Div then
           bind (throw (IntegerOpError.undefinedBehavior .divisionByZero) :
             Except IntegerOpError PUnit) jp0
         else jp0 PUnit.unit
       else jp1 PUnit.unit) := by
  have h_wrap :
      ∀ (k : PUnit → Except IntegerOpError IntegerResult),
        integerResultWf w (k PUnit.unit) →
        integerResultWf w
          (let jp1 := fun (_ : PUnit) =>
            if (toMiriIntType w s).signed &&
                (toMiriBinOp op == Miri.MIR.BinOp.Div || toMiriBinOp op == Miri.MIR.BinOp.Rem) then
              bind (((toMiriIntType w s).size.signedIntMin).mapError
                  (Function.comp IntegerOpError.scalar ScalarIntError.sizeError))
                (fun min =>
                  if l == min && r == Neg.neg (1 : Int) then
                    bind (throw (IntegerOpError.undefinedBehavior
                      (if toMiriBinOp op == Miri.MIR.BinOp.Div then .divisionOverflow
                       else .remainderOverflow)) : Except IntegerOpError PUnit) k
                  else k PUnit.unit)
            else k PUnit.unit
           if r == 0 then
             let jp0 := fun (_ : PUnit) =>
               if toMiriBinOp op == Miri.MIR.BinOp.Rem then
                 bind (throw (IntegerOpError.undefinedBehavior .remainderByZero) :
                   Except IntegerOpError PUnit) jp1
               else jp1 PUnit.unit
             if toMiriBinOp op == Miri.MIR.BinOp.Div then
               bind (throw (IntegerOpError.undefinedBehavior .divisionByZero) :
                 Except IntegerOpError PUnit) jp0
             else jp0 PUnit.unit
           else jp1 PUnit.unit) := by
    intro k hk
    have h_jp1 :
        integerResultWf w
          (if (toMiriIntType w s).signed &&
              (toMiriBinOp op == Miri.MIR.BinOp.Div || toMiriBinOp op == Miri.MIR.BinOp.Rem) then
            bind (((toMiriIntType w s).size.signedIntMin).mapError
                (Function.comp IntegerOpError.scalar ScalarIntError.sizeError))
              (fun min =>
                if l == min && r == Neg.neg (1 : Int) then
                  bind (throw (IntegerOpError.undefinedBehavior
                    (if toMiriBinOp op == Miri.MIR.BinOp.Div then .divisionOverflow
                     else .remainderOverflow)) : Except IntegerOpError PUnit) k
                else k PUnit.unit)
          else k PUnit.unit) := by
      rw [toMiriIntType_size, size_signedIntMin_eq]
      cases ((toMiriIntType w s).signed &&
          (toMiriBinOp op == Miri.MIR.BinOp.Div || toMiriBinOp op == Miri.MIR.BinOp.Rem)) with
      | false => exact hk
      | true =>
        dsimp only [ite_true_eq, Except.mapError, bind, Bind.bind, Except.bind]
        cases (l == signedMinInt w && r == Neg.neg (1 : Int)) with
        | true => exact True.intro
        | false => exact hk
    cases (r == 0) with
    | false => exact h_jp1
    | true =>
      dsimp only [ite_true_eq]
      cases h_div : (toMiriBinOp op == Miri.MIR.BinOp.Div) with
      | true => exact True.intro
      | false =>
        dsimp only [ite_false_eq]
        rw [h_div] at h_jp1
        cases h_rem : (toMiriBinOp op == Miri.MIR.BinOp.Rem) with
        | true => exact True.intro
        | false =>
          rw [h_rem] at h_jp1
          exact h_jp1
  apply h_wrap
  cases op with
  | add | addUnchecked | addWithOverflow => exact scalarResult_body_wf _ w s (l + r)
  | sub | subUnchecked | subWithOverflow => exact scalarResult_body_wf _ w s (l - r)
  | mul | mulUnchecked | mulWithOverflow => exact scalarResult_body_wf _ w s (l * r)
  | div => exact scalarResult_body_wf _ w s (Int.tdiv l r)
  | rem => exact scalarResult_body_wf _ w s (Int.tmod l r)
  | _ => exact True.intro

private theorem integerOps_binary_wf (op : BinOp) (w₁ w₂ : IntWidth)
    (s₁ s₂ : Bool) (b₁ b₂ : BitVec 128) :
    integerResultWf w₁
      (Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
        (miriIntValue ⟨w₁, s₁, b₁⟩) (miriIntValue ⟨w₂, s₂, b₂⟩)) := by
  dsimp only [Miri.Interpreter.IntegerOps.binary, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure]
  rw [integerOps_decode_eq, integerOps_decode_eq]
  dsimp only
  cases op with
  | shl =>
    have h_sh : (toMiriBinOp .shl == .Shl || toMiriBinOp .shl == .ShlUnchecked ||
        toMiriBinOp .shl == .Shr || toMiriBinOp .shl == .ShrUnchecked) = true := rfl
    rw [h_sh, ite_true_eq]
    exact shift_body_wf .shl w₁ w₂ s₁ s₂ (decodeScalar ⟨w₁, s₁, b₁⟩) (decodeScalar ⟨w₂, s₂, b₂⟩)
  | shlUnchecked =>
    have h_sh : (toMiriBinOp .shlUnchecked == .Shl || toMiriBinOp .shlUnchecked == .ShlUnchecked ||
        toMiriBinOp .shlUnchecked == .Shr || toMiriBinOp .shlUnchecked == .ShrUnchecked) = true := rfl
    rw [h_sh, ite_true_eq]
    exact shift_body_wf .shlUnchecked w₁ w₂ s₁ s₂ (decodeScalar ⟨w₁, s₁, b₁⟩) (decodeScalar ⟨w₂, s₂, b₂⟩)
  | shr =>
    have h_sh : (toMiriBinOp .shr == .Shl || toMiriBinOp .shr == .ShlUnchecked ||
        toMiriBinOp .shr == .Shr || toMiriBinOp .shr == .ShrUnchecked) = true := rfl
    rw [h_sh, ite_true_eq]
    exact shift_body_wf .shr w₁ w₂ s₁ s₂ (decodeScalar ⟨w₁, s₁, b₁⟩) (decodeScalar ⟨w₂, s₂, b₂⟩)
  | shrUnchecked =>
    have h_sh : (toMiriBinOp .shrUnchecked == .Shl || toMiriBinOp .shrUnchecked == .ShlUnchecked ||
        toMiriBinOp .shrUnchecked == .Shr || toMiriBinOp .shrUnchecked == .ShrUnchecked) = true := rfl
    rw [h_sh, ite_true_eq]
    exact shift_body_wf .shrUnchecked w₁ w₂ s₁ s₂ (decodeScalar ⟨w₁, s₁, b₁⟩) (decodeScalar ⟨w₂, s₂, b₂⟩)
  | eq | ne | lt | le | gt | ge | cmp =>
    dsimp only [toMiriBinOp]
    cases ((miriIntValue ⟨w₁, s₁, b₁⟩).type != (miriIntValue ⟨w₂, s₂, b₂⟩).type) <;>
      exact True.intro
  | bitAnd | bitOr | bitXor =>
    change integerResultWf w₁ (if false = true then _ else _)
    dsimp only [ite_false_eq, toMiriBinOp]
    cases ((miriIntValue ⟨w₁, s₁, b₁⟩).type != (miriIntValue ⟨w₂, s₂, b₂⟩).type) with
    | true => exact True.intro
    | false =>
      dsimp only [ite_false_eq, miriIntValue, toMiriIntType]
      rw [miriScalar_toUInt, miriScalar_toUInt]
      dsimp only [Except.mapError, bind, Bind.bind, Except.bind]
      rw [truncateFromUInt_eq_miriScalar w₁]
      dsimp only [Except.mapError, integerResultWf]
      rw [miriScalar_data w₁]
      exact ⟨(miriScalar_truncateBits w₁ _).symm, truncateBits_idem w₁ _⟩
  | add | sub | mul | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow | div | rem | offset =>
    change integerResultWf w₁ (if false = true then _ else _)
    dsimp only [ite_false_eq]
    cases ((miriIntValue ⟨w₁, s₁, b₁⟩).type != (miriIntValue ⟨w₂, s₂, b₂⟩).type) with
    | true => exact True.intro
    | false =>
      dsimp only [ite_false_eq]
      exact arith_body_wf _ w₁ s₁ (decodeScalar ⟨w₁, s₁, b₁⟩) (decodeScalar ⟨w₂, s₂, b₂⟩)

private theorem integerOps_binary_scalar_wf (op : BinOp) (w₁ w₂ : IntWidth)
    (s₁ s₂ : Bool) (b₁ b₂ : BitVec 128) (sc : Miri.Memory.ScalarInt)
    (h : Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
        (miriIntValue ⟨w₁, s₁, b₁⟩) (miriIntValue ⟨w₂, s₂, b₂⟩) = .ok (.scalar sc)) :
    sc = miriScalar w₁ sc.data ∧ truncateBits w₁ sc.data = sc.data := by
  have hw := integerOps_binary_wf op w₁ w₂ s₁ s₂ b₁ b₂
  rw [h] at hw
  exact hw

private theorem integerOps_binary_overflow_wf (op : BinOp) (w₁ w₂ : IntWidth)
    (s₁ s₂ : Bool) (b₁ b₂ : BitVec 128) (sc : Miri.Memory.ScalarInt) (o : Bool)
    (h : Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
        (miriIntValue ⟨w₁, s₁, b₁⟩) (miriIntValue ⟨w₂, s₂, b₂⟩) =
      .ok (.withOverflow sc o)) :
    sc = miriScalar w₁ sc.data ∧ truncateBits w₁ sc.data = sc.data := by
  have hw := integerOps_binary_wf op w₁ w₂ s₁ s₂ b₁ b₂
  rw [h] at hw
  exact hw

private theorem integerOps_binary_no_invalidBool_invalidChar (op : BinOp)
    (w₁ w₂ : IntWidth) (s₁ s₂ : Bool) (b₁ b₂ : BitVec 128) (se : ScalarIntError)
    (h : Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
        (miriIntValue ⟨w₁, s₁, b₁⟩) (miriIntValue ⟨w₂, s₂, b₂⟩) = .error (.scalar se)) :
    (match se with | .invalidBool _ | .invalidChar _ => False | _ => True) := by
  have hw := integerOps_binary_wf op w₁ w₂ s₁ s₂ b₁ b₂
  rw [h] at hw
  cases se <;> exact hw

private def unaryResultWf (w : IntWidth) :
    Except IntegerOpError Miri.Memory.ScalarInt → Prop
  | .ok sc => sc = miriScalar w sc.data ∧ truncateBits w sc.data = sc.data
  | .error (.scalar (.invalidBool _)) => False
  | .error (.scalar (.invalidChar _)) => False
  | .error _ => True

private theorem unary_truncate_wf (w : IntWidth) (s : Bool) (result : Int) :
    unaryResultWf w
      (bind
        (if (toMiriIntType w s).signed then
          let wrapped := (BitVec.ofInt 128 result).toInt
          (Miri.Memory.ScalarInt.truncateFromInt wrapped
            (toMiriIntType w s).size).mapError IntegerOpError.scalar
        else
          (Miri.Memory.ScalarInt.truncateFromUInt (BitVec.ofInt 128 result)
            (toMiriIntType w s).size).mapError IntegerOpError.scalar)
        (fun x => pure x.1)) := by
  have h_tr := truncate_body_wf w s result
  have h_step :
      ∀ (tr : Except IntegerOpError (Miri.Memory.ScalarInt × Bool)),
        truncatePairWf w tr →
        unaryResultWf w (bind tr (fun x => pure x.1)) := by
    intro tr htr
    cases tr with
    | error e =>
      cases e with
      | scalar se => cases se <;> exact htr
      | _ => exact True.intro
    | ok p => exact htr
  exact h_step _ h_tr

private theorem integerOps_unary_wf_all (op : UnOp) (w : IntWidth) (s : Bool)
    (bits : BitVec 128) :
    unaryResultWf w
      (Miri.Interpreter.IntegerOps.unary (toMiriUnOp op) (miriIntValue ⟨w, s, bits⟩)) := by
  dsimp only [Miri.Interpreter.IntegerOps.unary, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure]
  rw [integerOps_decode_eq]
  cases op with
  | ptrMetadata => exact True.intro
  | not => exact unary_truncate_wf w s (Complement.complement (decodeScalar ⟨w, s, bits⟩))
  | neg =>
    dsimp only [toMiriUnOp, miriIntValue]
    have h_sgn := toMiriIntType_signed w s
    cases s with
    | false =>
      simp only [h_sgn, Bool.false_eq_true, ite_false]
      exact True.intro
    | true =>
      simp only [h_sgn, ite_true]
      exact unary_truncate_wf w true (Neg.neg (decodeScalar ⟨w, true, bits⟩))

private theorem integerOps_unary_wf (op : UnOp) (w : IntWidth) (s : Bool)
    (bits : BitVec 128) (sc : Miri.Memory.ScalarInt)
    (h : Miri.Interpreter.IntegerOps.unary (toMiriUnOp op)
        (miriIntValue ⟨w, s, bits⟩) = .ok sc) :
    sc = miriScalar w sc.data ∧ truncateBits w sc.data = sc.data := by
  have hw := integerOps_unary_wf_all op w s bits
  rw [h] at hw
  exact hw

private theorem integerOps_unary_no_invalidBool_invalidChar (op : UnOp)
    (w : IntWidth) (s : Bool) (bits : BitVec 128) (se : ScalarIntError)
    (h : Miri.Interpreter.IntegerOps.unary (toMiriUnOp op)
        (miriIntValue ⟨w, s, bits⟩) = .error (.scalar se)) :
    (match se with | .invalidBool _ | .invalidChar _ => False | _ => True) := by
  have hw := integerOps_unary_wf_all op w s bits
  rw [h] at hw
  cases se <;> exact hw

private theorem scalarOps_classify_bool (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).classify c
        (tyIdFor rp.types .bool) st = .ok .boolean st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
    Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refScalarLeaves]
  rw [resolveTy_tyIdFor_of_aux (code := 0) rfl]

private theorem scalarOps_classify_int (rp : RefProg) (c : Choice)
    (w : IntWidth) (s : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).classify c
        (tyIdFor rp.types (.int w s)) st = .ok (.integer (toMiriIntKind w s)) st := by
  have h_res : resolveTy rp.types (tyIdFor rp.types (.int w s)) = some (.int w s) := by
    cases w <;> cases s <;> exact resolveTy_tyIdFor_of_aux rfl
  dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
    Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refScalarLeaves]
  rw [h_res]

theorem resolveTy_tyIdFor_bool (types : List MirTy) :
    resolveTy types (tyIdFor types .bool) = some .bool :=
  resolveTy_tyIdFor_of_aux (code := 0) rfl

theorem resolveTy_tyIdFor_int (types : List MirTy) (w : IntWidth) (s : Bool) :
    resolveTy types (tyIdFor types (.int w s)) = some (.int w s) := by
  cases w <;> cases s <;> exact resolveTy_tyIdFor_of_aux rfl

/-- `resolveTy` inverts `tyIdFor` whenever it succeeds. -/
theorem resolveTy_tyIdFor_some_eq {types : List MirTy} {ty t : MirTy}
    (h : resolveTy types (tyIdFor types ty) = some t) : t = ty := by
  cases h_idx : indexOfTy types ty with
  | some idx =>
    have h_ty : tyIdFor types ty = idx := by
      dsimp only [tyIdFor]; rw [h_idx]
    let ⟨h_g, _⟩ := indexOfTy_some_getElem? h_idx
    rw [h_ty] at h
    dsimp only [resolveTy] at h
    rw [h_g] at h
    injection h with h_eq
    exact h_eq.symm
  | none =>
    cases h_aux : auxTyCode ty with
    | some code =>
      rw [resolveTy_tyIdFor_of_aux h_aux] at h
      injection h with h_eq
      exact h_eq.symm
    | none =>
      have h_ty : tyIdFor types ty = types.length + 14 := by
        dsimp only [tyIdFor]; rw [h_idx, h_aux]
      rw [h_ty] at h
      dsimp only [resolveTy] at h
      have h_le : types.length ≤ types.length + 14 := Nat.le_add_right _ 14
      rw [mirGetElem?_none_of_ge h_le] at h
      have h_ble : Nat.ble types.length (types.length + 14) = true :=
        Nat.ble_eq.mpr h_le
      dsimp only at h
      rw [h_ble, ite_true_eq, Nat.add_sub_cancel_left] at h
      cases h

/-- Distinct types have distinct canonical `TyId`s when the first resolves. -/
theorem tyIdFor_beq_false_of_ne {types : List MirTy} {a b : MirTy}
    (h_a : resolveTy types (tyIdFor types a) = some a) (h_ne : a ≠ b) :
    (tyIdFor types a == tyIdFor types b) = false := by
  cases h_b : (tyIdFor types a == tyIdFor types b) with
  | false => rfl
  | true =>
    have h_eq : tyIdFor types a = tyIdFor types b := eq_of_beq h_b
    rw [h_eq] at h_a
    exact False.elim (h_ne (resolveTy_tyIdFor_some_eq h_a))

private theorem stepErrorFaultKind_integerError (err : IntegerOpError) :
    stepErrorFaultKind (Miri.Interpreter.ScalarOps.integerError err) =
      match err with
      | .undefinedBehavior _ => .undefined
      | .scalar (.invalidBool _) => .undefined
      | .scalar (.invalidChar _) => .undefined
      | _ => .unsupported := by
  cases err with
  | scalar se => cases se <;> rfl
  | undefinedBehavior _ => rfl
  | asymmetricTypes _ _ => rfl
  | invalidBinaryOperator _ => rfl
  | invalidUnaryOperator _ _ => rfl

private theorem checkVal_scalar_of_trunc (w : IntWidth) (s : Bool)
    (bits : BitVec 128) (h_tr : truncateBits w bits = bits) :
    checkVal (.scalar ⟨w, s, bits⟩) (.int w s) = true := by
  have h_wf : (ScalarVal.mk w s bits).wf = true := by
    dsimp only [ScalarVal.wf]; rw [h_tr]; exact beq_self_eq_true _
  dsimp only [checkVal, Val.ty?]
  rw [h_wf, ite_true_eq]
  dsimp only [MirTy.beq]
  rw [IntWidth.beq_refl]
  cases s <;> rfl

private theorem scalarOps_bool_bin_unfold (rp : RefProg) (c : Choice)
    (op : BinOp) (lb rb : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    let sc := Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)
    let lhs : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromBool lb), refLocalLayoutForTy rp.types .bool⟩
    let rhs : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromBool rb), refLocalLayoutForTy rp.types .bool⟩
    Miri.Interpreter.ScalarOps.binary sc c (toMiriBinOp op) lhs rhs st =
      match Miri.Interpreter.IntegerOps.binaryBool (toMiriBinOp op) lb rb with
      | .error e => .error (Miri.Interpreter.ScalarOps.integerError e) st
      | .ok (.boolean b) =>
        .ok ⟨.scalar (.fromBool b), refLocalLayoutForTy rp.types .bool⟩ st
      | .ok _ => .error (.invalidProgram "non-bool binaryBool") st := by
  intro sc lhs rhs
  dsimp only [Miri.Interpreter.ScalarOps.binary, bind, Bind.bind, lhs, rhs]
  change (EStateM.bind (sc.classify c (tyIdFor rp.types .bool)) _ st) = _
  rw [eStateM_bind_ok (scalarOps_classify_bool rp c st)]
  dsimp only
  change (EStateM.bind
      (if (tyIdFor rp.types .bool == tyIdFor rp.types .bool) = true then
        EStateM.pure ()
      else EStateM.throw (StepError.invalidProgram "asymmetric scalar operand types")) _ st) = _
  rw [beq_self_eq_true, ite_true_eq, eStateM_bind_pure]
  cases lb <;> cases rb <;> cases op <;> rfl

/-- Result of `ScalarOps.finish` (and the surrounding `liftResult`) on an
`IntegerOps.binary` result whose left operand has type `.int w s`. -/
private noncomputable def refIntBinRes (types : List MirTy) (w : IntWidth)
    (s : Bool) (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    Except IntegerOpError IntegerResult →
      EStateM.Result StepError (Miri.Interpreter.MachineHooks.State Unit RefUser)
        (RvalueImmTy Miri.Memory.Provenance)
  | .error err => .error (Miri.Interpreter.ScalarOps.integerError err) st
  | .ok (.scalar sv) =>
    .ok ⟨.scalar (.fromScalarInt sv), refLocalLayoutForTy types (.int w s)⟩ st
  | .ok (.boolean b) =>
    .ok ⟨.scalar (.fromBool b), refLocalLayoutForTy types .bool⟩ st
  | .ok (.withOverflow sv o) =>
    .ok ⟨.scalarPair (.fromScalarInt sv) (.fromBool o),
      refLocalLayoutForTy types (.tuple [.int w s, .bool])⟩ st
  | .ok (.ordering o) =>
    .ok ⟨valToMiriImmediate .ordering (.ordering (refOrderingOfMiri o)),
      refLocalLayoutForTy types .ordering⟩ st

private theorem scalarHooks_overflowLayout_int (rp : RefProg) (c : Choice)
    (w : IntWidth) (s : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).overflowLayout
        c (refLocalLayoutForTy rp.types (.int w s)) st =
      .ok (refLocalLayoutForTy rp.types (.tuple [.int w s, .bool])) st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
    Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refScalarLeaves, refLocalLayoutForTy]
  rw [resolveTy_tyIdFor_int]

private theorem scalarOps_int_bin_unfold (rp : RefProg) (c : Choice)
    (op : BinOp) (w₁ w₂ : IntWidth) (s₁ s₂ : Bool) (b₁ b₂ : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    let sc := Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)
    let lhs : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromScalarInt (miriScalar w₁ b₁)),
        refLocalLayoutForTy rp.types (.int w₁ s₁)⟩
    let rhs : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromScalarInt (miriScalar w₂ b₂)),
        refLocalLayoutForTy rp.types (.int w₂ s₂)⟩
    Miri.Interpreter.ScalarOps.binary sc c (toMiriBinOp op) lhs rhs st =
      (if !(toMiriBinOp op == .Shl || toMiriBinOp op == .ShlUnchecked ||
            toMiriBinOp op == .Shr || toMiriBinOp op == .ShrUnchecked) then
          if (tyIdFor rp.types (.int w₁ s₁) ==
              tyIdFor rp.types (.int w₂ s₂)) then
            refIntBinRes rp.types w₁ s₁ st
              (Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
                (miriIntValue ⟨w₁, s₁, b₁⟩) (miriIntValue ⟨w₂, s₂, b₂⟩))
          else .error (.invalidProgram "asymmetric scalar operand types") st
        else
          refIntBinRes rp.types w₁ s₁ st
            (Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
              (miriIntValue ⟨w₁, s₁, b₁⟩) (miriIntValue ⟨w₂, s₂, b₂⟩))) := by
  intro sc lhs rhs
  dsimp only [Miri.Interpreter.ScalarOps.binary, bind, Bind.bind, lhs, rhs]
  change (EStateM.bind (sc.classify c (tyIdFor rp.types (.int w₁ s₁))) _ st) = _
  rw [eStateM_bind_ok (scalarOps_classify_int rp c w₁ s₁ st)]
  dsimp only
  change (EStateM.bind (sc.classify c (tyIdFor rp.types (.int w₂ s₂))) _ st) = _
  rw [eStateM_bind_ok (scalarOps_classify_int rp c w₂ s₂ st)]
  dsimp only
  cases w₁ <;> (
    change (EStateM.bind (EStateM.pure (miriIntValue ⟨_, s₁, b₁⟩)) _ st) = _
    rw [eStateM_bind_pure]
    cases w₂ <;> (
      change (EStateM.bind (EStateM.pure (miriIntValue ⟨_, s₂, b₂⟩)) _ st) = _
      rw [eStateM_bind_pure]
      change (if (!(toMiriBinOp op == Miri.MIR.BinOp.Shl ||
          toMiriBinOp op == Miri.MIR.BinOp.ShlUnchecked ||
          toMiriBinOp op == Miri.MIR.BinOp.Shr ||
          toMiriBinOp op == Miri.MIR.BinOp.ShrUnchecked)) = true then
            (_ : Miri.Interpreter.RvalueM
              (Miri.Interpreter.MachineHooks.State Unit RefUser)
              (RvalueImmTy Miri.Memory.Provenance))
          else _) st = _
      cases (toMiriBinOp op == Miri.MIR.BinOp.Shl ||
          toMiriBinOp op == Miri.MIR.BinOp.ShlUnchecked ||
          toMiriBinOp op == Miri.MIR.BinOp.Shr ||
          toMiriBinOp op == Miri.MIR.BinOp.ShrUnchecked) with
      | true =>
        dsimp only [Bool.not, ite_false_eq]
        cases Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
            (miriIntValue ⟨_, s₁, b₁⟩) (miriIntValue ⟨_, s₂, b₂⟩) with
        | error _ => rfl
        | ok r =>
          cases r with
          | scalar _ => rfl
          | boolean _ => rfl
          | ordering o => cases o <;> rfl
          | withOverflow sv o =>
            change EStateM.bind
              ((Miri.Interpreter.ExecutionMachine.scalarHooks
                (refExecCfg rp)).overflowLayout c
                (refLocalLayoutForTy rp.types (.int _ s₁)))
              (fun layout => EStateM.pure
                (⟨.scalarPair (.fromScalarInt sv) (.fromBool o), layout⟩ :
                  RvalueImmTy Miri.Memory.Provenance)) st = _
            rw [eStateM_bind_ok (scalarHooks_overflowLayout_int rp c _ s₁ st)]
            rfl
      | false =>
        dsimp only [Bool.not, ite_true_eq]
        change (EStateM.bind
            (if (tyIdFor rp.types (.int _ s₁) ==
                tyIdFor rp.types (.int _ s₂)) = true then
              EStateM.pure ()
            else EStateM.throw
              (StepError.invalidProgram "asymmetric scalar operand types"))
            _ st) = _
        cases (tyIdFor rp.types (.int _ s₁) ==
            tyIdFor rp.types (.int _ s₂)) with
        | false => rfl
        | true =>
          dsimp only [ite_true_eq]
          rw [eStateM_bind_pure]
          cases Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
              (miriIntValue ⟨_, s₁, b₁⟩) (miriIntValue ⟨_, s₂, b₂⟩) with
          | error _ => rfl
          | ok r =>
            cases r with
            | scalar _ => rfl
            | boolean _ => rfl
            | ordering o => cases o <;> rfl
            | withOverflow sv o =>
              change EStateM.bind
                ((Miri.Interpreter.ExecutionMachine.scalarHooks
                  (refExecCfg rp)).overflowLayout c
                  (refLocalLayoutForTy rp.types (.int _ s₁)))
                (fun layout => EStateM.pure
                  (⟨.scalarPair (.fromScalarInt sv) (.fromBool o), layout⟩ :
                    RvalueImmTy Miri.Memory.Provenance)) st = _
              rw [eStateM_bind_ok
                (scalarHooks_overflowLayout_int rp c _ s₁ st)]
              rfl))

private theorem scalarOps_classify_char (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .char) = some .char) :
    (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).classify c
        (tyIdFor rp.types .char) st = .ok .character st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
    Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refScalarLeaves]
  rw [h_res]

/-- Classifying a `char` or overflow-pair type either fails closed
(`.unsupported`) or yields `.character`; it never yields `.integer` or
`.boolean`. -/
private theorem scalarOps_classify_char_or_pair (rp : RefProg) (c : Choice)
    (ty : MirTy) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_ty : ty = .char ∨ ∃ w s, ty = .tuple [.int w s, .bool]) :
    (∃ e, (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).classify
        c (tyIdFor rp.types ty) st = .error e st ∧
        stepErrorFaultKind e = .unsupported) ∨
      (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).classify c
        (tyIdFor rp.types ty) st = .ok .character st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
    Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refScalarLeaves]
  cases h_r : resolveTy rp.types (tyIdFor rp.types ty) with
  | none => exact Or.inl ⟨_, rfl, rfl⟩
  | some t =>
    have h_eq := resolveTy_tyIdFor_some_eq h_r
    subst h_eq
    cases h_ty with
    | inl hc => subst hc; exact Or.inr rfl
    | inr hp =>
      let ⟨w, s, hty⟩ := hp
      subst hty
      exact Or.inl ⟨_, rfl, rfl⟩

/-- `ScalarOps.binary` on two `char` operands. -/
private theorem scalarOps_char_bin_unfold (rp : RefProg) (c : Choice)
    (op : BinOp) (l r : Char)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .char) = some .char) :
    let sc := Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)
    let lhs : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromChar l), refLocalLayoutForTy rp.types .char⟩
    let rhs : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromChar r), refLocalLayoutForTy rp.types .char⟩
    Miri.Interpreter.ScalarOps.binary sc c (toMiriBinOp op) lhs rhs st =
      match Miri.Interpreter.IntegerOps.binaryChar (toMiriBinOp op) l r with
      | .error err => .error (Miri.Interpreter.ScalarOps.integerError err) st
      | .ok (.boolean b) =>
        .ok ⟨.scalar (.fromBool b), refLocalLayoutForTy rp.types .bool⟩ st
      | .ok (.ordering o) =>
        .ok ⟨valToMiriImmediate .ordering (.ordering (refOrderingOfMiri o)),
          refLocalLayoutForTy rp.types .ordering⟩ st
      | .ok (.scalar sv) =>
        .ok ⟨.scalar (.fromScalarInt sv), refLocalLayoutForTy rp.types .char⟩ st
      | .ok (.withOverflow _ _) =>
        .error (.invalidProgram "overflow layout on non-integer type") st := by
  intro sc lhs rhs
  dsimp only [Miri.Interpreter.ScalarOps.binary, bind, Bind.bind, lhs, rhs]
  change (EStateM.bind (sc.classify c (tyIdFor rp.types .char)) _ st) = _
  rw [eStateM_bind_ok (scalarOps_classify_char rp c st h_res)]
  dsimp only
  change (EStateM.bind
      (if (tyIdFor rp.types .char == tyIdFor rp.types .char) = true then
        EStateM.pure ()
      else EStateM.throw
        (StepError.invalidProgram "asymmetric scalar operand types")) _ st) = _
  rw [beq_self_eq_true, ite_true_eq, eStateM_bind_pure]
  change (EStateM.bind (EStateM.pure (Miri.Memory.Scalar.fromChar
    (Prov := Miri.Memory.Provenance) l)) _ st) = _
  rw [eStateM_bind_pure]
  change (EStateM.bind (EStateM.pure (Miri.Memory.Scalar.fromChar
    (Prov := Miri.Memory.Provenance) r)) _ st) = _
  rw [eStateM_bind_pure]
  rw [scalar_toChar_fromChar, scalar_toChar_fromChar]
  change (EStateM.bind (EStateM.pure l) _ st) = _
  rw [eStateM_bind_pure]
  change (EStateM.bind (EStateM.pure r) _ st) = _
  rw [eStateM_bind_pure]
  cases Miri.Interpreter.IntegerOps.binaryChar (toMiriBinOp op) l r with
  | error _ => rfl
  | ok res =>
    cases res with
    | scalar _ => rfl
    | boolean _ => rfl
    | ordering o => cases o <;> rfl
    | withOverflow sv o =>
      change EStateM.bind
        ((Miri.Interpreter.ExecutionMachine.scalarHooks
          (refExecCfg rp)).overflowLayout c (refLocalLayoutForTy rp.types .char))
        (fun layout => EStateM.pure
          (⟨.scalarPair (.fromScalarInt sv) (.fromBool o), layout⟩ :
            RvalueImmTy Miri.Memory.Provenance)) st = _
      have h_ovl :
          (Miri.Interpreter.ExecutionMachine.scalarHooks
            (refExecCfg rp)).overflowLayout c
            (refLocalLayoutForTy rp.types .char) st =
          .error (.invalidProgram "overflow layout on non-integer type") st := by
        dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
          Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
          Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
          refScalarLeaves, refLocalLayoutForTy]
        rw [h_res]
      rw [eStateM_bind_err h_ovl]

/-- With `evalRefMiriBinOp`'s scalar arm, the reference binary operator on two
integers is `refIntResultVal` of `IntegerOps.binary`. -/
private theorem evalRefMiriBinOp_eq_match (op : BinOp) (sv₁ sv₂ : ScalarVal) :
    evalRefBinOp op (.scalar sv₁) (.scalar sv₂) =
      refIntResultVal sv₁.width sv₁.signed
        (Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
          (miriIntValue sv₁) (miriIntValue sv₂)) := rfl

private theorem checkVal_scalar_of_trunc' (w : IntWidth) (s : Bool)
    (bits : BitVec 128) (h_tr : truncateBits w bits = bits) :
    (ScalarVal.mk w s bits).wf = true := by
  dsimp only [ScalarVal.wf]; rw [h_tr]; exact beq_self_eq_true _

private theorem checkVal_pair_of_trunc (w : IntWidth) (s : Bool)
    (bits : BitVec 128) (b : Bool) (h_tr : truncateBits w bits = bits) :
    checkVal (.tuple [.scalar ⟨w, s, bits⟩, .bool b])
      (.tuple [.int w s, .bool]) = true := by
  have h_wf := checkVal_scalar_of_trunc' w s bits h_tr
  dsimp only [checkVal, Val.ty?]
  rw [h_wf, ite_true_eq]
  dsimp only [MirTy.beq, MirTy.beqList]
  rw [IntWidth.beq_refl]
  cases s <;> rfl

/-- Result of an integer binary operator on `IntegerOps.binary`'s result
`res0`: the reference value and the `ScalarOps.binary` result agree. -/
private theorem refIntBinRes_handle (rp : RefProg) (op : BinOp)
    (w₁ w₂ : IntWidth) (s₁ s₂ : Bool) (b₁ b₂ : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (res0 : Except IntegerOpError IntegerResult)
    (h_bin : Miri.Interpreter.IntegerOps.binary (toMiriBinOp op)
      (miriIntValue ⟨w₁, s₁, b₁⟩) (miriIntValue ⟨w₂, s₂, b₂⟩) = res0) :
    match refIntResultVal w₁ s₁ res0 with
    | .error k =>
      ∃ err st', refIntBinRes rp.types w₁ s₁ st res0 = .error err st' ∧
        stepErrorFaultKind err = k
    | .ok v =>
      ∃ resTy : MirTy,
        checkVal v resTy = true ∧
        isSupportedScalarOrUnitTy resTy = true ∧
        refIntBinRes rp.types w₁ s₁ st res0 =
          .ok ⟨valToMiriImmediate resTy v, refLocalLayoutForTy rp.types resTy⟩
            st := by
  cases res0 with
  | error err =>
    cases err with
    | undefinedBehavior _ => exact ⟨_, _, rfl, rfl⟩
    | asymmetricTypes _ _ | invalidBinaryOperator _ | invalidUnaryOperator _ =>
      exact ⟨_, _, rfl, rfl⟩
    | scalar se =>
      have h_no := integerOps_binary_no_invalidBool_invalidChar op w₁ w₂ s₁ s₂
        b₁ b₂ se h_bin
      cases se with
      | invalidBool _ | invalidChar _ => exact False.elim h_no
      | _ => exact ⟨_, _, rfl, rfl⟩
  | ok r =>
    cases r with
    | boolean b => exact ⟨.bool, rfl, rfl, rfl⟩
    | ordering o => exact ⟨.ordering, rfl, rfl, rfl⟩
    | scalar sv =>
      let ⟨h_sv, h_tr⟩ := integerOps_binary_scalar_wf op w₁ w₂ s₁ s₂ b₁ b₂ sv
        h_bin
      refine ⟨.int w₁ s₁, checkVal_scalar_of_trunc w₁ s₁ sv.data h_tr, rfl, ?_⟩
      dsimp only [refIntBinRes, valToMiriImmediate]
      rw [← h_sv]
    | withOverflow sv o =>
      let ⟨h_sv, h_tr⟩ := integerOps_binary_overflow_wf op w₁ w₂ s₁ s₂ b₁ b₂
        sv o h_bin
      refine ⟨.tuple [.int w₁ s₁, .bool],
        checkVal_pair_of_trunc w₁ s₁ sv.data o h_tr, rfl, ?_⟩
      dsimp only [refIntBinRes, valToMiriImmediate]
      rw [← h_sv]

/-- `ScalarOps.binary` fails closed with an asymmetric-type error when the left
operand classifies as `boolean` or `character` and the operand types differ. -/
private theorem scalarOps_binary_asym (rp : RefProg) (c : Choice) (op : BinOp)
    (lTy rTy : MirTy) (lImm rImm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (k : Miri.Interpreter.ScalarTypeClass)
    (h_cl : (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)).classify
      c (tyIdFor rp.types lTy) st = .ok k st)
    (h_k : k = .boolean ∨ k = .character)
    (h_ne : (tyIdFor rp.types lTy == tyIdFor rp.types rTy) = false) :
    Miri.Interpreter.ScalarOps.binary
        (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)) c
        (toMiriBinOp op) ⟨lImm, refLocalLayoutForTy rp.types lTy⟩
        ⟨rImm, refLocalLayoutForTy rp.types rTy⟩ st =
      .error (.invalidProgram "asymmetric scalar operand types") st := by
  dsimp only [Miri.Interpreter.ScalarOps.binary, bind, Bind.bind]
  change (EStateM.bind ((Miri.Interpreter.ExecutionMachine.scalarHooks
    (refExecCfg rp)).classify c (tyIdFor rp.types lTy)) _ st) = _
  rw [eStateM_bind_ok h_cl]
  cases h_k with
  | inl hb =>
    subst hb
    change (EStateM.bind
        (if (tyIdFor rp.types lTy == tyIdFor rp.types rTy) = true then
          EStateM.pure ()
        else EStateM.throw
          (StepError.invalidProgram "asymmetric scalar operand types")) _ st) = _
    rw [h_ne]; rfl
  | inr hc =>
    subst hc
    change (EStateM.bind
        (if (tyIdFor rp.types lTy == tyIdFor rp.types rTy) = true then
          EStateM.pure ()
        else EStateM.throw
          (StepError.invalidProgram "asymmetric scalar operand types")) _ st) = _
    rw [h_ne]; rfl

theorem scalarOps_binary_ref_eq (rp : RefProg) (c : Choice) (op : BinOp)
    (lTy rTy : MirTy) (lVal rVal : Val)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_lcv : checkVal lVal lTy = true) (h_lpr : isPrimitiveReadableTy lTy = true)
    (h_rcv : checkVal rVal rTy = true) (h_rpr : isPrimitiveReadableTy rTy = true)
    (h_lres : resolveTy rp.types (tyIdFor rp.types lTy) = some lTy) :
    let sc := Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)
    let lhs : RvalueImmTy Miri.Memory.Provenance :=
      ⟨valToMiriImmediate lTy lVal, refLocalLayoutForTy rp.types lTy⟩
    let rhs : RvalueImmTy Miri.Memory.Provenance :=
      ⟨valToMiriImmediate rTy rVal, refLocalLayoutForTy rp.types rTy⟩
    let res := Miri.Interpreter.ScalarOps.binary sc c (toMiriBinOp op) lhs rhs st
    match evalBinOp op lVal rVal with
    | .error k =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
    | .ok v =>
      ∃ resTy : MirTy,
        checkVal v resTy = true ∧
        isSupportedScalarOrUnitTy resTy = true ∧
        res = .ok ⟨valToMiriImmediate resTy v, refLocalLayoutForTy rp.types resTy⟩
          st := by
  intro sc lhs rhs res
  rw [← evalRefBinOp_eq op lVal rVal]
  -- Shape of the right operand.
  have h_rshape : (∃ rb, rTy = .bool ∧ rVal = .bool rb) ∨
      (∃ w₂ s₂ b₂, rTy = .int w₂ s₂ ∧ rVal = .scalar ⟨w₂, s₂, b₂⟩ ∧
        truncateBits w₂ b₂ = b₂) ∨
      (∃ rc, rTy = .char ∧ rVal = .char rc) ∨
      (∃ w₂ s₂ b₂ bo, rTy = .tuple [.int w₂ s₂, .bool] ∧
        rVal = .tuple [.scalar ⟨w₂, s₂, b₂⟩, .bool bo]) := by
    cases isPrimitiveReadableTy_cases h_rpr with
    | inl hb =>
      subst hb
      let ⟨rb, hv⟩ := checkVal_bool_inv h_rcv
      exact Or.inl ⟨rb, rfl, hv⟩
    | inr h1 =>
      cases h1 with
      | inl hi =>
        let ⟨w₂, s₂, hty⟩ := hi
        subst hty
        let ⟨b₂, hv, htr⟩ := checkVal_int_inv h_rcv
        exact Or.inr (Or.inl ⟨w₂, s₂, b₂, rfl, hv, htr⟩)
      | inr h2 =>
        cases h2 with
        | inl hc =>
          subst hc
          let ⟨rc, hv⟩ := checkVal_char_inv h_rcv
          exact Or.inr (Or.inr (Or.inl ⟨rc, rfl, hv⟩))
        | inr hp =>
          let ⟨w₂, s₂, hty⟩ := hp
          subst hty
          let ⟨b₂, bo, hv, _⟩ := checkVal_pair_inv h_rcv
          exact Or.inr (Or.inr (Or.inr ⟨w₂, s₂, b₂, bo, rfl, hv⟩))
  cases isPrimitiveReadableTy_cases h_lpr with
  | inl hb =>
    subst hb
    let ⟨lb, hlv⟩ := checkVal_bool_inv h_lcv
    subst hlv
    cases h_rshape with
    | inl hrb =>
      let ⟨rb, hty, hv⟩ := hrb
      subst hty; subst hv
      have h_unfold := scalarOps_bool_bin_unfold rp c op lb rb st
      change (match evalRefBinOp op (.bool lb) (.bool rb) with
        | .error k => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
        | .ok v =>
          ∃ resTy, checkVal v resTy = true ∧
            isSupportedScalarOrUnitTy resTy = true ∧
            res = .ok ⟨valToMiriImmediate resTy v,
              refLocalLayoutForTy rp.types resTy⟩ st)
      dsimp only [res, lhs, rhs, valToMiriImmediate]
      rw [h_unfold]
      cases op <;> cases lb <;> cases rb <;>
        first | exact ⟨.bool, rfl, rfl, rfl⟩ | exact ⟨_, _, rfl, rfl⟩
    | inr hr =>
      have h_ne : rTy ≠ .bool := by
        cases hr with
        | inl hi => let ⟨_, _, _, hty, _⟩ := hi; subst hty; intro h; cases h
        | inr h2 =>
          cases h2 with
          | inl hc => let ⟨_, hty, _⟩ := hc; subst hty; intro h; cases h
          | inr hp =>
            let ⟨_, _, _, _, hty, _⟩ := hp; subst hty; intro h; cases h
      have h_err : res =
          .error (.invalidProgram "asymmetric scalar operand types") st :=
        scalarOps_binary_asym rp c op .bool rTy _ _ st .boolean
          (scalarOps_classify_bool rp c st) (Or.inl rfl)
          (tyIdFor_beq_false_of_ne (resolveTy_tyIdFor_bool rp.types)
            (fun h => h_ne h.symm))
      have h_ev : evalRefBinOp op (.bool lb) rVal = .error .unsupported := by
        cases hr with
        | inl hi => let ⟨_, _, _, _, hv, _⟩ := hi; subst hv; rfl
        | inr h2 =>
          cases h2 with
          | inl hc => let ⟨_, _, hv⟩ := hc; subst hv; rfl
          | inr hp => let ⟨_, _, _, _, _, hv⟩ := hp; subst hv; rfl
      rw [h_ev]
      exact ⟨_, _, h_err, rfl⟩
  | inr h1 =>
    cases h1 with
    | inl hi =>
      let ⟨w₁, s₁, hty⟩ := hi
      subst hty
      let ⟨b₁, hlv, _⟩ := checkVal_int_inv h_lcv
      subst hlv
      cases h_rshape with
      | inl hrb =>
        let ⟨rb, hty, hv⟩ := hrb
        subst hty; subst hv
        have h_res_err :
            res = .error (.invalidProgram "integer binary RHS is not integral")
              st := by
          dsimp only [res, Miri.Interpreter.ScalarOps.binary, bind, Bind.bind,
            EStateM.bind, pure, Pure.pure, EStateM.pure, lhs, rhs]
          change (EStateM.bind (sc.classify c (tyIdFor rp.types (.int w₁ s₁)))
            _ st) = _
          rw [eStateM_bind_ok (scalarOps_classify_int rp c w₁ s₁ st)]
          change (EStateM.bind (sc.classify c (tyIdFor rp.types .bool)) _ st) = _
          rw [eStateM_bind_ok (scalarOps_classify_bool rp c st)]
          rfl
        exact ⟨_, _, h_res_err, rfl⟩
      | inr hr =>
        cases hr with
        | inl hri =>
          let ⟨w₂, s₂, b₂, hty, hv, _⟩ := hri
          subst hty; subst hv
          have h_same_ty :
              (tyIdFor rp.types (.int w₁ s₁) == tyIdFor rp.types (.int w₂ s₂)) =
                (IntWidth.beq w₁ w₂ && (s₁ == s₂)) := by
            cases h_b : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) with
            | true =>
              have h_eq := eq_of_intWidth_beq_and_signed h_b
              rw [h_eq.1, h_eq.2]
              exact beq_self_eq_true _
            | false =>
              cases h_tid : (tyIdFor rp.types (.int w₁ s₁) ==
                  tyIdFor rp.types (.int w₂ s₂)) with
              | false => rfl
              | true =>
                have h_eq := (tyIdFor_eq_iff_of_resolve
                  (resolveTy_tyIdFor_int rp.types w₁ s₁)
                  (resolveTy_tyIdFor_int rp.types w₂ s₂)).mp (eq_of_beq h_tid)
                injection h_eq with hw hs; subst hw; subst hs
                rw [IntWidth.beq_refl, beq_self_eq_true] at h_b
                cases h_b
          have h_res_unfold := scalarOps_int_bin_unfold rp c op w₁ w₂ s₁ s₂ b₁ b₂
            st
          dsimp only [res, lhs, rhs, valToMiriImmediate]
          rw [h_res_unfold, h_same_ty]
          cases h_sh : (toMiriBinOp op == .Shl || toMiriBinOp op == .ShlUnchecked ||
              toMiriBinOp op == .Shr || toMiriBinOp op == .ShrUnchecked) with
          | true =>
            dsimp only [Bool.not, ite_false_eq]
            rw [evalRefMiriBinOp_eq_match]
            exact refIntBinRes_handle rp op w₁ w₂ s₁ s₂ b₁ b₂ st _ rfl
          | false =>
            dsimp only [Bool.not, ite_true_eq]
            cases h_eq_ty : (IntWidth.beq w₁ w₂ && (s₁ == s₂)) with
            | true =>
              dsimp only [ite_true_eq]
              rw [evalRefMiriBinOp_eq_match]
              exact refIntBinRes_handle rp op w₁ w₂ s₁ s₂ b₁ b₂ st _ rfl
            | false =>
              dsimp only [ite_false_eq]
              have h_bne := miriIntValue_type_bne_of_false w₁ w₂ s₁ s₂ b₁ b₂
                h_eq_ty
              have h_err_ev :
                  evalRefBinOp op (.scalar ⟨w₁, s₁, b₁⟩) (.scalar ⟨w₂, s₂, b₂⟩) =
                    .error .unsupported := by
                rw [evalRefMiriBinOp_eq_match]
                dsimp only [Miri.Interpreter.IntegerOps.binary, bind, Bind.bind,
                  Except.bind]
                rw [integerOps_decode_eq, integerOps_decode_eq]
                dsimp only
                rw [h_sh]
                dsimp only [ite_false_eq]
                rw [h_bne]
                rfl
              rw [h_err_ev]
              exact ⟨_, _, rfl, rfl⟩
        | inr hr2 =>
          have h_rcp : rTy = .char ∨ ∃ w s, rTy = .tuple [.int w s, .bool] := by
            cases hr2 with
            | inl hc => let ⟨_, hty, _⟩ := hc; exact Or.inl hty
            | inr hp =>
              let ⟨w₂, s₂, _, _, hty, _⟩ := hp; exact Or.inr ⟨w₂, s₂, hty⟩
          have h_ev : evalRefBinOp op (.scalar ⟨w₁, s₁, b₁⟩) rVal =
              .error .unsupported := by
            cases hr2 with
            | inl hc => let ⟨_, _, hv⟩ := hc; subst hv; rfl
            | inr hp => let ⟨_, _, _, _, _, hv⟩ := hp; subst hv; rfl
          rw [h_ev]
          cases scalarOps_classify_char_or_pair rp c rTy st h_rcp with
          | inl he =>
            let ⟨e, h_e, h_fk⟩ := he
            have h_err : res = .error e st := by
              dsimp only [res, Miri.Interpreter.ScalarOps.binary, bind,
                Bind.bind, lhs, rhs]
              change (EStateM.bind
                (sc.classify c (tyIdFor rp.types (.int w₁ s₁))) _ st) = _
              rw [eStateM_bind_ok (scalarOps_classify_int rp c w₁ s₁ st)]
              change (EStateM.bind (sc.classify c (tyIdFor rp.types rTy)) _ st) =
                _
              rw [eStateM_bind_err h_e]
            exact ⟨_, _, h_err, h_fk⟩
          | inr hch =>
            have h_err : res =
                .error (.invalidProgram "integer binary RHS is not integral")
                  st := by
              dsimp only [res, Miri.Interpreter.ScalarOps.binary, bind,
                Bind.bind, lhs, rhs]
              change (EStateM.bind
                (sc.classify c (tyIdFor rp.types (.int w₁ s₁))) _ st) = _
              rw [eStateM_bind_ok (scalarOps_classify_int rp c w₁ s₁ st)]
              change (EStateM.bind (sc.classify c (tyIdFor rp.types rTy)) _ st) =
                _
              rw [eStateM_bind_ok hch]
              rfl
            exact ⟨_, _, h_err, rfl⟩
    | inr h2 =>
      cases h2 with
      | inl hc =>
        subst hc
        let ⟨l, hlv⟩ := checkVal_char_inv h_lcv
        subst hlv
        have h_asym : ∀ (rTy' : MirTy), rTy' ≠ .char →
            Miri.Interpreter.ScalarOps.binary sc c (toMiriBinOp op)
                ⟨.scalar (.fromChar l), refLocalLayoutForTy rp.types .char⟩
                ⟨valToMiriImmediate rTy' rVal, refLocalLayoutForTy rp.types rTy'⟩
                st =
              .error (.invalidProgram "asymmetric scalar operand types") st := by
          intro rTy' h_ne
          exact scalarOps_binary_asym rp c op .char rTy' _ _ st .character
            (scalarOps_classify_char rp c st h_lres) (Or.inr rfl)
            (tyIdFor_beq_false_of_ne h_lres (fun h => h_ne h.symm))
        cases h_rshape with
        | inl hrb =>
          let ⟨rb, hty, hv⟩ := hrb
          subst hty; subst hv
          exact ⟨_, _, h_asym .bool (fun h => by cases h), rfl⟩
        | inr hr =>
          cases hr with
          | inl hri =>
            let ⟨w₂, s₂, b₂, hty, hv, _⟩ := hri
            subst hty; subst hv
            exact ⟨_, _, h_asym (.int w₂ s₂) (fun h => by cases h), rfl⟩
          | inr hr2 =>
            cases hr2 with
            | inr hrp =>
              let ⟨w₂, s₂, b₂, bo, hty, hv⟩ := hrp
              subst hty; subst hv
              exact ⟨_, _, h_asym (.tuple [.int w₂ s₂, .bool])
                (fun h => by cases h), rfl⟩
            | inl hrc =>
              let ⟨r, hty, hv⟩ := hrc
              subst hty; subst hv
              have h_unfold := scalarOps_char_bin_unfold rp c op l r st h_lres
              dsimp only [res, lhs, rhs, valToMiriImmediate]
              rw [h_unfold]
              cases op <;>
                first
                | exact ⟨.bool, rfl, rfl, rfl⟩
                | exact ⟨.ordering, rfl, rfl, rfl⟩
                | exact ⟨_, _, rfl, rfl⟩
      | inr hp =>
        let ⟨w₁, s₁, hty⟩ := hp
        subst hty
        let ⟨b₁, bo, hlv, _⟩ := checkVal_pair_inv h_lcv
        subst hlv
        have h_cl :
            sc.classify c (tyIdFor rp.types (.tuple [.int w₁ s₁, .bool])) st =
              .error (.invalidProgram "non-scalar operand type") st := by
          dsimp only [sc, Miri.Interpreter.ExecutionMachine.scalarHooks,
            Miri.Interpreter.ExecutionScalar.hooks, refExecCfg,
            Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
            refScalarLeaves]
          rw [h_lres]
        have h_err : res = .error (.invalidProgram "non-scalar operand type") st := by
          dsimp only [res, Miri.Interpreter.ScalarOps.binary, bind, Bind.bind,
            lhs, rhs]
          change (EStateM.bind (sc.classify c
            (tyIdFor rp.types (.tuple [.int w₁ s₁, .bool]))) _ st) = _
          rw [eStateM_bind_err h_cl]
        have h_ev : evalRefBinOp op (.tuple [.scalar ⟨w₁, s₁, b₁⟩, .bool bo]) rVal =
            .error .unsupported := by
          cases rVal <;> rfl
        rw [h_ev]
        exact ⟨_, _, h_err, rfl⟩

private theorem scalarOps_int_un_unfold (rp : RefProg) (c : Choice)
    (op : UnOp) (w : IntWidth) (s : Bool) (bits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    let sc := Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)
    let opImm : RvalueImmTy Miri.Memory.Provenance :=
      ⟨.scalar (.fromScalarInt (miriScalar w bits)),
        refLocalLayoutForTy rp.types (.int w s)⟩
    Miri.Interpreter.ScalarOps.unary sc c (toMiriUnOp op) opImm st =
      match Miri.Interpreter.IntegerOps.unary (toMiriUnOp op)
          (miriIntValue ⟨w, s, bits⟩) with
      | .error err => .error (Miri.Interpreter.ScalarOps.integerError err) st
      | .ok scv =>
        .ok ⟨.scalar (.fromScalarInt scv),
          refLocalLayoutForTy rp.types (.int w s)⟩ st := by
  intro sc opImm
  dsimp only [Miri.Interpreter.ScalarOps.unary, bind, Bind.bind, opImm]
  change (EStateM.bind (sc.classify c (tyIdFor rp.types (.int w s))) _ st) = _
  rw [eStateM_bind_ok (scalarOps_classify_int rp c w s st)]
  dsimp only
  cases w <;> (
    change (EStateM.bind (EStateM.pure (miriIntValue ⟨_, s, bits⟩)) _ st) = _
    rw [eStateM_bind_pure]
    cases Miri.Interpreter.IntegerOps.unary (toMiriUnOp op)
        (miriIntValue ⟨_, s, bits⟩) <;> rfl)

theorem scalarOps_unary_ref_eq (rp : RefProg) (c : Choice) (op : UnOp)
    (ty : MirTy) (v : Val)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_cv : checkVal v ty = true) (h_pr : isPrimitiveReadableTy ty = true) :
    let sc := Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp)
    let opImm : RvalueImmTy Miri.Memory.Provenance :=
      ⟨valToMiriImmediate ty v, refLocalLayoutForTy rp.types ty⟩
    let res := Miri.Interpreter.ScalarOps.unary sc c (toMiriUnOp op) opImm st
    match evalUnOp op v with
    | .error k =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
    | .ok u =>
      ∃ resTy : MirTy,
        checkVal u resTy = true ∧
        isSupportedScalarOrUnitTy resTy = true ∧
        res = .ok ⟨valToMiriImmediate resTy u, refLocalLayoutForTy rp.types resTy⟩
          st := by
  intro sc opImm res
  rw [← evalRefUnOp_eq op v]
  have h_other : (ty = .char ∨ ∃ w s, ty = .tuple [.int w s, .bool]) →
      evalRefUnOp op v = .error .unsupported →
      match evalRefUnOp op v with
      | .error k =>
        ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
      | .ok u =>
        ∃ resTy : MirTy,
          checkVal u resTy = true ∧
          isSupportedScalarOrUnitTy resTy = true ∧
          res = .ok ⟨valToMiriImmediate resTy u,
            refLocalLayoutForTy rp.types resTy⟩ st := by
    intro h_t h_ev
    rw [h_ev]
    dsimp only
    cases scalarOps_classify_char_or_pair rp c ty st h_t with
    | inl he =>
      let ⟨e, h_e, h_fk⟩ := he
      have h_err : res = .error e st := by
        dsimp only [res, Miri.Interpreter.ScalarOps.unary, bind, Bind.bind,
          opImm]
        change (EStateM.bind (sc.classify c (tyIdFor rp.types ty)) _ st) = _
        rw [eStateM_bind_err h_e]
      exact ⟨_, _, h_err, h_fk⟩
    | inr hch =>
      have h_err : res =
          .error (.invalidProgram "invalid character unary operation") st := by
        dsimp only [res, Miri.Interpreter.ScalarOps.unary, bind, Bind.bind,
          opImm]
        change (EStateM.bind (sc.classify c (tyIdFor rp.types ty)) _ st) = _
        rw [eStateM_bind_ok hch]
        rfl
      exact ⟨_, _, h_err, rfl⟩
  cases isPrimitiveReadableTy_cases h_pr with
  | inl hb =>
    subst hb
    let ⟨b, hv⟩ := checkVal_bool_inv h_cv; subst hv
    have h_unfold :
        res =
          if toMiriUnOp op != .Not then
            .error (.invalidProgram "invalid boolean unary operation") st
          else
            .ok ⟨.scalar (.fromBool (!b)), refLocalLayoutForTy rp.types .bool⟩
              st := by
      dsimp only [res, Miri.Interpreter.ScalarOps.unary, bind, Bind.bind,
        EStateM.bind, pure, Pure.pure, EStateM.pure, opImm]
      change (EStateM.bind (sc.classify c (tyIdFor rp.types .bool)) _ st) = _
      rw [eStateM_bind_ok (scalarOps_classify_bool rp c st)]
      cases b <;> cases op <;> rfl
    rw [h_unfold]
    cases op <;> cases b <;>
      first | exact ⟨.bool, rfl, rfl, rfl⟩ | exact ⟨_, _, rfl, rfl⟩
  | inr h1 =>
    cases h1 with
    | inl hi =>
      let ⟨w, s, hty⟩ := hi
      subst hty
      let ⟨bits, hv, _⟩ := checkVal_int_inv h_cv; subst hv
      have h_unfold := scalarOps_int_un_unfold rp c op w s bits st
      dsimp only [res, opImm, valToMiriImmediate]
      rw [h_unfold]
      have h_ev_int :
          evalRefUnOp op (.scalar ⟨w, s, bits⟩) =
            match Miri.Interpreter.IntegerOps.unary (toMiriUnOp op)
                (miriIntValue ⟨w, s, bits⟩) with
            | .ok scv => .ok (.scalar ⟨w, s, scv.data⟩)
            | .error (.undefinedBehavior _) => .error .undefined
            | .error _ => .error .unsupported := by
        cases op <;> rfl
      rw [h_ev_int]
      cases h_u : Miri.Interpreter.IntegerOps.unary (toMiriUnOp op)
          (miriIntValue ⟨w, s, bits⟩) with
      | error err =>
        cases err with
        | undefinedBehavior _ => exact ⟨_, _, rfl, rfl⟩
        | asymmetricTypes _ _ | invalidBinaryOperator _
        | invalidUnaryOperator _ _ =>
          exact ⟨_, _, rfl, rfl⟩
        | scalar se =>
          have h_no := integerOps_unary_no_invalidBool_invalidChar op w s bits
            se h_u
          cases se with
          | invalidBool _ | invalidChar _ => exact False.elim h_no
          | _ => exact ⟨_, _, rfl, rfl⟩
      | ok scv =>
        let ⟨h_sv, h_tr⟩ := integerOps_unary_wf op w s bits scv h_u
        refine ⟨.int w s, checkVal_scalar_of_trunc w s scv.data h_tr, rfl, ?_⟩
        dsimp only [valToMiriImmediate]
        rw [← h_sv]
    | inr h2 =>
      cases h2 with
      | inl hc =>
        subst hc
        let ⟨ch, hv⟩ := checkVal_char_inv h_cv; subst hv
        exact h_other (Or.inl rfl) (by cases op <;> rfl)
      | inr hp =>
        let ⟨w, s, hty⟩ := hp
        subst hty
        let ⟨bits, bo, hv, _⟩ := checkVal_pair_inv h_cv; subst hv
        exact h_other (Or.inr ⟨w, s, rfl⟩) (by cases op <;> rfl)

/-! ## Section 5: `Discriminant` Helpers -/

private theorem discrHooks_discriminantLayout (rp : RefProg) (c : Choice)
    (ty : MirTy) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types ty) = some ty) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).discriminantLayout
        c (tyIdFor rp.types ty) st =
      match ty with
      | .enum ety =>
        if refEnumAdmitted ety then
          .ok (refLocalLayoutForTy rp.types (.int ety.discrWidth ety.discrSigned)) st
        else
          .error (.unsupported "unadmitted enum in discriminantLayout") st
      | .ordering => .ok (refLocalLayoutForTy rp.types (.int .i8 true)) st
      | _ => .error (.unsupported "discriminant on non-enum type") st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refDiscriminantLeaves]
  rw [h_res]
  cases ty <;> rfl

private theorem discrHooks_projectRead_imm_enum (rp : RefProg) (c : Choice)
    (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.enum ety)) = some (.enum ety)) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).projectRead
        c ⟨.immediate imm, refLocalLayoutForTy rp.types (.enum ety)⟩ 0 st =
      .ok ⟨.immediate imm, refLocalLayoutForTy rp.types (.int tagW tagS)⟩ st := by
  have h_proj_field :
      Miri.Interpreter.projectField (refProjectionCx rp.types)
          ⟨.immediate imm, refLocalLayoutForTy rp.types (.enum ety)⟩ 0 =
        .ok ⟨.immediate imm, refLocalLayoutForTy rp.types (.int tagW tagS)⟩ := by
    dsimp only [Miri.Interpreter.projectField, refProjectionCx,
      refProjectFieldLayout, refLocalLayoutForTy, refLayoutDataForTy,
      refEnumLayoutData, Miri.Interpreter.OpTy.offsetWithMeta,
      Miri.Interpreter.projectionImmediateOffset,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    rw [h_res]
    dsimp only
    rw [h_tr]
    cases tagW <;> cases tagS <;> cases imm <;> rfl
  dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    Miri.Interpreter.ExecutionMachine.operandHooks,
    Miri.Interpreter.OperandMachine.field, bind, Bind.bind]
  change (EStateM.bind (EStateM.pure (refProjectionCx rp.types)) _ st) = _
  rw [eStateM_bind_pure, h_proj_field]
  rfl

/-- Shared core of `readDiscriminant` on an initialized scalar-tag immediate:
`ty` (a fieldless enum or `core::cmp::Ordering`) is laid out as the
scalar-tagged enum descriptor `ety`, and the discriminant hooks agree with
`ety` on `ty`'s `TyId`. -/
private theorem discrHooks_readDiscriminant_scalar_core (rp : RefProg)
    (c : Choice) (ty : MirTy) (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (variant disc : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_lay : refLayoutDataForTy ty = refEnumLayoutData ety)
    (h_dl : (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).discriminantLayout c (tyIdFor rp.types ty) st =
      .ok (refLocalLayoutForTy rp.types
        (.int ety.discrWidth ety.discrSigned)) st)
    (h_pr : ∀ imm, (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).projectRead c
          ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩ 0 st =
      .ok ⟨.immediate imm, refLocalLayoutForTy rp.types (.int tagW tagS)⟩ st)
    (h_vf : ∀ bits, (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).variantForDiscriminant c (tyIdFor rp.types ty)
          bits st =
      .ok (refFindDiscrVariant? bits ety.discriminants) st)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
        ⟨.immediate (.scalar (.fromScalarInt
            (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy rp.types ty⟩ st =
      .ok variant st := by
  let dh := Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)
  have h_tl : dh.tagLayout c (.Union (value := .Int (toMiriInteger tagW) tagS)) st =
      .ok (refLocalLayoutForTy rp.types (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)) st := rfl
  have h_pr' := h_pr
    (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))))
  have h_ri : dh.readImmediate c
      ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
        refLocalLayoutForTy rp.types (.int tagW tagS)⟩ st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))),
        refLocalLayoutForTy rp.types (.int tagW tagS)⟩ st :=
    readImmediate_imm_int_ok tagW tagS (BitVec.ofNat 128 disc) rp.types st h_pmd
  have h_vars : (refLocalLayoutForTy rp.types ty).layout.variants =
      .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct 0
        (ety.discriminants.map (fun _ => refInhabitedVariantLayout)).toArray := by
    dsimp only [refLocalLayoutForTy]
    rw [h_lay]
    dsimp only [refEnumLayoutData]
    rw [h_tr]
  have h_t_sz : (refLocalLayoutForTy rp.types
      (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)).layout.size = toMiriSize tagW := by
    cases tagW <;> cases tagS <;> rfl
  have h_v_sz : (refLocalLayoutForTy rp.types (.int tagW tagS)).layout.size = toMiriSize tagW := by
    cases tagW <;> cases tagS <;> rfl
  have h_t_sgn : (refLocalLayoutForTy rp.types
      (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)).layout.backendRepr.isSigned = .ok tagS := by
    cases tagW <;> cases tagS <;> rfl
  have h_v_sgn : (refLocalLayoutForTy rp.types (.int tagW tagS)).layout.backendRepr.isSigned = .ok tagS := by
    cases tagW <;> cases tagS <;> rfl
  have h_dl_sz : (refLocalLayoutForTy rp.types
      (.int ety.discrWidth ety.discrSigned)).layout.size = toMiriSize ety.discrWidth := by
    cases ety.discrWidth <;> cases ety.discrSigned <;> rfl
  have h_vr : (Miri.ABI.Scalar.Union (value := .Int (toMiriInteger tagW) tagS)).validRange
      dh.runtimeTarget = .ok (refFullWrappingRangeSize (toMiriSize tagW)) := by
    cases tagW <;> cases tagS <;> rfl
  let ⟨_, _, h_tag_all⟩ := enumAdmitted_parts h_adm
  rw [h_tr] at h_tag_all
  have h_tag_ok : tagBitsToDiscrBits tagW tagS ety.discrWidth
      (truncateBits tagW (BitVec.ofNat 128 disc)) = BitVec.ofNat 128 disc :=
    eq_of_beq (list_all_mirGetElem?
      (p := fun d =>
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW (BitVec.ofNat 128 d)) == BitVec.ofNat 128 d)
      h_tag_all h_get_d)
  have h_vf' : dh.variantForDiscriminant c (tyIdFor rp.types ty)
      (BitVec.ofNat 128 disc) st = .ok (some variant) st := by
    have h := h_vf (BitVec.ofNat 128 disc)
    rw [refFindDiscrVariant?_eq, findDiscrVariant?_of_enumAdmitted h_adm h_get_d] at h
    exact h
  dsimp only [Miri.Interpreter.Discriminant.readDiscriminant, bind, Bind.bind]
  change (EStateM.bind (dh.discriminantLayout c (tyIdFor rp.types ty)) _ st) = _
  rw [eStateM_bind_ok h_dl]
  rw [h_vars]
  change (EStateM.bind (dh.tagLayout c (.Union (value := .Int (toMiriInteger tagW) tagS))) _ st) = _
  rw [eStateM_bind_ok h_tl]
  change (EStateM.bind (dh.projectRead c _ 0) _ st) = _
  rw [eStateM_bind_ok h_pr']
  change (EStateM.bind (dh.readImmediate c _) _ st) = _
  rw [eStateM_bind_ok h_ri]
  rw [h_t_sz, h_v_sz, bne_self_eq_false]
  dsimp only [ite_false_eq]
  change (EStateM.bind
      (match (refLocalLayoutForTy rp.types (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)).layout.backendRepr.isSigned with
       | .ok v => EStateM.pure v | .error _ => EStateM.throw (StepError.invalidProgram "discriminant requires scalar backend representation")) _ st) = _
  rw [h_t_sgn, eStateM_bind_pure]
  change (EStateM.bind
      (match (refLocalLayoutForTy rp.types (.int tagW tagS)).layout.backendRepr.isSigned with
       | .ok v => EStateM.pure v | .error _ => EStateM.throw (StepError.invalidProgram "discriminant requires scalar backend representation")) _ st) = _
  rw [h_v_sgn, eStateM_bind_pure]
  rw [bne_self_eq_false]
  dsimp only [ite_false_eq]
  have h_tb : (miriScalar tagW (BitVec.ofNat 128 disc)).toBits (toMiriSize tagW) =
      .ok (truncateBits tagW (BitVec.ofNat 128 disc)) :=
    scalarInt_toBits_miriScalar tagW (BitVec.ofNat 128 disc)
  change (EStateM.bind (EStateM.pure (Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance) (miriScalar tagW (BitVec.ofNat 128 disc)))) _ st) = _
  rw [eStateM_bind_pure]
  change (EStateM.bind (EStateM.pure (Miri.Memory.ScalarIntCastResult.integer (miriScalar tagW (BitVec.ofNat 128 disc)))) _ st) = _
  rw [eStateM_bind_pure]
  dsimp only
  rw [h_tb]
  dsimp only [Except.mapError]
  change (EStateM.bind (EStateM.pure (truncateBits tagW (BitVec.ofNat 128 disc))) _ st) = _
  rw [eStateM_bind_pure]
  change (EStateM.bind
      (match (Miri.ABI.Scalar.Union (value := .Int (toMiriInteger tagW) tagS)).validRange dh.runtimeTarget with
       | .ok v => EStateM.pure v | .error _ => _) _ st) = _
  rw [h_vr, eStateM_bind_pure,
    wrappingRange_full_contains_truncateBits tagW (BitVec.ofNat 128 disc),
    ite_not_true_eq]
  have h_uninh_v :
      (refLocalLayoutForTy rp.types ty).layout.isVariantUninhabited variant = false := by
    dsimp only [refLocalLayoutForTy]
    rw [h_lay]
    exact refEnum_isVariantUninhabited_false ety tagW tagS variant h_tr
      (mirGetElem?_lt_of_some h_get_d)
  cases tagS with
  | false =>
    dsimp only [ite_false_eq, pure, Pure.pure]
    rw [eStateM_bind_pure, h_dl_sz, size_truncate_eq]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure]
    have h_tag_f : truncateBits ety.discrWidth (truncateBits tagW (BitVec.ofNat 128 disc)) =
        BitVec.ofNat 128 disc := by
      have h_eq : tagBitsToDiscrBits tagW false ety.discrWidth
          (truncateBits tagW (BitVec.ofNat 128 disc)) =
          truncateBits ety.discrWidth (truncateBits tagW (BitVec.ofNat 128 disc)) := by
        dsimp only [tagBitsToDiscrBits]
        rw [ite_false_eq, truncateBits_idem]
      rw [← h_eq]; exact h_tag_ok
    rw [h_tag_f]
    change (EStateM.bind (dh.variantForDiscriminant c (tyIdFor rp.types ty)
      (BitVec.ofNat 128 disc)) _ st) = _
    rw [eStateM_bind_ok h_vf']
    dsimp only
    rw [eStateM_bind_pure, h_uninh_v]
    rfl
  | true =>
    dsimp only [ite_true_eq, pure, Pure.pure]
    rw [size_signExtend_eq]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure, eStateM_bind_pure, h_dl_sz, size_truncate_eq, bitVec_ofInt_eq]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure]
    have h_tag_t : truncateBits ety.discrWidth
        (bvOfInt 128 (signExtendBits tagW (truncateBits tagW (BitVec.ofNat 128 disc)))) =
        BitVec.ofNat 128 disc := h_tag_ok
    rw [h_tag_t]
    change (EStateM.bind (dh.variantForDiscriminant c (tyIdFor rp.types ty)
      (BitVec.ofNat 128 disc)) _ st) = _
    rw [eStateM_bind_ok h_vf']
    dsimp only
    rw [eStateM_bind_pure, h_uninh_v]
    rfl

/-- Shared core of `readDiscriminant` on an uninitialized immediate of a type
`ty` laid out as the scalar-tagged enum descriptor `ety`. -/
private theorem discrHooks_readDiscriminant_scalar_uninit_core (rp : RefProg)
    (c : Choice) (ty : MirTy) (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_lay : refLayoutDataForTy ty = refEnumLayoutData ety)
    (h_dl : (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).discriminantLayout c (tyIdFor rp.types ty) st =
      .ok (refLocalLayoutForTy rp.types
        (.int ety.discrWidth ety.discrSigned)) st)
    (h_pr : (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).projectRead c
          ⟨.immediate .uninit, refLocalLayoutForTy rp.types ty⟩ 0 st =
      .ok ⟨.immediate .uninit, refLocalLayoutForTy rp.types (.int tagW tagS)⟩
        st)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    ∃ msg,
      Miri.Interpreter.Discriminant.readDiscriminant
          (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
          ⟨.immediate .uninit, refLocalLayoutForTy rp.types ty⟩ st =
        .error (.undefinedBehavior msg) st := by
  let dh := Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)
  have h_tl : dh.tagLayout c (.Union (value := .Int (toMiriInteger tagW) tagS)) st =
      .ok (refLocalLayoutForTy rp.types (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)) st := rfl
  let ⟨msg, h_ri⟩ := readImmediate_imm_int_uninit tagW tagS rp.types st h_pmd
  have h_ri' : dh.readImmediate c
      ⟨.immediate .uninit, refLocalLayoutForTy rp.types (.int tagW tagS)⟩ st =
      .error (.undefinedBehavior msg) st := h_ri
  have h_vars : (refLocalLayoutForTy rp.types ty).layout.variants =
      .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct 0
        (ety.discriminants.map (fun _ => refInhabitedVariantLayout)).toArray := by
    dsimp only [refLocalLayoutForTy]
    rw [h_lay]
    dsimp only [refEnumLayoutData]
    rw [h_tr]
  refine ⟨msg, ?_⟩
  dsimp only [Miri.Interpreter.Discriminant.readDiscriminant, bind, Bind.bind]
  change (EStateM.bind (dh.discriminantLayout c (tyIdFor rp.types ty)) _ st) = _
  rw [eStateM_bind_ok h_dl]
  rw [h_vars]
  change (EStateM.bind (dh.tagLayout c (.Union (value := .Int (toMiriInteger tagW) tagS))) _ st) = _
  rw [eStateM_bind_ok h_tl]
  change (EStateM.bind (dh.projectRead c _ 0) _ st) = _
  rw [eStateM_bind_ok h_pr]
  change (EStateM.bind (dh.readImmediate c _) _ st) = _
  rw [eStateM_bind_err h_ri']

/-- Shared core of `discriminantForVariant` for a type `ty` whose discriminant
hooks return the admitted enum descriptor `ety`'s discriminant `disc` for
`variant`. -/
private theorem discrHooks_discriminantForVariant_core (rp : RefProg)
    (c : Choice) (ty : MirTy) (ety : EnumTy) (variant disc : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_adm : enumAdmitted ety = true)
    (h_dl : (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).discriminantLayout c (tyIdFor rp.types ty) st =
      .ok (refLocalLayoutForTy rp.types
        (.int ety.discrWidth ety.discrSigned)) st)
    (h_dv : (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).discriminantValue c (tyIdFor rp.types ty) variant
          st =
      .ok (some (tyIdFor rp.types (.int ety.discrWidth ety.discrSigned),
        BitVec.ofNat 128 disc)) st)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc) :
    Miri.Interpreter.Discriminant.discriminantForVariant
        (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
        (tyIdFor rp.types ty) variant st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar ety.discrWidth (BitVec.ofNat 128 disc))),
        refLocalLayoutForTy rp.types (.int ety.discrWidth ety.discrSigned)⟩ st := by
  let dh := Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)
  let ⟨h_all, _, _⟩ := enumAdmitted_parts h_adm
  have hd_blt : Nat.blt disc (Nat.pow 2 ety.discrWidth.bitWidth) = true :=
    list_all_mirGetElem? (p := fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth))
      h_all h_get_d
  have hd_mod : disc < Nat.pow 2 ety.discrWidth.bitWidth :=
    Nat.blt_eq.mp hd_blt
  have hd_u128 : disc < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hd_mod (intWidth_pow_le_128 ety.discrWidth)
  have h_trunc_eq :
      truncateBits ety.discrWidth (BitVec.ofNat 128 disc) = BitVec.ofNat 128 disc := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_truncateBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd_u128]
    exact Nat.mod_eq_of_lt hd_mod
  have h_from_uint :
      Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
        (BitVec.ofNat 128 disc) (toMiriSize ety.discrWidth) =
        .ok (.fromScalarInt (miriScalar ety.discrWidth (BitVec.ofNat 128 disc))) := by
    dsimp only [Miri.Memory.Scalar.fromUInt]
    rw [tryFromUInt_eq_truncateFromUInt,
      truncateFromUInt_eq_miriScalar ety.discrWidth (BitVec.ofNat 128 disc),
      h_trunc_eq, bne_self_eq_false]
    rfl
  have h_dl_sz : (refLocalLayoutForTy rp.types
      (.int ety.discrWidth ety.discrSigned)).layout.size = toMiriSize ety.discrWidth := by
    cases ety.discrWidth <;> cases ety.discrSigned <;> rfl
  dsimp only [Miri.Interpreter.Discriminant.discriminantForVariant, bind, Bind.bind, pure, Pure.pure]
  change (EStateM.bind (dh.discriminantLayout c (tyIdFor rp.types ty)) _ st) = _
  rw [eStateM_bind_ok h_dl]
  change (EStateM.bind (dh.discriminantValue c (tyIdFor rp.types ty) variant) _ st) = _
  rw [eStateM_bind_ok h_dv]
  have h_ne_ty :
      (tyIdFor rp.types (.int ety.discrWidth ety.discrSigned) !=
        (refLocalLayoutForTy rp.types (.int ety.discrWidth ety.discrSigned)).ty) = false :=
    bne_self_eq_false _
  simp only [h_ne_ty, Bool.false_eq_true, ite_false]
  rw [eStateM_bind_pure, h_dl_sz, h_from_uint]
  rfl

private theorem discrHooks_discriminantLayout_enum (rp : RefProg) (c : Choice)
    (ety : EnumTy) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_adm : enumAdmitted ety = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.enum ety)) = some (.enum ety)) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).discriminantLayout c (tyIdFor rp.types (.enum ety)) st =
      .ok (refLocalLayoutForTy rp.types
        (.int ety.discrWidth ety.discrSigned)) st := by
  have h_ref_adm : refEnumAdmitted ety = true := by
    rw [refEnumAdmitted_eq]; exact h_adm
  rw [discrHooks_discriminantLayout rp c (.enum ety) st h_res]
  dsimp only; rw [h_ref_adm]; rfl

private theorem discrHooks_variantForDiscriminant_enum (rp : RefProg)
    (c : Choice) (ety : EnumTy) (bits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.enum ety)) = some (.enum ety)) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).variantForDiscriminant c (tyIdFor rp.types (.enum ety))
          bits st =
      .ok (refFindDiscrVariant? bits ety.discriminants) st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks,
    refExecCfg, Miri.Interpreter.ExecutionMachine.withValidation,
    refExecutionConfig, refDiscriminantLeaves]
  rw [h_res]

private theorem discrHooks_readDiscriminant_scalar_ok (rp : RefProg) (c : Choice)
    (ety : EnumTy) (tagW : IntWidth) (tagS : Bool) (variant disc : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.enum ety)) = some (.enum ety))
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy rp.types (.enum ety)⟩ st =
      .ok variant st :=
  discrHooks_readDiscriminant_scalar_core rp c (.enum ety) ety tagW tagS
    variant disc st h_tr h_adm rfl
    (discrHooks_discriminantLayout_enum rp c ety st h_adm h_res)
    (fun imm =>
      discrHooks_projectRead_imm_enum rp c ety tagW tagS imm st h_tr h_res)
    (fun bits => discrHooks_variantForDiscriminant_enum rp c ety bits st h_res)
    h_get_d h_pmd

private theorem discrHooks_readDiscriminant_scalar_uninit_ub (rp : RefProg) (c : Choice)
    (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.enum ety)) = some (.enum ety))
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    ∃ msg,
      Miri.Interpreter.Discriminant.readDiscriminant
          (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
          ⟨.immediate .uninit, refLocalLayoutForTy rp.types (.enum ety)⟩ st =
        .error (.undefinedBehavior msg) st :=
  discrHooks_readDiscriminant_scalar_uninit_core rp c (.enum ety) ety tagW tagS
    st h_tr rfl
    (discrHooks_discriminantLayout_enum rp c ety st h_adm h_res)
    (discrHooks_projectRead_imm_enum rp c ety tagW tagS .uninit st h_tr h_res)
    h_pmd

private theorem discrHooks_discriminantForVariant_ok (rp : RefProg) (c : Choice)
    (ety : EnumTy) (variant disc : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_adm : enumAdmitted ety = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.enum ety)) = some (.enum ety))
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc) :
    Miri.Interpreter.Discriminant.discriminantForVariant
        (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
        (tyIdFor rp.types (.enum ety)) variant st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar ety.discrWidth (BitVec.ofNat 128 disc))),
        refLocalLayoutForTy rp.types (.int ety.discrWidth ety.discrSigned)⟩ st := by
  have h_dv : (Miri.Interpreter.ExecutionMachine.discriminantHooks
      (refExecCfg rp)).discriminantValue c (tyIdFor rp.types (.enum ety))
        variant st =
      .ok (some (tyIdFor rp.types (.int ety.discrWidth ety.discrSigned),
        BitVec.ofNat 128 disc)) st := by
    dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks,
      refExecCfg, Miri.Interpreter.ExecutionMachine.withValidation,
      refExecutionConfig, refDiscriminantLeaves]
    rw [h_res]
    dsimp only
    rw [h_get_d]
  exact discrHooks_discriminantForVariant_core rp c (.enum ety) ety variant disc
    st h_adm (discrHooks_discriminantLayout_enum rp c ety st h_adm h_res) h_dv
    h_get_d

/-! ### `core::cmp::Ordering` discriminants

$M_{\text{ref}}$ lays out `MirTy.ordering` as `refEnumLayoutData
refOrderingEnumTy`, and the `.ordering` arms of the discriminant hooks mirror
the enum arms on `refOrderingEnumTy`, so these lemmas instantiate the
scalar-tag cores above with `ety := refOrderingEnumTy`. -/

/-- Variant index of a `core::cmp::Ordering` value in `refOrderingEnumTy`. -/
noncomputable def orderingVariantIdx : OrderingVal → Nat
  | .less => 0
  | .equal => 1
  | .greater => 2

theorem valToMiriImmediate_ordering (ord : OrderingVal) :
    valToMiriImmediate .ordering (.ordering ord) =
      .scalar (.fromScalarInt
        (miriScalar .i8 (BitVec.ofNat 128 (orderingTagBits ord)))) := by
  cases ord <;> rfl

private theorem refOrderingEnumTy_admitted :
    enumAdmitted refOrderingEnumTy = true := rfl

private theorem refOrderingEnumTy_getElem? (ord : OrderingVal) :
    MirSemantics.getElem? refOrderingEnumTy.discriminants
        (orderingVariantIdx ord) = some (orderingTagBits ord) := by
  cases ord <;> rfl

private theorem discrHooks_discriminantLayout_ordering (rp : RefProg)
    (c : Choice) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .ordering) = some .ordering) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).discriminantLayout c (tyIdFor rp.types .ordering) st =
      .ok (refLocalLayoutForTy rp.types
        (.int refOrderingEnumTy.discrWidth refOrderingEnumTy.discrSigned)) st := by
  rw [discrHooks_discriminantLayout rp c .ordering st h_res]
  rfl

private theorem discrHooks_projectRead_imm_ordering (rp : RefProg) (c : Choice)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .ordering) = some .ordering) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).projectRead
        c ⟨.immediate imm, refLocalLayoutForTy rp.types .ordering⟩ 0 st =
      .ok ⟨.immediate imm, refLocalLayoutForTy rp.types (.int .i8 true)⟩ st := by
  have h_proj_field :
      Miri.Interpreter.projectField (refProjectionCx rp.types)
          ⟨.immediate imm, refLocalLayoutForTy rp.types .ordering⟩ 0 =
        .ok ⟨.immediate imm, refLocalLayoutForTy rp.types (.int .i8 true)⟩ := by
    dsimp only [Miri.Interpreter.projectField, refProjectionCx,
      refProjectFieldLayout, refLocalLayoutForTy, refLayoutDataForTy,
      refEnumLayoutData, Miri.Interpreter.OpTy.offsetWithMeta,
      Miri.Interpreter.projectionImmediateOffset,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    rw [h_res]
    cases imm <;> rfl
  dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    Miri.Interpreter.ExecutionMachine.operandHooks,
    Miri.Interpreter.OperandMachine.field, bind, Bind.bind]
  change (EStateM.bind (EStateM.pure (refProjectionCx rp.types)) _ st) = _
  rw [eStateM_bind_pure, h_proj_field]
  rfl

private theorem discrHooks_variantForDiscriminant_ordering (rp : RefProg)
    (c : Choice) (bits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .ordering) = some .ordering) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).variantForDiscriminant c (tyIdFor rp.types .ordering)
          bits st =
      .ok (refFindDiscrVariant? bits refOrderingEnumTy.discriminants) st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks,
    refExecCfg, Miri.Interpreter.ExecutionMachine.withValidation,
    refExecutionConfig, refDiscriminantLeaves]
  rw [h_res]

private theorem discrHooks_readDiscriminant_ordering_ok (rp : RefProg) (c : Choice)
    (ord : OrderingVal) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .ordering) = some .ordering)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
        ⟨.immediate (valToMiriImmediate .ordering (.ordering ord)),
          refLocalLayoutForTy rp.types .ordering⟩ st =
      .ok (orderingVariantIdx ord) st := by
  rw [valToMiriImmediate_ordering]
  exact discrHooks_readDiscriminant_scalar_core rp c .ordering
    refOrderingEnumTy .i8 true (orderingVariantIdx ord) (orderingTagBits ord)
    st rfl refOrderingEnumTy_admitted rfl
    (discrHooks_discriminantLayout_ordering rp c st h_res)
    (fun imm => discrHooks_projectRead_imm_ordering rp c imm st h_res)
    (fun bits => discrHooks_variantForDiscriminant_ordering rp c bits st h_res)
    (refOrderingEnumTy_getElem? ord) h_pmd

private theorem discrHooks_readDiscriminant_ordering_uninit_ub (rp : RefProg)
    (c : Choice) (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .ordering) = some .ordering)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    ∃ msg,
      Miri.Interpreter.Discriminant.readDiscriminant
          (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
          ⟨.immediate .uninit, refLocalLayoutForTy rp.types .ordering⟩ st =
        .error (.undefinedBehavior msg) st :=
  discrHooks_readDiscriminant_scalar_uninit_core rp c .ordering
    refOrderingEnumTy .i8 true st rfl rfl
    (discrHooks_discriminantLayout_ordering rp c st h_res)
    (discrHooks_projectRead_imm_ordering rp c .uninit st h_res) h_pmd

private theorem discrHooks_discriminantForVariant_ordering_ok (rp : RefProg)
    (c : Choice) (ord : OrderingVal)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .ordering) = some .ordering) :
    Miri.Interpreter.Discriminant.discriminantForVariant
        (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
        (tyIdFor rp.types .ordering) (orderingVariantIdx ord) st =
      .ok ⟨.scalar (.fromScalarInt
          (miriScalar .i8 (BitVec.ofNat 128 (orderingTagBits ord)))),
        refLocalLayoutForTy rp.types (.int .i8 true)⟩ st := by
  have h_dv : (Miri.Interpreter.ExecutionMachine.discriminantHooks
      (refExecCfg rp)).discriminantValue c (tyIdFor rp.types .ordering)
        (orderingVariantIdx ord) st =
      .ok (some (tyIdFor rp.types
          (.int refOrderingEnumTy.discrWidth refOrderingEnumTy.discrSigned),
        BitVec.ofNat 128 (orderingTagBits ord))) st := by
    dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks,
      refExecCfg, Miri.Interpreter.ExecutionMachine.withValidation,
      refExecutionConfig, refDiscriminantLeaves]
    rw [h_res]
    cases ord <;> rfl
  exact discrHooks_discriminantForVariant_core rp c .ordering refOrderingEnumTy
    (orderingVariantIdx ord) (orderingTagBits ord) st refOrderingEnumTy_admitted
    (discrHooks_discriminantLayout_ordering rp c st h_res) h_dv
    (refOrderingEnumTy_getElem? ord)

/-- The M_anneal discriminant is well-typed. -/
theorem checkVal_orderingDiscr (ord : OrderingVal) :
    checkVal (.scalar ⟨.i8, true, BitVec.ofNat 128 (orderingTagBits ord)⟩)
      (.int .i8 true) = true := by
  cases ord <;> rfl

/-! ## Section 6: `PlaceDynamic.evalPlace`, Writes, and `evalRvalueIntoPlace` -/

private theorem localToPlace_ok (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (slot : LocalSlot)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.localToPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c id st =
      .ok ⟨.local 0 id none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types ty⟩ st := by
  intro st
  have h_cf := currentFrame_mkSimState rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_gl := mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty slot h_ty h_sl
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_pl :
      Miri.Interpreter.placeLayoutOfLocal
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c id st =
      .ok (refLocalLayoutForTy rp.types ty) st := by
    dsimp only [Miri.Interpreter.placeLayoutOfLocal, bind, Bind.bind, pure, Pure.pure]
    have h_gf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st =
        .ok (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace) st := h_cf
    rw [eStateM_bind_ok h_gf, h_gl]; rfl
  dsimp only [Miri.Interpreter.localToPlace, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_pl]
  simp only [h_sz, ite_true]
  rfl

private theorem localToPlace_oob (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId)
    (h_oob : MirSemantics.getElem? bodyLocals id = none ∨
      MirSemantics.getElem? slots id = none) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.localToPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c id st =
      .error (.stack (.invalidLocal id (liftLocals rp.types bodyLocals slots).length)) st := by
  intro st
  have h_cf := currentFrame_mkSimState rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_gl :
      (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace).getLocal id =
        .error (.invalidLocal id (liftLocals rp.types bodyLocals slots).length) := by
    cases h_oob with
    | inl h =>
      exact mkSimFrame_getLocal_none_left rp defId rbody blockIdx
        stmtIdx bodyLocals slots retPlace id h
    | inr h =>
      exact mkSimFrame_getLocal_none_right rp defId rbody blockIdx
        stmtIdx bodyLocals slots retPlace id h
  have h_pl :
      Miri.Interpreter.placeLayoutOfLocal
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c id st =
      .error (.stack (.invalidLocal id (liftLocals rp.types bodyLocals slots).length)) st := by
    dsimp only [Miri.Interpreter.placeLayoutOfLocal, bind, Bind.bind, pure, Pure.pure]
    have h_gf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st =
        .ok (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace) st := h_cf
    rw [eStateM_bind_ok h_gf, h_gl]; rfl
  dsimp only [Miri.Interpreter.localToPlace, bind, Bind.bind]
  rw [eStateM_bind_err h_pl]

private theorem placeDynamic_evalPlace_local_ok (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (skip : Bool) (ty : MirTy) (slot : LocalSlot)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.PlaceDynamic.evalPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
        c ⟨id, Array.empty⟩ skip st =
      .ok ⟨.local 0 id none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types ty⟩ st := by
  intro st
  have h_lp := localToPlace_ok rp c defId rbody blockIdx stmtIdx bodyLocals slots
    retPlace mem ctrl cm id ty slot h_ty h_sl
  dsimp only [Miri.Interpreter.PlaceDynamic.evalPlace, bind, Bind.bind]
  rw [eStateM_bind_ok h_lp]
  have h_arr_ne : (Array.empty == Array.mk [Miri.MIR.ProjectionElem.Deref]) = false := rfl
  rw [h_arr_ne, Bool.and_false, ite_false_eq]
  rw [eStateM_bind_ok (array_forIn_empty _ _ st)]
  rfl

private theorem placeDynamic_evalPlace_oob (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (pl : Miri.MIR.Place) (skip : Bool)
    (h_oob : MirSemantics.getElem? bodyLocals pl.localId = none ∨
      MirSemantics.getElem? slots pl.localId = none) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.PlaceDynamic.evalPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
        c pl skip st =
      .error (.stack (.invalidLocal pl.localId (liftLocals rp.types bodyLocals slots).length)) st := by
  intro st
  have h_lp := localToPlace_oob rp c defId rbody blockIdx stmtIdx bodyLocals slots
    retPlace mem ctrl cm pl.localId h_oob
  dsimp only [Miri.Interpreter.PlaceDynamic.evalPlace, bind, Bind.bind]
  rw [eStateM_bind_err h_lp]

private theorem placeDynamic_evalPlace_deref_err (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (slot : LocalSlot)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.PlaceDynamic.evalPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
        c ⟨id, Array.mk [.Deref]⟩ true st =
      .error (.unsupported "projections unsupported on Day 1") st := by
  intro st
  have h_lp := localToPlace_ok rp c defId rbody blockIdx stmtIdx bodyLocals slots
    retPlace mem ctrl cm id ty slot h_ty h_sl
  dsimp only [Miri.Interpreter.PlaceDynamic.evalPlace, bind, Bind.bind]
  rw [eStateM_bind_ok h_lp]
  rfl

private theorem writePlaceImmediateNoValidate_local_dead (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.writePlaceImmediateNoValidate
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c imm ⟨.local 0 id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .error (.stack (.localExpectedLive id)) st := by
  intro st
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_cf := currentFrame_mkSimState rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_go := mkSimFrame_getLocalOperand_dead rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty h_ty h_sl
  have h_as :
      Miri.Interpreter.asMplaceOrMutableLocal
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place c
        ⟨.local 0 id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .error (.stack (.localExpectedLive id)) st := by
    dsimp only [Miri.Interpreter.asMplaceOrMutableLocal, bind, Bind.bind]
    have h_da : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.debugAssertions = false := rfl
    change (EStateM.bind (EStateM.pure ()) (fun _ => EStateM.bind (EStateM.pure ()) (fun _ => EStateM.bind (EStateM.pure ()) (fun _ => _))) st) = _
    rw [eStateM_bind_pure, eStateM_bind_pure, eStateM_bind_pure]
    simp only [h_da, Bool.false_eq_true, ite_false]
    have h_gf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st =
        .ok (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace) st := h_cf
    rw [eStateM_bind_ok h_gf, h_go]; rfl
  dsimp only [Miri.Interpreter.writePlaceImmediateNoValidate, bind, Bind.bind]
  simp only [h_sz, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [eStateM_bind_err h_as]

private theorem writePlaceImmediateNoValidate_local_live (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots slots' : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (optVal optVal' : Option Val)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal))
    (h_set : MirSemantics.setElem? slots id (.immediate optVal') = some slots') :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    Miri.Interpreter.writePlaceImmediateNoValidate
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c (optValToMiriImm ty optVal')
        ⟨.local 0 id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .ok () (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots'
        retPlace mem ctrl cm) := by
  intro st
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_cf := currentFrame_mkSimState rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_go := mkSimFrame_getLocalOperand_live rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace id ty optVal h_ty h_sl
  have h_so := mkSimFrame_setLocalOperand_some rp defId rbody blockIdx stmtIdx
    bodyLocals slots slots' retPlace id ty optVal optVal' h_ty h_sl h_set
  have h_as :
      Miri.Interpreter.asMplaceOrMutableLocal
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place c
        ⟨.local 0 id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .ok (.immediateLocal id (refLocalLayoutForTy rp.types ty)) st := by
    dsimp only [Miri.Interpreter.asMplaceOrMutableLocal, bind, Bind.bind, pure, Pure.pure]
    have h_da : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.debugAssertions = false := rfl
    change (EStateM.bind (EStateM.pure ()) (fun _ => EStateM.bind (EStateM.pure ()) (fun _ => EStateM.bind (EStateM.pure ()) (fun _ => _))) st) = _
    rw [eStateM_bind_pure, eStateM_bind_pure, eStateM_bind_pure]
    simp only [h_da, Bool.false_eq_true, ite_false]
    have h_gf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st =
        .ok (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace) st := h_cf
    rw [eStateM_bind_ok h_gf, h_go]; rfl
  dsimp only [Miri.Interpreter.writePlaceImmediateNoValidate, bind, Bind.bind]
  simp only [h_sz, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [eStateM_bind_ok h_as]
  dsimp only
  have h_wl :
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.writeLocalImmediate
        c id (refLocalLayoutForTy rp.types ty) (optValToMiriImm ty optVal') st =
      Miri.Interpreter.placeWriteLocalImmediate
        Miri.Interpreter.MachineHooks.currentFrame
        Miri.Interpreter.MachineHooks.setCurrentFrame
        (EStateM.pure false)
        Miri.Interpreter.MachineHooks.afterLocalWrite
        (fun _ _ => EStateM.pure ())
        id (refLocalLayoutForTy rp.types ty) (optValToMiriImm ty optVal') st := rfl
  rw [h_wl]
  dsimp only [Miri.Interpreter.placeWriteLocalImmediate, bind, Bind.bind, pure, Pure.pure]
  simp only [h_sz, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [eStateM_bind_ok h_cf, h_go]
  change (EStateM.bind (EStateM.pure _) _ st) = _
  rw [eStateM_bind_pure]
  dsimp only
  rw [h_so]
  rfl

private theorem writePlaceImmediate_local_ok (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots slots' : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (optVal : Option Val) (v : Val)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal))
    (h_set : MirSemantics.setElem? slots id (.immediate (some v)) = some slots')
    (h_cv : checkVal v ty = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types ty) = some ty) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    let st' := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots'
      retPlace mem ctrl cm
    Miri.Interpreter.writePlaceImmediate
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c (valToMiriImmediate ty v)
        ⟨.local 0 id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .ok () st' := by
  intro st st'
  have h_nv := writePlaceImmediateNoValidate_local_live rp c defId rbody
    blockIdx stmtIdx bodyLocals slots slots' retPlace mem ctrl cm id ty
    optVal (some v) h_ty h_sl h_set
  have h_ev :
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.enforceValidity
        c (refLocalLayoutForTy rp.types ty) st' = .ok true st' := rfl
  have h_v :
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.validate
        c ⟨.local 0 id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st' =
      Miri.Interpreter.ValidityVisitor.validatePlace
        (Miri.Interpreter.TypedMachineBindings.bindValidity
          (refValidityHooks rp.types) refRetagHooks 8)
        c 8 ⟨.local 0 id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ false true st' := rfl
  have h_sl' : MirSemantics.getElem? slots' id = some (.immediate (some v)) := by
    have h_aux : ∀ (xs xs' : List LocalSlot) (i : Nat) (x : LocalSlot),
        MirSemantics.setElem? xs i x = some xs' →
        MirSemantics.getElem? xs' i = some x := by
      intro xs
      induction xs with
      | nil => intro xs' i x h; cases h
      | cons hd tl ih =>
        intro xs' i x h
        cases i with
        | zero => injection h with hx; subst hx; rfl
        | succ j =>
          dsimp only [MirSemantics.setElem?] at h
          cases h_r : MirSemantics.setElem? tl j x with
          | none => rw [h_r] at h; cases h
          | some tl' =>
            rw [h_r] at h; injection h with hx; subst hx
            exact ih tl' j x h_r
    exact h_aux slots slots' id (.immediate (some v)) h_set
  have h_val := validatePlace_local_ok rp.types c id ty v
    (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots' retPlace) st'
    rfl rfl rfl
    (mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx bodyLocals slots'
      retPlace id ty (.immediate (some v)) h_ty h_sl')
    h_cv h_res
  dsimp only [optValToMiriImm] at h_nv
  dsimp only [Miri.Interpreter.writePlaceImmediate, bind, Bind.bind, EStateM.bind]
  rw [h_nv]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ev]
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  simp only [ite_true]
  rw [h_v]
  exact h_val

/-- `refHasPadding` never fails on a canonical local layout. -/
private theorem refHasPadding_ok (types : List MirTy) (ty : MirTy) :
    ∃ b, refHasPadding (refLocalLayoutForTy types ty) = .ok b := by
  cases ty with
  | int w s => cases w <;> cases s <;> exact ⟨_, rfl⟩
  | bool | unit | never | char | ordering | ref _ _ | rawPtr _ _
  | unsupported => exact ⟨_, rfl⟩
  | enum ety =>
    dsimp only [refHasPadding, refLocalLayoutForTy, refLayoutDataForTy,
      refEnumLayoutData]
    cases ety.tagRepr <;> exact ⟨_, rfl⟩
  | tuple fs =>
    cases fs with
    | nil => exact ⟨_, rfl⟩
    | cons f rest =>
      cases rest with
      | nil => cases f <;> exact ⟨_, rfl⟩
      | cons g rest₂ =>
        cases rest₂ with
        | cons _ _ => cases f <;> cases g <;> exact ⟨_, rfl⟩
        | nil =>
          cases f with
          | int w s =>
            cases g with
            | bool => cases w <;> cases s <;> exact ⟨_, rfl⟩
            | _ => exact ⟨_, rfl⟩
          | _ => exact ⟨_, rfl⟩

private theorem copyRuntimePlace_imm_to_local (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (amem : MemoryState)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (dstId : LocalId) (srcTy dstTy : MirTy)
    (optVal : Option Val) (dstSlot : LocalSlot)
    (h_dst_ty : MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (h_dst_sl : MirSemantics.getElem? slots dstId = some dstSlot)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_dst_supp : isSupportedScalarOrUnitTy dstTy = true)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_sm : SlotMatchesTy srcTy (.immediate optVal)) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    let h := refExecCfg rp
    let res := Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
      ⟨.immediate (optValToMiriImm srcTy optVal), refLocalLayoutForTy rp.types srcTy⟩
      ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types dstTy⟩ false st
    if !(MirTy.beq srcTy dstTy) then
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = .unsupported
    else
      match optVal with
      | none =>
        ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = .undefined
      | some v =>
        match writePlace slots amem dstId dstTy v with
        | .error k =>
          ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
        | .ok (slots', _) =>
          res = .ok () (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals
            slots' retPlace mem ctrl cm) := by
  intro st h res
  have h_compat_eq :
      h.copy.compatible (refLocalLayoutForTy rp.types srcTy)
        (refLocalLayoutForTy rp.types dstTy) =
        .ok (MirTy.beq srcTy dstTy) := by
    dsimp only [h, refExecCfg, Miri.Interpreter.ExecutionMachine.withValidation,
      Miri.Interpreter.TypedMachineBindings.bindValidation,
      refExecutionConfig, refPlaceCopyHooks, refLocalLayoutForTy]
    cases h_b : MirTy.beq srcTy dstTy with
    | true =>
      have h_eq := MirTy.eq_of_beq h_b
      subst h_eq
      rw [beq_self_eq_true]
    | false =>
      cases h_tid : (tyIdFor rp.types srcTy == tyIdFor rp.types dstTy) with
      | false => rfl
      | true =>
        have h_eq := (tyIdFor_eq_iff_of_resolve h_src_res h_dst_res).mp (eq_of_beq h_tid)
        subst h_eq
        rw [MirTy.beq_refl] at h_b
        cases h_b
  cases h_ty_eq : MirTy.beq srcTy dstTy with
  | false =>
    rw [h_ty_eq] at h_compat_eq
    dsimp only [Bool.not, ite_true_eq]
    have h_err : res = .error (.invalidProgram "copy type mismatch") st := by
      dsimp only [res, Miri.Interpreter.copyRuntimePlace,
        Miri.Interpreter.copyRuntimePlaceNoValidate, bind, Bind.bind]
      rw [h_compat_eq]
      rfl
    exact ⟨_, _, h_err, rfl⟩
  | true =>
    have h_st_eq := MirTy.eq_of_beq h_ty_eq
    subst h_st_eq
    rw [h_ty_eq] at h_compat_eq
    dsimp only [Bool.not, ite_false_eq]
    have h_sz := refLayoutDataForTy_isSized srcTy
    have h_take : Miri.Interpreter.PlaceMachine.takePendingMoveDeinit true st = .ok false st := rfl
    have h_rr : Miri.Interpreter.PlaceMachine.readRaw refAccessConfig
        ⟨.immediate (optValToMiriImm srcTy optVal), refLocalLayoutForTy rp.types srcTy⟩ st =
        .ok (.immediate ⟨optValToMiriImm srcTy optVal,
          localMemoryLayout (refLocalLayoutForTy rp.types srcTy)⟩) st := rfl
    have h_nv_eq :
        Miri.Interpreter.copyRuntimePlaceNoValidate
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate (optValToMiriImm srcTy optVal), refLocalLayoutForTy rp.types srcTy⟩
          ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy rp.types srcTy⟩ false st =
        Miri.Interpreter.writePlaceImmediateNoValidate
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place c
          (optValToMiriImm srcTy optVal)
          ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy rp.types srcTy⟩ st := by
      dsimp only [Miri.Interpreter.copyRuntimePlaceNoValidate,
        Miri.Interpreter.ExecutionMachine.projectionHooks, bind, Bind.bind]
      rw [h_compat_eq]
      change (EStateM.bind (EStateM.pure true) _ st) = _
      rw [eStateM_bind_pure]
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
      let ⟨pb, h_pad⟩ := refHasPadding_ok rp.types srcTy
      have h_pad' : h.copy.hasPadding (refLocalLayoutForTy rp.types srcTy) =
          .ok pb := h_pad
      rw [h_pad']
      change (EStateM.bind (EStateM.pure pb) _ st) = _
      rw [eStateM_bind_pure]
      change (EStateM.bind
        (Miri.Interpreter.PlaceMachine.takePendingMoveDeinit true) _ st) = _
      rw [eStateM_bind_ok h_take]
      have h_sz' : (refLocalLayoutForTy rp.types srcTy).layout.isSized = true :=
        h_sz
      cases pb with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        change (EStateM.bind
          (Miri.Interpreter.PlaceMachine.readRaw refAccessConfig _) _ st) = _
        rw [eStateM_bind_ok h_rr]
        simp only [h_sz', bne_self_eq_false, Bool.false_eq_true, ite_false,
          ite_true]
        rfl
      | true =>
        rw [ite_true_eq]
        change (EStateM.bind (EStateM.pure (ImmediateOrPlace.immediate
          ⟨optValToMiriImm srcTy optVal,
            localMemoryLayout (refLocalLayoutForTy rp.types srcTy)⟩)) _ st) = _
        rw [eStateM_bind_pure]
        simp only [h_sz', bne_self_eq_false, Bool.false_eq_true, ite_false,
          ite_true]
        rfl
    cases dstSlot with
    | dead =>
      have h_dead := writePlaceImmediateNoValidate_local_dead rp c defId rbody
        blockIdx stmtIdx bodyLocals slots retPlace mem ctrl cm dstId srcTy
        (optValToMiriImm srcTy optVal) h_dst_ty h_dst_sl
      have h_res_dead : res = .error (.stack (.localExpectedLive dstId)) st := by
        dsimp only [res, Miri.Interpreter.copyRuntimePlace, bind, Bind.bind, EStateM.bind]
        rw [h_nv_eq, h_dead]
      cases optVal with
      | none => exact ⟨_, _, h_res_dead, rfl⟩
      | some v =>
        dsimp only [writePlace]
        rw [h_sm, ite_not_true_eq, h_dst_sl]
        exact ⟨_, _, h_res_dead, rfl⟩
    | indirect _ =>
      exact False.elim (SlotsMatchTys.not_indirect h_inv h_dst_ty h_dst_sl)
    | immediate dstOpt =>
      let ⟨slots', h_set⟩ := mirSetElem?_some_of_lt slots dstId (.immediate optVal)
        (mirGetElem?_lt_of_some h_dst_sl)
      have h_nv_ok := writePlaceImmediateNoValidate_local_live rp c defId rbody
        blockIdx stmtIdx bodyLocals slots slots' retPlace mem ctrl cm dstId srcTy
        dstOpt optVal h_dst_ty h_dst_sl h_set
      let st' := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots'
        retPlace mem ctrl cm
      have h_ev :
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place.enforceValidity
            c (refLocalLayoutForTy rp.types srcTy) st' = .ok true st' := rfl
      have h_v :
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place.validate
            c ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
              refLocalLayoutForTy rp.types srcTy⟩ st' =
          Miri.Interpreter.ValidityVisitor.validatePlace
            (Miri.Interpreter.TypedMachineBindings.bindValidity
              (refValidityHooks rp.types) refRetagHooks 8)
            c 8 ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
              refLocalLayoutForTy rp.types srcTy⟩ false true st' := rfl
      have h_sl' : MirSemantics.getElem? slots' dstId = some (.immediate optVal) := by
        have h_aux : ∀ (xs xs' : List LocalSlot) (i : Nat) (x : LocalSlot),
            MirSemantics.setElem? xs i x = some xs' →
            MirSemantics.getElem? xs' i = some x := by
          intro xs
          induction xs with
          | nil => intro xs' i x h; cases h
          | cons hd tl ih =>
            intro xs' i x h
            cases i with
            | zero => injection h with hx; subst hx; rfl
            | succ j =>
              dsimp only [MirSemantics.setElem?] at h
              cases h_r : MirSemantics.setElem? tl j x with
              | none => rw [h_r] at h; cases h
              | some tl' =>
                rw [h_r] at h; injection h with hx; subst hx
                exact ih tl' j x h_r
        exact h_aux slots slots' dstId (.immediate optVal) h_set
      have h_res_val :
          res =
            Miri.Interpreter.ValidityVisitor.validatePlace
              (Miri.Interpreter.TypedMachineBindings.bindValidity
                (refValidityHooks rp.types) refRetagHooks 8)
              c 8 ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
                refLocalLayoutForTy rp.types srcTy⟩ false true st' := by
        dsimp only [res, Miri.Interpreter.copyRuntimePlace, bind, Bind.bind, EStateM.bind]
        rw [h_nv_eq, h_nv_ok]
        dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
        rw [h_ev]
        dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
        simp only [ite_true]
        rw [bne_self_eq_false, ite_false_eq, h_v]
      cases optVal with
      | none =>
        let ⟨msg, st'', h_ub⟩ := validatePlace_local_uninit_ub rp.types c dstId srcTy
          (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots' retPlace) st'
          rfl rfl
          (mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx bodyLocals slots'
            retPlace dstId srcTy (.immediate none) h_dst_ty h_sl')
          h_sm h_dst_supp h_dst_res
        exact ⟨_, _, h_res_val.trans h_ub, rfl⟩
      | some v =>
        dsimp only [writePlace]
        rw [h_sm, ite_not_true_eq, h_dst_sl, h_set]
        have h_ok := validatePlace_local_ok rp.types c dstId srcTy v
          (mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots' retPlace) st'
          rfl rfl rfl
          (mkSimFrame_getLocal_some rp defId rbody blockIdx stmtIdx bodyLocals slots'
            retPlace dstId srcTy (.immediate (some v)) h_dst_ty h_sl')
          h_sm h_dst_res
        exact h_res_val.trans h_ok

/-- Write a validated primitive/discriminant value `v` of type `resTy` into
destination local `dstId` of type `dstTy`, matching `assertRvalueLayout` +
`writePlaceImmediate` against `writePlace`. -/
private theorem assertAndWrite_local_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (amem : MemoryState)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (dstId : LocalId) (resTy dstTy : MirTy) (v : Val)
    (dstSlot : LocalSlot)
    (h_dst_ty : MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (h_dst_sl : MirSemantics.getElem? slots dstId = some dstSlot)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_cv : checkVal v resTy = true) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    let res :=
      if (refLocalLayoutForTy rp.types resTy == refLocalLayoutForTy rp.types dstTy) then
        Miri.Interpreter.writePlaceImmediate
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
          c (valToMiriImmediate resTy v)
          ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy rp.types dstTy⟩ st
      else
        .error (.invalidProgram "rvalue result layout mismatch") st
    match writePlace slots amem dstId dstTy v with
    | .error k =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
    | .ok (slots', _) =>
      res = .ok () (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots'
        retPlace mem ctrl cm) := by
  intro st res
  have h_cv_iff : checkVal v dstTy = MirTy.beq resTy dstTy := by
    have h_vty : v.ty? = some resTy := by
      dsimp only [checkVal] at h_cv
      cases h_t : v.ty? with
      | none => rw [h_t] at h_cv; cases h_cv
      | some t =>
        rw [h_t] at h_cv
        have h_eq := MirTy.eq_of_beq h_cv
        subst h_eq
        rfl
    dsimp only [checkVal]
    rw [h_vty]
  have h_lay_eq :
      (refLocalLayoutForTy rp.types resTy == refLocalLayoutForTy rp.types dstTy) =
        MirTy.beq resTy dstTy := by
    cases h_b : MirTy.beq resTy dstTy with
    | true =>
      have h_eq := MirTy.eq_of_beq h_b
      subst h_eq
      exact beq_self_eq_true _
    | false =>
      cases h_l : (refLocalLayoutForTy rp.types resTy == refLocalLayoutForTy rp.types dstTy) with
      | false => rfl
      | true =>
        have h_le := eq_of_beq h_l
        have h_tid : tyIdFor rp.types resTy = tyIdFor rp.types dstTy :=
          congrArg Miri.ABI.TyAndLayout.ty h_le
        have h_r : resolveTy rp.types (tyIdFor rp.types resTy) = some dstTy := by
          rw [h_tid]; exact h_dst_res
        have h_eq : dstTy = resTy := resolveTy_tyIdFor_some_eq h_r
        subst h_eq
        rw [MirTy.beq_refl] at h_b
        cases h_b
  dsimp only [writePlace, res]
  rw [h_cv_iff, h_lay_eq]
  cases h_b : MirTy.beq resTy dstTy with
  | false => exact ⟨_, _, rfl, rfl⟩
  | true =>
    have h_eq := MirTy.eq_of_beq h_b
    subst h_eq
    dsimp only [ite_true_eq, ite_not_true_eq]
    rw [h_dst_sl]
    cases dstSlot with
    | dead =>
      have h_dead := writePlaceImmediateNoValidate_local_dead rp c defId rbody
        blockIdx stmtIdx bodyLocals slots retPlace mem ctrl cm dstId resTy
        (valToMiriImmediate resTy v) h_dst_ty h_dst_sl
      have h_err :
          Miri.Interpreter.writePlaceImmediate
            (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
            c (valToMiriImmediate resTy v)
            ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
              refLocalLayoutForTy rp.types resTy⟩ st =
          .error (.stack (.localExpectedLive dstId)) st := by
        dsimp only [Miri.Interpreter.writePlaceImmediate, bind, Bind.bind, EStateM.bind]
        rw [h_dead]
      exact ⟨_, _, h_err, rfl⟩
    | indirect _ =>
      exact False.elim (SlotsMatchTys.not_indirect h_inv h_dst_ty h_dst_sl)
    | immediate optVal =>
      let ⟨slots', h_set⟩ := mirSetElem?_some_of_lt slots dstId (.immediate (some v))
        (mirGetElem?_lt_of_some h_dst_sl)
      rw [h_set]
      exact writePlaceImmediate_local_ok rp c defId rbody blockIdx stmtIdx
        bodyLocals slots slots' retPlace mem ctrl cm dstId resTy optVal v
        h_dst_ty h_dst_sl h_set h_cv h_dst_res

/-! ### `Rvalue.cast .intToInt` -/

private theorem castHooks_takePendingMoveDeinit (rp : RefProg)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :
    (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).takePendingMoveDeinit
      (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace mem
        ctrl cm) =
      .ok false (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
        retPlace mem ctrl cm) := rfl

private theorem castHooks_destLayout (rp : RefProg)
    (r : Miri.Interpreter.RuntimePlaceRef Miri.Memory.Provenance)
    (l : Miri.Interpreter.LocalLayout) :
    (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).destLayout ⟨r, l⟩ = l := rfl

private theorem refLocalLayoutForTy_ty (types : List MirTy) (ty : MirTy) :
    (refLocalLayoutForTy types ty).ty = tyIdFor types ty := rfl

private theorem castHooks_enforceValidity (rp : RefProg) (c : Choice)
    (l : Miri.Interpreter.LocalLayout)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).enforceValidity c l st = .ok true st := rfl

private theorem castHooks_typeInfo (rp : RefProg) (c : Choice) (tid : TyId)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).typeInfo c tid st =
      match resolveTy rp.types tid with
      | some (.int w s) => .ok (.integer (toMiriIntKind w s)) st
      | some .bool => .ok .boolean st
      | some .char => .ok .character st
      | _ => .error (.unsupported "cast type unsupported") st := rfl

private theorem castHooks_bind_typeInfo (rp : RefProg) (c : Choice)
    (tid : TyId) {α : Type}
    (f : Miri.Interpreter.CastTypeInfo →
      EStateM Miri.Interpreter.StepError
        (Miri.Interpreter.MachineHooks.State Unit RefUser) α)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    EStateM.bind ((Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).typeInfo c tid) f st =
      match resolveTy rp.types tid with
      | some (.int w s) => f (.integer (toMiriIntKind w s)) st
      | some .bool => f .boolean st
      | some .char => f .character st
      | _ => .error (.unsupported "cast type unsupported") st := by
  dsimp only [EStateM.bind]
  rw [castHooks_typeInfo]
  cases resolveTy rp.types tid with
  | none => rfl
  | some t => cases t <;> rfl

private theorem castHooks_readImmediate (rp : RefProg) (c : Choice)
    (op : Miri.Interpreter.OpTy Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).readImmediate c op st =
      Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig op st := rfl

private theorem castHooks_writeImmediate (rp : RefProg) (c : Choice)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (dest : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).writeImmediate c imm dest st =
      Miri.Interpreter.writePlaceImmediate
        (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfg rp)).place
        c imm dest st := rfl

private theorem refLocalLayoutForTy_int_size (types : List MirTy)
    (w : IntWidth) (s : Bool) :
    (refLocalLayoutForTy types (.int w s)).layout.size = toMiriSize w := by
  cases w <;> cases s <;> rfl

private theorem toMiriIntKind_signed (w : IntWidth) (s : Bool) :
    (toMiriIntKind w s).signed = s := by
  cases w <;> cases s <;> rfl

private theorem cast_scalar_toUInt_miriScalar (w : IntWidth)
    (bits : BitVec 128) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).toUInt (toMiriSize w) = .ok
          (truncateBits w bits) := by
  have h : (Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).toUInt (toMiriSize w) =
      ((miriScalar w bits).toBits (toMiriSize w)).mapError
        Miri.Memory.ScalarError.scalarInt := by
    cases w <;> rfl
  rw [h, scalarInt_toBits_miriScalar]
  rfl

private theorem cast_intLikeValue_uint (rp : RefProg) (c : Choice)
    (w : IntWidth) (bits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.int w false)) =
      some (.int w false)) :
    Miri.Interpreter.Cast.intLikeValue
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
            refLimits) c
        (.fromScalarInt (miriScalar w bits))
        (refLocalLayoutForTy rp.types (.int w false)) st =
      .ok (truncateBits w bits, false) st := by
  have h_sg : (refLocalLayoutForTy rp.types (.int w
      false)).layout.backendRepr.isSigned =
      .ok false := by
    cases w <;> rfl
  dsimp only [Miri.Interpreter.Cast.intLikeValue, bind, Bind.bind,
      pure, Pure.pure]
  rw [h_sg]
  dsimp only
  rw [eStateM_bind_pure, castHooks_bind_typeInfo, refLocalLayoutForTy_ty, h_res]
  dsimp only
  rw [toMiriIntKind_signed, ite_false_eq, refLocalLayoutForTy_int_size,
    cast_scalar_toUInt_miriScalar]
  rfl

private theorem cast_bv_ofNat_toNat (x : BitVec 128) :
    BitVec.ofNat 128 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

private theorem cast_bv_toNat_ofNat {n : Nat} (h : n < HPow.hPow 2 128) :
    (BitVec.ofNat 128 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

private theorem cast_scalar_toInt_miriScalar (w : IntWidth)
    (bits : BitVec 128) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).toInt (toMiriSize w) =
      .ok (signExtendBits w (truncateBits w bits)) := by
  have h : (Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
      (miriScalar w bits)).toInt (toMiriSize w) =
      bind ((Miri.Memory.Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
        (miriScalar w bits)).toUInt (toMiriSize w))
        (fun b => ((toMiriSize w).signExtend b).mapError
          (Function.comp Miri.Memory.ScalarError.scalarInt
            Miri.Memory.ScalarIntError.sizeError)) := rfl
  rw [h, cast_scalar_toUInt_miriScalar]
  dsimp only [bind, Except.bind]
  rw [size_signExtend_eq]
  rfl

private theorem cast_intLikeValue_sint (rp : RefProg) (c : Choice)
    (w : IntWidth) (bits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.int w true)) =
      some (.int w true)) :
    Miri.Interpreter.Cast.intLikeValue
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
            refLimits) c
        (.fromScalarInt (miriScalar w bits))
        (refLocalLayoutForTy rp.types (.int w true)) st =
      .ok (BitVec.ofInt 128 (signExtendBits w (truncateBits w bits)),
          true) st := by
  have h_sg : (refLocalLayoutForTy rp.types (.int w
      true)).layout.backendRepr.isSigned =
      .ok true := by
    cases w <;> rfl
  dsimp only [Miri.Interpreter.Cast.intLikeValue, bind, Bind.bind,
      pure, Pure.pure]
  rw [h_sg]
  dsimp only
  rw [eStateM_bind_pure, castHooks_bind_typeInfo, refLocalLayoutForTy_ty, h_res]
  dsimp only
  rw [toMiriIntKind_signed, ite_true_eq, refLocalLayoutForTy_int_size,
    cast_scalar_toInt_miriScalar]
  rfl

private theorem cast_intLikeValue_bool (rp : RefProg) (c : Choice) (b : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .bool) = some .bool) :
    Miri.Interpreter.Cast.intLikeValue
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp) refLimits)
        c (.fromBool b)
        (refLocalLayoutForTy rp.types .bool) st =
      .ok (BitVec.ofNat 128 (if b then 1 else 0), false) st := by
  have h_sg : (refLocalLayoutForTy rp.types .bool).layout.backendRepr.isSigned =
      .ok false := rfl
  dsimp only [Miri.Interpreter.Cast.intLikeValue, bind, Bind.bind,
      pure, Pure.pure]
  rw [h_sg]
  dsimp only
  rw [eStateM_bind_pure, castHooks_bind_typeInfo, refLocalLayoutForTy_ty, h_res]
  dsimp only
  rw [scalar_toBool_fromBool]
  cases b <;> rfl

private theorem cast_intLikeValue_char (rp : RefProg) (c : Choice) (ch : Char)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .char) = some .char) :
    Miri.Interpreter.Cast.intLikeValue
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp) refLimits)
        c (.fromChar ch)
        (refLocalLayoutForTy rp.types .char) st =
      .ok (BitVec.ofNat 128 ch.toNat, false) st := by
  have h_sg : (refLocalLayoutForTy rp.types .char).layout.backendRepr.isSigned =
      .ok false := rfl
  dsimp only [Miri.Interpreter.Cast.intLikeValue, bind, Bind.bind,
      pure, Pure.pure]
  rw [h_sg]
  dsimp only
  rw [eStateM_bind_pure, castHooks_bind_typeInfo, refLocalLayoutForTy_ty, h_res]
  dsimp only
  rw [scalar_toChar_fromChar]
  rfl

private theorem cast_castFromIntLike_int (rp : RefProg) (c : Choice)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance)
    (src : Miri.Interpreter.LocalLayout) (n : Nat) (sg : Bool)
    (w : IntWidth) (s : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types (.int w s)) = some (.int w s))
    (h_ilv : Miri.Interpreter.Cast.intLikeValue
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp) refLimits)
        c sc src st =
      .ok (BitVec.ofNat 128 n, sg) st) :
    Miri.Interpreter.Cast.castFromIntLike
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits) c sc src
        (refLocalLayoutForTy rp.types (.int w s)) st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar w (BitVec.ofNat 128 n))),
        refLocalLayoutForTy rp.types (.int w s)⟩ st := by
  dsimp only [Miri.Interpreter.Cast.castFromIntLike, bind, Bind.bind, pure,
    Pure.pure]
  rw [eStateM_bind_ok h_ilv, castHooks_bind_typeInfo, refLocalLayoutForTy_ty,
    h_res]
  dsimp only
  rw [refLocalLayoutForTy_int_size, integerCast_u128_to_int]
  rfl

private theorem cast_castFromIntLike_char (rp : RefProg) (c : Choice)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance)
    (src : Miri.Interpreter.LocalLayout) (n : Nat) (sg : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_res : resolveTy rp.types (tyIdFor rp.types .char) = some .char)
    (h_n : n < HPow.hPow 2 128)
    (h_ilv : Miri.Interpreter.Cast.intLikeValue
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp) refLimits)
        c sc src st =
      .ok (BitVec.ofNat 128 n, sg) st) :
    Miri.Interpreter.Cast.castFromIntLike
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits) c sc src
        (refLocalLayoutForTy rp.types .char) st =
      if Nat.ble n 255 then
        .ok ⟨.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofChar
            (Char.ofNat n))),
          refLocalLayoutForTy rp.types .char⟩ st
      else
        .error (.invalidProgram "integer-to-char requires a u8 value") st := by
  dsimp only [Miri.Interpreter.Cast.castFromIntLike, bind, Bind.bind, pure,
    Pure.pure]
  rw [eStateM_bind_ok h_ilv, castHooks_bind_typeInfo, refLocalLayoutForTy_ty,
    h_res]
  dsimp only
  rw [integerCast_u128_to_char, cast_bv_toNat_ofNat h_n]
  cases Nat.ble n 255 <;> rfl

/-- `Cast.cast .IntToInt` after a successful source read: the result is
fixed by the destination type. -/
private theorem cast_intToInt_core (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (dref : Miri.Interpreter.RuntimePlaceRef Miri.Memory.Provenance)
    (srcTy dstTy : MirTy) (imm : Miri.Interpreter.Immediate
        Miri.Memory.Provenance)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance) (n : Nat) (sg : Bool)
    (h_take : (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).takePendingMoveDeinit st = .ok false st)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_il : isIntLikeTy srcTy = true) (h_n : n < HPow.hPow 2 128)
    (h_read : Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
        ⟨.immediate imm, refLocalLayoutForTy rp.types srcTy⟩ st =
      .ok ⟨.scalar sc, refLocalLayoutForTy rp.types srcTy⟩ st)
    (h_ilv : Miri.Interpreter.Cast.intLikeValue
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits) c sc
        (refLocalLayoutForTy rp.types srcTy) st =
      .ok (BitVec.ofNat 128 n, sg) st) :
    let res := Miri.Interpreter.Cast.cast
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp) refLimits)
        c refLimits.casts
      ⟨.immediate imm, refLocalLayoutForTy rp.types srcTy⟩
      .IntToInt (tyIdFor rp.types dstTy)
      ⟨dref, refLocalLayoutForTy rp.types dstTy⟩ st
    let place :=
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
    match dstTy with
    | .int w s =>
      res = Miri.Interpreter.writePlaceImmediate place c
        (valToMiriImmediate (.int w s)
          (.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 n)⟩))
        ⟨dref, refLocalLayoutForTy rp.types (.int w s)⟩ st
    | .char =>
      res =
        if Nat.ble n 255 then
          Miri.Interpreter.writePlaceImmediate place c
            (valToMiriImmediate .char (.char (Char.ofNat n)))
            ⟨dref, refLocalLayoutForTy rp.types .char⟩ st
        else .error (.invalidProgram "integer-to-char requires a u8 value") st
    | _ => ∃ err st', res = .error err st' ∧
        stepErrorFaultKind err = .unsupported := by
  intro res place
  have h_rd := (castHooks_readImmediate rp c _ st).trans h_read
  dsimp only [res, Miri.Interpreter.Cast.cast, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_take, castHooks_destLayout, refLocalLayoutForTy_ty,
    beq_self_eq_true, ite_true_eq, eStateM_bind_pure, ite_false_eq,
    eStateM_bind_ok (castHooks_enforceValidity rp c _ st), ite_true_eq,
    castHooks_bind_typeInfo]
  simp only [refLocalLayoutForTy_ty]
  rw [h_src_res]
  cases srcTy with
  | int w s =>
    dsimp only
    rw [eStateM_bind_ok h_rd]
    dsimp only
    rw [castHooks_bind_typeInfo, refLocalLayoutForTy_ty, h_src_res]
    dsimp only
    rw [castHooks_bind_typeInfo, h_dst_res]
    simp only [ite_false_eq]
    cases dstTy with
    | int w' s' =>
      dsimp only
      have h1 := cast_castFromIntLike_int rp c sc _ n sg w' s' st
          h_dst_res h_ilv
      have h2 := eStateM_bind_ok (f := fun result =>
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
            refLimits).writeImmediate c result.imm
          ⟨dref, refLocalLayoutForTy rp.types (.int w' s')⟩) h1
      rw [castHooks_writeImmediate] at h2
      have h3 : valToMiriImmediate (.int w' s')
          (.scalar ⟨w', s', truncateBits w' (BitVec.ofNat 128 n)⟩) =
          .scalar (.fromScalarInt (miriScalar w' (BitVec.ofNat 128 n))) := by
        dsimp only [valToMiriImmediate]
        rw [miriScalar_truncateBits]
      rw [h3]
      exact h2
    | char =>
      dsimp only
      have h1 := cast_castFromIntLike_char rp c sc _ n sg st h_dst_res h_n h_ilv
      cases h_b : Nat.ble n 255 with
      | true =>
        rw [h_b, ite_true_eq] at h1
        have h2 := eStateM_bind_ok (f := fun result =>
          (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
              refLimits).writeImmediate c result.imm
            ⟨dref, refLocalLayoutForTy rp.types .char⟩) h1
        rw [castHooks_writeImmediate] at h2
        rw [ite_true_eq]
        exact h2
      | false =>
        rw [h_b, ite_false_eq] at h1
        rw [ite_false_eq]
        have h2 := eStateM_bind_err (f := fun result =>
          (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
              refLimits).writeImmediate c result.imm
            ⟨dref, refLocalLayoutForTy rp.types .char⟩) h1
        exact h2
    | bool =>
      exact ⟨.invalidProgram
        "IntToInt/IntToFloat destination type is not integer/float/char",
        st, rfl, rfl⟩
    | _ => exact ⟨.unsupported "cast type unsupported", st, rfl, rfl⟩
  | bool =>
    dsimp only
    rw [eStateM_bind_ok h_rd]
    dsimp only
    rw [castHooks_bind_typeInfo, refLocalLayoutForTy_ty, h_src_res]
    dsimp only
    rw [castHooks_bind_typeInfo, h_dst_res]
    simp only [ite_false_eq]
    cases dstTy with
    | int w' s' =>
      dsimp only
      have h1 := cast_castFromIntLike_int rp c sc _ n sg w' s' st
          h_dst_res h_ilv
      have h2 := eStateM_bind_ok (f := fun result =>
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
            refLimits).writeImmediate c result.imm
          ⟨dref, refLocalLayoutForTy rp.types (.int w' s')⟩) h1
      rw [castHooks_writeImmediate] at h2
      have h3 : valToMiriImmediate (.int w' s')
          (.scalar ⟨w', s', truncateBits w' (BitVec.ofNat 128 n)⟩) =
          .scalar (.fromScalarInt (miriScalar w' (BitVec.ofNat 128 n))) := by
        dsimp only [valToMiriImmediate]
        rw [miriScalar_truncateBits]
      rw [h3]
      exact h2
    | char =>
      dsimp only
      have h1 := cast_castFromIntLike_char rp c sc _ n sg st h_dst_res h_n h_ilv
      cases h_b : Nat.ble n 255 with
      | true =>
        rw [h_b, ite_true_eq] at h1
        have h2 := eStateM_bind_ok (f := fun result =>
          (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
              refLimits).writeImmediate c result.imm
            ⟨dref, refLocalLayoutForTy rp.types .char⟩) h1
        rw [castHooks_writeImmediate] at h2
        rw [ite_true_eq]
        exact h2
      | false =>
        rw [h_b, ite_false_eq] at h1
        rw [ite_false_eq]
        have h2 := eStateM_bind_err (f := fun result =>
          (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
              refLimits).writeImmediate c result.imm
            ⟨dref, refLocalLayoutForTy rp.types .char⟩) h1
        exact h2
    | bool =>
      exact ⟨.invalidProgram
        "IntToInt/IntToFloat destination type is not integer/float/char",
        st, rfl, rfl⟩
    | _ => exact ⟨.unsupported "cast type unsupported", st, rfl, rfl⟩
  | char =>
    dsimp only
    rw [eStateM_bind_ok h_rd]
    dsimp only
    simp only [castHooks_bind_typeInfo, refLocalLayoutForTy_ty, h_src_res]
    simp only [h_dst_res]
    simp only [ite_false_eq]
    cases dstTy with
    | int w' s' =>
      dsimp only
      have h1 := cast_castFromIntLike_int rp c sc _ n sg w' s' st
          h_dst_res h_ilv
      have h2 := eStateM_bind_ok (f := fun result =>
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
            refLimits).writeImmediate c result.imm
          ⟨dref, refLocalLayoutForTy rp.types (.int w' s')⟩) h1
      rw [castHooks_writeImmediate] at h2
      have h3 : valToMiriImmediate (.int w' s')
          (.scalar ⟨w', s', truncateBits w' (BitVec.ofNat 128 n)⟩) =
          .scalar (.fromScalarInt (miriScalar w' (BitVec.ofNat 128 n))) := by
        dsimp only [valToMiriImmediate]
        rw [miriScalar_truncateBits]
      rw [h3]
      exact h2
    | char =>
      dsimp only
      have h1 := cast_castFromIntLike_char rp c sc _ n sg st h_dst_res h_n h_ilv
      cases h_b : Nat.ble n 255 with
      | true =>
        rw [h_b, ite_true_eq] at h1
        have h2 := eStateM_bind_ok (f := fun result =>
          (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
              refLimits).writeImmediate c result.imm
            ⟨dref, refLocalLayoutForTy rp.types .char⟩) h1
        rw [castHooks_writeImmediate] at h2
        rw [ite_true_eq]
        exact h2
      | false =>
        rw [h_b, ite_false_eq] at h1
        rw [ite_false_eq]
        have h2 := eStateM_bind_err (f := fun result =>
          (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
              refLimits).writeImmediate c result.imm
            ⟨dref, refLocalLayoutForTy rp.types .char⟩) h1
        exact h2
    | bool =>
      exact ⟨.invalidProgram
        "IntToInt/IntToFloat destination type is not integer/float/char",
        st, rfl, rfl⟩
    | _ => exact ⟨.unsupported "cast type unsupported", st, rfl, rfl⟩
  | _ => cases h_il

private theorem cast_ty?_of_checkVal {v : Val} {ty : MirTy}
    (h : checkVal v ty = true) : v.ty? = some ty := by
  dsimp only [checkVal] at h
  cases h_t : v.ty? with
  | none => rw [h_t] at h; cases h
  | some t => rw [h_t] at h; rw [MirTy.eq_of_beq h]

private theorem cast_ty?_tuple {l : List Val} {t : MirTy}
    (h : (Val.tuple l).ty? = some t) : ∃ fs, t = .tuple fs := by
  cases l with
  | nil => cases h
  | cons a rest =>
    cases rest with
    | nil => cases a <;> cases h
    | cons b rest₂ =>
      cases rest₂ with
      | cons _ _ => cases a <;> cases b <;> cases h
      | nil =>
        cases a with
        | scalar sv =>
          cases b with
          | bool bb =>
            dsimp only [Val.ty?] at h
            cases h_wf : sv.wf with
            | false => rw [h_wf] at h; cases h
            | true => rw [h_wf] at h; cases h; exact ⟨_, rfl⟩
          | _ => cases h
        | _ => cases b <;> cases h

private theorem cast_ty?_enumVal {ety : EnumTy} {k : Nat} {t : MirTy}
    (h : (Val.enumVal ety k).ty? = some t) : t = .enum ety := by
  dsimp only [Val.ty?] at h
  cases h_c : (enumAdmitted ety && Nat.blt k ety.discriminants.length) with
  | false => rw [h_c] at h; cases h
  | true => rw [h_c] at h; cases h; rfl

private theorem cast_checkVal_int_inv {v : Val} {w : IntWidth} {s : Bool}
    (h : checkVal v (.int w s) = true) : ∃ bits, v = .scalar ⟨w, s, bits⟩ := by
  have h_t := cast_ty?_of_checkVal h
  cases v with
  | scalar sv =>
    cases sv with
    | mk w' s' bits =>
      dsimp only [Val.ty?] at h_t
      cases h_wf : ScalarVal.wf ⟨w', s', bits⟩ with
      | false => rw [h_wf] at h_t; cases h_t
      | true => rw [h_wf] at h_t; cases h_t; exact ⟨bits, rfl⟩
  | tuple l => let ⟨_, h_fs⟩ := cast_ty?_tuple h_t; cases h_fs
  | enumVal ety k => cases cast_ty?_enumVal h_t
  | _ => cases h_t

private theorem cast_checkVal_bool_inv {v : Val}
    (h : checkVal v .bool = true) : ∃ b, v = .bool b := by
  have h_t := cast_ty?_of_checkVal h
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | scalar sv =>
    dsimp only [Val.ty?] at h_t
    cases h_wf : sv.wf with
    | false => rw [h_wf] at h_t; cases h_t
    | true => rw [h_wf] at h_t; cases h_t
  | tuple l => let ⟨_, h_fs⟩ := cast_ty?_tuple h_t; cases h_fs
  | enumVal ety k => cases cast_ty?_enumVal h_t
  | _ => cases h_t

private theorem cast_checkVal_char_inv {v : Val}
    (h : checkVal v .char = true) : ∃ ch, v = .char ch := by
  have h_t := cast_ty?_of_checkVal h
  cases v with
  | char ch => exact ⟨ch, rfl⟩
  | scalar sv =>
    dsimp only [Val.ty?] at h_t
    cases h_wf : sv.wf with
    | false => rw [h_wf] at h_t; cases h_t
    | true => rw [h_wf] at h_t; cases h_t
  | tuple l => let ⟨_, h_fs⟩ := cast_ty?_tuple h_t; cases h_fs
  | enumVal ety k => cases cast_ty?_enumVal h_t
  | _ => cases h_t

/-- `Cast.cast .IntToInt` propagates a source-read error. -/
private theorem cast_intToInt_readErr (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (dref : Miri.Interpreter.RuntimePlaceRef Miri.Memory.Provenance)
    (srcTy dstTy : MirTy) (imm : Miri.Interpreter.Immediate
        Miri.Memory.Provenance)
    (e : Miri.Interpreter.StepError)
    (h_take : (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).takePendingMoveDeinit st = .ok false st)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_il : isIntLikeTy srcTy = true)
    (h_read : Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
        ⟨.immediate imm, refLocalLayoutForTy rp.types srcTy⟩ st = .error e st) :
    Miri.Interpreter.Cast.cast (Miri.Interpreter.ExecutionMachine.castHooks
        (refExecCfg rp) refLimits) c refLimits.casts
        ⟨.immediate imm, refLocalLayoutForTy rp.types srcTy⟩
        .IntToInt (tyIdFor rp.types dstTy)
        ⟨dref, refLocalLayoutForTy rp.types dstTy⟩ st = .error e st := by
  have h_rd := (castHooks_readImmediate rp c _ st).trans h_read
  dsimp only [Miri.Interpreter.Cast.cast, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_take, castHooks_destLayout, refLocalLayoutForTy_ty,
    beq_self_eq_true, ite_true_eq, eStateM_bind_pure, ite_false_eq,
    eStateM_bind_ok (castHooks_enforceValidity rp c _ st), ite_true_eq,
    castHooks_bind_typeInfo]
  simp only [refLocalLayoutForTy_ty]
  rw [h_src_res]
  cases srcTy with
  | int w s => dsimp only; rw [eStateM_bind_err h_rd]
  | bool => dsimp only; rw [eStateM_bind_err h_rd]
  | char => dsimp only; rw [eStateM_bind_err h_rd]
  | _ => cases h_il

/-- `Cast.cast .IntToInt` rejects a source type that is not integer-like. -/
private theorem cast_intToInt_nonIntLike (rp : RefProg) (c : Choice)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (dref : Miri.Interpreter.RuntimePlaceRef Miri.Memory.Provenance)
    (srcTy dstTy : MirTy) (imm : Miri.Interpreter.Immediate
        Miri.Memory.Provenance)
    (h_take : (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).takePendingMoveDeinit st = .ok false st)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_il : isIntLikeTy srcTy = false) :
    ∃ err st',
      Miri.Interpreter.Cast.cast (Miri.Interpreter.ExecutionMachine.castHooks
          (refExecCfg rp) refLimits) c refLimits.casts
          ⟨.immediate imm, refLocalLayoutForTy rp.types srcTy⟩
          .IntToInt (tyIdFor rp.types dstTy)
          ⟨dref, refLocalLayoutForTy rp.types dstTy⟩ st = .error err st' ∧
        stepErrorFaultKind err = .unsupported := by
  dsimp only [Miri.Interpreter.Cast.cast, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_take, castHooks_destLayout, refLocalLayoutForTy_ty,
    beq_self_eq_true, ite_true_eq, eStateM_bind_pure, ite_false_eq,
    eStateM_bind_ok (castHooks_enforceValidity rp c _ st), ite_true_eq,
    castHooks_bind_typeInfo]
  simp only [refLocalLayoutForTy_ty]
  rw [h_src_res]
  cases srcTy with
  | int w s => cases h_il
  | bool => cases h_il
  | char => cases h_il
  | _ => exact ⟨.unsupported "cast type unsupported", st, rfl, rfl⟩

/-- Lockstep of `Cast.cast .IntToInt` with `evalIntToIntCast` + `writePlace`
once the source value `v` has been read as the scalar `sc` whose `u128`
intermediate is `intLikeBits v = some n`. -/
private theorem cast_intToInt_some (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (amem : MemoryState)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory)
    (dstId : LocalId) (srcTy dstTy : MirTy) (dstSlot : LocalSlot)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance) (n : Nat) (sg : Bool)
    (v : Val)
    (h_dst_ty : MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (h_dst_sl : MirSemantics.getElem? slots dstId = some dstSlot)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_il : isIntLikeTy srcTy = true) (h_n : n < HPow.hPow 2 128)
    (h_read : Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
        ⟨.immediate imm, refLocalLayoutForTy rp.types srcTy⟩
            (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
            retPlace mem
        ctrl cm) =
      .ok ⟨.scalar sc, refLocalLayoutForTy rp.types srcTy⟩
          (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
          retPlace mem
        ctrl cm))
    (h_ilv : Miri.Interpreter.Cast.intLikeValue
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits) c sc
        (refLocalLayoutForTy rp.types srcTy)
            (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
            retPlace mem
        ctrl cm) =
      .ok (BitVec.ofNat 128 n, sg) (mkSimState rp defId rbody blockIdx stmtIdx
          bodyLocals slots retPlace mem
        ctrl cm))
    (h_ilb : intLikeBits v = some n) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    let res := Miri.Interpreter.Cast.cast
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp) refLimits)
        c refLimits.casts
      ⟨.immediate imm, refLocalLayoutForTy rp.types srcTy⟩
      .IntToInt (tyIdFor rp.types dstTy)
      ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types dstTy⟩ st
    match
      (match evalIntToIntCast v dstTy with
       | .error k => .error k
       | .ok r => writePlace slots amem dstId dstTy r :
         Except FaultKind (List LocalSlot × MemoryState)) with
    | .error k => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
    | .ok (slots', _) =>
      res = .ok () (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals
        slots' retPlace mem ctrl cm) := by
  intro st res
  have h_core := cast_intToInt_core rp c st
    (.local 0 dstId none (LocalsIdentity.ofAllocationToken 0)) srcTy
        dstTy imm sc
    n sg (castHooks_takePendingMoveDeinit rp defId rbody blockIdx stmtIdx
      bodyLocals slots retPlace mem ctrl cm) h_src_res h_dst_res h_il h_n h_read
    h_ilv
  dsimp only [res, evalIntToIntCast]
  rw [h_ilb]
  cases dstTy with
  | int w s =>
    dsimp only at h_core
    dsimp only
    rw [h_core]
    have h_aw := assertAndWrite_local_eq rp c defId rbody blockIdx stmtIdx
      bodyLocals slots amem retPlace mem ctrl cm dstId (.int w s) (.int w s)
      (.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 n)⟩) dstSlot h_dst_ty
      h_dst_sl h_dst_res h_inv
      (checkVal_scalar_of_trunc w s _ (truncateBits_idem w _))
    dsimp only at h_aw
    rw [beq_self_eq_true, ite_true_eq] at h_aw
    exact h_aw
  | char =>
    dsimp only at h_core
    dsimp only
    cases h_b : Nat.ble n 255 with
    | true =>
      rw [h_b, ite_true_eq] at h_core
      dsimp only [ite_true_eq]
      rw [h_core]
      have h_aw := assertAndWrite_local_eq rp c defId rbody blockIdx stmtIdx
        bodyLocals slots amem retPlace mem ctrl cm dstId .char .char
        (.char (Char.ofNat n)) dstSlot h_dst_ty h_dst_sl h_dst_res
        h_inv rfl
      dsimp only at h_aw
      rw [beq_self_eq_true, ite_true_eq] at h_aw
      exact h_aw
    | false =>
      rw [h_b, ite_false_eq] at h_core
      dsimp only [ite_false_eq]
      exact ⟨_, _, h_core, rfl⟩
  | _ => exact h_core

private theorem cast_intToInt_local_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (amem : MemoryState)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (dstId : LocalId) (srcTy dstTy : MirTy)
    (optVal : Option Val) (dstSlot : LocalSlot)
    (h_dst_ty : MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (h_dst_sl : MirSemantics.getElem? slots dstId = some dstSlot)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_sm : SlotMatchesTy srcTy (.immediate optVal)) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots
      retPlace mem ctrl cm
    let res := Miri.Interpreter.Cast.cast
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp) refLimits)
      c refLimits.casts
      ⟨.immediate (optValToMiriImm srcTy optVal), refLocalLayoutForTy
          rp.types srcTy⟩
      .IntToInt (tyIdFor rp.types dstTy)
      ⟨.local 0 dstId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types dstTy⟩ st
    match
      (if !isIntLikeTy srcTy then .error .unsupported
       else
         match optVal with
         | none => .error .undefined
         | some v =>
           match evalIntToIntCast v dstTy with
           | .error k => .error k
           | .ok r => writePlace slots amem dstId dstTy r :
         Except FaultKind (List LocalSlot × MemoryState)) with
    | .error k => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
    | .ok (slots', _) =>
      res = .ok () (mkSimState rp defId rbody blockIdx stmtIdx bodyLocals
        slots' retPlace mem ctrl cm) := by
  intro st res
  have h_take := castHooks_takePendingMoveDeinit rp defId rbody blockIdx stmtIdx
    bodyLocals slots retPlace mem ctrl cm
  have h_pmd : st.machine.pendingMoveDeinit = false := rfl
  cases h_il : isIntLikeTy srcTy with
  | false =>
    dsimp only [ite_not_false_eq]
    exact cast_intToInt_nonIntLike rp c st _ srcTy dstTy _ h_take h_src_res h_il
  | true =>
    dsimp only [ite_not_true_eq]
    cases optVal with
    | none =>
      dsimp only
      cases srcTy with
      | int w s =>
        let ⟨_, h_u⟩ := readImmediate_imm_int_uninit w s rp.types st h_pmd
        exact ⟨_, _, cast_intToInt_readErr rp c st _ _ dstTy _ _ h_take
          h_src_res h_il h_u, rfl⟩
      | bool =>
        let ⟨_, h_u⟩ := readImmediate_imm_bool_uninit rp.types st h_pmd
        exact ⟨_, _, cast_intToInt_readErr rp c st _ _ dstTy _ _ h_take
          h_src_res h_il h_u, rfl⟩
      | char =>
        let ⟨_, h_u⟩ := readImmediate_imm_char_uninit rp.types st h_pmd
        exact ⟨_, _, cast_intToInt_readErr rp c st _ _ dstTy _ _ h_take
          h_src_res h_il h_u, rfl⟩
      | _ => cases h_il
    | some v =>
      have h_cv : checkVal v srcTy = true := h_sm
      dsimp only
      cases srcTy with
      | int w s =>
        let ⟨bits, h_v⟩ := cast_checkVal_int_inv h_cv
        subst h_v
        cases s with
        | false =>
          exact cast_intToInt_some rp c defId rbody blockIdx stmtIdx
            bodyLocals slots amem retPlace mem ctrl cm dstId
            (.int w false) dstTy dstSlot _ _ (truncateBits w bits).toNat false _
            h_dst_ty h_dst_sl h_src_res h_dst_res h_inv h_il (BitVec.isLt _)
            (readImmediate_imm_int_ok w false bits rp.types st h_pmd)
            (by
              rw [cast_bv_ofNat_toNat]
              exact cast_intLikeValue_uint rp c w bits st h_src_res)
            rfl
        | true =>
          exact cast_intToInt_some rp c defId rbody blockIdx stmtIdx
            bodyLocals slots amem retPlace mem ctrl cm dstId
            (.int w true) dstTy dstSlot _ _
            (bvOfInt 128 (decodeScalar ⟨w, true, bits⟩)).toNat true _
            h_dst_ty h_dst_sl h_src_res h_dst_res h_inv h_il (BitVec.isLt _)
            (readImmediate_imm_int_ok w true bits rp.types st h_pmd)
            (by
              rw [cast_bv_ofNat_toNat, ← bitVec_ofInt_eq]
              exact cast_intLikeValue_sint rp c w bits st h_src_res)
            rfl
      | bool =>
        let ⟨b, h_v⟩ := cast_checkVal_bool_inv h_cv
        subst h_v
        exact cast_intToInt_some rp c defId rbody blockIdx stmtIdx
            bodyLocals slots amem retPlace mem ctrl cm dstId
          .bool dstTy dstSlot _ _ (if b then 1 else 0) false _
          h_dst_ty h_dst_sl h_src_res h_dst_res h_inv h_il
          (by cases b <;> decide)
          (readImmediate_imm_bool_ok b rp.types st h_pmd)
          (cast_intLikeValue_bool rp c b st h_src_res) rfl
      | char =>
        let ⟨ch, h_v⟩ := cast_checkVal_char_inv h_cv
        subst h_v
        exact cast_intToInt_some rp c defId rbody blockIdx stmtIdx
            bodyLocals slots amem retPlace mem ctrl cm dstId
          .char dstTy dstSlot _ _ ch.toNat false _
          h_dst_ty h_dst_sl h_src_res h_dst_res h_inv h_il
          (Nat.lt_trans ch.val.toBitVec.isLt (by decide))
          (readImmediate_imm_char_ok ch rp.types st h_pmd)
          (cast_intLikeValue_char rp c ch st h_src_res) rfl
      | _ => cases h_il

/-- Complete per-assignment step simulation of
`Miri.Interpreter.evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (refExecCfg
rp) refLimits)` against `Trusted.MirSemantics.evalStatement`'s `.assign` arm. -/
theorem evalRvalueIntoPlace_ref_eq (rp : RefProg) (c : Choice)
    (defId : DefId) (rbody : RefBody) (body : Body)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (slots : List LocalSlot)
    (amem : MemoryState)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (rdst : RefPlace) (dst : Place)
    (rrv : RefRvalue) (rv : Rvalue)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_supp : body.locals.all isSupportedScalarOrUnitTy = true)
    (h_inv : SlotsMatchTys body.locals slots)
    (h_pl : decodePlace rp.types rdst = some dst)
    (h_rv : decodeRvalue rp.types rrv = some rv)
    (h_discr_ty :
      ∀ (src : Place) (ety : EnumTy) (dstTy : MirTy),
        rv = .discriminant src →
        dst.projection.isEmpty = true →
        src.projection.isEmpty = true →
        MirSemantics.getElem? body.locals src.localId = some (.enum ety) →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        enumAdmitted ety = true →
        dstTy = .int ety.discrWidth ety.discrSigned)
    (h_ord_discr_ty :
      ∀ (src : Place) (dstTy : MirTy),
        rv = .discriminant src →
        dst.projection.isEmpty = true →
        src.projection.isEmpty = true →
        MirSemantics.getElem? body.locals src.localId = some .ordering →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        dstTy = .int .i8 true)
    (h_cast_ty :
      ∀ (opnd : Operand) (castTy dstTy : MirTy),
        rv = .cast .intToInt opnd castTy →
        dst.projection.isEmpty = true →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        dstTy = castTy) :
    let st := mkSimState rp defId rbody blockIdx stmtIdx body.locals slots
      retPlace mem ctrl cm
    let res := Miri.Interpreter.evalRvalueIntoPlace
      (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfg rp) refLimits)
      c (toMiriRvalue rp.types rrv) (toMiriPlace rdst) st
    match
      (if !dst.projection.isEmpty then
        .error .unsupported
      else
        match MirSemantics.getElem? body.locals dst.localId with
        | none => .error .unsupported
        | some dstTy =>
          match evalRvalue body.locals slots amem dstTy rv with
          | .error k => .error k
          | .ok (val, localsAfterRval, memAfterRval) =>
            writePlace localsAfterRval memAfterRval dst.localId dstTy val :
              Except FaultKind (List LocalSlot × MemoryState)) with
    | .error k =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = k
    | .ok (slots', _) =>
      res = .ok () (mkSimState rp defId rbody blockIdx stmtIdx body.locals
        slots' retPlace mem ctrl cm) := by
  intro st res
  have h_len : slots.length = body.locals.length := SlotsMatchTys.length_eq h_inv
  have h_loc_res : ∀ (id : LocalId) (ty : MirTy),
      MirSemantics.getElem? body.locals id = some ty →
      resolveTy rp.types (tyIdFor rp.types ty) = some ty := by
    intro id ty h_get
    let ⟨tid, _, h_ts⟩ := decodeBody_local_mem_types h_bdec h_get
    exact (resolveTy_tyIdFor_of_mem h_ts).2
  let ⟨h_did, h_demp⟩ := decodePlace_inv h_pl
  have h_rvh_eq :
      Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfg rp) refLimits =
      Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecutionConfig rp) refLimits := by
    dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks]
    rw [refExecCfg_idempotent]
  cases h_dpe : dst.projection.isEmpty with
  | false =>
    have h_rdpe : rdst.projection.isEmpty = false := h_demp.trans h_dpe
    have h_tp : toMiriPlace rdst = ⟨dst.localId, Array.mk [.Deref]⟩ := by
      dsimp only [toMiriPlace]; rw [h_rdpe, h_did]; rfl
    dsimp only [Bool.not, ite_true_eq]
    cases h_dty : MirSemantics.getElem? body.locals dst.localId with
    | none =>
      have h_err : res = .error (.stack (.invalidLocal dst.localId (liftLocals rp.types body.locals slots).length)) st := by
        dsimp only [res, Miri.Interpreter.evalRvalueIntoPlace, bind, Bind.bind]
        rw [h_rvh_eq, h_tp]
        change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
          c ⟨dst.localId, Array.mk [.Deref]⟩ true) _ st) = _
        rw [eStateM_bind_err (placeDynamic_evalPlace_oob rp c defId rbody blockIdx
          stmtIdx body.locals slots retPlace mem ctrl cm ⟨dst.localId, Array.mk [.Deref]⟩
          true (Or.inl h_dty))]
      exact ⟨_, _, h_err, rfl⟩
    | some dstTy =>
      let ⟨dstSlot, h_dsl⟩ := getElem?_some_of_length_eq h_len.symm h_dty
      have h_err : res = .error (.unsupported "projections unsupported on Day 1") st := by
        dsimp only [res, Miri.Interpreter.evalRvalueIntoPlace, bind, Bind.bind]
        rw [h_rvh_eq, h_tp]
        change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
          c ⟨dst.localId, Array.mk [.Deref]⟩ true) _ st) = _
        rw [eStateM_bind_err (placeDynamic_evalPlace_deref_err rp c defId rbody
          blockIdx stmtIdx body.locals slots retPlace mem ctrl cm dst.localId
          dstTy dstSlot h_dty h_dsl)]
      exact ⟨_, _, h_err, rfl⟩
  | true =>
    have h_rdpe : rdst.projection.isEmpty = true := h_demp.trans h_dpe
    have h_tp : toMiriPlace rdst = ⟨dst.localId, Array.empty⟩ := by
      dsimp only [toMiriPlace]; rw [h_rdpe, h_did]; rfl
    dsimp only [Bool.not, ite_false_eq]
    cases h_dty : MirSemantics.getElem? body.locals dst.localId with
    | none =>
      have h_err : res = .error (.stack (.invalidLocal dst.localId (liftLocals rp.types body.locals slots).length)) st := by
        dsimp only [res, Miri.Interpreter.evalRvalueIntoPlace, bind, Bind.bind]
        rw [h_rvh_eq, h_tp]
        change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
          c ⟨dst.localId, Array.empty⟩ true) _ st) = _
        rw [eStateM_bind_err (placeDynamic_evalPlace_oob rp c defId rbody blockIdx
          stmtIdx body.locals slots retPlace mem ctrl cm ⟨dst.localId, Array.empty⟩
          true (Or.inl h_dty))]
      exact ⟨_, _, h_err, rfl⟩
    | some dstTy =>
      let ⟨dstSlot, h_dsl⟩ := getElem?_some_of_length_eq h_len.symm h_dty
      have h_dst_res := h_loc_res dst.localId dstTy h_dty
      have h_dst_supp : isSupportedScalarOrUnitTy dstTy = true :=
        list_all_mirGetElem? (p := isSupportedScalarOrUnitTy) h_supp h_dty
      have h_eval_dst := placeDynamic_evalPlace_local_ok rp c defId rbody blockIdx
        stmtIdx body.locals slots retPlace mem ctrl cm dst.localId true dstTy dstSlot
        h_dty h_dsl
      have h_copy_for_deref_err :
          Miri.Interpreter.evalRvalueIntoPlace
            (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfg rp) refLimits)
            c (.CopyForDeref ⟨0, Array.empty⟩) (toMiriPlace rdst) st =
          .error (.invalidProgram "CopyForDeref in runtime MIR") st := by
        dsimp only [Miri.Interpreter.evalRvalueIntoPlace, bind, Bind.bind]
        rw [h_rvh_eq, h_tp]
        change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
          c ⟨dst.localId, Array.empty⟩ true) _ st) = _
        rw [eStateM_bind_ok h_eval_dst]; rfl
      cases rrv with
      | ref _ _ =>
        dsimp only [decodeRvalue, optMap] at h_rv
        cases h_p : decodePlace rp.types _ with
        | none => rw [h_p] at h_rv; cases h_rv
        | some _ =>
          rw [h_p] at h_rv; injection h_rv with h_eq; subst h_eq
          exact ⟨_, _, h_copy_for_deref_err, rfl⟩
      | addressOf _ _ =>
        dsimp only [decodeRvalue, optMap] at h_rv
        cases h_p : decodePlace rp.types _ with
        | none => rw [h_p] at h_rv; cases h_rv
        | some _ =>
          rw [h_p] at h_rv; injection h_rv with h_eq; subst h_eq
          exact ⟨_, _, h_copy_for_deref_err, rfl⟩
      | aggregateTuple rops =>
        dsimp only [decodeRvalue, optMap] at h_rv
        cases h_ops : mapOption (decodeOperand rp.types) rops with
        | none => rw [h_ops] at h_rv; cases h_rv
        | some _ =>
          rw [h_ops] at h_rv; injection h_rv with h_eq; subst h_eq
          exact ⟨_, _, h_copy_for_deref_err, rfl⟩
      | unsupported =>
        injection h_rv with h_eq; subst h_eq
        exact ⟨_, _, h_copy_for_deref_err, rfl⟩
      | cast k rop rtid =>
        dsimp only [decodeRvalue, optMap2] at h_rv
        cases h_op : decodeOperand rp.types rop with
        | none => rw [h_op] at h_rv; cases h_rv
        | some opnd =>
          cases h_ct : MirSemantics.getElem? rp.types rtid with
          | none => rw [h_op, h_ct] at h_rv; cases h_rv
          | some castTy =>
            rw [h_op, h_ct] at h_rv; injection h_rv with h_eq; subst h_eq
            cases k with
            | unsupported => exact ⟨_, _, h_copy_for_deref_err, rfl⟩
            | intToInt =>
              have h_dst_eq : dstTy = castTy :=
                h_cast_ty opnd castTy dstTy rfl h_dpe h_dty
              subst h_dst_eq
              have h_canon : canonicalTyId rp.types rtid = tyIdFor rp.types dstTy :=
                (canonicalTyId_of_some h_ct).1
              have h_ev := operandMachine_evalOperandAt_eq rp c defId rbody blockIdx
                stmtIdx body.locals slots amem retPlace mem ctrl cm
                (Miri.Interpreter.OperandPath.rvalue "operand") rop opnd
                isIntLikeTy none h_inv h_op
              have h_res_step :
                  res =
                    EStateM.bind
                      (Miri.Interpreter.OperandMachine.evalOperandAt
                        (Miri.Interpreter.ExecutionMachine.operandHooks
                          (refExecCfg rp))
                        c (Miri.Interpreter.OperandPath.rvalue "operand")
                        (toMiriOperand rp.types rop) none)
                      (fun srcOp =>
                        Miri.Interpreter.Cast.cast
                          (Miri.Interpreter.ExecutionMachine.castHooks
                            (refExecCfg rp) refLimits)
                          c refLimits.casts srcOp .IntToInt (tyIdFor rp.types dstTy)
                          ⟨.local 0 dst.localId none
                              (LocalsIdentity.ofAllocationToken 0),
                            refLocalLayoutForTy rp.types dstTy⟩)
                      st := by
                dsimp only [res, toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
                  bind, Bind.bind]
                rw [h_rvh_eq, h_tp, h_canon]
                change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
                  (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
                  c ⟨dst.localId, Array.empty⟩ true) _ st) = _
                rw [eStateM_bind_ok h_eval_dst]
                rfl
              rw [h_res_step]
              dsimp only [evalRvalue]
              cases h_es : evalOperandToSlot body.locals slots amem isIntLikeTy
                  opnd with
              | error k =>
                rw [h_es] at h_ev
                let ⟨err, st', h_err, h_fk⟩ := h_ev
                rw [eStateM_bind_err h_err]
                exact ⟨err, st', rfl, h_fk⟩
              | ok tup =>
                let ⟨srcTy, optVal, slots₁, amem₁⟩ := tup
                rw [h_es] at h_ev
                rw [eStateM_bind_ok h_ev]
                let ⟨h_inv₁, h_sm₁, _⟩ := evalOperandToSlot_slotsMatchTys h_inv h_es
                have h_src_res := evalOperandToSlot_res rp h_op h_loc_res h_es
                let ⟨dstSlot₁, h_dsl₁⟩ := getElem?_some_of_length_eq
                  (SlotsMatchTys.length_eq h_inv₁).symm h_dty
                have h_c := cast_intToInt_local_eq rp c defId rbody blockIdx
                  stmtIdx body.locals slots₁ amem₁ retPlace mem ctrl cm dst.localId
                  srcTy dstTy optVal dstSlot₁ h_dty h_dsl₁ h_src_res h_dst_res
                  h_inv₁ h_sm₁
                dsimp only at h_c
                dsimp only
                cases h_il : isIntLikeTy srcTy with
                | false =>
                  rw [h_il] at h_c
                  exact h_c
                | true =>
                  rw [h_il] at h_c
                  dsimp only [Bool.not, ite_false_eq] at h_c
                  dsimp only [Bool.not, ite_false_eq]
                  cases optVal with
                  | none => exact h_c
                  | some v =>
                    dsimp only at h_c
                    dsimp only
                    cases h_cst : evalIntToIntCast v dstTy with
                    | error k => rw [h_cst] at h_c; exact h_c
                    | ok r => rw [h_cst] at h_c; exact h_c
      | use rop =>
        dsimp only [decodeRvalue, optMap] at h_rv
        cases h_op : decodeOperand rp.types rop with
        | none => rw [h_op] at h_rv; cases h_rv
        | some op =>
          rw [h_op] at h_rv; injection h_rv with h_eq; subst h_eq
          have h_ev := operandMachine_evalOperandAt_eq rp c defId rbody blockIdx
            stmtIdx body.locals slots amem retPlace mem ctrl cm
            (Miri.Interpreter.OperandPath.rvalue "operand") rop op
            (fun srcTy => MirTy.beq srcTy dstTy)
            (some (refLocalLayoutForTy rp.types dstTy)) h_inv h_op
          have h_res_step :
              res =
                EStateM.bind
                  (Miri.Interpreter.OperandMachine.evalOperandAt
                    (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
                    c (Miri.Interpreter.OperandPath.rvalue "operand")
                    (toMiriOperand rp.types rop)
                    (some (refLocalLayoutForTy rp.types dstTy)))
                  (fun srcOp =>
                    Miri.Interpreter.MachineHooks.withRetagMode .None
                      (Miri.Interpreter.copyRuntimePlace
                        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                        (refExecCfg rp).copy c srcOp
                        ⟨.local 0 dst.localId none (LocalsIdentity.ofAllocationToken 0),
                          refLocalLayoutForTy rp.types dstTy⟩ false))
                  st := by
            dsimp only [res, toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
              bind, Bind.bind]
            rw [h_rvh_eq, h_tp]
            change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
              (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
              c ⟨dst.localId, Array.empty⟩ true) _ st) = _
            rw [eStateM_bind_ok h_eval_dst]
            rfl
          rw [h_res_step]
          dsimp only [evalRvalue]
          cases h_es : evalOperandToSlot body.locals slots amem
              (fun srcTy => MirTy.beq srcTy dstTy) op with
          | error k =>
            rw [h_es] at h_ev
            let ⟨err, st', h_err, h_fk⟩ := h_ev
            rw [eStateM_bind_err h_err]
            exact ⟨err, st', rfl, h_fk⟩
          | ok tup =>
            let ⟨srcTy, optVal, slots₁, amem₁⟩ := tup
            rw [h_es] at h_ev
            rw [eStateM_bind_ok h_ev]
            let ⟨h_inv₁, h_sm₁, _⟩ := evalOperandToSlot_slotsMatchTys h_inv h_es
            have h_src_res := evalOperandToSlot_res rp h_op h_loc_res h_es
            let ⟨dstSlot₁, h_dsl₁⟩ := getElem?_some_of_length_eq
              (SlotsMatchTys.length_eq h_inv₁).symm h_dty
            have h_wr_none :
                Miri.Interpreter.MachineHooks.withRetagMode .None
                  (Miri.Interpreter.copyRuntimePlace
                    (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                    (refExecCfg rp).copy c
                    ⟨.immediate (optValToMiriImm srcTy optVal),
                      refLocalLayoutForTy rp.types srcTy⟩
                    ⟨.local 0 dst.localId none (LocalsIdentity.ofAllocationToken 0),
                      refLocalLayoutForTy rp.types dstTy⟩ false)
                  (mkSimState rp defId rbody blockIdx stmtIdx body.locals slots₁
                    retPlace mem ctrl cm) =
                Miri.Interpreter.copyRuntimePlace
                  (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                  (refExecCfg rp).copy c
                  ⟨.immediate (optValToMiriImm srcTy optVal),
                    refLocalLayoutForTy rp.types srcTy⟩
                  ⟨.local 0 dst.localId none (LocalsIdentity.ofAllocationToken 0),
                    refLocalLayoutForTy rp.types dstTy⟩ false
                  (mkSimState rp defId rbody blockIdx stmtIdx body.locals slots₁
                    retPlace mem ctrl cm) := rfl
            rw [h_wr_none]
            have h_cp := copyRuntimePlace_imm_to_local rp c defId rbody blockIdx
              stmtIdx body.locals slots₁ amem₁ retPlace mem ctrl cm dst.localId srcTy
              dstTy optVal dstSlot₁ h_dty h_dsl₁ h_src_res h_dst_res h_dst_supp
              h_inv₁ h_sm₁
            dsimp only
            cases h_b : MirTy.beq srcTy dstTy with
            | false => rw [h_b] at h_cp; exact h_cp
            | true =>
              rw [h_b] at h_cp
              cases optVal with
              | none => exact h_cp
              | some v => exact h_cp
      | binaryOp op rlhs rrhs =>
        dsimp only [decodeRvalue, optMap2] at h_rv
        cases h_l : decodeOperand rp.types rlhs with
        | none => rw [h_l] at h_rv; cases h_rv
        | some lhs =>
          cases h_r : decodeOperand rp.types rrhs with
          | none => rw [h_l, h_r] at h_rv; cases h_rv
          | some rhs =>
            rw [h_l, h_r] at h_rv; injection h_rv with h_eq; subst h_eq
            have h_res_step :
                res =
                  EStateM.bind
                    (Miri.Interpreter.OperandMachine.evalOperandAt
                      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
                      c (Miri.Interpreter.OperandPath.rvalue "left")
                      (toMiriOperand rp.types rlhs)
                      (if (toMiriBinOp op).leftHomogeneous then
                        some (refLocalLayoutForTy rp.types dstTy) else none))
                    (fun leftOp =>
                      EStateM.bind
                        (Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig leftOp)
                        (fun leftImm =>
                          EStateM.bind
                            (Miri.Interpreter.OperandMachine.evalOperandAt
                              (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
                              c (Miri.Interpreter.OperandPath.rvalue "right")
                              (toMiriOperand rp.types rrhs)
                              (if (toMiriBinOp op).rightHomogeneous then
                                some leftImm.layout else none))
                            (fun rightOp =>
                              EStateM.bind
                                (Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig rightOp)
                                (fun rightImm =>
                                  EStateM.bind
                                    (Miri.Interpreter.ScalarOps.binary
                                      (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp))
                                      c (toMiriBinOp op) leftImm rightImm)
                                    (fun outImm =>
                                      EStateM.bind
                                        (if (outImm.layout == refLocalLayoutForTy rp.types dstTy) = true then
                                          EStateM.pure ()
                                        else EStateM.throw (.invalidProgram "rvalue result layout mismatch"))
                                        (fun _ =>
                                          Miri.Interpreter.writePlaceImmediate
                                            (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                                            c outImm.imm
                                            ⟨.local 0 dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                              refLocalLayoutForTy rp.types dstTy⟩))))))
                    st := by
              dsimp only [res, toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
                bind, Bind.bind]
              rw [h_rvh_eq, h_tp]
              change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
                (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
                c ⟨dst.localId, Array.empty⟩ true) _ st) = _
              rw [eStateM_bind_ok h_eval_dst]
              rfl
            rw [h_res_step, ← eStateM_bind_assoc]
            dsimp only [evalRvalue]
            have h_evL := evalPrimitiveOperand_ref_eq rp c defId rbody blockIdx
              stmtIdx body.locals slots amem retPlace mem ctrl cm
              (Miri.Interpreter.OperandPath.rvalue "left") rlhs lhs
              (if (toMiriBinOp op).leftHomogeneous then
                some (refLocalLayoutForTy rp.types dstTy) else none) h_inv h_l
                h_loc_res
            cases h_pL : evalPrimitiveOperand body.locals slots amem lhs with
            | error k =>
              rw [h_pL] at h_evL
              let ⟨err, st', h_err, h_fk⟩ := h_evL
              rw [eStateM_bind_err h_err]
              exact ⟨err, st', rfl, h_fk⟩
            | ok tupL =>
              let ⟨lVal, slots₁, amem₁⟩ := tupL
              rw [h_pL] at h_evL
              let ⟨lTy, h_lcv, h_lpr, h_lres, h_okL⟩ := h_evL
              dsimp only
              rw [eStateM_bind_ok h_okL, ← eStateM_bind_assoc]
              have h_inv₁ := (evalPrimitiveOperand_slotsMatchTys h_inv h_pL).1
              have h_evR := evalPrimitiveOperand_ref_eq rp c defId rbody blockIdx
                stmtIdx body.locals slots₁ amem₁ retPlace mem ctrl cm
                (Miri.Interpreter.OperandPath.rvalue "right") rrhs rhs
                (if (toMiriBinOp op).rightHomogeneous then
                  some (refLocalLayoutForTy rp.types lTy) else none) h_inv₁ h_r
                  h_loc_res
              cases h_pR : evalPrimitiveOperand body.locals slots₁ amem₁ rhs with
              | error k =>
                rw [h_pR] at h_evR
                let ⟨err, st', h_err, h_fk⟩ := h_evR
                rw [eStateM_bind_err h_err]
                exact ⟨err, st', rfl, h_fk⟩
              | ok tupR =>
                let ⟨rVal, slots₂, amem₂⟩ := tupR
                rw [h_pR] at h_evR
                let ⟨rTy, h_rcv, h_rpr, _, h_okR⟩ := h_evR
                dsimp only
                rw [eStateM_bind_ok h_okR]
                have h_inv₂ := (evalPrimitiveOperand_slotsMatchTys h_inv₁ h_pR).1
                have h_bin := scalarOps_binary_ref_eq rp c op lTy rTy lVal rVal
                  (mkSimState rp defId rbody blockIdx stmtIdx body.locals slots₂
                    retPlace mem ctrl cm) h_lcv h_lpr h_rcv h_rpr h_lres
                cases h_eb : evalBinOp op lVal rVal with
                | error k =>
                  rw [h_eb] at h_bin
                  let ⟨err, st', h_err, h_fk⟩ := h_bin
                  rw [eStateM_bind_err h_err]
                  exact ⟨err, st', rfl, h_fk⟩
                | ok v =>
                  rw [h_eb] at h_bin
                  let ⟨resTy, h_vcv, h_vpr, h_okB⟩ := h_bin
                  rw [eStateM_bind_ok h_okB, eStateM_bind_ite_pure]
                  let ⟨dstSlot₂, h_dsl₂⟩ := getElem?_some_of_length_eq
                    (SlotsMatchTys.length_eq h_inv₂).symm h_dty
                  exact assertAndWrite_local_eq rp c defId rbody blockIdx stmtIdx
                    body.locals slots₂ amem₂ retPlace mem ctrl cm dst.localId resTy
                    dstTy v dstSlot₂ h_dty h_dsl₂
                    h_dst_res h_inv₂
                    h_vcv
      | unaryOp op rop =>
        dsimp only [decodeRvalue, optMap] at h_rv
        cases h_op : decodeOperand rp.types rop with
        | none => rw [h_op] at h_rv; cases h_rv
        | some opnd =>
          rw [h_op] at h_rv; injection h_rv with h_eq; subst h_eq
          have h_res_step :
              res =
                EStateM.bind
                  (Miri.Interpreter.OperandMachine.evalOperandAt
                    (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
                    c (Miri.Interpreter.OperandPath.rvalue "operand")
                    (toMiriOperand rp.types rop)
                    (if (toMiriUnOp op).homogeneous then
                      some (refLocalLayoutForTy rp.types dstTy) else none))
                  (fun opVal =>
                    EStateM.bind
                      (Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig opVal)
                      (fun opImm =>
                        EStateM.bind
                          (Miri.Interpreter.ScalarOps.unary
                            (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfg rp))
                            c (toMiriUnOp op) opImm)
                          (fun outImm =>
                            EStateM.bind
                              (if (outImm.layout == refLocalLayoutForTy rp.types dstTy) = true then
                                EStateM.pure ()
                              else EStateM.throw (.invalidProgram "rvalue result layout mismatch"))
                              (fun _ =>
                                Miri.Interpreter.writePlaceImmediate
                                  (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                                  c outImm.imm
                                  ⟨.local 0 dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                    refLocalLayoutForTy rp.types dstTy⟩))))
                  st := by
            dsimp only [res, toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
              bind, Bind.bind]
            rw [h_rvh_eq, h_tp]
            change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
              (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
              c ⟨dst.localId, Array.empty⟩ true) _ st) = _
            rw [eStateM_bind_ok h_eval_dst]
            rfl
          rw [h_res_step, ← eStateM_bind_assoc]
          dsimp only [evalRvalue]
          have h_evO := evalPrimitiveOperand_ref_eq rp c defId rbody blockIdx
            stmtIdx body.locals slots amem retPlace mem ctrl cm
            (Miri.Interpreter.OperandPath.rvalue "operand") rop opnd
            (if (toMiriUnOp op).homogeneous then
              some (refLocalLayoutForTy rp.types dstTy) else none) h_inv h_op
              h_loc_res
          cases h_pO : evalPrimitiveOperand body.locals slots amem opnd with
          | error k =>
            rw [h_pO] at h_evO
            let ⟨err, st', h_err, h_fk⟩ := h_evO
            rw [eStateM_bind_err h_err]
            exact ⟨err, st', rfl, h_fk⟩
          | ok tupO =>
            let ⟨v, slots₁, amem₁⟩ := tupO
            rw [h_pO] at h_evO
            let ⟨vTy, h_vcv, h_vpr, _, h_okO⟩ := h_evO
            dsimp only
            rw [eStateM_bind_ok h_okO]
            have h_inv₁ := (evalPrimitiveOperand_slotsMatchTys h_inv h_pO).1
            have h_un := scalarOps_unary_ref_eq rp c op vTy v
              (mkSimState rp defId rbody blockIdx stmtIdx body.locals slots₁
                retPlace mem ctrl cm) h_vcv h_vpr
            cases h_eu : evalUnOp op v with
            | error k =>
              rw [h_eu] at h_un
              let ⟨err, st', h_err, h_fk⟩ := h_un
              rw [eStateM_bind_err h_err]
              exact ⟨err, st', rfl, h_fk⟩
            | ok u =>
              rw [h_eu] at h_un
              let ⟨resTy, h_ucv, h_upr, h_okU⟩ := h_un
              rw [eStateM_bind_ok h_okU, eStateM_bind_ite_pure]
              let ⟨dstSlot₁, h_dsl₁⟩ := getElem?_some_of_length_eq
                (SlotsMatchTys.length_eq h_inv₁).symm h_dty
              exact assertAndWrite_local_eq rp c defId rbody blockIdx stmtIdx
                body.locals slots₁ amem₁ retPlace mem ctrl cm dst.localId resTy dstTy
                u dstSlot₁ h_dty h_dsl₁
                h_dst_res h_inv₁ h_ucv
      | discriminant rsrc =>
        dsimp only [decodeRvalue, optMap] at h_rv
        cases h_sp : decodePlace rp.types rsrc with
        | none => rw [h_sp] at h_rv; cases h_rv
        | some src =>
          rw [h_sp] at h_rv; injection h_rv with h_eq; subst h_eq
          have h_res_step :
              res =
                EStateM.bind
                  (Miri.Interpreter.OperandMachine.evalPlaceToOp
                    (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
                    c (toMiriPlace rsrc) none)
                  (fun srcOp =>
                    EStateM.bind
                      (Miri.Interpreter.Discriminant.readDiscriminant
                        (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp))
                        c srcOp)
                      (fun variant =>
                        EStateM.bind
                          (Miri.Interpreter.Discriminant.discriminantForVariant
                            (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp))
                            c srcOp.layout.ty variant)
                          (fun discr =>
                            Miri.Interpreter.writePlaceImmediate
                              (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                              c discr.imm
                              ⟨.local 0 dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                refLocalLayoutForTy rp.types dstTy⟩)))
                  st := by
            dsimp only [res, toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
              bind, Bind.bind]
            rw [h_rvh_eq, h_tp]
            change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
              (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
              c ⟨dst.localId, Array.empty⟩ true) _ st) = _
            rw [eStateM_bind_ok h_eval_dst]
            rfl
          rw [h_res_step]
          have h_evS := operandMachine_evalPlaceToOp_eq rp c defId rbody blockIdx
            stmtIdx body.locals slots retPlace mem ctrl cm rsrc src none h_sp h_inv
          dsimp only [evalRvalue]
          cases h_sty : MirSemantics.getElem? body.locals src.localId with
          | none =>
            rw [h_sty] at h_evS
            let ⟨err, st', h_err, h_fk⟩ := h_evS
            rw [eStateM_bind_err h_err]
            exact ⟨err, st', rfl, h_fk⟩
          | some srcTy =>
            cases h_ssl : MirSemantics.getElem? slots src.localId with
            | none =>
              rw [h_sty, h_ssl] at h_evS
              let ⟨err, st', h_err, h_fk⟩ := h_evS
              rw [eStateM_bind_err h_err]
              exact ⟨err, st', rfl, h_fk⟩
            | some srcSlot =>
              rw [h_sty, h_ssl] at h_evS
              cases srcSlot with
              | dead =>
                let ⟨err, st', h_err, h_fk⟩ := h_evS
                rw [eStateM_bind_err h_err]
                exact ⟨err, st', rfl, h_fk⟩
              | indirect _ =>
                exact False.elim (SlotsMatchTys.not_indirect h_inv h_sty h_ssl)
              | immediate srcOpt =>
                cases h_spe : src.projection.isEmpty with
                | false =>
                  rw [h_spe] at h_evS
                  let ⟨err, st', h_err, h_fk⟩ := h_evS
                  rw [eStateM_bind_err h_err]
                  exact ⟨err, st', rfl, h_fk⟩
                | true =>
                  rw [h_spe] at h_evS
                  dsimp only
                  rw [ite_not_true_eq, eStateM_bind_ok h_evS]
                  have h_src_res := h_loc_res src.localId srcTy h_sty
                  have h_dl_non_enum :
                      ∀ (t : MirTy),
                        (match t with | .enum _ | .ordering => False | _ => True) →
                        resolveTy rp.types (tyIdFor rp.types t) = some t →
                        Miri.Interpreter.Discriminant.readDiscriminant
                          (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                          ⟨.immediate (optValToMiriImm t srcOpt),
                            refLocalLayoutForTy rp.types t⟩ st =
                          .error (.unsupported "discriminant on non-enum type") st := by
                    intro t h_ne h_tr
                    dsimp only [Miri.Interpreter.Discriminant.readDiscriminant, bind, Bind.bind]
                    change (EStateM.bind
                      ((Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).discriminantLayout
                        c (tyIdFor rp.types t)) _ st) = _
                    dsimp only [EStateM.bind]
                    rw [discrHooks_discriminantLayout rp c t st h_tr]
                    cases t with
                    | enum _ => exact False.elim h_ne
                    | ordering => exact False.elim h_ne
                    | _ => rfl
                  cases srcTy with
                  | bool | int _ _ | unit | never | char | tuple _ | ref _ _
                  | rawPtr _ _ | unsupported =>
                    rw [eStateM_bind_err (h_dl_non_enum _ trivial h_src_res)]
                    exact ⟨_, _, rfl, rfl⟩
                  | ordering =>
                    have h_dst_eq : dstTy = .int .i8 true :=
                      h_ord_discr_ty src dstTy rfl h_dpe h_spe h_sty h_dty
                    subst h_dst_eq
                    have h_smS := SlotsMatchTys.getElem? h_inv h_sty h_ssl
                    dsimp only [evalOrderingDiscriminantOfVal]
                    cases srcOpt with
                    | none =>
                      dsimp only [optValToMiriImm]
                      let ⟨_, h_ub⟩ := discrHooks_readDiscriminant_ordering_uninit_ub
                        rp c st h_src_res rfl
                      rw [eStateM_bind_err h_ub]
                      exact ⟨_, _, rfl, rfl⟩
                    | some sv =>
                      let ⟨ord, h_sv_eq⟩ := checkVal_ordering_inv h_smS
                      subst h_sv_eq
                      have h_rd := discrHooks_readDiscriminant_ordering_ok rp c ord
                        st h_src_res rfl
                      have h_dfv := discrHooks_discriminantForVariant_ordering_ok rp
                        c ord st h_src_res
                      dsimp only [optValToMiriImm]
                      rw [eStateM_bind_ok h_rd]
                      change (match
                          (_ : Except FaultKind (List LocalSlot × MemoryState)) with
                        | Except.error k =>
                          ∃ err st',
                            EStateM.bind
                              (Miri.Interpreter.Discriminant.discriminantForVariant
                                _ c (tyIdFor rp.types .ordering)
                                (orderingVariantIdx ord)) _ st =
                              EStateM.Result.error err st' ∧ _
                        | Except.ok (slots', _) =>
                          EStateM.bind
                            (Miri.Interpreter.Discriminant.discriminantForVariant
                              _ c (tyIdFor rp.types .ordering)
                              (orderingVariantIdx ord)) _ st = _)
                      rw [eStateM_bind_ok h_dfv]
                      have h_aw := assertAndWrite_local_eq rp c defId rbody blockIdx
                        stmtIdx body.locals slots amem retPlace mem ctrl cm dst.localId
                        (.int .i8 true) (.int .i8 true)
                        (.scalar ⟨.i8, true, BitVec.ofNat 128 (orderingTagBits ord)⟩)
                        dstSlot h_dty h_dsl h_dst_res h_inv (checkVal_orderingDiscr ord)
                      dsimp only at h_aw
                      rw [beq_self_eq_true, ite_true_eq] at h_aw
                      exact h_aw
                  | enum ety =>
                    dsimp only [evalDiscriminantOfVal]
                    cases h_adm : enumAdmitted ety with
                    | false =>
                      have h_ref_adm : refEnumAdmitted ety = false := by
                        rw [refEnumAdmitted_eq]; exact h_adm
                      have h_dl_err :
                          Miri.Interpreter.Discriminant.readDiscriminant
                            (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                            ⟨.immediate (optValToMiriImm (.enum ety) srcOpt),
                              refLocalLayoutForTy rp.types (.enum ety)⟩ st =
                            .error (.unsupported "unadmitted enum in discriminantLayout") st := by
                        dsimp only [Miri.Interpreter.Discriminant.readDiscriminant,
                          bind, Bind.bind]
                        change (EStateM.bind
                          ((Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).discriminantLayout
                            c (tyIdFor rp.types (.enum ety))) _ st) = _
                        dsimp only [EStateM.bind]
                        rw [discrHooks_discriminantLayout rp c (.enum ety) st h_src_res]
                        dsimp only; rw [h_ref_adm]; rfl
                      rw [eStateM_bind_err h_dl_err]
                      exact ⟨_, _, rfl, rfl⟩
                    | true =>
                      have h_dst_eq : dstTy = .int ety.discrWidth ety.discrSigned :=
                        h_discr_ty src ety dstTy rfl h_dpe h_spe h_sty h_dty h_adm
                      subst h_dst_eq
                      have h_smS := SlotsMatchTys.getElem? h_inv h_sty h_ssl
                      have h_ref_adm : refEnumAdmitted ety = true := by
                        rw [refEnumAdmitted_eq]; exact h_adm
                      dsimp only [Bool.not, ite_false_eq]
                      cases h_tr : ety.tagRepr with
                      | zeroSized =>
                        have h_zst_rd :
                            Miri.Interpreter.Discriminant.readDiscriminant
                              (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                              ⟨.immediate (optValToMiriImm (.enum ety) srcOpt),
                                refLocalLayoutForTy rp.types (.enum ety)⟩ st =
                              .ok 0 st := by
                          dsimp only [Miri.Interpreter.Discriminant.readDiscriminant, bind, Bind.bind]
                          have h_dl : (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).discriminantLayout
                              c (tyIdFor rp.types (.enum ety)) st =
                              .ok (refLocalLayoutForTy rp.types (.int ety.discrWidth ety.discrSigned)) st := by
                            rw [discrHooks_discriminantLayout rp c (.enum ety) st h_src_res]
                            dsimp only; rw [h_ref_adm]; rfl
                          change (EStateM.bind
                            ((Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).discriminantLayout
                              c (tyIdFor rp.types (.enum ety))) _ st) = _
                          rw [eStateM_bind_ok h_dl]
                          have h_vars : (refLocalLayoutForTy rp.types (.enum ety)).layout.variants = .Single 0 := by
                            dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
                            rw [h_tr]; rfl
                          have h_uninh : (refLocalLayoutForTy rp.types (.enum ety)).layout.isUninhabited = false := by
                            dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
                            rw [h_tr]; rfl
                          rw [h_vars, h_uninh]; rfl
                        let ⟨h_all, _, h_tag_len⟩ := enumAdmitted_parts h_adm
                        rw [h_tr] at h_tag_len
                        have h_len1 : ety.discriminants.length = 1 :=
                          Nat.eq_of_beq_eq_true h_tag_len
                        let ⟨disc, h_d0⟩ := mirGetElem?_some_of_lt
                          (xs := ety.discriminants) (i := 0) (by rw [h_len1]; exact Nat.zero_lt_one)
                        have h_dfv := discrHooks_discriminantForVariant_ok rp c ety 0 disc st
                          h_adm h_src_res h_d0
                        have hd_blt : Nat.blt disc (Nat.pow 2 ety.discrWidth.bitWidth) = true :=
                          list_all_mirGetElem?
                            (p := fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth))
                            h_all h_d0
                        have hd_mod : disc < Nat.pow 2 ety.discrWidth.bitWidth :=
                          Nat.blt_eq.mp hd_blt
                        have hd_u128 : disc < Nat.pow 2 128 :=
                          Nat.lt_of_lt_of_le hd_mod (intWidth_pow_le_128 ety.discrWidth)
                        have h_trunc_eq :
                            truncateBits ety.discrWidth (BitVec.ofNat 128 disc) =
                              BitVec.ofNat 128 disc := by
                          apply BitVec.eq_of_toNat_eq
                          rw [toNat_truncateBits, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt hd_u128]
                          exact Nat.mod_eq_of_lt hd_mod
                        have h_cv_d :
                            checkVal (.scalar ⟨ety.discrWidth, ety.discrSigned,
                              truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
                              (.int ety.discrWidth ety.discrSigned) = true :=
                          checkVal_scalar_of_trunc ety.discrWidth ety.discrSigned _
                            (truncateBits_idem ety.discrWidth (BitVec.ofNat 128 disc))
                        have h_finish_0 :
                            match writePlace slots amem dst.localId
                                (.int ety.discrWidth ety.discrSigned)
                                (.scalar ⟨ety.discrWidth, ety.discrSigned,
                                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩) with
                            | .error k =>
                              ∃ err st',
                                Miri.Interpreter.writePlaceImmediate
                                  (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place c
                                  (.scalar (.fromScalarInt (miriScalar ety.discrWidth (BitVec.ofNat 128 disc))))
                                  ⟨.local 0 dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                    refLocalLayoutForTy rp.types (.int ety.discrWidth ety.discrSigned)⟩ st =
                                  .error err st' ∧ stepErrorFaultKind err = k
                            | .ok (slots', _) =>
                              Miri.Interpreter.writePlaceImmediate
                                (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place c
                                (.scalar (.fromScalarInt (miriScalar ety.discrWidth (BitVec.ofNat 128 disc))))
                                ⟨.local 0 dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                  refLocalLayoutForTy rp.types (.int ety.discrWidth ety.discrSigned)⟩ st =
                                .ok () (mkSimState rp defId rbody blockIdx stmtIdx
                                  body.locals slots' retPlace mem ctrl cm) := by
                          have h_aw := assertAndWrite_local_eq rp c defId rbody blockIdx
                            stmtIdx body.locals slots amem retPlace mem ctrl cm dst.localId
                            (.int ety.discrWidth ety.discrSigned)
                            (.int ety.discrWidth ety.discrSigned)
                            (.scalar ⟨ety.discrWidth, ety.discrSigned,
                              truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
                            dstSlot h_dty h_dsl h_dst_res h_inv h_cv_d
                          dsimp only at h_aw
                          rw [beq_self_eq_true, ite_true_eq] at h_aw
                          dsimp only [valToMiriImmediate] at h_aw
                          have h_ms :
                              miriScalar ety.discrWidth (truncateBits ety.discrWidth (BitVec.ofNat 128 disc)) =
                                miriScalar ety.discrWidth (BitVec.ofNat 128 disc) := by
                            rw [h_trunc_eq]
                          rw [h_ms] at h_aw
                          exact h_aw
                        rw [eStateM_bind_ok h_zst_rd]
                        change (match (_ : Except FaultKind (List LocalSlot × MemoryState)) with | Except.error k => ∃ err st', EStateM.bind (Miri.Interpreter.Discriminant.discriminantForVariant _ c (tyIdFor rp.types (.enum ety)) 0) _ st = EStateM.Result.error err st' ∧ _ | Except.ok (slots', _) => EStateM.bind (Miri.Interpreter.Discriminant.discriminantForVariant _ c (tyIdFor rp.types (.enum ety)) 0) _ st = _)
                        rw [eStateM_bind_ok h_dfv]
                        cases srcOpt with
                        | none =>
                          dsimp only; rw [h_d0]; exact h_finish_0
                        | some sv =>
                          let ⟨v, h_sv_eq, _, h_v_lt⟩ := checkVal_enum_inv h_smS
                          subst h_sv_eq
                          rw [h_len1] at h_v_lt
                          have h_v0 : v = 0 := by
                            cases v with
                            | zero => rfl
                            | succ n =>
                              exact False.elim (Nat.not_lt_zero n
                                (Nat.lt_of_succ_lt_succ h_v_lt))
                          subst h_v0
                          dsimp only
                          rw [EnumTy.beq_refl]
                          dsimp only [Nat.beq, Bool.and_self, ite_true_eq]
                          rw [h_d0]
                          exact h_finish_0
                      | scalar tagW tagS =>
                        cases srcOpt with
                        | none =>
                          dsimp only [optValToMiriImm]
                          let ⟨msg, h_ub⟩ := discrHooks_readDiscriminant_scalar_uninit_ub
                            rp c ety tagW tagS st h_tr h_adm h_src_res rfl
                          rw [eStateM_bind_err h_ub]
                          exact ⟨_, _, rfl, rfl⟩
                        | some sv =>
                          let ⟨v, h_sv_eq, _, h_v_lt⟩ := checkVal_enum_inv h_smS
                          subst h_sv_eq
                          let ⟨disc, h_dv⟩ := mirGetElem?_some_of_lt h_v_lt
                          have h_imm_eq :
                              optValToMiriImm (.enum ety) (some (.enumVal ety v)) =
                                .scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))) := by
                            dsimp only [optValToMiriImm, valToMiriImmediate]
                            rw [h_tr, h_dv]
                          rw [h_imm_eq]
                          have h_rd := discrHooks_readDiscriminant_scalar_ok rp c ety
                            tagW tagS v disc st h_tr h_adm h_src_res h_dv rfl
                          have h_dfv := discrHooks_discriminantForVariant_ok rp c ety
                            v disc st h_adm h_src_res h_dv
                          rw [eStateM_bind_ok h_rd]
                          change (match (_ : Except FaultKind (List LocalSlot × MemoryState)) with | Except.error k => ∃ err st', EStateM.bind (Miri.Interpreter.Discriminant.discriminantForVariant _ c (tyIdFor rp.types (.enum ety)) v) _ st = EStateM.Result.error err st' ∧ _ | Except.ok (slots', _) => EStateM.bind (Miri.Interpreter.Discriminant.discriminantForVariant _ c (tyIdFor rp.types (.enum ety)) v) _ st = _)
                          rw [eStateM_bind_ok h_dfv]
                          let ⟨h_all, _, _⟩ := enumAdmitted_parts h_adm
                          have hd_blt : Nat.blt disc (Nat.pow 2 ety.discrWidth.bitWidth) = true :=
                            list_all_mirGetElem?
                              (p := fun d => Nat.blt d (Nat.pow 2 ety.discrWidth.bitWidth))
                              h_all h_dv
                          have hd_mod : disc < Nat.pow 2 ety.discrWidth.bitWidth :=
                            Nat.blt_eq.mp hd_blt
                          have hd_u128 : disc < Nat.pow 2 128 :=
                            Nat.lt_of_lt_of_le hd_mod (intWidth_pow_le_128 ety.discrWidth)
                          have h_trunc_eq :
                              truncateBits ety.discrWidth (BitVec.ofNat 128 disc) =
                                BitVec.ofNat 128 disc := by
                            apply BitVec.eq_of_toNat_eq
                            rw [toNat_truncateBits, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt hd_u128]
                            exact Nat.mod_eq_of_lt hd_mod
                          have h_cv_d :
                              checkVal (.scalar ⟨ety.discrWidth, ety.discrSigned,
                                truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
                                (.int ety.discrWidth ety.discrSigned) = true :=
                            checkVal_scalar_of_trunc ety.discrWidth ety.discrSigned _
                              (truncateBits_idem ety.discrWidth (BitVec.ofNat 128 disc))
                          have h_aw := assertAndWrite_local_eq rp c defId rbody blockIdx
                            stmtIdx body.locals slots amem retPlace mem ctrl cm dst.localId
                            (.int ety.discrWidth ety.discrSigned)
                            (.int ety.discrWidth ety.discrSigned)
                            (.scalar ⟨ety.discrWidth, ety.discrSigned,
                              truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
                            dstSlot h_dty h_dsl h_dst_res h_inv h_cv_d
                          dsimp only at h_aw
                          rw [beq_self_eq_true, ite_true_eq] at h_aw
                          dsimp only [valToMiriImmediate] at h_aw
                          have h_ms :
                              miriScalar ety.discrWidth (truncateBits ety.discrWidth (BitVec.ofNat 128 disc)) =
                                miriScalar ety.discrWidth (BitVec.ofNat 128 disc) := by
                            rw [h_trunc_eq]
                          rw [h_ms] at h_aw
                          have h_wp_eq :
                              (match
                                (if (ety.beq ety && v.blt ety.discriminants.length) = true then
                                  match MirSemantics.getElem? ety.discriminants v with
                                  | some disc =>
                                    Except.ok
                                      (Val.scalar ⟨ety.discrWidth, ety.discrSigned,
                                        truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, slots, amem)
                                  | none => Except.error FaultKind.unsupported
                                else Except.error FaultKind.unsupported) with
                               | Except.error k => Except.error k
                               | Except.ok (val, localsAfterRval, memAfterRval) =>
                                 writePlace localsAfterRval memAfterRval dst.localId
                                   (.int ety.discrWidth ety.discrSigned) val) =
                              writePlace slots amem dst.localId (.int ety.discrWidth ety.discrSigned)
                                (.scalar ⟨ety.discrWidth, ety.discrSigned,
                                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩) := by
                            rw [EnumTy.beq_refl, Nat.blt_eq.mpr h_v_lt]
                            rw [Bool.and_self, ite_true_eq, h_dv]
                          rw [← h_wp_eq] at h_aw
                          exact h_aw

end Anneal.MirCorrespondence
