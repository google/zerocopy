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
import Anneal.MirCorrespondence.ValidateLocal

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
def stepErrorFaultKind : Miri.Interpreter.StepError → Option FaultKind
  | .undefinedBehavior _ => some .undefined
  | .stack (.localExpectedLive _) => some .undefined
  | .termination (.abort _) => none
  | _ => some .unsupported

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
  | slice _ | array _ _ | rangeTo _ | rangeFrom _ | unsupported => rfl
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
  | slice _ | array _ _ | rangeTo _ | rangeFrom _ | unsupported => rfl
  | enum ety =>
    dsimp only [refLayoutDataForTy, refAsEnumTy?, refEnumLayoutData]
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
                  dsimp only [optValToMiriImm, valToMiriImmediate,
                    refAsEnumTy?, refEnumVariantOfVal?]
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
                  dsimp only [refLayoutDataForTy, refAsEnumTy?, refEnumLayoutData]
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

structure SimFrameCtx where
  below : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
    Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
  topRel? : Option Nat
  fnTag : DefId
  retCont : Miri.Interpreter.ReturnContinuation
  retPlace : Miri.Interpreter.RuntimeStackPlace Miri.Memory.Provenance
  locOverride : Option Miri.Interpreter.FrameLocation := none

noncomputable def SimFrameCtx.root (defId : DefId)
    (retPlace : MPlaceTy Miri.Memory.Provenance) : SimFrameCtx where
  below := Array.empty
  topRel? := none
  fnTag := defId
  retCont := .stop false
  retPlace := .memory retPlace
  locOverride := none

noncomputable def SimFrameCtx.call (types : List MirTy)
    (below : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (topRel? : Option Nat) (fnTag : DefId) (callerIdx : Nat)
    (dstLocalId : LocalId) (dstTy : MirTy) (retTarget? : Option BasicBlockId) :
    SimFrameCtx where
  below := below
  topRel? := topRel?
  fnTag := fnTag
  retCont := .goto retTarget? .Unreachable
  retPlace := .frameLocal callerIdx dstLocalId none
    (refLocalLayoutForTy types dstTy)
    (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)
  locOverride := none

noncomputable def cacheTouch : List Bool → Nat → List Bool
  | [], _ => []
  | _ :: rest, 0 => true :: rest
  | b :: rest, i + 1 => b :: cacheTouch rest i

noncomputable def operandCacheTouch (cache : List Bool) : Operand → List Bool
  | .copy p | .move p => cacheTouch cache p.localId
  | .constant _ => cache

noncomputable def rvalueCacheTouch (dstId : LocalId) : Rvalue → List Bool → List Bool
  | .use op, cache => operandCacheTouch (cacheTouch cache dstId) op
  | .binaryOp _ lhs rhs, cache =>
    operandCacheTouch (operandCacheTouch (cacheTouch cache dstId) lhs) rhs
  | .unaryOp _ op, cache => operandCacheTouch (cacheTouch cache dstId) op
  | .cast .intToInt op _, cache => operandCacheTouch (cacheTouch cache dstId) op
  | .discriminant src, cache => cacheTouch (cacheTouch cache dstId) src.localId
  | _, cache => cacheTouch cache dstId

def localKnownOk (types : List MirTy) (bodyLocals : List MirTy)
    (cache : List Bool) (id : LocalId) (known : Option LocalLayout) : Prop :=
  MirSemantics.getElem? cache id = some false →
    match known with
    | none => True
    | some kl =>
      match MirSemantics.getElem? bodyLocals id with
      | some ty => kl = refLocalLayoutForTy types ty
      | none => True

def placeKnownOk (types : List MirTy) (bodyLocals : List MirTy)
    (cache : List Bool) (pl : Place) (known : Option LocalLayout) : Prop :=
  pl.projection.isEmpty = true → localKnownOk types bodyLocals cache pl.localId known

def operandKnownOk (types : List MirTy) (bodyLocals : List MirTy)
    (cache : List Bool) (op : Operand) (known : Option LocalLayout) : Prop :=
  match op with
  | .copy pl | .move pl => placeKnownOk types bodyLocals cache pl known
  | .constant _ => True

private theorem ite_false_eq_early {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

private theorem ite_true_eq_early {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

/-- Generalized frame constructor supporting arbitrary call depth, return
continuation/destination, and per-local layout cache flags `cache`. -/
noncomputable def mkGenSimFrame (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool) :
    Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra := {
  body := toMiriBody rp.types rbody
  bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex ctx.fnTag
  functionInstance := { kind := .Item ctx.fnTag, args := Array.empty }
  extra := {
    borrowTracker := none
    catchUnwind := none
    userRelevance := 255
    dataRace := none
  }
  returnContinuation := ctx.retCont
  returnPlace := ctx.retPlace
  localsIdentity := Miri.Interpreter.LocalsIdentity.ofAllocationToken 0
  locals := Array.mk (liftLocalsCached rp.types bodyLocals slots cache)
  vaList := Array.empty
  trackCallerArg := none
  location := match ctx.locOverride with
    | some loc => loc
    | none => .mir ⟨blockIdx, stmtIdx⟩
}

/-- Generalized stack state constructor placing `mkGenSimFrame` atop `ctx.below`
with cached `ctx.topRel?`. -/
noncomputable def mkGenSimState (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :
    Miri.Interpreter.MachineHooks.State Unit RefUser :=
  mkRefMiriStackState
    (ctx.below.push
      (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache))
    ctx.topRel? mem ctrl cm

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

theorem mkGenSimFrame_root_eq_mkSimFrame (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (h_len : slots.length = bodyLocals.length) :
    mkGenSimFrame rp (SimFrameCtx.root defId retPlace) rbody blockIdx stmtIdx
      bodyLocals slots (List.replicate bodyLocals.length true) =
      mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace := by
  dsimp only [mkGenSimFrame, SimFrameCtx.root, mkSimFrame, mkRefMiriFrame]
  rw [liftLocalsCached_replicate_true rp.types h_len]

theorem mkGenSimState_root_eq_mkSimState (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory)
    (h_len : slots.length = bodyLocals.length) :
    mkGenSimState rp (SimFrameCtx.root defId retPlace) rbody blockIdx stmtIdx
      bodyLocals slots (List.replicate bodyLocals.length true) mem ctrl cm =
      mkSimState rp defId rbody blockIdx stmtIdx bodyLocals slots retPlace
        mem ctrl cm := by
  dsimp only [mkGenSimState, mkSimState, mkRefMiriState]
  rw [mkGenSimFrame_root_eq_mkSimFrame rp defId rbody blockIdx stmtIdx bodyLocals
    slots retPlace h_len]
  rfl

theorem cacheTouch_length (cache : List Bool) (id : Nat) :
    (cacheTouch cache id).length = cache.length := by
  induction cache generalizing id with
  | nil => rfl
  | cons _ rest ih =>
    cases id with
    | zero => rfl
    | succ j => dsimp only [cacheTouch, List.length_cons]; rw [ih]

theorem operandCacheTouch_length (cache : List Bool) (op : Operand) :
    (operandCacheTouch cache op).length = cache.length := by
  cases op with
  | copy p | move p => exact cacheTouch_length cache p.localId
  | constant _ => rfl

theorem rvalueCacheTouch_length (dstId : LocalId) (rv : Rvalue)
    (cache : List Bool) :
    (rvalueCacheTouch dstId rv cache).length = cache.length := by
  cases rv with
  | use op =>
    dsimp only [rvalueCacheTouch]
    rw [operandCacheTouch_length, cacheTouch_length]
  | binaryOp _ lhs rhs =>
    dsimp only [rvalueCacheTouch]
    rw [operandCacheTouch_length, operandCacheTouch_length, cacheTouch_length]
  | unaryOp _ op =>
    dsimp only [rvalueCacheTouch]
    rw [operandCacheTouch_length, cacheTouch_length]
  | cast k op _ =>
    cases k <;> dsimp only [rvalueCacheTouch]
    · rw [operandCacheTouch_length, cacheTouch_length]
    · exact cacheTouch_length _ _
    · exact cacheTouch_length _ _
    · exact cacheTouch_length _ _
    · exact cacheTouch_length _ _
  | discriminant src =>
    dsimp only [rvalueCacheTouch]
    rw [cacheTouch_length, cacheTouch_length]
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported | useRetag _
  | aggregateRangeTo _ _ | aggregateRangeFrom _ _ | aggregateArray _ _
  | repeat_ _ _ _ =>
    exact cacheTouch_length _ _

theorem getElem?_cacheTouch_self {cache : List Bool} {id : Nat} {b : Bool}
    (h : MirSemantics.getElem? cache id = some b) :
    MirSemantics.getElem? (cacheTouch cache id) id = some true := by
  induction cache generalizing id with
  | nil => cases h
  | cons hd rest ih =>
    cases id with
    | zero => rfl
    | succ j => exact ih h

theorem getElem?_cacheTouch_mono {cache : List Bool} {i id : Nat}
    (h : MirSemantics.getElem? cache i = some true) :
    MirSemantics.getElem? (cacheTouch cache id) i = some true := by
  induction cache generalizing i id with
  | nil => cases h
  | cons hd rest ih =>
    cases i with
    | zero =>
      cases id with
      | zero => rfl
      | succ _ => exact h
    | succ j =>
      cases id with
      | zero => exact h
      | succ k => exact ih h

theorem getElem?_operandCacheTouch_mono {cache : List Bool} {i : Nat}
    {op : Operand} (h : MirSemantics.getElem? cache i = some true) :
    MirSemantics.getElem? (operandCacheTouch cache op) i = some true := by
  cases op with
  | copy p | move p => exact getElem?_cacheTouch_mono h
  | constant _ => exact h

theorem cacheTouch_eq_self_of_true {cache : List Bool} {id : Nat}
    (h : MirSemantics.getElem? cache id = some true) :
    cacheTouch cache id = cache := by
  induction cache generalizing id with
  | nil => cases h
  | cons hd rest ih =>
    cases id with
    | zero =>
      dsimp only [MirSemantics.getElem?] at h
      injection h with hb
      subst hb
      rfl
    | succ j =>
      dsimp only [cacheTouch]
      rw [ih h]

theorem mirSetElem?_cacheTouch {cache : List Bool} {id : Nat} {b : Bool}
    (h : MirSemantics.getElem? cache id = some b) :
    MirSemantics.setElem? cache id true = some (cacheTouch cache id) := by
  induction cache generalizing id with
  | nil => cases h
  | cons hd rest ih =>
    cases id with
    | zero => rfl
    | succ j =>
      dsimp only [MirSemantics.setElem?, cacheTouch]
      rw [ih h]

theorem cacheTouch_replicate_true (n id : Nat) :
    cacheTouch (List.replicate n true) id = List.replicate n true := by
  induction n generalizing id with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    cases id with
    | zero => rfl
    | succ j =>
      dsimp only [cacheTouch]
      rw [ih j]

theorem operandCacheTouch_replicate_true (n : Nat) (op : Operand) :
    operandCacheTouch (List.replicate n true) op = List.replicate n true := by
  cases op with
  | copy p | move p => exact cacheTouch_replicate_true n p.localId
  | constant _ => rfl

theorem localKnownOk_none (types : List MirTy) (bodyLocals : List MirTy)
    (cache : List Bool) (id : LocalId) :
    localKnownOk types bodyLocals cache id none := by
  intro _; exact True.intro

theorem placeKnownOk_none (types : List MirTy) (bodyLocals : List MirTy)
    (cache : List Bool) (pl : Place) :
    placeKnownOk types bodyLocals cache pl none := by
  intro _ _; exact True.intro

theorem operandKnownOk_none (types : List MirTy) (bodyLocals : List MirTy)
    (cache : List Bool) (op : Operand) :
    operandKnownOk types bodyLocals cache op none := by
  cases op with
  | copy pl | move pl => exact placeKnownOk_none types bodyLocals cache pl
  | constant _ => exact True.intro

theorem getElem?_replicate_some {α : Type} {n i : Nat} {x y : α}
    (h : MirSemantics.getElem? (List.replicate n x) i = some y) : y = x := by
  induction n generalizing i with
  | zero => cases h
  | succ k ih =>
    rw [List.replicate_succ] at h
    cases i with
    | zero => injection h with heq; exact heq.symm
    | succ j => exact ih h

theorem operandKnownOk_of_replicate_true (types : List MirTy)
    (bodyLocals : List MirTy) (n : Nat) (op : Operand)
    (known : Option LocalLayout) :
    operandKnownOk types bodyLocals (List.replicate n true) op known := by
  cases op with
  | constant _ => exact True.intro
  | copy pl | move pl =>
    intro _ h_false
    have h_eq := getElem?_replicate_some h_false
    cases h_eq

theorem operandKnownOk_of_localOperandMatchesTy (types : List MirTy)
    (bodyLocals : List MirTy) (cache : List Bool) (op : Operand)
    (expectedTy : MirTy)
    (h_match : localOperandMatchesTy bodyLocals op expectedTy = true) :
    operandKnownOk types bodyLocals cache op
      (some (refLocalLayoutForTy types expectedTy)) := by
  cases op with
  | constant _ => exact True.intro
  | copy pl | move pl =>
    intro h_pe _
    dsimp only [localOperandMatchesTy] at h_match
    rw [h_pe, ite_true_eq_early] at h_match
    cases h_ty : MirSemantics.getElem? bodyLocals pl.localId with
    | none => exact True.intro
    | some srcTy =>
      rw [h_ty] at h_match
      have h_eq := MirTy.eq_of_beq h_match
      subst h_eq
      rfl

theorem toMiriBinOp_leftHomogeneous (op : BinOp) :
    (toMiriBinOp op).leftHomogeneous = binOpLeftHomogeneous op := by
  cases op <;> rfl

theorem toMiriBinOp_rightHomogeneous (op : BinOp) :
    (toMiriBinOp op).rightHomogeneous = binOpRightHomogeneous op := by
  cases op <;> rfl

theorem toMiriUnOp_homogeneous (op : UnOp) :
    (toMiriUnOp op).homogeneous = unOpHomogeneous op := by
  cases op <;> rfl

theorem stack_currentFrame?_push
    (below : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (fr : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra) :
    ({ frames := below.push fr } :
      Miri.Interpreter.Stack Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra).currentFrame? =
      some fr := by
  simp [Miri.Interpreter.Stack.currentFrame?]

theorem stack_frameIndex_push
    (below : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (fr : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra) :
    ({ frames := below.push fr } :
      Miri.Interpreter.Stack Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra).frameIndex =
      .ok below.size := by
  simp [Miri.Interpreter.Stack.frameIndex, pure, Pure.pure, Except.pure]

theorem array_pop_push_eq {α : Type} (arr : Array α) (x : α) :
    (arr.push x).pop = arr := by
  simp

theorem array_isEmpty_push_false {α : Type} (arr : Array α) (x : α) :
    (arr.push x).isEmpty = false := by
  simp

theorem setCurrentFrame_mkGenSimState (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots slots' : List LocalSlot)
    (cache cache' : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :
    Miri.Interpreter.MachineHooks.setCurrentFrame
        (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache')
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) =
      .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache'
        mem ctrl cm) := by
  dsimp only [Miri.Interpreter.MachineHooks.setCurrentFrame, get, getThe,
    MonadStateOf.get, set, MonadStateOf.set, EStateM.get, EStateM.set,
    mkGenSimState, mkRefMiriStackState, bind, Bind.bind, pure, Pure.pure,
    EStateM.bind, EStateM.pure]
  rw [array_isEmpty_push_false]
  simp only [Bool.false_eq_true, ite_false]
  rw [array_pop_push_eq]
  rfl

theorem mirSetElem?_self {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : MirSemantics.getElem? xs i = some x) :
    MirSemantics.setElem? xs i x = some xs := by
  induction xs generalizing i with
  | nil => cases h
  | cons hd tl ih =>
    cases i with
    | zero =>
      dsimp only [MirSemantics.getElem?] at h
      injection h with hx
      subst hx
      rfl
    | succ j =>
      dsimp only [MirSemantics.setElem?]
      rw [ih h]

theorem getElem?_liftLocalsCached_none_left (types : List MirTy)
    {bodyLocals : List MirTy} {slots : List LocalSlot} {cache : List Bool}
    {i : Nat} (h : MirSemantics.getElem? bodyLocals i = none) :
    MirSemantics.getElem? (liftLocalsCached types bodyLocals slots cache) i =
      none := by
  induction bodyLocals generalizing slots cache i with
  | nil => rfl
  | cons _ _ ih =>
    cases slots with
    | nil => rfl
    | cons _ _ =>
      cases cache with
      | nil => rfl
      | cons _ _ =>
        cases i with
        | zero => cases h
        | succ j => exact ih h

theorem getElem?_liftLocalsCached_none_right (types : List MirTy)
    {bodyLocals : List MirTy} {slots : List LocalSlot} {cache : List Bool}
    {i : Nat} (h : MirSemantics.getElem? slots i = none) :
    MirSemantics.getElem? (liftLocalsCached types bodyLocals slots cache) i =
      none := by
  induction bodyLocals generalizing slots cache i with
  | nil => rfl
  | cons _ _ ih =>
    cases slots with
    | nil => rfl
    | cons _ _ =>
      cases cache with
      | nil => rfl
      | cons _ _ =>
        cases i with
        | zero => cases h
        | succ j => exact ih h

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

theorem mkGenSimFrame_getLocal_some (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (id : LocalId) (ty : MirTy) (slot : LocalSlot) (b : Bool)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot)
    (h_c : MirSemantics.getElem? cache id = some b) :
    (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).getLocal id =
      .ok (refLocalStateOfSlotWithCache rp.types ty slot b) := by
  have h_lift := getElem?_liftLocalsCached_some rp.types h_ty h_sl h_c
  have h_sz : id < (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).size :=
    mirGetElem?_lt_of_some h_lift
  dsimp only [Miri.Interpreter.Frame.getLocal, mkGenSimFrame]
  rw [dite_eq_left h_sz]
  have h_idx : GetElem.getElem (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)) id h_sz =
      refLocalStateOfSlotWithCache rp.types ty slot b := by
    have h_opt : (Array.mk (liftLocalsCached rp.types bodyLocals slots cache))[id]? =
        some (refLocalStateOfSlotWithCache rp.types ty slot b) := by
      rw [array_getElem?_eq_mirGetElem?]; exact h_lift
    rw [Array.getElem?_eq_getElem h_sz] at h_opt
    injection h_opt
  rw [h_idx]
  rfl

theorem mkGenSimFrame_getLocal_none_left (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (id : LocalId) (h_ty : MirSemantics.getElem? bodyLocals id = none) :
    (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).getLocal id =
      .error (.invalidLocal id (liftLocalsCached rp.types bodyLocals slots cache).length) := by
  have h_none := getElem?_liftLocalsCached_none_left rp.types
    (slots := slots) (cache := cache) h_ty
  have h_not : ¬ (id < (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).size) :=
    Nat.not_lt.mpr (mirGetElem?_ge_of_none h_none)
  dsimp only [Miri.Interpreter.Frame.getLocal, mkGenSimFrame]
  rw [dite_eq_right h_not]
  rfl

theorem mkGenSimFrame_getLocal_none_right (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (id : LocalId) (h_sl : MirSemantics.getElem? slots id = none) :
    (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).getLocal id =
      .error (.invalidLocal id (liftLocalsCached rp.types bodyLocals slots cache).length) := by
  have h_none := getElem?_liftLocalsCached_none_right rp.types
    (bodyLocals := bodyLocals) (cache := cache) h_sl
  have h_not : ¬ (id < (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).size) :=
    Nat.not_lt.mpr (mirGetElem?_ge_of_none h_none)
  dsimp only [Miri.Interpreter.Frame.getLocal, mkGenSimFrame]
  rw [dite_eq_right h_not]
  rfl

theorem mkGenSimFrame_getLocalOperand_dead (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (id : LocalId) (ty : MirTy) (b : Bool)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead)
    (h_c : MirSemantics.getElem? cache id = some b) :
    (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).getLocalOperand id =
      .error (.localExpectedLive id) := by
  dsimp only [Miri.Interpreter.Frame.getLocalOperand, bind, Bind.bind, Except.bind]
  rw [mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx bodyLocals slots
    cache id ty .dead b h_ty h_sl h_c]
  rfl

theorem mkGenSimFrame_getLocalOperand_live (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (id : LocalId) (ty : MirTy) (optVal : Option Val) (b : Bool)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal))
    (h_c : MirSemantics.getElem? cache id = some b) :
    (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).getLocalOperand id =
      .ok (.immediate (optValToMiriImm ty optVal)) := by
  dsimp only [Miri.Interpreter.Frame.getLocalOperand, bind, Bind.bind, Except.bind]
  rw [mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx bodyLocals slots
    cache id ty (.immediate optVal) b h_ty h_sl h_c]
  dsimp only [refLocalStateOfSlotWithCache]
  cases b with
  | false => rw [ite_false_eq, slotToMiriLocalValue_live]; rfl
  | true => rw [ite_true_eq, slotToMiriLocalValue_live]; rfl

theorem mkGenSimFrame_replaceLocalValue_some (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots slots' : List LocalSlot) (cache : List Bool)
    (id : LocalId) (ty : MirTy) (slot slot' : LocalSlot) (b : Bool)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot)
    (h_c : MirSemantics.getElem? cache id = some b)
    (h_set : MirSemantics.setElem? slots id slot' = some slots') :
    (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).replaceLocalValue
        id (slotToMiriLocalValue ty slot') =
      .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache) := by
  have h_lift_get :
      MirSemantics.getElem? (liftLocalsCached rp.types bodyLocals slots cache) id =
        some (refLocalStateOfSlotWithCache rp.types ty slot b) :=
    getElem?_liftLocalsCached_some rp.types h_ty h_sl h_c
  have h_lt : id < (liftLocalsCached rp.types bodyLocals slots cache).length :=
    mirGetElem?_lt_of_some h_lift_get
  have h_lift_set :
      MirSemantics.setElem? (liftLocalsCached rp.types bodyLocals slots cache) id
        (refLocalStateOfSlotWithCache rp.types ty slot' b) =
        some (liftLocalsCached rp.types bodyLocals slots' cache) :=
    setElem?_liftLocalsCached_some rp.types h_ty h_set (mirSetElem?_self h_c)
  have h_arr_set := array_set_eq_mirSetElem? h_lt h_lift_set
  dsimp only [Miri.Interpreter.Frame.replaceLocalValue, mkGenSimFrame]
  have h_sz : id < (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).size := h_lt
  rw [dite_eq_left h_sz]
  have h_idx : GetElem.getElem (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)) id h_sz =
      refLocalStateOfSlotWithCache rp.types ty slot b := by
    have h_opt : (Array.mk (liftLocalsCached rp.types bodyLocals slots cache))[id]? =
        some (refLocalStateOfSlotWithCache rp.types ty slot b) := by
      rw [array_getElem?_eq_mirGetElem?]; exact h_lift_get
    rw [Array.getElem?_eq_getElem h_sz] at h_opt
    injection h_opt
  rw [h_idx]
  have h_val_eq :
      { refLocalStateOfSlotWithCache rp.types ty slot b with
          value := slotToMiriLocalValue ty slot' } =
        refLocalStateOfSlotWithCache rp.types ty slot' b := by
    cases b <;> rfl
  rw [h_val_eq]
  change Except.ok ({
    body := toMiriBody rp.types rbody,
    bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex ctx.fnTag,
    functionInstance := { kind := .Item ctx.fnTag, args := Array.empty },
    extra := { borrowTracker := none, catchUnwind := none, userRelevance := 255, dataRace := none },
    returnContinuation := ctx.retCont,
    returnPlace := ctx.retPlace,
    localsIdentity := LocalsIdentity.ofAllocationToken 0,
    locals := (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).set id
      (refLocalStateOfSlotWithCache rp.types ty slot' b) h_sz,
    vaList := Array.empty,
    trackCallerArg := none,
    location := match ctx.locOverride with
      | some loc => loc
      | none => FrameLocation.mir { block := blockIdx, statementIndex := stmtIdx }
  } : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra) = _
  rw [h_arr_set]

theorem mkGenSimFrame_setLocalOperand_some (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots slots' : List LocalSlot) (cache : List Bool)
    (id : LocalId) (ty : MirTy) (optVal : Option Val) (optVal' : Option Val)
    (b : Bool)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal))
    (h_c : MirSemantics.getElem? cache id = some b)
    (h_set : MirSemantics.setElem? slots id (.immediate optVal') = some slots') :
    (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).setLocalOperand
        id (.immediate (optValToMiriImm ty optVal')) =
      .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache) := by
  dsimp only [Miri.Interpreter.Frame.setLocalOperand, bind, Bind.bind, Except.bind]
  rw [mkGenSimFrame_getLocalOperand_live rp ctx rbody blockIdx stmtIdx bodyLocals slots
    cache id ty optVal b h_ty h_sl h_c]
  have h_rep := mkGenSimFrame_replaceLocalValue_some rp ctx rbody blockIdx stmtIdx
    bodyLocals slots slots' cache id ty (.immediate optVal) (.immediate optVal')
    b h_ty h_sl h_c h_set
  rw [slotToMiriLocalValue_live] at h_rep
  exact h_rep

theorem mkGenSimFrame_getOrCacheLocalLayout_some (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (id : LocalId) (ty : MirTy) (slot : LocalSlot) (b : Bool)
    (computed : LocalLayout)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot)
    (h_c : MirSemantics.getElem? cache id = some b)
    (h_comp : b = false → computed = refLocalLayoutForTy rp.types ty) :
    (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).getOrCacheLocalLayout
        id computed =
      .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots (cacheTouch cache id),
        refLocalLayoutForTy rp.types ty) := by
  dsimp only [Miri.Interpreter.Frame.getOrCacheLocalLayout, bind, Bind.bind,
    Except.bind, pure, Pure.pure, Except.pure]
  rw [mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx bodyLocals slots
    cache id ty slot b h_ty h_sl h_c]
  cases b with
  | true =>
    rw [cacheTouch_eq_self_of_true h_c]
    rfl
  | false =>
    have h_ceq := h_comp rfl
    subst h_ceq
    have h_lift_get :
        MirSemantics.getElem? (liftLocalsCached rp.types bodyLocals slots cache) id =
          some (refLocalStateOfSlotWithCache rp.types ty slot false) :=
      getElem?_liftLocalsCached_some rp.types h_ty h_sl h_c
    have h_lt : id < (liftLocalsCached rp.types bodyLocals slots cache).length :=
      mirGetElem?_lt_of_some h_lift_get
    have h_lift_set :
        MirSemantics.setElem? (liftLocalsCached rp.types bodyLocals slots cache) id
          (refLocalStateOfSlotWithCache rp.types ty slot true) =
          some (liftLocalsCached rp.types bodyLocals slots (cacheTouch cache id)) :=
      setElem?_liftLocalsCached_some rp.types h_ty (mirSetElem?_self h_sl)
        (mirSetElem?_cacheTouch h_c)
    have h_arr_set := array_set_eq_mirSetElem? h_lt h_lift_set
    dsimp only [refLocalStateOfSlotWithCache]
    rw [ite_false_eq]
    have h_sz_fr : id < (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).locals.size := h_lt
    rw [dite_eq_left h_sz_fr]
    dsimp only [mkGenSimFrame]
    let lsTrue : Miri.Interpreter.LocalState Miri.Memory.Provenance LocalLayout :=
      { value := slotToMiriLocalValue ty slot,
        layout := some (refLocalLayoutForTy rp.types ty) }
    have h_rls : lsTrue = refLocalStateOfSlotWithCache rp.types ty slot true := rfl
    let updatedFr : Miri.Interpreter.Frame Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra := {
      body := toMiriBody rp.types rbody,
      bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex ctx.fnTag,
      functionInstance := { kind := .Item ctx.fnTag, args := Array.empty },
      extra := { borrowTracker := none, catchUnwind := none, userRelevance := 255, dataRace := none },
      returnContinuation := ctx.retCont,
      returnPlace := ctx.retPlace,
      localsIdentity := Miri.Interpreter.LocalsIdentity.ofAllocationToken 0,
      locals := (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).set id lsTrue h_lt,
      vaList := Array.empty,
      trackCallerArg := none,
      location := match ctx.locOverride with
        | some loc => loc
        | none => FrameLocation.mir { block := blockIdx, statementIndex := stmtIdx }
    }
    change Except.ok (updatedFr, refLocalLayoutForTy rp.types ty) = _
    dsimp only [updatedFr]
    rw [h_rls, h_arr_set]

theorem mkGenSimFrame_getOrCacheLocalLayout_dead (rp : RefProg)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (id : LocalId) (ty : MirTy) (b : Bool) (computed : LocalLayout)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead)
    (h_c : MirSemantics.getElem? cache id = some b) :
    ∃ fr',
      (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).getOrCacheLocalLayout
          id computed = .ok (fr', if b then refLocalLayoutForTy rp.types ty else computed) ∧
      fr'.getLocalOperand id = .error (.localExpectedLive id) := by
  dsimp only [Miri.Interpreter.Frame.getOrCacheLocalLayout, bind, Bind.bind,
    Except.bind, pure, Pure.pure, Except.pure]
  rw [mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx bodyLocals slots
    cache id ty .dead b h_ty h_sl h_c]
  cases b with
  | true =>
    refine ⟨mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache, rfl, ?_⟩
    exact mkGenSimFrame_getLocalOperand_dead rp ctx rbody blockIdx stmtIdx bodyLocals
      slots cache id ty true h_ty h_sl h_c
  | false =>
    have h_lift_get :
        MirSemantics.getElem? (liftLocalsCached rp.types bodyLocals slots cache) id =
          some (refLocalStateOfSlotWithCache rp.types ty .dead false) :=
      getElem?_liftLocalsCached_some rp.types h_ty h_sl h_c
    have h_lt : id < (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).size :=
      mirGetElem?_lt_of_some h_lift_get
    let ls' : Miri.Interpreter.LocalState Miri.Memory.Provenance LocalLayout :=
      { value := .dead, layout := some computed }
    let fr0 := mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
    let fr' := { fr0 with
      locals := (Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).set id ls' h_lt }
    dsimp only [refLocalStateOfSlotWithCache]
    rw [ite_false_eq]
    have h_sz_fr : id < (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).locals.size := h_lt
    rw [dite_eq_left h_sz_fr]
    dsimp only [mkGenSimFrame]
    refine ⟨fr', rfl, ?_⟩
    dsimp only [Miri.Interpreter.Frame.getLocalOperand, Miri.Interpreter.Frame.getLocal,
      bind, Bind.bind, Except.bind, fr']
    have h_sz' : id < ((Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).set id ls' h_lt).size := by
      rw [Array.size_set]; exact h_lt
    rw [dite_eq_left h_sz']
    have h_get_eq :
        GetElem.getElem ((Array.mk (liftLocalsCached rp.types bodyLocals slots cache)).set id ls' h_lt) id h_sz' = ls' := by
      simp
    rw [h_get_eq]
    rfl

private theorem refLayoutOfTyId_of_decodeLocalTys {ts : List MirTy}
    {rbody : RefBody} {bodyLocals : List MirTy} {id : LocalId} {ty : MirTy}
    (h_locs : decodeLocalTys ts rbody.locals = some bodyLocals)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty) :
    (toMiriBody ts rbody).locals[id]? = some (tyIdFor ts ty) ∧
    refLayoutOfTyId ts (tyIdFor ts ty) = .ok (refLocalLayoutForTy ts ty) := by
  let ⟨tid, h_rloc, h_ts⟩ := decodeLocalTys_mirGetElem? h_locs h_ty
  let ⟨h_can, _, h_res⟩ := canonicalTyId_of_some h_ts
  have h_m : MirSemantics.getElem? (rbody.locals.map (canonicalTyId ts)) id =
      some (canonicalTyId ts tid) := by
    rw [mirGetElem?_map, h_rloc]
    rfl
  dsimp only [toMiriBody]
  rw [array_getElem?_eq_mirGetElem?, h_m, h_can]
  rw [h_can] at h_res
  exact ⟨rfl, refLayoutOfTyId_tyIdFor_of_resolve h_res⟩

/-! ## Section 2: `OperandMachine` (`localToOp`, `evalPlaceToOp`) -/

theorem currentFrame_mkGenSimState (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :
    Miri.Interpreter.MachineHooks.currentFrame
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) =
      .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache)
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) := by
  dsimp only [Miri.Interpreter.MachineHooks.currentFrame, mkGenSimState,
    mkRefMiriStackState, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
    EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]
  rw [stack_currentFrame?_push]
  rfl

theorem operandHooks_compiler_layout_ok (rp : RefProg) (ctx : SimFrameCtx)
    (c : Choice) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty) :
    (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).compiler.layout c id
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) =
      .ok (refLocalLayoutForTy rp.types ty)
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) := by
  let ⟨h_loc, h_lay⟩ := refLayoutOfTyId_of_decodeLocalTys h_locs h_ty
  dsimp only [Miri.Interpreter.ExecutionMachine.operandHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refOperandLeaves]
  change (match (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm).stack.currentFrame? with
    | none => _
    | some frame =>
      match frame.body.locals[id]? with
      | none => _
      | some tyId =>
        match refLayoutOfTyId rp.types tyId with
        | Except.ok l => EStateM.Result.ok l _
        | Except.error e => EStateM.Result.error e _) = _
  dsimp only [mkGenSimState, mkRefMiriStackState]
  rw [stack_currentFrame?_push]
  dsimp only [mkGenSimFrame]
  rw [h_loc]
  dsimp only
  rw [h_lay]

theorem operandHooks_validationInProgress_false (rp : RefProg)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).compiler.validationInProgress st =
      .ok false st := rfl

theorem afterLocalRead_mkGenSimState (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) :
    Miri.Interpreter.MachineHooks.afterLocalRead id
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) =
      .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
        mem ctrl cm) := by
  dsimp only [Miri.Interpreter.MachineHooks.afterLocalRead, bind, Bind.bind,
    pure, Pure.pure, EStateM.pure]
  rw [eStateM_bind_ok (currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm)]
  rfl

theorem afterLocalWrite_mkGenSimState (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (sl : Bool) :
    Miri.Interpreter.MachineHooks.afterLocalWrite id sl
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) =
      .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
        mem ctrl cm) := by
  dsimp only [Miri.Interpreter.MachineHooks.afterLocalWrite, bind, Bind.bind,
    pure, Pure.pure, EStateM.pure]
  rw [eStateM_bind_ok (currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm)]
  rfl

theorem operandMachine_localToOp_ok (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (known : Option LocalLayout)
    (ty : MirTy) (optVal : Option Val)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal))
    (h_known : localKnownOk rp.types bodyLocals cache id known) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    Miri.Interpreter.OperandMachine.localToOp
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
        c id known st =
      .ok ⟨.immediate (optValToMiriImm ty optVal),
        refLocalLayoutForTy rp.types ty⟩
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
          (cacheTouch cache id) mem ctrl cm) := by
  intro st
  let ⟨b, h_c⟩ := getElem?_some_of_length_eq h_c_len.symm h_ty
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
  have h_gl := mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache id ty (.immediate optVal) b h_ty h_sl h_c
  have h_c' := getElem?_cacheTouch_self h_c
  have h_cf' := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots (cacheTouch cache id) mem ctrl cm
  have h_go' := mkGenSimFrame_getLocalOperand_live rp ctx rbody blockIdx stmtIdx
    bodyLocals slots (cacheTouch cache id) id ty optVal true h_ty h_sl h_c'
  have h_un : (refLocalLayoutForTy rp.types ty).layout.backendRepr.isUnsized = false :=
    refLayoutDataForTy_isUnsized ty
  cases b with
  | true =>
    rw [cacheTouch_eq_self_of_true h_c] at h_cf' h_go'
    rw [cacheTouch_eq_self_of_true h_c]
    dsimp only [Miri.Interpreter.OperandMachine.localToOp, bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_cf, h_gl]
    dsimp only [refLocalStateOfSlotWithCache]
    rw [ite_true_eq]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure]
    dsimp only
    rw [eStateM_bind_pure, eStateM_bind_ok h_cf, h_go']
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure]
    simp only [h_un, Bool.false_eq_true, ite_false]
    rw [eStateM_bind_ok (operandHooks_validationInProgress_false rp st)]
    rw [ite_false_eq, eStateM_bind_ok (afterLocalRead_mkGenSimState rp ctx rbody blockIdx
      stmtIdx bodyLocals slots cache mem ctrl cm id)]
    rfl
  | false =>
    have h_gc := mkGenSimFrame_getOrCacheLocalLayout_some rp ctx rbody blockIdx
      stmtIdx bodyLocals slots cache id ty (.immediate optVal) false
      (refLocalLayoutForTy rp.types ty) h_ty h_sl h_c (fun _ => rfl)
    have h_set := setCurrentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
      bodyLocals slots slots cache (cacheTouch cache id) mem ctrl cm
    let st' := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
      (cacheTouch cache id) mem ctrl cm
    dsimp only [Miri.Interpreter.OperandMachine.localToOp, bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_cf, h_gl]
    dsimp only [refLocalStateOfSlotWithCache]
    rw [ite_false_eq]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure]
    dsimp only
    cases known with
    | none =>
      dsimp only
      have h_rl := operandHooks_compiler_layout_ok rp ctx c rbody blockIdx stmtIdx
        bodyLocals slots cache mem ctrl cm id ty h_locs h_ty
      rw [eStateM_bind_ok h_rl]
      rw [eStateM_bind_ok h_cf, h_gc]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      rw [eStateM_bind_ok h_set]
      change (EStateM.bind (EStateM.pure _) _ _) = _
      rw [eStateM_bind_pure]
      rw [eStateM_bind_ok h_cf', h_go']
      change (EStateM.bind (EStateM.pure _) _ _) = _
      rw [eStateM_bind_pure]
      simp only [h_un, Bool.false_eq_true, ite_false]
      rw [eStateM_bind_ok (operandHooks_validationInProgress_false rp st')]
      rw [ite_false_eq, eStateM_bind_ok (afterLocalRead_mkGenSimState rp ctx rbody blockIdx
        stmtIdx bodyLocals slots (cacheTouch cache id) mem ctrl cm id)]
      rfl
    | some kl =>
      dsimp only
      have h_kl := h_known h_c
      dsimp only at h_kl
      rw [h_ty] at h_kl
      subst h_kl
      have h_da : (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).compiler.debugAssertions = false := rfl
      rw [h_da]
      simp only [Bool.false_eq_true, ite_false]
      rw [eStateM_bind_pure]
      rw [eStateM_bind_ok h_cf, h_gc]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      rw [eStateM_bind_ok h_set]
      change (EStateM.bind (EStateM.pure _) _ _) = _
      rw [eStateM_bind_pure]
      rw [eStateM_bind_ok h_cf', h_go']
      change (EStateM.bind (EStateM.pure _) _ _) = _
      rw [eStateM_bind_pure]
      simp only [h_un, Bool.false_eq_true, ite_false]
      rw [eStateM_bind_ok (operandHooks_validationInProgress_false rp st')]
      rw [ite_false_eq, eStateM_bind_ok (afterLocalRead_mkGenSimState rp ctx rbody blockIdx
        stmtIdx bodyLocals slots (cacheTouch cache id) mem ctrl cm id)]
      rfl

theorem operandMachine_localToOp_dead (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (known : Option LocalLayout)
    (ty : MirTy)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    ∃ st', Miri.Interpreter.OperandMachine.localToOp
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
        c id known st =
      .error (.stack (.localExpectedLive id)) st' := by
  intro st
  let ⟨b, h_c⟩ := getElem?_some_of_length_eq h_c_len.symm h_ty
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
  have h_gl := mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache id ty .dead b h_ty h_sl h_c
  cases b with
  | true =>
    have h_go := mkGenSimFrame_getLocalOperand_dead rp ctx rbody blockIdx stmtIdx
      bodyLocals slots cache id ty true h_ty h_sl h_c
    refine ⟨st, ?_⟩
    dsimp only [Miri.Interpreter.OperandMachine.localToOp, bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_cf, h_gl]
    dsimp only [refLocalStateOfSlotWithCache]
    rw [ite_true_eq]
    change (EStateM.bind (EStateM.pure _) _ st) = _
    rw [eStateM_bind_pure]
    dsimp only
    rw [eStateM_bind_pure, eStateM_bind_ok h_cf, h_go]
    rfl
  | false =>
    dsimp only [Miri.Interpreter.OperandMachine.localToOp, bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok h_cf, h_gl]
    dsimp only [refLocalStateOfSlotWithCache]
    rw [ite_false_eq]
    cases known with
    | none =>
      have h_rl := operandHooks_compiler_layout_ok rp ctx c rbody blockIdx stmtIdx
        bodyLocals slots cache mem ctrl cm id ty h_locs h_ty
      let ⟨fr', h_gc, h_go'⟩ := mkGenSimFrame_getOrCacheLocalLayout_dead rp ctx rbody
        blockIdx stmtIdx bodyLocals slots cache id ty false
        (refLocalLayoutForTy rp.types ty) h_ty h_sl h_c
      let st' := mkRefMiriStackState (ctx.below.push fr') ctx.topRel? mem ctrl cm
      have h_set' : Miri.Interpreter.MachineHooks.setCurrentFrame fr' st = .ok () st' := by
        dsimp only [Miri.Interpreter.MachineHooks.setCurrentFrame, get, getThe,
          MonadStateOf.get, set, MonadStateOf.set, EStateM.get, EStateM.set,
          st, st', mkGenSimState, mkRefMiriStackState, bind, Bind.bind, pure, Pure.pure,
          EStateM.bind, EStateM.pure]
        rw [array_isEmpty_push_false]
        simp only [Bool.false_eq_true, ite_false]
        rw [array_pop_push_eq]
        rfl
      have h_cf' : Miri.Interpreter.MachineHooks.currentFrame st' = .ok fr' st' := by
        dsimp only [Miri.Interpreter.MachineHooks.currentFrame, st', mkRefMiriStackState,
          bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
          get, getThe, MonadStateOf.get, EStateM.get]
        rw [stack_currentFrame?_push]
        rfl
      refine ⟨st', ?_⟩
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      rw [eStateM_bind_ok h_rl]
      rw [eStateM_bind_ok h_cf, h_gc]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      rw [eStateM_bind_ok h_set']
      change (EStateM.bind (EStateM.pure _) _ st') = _
      rw [eStateM_bind_pure]
      rw [eStateM_bind_ok h_cf', h_go']
      rfl
    | some kl =>
      have h_da : (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).compiler.debugAssertions = false := rfl
      let ⟨fr', h_gc, h_go'⟩ := mkGenSimFrame_getOrCacheLocalLayout_dead rp ctx rbody
        blockIdx stmtIdx bodyLocals slots cache id ty false kl h_ty h_sl h_c
      let st' := mkRefMiriStackState (ctx.below.push fr') ctx.topRel? mem ctrl cm
      have h_set' : Miri.Interpreter.MachineHooks.setCurrentFrame fr' st = .ok () st' := by
        dsimp only [Miri.Interpreter.MachineHooks.setCurrentFrame, get, getThe,
          MonadStateOf.get, set, MonadStateOf.set, EStateM.get, EStateM.set,
          st, st', mkGenSimState, mkRefMiriStackState, bind, Bind.bind, pure, Pure.pure,
          EStateM.bind, EStateM.pure]
        rw [array_isEmpty_push_false]
        simp only [Bool.false_eq_true, ite_false]
        rw [array_pop_push_eq]
        rfl
      have h_cf' : Miri.Interpreter.MachineHooks.currentFrame st' = .ok fr' st' := by
        dsimp only [Miri.Interpreter.MachineHooks.currentFrame, st', mkRefMiriStackState,
          bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
          get, getThe, MonadStateOf.get, EStateM.get]
        rw [stack_currentFrame?_push]
        rfl
      refine ⟨st', ?_⟩
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      rw [h_da]
      simp only [Bool.false_eq_true, ite_false]
      rw [eStateM_bind_pure]
      rw [eStateM_bind_ok h_cf, h_gc]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      rw [eStateM_bind_ok h_set']
      change (EStateM.bind (EStateM.pure _) _ st') = _
      rw [eStateM_bind_pure]
      rw [eStateM_bind_ok h_cf', h_go']
      rfl

theorem operandMachine_localToOp_none (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (known : Option LocalLayout)
    (h_oob : MirSemantics.getElem? bodyLocals id = none ∨
      MirSemantics.getElem? slots id = none) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    Miri.Interpreter.OperandMachine.localToOp
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
        c id known st =
      .error (.stack (.invalidLocal id (liftLocalsCached rp.types bodyLocals slots cache).length)) st := by
  intro st
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
  have h_gl :
      (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).getLocal id =
        .error (.invalidLocal id (liftLocalsCached rp.types bodyLocals slots cache).length) := by
    cases h_oob with
    | inl h =>
      exact mkGenSimFrame_getLocal_none_left rp ctx rbody blockIdx
        stmtIdx bodyLocals slots cache id h
    | inr h =>
      exact mkGenSimFrame_getLocal_none_right rp ctx rbody blockIdx
        stmtIdx bodyLocals slots cache id h
  dsimp only [Miri.Interpreter.OperandMachine.localToOp, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_cf, h_gl]
  rfl

theorem operandMachine_evalPlaceToOp_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (rpl : RefPlace) (pl : Place)
    (known : Option LocalLayout)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_pl : decodePlace rp.types rpl = some pl)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_known : placeKnownOk rp.types bodyLocals cache pl known) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let res := Miri.Interpreter.OperandMachine.evalPlaceToOp
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
      c (toMiriPlace rpl) known st
    match MirSemantics.getElem? bodyLocals pl.localId,
        MirSemantics.getElem? slots pl.localId with
    | some _, some .dead =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .undefined
    | some ty, some (.immediate optVal) =>
      if !pl.projection.isEmpty then
        ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .unsupported
      else
        res = .ok ⟨.immediate (optValToMiriImm ty optVal),
            refLocalLayoutForTy rp.types ty⟩
          (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
            (cacheTouch cache pl.localId) mem ctrl cm)
    | _, _ =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .unsupported := by
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
    rw [eStateM_bind_err (operandMachine_localToOp_none rp c ctx rbody
      blockIdx stmtIdx bodyLocals slots cache mem ctrl cm pl.localId _
      (Or.inl h_ty))]
    exact ⟨_, _, rfl, rfl⟩
  | some ty =>
    cases h_sl : MirSemantics.getElem? slots pl.localId with
    | none =>
      rw [eStateM_bind_err (operandMachine_localToOp_none rp c ctx rbody
        blockIdx stmtIdx bodyLocals slots cache mem ctrl cm pl.localId _
        (Or.inr h_sl))]
      exact ⟨_, _, rfl, rfl⟩
    | some slot =>
      cases slot with
      | dead =>
        let ⟨st', h_dead⟩ := operandMachine_localToOp_dead rp c ctx rbody
          blockIdx stmtIdx bodyLocals slots cache mem ctrl cm pl.localId
          (if (toMiriPlace rpl).projection.isEmpty then known else none)
          ty h_locs h_c_len h_ty h_sl
        rw [eStateM_bind_err h_dead]
        exact ⟨_, _, rfl, rfl⟩
      | indirect _ => exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
      | partialTuple _ =>
        exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)
      | immediate optVal =>
        have h_lk : localKnownOk rp.types bodyLocals cache pl.localId
            (if (toMiriPlace rpl).projection.isEmpty then known else none) := by
          cases h_p : (toMiriPlace rpl).projection.isEmpty with
          | false => exact localKnownOk_none _ _ _ _
          | true =>
            have h_rpe : rpl.projection.isEmpty = true := by
              dsimp only [toMiriPlace] at h_p
              cases h_r : rpl.projection.isEmpty with
              | true => rfl
              | false => rw [h_r] at h_p; cases h_p
            exact h_known (h_emp.symm.trans h_rpe)
        rw [eStateM_bind_ok (operandMachine_localToOp_ok rp c ctx rbody
          blockIdx stmtIdx bodyLocals slots cache mem ctrl cm pl.localId _
          ty optVal h_locs h_c_len h_ty h_sl h_lk)]
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

private theorem path_push_const_beq_fn_false
    {path : Miri.Interpreter.OperandPath}
    (h_ne : path ≠ Miri.Interpreter.OperandPath.instruction "function") :
    (path.push (.field "constant") ==
      (Miri.Interpreter.OperandPath.instruction "function").push
        (.field "constant")) = false := by
  cases h_b : (path.push (.field "constant") ==
      (Miri.Interpreter.OperandPath.instruction "function").push
        (.field "constant")) with
  | false => rfl
  | true =>
    exact False.elim (h_ne (by
      have h_arr : path.push (.field "constant") =
          (Miri.Interpreter.OperandPath.instruction "function").push
            (.field "constant") := eq_of_beq h_b
      have h_list := congrArg Array.toList h_arr
      rw [Array.toList_push, Array.toList_push] at h_list
      have h_eq := List.append_cancel_right h_list
      cases path; dsimp only at h_eq; exact congrArg Array.mk h_eq))

/-- Function-item dispatch arm of `refOperandLeaves`'s `constantAt`, which every
operand path outside `OperandPath.assertion` reaches. -/
noncomputable def refConstantAtFnArm (types : List MirTy)
    (path : Miri.Interpreter.OperandPath) (c : Miri.MIR.ConstOperand)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    EStateM.Result Miri.Interpreter.StepError
      (Miri.Interpreter.MachineHooks.State Unit RefUser)
      (Miri.Interpreter.OpTy Miri.Memory.Provenance) :=
  match c with
  | ⟨_, _, .Val .ZeroSized fnTyId⟩ =>
    if path == (Miri.Interpreter.OperandPath.instruction "function").push
        (.field "constant") then
      if Nat.ble (fnTyBase types) fnTyId then
        .ok ⟨.immediate .uninit, ⟨fnTyId, refUnitLayoutData⟩⟩ st
      else
        .error (.unsupported "invalid function TyId") st
    else
      refEvalConstOperand types c st
  | _ => refEvalConstOperand types c st

/-- At an operand path other than `OperandPath.instruction "function"` whose
`constantAt` dispatch reaches `refConstantAtFnArm` (`h_arm`, closed by `rfl`
for concrete non-assertion paths), `constantAt` is `refEvalConstOperand`. -/
theorem refConstantAt_eq_of_ne_fn (rp : RefProg) (c : Choice)
    (path : Miri.Interpreter.OperandPath)
    (h_fn : path ≠ Miri.Interpreter.OperandPath.instruction "function")
    (h_arm : ∀ (mc : Miri.MIR.ConstOperand)
      (known : Option Miri.Interpreter.LocalLayout)
      (st : Miri.Interpreter.MachineHooks.State Unit RefUser),
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).constantAt
        c (path.push (.field "constant")) mc known st =
        refConstantAtFnArm rp.types (path.push (.field "constant")) mc st) :
    ∀ (mc : Miri.MIR.ConstOperand)
      (known : Option Miri.Interpreter.LocalLayout)
      (st : Miri.Interpreter.MachineHooks.State Unit RefUser),
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).constantAt
        c (path.push (.field "constant")) mc known st =
        refEvalConstOperand rp.types mc st := by
  intro mc known st
  rw [h_arm]
  cases mc with
  | mk sp ut v =>
    cases v with
    | Val cv ty =>
      cases cv with
      | ZeroSized =>
        dsimp only [refConstantAtFnArm]
        rw [path_push_const_beq_fn_false h_fn]
        rfl
      | _ => rfl
    | _ => rfl

theorem operandMachine_evalOperandAt_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (amem : MemoryState)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (path : Miri.Interpreter.OperandPath)
    (rop : RefOperand) (op : Operand) (tyOk : MirTy → Bool)
    (known : Option LocalLayout)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_path : ∀ (mc : Miri.MIR.ConstOperand)
      (known' : Option Miri.Interpreter.LocalLayout)
      (st' : Miri.Interpreter.MachineHooks.State Unit RefUser),
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).constantAt
        c (path.push (.field "constant")) mc known' st' =
        refEvalConstOperand rp.types mc st')
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_op : decodeOperand rp.types rop = some op)
    (h_known : operandKnownOk rp.types bodyLocals cache op known) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let res := Miri.Interpreter.OperandMachine.evalOperandAt
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
      c path (toMiriOperand rp.types rop) known st
    match evalOperandToSlot bodyLocals slots amem tyOk op with
    | .error k =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
    | .ok (ty, optVal, slots', _) =>
      res = .ok ⟨.immediate (optValToMiriImm ty optVal),
          refLocalLayoutForTy rp.types ty⟩
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots'
          (operandCacheTouch cache op) mem ctrl cm) := by
  intro st res
  cases rop with
  | copy rpl =>
    dsimp only [decodeOperand, optMap] at h_op
    cases h_pl : decodePlace rp.types rpl with
    | none => rw [h_pl] at h_op; cases h_op
    | some pl =>
      rw [h_pl] at h_op; injection h_op with h_eq; subst h_eq
      have h_ev := operandMachine_evalPlaceToOp_eq rp c ctx rbody blockIdx
        stmtIdx bodyLocals slots cache mem ctrl cm rpl pl known h_locs h_c_len
        h_pl h_inv h_known
      change (match evalOperandToSlot bodyLocals slots amem tyOk (.copy pl) with
        | .error k => ∃ err st', Miri.Interpreter.OperandMachine.evalPlaceToOp
            (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
            c (toMiriPlace rpl) known st = .error err st' ∧ stepErrorFaultKind err = some k
        | .ok (ty, optVal, slots', _) =>
          Miri.Interpreter.OperandMachine.evalPlaceToOp
            (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
            c (toMiriPlace rpl) known st =
            .ok ⟨.immediate (optValToMiriImm ty optVal), refLocalLayoutForTy rp.types ty⟩
              (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots'
                (cacheTouch cache pl.localId) mem ctrl cm))
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
          | partialTuple _ =>
            exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)
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
      have h_ev := operandMachine_evalPlaceToOp_eq rp c ctx rbody blockIdx
        stmtIdx bodyLocals slots cache mem ctrl cm rpl pl known h_locs h_c_len
        h_pl h_inv h_known
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
          | partialTuple _ =>
            exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)
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
              let ⟨b, h_c⟩ := getElem?_some_of_length_eq h_c_len.symm h_ty
              have h_c' := getElem?_cacheTouch_self h_c
              dsimp only
              rw [ite_not_true_eq, h_set]
              have h_rep := mkGenSimFrame_replaceLocalValue_some rp ctx rbody
                blockIdx stmtIdx bodyLocals slots slots' (cacheTouch cache pl.localId)
                pl.localId ty (.immediate optVal) (liveUninitSlot ty) true
                h_ty h_sl h_c' h_set
              rw [slotToMiriLocalValue_liveUninit ty] at h_rep
              have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
                bodyLocals slots (cacheTouch cache pl.localId) mem ctrl cm
              have h_set_fr := setCurrentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
                bodyLocals slots slots' (cacheTouch cache pl.localId)
                (cacheTouch cache pl.localId) mem ctrl cm
              dsimp only [res, Miri.Interpreter.OperandMachine.evalOperandAt,
                Miri.Interpreter.OperandMachine.evalOperand, toMiriOperand]
              rw [h_deinit]
              dsimp only [Bool.not, ite_false_eq, bind, Bind.bind, pure, Pure.pure]
              rw [eStateM_bind_ok h_ev]
              simp only [h_proj_empty, ite_true]
              dsimp only [toMiriPlace]
              rw [h_id, h_deinit_eq, eStateM_bind_ok h_cf, h_rep]
              change (EStateM.bind (EStateM.pure _) _ _) = _
              rw [eStateM_bind_pure]
              rw [eStateM_bind_ok h_set_fr]
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
                    (canonicalTyId rp.types tyId)⟩ st := by
            have h_eq :
                res =
                  (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).constantAt
                    c (path.push (.field "constant"))
                    ⟨⟨0⟩, none, .Val (.Scalar (.Int bits.toNat 16))
                      (canonicalTyId rp.types tyId)⟩ known st := rfl
            rw [h_eq]
            exact h_path _ known st
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
                  ⟨⟨0⟩, none, .Val .ZeroSized (canonicalTyId rp.types tyId)⟩ st := by
            have h_eq :
                res =
                  (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).constantAt
                    c (path.push (.field "constant"))
                    ⟨⟨0⟩, none, .Val .ZeroSized (canonicalTyId rp.types tyId)⟩ known st := rfl
            rw [h_eq]
            exact h_path _ known st
          dsimp only [evalOperandToSlot]
          rw [h_step]
          dsimp only [refEvalConstOperand]
          rw [h_can.1, h_get_can]
          dsimp only
          rw [evalRefConstLit_eq]
          cases evalConstLit ty .zeroSized with
          | error k => cases k <;> exact ⟨_, _, rfl, rfl⟩
          | ok v => rfl
        | rodataBytes _ | rodataRef _ _ _ _ =>
          have h_step :
              res =
                refEvalConstOperand rp.types
                  ⟨⟨0⟩, none, .Val (.Indirect 0 0) (canonicalTyId rp.types tyId)⟩ st := by
            have h_eq :
                res =
                  (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).constantAt
                    c (path.push (.field "constant"))
                    ⟨⟨0⟩, none, .Val (.Indirect 0 0) (canonicalTyId rp.types tyId)⟩ known st := rfl
            rw [h_eq]
            exact h_path _ known st
          dsimp only [evalOperandToSlot]
          rw [h_step]
          dsimp only [refEvalConstOperand]
          exact ⟨_, _, rfl, rfl⟩

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
  | unit | never | ordering | enum _ | ref _ _ | rawPtr _ _
  | slice _ | array _ _ | rangeTo _ | rangeFrom _ | unsupported =>
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
      stepErrorFaultKind err = some .unsupported := by
  cases ty with
  | bool | int _ _ | char => cases h_np
  | unit | never | ordering | ref _ _ | rawPtr _ _
  | slice _ | array _ _ | rangeTo _ | rangeFrom _ | unsupported =>
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
          refAsEnumTy?, refEnumLayoutData]
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
          refAsEnumTy?, refEnumLayoutData]
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
        | partialTuple _ => cases h_es
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
        | partialTuple _ => cases h_es
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

private theorem evalOperandToSlot_operandTy? {bodyLocals : List MirTy}
    {slots : List LocalSlot} {amem : MemoryState} {tyOk : MirTy → Bool}
    {op : Operand} {ty : MirTy} {optVal : Option Val}
    {slots' : List LocalSlot} {amem' : MemoryState}
    (h_es : evalOperandToSlot bodyLocals slots amem tyOk op =
      .ok (ty, optVal, slots', amem')) :
    operandTy? bodyLocals op = some ty := by
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
        | partialTuple _ => cases h_es
        | immediate _ =>
          cases h_pe : pl.projection.isEmpty with
          | false => rw [h_pe] at h_es; cases h_es
          | true =>
            rw [h_pe] at h_es; dsimp only at h_es; injection h_es with h_t'
            have h_eq : t = ty := congrArg Prod.fst h_t'
            subst h_eq
            dsimp only [operandTy?]
            rw [h_pe, ite_true_eq, h_t]
        | indirect _ =>
          cases h_pe : pl.projection.isEmpty with
          | false => rw [h_pe] at h_es; cases h_es
          | true =>
            rw [h_pe] at h_es; dsimp only at h_es
            cases h_ok : tyOk t with
            | false => rw [h_ok] at h_es; cases h_es
            | true =>
              rw [h_ok] at h_es
              cases h_ld : loadIndirect amem t _ with
              | error _ => rw [h_ld] at h_es; cases h_es
              | ok _ =>
                rw [h_ld] at h_es; injection h_es with h_t'
                have h_eq : t = ty := congrArg Prod.fst h_t'
                subst h_eq
                dsimp only [operandTy?]
                rw [h_pe, ite_true_eq, h_t]
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
        | partialTuple _ => cases h_es
        | immediate _ =>
          cases h_pe : pl.projection.isEmpty with
          | false => rw [h_pe] at h_es; cases h_es
          | true =>
            rw [h_pe] at h_es; dsimp only at h_es
            cases h_set : MirSemantics.setElem? slots pl.localId (liveUninitSlot t) with
            | none => rw [h_set] at h_es; cases h_es
            | some _ =>
              rw [h_set] at h_es; injection h_es with h_t'
              have h_eq : t = ty := congrArg Prod.fst h_t'
              subst h_eq
              dsimp only [operandTy?]
              rw [h_pe, ite_true_eq, h_t]
        | indirect _ =>
          cases h_pe : pl.projection.isEmpty with
          | false => rw [h_pe] at h_es; cases h_es
          | true =>
            rw [h_pe] at h_es; dsimp only at h_es
            cases h_ok : tyOk t with
            | false => rw [h_ok] at h_es; cases h_es
            | true =>
              rw [h_ok] at h_es
              cases h_ld : loadIndirect amem t _ with
              | error _ => rw [h_ld] at h_es; cases h_es
              | ok _ =>
                rw [h_ld] at h_es
                cases h_di : deinitIndirect amem t _ with
                | error _ => rw [h_di] at h_es; cases h_es
                | ok _ =>
                  rw [h_di] at h_es; injection h_es with h_t'
                  have h_eq : t = ty := congrArg Prod.fst h_t'
                  subst h_eq
                  dsimp only [operandTy?]
                  rw [h_pe, ite_true_eq, h_t]
  | constant c =>
    dsimp only [evalOperandToSlot] at h_es
    cases h_ev : evalConstLit c.ty c.lit with
    | error _ => rw [h_ev] at h_es; cases h_es
    | ok _ =>
      rw [h_ev] at h_es; injection h_es with h_t'
      have h_eq : c.ty = ty := congrArg Prod.fst h_t'
      subst h_eq
      rfl

theorem evalPrimitiveOperand_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (amem : MemoryState)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (path : Miri.Interpreter.OperandPath)
    (rop : RefOperand) (op : Operand) (known : Option LocalLayout)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_path : ∀ (mc : Miri.MIR.ConstOperand)
      (known' : Option Miri.Interpreter.LocalLayout)
      (st' : Miri.Interpreter.MachineHooks.State Unit RefUser),
      (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp)).constantAt
        c (path.push (.field "constant")) mc known' st' =
        refEvalConstOperand rp.types mc st')
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_op : decodeOperand rp.types rop = some op)
    (h_known : operandKnownOk rp.types bodyLocals cache op known)
    (h_loc_res : ∀ (id : LocalId) (ty : MirTy),
      MirSemantics.getElem? bodyLocals id = some ty →
      resolveTy rp.types (tyIdFor rp.types ty) = some ty) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let res := EStateM.bind
      (Miri.Interpreter.OperandMachine.evalOperandAt
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfg rp))
        c path (toMiriOperand rp.types rop) known)
      (Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig) st
    match evalPrimitiveOperand bodyLocals slots amem op with
    | .error k =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
    | .ok (v, slots', _) =>
      ∃ ty : MirTy,
        checkVal v ty = true ∧
        isPrimitiveReadableTy ty = true ∧
        resolveTy rp.types (tyIdFor rp.types ty) = some ty ∧
        operandTy? bodyLocals op = some ty ∧
        res = .ok ⟨valToMiriImmediate ty v, refLocalLayoutForTy rp.types ty⟩
          (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots'
            (operandCacheTouch cache op) mem ctrl cm) := by
  intro st res
  have h_ev := operandMachine_evalOperandAt_eq rp c ctx rbody blockIdx stmtIdx
    bodyLocals slots cache amem mem ctrl cm path rop op
    isPrimitiveReadableTy known h_locs h_c_len h_path h_inv h_op h_known
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
    have h_opty := evalOperandToSlot_operandTy? h_es
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
        let st' := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots'
          (operandCacheTouch cache op) mem ctrl cm
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
        let st' := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots'
          (operandCacheTouch cache op) mem ctrl cm
        have h_cv : checkVal v ty = true := h_sm
        cases checkVal_eq_true_inv h_cv with
        | inl hi =>
          let ⟨w, s, bits, hty, hv, _⟩ := hi
          subst hty; subst hv
          exact ⟨.int w s, h_cv, rfl, h_tres, h_opty,
            readImmediate_imm_int_ok w s bits rp.types st' rfl⟩
        | inr h1 =>
          cases h1 with
          | inl hb =>
            let ⟨b, hty, hv⟩ := hb
            subst hty; subst hv
            exact ⟨.bool, h_cv, rfl, h_tres, h_opty,
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
                  exact ⟨.char, h_cv, rfl, h_tres, h_opty,
                    readImmediate_imm_char_ok ch rp.types st' rfl⟩
                | inr h5 =>
                  cases h5 with
                  | inl ho => let ⟨_, hty, _⟩ := ho; subst hty; cases h_pr
                  | inr hp =>
                    let ⟨w, s, bits, b, hty, hv, _⟩ := hp
                    subst hty; subst hv
                    exact ⟨_, h_cv, rfl, h_tres, h_opty,
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
      some (match err with
      | .undefinedBehavior _ => .undefined
      | .scalar (.invalidBool _) => .undefined
      | .scalar (.invalidChar _) => .undefined
      | _ => .unsupported) := by
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
        stepErrorFaultKind e = some .unsupported) ∨
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
        stepErrorFaultKind err = some k
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
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
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
        | .error k => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
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
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
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
        ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
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
      match refAsEnumTy? ty with
      | some ety =>
        if refEnumAdmitted ety then
          .ok (refLocalLayoutForTy rp.types (.int ety.discrWidth ety.discrSigned)) st
        else
          .error (.unsupported "unadmitted enum in discriminantLayout") st
      | none => .error (.unsupported "discriminant on non-enum type") st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refDiscriminantLeaves]
  rw [h_res]
  rfl

private theorem discrHooks_discriminantLayout_enumLike (rp : RefProg)
    (c : Choice) {ty : MirTy} {ety : EnumTy}
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike rp.types ty ety)
    (h_adm : enumAdmitted ety = true) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).discriminantLayout c (tyIdFor rp.types ty) st =
      .ok (refLocalLayoutForTy rp.types
        (.int ety.discrWidth ety.discrSigned)) st := by
  have h_ref_adm : refEnumAdmitted ety = true := by
    rw [refEnumAdmitted_eq]; exact h_adm
  rw [discrHooks_discriminantLayout rp c ty st h_el.2, h_el.1]
  dsimp only; rw [h_ref_adm]; rfl

private theorem discrHooks_projectRead_imm_enumLike (rp : RefProg) (c : Choice)
    {ty : MirTy} {ety : EnumTy} (tagW : IntWidth) (tagS : Bool)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike rp.types ty ety)
    (h_tr : ety.tagRepr = .scalar tagW tagS) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).projectRead
        c ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩ 0 st =
      .ok ⟨.immediate imm, refLocalLayoutForTy rp.types (.int tagW tagS)⟩ st := by
  have h_proj_field :
      Miri.Interpreter.projectField (refProjectionCx rp.types)
          ⟨.immediate imm, refLocalLayoutForTy rp.types ty⟩ 0 =
        .ok ⟨.immediate imm, refLocalLayoutForTy rp.types (.int tagW tagS)⟩ := by
    dsimp only [Miri.Interpreter.projectField, refProjectionCx]
    rw [enumLike_projectField0 h_el h_tr, enumLike_layout h_el,
      refEnumLayoutData_scalar ety tagW tagS h_tr]
    cases tagW <;> cases tagS <;> cases imm <;> rfl
  dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    Miri.Interpreter.ExecutionMachine.operandHooks,
    Miri.Interpreter.OperandMachine.field, bind, Bind.bind]
  change (EStateM.bind (EStateM.pure (refProjectionCx rp.types)) _ st) = _
  rw [eStateM_bind_pure, h_proj_field]
  rfl

private theorem discrHooks_variantForDiscriminant_enumLike (rp : RefProg)
    (c : Choice) {ty : MirTy} {ety : EnumTy} (bits : BitVec 128)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike rp.types ty ety) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).variantForDiscriminant c (tyIdFor rp.types ty)
          bits st =
      .ok (refFindDiscrVariant? bits ety.discriminants) st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks,
    refExecCfg, Miri.Interpreter.ExecutionMachine.withValidation,
    refExecutionConfig, refDiscriminantLeaves]
  rw [h_el.2]
  dsimp only [Option.bind]
  rw [h_el.1]

private theorem discrHooks_discriminantValue_enumLike (rp : RefProg)
    (c : Choice) {ty : MirTy} {ety : EnumTy} (variant disc : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike rp.types ty ety)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc) :
    (Miri.Interpreter.ExecutionMachine.discriminantHooks
        (refExecCfg rp)).discriminantValue c (tyIdFor rp.types ty)
          variant st =
      .ok (some (tyIdFor rp.types (.int ety.discrWidth ety.discrSigned),
        BitVec.ofNat 128 disc)) st := by
  dsimp only [Miri.Interpreter.ExecutionMachine.discriminantHooks,
    refExecCfg, Miri.Interpreter.ExecutionMachine.withValidation,
    refExecutionConfig, refDiscriminantLeaves]
  rw [h_el.2]
  dsimp only [Option.bind]
  rw [h_el.1]
  dsimp only
  rw [h_get_d]

/-- `Discriminant.readDiscriminant` on an initialized scalar-tag immediate of an
`EnumLike` local type (`.enum ety` or `core::cmp::Ordering`). -/
private theorem discrHooks_readDiscriminant_scalar_ok (rp : RefProg)
    (c : Choice) (ty : MirTy) (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (variant disc : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike rp.types ty ety)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.Discriminant.readDiscriminant
        (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
        ⟨.immediate (.scalar (.fromScalarInt
            (miriScalar tagW (BitVec.ofNat 128 disc)))),
          refLocalLayoutForTy rp.types ty⟩ st =
      .ok variant st := by
  let dh := Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)
  have h_lay : refLayoutDataForTy ty = refEnumLayoutData ety :=
    enumLike_layoutData h_el.1
  have h_dl := discrHooks_discriminantLayout_enumLike rp c st h_el h_adm
  have h_tl : dh.tagLayout c (.Union (value := .Int (toMiriInteger tagW) tagS)) st =
      .ok (refLocalLayoutForTy rp.types (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)) st := rfl
  have h_pr' := discrHooks_projectRead_imm_enumLike rp c tagW tagS
    (.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))) st h_el h_tr
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
    have h := discrHooks_variantForDiscriminant_enumLike rp c (BitVec.ofNat 128 disc) st h_el
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

/-- `Discriminant.readDiscriminant` on an uninitialized immediate of an
`EnumLike` scalar-tagged local type fails with `.undefinedBehavior`. -/
private theorem discrHooks_readDiscriminant_scalar_uninit_ub (rp : RefProg)
    (c : Choice) (ty : MirTy) (ety : EnumTy) (tagW : IntWidth) (tagS : Bool)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike rp.types ty ety)
    (h_tr : ety.tagRepr = .scalar tagW tagS)
    (h_adm : enumAdmitted ety = true)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    ∃ msg,
      Miri.Interpreter.Discriminant.readDiscriminant
          (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
          ⟨.immediate .uninit, refLocalLayoutForTy rp.types ty⟩ st =
        .error (.undefinedBehavior msg) st := by
  let dh := Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)
  have h_dl := discrHooks_discriminantLayout_enumLike rp c st h_el h_adm
  have h_pr := discrHooks_projectRead_imm_enumLike rp c tagW tagS .uninit st h_el h_tr
  have h_tl : dh.tagLayout c (.Union (value := .Int (toMiriInteger tagW) tagS)) st =
      .ok (refLocalLayoutForTy rp.types (.int (intWidthOfMiriInteger (toMiriInteger tagW)) tagS)) st := rfl
  let ⟨msg, h_ri⟩ := readImmediate_imm_int_uninit tagW tagS rp.types st h_pmd
  have h_ri' : dh.readImmediate c
      ⟨.immediate .uninit, refLocalLayoutForTy rp.types (.int tagW tagS)⟩ st =
      .error (.undefinedBehavior msg) st := h_ri
  have h_vars : (refLocalLayoutForTy rp.types ty).layout.variants =
      .Multiple (.Union (value := .Int (toMiriInteger tagW) tagS)) .Direct 0
        (ety.discriminants.map (fun _ => refInhabitedVariantLayout)).toArray := by
    rw [enumLike_layout h_el]
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

/-- `Discriminant.discriminantForVariant` for an `EnumLike` local type whose
admitted descriptor `ety` maps `variant` to `disc`. -/
private theorem discrHooks_discriminantForVariant_ok (rp : RefProg)
    (c : Choice) (ty : MirTy) (ety : EnumTy) (variant disc : Nat)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_el : EnumLike rp.types ty ety)
    (h_adm : enumAdmitted ety = true)
    (h_get_d : MirSemantics.getElem? ety.discriminants variant = some disc) :
    Miri.Interpreter.Discriminant.discriminantForVariant
        (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
        (tyIdFor rp.types ty) variant st =
      .ok ⟨.scalar (.fromScalarInt (miriScalar ety.discrWidth (BitVec.ofNat 128 disc))),
        refLocalLayoutForTy rp.types (.int ety.discrWidth ety.discrSigned)⟩ st := by
  let dh := Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)
  have h_dl := discrHooks_discriminantLayout_enumLike rp c st h_el h_adm
  have h_dv := discrHooks_discriminantValue_enumLike rp c variant disc st h_el h_get_d
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

/-! ## Section 6: `PlaceDynamic.evalPlace`, Writes, and `evalRvalueIntoPlace` -/

theorem placeHooks_frameIndex_ok (rp : RefProg) (ctx : SimFrameCtx)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :
    (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.frameIndex
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) =
      .ok ctx.below.size
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm) := by
  dsimp only [Miri.Interpreter.ExecutionMachine.projectionHooks, refExecCfg,
    Miri.Interpreter.ExecutionMachine.withValidation, refExecutionConfig,
    refPlaceProjectionHooks, Miri.Interpreter.PlaceMachine.placeHooks,
    bind, Bind.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, Pure.pure,
    EStateM.pure, EStateM.bind]
  dsimp only [mkGenSimState, mkRefMiriStackState]
  rw [stack_frameIndex_push]
  rfl

private theorem localToPlace_ok (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (slot : LocalSlot)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    Miri.Interpreter.localToPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c id st =
      .ok ⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types ty⟩
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
          (cacheTouch cache id) mem ctrl cm) := by
  intro st
  let ⟨b, h_c⟩ := getElem?_some_of_length_eq h_c_len.symm h_ty
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
  have h_gl := mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache id ty slot b h_ty h_sl h_c
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_pl :
      Miri.Interpreter.placeLayoutOfLocal
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c id st =
      .ok (refLocalLayoutForTy rp.types ty)
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
          (cacheTouch cache id) mem ctrl cm) := by
    cases b with
    | true =>
      rw [cacheTouch_eq_self_of_true h_c]
      dsimp only [Miri.Interpreter.placeLayoutOfLocal, bind, Bind.bind, pure, Pure.pure]
      have h_gf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st =
          .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache) st := h_cf
      rw [eStateM_bind_ok h_gf, h_gl]; rfl
    | false =>
      have h_rl :
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.resolveLayout c id st =
            .ok (refLocalLayoutForTy rp.types ty) st :=
        operandHooks_compiler_layout_ok rp ctx c rbody blockIdx stmtIdx
          bodyLocals slots cache mem ctrl cm id ty h_locs h_ty
      have h_gc := mkGenSimFrame_getOrCacheLocalLayout_some rp ctx rbody blockIdx
        stmtIdx bodyLocals slots cache id ty slot false
        (refLocalLayoutForTy rp.types ty) h_ty h_sl h_c (fun _ => rfl)
      have h_set := setCurrentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
        bodyLocals slots slots cache (cacheTouch cache id) mem ctrl cm
      dsimp only [Miri.Interpreter.placeLayoutOfLocal, bind, Bind.bind, pure, Pure.pure]
      have h_gf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st =
          .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache) st := h_cf
      rw [eStateM_bind_ok h_gf, h_gl]
      dsimp only [refLocalStateOfSlotWithCache]
      rw [ite_false_eq]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      rw [eStateM_bind_ok h_rl, eStateM_bind_ok h_gf, h_gc]
      change (EStateM.bind (EStateM.pure _) _ st) = _
      rw [eStateM_bind_pure]
      dsimp only
      have h_sf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.setFrame
          (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots (cacheTouch cache id)) st =
          .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
            (cacheTouch cache id) mem ctrl cm) := h_set
      rw [eStateM_bind_ok h_sf]
      rfl
  let st' := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
    (cacheTouch cache id) mem ctrl cm
  have h_fi := placeHooks_frameIndex_ok rp ctx rbody blockIdx stmtIdx bodyLocals
    slots (cacheTouch cache id) mem ctrl cm
  have h_cf' := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots (cacheTouch cache id) mem ctrl cm
  have h_gf' : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st' =
      .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots
        (cacheTouch cache id)) st' := h_cf'
  dsimp only [Miri.Interpreter.localToPlace, bind, Bind.bind, pure, Pure.pure]
  rw [eStateM_bind_ok h_pl]
  simp only [h_sz, ite_true]
  rw [eStateM_bind_ok h_fi, eStateM_bind_ok h_gf']
  rfl

private theorem localToPlace_oob (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId)
    (h_oob : MirSemantics.getElem? bodyLocals id = none ∨
      MirSemantics.getElem? slots id = none) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    Miri.Interpreter.localToPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c id st =
      .error (.stack (.invalidLocal id (liftLocalsCached rp.types bodyLocals slots cache).length)) st := by
  intro st
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
  have h_gl :
      (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache).getLocal id =
        .error (.invalidLocal id (liftLocalsCached rp.types bodyLocals slots cache).length) := by
    cases h_oob with
    | inl h =>
      exact mkGenSimFrame_getLocal_none_left rp ctx rbody blockIdx
        stmtIdx bodyLocals slots cache id h
    | inr h =>
      exact mkGenSimFrame_getLocal_none_right rp ctx rbody blockIdx
        stmtIdx bodyLocals slots cache id h
  have h_pl :
      Miri.Interpreter.placeLayoutOfLocal
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c id st =
      .error (.stack (.invalidLocal id (liftLocalsCached rp.types bodyLocals slots cache).length)) st := by
    dsimp only [Miri.Interpreter.placeLayoutOfLocal, bind, Bind.bind, pure, Pure.pure]
    have h_gf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st =
        .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache) st := h_cf
    rw [eStateM_bind_ok h_gf, h_gl]; rfl
  dsimp only [Miri.Interpreter.localToPlace, bind, Bind.bind]
  rw [eStateM_bind_err h_pl]

theorem placeDynamic_evalPlace_local_ok (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (skip : Bool) (ty : MirTy) (slot : LocalSlot)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    Miri.Interpreter.PlaceDynamic.evalPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
        c ⟨id, Array.empty⟩ skip st =
      .ok ⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types ty⟩
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
          (cacheTouch cache id) mem ctrl cm) := by
  intro st
  have h_lp := localToPlace_ok rp c ctx rbody blockIdx stmtIdx bodyLocals slots
    cache mem ctrl cm id ty slot h_locs h_c_len h_ty h_sl
  let st' := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
    (cacheTouch cache id) mem ctrl cm
  dsimp only [Miri.Interpreter.PlaceDynamic.evalPlace, bind, Bind.bind]
  rw [eStateM_bind_ok h_lp]
  have h_arr_ne : (Array.empty == Array.mk [Miri.MIR.ProjectionElem.Deref]) = false := rfl
  rw [h_arr_ne, Bool.and_false, ite_false_eq]
  rw [eStateM_bind_ok (array_forIn_empty _ _ st')]
  rfl

theorem placeDynamic_evalPlace_oob (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (pl : Miri.MIR.Place) (skip : Bool)
    (h_oob : MirSemantics.getElem? bodyLocals pl.localId = none ∨
      MirSemantics.getElem? slots pl.localId = none) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    Miri.Interpreter.PlaceDynamic.evalPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
        c pl skip st =
      .error (.stack (.invalidLocal pl.localId (liftLocalsCached rp.types bodyLocals slots cache).length)) st := by
  intro st
  have h_lp := localToPlace_oob rp c ctx rbody blockIdx stmtIdx bodyLocals slots
    cache mem ctrl cm pl.localId h_oob
  dsimp only [Miri.Interpreter.PlaceDynamic.evalPlace, bind, Bind.bind]
  rw [eStateM_bind_err h_lp]

private theorem placeDynamic_evalPlace_deref_err (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (slot : LocalSlot)
    (h_locs : decodeLocalTys rp.types rbody.locals = some bodyLocals)
    (h_c_len : cache.length = bodyLocals.length)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some slot) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    Miri.Interpreter.PlaceDynamic.evalPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
        c ⟨id, Array.mk [.Deref]⟩ true st =
      .error (.unsupported "projections unsupported on Day 1")
        (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
          (cacheTouch cache id) mem ctrl cm) := by
  intro st
  have h_lp := localToPlace_ok rp c ctx rbody blockIdx stmtIdx bodyLocals slots
    cache mem ctrl cm id ty slot h_locs h_c_len h_ty h_sl
  dsimp only [Miri.Interpreter.PlaceDynamic.evalPlace, bind, Bind.bind]
  rw [eStateM_bind_ok h_lp]
  rfl

private theorem writePlaceImmediateNoValidate_local_dead (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (b : Bool)
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some .dead)
    (h_c : MirSemantics.getElem? cache id = some b) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    Miri.Interpreter.writePlaceImmediateNoValidate
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c imm ⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .error (.stack (.localExpectedLive id)) st := by
  intro st
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
  have h_go := mkGenSimFrame_getLocalOperand_dead rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache id ty b h_ty h_sl h_c
  have h_fi := placeHooks_frameIndex_ok rp ctx rbody blockIdx stmtIdx bodyLocals
    slots cache mem ctrl cm
  have h_as :
      Miri.Interpreter.asMplaceOrMutableLocal
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place c
        ⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .error (.stack (.localExpectedLive id)) st := by
    dsimp only [Miri.Interpreter.asMplaceOrMutableLocal, Option.isSome]
    rw [ite_false_eq, Miri.Interpreter.requireCurrent_eq]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_assoc, eStateM_bind_ok h_fi, bne_self_eq_false]
    simp only [Bool.false_eq_true, ite_false]
    rw [eStateM_bind_pure]
    have h_da : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.debugAssertions = false := rfl
    rw [Miri.Interpreter.checkLocalIdentity_debugOff _ _ h_da]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure]
    simp only [h_da, Bool.false_eq_true, ite_false]
    have h_gf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st =
        .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache) st := h_cf
    rw [eStateM_bind_ok h_gf, h_go]; rfl
  dsimp only [Miri.Interpreter.writePlaceImmediateNoValidate, bind, Bind.bind]
  simp only [h_sz, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [eStateM_bind_err h_as]

private theorem writePlaceImmediateNoValidate_local_live (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots slots' : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (optVal optVal' : Option Val)
    (b : Bool)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal))
    (h_c : MirSemantics.getElem? cache id = some b)
    (h_set : MirSemantics.setElem? slots id (.immediate optVal') = some slots') :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    Miri.Interpreter.writePlaceImmediateNoValidate
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c (optValToMiriImm ty optVal')
        ⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache
        mem ctrl cm) := by
  intro st
  have h_sz : (refLocalLayoutForTy rp.types ty).layout.isSized = true :=
    refLayoutDataForTy_isSized ty
  have h_cf := currentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
  have h_go := mkGenSimFrame_getLocalOperand_live rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache id ty optVal b h_ty h_sl h_c
  have h_so := mkGenSimFrame_setLocalOperand_some rp ctx rbody blockIdx stmtIdx
    bodyLocals slots slots' cache id ty optVal optVal' b h_ty h_sl h_c h_set
  have h_set_fr := setCurrentFrame_mkGenSimState rp ctx rbody blockIdx stmtIdx
    bodyLocals slots slots' cache cache mem ctrl cm
  have h_fi := placeHooks_frameIndex_ok rp ctx rbody blockIdx stmtIdx bodyLocals
    slots cache mem ctrl cm
  have h_as :
      Miri.Interpreter.asMplaceOrMutableLocal
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place c
        ⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .ok (.immediateLocal id (refLocalLayoutForTy rp.types ty)) st := by
    dsimp only [Miri.Interpreter.asMplaceOrMutableLocal, Option.isSome]
    rw [ite_false_eq, Miri.Interpreter.requireCurrent_eq]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_assoc, eStateM_bind_ok h_fi, bne_self_eq_false]
    simp only [Bool.false_eq_true, ite_false]
    rw [eStateM_bind_pure]
    have h_da : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.debugAssertions = false := rfl
    rw [Miri.Interpreter.checkLocalIdentity_debugOff _ _ h_da]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure]
    simp only [h_da, Bool.false_eq_true, ite_false]
    have h_gf : (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.getFrame st =
        .ok (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots cache) st := h_cf
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
  change (EStateM.bind (EStateM.pure _) _ st) = _
  rw [eStateM_bind_pure]
  rw [eStateM_bind_ok h_set_fr, eStateM_bind_pure]
  rw [ite_false_eq, eStateM_bind_ok (afterLocalWrite_mkGenSimState rp ctx rbody blockIdx
    stmtIdx bodyLocals slots' cache mem ctrl cm id false)]
  rfl

private theorem writePlaceImmediate_local_ok (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots slots' : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (id : LocalId) (ty : MirTy) (optVal : Option Val) (v : Val)
    (h_ty : MirSemantics.getElem? bodyLocals id = some ty)
    (h_sl : MirSemantics.getElem? slots id = some (.immediate optVal))
    (h_c : MirSemantics.getElem? cache id = some true)
    (h_set : MirSemantics.setElem? slots id (.immediate (some v)) = some slots')
    (h_cv : checkVal v ty = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types ty) = some ty) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let st' := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache
      mem ctrl cm
    Miri.Interpreter.writePlaceImmediate
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
        c (valToMiriImmediate ty v)
        ⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st =
      .ok () st' := by
  intro st st'
  have h_nv := writePlaceImmediateNoValidate_local_live rp c ctx rbody
    blockIdx stmtIdx bodyLocals slots slots' cache mem ctrl cm id ty
    optVal (some v) true h_ty h_sl h_c h_set
  have h_ev :
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.enforceValidity
        c (refLocalLayoutForTy rp.types ty) st' = .ok true st' := rfl
  have h_v :
      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place.validate
        c ⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
          refLocalLayoutForTy rp.types ty⟩ st' =
      Miri.Interpreter.ValidityVisitor.validatePlace
        (Miri.Interpreter.TypedMachineBindings.bindValidity
          (refValidityHooks rp.types) refRetagHooks 8)
        c 8 ⟨.local ctx.below.size id none (LocalsIdentity.ofAllocationToken 0),
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
  have h_curr' : st'.stack.currentFrame? =
      some (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache) := by
    dsimp only [st', mkGenSimState, mkRefMiriStackState]
    exact stack_currentFrame?_push _ _
  have h_fidx' : st'.stack.frameIndex = .ok ctx.below.size := by
    dsimp only [st', mkGenSimState, mkRefMiriStackState]
    exact stack_frameIndex_push _ _
  have h_val := validatePlace_local_ok rp.types c ctx.below.size id ty v
    (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache) st'
    h_curr' h_fidx' rfl rfl
    (mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx bodyLocals slots'
      cache id ty (.immediate (some v)) true h_ty h_sl' h_c)
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

private theorem copyRuntimePlace_imm_to_local_gen (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (amem : MemoryState)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (dstId : LocalId) (srcTy dstTy : MirTy)
    (optVal : Option Val) (dstSlot : LocalSlot) (allowTransmute : Bool)
    (h_dst_ty : MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (h_dst_sl : MirSemantics.getElem? slots dstId = some dstSlot)
    (h_dst_c : MirSemantics.getElem? cache dstId = some true)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_dst_supp : isSupportedScalarOrUnitTy dstTy = true)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_sm : SlotMatchesTy srcTy (.immediate optVal))
    (h_compat : allowTransmute = false ∨ MirTy.beq srcTy dstTy = true) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let h := refExecCfg rp
    let res := Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
      ⟨.immediate (optValToMiriImm srcTy optVal), refLocalLayoutForTy rp.types srcTy⟩
      ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types dstTy⟩ allowTransmute st
    if !(MirTy.beq srcTy dstTy) then
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .unsupported
    else
      match optVal with
      | none =>
        ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .undefined
      | some v =>
        match writePlace slots amem dstId dstTy v with
        | .error k =>
          ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
        | .ok (slots', _) =>
          res = .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals
            slots' cache mem ctrl cm) := by
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
    cases h_compat with
    | inr h_t => rw [h_t] at h_ty_eq; cases h_ty_eq
    | inl h_fa =>
      subst h_fa
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
          ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy rp.types srcTy⟩ allowTransmute st =
        Miri.Interpreter.writePlaceImmediateNoValidate
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place c
          (optValToMiriImm srcTy optVal)
          ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
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
      have h_dead := writePlaceImmediateNoValidate_local_dead rp c ctx rbody
        blockIdx stmtIdx bodyLocals slots cache mem ctrl cm dstId srcTy true
        (optValToMiriImm srcTy optVal) h_dst_ty h_dst_sl h_dst_c
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
    | partialTuple _ =>
      exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_dst_ty h_dst_sl)
    | immediate dstOpt =>
      let ⟨slots', h_set⟩ := mirSetElem?_some_of_lt slots dstId (.immediate optVal)
        (mirGetElem?_lt_of_some h_dst_sl)
      have h_nv_ok := writePlaceImmediateNoValidate_local_live rp c ctx rbody
        blockIdx stmtIdx bodyLocals slots slots' cache mem ctrl cm dstId srcTy
        dstOpt optVal true h_dst_ty h_dst_sl h_dst_c h_set
      let st' := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots'
        cache mem ctrl cm
      have h_ev :
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place.enforceValidity
            c (refLocalLayoutForTy rp.types srcTy) st' = .ok true st' := rfl
      have h_v :
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place.validate
            c ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
              refLocalLayoutForTy rp.types srcTy⟩ st' =
          Miri.Interpreter.ValidityVisitor.validatePlace
            (Miri.Interpreter.TypedMachineBindings.bindValidity
              (refValidityHooks rp.types) refRetagHooks 8)
            c 8 ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
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
              c 8 ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
                refLocalLayoutForTy rp.types srcTy⟩ false true st' := by
        dsimp only [res, Miri.Interpreter.copyRuntimePlace, bind, Bind.bind, EStateM.bind]
        rw [h_nv_eq, h_nv_ok]
        dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
        rw [h_ev]
        dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
        simp only [ite_true]
        rw [bne_self_eq_false, ite_false_eq, h_v]
      have h_curr' : st'.stack.currentFrame? =
          some (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache) := by
        dsimp only [st', mkGenSimState, mkRefMiriStackState]
        exact stack_currentFrame?_push _ _
      have h_fidx' : st'.stack.frameIndex = .ok ctx.below.size := by
        dsimp only [st', mkGenSimState, mkRefMiriStackState]
        exact stack_frameIndex_push _ _
      cases optVal with
      | none =>
        let ⟨msg, st'', h_ub⟩ := validatePlace_local_uninit_ub rp.types c
          ctx.below.size dstId srcTy
          (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache) st'
          h_curr' h_fidx' rfl
          (mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx bodyLocals slots'
            cache dstId srcTy (.immediate none) true h_dst_ty h_sl' h_dst_c)
          h_sm h_dst_supp h_dst_res
        exact ⟨_, _, h_res_val.trans h_ub, rfl⟩
      | some v =>
        dsimp only [writePlace]
        rw [h_sm, ite_not_true_eq, h_dst_sl, h_set]
        have h_ok := validatePlace_local_ok rp.types c ctx.below.size dstId srcTy v
          (mkGenSimFrame rp ctx rbody blockIdx stmtIdx bodyLocals slots' cache) st'
          h_curr' h_fidx' rfl rfl
          (mkGenSimFrame_getLocal_some rp ctx rbody blockIdx stmtIdx bodyLocals slots'
            cache dstId srcTy (.immediate (some v)) true h_dst_ty h_sl' h_dst_c)
          h_sm h_dst_res
        exact h_res_val.trans h_ok

theorem copyRuntimePlace_imm_to_local (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (amem : MemoryState)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (dstId : LocalId) (srcTy dstTy : MirTy)
    (optVal : Option Val) (dstSlot : LocalSlot)
    (h_dst_ty : MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (h_dst_sl : MirSemantics.getElem? slots dstId = some dstSlot)
    (h_dst_c : MirSemantics.getElem? cache dstId = some true)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_dst_supp : isSupportedScalarOrUnitTy dstTy = true)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_sm : SlotMatchesTy srcTy (.immediate optVal)) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let h := refExecCfg rp
    let res := Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
      ⟨.immediate (optValToMiriImm srcTy optVal), refLocalLayoutForTy rp.types srcTy⟩
      ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types dstTy⟩ false st
    if !(MirTy.beq srcTy dstTy) then
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .unsupported
    else
      match optVal with
      | none =>
        ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .undefined
      | some v =>
        match writePlace slots amem dstId dstTy v with
        | .error k =>
          ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
        | .ok (slots', _) =>
          res = .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals
            slots' cache mem ctrl cm) :=
  copyRuntimePlace_imm_to_local_gen rp c ctx rbody blockIdx stmtIdx bodyLocals
    slots cache amem mem ctrl cm dstId srcTy dstTy optVal dstSlot false
    h_dst_ty h_dst_sl h_dst_c h_src_res h_dst_res h_dst_supp h_inv h_sm
    (Or.inl rfl)

theorem copyRuntimePlace_imm_to_local_transmute (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (amem : MemoryState)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (dstId : LocalId) (srcTy dstTy : MirTy)
    (optVal : Option Val) (dstSlot : LocalSlot)
    (h_dst_ty : MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (h_dst_sl : MirSemantics.getElem? slots dstId = some dstSlot)
    (h_dst_c : MirSemantics.getElem? cache dstId = some true)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_dst_supp : isSupportedScalarOrUnitTy dstTy = true)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_sm : SlotMatchesTy srcTy (.immediate optVal))
    (h_eq_ty : MirTy.beq srcTy dstTy = true) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let h := refExecCfg rp
    let res := Miri.Interpreter.copyRuntimePlace
      (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
      ⟨.immediate (optValToMiriImm srcTy optVal), refLocalLayoutForTy rp.types srcTy⟩
      ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types dstTy⟩ true st
    match optVal with
    | none =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some .undefined
    | some v =>
      match writePlace slots amem dstId dstTy v with
      | .error k =>
        ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
      | .ok (slots', _) =>
        res = .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals
          slots' cache mem ctrl cm) := by
  have h := copyRuntimePlace_imm_to_local_gen rp c ctx rbody blockIdx stmtIdx
    bodyLocals slots cache amem mem ctrl cm dstId srcTy dstTy optVal dstSlot
    true h_dst_ty h_dst_sl h_dst_c h_src_res h_dst_res h_dst_supp h_inv h_sm
    (Or.inr h_eq_ty)
  dsimp only at h
  dsimp only
  rw [h_eq_ty] at h
  exact h

/-- Write a validated primitive/discriminant value `v` of type `resTy` into
destination local `dstId` of type `dstTy`, matching `assertRvalueLayout` +
`writePlaceImmediate` against `writePlace`. -/
private theorem assertAndWrite_local_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (amem : MemoryState)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (dstId : LocalId) (resTy dstTy : MirTy) (v : Val)
    (dstSlot : LocalSlot)
    (h_dst_ty : MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (h_dst_sl : MirSemantics.getElem? slots dstId = some dstSlot)
    (h_dst_c : MirSemantics.getElem? cache dstId = some true)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_cv : checkVal v resTy = true) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let res :=
      if (refLocalLayoutForTy rp.types resTy == refLocalLayoutForTy rp.types dstTy) then
        Miri.Interpreter.writePlaceImmediate
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
          c (valToMiriImmediate resTy v)
          ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
            refLocalLayoutForTy rp.types dstTy⟩ st
      else
        .error (.invalidProgram "rvalue result layout mismatch") st
    match writePlace slots amem dstId dstTy v with
    | .error k =>
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
    | .ok (slots', _) =>
      res = .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots'
        cache mem ctrl cm) := by
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
      have h_dead := writePlaceImmediateNoValidate_local_dead rp c ctx rbody
        blockIdx stmtIdx bodyLocals slots cache mem ctrl cm dstId resTy true
        (valToMiriImmediate resTy v) h_dst_ty h_dst_sl h_dst_c
      have h_err :
          Miri.Interpreter.writePlaceImmediate
            (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
            c (valToMiriImmediate resTy v)
            ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
              refLocalLayoutForTy rp.types resTy⟩ st =
          .error (.stack (.localExpectedLive dstId)) st := by
        dsimp only [Miri.Interpreter.writePlaceImmediate, bind, Bind.bind, EStateM.bind]
        rw [h_dead]
      exact ⟨_, _, h_err, rfl⟩
    | indirect _ =>
      exact False.elim (SlotsMatchTys.not_indirect h_inv h_dst_ty h_dst_sl)
    | partialTuple _ =>
      exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_dst_ty h_dst_sl)
    | immediate optVal =>
      let ⟨slots', h_set⟩ := mirSetElem?_some_of_lt slots dstId (.immediate (some v))
        (mirGetElem?_lt_of_some h_dst_sl)
      rw [h_set]
      exact writePlaceImmediate_local_ok rp c ctx rbody blockIdx stmtIdx
        bodyLocals slots slots' cache mem ctrl cm dstId resTy optVal v
        h_dst_ty h_dst_sl h_dst_c h_set h_cv h_dst_res

/-! ### `Rvalue.cast .intToInt` -/

private theorem castHooks_takePendingMoveDeinit (rp : RefProg)
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) :
    (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits).takePendingMoveDeinit
      (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache mem
        ctrl cm) =
      .ok false (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots
        cache mem ctrl cm) := rfl

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
        stepErrorFaultKind err = some .unsupported := by
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
        stepErrorFaultKind err = some .unsupported := by
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
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (amem : MemoryState)
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
    (h_dst_c : MirSemantics.getElem? cache dstId = some true)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_il : isIntLikeTy srcTy = true) (h_n : n < HPow.hPow 2 128)
    (h_read : Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig
        ⟨.immediate imm, refLocalLayoutForTy rp.types srcTy⟩
            (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
            mem ctrl cm) =
      .ok ⟨.scalar sc, refLocalLayoutForTy rp.types srcTy⟩
          (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
          mem ctrl cm))
    (h_ilv : Miri.Interpreter.Cast.intLikeValue
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp)
        refLimits) c sc
        (refLocalLayoutForTy rp.types srcTy)
            (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
            mem ctrl cm) =
      .ok (BitVec.ofNat 128 n, sg) (mkGenSimState rp ctx rbody blockIdx stmtIdx
          bodyLocals slots cache mem ctrl cm))
    (h_ilb : intLikeBits v = some n) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let res := Miri.Interpreter.Cast.cast
        (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp) refLimits)
        c refLimits.casts
      ⟨.immediate imm, refLocalLayoutForTy rp.types srcTy⟩
      .IntToInt (tyIdFor rp.types dstTy)
      ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
        refLocalLayoutForTy rp.types dstTy⟩ st
    match
      (match evalIntToIntCast v dstTy with
       | .error k => .error k
       | .ok r => writePlace slots amem dstId dstTy r :
         Except FaultKind (List LocalSlot × MemoryState)) with
    | .error k => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
    | .ok (slots', _) =>
      res = .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals
        slots' cache mem ctrl cm) := by
  intro st res
  have h_core := cast_intToInt_core rp c st
    (.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0)) srcTy
        dstTy imm sc
    n sg (castHooks_takePendingMoveDeinit rp ctx rbody blockIdx stmtIdx
      bodyLocals slots cache mem ctrl cm) h_src_res h_dst_res h_il h_n h_read
    h_ilv
  dsimp only [res, evalIntToIntCast]
  rw [h_ilb]
  cases dstTy with
  | int w s =>
    dsimp only at h_core
    dsimp only
    rw [h_core]
    have h_aw := assertAndWrite_local_eq rp c ctx rbody blockIdx stmtIdx
      bodyLocals slots cache amem mem ctrl cm dstId (.int w s) (.int w s)
      (.scalar ⟨w, s, truncateBits w (BitVec.ofNat 128 n)⟩) dstSlot h_dst_ty
      h_dst_sl h_dst_c h_dst_res h_inv
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
      have h_aw := assertAndWrite_local_eq rp c ctx rbody blockIdx stmtIdx
        bodyLocals slots cache amem mem ctrl cm dstId .char .char
        (.char (Char.ofNat n)) dstSlot h_dst_ty h_dst_sl h_dst_c h_dst_res
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
    (ctx : SimFrameCtx) (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (bodyLocals : List MirTy) (slots : List LocalSlot) (cache : List Bool)
    (amem : MemoryState)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (dstId : LocalId) (srcTy dstTy : MirTy)
    (optVal : Option Val) (dstSlot : LocalSlot)
    (h_dst_ty : MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (h_dst_sl : MirSemantics.getElem? slots dstId = some dstSlot)
    (h_dst_c : MirSemantics.getElem? cache dstId = some true)
    (h_src_res : resolveTy rp.types (tyIdFor rp.types srcTy) = some srcTy)
    (h_dst_res : resolveTy rp.types (tyIdFor rp.types dstTy) = some dstTy)
    (h_inv : SlotsMatchTys bodyLocals slots)
    (h_sm : SlotMatchesTy srcTy (.immediate optVal)) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals slots cache
      mem ctrl cm
    let res := Miri.Interpreter.Cast.cast
      (Miri.Interpreter.ExecutionMachine.castHooks (refExecCfg rp) refLimits)
      c refLimits.casts
      ⟨.immediate (optValToMiriImm srcTy optVal), refLocalLayoutForTy
          rp.types srcTy⟩
      .IntToInt (tyIdFor rp.types dstTy)
      ⟨.local ctx.below.size dstId none (LocalsIdentity.ofAllocationToken 0),
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
    | .error k => ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
    | .ok (slots', _) =>
      res = .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx bodyLocals
        slots' cache mem ctrl cm) := by
  intro st res
  have h_take := castHooks_takePendingMoveDeinit rp ctx rbody blockIdx stmtIdx
    bodyLocals slots cache mem ctrl cm
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
          exact cast_intToInt_some rp c ctx rbody blockIdx stmtIdx
            bodyLocals slots cache amem mem ctrl cm dstId
            (.int w false) dstTy dstSlot _ _ (truncateBits w bits).toNat false _
            h_dst_ty h_dst_sl h_dst_c h_src_res h_dst_res h_inv h_il (BitVec.isLt _)
            (readImmediate_imm_int_ok w false bits rp.types st h_pmd)
            (by
              rw [cast_bv_ofNat_toNat]
              exact cast_intLikeValue_uint rp c w bits st h_src_res)
            rfl
        | true =>
          exact cast_intToInt_some rp c ctx rbody blockIdx stmtIdx
            bodyLocals slots cache amem mem ctrl cm dstId
            (.int w true) dstTy dstSlot _ _
            (bvOfInt 128 (decodeScalar ⟨w, true, bits⟩)).toNat true _
            h_dst_ty h_dst_sl h_dst_c h_src_res h_dst_res h_inv h_il (BitVec.isLt _)
            (readImmediate_imm_int_ok w true bits rp.types st h_pmd)
            (by
              rw [cast_bv_ofNat_toNat, ← bitVec_ofInt_eq]
              exact cast_intLikeValue_sint rp c w bits st h_src_res)
            rfl
      | bool =>
        let ⟨b, h_v⟩ := cast_checkVal_bool_inv h_cv
        subst h_v
        exact cast_intToInt_some rp c ctx rbody blockIdx stmtIdx
            bodyLocals slots cache amem mem ctrl cm dstId
          .bool dstTy dstSlot _ _ (if b then 1 else 0) false _
          h_dst_ty h_dst_sl h_dst_c h_src_res h_dst_res h_inv h_il
          (by cases b <;> decide)
          (readImmediate_imm_bool_ok b rp.types st h_pmd)
          (cast_intLikeValue_bool rp c b st h_src_res) rfl
      | char =>
        let ⟨ch, h_v⟩ := cast_checkVal_char_inv h_cv
        subst h_v
        exact cast_intToInt_some rp c ctx rbody blockIdx stmtIdx
            bodyLocals slots cache amem mem ctrl cm dstId
          .char dstTy dstSlot _ _ ch.toNat false _
          h_dst_ty h_dst_sl h_dst_c h_src_res h_dst_res h_inv h_il
          (Nat.lt_trans ch.val.toBitVec.isLt (by decide))
          (readImmediate_imm_char_ok ch rp.types st h_pmd)
          (cast_intLikeValue_char rp c ch st h_src_res) rfl
      | _ => cases h_il

noncomputable def mirAssignStmtOk (localTys : List MirTy) :
    StatementKind → Bool
  | .assign dst rv =>
    if dst.projection.isEmpty then
      match MirSemantics.getElem? localTys dst.localId with
      | none => true
      | some dstTy =>
        match rv with
        | .use opnd => localOperandMatchesTy localTys opnd dstTy
        | .binaryOp op lhs rhs =>
          let lhsOk : Bool :=
            if binOpLeftHomogeneous op then
              localOperandMatchesTy localTys lhs dstTy
            else
              true
          let rhsOk : Bool :=
            if binOpRightHomogeneous op then
              match operandTy? localTys lhs with
              | none => true
              | some lTy => localOperandMatchesTy localTys rhs lTy
            else
              true
          lhsOk && rhsOk
        | .unaryOp op opnd =>
          if unOpHomogeneous op then
            localOperandMatchesTy localTys opnd dstTy
          else
            true
        | _ => true
    else
      true
  | _ => true

private theorem decodeBody_locals_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body} (h : decodeBody ts rbody = some body) :
    decodeLocalTys ts rbody.locals = some body.locals := by
  dsimp only [decodeBody, optMap2] at h
  cases h_l : decodeLocalTys ts rbody.locals with
  | none => rw [h_l] at h; cases h
  | some locs =>
    cases h_b : mapOption (decodeBasicBlock ts) rbody.basicBlocks with
    | none => rw [h_l, h_b] at h; cases h
    | some _ =>
      rw [h_l, h_b] at h
      injection h with h_eq
      rw [← h_eq]

/-- Complete per-assignment step simulation of
`Miri.Interpreter.evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (refExecCfg
rp) refLimits)` against `Trusted.MirSemantics.evalStatement`'s `.assign` arm. -/
theorem evalRvalueIntoPlace_ref_eq (rp : RefProg) (c : Choice)
    (ctx : SimFrameCtx) (rbody : RefBody) (body : Body)
    (blockIdx : BasicBlockId) (stmtIdx : Nat) (slots : List LocalSlot)
    (cache : List Bool) (amem : MemoryState)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (cm : CallerMemory) (rdst : RefPlace) (dst : Place)
    (rrv : RefRvalue) (rv : Rvalue)
    (h_bdec : decodeBody rp.types rbody = some body)
    (h_c_len : cache.length = body.locals.length)
    (h_assign_ok :
      cache = List.replicate body.locals.length true ∨
      mirAssignStmtOk body.locals (.assign dst rv) = true)
    (h_supp : body.locals.all isSupportedScalarOrUnitTy = true)
    (h_inv : SlotsMatchTys body.locals slots)
    (h_pl : decodePlace rp.types rdst = some dst)
    (h_rv : decodeRvalue rp.types rrv = some rv)
    (h_discr_ty :
      ∀ (src : Place) (srcTy : MirTy) (ety : EnumTy) (dstTy : MirTy),
        rv = .discriminant src →
        dst.projection.isEmpty = true →
        src.projection.isEmpty = true →
        MirSemantics.getElem? body.locals src.localId = some srcTy →
        refAsEnumTy? srcTy = some ety →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        enumAdmitted ety = true →
        dstTy = .int ety.discrWidth ety.discrSigned)
    (h_cast_ty :
      ∀ (opnd : Operand) (castTy dstTy : MirTy),
        rv = .cast .intToInt opnd castTy →
        dst.projection.isEmpty = true →
        MirSemantics.getElem? body.locals dst.localId = some dstTy →
        dstTy = castTy) :
    let st := mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots cache
      mem ctrl cm
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
      ∃ err st', res = .error err st' ∧ stepErrorFaultKind err = some k
    | .ok (slots', _) =>
      res = .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals
        slots' (rvalueCacheTouch dst.localId rv cache) mem ctrl cm) := by
  intro st res
  have h_locs := decodeBody_locals_eq h_bdec
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
      have h_err : res = .error (.stack (.invalidLocal dst.localId (liftLocalsCached rp.types body.locals slots cache).length)) st := by
        dsimp only [res, Miri.Interpreter.evalRvalueIntoPlace, bind, Bind.bind]
        rw [h_rvh_eq, h_tp]
        change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
          c ⟨dst.localId, Array.mk [.Deref]⟩ true) _ st) = _
        rw [eStateM_bind_err (placeDynamic_evalPlace_oob rp c ctx rbody blockIdx
          stmtIdx body.locals slots cache mem ctrl cm ⟨dst.localId, Array.mk [.Deref]⟩
          true (Or.inl h_dty))]
      exact ⟨_, _, h_err, rfl⟩
    | some dstTy =>
      let ⟨dstSlot, h_dsl⟩ := getElem?_some_of_length_eq h_len.symm h_dty
      have h_err : res = .error (.unsupported "projections unsupported on Day 1")
          (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots
            (cacheTouch cache dst.localId) mem ctrl cm) := by
        dsimp only [res, Miri.Interpreter.evalRvalueIntoPlace, bind, Bind.bind]
        rw [h_rvh_eq, h_tp]
        change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
          c ⟨dst.localId, Array.mk [.Deref]⟩ true) _ st) = _
        rw [eStateM_bind_err (placeDynamic_evalPlace_deref_err rp c ctx rbody
          blockIdx stmtIdx body.locals slots cache mem ctrl cm dst.localId
          dstTy dstSlot h_locs h_c_len h_dty h_dsl)]
      exact ⟨_, _, h_err, rfl⟩
  | true =>
    have h_rdpe : rdst.projection.isEmpty = true := h_demp.trans h_dpe
    have h_tp : toMiriPlace rdst = ⟨dst.localId, Array.empty⟩ := by
      dsimp only [toMiriPlace]; rw [h_rdpe, h_did]; rfl
    dsimp only [Bool.not, ite_false_eq]
    cases h_dty : MirSemantics.getElem? body.locals dst.localId with
    | none =>
      have h_err : res = .error (.stack (.invalidLocal dst.localId (liftLocalsCached rp.types body.locals slots cache).length)) st := by
        dsimp only [res, Miri.Interpreter.evalRvalueIntoPlace, bind, Bind.bind]
        rw [h_rvh_eq, h_tp]
        change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
          c ⟨dst.localId, Array.empty⟩ true) _ st) = _
        rw [eStateM_bind_err (placeDynamic_evalPlace_oob rp c ctx rbody blockIdx
          stmtIdx body.locals slots cache mem ctrl cm ⟨dst.localId, Array.empty⟩
          true (Or.inl h_dty))]
      exact ⟨_, _, h_err, rfl⟩
    | some dstTy =>
      let ⟨dstSlot, h_dsl⟩ := getElem?_some_of_length_eq h_len.symm h_dty
      have h_dst_res := h_loc_res dst.localId dstTy h_dty
      have h_dst_supp : isSupportedScalarOrUnitTy dstTy = true :=
        list_all_mirGetElem? (p := isSupportedScalarOrUnitTy) h_supp h_dty
      have h_eval_dst := placeDynamic_evalPlace_local_ok rp c ctx rbody blockIdx
        stmtIdx body.locals slots cache mem ctrl cm dst.localId true dstTy dstSlot
        h_locs h_c_len h_dty h_dsl
      let cache₁ := cacheTouch cache dst.localId
      have h_c1_len : cache₁.length = body.locals.length :=
        (cacheTouch_length cache dst.localId).trans h_c_len
      let ⟨_, h_dst_c0⟩ := getElem?_some_of_length_eq h_c_len.symm h_dty
      have h_dst_c1 : MirSemantics.getElem? cache₁ dst.localId = some true :=
        getElem?_cacheTouch_self h_dst_c0
      let st₁ := mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots
        cache₁ mem ctrl cm
      have h_copy_for_deref_err :
          Miri.Interpreter.evalRvalueIntoPlace
            (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfg rp) refLimits)
            c (.CopyForDeref ⟨0, Array.empty⟩) (toMiriPlace rdst) st =
          .error (.invalidProgram "CopyForDeref in runtime MIR") st₁ := by
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
      | useRetag rop =>
        dsimp only [decodeRvalue, optMap] at h_rv
        cases h_op : decodeOperand rp.types rop with
        | none => rw [h_op] at h_rv; cases h_rv
        | some _ =>
          rw [h_op] at h_rv; injection h_rv with h_eq; subst h_eq
          exact ⟨_, _, h_copy_for_deref_err, rfl⟩
      | aggregateTuple rops =>
        dsimp only [decodeRvalue, optMap] at h_rv
        cases h_ops : mapOption (decodeOperand rp.types) rops with
        | none => rw [h_ops] at h_rv; cases h_rv
        | some _ =>
          rw [h_ops] at h_rv; injection h_rv with h_eq; subst h_eq
          exact ⟨_, _, h_copy_for_deref_err, rfl⟩
      | aggregateArray tyId rops =>
        dsimp only [decodeRvalue, optMap2] at h_rv
        cases h_ty : MirSemantics.getElem? rp.types tyId with
        | none => rw [h_ty] at h_rv; cases h_rv
        | some _ =>
          cases h_ops : mapOption (decodeOperand rp.types) rops with
          | none => rw [h_ty, h_ops] at h_rv; cases h_rv
          | some _ =>
            rw [h_ty, h_ops] at h_rv; injection h_rv with h_eq; subst h_eq
            exact ⟨_, _, h_copy_for_deref_err, rfl⟩
      | repeat_ rop tyId _ =>
        dsimp only [decodeRvalue, optMap2] at h_rv
        cases h_op : decodeOperand rp.types rop with
        | none => rw [h_op] at h_rv; cases h_rv
        | some _ =>
          cases h_ty : MirSemantics.getElem? rp.types tyId with
          | none => rw [h_op, h_ty] at h_rv; cases h_rv
          | some _ =>
            rw [h_op, h_ty] at h_rv; injection h_rv with h_eq; subst h_eq
            exact ⟨_, _, h_copy_for_deref_err, rfl⟩
      | aggregateRangeTo tyId rop =>
        dsimp only [decodeRvalue, optMap2] at h_rv
        cases h_ty : MirSemantics.getElem? rp.types tyId with
        | none => rw [h_ty] at h_rv; cases h_rv
        | some _ =>
          cases h_op : decodeOperand rp.types rop with
          | none => rw [h_ty, h_op] at h_rv; cases h_rv
          | some _ =>
            rw [h_ty, h_op] at h_rv; injection h_rv with h_eq; subst h_eq
            exact ⟨_, _, h_copy_for_deref_err, rfl⟩
      | aggregateRangeFrom tyId rop =>
        dsimp only [decodeRvalue, optMap2] at h_rv
        cases h_ty : MirSemantics.getElem? rp.types tyId with
        | none => rw [h_ty] at h_rv; cases h_rv
        | some _ =>
          cases h_op : decodeOperand rp.types rop with
          | none => rw [h_ty, h_op] at h_rv; cases h_rv
          | some _ =>
            rw [h_ty, h_op] at h_rv; injection h_rv with h_eq; subst h_eq
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
            | unsupported | ptrToPtr | intToPtr | unsize =>
              exact ⟨_, _, h_copy_for_deref_err, rfl⟩
            | intToInt =>
              have h_dst_eq : dstTy = castTy :=
                h_cast_ty opnd castTy dstTy rfl h_dpe h_dty
              subst h_dst_eq
              have h_canon : canonicalTyId rp.types rtid = tyIdFor rp.types dstTy :=
                (canonicalTyId_of_some h_ct).1
              have h_ev := operandMachine_evalOperandAt_eq rp c ctx rbody blockIdx
                stmtIdx body.locals slots cache₁ amem mem ctrl cm
                (Miri.Interpreter.OperandPath.rvalue "operand") rop opnd
                isIntLikeTy none h_locs h_c1_len
                (refConstantAt_eq_of_ne_fn rp c _ (by decide) (fun _ _ _ => rfl))
                h_inv h_op (operandKnownOk_none _ _ _ _)
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
                          ⟨.local ctx.below.size dst.localId none
                              (LocalsIdentity.ofAllocationToken 0),
                            refLocalLayoutForTy rp.types dstTy⟩)
                      st₁ := by
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
                have h_dst_c2 : MirSemantics.getElem? (operandCacheTouch cache₁ opnd)
                    dst.localId = some true :=
                  getElem?_operandCacheTouch_mono h_dst_c1
                have h_c := cast_intToInt_local_eq rp c ctx rbody blockIdx
                  stmtIdx body.locals slots₁ (operandCacheTouch cache₁ opnd)
                  amem₁ mem ctrl cm dst.localId
                  srcTy dstTy optVal dstSlot₁ h_dty h_dsl₁ h_dst_c2
                  h_src_res h_dst_res h_inv₁ h_sm₁
                dsimp only at h_c
                dsimp only [rvalueCacheTouch]
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
          have h_known : operandKnownOk rp.types body.locals cache₁ op
              (some (refLocalLayoutForTy rp.types dstTy)) := by
            cases h_assign_ok with
            | inl h_rep =>
              dsimp only [cache₁]
              rw [h_rep, cacheTouch_replicate_true]
              exact operandKnownOk_of_replicate_true _ _ _ _ _
            | inr h_st =>
              dsimp only [mirAssignStmtOk] at h_st
              rw [h_dpe, ite_true_eq, h_dty] at h_st
              exact operandKnownOk_of_localOperandMatchesTy _ _ _ _ _ h_st
          have h_ev := operandMachine_evalOperandAt_eq rp c ctx rbody blockIdx
            stmtIdx body.locals slots cache₁ amem mem ctrl cm
            (Miri.Interpreter.OperandPath.rvalue "operand") rop op
            (fun srcTy => MirTy.beq srcTy dstTy)
            (some (refLocalLayoutForTy rp.types dstTy)) h_locs h_c1_len
            (refConstantAt_eq_of_ne_fn rp c _ (by decide) (fun _ _ _ => rfl))
            h_inv h_op h_known
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
                        ⟨.local ctx.below.size dst.localId none (LocalsIdentity.ofAllocationToken 0),
                          refLocalLayoutForTy rp.types dstTy⟩ false))
                  st₁ := by
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
            have h_dst_c2 : MirSemantics.getElem? (operandCacheTouch cache₁ op)
                dst.localId = some true :=
              getElem?_operandCacheTouch_mono h_dst_c1
            have h_wr_none :
                Miri.Interpreter.MachineHooks.withRetagMode .None
                  (Miri.Interpreter.copyRuntimePlace
                    (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                    (refExecCfg rp).copy c
                    ⟨.immediate (optValToMiriImm srcTy optVal),
                      refLocalLayoutForTy rp.types srcTy⟩
                    ⟨.local ctx.below.size dst.localId none (LocalsIdentity.ofAllocationToken 0),
                      refLocalLayoutForTy rp.types dstTy⟩ false)
                  (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots₁
                    (operandCacheTouch cache₁ op) mem ctrl cm) =
                Miri.Interpreter.copyRuntimePlace
                  (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                  (refExecCfg rp).copy c
                  ⟨.immediate (optValToMiriImm srcTy optVal),
                    refLocalLayoutForTy rp.types srcTy⟩
                  ⟨.local ctx.below.size dst.localId none (LocalsIdentity.ofAllocationToken 0),
                    refLocalLayoutForTy rp.types dstTy⟩ false
                  (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots₁
                    (operandCacheTouch cache₁ op) mem ctrl cm) := rfl
            rw [h_wr_none]
            have h_cp := copyRuntimePlace_imm_to_local rp c ctx rbody blockIdx
              stmtIdx body.locals slots₁ (operandCacheTouch cache₁ op) amem₁
              mem ctrl cm dst.localId srcTy
              dstTy optVal dstSlot₁ h_dty h_dsl₁ h_dst_c2 h_src_res h_dst_res
              h_dst_supp h_inv₁ h_sm₁
            dsimp only [rvalueCacheTouch]
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
                                            ⟨.local ctx.below.size dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                              refLocalLayoutForTy rp.types dstTy⟩))))))
                    st₁ := by
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
            have h_knownL : operandKnownOk rp.types body.locals cache₁ lhs
                (if (toMiriBinOp op).leftHomogeneous then
                  some (refLocalLayoutForTy rp.types dstTy) else none) := by
              cases h_lh : (toMiriBinOp op).leftHomogeneous with
              | false => exact operandKnownOk_none _ _ _ _
              | true =>
                cases h_assign_ok with
                | inl h_rep =>
                  dsimp only [cache₁]
                  rw [h_rep, cacheTouch_replicate_true]
                  exact operandKnownOk_of_replicate_true _ _ _ _ _
                | inr h_st =>
                  dsimp only [mirAssignStmtOk] at h_st
                  rw [h_dpe, ite_true_eq, h_dty] at h_st
                  dsimp only at h_st
                  have h_st' := ((Bool.and_eq_true _ _).mp h_st).1
                  rw [← toMiriBinOp_leftHomogeneous op, h_lh, ite_true_eq] at h_st'
                  exact operandKnownOk_of_localOperandMatchesTy _ _ _ _ _ h_st'
            have h_evL := evalPrimitiveOperand_ref_eq rp c ctx rbody blockIdx
              stmtIdx body.locals slots cache₁ amem mem ctrl cm
              (Miri.Interpreter.OperandPath.rvalue "left") rlhs lhs
              (if (toMiriBinOp op).leftHomogeneous then
                some (refLocalLayoutForTy rp.types dstTy) else none)
              h_locs h_c1_len
              (refConstantAt_eq_of_ne_fn rp c _ (by decide) (fun _ _ _ => rfl))
              h_inv h_l h_knownL h_loc_res
            cases h_pL : evalPrimitiveOperand body.locals slots amem lhs with
            | error k =>
              rw [h_pL] at h_evL
              let ⟨err, st', h_err, h_fk⟩ := h_evL
              rw [eStateM_bind_err h_err]
              exact ⟨err, st', rfl, h_fk⟩
            | ok tupL =>
              let ⟨lVal, slots₁, amem₁⟩ := tupL
              rw [h_pL] at h_evL
              let ⟨lTy, h_lcv, h_lpr, h_lres, h_l_oty, h_okL⟩ := h_evL
              dsimp only
              rw [eStateM_bind_ok h_okL, ← eStateM_bind_assoc]
              have h_inv₁ := (evalPrimitiveOperand_slotsMatchTys h_inv h_pL).1
              let cache₂ := operandCacheTouch cache₁ lhs
              have h_c2_len : cache₂.length = body.locals.length :=
                (operandCacheTouch_length cache₁ lhs).trans h_c1_len
              have h_knownR : operandKnownOk rp.types body.locals cache₂ rhs
                  (if (toMiriBinOp op).rightHomogeneous then
                    some (refLocalLayoutForTy rp.types lTy) else none) := by
                cases h_rh : (toMiriBinOp op).rightHomogeneous with
                | false => exact operandKnownOk_none _ _ _ _
                | true =>
                  cases h_assign_ok with
                  | inl h_rep =>
                    dsimp only [cache₂, cache₁]
                    rw [h_rep, cacheTouch_replicate_true, operandCacheTouch_replicate_true]
                    exact operandKnownOk_of_replicate_true _ _ _ _ _
                  | inr h_st =>
                    dsimp only [mirAssignStmtOk] at h_st
                    rw [h_dpe, ite_true_eq, h_dty] at h_st
                    dsimp only at h_st
                    have h_st' := ((Bool.and_eq_true _ _).mp h_st).2
                    rw [← toMiriBinOp_rightHomogeneous op, h_rh, ite_true_eq, h_l_oty] at h_st'
                    exact operandKnownOk_of_localOperandMatchesTy _ _ _ _ _ h_st'
              have h_evR := evalPrimitiveOperand_ref_eq rp c ctx rbody blockIdx
                stmtIdx body.locals slots₁ cache₂ amem₁ mem ctrl cm
                (Miri.Interpreter.OperandPath.rvalue "right") rrhs rhs
                (if (toMiriBinOp op).rightHomogeneous then
                  some (refLocalLayoutForTy rp.types lTy) else none)
                h_locs h_c2_len
                (refConstantAt_eq_of_ne_fn rp c _ (by decide) (fun _ _ _ => rfl))
                h_inv₁ h_r h_knownR h_loc_res
              cases h_pR : evalPrimitiveOperand body.locals slots₁ amem₁ rhs with
              | error k =>
                rw [h_pR] at h_evR
                let ⟨err, st', h_err, h_fk⟩ := h_evR
                rw [eStateM_bind_err h_err]
                exact ⟨err, st', rfl, h_fk⟩
              | ok tupR =>
                let ⟨rVal, slots₂, amem₂⟩ := tupR
                rw [h_pR] at h_evR
                let ⟨rTy, h_rcv, h_rpr, _, _, h_okR⟩ := h_evR
                dsimp only
                rw [eStateM_bind_ok h_okR]
                have h_inv₂ := (evalPrimitiveOperand_slotsMatchTys h_inv₁ h_pR).1
                let cache₃ := operandCacheTouch cache₂ rhs
                have h_dst_c3 : MirSemantics.getElem? cache₃ dst.localId = some true :=
                  getElem?_operandCacheTouch_mono (getElem?_operandCacheTouch_mono h_dst_c1)
                have h_bin := scalarOps_binary_ref_eq rp c op lTy rTy lVal rVal
                  (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots₂
                    cache₃ mem ctrl cm) h_lcv h_lpr h_rcv h_rpr h_lres
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
                  exact assertAndWrite_local_eq rp c ctx rbody blockIdx stmtIdx
                    body.locals slots₂ cache₃ amem₂ mem ctrl cm dst.localId resTy
                    dstTy v dstSlot₂ h_dty h_dsl₂ h_dst_c3
                    h_dst_res h_inv₂ h_vcv
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
                                  ⟨.local ctx.below.size dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                    refLocalLayoutForTy rp.types dstTy⟩))))
                  st₁ := by
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
          have h_knownO : operandKnownOk rp.types body.locals cache₁ opnd
              (if (toMiriUnOp op).homogeneous then
                some (refLocalLayoutForTy rp.types dstTy) else none) := by
            cases h_uh : (toMiriUnOp op).homogeneous with
            | false => exact operandKnownOk_none _ _ _ _
            | true =>
              cases h_assign_ok with
              | inl h_rep =>
                dsimp only [cache₁]
                rw [h_rep, cacheTouch_replicate_true]
                exact operandKnownOk_of_replicate_true _ _ _ _ _
              | inr h_st =>
                dsimp only [mirAssignStmtOk] at h_st
                rw [h_dpe, ite_true_eq, h_dty] at h_st
                dsimp only at h_st
                rw [← toMiriUnOp_homogeneous op, h_uh, ite_true_eq] at h_st
                exact operandKnownOk_of_localOperandMatchesTy _ _ _ _ _ h_st
          have h_evO := evalPrimitiveOperand_ref_eq rp c ctx rbody blockIdx
            stmtIdx body.locals slots cache₁ amem mem ctrl cm
            (Miri.Interpreter.OperandPath.rvalue "operand") rop opnd
            (if (toMiriUnOp op).homogeneous then
              some (refLocalLayoutForTy rp.types dstTy) else none)
            h_locs h_c1_len
            (refConstantAt_eq_of_ne_fn rp c _ (by decide) (fun _ _ _ => rfl))
            h_inv h_op h_knownO h_loc_res
          cases h_pO : evalPrimitiveOperand body.locals slots amem opnd with
          | error k =>
            rw [h_pO] at h_evO
            let ⟨err, st', h_err, h_fk⟩ := h_evO
            rw [eStateM_bind_err h_err]
            exact ⟨err, st', rfl, h_fk⟩
          | ok tupO =>
            let ⟨v, slots₁, amem₁⟩ := tupO
            rw [h_pO] at h_evO
            let ⟨vTy, h_vcv, h_vpr, _, _, h_okO⟩ := h_evO
            dsimp only
            rw [eStateM_bind_ok h_okO]
            have h_inv₁ := (evalPrimitiveOperand_slotsMatchTys h_inv h_pO).1
            let cache₂ := operandCacheTouch cache₁ opnd
            have h_dst_c2 : MirSemantics.getElem? cache₂ dst.localId = some true :=
              getElem?_operandCacheTouch_mono h_dst_c1
            have h_un := scalarOps_unary_ref_eq rp c op vTy v
              (mkGenSimState rp ctx rbody blockIdx stmtIdx body.locals slots₁
                cache₂ mem ctrl cm) h_vcv h_vpr
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
              exact assertAndWrite_local_eq rp c ctx rbody blockIdx stmtIdx
                body.locals slots₁ cache₂ amem₁ mem ctrl cm dst.localId resTy dstTy
                u dstSlot₁ h_dty h_dsl₁ h_dst_c2 h_dst_res h_inv₁ h_ucv
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
                              ⟨.local ctx.below.size dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                refLocalLayoutForTy rp.types dstTy⟩)))
                  st₁ := by
            dsimp only [res, toMiriRvalue, Miri.Interpreter.evalRvalueIntoPlace,
              bind, Bind.bind]
            rw [h_rvh_eq, h_tp]
            change (EStateM.bind (Miri.Interpreter.PlaceDynamic.evalPlace
              (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp))
              c ⟨dst.localId, Array.empty⟩ true) _ st) = _
            rw [eStateM_bind_ok h_eval_dst]
            rfl
          rw [h_res_step]
          have h_evS := operandMachine_evalPlaceToOp_eq rp c ctx rbody blockIdx
            stmtIdx body.locals slots cache₁ mem ctrl cm rsrc src none h_locs
            h_c1_len h_sp h_inv (placeKnownOk_none _ _ _ _)
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
              | partialTuple _ =>
                exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_sty h_ssl)
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
                  let cache₂ := cacheTouch cache₁ src.localId
                  have h_dst_c2 : MirSemantics.getElem? cache₂ dst.localId = some true :=
                    getElem?_cacheTouch_mono h_dst_c1
                  let st₂ := mkGenSimState rp ctx rbody blockIdx stmtIdx
                    body.locals slots cache₂ mem ctrl cm
                  have h_src_res := h_loc_res src.localId srcTy h_sty
                  have h_dl_non_enum :
                      ∀ (t : MirTy),
                        refAsEnumTy? t = none →
                        resolveTy rp.types (tyIdFor rp.types t) = some t →
                        Miri.Interpreter.Discriminant.readDiscriminant
                          (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                          ⟨.immediate (optValToMiriImm t srcOpt),
                            refLocalLayoutForTy rp.types t⟩ st₂ =
                          .error (.unsupported "discriminant on non-enum type") st₂ := by
                    intro t h_ne h_tr
                    dsimp only [Miri.Interpreter.Discriminant.readDiscriminant, bind, Bind.bind]
                    change (EStateM.bind
                      ((Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).discriminantLayout
                        c (tyIdFor rp.types t)) _ st₂) = _
                    dsimp only [EStateM.bind]
                    rw [discrHooks_discriminantLayout rp c t st₂ h_tr, h_ne]
                  have h_finish_discr :
                      ∀ (rhs : Except FaultKind (List LocalSlot × MemoryState))
                        {t : MirTy} {ety : EnumTy} {opt : Option Val}
                        {v disc : Nat},
                        EnumLike rp.types t ety →
                        enumAdmitted ety = true →
                        dstTy = .int ety.discrWidth ety.discrSigned →
                        MirSemantics.getElem? ety.discriminants v = some disc →
                        Miri.Interpreter.Discriminant.readDiscriminant
                          (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                          ⟨.immediate (optValToMiriImm t opt),
                            refLocalLayoutForTy rp.types t⟩ st₂ = .ok v st₂ →
                        (truncateBits ety.discrWidth (BitVec.ofNat 128 disc) =
                          BitVec.ofNat 128 disc →
                          rhs = writePlace slots amem dst.localId dstTy
                            (.scalar ⟨ety.discrWidth, ety.discrSigned,
                              BitVec.ofNat 128 disc⟩)) →
                        match rhs with
                        | .error k =>
                          ∃ err st',
                            EStateM.bind
                              (Miri.Interpreter.Discriminant.readDiscriminant
                                (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                                ⟨.immediate (optValToMiriImm t opt),
                                  refLocalLayoutForTy rp.types t⟩)
                              (fun variant =>
                                EStateM.bind
                                  (Miri.Interpreter.Discriminant.discriminantForVariant
                                    (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp))
                                    c (tyIdFor rp.types t) variant)
                                  (fun discr =>
                                    Miri.Interpreter.writePlaceImmediate
                                      (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                                      c discr.imm
                                      ⟨.local ctx.below.size dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                        refLocalLayoutForTy rp.types dstTy⟩)) st₂ =
                              .error err st' ∧ stepErrorFaultKind err = some k
                        | .ok (slots', _) =>
                          EStateM.bind
                            (Miri.Interpreter.Discriminant.readDiscriminant
                              (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                              ⟨.immediate (optValToMiriImm t opt),
                                refLocalLayoutForTy rp.types t⟩)
                            (fun variant =>
                              EStateM.bind
                                (Miri.Interpreter.Discriminant.discriminantForVariant
                                  (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp))
                                  c (tyIdFor rp.types t) variant)
                                (fun discr =>
                                  Miri.Interpreter.writePlaceImmediate
                                    (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfg rp)).place
                                    c discr.imm
                                    ⟨.local ctx.below.size dst.localId none (LocalsIdentity.ofAllocationToken 0),
                                      refLocalLayoutForTy rp.types dstTy⟩)) st₂ =
                            .ok () (mkGenSimState rp ctx rbody blockIdx stmtIdx
                              body.locals slots' cache₂ mem ctrl cm) := by
                    intro rhs t ety opt v disc h_el h_adm h_dst_eq h_dv h_rd h_rhs_fn
                    subst h_dst_eq
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
                    have h_rhs := h_rhs_fn h_trunc_eq
                    subst h_rhs
                    have h_dfv := discrHooks_discriminantForVariant_ok rp c t ety
                      v disc st₂ h_el h_adm h_dv
                    rw [eStateM_bind_ok h_rd]
                    change (match (_ : Except FaultKind (List LocalSlot × MemoryState)) with
                      | Except.error k =>
                        ∃ err st',
                          EStateM.bind
                            (Miri.Interpreter.Discriminant.discriminantForVariant _ c
                              (tyIdFor rp.types t) v) _ st₂ =
                            EStateM.Result.error err st' ∧ _
                      | Except.ok (slots', _) =>
                        EStateM.bind
                          (Miri.Interpreter.Discriminant.discriminantForVariant _ c
                            (tyIdFor rp.types t) v) _ st₂ = _)
                    rw [eStateM_bind_ok h_dfv]
                    have h_cv_d :
                        checkVal (.scalar ⟨ety.discrWidth, ety.discrSigned,
                          BitVec.ofNat 128 disc⟩)
                          (.int ety.discrWidth ety.discrSigned) = true :=
                      checkVal_scalar_of_trunc ety.discrWidth ety.discrSigned _
                        h_trunc_eq
                    have h_aw := assertAndWrite_local_eq rp c ctx rbody blockIdx
                      stmtIdx body.locals slots cache₂ amem mem ctrl cm dst.localId
                      (.int ety.discrWidth ety.discrSigned)
                      (.int ety.discrWidth ety.discrSigned)
                      (.scalar ⟨ety.discrWidth, ety.discrSigned, BitVec.ofNat 128 disc⟩)
                      dstSlot h_dty h_dsl h_dst_c2 h_dst_res h_inv h_cv_d
                    dsimp only at h_aw
                    rw [beq_self_eq_true, ite_true_eq] at h_aw
                    exact h_aw
                  cases srcTy with
                  | bool | int _ _ | unit | never | char | tuple _ | ref _ _
                  | rawPtr _ _ | slice _ | array _ _ | rangeTo _ | rangeFrom _
                  | unsupported =>
                    rw [eStateM_bind_err (h_dl_non_enum _ rfl h_src_res)]
                    exact ⟨_, _, rfl, rfl⟩
                  | ordering =>
                    have h_el : EnumLike rp.types .ordering refOrderingEnumTy :=
                      ⟨rfl, h_src_res⟩
                    have h_dst_eq : dstTy = .int .i8 true :=
                      h_discr_ty src .ordering refOrderingEnumTy dstTy rfl h_dpe
                        h_spe h_sty rfl h_dty mem_refOrderingEnumTy_admitted
                    have h_smS := SlotsMatchTys.getElem? h_inv h_sty h_ssl
                    dsimp only [evalOrderingDiscriminantOfVal]
                    cases srcOpt with
                    | none =>
                      dsimp only [optValToMiriImm]
                      let ⟨_, h_ub⟩ := discrHooks_readDiscriminant_scalar_uninit_ub
                        rp c .ordering refOrderingEnumTy .i8 true st₂ h_el rfl
                        mem_refOrderingEnumTy_admitted rfl
                      rw [eStateM_bind_err h_ub]
                      exact ⟨_, _, rfl, rfl⟩
                    | some sv =>
                      let ⟨ord, h_sv_eq⟩ := checkVal_ordering_inv h_smS
                      subst h_sv_eq
                      have h_imm_eq :
                          optValToMiriImm .ordering (some (.ordering ord)) =
                            .scalar (.fromScalarInt
                              (miriScalar .i8 (BitVec.ofNat 128 (orderingTagBits ord)))) :=
                        valToMiriImmediate_scalar_enumLike rfl
                          (orderingVariant_enumVariantOfVal ord) rfl
                          (orderingVariant_getElem? ord)
                      have h_rd :
                          Miri.Interpreter.Discriminant.readDiscriminant
                            (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                            ⟨.immediate (optValToMiriImm .ordering (some (.ordering ord))),
                              refLocalLayoutForTy rp.types .ordering⟩ st₂ =
                            .ok (orderingVariantIdx ord) st₂ := by
                        rw [h_imm_eq]
                        exact discrHooks_readDiscriminant_scalar_ok rp c .ordering
                          refOrderingEnumTy .i8 true (orderingVariantIdx ord)
                          (orderingTagBits ord) st₂ h_el rfl
                          mem_refOrderingEnumTy_admitted
                          (orderingVariant_getElem? ord) rfl
                      exact h_finish_discr _ h_el mem_refOrderingEnumTy_admitted
                        h_dst_eq (orderingVariant_getElem? ord) h_rd
                        (fun _ => rfl)
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
                              refLocalLayoutForTy rp.types (.enum ety)⟩ st₂ =
                            .error (.unsupported "unadmitted enum in discriminantLayout") st₂ := by
                        dsimp only [Miri.Interpreter.Discriminant.readDiscriminant,
                          bind, Bind.bind]
                        change (EStateM.bind
                          ((Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).discriminantLayout
                            c (tyIdFor rp.types (.enum ety))) _ st₂) = _
                        dsimp only [EStateM.bind]
                        rw [discrHooks_discriminantLayout rp c (.enum ety) st₂ h_src_res]
                        dsimp only [refAsEnumTy?]; rw [h_ref_adm]; rfl
                      rw [eStateM_bind_err h_dl_err]
                      exact ⟨_, _, rfl, rfl⟩
                    | true =>
                      have h_el : EnumLike rp.types (.enum ety) ety :=
                        ⟨rfl, h_src_res⟩
                      have h_dst_eq : dstTy = .int ety.discrWidth ety.discrSigned :=
                        h_discr_ty src (.enum ety) ety dstTy rfl h_dpe h_spe h_sty
                          rfl h_dty h_adm
                      have h_smS := SlotsMatchTys.getElem? h_inv h_sty h_ssl
                      have h_ref_adm : refEnumAdmitted ety = true := by
                        rw [refEnumAdmitted_eq]; exact h_adm
                      dsimp only [Bool.not, ite_false_eq]
                      cases h_tr : ety.tagRepr with
                      | zeroSized =>
                        have h_zst_rd :
                            ∀ (opt : Option Val),
                              Miri.Interpreter.Discriminant.readDiscriminant
                                (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                                ⟨.immediate (optValToMiriImm (.enum ety) opt),
                                  refLocalLayoutForTy rp.types (.enum ety)⟩ st₂ =
                                .ok 0 st₂ := by
                          intro opt
                          dsimp only [Miri.Interpreter.Discriminant.readDiscriminant, bind, Bind.bind]
                          have h_dl := discrHooks_discriminantLayout_enumLike rp c
                            st₂ h_el h_adm
                          change (EStateM.bind
                            ((Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)).discriminantLayout
                              c (tyIdFor rp.types (.enum ety))) _ st₂) = _
                          rw [eStateM_bind_ok h_dl]
                          have h_vars : (refLocalLayoutForTy rp.types (.enum ety)).layout.variants = .Single 0 := by
                            dsimp only [refLocalLayoutForTy, refLayoutDataForTy,
                              refAsEnumTy?, refEnumLayoutData]
                            rw [h_tr]; rfl
                          have h_uninh : (refLocalLayoutForTy rp.types (.enum ety)).layout.isUninhabited = false := by
                            dsimp only [refLocalLayoutForTy, refLayoutDataForTy,
                              refAsEnumTy?, refEnumLayoutData]
                            rw [h_tr]; rfl
                          rw [h_vars, h_uninh]; rfl
                        let ⟨_, _, h_tag_len⟩ := enumAdmitted_parts h_adm
                        rw [h_tr] at h_tag_len
                        have h_len1 : ety.discriminants.length = 1 :=
                          Nat.eq_of_beq_eq_true h_tag_len
                        let ⟨disc, h_d0⟩ := mirGetElem?_some_of_lt
                          (xs := ety.discriminants) (i := 0) (by rw [h_len1]; exact Nat.zero_lt_one)
                        cases srcOpt with
                        | none =>
                          exact h_finish_discr _ h_el h_adm h_dst_eq h_d0
                            (h_zst_rd none) (fun h_trunc_eq => by
                              dsimp only
                              rw [h_d0]
                              dsimp only
                              rw [h_trunc_eq])
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
                          exact h_finish_discr _ h_el h_adm h_dst_eq h_d0
                            (h_zst_rd _) (fun h_trunc_eq => by
                              dsimp only
                              rw [EnumTy.beq_refl, h_d0]
                              dsimp only
                              rw [h_trunc_eq]
                              rfl)
                      | scalar tagW tagS =>
                        cases srcOpt with
                        | none =>
                          dsimp only [optValToMiriImm]
                          let ⟨msg, h_ub⟩ := discrHooks_readDiscriminant_scalar_uninit_ub
                            rp c (.enum ety) ety tagW tagS st₂ h_el h_tr h_adm rfl
                          rw [eStateM_bind_err h_ub]
                          exact ⟨_, _, rfl, rfl⟩
                        | some sv =>
                          let ⟨v, h_sv_eq, _, h_v_lt⟩ := checkVal_enum_inv h_smS
                          subst h_sv_eq
                          let ⟨disc, h_dv⟩ := mirGetElem?_some_of_lt h_v_lt
                          have h_imm_eq :
                              optValToMiriImm (.enum ety) (some (.enumVal ety v)) =
                                .scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))) :=
                            valToMiriImmediate_scalar_enumLike (ty := .enum ety)
                              (v := .enumVal ety v) rfl rfl h_tr h_dv
                          have h_rd :
                              Miri.Interpreter.Discriminant.readDiscriminant
                                (Miri.Interpreter.ExecutionMachine.discriminantHooks (refExecCfg rp)) c
                                ⟨.immediate (optValToMiriImm (.enum ety) (some (.enumVal ety v))),
                                  refLocalLayoutForTy rp.types (.enum ety)⟩ st₂ =
                                .ok v st₂ := by
                            rw [h_imm_eq]
                            exact discrHooks_readDiscriminant_scalar_ok rp c
                              (.enum ety) ety tagW tagS v disc st₂ h_el h_tr h_adm
                              h_dv rfl
                          exact h_finish_discr _ h_el h_adm h_dst_eq h_dv h_rd
                            (fun h_trunc_eq => by
                              dsimp only
                              rw [EnumTy.beq_refl, Nat.blt_eq.mpr h_v_lt,
                                Bool.and_self, ite_true_eq, h_dv]
                              dsimp only
                              rw [h_trunc_eq])

end Anneal.MirCorrespondence
