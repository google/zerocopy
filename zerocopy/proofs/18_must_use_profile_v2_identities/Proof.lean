-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.SimpLemmas
import Init.Data.List.Basic
import Init.RCases
import Expected
import Anneal.MirWp.V2StepShield

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Shared Plumbing -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  nomatch h

/-- An exact-outcome execution yields well-formedness and `returnsExactly`. -/
private theorem returnsExactly_of_exec {defId : DefId} {q : Query}
    {fuel : Nat} {out : TerminalOut}
    (hExec : execProgV2 (entryProgForBody Captured.program defId) fuel q
      (fun o => o = out)) :
    WellFormedV2 (entryProgForBody Captured.program defId) q ∧
    Spec.returnsExactly Captured.program defId q out := by
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  exact ⟨hRes.1, hRes.2.1, hRes.2.2.2 _ rfl⟩

/-- Evaluate `Rvalue.use (.move ⟨lid, []⟩)` on an immediate local. -/
private theorem evalRvalueV2_use_move_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState} {ty : MirTy}
    {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) =
      some locals') :
    evalRvalueV2 bodyLocals locals mem ty (.use (.move ⟨lid, []⟩)) =
      .ok (v, locals', mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_move_local hTy hSlot hSup hSet]
  dsimp only
  rw [mirTy_beq_refl ty]
  rfl

/-- Evaluate `Rvalue.useRetag (.move ⟨lid, []⟩)` on a reference-valid
immediate local. -/
private theorem evalRvalueV2_useRetag_move_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState} {ty : MirTy}
    {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) =
      some locals')
    (hRV : refsValidInMem mem ty v = true) :
    evalRvalueV2 bodyLocals locals mem ty (.useRetag (.move ⟨lid, []⟩)) =
      .ok (v, locals', mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_move_local hTy hSlot hSup hSet]
  dsimp only
  rw [mirTy_beq_refl ty, hRV]
  rfl

/-- A boolean reference-validity check yields the underlying
`refValidInMem` success. -/
private theorem refValid_of_refsValid {m : MemoryState} {reqMut : Mutability}
    {pt : MirTy} {v : Val}
    (h : refsValidInMem m (.ref reqMut pt) v = true) :
    refValidInMem m reqMut pt v = .ok () := by
  unfold refsValidInMem at h
  revert h
  cases hR : refValidInMem m reqMut pt v with
  | ok u => intro _; cases u; rfl
  | error k => intro h; exact False.elim (boolFalseNeTrue h)

/-- A valid reference argument stays in caller memory. -/
private theorem refStay {cm : CallerMemory} {reqMut : Mutability}
    {pt : MirTy} {v : Val}
    (h : refsValidInMem (entryMemoryWithCaller cm) (.ref reqMut pt) v =
      true) :
    refsStayInCallerMem cm (.ref reqMut pt) v = true :=
  refsStayInCallerMem_of_refValid (refValid_of_refsValid h)

/-! ## Identity Bodies (`_0 = move _1; return`) -/

/-- A one-parameter body of parameter type `t` without raw pointers, which
steps from its entry frame `[r0, v]` by moving `_1` into `_0` and then
returns `_0`, returns its argument with caller memory unchanged on every
valid entry. -/
private theorem identity_body_exec {defId : DefId} {body : Body}
    {t : MirTy} {r0 : LocalSlot}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hNoRaw : tyListHasRawPtrV2 [t] = false)
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [r0, .immediate (some v)])
    (hStep1 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      checkValV2 v t = true → refsValidInMem m t v = true →
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0 [r0, .immediate (some v)]) cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some v), liveUninitSlot t]) cm m))
    (hStep2 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      refsStayInCallerMem cm t v = true → refsValidInMem m t v = true →
      spansPairwiseDisjoint (refAccessSpans t v) = true →
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some v), liveUninitSlot t]) cm m) =
      .done (.returned ⟨v, extractReturnMemoryV2 cm m
        [.immediate (some v), liveUninitSlot t]⟩))
    (hStay : ∀ (cm : CallerMemory) (v : Val), checkValV2 v t = true →
      refsValidInMem (entryMemoryWithCaller cm) t v = true →
      refsStayInCallerMem cm t v = true)
    (q : Query) (hValid : ValidEntryArgsV2 body q) :
    ∃ v : Val, q.args = [v] ∧
      execProgV2 (entryProgForBody Captured.program defId) 2 q
        (fun o => o = .returned ⟨v, q.callerMem⟩) := by
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  have hMatch : checkArgsMatchV2 q.args [t] = true := by
    have h : checkArgsMatchV2 q.args
        ((body.locals.drop 1).take body.argumentCount) = true := hValid.2.1
    rw [hParams] at h
    exact h
  let ⟨v, hArgs, hCheck⟩ := checkArgsMatchV2_singleton_inv hMatch
  have hRV : refsValidInMem (entryMemoryWithCaller q.callerMem) t v = true := by
    have h : refsValidInMemList (entryMemoryWithCaller q.callerMem)
        ((body.locals.drop 1).take body.argumentCount) q.args = true :=
      hValid.2.2.1
    rw [hParams, hArgs] at h
    unfold refsValidInMemList refsValidInMemList at h
    revert h
    cases refsValidInMem (entryMemoryWithCaller q.callerMem) t v with
    | true => intro _; rfl
    | false => intro h; exact False.elim (boolFalseNeTrue h)
  have hDisj : spansPairwiseDisjoint (refAccessSpans t v) = true := by
    have h : spansPairwiseDisjoint (refAccessSpansList
        ((body.locals.drop 1).take body.argumentCount) q.args) = true :=
      hValid.2.2.2
    rw [hParams, hArgs] at h
    unfold refAccessSpansList refAccessSpansList at h
    rw [List.append_nil] at h
    exact h
  have hMem : entryMemoryForArgsV2 q.callerMem
      ((body.locals.drop 1).take body.argumentCount) [v] =
      entryMemoryWithCaller q.callerMem := by
    rw [hParams]
    unfold entryMemoryForArgsV2
    rw [hNoRaw]
    rfl
  let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
  have hInitState :
      initStateV2 (entryProgForBody Captured.program defId) q =
      .ok (stateV2 (frameV2 defId 0 0 [r0, .immediate (some v)])
        q.callerMem (entryMemoryWithCaller q.callerMem)) := by
    have h := ctx.initStateV2_ok_frameV2_forArgs hBody hAdm hValid
    rw [hArgs, hInit, hMem] at h
    exact h
  refine ⟨v, hArgs, ?_⟩
  unfold execProgV2
  rw [hInitState]
  apply execOutcomeStateV2_step (hStep1 v _ _ hCheck hRV)
  exact execOutcomeStateV2_done
    (hStep2 v _ _ (hStay q.callerMem v hCheck hRV) hRV hDisj)
    (by rw [extractReturnMemoryV2_entryMemory,
      extractCallerMemory_entry q.callerMem hCM])

/-- `identity_body_exec` packaged as `BodyVerifiedV2` plus
`identityBodyPost`. -/
private theorem identity_body_verified {defId : DefId} {body : Body}
    {t : MirTy} {r0 : LocalSlot} {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hNoRaw : tyListHasRawPtrV2 [t] = false)
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [r0, .immediate (some v)])
    (hStep1 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      checkValV2 v t = true → refsValidInMem m t v = true →
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0 [r0, .immediate (some v)]) cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some v), liveUninitSlot t]) cm m))
    (hStep2 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      refsStayInCallerMem cm t v = true → refsValidInMem m t v = true →
      spansPairwiseDisjoint (refAccessSpans t v) = true →
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some v), liveUninitSlot t]) cm m) =
      .done (.returned ⟨v, extractReturnMemoryV2 cm m
        [.immediate (some v), liveUninitSlot t]⟩))
    (hStay : ∀ (cm : CallerMemory) (v : Val), checkValV2 v t = true →
      refsValidInMem (entryMemoryWithCaller cm) t v = true →
      refsStayInCallerMem cm t v = true) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.identityBodyPost Captured.program defId identity := by
  have hExec := identity_body_exec hBody hAdm hParams hNoRaw hInit hStep1
    hStep2 hStay
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    let ⟨_, _, hE⟩ := hExec q hValid
    (returnsExactly_of_exec hE).1⟩, ?_⟩
  unfold Spec.identityBodyPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    let ⟨v, hArgs, hE⟩ := hExec q hValid
    ⟨v, hArgs, (returnsExactly_of_exec hE).2⟩⟩

/-! ## Per-Body Proofs -/

/-- Body 0: `must_use::<&[u8; 4]>`. -/
private theorem body0_verified :
    BodyVerifiedV2 Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.identityBodyPost Captured.program 0
      (Spec.mustUseId "&[u8; 4]") :=
  identity_body_verified (t := (.ref .shared (.array (.int .i8 false) 4)))
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC hR => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_useRetag_move_ok rfl rfl rfl rfl hR)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ _ _ hR => refStay hR)

/-- Body 1: `must_use::<&[u8]>`. -/
private theorem body1_verified :
    BodyVerifiedV2 Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.identityBodyPost Captured.program 1
      (Spec.mustUseId "&[u8]") :=
  identity_body_verified (t := (.ref .shared (.slice (.int .i8 false))))
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC hR => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_useRetag_move_ok rfl rfl rfl rfl hR)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ _ _ hR => refStay hR)

/-- Body 2: `must_use::<&mut u8>`. -/
private theorem body2_verified :
    BodyVerifiedV2 Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.identityBodyPost Captured.program 2
      (Spec.mustUseId "&mut u8") :=
  identity_body_verified (t := (.ref .mut (.int .i8 false)))
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC hR => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_useRetag_move_ok rfl rfl rfl rfl hR)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ _ _ hR => refStay hR)

/-- Body 3: `must_use::<&str>`. -/
private theorem body3_verified :
    BodyVerifiedV2 Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.identityBodyPost Captured.program 3
      (Spec.mustUseId "&str") :=
  identity_body_verified (t := (.ref .shared .str))
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC hR => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_useRetag_move_ok rfl rfl rfl rfl hR)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ _ _ hR => refStay hR)

/-- Body 4: `must_use::<&u8>`. -/
private theorem body4_verified :
    BodyVerifiedV2 Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.identityBodyPost Captured.program 4
      (Spec.mustUseId "&u8") :=
  identity_body_verified (t := (.ref .shared (.int .i8 false)))
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC hR => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_useRetag_move_ok rfl rfl rfl rfl hR)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ _ _ hR => refStay hR)

/-- Body 5: `must_use::<()>`. -/
private theorem body5_verified :
    BodyVerifiedV2 Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.identityBodyPost Captured.program 5
      (Spec.mustUseId "()") :=
  identity_body_verified (t := .unit)
    (r0 := .immediate (some .unit))
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC _ => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_move_ok rfl rfl rfl rfl)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ v hC _ => by
      cases v with
      | unit => rfl
      | optionVal o =>
        cases o with
        | none => exact False.elim (boolFalseNeTrue hC)
        | some _ => exact False.elim (boolFalseNeTrue hC)
      | boxPtr _ len =>
        cases len <;> exact False.elim (boolFalseNeTrue hC)
      | _ => exact False.elim (boolFalseNeTrue hC))

/-- Body 6: `must_use::<char>`. -/
private theorem body6_verified :
    BodyVerifiedV2 Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.identityBodyPost Captured.program 6
      (Spec.mustUseId "char") :=
  identity_body_verified (t := .char)
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC _ => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_move_ok rfl rfl rfl rfl)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ v hC _ => by
      cases v with
      | char _ => rfl
      | optionVal o =>
        cases o with
        | none => exact False.elim (boolFalseNeTrue hC)
        | some _ => exact False.elim (boolFalseNeTrue hC)
      | boxPtr _ len =>
        cases len <;> exact False.elim (boolFalseNeTrue hC)
      | _ => exact False.elim (boolFalseNeTrue hC))

/-- Body 7: `must_use::<core::cmp::Ordering>`. -/
private theorem body7_verified :
    BodyVerifiedV2 Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.identityBodyPost Captured.program 7
      (Spec.mustUseId "core::cmp::Ordering") :=
  identity_body_verified (t := .ordering)
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC _ => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_move_ok rfl rfl rfl rfl)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ v hC _ => by
      cases v with
      | ordering _ => rfl
      | optionVal o =>
        cases o with
        | none => exact False.elim (boolFalseNeTrue hC)
        | some _ => exact False.elim (boolFalseNeTrue hC)
      | boxPtr _ len =>
        cases len <;> exact False.elim (boolFalseNeTrue hC)
      | _ => exact False.elim (boolFalseNeTrue hC))

/-- Body 8: `must_use::<core::ops::range::Range<usize>>`. -/
private theorem body8_verified :
    BodyVerifiedV2 Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.identityBodyPost Captured.program 8
      (Spec.mustUseId "core::ops::range::Range<usize>") :=
  identity_body_verified (t := (.range (.int .isize false)))
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC _ => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_move_ok rfl rfl rfl rfl)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ v hC _ => by
      cases v with
      | range _ _ => rfl
      | optionVal o =>
        cases o with
        | none => exact False.elim (boolFalseNeTrue hC)
        | some _ => exact False.elim (boolFalseNeTrue hC)
      | boxPtr _ len =>
        cases len <;> exact False.elim (boolFalseNeTrue hC)
      | _ => exact False.elim (boolFalseNeTrue hC))

/-- Body 9: `must_use::<core::option::Option<u32>>`. -/
private theorem body9_verified :
    BodyVerifiedV2 Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.identityBodyPost Captured.program 9
      (Spec.mustUseId "core::option::Option<u32>") :=
  identity_body_verified (t := (.option (.int .i32 false)))
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC _ => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_move_ok rfl rfl rfl rfl)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ v hC _ => by
      cases v with
      | optionVal o =>
        cases o with
        | none => rfl
        | some w =>
          cases w with
          | scalar _ => rfl
          | optionVal o =>
            cases o with
            | none => exact False.elim (boolFalseNeTrue hC)
            | some _ => exact False.elim (boolFalseNeTrue hC)
          | boxPtr _ len =>
            cases len <;> exact False.elim (boolFalseNeTrue hC)
          | _ => exact False.elim (boolFalseNeTrue hC)
      | boxPtr _ len =>
        cases len <;> exact False.elim (boolFalseNeTrue hC)
      | _ => exact False.elim (boolFalseNeTrue hC))

/-- Body 10: `must_use::<i8>`. -/
private theorem body10_verified :
    BodyVerifiedV2 Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.identityBodyPost Captured.program 10
      (Spec.mustUseId "i8") :=
  identity_body_verified (t := (.int .i8 true))
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC _ => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_move_ok rfl rfl rfl rfl)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ v hC _ => by
      cases v with
      | scalar _ => rfl
      | optionVal o =>
        cases o with
        | none => exact False.elim (boolFalseNeTrue hC)
        | some _ => exact False.elim (boolFalseNeTrue hC)
      | boxPtr _ len =>
        cases len <;> exact False.elim (boolFalseNeTrue hC)
      | _ => exact False.elim (boolFalseNeTrue hC))

/-- Body 11: `must_use::<u64>`. -/
private theorem body11_verified :
    BodyVerifiedV2 Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.identityBodyPost Captured.program 11
      (Spec.mustUseId "u64") :=
  identity_body_verified (t := (.int .i64 false))
    (r0 := .immediate none)
    rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ _ hC _ => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_move_ok rfl rfl rfl rfl)
      (writePlaceDestV2_immediate_ok hC rfl rfl))
    (fun _ _ _ hS hR hD => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl
      rfl hS hR hD)
    (fun _ v hC _ => by
      cases v with
      | scalar _ => rfl
      | optionVal o =>
        cases o with
        | none => exact False.elim (boolFalseNeTrue hC)
        | some _ => exact False.elim (boolFalseNeTrue hC)
      | boxPtr _ len =>
        cases len <;> exact False.elim (boolFalseNeTrue hC)
      | _ => exact False.elim (boolFalseNeTrue hC))

/-! ## Top-Level Claim -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    match defId, hBody with
    | 0, h =>
      cases (h : some Captured.body_0 = some body); exact body0_verified.1
    | 1, h =>
      cases (h : some Captured.body_1 = some body); exact body1_verified.1
    | 2, h =>
      cases (h : some Captured.body_2 = some body); exact body2_verified.1
    | 3, h =>
      cases (h : some Captured.body_3 = some body); exact body3_verified.1
    | 4, h =>
      cases (h : some Captured.body_4 = some body); exact body4_verified.1
    | 5, h =>
      cases (h : some Captured.body_5 = some body); exact body5_verified.1
    | 6, h =>
      cases (h : some Captured.body_6 = some body); exact body6_verified.1
    | 7, h =>
      cases (h : some Captured.body_7 = some body); exact body7_verified.1
    | 8, h =>
      cases (h : some Captured.body_8 = some body); exact body8_verified.1
    | 9, h =>
      cases (h : some Captured.body_9 = some body); exact body9_verified.1
    | 10, h =>
      cases (h : some Captured.body_10 = some body); exact body10_verified.1
    | 11, h =>
      cases (h : some Captured.body_11 = some body); exact body11_verified.1
    | n + 12, h => nomatch (h : (none : Option Body) = some body)
  · exact ⟨body0_verified.2, body1_verified.2, body2_verified.2,
      body3_verified.2, body4_verified.2, body5_verified.2, body6_verified.2,
      body7_verified.2, body8_verified.2, body9_verified.2, body10_verified.2,
      body11_verified.2, trivial⟩

end Proof
