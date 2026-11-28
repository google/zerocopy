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

/-- An exact-outcome execution yields well-formedness and `returnsExactly`. -/
private theorem returnsExactly_of_exec {defId : DefId} {q : Query}
    {fuel : Nat} {out : TerminalOut}
    (hExec : execProgV2 (entryProgForBody Captured.program defId) fuel q
      (fun o => o = out)) :
    WellFormedV2 (entryProgForBody Captured.program defId) q ∧
    Spec.returnsExactly Captured.program defId q out := by
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  exact ⟨hRes.1, hRes.2.1, hRes.2.2.2 _ rfl⟩

/-- A valid entry of a one-parameter body passes exactly one argument. -/
private theorem single_arg_of_valid {body : Body} {q : Query} {t : MirTy}
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hValid : ValidEntryArgsV2 body q) :
    ∃ v : Val, q.args = [v] := by
  have hMatch : checkArgsMatchV2 q.args [t] = true := by
    have h : checkArgsMatchV2 q.args
        ((body.locals.drop 1).take body.argumentCount) = true := hValid.2.1
    rw [hParams] at h
    exact h
  let ⟨v, hArgs, _⟩ := checkArgsMatchV2_singleton_inv hMatch
  exact ⟨v, hArgs⟩

/-- Returning from an entry state built by `entryMemoryForArgsV2` without
touching memory hands the caller its memory back unchanged. The raw-pointer
`AllocId` bound that `entryMemoryForArgsV2` adds changes only `nextAllocId`,
so its allocations are the caller's, as in `extractCallerMemory_entry`. -/
private theorem extractCallerMemory_forArgs (cm : CallerMemory)
    (paramTys : List MirTy) (args : List Val)
    (hValid : validCallerMemory cm = true) :
    extractCallerMemory cm (entryMemoryForArgsV2 cm paramTys args) = cm := by
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    have hAllocs :
        (entryMemoryForArgsV2 ⟨allocs⟩ paramTys args).allocations = allocs :=
      entryMemoryForArgsV2_allocations_eq ⟨allocs⟩ paramTys args
    have hEq := extractCallerAllocations_suffix
      (entryMemoryForArgsV2 ⟨allocs⟩ paramTys args) [] allocs hAllocs
      (by
        rw [hAllocs]
        exact findAllocation_in_allocIdsValid [] allocs []
          (fun _ hz => by cases hz) (fun _ hz => by cases hz) hValid)
    rw [hEq]

private theorem natNotElem_false_of_mem {x : Nat} {xs : List Nat}
    (h : x ∈ xs) : natNotElem x xs = false := by
  induction h with
  | head _ =>
    unfold natNotElem
    rw [Nat.beq_refl]
    rfl
  | tail _ _ ih =>
    unfold natNotElem
    rw [ih, Bool.and_false]

private theorem mem_allocIdsOf {a : Allocation} {l : List Allocation}
    (h : a ∈ l) : a.allocId ∈ allocIdsOf l := by
  induction h with
  | head _ => unfold allocIdsOf; exact .head _
  | tail _ _ ih => unfold allocIdsOf; exact .tail _ ih

/-- No allocation whose id the caller already owns is a callee allocation. -/
private theorem calleeLive_nil_of_sub {ids f : List AllocId} :
    ∀ {l : List Allocation}, (∀ a, a ∈ l → a.allocId ∈ ids) →
      calleeLiveAllocations ids f l = []
  | [], _ => rfl
  | a :: _, h => by
    unfold calleeLiveAllocations
    rw [natNotElem_false_of_mem (h a (.head _)), Bool.and_false,
      Bool.false_and]
    exact calleeLive_nil_of_sub (fun b hb => h b (.tail _ hb))

/-- A return from the unchanged entry memory creates no callee heap buffer, so
`extractReturnMemoryV2` hands the caller its memory back unchanged. -/
private theorem extractReturnMemoryV2_forArgs (cm : CallerMemory)
    (paramTys : List MirTy) (args : List Val) (locals : List LocalSlot)
    (hValid : validCallerMemory cm = true) :
    extractReturnMemoryV2 cm (entryMemoryForArgsV2 cm paramTys args) locals =
      cm := by
  unfold extractReturnMemoryV2
  rw [calleeLive_nil_of_sub (fun a ha => by
      rw [entryMemoryForArgsV2_allocations_eq] at ha
      exact mem_allocIdsOf ha),
    List.append_nil, extractCallerMemory_forArgs cm paramTys args hValid]

/-! ## Unit-Returning Bodies (`_0 = const (); return`) -/

/-- A one-parameter body whose return local starts as `()` and which steps by
`_0 = const ()` and then `return` returns `()` with caller memory unchanged on
every valid entry. -/
private theorem unit_body_exec {defId : DefId} {body : Body} {t : MirTy}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate (some .unit), .immediate (some v)])
    (hStep1 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some .unit), .immediate (some v)]) cm m))
    (hStep2 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .done (.returned ⟨.unit, extractReturnMemoryV2 cm m
        [.immediate (some .unit), .immediate (some v)]⟩))
    (q : Query) (hValid : ValidEntryArgsV2 body q) :
    execProgV2 (entryProgForBody Captured.program defId) 2 q
      (fun o => o = .returned ⟨.unit, q.callerMem⟩) := by
  let ⟨v, hArgs⟩ := single_arg_of_valid hParams hValid
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
  have hInitState :
      initStateV2 (entryProgForBody Captured.program defId) q =
      .ok (stateV2 (frameV2 defId 0 0
        [.immediate (some .unit), .immediate (some v)])
        q.callerMem (entryMemoryForArgsV2 q.callerMem
          ((body.locals.drop 1).take body.argumentCount) [v])) := by
    have h := ctx.initStateV2_ok_frameV2_forArgs hBody hAdm hValid
    rw [hArgs, hInit] at h
    exact h
  unfold execProgV2
  rw [hInitState]
  apply execOutcomeStateV2_step (hStep1 v _ _)
  exact execOutcomeStateV2_done (hStep2 v _ _)
    (by rw [extractReturnMemoryV2_forArgs q.callerMem _ _ _ hCM])

/-- `unit_body_exec` packaged as `BodyVerifiedV2` plus `unitBodyPost`. -/
private theorem unit_body_verified {defId : DefId} {body : Body} {t : MirTy}
    {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate (some .unit), .immediate (some v)])
    (hStep1 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some .unit), .immediate (some v)]) cm m))
    (hStep2 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .done (.returned ⟨.unit, extractReturnMemoryV2 cm m
        [.immediate (some .unit), .immediate (some v)]⟩)) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.unitBodyPost Captured.program defId identity := by
  have hExec := unit_body_exec hBody hAdm hParams hInit hStep1 hStep2
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    (returnsExactly_of_exec (hExec q hValid)).1⟩, ?_⟩
  unfold Spec.unitBodyPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    (returnsExactly_of_exec (hExec q hValid)).2⟩

/-! ## Zero-Parameter Unit-Returning Bodies -/

/-- A valid entry of a zero-parameter body passes no arguments. -/
private theorem nil_args_of_valid {body : Body} {q : Query}
    (hParams : (body.locals.drop 1).take body.argumentCount = [])
    (hValid : ValidEntryArgsV2 body q) :
    q.args = [] := by
  have h : checkArgsMatchV2 q.args
      ((body.locals.drop 1).take body.argumentCount) = true := hValid.2.1
  rw [hParams] at h
  revert h
  cases q.args with
  | nil => intro _; rfl
  | cons _ _ => intro h; nomatch h

/-- A zero-parameter body whose return local starts as `()` and which steps
by `_0 = const ()` and then `return` returns `()` with caller memory unchanged
on every valid entry. -/
private theorem zero_body_exec {defId : DefId} {body : Body}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hParams : (body.locals.drop 1).take body.argumentCount = [])
    (hInit : initLocalsLoop body [] 0 body.locals =
      [.immediate (some .unit)])
    (hStep1 : ∀ (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0 [.immediate (some .unit)]) cm m) =
      .step (stateV2 (frameV2 defId 0 1 [.immediate (some .unit)]) cm m))
    (hStep2 : ∀ (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1 [.immediate (some .unit)]) cm m) =
      .done (.returned ⟨.unit, extractReturnMemoryV2 cm m
        [.immediate (some .unit)]⟩))
    (q : Query) (hValid : ValidEntryArgsV2 body q) :
    execProgV2 (entryProgForBody Captured.program defId) 2 q
      (fun o => o = .returned ⟨.unit, q.callerMem⟩) := by
  have hArgs := nil_args_of_valid hParams hValid
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
  have hInitState :
      initStateV2 (entryProgForBody Captured.program defId) q =
      .ok (stateV2 (frameV2 defId 0 0 [.immediate (some .unit)])
        q.callerMem (entryMemoryForArgsV2 q.callerMem
          ((body.locals.drop 1).take body.argumentCount) [])) := by
    have h := ctx.initStateV2_ok_frameV2_forArgs hBody hAdm hValid
    rw [hArgs, hInit] at h
    exact h
  unfold execProgV2
  rw [hInitState]
  apply execOutcomeStateV2_step (hStep1 _ _)
  exact execOutcomeStateV2_done (hStep2 _ _)
    (by rw [extractReturnMemoryV2_forArgs q.callerMem _ _ _ hCM])

/-- `zero_body_exec` packaged as `BodyVerifiedV2` plus `unitBodyPost`. -/
private theorem zero_body_verified {defId : DefId} {body : Body}
    {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [])
    (hInit : initLocalsLoop body [] 0 body.locals =
      [.immediate (some .unit)])
    (hStep1 : ∀ (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0 [.immediate (some .unit)]) cm m) =
      .step (stateV2 (frameV2 defId 0 1 [.immediate (some .unit)]) cm m))
    (hStep2 : ∀ (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1 [.immediate (some .unit)]) cm m) =
      .done (.returned ⟨.unit, extractReturnMemoryV2 cm m
        [.immediate (some .unit)]⟩)) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.unitBodyPost Captured.program defId identity := by
  have hExec := zero_body_exec hBody hAdm hParams hInit hStep1 hStep2
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    (returnsExactly_of_exec (hExec q hValid)).1⟩, ?_⟩
  unfold Spec.unitBodyPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    (returnsExactly_of_exec (hExec q hValid)).2⟩

/-! ## Per-Body Proofs -/

private theorem body0_verified :
    BodyVerifiedV2 Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.unitBodyPost Captured.program 0
      (Spec.markerId "_::<impl KnownLayout for &mut u8") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body1_verified :
    BodyVerifiedV2 Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.unitBodyPost Captured.program 1
      (Spec.markerId "_::<impl KnownLayout for &u8") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body2_verified :
    BodyVerifiedV2 Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.unitBodyPost Captured.program 2
      (Spec.arrayPtrMetaId "[u32; 0]") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body3_verified :
    BodyVerifiedV2 Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.unitBodyPost Captured.program 3
      (Spec.arrayPtrMetaId "[u32; 4]") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body4_verified :
    BodyVerifiedV2 Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.unitBodyPost Captured.program 4
      (Spec.arrayPtrMetaId "[u8; 0]") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body5_verified :
    BodyVerifiedV2 Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.unitBodyPost Captured.program 5
      (Spec.arrayPtrMetaId "[u8; 4]") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body6_verified :
    BodyVerifiedV2 Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.unitBodyPost Captured.program 6
      (Spec.markerId "impls::_::<impl FromBytes for [u8]") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body7_verified :
    BodyVerifiedV2 Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.unitBodyPost Captured.program 7
      (Spec.markerId "impls::_::<impl FromZeros for [u8]") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body8_verified :
    BodyVerifiedV2 Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.unitBodyPost Captured.program 8
      (Spec.markerId
        "impls::_::<impl FromZeros for core::option::Option<&mut u8>") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body9_verified :
    BodyVerifiedV2 Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.unitBodyPost Captured.program 9
      (Spec.markerId "impls::_::<impl Immutable for &mut u8") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body10_verified :
    BodyVerifiedV2 Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.unitBodyPost Captured.program 10
      (Spec.markerId "impls::_::<impl Immutable for &u8") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body11_verified :
    BodyVerifiedV2 Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.unitBodyPost Captured.program 11
      (Spec.markerId "impls::_::<impl Immutable for [u8]") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body12_verified :
    BodyVerifiedV2 Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.unitBodyPost Captured.program 12
      (Spec.markerId
        "impls::_::<impl Immutable for core::ptr::non_null::NonNull<u8>") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body13_verified :
    BodyVerifiedV2 Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.unitBodyPost Captured.program 13
      (Spec.markerId "impls::_::<impl IntoBytes for [u8]") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body14_verified :
    BodyVerifiedV2 Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.unitBodyPost Captured.program 14
      (Spec.markerId "impls::_::<impl TryFromBytes for [u8]") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body15_verified :
    BodyVerifiedV2 Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.unitBodyPost Captured.program 15
      (Spec.markerId
        "impls::_::<impl TryFromBytes for core::option::Option<&mut u8>") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body16_verified :
    BodyVerifiedV2 Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.unitBodyPost Captured.program 16
      (Spec.markerId "impls::_::<impl Unaligned for [u8]") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body17_verified :
    BodyVerifiedV2 Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.unitBodyPost Captured.program 17
      (Spec.markerId "impls::tuples::_::<impl FromBytes for (u8, u32)") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body18_verified :
    BodyVerifiedV2 Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.unitBodyPost Captured.program 18
      (Spec.markerId "impls::tuples::_::<impl FromBytes for (u8,)") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body19_verified :
    BodyVerifiedV2 Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.unitBodyPost Captured.program 19
      (Spec.markerId "impls::tuples::_::<impl FromZeros for (u8, u32)") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body20_verified :
    BodyVerifiedV2 Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.unitBodyPost Captured.program 20
      (Spec.markerId "impls::tuples::_::<impl FromZeros for (u8,)") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body21_verified :
    BodyVerifiedV2 Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.unitBodyPost Captured.program 21
      (Spec.markerId "impls::tuples::_::<impl Immutable for (u8, u32)") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body22_verified :
    BodyVerifiedV2 Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.unitBodyPost Captured.program 22
      (Spec.markerId "impls::tuples::_::<impl Immutable for (u8,)") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body23_verified :
    BodyVerifiedV2 Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.unitBodyPost Captured.program 23
      (Spec.markerId "impls::tuples::_::<impl TryFromBytes for (u8, u32)") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body24_verified :
    BodyVerifiedV2 Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.unitBodyPost Captured.program 24
      (Spec.markerId "impls::tuples::_::<impl TryFromBytes for (u8,)") :=
  zero_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

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
    | 12, h =>
      cases (h : some Captured.body_12 = some body); exact body12_verified.1
    | 13, h =>
      cases (h : some Captured.body_13 = some body); exact body13_verified.1
    | 14, h =>
      cases (h : some Captured.body_14 = some body); exact body14_verified.1
    | 15, h =>
      cases (h : some Captured.body_15 = some body); exact body15_verified.1
    | 16, h =>
      cases (h : some Captured.body_16 = some body); exact body16_verified.1
    | 17, h =>
      cases (h : some Captured.body_17 = some body); exact body17_verified.1
    | 18, h =>
      cases (h : some Captured.body_18 = some body); exact body18_verified.1
    | 19, h =>
      cases (h : some Captured.body_19 = some body); exact body19_verified.1
    | 20, h =>
      cases (h : some Captured.body_20 = some body); exact body20_verified.1
    | 21, h =>
      cases (h : some Captured.body_21 = some body); exact body21_verified.1
    | 22, h =>
      cases (h : some Captured.body_22 = some body); exact body22_verified.1
    | 23, h =>
      cases (h : some Captured.body_23 = some body); exact body23_verified.1
    | 24, h =>
      cases (h : some Captured.body_24 = some body); exact body24_verified.1
    | n + 25, h => nomatch (h : (none : Option Body) = some body)
  · exact ⟨body0_verified.2, body1_verified.2, body2_verified.2,
      body3_verified.2, body4_verified.2, body5_verified.2, body6_verified.2,
      body7_verified.2, body8_verified.2, body9_verified.2, body10_verified.2,
      body11_verified.2, body12_verified.2, body13_verified.2,
      body14_verified.2, body15_verified.2, body16_verified.2,
      body17_verified.2, body18_verified.2, body19_verified.2,
      body20_verified.2, body21_verified.2, body22_verified.2,
      body23_verified.2, body24_verified.2, trivial⟩

end Proof
