-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.Framework
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

/-! ## Entry Memory with Raw-Pointer Arguments

With raw-pointer parameters, the entry memory is `entryMemoryForArgsV2`,
which differs from `entryMemoryWithCaller` only in `nextAllocId`. Its
allocations are the caller's, so a body that never allocates returns exactly
the caller's memory. -/

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

private theorem calleeLive_nil_of_sub {ids f : List AllocId} :
    ∀ {l : List Allocation}, (∀ a, a ∈ l → a.allocId ∈ ids) →
      calleeLiveAllocations ids f l = []
  | [], _ => rfl
  | a :: _, h => by
    unfold calleeLiveAllocations
    rw [natNotElem_false_of_mem (h a (.head _)), Bool.and_false,
      Bool.false_and]
    exact calleeLive_nil_of_sub (fun b hb => h b (.tail _ hb))

/-- Returning from untouched raw-pointer entry memory hands back exactly the
caller's memory. -/
private theorem extractReturnMemoryV2_forArgs (cm : CallerMemory)
    (paramTys : List MirTy) (args : List Val) (locals : List LocalSlot)
    (hValid : validCallerMemory cm = true) :
    extractReturnMemoryV2 cm (entryMemoryForArgsV2 cm paramTys args) locals =
      cm := by
  have hA : (entryMemoryForArgsV2 cm paramTys args).allocations =
      cm.allocations := entryMemoryForArgsV2_allocations_eq cm paramTys args
  unfold extractReturnMemoryV2
  rw [calleeLive_nil_of_sub (by rw [hA]; exact fun _ ha => mem_allocIdsOf ha),
    List.append_nil,
    Anneal.Framework.extractCallerMemory_entryMemoryForArgsV2 cm paramTys args
      hValid]

/-- A `return` step whose value carries no escaping `.rodata` pointer. -/
private theorem evalStepV2_return_noRodata_ok {p : Program} {body : Body}
    {bb : BasicBlock} {defId : DefId} {b i : Nat} {l : List LocalSlot}
    {cm : CallerMemory} {m : MemoryState} {retTy : MirTy} {retVal : Val}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = none)
    (hEnd : Nat.beq i bb.statements.length = true)
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? l 0 =
      some (.immediate (some retVal)))
    (hNoRodata : hasEscapingRodataPtr cm m retTy retVal = false)
    (hStay : refsStayInCallerMem cm retTy retVal = true)
    (hValid : refsValidInMem m retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true) :
    evalStepV2 p (stateV2 (frameV2 defId b i l) cm m) =
      .done (.returned ⟨retVal, extractReturnMemoryV2 cm m l⟩) :=
  (evalStepV2_term hBody hBB hStmt hEnd).trans
    (evalTerminatorV2_return_ok_of_noRodata hTerm hCleanup hRetTy hRetSlot
      hNoRodata hStay hValid hDisj)

/-! ## `pointer_to_metadata` Bodies (`_0 = const (); return`) -/

/-- The entry frame of a one-parameter body returning `()`: the
zero-sized return local starts initialized to `()`. -/
private abbrev unitEntry (v : Val) : List LocalSlot :=
  [.immediate (some .unit), .immediate (some v)]

/-- The run hypothesis of a one-parameter body returning `()`: for any
postcondition that holds of every return of `()` with the memory the body
ends in, two steps from the entry frame establish it. -/
private abbrev UnitRuns (defId : DefId) : Prop :=
  ∀ (v : Val) (cm : CallerMemory) (m : MemoryState)
    (post : TerminalOut → Prop),
    (∀ l : List LocalSlot,
      post (.returned ⟨.unit, extractReturnMemoryV2 cm m l⟩)) →
    execOutcomeStateV2 (entryProgForBody Captured.program defId) post
      (fun _ => False) 2
      (stateV2 (frameV2 defId 0 0 (unitEntry v)) cm m)

/-- A body satisfying `UnitRuns` returns `()` with caller memory unchanged on
every valid entry. -/
private theorem unit_body_verified {defId : DefId} {body : Body}
    {t : MirTy} {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      unitEntry v)
    (hRun : UnitRuns defId) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.returnsUnitPost Captured.program defId identity := by
  have hExec : ∀ q : Query, ValidEntryArgsV2 body q →
      ∃ v : Val, q.args = [v] ∧
        execProgV2 (entryProgForBody Captured.program defId) 2 q
          (fun o => o = .returned ⟨.unit, q.callerMem⟩) := by
    intro q hValid
    have hCM : validCallerMemory q.callerMem = true := hValid.1
    have hMatch : checkArgsMatchV2 q.args [t] = true := by
      have h : checkArgsMatchV2 q.args
          ((body.locals.drop 1).take body.argumentCount) = true := hValid.2.1
      rw [hParams] at h
      exact h
    let ⟨v, hArgs, _⟩ := checkArgsMatchV2_singleton_inv hMatch
    let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
    have hInitState :
        initStateV2 (entryProgForBody Captured.program defId) q =
        .ok (stateV2 (frameV2 defId 0 0 (unitEntry v))
          q.callerMem (entryMemoryForArgsV2 q.callerMem [t] [v])) := by
      have h := ctx.initStateV2_ok_frameV2_forArgs hBody hAdm hValid
      rw [hArgs, hInit, hParams] at h
      exact h
    refine ⟨v, hArgs, ?_⟩
    unfold execProgV2
    rw [hInitState]
    exact hRun v q.callerMem (entryMemoryForArgsV2 q.callerMem [t] [v]) _
      (fun l => by rw [extractReturnMemoryV2_forArgs _ _ _ l hCM])
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    let ⟨_, _, hE⟩ := hExec q hValid
    (returnsExactly_of_exec hE).1⟩, ?_⟩
  unfold Spec.returnsUnitPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    let ⟨v, hArgs, hE⟩ := hExec q hValid
    ⟨v, hArgs, (returnsExactly_of_exec hE).2⟩⟩

/-- Body 0: `<Option<()> as KnownLayout>::pointer_to_metadata`. -/
private theorem b0 :
    BodyVerifiedV2 Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.returnsUnitPost Captured.program 0 (Spec.optionPtmId "()") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 1: `<Option<bool> as KnownLayout>::pointer_to_metadata`. -/
private theorem b1 :
    BodyVerifiedV2 Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.returnsUnitPost Captured.program 1 (Spec.optionPtmId "bool") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 2: `<Option<i128> as KnownLayout>::pointer_to_metadata`. -/
private theorem b2 :
    BodyVerifiedV2 Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.returnsUnitPost Captured.program 2 (Spec.optionPtmId "i128") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 3: `<Option<i16> as KnownLayout>::pointer_to_metadata`. -/
private theorem b3 :
    BodyVerifiedV2 Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.returnsUnitPost Captured.program 3 (Spec.optionPtmId "i16") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 4: `<Option<i32> as KnownLayout>::pointer_to_metadata`. -/
private theorem b4 :
    BodyVerifiedV2 Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.returnsUnitPost Captured.program 4 (Spec.optionPtmId "i32") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 5: `<Option<i64> as KnownLayout>::pointer_to_metadata`. -/
private theorem b5 :
    BodyVerifiedV2 Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.returnsUnitPost Captured.program 5 (Spec.optionPtmId "i64") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 6: `<Option<i8> as KnownLayout>::pointer_to_metadata`. -/
private theorem b6 :
    BodyVerifiedV2 Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.returnsUnitPost Captured.program 6 (Spec.optionPtmId "i8") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 7: `<Option<isize> as KnownLayout>::pointer_to_metadata`. -/
private theorem b7 :
    BodyVerifiedV2 Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.returnsUnitPost Captured.program 7 (Spec.optionPtmId "isize") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 8: `<Option<u128> as KnownLayout>::pointer_to_metadata`. -/
private theorem b8 :
    BodyVerifiedV2 Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.returnsUnitPost Captured.program 8 (Spec.optionPtmId "u128") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 9: `<Option<u16> as KnownLayout>::pointer_to_metadata`. -/
private theorem b9 :
    BodyVerifiedV2 Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.returnsUnitPost Captured.program 9 (Spec.optionPtmId "u16") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 10: `<Option<u32> as KnownLayout>::pointer_to_metadata`. -/
private theorem b10 :
    BodyVerifiedV2 Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.returnsUnitPost Captured.program 10 (Spec.optionPtmId "u32") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 11: `<Option<u64> as KnownLayout>::pointer_to_metadata`. -/
private theorem b11 :
    BodyVerifiedV2 Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.returnsUnitPost Captured.program 11 (Spec.optionPtmId "u64") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 12: `<Option<u8> as KnownLayout>::pointer_to_metadata`. -/
private theorem b12 :
    BodyVerifiedV2 Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.returnsUnitPost Captured.program 12 (Spec.optionPtmId "u8") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-- Body 13: `<Option<usize> as KnownLayout>::pointer_to_metadata`. -/
private theorem b13 :
    BodyVerifiedV2 Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.returnsUnitPost Captured.program 13 (Spec.optionPtmId "usize") :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost =>
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok rfl rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl)
        (hPost _))

/-! ## Top-Level Claim -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    match defId, hBody with
    | 0, h =>
      cases (h : some Captured.body_0 = some body); exact b0.1
    | 1, h =>
      cases (h : some Captured.body_1 = some body); exact b1.1
    | 2, h =>
      cases (h : some Captured.body_2 = some body); exact b2.1
    | 3, h =>
      cases (h : some Captured.body_3 = some body); exact b3.1
    | 4, h =>
      cases (h : some Captured.body_4 = some body); exact b4.1
    | 5, h =>
      cases (h : some Captured.body_5 = some body); exact b5.1
    | 6, h =>
      cases (h : some Captured.body_6 = some body); exact b6.1
    | 7, h =>
      cases (h : some Captured.body_7 = some body); exact b7.1
    | 8, h =>
      cases (h : some Captured.body_8 = some body); exact b8.1
    | 9, h =>
      cases (h : some Captured.body_9 = some body); exact b9.1
    | 10, h =>
      cases (h : some Captured.body_10 = some body); exact b10.1
    | 11, h =>
      cases (h : some Captured.body_11 = some body); exact b11.1
    | 12, h =>
      cases (h : some Captured.body_12 = some body); exact b12.1
    | 13, h =>
      cases (h : some Captured.body_13 = some body); exact b13.1
    | n + 14, h => nomatch (h : (none : Option Body) = some body)
  · refine ⟨rfl, ?_⟩
    exact ⟨b0.2, b1.2, b2.2, b3.2, b4.2, b5.2, b6.2, b7.2, b8.2, b9.2, b10.2,
      b11.2, b12.2, b13.2, trivial⟩

end Proof
