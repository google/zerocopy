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

/-! ## `maximum_trailing_slice_len` Bodies (`_0 = const n; return`) -/

/-- A parameterless body whose return local starts uninitialized and which
steps by `_0 = const v` and then `return` returns `v` with caller memory
unchanged on every valid entry. -/
private theorem const_body_exec {defId : DefId} {body : Body} {v : Val}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hParams : (body.locals.drop 1).take body.argumentCount = [])
    (hInit : initLocalsLoop body [] 0 body.locals = [.immediate none])
    (hStep1 : ∀ (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0 [.immediate none]) cm m) =
      .step (stateV2 (frameV2 defId 0 1 [.immediate (some v)]) cm m))
    (hStep2 : ∀ (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1 [.immediate (some v)]) cm m) =
      .done (.returned ⟨v,
        extractReturnMemoryV2 cm m [.immediate (some v)]⟩))
    (q : Query) (hValid : ValidEntryArgsV2 body q) :
    execProgV2 (entryProgForBody Captured.program defId) 2 q
      (fun o => o = .returned ⟨v, q.callerMem⟩) := by
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  have hArgs : q.args = [] := by
    have h : checkArgsMatchV2 q.args
        ((body.locals.drop 1).take body.argumentCount) = true := hValid.2.1
    rw [hParams] at h
    revert h
    cases q.args with
    | nil => intro _; rfl
    | cons _ _ => intro h; exact False.elim (boolFalseNeTrue h)
  let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
  have hInitState :
      initStateV2 (entryProgForBody Captured.program defId) q =
      .ok (stateV2 (frameV2 defId 0 0 [.immediate none])
        q.callerMem (entryMemoryWithCaller q.callerMem)) := by
    have h := ctx.initStateV2_ok_frameV2 hBody hAdm hValid
      (by rw [hParams]; rfl)
    rw [hArgs, hInit] at h
    exact h
  unfold execProgV2
  rw [hInitState]
  apply execOutcomeStateV2_step (hStep1 _ _)
  exact execOutcomeStateV2_done (hStep2 _ _)
    (by rw [extractReturnMemoryV2_entryMemory,
      extractCallerMemory_entry q.callerMem hCM])

/-- `const_body_exec` packaged as `BodyVerifiedV2` plus `constBodyPost`. -/
private theorem const_body_verified {defId : DefId} {body : Body}
    {identity : String} {n : Nat}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [])
    (hInit : initLocalsLoop body [] 0 body.locals = [.immediate none])
    (hStep1 : ∀ (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0 [.immediate none]) cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some (Spec.usizeVal n))]) cm m))
    (hStep2 : ∀ (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some (Spec.usizeVal n))]) cm m) =
      .done (.returned ⟨Spec.usizeVal n,
        extractReturnMemoryV2 cm m [.immediate (some (Spec.usizeVal n))]⟩)) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.constBodyPost Captured.program defId identity n := by
  have hExec := const_body_exec hBody hAdm hParams hInit hStep1 hStep2
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    (returnsExactly_of_exec (hExec q hValid)).1⟩, ?_⟩
  unfold Spec.constBodyPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    (returnsExactly_of_exec (hExec q hValid)).2⟩

/-- Body 0: `maximum_trailing_slice_len::<()>`. -/
private theorem body0_verified :
    BodyVerifiedV2 Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.constBodyPost Captured.program 0 (Spec.maxLenId "()")
      (Spec.maxTrailingSliceLen none) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-- Body 1: `maximum_trailing_slice_len::<[()]>`. -/
private theorem body1_verified :
    BodyVerifiedV2 Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.constBodyPost Captured.program 1 (Spec.maxLenId "[()]")
      (Spec.maxTrailingSliceLen (some 0)) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-- Body 2: `maximum_trailing_slice_len::<[[u8; 3]]>`. -/
private theorem body2_verified :
    BodyVerifiedV2 Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.constBodyPost Captured.program 2 (Spec.maxLenId "[[u8; 3]]")
      (Spec.maxTrailingSliceLen (some 3)) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-- Body 3: `maximum_trailing_slice_len::<[u128]>`. -/
private theorem body3_verified :
    BodyVerifiedV2 Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.constBodyPost Captured.program 3 (Spec.maxLenId "[u128]")
      (Spec.maxTrailingSliceLen (some 16)) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-- Body 4: `maximum_trailing_slice_len::<[u16]>`. -/
private theorem body4_verified :
    BodyVerifiedV2 Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.constBodyPost Captured.program 4 (Spec.maxLenId "[u16]")
      (Spec.maxTrailingSliceLen (some 2)) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-- Body 5: `maximum_trailing_slice_len::<[u32]>`. -/
private theorem body5_verified :
    BodyVerifiedV2 Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.constBodyPost Captured.program 5 (Spec.maxLenId "[u32]")
      (Spec.maxTrailingSliceLen (some 4)) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-- Body 6: `maximum_trailing_slice_len::<[u64]>`. -/
private theorem body6_verified :
    BodyVerifiedV2 Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.constBodyPost Captured.program 6 (Spec.maxLenId "[u64]")
      (Spec.maxTrailingSliceLen (some 8)) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-- Body 7: `maximum_trailing_slice_len::<[u8]>`. -/
private theorem body7_verified :
    BodyVerifiedV2 Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.constBodyPost Captured.program 7 (Spec.maxLenId "[u8]")
      (Spec.maxTrailingSliceLen (some 1)) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-- Body 8: `maximum_trailing_slice_len::<str>`. -/
private theorem body8_verified :
    BodyVerifiedV2 Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.constBodyPost Captured.program 8 (Spec.maxLenId "str")
      (Spec.maxTrailingSliceLen (some 1)) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-- Body 9: `maximum_trailing_slice_len::<u32>`. -/
private theorem body9_verified :
    BodyVerifiedV2 Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.constBodyPost Captured.program 9 (Spec.maxLenId "u32")
      (Spec.maxTrailingSliceLen none) :=
  const_body_verified rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-! ## `swap` Bodies -/

/-- The entry frame of a `swap` body: an uninitialized return local, the
argument pair, and four dead temporaries. -/
private abbrev swapEntry (a b : Val) : List LocalSlot :=
  [.immediate none, .immediate (some (.tuple [a, b])), .dead, .dead, .dead,
   .dead]

/-- A valid single argument of tuple type `(tA, tB)` is a pair of values of
those types. -/
private theorem pair_arg_of_valid {body : Body} {q : Query} {tA tB : MirTy}
    (hParams : (body.locals.drop 1).take body.argumentCount = [.tuple [tA, tB]])
    (hValid : ValidEntryArgsV2 body q) :
    ∃ a b : Val, q.args = [.tuple [a, b]] ∧ checkValV2 a tA = true ∧
      checkValV2 b tB = true := by
  have hMatch : checkArgsMatchV2 q.args [.tuple [tA, tB]] = true := by
    have h : checkArgsMatchV2 q.args
        ((body.locals.drop 1).take body.argumentCount) = true := hValid.2.1
    rw [hParams] at h
    exact h
  let ⟨v, hArgs, hCheck⟩ := checkArgsMatchV2_singleton_inv hMatch
  cases v with
  | tuple vs =>
    match vs, hCheck with
    | [a, b], h =>
      have h' : (checkValV2 a tA && (checkValV2 b tB && true)) = true := h
      revert h'
      cases hA : checkValV2 a tA with
      | false => intro h'; exact False.elim (boolFalseNeTrue h')
      | true =>
        cases hB : checkValV2 b tB with
        | false => intro h'; exact False.elim (boolFalseNeTrue h')
        | true => intro _; exact ⟨a, b, hArgs, hA, hB⟩
    | [], h => exact False.elim (boolFalseNeTrue h)
    | [_], h =>
      have h' : (checkValV2 _ tA && false) = true := h
      revert h'
      cases checkValV2 _ tA <;> intro h' <;>
        exact False.elim (boolFalseNeTrue h')
    | _ :: _ :: _ :: _, h =>
      have h' : (checkValV2 _ tA && (checkValV2 _ tB && false)) = true := h
      revert h'
      cases checkValV2 _ tA <;> cases checkValV2 _ tB <;> intro h' <;>
        exact False.elim (boolFalseNeTrue h')
  | optionVal o =>
    cases o with
    | none => exact False.elim (boolFalseNeTrue hCheck)
    | some _ => exact False.elim (boolFalseNeTrue hCheck)
  | boxPtr _ len =>
    cases len with
    | none => exact False.elim (boolFalseNeTrue hCheck)
    | some _ => exact False.elim (boolFalseNeTrue hCheck)
  | _ => exact False.elim (boolFalseNeTrue hCheck)

/-- A `swap` body whose 14 steps from its entry frame return the swapped pair
with memory untouched returns `(b, a)` with caller memory unchanged on every
valid entry. -/
private theorem swap_body_exec {defId : DefId} {body : Body} {tA tB : MirTy}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hParams : (body.locals.drop 1).take body.argumentCount = [.tuple [tA, tB]])
    (hNoRaw : tyListHasRawPtrV2 [.tuple [tA, tB]] = false)
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v), .dead, .dead, .dead, .dead])
    (hRun : ∀ (a b : Val) (cm : CallerMemory),
      checkValV2 a tA = true → checkValV2 b tB = true →
      execOutcomeStateV2 (entryProgForBody Captured.program defId)
        (fun o => o = .returned ⟨.tuple [b, a],
          extractCallerMemory cm (entryMemoryWithCaller cm)⟩)
        (fun _ => False) 14
        (stateV2 (frameV2 defId 0 0 (swapEntry a b)) cm
          (entryMemoryWithCaller cm)))
    (q : Query) (hValid : ValidEntryArgsV2 body q) :
    ∃ a b : Val, q.args = [.tuple [a, b]] ∧
      execProgV2 (entryProgForBody Captured.program defId) 14 q
        (fun o => o = .returned ⟨.tuple [b, a], q.callerMem⟩) := by
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  let ⟨a, b, hArgs, hA, hB⟩ := pair_arg_of_valid hParams hValid
  let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
  have hInitState :
      initStateV2 (entryProgForBody Captured.program defId) q =
      .ok (stateV2 (frameV2 defId 0 0 (swapEntry a b))
        q.callerMem (entryMemoryWithCaller q.callerMem)) := by
    have h := ctx.initStateV2_ok_frameV2 hBody hAdm hValid
      (by rw [hParams]; exact hNoRaw)
    rw [hArgs, hInit] at h
    exact h
  refine ⟨a, b, hArgs, ?_⟩
  have hR := hRun a b q.callerMem hA hB
  rw [extractCallerMemory_entry q.callerMem hCM] at hR
  unfold execProgV2
  rw [hInitState]
  exact hR

/-- `swap_body_exec` packaged as `BodyVerifiedV2` plus `swapBodyPost`. -/
private theorem swap_body_verified {defId : DefId} {body : Body}
    {tA tB : MirTy} {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [.tuple [tA, tB]])
    (hNoRaw : tyListHasRawPtrV2 [.tuple [tA, tB]] = false)
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v), .dead, .dead, .dead, .dead])
    (hRun : ∀ (a b : Val) (cm : CallerMemory),
      checkValV2 a tA = true → checkValV2 b tB = true →
      execOutcomeStateV2 (entryProgForBody Captured.program defId)
        (fun o => o = .returned ⟨.tuple [b, a],
          extractCallerMemory cm (entryMemoryWithCaller cm)⟩)
        (fun _ => False) 14
        (stateV2 (frameV2 defId 0 0 (swapEntry a b)) cm
          (entryMemoryWithCaller cm))) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.swapBodyPost Captured.program defId identity := by
  have hExec := swap_body_exec hBody hAdm hParams hNoRaw hInit hRun
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    let ⟨_, _, _, hE⟩ := hExec q hValid
    (returnsExactly_of_exec hE).1⟩, ?_⟩
  unfold Spec.swapBodyPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    let ⟨a, b, hArgs, hE⟩ := hExec q hValid
    ⟨a, b, hArgs, (returnsExactly_of_exec hE).2⟩⟩

/-- A type whose values never hold references: no allocation ids, every
value reference-valid, and no access spans. -/
private def RefFree (t : MirTy) : Prop :=
  (∀ v : Val, refAllocIds t v = []) ∧
  (∀ (m : MemoryState) (v : Val), refsValidInMem m t v = true) ∧
  (∀ v : Val, refAccessSpans t v = [])

private theorem refFree_int (w : IntWidth) (s : Bool) : RefFree (.int w s) :=
  ⟨fun v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl,
   fun _ v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl,
   fun v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl⟩

private theorem refFree_bool : RefFree .bool :=
  ⟨fun v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl,
   fun _ v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl,
   fun v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl⟩

private theorem refFree_char : RefFree .char :=
  ⟨fun v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl,
   fun _ v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl,
   fun v => by cases v with | optionVal o => cases o <;> rfl | _ => rfl⟩

/-- Arrays of reference-free elements are reference-free. -/
private theorem refFree_array {e : MirTy} (n : Nat) (he : RefFree e) :
    RefFree (.array e n) := by
  refine ⟨fun v => ?_, fun m v => ?_, fun v => ?_⟩
  · cases v with
    | optionVal o => cases o <;> rfl
    | array vs =>
      change refAllocIdsArray e vs = []
      induction vs with
      | nil => rfl
      | cons x xs ih =>
        change refAllocIds e x ++ refAllocIdsArray e xs = []
        rw [he.1 x, ih]
        rfl
    | _ => rfl
  · cases v with
    | optionVal o => cases o <;> rfl
    | array vs =>
      change refsValidInMemArray m e vs = true
      induction vs with
      | nil => rfl
      | cons x xs ih =>
        change (refsValidInMem m e x && refsValidInMemArray m e xs) = true
        rw [he.2.1 m x, ih]
        rfl
    | _ => rfl
  · cases v with
    | optionVal o => cases o <;> rfl
    | array vs =>
      change refAccessSpansArray e vs = []
      induction vs with
      | nil => rfl
      | cons x xs ih =>
        change refAccessSpans e x ++ refAccessSpansArray e xs = []
        rw [he.2.2 x, ih]
        rfl
    | _ => rfl

/-- The `return` side conditions for a pair of reference-free values. -/
private theorem pair_return_facts {cm : CallerMemory} {m : MemoryState}
    {tA tB : MirTy} {a b : Val} (hA : RefFree tA) (hB : RefFree tB) :
    refsStayInCallerMem cm (.tuple [tB, tA]) (.tuple [b, a]) = true ∧
    refsValidInMem m (.tuple [tB, tA]) (.tuple [b, a]) = true ∧
    spansPairwiseDisjoint (refAccessSpans (.tuple [tB, tA]) (.tuple [b, a])) =
      true := by
  refine ⟨?_, ?_, ?_⟩
  · change (refAllocIds tB b ++ (refAllocIds tA a ++ [])).all
      (fun aid => (findAllocation aid cm.allocations).isSome) = true
    rw [hB.1 b, hA.1 a]
    rfl
  · change (refsValidInMem m tB b && (refsValidInMem m tA a && true)) = true
    rw [hB.2.1 m b, hA.2.1 m a]
    rfl
  · change spansPairwiseDisjoint
      (refAccessSpans tB b ++ (refAccessSpans tA a ++ [])) = true
    rw [hB.2.2 b, hA.2.2 a]
    rfl

/-- Evaluate the `swap` result aggregate `(move _4, move _5)`. -/
private theorem evalRvalueV2_swap_pair {bodyLocals : List MirTy}
    {locals locals1 : List LocalSlot} {mem : MemoryState} {tA tB : MirTy}
    {a b : Val} {typedVals : List (MirTy × Val)}
    (hOps : evalArgOperandsV2 bodyLocals locals mem
      [.move ⟨4, []⟩, .move ⟨5, []⟩] = .ok (typedVals, locals1, mem))
    (hVals : argValues typedVals = [b, a])
    (hB : checkValV2 b tB = true) (hA : checkValV2 a tA = true) :
    evalRvalueV2 bodyLocals locals mem (.tuple [tB, tA])
      (.aggregateTuple [.move ⟨4, []⟩, .move ⟨5, []⟩]) =
      .ok (.tuple [b, a], locals1, mem) := by
  unfold evalRvalueV2
  dsimp only
  rw [hOps]
  dsimp only
  rw [hVals]
  have hList : checkValV2List [b, a] [tB, tA] = true := by
    change (checkValV2 b tB && (checkValV2 a tA && true)) = true
    rw [hB, hA]
    rfl
  rw [hList]
  rfl

/-- `checkValV2` of a pair from its components. -/
private theorem checkValV2_pair {a b : Val} {tA tB : MirTy}
    (hB : checkValV2 b tB = true) (hA : checkValV2 a tA = true) :
    checkValV2 (.tuple [b, a]) (.tuple [tB, tA]) = true := by
  change (checkValV2 b tB && (checkValV2 a tA && true)) = true
  rw [hB, hA]
  rfl

/-- Body 10: `swap::<[u8; 2], u16>`. -/
private theorem body10_verified :
    BodyVerifiedV2 Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.swapBodyPost Captured.program 10 (Spec.swapId "[u8; 2], u16") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ cm hA hB =>
      let hR := pair_return_facts (cm := cm)
        (m := entryMemoryWithCaller cm)
        (refFree_array 2 (refFree_int .i8 false)) (refFree_int .i16 false)
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 11: `swap::<bool, char>`. -/
private theorem body11_verified :
    BodyVerifiedV2 Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.swapBodyPost Captured.program 11 (Spec.swapId "bool, char") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ cm hA hB =>
      let hR := pair_return_facts (cm := cm)
        (m := entryMemoryWithCaller cm)
        refFree_bool refFree_char
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 12: `swap::<i16, u64>`. -/
private theorem body12_verified :
    BodyVerifiedV2 Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.swapBodyPost Captured.program 12 (Spec.swapId "i16, u64") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ cm hA hB =>
      let hR := pair_return_facts (cm := cm)
        (m := entryMemoryWithCaller cm)
        (refFree_int .i16 true) (refFree_int .i64 false)
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 13: `swap::<u128, i8>`. -/
private theorem body13_verified :
    BodyVerifiedV2 Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.swapBodyPost Captured.program 13 (Spec.swapId "u128, i8") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ cm hA hB =>
      let hR := pair_return_facts (cm := cm)
        (m := entryMemoryWithCaller cm)
        (refFree_int .i128 false) (refFree_int .i8 true)
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 14: `swap::<u8, u32>`. -/
private theorem body14_verified :
    BodyVerifiedV2 Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.swapBodyPost Captured.program 14 (Spec.swapId "u8, u32") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ cm hA hB =>
      let hR := pair_return_facts (cm := cm)
        (m := entryMemoryWithCaller cm)
        (refFree_int .i8 false) (refFree_int .i32 false)
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

/-- Body 15: `swap::<usize, isize>`. -/
private theorem body15_verified :
    BodyVerifiedV2 Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.swapBodyPost Captured.program 15 (Spec.swapId "usize, isize") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl rfl (fun _ => rfl)
    (fun _ _ cm hA hB =>
      let hR := pair_return_facts (cm := cm)
        (m := entryMemoryWithCaller cm)
        (refFree_int .isize false) (refFree_int .isize true)
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hB rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageLive rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hA rfl rfl)) <|
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
        (evalRvalueV2_swap_pair rfl rfl hB hA)
        (writePlaceDestV2_immediate_ok (checkValV2_pair hB hA) rfl rfl)) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_step
        (evalStepV2_storageDead rfl rfl rfl rfl rfl rfl rfl) <|
      execOutcomeStateV2_done
        (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          hR.1 hR.2.1 hR.2.2)
        (by rw [extractReturnMemoryV2_entryMemory]))

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
    | n + 16, h => nomatch (h : (none : Option Body) = some body)
  · exact ⟨⟨body0_verified.2, body1_verified.2, body2_verified.2,
      body3_verified.2, body4_verified.2, body5_verified.2, body6_verified.2,
      body7_verified.2, body8_verified.2, body9_verified.2, trivial⟩,
      ⟨body10_verified.2, body11_verified.2, body12_verified.2,
      body13_verified.2, body14_verified.2, body15_verified.2, trivial⟩⟩

end Proof
