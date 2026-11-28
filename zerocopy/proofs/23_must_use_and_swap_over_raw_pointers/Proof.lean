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
import Anneal.Framework
import Anneal.MirWp.V2StepShield

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Shared Plumbing -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  nomatch h

/-- Split a Boolean conjunction that holds. -/
private theorem and_true_split {x y : Bool} (h : (x && y) = true) :
    x = true ∧ y = true := by
  cases x <;> cases y <;> first | exact ⟨rfl, rfl⟩ | exact nomatch h

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
the caller's memory, and no returned pointer can name a read-only allocation
that the callee created. -/

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

/-- No allocation id is a callee `.rodata` allocation in a memory whose
allocations are the caller's. -/
private theorem anyRodataAllocId_false_of_allocs {cm : CallerMemory}
    {mem : MemoryState} (h : mem.allocations = cm.allocations) :
    ∀ ids : List AllocId, anyRodataAllocId cm mem ids = false
  | [] => rfl
  | aid :: rest => by
    have hRest := anyRodataAllocId_false_of_allocs h rest
    unfold anyRodataAllocId isRodataAllocId
    cases hF : findAllocation aid cm.allocations with
    | some _ => exact hRest
    | none =>
      rw [h, hF]
      exact hRest

/-- A value returned from raw-pointer entry memory carries no escaping
`.rodata` pointer. -/
private theorem noRodata_forArgs (cm : CallerMemory) (paramTys : List MirTy)
    (args : List Val) (ty : MirTy) (v : Val) :
    hasEscapingRodataPtr cm (entryMemoryForArgsV2 cm paramTys args) ty v =
      false :=
  anyRodataAllocId_false_of_allocs
    (entryMemoryForArgsV2_allocations_eq cm paramTys args) _

/-! ## Types Without References -/

/-- A type whose values hold no references (raw pointers are not
references): no reference allocation ids, every value reference-valid, and
no mutable-borrow spans. -/
private def NoRefs (t : MirTy) : Prop :=
  (∀ v : Val, refAllocIds t v = []) ∧
  (∀ (m : MemoryState) (v : Val), refsValidInMem m t v = true) ∧
  (∀ v : Val, refAccessSpans t v = [])

private theorem noRefs_rawPtr (mu : Mutability) (pt : MirTy) :
    NoRefs (.rawPtr mu pt) :=
  ⟨fun v => by
    cases v with
    | optionVal o => cases o <;> rfl
    | boxPtr _ l => cases l <;> rfl
    | _ => rfl,
   fun _ v => by
    cases v with
    | optionVal o => cases o <;> rfl
    | boxPtr _ l => cases l <;> rfl
    | _ => rfl,
   fun v => by
    cases v with
    | optionVal o => cases o <;> rfl
    | boxPtr _ l => cases l <;> rfl
    | _ => rfl⟩

private theorem noRefs_bool : NoRefs .bool :=
  ⟨fun v => by
    cases v with
    | optionVal o => cases o <;> rfl
    | boxPtr _ l => cases l <;> rfl
    | _ => rfl,
   fun _ v => by
    cases v with
    | optionVal o => cases o <;> rfl
    | boxPtr _ l => cases l <;> rfl
    | _ => rfl,
   fun v => by
    cases v with
    | optionVal o => cases o <;> rfl
    | boxPtr _ l => cases l <;> rfl
    | _ => rfl⟩

private theorem noRefs_option {t : MirTy} (h : NoRefs t) :
    NoRefs (.option t) :=
  ⟨fun v => by
    cases v with
    | optionVal o =>
      cases o with
      | none => rfl
      | some w => exact h.1 w
    | boxPtr _ l => cases l <;> rfl
    | _ => rfl,
   fun m v => by
    cases v with
    | optionVal o =>
      cases o with
      | none => rfl
      | some w => exact h.2.1 m w
    | boxPtr _ l => cases l <;> rfl
    | _ => rfl,
   fun v => by
    cases v with
    | optionVal o =>
      cases o with
      | none => rfl
      | some w => exact h.2.2 w
    | boxPtr _ l => cases l <;> rfl
    | _ => rfl⟩

/-- The `return` side conditions for a value of a type without
references. -/
private theorem noRefs_return_facts {cm : CallerMemory} {m : MemoryState}
    {t : MirTy} {v : Val} (h : NoRefs t) :
    refsStayInCallerMem cm t v = true ∧ refsValidInMem m t v = true ∧
    spansPairwiseDisjoint (refAccessSpans t v) = true := by
  refine ⟨?_, h.2.1 m v, ?_⟩
  · unfold refsStayInCallerMem
    rw [h.1 v]
    rfl
  · rw [h.2.2 v]
    rfl

/-- The `return` side conditions for a pair of values of types without
references. -/
private theorem noRefs_pair_return_facts {cm : CallerMemory}
    {m : MemoryState} {tA tB : MirTy} {a b : Val} (hA : NoRefs tA)
    (hB : NoRefs tB) :
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

/-- A `return` step whose value carries no escaping `.rodata` pointer, for
return types that may hold raw pointers. -/
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

/-! ## `must_use` Bodies (`_0 = move _1; return`) -/

/-- The run hypothesis of a one-parameter identity body: for any
postcondition that holds of every return of `v` with the memory the body
ends in, two steps from the entry frame establish it. -/
private abbrev IdentityRuns (defId : DefId) (t : MirTy) : Prop :=
  ∀ (v : Val) (cm : CallerMemory) (m : MemoryState)
    (post : TerminalOut → Prop),
    (∀ l : List LocalSlot,
      post (.returned ⟨v, extractReturnMemoryV2 cm m l⟩)) →
    checkValV2 v t = true → hasEscapingRodataPtr cm m t v = false →
    execOutcomeStateV2 (entryProgForBody Captured.program defId) post
      (fun _ => False) 2
      (stateV2 (frameV2 defId 0 0 [.immediate none, .immediate (some v)]) cm m)

/-- An identity body satisfying `IdentityRuns` returns its argument with
caller memory unchanged on every valid entry. -/
private theorem identity_body_verified {defId : DefId} {body : Body}
    {t : MirTy} {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v)])
    (hRun : IdentityRuns defId t) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.identityBodyPost Captured.program defId identity := by
  have hExec : ∀ q : Query, ValidEntryArgsV2 body q →
      ∃ v : Val, q.args = [v] ∧
        execProgV2 (entryProgForBody Captured.program defId) 2 q
          (fun o => o = .returned ⟨v, q.callerMem⟩) := by
    intro q hValid
    have hCM : validCallerMemory q.callerMem = true := hValid.1
    have hMatch : checkArgsMatchV2 q.args [t] = true := by
      have h : checkArgsMatchV2 q.args
          ((body.locals.drop 1).take body.argumentCount) = true := hValid.2.1
      rw [hParams] at h
      exact h
    let ⟨v, hArgs, hCheck⟩ := checkArgsMatchV2_singleton_inv hMatch
    let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
    have hInitState :
        initStateV2 (entryProgForBody Captured.program defId) q =
        .ok (stateV2 (frameV2 defId 0 0 [.immediate none, .immediate (some v)])
          q.callerMem (entryMemoryForArgsV2 q.callerMem [t] [v])) := by
      have h := ctx.initStateV2_ok_frameV2_forArgs hBody hAdm hValid
      rw [hArgs, hInit, hParams] at h
      exact h
    refine ⟨v, hArgs, ?_⟩
    unfold execProgV2
    rw [hInitState]
    exact hRun v q.callerMem (entryMemoryForArgsV2 q.callerMem [t] [v]) _
      (fun l => by rw [extractReturnMemoryV2_forArgs _ _ _ l hCM]) hCheck
      (noRodata_forArgs _ _ _ _ _)
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    let ⟨_, _, hE⟩ := hExec q hValid
    (returnsExactly_of_exec hE).1⟩, ?_⟩
  unfold Spec.identityBodyPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    let ⟨v, hArgs, hE⟩ := hExec q hValid
    ⟨v, hArgs, (returnsExactly_of_exec hE).2⟩⟩

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
      let ⟨hA, hB'⟩ := and_true_split h'
      exact ⟨a, b, hArgs, hA, (and_true_split hB').1⟩
    | [], h => exact False.elim (boolFalseNeTrue h)
    | [_], h =>
      have h' : (checkValV2 _ tA && false) = true := h
      exact False.elim (boolFalseNeTrue (and_true_split h').2)
    | _ :: _ :: _ :: _, h =>
      have h' : (checkValV2 _ tA && (checkValV2 _ tB && false)) = true := h
      exact False.elim
        (boolFalseNeTrue (and_true_split (and_true_split h').2).2)
  | optionVal o =>
    cases o with
    | none => exact False.elim (boolFalseNeTrue hCheck)
    | some _ => exact False.elim (boolFalseNeTrue hCheck)
  | boxPtr _ len =>
    cases len with
    | none => exact False.elim (boolFalseNeTrue hCheck)
    | some _ => exact False.elim (boolFalseNeTrue hCheck)
  | _ => exact False.elim (boolFalseNeTrue hCheck)

/-- The run hypothesis of a `swap` body: for any postcondition that holds of
every return of `(b, a)` with the memory the body ends in, 14 steps from the
entry frame establish it. -/
private abbrev SwapRuns (defId : DefId) (tA tB : MirTy) : Prop :=
  ∀ (a b : Val) (cm : CallerMemory) (m : MemoryState)
    (post : TerminalOut → Prop),
    (∀ l : List LocalSlot,
      post (.returned ⟨.tuple [b, a], extractReturnMemoryV2 cm m l⟩)) →
    checkValV2 a tA = true → checkValV2 b tB = true →
    hasEscapingRodataPtr cm m (.tuple [tB, tA]) (.tuple [b, a]) = false →
    execOutcomeStateV2 (entryProgForBody Captured.program defId) post
      (fun _ => False) 14 (stateV2 (frameV2 defId 0 0 (swapEntry a b)) cm m)

/-- A `swap` body satisfying `SwapRuns` returns `(b, a)` with caller memory
unchanged on every valid entry. -/
private theorem swap_body_verified {defId : DefId} {body : Body}
    {tA tB : MirTy} {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [.tuple [tA, tB]])
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v), .dead, .dead, .dead, .dead])
    (hRun : SwapRuns defId tA tB) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.swapBodyPost Captured.program defId identity := by
  have hExec : ∀ q : Query, ValidEntryArgsV2 body q →
      ∃ a b : Val, q.args = [.tuple [a, b]] ∧
        execProgV2 (entryProgForBody Captured.program defId) 14 q
          (fun o => o = .returned ⟨.tuple [b, a], q.callerMem⟩) := by
    intro q hValid
    have hCM : validCallerMemory q.callerMem = true := hValid.1
    let ⟨a, b, hArgs, hA, hB⟩ := pair_arg_of_valid hParams hValid
    let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
    have hInitState :
        initStateV2 (entryProgForBody Captured.program defId) q =
        .ok (stateV2 (frameV2 defId 0 0 (swapEntry a b)) q.callerMem
          (entryMemoryForArgsV2 q.callerMem [.tuple [tA, tB]]
            [.tuple [a, b]])) := by
      have h := ctx.initStateV2_ok_frameV2_forArgs hBody hAdm hValid
      rw [hArgs, hInit, hParams] at h
      exact h
    refine ⟨a, b, hArgs, ?_⟩
    unfold execProgV2
    rw [hInitState]
    exact hRun a b q.callerMem _ _
      (fun l => by rw [extractReturnMemoryV2_forArgs _ _ _ l hCM]) hA hB
      (noRodata_forArgs _ _ _ _ _)
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    let ⟨_, _, _, hE⟩ := hExec q hValid
    (returnsExactly_of_exec hE).1⟩, ?_⟩
  unfold Spec.swapBodyPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    let ⟨a, b, hArgs, hE⟩ := hExec q hValid
    ⟨a, b, hArgs, (returnsExactly_of_exec hE).2⟩⟩

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

/-! ## Per-Body Proofs -/

/-- Body 0: `swap::<*const u8, *mut u16>`. -/
private theorem body0_verified :
    BodyVerifiedV2 Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.swapBodyPost Captured.program 0 (Spec.swapId "*const u8, *mut u16") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ _ hPost hA hB hN =>
      let hR := noRefs_pair_return_facts
        (noRefs_rawPtr .shared (.int .i8 false))
        (noRefs_rawPtr .mut (.int .i16 false))
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
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl hN
          hR.1 hR.2.1 hR.2.2)
        (hPost _))

/-- Body 1: `swap::<*mut [u8], bool>`. -/
private theorem body1_verified :
    BodyVerifiedV2 Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.swapBodyPost Captured.program 1 (Spec.swapId "*mut [u8], bool") :=
  swap_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ _ hPost hA hB hN =>
      let hR := noRefs_pair_return_facts
        (noRefs_rawPtr .mut (.slice (.int .i8 false)))
        noRefs_bool
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
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl hN
          hR.1 hR.2.1 hR.2.2)
        (hPost _))

/-- Body 2: `must_use::<*const [u8]>`. -/
private theorem body2_verified :
    BodyVerifiedV2 Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.identityBodyPost Captured.program 2
      (Spec.mustUseId "*const [u8]") :=
  identity_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost hC hN =>
      let hR := noRefs_return_facts
        (noRefs_rawPtr .shared (.slice (.int .i8 false)))
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hC rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl hN
          hR.1 hR.2.1 hR.2.2)
        (hPost _))

/-- Body 3: `must_use::<*const u8>`. -/
private theorem body3_verified :
    BodyVerifiedV2 Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.identityBodyPost Captured.program 3
      (Spec.mustUseId "*const u8") :=
  identity_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost hC hN =>
      let hR := noRefs_return_facts
        (noRefs_rawPtr .shared (.int .i8 false))
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hC rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl hN
          hR.1 hR.2.1 hR.2.2)
        (hPost _))

/-- Body 4: `must_use::<*mut [u16]>`. -/
private theorem body4_verified :
    BodyVerifiedV2 Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.identityBodyPost Captured.program 4
      (Spec.mustUseId "*mut [u16]") :=
  identity_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost hC hN =>
      let hR := noRefs_return_facts
        (noRefs_rawPtr .mut (.slice (.int .i16 false)))
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hC rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl hN
          hR.1 hR.2.1 hR.2.2)
        (hPost _))

/-- Body 5: `must_use::<*mut u32>`. -/
private theorem body5_verified :
    BodyVerifiedV2 Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.identityBodyPost Captured.program 5
      (Spec.mustUseId "*mut u32") :=
  identity_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost hC hN =>
      let hR := noRefs_return_facts
        (noRefs_rawPtr .mut (.int .i32 false))
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hC rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl hN
          hR.1 hR.2.1 hR.2.2)
        (hPost _))

/-- Body 6: `must_use::<core::option::Option<*const u8>>`. -/
private theorem body6_verified :
    BodyVerifiedV2 Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.identityBodyPost Captured.program 6
      (Spec.mustUseId "core::option::Option<*const u8>") :=
  identity_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ _ hPost hC hN =>
      let hR := noRefs_return_facts
        (noRefs_option (noRefs_rawPtr .shared (.int .i8 false)))
      execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl rfl
        (writePlaceDestV2_immediate_ok hC rfl rfl)) <|
      execOutcomeStateV2_done
        (evalStepV2_return_noRodata_ok rfl rfl rfl rfl rfl rfl rfl rfl hN
          hR.1 hR.2.1 hR.2.2)
        (hPost _))

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
    | n + 7, h => nomatch (h : (none : Option Body) = some body)
  · exact ⟨body0_verified.2, body1_verified.2, body2_verified.2,
      body3_verified.2, body4_verified.2, body5_verified.2, body6_verified.2⟩

end Proof
