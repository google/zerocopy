-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Expected
import Anneal.MirWp
import Anneal.Framework

namespace Proof

open Specs.zerocopy.zc01_usize_pointer_metadata
  (reachesDoneWithin contractTerminalPost fn0_id fn0_sig fn0_contract
   fn1_id fn1_sig fn1_contract specs)
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
open Anneal.Framework.StepWp Anneal.MirWp Anneal.Framework

private theorem body0_adm :
    BodyStaticAdmitted Captured.program Captured.body_0 = true := rfl

private theorem body1_adm :
    BodyStaticAdmitted Captured.program Captured.body_1 = true := rfl

private theorem writePlace_isize {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    writePlace [.immediate none, .immediate (some v)] entryMemory 0
        (.int .isize false) v =
      .ok ([.immediate (some v), .immediate (some v)], entryMemory) := by
  unfold writePlace
  rw [hv]
  rfl

private theorem step_copy_isize (body : Body) {v : Val}
    (hLoc : initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v)])
    (hRval : evalRvalue body.locals
        [.immediate none, .immediate (some v)]
        entryMemory (.int .isize false) (.use (.copy ⟨1, []⟩)) =
      .ok (v, [.immediate none, .immediate (some v)], entryMemory))
    (hStep : evalStep (bodyProg body) 0
        (mkState 0 0 [.immediate none, .immediate (some v)]) =
      match evalRvalue body.locals
          [.immediate none, .immediate (some v)]
          entryMemory (.int .isize false) (.use (.copy ⟨1, []⟩)) with
      | .error k => .fault k
      | .ok (val, l1, m1) =>
        match writePlace l1 m1 0 (.int .isize false) val with
        | .error k => .fault k
        | .ok (l2, m2) =>
          .step
            { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1,
                           locals := l2 }],
              callerMem := ⟨[]⟩, mem := m2 })
    (hv : checkVal v (.int .isize false) = true) :
    evalStep (bodyProg body) 0
      (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) =
    .step (mkState 0 1 [.immediate (some v), .immediate (some v)]) := by
  rw [hLoc, hStep, hRval]
  dsimp only
  rw [writePlace_isize hv]
  rfl

/-- Exact 2-step `execProg` witness (`1` `Copy` step + `1` `Return` step) from
`step_copy_isize` and `.ret rfl`. -/
private theorem exec2_of_copy_ret {defId : DefId} {body : Body} {v : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body [v])
    (h_step1 : evalStep (bodyProg body) 0
      (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) =
      .step (mkState 0 1 [.immediate (some v), .immediate (some v)]))
    (h_step2 : evalStep (bodyProg body) 0
      (mkState 0 1 [.immediate (some v), .immediate (some v)]) =
      .done (.returned ⟨v, ⟨[]⟩⟩)) :
    execProg (entryProgForBody Captured.program defId) 2 { args := [v] }
      (fun outcome => outcome = .returned ⟨v, ⟨[]⟩⟩) := by
  unfold execProg
  rw [initState_entryProgForBody h_body h_adm h_args]
  refine (execOutcomeState_entryProg_iff h_body
    (isSingleFrame0_mkState 0 0 _)).mpr ?_
  have hDone : execState (bodyProg body) 1
      (mkState 0 1 [.immediate (some v), .immediate (some v)])
      (fun outcome => outcome = .returned ⟨v, ⟨[]⟩⟩) := by
    dsimp only [execState, execOutcomeState, execStepOutcome]
    rw [execStepPred_succ_iff, h_step2]
  dsimp only [execState, execOutcomeState, execStepOutcome]
  rw [execStepPred_succ_iff, h_step1]
  exact hDone

/-- Bridge `wpState p b s post` (`Anneal.MirWp`) to `reachesDoneWithin`. -/
private theorem reachesDoneWithin_of_wpState {p : Program}
    {post : TerminalOut → Prop} :
    ∀ {b : Nat} {s : State},
      wpState p b s post → reachesDoneWithin p post b s
  | 0, _, h => False.elim h
  | b + 1, s, h => by
    unfold wpState wpOutcomeState wpStepOutcome at h
    rw [Anneal.Framework.StepWp.wpStepPred_succ_iff] at h
    let ⟨_, hAll⟩ := h
    have hZero := hAll 0 rfl
    cases hEval : evalStep p 0 s with
    | step s' =>
      rw [hEval] at hZero
      exact Or.inr ⟨s', ⟨0, rfl, hEval⟩,
        reachesDoneWithin_of_wpState (b := b) hZero⟩
    | done out =>
      rw [hEval] at hZero
      exact Or.inl ⟨out, ⟨0, rfl, hEval⟩, hZero⟩
    | fault _ =>
      rw [hEval] at hZero
      exact False.elim hZero

private theorem reachesDoneWithin_weaken {p : Program}
    {post₁ post₂ : TerminalOut → Prop} (hImp : ∀ out, post₁ out → post₂ out) :
    ∀ {b : Nat} {s : State},
      reachesDoneWithin p post₁ b s →
      reachesDoneWithin p post₂ b s
  | 0, _, h => False.elim h
  | _ + 1, _, h => by
    cases h with
    | inl hDone =>
      let ⟨out, hs, hp⟩ := hDone
      exact Or.inl ⟨out, hs, hImp out hp⟩
    | inr hStep =>
      let ⟨s', hs, hRest⟩ := hStep
      exact Or.inr ⟨s', hs, reachesDoneWithin_weaken hImp hRest⟩

private theorem execWithinSteps_of_wpProg {p : Program} {b : Nat} {q : Query}
    {ret : Val} {c : Trusted.Framework.FnContract Query Val CallerMemory}
    (hWp : wpProg p b q (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩))
    (hPost : c.postReturn q ret ⟨[]⟩) :
    ∃ s₀ : State,
      initState p q = .ok s₀ ∧
      reachesDoneWithin p (contractTerminalPost c q) b s₀ := by
  unfold wpProg at hWp
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at hWp
    exact False.elim hWp
  | ok s₀ =>
    rw [hInit] at hWp
    refine ⟨s₀, rfl,
      reachesDoneWithin_weaken ?_ (reachesDoneWithin_of_wpState hWp)⟩
    intro out hEq
    subst hEq
    exact hPost

private theorem satisfies_of_wp {defId : DefId} {body : Body}
    {gaps : List DisclosedGap} {e : MirVerifiedEntry}
    (hId : body.identity = e.identity)
    (hSig : bodyMatchesMirSignature body e.sig = true)
    (hRun : ∀ args : List Val, ValidEntryArgs body args →
      ∃ ret : Val,
        ValidMirReturnVal body ret ⟨[]⟩ ∧
        wpProg (entryProgForBody Captured.program defId) 2
          { args := args } (fun o => o = .returned ⟨ret, ⟨[]⟩⟩) ∧
        e.contract.postReturn { args := args } ret ⟨[]⟩)
    (hNonVac : NonVacuousEntry MirProfileV1 body
      (e.contract.effectiveBehaviorPre body.isUnsafe))
    (hReq : e.requireInhabited = true) :
    BodySatisfiesEntry MirProfileV1 Captured.program defId gaps body e := by
  refine ⟨rfl, hId, hSig, absurd_mem_nil, ?_, ?_,
    Or.inl ⟨hReq, hNonVac⟩⟩
  · intro q hDom _
    cases q with
    | mk args callerMem =>
      let ⟨valid, hMem⟩ := hDom
      dsimp at valid hMem
      subst hMem
      let ⟨_, _, hWp, _⟩ := hRun args valid
      exact (spec_and_behavior_of_wp_eq hWp).1
  · intro q hDom _
    cases q with
    | mk args callerMem =>
      let ⟨valid, hMem⟩ := hDom
      dsimp at valid hMem
      subst hMem
      let ⟨ret, hRetVal, hWp, hPost⟩ := hRun args valid
      have hSpec := spec_and_behavior_of_wp_eq hWp
      refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
      · intro r m ⟨out, hBehOut, hMap⟩
        have hEq := (hSpec.2.2.2 _ rfl).2 out hBehOut
        subst hEq
        injection hMap with hR hM
        subst hR hM
        exact ⟨hRetVal, hPost⟩
      · intro m ⟨out, hBehOut, hMap⟩
        have hEq := (hSpec.2.2.2 _ rfl).2 out hBehOut
        subst hEq
        cases hMap
      · intro m ⟨out, hBehOut, hMap⟩
        have hEq := (hSpec.2.2.2 _ rfl).2 out hBehOut
        subst hEq
        cases hMap

private def usizeZero : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩

private theorem body0_wp2 {v : Val} (valid : ValidEntryArgs Captured.body_0 [v])
    (hv : checkVal v (.int .isize false) = true) :
    wpProg (entryProgForBody Captured.program 0) 2 { args := [v] }
      (fun outcome => outcome = .returned ⟨v, ⟨[]⟩⟩) :=
  wpProg_of_execProg
    (exec2_of_copy_ret (defId := 0) rfl body0_adm valid
      (step_copy_isize Captured.body_0 rfl rfl rfl hv) rfl)

private theorem body1_wp2 {v : Val} (valid : ValidEntryArgs Captured.body_1 [v])
    (hv : checkVal v (.int .isize false) = true) :
    wpProg (entryProgForBody Captured.program 1) 2 { args := [v] }
      (fun outcome => outcome = .returned ⟨v, ⟨[]⟩⟩) :=
  wpProg_of_execProg
    (exec2_of_copy_ret (defId := 1) rfl body1_adm valid
      (step_copy_isize Captured.body_1 rfl rfl rfl hv) rfl)

private theorem body0_entry :
    BodySatisfiesEntry MirProfileV1 Captured.program 0 specs.gaps
      Captured.body_0
      { identity := fn0_id, sig := fn0_sig, contract := fn0_contract } :=
  satisfies_of_wp rfl rfl
    (fun args valid => by
      have hMatch : checkArgsMatch args [.int .isize false] = true := valid
      let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
      have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
      subst hEq; subst hNil
      exact ⟨v, ⟨hv, rfl⟩, body0_wp2 valid hv, rfl⟩)
    (Or.inl ⟨{ args := [usizeZero] }, ⟨rfl, rfl⟩,
      ⟨fun h => Bool.noConfusion h, True.intro⟩⟩)
    rfl

private theorem body1_entry :
    BodySatisfiesEntry MirProfileV1 Captured.program 1 specs.gaps
      Captured.body_1
      { identity := fn1_id, sig := fn1_sig, contract := fn1_contract } :=
  satisfies_of_wp rfl rfl
    (fun args valid => by
      have hMatch : checkArgsMatch args [.int .isize false] = true := valid
      let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
      have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
      subst hEq; subst hNil
      exact ⟨v, ⟨hv, rfl⟩, body1_wp2 valid hv, rfl⟩)
    (Or.inl ⟨{ args := [usizeZero] }, ⟨rfl, rfl⟩,
      ⟨fun h => Bool.noConfusion h, True.intro⟩⟩)
    rfl

theorem verify : Expected.claim := by
  dsimp only [Expected.claim, UnitMirEnvelopeTheoremV1, MirEnvelopeHolds,
    EnvelopeTheorem, mkEnvelope, AllSpecLaws, NoDupStrings, List.map,
    List.append, specs]
  refine ⟨rfl, (fun _ => List.Mem.head _),
    ⟨⟨nonEmpty_profile_id, rfl, ?_, rfl, (fun _ => List.Mem.head _),
        nonEmpty_oracle_id, ?_, (fun _ h => List.Mem.tail _ h)⟩,
      ?_, ?_, ?_, (fun _ h => by cases h),
      (fun _ h => by cases h), ?_⟩,
    True.intro, ?_, ?_, True.intro⟩
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact body0_adm
    | succ k =>
      cases k with
      | zero =>
        injection hGet with hEq
        subst hEq
        exact body1_adm
      | succ _ =>
        dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
        cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · refine ⟨ne_string_of_len_beq_false rfl, ?_,
      ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩⟩
    intro t hMem
    cases hMem with
    | head => exact ne_string_of_len_beq_false rfl
    | tail _ hNil => cases hNil
  · intro e hMem
    cases hMem with
    | head => exact ⟨0, Captured.body_0, rfl, body0_entry⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨1, Captured.body_1, rfl, body1_entry⟩
      | tail _ hNil => cases hNil
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ k =>
      cases k with
      | zero =>
        injection hGet with hEq
        subst hEq
        exact List.Mem.tail _ (List.Mem.head _)
      | succ _ =>
        dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
        cases hGet
  · refine ⟨0, Captured.body_0, rfl, rfl, rfl, fun args valid _ => ?_⟩
    have hMatch : checkArgsMatch args [.int .isize false] = true := valid
    let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
    have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
    subst hEq; subst hNil
    exact execWithinSteps_of_wpProg (c := fn0_contract)
      (body0_wp2 valid hv) rfl
  · refine ⟨1, Captured.body_1, rfl, rfl, rfl, fun args valid _ => ?_⟩
    have hMatch : checkArgsMatch args [.int .isize false] = true := valid
    let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
    have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
    subst hEq; subst hNil
    exact execWithinSteps_of_wpProg (c := fn1_contract)
      (body1_wp2 valid hv) rfl

end Proof
