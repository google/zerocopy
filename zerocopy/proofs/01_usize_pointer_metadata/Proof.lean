-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.Framework.StepWp Anneal.MirWp

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
            { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := l2 }],
              callerMem := ⟨[]⟩, mem := m2 })
    (hv : checkVal v (.int .isize false) = true) :
    evalStep (bodyProg body) 0
      (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) =
    .step (mkState 0 1 [.immediate (some v), .immediate (some v)]) := by
  rw [hLoc, hStep, hRval]
  dsimp only
  rw [writePlace_isize hv]
  rfl

private theorem body0_executes {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    Executes Captured.body_0
      (mkState 0 0 (initLocalsLoop Captured.body_0 [v] 0 Captured.body_0.locals))
      v :=
  .next (step_copy_isize Captured.body_0 rfl rfl rfl hv) (.ret rfl)

private theorem body1_executes {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    Executes Captured.body_1
      (mkState 0 0 (initLocalsLoop Captured.body_1 [v] 0 Captured.body_1.locals))
      v :=
  .next (step_copy_isize Captured.body_1 rfl rfl rfl hv) (.ret rfl)

/-- Exact 2-step `execProg` witness (`1` `Copy` step + `1` `Return` step) from
`step_copy_isize` and `.ret rfl`. -/
private theorem exec2_of_copy_ret {defId : DefId} {body : Body} {v : Val}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
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
  refine (execOutcomeState_entryProg_iff h_body (isSingleFrame0_mkState 0 0 _)).mpr ?_
  have hDone : execState (bodyProg body) 1
      (mkState 0 1 [.immediate (some v), .immediate (some v)])
      (fun outcome => outcome = .returned ⟨v, ⟨[]⟩⟩) := by
    dsimp only [execState, execOutcomeState, execStepOutcome]
    rw [execStepPred_succ_iff, h_step2]
  dsimp only [execState, execOutcomeState, execStepOutcome]
  rw [execStepPred_succ_iff, h_step1]
  exact hDone

/-- Mirror of `Anneal.StepBound.ReachesDoneWithin` (`@Nat.rec` form,
definitionally equal to the generated specification's `reachesDoneWithin`). -/
private noncomputable def reachesDoneWithinLocal (p : Program)
    (post : TerminalOut → Prop) : Nat → State → Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih s =>
      (∃ out : TerminalOut, Step p s (.done out) ∧ post out) ∨
      (∃ s' : State, Step p s (.step s') ∧ ih s'))

/-- Bridge `wpState p b s post` (`Anneal.MirWp`) to `reachesDoneWithinLocal`,
matching `Anneal.StepBound.reachesDoneWithin_iff_wpState.mpr`. -/
private theorem reachesDoneWithin_of_wpState {p : Program}
    {post : TerminalOut → Prop} :
    ∀ {b : Nat} {s : State},
      wpState p b s post → reachesDoneWithinLocal p post b s
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
      reachesDoneWithinLocal p post₁ b s →
      reachesDoneWithinLocal p post₂ b s
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
    {ret : Val} {c : FnContract}
    (hWp : wpProg p b q (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩))
    (hPost : c.postReturn q ⟨ret, ⟨[]⟩⟩) :
    ∃ s₀ : State,
      initState p q = .ok s₀ ∧
      reachesDoneWithinLocal p
        (fun out =>
          match out with
          | .returned retOut => c.postReturn q retOut
          | .unwound uwMem => c.effects.noUnwind = false ∧ c.postUnwind q uwMem
          | .aborted _ => False)
        b s₀ := by
  unfold wpProg at hWp
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at hWp
    exact False.elim hWp
  | ok s₀ =>
    rw [hInit] at hWp
    refine ⟨s₀, rfl, reachesDoneWithin_weaken ?_ (reachesDoneWithin_of_wpState hWp)⟩
    intro out hEq
    subst hEq
    exact hPost

private theorem obligations_of_wp {defId : DefId} {args : List Val}
    {ret : Val} {fuel : Nat} {c : FnContract} {isUnsafe : Bool}
    (h_wp : wpProg (entryProgForBody Captured.program defId) fuel { args := args }
      (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩))
    (h_post : c.postReturn { args := args } ⟨ret, ⟨[]⟩⟩) :
    (c.effectiveSafetyPre isUnsafe { args := args } →
      WellFormed (entryProgForBody Captured.program defId) { args := args }) ∧
    (c.effectiveBehaviorPre isUnsafe { args := args } →
      (∀ out : TerminalOut,
        Behavior (entryProgForBody Captured.program defId) { args := args } out →
        match out with
        | .returned retOut => c.postReturn { args := args } retOut
        | .unwound uwMem =>
          c.effects.noUnwind = false ∧ c.postUnwind { args := args } uwMem
        | .aborted _ => False) ∧
      (c.effects.terminates = true →
        ¬ Diverges (entryProgForBody Captured.program defId) { args := args })) := by
  have h := spec_and_behavior_of_wp_eq h_wp
  refine ⟨fun _ => h.1, fun _ => ⟨fun out hOut => ?_, fun _ => h.2.2.1⟩⟩
  have hEq := (h.2.2.2 (fun o => o = .returned ⟨ret, ⟨[]⟩⟩) rfl).2 out hOut
  subst hEq
  exact h_post

private theorem body0_safe_verified :
    BodyVerified Captured.program 0 Captured.body_0
      (Specs.zerocopy.zc01_usize_pointer_metadata.specs.safety Captured.body_0.identity) := by
  refine bodyVerified_of_safe rfl body0_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact executes_safe (body0_executes hv)

private theorem body1_safe_verified :
    BodyVerified Captured.program 1 Captured.body_1
      (Specs.zerocopy.zc01_usize_pointer_metadata.specs.safety Captured.body_1.identity) := by
  refine bodyVerified_of_safe rfl body1_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact executes_safe (body1_executes hv)

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

private theorem body0_contract :
    BodyContractSatisfied Captured.program 0 Captured.body_0 Specs.zerocopy.zc01_usize_pointer_metadata.fn0_contract := by
  refine ⟨rfl, body0_adm, fun args valid => ?_⟩
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact obligations_of_wp (body0_wp2 valid hv) rfl

private theorem body1_contract :
    BodyContractSatisfied Captured.program 1 Captured.body_1 Specs.zerocopy.zc01_usize_pointer_metadata.fn1_contract := by
  refine ⟨rfl, body1_adm, fun args valid => ?_⟩
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact obligations_of_wp (body1_wp2 valid hv) rfl

private theorem body0_inhabited :
    ContractPreInhabited Captured.body_0 Specs.zerocopy.zc01_usize_pointer_metadata.fn0_contract :=
  ⟨[usizeZero], rfl, fun _ => trivial, trivial⟩

private theorem body1_inhabited :
    ContractPreInhabited Captured.body_1 Specs.zerocopy.zc01_usize_pointer_metadata.fn1_contract :=
  ⟨[usizeZero], rfl, fun _ => trivial, trivial⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Specs.zerocopy.zc01_usize_pointer_metadata.specs 0 Captured.program.bodies :=
      ⟨body0_safe_verified, body1_safe_verified, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨⟨rfl,
      ⟨0, Captured.body_0, rfl, rfl, rfl, body0_contract, fun _ => body0_inhabited⟩,
      ⟨1, Captured.body_1, rfl, rfl, rfl, body1_contract, fun _ => body1_inhabited⟩,
      trivial⟩, ?_, ?_⟩
    · refine ⟨0, Captured.body_0, rfl, rfl, rfl, fun args valid _ => ?_⟩
      have hMatch : checkArgsMatch args [.int .isize false] = true := valid
      let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
      have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
      subst hEq; subst hNil
      exact execWithinSteps_of_wpProg (c := Specs.zerocopy.zc01_usize_pointer_metadata.fn0_contract) (body0_wp2 valid hv) rfl
    · refine ⟨1, Captured.body_1, rfl, rfl, rfl, fun args valid _ => ?_⟩
      have hMatch : checkArgsMatch args [.int .isize false] = true := valid
      let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
      have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
      subst hEq; subst hNil
      exact execWithinSteps_of_wpProg (c := Specs.zerocopy.zc01_usize_pointer_metadata.fn1_contract) (body1_wp2 valid hv) rfl

end Proof
