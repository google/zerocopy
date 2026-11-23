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

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

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

/-- An `Executes` certificate from the entry state yields an exact-outcome
`wpProg` proof. -/
private theorem wp_of_executes {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_exec : Executes body (mkState 0 0 (initLocalsLoop body args 0 body.locals)) ret) :
    ∃ fuel, wpProg (entryProgForBody Captured.program defId) fuel { args := args }
      (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩) := by
  let ⟨fuel, h_execState⟩ := executes_iff_wpState.mp h_exec
  have h_execProg :
      execProg (entryProgForBody Captured.program defId) fuel { args := args }
        (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_entryProgForBody h_body h_adm h_args]
    exact (execOutcomeState_entryProg_iff h_body (isSingleFrame0_mkState 0 0 _)).mpr h_execState
  exact ⟨fuel, wpProg_of_execProg h_execProg⟩

/-- The per-argument obligations of `BodyContractSatisfied`, discharged from an
exact-outcome `wpProg` proof whose unique return satisfies `postReturn`. -/
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
      (Spec.specs.safety Captured.body_0.identity) := by
  refine bodyVerified_of_safe rfl body0_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact executes_safe (body0_executes hv)

private theorem body1_safe_verified :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) := by
  refine bodyVerified_of_safe rfl body1_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact executes_safe (body1_executes hv)

/-- `0usize`, a witness `usize` argument for the non-vacuity obligations. -/
private def usizeZero : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩

private theorem body0_contract :
    BodyContractSatisfied Captured.program 0 Captured.body_0 Spec.fn0_contract := by
  refine ⟨rfl, body0_adm, fun args valid => ?_⟩
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  let ⟨_, h_wp⟩ := wp_of_executes (defId := 0) rfl body0_adm valid (body0_executes hv)
  exact obligations_of_wp h_wp rfl

private theorem body1_contract :
    BodyContractSatisfied Captured.program 1 Captured.body_1 Spec.fn1_contract := by
  refine ⟨rfl, body1_adm, fun args valid => ?_⟩
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  let ⟨_, h_wp⟩ := wp_of_executes (defId := 1) rfl body1_adm valid (body1_executes hv)
  exact obligations_of_wp h_wp rfl

private theorem body0_inhabited :
    ContractPreInhabited Captured.body_0 Spec.fn0_contract :=
  ⟨[usizeZero], rfl, fun _ => trivial, trivial⟩

private theorem body1_inhabited :
    ContractPreInhabited Captured.body_1 Spec.fn1_contract :=
  ⟨[usizeZero], rfl, fun _ => trivial, trivial⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Spec.specs 0 Captured.program.bodies :=
      ⟨body0_safe_verified, body1_safe_verified, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · exact ⟨rfl, ⟨0, Captured.body_0, rfl, rfl, rfl, body0_contract, fun _ => body0_inhabited⟩,
      ⟨1, Captured.body_1, rfl, rfl, rfl, body1_contract, fun _ => body1_inhabited⟩,
      trivial⟩

end Proof
