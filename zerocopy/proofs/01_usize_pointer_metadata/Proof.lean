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

private theorem total_of_executes {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_exec : Executes body (mkState 0 0 (initLocalsLoop body args 0 body.locals)) ret) :
    Spec.ReturnsTotal Captured.program defId args ret := by
  let ⟨fuel, h_execState⟩ := executes_iff_wpState.mp h_exec
  have h_execProg :
      execProg (entryProgForBody Captured.program defId) fuel { args := args }
        (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_entryProgForBody h_body h_adm h_args]
    exact (execOutcomeState_entryProg_iff h_body (isSingleFrame0_mkState 0 0 _)).mpr h_execState
  have h_all := spec_and_behavior_of_wp_eq (wpProg_of_execProg h_execProg)
  exact ⟨h_all.2.2.2 _ rfl, h_all.2.2.1, h_all.2.1⟩

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

private theorem usize_valid (n : Spec.UsizeWord) :
    checkVal (Spec.usizeVal n) (.int .isize false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .isize
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

private theorem body0_total (n : Spec.UsizeWord) :
    Spec.ReturnsTotal Captured.program 0 [Spec.usizeVal n] (Spec.usizeVal n) := by
  have hv := usize_valid n
  have hArgs : ValidEntryArgs Captured.body_0 [Spec.usizeVal n] :=
    checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, hv, rfl⟩
  exact total_of_executes rfl body0_adm hArgs (body0_executes hv)

private theorem body1_total (m : Spec.UsizeWord) :
    Spec.ReturnsTotal Captured.program 1 [Spec.usizeVal m] (Spec.usizeVal m) := by
  have hv := usize_valid m
  have hArgs : ValidEntryArgs Captured.body_1 [Spec.usizeVal m] :=
    checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, hv, rfl⟩
  exact total_of_executes rfl body1_adm hArgs (body1_executes hv)

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Spec.specs 0 Captured.program.bodies :=
      ⟨body0_safe_verified, body1_safe_verified, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨rfl, 0, Captured.body_0, 1, Captured.body_1,
      rfl, rfl, rfl, rfl, rfl, rfl,
      body0_total, body1_total,
      (fun n => ⟨n, body0_total n, body1_total n⟩),
      (fun m => ⟨m, body1_total m, body0_total m⟩)⟩

end Proof
