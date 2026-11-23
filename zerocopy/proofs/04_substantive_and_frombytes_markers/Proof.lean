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

set_option maxRecDepth 4096

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem body0_adm : BodyStaticAdmitted Captured.program Captured.body_0 = true := rfl
private theorem body1_adm : BodyStaticAdmitted Captured.program Captured.body_1 = true := rfl
private theorem body2_adm : BodyStaticAdmitted Captured.program Captured.body_2 = true := rfl
private theorem body3_adm : BodyStaticAdmitted Captured.program Captured.body_3 = true := rfl
private theorem body4_adm : BodyStaticAdmitted Captured.program Captured.body_4 = true := rfl
private theorem body5_adm : BodyStaticAdmitted Captured.program Captured.body_5 = true := rfl
private theorem body6_adm : BodyStaticAdmitted Captured.program Captured.body_6 = true := rfl
private theorem body7_adm : BodyStaticAdmitted Captured.program Captured.body_7 = true := rfl
private theorem body8_adm : BodyStaticAdmitted Captured.program Captured.body_8 = true := rfl

private theorem body0_runs : Runs Captured.body_0 2 [] .unit := rfl
private theorem body1_runs (v : Val) : Runs Captured.body_1 2 [v] .unit := rfl
private theorem body2_runs : Runs Captured.body_2 2 [.unit] (Spec.usizeVal 0) := rfl
private theorem body5_runs : Runs Captured.body_5 2 [] .unit := rfl
private theorem body6_runs : Runs Captured.body_6 2 [] .unit := rfl
private theorem body7_runs : Runs Captured.body_7 2 [] .unit := rfl
private theorem body8_runs : Runs Captured.body_8 2 [] .unit := rfl

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

private theorem body3_executes {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    Executes Captured.body_3
      (mkState 0 0 (initLocalsLoop Captured.body_3 [v] 0 Captured.body_3.locals))
      v :=
  .next (step_copy_isize Captured.body_3 rfl rfl rfl hv) (.ret rfl)

private theorem body4_executes {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    Executes Captured.body_4
      (mkState 0 0 (initLocalsLoop Captured.body_4 [v] 0 Captured.body_4.locals))
      v :=
  .next (step_copy_isize Captured.body_4 rfl rfl rfl hv) (.ret rfl)

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

private theorem total_of_runs {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_runs : Runs body fuel args ret) :
    Spec.ReturnsTotal Captured.program defId args ret :=
  total_of_executes h_body h_adm h_args (run_executes h_runs)

private theorem unit0_safe_verified {defId : DefId} {body : Body}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [])
    (h_runs : Runs body 2 [] .unit) :
    BodyVerified Captured.program defId body (Spec.specs.safety body.identity) := by
  refine bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [] = true := by
    unfold ValidEntryArgs at valid
    rw [h_tys] at valid
    exact valid
  have hNil : args = [] := checkArgsMatch_nil_iff.mp hMatch
  subst hNil
  exact (run_initial_success h_runs).1

private theorem isize_copy_safe_verified {defId : DefId} {body : Body}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (h_exec : ∀ {v : Val}, checkVal v (.int .isize false) = true →
      Executes body (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) v) :
    BodyVerified Captured.program defId body (Spec.specs.safety body.identity) := by
  refine bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [.int .isize false] = true := by
    unfold ValidEntryArgs at valid
    rw [h_tys] at valid
    exact valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact executes_safe (h_exec hv)

private theorem body0_safe_verified :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) :=
  unit0_safe_verified rfl body0_adm rfl body0_runs

private theorem body1_safe_verified :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) := by
  refine bodyVerified_of_safe rfl body1_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, _, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact (run_initial_success (body1_runs v)).1

private theorem body2_safe_verified :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) := by
  refine bodyVerified_of_safe rfl body2_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [.unit] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  have hUnit : v = .unit := checkVal_unit_iff.mp hv
  subst hEq; subst hNil; subst hUnit
  exact (run_initial_success body2_runs).1

private theorem body3_safe_verified :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) :=
  isize_copy_safe_verified rfl body3_adm rfl body3_executes

private theorem body4_safe_verified :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) :=
  isize_copy_safe_verified rfl body4_adm rfl body4_executes

private theorem body5_safe_verified :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) :=
  unit0_safe_verified rfl body5_adm rfl body5_runs

private theorem body6_safe_verified :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) :=
  unit0_safe_verified rfl body6_adm rfl body6_runs

private theorem body7_safe_verified :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) :=
  unit0_safe_verified rfl body7_adm rfl body7_runs

private theorem body8_safe_verified :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) :=
  unit0_safe_verified rfl body8_adm rfl body8_runs

private theorem usize_valid (n : Spec.UsizeWord) :
    checkVal (Spec.usizeVal n) (.int .isize false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .isize
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

private theorem body0_total : Spec.ReturnsTotal Captured.program 0 [] .unit :=
  total_of_runs rfl body0_adm rfl body0_runs

private theorem body1_total (n : Spec.UsizeWord) :
    Spec.ReturnsTotal Captured.program 1 [Spec.usizeVal n] .unit := by
  have hArgs : ValidEntryArgs Captured.body_1 [Spec.usizeVal n] :=
    checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, usize_valid n, rfl⟩
  exact total_of_runs rfl body1_adm hArgs (body1_runs (Spec.usizeVal n))

private theorem body2_total :
    Spec.ReturnsTotal Captured.program 2 [.unit] (Spec.usizeVal 0) :=
  total_of_runs rfl body2_adm rfl body2_runs

private theorem body3_total (n : Spec.UsizeWord) :
    Spec.ReturnsTotal Captured.program 3 [Spec.usizeVal n] (Spec.usizeVal n) := by
  have hv := usize_valid n
  have hArgs : ValidEntryArgs Captured.body_3 [Spec.usizeVal n] :=
    checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, hv, rfl⟩
  exact total_of_executes rfl body3_adm hArgs (body3_executes hv)

private theorem body4_total (m : Spec.UsizeWord) :
    Spec.ReturnsTotal Captured.program 4 [Spec.usizeVal m] (Spec.usizeVal m) := by
  have hv := usize_valid m
  have hArgs : ValidEntryArgs Captured.body_4 [Spec.usizeVal m] :=
    checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, hv, rfl⟩
  exact total_of_executes rfl body4_adm hArgs (body4_executes hv)

private theorem body5_total : Spec.ReturnsTotal Captured.program 5 [] .unit :=
  total_of_runs rfl body5_adm rfl body5_runs

private theorem body6_total : Spec.ReturnsTotal Captured.program 6 [] .unit :=
  total_of_runs rfl body6_adm rfl body6_runs

private theorem body7_total : Spec.ReturnsTotal Captured.program 7 [] .unit :=
  total_of_runs rfl body7_adm rfl body7_runs

private theorem body8_total : Spec.ReturnsTotal Captured.program 8 [] .unit :=
  total_of_runs rfl body8_adm rfl body8_runs

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Spec.specs 0 Captured.program.bodies :=
      ⟨body0_safe_verified, body1_safe_verified, body2_safe_verified,
       body3_safe_verified, body4_safe_verified, body5_safe_verified,
       body6_safe_verified, body7_safe_verified, body8_safe_verified, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨rfl,
      ⟨0, Captured.body_0, rfl, rfl, rfl, rfl, body0_total⟩,
      ⟨1, Captured.body_1, 2, Captured.body_2,
        rfl, rfl, rfl, rfl, rfl, rfl, body1_total, body2_total⟩,
      ⟨3, Captured.body_3, 4, Captured.body_4,
        rfl, rfl, rfl, rfl, rfl, rfl, body3_total, body4_total⟩,
      ⟨5, Captured.body_5, rfl, rfl, rfl, rfl, body5_total⟩,
      ⟨6, Captured.body_6, rfl, rfl, rfl, rfl, body6_total⟩,
      ⟨7, Captured.body_7, rfl, rfl, rfl, rfl, body7_total⟩,
      ⟨8, Captured.body_8, rfl, rfl, rfl, rfl, body8_total⟩⟩

end Proof
