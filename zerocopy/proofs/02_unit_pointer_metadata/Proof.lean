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

private theorem body0_runs (v : Val) :
    Runs Captured.program.targetEndian Captured.body_0 2 [v] .unit := rfl

private theorem body1_runs :
    Runs Captured.program.targetEndian
      Captured.body_1 2 [.unit] (Spec.usizeVal 0) := rfl

private theorem total_of_runs {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_runs : Runs Captured.program.targetEndian body fuel args ret) :
    Spec.ReturnsTotal Captured.program defId args ret := by
  have h_execProg :
      execProg (entryProgForBody Captured.program defId) fuel { args := args }
        (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_entryProgForBody h_body h_adm h_args]
    exact (execOutcomeState_entryProg_iff h_body (isSingleFrame0_mkState 0 0 _)).mpr h_runs
  have h_all := spec_and_behavior_of_wp_eq (wpProg_of_execProg h_execProg)
  exact ⟨h_all.2.2.2 _ rfl, h_all.2.2.1, h_all.2.1⟩

private theorem body0_safe_verified :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) := by
  refine bodyVerified_of_safe rfl body0_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [.int .isize false] = true := valid
  let ⟨v, rest, hEq, _, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact (run_initial_success (body0_runs v)).1

private theorem body1_safe_verified :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) := by
  refine bodyVerified_of_safe rfl body1_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [.unit] = true := valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  have hUnit : v = .unit := checkVal_unit_iff.mp hv
  subst hEq; subst hNil; subst hUnit
  exact (run_initial_success body1_runs).1

private theorem usize_valid (n : Spec.UsizeWord) :
    checkVal (Spec.usizeVal n) (.int .isize false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .isize
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

private theorem body0_total (n : Spec.UsizeWord) :
    Spec.ReturnsTotal Captured.program 0 [Spec.usizeVal n] .unit := by
  have hArgs : ValidEntryArgs Captured.body_0 [Spec.usizeVal n] :=
    checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, usize_valid n, rfl⟩
  exact total_of_runs rfl body0_adm hArgs (body0_runs (Spec.usizeVal n))

private theorem body1_total :
    Spec.ReturnsTotal Captured.program 1 [.unit] (Spec.usizeVal 0) :=
  total_of_runs rfl body1_adm rfl body1_runs

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
      ⟨body1_total, body0_total 0⟩,
      (fun n => ⟨body0_total n, body1_total⟩)⟩

end Proof
