-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem body0_adm :
    BodyStaticAdmitted Captured.program Captured.body_0 = true := rfl

private theorem body0_runs :
    Runs Captured.body_0 2 [] .unit := rfl

private theorem total_of_runs {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_runs : Runs body fuel args ret) :
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
  have hMatch : checkArgsMatch args [] = true := valid
  have hNil : args = [] := checkArgsMatch_nil_iff.mp hMatch
  subst hNil
  exact (run_initial_success body0_runs).1

private theorem body0_total :
    Spec.ReturnsTotal Captured.program 0 [] .unit :=
  total_of_runs rfl body0_adm rfl body0_runs

public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Spec.specs 0 Captured.program.bodies :=
      ⟨body0_safe_verified, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · exact ⟨rfl, 0, Captured.body_0, rfl, rfl, rfl, rfl, body0_total⟩

end Proof
