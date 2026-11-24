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

namespace AutoScaffold

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

abbrev ScafReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

theorem ok_of_executes {p : Program} {d : DefId} {b : Body}
    {args : List Val} {ret : Val}
    (hb : Trusted.MirSemantics.getElem? p.bodies d = some b)
    (hadm : BodyStaticAdmitted p b = true)
    (hargs : ValidEntryArgs b args)
    (hexec :
      Executes b (mkState 0 0 (initLocalsLoop b args 0 b.locals)) ret) :
    WellFormed (entryProgForBody p d) { args := args } ∧
    ScafReturnsTotal p d args ret :=
  Exists.elim (executes_iff_wpState.mp hexec) fun _ hruns =>
    let h := spec_and_behavior_of_wp_eq (wpProg_of_execProg (by
      unfold execProg
      rw [initState_entryProgForBody hb hadm hargs]
      exact (execOutcomeState_entryProg_iff hb
        (isSingleFrame0_mkState 0 0 _)).mpr hruns))
    ⟨h.1, h.2.2.2 _ rfl, h.2.2.1, h.2.1⟩

theorem total_of_executes {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_exec :
      Executes body
        (mkState 0 0 (initLocalsLoop body args 0 body.locals)) ret) :
    ScafReturnsTotal Captured.program defId args ret :=
  (ok_of_executes h_body h_adm h_args h_exec).2

theorem total_of_runs {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_runs : Runs body fuel args ret) :
    ScafReturnsTotal Captured.program defId args ret :=
  total_of_executes h_body h_adm h_args (run_executes h_runs)

theorem unit0_ok {defId : DefId} {body : Body} {fuel : Nat}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [])
    (h_runs : Runs body fuel [] .unit) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    ScafReturnsTotal Captured.program defId [] .unit := by
  refine ⟨bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_), ?_⟩
  · have hMatch : checkArgsMatch args [] = true := by
      unfold ValidEntryArgs at valid
      rw [h_tys] at valid
      exact valid
    have hNil : args = [] := checkArgsMatch_nil_iff.mp hMatch
    subst hNil
    exact (run_initial_success h_runs).1
  · have hArgs : ValidEntryArgs body [] := by
      unfold ValidEntryArgs
      rw [h_tys]
      rfl
    exact total_of_runs h_body h_adm hArgs h_runs

def id_unsafe_macro : DefId := 0
abbrev body_unsafe_macro : Body := Captured.body_0
theorem get_unsafe_macro :
    Trusted.MirSemantics.getElem? Captured.program.bodies
      id_unsafe_macro = some body_unsafe_macro := rfl
theorem adm_unsafe_macro :
    BodyStaticAdmitted Captured.program body_unsafe_macro = true :=
  rfl
theorem runs_unsafe_macro :
    Runs body_unsafe_macro 3 [] .unit := rfl
theorem ok_unsafe_macro :
    BodyVerified Captured.program id_unsafe_macro body_unsafe_macro
      (Spec.specs.safety body_unsafe_macro.identity) ∧
    ScafReturnsTotal Captured.program id_unsafe_macro [] .unit :=
  unit0_ok get_unsafe_macro adm_unsafe_macro
    rfl runs_unsafe_macro

theorem all_bodies_safe :
    ∀ (defId : DefId) (body : Body),
      Trusted.MirSemantics.getElem? Captured.program.bodies defId =
        some body →
      BodyVerified Captured.program defId body
        (Spec.specs.safety body.identity) := by
  have hAll :
      BodiesVerified Captured.program Spec.specs 0
        Captured.program.bodies :=
    ⟨ok_unsafe_macro.1, True.intro⟩
  intro defId body found
  have hSub := bodiesVerified_getElem hAll defId body found
  rw [Nat.zero_add] at hSub
  exact hSub

end AutoScaffold
