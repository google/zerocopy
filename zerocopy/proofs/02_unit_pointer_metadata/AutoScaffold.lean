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

abbrev scafUsizeVal (n : BitVec 64) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n.toNat⟩

theorem valid_isize_word (n : BitVec 64) :
    checkVal (scafUsizeVal n) (.int .isize false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .isize
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

theorem validEntry_isize1 {body : Body}
    (h_tys :
      (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (n : BitVec 64) :
    ValidEntryArgs body [scafUsizeVal n] := by
  unfold ValidEntryArgs
  rw [h_tys]
  exact checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, valid_isize_word n, rfl⟩

theorem unit_const_1arg_ok {defId : DefId} {body : Body}
    {fuel : Nat} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [.unit])
    (h_runs : Runs body fuel [.unit] ret) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    ScafReturnsTotal Captured.program defId [.unit] ret := by
  refine ⟨bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_), ?_⟩
  · have hMatch : checkArgsMatch args [.unit] = true := by
      unfold ValidEntryArgs at valid
      rw [h_tys] at valid
      exact valid
    let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
    have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
    have hUnit : v = .unit := checkVal_unit_iff.mp hv
    subst hEq; subst hNil; subst hUnit
    exact (run_initial_success h_runs).1
  · have hArgs : ValidEntryArgs body [.unit] := by
      unfold ValidEntryArgs
      rw [h_tys]
      rfl
    exact total_of_runs h_body h_adm hArgs h_runs

theorem isize_const_1arg_ok {defId : DefId} {body : Body}
    {fuel : Nat} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys :
      (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (h_runs : ∀ v : Val, Runs body fuel [v] ret) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    ∀ a0 : BitVec 64,
      ScafReturnsTotal Captured.program defId [scafUsizeVal a0] ret := by
  refine ⟨bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_),
    fun a0 => total_of_runs h_body h_adm
      (validEntry_isize1 h_tys a0) (h_runs (scafUsizeVal a0))⟩
  have hMatch : checkArgsMatch args [.int .isize false] = true := by
    unfold ValidEntryArgs at valid
    rw [h_tys] at valid
    exact valid
  let ⟨v, rest, hEq, _, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact (run_initial_success (h_runs v)).1

def id_unit_from_elem_count : DefId := 0
abbrev body_unit_from_elem_count : Body := Captured.body_0
theorem get_unit_from_elem_count :
    Trusted.MirSemantics.getElem? Captured.program.bodies
      id_unit_from_elem_count = some body_unit_from_elem_count := rfl
theorem adm_unit_from_elem_count :
    BodyStaticAdmitted Captured.program body_unit_from_elem_count = true :=
  rfl
theorem runs_unit_from_elem_count (v : Val) :
    Runs body_unit_from_elem_count 3 [v]
      .unit := rfl
theorem ok_unit_from_elem_count :
    BodyVerified Captured.program id_unit_from_elem_count body_unit_from_elem_count
      (Spec.specs.safety body_unit_from_elem_count.identity) ∧
    ∀ a0 : BitVec 64,
      ScafReturnsTotal Captured.program id_unit_from_elem_count
        [scafUsizeVal a0] .unit :=
  isize_const_1arg_ok get_unit_from_elem_count adm_unit_from_elem_count
    rfl runs_unit_from_elem_count

def id_unit_to_elem_count : DefId := 1
abbrev body_unit_to_elem_count : Body := Captured.body_1
theorem get_unit_to_elem_count :
    Trusted.MirSemantics.getElem? Captured.program.bodies
      id_unit_to_elem_count = some body_unit_to_elem_count := rfl
theorem adm_unit_to_elem_count :
    BodyStaticAdmitted Captured.program body_unit_to_elem_count = true :=
  rfl
theorem runs_unit_to_elem_count :
    Runs body_unit_to_elem_count 3 [.unit]
      (scafUsizeVal (BitVec.ofNat 64 0)) := rfl
theorem ok_unit_to_elem_count :
    BodyVerified Captured.program id_unit_to_elem_count body_unit_to_elem_count
      (Spec.specs.safety body_unit_to_elem_count.identity) ∧
    ScafReturnsTotal Captured.program id_unit_to_elem_count [.unit]
      (scafUsizeVal (BitVec.ofNat 64 0)) :=
  unit_const_1arg_ok get_unit_to_elem_count adm_unit_to_elem_count
    rfl runs_unit_to_elem_count

theorem all_bodies_safe :
    ∀ (defId : DefId) (body : Body),
      Trusted.MirSemantics.getElem? Captured.program.bodies defId =
        some body →
      BodyVerified Captured.program defId body
        (Spec.specs.safety body.identity) := by
  have hAll :
      BodiesVerified Captured.program Spec.specs 0
        Captured.program.bodies :=
    ⟨ok_unit_from_elem_count.1, ok_unit_to_elem_count.1, True.intro⟩
  intro defId body found
  have hSub := bodiesVerified_getElem hAll defId body found
  rw [Nat.zero_add] at hSub
  exact hSub

end AutoScaffold
