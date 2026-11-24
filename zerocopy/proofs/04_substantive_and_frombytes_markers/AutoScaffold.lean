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

def EvalAssignIsizeWith (body : Body) (s : State)
    (overrideVal : Val) (next : State) : Prop :=
  match s.frames with
  | [frame] =>
    match Nat.beq frame.defId 0 with
    | false => False
    | true =>
      match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => False
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some (.assign dst rvalue) =>
          match dst.projection.isEmpty with
          | false => False
          | true =>
            match Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => False
            | some dstTy =>
              match MirTy.beq dstTy (.int .isize false) with
              | false => False
              | true =>
                match evalRvalue body.locals frame.locals s.mem
                    dstTy rvalue with
                | .error _ => False
                | .ok (_, localsAfterRval, memAfterRval) =>
                  match Trusted.MirSemantics.getElem?
                      localsAfterRval dst.localId with
                  | some (.immediate _) =>
                    match setElem? localsAfterRval dst.localId
                        (.immediate (some overrideVal)) with
                    | some localsAfterWrite =>
                      (.step {
                        frames := [{
                          frame with
                          stmtIdx := frame.stmtIdx + 1
                          locals := localsAfterWrite
                        }]
                        callerMem := s.callerMem
                        mem := memAfterRval
                      } : StepResult State TerminalOut) = .step next
                    | none => False
                  | _ => False
        | _ => False
  | _ => False

theorem step_isizeVal {body : Body} {s next : State} {v : Val}
    (hv : checkVal v (.int .isize false) = true)
    (h_val : EvalAssignVal body s v)
    (h_next : EvalAssignIsizeWith body s v next) :
    evalStep (bodyProg body) 0 s = .step next := by
  unfold EvalAssignVal at h_val
  unfold EvalAssignIsizeWith at h_next
  unfold bodyProg evalStep
  cases h_fr : s.frames with
  | nil => rw [h_fr] at h_next; cases h_next
  | cons frame rest =>
    cases rest with
    | cons _ _ => rw [h_fr] at h_next; cases h_next
    | nil =>
      rw [h_fr] at h_val h_next
      dsimp only at h_val h_next ⊢
      cases h_def : Nat.beq frame.defId 0 with
      | false => rw [h_def] at h_next; cases h_next
      | true =>
        rw [h_def] at h_next
        dsimp only at h_next
        rw [Nat.eq_of_beq_eq_true h_def]
        rw [show Trusted.MirSemantics.getElem? [body] 0 = some body from rfl]
        dsimp only
        cases h_bb :
            Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rw [h_bb] at h_next; cases h_next
        | some bb =>
          rw [h_bb] at h_val h_next
          dsimp only at h_val h_next ⊢
          cases h_st :
              Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | none => rw [h_st] at h_next; cases h_next
          | some stmt =>
            rw [h_st] at h_val h_next
            dsimp only
            cases stmt with
            | nop | storageLive _ | storageDead _ | unsupported =>
              cases h_next
            | assign dst rvalue =>
              dsimp only at h_val h_next
              unfold evalStatement
              dsimp only
              cases h_proj : dst.projection.isEmpty with
              | false => rw [h_proj] at h_next; cases h_next
              | true =>
                rw [h_proj] at h_next
                rw [ite_bool_false (rfl : (!true) = false)]
                dsimp only at h_next
                cases h_dst :
                    Trusted.MirSemantics.getElem? body.locals dst.localId with
                | none => rw [h_dst] at h_next; cases h_next
                | some dstTy =>
                  rw [h_dst] at h_val h_next
                  dsimp only at h_val h_next ⊢
                  cases h_ty : MirTy.beq dstTy (.int .isize false) with
                  | false => rw [h_ty] at h_next; cases h_next
                  | true =>
                    rw [h_ty] at h_next
                    dsimp only at h_next
                    have h_ty_eq := MirTy.beq_iff.mp h_ty
                    subst h_ty_eq
                    cases h_rv : evalRvalue body.locals frame.locals s.mem
                        (.int .isize false) rvalue with
                    | error _ => rw [h_rv] at h_val; cases h_val
                    | ok triple =>
                      cases triple with
                      | mk v_rv rest_rv =>
                        cases rest_rv with
                        | mk localsAfterRval memAfterRval =>
                          rw [h_rv] at h_val h_next
                          dsimp only at h_val h_next ⊢
                          rw [h_val]
                          unfold writePlace
                          rw [ite_bool_false (by rw [hv]; rfl)]
                          cases h_slot : Trusted.MirSemantics.getElem?
                              localsAfterRval dst.localId with
                          | none => rw [h_slot] at h_next; cases h_next
                          | some slot =>
                            rw [h_slot] at h_next
                            cases slot with
                            | dead | indirect _ => cases h_next
                            | immediate _ =>
                              dsimp only at h_next ⊢
                              cases h_set : setElem? localsAfterRval
                                  dst.localId (.immediate (some v)) with
                              | none => rw [h_set] at h_next; cases h_next
                              | some localsAfterWrite =>
                                rw [h_set] at h_next
                                exact h_next

theorem isize_id_1arg_ok {defId : DefId} {body : Body}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys :
      (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (h_exec : ∀ {v : Val}, checkVal v (.int .isize false) = true →
      Executes body
        (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) v) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    ∀ a0 : BitVec 64,
      ScafReturnsTotal Captured.program defId
        [scafUsizeVal a0] (scafUsizeVal a0) := by
  refine ⟨bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_),
    fun a0 => total_of_executes h_body h_adm
      (validEntry_isize1 h_tys a0) (h_exec (valid_isize_word a0))⟩
  have hMatch : checkArgsMatch args [.int .isize false] = true := by
    unfold ValidEntryArgs at valid
    rw [h_tys] at valid
    exact valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact executes_safe (h_exec hv)

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

def id_unit_from_elem_count : DefId := 1
abbrev body_unit_from_elem_count : Body := Captured.body_1
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

def id_unit_to_elem_count : DefId := 2
abbrev body_unit_to_elem_count : Body := Captured.body_2
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

def id_usize_from_elem_count : DefId := 3
abbrev body_usize_from_elem_count : Body := Captured.body_3
theorem get_usize_from_elem_count :
    Trusted.MirSemantics.getElem? Captured.program.bodies
      id_usize_from_elem_count = some body_usize_from_elem_count := rfl
theorem adm_usize_from_elem_count :
    BodyStaticAdmitted Captured.program body_usize_from_elem_count = true :=
  rfl
private theorem exec_usize_from_elem_count {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    Executes body_usize_from_elem_count
      (mkState 0 0
        (initLocalsLoop body_usize_from_elem_count [v] 0 body_usize_from_elem_count.locals))
      v :=
  let v_a0 := some v
  let s1 := mkState 0 1 [.immediate v_a0, .immediate v_a0]
  (.next (next := s1) (step_isizeVal hv rfl rfl)
    (.ret rfl))
theorem ok_usize_from_elem_count :
    BodyVerified Captured.program id_usize_from_elem_count body_usize_from_elem_count
      (Spec.specs.safety body_usize_from_elem_count.identity) ∧
    ∀ a0 : BitVec 64,
      ScafReturnsTotal Captured.program id_usize_from_elem_count
        [scafUsizeVal a0] (scafUsizeVal a0) :=
  isize_id_1arg_ok get_usize_from_elem_count adm_usize_from_elem_count
    rfl exec_usize_from_elem_count

def id_usize_to_elem_count : DefId := 4
abbrev body_usize_to_elem_count : Body := Captured.body_4
theorem get_usize_to_elem_count :
    Trusted.MirSemantics.getElem? Captured.program.bodies
      id_usize_to_elem_count = some body_usize_to_elem_count := rfl
theorem adm_usize_to_elem_count :
    BodyStaticAdmitted Captured.program body_usize_to_elem_count = true :=
  rfl
private theorem exec_usize_to_elem_count {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    Executes body_usize_to_elem_count
      (mkState 0 0
        (initLocalsLoop body_usize_to_elem_count [v] 0 body_usize_to_elem_count.locals))
      v :=
  let v_a0 := some v
  let s1 := mkState 0 1 [.immediate v_a0, .immediate v_a0]
  (.next (next := s1) (step_isizeVal hv rfl rfl)
    (.ret rfl))
theorem ok_usize_to_elem_count :
    BodyVerified Captured.program id_usize_to_elem_count body_usize_to_elem_count
      (Spec.specs.safety body_usize_to_elem_count.identity) ∧
    ∀ a0 : BitVec 64,
      ScafReturnsTotal Captured.program id_usize_to_elem_count
        [scafUsizeVal a0] (scafUsizeVal a0) :=
  isize_id_1arg_ok get_usize_to_elem_count adm_usize_to_elem_count
    rfl exec_usize_to_elem_count

def id_u8_Immutable_marker : DefId := 5
abbrev body_u8_Immutable_marker : Body := Captured.body_5
theorem get_u8_Immutable_marker :
    Trusted.MirSemantics.getElem? Captured.program.bodies
      id_u8_Immutable_marker = some body_u8_Immutable_marker := rfl
theorem adm_u8_Immutable_marker :
    BodyStaticAdmitted Captured.program body_u8_Immutable_marker = true :=
  rfl
theorem runs_u8_Immutable_marker :
    Runs body_u8_Immutable_marker 3 [] .unit := rfl
theorem ok_u8_Immutable_marker :
    BodyVerified Captured.program id_u8_Immutable_marker body_u8_Immutable_marker
      (Spec.specs.safety body_u8_Immutable_marker.identity) ∧
    ScafReturnsTotal Captured.program id_u8_Immutable_marker [] .unit :=
  unit0_ok get_u8_Immutable_marker adm_u8_Immutable_marker
    rfl runs_u8_Immutable_marker

def id_u8_TryFromBytes_marker : DefId := 6
abbrev body_u8_TryFromBytes_marker : Body := Captured.body_6
theorem get_u8_TryFromBytes_marker :
    Trusted.MirSemantics.getElem? Captured.program.bodies
      id_u8_TryFromBytes_marker = some body_u8_TryFromBytes_marker := rfl
theorem adm_u8_TryFromBytes_marker :
    BodyStaticAdmitted Captured.program body_u8_TryFromBytes_marker = true :=
  rfl
theorem runs_u8_TryFromBytes_marker :
    Runs body_u8_TryFromBytes_marker 3 [] .unit := rfl
theorem ok_u8_TryFromBytes_marker :
    BodyVerified Captured.program id_u8_TryFromBytes_marker body_u8_TryFromBytes_marker
      (Spec.specs.safety body_u8_TryFromBytes_marker.identity) ∧
    ScafReturnsTotal Captured.program id_u8_TryFromBytes_marker [] .unit :=
  unit0_ok get_u8_TryFromBytes_marker adm_u8_TryFromBytes_marker
    rfl runs_u8_TryFromBytes_marker

def id_u8_FromZeros_marker : DefId := 7
abbrev body_u8_FromZeros_marker : Body := Captured.body_7
theorem get_u8_FromZeros_marker :
    Trusted.MirSemantics.getElem? Captured.program.bodies
      id_u8_FromZeros_marker = some body_u8_FromZeros_marker := rfl
theorem adm_u8_FromZeros_marker :
    BodyStaticAdmitted Captured.program body_u8_FromZeros_marker = true :=
  rfl
theorem runs_u8_FromZeros_marker :
    Runs body_u8_FromZeros_marker 3 [] .unit := rfl
theorem ok_u8_FromZeros_marker :
    BodyVerified Captured.program id_u8_FromZeros_marker body_u8_FromZeros_marker
      (Spec.specs.safety body_u8_FromZeros_marker.identity) ∧
    ScafReturnsTotal Captured.program id_u8_FromZeros_marker [] .unit :=
  unit0_ok get_u8_FromZeros_marker adm_u8_FromZeros_marker
    rfl runs_u8_FromZeros_marker

def id_u8_FromBytes_marker : DefId := 8
abbrev body_u8_FromBytes_marker : Body := Captured.body_8
theorem get_u8_FromBytes_marker :
    Trusted.MirSemantics.getElem? Captured.program.bodies
      id_u8_FromBytes_marker = some body_u8_FromBytes_marker := rfl
theorem adm_u8_FromBytes_marker :
    BodyStaticAdmitted Captured.program body_u8_FromBytes_marker = true :=
  rfl
theorem runs_u8_FromBytes_marker :
    Runs body_u8_FromBytes_marker 3 [] .unit := rfl
theorem ok_u8_FromBytes_marker :
    BodyVerified Captured.program id_u8_FromBytes_marker body_u8_FromBytes_marker
      (Spec.specs.safety body_u8_FromBytes_marker.identity) ∧
    ScafReturnsTotal Captured.program id_u8_FromBytes_marker [] .unit :=
  unit0_ok get_u8_FromBytes_marker adm_u8_FromBytes_marker
    rfl runs_u8_FromBytes_marker

theorem all_bodies_safe :
    ∀ (defId : DefId) (body : Body),
      Trusted.MirSemantics.getElem? Captured.program.bodies defId =
        some body →
      BodyVerified Captured.program defId body
        (Spec.specs.safety body.identity) := by
  have hAll :
      BodiesVerified Captured.program Spec.specs 0
        Captured.program.bodies :=
    ⟨ok_unsafe_macro.1, ok_unit_from_elem_count.1, ok_unit_to_elem_count.1,
     ok_usize_from_elem_count.1, ok_usize_to_elem_count.1, ok_u8_Immutable_marker.1,
     ok_u8_TryFromBytes_marker.1, ok_u8_FromZeros_marker.1, ok_u8_FromBytes_marker.1,
     True.intro⟩
  intro defId body found
  have hSub := bodiesVerified_getElem hAll defId body found
  rw [Nat.zero_add] at hSub
  exact hSub

end AutoScaffold
