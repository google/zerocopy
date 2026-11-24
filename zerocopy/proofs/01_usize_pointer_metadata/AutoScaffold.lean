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

def id_usize_from_elem_count : DefId := 0
abbrev body_usize_from_elem_count : Body := Captured.body_0
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

def id_usize_to_elem_count : DefId := 1
abbrev body_usize_to_elem_count : Body := Captured.body_1
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

theorem all_bodies_safe :
    ∀ (defId : DefId) (body : Body),
      Trusted.MirSemantics.getElem? Captured.program.bodies defId =
        some body →
      BodyVerified Captured.program defId body
        (Spec.specs.safety body.identity) := by
  have hAll :
      BodiesVerified Captured.program Spec.specs 0
        Captured.program.bodies :=
    ⟨ok_usize_from_elem_count.1, ok_usize_to_elem_count.1, True.intro⟩
  intro defId body found
  have hSub := bodiesVerified_getElem hAll defId body found
  rw [Nat.zero_add] at hSub
  exact hSub

end AutoScaffold
