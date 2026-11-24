-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.Codec
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.EnumEquiv
import Anneal.MirCorrespondence.MemRoundTrip
import Anneal.MirCorrespondence.RvalueStep
import Anneal.MirCorrespondence.StmtTermStep

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-! ## Entry Initialization Simulation (`initRefState_sim_base`) -/

theorem refStmtHasStorageMarker_eq {ts : List MirTy} {localId : LocalId}
    {rstmt : Miri.MIR.Statement} {stmt : StatementKind}
    (h : decodeStmt ts rstmt.kind = some stmt) :
    refStmtHasStorageMarker localId rstmt =
      stmtHasStorageMarker localId stmt := by
  dsimp only [refStmtHasStorageMarker]
  cases h_k : rstmt.kind with
  | StorageLive id =>
    rw [h_k] at h
    injection h with h_eq; subst h_eq; rfl
  | StorageDead id =>
    rw [h_k] at h
    injection h with h_eq; subst h_eq; rfl
  | Nop =>
    rw [h_k] at h
    injection h with h_eq; subst h_eq; rfl
  | Intrinsic intr =>
    rw [h_k] at h
    have h_u : intr = .Assume (.RuntimeChecks .UbChecks) := by
      cases intr with
      | Assume k =>
        cases k with
        | RuntimeChecks rc =>
          cases rc <;> first | rfl | cases h
        | _ => cases h
      | _ => cases h
    subst h_u
    injection h with h_eq; subst h_eq; rfl
  | Assign rdst rrv =>
    rw [h_k] at h
    dsimp only [decodeStmt, optMap2] at h
    cases h₁ : decodePlace ts rdst with
    | none => rw [h₁] at h; cases h
    | some dst =>
      cases h₂ : decodeRvalue ts rrv with
      | none => rw [h₁, h₂] at h; cases h
      | some rv =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        rfl
  | _ => rw [h_k] at h; cases h

theorem refHasStorageAnnotation_eq {ts : List MirTy} {bm : MiriBodyMeta}
    {rbody : Miri.MIR.Body} {body : Body}
    (h : decodeBody ts bm rbody = some body) (localId : LocalId) :
    refHasStorageAnnotation rbody localId =
      hasStorageAnnotation body localId := by
  let ⟨_, _, _, _, h_bbs, _, _⟩ := decodeBody_inv h
  unfold refHasStorageAnnotation hasStorageAnnotation
  exact mapOption_any_eq
    (fun _ _ h_bb =>
      mapOption_any_eq (fun _ _ hs => refStmtHasStorageMarker_eq hs)
        (decodeBasicBlock_inv h_bb).1)
    h_bbs

noncomputable def refStmtInBounds (n : Nat) (st : Miri.MIR.Statement) : Bool :=
  match st.kind with
  | .StorageLive id | .StorageDead id => Nat.blt id n
  | _ => true

noncomputable def stmtInBounds (n : Nat) : StatementKind → Bool
  | .storageLive id | .storageDead id => Nat.blt id n
  | _ => true

theorem refStmtInBounds_eq {ts : List MirTy} {n : Nat}
    {rstmt : Miri.MIR.Statement} {stmt : StatementKind}
    (h : decodeStmt ts rstmt.kind = some stmt) :
    refStmtInBounds n rstmt = stmtInBounds n stmt := by
  dsimp only [refStmtInBounds]
  cases h_k : rstmt.kind with
  | StorageLive id =>
    rw [h_k] at h
    injection h with h_eq; subst h_eq; rfl
  | StorageDead id =>
    rw [h_k] at h
    injection h with h_eq; subst h_eq; rfl
  | Nop =>
    rw [h_k] at h
    injection h with h_eq; subst h_eq; rfl
  | Intrinsic intr =>
    rw [h_k] at h
    have h_u : intr = .Assume (.RuntimeChecks .UbChecks) := by
      cases intr with
      | Assume k =>
        cases k with
        | RuntimeChecks rc =>
          cases rc <;> first | rfl | cases h
        | _ => cases h
      | _ => cases h
    subst h_u
    injection h with h_eq; subst h_eq; rfl
  | Assign rdst rrv =>
    rw [h_k] at h
    dsimp only [decodeStmt, optMap2] at h
    cases h₁ : decodePlace ts rdst with
    | none => rw [h₁] at h; cases h
    | some dst =>
      cases h₂ : decodeRvalue ts rrv with
      | none => rw [h₁, h₂] at h; cases h
      | some rv =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        rfl
  | _ => rw [h_k] at h; cases h

theorem refStorageAnnotationsInBounds_eq {ts : List MirTy} {bm : MiriBodyMeta}
    {rbody : Miri.MIR.Body} {body : Body}
    (h : decodeBody ts bm rbody = some body) :
    refStorageAnnotationsInBounds rbody = storageAnnotationsInBounds body := by
  let ⟨_, _, _, h_loc, h_bbs, _, _⟩ := decodeBody_inv h
  have h_len : rbody.locals.size = body.locals.length := by
    have h_l : rbody.locals.size = rbody.locals.toList.length := by
      cases rbody.locals with
      | mk xs => rfl
    rw [h_l, mapOption_length h_loc]
  unfold refStorageAnnotationsInBounds storageAnnotationsInBounds
  rw [h_len]
  exact mapOption_all_eq
    (fun _ _ h_bb =>
      mapOption_all_eq (fun _ _ hs => refStmtInBounds_eq hs)
        (decodeBasicBlock_inv h_bb).1)
    h_bbs

theorem initRefLocalsLoop_eq {ts : List MirTy} {bm : MiriBodyMeta}
    {rbody : Miri.MIR.Body} {body : Body}
    (h : decodeBody ts bm rbody = some body) (args : List Val) (idx : Nat)
    (tys : List MirTy) :
    initRefLocalsLoop ts rbody args idx tys =
      liftLocals ts tys (initLocalsLoop body args idx tys) := by
  induction tys generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    let ⟨_, _, h_arg, _, _, _, _⟩ := decodeBody_inv h
    dsimp only [initRefLocalsLoop, initLocalsLoop, liftLocals]
    rw [h_arg, refHasStorageAnnotation_eq h idx, refLiveUninitSlot_eq,
      ih (idx + 1)]
    rfl

private theorem checkArgsMatch_getElem? {args : List Val} {tys : List MirTy}
    (h : checkArgsMatch args tys = true) :
    ∀ (k : Nat) (ty : MirTy),
      MirSemantics.getElem? tys k = some ty →
      ∃ v : Val, MirSemantics.getElem? args k = some v ∧
        checkVal v ty = true := by
  induction args generalizing tys with
  | nil =>
    cases tys with
    | nil => intro k ty hk; cases hk
    | cons _ _ => cases h
  | cons a rest ih =>
    cases tys with
    | nil => cases h
    | cons t ts =>
      dsimp only [checkArgsMatch] at h
      cases h_cv : checkVal a t with
      | false => rw [h_cv] at h; cases h
      | true =>
        rw [h_cv] at h
        intro k ty hk
        cases k with
        | zero =>
          injection hk with h_eq; subst h_eq
          exact ⟨a, rfl, h_cv⟩
        | succ k' => exact ih h k' ty hk

private theorem getElem?_take_of_lt {α : Type} :
    ∀ (xs : List α) (n i : Nat),
      i < n → MirSemantics.getElem? (xs.take n) i = MirSemantics.getElem? xs i
  | [], n, _, _ => by cases n <;> rfl
  | x :: rest, 0, _, hlt => nomatch hlt
  | x :: rest, n + 1, 0, _ => rfl
  | x :: rest, n + 1, i + 1, hlt =>
    getElem?_take_of_lt rest n i (Nat.lt_of_succ_lt_succ hlt)

private theorem getElem?_drop_one {α : Type} (xs : List α) (j : Nat) :
    MirSemantics.getElem? (xs.drop 1) j = MirSemantics.getElem? xs (j + 1) := by
  cases xs <;> rfl

private theorem initLocalsLoop_slotsMatchTys_aux (body : Body) (args : List Val) :
    ∀ (idx : Nat) (tys : List MirTy),
      (∀ (j : Nat) (ty : MirTy),
        MirSemantics.getElem? tys j = some ty →
        Nat.beq (idx + j) 0 = false →
        Nat.ble (idx + j) body.argumentCount = true →
        ∀ (v : Val), MirSemantics.getElem? args (idx + j - 1) = some v →
          checkVal v ty = true) →
      SlotsMatchTys tys (initLocalsLoop body args idx tys) := by
  intro idx tys h_ok
  induction tys generalizing idx with
  | nil => exact SlotsMatchTys.nil
  | cons ty rest ih =>
    dsimp only [initLocalsLoop]
    apply SlotsMatchTys.cons
    · cases h0 : Nat.beq idx 0 with
      | true =>
        rw [ite_eq_left rfl]
        exact slotMatchesTy_liveUninitSlot ty
      | false =>
        rw [ite_eq_right (by decide)]
        cases hle : Nat.ble idx body.argumentCount with
        | true =>
          rw [ite_eq_left rfl]
          cases h_a : MirSemantics.getElem? args (idx - 1) with
          | none => exact True.intro
          | some v =>
            exact h_ok 0 ty rfl (by rw [Nat.add_zero]; exact h0)
              (by rw [Nat.add_zero]; exact hle) v h_a
        | false =>
          rw [ite_eq_right (by decide)]
          cases hasStorageAnnotation body idx with
          | true => exact True.intro
          | false => exact slotMatchesTy_liveUninitSlot ty
    · apply ih (idx + 1)
      intro j ty' h_get h0' hle' v h_a
      have h_assoc : idx + 1 + j = idx + (j + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 j]
      rw [h_assoc] at h0' hle' h_a
      exact h_ok (j + 1) ty' h_get h0' hle' v h_a

private theorem initLocalsLoop_slotsMatchTys (body : Body) (args : List Val)
    (h_args : checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) =
      true) :
    SlotsMatchTys body.locals (initLocalsLoop body args 0 body.locals) := by
  apply initLocalsLoop_slotsMatchTys_aux body args 0 body.locals
  intro j ty h_get h0 hle v h_a
  rw [Nat.zero_add] at h0 hle h_a
  cases j with
  | zero => cases h0
  | succ k =>
    have h_le : k + 1 ≤ body.argumentCount := Nat.ble_eq.mp hle
    have h_lt : k < body.argumentCount := h_le
    have h_pt :
        MirSemantics.getElem? ((body.locals.drop 1).take body.argumentCount) k =
          some ty := by
      rw [getElem?_take_of_lt _ _ _ h_lt, getElem?_drop_one]
      exact h_get
    let ⟨v', h_av', h_cv'⟩ := checkArgsMatch_getElem? h_args k ty h_pt
    have h_sub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
    rw [h_sub] at h_a
    rw [h_a] at h_av'
    injection h_av' with h_veq
    rw [h_veq]
    exact h_cv'

theorem getElem?_zero_of_blt {α : Type} {xs : List α} {n : Nat}
    (h : Nat.blt n xs.length = true) :
    ∃ x : α, MirSemantics.getElem? xs 0 = some x := by
  cases xs with
  | nil => cases h
  | cons x _ => exact ⟨x, rfl⟩

theorem initRefState_sim_base : InitRefStateSimClaim := by
  intro rp p q maxSteps h_dec
  let ⟨h_bodies, h_entry, h_width, h_prof, _⟩ := decodeProg_inv h_dec
  unfold initRefState initState
  rw [h_entry, h_width, h_prof]
  cases Nat.beq p.pointerWidthBits 64
  · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
    intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
  · dsimp only
    cases Nat.beq p.mirProfileVersion 1
    · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
      intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
    · cases q.callerMem.allocations.isEmpty
      · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
        intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
      · cases h_b : MirSemantics.getElem? p.bodies p.entryDefId with
        | none =>
          rw [decodeBodies_getElem?_none h_bodies h_b]
          refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
          intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
        | some body =>
          let ⟨rbody, rmeta, h_rb_get, h_rm_get, h_rb_dec⟩ :=
            decodeBodies_getElem?_some h_bodies h_b
          let ⟨_, _, h_arg, h_loc_dec, h_bbs_dec, _, _⟩ := decodeBody_inv h_rb_dec
          rw [h_rb_get]
          dsimp only
          rw [h_loc_dec]
          dsimp only
          rw [mapOption_isEmpty h_bbs_dec, h_arg,
            refStorageAnnotationsInBounds_eq h_rb_dec,
            refDiscriminantTypesValid_eq h_rb_dec,
            refCastTypesValid_eq h_rb_dec]
          cases body.basicBlocks.isEmpty
          · cases h_blt : Nat.blt body.argumentCount body.locals.length
            · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
              intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
            · cases h_sa : storageAnnotationsInBounds body
              · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
              · cases h_dv : discriminantTypesValid body
                · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                  intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                · cases h_cv : castTypesValid body
                  · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                    intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                  · rw [list_all_congr_eq body.locals _ _
                      refIsSupportedLocalTy_eq]
                    cases h_supp : body.locals.all isSupportedScalarOrUnitTy
                    · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                      intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                    · rw [checkRefArgsMatch_eq]
                      cases h_args : checkArgsMatch q.args
                          ((body.locals.drop 1).take body.argumentCount)
                      · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                        intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                      · let ⟨retTy, h_ret⟩ := getElem?_zero_of_blt h_blt
                        let ⟨mem, retPlace, h_init_mem⟩ :=
                          refInitMemoryAndRetPlace_ok rp.types retTy
                        rw [h_ret]
                        dsimp only
                        rw [h_init_mem]
                        dsimp only
                        refine ⟨?_, ?_⟩
                        · intro k hk; cases hk
                        · intro s₀ hs₀
                          injection hs₀ with h_s₀
                          subst h_s₀
                          rw [initRefLocalsLoop_eq h_rb_dec q.args 0
                            body.locals]
                          have h_entry_ret : entryRetTy? p = some retTy := by
                            dsimp only [entryRetTy?]
                            rw [h_b]
                            exact h_ret
                          refine ⟨_, rfl, ?_, rfl, rfl⟩
                          exact ⟨_, _, retTy, mem, refInitControl, h_dec,
                            rfl, rfl, rfl, h_entry_ret, rfl, h_init_mem,
                            refControlValid_init, rfl, body, rbody, rmeta, h_b,
                            h_rb_get, h_rm_get, h_rb_dec, h_blt, h_sa, h_dv, h_cv,
                            h_supp,
                            initLocalsLoop_slotsMatchTys body q.args h_args,
                            fun _ _ => Nat.zero_le _, rfl⟩
          · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
            intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl

/-! ## Single-Step and Multi-Step Simulation Helpers -/

theorem simulationInv_with_counters {rp : MiriProg} {p : Program} {s : State}
    {rs : RefState} (steps max : Nat) (h : SimulationInv rp p s rs) :
    SimulationInv rp p s { rs with stepsExecuted := steps, maxSteps := max } := by
  let ⟨f, rf, retTy, mem, ctrl, h_dec, hs, hm, hdef, hert, hrty, hinit, hctrl,
    hmiri, hframe⟩ := h
  exact ⟨f, rf, retTy, mem, ctrl, h_dec, hs, hm, hdef, hert, hrty, hinit, hctrl,
    hmiri, hframe⟩

theorem simulationInv_of_with_counters {rp : MiriProg} {p : Program} {s : State}
    {rs : RefState} {steps max : Nat}
    (h : SimulationInv rp p s
      { rs with stepsExecuted := steps, maxSteps := max }) :
    SimulationInv rp p s rs := by
  let ⟨f, rf, retTy, mem, ctrl, h_dec, hs, hm, hdef, hert, hrty, hinit, hctrl,
    hmiri, hframe⟩ := h
  exact ⟨f, rf, retTy, mem, ctrl, h_dec, hs, hm, hdef, hert, hrty, hinit, hctrl,
    hmiri, hframe⟩

theorem nat_blt_eq_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

/-- Choice-coupled single-step backward simulation: a running $M_{\text{ref}}$
transition at choice `c` from a simulated state is matched by an
$M_{\text{anneal}}$ transition at the exact same choice `c`. -/
theorem sim_of_refStep_at_choice {rp : MiriProg} {p : Program} {s : State}
    {rs rs' : RefState} {c : Choice}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (hc : ValidRefChoice rp rs c)
    (h_eval : evalRefStep rp c rs = .running rs') :
    ∃ s' : State,
      ValidChoice p s c ∧
      evalStep p c s = .step s' ∧
      SimulationInv rp p s' rs' := by
  let ⟨f, rf, retTy, mem, ctrl, _, hs, hm, hdef, hert, hrty, hinit, hctrl,
    hmiri, hframe⟩ := h_sim
  let ⟨body, rbody, rmeta, hbody, hrbody, hrmeta, hbdec, harg, hsa, hdv, hcv, hsupp, hinv, hpc,
    hrf⟩ := hframe
  cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
  | false =>
    unfold evalRefStep at h_eval
    rw [h_lt] at h_eval
    cases h_eval
  | true =>
    rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_eval
    cases h_es : evalStep p c s with
    | done out =>
      rw [h_es] at h_eval
      cases h_eval
    | fault k =>
      rw [h_es] at h_eval
      cases k <;> cases h_eval
    | step s₁ =>
      let ⟨f₁, hs₁, hdef₁, hinv₁, hpc₁⟩ := evalStep_step_inv hs hbody hinv h_es
      rw [h_es, hs₁] at h_eval
      dsimp only [mapStepRes, stepResultToRefOutcome] at h_eval
      injection h_eval with h_rs'
      subst h_rs'
      have hbody₁ : MirSemantics.getElem? p.bodies f₁.defId = some body := by
        rw [hdef₁]; exact hbody
      have hrbody₁ : MirSemantics.getElem? rp.bodies f₁.defId = some rbody := by
        rw [hdef₁]; exact hrbody
      have hrmeta₁ : MirSemantics.getElem? rp.bodyMeta f₁.defId = some rmeta := by
        rw [hdef₁]; exact hrmeta
      have hctrl' : RefControlValid
          (nextRefControlForStep body f rs.miri.machine.user.control) := by
        rw [hmiri]
        exact refControlValid_nextRefControlForStep hctrl
      have hmem : rs.miri.machine.memory = mem := by rw [hmiri]; rfl
      refine ⟨s₁, hc, rfl, f₁,
        mkRefMiriFrame f₁.defId rbody f₁.blockIdx f₁.stmtIdx
          (liftLocals rp.types body.locals f₁.locals) rs.retPlace,
        retTy, mem, nextRefControlForStep body f rs.miri.machine.user.control,
        h_dec, ?_, ?_, hdef₁.trans hdef, hert, hrty, hinit, hctrl', ?_,
        body, rbody, rmeta, hbody₁, hrbody₁, hrmeta₁, hbdec, harg, hsa, hdv, hcv, hsupp,
        hinv₁, hpc₁, rfl⟩
      · rw [hs₁]
      · rw [hs₁]; exact hm
      · dsimp only
        rw [hmem, hs₁]

/-- Backward simulation for one step: a running $M_{\text{ref}}$ transition
from a simulated state is matched by an $M_{\text{anneal}}$ transition that
re-establishes `SimulationInv`. -/
theorem sim_of_refStep_base : SimOfRefStepClaim := by
  intro rp p s rs rs' h_dec h_sim h_rstep
  let ⟨c, hc, h_eval⟩ := h_rstep
  let ⟨s', hc', h_es, h_sim'⟩ := sim_of_refStep_at_choice h_dec h_sim hc h_eval
  exact ⟨s', ⟨c, hc', h_es⟩, h_sim'⟩

/-- Backward simulation: every $M_{\text{ref}}$ state reachable from a
simulated state is simulated by a reachable $M_{\text{anneal}}$ state. -/
theorem sim_of_refReaches_base : SimOfRefReachesClaim := by
  intro rp p s₀ rs₀ rs h_dec h_sim₀ h_reach
  induction h_reach with
  | refl => exact ⟨s₀, Reaches.refl s₀, h_sim₀⟩
  | tail _ h_rstep ih =>
    let ⟨s₂, h_reach₂, h_sim₂⟩ := ih
    let ⟨s₃, h_step, h_sim₃⟩ := sim_of_refStep_base h_dec h_sim₂ h_rstep
    exact ⟨s₃, Reaches.tail h_reach₂ h_step, h_sim₃⟩

/-- Choice-coupled backward reachability simulation. -/
theorem sim_of_refReachesAtChoices {rp : MiriProg} {p : Program}
    {s₀ : State} {rs₀ rs : RefState} {cs : List Choice}
    (h_dec : decodeProg rp = some p)
    (h_sim₀ : SimulationInv rp p s₀ rs₀)
    (h_reach : RefReachesAtChoices rp rs₀ cs rs) :
    ∃ s : State, ReachesAtChoices p s₀ cs s ∧ SimulationInv rp p s rs := by
  induction h_reach generalizing s₀ with
  | nil _ => exact ⟨s₀, ReachesAtChoices.nil s₀, h_sim₀⟩
  | cons hc h_eval _ ih =>
    let ⟨s₁, hc', h_es, h_sim₁⟩ :=
      sim_of_refStep_at_choice h_dec h_sim₀ hc h_eval
    let ⟨s₂, h_r₂, h_sim₂⟩ := ih h_sim₁
    exact ⟨s₂, ReachesAtChoices.cons hc' h_es h_r₂, h_sim₂⟩

/-- Choice-coupled single-step forward simulation: while the step budget is not
exhausted, an $M_{\text{anneal}}$ transition at choice `c` from a simulated
state is matched by one running $M_{\text{ref}}$ transition at the exact same
choice `c`. -/
theorem refStep_of_step_at_choice {rp : MiriProg} {p : Program} {s s' : State}
    {rs : RefState} {c : Choice}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (hc : ValidChoice p s c)
    (h_es : evalStep p c s = .step s')
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true) :
    ∃ rs' : RefState,
      ValidRefChoice rp rs c ∧
      evalRefStep rp c rs = .running rs' ∧
      SimulationInv rp p s' rs' ∧
      rs'.stepsExecuted = rs.stepsExecuted + 1 ∧
      rs'.maxSteps = rs.maxSteps := by
  let ⟨f, rf, retTy, mem, ctrl, _, hs, hm, hdef, hert, hrty, hinit, hctrl,
    hmiri, hframe⟩ := h_sim
  let ⟨body, rbody, rmeta, hbody, hrbody, hrmeta, hbdec, harg, hsa, hdv, hcv, hsupp, hinv, hpc,
    hrf⟩ := hframe
  have h_ref_eq := evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c
  let ⟨f', hs', hdef', hinv', hpc'⟩ := evalStep_step_inv hs hbody hinv h_es
  rw [h_es, hs'] at h_ref_eq
  dsimp only [mapStepRes, stepResultToRefOutcome] at h_ref_eq
  let rf' := mkRefMiriFrame f'.defId rbody f'.blockIdx f'.stmtIdx
    (liftLocals rp.types body.locals f'.locals) rs.retPlace
  let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
  let rs' : RefState := {
    rs with
    miri := mkRefMiriState rf' rs.miri.machine.memory ctrl' s.callerMem
    stepsExecuted := rs.stepsExecuted + 1
  }
  have hbody' : MirSemantics.getElem? p.bodies f'.defId = some body := by
    rw [hdef']; exact hbody
  have hrbody' : MirSemantics.getElem? rp.bodies f'.defId = some rbody := by
    rw [hdef']; exact hrbody
  have hrmeta' : MirSemantics.getElem? rp.bodyMeta f'.defId = some rmeta := by
    rw [hdef']; exact hrmeta
  have hctrl' : RefControlValid ctrl' := by
    dsimp only [ctrl']; rw [hmiri]; exact refControlValid_nextRefControlForStep hctrl
  have hmem : rs.miri.machine.memory = mem := by rw [hmiri]; rfl
  refine ⟨rs', hc, h_ref_eq, ?_, rfl, rfl⟩
  rw [hs']
  refine ⟨f', rf', retTy, mem, ctrl', h_dec, rfl, hm, hdef'.trans hdef, hert,
    hrty, hinit, hctrl', ?_, body, rbody, rmeta, hbody', hrbody', hrmeta', hbdec, harg, hsa,
    hdv, hcv, hsupp, hinv', hpc', rfl⟩
  dsimp only [rs']
  rw [hmem]

/-- Step-indexed reachability in $M_{\text{anneal}}$: `s₂` is reached from `s₁`
in exactly `n` transitions. -/
inductive ReachesN (p : Program) (s₁ : State) : Nat → State → Prop where
  | refl : ReachesN p s₁ 0 s₁
  | tail {n : Nat} {s₂ s₃ : State} :
      ReachesN p s₁ n s₂ →
      Step p s₂ (.step s₃) →
      ReachesN p s₁ (n + 1) s₃

/-- Step-indexed reachability in $M_{\text{ref}}$: `rs₂` is reached from `rs₁`
in exactly `n` `.running` transitions. -/
inductive RefReachesN (rp : MiriProg) (rs₁ : RefState) :
    Nat → RefState → Prop where
  | refl : RefReachesN rp rs₁ 0 rs₁
  | tail {n : Nat} {rs₂ rs₃ : RefState} :
      RefReachesN rp rs₁ n rs₂ →
      RefStep rp rs₂ (.running rs₃) →
      RefReachesN rp rs₁ (n + 1) rs₃

theorem exists_reachesN_of_reaches {p : Program} {s₁ s₂ : State}
    (h : Reaches p s₁ s₂) :
    ∃ n : Nat, ReachesN p s₁ n s₂ := by
  induction h with
  | refl => exact ⟨0, ReachesN.refl⟩
  | tail _ h_step ih =>
    let ⟨n, h_in⟩ := ih
    exact ⟨n + 1, ReachesN.tail h_in h_step⟩

theorem refReaches_of_refReachesN {rp : MiriProg} {rs₁ rs₂ : RefState}
    {n : Nat} (h : RefReachesN rp rs₁ n rs₂) :
    RefReaches rp rs₁ rs₂ := by
  induction h with
  | refl => exact RefReaches.refl rs₁
  | tail _ h_step ih => exact RefReaches.tail ih h_step

/-- Forward simulation for one step: while the step budget is not exhausted,
an $M_{\text{anneal}}$ transition from a simulated state is matched by one
running $M_{\text{ref}}$ transition that re-establishes `SimulationInv`. -/
theorem refStep_of_step {rp : MiriProg} {p : Program} {s s' : State}
    {rs : RefState}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (h_step : Step p s (.step s'))
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true) :
    ∃ rs' : RefState,
      RefStep rp rs (.running rs') ∧
      SimulationInv rp p s' rs' ∧
      rs'.stepsExecuted = rs.stepsExecuted + 1 ∧
      rs'.maxSteps = rs.maxSteps := by
  let ⟨c, hc, h_es⟩ := h_step
  let ⟨rs', hc', h_ev, h_sim', h_st, h_mx⟩ :=
    refStep_of_step_at_choice h_dec h_sim hc h_es h_lt
  exact ⟨rs', ⟨c, hc', h_ev⟩, h_sim', h_st, h_mx⟩

/-- Step-indexed forward simulation: an `n`-step $M_{\text{anneal}}$ execution
from a simulated state is matched by an `n`-step $M_{\text{ref}}$ execution
whenever the reference step budget leaves room for `n` more steps. -/
theorem refReachesN_of_reachesN {rp : MiriProg} {p : Program} {n : Nat}
    {s₁ s₂ : State} {rs₁ : RefState}
    (h_dec : decodeProg rp = some p)
    (h_in : ReachesN p s₁ n s₂)
    (h_sim₁ : SimulationInv rp p s₁ rs₁)
    (h_budget : rs₁.stepsExecuted + n ≤ rs₁.maxSteps) :
    ∃ rs₂ : RefState,
      RefReachesN rp rs₁ n rs₂ ∧
      SimulationInv rp p s₂ rs₂ ∧
      rs₂.stepsExecuted = rs₁.stepsExecuted + n ∧
      rs₂.maxSteps = rs₁.maxSteps := by
  induction h_in with
  | refl =>
    exact ⟨rs₁, RefReachesN.refl, h_sim₁, (Nat.add_zero _).symm, rfl⟩
  | @tail m s_mid s_next h_prev h_step ih =>
    have h_b₁ : rs₁.stepsExecuted + m ≤ rs₁.maxSteps :=
      Nat.le_of_succ_le h_budget
    let ⟨rs₂, h_rreach, h_sim₂, h_steps₂, h_max₂⟩ := ih h_b₁
    have h_lt : Nat.blt rs₂.stepsExecuted rs₂.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      rw [h_steps₂, h_max₂]
      exact h_budget
    let ⟨rs₃, h_rstep, h_sim₃, h_steps₃, h_max₃⟩ :=
      refStep_of_step h_dec h_sim₂ h_step h_lt
    refine ⟨rs₃, RefReachesN.tail h_rreach h_rstep, h_sim₃, ?_, ?_⟩
    · rw [h_steps₃, h_steps₂]
      rfl
    · rw [h_max₃, h_max₂]

/-- Choice-coupled forward reachability simulation. -/
theorem refReachesAtChoices_of_reachesAtChoices {rp : MiriProg} {p : Program}
    {cs : List Choice} {s₁ s₂ : State} {rs₁ : RefState}
    (h_dec : decodeProg rp = some p)
    (h_reach : ReachesAtChoices p s₁ cs s₂)
    (h_sim₁ : SimulationInv rp p s₁ rs₁)
    (h_budget : rs₁.stepsExecuted + cs.length ≤ rs₁.maxSteps) :
    ∃ rs₂ : RefState,
      RefReachesAtChoices rp rs₁ cs rs₂ ∧
      SimulationInv rp p s₂ rs₂ ∧
      rs₂.stepsExecuted = rs₁.stepsExecuted + cs.length ∧
      rs₂.maxSteps = rs₁.maxSteps := by
  induction h_reach generalizing rs₁ with
  | nil _ =>
    exact ⟨rs₁, RefReachesAtChoices.nil rs₁, h_sim₁, (Nat.add_zero _).symm, rfl⟩
  | @cons s_a s_b s_c c rest hc h_es _ ih =>
    have h_lt : Nat.blt rs₁.stepsExecuted rs₁.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      have h_pos : rs₁.stepsExecuted + 1 ≤ rs₁.stepsExecuted + (rest.length + 1) :=
        Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rest.length)) _
      exact Nat.le_trans h_pos h_budget
    let ⟨rs_b, hc', h_ev, h_sim_b, h_st_b, h_mx_b⟩ :=
      refStep_of_step_at_choice h_dec h_sim₁ hc h_es h_lt
    have h_budget_b : rs_b.stepsExecuted + rest.length ≤ rs_b.maxSteps := by
      rw [h_st_b, h_mx_b, Nat.add_assoc, Nat.add_comm 1 rest.length]
      exact h_budget
    let ⟨rs_c, h_r_c, h_sim_c, h_st_c, h_mx_c⟩ := ih h_sim_b h_budget_b
    refine ⟨rs_c, RefReachesAtChoices.cons hc' h_ev h_r_c, h_sim_c, ?_, ?_⟩
    · rw [h_st_c, h_st_b, Nat.add_assoc, Nat.add_comm 1 rest.length]
      rfl
    · rw [h_mx_c, h_mx_b]

/-! ## Aggregate Well-Formedness, Behavior, Divergence, and Fault Claims -/

/-- UB transfer: if `(p, q)` is well-formed in $M_{\text{anneal}}$, then
`encodeToMiri p` neither reaches `.ub` nor `.blocked` in $M_{\text{ref}}$ under
any step budget `maxSteps : Nat`. -/
theorem refWellFormed_of_wellFormed_base : RefWellFormedOfWellFormedClaim := by
  intro p q h_wf
  have h_dec : decodeProg (encodeToMiri p) = some p := decodeProg_encodeProg_base p
  let ⟨⟨s₀, h_init, _⟩, h_no_fault⟩ := h_wf
  intro maxSteps
  let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
    (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
  refine ⟨⟨rs₀, h_rinit, fun _ _ => ⟨0, rfl⟩⟩, ?_, ?_⟩
  · intro h_ub
    unfold RefReachesOutcome at h_ub
    rw [h_rinit] at h_ub
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_ub
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches_base h_dec h_sim₀ h_rreach
    let ⟨f, _, _, _, _, _, hs, _, _, _, _, _, _, _, hframe⟩ := h_sim
    let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, hinv, _, _⟩ := hframe
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, hs', _, _, _⟩ := evalStep_step_inv hs hbody hinv h_es
        rw [h_es, hs'] at h_reval
        cases h_reval
      | done out =>
        rw [h_es] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k with
        | unsupported => cases h_reval
        | undefined =>
          apply h_no_fault .undefined
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩
  · intro h_blk
    unfold RefReachesOutcome at h_blk
    rw [h_rinit] at h_blk
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_blk
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches_base h_dec h_sim₀ h_rreach
    let ⟨f, _, _, _, _, _, hs, _, _, _, _, _, _, _, hframe⟩ := h_sim
    let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, hinv, _, _⟩ := hframe
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, hs', _, _, _⟩ := evalStep_step_inv hs hbody hinv h_es
        rw [h_es, hs'] at h_reval
        cases h_reval
      | done out =>
        rw [h_es] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k with
        | undefined => cases h_reval
        | unsupported =>
          apply h_no_fault .unsupported
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩

/-- Forward behavior transfer: every terminal behavior of `(p, q)` in
$M_{\text{anneal}}$ is a reference behavior of `encodeToMiri p` (witnessed by
step budget `n + 1` for an `n`-step execution). -/
theorem refBehavior_of_behavior_base : RefBehaviorOfBehaviorClaim := by
  intro p q out h_beh
  have h_dec : decodeProg (encodeToMiri p) = some p := decodeProg_encodeProg_base p
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState p q with
  | error k =>
    rw [h_init] at h_beh
    cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨s_end, h_reach, c, hc, h_es⟩ := h_beh
    let ⟨n, h_in⟩ := exists_reachesN_of_reaches h_reach
    let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
      (initRefState_sim_base (n + 1) h_dec).2 s₀ h_init
    have h_budget : rs₀.stepsExecuted + n ≤ rs₀.maxSteps := by
      rw [h_steps₀, h_max₀, Nat.zero_add]
      exact Nat.le_succ n
    let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
      refReachesN_of_reachesN h_dec h_in h_sim₀ h_budget
    let ⟨f, _, _, _, _, _, hs, _, _, _, _, _, _, _, hframe⟩ := h_sim_end
    let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, _, _, _⟩ := hframe
    have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
      exact Nat.lt_succ_self n
    have h_reval := evalRefStep_eq_base h_dec h_sim_end hs hbody hrbody h_lt c
    rw [h_es] at h_reval
    refine ⟨n + 1, ?_⟩
    unfold RefReachesOutcome
    rw [h_rinit]
    exact ⟨rs_end, refReaches_of_refReachesN h_rreach, c, hc, h_reval⟩

/-- Backward behavior transfer: every reference behavior of `encodeToMiri p` is
a terminal behavior of `(p, q)` in $M_{\text{anneal}}$, so $M_{\text{ref}}$
has no outcomes that $M_{\text{anneal}}$ omits. -/
theorem behavior_of_refBehavior_base : BehaviorOfRefBehaviorClaim := by
  intro p q out h_ref
  have h_dec : decodeProg (encodeToMiri p) = some p := decodeProg_encodeProg_base p
  let ⟨maxSteps, h_out⟩ := h_ref
  unfold RefReachesOutcome at h_out
  unfold Behavior ReachesResult
  cases h_init : initState p q with
  | error k =>
    rw [(initRefState_sim_base maxSteps h_dec).1 k h_init] at h_out
    cases k <;> cases h_out
  | ok s₀ =>
    let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
      (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
    rw [h_rinit] at h_out
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_out
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches_base h_dec h_sim₀ h_rreach
    let ⟨f, _, _, _, _, _, hs, _, _, _, _, _, _, _, hframe⟩ := h_sim
    let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, hinv, _, _⟩ := hframe
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, hs', _, _, _⟩ := evalStep_step_inv hs hbody hinv h_es
        rw [h_es, hs'] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k <;> cases h_reval
      | done out' =>
        rw [h_es] at h_reval
        dsimp only [mapStepRes, stepResultToRefOutcome] at h_reval
        injection h_reval with h_out_eq
        subst h_out_eq
        exact ⟨s, h_reach, c, hc, h_es⟩

/-- Terminal behaviors coincide exactly in $M_{\text{anneal}}$ and
$M_{\text{ref}}$. -/
theorem behavior_iff_refBehavior_base : BehaviorIffRefBehaviorClaim :=
  fun p q out =>
    ⟨refBehavior_of_behavior_base p q out, behavior_of_refBehavior_base p q out⟩

/-- Advance a lifted $M_{\text{ref}}$ trace state across one $M_{\text{anneal}}$
transition `(sPrev → sNext)` while preserving `retPlace`, `memory`, and
advancing `control` via `nextRefControlForStep` at counters `(0, 0)`. -/
noncomputable def stepRefTrace (rp : MiriProg) (p : Program)
    (sPrev sNext : State) (rsPrev : RefState) : RefState :=
  match sPrev.frames, sNext.frames with
  | [fPrev], [fNext] =>
    match MirSemantics.getElem? p.bodies fPrev.defId,
        MirSemantics.getElem? rp.bodies fPrev.defId with
    | some body, some rbody =>
      let rf' := mkRefMiriFrame fNext.defId rbody fNext.blockIdx
        fNext.stmtIdx (liftLocals rp.types body.locals fNext.locals) rsPrev.retPlace
      let ctrl' := nextRefControlForStep body fPrev rsPrev.miri.machine.user.control
      { rsPrev with
        miri := mkRefMiriState rf' rsPrev.miri.machine.memory ctrl' sNext.callerMem
        stepsExecuted := 0
        maxSteps := 0 }
    | _, _ => rsPrev
  | _, _ => rsPrev

/-- Recursively lift an infinite $M_{\text{anneal}}$ execution trace into a
corresponding $M_{\text{ref}}$ execution trace starting at `rs₀`. -/
noncomputable def liftTrace (rp : MiriProg) (p : Program) (rs₀ : RefState)
    (trace : Nat → State) : Nat → RefState
  | 0 => rs₀
  | n + 1 =>
    stepRefTrace rp p (trace n) (trace (n + 1)) (liftTrace rp p rs₀ trace n)

/-- Construct the $M_{\text{anneal}}$ state trace driven deterministically by
an infinite choice stream `choiceStream : Nat → Choice`. -/
noncomputable def traceFromChoices (p : Program) (s₀ : State)
    (choiceStream : Nat → Choice) : Nat → State
  | 0 => s₀
  | n + 1 =>
    match evalStep p (choiceStream n) (traceFromChoices p s₀ choiceStream n) with
    | .step s' => s'
    | _ => s₀

/-- Choice-coupled backward divergence simulation: every infinite
$M_{\text{ref}}$ trace along `choiceStream` is matched by an infinite
$M_{\text{anneal}}$ trace along the exact same `choiceStream`. -/
theorem divergesAtChoices_of_refDivergesAtChoices (p : Program) (q : Query)
    (choiceStream : Nat → Choice)
    (h_rdiv : RefDivergesAtChoices (encodeToMiri p) q choiceStream) :
    DivergesAtChoices p q choiceStream := by
  have h_dec : decodeProg (encodeToMiri p) = some p := decodeProg_encodeProg_base p
  let ⟨rs₀, h_rinit, rtrace, h_rt0, h_rstep⟩ := h_rdiv
  cases h_init : initState p q with
  | error k =>
    rw [(initRefState_sim_base 0 h_dec).1 k h_init] at h_rinit
    cases h_rinit
  | ok s₀ =>
    let ⟨rs₀', h_rinit', h_sim₀, _, _⟩ :=
      (initRefState_sim_base 0 h_dec).2 s₀ h_init
    rw [h_rinit'] at h_rinit
    injection h_rinit with h_eq
    subst h_eq
    let tr := traceFromChoices p s₀ choiceStream
    have h_inv : ∀ n : Nat, SimulationInv (encodeToMiri p) p (tr n) (rtrace n) := by
      intro n
      induction n with
      | zero =>
        dsimp only [tr, traceFromChoices]
        rw [h_rt0]
        exact h_sim₀
      | succ m ih =>
        have h_sim_m := simulationInv_with_counters m (m + 1) ih
        let ⟨hc_m, h_ev_m⟩ := h_rstep m
        let ⟨s', _, h_es_m, h_sim'⟩ :=
          sim_of_refStep_at_choice h_dec h_sim_m hc_m h_ev_m
        have h_tr_next : tr (m + 1) = s' := by
          dsimp only [tr, traceFromChoices]
          rw [h_es_m]
        rw [h_tr_next]
        exact simulationInv_of_with_counters h_sim'
    refine ⟨s₀, h_init, tr, rfl, ?_⟩
    intro n
    have h_sim_n := simulationInv_with_counters n (n + 1) (h_inv n)
    let ⟨hc_n, h_ev_n⟩ := h_rstep n
    let ⟨s', hc_n', h_es_n, _⟩ :=
      sim_of_refStep_at_choice h_dec h_sim_n hc_n h_ev_n
    have h_tr_next : tr (n + 1) = s' := by
      dsimp only [tr, traceFromChoices]
      rw [h_es_n]
    rw [h_tr_next]
    exact ⟨hc_n', h_es_n⟩

/-- Divergence coincides exactly in $M_{\text{anneal}}$ and $M_{\text{ref}}$:
`(p, q)` has an infinite execution trace in $M_{\text{anneal}}$ if and only if
`encodeToMiri p` has an infinite running execution trace in $M_{\text{ref}}$. -/
theorem diverges_iff_refDiverges_base : DivergesIffRefDivergesClaim := by
  intro p q
  have h_dec : decodeProg (encodeToMiri p) = some p := decodeProg_encodeProg_base p
  let rp := encodeToMiri p
  constructor
  · intro h_div
    let ⟨s₀, h_init, trace, h_t0, h_step⟩ := h_div
    let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
      (initRefState_sim_base 0 h_dec).2 s₀ h_init
    let rtrace := liftTrace rp p rs₀ trace
    have h_inv_step : ∀ n : Nat,
        SimulationInv rp p (trace n) (rtrace n) := by
      intro n
      induction n with
      | zero =>
        dsimp only [rtrace, liftTrace]
        rw [h_t0]
        exact h_sim₀
      | succ m ih =>
        have h_sim_m := simulationInv_with_counters m (m + 1) ih
        have h_lt : Nat.blt m (m + 1) = true :=
          nat_blt_eq_true_of_lt (Nat.lt_succ_self m)
        let ⟨c, hc, h_es⟩ := h_step m
        let ⟨f, rf, retTy, mem, ctrl, _, hs, hm, hdef, hert, hrty, hinit, hctrl,
          hmiri, hframe⟩ := ih
        let ⟨body, rbody, rmeta, hbody, hrbody, hrmeta, hbdec, harg, hsa, hdv, hcv, hsupp,
          hinv, hpc, hrf⟩ := hframe
        let ⟨f', hs', hdef', hinv', hpc'⟩ := evalStep_step_inv hs hbody hinv h_es
        have h_next : rtrace (m + 1) =
            { rtrace m with
              miri := mkRefMiriState
                (mkRefMiriFrame f'.defId rbody f'.blockIdx f'.stmtIdx
                  (liftLocals rp.types body.locals f'.locals) (rtrace m).retPlace)
                mem
                (nextRefControlForStep body f ctrl)
                (trace m).callerMem
              stepsExecuted := 0
              maxSteps := 0 } := by
          dsimp only [rtrace, liftTrace, stepRefTrace]
          rw [hs, hs']
          dsimp only
          rw [hbody, hrbody]
          dsimp only
          rw [hmiri]
          rfl
        rw [h_next]
        have hbody' : MirSemantics.getElem? p.bodies f'.defId = some body := by
          rw [hdef']; exact hbody
        have hrbody' : MirSemantics.getElem? rp.bodies f'.defId = some rbody := by
          rw [hdef']; exact hrbody
        have hrmeta' : MirSemantics.getElem? rp.bodyMeta f'.defId = some rmeta := by
          rw [hdef']; exact hrmeta
        exact ⟨f', _, retTy, mem, nextRefControlForStep body f ctrl, h_dec,
          congrArg State.frames hs', (congrArg State.mem hs').trans hm,
          hdef'.trans hdef, hert, hrty, hinit,
          refControlValid_nextRefControlForStep hctrl, by rw [hs'],
          body, rbody, rmeta, hbody', hrbody', hrmeta', hbdec, harg, hsa, hdv, hcv, hsupp,
          hinv', hpc', rfl⟩
    refine ⟨rs₀, h_rinit, rtrace, rfl, ?_⟩
    intro n
    have h_sim_n := simulationInv_with_counters n (n + 1) (h_inv_step n)
    have h_lt : Nat.blt n (n + 1) = true :=
      nat_blt_eq_true_of_lt (Nat.lt_succ_self n)
    let ⟨c, hc, h_es⟩ := h_step n
    let ⟨f, rf, retTy, mem, ctrl, _, hs, hm, hdef, hert, hrty, hinit, hctrl,
      hmiri, hframe⟩ := h_inv_step n
    let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, hinv, _, _⟩ := hframe
    let ⟨f', hs', _, _, _⟩ := evalStep_step_inv hs hbody hinv h_es
    have h_ref_eq := evalRefStep_eq_base h_dec h_sim_n hs hbody hrbody h_lt c
    rw [h_es, hs'] at h_ref_eq
    dsimp only [mapStepRes, stepResultToRefOutcome] at h_ref_eq
    have h_next_eq :
        { rtrace (n + 1) with stepsExecuted := n + 1, maxSteps := n + 1 } =
        { rtrace n with
          miri := mkRefMiriState
            (mkRefMiriFrame f'.defId rbody f'.blockIdx f'.stmtIdx
              (liftLocals rp.types body.locals f'.locals) (rtrace n).retPlace)
            (rtrace n).miri.machine.memory
            (nextRefControlForStep body f (rtrace n).miri.machine.user.control)
            (trace n).callerMem
          stepsExecuted := n + 1
          maxSteps := n + 1 } := by
      dsimp only [rtrace, liftTrace, stepRefTrace]
      rw [hs, hs']
      dsimp only
      rw [hbody, hrbody]
    rw [h_next_eq]
    exact ⟨c, hc, h_ref_eq⟩
  · intro h_rdiv
    let ⟨rs₀, h_rinit, rtrace, h_rt0, h_rstep⟩ := h_rdiv
    have h_rdiv_c : RefDivergesAtChoices (encodeToMiri p) q (fun _ => 0) := by
      refine ⟨rs₀, h_rinit, rtrace, h_rt0, ?_⟩
      intro n
      let ⟨c, hc, h_ev⟩ := h_rstep n
      have hc0 : c = 0 := hc
      subst hc0
      exact ⟨rfl, h_ev⟩
    let ⟨s₀, h_init, tr, h_t0, h_step⟩ :=
      divergesAtChoices_of_refDivergesAtChoices p q (fun _ => 0) h_rdiv_c
    exact ⟨s₀, h_init, tr, h_t0, fun n => ⟨0, (h_step n).1, (h_step n).2⟩⟩

/-- Main end-to-end operational correspondence theorem: for any
`p : Program` and `q : Query`, if `WellFormed p q` holds in
$M_{\text{anneal}}$, then:
1. `RefWellFormed (encodeToMiri p) q` holds across all step budgets
   `maxSteps : Nat` in the real `ExecutionMachine.step` reference machine
   $M_{\text{ref}}$;
2. `Behavior p q out` holds in $M_{\text{anneal}}$ exactly when
   `RefBehavior (encodeToMiri p) q out` holds in $M_{\text{ref}}$; and
3. `(p, q)` diverges in $M_{\text{anneal}}$ exactly when `encodeToMiri p`
   diverges in $M_{\text{ref}}$. -/
theorem anneal_corresponds_to_miri : CorrespondenceClaim :=
  fun p q h_wf =>
    ⟨refWellFormed_of_wellFormed_base p q h_wf, behavior_iff_refBehavior_base p q,
      diverges_iff_refDiverges_base p q⟩

/-- Bidirectional fault-kind correspondence theorem:
fault kinds `.undefined` and `.unsupported` in $M_{\text{anneal}}$ correspond
one-to-one with `.ub` and `.blocked` in $M_{\text{ref}}$
(`faultToRefOutcome k`). -/
theorem reachesResult_fault_iff_refReachesOutcome :
    FaultEquivalenceClaim := by
  intro p q k
  have h_dec : decodeProg (encodeToMiri p) = some p := decodeProg_encodeProg_base p
  constructor
  · intro h_res
    unfold ReachesResult at h_res
    cases h_init : initState p q with
    | error k₀ =>
      rw [h_init] at h_res
      injection h_res with h_k
      subst h_k
      refine ⟨0, ?_⟩
      unfold RefReachesOutcome
      rw [(initRefState_sim_base 0 h_dec).1 k h_init]
    | ok s₀ =>
      rw [h_init] at h_res
      let ⟨s_end, h_reach, c, hc, h_es⟩ := h_res
      let ⟨n, h_in⟩ := exists_reachesN_of_reaches h_reach
      let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
        (initRefState_sim_base (n + 1) h_dec).2 s₀ h_init
      have h_budget : rs₀.stepsExecuted + n ≤ rs₀.maxSteps := by
        rw [h_steps₀, h_max₀, Nat.zero_add]
        exact Nat.le_succ n
      let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
        refReachesN_of_reachesN h_dec h_in h_sim₀ h_budget
      let ⟨f, _, _, _, _, _, hs, _, _, _, _, _, _, _, hframe⟩ := h_sim_end
      let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, _, _, _⟩ := hframe
      have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
        apply nat_blt_eq_true_of_lt
        rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
        exact Nat.lt_succ_self n
      have h_reval := evalRefStep_eq_base h_dec h_sim_end hs hbody hrbody h_lt c
      rw [h_es] at h_reval
      refine ⟨n + 1, ?_⟩
      unfold RefReachesOutcome
      rw [h_rinit]
      exact ⟨rs_end, refReaches_of_refReachesN h_rreach, c, hc, h_reval⟩
  · intro h_ex
    let ⟨maxSteps, h_ref⟩ := h_ex
    unfold RefReachesOutcome at h_ref
    cases h_init : initState p q with
    | error k₀ =>
      rw [(initRefState_sim_base maxSteps h_dec).1 k₀ h_init] at h_ref
      unfold ReachesResult
      rw [h_init]
      cases k₀ <;> cases k <;> cases h_ref <;> rfl
    | ok s₀ =>
      let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
        (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
      rw [h_rinit] at h_ref
      let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_ref
      let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches_base h_dec h_sim₀ h_rreach
      let ⟨f, _, _, _, _, _, hs, _, _, _, _, _, _, _, hframe⟩ := h_sim
      let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, hinv, _, _⟩ := hframe
      cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
      | false =>
        unfold evalRefStep at h_reval
        rw [h_lt] at h_reval
        cases k <;> cases h_reval
      | true =>
        rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
        cases h_es : evalStep p c s with
        | step s' =>
          let ⟨_, hs', _, _, _⟩ := evalStep_step_inv hs hbody hinv h_es
          rw [h_es, hs'] at h_reval
          cases k <;> cases h_reval
        | done out =>
          rw [h_es] at h_reval
          cases k <;> cases h_reval
        | fault k₀ =>
          rw [h_es] at h_reval
          have hk_eq : k₀ = k := by
            cases k₀ <;> cases k <;> cases h_reval <;> rfl
          subst hk_eq
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩

/-! ## Choice-Coupled Correspondence and Fault-Equivalence Claims -/

/-- Unconditional choice-coupled correspondence theorem
(`CorrespondenceAtChoicesClaim`). -/
theorem correspondence_at_choices_claim_holds_base :
    CorrespondenceAtChoicesClaim := by
  intro p q
  have h_dec : decodeProg (encodeToMiri p) = some p := decodeProg_encodeProg_base p
  refine ⟨refWellFormed_of_wellFormed_base p q, ?_, ?_, ?_⟩
  · intro choices h_pref
    let ⟨maxSteps, rs₀, rs, h_rinit, h_rreach⟩ := h_pref
    cases h_init : initState p q with
    | error k =>
      rw [(initRefState_sim_base maxSteps h_dec).1 k h_init] at h_rinit
      cases h_rinit
    | ok s₀ =>
      let ⟨rs₀', h_rinit', h_sim₀, _, _⟩ :=
        (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
      rw [h_rinit'] at h_rinit
      injection h_rinit with h_eq
      subst h_eq
      let ⟨s, h_reach, _⟩ := sim_of_refReachesAtChoices h_dec h_sim₀ h_rreach
      exact ⟨s₀, s, h_init, h_reach⟩
  · intro choices out h_rbeh
    let ⟨maxSteps, h_out⟩ := h_rbeh
    unfold RefReachesOutcomeAtChoices at h_out
    unfold BehaviorAtChoices ReachesResultAtChoices
    cases h_init : initState p q with
    | error k =>
      rw [(initRefState_sim_base maxSteps h_dec).1 k h_init] at h_out
      cases k <;> cases h_out.2
    | ok s₀ =>
      let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
        (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
      rw [h_rinit] at h_out
      let ⟨prefixChoices, c, rs, h_ceq, h_rreach, hc, h_reval⟩ := h_out
      let ⟨s, h_reach, h_sim⟩ := sim_of_refReachesAtChoices h_dec h_sim₀ h_rreach
      let ⟨f, _, _, _, _, _, hs, _, _, _, _, _, _, _, hframe⟩ := h_sim
      let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, hinv, _, _⟩ := hframe
      cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
      | false =>
        unfold evalRefStep at h_reval
        rw [h_lt] at h_reval
        cases h_reval
      | true =>
        rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
        cases h_es : evalStep p c s with
        | step s' =>
          let ⟨_, hs', _, _, _⟩ := evalStep_step_inv hs hbody hinv h_es
          rw [h_es, hs'] at h_reval
          cases h_reval
        | fault k =>
          rw [h_es] at h_reval
          cases k <;> cases h_reval
        | done out' =>
          rw [h_es] at h_reval
          dsimp only [mapStepRes, stepResultToRefOutcome] at h_reval
          injection h_reval with h_out_eq
          subst h_out_eq
          exact ⟨prefixChoices, c, s, h_ceq, h_reach, hc, h_es⟩
  · intro choiceStream h_rdiv
    exact divergesAtChoices_of_refDivergesAtChoices p q choiceStream h_rdiv

/-- Unconditional choice-coupled bidirectional fault-equivalence theorem
(`FaultEquivalenceAtChoicesClaim`). -/
theorem fault_equivalence_at_choices_claim_holds_base :
    FaultEquivalenceAtChoicesClaim := by
  intro p q choices k
  have h_dec : decodeProg (encodeToMiri p) = some p := decodeProg_encodeProg_base p
  constructor
  · intro h_res
    unfold ReachesResultAtChoices at h_res
    cases h_init : initState p q with
    | error k₀ =>
      rw [h_init] at h_res
      let ⟨h_ch, h_fk⟩ := h_res
      injection h_fk with h_k
      subst h_k
      refine ⟨0, ?_⟩
      unfold RefReachesOutcomeAtChoices
      rw [(initRefState_sim_base 0 h_dec).1 k h_init]
      exact ⟨h_ch, rfl⟩
    | ok s₀ =>
      rw [h_init] at h_res
      let ⟨prefixChoices, c, s_end, h_ceq, h_reach, hc, h_es⟩ := h_res
      let n := prefixChoices.length
      let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
        (initRefState_sim_base (n + 1) h_dec).2 s₀ h_init
      have h_budget : rs₀.stepsExecuted + prefixChoices.length ≤ rs₀.maxSteps := by
        rw [h_steps₀, h_max₀, Nat.zero_add]
        exact Nat.le_succ n
      let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
        refReachesAtChoices_of_reachesAtChoices h_dec h_reach h_sim₀ h_budget
      let ⟨f, _, _, _, _, _, hs, _, _, _, _, _, _, _, hframe⟩ := h_sim_end
      let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, _, _, _⟩ := hframe
      have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
        apply nat_blt_eq_true_of_lt
        rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
        exact Nat.lt_succ_self n
      have h_reval := evalRefStep_eq_base h_dec h_sim_end hs hbody hrbody h_lt c
      rw [h_es] at h_reval
      refine ⟨n + 1, ?_⟩
      unfold RefReachesOutcomeAtChoices
      rw [h_rinit]
      exact ⟨prefixChoices, c, rs_end, h_ceq, h_rreach, hc, h_reval⟩
  · intro h_ex
    let ⟨maxSteps, h_ref⟩ := h_ex
    unfold RefReachesOutcomeAtChoices at h_ref
    cases h_init : initState p q with
    | error k₀ =>
      rw [(initRefState_sim_base maxSteps h_dec).1 k₀ h_init] at h_ref
      unfold ReachesResultAtChoices
      rw [h_init]
      let ⟨h_ch, h_fk⟩ := h_ref
      have hk_eq : k₀ = k := by
        cases k₀ <;> cases k <;> cases h_fk <;> rfl
      subst hk_eq
      exact ⟨h_ch, rfl⟩
    | ok s₀ =>
      let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
        (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
      rw [h_rinit] at h_ref
      let ⟨prefixChoices, c, rs, h_ceq, h_rreach, hc, h_reval⟩ := h_ref
      let ⟨s, h_reach, h_sim⟩ := sim_of_refReachesAtChoices h_dec h_sim₀ h_rreach
      let ⟨f, _, _, _, _, _, hs, _, _, _, _, _, _, _, hframe⟩ := h_sim
      let ⟨body, rbody, _, hbody, hrbody, _, _, _, _, _, _, _, hinv, _, _⟩ := hframe
      cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
      | false =>
        unfold evalRefStep at h_reval
        rw [h_lt] at h_reval
        cases k <;> cases h_reval
      | true =>
        rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
        cases h_es : evalStep p c s with
        | step s' =>
          let ⟨_, hs', _, _, _⟩ := evalStep_step_inv hs hbody hinv h_es
          rw [h_es, hs'] at h_reval
          cases k <;> cases h_reval
        | done out =>
          rw [h_es] at h_reval
          cases k <;> cases h_reval
        | fault k₀ =>
          rw [h_es] at h_reval
          have hk_eq : k₀ = k := by
            cases k₀ <;> cases k <;> cases h_reval <;> rfl
          subst hk_eq
          unfold ReachesResultAtChoices
          rw [h_init]
          exact ⟨prefixChoices, c, s, h_ceq, h_reach, hc, h_es⟩

/-! ## Vendored `ExecutionMachine` & `OperandMachine` Wiring Claim -/

theorem miri_move_deinit_wiring_claim_holds_base : MiriMoveDeinitWiringClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K U C O X Host _ cfg limits c state
    rfl
  · intro K U C O X Host _ cfg limits h_true
    refine ⟨?_, ?_⟩ <;>
      change (cfg.deinitMovedPlace || cfg.access.deinitMovedPlace) = true <;>
      rw [h_true] <;> rfl
  · intro K U C hooks c localId known state h_false
    dsimp only [Miri.Interpreter.OperandMachine.evalOperand]
    rw [h_false]
    rfl
  · intro K U C hooks c localId known state state₁ frame₁ frame₂ imm layout
        h_true h_place h_cf h_ne h_rep
    dsimp only [Miri.Interpreter.OperandMachine.evalOperand, bind, Bind.bind,
      pure, Pure.pure]
    rw [h_true]
    change EStateM.bind
      (Miri.Interpreter.OperandMachine.evalPlaceToOp hooks c
        ⟨localId, Array.empty⟩ known) _ state = _
    rw [eStateM_bind_ok h_place]
    change EStateM.bind Miri.Interpreter.MachineHooks.currentFrame _ state₁ = _
    have h_curr : Miri.Interpreter.MachineHooks.currentFrame state₁ =
        .ok frame₁ state₁ := by
      dsimp only [Miri.Interpreter.MachineHooks.currentFrame, bind, Bind.bind,
        EStateM.bind, get, MonadState.get, getThe, MonadStateOf.get, EStateM.get]
      rw [h_cf]
      rfl
    rw [eStateM_bind_ok h_curr, h_rep]
    change (EStateM.bind (EStateM.pure frame₂) _ state₁) = _
    rw [eStateM_bind_pure]
    have h_scf : Miri.Interpreter.MachineHooks.setCurrentFrame frame₂ state₁ =
        .ok () { state₁ with stack := ⟨state₁.stack.frames.pop.push frame₂⟩ } := by
      dsimp only [Miri.Interpreter.MachineHooks.setCurrentFrame, bind, Bind.bind,
        EStateM.bind, get, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
        set, MonadStateOf.set, EStateM.set]
      rw [h_ne]
      rfl
    rw [eStateM_bind_ok h_scf]
    rfl
  · intro Prov Extra State hooks frame state localId known h_false
    dsimp only [Miri.Interpreter.evalOperand]
    rw [h_false]
    rfl
  · intro Prov Extra State hooks frame frame₁ frame₂ state state₁ localId
        known imm layout h_true h_place h_rep
    dsimp only [Miri.Interpreter.evalOperand]
    rw [h_true, h_place]
    dsimp only [Array.isEmpty, Array.size, List.length]
    rw [h_rep]
    rfl
  · intro K U m isMove
    rfl
  · intro P S C E Other Extern FnABI ArgABI h choice place snap
    exact ⟨rfl, rfl⟩

/-- Every non-exhausted `RefStep` transition (`.running` or `.returned`) is
directly witnessed by `RefAllowedStep` (`ExecutionMachine.AllowedStep` at
`refLimits`). -/
theorem refStep_sound_for_allowedStep_base :
    RefStepSoundForAllowedStepClaim := by
  intro rp rs out h_lt h_step
  let ⟨c, h_vc, h_ev⟩ := h_step
  dsimp only [evalRefStep] at h_ev
  rw [h_lt] at h_ev
  change (match Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfig rp) refLimits c rs.miri with
    | (miri', .ok true) =>
      if miri'.stack.frames.isEmpty then
        match refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace with
        | .ok retVal =>
          .returned (.returned ⟨retVal, miri'.machine.user.callerMem⟩)
        | .error k => faultToRefOutcome k
      else
        .running { rs with miri := miri', stepsExecuted := rs.stepsExecuted + 1 }
    | (_, .ok false) => .blocked
    | (_, .error (.undefinedBehavior _)) => .ub
    | (_, .error (.stack (.localExpectedLive _))) => .ub
    | (_, .error _) => .blocked) = out at h_ev
  cases h_st : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfig rp) refLimits c rs.miri with
  | mk miri' res =>
    rw [h_st] at h_ev
    cases res with
    | error err =>
      cases err with
      | undefinedBehavior _ =>
        change RefOutcome.ub = out at h_ev
        subst h_ev
        exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | stack se =>
        cases se with
        | localExpectedLive _ =>
          change RefOutcome.ub = out at h_ev
          subst h_ev
          exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
        | _ =>
          change RefOutcome.blocked = out at h_ev
          subst h_ev
          exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | _ =>
        change RefOutcome.blocked = out at h_ev
        subst h_ev
        exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | ok cont =>
      cases cont with
      | false =>
        change RefOutcome.blocked = out at h_ev
        subst h_ev
        exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | true =>
        change (if miri'.stack.frames.isEmpty then
            match refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace with
            | .ok retVal =>
              .returned (.returned ⟨retVal, miri'.machine.user.callerMem⟩)
            | .error k => faultToRefOutcome k
          else
            .running { rs with miri := miri', stepsExecuted := rs.stepsExecuted + 1 }) = out at h_ev
        cases h_emp : miri'.stack.frames.isEmpty with
        | false =>
          rw [h_emp] at h_ev
          change RefOutcome.running
            { rs with miri := miri', stepsExecuted := rs.stepsExecuted + 1 } = out at h_ev
          subst h_ev
          refine ⟨fun rs' h_r => ?_, fun _ h_t => (by cases h_t)⟩
          injection h_r with h_rs'
          subst h_rs'
          exact ⟨refLimits, c, h_vc, h_st⟩
        | true =>
          rw [h_emp] at h_ev
          change (match refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace with
            | .ok retVal =>
              .returned (.returned ⟨retVal, miri'.machine.user.callerMem⟩)
            | .error k => faultToRefOutcome k) = out at h_ev
          cases h_rv : refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace with
          | error k =>
            rw [h_rv] at h_ev
            cases k with
            | undefined =>
              change RefOutcome.ub = out at h_ev
              subst h_ev
              exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
            | unsupported =>
              change RefOutcome.blocked = out at h_ev
              subst h_ev
              exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
          | ok retVal =>
            rw [h_rv] at h_ev
            change RefOutcome.returned
              (.returned ⟨retVal, miri'.machine.user.callerMem⟩) = out at h_ev
            subst h_ev
            refine ⟨fun _ h_r => (by cases h_r), fun t h_t => ?_⟩
            injection h_t with h_teq
            exact ⟨miri', ⟨refLimits, c, h_vc, h_st⟩, h_emp, retVal, h_rv, h_teq.symm⟩

end Anneal.MirCorrespondence
