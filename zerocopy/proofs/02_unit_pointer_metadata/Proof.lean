-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Expected
import Anneal.MirWp
import Anneal.Framework

namespace Proof

open Specs.zerocopy.zc02_unit_pointer_metadata
  (fn0_id fn0_sig fn0_contract fn1_id fn1_sig fn1_contract specs)
open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
open Anneal.MirWp Anneal.Framework

private theorem body0_adm :
    BodyStaticAdmitted Captured.program Captured.body_0 = true := rfl

private theorem body1_adm :
    BodyStaticAdmitted Captured.program Captured.body_1 = true := rfl

/-- `0usize`, the value `to_elem_count` returns and a witness `usize` argument
for the non-vacuity obligation of `from_elem_count`. -/
private def usizeZero : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩

private theorem body0_runs (v : Val) :
    Runs Captured.body_0 2 [v] .unit := rfl

private theorem body1_runs :
    Runs Captured.body_1 2 [.unit] usizeZero := rfl

/-- A concrete run of the entry body yields an exact-outcome `wpProg` proof. -/
private theorem wp_of_runs {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_runs : Runs body fuel args ret) :
    wpProg (entryProgForBody Captured.program defId) fuel { args := args }
      (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩) := by
  have h_execProg :
      execProg (entryProgForBody Captured.program defId) fuel { args := args }
        (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_entryProgForBody h_body h_adm h_args]
    exact
      (execOutcomeState_entryProg_iff h_body (isSingleFrame0_mkState 0 0 _)).mpr
        h_runs
  exact wpProg_of_execProg h_execProg

private theorem satisfies_of_wp {defId : DefId} {body : Body}
    {gaps : List DisclosedGap} {e : MirVerifiedEntry}
    (hId : body.identity = e.identity)
    (hSig : bodyMatchesMirSignature body e.sig = true)
    (hRun : ∀ args : List Val, ValidEntryArgs body args →
      ∃ ret : Val,
        ValidMirReturnVal body ret ⟨[]⟩ ∧
        wpProg (entryProgForBody Captured.program defId) 2
          { args := args } (fun o => o = .returned ⟨ret, ⟨[]⟩⟩) ∧
        e.contract.postReturn { args := args } ret ⟨[]⟩)
    (hNonVac : NonVacuousEntry MirProfileV1 body
      (e.contract.effectiveBehaviorPre body.isUnsafe))
    (hReq : e.requireInhabited = true) :
    BodySatisfiesEntry MirProfileV1 Captured.program defId gaps body e := by
  refine ⟨rfl, hId, hSig, absurd_mem_nil, ?_, ?_,
    Or.inl ⟨hReq, hNonVac⟩⟩
  · intro q hDom _
    cases q with
    | mk args callerMem =>
      let ⟨valid, hMem⟩ := hDom
      dsimp at valid hMem
      subst hMem
      let ⟨_, _, hWp, _⟩ := hRun args valid
      exact (spec_and_behavior_of_wp_eq hWp).1
  · intro q hDom _
    cases q with
    | mk args callerMem =>
      let ⟨valid, hMem⟩ := hDom
      dsimp at valid hMem
      subst hMem
      let ⟨ret, hRetVal, hWp, hPost⟩ := hRun args valid
      have hSpec := spec_and_behavior_of_wp_eq hWp
      refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
      · intro r m ⟨out, hBehOut, hMap⟩
        have hEq := (hSpec.2.2.2 _ rfl).2 out hBehOut
        subst hEq
        injection hMap with hR hM
        subst hR hM
        exact ⟨hRetVal, hPost⟩
      · intro m ⟨out, hBehOut, hMap⟩
        have hEq := (hSpec.2.2.2 _ rfl).2 out hBehOut
        subst hEq
        cases hMap
      · intro m ⟨out, hBehOut, hMap⟩
        have hEq := (hSpec.2.2.2 _ rfl).2 out hBehOut
        subst hEq
        cases hMap

private theorem body0_entry :
    BodySatisfiesEntry MirProfileV1 Captured.program 0 specs.gaps
      Captured.body_0
      { identity := fn0_id, sig := fn0_sig, contract := fn0_contract } :=
  satisfies_of_wp rfl rfl
    (fun args valid => by
      have hMatch : checkArgsMatch args [.int .isize false] = true := valid
      let ⟨v, rest, hEq, _, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
      have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
      subst hEq; subst hNil
      exact ⟨.unit, ⟨rfl, rfl⟩,
        wp_of_runs rfl body0_adm valid (body0_runs v), rfl⟩)
    (Or.inl ⟨{ args := [usizeZero] }, ⟨rfl, rfl⟩,
      ⟨fun h => Bool.noConfusion h, True.intro⟩⟩)
    rfl

private theorem body1_entry :
    BodySatisfiesEntry MirProfileV1 Captured.program 1 specs.gaps
      Captured.body_1
      { identity := fn1_id, sig := fn1_sig, contract := fn1_contract } :=
  satisfies_of_wp rfl rfl
    (fun args valid => by
      have hMatch : checkArgsMatch args [.unit] = true := valid
      let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
      have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
      have hUnit : v = .unit := checkVal_unit_iff.mp hv
      subst hEq; subst hNil; subst hUnit
      exact ⟨usizeZero, ⟨rfl, rfl⟩,
        wp_of_runs rfl body1_adm valid body1_runs, rfl⟩)
    (Or.inl ⟨{ args := [.unit] }, ⟨rfl, rfl⟩,
      ⟨fun h => Bool.noConfusion h, True.intro⟩⟩)
    rfl

theorem verify : Expected.claim := by
  dsimp only [Expected.claim, UnitMirEnvelopeTheoremV1, MirEnvelopeHolds,
    EnvelopeTheorem, mkEnvelope, AllSpecLaws, NoDupStrings, List.map,
    List.append, specs]
  refine ⟨rfl, (fun _ => List.Mem.head _),
    ⟨⟨nonEmpty_profile_id, rfl, ?_, rfl, (fun _ => List.Mem.head _),
        nonEmpty_oracle_id, ?_, (fun _ h => List.Mem.tail _ h)⟩,
      ?_, ?_, ?_, (fun _ h => by cases h),
      (fun _ h => by cases h), ?_⟩,
    True.intro, True.intro⟩
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact body0_adm
    | succ k =>
      cases k with
      | zero =>
        injection hGet with hEq
        subst hEq
        exact body1_adm
      | succ _ =>
        dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
        cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · refine ⟨ne_string_of_len_beq_false rfl, ?_,
      ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩⟩
    intro t hMem
    cases hMem with
    | head => exact ne_string_of_len_beq_false rfl
    | tail _ hNil => cases hNil
  · intro e hMem
    cases hMem with
    | head => exact ⟨0, Captured.body_0, rfl, body0_entry⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨1, Captured.body_1, rfl, body1_entry⟩
      | tail _ hNil => cases hNil
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ k =>
      cases k with
      | zero =>
        injection hGet with hEq
        subst hEq
        exact List.Mem.tail _ (List.Mem.head _)
      | succ _ =>
        dsimp [Captured.program, Trusted.MirSemantics.getElem?] at hGet
        cases hGet

end Proof
