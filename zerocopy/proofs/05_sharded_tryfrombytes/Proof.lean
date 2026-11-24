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
import Anneal.SccSharding
import Proof.IdTree
import Proof.Shard_000
import Proof.Shard_001

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.SccSharding

private def rootTree : BinChunkTree Body :=
  .branch 13 Proof.Shard_000.shardTree Proof.Shard_001.shardTree

private theorem bodies_eq :
    Captured.program.bodies = BinChunkTree.toList rootTree :=
  BinChunkTree.toList_branch 13 Proof.Shard_000.shardTree
    Proof.Shard_001.shardTree Proof.Shard_000.shardBodies_eq
    Proof.Shard_001.shardBodies_eq

private theorem tree_wf : BinChunkTree.wf rootTree = true :=
  BinChunkTree.wf_branch Proof.Shard_000.shardSize
    Proof.Shard_000.shardWf Proof.Shard_001.shardWf

private theorem root_size : BinChunkTree.size rootTree = 25 :=
  BinChunkTree.size_branch 13 Proof.Shard_000.shardTree
    Proof.Shard_001.shardTree Proof.Shard_000.shardSize
    Proof.Shard_001.shardSize rfl

private theorem root_get0 {idx : Nat} {b : Body}
    (hLT : Nat.blt idx 13 = true)
    (hS : BinChunkTree.get? Proof.Shard_000.shardTree idx = some b) :
    Trusted.MirSemantics.getElem? Captured.program.bodies idx = some b := by
  rw [bodies_eq, BinChunkTree.getElem?_toList_eq_get? tree_wf idx]
  change (if Nat.blt idx 13 then BinChunkTree.get? Proof.Shard_000.shardTree idx
    else BinChunkTree.get? Proof.Shard_001.shardTree (idx - 13)) = some b
  rw [hLT]
  exact hS

private theorem root_get1 {idx off : Nat} {b : Body}
    (hLT : Nat.blt idx 13 = false)
    (hOff : idx - 13 = off)
    (hS : BinChunkTree.get? Proof.Shard_001.shardTree off = some b) :
    Trusted.MirSemantics.getElem? Captured.program.bodies idx = some b := by
  rw [bodies_eq, BinChunkTree.getElem?_toList_eq_get? tree_wf idx]
  change (if Nat.blt idx 13 then BinChunkTree.get? Proof.Shard_000.shardTree idx
    else BinChunkTree.get? Proof.Shard_001.shardTree (idx - 13)) = some b
  rw [hLT, hOff]
  exact hS

private theorem total_of_executes {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId =
      some body)
    (h_intr : BodyStaticIntrinsic body = true)
    (h_args : ValidEntryArgs body args)
    (h_exec : Executes body
      (mkState 0 0 (initLocalsLoop body args 0 body.locals)) ret) :
    Spec.ReturnsTotal Captured.program defId args ret := by
  have ⟨h_adm, h_nocall⟩ :=
    bodyStaticAdmitted_and_noCall_of_intrinsic (p := Captured.program)
      rfl rfl h_intr
  let ⟨fuel, h_execState⟩ := executes_iff_wpState.mp h_exec
  have h_execProg :
      execProg (entryProgForBody Captured.program defId) fuel { args := args }
        (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_entryProgForBody h_body h_adm h_args]
    exact (execOutcomeState_entryProg_iff h_body
      (isSingleFrame0_mkState 0 0 _) h_nocall).mpr h_execState
  have h_all := spec_and_behavior_of_wp_eq (wpProg_of_execProg h_execProg)
  exact ⟨h_all.2.2.2 _ rfl, h_all.2.2.1, h_all.2.1⟩

private theorem total_of_runs {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId =
      some body)
    (h_intr : BodyStaticIntrinsic body = true)
    (h_args : ValidEntryArgs body args)
    (h_runs : Runs body fuel args ret) :
    Spec.ReturnsTotal Captured.program defId args ret :=
  total_of_executes h_body h_intr h_args (run_executes h_runs)

private theorem usize_valid (n : Spec.UsizeWord) :
    checkVal (Spec.usizeVal n) (.int .isize false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .isize
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

private theorem markerSpec_intro {defId : DefId} {body : Body} {id : String}
    (h_body : Trusted.MirSemantics.getElem? Captured.program.bodies defId =
      some body)
    (h_id : body.identity = id)
    (h_safe : body.isUnsafe = false)
    (h_argc : body.argumentCount = 0)
    (h_intr : BodyStaticIntrinsic body = true)
    (h_args : ValidEntryArgs body [])
    (h_runs : Runs body 2 [] .unit) :
    Spec.UnitMarkerSpec Captured.program id :=
  ⟨defId, body, h_body, h_id, h_safe, h_argc,
    total_of_runs h_body h_intr h_args h_runs⟩

public theorem verify : Expected.claim := by
  have hLen : Captured.program.bodies.length = 25 := by
    rw [bodies_eq, BinChunkTree.toList_length, root_size]
  have hEntry : Nat.blt Captured.program.entryDefId
      (BinChunkTree.size rootTree) = true := by
    rw [root_size]
    rfl
  have hPos : Nat.blt 0 (BinChunkTree.size rootTree) = true := by
    rw [root_size]
    rfl
  have hUniq : BinChunkTree.allIdx
      (checkBodyIdentityAt Proof.IdTree.idDecisionTree) rootTree 0 = true :=
    BinChunkTree.allIdx_branch Proof.Shard_000.shardSize
      Proof.Shard_000.shardUniq Proof.Shard_001.shardUniq
  have hProp : Spec.specs.property Captured.program := by
    refine ⟨hLen, ?_, ?_, ?_,
        markerSpec_intro (root_get1 (idx := 17) rfl rfl Proof.Shard_001.get_4)
          Proof.Shard_001.b4_id Proof.Shard_001.b4_safe Proof.Shard_001.b4_argc
          Proof.Shard_001.b4_intr Proof.Shard_001.b4_valid Proof.Shard_001.b4_runs,
        markerSpec_intro (root_get1 (idx := 22) rfl rfl Proof.Shard_001.get_9)
          Proof.Shard_001.b9_id Proof.Shard_001.b9_safe Proof.Shard_001.b9_argc
          Proof.Shard_001.b9_intr Proof.Shard_001.b9_valid Proof.Shard_001.b9_runs,
        markerSpec_intro (root_get0 (idx := 12) rfl Proof.Shard_000.get_12)
          Proof.Shard_000.b12_id Proof.Shard_000.b12_safe Proof.Shard_000.b12_argc
          Proof.Shard_000.b12_intr Proof.Shard_000.b12_valid Proof.Shard_000.b12_runs,
        markerSpec_intro (root_get0 (idx := 7) rfl Proof.Shard_000.get_7)
          Proof.Shard_000.b7_id Proof.Shard_000.b7_safe Proof.Shard_000.b7_argc
          Proof.Shard_000.b7_intr Proof.Shard_000.b7_valid Proof.Shard_000.b7_runs,
        markerSpec_intro (root_get1 (idx := 15) rfl rfl Proof.Shard_001.get_2)
          Proof.Shard_001.b2_id Proof.Shard_001.b2_safe Proof.Shard_001.b2_argc
          Proof.Shard_001.b2_intr Proof.Shard_001.b2_valid Proof.Shard_001.b2_runs,
        markerSpec_intro (root_get1 (idx := 20) rfl rfl Proof.Shard_001.get_7)
          Proof.Shard_001.b7_id Proof.Shard_001.b7_safe Proof.Shard_001.b7_argc
          Proof.Shard_001.b7_intr Proof.Shard_001.b7_valid Proof.Shard_001.b7_runs,
        markerSpec_intro (root_get0 (idx := 10) rfl Proof.Shard_000.get_10)
          Proof.Shard_000.b10_id Proof.Shard_000.b10_safe Proof.Shard_000.b10_argc
          Proof.Shard_000.b10_intr Proof.Shard_000.b10_valid Proof.Shard_000.b10_runs,
        markerSpec_intro (root_get0 (idx := 5) rfl Proof.Shard_000.get_5)
          Proof.Shard_000.b5_id Proof.Shard_000.b5_safe Proof.Shard_000.b5_argc
          Proof.Shard_000.b5_intr Proof.Shard_000.b5_valid Proof.Shard_000.b5_runs,
        markerSpec_intro (root_get1 (idx := 16) rfl rfl Proof.Shard_001.get_3)
          Proof.Shard_001.b3_id Proof.Shard_001.b3_safe Proof.Shard_001.b3_argc
          Proof.Shard_001.b3_intr Proof.Shard_001.b3_valid Proof.Shard_001.b3_runs,
        markerSpec_intro (root_get1 (idx := 21) rfl rfl Proof.Shard_001.get_8)
          Proof.Shard_001.b8_id Proof.Shard_001.b8_safe Proof.Shard_001.b8_argc
          Proof.Shard_001.b8_intr Proof.Shard_001.b8_valid Proof.Shard_001.b8_runs,
        markerSpec_intro (root_get0 (idx := 11) rfl Proof.Shard_000.get_11)
          Proof.Shard_000.b11_id Proof.Shard_000.b11_safe Proof.Shard_000.b11_argc
          Proof.Shard_000.b11_intr Proof.Shard_000.b11_valid Proof.Shard_000.b11_runs,
        markerSpec_intro (root_get0 (idx := 6) rfl Proof.Shard_000.get_6)
          Proof.Shard_000.b6_id Proof.Shard_000.b6_safe Proof.Shard_000.b6_argc
          Proof.Shard_000.b6_intr Proof.Shard_000.b6_valid Proof.Shard_000.b6_runs,
        markerSpec_intro (root_get1 (idx := 14) rfl rfl Proof.Shard_001.get_1)
          Proof.Shard_001.b1_id Proof.Shard_001.b1_safe Proof.Shard_001.b1_argc
          Proof.Shard_001.b1_intr Proof.Shard_001.b1_valid Proof.Shard_001.b1_runs,
        markerSpec_intro (root_get1 (idx := 19) rfl rfl Proof.Shard_001.get_6)
          Proof.Shard_001.b6_id Proof.Shard_001.b6_safe Proof.Shard_001.b6_argc
          Proof.Shard_001.b6_intr Proof.Shard_001.b6_valid Proof.Shard_001.b6_runs,
        markerSpec_intro (root_get0 (idx := 9) rfl Proof.Shard_000.get_9)
          Proof.Shard_000.b9_id Proof.Shard_000.b9_safe Proof.Shard_000.b9_argc
          Proof.Shard_000.b9_intr Proof.Shard_000.b9_valid Proof.Shard_000.b9_runs,
        markerSpec_intro (root_get0 (idx := 4) rfl Proof.Shard_000.get_4)
          Proof.Shard_000.b4_id Proof.Shard_000.b4_safe Proof.Shard_000.b4_argc
          Proof.Shard_000.b4_intr Proof.Shard_000.b4_valid Proof.Shard_000.b4_runs,
        markerSpec_intro (root_get1 (idx := 18) rfl rfl Proof.Shard_001.get_5)
          Proof.Shard_001.b5_id Proof.Shard_001.b5_safe Proof.Shard_001.b5_argc
          Proof.Shard_001.b5_intr Proof.Shard_001.b5_valid Proof.Shard_001.b5_runs,
        markerSpec_intro (root_get1 (idx := 23) rfl rfl Proof.Shard_001.get_10)
          Proof.Shard_001.b10_id Proof.Shard_001.b10_safe Proof.Shard_001.b10_argc
          Proof.Shard_001.b10_intr Proof.Shard_001.b10_valid Proof.Shard_001.b10_runs,
        markerSpec_intro (root_get1 (idx := 13) rfl rfl Proof.Shard_001.get_0)
          Proof.Shard_001.b0_id Proof.Shard_001.b0_safe Proof.Shard_001.b0_argc
          Proof.Shard_001.b0_intr Proof.Shard_001.b0_valid Proof.Shard_001.b0_runs,
        markerSpec_intro (root_get0 (idx := 8) rfl Proof.Shard_000.get_8)
          Proof.Shard_000.b8_id Proof.Shard_000.b8_safe Proof.Shard_000.b8_argc
          Proof.Shard_000.b8_intr Proof.Shard_000.b8_valid Proof.Shard_000.b8_runs⟩
    · have hb := root_get1 (idx := 24) rfl rfl Proof.Shard_001.get_11
      exact ⟨24, Captured.Shard_001.body_11, hb,
        Proof.Shard_001.b11_id, Proof.Shard_001.b11_unsafe, Proof.Shard_001.b11_argc,
        total_of_runs hb Proof.Shard_001.b11_intr Proof.Shard_001.b11_valid
          Proof.Shard_001.b11_runs⟩
    · have hb0 := root_get0 (idx := 0) rfl Proof.Shard_000.get_0
      have hb1 := root_get0 (idx := 1) rfl Proof.Shard_000.get_1
      refine ⟨0, Captured.Shard_000.body_0, 1, Captured.Shard_000.body_1,
        hb0, Proof.Shard_000.b0_id, Proof.Shard_000.b0_safe,
        hb1, Proof.Shard_000.b1_id, Proof.Shard_000.b1_safe, fun n => ?_, ?_⟩
      · have hArgs : ValidEntryArgs Captured.Shard_000.body_0
            [Spec.usizeVal n] := by
          unfold ValidEntryArgs
          rw [Proof.Shard_000.b0_arg_tys]
          exact checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, usize_valid n, rfl⟩
        exact total_of_runs hb0 Proof.Shard_000.b0_intr hArgs
          (Proof.Shard_000.b0_runs (Spec.usizeVal n))
      · exact total_of_runs hb1 Proof.Shard_000.b1_intr Proof.Shard_000.b1_valid
          Proof.Shard_000.b1_runs
    · have hb2 := root_get0 (idx := 2) rfl Proof.Shard_000.get_2
      have hb3 := root_get0 (idx := 3) rfl Proof.Shard_000.get_3
      refine ⟨2, Captured.Shard_000.body_2, 3, Captured.Shard_000.body_3,
        hb2, Proof.Shard_000.b2_id, Proof.Shard_000.b2_safe,
        hb3, Proof.Shard_000.b3_id, Proof.Shard_000.b3_safe, fun n => ?_, fun m => ?_⟩
      · have hv := usize_valid n
        have hArgs : ValidEntryArgs Captured.Shard_000.body_2
            [Spec.usizeVal n] := by
          unfold ValidEntryArgs
          rw [Proof.Shard_000.b2_arg_tys]
          exact checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, hv, rfl⟩
        exact total_of_executes hb2 Proof.Shard_000.b2_intr hArgs
          (Proof.Shard_000.b2_exec hv)
      · have hv := usize_valid m
        have hArgs : ValidEntryArgs Captured.Shard_000.body_3
            [Spec.usizeVal m] := by
          unfold ValidEntryArgs
          rw [Proof.Shard_000.b3_arg_tys]
          exact checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, hv, rfl⟩
        exact total_of_executes hb3 Proof.Shard_000.b3_intr hArgs
          (Proof.Shard_000.b3_exec hv)
  exact unitTheorem_of_shardedTree Proof.IdTree.idDecisionTree
    rfl bodies_eq rfl rfl tree_wf hEntry hPos hUniq
    ⟨Proof.Shard_000.shardVerified, Proof.Shard_001.shardVerified⟩ hProp

end Proof
