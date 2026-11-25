-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.CnfOrd.Ord
public import Anneal.CnfOrd.Worklist
public import Anneal.ByteSubLens.Lens
public import Anneal.WavefrontReclaim.SpatialPcm
public import Anneal.WavefrontReclaim.Wavefront

public section

/-!
# Concrete Wavefront Drain & Loan Reclamation Canaries
(`Anneal.WavefrontReclaim.Canaries`)

End-to-end concrete witnesses and single-cause fail-closed negative regressions
exercising `Anneal.WavefrontReclaim`:

1. `nonemptyPool_pureFastpath_witness`: mod-`2^32` wraparound, non-empty
   worklist fast-path pure-lifted write (`+ 32 -> 42`), and refutation of
   unbacked `.empty` pool capacity.
2. `submitTaskBurst_amortized_witness_and_unfunded_refutation`: amortized
   ordinal-debt consumption, refutation of double-spending `ordDebtProp` in
   `VSepWpOrdRel`, and refutation of zero-debt task submission.
3. `multiRank_5_to_0_wavefront_drain_witness`: concrete 10-step rank
   `5 -> 3 -> 2 -> 1 -> 0` drain reclaiming `path0` to `.activeMut` (`42`).
4. `endToEnd_checkout_burst_drain_reclaim_pureLift_verified`: full 5-stage
   chained `VSepWpOrdRel` lifecycle on `Trusted.MirSemantics.MemoryState`
   preserving spatial frame `cellAuthProp path2 99`.
5. `updateSpatialCell_positive_witness`: spatial cell capability/authority
   mutation preserving `ordDebtProp` and `WorldMatches`.
6. `canary_wavefrontReclaim_negative_fail_closed_tests`: 14 single-cause
   fail-closed negative regressions (15 conjuncts) across leaf writeback, spawn
   admissibility, pure-lifted access phases, checkout, burst submission, cell
   updates, and `byteSubLensPut` memory-write failures.

All definitions are computable (`0` `noncomputable`, `0` `._unsafe_rec`,
`0` `omega`, `0` `decide`). Pure evaluation canaries use `[]` zero axioms;
theorems touching `Trusted.MirSemantics` byte lenses / `Nat.mod` use at most
`[propext]` (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.WavefrontReclaim

open Trusted.MirAst Trusted.MirSemantics
open Anneal.CnfOrd Anneal.ByteSubLens

private theorem boolFalseNeTrueC (h : false = true) : False :=
  Bool.noConfusion h

private theorem bandLeftC {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrueC h)
  | true => rfl

private theorem bandRightC {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrueC h)
  | true => exact h

/-- Constructs a concrete 24-byte mutable `Trusted.MirSemantics.MemoryState`
allocation (`allocId = 2`, 4-byte aligned) holding six big-endian `u32` fields.
-/
@[expose] def wfMkCNodeMem (e ac s0 s1 s2 s3 : Nat) : MemoryState :=
  ⟨3, [⟨2, 2, .mut,
    wfEncodeU32BeSlice e ++ wfEncodeU32BeSlice ac ++ wfEncodeU32BeSlice s0 ++
    wfEncodeU32BeSlice s1 ++ wfEncodeU32BeSlice s2 ++ wfEncodeU32BeSlice s3,
    true⟩]⟩

/-- Concrete 24-byte initial memory fixture (`epoch = 10`, `activeCount = 0`).
-/
@[expose] def wfCNode24Mem0 : MemoryState := wfMkCNodeMem 10 0 0 77 0 99

/-- 4-byte big-endian `u32` sub-lens for the `epoch` field at offset `0`. -/
@[expose] def wfCNodeEpochLens : ByteSubLens := ⟨2, 0, 4, 2⟩

/-- 4-byte big-endian `u32` sub-lens for the `activeCount` field at offset `4`.
-/
@[expose] def wfCNodeActiveCountLens : ByteSubLens := ⟨2, 4, 4, 2⟩

private theorem wfCNode24Mem0_get_epoch :
    byteSubLensGet wfCNodeEpochLens wfCNode24Mem0 =
      some (wfEncodeU32BeSlice 10) :=
  rfl

private theorem wfCNode24Mem0_get_activeCount :
    byteSubLensGet wfCNodeActiveCountLens wfCNode24Mem0 =
      some (wfEncodeU32BeSlice 0) :=
  rfl

/-- Concrete world with both `fifoQueue` and `stealDeque` non-empty while
`path0` remains `.activeMut` (`10`) and `path1` is `.spatialCheckedOut 1`. -/
@[expose] def nonemptyPoolWitnessWorld : WavefrontWorld :=
  { mem := wfCNode24Mem0
    loans := [
      WfLoanEntry.mk path0 .activeMut wfCNodeEpochLens 10,
      WfLoanEntry.mk path1 (.spatialCheckedOut 1) wfCNodeActiveCountLens 0
    ]
    cells := .empty
    fifoQueue := [WorkerTask.mk 0 2 1 path1 1 5]
    stealDeque := [WorkerTask.mk 1 0 0 path1 1 7]
    nextTaskId := 2
    completedCount := 0
    stepCount := 5 }

/-- Backing pool resource tree for `nonemptyPoolWitnessWorld`. -/
@[expose] def nonemptyPoolWitnessRes : ResTrie ResElem :=
  singleRes poolPath (.pool [(5, 1), (4, 1), (1, 1)])

/-- Concrete fast-path canary (`[propext]`): mod-`2^32` wraparound, non-empty
queues, unbacked `.empty` refutation, and pure-lifted `+ 32 -> 42` preserving
`worldMeasure`. -/
theorem nonemptyPool_pureFastpath_witness :
    wrapU32 (4294967295 + 2) = 1 ∧
    wfEncodeU32BeSlice (4294967295 + 2) =
      wfEncodeU32BeSlice (wrapU32 (4294967295 + 2)) ∧
    nonemptyPoolWitnessWorld.fifoQueue ≠ [] ∧
    nonemptyPoolWitnessWorld.stealDeque ≠ [] ∧
    WorldMatches [5] nonemptyPoolWitnessRes nonemptyPoolWitnessWorld ∧
    (WorldMatches [5] .empty nonemptyPoolWitnessWorld → False) ∧
    (∃ wOut : WavefrontWorld,
      evalHybridCmd (.pureLiftSafe path0 32) nonemptyPoolWitnessWorld =
        .returned wOut ∧
      WorldMatches [5] nonemptyPoolWitnessRes wOut ∧
      worldMeasure wOut = worldMeasure nonemptyPoolWitnessWorld ∧
      byteSubLensGet wfCNodeEpochLens wOut.mem = some (wfEncodeU32BeSlice 42) ∧
      (worldMeasure wOut = [] → False)) := by
  have hMWitness :
      WorldMatches [5] nonemptyPoolWitnessRes nonemptyPoolWitnessWorld :=
    WorldMatches.mk rfl
      ⟨rfl, ⟨rfl, True.intro⟩, rfl, rfl, wfCNode24Mem0_get_epoch,
       ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_activeCount, True.intro⟩⟩
      rfl
      rfl
      (fun cid => by
        dsimp only [nonemptyPoolWitnessRes]
        rw [singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
        exact True.intro)
      (fun lid2 => by
        dsimp only [nonemptyPoolWitnessRes]
        rw [singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
        exact True.intro)
  have hUnbackedFalse :
      WorldMatches [5] .empty nonemptyPoolWitnessWorld → False := fun hBad =>
    boolFalseNeTrueC hBad.poolDebtOk
  have hActW :
      ActivePureLoanAt path0 wfCNodeEpochLens 10 nonemptyPoolWitnessWorld :=
    ⟨WfLoanEntry.mk path0 .activeMut wfCNodeEpochLens 10, rfl, rfl, rfl, rfl⟩
  refine ⟨rfl, rfl, (fun h => by nomatch h), (fun h => by nomatch h),
    hMWitness, hUnbackedFalse, ?_⟩
  cases (vsepWpOrdRel_pure_fastpath path0 wfCNodeEpochLens 10 32).2 [5] vemp
      nonemptyPoolWitnessRes nonemptyPoolWitnessWorld hActW
      (vsep_vemp_intro [5] vemp nonemptyPoolWitnessRes True.intro)
      hMWitness with
  | intro wOutW hwW =>
    have h42Eq : wrapU32 (10 + 32) = 42 := rfl
    have hGet42 := hwW.2.2.2.2.2.1
    rw [h42Eq] at hGet42
    have hMeasW : worldMeasure wOutW = worldMeasure nonemptyPoolWitnessWorld :=
      hwW.2.2.1
    exact ⟨wOutW, hwW.1, hwW.2.1, hMeasW, hGet42,
      fun hEmpty => by rw [hMeasW] at hEmpty; nomatch hEmpty⟩

/-- Concrete checked-out world fixture for amortized burst submission. -/
@[expose] def burstWitnessWorld0 : WavefrontWorld :=
  { mem := wfCNode24Mem0
    loans := [WfLoanEntry.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10]
    cells := .empty
    fifoQueue := []
    stealDeque := []
    nextTaskId := 1
    completedCount := 0
    stepCount := 0 }

/-- Concrete resource tree carrying `ordDebtProp [(5, 2)]` and
`checkedOutLoanProp path0 77 10`. -/
@[expose] def burstWitnessRes0 : ResTrie ResElem :=
  ResTrie.modifyBits (checkedLoanPath path0)
    (fun _ => some (.checkedOutLoan 77 10))
    (ordDebtTree [(5, 2)])

/-- Concrete amortized burst canary (`[]`): verifies strict ordinal growth
within the spent debt budget, consumes `ordDebtProp`, refutes retaining
`ordDebtProp [(5, 2)]` in the `VSepWpOrdRel` postcondition (no double-spend),
and refutes unfunded zero-debt `VSepWpOrdRel` submission. -/
theorem submitTaskBurst_amortized_witness_and_unfunded_refutation :
    WorldMatches [0] burstWitnessRes0 burstWitnessWorld0 ∧
    (∃ (wOut : WavefrontWorld) (rOut : ResTrie ResElem),
      evalHybridCmd (.submitTaskBurst 2 0 path0 77 5) burstWitnessWorld0 =
        .returned wOut ∧
      cnfLt (worldMeasure burstWitnessWorld0) (worldMeasure wOut) = true ∧
      cnfLt (worldMeasure wOut)
        (cnfAddOrd [(5, 2)] (worldMeasure burstWitnessWorld0)) = true ∧
      WorldMatches [1] rOut wOut ∧
      (poolBackingProp [(5, 2)]).holds [1] rOut ∧
      ((ordDebtProp [(5, 2)]).holds [1] rOut → False)) ∧
    (VSepWpOrdRel (.submitTaskBurst 2 0 path0 77 5) (.amortized [(5, 2)])
      (fun _ => True)
      (vsep (ordDebtProp [(5, 2)]) (checkedOutLoanProp path0 77 10))
      (fun _ => ordDebtProp [(5, 2)]) → False) ∧
    (VSepWpOrdRel (.submitTaskBurst 2 0 path0 77 5) (.amortized [(5, 2)])
      (fun w =>
        wfFindLoan path0 w.loans =
          some ⟨path0, .spatialCheckedOut 77, wfCNodeEpochLens, 10⟩)
      vemp (fun _ => vemp) → False) := by
  have hM0 : WorldMatches [0] burstWitnessRes0 burstWitnessWorld0 :=
    WorldMatches.mk rfl
      ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_epoch, True.intro⟩
      rfl
      rfl
      (fun cid => by
        dsimp only [burstWitnessRes0, ordDebtTree]
        rw [resTrie_getBits_modifyBits_ne (checkedLoanPath path0)
              (cellPath cid) rfl rfl,
          resTrie_getBits_modifyBits_ne debtPath (cellPath cid) rfl rfl,
          singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
        exact True.intro)
      (fun lid2 => by
        cases hEq0 : Pos4.beq path0 lid2 with
        | true =>
          rw [← pos4_eq_of_beq path0 lid2 hEq0]
          dsimp only [burstWitnessRes0]
          rw [resTrie_getBits_modifyBits_same]
          exact ⟨rfl,
            ⟨⟨path0, .spatialCheckedOut 77, wfCNodeEpochLens, 10⟩,
              rfl, rfl, rfl⟩⟩
        | false =>
          have hNe0 :
              listBoolBeq (checkedLoanPath path0) (checkedLoanPath lid2) =
                false := by
            dsimp only [checkedLoanPath, listBoolBeq, Bool.and]
            exact hEq0
          dsimp only [burstWitnessRes0, ordDebtTree]
          rw [resTrie_getBits_modifyBits_ne (checkedLoanPath path0)
                (checkedLoanPath lid2) rfl hNe0,
            resTrie_getBits_modifyBits_ne debtPath
              (checkedLoanPath lid2) rfl rfl,
            singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
          exact True.intro)
  let wOutB : WavefrontWorld :=
    { mem := wfCNode24Mem0
      loans := [WfLoanEntry.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens
        10]
      cells := .empty
      fifoQueue := [WorkerTask.mk 1 2 0 path0 77 5]
      stealDeque := []
      nextTaskId := 2
      completedCount := 0
      stepCount := 1 }
  let rOutB : ResTrie ResElem := singleRes poolPath (.pool [(5, 2)])
  have hMOutB : WorldMatches [1] rOutB wOutB :=
    WorldMatches.mk rfl
      ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_epoch, True.intro⟩
      rfl
      rfl
      (fun cid => by
        dsimp only [rOutB]
        rw [singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
        exact True.intro)
      (fun lid2 => by
        dsimp only [rOutB]
        rw [singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
        exact True.intro)
  have hNoDoubleSpend : (ordDebtProp [(5, 2)]).holds [1] rOutB → False := by
    intro hD
    cases hD with
    | mk hEx =>
      cases hEx with
      | intro rf hMrg =>
      have hG :=
        resTrie_getBits_resTrieMerge debtPath (ordDebtTree [(5, 2)]) rf rOutB
          rfl hMrg
      have hGetD :
          ResTrie.getBits debtPath (ordDebtTree [(5, 2)]) =
            some (.debt [(5, 2)]) := rfl
      have hGetOut : ResTrie.getBits debtPath rOutB = none := rfl
      rw [hGetD, hGetOut] at hG
      cases hGf : ResTrie.getBits debtPath rf with
      | none =>
        rw [hGf] at hG
        dsimp only [optOp] at hG
        injection hG with hBad
        nomatch hBad
      | some ef =>
        rw [hGf] at hG
        cases ef with
        | pool _ | checkedOutLoan _ _ | cell _ =>
          dsimp only [optOp, resMerge] at hG; nomatch hG
        | debt _ =>
          dsimp only [optOp, resMerge] at hG
          injection hG with hBad
          nomatch hBad
  have hZeroDebtImpossible :
      VSepWpOrdRel (.submitTaskBurst 2 0 path0 77 5) (.amortized [(5, 2)])
        (fun w =>
          wfFindLoan path0 w.loans =
            some ⟨path0, .spatialCheckedOut 77, wfCNodeEpochLens, 10⟩)
        vemp (fun _ => vemp) → False := by
    intro hBadWp
    have hM0Empty : WorldMatches [0] .empty burstWitnessWorld0 :=
      WorldMatches.mk rfl
        ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_epoch, True.intro⟩
        rfl
        rfl
        (fun cid => by rw [resTrie_getBits_empty]; exact True.intro)
        (fun lid2 => by rw [resTrie_getBits_empty]; exact True.intro)
    cases hBadWp.run [0] vemp .empty burstWitnessWorld0 rfl
        (vsep_vemp_intro [0] vemp .empty True.intro) hM0Empty with
    | intro wOut hw =>
      cases hw with
      | intro rOut hr =>
        cases hr with
        | intro vOut hv =>
          have hEv := hv.1
          dsimp only [evalHybridCmd, execSubmitTaskBurst, burstWitnessWorld0,
            wfFindLoan, List.foldr, Pos4.beq, pos4ToList, listBoolBeq,
            Bool.and, loanPhaseMatchesScope, Nat.beq] at hEv
          injection hEv with hwEq
          have hPd := hv.2.2.2.2.1.poolDebtOk
          dsimp only [checkWorldMatchesPoolBool] at hPd
          have hPcEmpty : extractPoolCap .empty = some [] := rfl
          rw [hv.2.2.1, hPcEmpty] at hPd
          dsimp only at hPd
          cases hDc : extractDebtCap rOut with
          | none => rw [hDc] at hPd; exact boolFalseNeTrueC hPd
          | some dc =>
            rw [hDc] at hPd
            dsimp only at hPd
            have hLeNil := bandLeftC hPd
            rw [← hwEq] at hLeNil
            exact boolFalseNeTrueC hLeNil
  have hDoubleSpendImpossible :
      VSepWpOrdRel (.submitTaskBurst 2 0 path0 77 5) (.amortized [(5, 2)])
        (fun _ => True)
        (vsep (ordDebtProp [(5, 2)]) (checkedOutLoanProp path0 77 10))
        (fun _ => ordDebtProp [(5, 2)]) → False := by
    intro hBadDbl
    have hPreBurst :
        (vsep (vsep (ordDebtProp [(5, 2)]) (checkedOutLoanProp path0 77 10))
          vemp).holds [0] burstWitnessRes0 :=
      ⟨burstWitnessRes0, .empty, rfl,
        ⟨ordDebtTree [(5, 2)],
          singleRes (checkedLoanPath path0) (.checkedOutLoan 77 10),
          rfl, resTrieSub_refl _, resTrieSub_refl _⟩,
        True.intro⟩
    cases hBadDbl.run [0] vemp burstWitnessRes0 burstWitnessWorld0 True.intro
        hPreBurst hM0 with
    | intro wOut hw =>
      cases hw with
      | intro rOut hr =>
        cases hr with
        | intro vOut hv =>
          have hEvB :
              evalHybridCmd (.submitTaskBurst 2 0 path0 77 5)
                burstWitnessWorld0 = .returned wOutB := rfl
          have hEv := hv.1
          rw [hEvB] at hEv
          injection hEv with hwEq
          have hPcInit : extractPoolCap burstWitnessRes0 = some [(5, 2)] := rfl
          have hPcOut : extractPoolCap rOut = some [(5, 2)] :=
            Eq.trans hv.2.2.1 hPcInit
          cases hv.2.2.2.1 with
          | intro r1 hr1 =>
            cases hr1 with
            | intro r2 hm12 =>
              cases hm12.2.1 with
              | mk hEx1 =>
                cases hEx1 with
                | intro rf1 hM1 =>
                  cases resTrieMerge_assoc (ordDebtTree [(5, 2)]) rf1 r2 r1
                      rOut hM1 hm12.1 with
                  | intro rf hAssoc =>
                    have hG :=
                      resTrie_getBits_resTrieMerge debtPath
                        (ordDebtTree [(5, 2)]) rf rOut rfl hAssoc.2
                    have hGetD :
                        ResTrie.getBits debtPath (ordDebtTree [(5, 2)]) =
                          some (.debt [(5, 2)]) := rfl
                    rw [hGetD] at hG
                    have hPd := hv.2.2.2.2.1.poolDebtOk
                    dsimp only [checkWorldMatchesPoolBool] at hPd
                    rw [hPcOut, ← hwEq] at hPd
                    cases hGf : ResTrie.getBits debtPath rf with
                    | none =>
                      rw [hGf] at hG
                      dsimp only [optOp] at hG
                      injection hG with hOutEq
                      have hDcOut : extractDebtCap rOut = some [(5, 2)] := by
                        dsimp only [extractDebtCap]
                        rw [← hOutEq]
                        rfl
                      rw [hDcOut] at hPd
                      dsimp only at hPd
                      exact boolFalseNeTrueC (bandRightC hPd)
                    | some ef =>
                      rw [hGf] at hG
                      cases ef with
                      | pool _ | checkedOutLoan _ _ | cell _ =>
                        dsimp only [optOp, resMerge] at hG
                        nomatch hG
                      | debt df =>
                        dsimp only [optOp, resMerge] at hG
                        injection hG with hOutEq
                        have hDcOut :
                            extractDebtCap rOut =
                              some (cnfNatAdd [(5, 2)] df) := by
                          dsimp only [extractDebtCap]
                          rw [← hOutEq]
                          exact congrArg some
                            (cnfNorm_eq_of_canonical _
                              (isCanonicalCnf_cnfNatAdd [(5, 2)] df))
                        rw [hDcOut] at hPd
                        dsimp only at hPd
                        have hBle := bandRightC hPd
                        have hMeasB : worldMeasure wOutB = [(5, 1)] := rfl
                        rw [hMeasB] at hBle
                        change cnfBle
                          (cnfNatAdd (cnfNatAdd [(5, 2)] df) [(5, 1)]) [(5, 2)]
                            = true at hBle
                        rw [cnfNatAdd_comm [(5, 2)] df,
                          cnfNatAdd_assoc df [(5, 2)] [(5, 1)]] at hBle
                        have h23 : cnfNatAdd [(5, 2)] [(5, 1)] = [(5, 3)] := rfl
                        rw [h23] at hBle
                        have hLt3 :
                            cnfLt [(5, 2)] (cnfNatAdd df [(5, 3)]) = true :=
                          cnfLt_cnfAddOrd_of_lt df [(5, 2)] [(5, 3)] rfl rfl
                        exact boolFalseNeTrueC
                          (cnfLt_of_lt_of_ble [(5, 2)] (cnfNatAdd df [(5, 3)])
                            [(5, 2)] hLt3 hBle)
  exact ⟨hM0,
    ⟨wOutB, rOutB, rfl, rfl, rfl, hMOutB, resTrieSub_refl rOutB,
      hNoDoubleSpend⟩,
    hDoubleSpendImpossible,
    hZeroDebtImpossible⟩

/-- 5-tier strictly descending rank tower `[5, 3, 2, 1, 0]`. -/
@[expose] def wfTower53210 : List Nat := [5, 3, 2, 1, 0]

/-- Admissible spawn policy descending along `wfTower53210` with fanout `1`. -/
@[expose] def wfPolicyTower53210 : SpawnPolicy := towerLookupNext wfTower53210 1
    0

/-- Concrete rank-5 initial world fixture with two leaves summing `+ 32`. -/
@[expose] def multiRankWitnessWorld0 : WavefrontWorld :=
  { mem := wfCNode24Mem0
    loans := [WfLoanEntry.mk path0 (.spatialCheckedOut 1) wfCNodeEpochLens 10]
    cells := .empty
    fifoQueue := [WorkerTask.mk 0 5 1 path0 1 16]
    stealDeque := []
    nextTaskId := 1
    completedCount := 0
    stepCount := 0 }

/-- Intermediate memory fixture (`epoch = 26`) for the 10-step drain witness. -/
@[expose] def mwMem26 : MemoryState := wfMkCNodeMem 26 0 0 77 0 99
/-- Final memory fixture (`epoch = 42`) for the 10-step drain witness. -/
@[expose] def mwMem42 : MemoryState := wfMkCNodeMem 42 0 0 77 0 99
/-- Checked-out loan list (`val = 10`) for the 10-step drain witness. -/
@[expose] def mwLoans10 : List WfLoanEntry :=
  [WfLoanEntry.mk path0 (.spatialCheckedOut 1) wfCNodeEpochLens 10]
/-- Checked-out loan list (`val = 26`) after first leaf writeback. -/
@[expose] def mwLoans26 : List WfLoanEntry :=
  [WfLoanEntry.mk path0 (.spatialCheckedOut 1) wfCNodeEpochLens 26]
/-- Reclaimed `.activeMut` loan list (`val = 42`) after final leaf writeback. -/
@[expose] def mwLoans42 : List WfLoanEntry :=
  [WfLoanEntry.mk path0 .activeMut wfCNodeEpochLens 42]

/-- Step-1 world state in `multiRank_5_to_0_wavefront_drain_witness`. -/
@[expose] def mwW1 : WavefrontWorld :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [⟨0, 5, 0, path0, 1, 16⟩], [⟨1, 3, 0, path0, 1, 16⟩], 2, 0, 1⟩
/-- Step-2 world state in `multiRank_5_to_0_wavefront_drain_witness`. -/
@[expose] def mwW2 : WavefrontWorld :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [], [⟨2, 3, 0, path0, 1, 16⟩, ⟨1, 3, 0, path0, 1, 16⟩], 3, 1, 2⟩
/-- Step-3 world state in `multiRank_5_to_0_wavefront_drain_witness`. -/
@[expose] def mwW3 : WavefrontWorld :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [], [⟨3, 2, 0, path0, 1, 16⟩, ⟨1, 3, 0, path0, 1, 16⟩], 4, 2, 3⟩
/-- Step-4 world state in `multiRank_5_to_0_wavefront_drain_witness`. -/
@[expose] def mwW4 : WavefrontWorld :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [], [⟨4, 1, 0, path0, 1, 16⟩, ⟨1, 3, 0, path0, 1, 16⟩], 5, 3, 4⟩
/-- Step-5 world state in `multiRank_5_to_0_wavefront_drain_witness`. -/
@[expose] def mwW5 : WavefrontWorld :=
  ⟨wfCNode24Mem0, mwLoans10, .empty,
    [], [⟨5, 0, 0, path0, 1, 16⟩, ⟨1, 3, 0, path0, 1, 16⟩], 6, 4, 5⟩
/-- Step-6 world state in `multiRank_5_to_0_wavefront_drain_witness`. -/
@[expose] def mwW6 : WavefrontWorld :=
  ⟨mwMem26, mwLoans26, .empty, [], [⟨1, 3, 0, path0, 1, 16⟩], 6, 5, 6⟩
/-- Step-7 world state in `multiRank_5_to_0_wavefront_drain_witness`. -/
@[expose] def mwW7 : WavefrontWorld :=
  ⟨mwMem26, mwLoans26, .empty, [], [⟨6, 2, 0, path0, 1, 16⟩], 7, 6, 7⟩
/-- Step-8 world state in `multiRank_5_to_0_wavefront_drain_witness`. -/
@[expose] def mwW8 : WavefrontWorld :=
  ⟨mwMem26, mwLoans26, .empty, [], [⟨7, 1, 0, path0, 1, 16⟩], 8, 7, 8⟩
/-- Step-9 world state in `multiRank_5_to_0_wavefront_drain_witness`. -/
@[expose] def mwW9 : WavefrontWorld :=
  ⟨mwMem26, mwLoans26, .empty, [], [⟨8, 0, 0, path0, 1, 16⟩], 9, 8, 9⟩
/-- Quiescent step-10 world state in `multiRank_5_to_0_wavefront_drain_witness`.
-/
@[expose] def mwW10 : WavefrontWorld :=
  ⟨mwMem42, mwLoans42, .empty, [], [], 9, 9, 10⟩

private theorem runWavefrontStep_chain (f : Nat) (w next wf : WavefrontWorld)
    (hNe : wfPoolIsNonEmpty w = true)
    (hStep : evalHybridCmd (.poolWavefrontStep wfPolicyTower53210) w =
      .returned next)
    (hRest : runWavefrontSteps f wfPolicyTower53210 next = some wf) :
    runWavefrontSteps (f + 1) wfPolicyTower53210 w = some wf := by
  change
    (match wfPoolIsNonEmpty w with
     | false => some w
     | true =>
       match evalHybridCmd (.poolWavefrontStep wfPolicyTower53210) w with
       | .returned wNext => runWavefrontSteps f wfPolicyTower53210 wNext
       | .faultInvalidSpawn | .faultLoanViolation => none) = some wf
  rw [hNe, hStep]
  exact hRest

/-- Concrete 10-step rank-`5 -> 3 -> 2 -> 1 -> 0` drain witness (`[]`):
verifies `runWavefrontSteps 11` terminates at `mwW10` with `completedCount = 9`,
`stepCount = 10`, empty measure, and `path0` reclaimed to `.activeMut` (`42`).
-/
theorem multiRank_5_to_0_wavefront_drain_witness :
    isStrictlyDescendingTower wfTower53210 = true ∧
    runWavefrontSteps 11 wfPolicyTower53210 multiRankWitnessWorld0 =
      some mwW10 ∧
    mwW10.completedCount = 9 ∧
    mwW10.stepCount = 10 ∧
    worldMeasure mwW10 = [] ∧
    wfFindLoan path0 mwW10.loans =
      some (WfLoanEntry.mk path0 .activeMut wfCNodeEpochLens 42) ∧
    byteSubLensGet wfCNodeEpochLens mwW10.mem =
      some (wfEncodeU32BeSlice 42) := by
  have hRun :
      runWavefrontSteps 11 wfPolicyTower53210 multiRankWitnessWorld0 =
        some mwW10 :=
    runWavefrontStep_chain 10 multiRankWitnessWorld0 mwW1 mwW10 rfl rfl
      (runWavefrontStep_chain 9 mwW1 mwW2 mwW10 rfl rfl
        (runWavefrontStep_chain 8 mwW2 mwW3 mwW10 rfl rfl
          (runWavefrontStep_chain 7 mwW3 mwW4 mwW10 rfl rfl
            (runWavefrontStep_chain 6 mwW4 mwW5 mwW10 rfl rfl
              (runWavefrontStep_chain 5 mwW5 mwW6 mwW10 rfl rfl
                (runWavefrontStep_chain 4 mwW6 mwW7 mwW10 rfl rfl
                  (runWavefrontStep_chain 3 mwW7 mwW8 mwW10 rfl rfl
                    (runWavefrontStep_chain 2 mwW8 mwW9 mwW10 rfl rfl
                      (runWavefrontStep_chain 1 mwW9 mwW10 mwW10 rfl rfl
                        rfl)))))))))
  exact ⟨rfl, hRun, rfl, rfl, rfl, rfl, rfl⟩

/-- 2-tier rank tower `[1, 0]` with fanout `2` for the 5-stage canary. -/
@[expose] def policyTower10 : SpawnPolicy := towerLookupNext [1, 0] 2 0

/-- Initial world fixture for
`endToEnd_checkout_burst_drain_reclaim_pureLift_verified`.
-/
@[expose] def reclaimDemoWorld0 : WavefrontWorld :=
  { mem := wfCNode24Mem0
    loans := [
      WfLoanEntry.mk path0 .activeMut wfCNodeEpochLens 10,
      WfLoanEntry.mk path1 .activeMut wfCNodeActiveCountLens 0
    ]
    cells := ResTrie.modifyBits (pos4ToList path2) (fun _ => some 99) .empty
    fifoQueue := []
    stealDeque := []
    nextTaskId := 1
    completedCount := 0
    stepCount := 0 }

/-- Initial resource trie carrying `ordDebtProp [(3, 2)]` and
`cellAuthProp path2 99`. -/
@[expose] def reclaimDemoRes0 : ResTrie ResElem :=
  ResTrie.modifyBits (cellPath path2) (fun _ => some (.cell (.capAndAuth 99)))
    (ordDebtTree [(3, 2)])

/-- Concrete instantiation of `vsepWpOrdRel_fiveStage_chained_lifecycle` on
`reclaimDemoWorld0` with spatial frame `cellAuthProp path2 99` (`[propext]`):
`path0` (`wfCNodeEpochLens = 10`) is checked out, burst-spawned at rank `1`
under
`policyTower10` (fanout `2` into rank-`0` leaves with `writeDelta = 6` ->
`10 + 2 * 6 = 22`), drained to quiescence, universally reclaimed to
`.activeMut`,
and mutated via `.pureLiftSafe` (`+ 20` -> `42` in `w4.mem`) while preserving
spatial `cellAuthProp path2 99` and `WorldMatches`. -/
theorem endToEnd_checkout_burst_drain_reclaim_pureLift_verified :
    ∃ (w1 w2 w3 w4 : WavefrontWorld) (r1 r2 r3 r4 : ResTrie ResElem)
      (v1 v2 v3 v4 : View),
      evalHybridCmd (.checkoutLoan path0 55) reclaimDemoWorld0 =
        .returned w1 ∧
      WorldMatches v1 r1 w1 ∧
      evalHybridCmd (.submitTaskBurst 1 0 path0 55 6) w1 = .returned w2 ∧
      WorldMatches v2 r2 w2 ∧
      WavefrontConverges policyTower10 w2 w3 ∧
      WorldMatches v3 r3 w3 ∧
      ActivePureLoanAt path0 wfCNodeEpochLens 22 w3 ∧
      byteSubLensGet wfCNodeEpochLens w3.mem = some (wfEncodeU32BeSlice 22) ∧
      evalHybridCmd (.pureLiftSafe path0 20) w3 = .returned w4 ∧
      WorldMatches v4 r4 w4 ∧
      (vsep (vMinStep w3.stepCount) (cellAuthProp path2 99)).holds v4 r4 ∧
      byteSubLensGet wfCNodeEpochLens w4.mem = some (wfEncodeU32BeSlice 42) :=
        by
  have hPol10 : PolicyAdmissible policyTower10 :=
    towerLookupNext_admissible [1, 0] 2 0 rfl
  have hChk0 : CheckoutLoanGuard path0 wfCNodeEpochLens 10 reclaimDemoWorld0 :=
    ⟨⟨WfLoanEntry.mk path0 .activeMut wfCNodeEpochLens 10, rfl, rfl, rfl, rfl⟩,
      rfl⟩
  have hM0 : WorldMatches [0] reclaimDemoRes0 reclaimDemoWorld0 :=
    WorldMatches.mk rfl
      ⟨rfl, ⟨rfl, True.intro⟩, rfl, rfl, wfCNode24Mem0_get_epoch,
       ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_activeCount, True.intro⟩⟩
      rfl
      rfl
      (fun cid => by
        cases hEq2 : Pos4.beq path2 cid with
        | true =>
          rw [← pos4_eq_of_beq path2 cid hEq2]
          rfl
        | false =>
          have hNeCell :
              listBoolBeq (cellPath path2) (cellPath cid) = false := by
            dsimp only [cellPath, listBoolBeq, Bool.and]
            exact hEq2
          dsimp only [reclaimDemoRes0, ordDebtTree]
          rw [resTrie_getBits_modifyBits_ne (cellPath path2) (cellPath cid)
                rfl hNeCell,
            resTrie_getBits_modifyBits_ne debtPath (cellPath cid) rfl rfl,
            singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
          exact True.intro)
      (fun lid2 => by
        dsimp only [reclaimDemoRes0, ordDebtTree]
        rw [resTrie_getBits_modifyBits_ne (cellPath path2)
              (checkedLoanPath lid2) rfl rfl,
          resTrie_getBits_modifyBits_ne debtPath
            (checkedLoanPath lid2) rfl rfl,
          singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
        exact True.intro)
  have hPre0 :
      (vsep (ordDebtProp [(3, 2)]) (cellAuthProp path2 99)).holds [0]
        reclaimDemoRes0 :=
    ⟨ordDebtTree [(3, 2)],
      singleRes (cellPath path2) (.cell (.capAndAuth 99)),
      rfl,
      resTrieSub_refl (ordDebtTree [(3, 2)]),
      ResTrieSub.mk ⟨singleRes (cellPath path2) (.cell .capOnly), rfl⟩⟩
  cases vsepWpOrdRel_fiveStage_chained_lifecycle policyTower10 hPol10
      path0 wfCNodeEpochLens 10 55 1 0 6 20 [(3, 2)] rfl rfl
      [0] (cellAuthProp path2 99) reclaimDemoRes0 reclaimDemoWorld0 hChk0
      hPre0 hM0 with
  | intro w1 hw1 =>
    cases hw1 with
    | intro w2 hw2 =>
      cases hw2 with
      | intro w3 hw3 =>
        cases hw3 with
        | intro w4 hw4 =>
          cases hw4 with
          | intro r1 hr1 =>
            cases hr1 with
            | intro r2 hr2 =>
              cases hr2 with
              | intro r3 hr3 =>
                cases hr3 with
                | intro r4 hr4 =>
                  cases hr4 with
                  | intro v1 hv1 =>
                    cases hv1 with
                    | intro v2 hv2 =>
                      cases hv2 with
                      | intro v3 hv3 =>
                        cases hv3 with
                        | intro v4 hv =>
                          have hMultEq :
                              wrapU32 (10 + taskLeafMult policyTower10 1 0 * 6)
                                = 22 := rfl
                          have hFinalEq : wrapU32 (22 + 20) = 42 := rfl
                          have hAct22 := hv.2.2.2.2.2.2.2.2.1
                          have hGet22 := hv.2.2.2.2.2.2.2.2.2.1
                          have hGet42 :=
                            hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                          rw [hMultEq] at hAct22 hGet22 hGet42
                          rw [hFinalEq] at hGet42
                          exact ⟨w1, w2, w3, w4, r1, r2, r3, r4, v1, v2, v3, v4,
                            hv.1, hv.2.1,
                            hv.2.2.2.1, hv.2.2.2.2.1,
                            hv.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.1,
                            hAct22, hGet22,
                            hv.2.2.2.2.2.2.2.2.2.2.1,
                            hv.2.2.2.2.2.2.2.2.2.2.2.1,
                            hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                            hGet42⟩

/-- Positive spatial-cell update witness exercising
`vsepWpOrdRel_updateSpatialCell` on `(reclaimDemoRes0, reclaimDemoWorld0)` while
preserving `ordDebtProp [(3, 2)]` and `WorldMatches`. -/
theorem updateSpatialCell_positive_witness :
    ∃ (wOut : WavefrontWorld) (rOut : ResTrie ResElem) (vOut : View),
      evalHybridCmd (.updateSpatialCell path2 123) reclaimDemoWorld0 =
        .returned wOut ∧
      ResTrie.getBits (pos4ToList path2) wOut.cells = some 123 ∧
      WorldMatches vOut rOut wOut ∧
      (vsep (vsep (cellCapProp path2) (cellAuthProp path2 123))
        (ordDebtProp [(3, 2)])).holds vOut rOut := by
  have hM0 : WorldMatches [0] reclaimDemoRes0 reclaimDemoWorld0 :=
    WorldMatches.mk rfl
      ⟨rfl, ⟨rfl, True.intro⟩, rfl, rfl, wfCNode24Mem0_get_epoch,
       ⟨rfl, True.intro, rfl, rfl, wfCNode24Mem0_get_activeCount, True.intro⟩⟩
      rfl
      rfl
      (fun cid => by
        cases hEq2 : Pos4.beq path2 cid with
        | true =>
          rw [← pos4_eq_of_beq path2 cid hEq2]
          rfl
        | false =>
          have hNeCell :
              listBoolBeq (cellPath path2) (cellPath cid) = false := by
            dsimp only [cellPath, listBoolBeq, Bool.and]
            exact hEq2
          dsimp only [reclaimDemoRes0, ordDebtTree]
          rw [resTrie_getBits_modifyBits_ne (cellPath path2) (cellPath cid)
                rfl hNeCell,
            resTrie_getBits_modifyBits_ne debtPath (cellPath cid) rfl rfl,
            singleRes_getBits_ne poolPath (cellPath cid) _ rfl rfl]
          exact True.intro)
      (fun lid2 => by
        dsimp only [reclaimDemoRes0, ordDebtTree]
        rw [resTrie_getBits_modifyBits_ne (cellPath path2)
              (checkedLoanPath lid2) rfl rfl,
          resTrie_getBits_modifyBits_ne debtPath
            (checkedLoanPath lid2) rfl rfl,
          singleRes_getBits_ne poolPath (checkedLoanPath lid2) _ rfl rfl]
        exact True.intro)
  have hPre :
      (vsep (vsep (cellCapProp path2) (cellAuthProp path2 99))
        (ordDebtProp [(3, 2)])).holds [0] reclaimDemoRes0 :=
    ⟨singleRes (cellPath path2) (.cell (.capAndAuth 99)),
      ordDebtTree [(3, 2)],
      rfl,
      ⟨singleRes (cellPath path2) (.cell .capOnly),
        singleRes (cellPath path2) (.cell (.authOnly 99)),
        rfl,
        resTrieSub_refl _,
        resTrieSub_refl _⟩,
      resTrieSub_refl _⟩
  cases (vsepWpOrdRel_updateSpatialCell path2 99 123).run [0]
      (ordDebtProp [(3, 2)]) reclaimDemoRes0 reclaimDemoWorld0 True.intro
      hPre hM0 with
  | intro wOut hw =>
    cases hw with
    | intro rOut hr =>
      cases hr with
      | intro vOut hv =>
        have hEv :
            evalHybridCmd (.updateSpatialCell path2 123) reclaimDemoWorld0 =
              .returned (
                match evalHybridCmd (.updateSpatialCell path2 123)
                    reclaimDemoWorld0 with
                | .returned w => w
                | .faultLoanViolation | .faultInvalidSpawn =>
                  reclaimDemoWorld0) := rfl
        have hEqW :
            wOut =
              (match evalHybridCmd (.updateSpatialCell path2 123)
                  reclaimDemoWorld0 with
               | .returned w => w
               | .faultLoanViolation | .faultInvalidSpawn =>
                 reclaimDemoWorld0) := by
          have h1 := hv.1
          rw [hEv] at h1
          injection h1 with h2
          exact h2.symm
        have hCell123 :
            ResTrie.getBits (pos4ToList path2) wOut.cells = some 123 := by
          rw [hEqW]
          rfl
        exact ⟨wOut, rOut, vOut, hv.1, hCell123, hv.2.2.2.2.1, hv.2.2.2.1⟩

/-- Constructs a single-cause negative test world over `wfCNode24Mem0` with
custom `loans` and `fifoQueue`. -/
@[expose] def mkNegWorld (loans : List WfLoanEntry)
    (fifo : List WorkerTask) : WavefrontWorld :=
  { mem := wfCNode24Mem0
    loans := loans
    cells := .empty
    fifoQueue := fifo
    stealDeque := []
    nextTaskId := 1
    completedCount := 0
    stepCount := 0 }

/-- 14-case single-cause fail-closed negative regression suite (15 conjuncts,
`[]`):
1. missing loan on leaf writeback -> `.faultLoanViolation`;
2. stale scope on leaf writeback (`.spatialCheckedOut 88` vs `77`) ->
   `.faultLoanViolation`;
3. active-not-checked-out loan on leaf writeback -> `.faultLoanViolation`;
4. empty-queue wavefront step -> `.faultInvalidSpawn`;
5. inadmissible equal-rank spawn (`pol _ = (1, 5, 0)` on rank `5`) ->
   `.faultInvalidSpawn`;
6. pure write to `.spatialCheckedOut` loan -> `.faultLoanViolation`;
7. pure write to `.frozen` loan -> `.faultLoanViolation` (paired with positive
   pure read `wfCanPureAccessLoan ... false = true`);
8. pure write to `.ended` loan -> `.faultLoanViolation`;
9. checkout of already `.spatialCheckedOut` loan -> `.faultLoanViolation`;
10. checkout while a queued task references the loan -> `.faultLoanViolation`;
11. burst submission with mismatched scope -> `.faultLoanViolation`;
12. spatial cell update on missing cell -> `.faultLoanViolation`;
13. pure write through dangling `allocId = 99` lens (`byteSubLensPut = none`)
    -> `.faultLoanViolation`;
14. leaf writeback through out-of-bounds `[24..28)` lens in 24-byte allocation
    (`byteSubLensPut = none`) -> `.faultLoanViolation`. -/
theorem canary_wavefrontReclaim_negative_fail_closed_tests :
    evalHybridCmd (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorld [] [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation ∧
    evalHybridCmd (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorld
        [WfLoanEntry.mk path0 (.spatialCheckedOut 88) wfCNodeEpochLens 10]
        [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation ∧
    evalHybridCmd (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorld
        [WfLoanEntry.mk path0 .activeMut wfCNodeEpochLens 10]
        [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation ∧
    evalHybridCmd (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorld
        [WfLoanEntry.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10] []) =
        .faultInvalidSpawn ∧
    evalHybridCmd (.poolWavefrontStep (fun _ => (1, 5, 0)))
      (mkNegWorld
        [WfLoanEntry.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10]
        [WorkerTask.mk 0 5 0 path0 77 5]) =
        .faultInvalidSpawn ∧
    evalHybridCmd (.pureLiftSafe path0 1)
      (mkNegWorld
        [WfLoanEntry.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmd (.pureLiftSafe path0 1)
      (mkNegWorld [WfLoanEntry.mk path0 .frozen wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    wfCanPureAccessLoan [WfLoanEntry.mk path0 .frozen wfCNodeEpochLens 10]
      path0 false = true ∧
    evalHybridCmd (.pureLiftSafe path0 1)
      (mkNegWorld [WfLoanEntry.mk path0 .ended wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmd (.checkoutLoan path0 77)
      (mkNegWorld
        [WfLoanEntry.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmd (.checkoutLoan path0 77)
      (mkNegWorld
        [WfLoanEntry.mk path0 .activeMut wfCNodeEpochLens 10]
        [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation ∧
    evalHybridCmd (.submitTaskBurst 1 0 path0 88 5)
      (mkNegWorld
        [WfLoanEntry.mk path0 (.spatialCheckedOut 77) wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmd (.updateSpatialCell path2 100)
      (mkNegWorld [WfLoanEntry.mk path0 .activeMut wfCNodeEpochLens 10] []) =
        .faultLoanViolation ∧
    evalHybridCmd (.pureLiftSafe path0 1)
      (mkNegWorld [WfLoanEntry.mk path0 .activeMut ⟨99, 0, 4, 2⟩ 10] []) =
        .faultLoanViolation ∧
    evalHybridCmd (.poolWavefrontStep (fun _ => (0, 0, 0)))
      (mkNegWorld
        [WfLoanEntry.mk path0 (.spatialCheckedOut 77) ⟨2, 24, 4, 2⟩ 10]
        [WorkerTask.mk 0 0 0 path0 77 5]) =
        .faultLoanViolation :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.WavefrontReclaim

end
