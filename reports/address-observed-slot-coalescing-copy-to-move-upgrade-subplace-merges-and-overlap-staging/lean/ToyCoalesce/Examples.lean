import ToyCoalesce.CexMerge

/-!
# Positive and negative examples for the definitions
-/

namespace Toy.Coalesce

theorem ex_disj_pos : Disj 0 1 1 1 := by decide
theorem ex_disj_empty : Disj 5 0 5 3 := by decide
theorem ex_disj_neg : ¬ Disj 0 2 1 1 := by decide

theorem ex_windowsDisjoint_pos : WindowsDisjoint ⟨0, 0, 1⟩ ⟨0, 1, 1⟩ := by decide
theorem ex_windowsDisjoint_neg : ¬ WindowsDisjoint ⟨0, 0, 2⟩ ⟨0, 1, 1⟩ := by decide

theorem ex_upgradeSite_pos : UpgradeSite pDtor 5 qx := Or.inl ⟨⟨2, 0, 1⟩, by decide, by decide⟩
theorem ex_upgradeSite_neg : ¬ UpgradeSite pDtor 4 qx := by
  simp [UpgradeSite, pDtor, qx]

theorem ex_noReadBeforeReinit_pos : NoReadBeforeReinit (run semD pNoDtor A0).log 5 true qx := by
  decide
theorem ex_noReadBeforeReinit_neg : ¬ NoReadBeforeReinit (run semD pDtor A0).log 5 true qx := by
  decide

theorem ex_calleeAvoids_pos : CalleeAvoids (run semI pIPAfter A0).log 4 qx := by decide
theorem ex_calleeAvoids_neg : ¬ CalleeAvoids (run semI pIPStore A0).log 4 qx := by decide

theorem ex_calleeNoParamAddr_pos : CalleeNoParamAddr pIPStore 0 := by decide
theorem ex_calleeNoParamAddr_neg : ¬ CalleeNoParamAddr pIPAddr 0 := by decide

/-- A program that passes `x` (local 0) by `move` to a callee that takes the address of its
parameter (local 1); no statement takes `&x` directly. -/
def pEscape : Prog where
  sizes := [1, 1]
  body := [.storageLive 0, .assign ⟨0, 0, 1⟩ [.lit 1], .call 0 (.move ⟨0, 0, 1⟩)]
  dtors := []
  fns := [⟨1, [.out (.addrOf ⟨1, 0, 1⟩)]⟩]

theorem ex_addrTaken_pos : AddrTaken p3 0 := by decide
theorem ex_addrTaken_inPlace_channel : AddrTaken pEscape 0 := by decide
theorem ex_addrTaken_neg : ¬ AddrTaken p3x 1 := by decide

theorem ex_obsCert_pos : ObsCert pDtor (obsAnalysis pDtor) := by unfold ObsCert; decide
theorem ex_obsCert_neg : ¬ ObsCert pDtor (obsBodyOnly pDtor) := by unfold ObsCert; decide

theorem ex_checkObs_neg : checkObs pDtor (fun _ _ => false) = false := by decide

theorem ex_licensed_pos : Licensed .deinit pNoDtor (obsAnalysis pNoDtor) 5 qx :=
  nonvacuous_upgrade_refines_of_obsCert_licensed.2.2
theorem ex_licensed_neg : ¬ Licensed .deinit pDtor (obsAnalysis pDtor) 5 qx :=
  obsAnalysis_rejects_dtorLoad.2

theorem ex_forestWF_pos : ForestWF pChain μChain := by decide
/-- A cycle is rejected. -/
theorem ex_forestWF_neg_cycle : ¬ ForestWF pPrecise [⟨0, 1, 0⟩, ⟨1, 0, 0⟩] := by decide
/-- A two-cell local does not fit in a one-cell local. -/
theorem ex_forestWF_neg_fit : ¬ ForestWF p3 (single 1 0 0) := by decide

theorem ex_coalesce_p3 : (coalesce (single 0 1 0) p3).body =
    [.storageLive 1, .nop, .nop, .assign ⟨1, 1, 1⟩ [.lit 5], .assign ⟨1, 0, 1⟩ [.lit 7],
      .out (.copy ⟨1, 0, 1⟩), .assign ⟨1, 0, 1⟩ [.lit 9],
      .ptrInRange (.addrOf ⟨1, 0, 1⟩) (.addrOf ⟨1, 0, 2⟩) 2, .out (.copy ⟨1, 0, 2⟩)] := by decide

theorem ex_coalesce_chain_offset : μChain.resolve 0 = (2, 2) := by decide

theorem ex_noValueClobber_pos : NoValueClobber (single 0 1 0) (run semD p3 A0).log := by decide
theorem ex_noValueClobber_neg : ¬ NoValueClobber (single 0 1 0) (run semD pClobber A0).log := by
  decide

theorem ex_lexOverlap_pos : LexOverlap p3 0 1 := by decide
theorem ex_lexOverlap_neg : ¬ LexOverlap pChain 0 1 := by decide

theorem ex_ivOverlap_precise_neg : ¬ IvOverlap .precise .precise pPrecise 0 1 := by decide
theorem ex_ivOverlap_precise_pos : IvOverlap .precise .precise pClobber 0 1 := by decide

theorem ex_classAddrDisjoint_pos : ClassAddrDisjoint pChainOk μChain := by decide
theorem ex_classAddrDisjoint_neg : ¬ ClassAddrDisjoint pChain μChain := by decide

theorem ex_edgeAddrCheck_pos : EdgeAddrCheck pChain μChain := by decide
theorem ex_edgeAddrCheck_neg : ¬ EdgeAddrCheck p3 (single 0 1 0) := by decide

theorem ex_rootAddrCheck_pos : RootAddrCheck pSib μSib := by decide
theorem ex_rootAddrCheck_neg : ¬ RootAddrCheck pChain μChain := by decide

theorem ex_policyCheck_pos :
    PolicyCheck (fun b => if b then .lexical else .precise) pPreciseOk (single 1 0 0) := by decide
theorem ex_policyCheck_neg :
    ¬ PolicyCheck (fun b => if b then .lexical else .precise) pPrecise (single 1 0 0) := by decide

theorem ex_noStagingNeeded_pos : NoStagingNeeded pSwap := by decide
theorem ex_noStagingNeeded_neg : ¬ NoStagingNeeded (coalesce (single 1 0 0) pSwap) := by decide

theorem ex_stage_body : (stage (coalesce (single 1 0 0) pSwap)).body =
    [.storageLive 0, .nop, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .nop,
      .storageLive 2, .assign ⟨2, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩],
      .assign ⟨0, 0, 2⟩ [.move ⟨2, 0, 2⟩], .storageDead 2, .out (.copy ⟨0, 0, 2⟩)] := by decide

theorem ex_localsInRange_pos : LocalsInRange pSwap := by decide
theorem ex_localsInRange_neg : ¬ LocalsInRange { pSwap with body := [.storageLive 5] } := by decide

theorem ex_addrFree_pos : AddrFree (erasedIs [.vals [.int 1]]) := erasedIs_addrFree _
theorem ex_addrFree_neg : ¬ AddrFree cmpAllFalse := by
  intro h
  have := (h [.cmp true] [.cmp false] rfl).2 (by decide)
  revert this; decide

theorem ex_ubFree_pos : UBFree semD p3x := nonvacuous_vc_backward.2.2.1
theorem ex_ubFree_neg : ¬ UBFree semD pUBRemoved := cex_vc_backward_needs_ubFree.2.2.2.1

theorem ex_moveSem_outcomes :
    outcome semC (pDtor.upgradeAt 5) A0 = .done [.vals [.int 7], .vals [.int 7]] ∧
    outcome semD (pDtor.upgradeAt 5) A0 = .ub ∧
    outcome semI (pIPStore.upgradeAt 4) A0 = .done [.vals [.int 2]] ∧
    outcome semD (pIPStore.upgradeAt 4) A0 = .done [.vals [.int 1]] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pDtor_upgradeAt]; decide
  · rw [pDtor_upgradeAt]; decide
  · simp only [pIPStore, pCall_upgradeAt]; decide
  · simp only [pIPStore, pCall_upgradeAt]; decide

theorem ex_assignMode_outcomes :
    outcome ⟨.deinit, .atomic⟩ (coalesce (single 1 0 0) pSwap) A0 = .done [.vals [.int 2, .int 1]] ∧
    outcome ⟨.deinit, .inOrder⟩ (coalesce (single 1 0 0) pSwap) A0 = .done [.vals [.int 2, .int 2]] := by
  decide

/-- Excluded runs: a layout that overlaps two simultaneously allocated locals is excluded. -/
theorem ex_badLayout : outcome semD p3 (fun _ => 0) = .badLayout := by decide

/-! ## Edge cases and the definitions added for callee parameters and in-place aliasing -/

theorem ex_windowsDisjoint_empty_edge : WindowsDisjoint ⟨0, 0, 0⟩ ⟨0, 0, 2⟩ := by decide
/-- The conservative edge case: a width-`0` window strictly inside another counts as
overlapping it. -/
theorem ex_windowsDisjoint_empty_interior : ¬ WindowsDisjoint ⟨0, 1, 0⟩ ⟨0, 0, 2⟩ := by decide

theorem ex_callsInBounds_pos : CallsInBounds pIPStore := by decide
theorem ex_callsInBounds_neg : ¬ CallsInBounds pOobCall := by decide
/-- A forest is not well formed for a program that calls an absent callee. -/
theorem ex_forestWF_neg_oob_call : ¬ ForestWF pOobCall (single 1 0 0) := by decide

theorem ex_paramsInRange_pos : ParamsInRange pIPStore := by decide
theorem ex_paramsInRange_neg : ¬ ParamsInRange pStageOobPrm := by decide

/-- A callee that touches a local by name marks both half-statement points of the call tick. -/
theorem ex_accessPt_callee_both_halves :
    AccessPt pCalleeReorder 0 6 = true ∧ AccessPt pCalleeReorder 0 7 = true ∧
    AccessPt pCalleeReorder 1 6 = true ∧ AccessPt pCalleeReorder 1 7 = true := by decide
/-- A non-call statement marks its read half for a by-name read and its write half for a by-name
write. -/
theorem ex_accessPt_noncall :
    AccessPt pPreciseOk 0 5 = true ∧ AccessPt pPreciseOk 0 6 = true ∧
    AccessPt pPreciseOk 0 7 = false := by decide
/-- The precise intervals of two locals touched by the same callee overlap. -/
theorem ex_ivOverlap_precise_callee : IvOverlap .precise .precise pCalleeReorder 0 1 := by decide

theorem ex_paramSplit_pos : Place.paramSplit 1 ⟨1, 0, 2⟩ ⟨0, 1, 1⟩ = true := by decide
theorem ex_paramSplit_neg : Place.paramSplit 1 ⟨1, 0, 2⟩ ⟨1, 1, 1⟩ = false := by decide
theorem ex_calleesNoStaging_pos : CalleesNoStaging pCalleeCoalSwap := by decide
/-- A callee assignment that mixes places based at the parameter with other places needs staging
(under in-place passing the parameter may alias them). -/
theorem ex_calleesNoStaging_neg_alias : ¬ CalleesNoStaging pAliasSwap := by decide

theorem ex_licensed_inPlaceCall_pos : Licensed .inPlaceCall pIPOk (obsAnalysis pIPOk) 4 qx := by
  intro fn h
  have hfn : fn = 0 := by simp [pIPOk, pCall, qx] at h; omega
  subst hfn
  exact ⟨by decide, by decide, by decide, by decide⟩
/-- The parameter local of the callee is address-taken in the caller, so the call-argument
upgrade is not licensed under `MoveSem.inPlaceCall`. -/
theorem ex_licensed_inPlaceCall_neg :
    ¬ Licensed .inPlaceCall pPrmEscaped (obsAnalysis pPrmEscaped) 6 qx := by
  intro h
  exact (h 0 (by decide)).2.2.2 (by decide)

end Toy.Coalesce
