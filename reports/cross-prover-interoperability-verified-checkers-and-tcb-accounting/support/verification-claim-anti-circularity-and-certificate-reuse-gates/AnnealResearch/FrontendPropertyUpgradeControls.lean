import AnnealResearch.FrontendPropertyAndUpgrade
set_option Elab.async false

/-!
Negative controls for `FE-10` (shared exporter omission agreement), `FE-11` (output-only /
termination-shortcut masquerade and scalar-cost scope hiding), and `FE-12` (silent semantic
drift passing syntax/snapshot oracles and agent self-weakened upgrade contracts) in live Issue
`#45` (`<!-- anneal-frontend-evaluation-program-2026-10-16 -->`).
-/

namespace AnnealResearch.FrontendPropertyUpgradeControls

open AnnealResearch.FrontendPropertyAndUpgrade

/-- Shared exporter bridge omission (`preservesAllPrefixNoUB = false`): models two routes
(such as `routeCharonLLBC = 0` and `routeCharonULLBC = 1`) that share an upstream extraction
pass or `optimized_mir` fallback that erases an intermediate UB prefix. -/
noncomputable def sharedOmissionCert : RouteBridgeCert :=
  (true, false, true, true)

/-- Mutant of `guarded_slice_update_with_cleanup` with an intermediate UB prefix
(`hasBadIntermediatePrefix = true`) that still reaches the normal completed output state
`(1, false, 1, 42)`. -/
noncomputable def badPrefixMutant : ConsequentialSubject :=
  (true, 1, 42, true, true, false)

/-- Control 1 (`FE-10`): Two distinct routes (`routeCharonLLBC ≠ routeCharonULLBC`) sharing
`sharedOmissionCert` agree on `ModelRelativeProof sharedOmissionCert badPrefixMutant = true`
and reach the normal-looking completed state `(1, false, 1, 42)`, even though `badPrefixMutant`
first visits the unsafe intermediate state `(2, true, 1, 42)` and violates `Execution.NoUB`
and `JustifiedRustClaim`. -/
theorem shared_exporter_omission_agreement_control :
    routeCharonLLBC ≠ routeCharonULLBC ∧
    ModelRelativeProof sharedOmissionCert badPrefixMutant = true ∧
    ModelRelativeProof fullRouteBridgeCert badPrefixMutant = false ∧
    ¬ RouteBridgeValid sharedOmissionCert ∧
    Execution.Reach (subjectStep badPrefixMutant) initSubjState (2, true, 1, 42) ∧
    Execution.Reach (subjectStep badPrefixMutant) initSubjState (1, false, 1, 42) ∧
    ¬ Execution.NoUB (subjectStep badPrefixMutant) SubjBad initSubjState ∧
    ¬ JustifiedRustClaim badPrefixMutant := by
  have hNotSafe : ¬ SubjSafeStepCond badPrefixMutant :=
    fun ⟨_, hNoBad, _⟩ => Bool.noConfusion hNoBad
  have hStepBad : subjectStep badPrefixMutant initSubjState (2, true, 1, 42) :=
    Or.inr ⟨hNotSafe, Or.inl ⟨rfl, rfl⟩⟩
  have hStepDone : subjectStep badPrefixMutant (2, true, 1, 42) (1, false, 1, 42) :=
    Or.inr ⟨hNotSafe, Or.inr ⟨rfl, rfl⟩⟩
  have hReachBad : Execution.Reach (subjectStep badPrefixMutant) initSubjState (2, true, 1, 42) :=
    Execution.Reach.tail (Execution.Reach.refl initSubjState) hStepBad
  have hReachDone : Execution.Reach (subjectStep badPrefixMutant) initSubjState (1, false, 1, 42) :=
    Execution.Reach.tail hReachBad hStepDone
  have hNotNoUB : ¬ Execution.NoUB (subjectStep badPrefixMutant) SubjBad initSubjState :=
    Execution.bad_prefix_not_noUB hReachBad rfl
  exact ⟨fun (h : 0 = 1) => Nat.noConfusion h,
         rfl,
         rfl,
         fun ⟨_, hP2, _, _⟩ => Bool.noConfusion hP2,
         hReachBad,
         hReachDone,
         hNotNoUB,
         fun hClaim => hNotNoUB hClaim.1⟩

/-- Bridge shortcut that drops cleanup and divergence obligations (`preservesCleanupAndDivergence = false`). -/
noncomputable def shortcutBridgeCert : RouteBridgeCert :=
  (true, true, false, true)

/-- Subject that omits stateful cleanup before diverging (`cleanupExecuted = false`, `divergesAfterCleanup = true`). -/
noncomputable def cleanupDropFaultBeforeDivergenceSubj : ConsequentialSubject :=
  (true, 1, 42, false, false, true)

/-- Shortcut usability ledger that drops divergence and stateful cleanup (`preservesDivergenceAndCleanup = false`)
to achieve lower proof cost (`5 < 9`) and lower total cost (`12 < 18`). -/
noncomputable def shortcutCostLedger : RouteCostAndScopeLedger :=
  (4, 0, false, 3, 5, 4, 1)

/-- Control 2 (`FE-11`): Dropping divergence and stateful cleanup lowers proof cost (`5` vs `9`)
and total route cost (`12` vs `18`), but falsely admits `cleanupDropFaultBeforeDivergenceSubj`
(`¬ Execution.NoUB`) and is rejected by `MatchedUsabilityComparison`. -/
theorem output_only_termination_shortcut_masquerade_control :
    decide (shortcutCostLedger.2.2.2.2.1 < charonSidecarFullLedger.2.2.2.2.1) = true ∧
    totalRouteCost shortcutCostLedger = 12 ∧
    totalRouteCost charonSidecarFullLedger = 18 ∧
    MatchedUsabilityComparison shortcutCostLedger charonSidecarFullLedger = false ∧
    ModelRelativeProof shortcutBridgeCert cleanupDropFaultBeforeDivergenceSubj = true ∧
    ModelRelativeProof fullRouteBridgeCert cleanupDropFaultBeforeDivergenceSubj = false ∧
    ¬ Execution.NoUB (subjectStep cleanupDropFaultBeforeDivergenceSubj) SubjBad initSubjState ∧
    ¬ JustifiedRustClaim cleanupDropFaultBeforeDivergenceSubj := by
  have hNotSafe : ¬ SubjSafeStepCond cleanupDropFaultBeforeDivergenceSubj :=
    fun ⟨_, _, hClean⟩ => Bool.noConfusion hClean
  have hStepBad : subjectStep cleanupDropFaultBeforeDivergenceSubj initSubjState (2, true, 1, 42) :=
    Or.inr ⟨hNotSafe, Or.inl ⟨rfl, rfl⟩⟩
  have hReachBad :
      Execution.Reach (subjectStep cleanupDropFaultBeforeDivergenceSubj) initSubjState (2, true, 1, 42) :=
    Execution.Reach.tail (Execution.Reach.refl initSubjState) hStepBad
  have hNotNoUB :
      ¬ Execution.NoUB (subjectStep cleanupDropFaultBeforeDivergenceSubj) SubjBad initSubjState :=
    Execution.bad_prefix_not_noUB hReachBad rfl
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hNotNoUB, fun hClaim => hNotNoUB hClaim.1⟩

/-- Naive parser/snapshot-only upgrade oracle that checks only whether the adapter parses and
theorem snapshots match, ignoring semantic drift and the independent semantic audit. -/
noncomputable def SnapshotUpgradeOracle (adapterRepaired : Bool) (claimPreserved : Bool)
    (_d : CompilerUpgradeDelta) : Bool :=
  match adapterRepaired, claimPreserved with
  | true, true => true
  | _, _ => false

/-- Silent unwind-order semantic drift across a compiler upgrade (`syntaxOrWireChanged = false`,
`unwindSemanticsDrifted = true`, `independentSemanticAuditPassed = false`). -/
noncomputable def silentUnwindDriftUpgrade : CompilerUpgradeDelta :=
  (false, true, false, false, false)

/-- Silent call-instance resolution drift across a compiler upgrade (`syntaxOrWireChanged = false`,
`callInstanceDrifted = true`, `independentSemanticAuditPassed = false`). -/
noncomputable def silentCallInstanceDriftUpgrade : CompilerUpgradeDelta :=
  (false, false, false, true, false)

/-- Control 3 (`FE-12`): Unchanged constructor/wire syntax with silent unwind or call-instance
drift passes `SnapshotUpgradeOracle` (`true`) while `UpgradeAccepted` rejects both (`false`). -/
theorem silent_semantic_drift_passes_syntax_and_snapshot_oracle_control :
    silentUnwindDriftUpgrade.1 = false ∧
    silentUnwindDriftUpgrade.2.1 = true ∧
    SnapshotUpgradeOracle true true silentUnwindDriftUpgrade = true ∧
    UpgradeAccepted true true silentUnwindDriftUpgrade = false ∧
    SnapshotUpgradeOracle true true silentCallInstanceDriftUpgrade = true ∧
    UpgradeAccepted true true silentCallInstanceDriftUpgrade = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Upgrade checker that omits frozen-claim hash equality (`claimPreserved` assumed `true`). -/
noncomputable def UnpinnedUpgradeChecker (adapterRepaired : Bool)
    (d : CompilerUpgradeDelta) : Bool :=
  UpgradeAccepted adapterRepaired true d

/-- Claim-pinned upgrade gate requiring `submittedClaimHash = frozenClaimHash`. -/
noncomputable def ClaimPinnedUpgradeGate (frozenClaimHash submittedClaimHash : Nat)
    (adapterRepaired : Bool) (d : CompilerUpgradeDelta) : Bool :=
  UpgradeAccepted adapterRepaired (decide (submittedClaimHash = frozenClaimHash)) d

/-- Control 4 (`FE-12`): An upgrading agent that repairs a broken proof by weakening the frozen
contract (`submittedClaimHash = 102 ≠ 101 = frozenClaimHash`) passes `UnpinnedUpgradeChecker`
(`true`) while failing `ClaimPinnedUpgradeGate` (`false`). -/
theorem agent_self_weakened_upgrade_contract_control :
    UnpinnedUpgradeChecker true visibleStructuralRenameUpgrade = true ∧
    ClaimPinnedUpgradeGate 101 102 true visibleStructuralRenameUpgrade = false ∧
    ClaimPinnedUpgradeGate 101 101 true visibleStructuralRenameUpgrade = true :=
  ⟨rfl, rfl, rfl⟩

/-- Naive cost-only comparator that ranks routes by `totalRouteCost` without checking unsupported scope. -/
noncomputable def ScalarCostOnlyPrefers (L1 L2 : RouteCostAndScopeLedger) : Bool :=
  decide (totalRouteCost L1 < totalRouteCost L2)

/-- Control 5 (`FE-11`): `charonUnpatchedLedger` has strictly lower `totalRouteCost` (`10 < 18`)
than `charonSidecarFullLedger` because it leaves 2 of 4 tasks unsupported (`unsupportedTasks = 2`)
and drops divergence/cleanup (`preservesDivergenceAndCleanup = false`), so `ScalarCostOnlyPrefers`
prefers it (`true`) while `MatchedUsabilityComparison` rejects the comparison (`false`). -/
theorem scalar_score_hides_unsupported_scope_control :
    totalRouteCost charonUnpatchedLedger = 10 ∧
    totalRouteCost charonSidecarFullLedger = 18 ∧
    ScalarCostOnlyPrefers charonUnpatchedLedger charonSidecarFullLedger = true ∧
    charonUnpatchedLedger.2.1 = 2 ∧
    charonUnpatchedLedger.2.2.1 = false ∧
    MatchedUsabilityComparison charonUnpatchedLedger charonSidecarFullLedger = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms shared_exporter_omission_agreement_control
#print axioms output_only_termination_shortcut_masquerade_control
#print axioms silent_semantic_drift_passes_syntax_and_snapshot_oracle_control
#print axioms agent_self_weakened_upgrade_contract_control
#print axioms scalar_score_hides_unsupported_scope_control

end AnnealResearch.FrontendPropertyUpgradeControls
