/-
  Experiment: experiments/opsem/cost-incremental-and-frontiers
  Tasks FD-07, FD-08 (Study P4), and FD-09 (Study P5) Controls:
  Negative Controls for Incremental Proof Caching and Async/Frontier Capture
-/

import AnnealResearch.CostIncrementalAndFrontiers

set_option autoImplicit false

namespace AnnealResearch.CostIncrementalAndFrontiersControls

open AnnealResearch.CostIncrementalAndFrontiers

/-- Negative Control 1: Keying incremental proof validity solely by `DefPathHash` and
    caller body bytes (without requiring `AlphaContract` to hold on the updated callee)
    unsoundly accepts `beta` in `rev2_contract_change_same_sig`, where `beta`'s `.amir` v3
    body bytes and `alpha`'s signature `fn(u32) -> u32` are unchanged, but `alpha_rev2`
    violates `AlphaContract` and causes `beta` to violate `BetaContract`. -/
def unsoundCallerBodyOnlyCacheValid (prevBytes currBytes : List Nat) : Bool :=
  findDecodedBodyBySym prevBytes 58 == findDecodedBodyBySym currBytes 58

theorem control_caller_body_only_cache_unsound_when_callee_contract_changes :
    unsoundCallerBodyOnlyCacheValid realIncrementalRev0Bytes realIncrementalRev2Bytes = true ∧
    ¬ AlphaContract (evalDecodedAlpha realIncrementalRev2Bytes) ∧
    ¬ BetaContract (evalDecodedBetaWithCallee realIncrementalRev2Bytes (evalDecodedAlpha realIncrementalRev2Bytes)) := by
  refine ⟨rfl, alpha_rev2_falsifies_old_contract.1, alpha_rev2_falsifies_old_contract.2⟩

/-- Negative Control 2: Keying incremental proof validity solely by `DefPathHash`
    (without checking the normalized `.amir` body digest or callee contract digest)
    unsoundly accepts `alpha` after its body changes and `beta` after `alpha`'s contract changes. -/
def unsoundDefPathHashOnlyCacheValid (prev curr : IncrementalFnSnapshot) : Bool :=
  prev.defPathHashTag == curr.defPathHashTag

theorem control_def_path_hash_only_cache_unsoundly_accepts_mutated_bodies :
    unsoundDefPathHashOnlyCacheValid
      (observedIncrementalSnapshot .rev0Baseline).alpha
      (observedIncrementalSnapshot .rev2AlphaBodyOnlyEdit).alpha = true ∧
    (observedIncrementalSnapshot .rev0Baseline).alpha.normalizedBodyDigestTag ≠
      (observedIncrementalSnapshot .rev2AlphaBodyOnlyEdit).alpha.normalizedBodyDigestTag ∧
    unsoundDefPathHashOnlyCacheValid
      (observedIncrementalSnapshot .rev0Baseline).beta
      (observedIncrementalSnapshot .rev3AlphaSignatureEdit).beta = true ∧
    callerProofCacheValid
      (observedIncrementalSnapshot .rev0Baseline).beta
      (observedIncrementalSnapshot .rev3AlphaSignatureEdit).beta = false :=
  ⟨rfl, by decide, rfl, rfl⟩

/-- Negative Control 3: Keying incremental proof validity by whole-crate `.amir` digest
    falsely invalidates `beta`'s cached proof when only `alpha`'s body changes (`rev1`)
    while preserving `AlphaContract`. -/
theorem control_whole_crate_digest_falsely_invalidates_unchanged_caller :
    (observedIncrementalSnapshot .rev0Baseline).wholeCrateAmirDigestTag ≠
      (observedIncrementalSnapshot .rev2AlphaBodyOnlyEdit).wholeCrateAmirDigestTag ∧
    callerProofCacheValid
      (observedIncrementalSnapshot .rev0Baseline).beta
      (observedIncrementalSnapshot .rev2AlphaBodyOnlyEdit).beta = true ∧
    BetaContract (evalDecodedBetaWithCallee realIncrementalRev1Bytes (evalDecodedAlpha realIncrementalRev1Bytes)) :=
  ⟨by decide, rfl, beta_rev1_verified_by_compositional_reuse⟩

/-- Negative Control 4: Relying on `after_analysis` passive queries without the
    `mir_drops_elaborated_and_const_checked` query override loses the async coroutine
    closure body (`stolenBeforeAfterAnalysis = true` and `bodyAvailable = false`). -/
theorem control_after_analysis_passive_query_loses_async_coroutine_closure :
    (observedFrontier .f2AsyncCoroutineClosure).stolenBeforeAfterAnalysis = true ∧
    (observedFrontier .f2AsyncCoroutineClosure).capturedInHookDropsElaborated = true ∧
    (observedAsyncSuspensionStage .afterAnalysisElaboratedQuery).bodyAvailable = false ∧
    (observedAsyncSuspensionStage .hookMirDropsElaborated).bodyAvailable = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Negative Control 5 (`R7` Stale, Canceled, and Config/Dependency-Changed Proof Cache Controls):
    1. A valid proof certificate from `rev0` (`staleRev0CertArrivingAtRev2`, `gen = 1`) remains
       valid for its own `rev0` subject, but is rejected with `.rejectedStaleSubjectGeneration`
       when surfaced after the workspace has advanced to `rev2` (`gen = 3`).
    2. A canceled proof job (`canceledCertOnRev1`) is rejected with `.rejectedCanceledJob`.
    3. Changing configuration/dependency/model digest (`configChangedCertOnRev1`) invalidates
       reuse with `.invalidatedConfigOrDependencyChange`.
    4. Attempting to claim `calleeContractVerifiedOnCurrentPkg = true` on `rev2` (`brokenCalleeCertOnRev2`)
       is caught by `checkDecodedAlphaContractWitnesses realIncrementalRev2Bytes = false`
       (`.invalidatedCalleeContractMismatch`). -/
theorem control_r7_stale_canceled_and_config_changed_certificates_rejected :
    validateConfiguredProofCache currSubjectRev2BrokenContract staleRev0CertArrivingAtRev2 =
      .rejectedStaleSubjectGeneration ∧
    validateConfiguredProofCache currSubjectRev1 canceledCertOnRev1 =
      .rejectedCanceledJob ∧
    validateConfiguredProofCache currSubjectRev1 configChangedCertOnRev1 =
      .invalidatedConfigOrDependencyChange ∧
    checkDecodedAlphaSatisfiesContractUniversal realIncrementalRev2Bytes = false ∧
    checkDecodedAlphaContractWitnesses realIncrementalRev2Bytes = false ∧
    validateConfiguredProofCache currSubjectRev2BrokenContract brokenCalleeCertOnRev2 =
      .invalidatedCalleeContractMismatch ∧
    BetaContract (evalDecodedBetaWithCallee currSubjectRev1.pkgBytes (evalDecodedAlpha currSubjectRev1.pkgBytes)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact (validateConfiguredProofCache_implies_verified_caller_cache_and_beta_contract
    currSubjectRev1 validCertRev1FromRev0Caller rfl (by decide)).2.1

#print axioms control_caller_body_only_cache_unsound_when_callee_contract_changes
#print axioms control_def_path_hash_only_cache_unsoundly_accepts_mutated_bodies
#print axioms control_whole_crate_digest_falsely_invalidates_unchanged_caller
#print axioms control_after_analysis_passive_query_loses_async_coroutine_closure
#print axioms control_r7_stale_canceled_and_config_changed_certificates_rejected

end AnnealResearch.CostIncrementalAndFrontiersControls
