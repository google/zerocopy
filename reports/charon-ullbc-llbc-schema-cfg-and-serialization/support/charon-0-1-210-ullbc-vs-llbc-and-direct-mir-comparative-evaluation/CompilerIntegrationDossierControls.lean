/-
  Experiment: experiments/opsem/compiler-integration-dossier
  Tasks FD-10 & FD-11 Controls: Negative Controls for Rejected Frontend Architectures
-/

import AnnealResearch.CompilerIntegrationDossier

set_option autoImplicit false
set_option Elab.async false

namespace AnnealResearch.CompilerIntegrationDossierControls

open AnnealResearch.CompilerIntegrationDossier

/-- Negative Control 1: A pure Charon LLBC architecture fails Gate G4 criteria because
    it loses cross-crate non-inline/check workspace bodies, strips `PlaceMention`/`Retag`/
    `UbChecks`/`StorageLive`, and is unsound on unwind and partial-field drop tasks. -/
def rejectedCharonLlbcArchitecture : FrontendArchitectureRecommendation :=
  { acquisition := .externalCharonCargoCli
  , semanticBoundary := .charonLlbcStructuredAsTruth
  , interchange := .unverifiedJsonTextAst
  , proofRep := .charonLlbcStructuredOnly }

theorem control_charon_llbc_architecture_fails_g4_criteria :
    architectureSatisfiesAllG4Criteria rejectedCharonLlbcArchitecture = false :=
  rfl

/-- Negative Control 2: A `rustc_public`-only architecture fails Gate G4 criteria because
    `rustc_public::CrateItem::body()` exposes `Runtime(Optimized)` after `RemoveStorageMarkers`
    and `InstSimplify`, cannot intercept stolen `const`/coroutine bodies before optimization,
    and still broke across the `1.97 -> 1.98` `WithRetag` transition. -/
def rejectedRustcPublicArchitecture : FrontendArchitectureRecommendation :=
  { acquisition := .rustcPublicFacadeOnly
  , semanticBoundary := .mirRuntimeOptimized
  , interchange := .canonicalAmirV3BinaryWithTotalLeanParser
  , proofRep := .rawMirCfgAnonymousOnly }

theorem control_rustc_public_architecture_fails_g4_criteria :
    architectureSatisfiesAllG4Criteria rejectedRustcPublicArchitecture = false :=
  rfl

/-- Negative Control 3: Direct-MIR `Runtime(PostCleanup)` without the `MirPhase::Built`
    `VarDebugInfo` + `LocalInfo` sidecar fails Gate G4's agent localization and proof-repair criterion. -/
def rejectedAnonymousMirArchitecture : FrontendArchitectureRecommendation :=
  { acquisition := .inProcessRustcWrapperTripleHook
  , semanticBoundary := .postCleanupWithBuiltSidecarAndPreserveUb
  , interchange := .canonicalAmirV3BinaryWithTotalLeanParser
  , proofRep := .rawMirCfgAnonymousOnly }

theorem control_anonymous_mir_without_sidecar_fails_g4_criteria :
    architectureSatisfiesAllG4Criteria rejectedAnonymousMirArchitecture = false :=
  rfl

/-- Negative Control 4: The legacy lossy `.amir` v2 binary interchange (`direct_mir_driver_v3.rs`)
    fails Gate G4 because it silently truncated basic blocks at 15 and clamped targets rather
    than failing closed (`failsClosedWithoutSilentTruncation = false`). -/
def rejectedLossyAmirV2Architecture : FrontendArchitectureRecommendation :=
  { acquisition := .inProcessRustcWrapperTripleHook
  , semanticBoundary := .postCleanupWithBuiltSidecarAndPreserveUb
  , interchange := .legacyLossyAmirV2Binary
  , proofRep := .mirCfgTruthWithVarDebugSidecarImplementedPlusProposedSafeStructuredView }

theorem control_lossy_amir_v2_architecture_fails_g4_criteria :
    architectureSatisfiesAllG4Criteria rejectedLossyAmirV2Architecture = false :=
  rfl

/-- Negative Control 5 (`#62` Section 5 Honesty Control):
    Claiming that a verified safe structured-view layer, general-crate open symbol table,
    or standalone runtime decoder is already implemented (`implementedAndTestedInSlice`)
    is refuted by `statusOfComponent`. -/
theorem control_presenting_proposed_structured_view_as_implemented_rejected :
    statusOfComponent .verifiedSafeStructuredViewLayer ≠ .implementedAndTestedInSlice ∧
    statusOfComponent .generalCrateOpenSymbolAndTypeTable ≠ .implementedAndTestedInSlice ∧
    statusOfComponent .productionStandaloneRuntimeDecoder ≠ .implementedAndTestedInSlice ∧
    statusOfComponent .asyncCoroutineOperationalVerification ≠ .implementedAndTestedInSlice ∧
    statusOfComponent .aSafe01ReferenceSourceSemanticsAndLowering ≠ .implementedAndTestedInSlice := by
  decide

/-- Negative Control 6 (`#68` §6 `N5` External `.rlib` Phase-Loss Control):
    Treating `.rlib`-recovered `Runtime(Optimized)` MIR (`mirRuntimeOptimized`) as a substitute for
    `Runtime(PostCleanup)` (`postCleanupWithBuiltSidecarAndPreserveUb`) fails both
    `soundForPlaceMentionAndUbChecks` and `preservesSourceVarLocalization`. -/
theorem control_external_rlib_optimized_mir_rejected_for_pre_optimization_ub_and_storage_obligations :
    (evalSemanticBoundary .mirRuntimeOptimized).soundForPlaceMentionAndUbChecks = false ∧
    (evalSemanticBoundary .mirRuntimeOptimized).preservesSourceVarLocalization = false ∧
    (evalSemanticBoundary .postCleanupWithBuiltSidecarAndPreserveUb).soundForPlaceMentionAndUbChecks = true ∧
    (evalSemanticBoundary .postCleanupWithBuiltSidecarAndPreserveUb).preservesSourceVarLocalization = true := by
  decide

/-- Negative Control 7 (`#68` §6 `N0` Evidence Status Taxonomy Control):
    `EvidenceStatusTaxonomyN0` keeps abstract meta-models, explicit assumptions, deliberate
    exclusions, and stopped/failed runs strictly distinct from universal operational and
    bounded concrete operational Lean proofs. -/
theorem control_n0_eight_status_taxonomy_never_conflates_meta_or_stopped_with_universal_operational :
    EvidenceStatusTaxonomyN0.leanProvedMetaModelOnly ≠ .leanProvedUniversalOperational ∧
    EvidenceStatusTaxonomyN0.leanProvedMetaModelOnly ≠ .leanProvedBoundedConcrete ∧
    EvidenceStatusTaxonomyN0.stoppedOrFailedExcluded ≠ .leanProvedUniversalOperational ∧
    EvidenceStatusTaxonomyN0.stoppedOrFailedExcluded ≠ .leanProvedBoundedConcrete ∧
    EvidenceStatusTaxonomyN0.explicitAssumption ≠ .leanProvedUniversalOperational ∧
    EvidenceStatusTaxonomyN0.deliberateExclusionOrDeferred ≠ .leanProvedUniversalOperational ∧
    primaryEvidenceStatusOfContractRow .assuranceEndpoint = .explicitAssumption := by
  decide

#print axioms control_charon_llbc_architecture_fails_g4_criteria
#print axioms control_rustc_public_architecture_fails_g4_criteria
#print axioms control_anonymous_mir_without_sidecar_fails_g4_criteria
#print axioms control_lossy_amir_v2_architecture_fails_g4_criteria
#print axioms control_presenting_proposed_structured_view_as_implemented_rejected
#print axioms control_external_rlib_optimized_mir_rejected_for_pre_optimization_ub_and_storage_obligations
#print axioms control_n0_eight_status_taxonomy_never_conflates_meta_or_stopped_with_universal_operational

/-- Negative Control 8 (`#93` §12 `Q7` & `F1`–`F6` Scope Calibration Control):
    `reconstructVerifiedStructuredViewInEnv` (`q7TwoBodyCanonicalStructuredRecognizerScopeCalibration`)
    is calibrated as an implemented two-body canonical recognizer with extracted scalar constants,
    kept strictly distinct from a proposed general safe structured-view decompiler
    (`verifiedSafeStructuredViewLayer = .proposedNotYetImplemented`), while all 6 `PR #92`
    audit findings (`F1`–`F6`) are paired with retained counterexamples and repairs. -/
theorem control_q7_two_body_canonical_recognizer_never_conflated_with_general_safe_structured_view :
    statusOfComponent .q7TwoBodyCanonicalStructuredRecognizerScopeCalibration = .implementedAndTestedInSlice ∧
    statusOfComponent .verifiedSafeStructuredViewLayer = .proposedNotYetImplemented ∧
    statusOfComponent .verifiedSafeStructuredViewLayer ≠ .implementedAndTestedInSlice ∧
    allPr92AuditFindings.length = 6 ∧
    (allPr92AuditFindings.all isPr92AuditFindingRepairedWithRetainedCounterexample) = true := by
  decide

#print axioms control_q7_two_body_canonical_recognizer_never_conflated_with_general_safe_structured_view

/-- Negative Control 9 (`#95` §§5–6 `C1` Meta-Model & Residual-Premise Honesty Control):
    Proving a Boolean catalog of architecture choices (`recommended_anneal_frontend_satisfies_all_g4_criteria`)
    has status `EvidenceStatusTaxonomyN0.leanProvedMetaModelOnly` (`≠ .leanProvedUniversalOperational`),
    not a proof that the architecture choices satisfy authoritative Rust semantics, and each `D1`–`D5`
    closeout repair explicitly preserves its residual deferred engineering gate or reviewed producer premise. -/
theorem control_c1_boolean_architecture_catalog_classified_as_meta_model_with_explicit_d1_to_d5_residual_premises :
    EvidenceStatusTaxonomyN0.leanProvedMetaModelOnly ≠ .leanProvedUniversalOperational ∧
    primaryEvidenceStatusOfContractRow .assuranceEndpoint = .explicitAssumption ∧
    allPr94CloseoutFindings.length = 5 ∧
    (allPr94CloseoutFindings.all (fun f => primaryCloseoutDisposition f == .repairedAndChecked)) = true ∧
    residualPremiseOrMilestoneDisposition .d1NominalIdentityIncompleteConsumerJoin =
      .deferredEngineeringGateWithNarrowedClaim ∧
    residualPremiseOrMilestoneDisposition .d2EndorsementHeaderChecksumAndOsPremise =
      .reviewedExactInputOrProducerPremise ∧
    residualPremiseOrMilestoneDisposition .d3SelectedLayoutCaptureAndStorageBoundaries =
      .deferredEngineeringGateWithNarrowedClaim ∧
    residualPremiseOrMilestoneDisposition .d4CharonSupportedDomainEnforcement =
      .reviewedExactInputOrProducerPremise := by
  decide

#print axioms control_c1_boolean_architecture_catalog_classified_as_meta_model_with_explicit_d1_to_d5_residual_premises

end AnnealResearch.CompilerIntegrationDossierControls
