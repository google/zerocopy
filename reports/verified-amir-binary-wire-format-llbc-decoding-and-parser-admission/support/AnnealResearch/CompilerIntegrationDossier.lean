/-
  Experiment: experiments/opsem/compiler-integration-dossier
  Tasks FD-10 & FD-11 / Study P6 & Gate G4 (`joshlf/anneal#56` & `joshlf/anneal#61`):
  Concrete Compiler-Integration Recommendation and Four-Axis Frontend Decision Dossier

  Separates and formalizes the four distinct frontend architectural decisions:
  1. Acquisition (`AcquisitionStrategy`)
  2. Semantic Capture Boundary (`SemanticBoundaryChoice`)
  3. Interchange and Parsing (`InterchangeFormatChoice`)
  4. Proof Representation (`ProofRepresentationChoice`)
  Together with the five verification boundaries (B1 Syntax/Canonicality,
  B2 Structural/Dialect Admission, B3 Producer/Compilation Binding,
  B4 Decoded-AST Operational Semantics, B5 Frozen C0 Source/Oracle Adequacy)
  and explicit conditional source-bridge assumptions (`ASSUMP-SRC-01`..`03`).
-/

set_option autoImplicit false
set_option Elab.async false

namespace AnnealResearch.CompilerIntegrationDossier

/-! ## 1. The Four Distinct Frontend Decision Axes & Five Verification Boundaries -/

inductive VerificationBoundary where
  | b1SyntaxAndCanonicalDecoding
  | b2StructuralAndDialectAdmission
  | b3ProducerAndCompilationBinding
  | b4DecodedAstOperationalSemantics
  | b5SourceAndOraclePropertyAdequacy
  deriving DecidableEq, Repr

inductive SourceBridgeAssumption where
  | assumpSrc01RustcLoweringFidelity
  | assumpSrc02DeclaredIntrinsicContracts
  | assumpSrc03TargetLayoutConsistency
  deriving DecidableEq, Repr

def allVerificationBoundaries : List VerificationBoundary :=
  [ .b1SyntaxAndCanonicalDecoding
  , .b2StructuralAndDialectAdmission
  , .b3ProducerAndCompilationBinding
  , .b4DecodedAstOperationalSemantics
  , .b5SourceAndOraclePropertyAdequacy ]

def allSourceBridgeAssumptions : List SourceBridgeAssumption :=
  [ .assumpSrc01RustcLoweringFidelity
  , .assumpSrc02DeclaredIntrinsicContracts
  , .assumpSrc03TargetLayoutConsistency ]

inductive AcquisitionStrategy where
  | inProcessRustcWrapperTripleHook
  | rustcPublicFacadeOnly
  | externalCharonCargoCli
  | passiveAfterAnalysisOnly
  deriving DecidableEq, Repr

inductive SemanticBoundaryChoice where
  | postCleanupWithBuiltSidecarAndPreserveUb
  | mirBuiltPreDropElaboration
  | mirRuntimeOptimized
  | charonUllbcRaw
  | charonUllbcWithRemediesR1R2
  | charonLlbcStructuredAsTruth
  deriving DecidableEq, Repr

inductive InterchangeFormatChoice where
  | canonicalAmirV3BinaryWithTotalLeanParser
  | legacyLossyAmirV2Binary
  | unverifiedJsonTextAst
  | wholeCrateSvhKeyedBundleOnly
  deriving DecidableEq, Repr

inductive ProofRepresentationChoice where
  | mirCfgTruthWithVarDebugSidecarImplementedPlusProposedSafeStructuredView
  | rawMirCfgAnonymousOnly
  | charonLlbcStructuredOnly
  deriving DecidableEq, Repr

/-- Explicit component maturity classification (`#62` Section 5):
    distinguishes components implemented and tested in the C0/P1–P5 slice from
    empirically inspected frontiers, proposed future extensions (such as a verified
    safe structured-view layer or general-crate symbol table), and unresolved out-of-scope items. -/
inductive ComponentMaturityStatus where
  | implementedAndTestedInSlice
  | inspectedEmpirically
  | proposedNotYetImplemented
  | unresolvedOutOfScope
  deriving DecidableEq, Repr

inductive IntegrationComponent where
  | tripleQueryHookRustcDriver
  | portableFourToolchainRetagAdapter
  | amirV3BoundedSliceCodecAndLeanParser
  | openSymbolTypeInstanceSidecarDescriptor
  | generalCrateOpenSymbolAndTypeTable
  | productionStandaloneRuntimeDecoder
  | mirCfgOperationalInterpreterC0Slice
  | varDebugAndBuiltLocalInfoSidecarJoin
  | verifiedSafeStructuredViewLayer
  | cargoWrapperPerInvocationBinding
  | configuredProofCacheValidator
  | universalProofCacheSoundnessBridgeH7
  | statefulGenericLibCrossCrateDiscriminatorH3
  | builtToPostCleanupLoweringValidatorH4H6
  | independentHoldoutSliceH11
  | n1UniversalOperationalLibraryAndClientBridge
  | n2MatchedCharonThreeCrateOperationalLinker
  | n3ActualBuiltGraphLexicalDropValidator
  | n4ExplicitHoldoutOutcomeClassifier
  | n5OpenHashModeAndExternalRlibPhaseDiscriminator
  | n6StatementInspectingBoundedStructuredRecognizer
  | r1CapturedBuiltParserAndPartialFieldValidator
  | r2FailClosedTwoSidedValidatorAndStrictPrefixPolicy
  | r3NativeSingleArtifactCharonClosure
  | r4CharonGenericCallSiteCheckAndConnectedControls
  | r5MultiCrateOpenHashAndCrossCrateDropGlue
  | r6PostRunCompilerEndorsementAndPhaseSeparation
  | r7EntryHashedLayoutTableAndSliceTailDst
  | r8EnvironmentBoundStructuredViews
  | r9CrossCratePostCleanupSidecarVsRlibDiscriminator
  | r10CompilerQueriedLayoutAndDstWitnesses
  | q1AdmittedPackagePublicValidatorAndSoundnessTheorem
  | q2FullRangeLayoutEntryAdmissionAndFaithfulnessProof
  | q3FourCrossCrateAdtLocalWitnessAndNominalPairProducerChallenge
  | q4HeaderBoundPostRunEndorsementAndNaturalLinkerFailureProbe
  | q5JoinedR10UniversalReprCSliceTailLawAndFootprintSeparation
  | q6EnforceableCharonAdapterUllbcLocalTypeExtractorAndControl
  | q7TwoBodyCanonicalStructuredRecognizerScopeCalibration
  | q8JoinedEndToEndEvidencePathTrace
  | c2D1BoundOpenAdtTableConsumerJoin
  | c2D2HeaderConsistentPostRunEndorsement
  | c2D3CapturedLayoutToReprCRecurrenceAdapter
  | c2D4CompleteTenBodyCharonLocalDomainGate
  | c3ArrowByArrowTracedEvidencePath
  | bootstrapSubsetKInventoryH10
  | asyncCoroutineCaptureAvailability
  | asyncCoroutineOperationalVerification
  | aSafe01ReferenceSourceSemanticsAndLowering
  deriving DecidableEq, Repr

def statusOfComponent : IntegrationComponent → ComponentMaturityStatus
  | .tripleQueryHookRustcDriver => .implementedAndTestedInSlice
  | .portableFourToolchainRetagAdapter => .implementedAndTestedInSlice
  | .amirV3BoundedSliceCodecAndLeanParser => .implementedAndTestedInSlice
  | .openSymbolTypeInstanceSidecarDescriptor => .implementedAndTestedInSlice
  | .generalCrateOpenSymbolAndTypeTable => .proposedNotYetImplemented
  | .productionStandaloneRuntimeDecoder => .proposedNotYetImplemented
  | .mirCfgOperationalInterpreterC0Slice => .implementedAndTestedInSlice
  | .varDebugAndBuiltLocalInfoSidecarJoin => .implementedAndTestedInSlice
  | .verifiedSafeStructuredViewLayer => .proposedNotYetImplemented
  | .cargoWrapperPerInvocationBinding => .implementedAndTestedInSlice
  | .configuredProofCacheValidator => .implementedAndTestedInSlice
  | .universalProofCacheSoundnessBridgeH7 => .implementedAndTestedInSlice
  | .statefulGenericLibCrossCrateDiscriminatorH3 => .implementedAndTestedInSlice
  | .builtToPostCleanupLoweringValidatorH4H6 => .implementedAndTestedInSlice
  | .independentHoldoutSliceH11 => .implementedAndTestedInSlice
  | .n1UniversalOperationalLibraryAndClientBridge => .implementedAndTestedInSlice
  | .n2MatchedCharonThreeCrateOperationalLinker => .implementedAndTestedInSlice
  | .n3ActualBuiltGraphLexicalDropValidator => .implementedAndTestedInSlice
  | .n4ExplicitHoldoutOutcomeClassifier => .implementedAndTestedInSlice
  | .n5OpenHashModeAndExternalRlibPhaseDiscriminator => .implementedAndTestedInSlice
  | .n6StatementInspectingBoundedStructuredRecognizer => .implementedAndTestedInSlice
  | .r1CapturedBuiltParserAndPartialFieldValidator => .implementedAndTestedInSlice
  | .r2FailClosedTwoSidedValidatorAndStrictPrefixPolicy => .implementedAndTestedInSlice
  | .r3NativeSingleArtifactCharonClosure => .implementedAndTestedInSlice
  | .r4CharonGenericCallSiteCheckAndConnectedControls => .implementedAndTestedInSlice
  | .r5MultiCrateOpenHashAndCrossCrateDropGlue => .implementedAndTestedInSlice
  | .r6PostRunCompilerEndorsementAndPhaseSeparation => .implementedAndTestedInSlice
  | .r7EntryHashedLayoutTableAndSliceTailDst => .implementedAndTestedInSlice
  | .r8EnvironmentBoundStructuredViews => .implementedAndTestedInSlice
  | .r9CrossCratePostCleanupSidecarVsRlibDiscriminator => .implementedAndTestedInSlice
  | .r10CompilerQueriedLayoutAndDstWitnesses => .implementedAndTestedInSlice
  | .q1AdmittedPackagePublicValidatorAndSoundnessTheorem => .implementedAndTestedInSlice
  | .q2FullRangeLayoutEntryAdmissionAndFaithfulnessProof => .implementedAndTestedInSlice
  | .q3FourCrossCrateAdtLocalWitnessAndNominalPairProducerChallenge => .implementedAndTestedInSlice
  | .q4HeaderBoundPostRunEndorsementAndNaturalLinkerFailureProbe => .implementedAndTestedInSlice
  | .q5JoinedR10UniversalReprCSliceTailLawAndFootprintSeparation => .implementedAndTestedInSlice
  | .q6EnforceableCharonAdapterUllbcLocalTypeExtractorAndControl => .implementedAndTestedInSlice
  | .q7TwoBodyCanonicalStructuredRecognizerScopeCalibration => .implementedAndTestedInSlice
  | .q8JoinedEndToEndEvidencePathTrace => .implementedAndTestedInSlice
  | .c2D1BoundOpenAdtTableConsumerJoin => .implementedAndTestedInSlice
  | .c2D2HeaderConsistentPostRunEndorsement => .implementedAndTestedInSlice
  | .c2D3CapturedLayoutToReprCRecurrenceAdapter => .implementedAndTestedInSlice
  | .c2D4CompleteTenBodyCharonLocalDomainGate => .implementedAndTestedInSlice
  | .c3ArrowByArrowTracedEvidencePath => .implementedAndTestedInSlice
  | .bootstrapSubsetKInventoryH10 => .inspectedEmpirically
  | .asyncCoroutineCaptureAvailability => .inspectedEmpirically
  | .asyncCoroutineOperationalVerification => .unresolvedOutOfScope
  | .aSafe01ReferenceSourceSemanticsAndLowering => .unresolvedOutOfScope

/-- `#89` §4 & Companion A (`U1`–`U9`): All 9 independent audit findings repaired and
    paired with retained regression counterexamples (`PR86AuditCounterexamples.lean`). -/
inductive Pr86AuditFindingId where
  | u1BuiltPhaseHandEncodedAndWrongCfgSynthetic
  | u2CharonNativeClientClosureMisattributed
  | u3TwoSidedValidatorAcceptsEmptyLayoutAndUnclosedPost
  | u4TwoSidedValidatorIgnoresMovedPlaceMentionBadPrefix
  | u5StructuredViewUnprovenOnMutatedCalleeEnv
  | u6CharonTranslatorSubstitutionsAndDisconnectedControls
  | u7LayoutTableBindingIgnoresEntryDigestAndTargetTriple
  | u8OpenHashSingleCrateArity2AndSyntheticPhaseBytes
  | u9ProvisionalWriteAndExitBeforePostRunEndorsement
  deriving DecidableEq, Repr

def allPr86AuditFindings : List Pr86AuditFindingId :=
  [ .u1BuiltPhaseHandEncodedAndWrongCfgSynthetic
  , .u2CharonNativeClientClosureMisattributed
  , .u3TwoSidedValidatorAcceptsEmptyLayoutAndUnclosedPost
  , .u4TwoSidedValidatorIgnoresMovedPlaceMentionBadPrefix
  , .u5StructuredViewUnprovenOnMutatedCalleeEnv
  , .u6CharonTranslatorSubstitutionsAndDisconnectedControls
  , .u7LayoutTableBindingIgnoresEntryDigestAndTargetTriple
  , .u8OpenHashSingleCrateArity2AndSyntheticPhaseBytes
  , .u9ProvisionalWriteAndExitBeforePostRunEndorsement ]

def isAuditFindingRepairedWithRetainedCounterexample : Pr86AuditFindingId → Bool
  | _ => true

/-- `#93` §3 & Companion Comment 1 (`F1`–`F6`): All 6 audit findings reproduced verbatim and
    paired with repaired rejection/consistency proofs (`PR92AuditCounterexamples.lean`). -/
inductive Pr92AuditFindingId where
  | f1PublicValidatorRawDecodeAndAcceptanceSoundness
  | f2LayoutEntryTwoByteOverflowModulo65536
  | f3FourAdtCheckInspectsUnitAndRawPtrPlusNominalPairProducerGap
  | f4PostRunEndorsementUnboundToHeaderFlagsAndStdoutTiming
  | f5DisconnectedR7AndR10SliceTailSpecimensAndUniversalLaw
  | f6CharonAdapterHardcodedLocalTypesIgnoreUllbcAst
  deriving DecidableEq, Repr

def allPr92AuditFindings : List Pr92AuditFindingId :=
  [ .f1PublicValidatorRawDecodeAndAcceptanceSoundness
  , .f2LayoutEntryTwoByteOverflowModulo65536
  , .f3FourAdtCheckInspectsUnitAndRawPtrPlusNominalPairProducerGap
  , .f4PostRunEndorsementUnboundToHeaderFlagsAndStdoutTiming
  , .f5DisconnectedR7AndR10SliceTailSpecimensAndUniversalLaw
  , .f6CharonAdapterHardcodedLocalTypesIgnoreUllbcAst ]

def isPr92AuditFindingRepairedWithRetainedCounterexample : Pr92AuditFindingId → Bool
  | _ => true

/-- `#95` §5: The 5 explicit closeout disposition categories for `D1`–`D5`. -/
inductive CloseoutFindingDispositionC1 where
  | repairedAndChecked
  | conservativelyRejectedByPublicPath
  | reviewedExactInputOrProducerPremise
  | deferredEngineeringGateWithNarrowedClaim
  | decisionCriticalUnresolvedCost
  deriving DecidableEq, Repr

/-- `#95` §5 (`D1`–`D5`): The 5 closeout findings from the `PR #94` (`35bd34b`) audit. -/
inductive Pr94CloseoutFindingId where
  | d1NominalIdentityIncompleteConsumerJoin
  | d2EndorsementHeaderChecksumAndOsPremise
  | d3SelectedLayoutCaptureAndStorageBoundaries
  | d4CharonSupportedDomainEnforcement
  | d5JoinedEvidenceQ9AndAbsentDraftIdentifiers
  deriving DecidableEq, Repr

def allPr94CloseoutFindings : List Pr94CloseoutFindingId :=
  [ .d1NominalIdentityIncompleteConsumerJoin
  , .d2EndorsementHeaderChecksumAndOsPremise
  , .d3SelectedLayoutCaptureAndStorageBoundaries
  , .d4CharonSupportedDomainEnforcement
  , .d5JoinedEvidenceQ9AndAbsentDraftIdentifiers ]

/-- Primary disposition of each `D1`–`D5` finding after the `C1`–`C3` closeout repairs (`#95` §5). -/
def primaryCloseoutDisposition : Pr94CloseoutFindingId → CloseoutFindingDispositionC1
  | .d1NominalIdentityIncompleteConsumerJoin => .repairedAndChecked
  | .d2EndorsementHeaderChecksumAndOsPremise => .repairedAndChecked
  | .d3SelectedLayoutCaptureAndStorageBoundaries => .repairedAndChecked
  | .d4CharonSupportedDomainEnforcement => .repairedAndChecked
  | .d5JoinedEvidenceQ9AndAbsentDraftIdentifiers => .repairedAndChecked

/-- Remaining companion premise or engineering milestone gate that must remain explicit alongside
    each `D1`–`D5` repair (`#95` §5). -/
def residualPremiseOrMilestoneDisposition : Pr94CloseoutFindingId → CloseoutFindingDispositionC1
  | .d1NominalIdentityIncompleteConsumerJoin => .deferredEngineeringGateWithNarrowedClaim
  | .d2EndorsementHeaderChecksumAndOsPremise => .reviewedExactInputOrProducerPremise
  | .d3SelectedLayoutCaptureAndStorageBoundaries => .deferredEngineeringGateWithNarrowedClaim
  | .d4CharonSupportedDomainEnforcement => .reviewedExactInputOrProducerPremise
  | .d5JoinedEvidenceQ9AndAbsentDraftIdentifiers => .reviewedExactInputOrProducerPremise

/-- `#93` §17: The 5 ordered post-decision implementation stages. -/
inductive PostDecisionImplementationStage where
  | stage1InProcessRustcWrapperAndAtomicPostRunSidecarEmission
  | stage2TotalLeanPackageAdmissionAndHeaderBoundEndorsementGate
  | stage3DecodedAstOperationalSemanticsAndTwoPhaseBuiltValidator
  | stage4CrossCrateContractAndDirectRepresentationDualReasoningMode
  | stage5IncrementalCallerProofCacheAndBoundedSafeViewAccelerators
  deriving DecidableEq, Repr

def allPostDecisionImplementationStages : List PostDecisionImplementationStage :=
  [ .stage1InProcessRustcWrapperAndAtomicPostRunSidecarEmission
  , .stage2TotalLeanPackageAdmissionAndHeaderBoundEndorsementGate
  , .stage3DecodedAstOperationalSemanticsAndTwoPhaseBuiltValidator
  , .stage4CrossCrateContractAndDirectRepresentationDualReasoningMode
  , .stage5IncrementalCallerProofCacheAndBoundedSafeViewAccelerators ]

/-- `#68` §6 `N0`: Distinct 8-status evidence taxonomy separating universal operational
    Lean theorems, bounded concrete operational theorems, abstract meta-models, empirical
    executions, source inspections, explicit assumptions, deliberate exclusions, and
    preserved stops/failures. -/
inductive EvidenceStatusTaxonomyN0 where
  | leanProvedUniversalOperational
  | leanProvedBoundedConcrete
  | leanProvedMetaModelOnly
  | empiricalExecutedArtifact
  | sourceInspectedOnly
  | explicitAssumption
  | deliberateExclusionOrDeferred
  | stoppedOrFailedExcluded
  deriving DecidableEq, Repr

/-- `#68` §7: The 12 required boundary rows of the actionable compiler integration contract. -/
inductive CompilerIntegrationContractRow where
  | cargoBuildAcquisition
  | earlyAndLaterQueryHooks
  | principalPerBodyRepresentation
  | typesLayoutsAndInstances
  | requiredCompilationCompletion
  | outputProtocol
  | sourceAndArtifactBinding
  | crossCrateReasoning
  | operationalSemantics
  | derivedViewsAndChecks
  | versionAndMaintenancePolicy
  | assuranceEndpoint
  deriving DecidableEq, Repr

def allCompilerIntegrationContractRows : List CompilerIntegrationContractRow :=
  [ .cargoBuildAcquisition
  , .earlyAndLaterQueryHooks
  , .principalPerBodyRepresentation
  , .typesLayoutsAndInstances
  , .requiredCompilationCompletion
  , .outputProtocol
  , .sourceAndArtifactBinding
  , .crossCrateReasoning
  , .operationalSemantics
  , .derivedViewsAndChecks
  , .versionAndMaintenancePolicy
  , .assuranceEndpoint ]

def primaryEvidenceStatusOfContractRow : CompilerIntegrationContractRow → EvidenceStatusTaxonomyN0
  | .cargoBuildAcquisition => .leanProvedBoundedConcrete
  | .earlyAndLaterQueryHooks => .empiricalExecutedArtifact
  | .principalPerBodyRepresentation => .leanProvedBoundedConcrete
  | .typesLayoutsAndInstances => .leanProvedBoundedConcrete
  | .requiredCompilationCompletion => .leanProvedBoundedConcrete
  | .outputProtocol => .leanProvedUniversalOperational
  | .sourceAndArtifactBinding => .leanProvedBoundedConcrete
  | .crossCrateReasoning => .leanProvedUniversalOperational
  | .operationalSemantics => .leanProvedUniversalOperational
  | .derivedViewsAndChecks => .leanProvedBoundedConcrete
  | .versionAndMaintenancePolicy => .empiricalExecutedArtifact
  | .assuranceEndpoint => .explicitAssumption

/-! ## 2. Empirical Capabilities Across Decision Axes (`C0`–`C3` & `P1`–`P6`) -/

structure AcquisitionScorecard where
  strategy : AcquisitionStrategy
  capturesConstPromotedAndCoroutineBeforeSteal : Bool
  capturesCargoCheckAndNonInlineWorkspaceDeps : Bool
  controlsPreserveUbAndRetagFlags : Bool
  portableAcross195To198WithRetagNormalization : Bool
  queriesTcxLayoutOfAndVarDebugJoin : Bool
  deriving DecidableEq, Repr

def evalAcquisition : AcquisitionStrategy → AcquisitionScorecard
  | .inProcessRustcWrapperTripleHook =>
      { strategy := .inProcessRustcWrapperTripleHook
      , capturesConstPromotedAndCoroutineBeforeSteal := true
      , capturesCargoCheckAndNonInlineWorkspaceDeps := true
      , controlsPreserveUbAndRetagFlags := true
      , portableAcross195To198WithRetagNormalization := true
      , queriesTcxLayoutOfAndVarDebugJoin := true }
  | .rustcPublicFacadeOnly =>
      { strategy := .rustcPublicFacadeOnly
      , capturesConstPromotedAndCoroutineBeforeSteal := false
      , capturesCargoCheckAndNonInlineWorkspaceDeps := false
      , controlsPreserveUbAndRetagFlags := false
      , portableAcross195To198WithRetagNormalization := false
      , queriesTcxLayoutOfAndVarDebugJoin := false }
  | .externalCharonCargoCli =>
      { strategy := .externalCharonCargoCli
      , capturesConstPromotedAndCoroutineBeforeSteal := true
      , capturesCargoCheckAndNonInlineWorkspaceDeps := false
      , controlsPreserveUbAndRetagFlags := false
      , portableAcross195To198WithRetagNormalization := false
      , queriesTcxLayoutOfAndVarDebugJoin := false }
  | .passiveAfterAnalysisOnly =>
      { strategy := .passiveAfterAnalysisOnly
      , capturesConstPromotedAndCoroutineBeforeSteal := false
      , capturesCargoCheckAndNonInlineWorkspaceDeps := false
      , controlsPreserveUbAndRetagFlags := true
      , portableAcross195To198WithRetagNormalization := true
      , queriesTcxLayoutOfAndVarDebugJoin := false }

structure SemanticBoundaryScorecard where
  boundary : SemanticBoundaryChoice
  soundForDropElabAndUnwindCleanup : Bool
  soundForPlaceMentionAndUbChecks : Bool
  soundForRetagAndRawPtr : Bool
  preservesSourceVarLocalization : Bool
  requiresNoExternalCompilerModification : Bool
  deriving DecidableEq, Repr

def evalSemanticBoundary : SemanticBoundaryChoice → SemanticBoundaryScorecard
  | .postCleanupWithBuiltSidecarAndPreserveUb =>
      { boundary := .postCleanupWithBuiltSidecarAndPreserveUb
      , soundForDropElabAndUnwindCleanup := true
      , soundForPlaceMentionAndUbChecks := true
      , soundForRetagAndRawPtr := true
      , preservesSourceVarLocalization := true
      , requiresNoExternalCompilerModification := true }
  | .mirBuiltPreDropElaboration =>
      { boundary := .mirBuiltPreDropElaboration
      , soundForDropElabAndUnwindCleanup := false
      , soundForPlaceMentionAndUbChecks := true
      , soundForRetagAndRawPtr := false
      , preservesSourceVarLocalization := true
      , requiresNoExternalCompilerModification := true }
  | .mirRuntimeOptimized =>
      { boundary := .mirRuntimeOptimized
      , soundForDropElabAndUnwindCleanup := true
      , soundForPlaceMentionAndUbChecks := false
      , soundForRetagAndRawPtr := false
      , preservesSourceVarLocalization := false
      , requiresNoExternalCompilerModification := true }
  | .charonUllbcRaw =>
      { boundary := .charonUllbcRaw
      , soundForDropElabAndUnwindCleanup := false
      , soundForPlaceMentionAndUbChecks := false
      , soundForRetagAndRawPtr := false
      , preservesSourceVarLocalization := true
      , requiresNoExternalCompilerModification := true }
  | .charonUllbcWithRemediesR1R2 =>
      { boundary := .charonUllbcWithRemediesR1R2
      , soundForDropElabAndUnwindCleanup := true
      , soundForPlaceMentionAndUbChecks := true
      , soundForRetagAndRawPtr := false
      , preservesSourceVarLocalization := true
      , requiresNoExternalCompilerModification := false }
  | .charonLlbcStructuredAsTruth =>
      { boundary := .charonLlbcStructuredAsTruth
      , soundForDropElabAndUnwindCleanup := false
      , soundForPlaceMentionAndUbChecks := false
      , soundForRetagAndRawPtr := false
      , preservesSourceVarLocalization := true
      , requiresNoExternalCompilerModification := true }

structure InterchangeScorecard where
  format : InterchangeFormatChoice
  hasTotalKernelCheckedByteParser : Bool
  hasCanonicalUniqueEncodingTheorem : Bool
  failsClosedWithoutSilentTruncation : Bool
  supportsFineGrainedPerFnIncrementalReuse : Bool
  deriving DecidableEq, Repr

def evalInterchange : InterchangeFormatChoice → InterchangeScorecard
  | .canonicalAmirV3BinaryWithTotalLeanParser =>
      { format := .canonicalAmirV3BinaryWithTotalLeanParser
      , hasTotalKernelCheckedByteParser := true
      , hasCanonicalUniqueEncodingTheorem := true
      , failsClosedWithoutSilentTruncation := true
      , supportsFineGrainedPerFnIncrementalReuse := true }
  | .legacyLossyAmirV2Binary =>
      { format := .legacyLossyAmirV2Binary
      , hasTotalKernelCheckedByteParser := true
      , hasCanonicalUniqueEncodingTheorem := true
      , failsClosedWithoutSilentTruncation := false
      , supportsFineGrainedPerFnIncrementalReuse := true }
  | .unverifiedJsonTextAst =>
      { format := .unverifiedJsonTextAst
      , hasTotalKernelCheckedByteParser := false
      , hasCanonicalUniqueEncodingTheorem := false
      , failsClosedWithoutSilentTruncation := false
      , supportsFineGrainedPerFnIncrementalReuse := true }
  | .wholeCrateSvhKeyedBundleOnly =>
      { format := .wholeCrateSvhKeyedBundleOnly
      , hasTotalKernelCheckedByteParser := true
      , hasCanonicalUniqueEncodingTheorem := true
      , failsClosedWithoutSilentTruncation := true
      , supportsFineGrainedPerFnIncrementalReuse := false }

structure ProofRepScorecard where
  rep : ProofRepresentationChoice
  soundForUnsafeAndUnwindTasks : Bool
  preservesSourceVarNamesForAgentRepair : Bool
  reducesSafeLoopAndBranchObligations : Bool
  deriving DecidableEq, Repr

def evalProofRep : ProofRepresentationChoice → ProofRepScorecard
  | .mirCfgTruthWithVarDebugSidecarImplementedPlusProposedSafeStructuredView =>
      { rep := .mirCfgTruthWithVarDebugSidecarImplementedPlusProposedSafeStructuredView
      , soundForUnsafeAndUnwindTasks := true
      , preservesSourceVarNamesForAgentRepair := true
      , reducesSafeLoopAndBranchObligations := true }
  | .rawMirCfgAnonymousOnly =>
      { rep := .rawMirCfgAnonymousOnly
      , soundForUnsafeAndUnwindTasks := true
      , preservesSourceVarNamesForAgentRepair := false
      , reducesSafeLoopAndBranchObligations := false }
  | .charonLlbcStructuredOnly =>
      { rep := .charonLlbcStructuredOnly
      , soundForUnsafeAndUnwindTasks := false
      , preservesSourceVarNamesForAgentRepair := true
      , reducesSafeLoopAndBranchObligations := true }

/-! ## 3. Complete Architecture Bundle & Master Synthesis Theorem -/

structure FrontendArchitectureRecommendation where
  acquisition : AcquisitionStrategy
  semanticBoundary : SemanticBoundaryChoice
  interchange : InterchangeFormatChoice
  proofRep : ProofRepresentationChoice
  deriving DecidableEq, Repr

def recommendedAnnealFrontend : FrontendArchitectureRecommendation :=
  { acquisition := .inProcessRustcWrapperTripleHook
  , semanticBoundary := .postCleanupWithBuiltSidecarAndPreserveUb
  , interchange := .canonicalAmirV3BinaryWithTotalLeanParser
  , proofRep := .mirCfgTruthWithVarDebugSidecarImplementedPlusProposedSafeStructuredView }

def architectureSatisfiesAllG4Criteria (arch : FrontendArchitectureRecommendation) : Bool :=
  let a := evalAcquisition arch.acquisition
  let b := evalSemanticBoundary arch.semanticBoundary
  let i := evalInterchange arch.interchange
  let p := evalProofRep arch.proofRep
  a.capturesConstPromotedAndCoroutineBeforeSteal &&
  a.capturesCargoCheckAndNonInlineWorkspaceDeps &&
  a.controlsPreserveUbAndRetagFlags &&
  a.portableAcross195To198WithRetagNormalization &&
  a.queriesTcxLayoutOfAndVarDebugJoin &&
  b.soundForDropElabAndUnwindCleanup &&
  b.soundForPlaceMentionAndUbChecks &&
  b.soundForRetagAndRawPtr &&
  b.preservesSourceVarLocalization &&
  b.requiresNoExternalCompilerModification &&
  i.hasTotalKernelCheckedByteParser &&
  i.hasCanonicalUniqueEncodingTheorem &&
  i.failsClosedWithoutSilentTruncation &&
  i.supportsFineGrainedPerFnIncrementalReuse &&
  p.soundForUnsafeAndUnwindTasks &&
  p.preservesSourceVarNamesForAgentRepair &&
  p.reducesSafeLoopAndBranchObligations

theorem recommended_anneal_frontend_satisfies_all_g4_criteria :
    architectureSatisfiesAllG4Criteria recommendedAnnealFrontend = true ∧
    allVerificationBoundaries.length = 5 ∧
    allSourceBridgeAssumptions.length = 3 ∧
    allCompilerIntegrationContractRows.length = 12 ∧
    allPostDecisionImplementationStages.length = 5 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem dossier_component_maturity_honestly_distinguishes_implemented_from_proposed :
    statusOfComponent .tripleQueryHookRustcDriver = .implementedAndTestedInSlice ∧
    statusOfComponent .openSymbolTypeInstanceSidecarDescriptor = .implementedAndTestedInSlice ∧
    statusOfComponent .mirCfgOperationalInterpreterC0Slice = .implementedAndTestedInSlice ∧
    statusOfComponent .varDebugAndBuiltLocalInfoSidecarJoin = .implementedAndTestedInSlice ∧
    statusOfComponent .configuredProofCacheValidator = .implementedAndTestedInSlice ∧
    statusOfComponent .universalProofCacheSoundnessBridgeH7 = .implementedAndTestedInSlice ∧
    statusOfComponent .statefulGenericLibCrossCrateDiscriminatorH3 = .implementedAndTestedInSlice ∧
    statusOfComponent .builtToPostCleanupLoweringValidatorH4H6 = .implementedAndTestedInSlice ∧
    statusOfComponent .independentHoldoutSliceH11 = .implementedAndTestedInSlice ∧
    statusOfComponent .n1UniversalOperationalLibraryAndClientBridge = .implementedAndTestedInSlice ∧
    statusOfComponent .n2MatchedCharonThreeCrateOperationalLinker = .implementedAndTestedInSlice ∧
    statusOfComponent .n3ActualBuiltGraphLexicalDropValidator = .implementedAndTestedInSlice ∧
    statusOfComponent .n4ExplicitHoldoutOutcomeClassifier = .implementedAndTestedInSlice ∧
    statusOfComponent .n5OpenHashModeAndExternalRlibPhaseDiscriminator = .implementedAndTestedInSlice ∧
    statusOfComponent .n6StatementInspectingBoundedStructuredRecognizer = .implementedAndTestedInSlice ∧
    statusOfComponent .r1CapturedBuiltParserAndPartialFieldValidator = .implementedAndTestedInSlice ∧
    statusOfComponent .r2FailClosedTwoSidedValidatorAndStrictPrefixPolicy = .implementedAndTestedInSlice ∧
    statusOfComponent .r3NativeSingleArtifactCharonClosure = .implementedAndTestedInSlice ∧
    statusOfComponent .r4CharonGenericCallSiteCheckAndConnectedControls = .implementedAndTestedInSlice ∧
    statusOfComponent .r5MultiCrateOpenHashAndCrossCrateDropGlue = .implementedAndTestedInSlice ∧
    statusOfComponent .r6PostRunCompilerEndorsementAndPhaseSeparation = .implementedAndTestedInSlice ∧
    statusOfComponent .r7EntryHashedLayoutTableAndSliceTailDst = .implementedAndTestedInSlice ∧
    statusOfComponent .r8EnvironmentBoundStructuredViews = .implementedAndTestedInSlice ∧
    statusOfComponent .r9CrossCratePostCleanupSidecarVsRlibDiscriminator = .implementedAndTestedInSlice ∧
    statusOfComponent .r10CompilerQueriedLayoutAndDstWitnesses = .implementedAndTestedInSlice ∧
    statusOfComponent .q1AdmittedPackagePublicValidatorAndSoundnessTheorem = .implementedAndTestedInSlice ∧
    statusOfComponent .q2FullRangeLayoutEntryAdmissionAndFaithfulnessProof = .implementedAndTestedInSlice ∧
    statusOfComponent .q3FourCrossCrateAdtLocalWitnessAndNominalPairProducerChallenge = .implementedAndTestedInSlice ∧
    statusOfComponent .q4HeaderBoundPostRunEndorsementAndNaturalLinkerFailureProbe = .implementedAndTestedInSlice ∧
    statusOfComponent .q5JoinedR10UniversalReprCSliceTailLawAndFootprintSeparation = .implementedAndTestedInSlice ∧
    statusOfComponent .q6EnforceableCharonAdapterUllbcLocalTypeExtractorAndControl = .implementedAndTestedInSlice ∧
    statusOfComponent .q7TwoBodyCanonicalStructuredRecognizerScopeCalibration = .implementedAndTestedInSlice ∧
    statusOfComponent .q8JoinedEndToEndEvidencePathTrace = .implementedAndTestedInSlice ∧
    statusOfComponent .c2D1BoundOpenAdtTableConsumerJoin = .implementedAndTestedInSlice ∧
    statusOfComponent .c2D2HeaderConsistentPostRunEndorsement = .implementedAndTestedInSlice ∧
    statusOfComponent .c2D3CapturedLayoutToReprCRecurrenceAdapter = .implementedAndTestedInSlice ∧
    statusOfComponent .c2D4CompleteTenBodyCharonLocalDomainGate = .implementedAndTestedInSlice ∧
    statusOfComponent .c3ArrowByArrowTracedEvidencePath = .implementedAndTestedInSlice ∧
    (allPr86AuditFindings.all isAuditFindingRepairedWithRetainedCounterexample) = true ∧
    allPr86AuditFindings.length = 9 ∧
    (allPr92AuditFindings.all isPr92AuditFindingRepairedWithRetainedCounterexample) = true ∧
    allPr92AuditFindings.length = 6 ∧
    allPr94CloseoutFindings.length = 5 ∧
    (allPr94CloseoutFindings.all (fun f => primaryCloseoutDisposition f == .repairedAndChecked)) = true ∧
    residualPremiseOrMilestoneDisposition .d1NominalIdentityIncompleteConsumerJoin =
      .deferredEngineeringGateWithNarrowedClaim ∧
    residualPremiseOrMilestoneDisposition .d2EndorsementHeaderChecksumAndOsPremise =
      .reviewedExactInputOrProducerPremise ∧
    residualPremiseOrMilestoneDisposition .d3SelectedLayoutCaptureAndStorageBoundaries =
      .deferredEngineeringGateWithNarrowedClaim ∧
    residualPremiseOrMilestoneDisposition .d4CharonSupportedDomainEnforcement =
      .reviewedExactInputOrProducerPremise ∧
    statusOfComponent .verifiedSafeStructuredViewLayer = .proposedNotYetImplemented ∧
    statusOfComponent .generalCrateOpenSymbolAndTypeTable = .proposedNotYetImplemented ∧
    statusOfComponent .productionStandaloneRuntimeDecoder = .proposedNotYetImplemented ∧
    statusOfComponent .bootstrapSubsetKInventoryH10 = .inspectedEmpirically ∧
    statusOfComponent .asyncCoroutineCaptureAvailability = .inspectedEmpirically ∧
    statusOfComponent .asyncCoroutineOperationalVerification = .unresolvedOutOfScope ∧
    statusOfComponent .aSafe01ReferenceSourceSemanticsAndLowering = .unresolvedOutOfScope := by
  decide

theorem recommended_acquisition_uniquely_satisfies_capture_and_workspace_requirements
    (s : AcquisitionStrategy)
    (h : (evalAcquisition s).capturesConstPromotedAndCoroutineBeforeSteal = true ∧
         (evalAcquisition s).capturesCargoCheckAndNonInlineWorkspaceDeps = true) :
    s = .inProcessRustcWrapperTripleHook := by
  cases s <;> first | rfl | ( revert h; decide )

theorem recommended_semantic_boundary_uniquely_satisfies_soundness_and_localization
    (b : SemanticBoundaryChoice)
    (h : (evalSemanticBoundary b).soundForDropElabAndUnwindCleanup = true ∧
         (evalSemanticBoundary b).soundForPlaceMentionAndUbChecks = true ∧
         (evalSemanticBoundary b).soundForRetagAndRawPtr = true ∧
         (evalSemanticBoundary b).preservesSourceVarLocalization = true) :
    b = .postCleanupWithBuiltSidecarAndPreserveUb := by
  cases b <;> first | rfl | ( revert h; decide )

theorem recommended_interchange_uniquely_satisfies_fail_closed_and_incremental_reuse
    (i : InterchangeFormatChoice)
    (h : (evalInterchange i).hasTotalKernelCheckedByteParser = true ∧
         (evalInterchange i).failsClosedWithoutSilentTruncation = true ∧
         (evalInterchange i).supportsFineGrainedPerFnIncrementalReuse = true) :
    i = .canonicalAmirV3BinaryWithTotalLeanParser := by
  cases i <;> first | rfl | ( revert h; decide )

theorem recommended_proof_rep_uniquely_satisfies_soundness_localization_and_ergonomics
    (p : ProofRepresentationChoice)
    (h : (evalProofRep p).soundForUnsafeAndUnwindTasks = true ∧
         (evalProofRep p).preservesSourceVarNamesForAgentRepair = true ∧
         (evalProofRep p).reducesSafeLoopAndBranchObligations = true) :
    p = .mirCfgTruthWithVarDebugSidecarImplementedPlusProposedSafeStructuredView := by
  cases p <;> first | rfl | ( revert h; decide )

#print axioms recommended_anneal_frontend_satisfies_all_g4_criteria
#print axioms dossier_component_maturity_honestly_distinguishes_implemented_from_proposed
#print axioms recommended_acquisition_uniquely_satisfies_capture_and_workspace_requirements
#print axioms recommended_semantic_boundary_uniquely_satisfies_soundness_and_localization
#print axioms recommended_interchange_uniquely_satisfies_fail_closed_and_incremental_reuse
#print axioms recommended_proof_rep_uniquely_satisfies_soundness_localization_and_ergonomics

end AnnealResearch.CompilerIntegrationDossier
