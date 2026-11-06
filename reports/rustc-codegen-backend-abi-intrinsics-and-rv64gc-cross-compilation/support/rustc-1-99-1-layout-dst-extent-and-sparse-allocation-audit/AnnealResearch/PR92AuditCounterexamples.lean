import AnnealResearch.PR86AuditCounterexamples
import AnnealResearch.OpenHashMultiCrateR5R6R9R10

set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.PR92AuditCounterexamples

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.StatefulGenericLibraryH3H7
open AnnealResearch.StatefulGenericLibraryH3H7Controls
open AnnealResearch.PR86AuditRepairs
open AnnealResearch.PR86AuditCounterexamples
open AnnealResearch.CharonNativeAndControlsR3R4
open AnnealResearch.OpenHashMultiCrateR5R6R9R10

/-!
# `Q0`–`Q9`: Verbatim `#93` Appendix B Counterexamples (`F1`–`F6`), Paired Repaired Rejections, and `Q9` Shape-Preserving Challenge

1. **Section 1 (`Q0`, `#93` §5 & Appendix B):** Reproduces all 6 verbatim Lean counterexample
   theorems from `#93#issuecomment-6248388233` Appendix B against the preserved historical
   `PR #92` (`39c56d016351207792a0d29a7a51a6c7dabec18e`) definitions.
2. **Section 2 (`Q1`–`Q6`, `#93` §§6–11):** Proves the 6 paired repaired rejection and
   consistency theorems on the upgraded `Q1`–`Q6` entrypoints.
3. **Section 3 (`Q9`, `#93` §14):** Proves a new shape-preserving nominal-return-type-swap
   challenge (`q9_shape_preserving_nominal_return_swap_challenge`) on the `280`-byte
   `q3_nominal_pair_client.amir` package.
-/

/-! ## 1. Verbatim `#93` Appendix B Counterexamples Against Historical `39c56d0` Definitions (`F1`–`F5`) -/

def rawPost := decodePackageBodies realStatefulGenericLibAmirBytes

def duplicatedPost := rawPost ++ [body_D_64_4]

def mixedPhasePost := rawPost.map (fun b =>
  if b.symId == 64 then { b with mirPhase := .built } else b)

def checkPost (post : List WireBody)
    (layout : BoundCompilerLayoutTable := statefulGenericLibLayoutTable) : Bool :=
  validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving
    statefulGenericLibExpectedCtx statefulGenericLibBuiltBindingRec
    (bindingForPostBodies post) statefulGenericLibCrateBytes
    x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
    realStatefulGenericLibBuiltAmirBytes (encodePostBodies post)
    layout x86_64LinuxTargetTripleBytes

theorem repaired_validator_accepts_duplicate_symbols :
    checkPost duplicatedPost = true ∧
    isAdmittedPackageBytes (encodePostBodies duplicatedPost) = false := by decide

theorem repaired_validator_accepts_mixed_phases :
    checkPost mixedPhasePost = true ∧
    isAdmittedPackageBytes (encodePostBodies mixedPhasePost) = false := by decide

def aliasedSizeLayout : BoundCompilerLayoutTable :=
  { statefulGenericLibLayoutTable with entries :=
    statefulGenericLibLayoutTable.entries.map (fun e =>
      if e.typeTag == .u32 then { e with sizeBytes := e.sizeBytes + 65536 } else e) }

theorem layout_binding_loses_high_size_bits :
    encodeLayoutEntriesPayload aliasedSizeLayout.entries =
      encodeLayoutEntriesPayload statefulGenericLibLayoutTable.entries ∧
    checkLayoutTableBindingWithEntries statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16 aliasedSizeLayout x86_64LinuxTargetTripleBytes = true ∧
    checkPost rawPost aliasedSizeLayout = true := by decide

def claimedFourAdtTags : List Nat :=
  [ (findBodyBySym r5ClientAppBodies 208).map
      (fun b => specEncodeTypeTag (getLocalTypeAt b.localTypes 1))
  , (findBodyBySym r5ClientAppBodies 168).map
      (fun b => specEncodeTypeTag (getLocalTypeAt b.localTypes 1))
  , (findBodyBySym r5ClientAppBodies 117).map
      (fun b => specEncodeTypeTag (getLocalTypeAt b.localTypes 0))
  , (findBodyBySym r5ClientAppBodies 152).map
      (fun b => specEncodeTypeTag (getLocalTypeAt b.localTypes 1))
  ].map (fun x => x.getD 255)

theorem four_adt_check_compares_reference_pointer_unit_and_one_adt :
    claimedFourAdtTags = [6, 5, 1, 17] ∧
    hasDistinctFourCrossCrateAdtTags r5ClientAppBodies 208 168 117 152 = true := by decide

def falselyPreservedEndorsement : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with
    packageBytes := r5ClientAppDefaultNoPreserveUbBytes
    expectedFp16 := recomputeR6PayloadFp16 r5ClientAppCrateNameBytes
      r5ClientAppDefaultNoPreserveUbBytes }

theorem endorsement_accepts_unpreserved_payload :
    falselyPreservedEndorsement.preserveUb = true ∧
    falselyPreservedEndorsement.packageBytes.getD 6 0 = 9 ∧
    verifyPostRunEndorsedArtifact falselyPreservedEndorsement = true := by decide

theorem r7_and_r10_use_different_layouts :
    computeReprCStructAndSliceTailLayout packetWithTailHeaderFields 2 2 none 3 =
      some ([0, 4], 8, 14, 16, 4) ∧
    computeDstTotalSizeChecked r10PacketWithTailDstLayout 3 = some 20 := by decide

/-! ## 2. Paired Repaired Rejection & Consistency Theorems (`Q1`–`Q6`, `#93` §§6–11) -/

def checkPostAdmittedQ1 (post : List WireBody)
    (layout : BoundCompilerLayoutTable := statefulGenericLibLayoutTable) : Bool :=
  validateBuiltToPostCleanupAdmittedQ1 .strictPrefixTracePreserving
    statefulGenericLibExpectedCtx statefulGenericLibBuiltBindingRec
    (bindingForPostBodies post) statefulGenericLibCrateBytes
    x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
    realStatefulGenericLibBuiltAmirBytes (encodePostBodies post)
    layout x86_64LinuxTargetTripleBytes

theorem q1_repaired_admitted_validator_rejects_duplicate_symbols_and_mixed_phases :
    validateBuiltToPostCleanupAdmittedQ1 .strictPrefixTracePreserving
      statefulGenericLibExpectedCtx statefulGenericLibBuiltBindingRec
      statefulGenericLibBindingRec statefulGenericLibCrateBytes
      x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes realStatefulGenericLibAmirBytes
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = true ∧
    checkPostAdmittedQ1 duplicatedPost = false ∧
    checkPostAdmittedQ1 mixedPhasePost = false :=
  ⟨q1_admitted_validator_accepts_real_package, by decide, by decide⟩

theorem q2_repaired_full_range_layout_binding_rejects_aliased_65540_size :
    checkLayoutTableBindingFullRangeQ2 statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16 statefulGenericLibLayoutTable
      x86_64LinuxTargetTripleBytes = true ∧
    checkLayoutTableBindingFullRangeQ2 statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16 aliasedSizeLayout
      x86_64LinuxTargetTripleBytes = false ∧
    checkPostAdmittedQ1 rawPost aliasedSizeLayout = false := by
  decide

theorem q3_repaired_four_adt_witness_and_nominal_pair_challenge_verified :
    extractFourActualCrossCrateAdtTagsQ3 r5ClientAppBodies =
      some [.refMutEffectLog, .guard, .pairUsize, .optPairUsize] ∧
    hasDistinctFourActualCrossCrateAdtTagsQ3 r5ClientAppBodies = true ∧
    hasDistinctFourActualCrossCrateAdtTagsQ3 r5ControlCollapsedCrossCrateAdtBodies = false ∧
    checkNominalPairClientTypesQ3 q3NominalPairClientBodies = true ∧
    checkNominalPairClientTypesQ3 q3NominalPairClientSwappedSigBodies = false ∧
    evalNominalPairPipelineQ3 q3NominalPairClientBodies 100 5 = .returned (.scalar 146) ∧
    evalNominalPairPipelineQ3 q3NominalPairClientSwappedSigBodies 100 5 = .returned (.scalar 155) :=
  ⟨q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified.1,
   q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified.2.1,
   q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified.2.2.1,
   q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified.2.2.2.2.2.2.2.1,
   q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified.2.2.2.2.2.2.2.2.2.1,
   q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified.2.2.2.2.2.2.2.2.2.2.1,
   q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem q4_repaired_header_bound_endorsement_rejects_falsely_preserved_payload :
    verifyPostRunEndorsedArtifactBoundQ4 r6EndorsedClientAppRecord = true ∧
    verifyPostRunEndorsedArtifact falselyPreservedEndorsement = true ∧
    verifyPostRunEndorsedArtifactBoundQ4 falselyPreservedEndorsement = false := by
  decide

theorem q5_repaired_joined_r10_specimen_matches_independent_repr_c_law_for_all_n (n : Nat) :
    computeDstTotalSizeChecked r10PacketWithTailDstLayout n = some (8 + n * 4) ∧
    computeReprCStructAndSliceTailLayout r10PacketWithTailHeaderFieldsQ5 4 4 none n =
      some ([0, 4], 8, 8 + n * 4, 8 + n * 4, 4) :=
  ⟨q5_r10_captured_descriptor_universal_size_law n,
   q5_r10_packet_with_tail_repr_c_universal_law n⟩

theorem q6_repaired_charon_adapter_domain_rejects_ullbc_local_u64_mutation :
    verifyCharonNativeInspectorClosureQ6 charonNativeClientInspectorClosureAmirBytes = true ∧
    isAdmittedPackageBytes charonCtrl6LocalU64TypeMismatchAmirBytes = true ∧
    verifyCharonNativeInspectorClosureQ6 charonCtrl6LocalU64TypeMismatchAmirBytes = false :=
  ⟨q6_charon_adapter_domain_accepts_native_closure_and_rejects_local_u64_type_mismatch.1,
   q6_charon_adapter_domain_accepts_native_closure_and_rejects_local_u64_type_mismatch.2.1,
   q6_charon_adapter_domain_accepts_native_closure_and_rejects_local_u64_type_mismatch.2.2.2.2.2⟩

/-! ## 3. `Q9` (`#93` §14): Shape-Preserving Nominal-Return-Type-Swap Challenge -/

/-- Shape-preserving mutation of `q3NominalPairClientBytes` (`280` B): swaps ONLY the nominal
    return type tags (`7` `.effectLog` <-> `12` `.optUsize`) on `symId = 104` (`make_meter_reading`)
    and `symId = 162` (`make_limit_threshold`) while keeping the exact byte length (`280` B),
    body count (`4`), block counts (`[5, 2, 2, 3]`), and all statements/terminators identical. -/
def mutateSwapNominalReturnTypesQ9 (bodies : List WireBody) : List WireBody :=
  bodies.map (fun b =>
    if b.symId == 104 then
      match b.localTypes with
      | _ :: rest => { b with localTypes := .optUsize :: rest }
      | [] => b
    else if b.symId == 162 then
      match b.localTypes with
      | _ :: rest => { b with localTypes := .effectLog :: rest }
      | [] => b
    else b)

def q3NominalPairClientCrateNameBytes : List Nat :=
  [113, 51, 95, 110, 111, 109, 105, 110, 97, 108, 95, 112, 97, 105, 114, 95, 99, 108, 105, 101, 110, 116]

def q9ShapePreservingNominalReturnSwapBytes : List Nat :=
  let bodies := mutateSwapNominalReturnTypesQ9 q3NominalPairClientBodies
  let payload := specEncodeBodiesCons bodies
  let fp := computeCargoPayloadFp16 q3NominalPairClientCrateNameBytes payload
  [65, 77, 73, 82, 3, 3, 11, fp.1, fp.2, bodies.length] ++ payload

theorem q9_shape_preserving_nominal_return_swap_challenge :
    q9ShapePreservingNominalReturnSwapBytes.length = q3NominalPairClientBytes.length ∧
    q9ShapePreservingNominalReturnSwapBytes.length = 280 ∧
    isAdmittedPackageBytes q9ShapePreservingNominalReturnSwapBytes = true ∧
    (decodePackageBodies q9ShapePreservingNominalReturnSwapBytes).length = 4 ∧
    checkNominalPairClientTypesQ3 q3NominalPairClientBodies = true ∧
    checkNominalPairClientTypesQ3 (decodePackageBodies q9ShapePreservingNominalReturnSwapBytes) = false := by
  decide

#print axioms repaired_validator_accepts_duplicate_symbols
#print axioms repaired_validator_accepts_mixed_phases
#print axioms layout_binding_loses_high_size_bits
#print axioms four_adt_check_compares_reference_pointer_unit_and_one_adt
#print axioms endorsement_accepts_unpreserved_payload
#print axioms r7_and_r10_use_different_layouts
#print axioms q1_repaired_admitted_validator_rejects_duplicate_symbols_and_mixed_phases
#print axioms q2_repaired_full_range_layout_binding_rejects_aliased_65540_size
#print axioms q3_repaired_four_adt_witness_and_nominal_pair_challenge_verified
#print axioms q4_repaired_header_bound_endorsement_rejects_falsely_preserved_payload
#print axioms q5_repaired_joined_r10_specimen_matches_independent_repr_c_law_for_all_n
#print axioms q6_repaired_charon_adapter_domain_rejects_ullbc_local_u64_mutation
#print axioms q9_shape_preserving_nominal_return_swap_challenge

end AnnealResearch.PR92AuditCounterexamples
