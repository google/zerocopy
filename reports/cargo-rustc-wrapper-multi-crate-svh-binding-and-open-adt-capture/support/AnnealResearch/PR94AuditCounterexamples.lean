import AnnealResearch.PR92AuditCounterexamples

set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.PR94AuditCounterexamples

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.CargoWorkspaceIntegrationControls
open AnnealResearch.PR86AuditRepairs
open AnnealResearch.CharonNativeAndControlsR3R4
open AnnealResearch.OpenHashMultiCrateR5R6R9R10
open AnnealResearch.PR92AuditCounterexamples

/-!
# `C0`–`C3`: Verbatim `#95` Companion Counterexamples Against `PR #94` (`35bd34b`) and Paired `C2` Closeout Repairs (`D1`–`D4`)

1. **Section 1 (`C0`, `#95#issuecomment-6250515087` §§C–D):** Reproduces both verbatim `Audit94`
   counterexample theorems (`endorsement_still_accepts_inconsistent_header_fingerprint` and
   `charon_gate_accepts_unchecked_local_type_change`) against the preserved `PR #94`
   (`35bd34bf1fcd1fd77a3b996d7dbf3773d6aa6318`) definitions (`verifyPostRunEndorsedArtifactBoundQ4`
   and `verifyCharonNativeInspectorClosureQ6`).
2. **Section 2 (`C2`, `#95` §§5–6 `D1`–`D4`):** Proves the paired repaired rejection and
   table/layout-binding theorems on `verifyPostRunEndorsedArtifactHeaderConsistentC2`,
   `verifyCharonNativeInspectorClosureCompleteC2`, `checkNominalPairClientBoundToOpenAdtTableC2`,
   and `checkCapturedSliceTailDstLayoutAgainstReprCC2`.
-/

/-! ## 1. Verbatim `#95` Companion Counterexamples Against Historical `35bd34b` Definitions (`D2` & `D4`) -/

def uncheckedLocalMutantBytes : List Nat :=
  charonCtrl7UncheckedLocalMutantAmirBytes

theorem endorsement_still_accepts_inconsistent_header_fingerprint :
    mismatchedHeaderQ4.packageBytes.getD 7 0 = 0 ∧
    mismatchedHeaderQ4.packageBytes.getD 8 0 = 0 ∧
    mismatchedHeaderQ4.expectedFp16 = (45, 98) ∧
    verifyPostRunEndorsedArtifactBoundQ4 mismatchedHeaderQ4 = true := by decide

theorem charon_gate_accepts_unchecked_local_type_change :
    uncheckedLocalMutantBytes ≠ charonNativeClientInspectorClosureAmirBytes ∧
    isAdmittedPackageBytes uncheckedLocalMutantBytes = true ∧
    verifyCharonNativeInspectorClosureQ6 uncheckedLocalMutantBytes = true := by decide

/-! ## 2. Paired `C2` Closeout Repairs (`D1`–`D4`, `#95` §§5–6) -/

theorem c2_repaired_endorsement_rejects_inconsistent_header_fingerprint :
    verifyPostRunEndorsedArtifactHeaderConsistentC2 r6EndorsedClientAppRecord = true ∧
    verifyPostRunEndorsedArtifactBoundQ4 mismatchedHeaderQ4 = true ∧
    verifyPostRunEndorsedArtifactHeaderConsistentC2 mismatchedHeaderQ4 = false :=
  ⟨c2_d2_header_consistent_endorsement_rejects_mismatched_header_q4.1,
   c2_d2_header_consistent_endorsement_rejects_mismatched_header_q4.2.1,
   c2_d2_header_consistent_endorsement_rejects_mismatched_header_q4.2.2.1⟩

theorem c2_repaired_complete_charon_gate_rejects_unchecked_local_type_change :
    verifyCharonNativeInspectorClosureCompleteC2 charonNativeClientInspectorClosureAmirBytes = true ∧
    verifyCharonNativeInspectorClosureQ6 uncheckedLocalMutantBytes = true ∧
    verifyCharonNativeInspectorClosureCompleteC2 uncheckedLocalMutantBytes = false ∧
    verifyCharonNativeInspectorClosureCompleteC2 charonCtrl6LocalU64TypeMismatchAmirBytes = false :=
  ⟨c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant.1,
   c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant.2.2.2.2.1,
   c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant.2.2.2.2.2.2,
   c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant.2.2.2.2.2.1⟩

theorem c2_repaired_nominal_open_adt_table_join_and_table_substitutions :
    checkNominalPairClientBoundToOpenAdtTableC2 q3BaselineOpenAdtTableC2 q3NominalPairClientBodies = true ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3BaselineOpenAdtTableC2 q3NominalPairClientRefactoredBodies = true ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3SwappedSigOpenAdtTableC2 q3NominalPairClientSwappedSigBodies = true ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3SwappedSigOpenAdtTableC2 q3NominalPairClientBodies = false ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3BaselineOpenAdtTableC2 q3NominalPairClientSwappedSigBodies = false ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3BaselineOpenAdtTableC2
      (decodePackageBodies q9ShapePreservingNominalReturnSwapBytes) = false := by
  decide

theorem c2_repaired_captured_layout_to_repr_c_recurrence_rejects_tail_and_context_mutations :
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 x86_64LinuxTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 r10PacketWithTailDstLayout = true ∧
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 x86_64LinuxTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 mutatedTailOffsetDstLayoutC2 = false ∧
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 x86_64LinuxTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 mutatedTailElemLayoutC2 = false ∧
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 mutatedTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 r10PacketWithTailDstLayout = false :=
  c2_d3_captured_layout_to_repr_c_recurrence_and_mutations_verified

theorem c2_repaired_captured_layout_to_repr_c_universal_law_joined (n : Nat) :
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 x86_64LinuxTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 r10PacketWithTailDstLayout = true ∧
    computeDstTotalSizeChecked r10PacketWithTailDstLayout n = some (8 + n * 4) ∧
    computeReprCStructAndSliceTailLayout r10PacketWithTailHeaderFieldsQ5 4 4 none n =
      some ([0, 4], 8, 8 + n * 4, 8 + n * 4, 4) :=
  ⟨c2_d3_captured_layout_to_repr_c_recurrence_and_mutations_verified.1,
   q5_r10_captured_descriptor_universal_size_law n,
   q5_r10_packet_with_tail_repr_c_universal_law n⟩

#print axioms endorsement_still_accepts_inconsistent_header_fingerprint
#print axioms charon_gate_accepts_unchecked_local_type_change
#print axioms c2_repaired_endorsement_rejects_inconsistent_header_fingerprint
#print axioms c2_repaired_complete_charon_gate_rejects_unchecked_local_type_change
#print axioms c2_repaired_nominal_open_adt_table_join_and_table_substitutions
#print axioms c2_repaired_captured_layout_to_repr_c_recurrence_rejects_tail_and_context_mutations
#print axioms c2_repaired_captured_layout_to_repr_c_universal_law_joined

end AnnealResearch.PR94AuditCounterexamples
