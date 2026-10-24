import AnnealResearch.SemanticVerticalSliceCore

set_option autoImplicit false
set_option maxRecDepth 65536

namespace AnnealResearch.SemanticVerticalSlice

open AnnealResearch.SubstantiveMirByteParser

/-! ## C2 Theorem 3: Decoded-AST Execution Satisfies Frozen C0 `zerocopy` Holdout Endpoint -/

theorem direct_mir_zerocopy_align_extend_satisfies_c0 :
    evalZerocopyAlignExtendOnBytes realZerocopyLayoutHoldoutBytes =
      some c0SpecZerocopyAlignExtendSuite := by
  rfl

theorem direct_mir_zerocopy_validate_count_satisfies_c0 :
    evalZerocopyValidateCountOnBytes realZerocopyLayoutHoldoutBytes =
      some c0SpecZerocopyValidateCountSuite := by
  rfl

theorem direct_mir_zerocopy_suite_satisfies_c0_all_cases :
    isAdmittedPackageBytes realZerocopyLayoutHoldoutBytes = true ∧
    evalZerocopyAlignExtendOnBytes realZerocopyLayoutHoldoutBytes =
      some c0SpecZerocopyAlignExtendSuite ∧
    evalZerocopyValidateCountOnBytes realZerocopyLayoutHoldoutBytes =
      some c0SpecZerocopyValidateCountSuite := by
  exact ⟨real_zerocopy_layout_holdout_bytes_accepted_without_block_truncation.2,
         direct_mir_zerocopy_align_extend_satisfies_c0,
         direct_mir_zerocopy_validate_count_satisfies_c0⟩

#print axioms direct_mir_zerocopy_align_extend_satisfies_c0
#print axioms direct_mir_zerocopy_validate_count_satisfies_c0
#print axioms direct_mir_zerocopy_suite_satisfies_c0_all_cases

end AnnealResearch.SemanticVerticalSlice
