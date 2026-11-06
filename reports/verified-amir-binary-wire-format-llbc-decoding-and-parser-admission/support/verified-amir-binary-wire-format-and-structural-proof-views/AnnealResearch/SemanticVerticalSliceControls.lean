/-
  Experiment: experiments/opsem/semantic-vertical-slice
  Task FD-03 (FE-I1 & FE-I4) / Milestones C2 & C3 Negative Controls (Part 2 — Zerocopy, R4 Loop, & C3 LLBC):
  Behavior-Changing Semantic Mutations Inside the Supported Subset (`align_to` Wrong Rounding,
  `DstLayout::extend` Slice-Error Inversion, `R4` Unproductive `unbounded_period4_probe`
  Loop Mutation, and C3 Structured LLBC Unwind-Cleanup Falsification)
-/

import AnnealResearch.SemanticVerticalSliceControlsCleanup

set_option autoImplicit false
set_option maxRecDepth 65536

namespace AnnealResearch.SemanticVerticalSliceControls

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice

/-! ## Mutant 5: Wrong Rounding Arithmetic (`add` vs `sub`) in `align_to` -/

def mutant5AlignToWrongRoundBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 227, 80, 2, 1, 11, 1, 3, 23, 2, 11, 14, 4, 4, 1, 2, 4, 19, 11, 4, 4, 4, 2, 2, 4, 4, 4, 4, 4, 16, 12, 4, 4, 11, 0, 5, 32, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 21, 4, 0, 1, 69, 0, 130, 0, 69, 68, 0, 0, 2, 1, 0, 7, 33, 5, 32, 7, 23, 7, 0, 1, 24, 0, 0, 2, 71, 0, 33, 7, 33, 4, 33, 3, 68, 10, 0, 10, 33, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 8, 32, 9, 17, 9, 0, 1, 0, 32, 10, 17, 10, 0, 2, 0, 21, 11, 0, 1, 10, 0, 130, 0, 72, 75, 0, 0, 3, 252, 0, 7, 21, 8, 0, 11, 73, 0, 74, 0, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 8, 0, 21, 12, 0, 1, 77, 0, 130, 0, 69, 76, 0, 0, 5, 4, 0, 5, 33, 13, 32, 14, 17, 14, 0, 1, 0, 24, 0, 0, 1, 78, 0, 33, 14, 68, 9, 0, 7, 33, 13, 32, 15, 32, 16, 17, 16, 0, 2, 0, 32, 17, 17, 17, 0, 8, 0, 21, 18, 0, 13, 16, 0, 17, 0, 72, 82, 2, 0, 6, 252, 0, 8, 17, 15, 0, 82, 1, 33, 17, 33, 16, 32, 19, 32, 20, 17, 20, 0, 1, 0, 32, 21, 17, 21, 0, 15, 0, 75, 23, 19, 0, 7, 252, 84, 0, 85, 0, 0, 4, 33, 21, 33, 20, 32, 22, 23, 22, 0, 1, 75, 28, 0, 0, 8, 252, 83, 0, 86, 0, 0, 3, 33, 22, 33, 19, 33, 15, 68, 9, 0, 2, 33, 12, 33, 8, 68, 10, 0, 0, 64, 2, 12, 1, 3, 40, 2, 23, 15, 10, 10, 1, 2, 19, 11, 4, 14, 14, 4, 4, 4, 14, 19, 14, 4, 4, 2, 4, 4, 4, 2, 14, 14, 12, 4, 4, 11, 4, 14, 19, 14, 4, 18, 10, 4, 4, 2, 4, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 3, 69, 68, 0, 0, 2, 1, 0, 6, 32, 6, 23, 6, 0, 1, 24, 0, 0, 2, 70, 0, 33, 6, 33, 4, 33, 3, 68, 22, 0, 10, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 7, 32, 8, 32, 9, 32, 10, 17, 10, 0, 1, 2, 32, 11, 17, 11, 0, 2, 1, 75, 11, 9, 0, 3, 252, 74, 0, 75, 0, 0, 2, 33, 11, 33, 10, 74, 29, 8, 0, 4, 252, 73, 0, 0, 3, 33, 9, 48, 8, 0, 20, 12, 0, 8, 0, 70, 76, 0, 0, 6, 1, 7, 5, 0, 0, 67, 0, 12, 32, 16, 17, 16, 0, 8, 8, 17, 7, 0, 16, 0, 33, 16, 33, 8, 32, 17, 32, 18, 32, 19, 17, 19, 0, 1, 1, 32, 20, 17, 20, 0, 2, 1, 21, 18, 0, 6, 83, 0, 84, 0, 69, 82, 0, 0, 10, 9, 0, 4, 32, 13, 17, 13, 0, 8, 9, 32, 15, 17, 15, 0, 13, 0, 74, 30, 0, 0, 8, 252, 79, 0, 0, 3, 33, 15, 33, 13, 33, 8, 68, 21, 0, 3, 33, 20, 33, 19, 17, 17, 0, 1, 1, 68, 11, 0, 3, 33, 20, 33, 19, 17, 17, 0, 2, 1, 68, 11, 0, 4, 33, 18, 32, 21, 32, 22, 17, 22, 0, 2, 3, 69, 86, 0, 0, 13, 12, 0, 1, 17, 21, 0, 7, 0, 68, 20, 0, 7, 32, 23, 32, 24, 32, 25, 32, 26, 17, 26, 0, 7, 0, 32, 27, 17, 27, 0, 2, 2, 75, 23, 25, 0, 14, 252, 90, 0, 91, 0, 0, 4, 33, 27, 33, 26, 32, 28, 23, 28, 0, 1, 75, 28, 24, 0, 15, 252, 89, 0, 92, 0, 0, 2, 33, 28, 33, 25, 74, 29, 23, 0, 16, 252, 88, 0, 0, 3, 33, 24, 48, 23, 0, 20, 29, 0, 23, 0, 70, 93, 0, 0, 17, 1, 18, 5, 0, 5, 32, 33, 17, 33, 0, 23, 8, 17, 21, 0, 33, 0, 33, 33, 33, 23, 68, 20, 0, 4, 32, 30, 17, 30, 0, 23, 9, 32, 32, 17, 32, 0, 30, 0, 74, 30, 0, 0, 19, 252, 96, 0, 0, 6, 33, 32, 33, 30, 33, 23, 33, 22, 33, 21, 33, 17, 68, 21, 0, 23, 33, 22, 32, 34, 32, 35, 32, 36, 17, 36, 0, 17, 0, 32, 37, 17, 37, 0, 21, 0, 32, 38, 17, 38, 0, 2, 3, 26, 35, 0, 1, 100, 0, 101, 0, 102, 0, 33, 38, 33, 37, 33, 36, 32, 39, 17, 39, 0, 7, 0, 25, 34, 0, 4, 99, 0, 103, 0, 33, 39, 33, 35, 24, 0, 0, 1, 98, 0, 33, 34, 33, 21, 33, 17, 33, 7, 68, 22, 0, 1, 33, 7, 68, 22, 0, 0, 64]

theorem mutant5_accepted_by_byte_parser_and_falsifies_c0_align_to :
    isAcceptedWirePackage mutant5AlignToWrongRoundBytes = true ∧
    evalAlignToOnBytes mutant5AlignToWrongRoundBytes 13 4 = some (some 18) ∧
    c0SpecAlignTo 13 4 = some 16 := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Mutant 6: Inverted `self.is_slice_dst` Guard in `DstLayout::extend` -/

def mutant6ExtendSkipSliceErrBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 227, 80, 2, 1, 11, 1, 3, 23, 2, 11, 14, 4, 4, 1, 2, 4, 19, 11, 4, 4, 4, 2, 2, 4, 4, 4, 4, 4, 16, 12, 4, 4, 11, 0, 5, 32, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 21, 4, 0, 1, 69, 0, 130, 0, 69, 68, 0, 0, 2, 1, 0, 7, 33, 5, 32, 7, 23, 7, 0, 1, 24, 0, 0, 2, 71, 0, 33, 7, 33, 4, 33, 3, 68, 10, 0, 10, 33, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 8, 32, 9, 17, 9, 0, 1, 0, 32, 10, 17, 10, 0, 2, 0, 21, 11, 0, 1, 10, 0, 130, 0, 72, 75, 0, 0, 3, 252, 0, 7, 21, 8, 0, 11, 73, 0, 74, 0, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 8, 0, 21, 12, 0, 1, 77, 0, 130, 0, 69, 76, 0, 0, 5, 4, 0, 5, 33, 13, 32, 14, 17, 14, 0, 1, 0, 24, 0, 0, 1, 78, 0, 33, 14, 68, 9, 0, 7, 33, 13, 32, 15, 32, 16, 17, 16, 0, 2, 0, 32, 17, 17, 17, 0, 8, 0, 21, 18, 0, 14, 16, 0, 17, 0, 72, 82, 2, 0, 6, 252, 0, 8, 17, 15, 0, 82, 1, 33, 17, 33, 16, 32, 19, 32, 20, 17, 20, 0, 1, 0, 32, 21, 17, 21, 0, 15, 0, 75, 23, 19, 0, 7, 252, 84, 0, 85, 0, 0, 4, 33, 21, 33, 20, 32, 22, 23, 22, 0, 1, 75, 28, 0, 0, 8, 252, 83, 0, 86, 0, 0, 3, 33, 22, 33, 19, 33, 15, 68, 9, 0, 2, 33, 12, 33, 8, 68, 10, 0, 0, 64, 2, 12, 1, 3, 40, 2, 23, 15, 10, 10, 1, 2, 19, 11, 4, 14, 14, 4, 4, 4, 14, 19, 14, 4, 4, 2, 4, 4, 4, 2, 14, 14, 12, 4, 4, 11, 4, 14, 19, 14, 4, 18, 10, 4, 4, 2, 4, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 3, 69, 68, 0, 0, 1, 2, 0, 6, 32, 6, 23, 6, 0, 1, 24, 0, 0, 2, 70, 0, 33, 6, 33, 4, 33, 3, 68, 22, 0, 10, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 7, 32, 8, 32, 9, 32, 10, 17, 10, 0, 1, 2, 32, 11, 17, 11, 0, 2, 1, 75, 11, 9, 0, 3, 252, 74, 0, 75, 0, 0, 2, 33, 11, 33, 10, 74, 29, 8, 0, 4, 252, 73, 0, 0, 3, 33, 9, 48, 8, 0, 20, 12, 0, 8, 0, 70, 76, 0, 0, 6, 1, 7, 5, 0, 0, 67, 0, 12, 32, 16, 17, 16, 0, 8, 8, 17, 7, 0, 16, 0, 33, 16, 33, 8, 32, 17, 32, 18, 32, 19, 17, 19, 0, 1, 1, 32, 20, 17, 20, 0, 2, 1, 21, 18, 0, 6, 83, 0, 84, 0, 69, 82, 0, 0, 10, 9, 0, 4, 32, 13, 17, 13, 0, 8, 9, 32, 15, 17, 15, 0, 13, 0, 74, 30, 0, 0, 8, 252, 79, 0, 0, 3, 33, 15, 33, 13, 33, 8, 68, 21, 0, 3, 33, 20, 33, 19, 17, 17, 0, 1, 1, 68, 11, 0, 3, 33, 20, 33, 19, 17, 17, 0, 2, 1, 68, 11, 0, 4, 33, 18, 32, 21, 32, 22, 17, 22, 0, 2, 3, 69, 86, 0, 0, 13, 12, 0, 1, 17, 21, 0, 7, 0, 68, 20, 0, 7, 32, 23, 32, 24, 32, 25, 32, 26, 17, 26, 0, 7, 0, 32, 27, 17, 27, 0, 2, 2, 75, 23, 25, 0, 14, 252, 90, 0, 91, 0, 0, 4, 33, 27, 33, 26, 32, 28, 23, 28, 0, 1, 75, 28, 24, 0, 15, 252, 89, 0, 92, 0, 0, 2, 33, 28, 33, 25, 74, 29, 23, 0, 16, 252, 88, 0, 0, 3, 33, 24, 48, 23, 0, 20, 29, 0, 23, 0, 70, 93, 0, 0, 17, 1, 18, 5, 0, 5, 32, 33, 17, 33, 0, 23, 8, 17, 21, 0, 33, 0, 33, 33, 33, 23, 68, 20, 0, 4, 32, 30, 17, 30, 0, 23, 9, 32, 32, 17, 32, 0, 30, 0, 74, 30, 0, 0, 19, 252, 96, 0, 0, 6, 33, 32, 33, 30, 33, 23, 33, 22, 33, 21, 33, 17, 68, 21, 0, 23, 33, 22, 32, 34, 32, 35, 32, 36, 17, 36, 0, 17, 0, 32, 37, 17, 37, 0, 21, 0, 32, 38, 17, 38, 0, 2, 3, 26, 35, 0, 1, 100, 0, 101, 0, 102, 0, 33, 38, 33, 37, 33, 36, 32, 39, 17, 39, 0, 7, 0, 25, 34, 0, 4, 99, 0, 103, 0, 33, 39, 33, 35, 24, 0, 0, 1, 98, 0, 33, 34, 33, 21, 33, 17, 33, 7, 68, 22, 0, 1, 33, 7, 68, 22, 0, 0, 64]

theorem mutant6_accepted_by_byte_parser_and_falsifies_c0_extend :
    isAcceptedWirePackage mutant6ExtendSkipSliceErrBytes = true ∧
    evalExtendOnBytes mutant6ExtendSkipSliceErrBytes 4 8 true 4 4 false =
      some (some (4, 12, false, 8)) ∧
    c0SpecExtend 4 8 true 4 4 false = none := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Mutant 7 (`R4` Loop Control): Unproductive `ticks.wrapping_add(0)` in `unbounded_period4_probe` Falsifies Period-4 Loop Progression -/

def mutant7UnproductiveLoopBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 13, 126, 1, 1, 43, 1, 3, 22, 4, 9, 3, 5, 2, 4, 4, 1, 2, 4, 3, 1, 1, 2, 4, 4, 4, 4, 4, 3, 3, 19, 1, 19, 0, 3, 32, 5, 32, 6, 17, 6, 0, 2, 0, 69, 70, 0, 0, 2, 1, 0, 2, 48, 1, 4, 17, 5, 0, 131, 0, 68, 3, 0, 1, 17, 5, 0, 131, 0, 68, 3, 0, 7, 33, 6, 33, 5, 32, 7, 17, 7, 0, 130, 0, 32, 8, 17, 8, 0, 129, 0, 32, 9, 68, 4, 0, 6, 32, 11, 32, 12, 17, 12, 0, 7, 0, 32, 13, 17, 13, 0, 3, 0, 21, 11, 0, 2, 76, 0, 77, 0, 69, 75, 0, 0, 8, 5, 0, 7, 33, 13, 33, 12, 32, 14, 32, 15, 17, 15, 0, 7, 0, 32, 16, 17, 16, 0, 4, 0, 75, 40, 14, 0, 6, 252, 79, 0, 80, 0, 0, 7, 33, 16, 33, 15, 17, 7, 0, 78, 0, 33, 14, 32, 17, 32, 18, 17, 18, 0, 8, 0, 75, 20, 17, 0, 7, 252, 82, 0, 129, 0, 0, 5, 33, 18, 21, 8, 0, 12, 81, 0, 129, 3, 33, 17, 17, 10, 0, 131, 0, 33, 11, 68, 4, 0, 10, 33, 13, 33, 12, 32, 20, 17, 9, 0, 131, 0, 33, 20, 33, 11, 33, 9, 17, 0, 0, 8, 0, 33, 8, 33, 7, 64]

def checkPeriod4LoopProductiveOnBytes (bytes : List Nat) : Bool :=
  match parseAdmittedRawPackageBytes bytes with
  | some pkg =>
      let bodies := pkg.bodies
      let st7 := runSteps bodies 7 (initEntryState bodies 43 [.extPtr true, .scalar 0, .scalar 8, .scalar 0])
      decide (readLoopPeriod4Ticks st7 = some 1)
  | none => false

theorem mutant7_accepted_by_byte_parser_and_fails_productive_step_relation :
    isAcceptedWirePackage mutant7UnproductiveLoopBytes = true ∧
    checkPeriod4LoopProductiveOnBytes realLoopPrefixProbePreserveUbBytes = true ∧
    checkPeriod4LoopProductiveOnBytes mutant7UnproductiveLoopBytes = false := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## C3 Negative Control: Structured LLBC Falsifies C0 Unwind-Cleanup Specification -/

theorem charon_llbc_falsifies_c0_unwind_cleanup_spec :
    isAcceptedWirePackage charonLlbcCleanupRemedyR2Bytes = true ∧
    evalPartialInitOnBytes charonLlbcCleanupRemedyR2Bytes false true =
      some (.unwoundWithCleanup (0, 0) (0, 0) []) ∧
    c0SpecPartialInit false true = .unwoundWithCleanup (1, 1) (1, 2) [1, 2] := by
  refine ⟨rfl, rfl, rfl⟩

#print axioms mutant5_accepted_by_byte_parser_and_falsifies_c0_align_to
#print axioms mutant6_accepted_by_byte_parser_and_falsifies_c0_extend
#print axioms mutant7_accepted_by_byte_parser_and_fails_productive_step_relation
#print axioms charon_llbc_falsifies_c0_unwind_cleanup_spec

end AnnealResearch.SemanticVerticalSliceControls
