/-
  Experiment: experiments/opsem/compiler-upgrade-and-agent-tasks
  Tasks FD-05 (Study P2 / Milestone R5) & FD-06 (Study P3) Controls:
  Negative Controls for Live Bounded Agent Tasks, `VarDebugInfo` Join,
  Weakening-Trap Rejection (Traps A, B, and C via Decoded-AST Execution & Gates),
  and Compiler Upgrade
-/

import AnnealResearch.AgentTasksAndCompilerUpgrade

set_option autoImplicit false
set_option maxRecDepth 65536

namespace AnnealResearch.AgentTasksAndUpgradeControls

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SubstantiveMirByteParserControls
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.SemanticVerticalSliceControls
open AnnealResearch.AgentTasksAndCompilerUpgrade

/-- Control 1: Anonymous `Runtime(PostCleanup)` MIR (without the `MirPhase::Built` +
    `VarDebugInfo` join sidecar) loses all named source variable bindings across Tasks A1..A4. -/
theorem control_anonymous_post_cleanup_loses_source_variable_localization :
    (metricsTaskA1 .directMirPostCleanupAnonymous).namedSourceVarsRecovered = 0 ∧
    (metricsTaskA2 .directMirPostCleanupAnonymous).namedSourceVarsRecovered = 0 ∧
    (metricsTaskA3 .directMirPostCleanupAnonymous).namedSourceVarsRecovered = 0 ∧
    (metricsTaskA4 .directMirPostCleanupAnonymous).namedSourceVarsRecovered = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Control 2: Hardcoding raw `Runtime(PostCleanup)` local indices (`_8` for `rem`, `_15` for `pad`,
    `_12` for `moved_first`) breaks under behavior-preserving refactors (`Task 3`), whereas
    `lookupLocalBySourceName` over the `VarDebugInfo` join table tracks the shifted indices. -/
theorem control_raw_local_index_invariants_break_under_behavior_preserving_refactor :
    lookupBindingByLocalIdx varDebugAlignToBaseline 8 = some (.uniqueUserVar "rem") ∧
    lookupBindingByLocalIdx varDebugAlignToRefactored 8 = some (.uniqueUserVar "aligned_rem") ∧
    lookupBindingByLocalIdx varDebugAlignToBaseline 8 ≠
      lookupBindingByLocalIdx varDebugAlignToRefactored 8 ∧
    lookupLocalBySourceName varDebugAlignToBaseline "pad" ≠
      lookupLocalBySourceName varDebugAlignToRefactored "pad" ∧
    lookupLocalBySourceName varDebugPartialInitMoveCleanup "moved_first" ≠
      lookupLocalBySourceName varDebugPartialInitMoveCleanupRefactored "moved_first" := by
  decide

/-- Control 3 (Trap A Negative Control — Tempting Postcondition Weakenings):
    1. Weakening `partial_field_reinit_cleanup` to accept `[10, 1, 2]` or `[10, 2, 3]`
       (`trapAWeakenedPartialReinitCheck`) or ignoring disjoint per-log residuals accepts
       `mutant3ReinitKeepField0DropBytes`, `mutant1SwapDropOrderBytes`, and `mutantWrongLogTargetBytes`,
       all of which are rejected by `checkPartialFieldReinitAgainstC0` / C0 disjoint-residual check.
    2. Weakening `DstLayout::extend` on slice DSTs to ignore `sizeInfo` (`trapAWeakenedExtendSliceCheck`)
       accepts the buggy `realTask2ExtendBuggyBytes` package, which is rejected by
       `checkExtendSuiteAgainstC0`. -/
theorem control_trap_a_weakened_extend_and_cleanup_contracts_unsound :
    trapAWeakenedPartialReinitCheck mutant1SwapDropOrderBytes false = true ∧
    trapAWeakenedPartialReinitCheck mutant3ReinitKeepField0DropBytes true = true ∧
    checkPartialFieldReinitAgainstC0 mutant1SwapDropOrderBytes false = false ∧
    checkPartialFieldReinitAgainstC0 mutant3ReinitKeepField0DropBytes true = false ∧
    evalPartialInitOnBytes mutantWrongLogTargetBytes false false ≠
      some (c0SpecPartialInit false false) ∧
    trapAWeakenedExtendSliceCheck realTask2ExtendBuggyBytes = true ∧
    checkExtendSuiteAgainstC0 realTask2ExtendBuggyBytes = false := by
  have hw : evalPartialInitOnBytes mutantWrongLogTargetBytes false false ≠
      some (c0SpecPartialInit false false) := by
    rw [mutant_wrong_log_target_accepted_and_falsifies_disjoint_residuals.2.1]
    decide
  exact ⟨task4_all_three_weakening_traps_rejected.1.1,
         task4_all_three_weakening_traps_rejected.1.2.1,
         task4_all_three_weakening_traps_rejected.1.2.2.1,
         task4_all_three_weakening_traps_rejected.1.2.2.2.1,
         hw,
         task4_all_three_weakening_traps_rejected.1.2.2.2.2.2.1,
         task4_all_three_weakening_traps_rejected.1.2.2.2.2.2.2.1⟩

/-- Control 4 (Trap B Negative Control — Dropping `-Z mir-preserve-ub`):
    Capturing `place_mention_probe.rs` without `-Z mir-preserve-ub` (`realPlaceMentionDefaultBytes`)
    is rejected at Boundary 3 (`checkEndorsedCompilationBinding` and `boundary3PreserveUbGate`) AND
    at Boundary 5 (`evalPlaceMentionOnBytes realPlaceMentionDefaultBytes 9 false = some (some 0)`
    instead of `some none`, failing `checkPlaceMentionSuiteAgainstC0`). -/
theorem control_trap_b_dropped_preserve_ub_rejected_at_boundary3_and_boundary5 :
    boundary3PreserveUbGate realPlaceMentionDefaultBytes = false ∧
    checkEndorsedCompilationBinding placeMentionPreserveUbEndorsedRecord
      placeMentionProbeCrateBytes 1002 1980 true 5002 realPlaceMentionDefaultBytes = false ∧
    evalPlaceMentionOnBytes realPlaceMentionDefaultBytes 9 false = some (some 0) ∧
    c0SpecPlaceMentionPreserveUb 9 false = none ∧
    checkPlaceMentionSuiteAgainstC0 realPlaceMentionDefaultBytes = false := by
  exact ⟨task4_all_three_weakening_traps_rejected.2.1.1,
         task4_all_three_weakening_traps_rejected.2.1.2.2.1,
         rfl,
         rfl,
         task4_all_three_weakening_traps_rejected.2.1.2.2.2.1⟩

/-- Control 5 (Trap C Negative Control — Unverified Charon Routes & Admissibility Widening):
    Claiming raw Charon ULLBC (`charonUllbcCleanupRawBytes`) or structured Charon LLBC
    (`charonLlbcCleanupRemedyR2Bytes`) satisfies C0 cleanup without passing `checkCleanupSuiteAgainstC0`
    fails under actual decoded-AST execution (`checkCleanupSuiteAgainstC0 = false`). -/
theorem control_trap_c_unverified_charon_routes_fail_c0_cleanup_gate :
    checkCleanupSuiteAgainstC0 charonUllbcCleanupRawBytes = false ∧
    checkCleanupSuiteAgainstC0 charonLlbcCleanupRemedyR2Bytes = false ∧
    checkCleanupSuiteAgainstC0 charonUllbcCleanupRemedyR2Bytes = true ∧
    (metricsTaskA4 .charonUllbcRaw).semanticallySoundForTask = false ∧
    (metricsTaskA4 .charonLlbcStructured).semanticallySoundForTask = false := by
  exact ⟨task4_all_three_weakening_traps_rejected.2.2.1,
         task4_all_three_weakening_traps_rejected.2.2.2.1,
         task4_all_three_weakening_traps_rejected.2.2.2.2.1,
         rfl,
         rfl⟩

/-- Control 6: `rustc_public` did not insulate against the `1.97 -> 1.98` `WithRetag` breakage. -/
theorem control_rustc_public_breaks_across_1_97_to_1_98_transition :
    (obsToolchain .nightly195_2026_02_06).unmodified198RustcPublicExitCode = 1 ∧
    (obsToolchain .nightly196_2026_04_10).unmodified198RustcPublicExitCode = 1 ∧
    (obsToolchain .nightly197_2026_04_11).unmodified198RustcPublicExitCode = 1 ∧
    (obsToolchain .nightly198_2026_05_30).unmodified198RustcPublicExitCode = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Structure-preserving semantic-drift negative control 1 (`R6`):
    `drift_control_alter_reinit_constant.amir` (`1,066` bytes,
    `sha256: 4f197602d4ecc80385c17ec0de70b9bc08b8606065c6ab159d771d416e6c93c9`),
    altering the reinitialized `Guard` drop tag in `partial_field_reinit_cleanup` (`sym = 5`)
    from `3` to `4` while preserving all symbol IDs, basic-block counts, statement counts,
    cleanup drop chains, and `PlaceMention` markers. -/
def driftControlAlterReinitConstantBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 43, 43, 9, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 3, 1, 3, 10, 2, 5, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 252, 131, 2, 0, 0, 74, 27, 7, 0, 255, 252, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 252, 73, 0, 129, 100, 0, 1, 33, 9, 64, 4, 4, 1, 3, 22, 4, 17, 3, 2, 2, 6, 6, 9, 8, 6, 8, 6, 1, 2, 8, 1, 6, 1, 8, 3, 2, 6, 2, 2, 0, 20, 17, 21, 0, 128, 0, 17, 20, 0, 128, 0, 32, 5, 32, 6, 32, 7, 19, 7, 0, 1, 3, 4, 25, 6, 0, 1, 129, 1, 71, 0, 33, 7, 32, 8, 32, 9, 19, 9, 0, 1, 4, 4, 25, 8, 0, 1, 129, 2, 73, 0, 33, 9, 17, 20, 0, 128, 1, 25, 5, 0, 2, 70, 0, 72, 0, 33, 8, 33, 6, 32, 10, 32, 11, 17, 11, 0, 1, 0, 69, 75, 0, 0, 4, 1, 0, 8, 32, 12, 17, 20, 0, 128, 0, 17, 21, 0, 128, 1, 17, 12, 0, 69, 1, 32, 13, 32, 14, 16, 19, 0, 12, 2, 19, 14, 0, 1, 19, 4, 75, 1, 13, 0, 2, 13, 78, 0, 129, 10, 0, 6, 33, 14, 33, 13, 32, 15, 32, 16, 17, 21, 0, 128, 0, 17, 16, 0, 76, 0, 74, 24, 15, 0, 3, 13, 80, 0, 0, 5, 33, 16, 33, 15, 17, 10, 0, 131, 0, 17, 21, 0, 128, 0, 33, 12, 68, 5, 0, 1, 17, 10, 0, 131, 0, 68, 5, 0, 5, 33, 11, 33, 10, 32, 17, 32, 18, 17, 18, 0, 2, 0, 75, 3, 17, 0, 6, 16, 82, 0, 129, 5, 0, 3, 33, 18, 17, 0, 0, 17, 0, 33, 17, 69, 20, 0, 0, 10, 11, 1, 0, 65, 0, 2, 17, 20, 0, 128, 0, 33, 5, 64, 1, 0, 71, 5, 2, 7, 7, 255, 0, 0, 71, 5, 2, 7, 8, 7, 0, 0, 71, 5, 1, 7, 10, 9, 1, 0, 71, 12, 0, 7, 16, 255, 1, 0, 69, 21, 0, 0, 16, 12, 1, 0, 71, 5, 2, 7, 7, 255, 1, 0, 71, 5, 1, 7, 14, 255, 1, 0, 69, 20, 0, 0, 14, 15, 5, 5, 1, 3, 24, 3, 9, 3, 2, 6, 6, 9, 8, 6, 8, 6, 8, 1, 6, 6, 1, 8, 3, 2, 8, 6, 6, 6, 6, 6, 2, 0, 22, 17, 23, 0, 128, 0, 32, 4, 32, 5, 32, 6, 19, 6, 0, 1, 2, 4, 25, 5, 0, 1, 129, 1, 70, 0, 33, 6, 32, 7, 32, 8, 19, 8, 0, 1, 3, 4, 25, 7, 0, 1, 129, 2, 72, 0, 33, 8, 25, 4, 0, 2, 69, 0, 71, 0, 33, 7, 33, 5, 32, 9, 17, 23, 0, 128, 1, 17, 9, 0, 68, 1, 32, 10, 32, 11, 16, 21, 0, 9, 2, 19, 11, 0, 1, 21, 4, 75, 1, 10, 0, 1, 8, 75, 0, 129, 10, 0, 9, 33, 11, 33, 10, 32, 12, 16, 22, 0, 9, 2, 19, 12, 0, 3, 22, 4, 32, 13, 32, 14, 17, 23, 0, 128, 0, 17, 14, 0, 73, 0, 74, 25, 13, 0, 2, 8, 78, 0, 0, 5, 33, 14, 33, 13, 32, 15, 32, 16, 17, 16, 0, 1, 0, 75, 3, 15, 0, 3, 8, 80, 0, 129, 7, 0, 19, 33, 16, 32, 17, 32, 18, 32, 19, 32, 20, 19, 20, 0, 1, 12, 4, 19, 19, 0, 1, 20, 4, 19, 18, 0, 1, 19, 4, 25, 17, 0, 1, 129, 4, 82, 0, 33, 18, 17, 4, 1, 81, 0, 33, 17, 33, 20, 33, 19, 17, 0, 0, 15, 0, 33, 15, 33, 12, 17, 23, 0, 128, 0, 33, 9, 71, 4, 0, 8, 4, 6, 0, 1, 33, 4, 64, 1, 0, 71, 4, 2, 7, 6, 255, 1, 0, 65, 1, 0, 71, 9, 0, 7, 5, 255, 1, 0, 69, 23, 0, 0, 5, 7, 6, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 8, 2, 4, 2, 1, 5, 1, 23, 0, 0, 71, 1, 5, 7, 4, 3, 1, 0, 65, 0, 0, 64, 1, 0, 71, 1, 6, 7, 1, 255, 0, 0, 71, 1, 6, 7, 2, 252, 9, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

/-- Structure-preserving semantic-drift negative control 2 (`R6`):
    `drift_control_swap_extend_slice_branch.amir` (`2,154` bytes,
    `sha256: 1e70c4241c8240d21d899587e63e787b627f66f2bce36694d56ffd41529a7b60`),
    swapping the `SwitchInt1` branch targets at `bb11` of `DstLayout::extend` (`sym = 12`)
    from `(false -> bb13, otherwise -> bb12)` to `(false -> bb12, otherwise -> bb13)`
    while preserving all symbol IDs, basic-block counts, statement counts, and local types. -/
def driftControlSwapExtendSliceBranchBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 115, 234, 10, 1, 15, 1, 3, 2, 1, 1, 10, 10, 0, 1, 17, 0, 0, 1, 4, 64, 2, 16, 1, 3, 11, 2, 7, 2, 10, 10, 2, 2, 2, 2, 4, 4, 4, 4, 0, 6, 32, 3, 32, 4, 17, 4, 0, 1, 7, 32, 5, 17, 5, 0, 2, 7, 21, 3, 0, 1, 68, 0, 69, 0, 69, 67, 0, 0, 4, 1, 0, 8, 33, 5, 33, 4, 32, 6, 32, 7, 17, 7, 0, 1, 5, 32, 8, 17, 8, 0, 2, 5, 21, 6, 0, 1, 71, 0, 72, 0, 69, 70, 0, 0, 3, 2, 0, 9, 33, 8, 33, 7, 32, 9, 17, 9, 0, 1, 6, 32, 10, 17, 10, 0, 2, 6, 21, 0, 0, 1, 73, 0, 74, 0, 33, 10, 33, 9, 68, 6, 0, 2, 33, 8, 33, 7, 68, 5, 0, 2, 33, 5, 33, 4, 68, 5, 0, 1, 17, 0, 0, 128, 0, 68, 6, 0, 2, 33, 6, 33, 3, 64, 3, 17, 1, 3, 2, 1, 1, 1, 10, 0, 1, 17, 0, 0, 131, 0, 64, 4, 18, 1, 3, 2, 1, 1, 11, 11, 0, 1, 17, 0, 0, 1, 4, 64, 5, 19, 1, 3, 3, 2, 1, 2, 11, 11, 0, 1, 17, 0, 0, 128, 1, 64, 6, 44, 1, 3, 2, 1, 1, 1, 11, 0, 1, 17, 0, 0, 131, 0, 64, 7, 11, 1, 3, 23, 2, 11, 14, 4, 4, 1, 2, 4, 19, 11, 4, 4, 4, 2, 2, 4, 4, 4, 4, 4, 16, 12, 4, 4, 11, 0, 5, 32, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 21, 4, 0, 1, 69, 0, 130, 0, 69, 68, 0, 0, 2, 1, 0, 7, 33, 5, 32, 7, 23, 7, 0, 1, 24, 0, 0, 2, 71, 0, 33, 7, 33, 4, 33, 3, 68, 10, 0, 10, 33, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 8, 32, 9, 17, 9, 0, 1, 0, 32, 10, 17, 10, 0, 2, 0, 21, 11, 0, 1, 10, 0, 130, 0, 72, 75, 0, 0, 3, 252, 0, 7, 21, 8, 0, 11, 73, 0, 74, 0, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 8, 0, 21, 12, 0, 1, 77, 0, 130, 0, 69, 76, 0, 0, 5, 4, 0, 5, 33, 13, 32, 14, 17, 14, 0, 1, 0, 24, 0, 0, 1, 78, 0, 33, 14, 68, 9, 0, 7, 33, 13, 32, 15, 32, 16, 17, 16, 0, 2, 0, 32, 17, 17, 17, 0, 8, 0, 21, 18, 0, 14, 16, 0, 17, 0, 72, 82, 2, 0, 6, 252, 0, 8, 17, 15, 0, 82, 1, 33, 17, 33, 16, 32, 19, 32, 20, 17, 20, 0, 1, 0, 32, 21, 17, 21, 0, 15, 0, 75, 23, 19, 0, 7, 252, 84, 0, 85, 0, 0, 4, 33, 21, 33, 20, 32, 22, 23, 22, 0, 1, 75, 28, 0, 0, 8, 252, 83, 0, 86, 0, 0, 3, 33, 22, 33, 19, 33, 15, 68, 9, 0, 2, 33, 12, 33, 8, 68, 10, 0, 0, 64, 8, 12, 1, 3, 40, 2, 23, 15, 10, 10, 1, 2, 19, 11, 4, 14, 14, 4, 4, 4, 14, 19, 14, 4, 4, 2, 4, 4, 4, 2, 14, 14, 12, 4, 4, 11, 4, 14, 19, 14, 4, 18, 10, 4, 4, 2, 4, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 3, 69, 68, 0, 0, 2, 1, 0, 6, 32, 6, 23, 6, 0, 1, 24, 0, 0, 2, 70, 0, 33, 6, 33, 4, 33, 3, 68, 22, 0, 10, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 7, 32, 8, 32, 9, 32, 10, 17, 10, 0, 1, 2, 32, 11, 17, 11, 0, 2, 1, 75, 11, 9, 0, 3, 252, 74, 0, 75, 0, 0, 2, 33, 11, 33, 10, 74, 29, 8, 0, 4, 252, 73, 0, 0, 3, 33, 9, 48, 8, 0, 20, 12, 0, 8, 0, 70, 76, 0, 0, 6, 1, 7, 5, 0, 0, 67, 0, 12, 32, 16, 17, 16, 0, 8, 8, 17, 7, 0, 16, 0, 33, 16, 33, 8, 32, 17, 32, 18, 32, 19, 17, 19, 0, 1, 1, 32, 20, 17, 20, 0, 2, 1, 21, 18, 0, 6, 83, 0, 84, 0, 69, 82, 0, 0, 10, 9, 0, 4, 32, 13, 17, 13, 0, 8, 9, 32, 15, 17, 15, 0, 13, 0, 74, 30, 0, 0, 8, 252, 79, 0, 0, 3, 33, 15, 33, 13, 33, 8, 68, 21, 0, 3, 33, 20, 33, 19, 17, 17, 0, 1, 1, 68, 11, 0, 3, 33, 20, 33, 19, 17, 17, 0, 2, 1, 68, 11, 0, 4, 33, 18, 32, 21, 32, 22, 17, 22, 0, 2, 3, 69, 86, 0, 0, 12, 13, 0, 1, 17, 21, 0, 7, 0, 68, 20, 0, 7, 32, 23, 32, 24, 32, 25, 32, 26, 17, 26, 0, 7, 0, 32, 27, 17, 27, 0, 2, 2, 75, 23, 25, 0, 14, 252, 90, 0, 91, 0, 0, 4, 33, 27, 33, 26, 32, 28, 23, 28, 0, 1, 75, 28, 24, 0, 15, 252, 89, 0, 92, 0, 0, 2, 33, 28, 33, 25, 74, 29, 23, 0, 16, 252, 88, 0, 0, 3, 33, 24, 48, 23, 0, 20, 29, 0, 23, 0, 70, 93, 0, 0, 17, 1, 18, 5, 0, 5, 32, 33, 17, 33, 0, 23, 8, 17, 21, 0, 33, 0, 33, 33, 33, 23, 68, 20, 0, 4, 32, 30, 17, 30, 0, 23, 9, 32, 32, 17, 32, 0, 30, 0, 74, 30, 0, 0, 19, 252, 96, 0, 0, 6, 33, 32, 33, 30, 33, 23, 33, 22, 33, 21, 33, 17, 68, 21, 0, 23, 33, 22, 32, 34, 32, 35, 32, 36, 17, 36, 0, 17, 0, 32, 37, 17, 37, 0, 21, 0, 32, 38, 17, 38, 0, 2, 3, 26, 35, 0, 1, 100, 0, 101, 0, 102, 0, 33, 38, 33, 37, 33, 36, 32, 39, 17, 39, 0, 7, 0, 25, 34, 0, 4, 99, 0, 103, 0, 33, 39, 33, 35, 24, 0, 0, 1, 98, 0, 33, 34, 33, 21, 33, 17, 33, 7, 68, 22, 0, 1, 33, 7, 68, 22, 0, 0, 64, 9, 13, 1, 3, 53, 4, 25, 13, 10, 4, 4, 4, 1, 2, 4, 2, 4, 4, 4, 2, 19, 2, 1, 2, 4, 4, 19, 17, 4, 4, 4, 16, 1, 2, 4, 4, 2, 4, 19, 4, 4, 4, 16, 4, 4, 4, 2, 4, 4, 4, 4, 4, 16, 16, 17, 4, 4, 4, 16, 4, 0, 5, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 1, 21, 6, 0, 1, 71, 0, 130, 0, 69, 70, 0, 0, 2, 1, 0, 1, 33, 7, 68, 5, 0, 8, 33, 7, 32, 8, 32, 9, 32, 10, 17, 10, 0, 2, 0, 32, 11, 17, 11, 0, 1, 1, 21, 12, 0, 1, 11, 0, 130, 0, 72, 76, 0, 0, 3, 252, 0, 4, 21, 9, 0, 11, 74, 0, 75, 0, 33, 11, 33, 10, 21, 8, 0, 2, 73, 0, 130, 0, 69, 72, 0, 0, 6, 4, 0, 1, 33, 9, 68, 5, 0, 4, 23, 0, 0, 2, 33, 8, 33, 6, 33, 5, 68, 24, 0, 7, 33, 9, 17, 5, 0, 131, 0, 33, 8, 33, 6, 33, 5, 32, 14, 17, 14, 0, 1, 3, 69, 78, 0, 0, 8, 7, 0, 7, 32, 25, 32, 26, 32, 27, 17, 27, 0, 3, 0, 32, 28, 17, 28, 0, 1, 2, 21, 26, 0, 3, 91, 0, 92, 0, 69, 90, 0, 0, 13, 12, 0, 7, 32, 15, 32, 16, 32, 17, 17, 17, 0, 3, 0, 32, 18, 17, 18, 0, 1, 2, 21, 16, 0, 3, 81, 0, 82, 0, 69, 80, 0, 0, 10, 9, 0, 5, 33, 18, 33, 17, 23, 0, 0, 2, 33, 16, 33, 15, 68, 23, 0, 12, 33, 18, 33, 17, 17, 15, 0, 131, 0, 33, 16, 33, 15, 32, 20, 32, 21, 32, 22, 17, 22, 0, 3, 0, 32, 23, 17, 23, 0, 1, 2, 21, 24, 0, 14, 22, 0, 23, 0, 72, 88, 2, 0, 11, 252, 0, 7, 17, 21, 0, 88, 1, 33, 23, 33, 22, 25, 20, 0, 4, 85, 0, 130, 1, 33, 21, 24, 0, 0, 1, 84, 0, 33, 20, 68, 22, 0, 2, 33, 28, 33, 27, 68, 16, 0, 6, 33, 28, 33, 27, 32, 29, 32, 30, 17, 30, 0, 4, 0, 21, 29, 0, 1, 94, 0, 130, 0, 69, 93, 0, 0, 15, 14, 0, 1, 33, 30, 68, 16, 0, 11, 33, 30, 17, 25, 0, 131, 0, 33, 29, 33, 26, 33, 25, 32, 32, 32, 33, 17, 33, 0, 3, 0, 32, 34, 17, 34, 0, 1, 2, 21, 35, 0, 14, 33, 0, 34, 0, 72, 99, 2, 0, 17, 252, 0, 4, 23, 0, 0, 2, 33, 29, 33, 26, 33, 25, 68, 23, 0, 9, 17, 32, 0, 99, 1, 33, 34, 33, 33, 32, 36, 32, 37, 17, 37, 0, 32, 0, 32, 38, 17, 38, 0, 4, 0, 21, 39, 0, 1, 38, 0, 130, 0, 72, 103, 0, 0, 18, 252, 0, 12, 21, 36, 0, 10, 101, 0, 102, 0, 33, 38, 33, 37, 32, 40, 32, 41, 17, 41, 0, 1, 2, 32, 42, 32, 43, 17, 43, 0, 36, 0, 32, 44, 17, 44, 0, 4, 0, 21, 45, 0, 15, 43, 0, 44, 0, 72, 109, 2, 0, 19, 252, 0, 4, 17, 42, 0, 109, 1, 33, 44, 33, 43, 21, 46, 0, 13, 41, 0, 42, 0, 72, 110, 2, 0, 20, 252, 0, 10, 17, 40, 0, 110, 1, 33, 42, 33, 41, 32, 47, 32, 48, 32, 49, 17, 49, 0, 3, 0, 32, 50, 17, 50, 0, 40, 0, 21, 51, 0, 14, 49, 0, 50, 0, 72, 115, 2, 0, 21, 252, 0, 13, 17, 48, 0, 115, 1, 33, 50, 33, 49, 32, 52, 17, 52, 0, 36, 0, 25, 47, 0, 4, 112, 0, 116, 0, 33, 52, 33, 48, 24, 0, 0, 1, 111, 0, 33, 47, 33, 40, 33, 36, 33, 32, 68, 22, 0, 1, 33, 14, 68, 24, 0, 1, 33, 14, 68, 24, 0, 0, 64, 10, 14, 1, 3, 31, 3, 14, 4, 4, 4, 4, 10, 4, 4, 1, 1, 2, 4, 4, 1, 2, 13, 13, 10, 4, 4, 4, 4, 1, 2, 4, 19, 4, 4, 4, 19, 1, 19, 0, 7, 32, 4, 26, 4, 0, 1, 130, 4, 130, 8, 128, 1, 32, 5, 17, 5, 0, 130, 8, 32, 6, 17, 6, 0, 130, 0, 32, 7, 68, 1, 0, 6, 32, 9, 32, 10, 17, 10, 0, 5, 0, 32, 11, 17, 11, 0, 2, 0, 21, 9, 0, 4, 74, 0, 75, 0, 69, 73, 0, 0, 12, 2, 0, 12, 33, 11, 33, 10, 32, 12, 32, 13, 32, 14, 32, 15, 32, 16, 17, 16, 0, 4, 0, 32, 17, 17, 17, 0, 1, 0, 32, 18, 17, 18, 0, 5, 0, 77, 13, 15, 0, 3, 252, 80, 0, 81, 0, 82, 0, 130, 4, 0, 4, 19, 14, 0, 0, 15, 0, 33, 18, 33, 17, 33, 16, 74, 31, 13, 0, 4, 252, 78, 0, 0, 0, 69, 77, 0, 0, 7, 5, 0, 5, 33, 15, 33, 14, 32, 19, 32, 20, 17, 20, 0, 6, 0, 75, 40, 19, 0, 6, 252, 84, 0, 130, 1, 0, 4, 33, 20, 17, 6, 0, 83, 0, 33, 19, 17, 12, 0, 131, 0, 68, 8, 0, 3, 33, 15, 33, 14, 17, 12, 0, 131, 0, 68, 8, 0, 7, 33, 13, 33, 12, 32, 21, 32, 22, 32, 23, 17, 23, 0, 3, 0, 21, 22, 0, 1, 87, 0, 130, 0, 69, 86, 0, 0, 10, 9, 0, 4, 33, 23, 17, 7, 0, 131, 0, 33, 22, 33, 21, 68, 13, 0, 9, 33, 23, 17, 21, 0, 131, 0, 33, 22, 33, 21, 32, 25, 32, 26, 17, 26, 0, 5, 0, 32, 27, 17, 27, 0, 3, 0, 75, 40, 25, 0, 11, 252, 90, 0, 91, 0, 0, 6, 33, 27, 33, 26, 17, 5, 0, 89, 0, 33, 25, 17, 8, 0, 131, 0, 33, 9, 68, 1, 0, 5, 33, 11, 33, 10, 32, 29, 17, 7, 0, 131, 0, 33, 29, 68, 13, 0, 6, 33, 9, 33, 7, 17, 0, 0, 6, 0, 33, 6, 33, 5, 33, 4, 64]

def evalSinglePartialFieldReinitFalseOnBytes (bytes : List Nat) : Option CleanupExecOutcome :=
  match parseRawPackageBytes bytes with
  | .ok (pkg, []) => some (evalPartialFieldReinitBodies pkg.bodies false)
  | _ => none

def evalSingleExtendSliceValidOnBytes (bytes : List Nat) : Option (Nat × Nat × Bool × Nat) :=
  match parseRawPackageBytes bytes with
  | .ok (pkg, []) => evalExtendBodies (pkg.bodies.drop 6) 4 6 false 4 4 true
  | _ => none

/-- Control 7 (R6 Structure-Preserving Semantic-Drift Controls):
    1. `driftControlAlterReinitConstantBytes` preserves the `24` blocks and `24` locals of `sym = 5`
       (`partial_field_reinit_cleanup`), yet decoded-AST execution on `trigger_panic = false`
       evaluates to `.normalReturn 108 (2, 164) (1, 2) [10, 4, 2]`, falsifying `c0SpecPartialFieldReinit false`.
    2. `driftControlSwapExtendSliceBranchBytes` preserves the `23` blocks and `40` locals of `sym = 12`
       (`DstLayout::extend`) while swapping `bb11` branch targets `(.switchInt1 ... 0 12 13)`, and
       decoded-AST execution on `extend({4, 6, false}, {4, 4, true})` evaluates to
       `some (4, 12, true, 8)`, falsifying `c0SpecExtend 4 6 false 4 4 true = some (4, 8, true, 8)`. -/
theorem control_r6_structure_preserving_drift_rejected_by_decoded_ast_c0_oracle :
    extractDecodedBlock driftControlSwapExtendSliceBranchBytes 12 11 =
      some { isCleanup := false
           , stmts := [ .storageDead 18
                      , .storageLive 21
                      , .storageLive 22
                      , .assignUseRetagYes { localIdx := 22, proj := .here } (.copy { localIdx := 2, proj := .field2 }) ]
           , term := .switchInt1 (.move { localIdx := 22, proj := .here }) 0 12 13 } ∧
    evalSinglePartialFieldReinitFalseOnBytes driftControlAlterReinitConstantBytes =
      some (.normalReturn 107 (2, 164) (1, 2) [10, 4, 2]) ∧
    c0SpecPartialFieldReinit false =
      .normalReturn 107 (2, 163) (1, 2) [10, 3, 2] ∧
    evalSingleExtendSliceValidOnBytes driftControlSwapExtendSliceBranchBytes =
      some (4, 12, true, 8) ∧
    c0SpecExtend 4 6 false 4 4 true =
      some (4, 8, true, 8) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms control_r6_structure_preserving_drift_rejected_by_decoded_ast_c0_oracle
#print axioms control_anonymous_post_cleanup_loses_source_variable_localization
#print axioms control_raw_local_index_invariants_break_under_behavior_preserving_refactor
#print axioms control_trap_a_weakened_extend_and_cleanup_contracts_unsound
#print axioms control_trap_b_dropped_preserve_ub_rejected_at_boundary3_and_boundary5
#print axioms control_trap_c_unverified_charon_routes_fail_c0_cleanup_gate
#print axioms control_rustc_public_breaks_across_1_97_to_1_98_transition

end AnnealResearch.AgentTasksAndUpgradeControls
