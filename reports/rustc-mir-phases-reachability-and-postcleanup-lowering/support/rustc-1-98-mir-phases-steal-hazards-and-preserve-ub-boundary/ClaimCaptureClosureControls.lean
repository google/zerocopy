/-
  Experiment: experiments/opsem/claim-capture-closure
  Task FD-01 Controls: Negative and Calibration Controls for Claim-to-Capture Closure
-/

import AnnealResearch.ClaimCaptureClosure

set_option autoImplicit false

namespace AnnealResearch.ClaimCaptureClosureControls

open AnnealResearch.ClaimCaptureClosure

/-- Negative Control 1: Attempting to capture all 8 claim families using only
    `after_analysis` without `hook_mir_built` (`LocalInfo`), `hook_mir_drops_elaborated`
    (pre-`StateTransform` coroutine elaborated MIR), or `-Z mir-preserve-ub`
    fails on `validityAndUnusedLoad`, `asyncCoroutineStateMachine`, and `LocalInfo`. -/
def unhookedAfterAnalysisDefaultCapability : CaptureCapability :=
  { route := .directMirDriverV3
  , preservesStorageLiveness := true
  , preservesPlaceMentionDerefs := false
  , preservesRetagOperands := true
  , preservesExplicitDropGlue := true
  , preservesUnwindCleanupGraph := true
  , capturesBuiltLocalInfo := false
  , capturesMonoCollectorGraph := true
  , capturesPreStateTransformAsync := false }

theorem control_unhooked_after_analysis_default_insufficient :
    unhookedAfterAnalysisDefaultCapability.preservesPlaceMentionDerefs = false ∧
    unhookedAfterAnalysisDefaultCapability.capturesBuiltLocalInfo = false ∧
    unhookedAfterAnalysisDefaultCapability.capturesPreStateTransformAsync = false ∧
    ladderAsyncCoroutineClosure.directCapturedAtAfterAnalysisElab = false := by
  decide

/-- Negative Control 2: Claiming that `rustc_public` under default flags suffices
    for storage-liveness (`StorageLive`/`StorageDead`) or raw-pointer validity
    probes (`ub_boundary_probe`) is refuted by `rustc_public_cleanup_default.json`. -/
theorem control_rustc_public_default_insufficient_for_ub_and_liveness :
    routeSupportsClaim .rustcPublicDefault .validityAndUnusedLoad = false ∧
    routeSupportsClaim .rustcPublicDefault .aliasingAndRetagSensitivity = false ∧
    rpPartialInitDefault.storageLive = 0 ∧
    rpUbProbeDefault.blocks = 1 ∧
    rpUbProbeDefault.useRetagYes = 1 := by
  decide

/-- Negative Control 3: Claiming that `let _ = unsafe { *ptr };` (`ub_boundary_probe`)
    has the same `Runtime(PostCleanup)` default behavior as `match *ptr { _ => 0 }`
    (`match_wildcard_probe`) or `_ = *ptr;` (`assign_underscore_probe`) is refuted
    by `bodies_place_mention_default.json`. -/
theorem control_conflating_let_underscore_with_match_wildcard_refuted :
    obsUbBoundaryPostCleanupDefault.hasDerefCopyAssign = true ∧
    obsMatchWildcardPostCleanupDefault.hasDerefCopyAssign = false ∧
    obsAssignUnderscorePostCleanupDefault.hasDerefCopyAssign = false ∧
    bodyRetainsPointerCheck obsUbBoundaryPostCleanupDefault ≠
      bodyRetainsPointerCheck obsMatchWildcardPostCleanupDefault := by
  decide

#print axioms control_unhooked_after_analysis_default_insufficient
#print axioms control_rustc_public_default_insufficient_for_ub_and_liveness
#print axioms control_conflating_let_underscore_with_match_wildcard_refuted

end AnnealResearch.ClaimCaptureClosureControls
