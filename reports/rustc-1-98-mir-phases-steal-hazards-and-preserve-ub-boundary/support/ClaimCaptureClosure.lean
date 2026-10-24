/-
  Experiment: experiments/opsem/claim-capture-closure
  Task FD-01 / Milestone C1 & P5: Claim-to-Capture Closure, Feature Ladder,
  and rustc_public Comparison (`.amir` v3 / `direct_mir_driver_v4.rs`)

  Formalizes the 8-family claim-to-capture matrix, the empirical comparison of
  `direct_mir_driver_v4` (`.amir` v3 with `hook_mir_built`, `hook_mir_promoted`,
  `hook_mir_drops_elaborated`, `tcx.layout_of`, and `VarDebugInfo` + `LocalInfo`
  sidecar join) vs. `charon 0.1.210` vs. `rustc_public` on the pinned toolchain
  (`rustc 1.98.0-nightly (f8a08b688 2026-05-30)`), the `LocalInfo` clearing
  boundary between `MirPhase::Built` and `Runtime(PostCleanup)`, the genuine
  `PlaceMention((*_1))` discriminator (`match_wildcard_probe` and
  `assign_underscore_probe` vs. `ub_boundary_probe`), and the empirical async
  `.await` pass-ordering observation (`ElaborateDrops` runs before `StateTransform`,
  so `hook_mir_drops_elaborated` captures pre-`StateTransform` `Yield` while
  post-`StateTransform` coroutine state machines are captured at `mir_coroutine_witnesses` /
  `optimized_mir`).
-/

set_option autoImplicit false

namespace AnnealResearch.ClaimCaptureClosure

inductive ClaimFamily where
  | functionalReturnAndPanicSafety
  | loopTerminationAndFuel
  | dropOrderAndUnwindCleanup
  | aliasingAndRetagSensitivity
  | validityAndUnusedLoad
  | specializationAndTraitResolution
  | layoutCastAndConstRequired
  | asyncCoroutineStateMachine
  deriving DecidableEq, Repr

inductive CaptureRoute where
  | directMirDriverV3
  | charonUllbcElaborated
  | charonLlbcElaborated
  | rustcPublicDefault
  | rustcPublicOpt0PreserveUb
  deriving DecidableEq, Repr

structure CaptureCapability where
  route : CaptureRoute
  preservesStorageLiveness : Bool
  preservesPlaceMentionDerefs : Bool
  preservesRetagOperands : Bool
  preservesExplicitDropGlue : Bool
  preservesUnwindCleanupGraph : Bool
  capturesBuiltLocalInfo : Bool
  capturesMonoCollectorGraph : Bool
  capturesPreStateTransformAsync : Bool
  deriving DecidableEq, Repr

def capabilityOfRoute : CaptureRoute → CaptureCapability
  | .directMirDriverV3 =>
      { route := .directMirDriverV3
      , preservesStorageLiveness := true
      , preservesPlaceMentionDerefs := true
      , preservesRetagOperands := true
      , preservesExplicitDropGlue := true
      , preservesUnwindCleanupGraph := true
      , capturesBuiltLocalInfo := true
      , capturesMonoCollectorGraph := true
      , capturesPreStateTransformAsync := true }
  | .charonUllbcElaborated =>
      { route := .charonUllbcElaborated
      , preservesStorageLiveness := true
      , preservesPlaceMentionDerefs := false
      , preservesRetagOperands := false
      , preservesExplicitDropGlue := false
      , preservesUnwindCleanupGraph := true
      , capturesBuiltLocalInfo := true
      , capturesMonoCollectorGraph := false
      , capturesPreStateTransformAsync := false }
  | .charonLlbcElaborated =>
      { route := .charonLlbcElaborated
      , preservesStorageLiveness := false
      , preservesPlaceMentionDerefs := false
      , preservesRetagOperands := false
      , preservesExplicitDropGlue := false
      , preservesUnwindCleanupGraph := false
      , capturesBuiltLocalInfo := true
      , capturesMonoCollectorGraph := false
      , capturesPreStateTransformAsync := false }
  | .rustcPublicDefault =>
      { route := .rustcPublicDefault
      , preservesStorageLiveness := false
      , preservesPlaceMentionDerefs := false
      , preservesRetagOperands := true
      , preservesExplicitDropGlue := false
      , preservesUnwindCleanupGraph := true
      , capturesBuiltLocalInfo := false
      , capturesMonoCollectorGraph := false
      , capturesPreStateTransformAsync := false }
  | .rustcPublicOpt0PreserveUb =>
      { route := .rustcPublicOpt0PreserveUb
      , preservesStorageLiveness := true
      , preservesPlaceMentionDerefs := true
      , preservesRetagOperands := true
      , preservesExplicitDropGlue := false
      , preservesUnwindCleanupGraph := true
      , capturesBuiltLocalInfo := false
      , capturesMonoCollectorGraph := false
      , capturesPreStateTransformAsync := false }

def routeSupportsClaim (r : CaptureRoute) (f : ClaimFamily) : Bool :=
  let c := capabilityOfRoute r
  match f with
  | .functionalReturnAndPanicSafety => true
  | .loopTerminationAndFuel => true
  | .dropOrderAndUnwindCleanup =>
      c.preservesUnwindCleanupGraph && c.preservesExplicitDropGlue
  | .aliasingAndRetagSensitivity =>
      c.preservesRetagOperands && c.preservesStorageLiveness
  | .validityAndUnusedLoad =>
      c.preservesPlaceMentionDerefs && c.preservesStorageLiveness
  | .specializationAndTraitResolution =>
      c.capturesMonoCollectorGraph
  | .layoutCastAndConstRequired =>
      true
  | .asyncCoroutineStateMachine =>
      c.capturesPreStateTransformAsync

def allClaimFamilies : List ClaimFamily :=
  [ .functionalReturnAndPanicSafety
  , .loopTerminationAndFuel
  , .dropOrderAndUnwindCleanup
  , .aliasingAndRetagSensitivity
  , .validityAndUnusedLoad
  , .specializationAndTraitResolution
  , .layoutCastAndConstRequired
  , .asyncCoroutineStateMachine
  ]

/-- Observed summary record from `artifacts/v3/out_place_mention_default.json` and
    `artifacts/v3/out_place_mention_preserve_ub.json` together with body-level
    inspection in `artifacts/v3/bodies_place_mention_*.json`. -/
structure PlaceMentionProbeObservation where
  probeName : String
  phaseTag : String
  preserveUb : Bool
  blocks : Nat
  locals : Nat
  localInfoSet : Nat
  localInfoCleared : Nat
  assigns : Nat
  placeMentions : Nat
  hasDerefCopyAssign : Bool
  hasDerefPlaceMention : Bool
  deriving DecidableEq, Repr

def obsUbBoundaryBuilt : PlaceMentionProbeObservation :=
  { probeName := "ub_boundary_probe"
  , phaseTag := "Built"
  , preserveUb := false
  , blocks := 4, locals := 6, localInfoSet := 6, localInfoCleared := 0
  , assigns := 5, placeMentions := 1
  , hasDerefCopyAssign := true, hasDerefPlaceMention := false }

def obsUbBoundaryPostCleanupDefault : PlaceMentionProbeObservation :=
  { probeName := "ub_boundary_probe"
  , phaseTag := "Runtime(PostCleanup)"
  , preserveUb := false
  , blocks := 4, locals := 6, localInfoSet := 0, localInfoCleared := 6
  , assigns := 5, placeMentions := 0
  , hasDerefCopyAssign := true, hasDerefPlaceMention := false }

def obsUbBoundaryOptimizedDefault : PlaceMentionProbeObservation :=
  { probeName := "ub_boundary_probe"
  , phaseTag := "Runtime(Optimized)"
  , preserveUb := false
  , blocks := 1, locals := 3, localInfoSet := 0, localInfoCleared := 3
  , assigns := 1, placeMentions := 0
  , hasDerefCopyAssign := false, hasDerefPlaceMention := false }

def obsUbBoundaryPostCleanupPreserveUb : PlaceMentionProbeObservation :=
  { probeName := "ub_boundary_probe"
  , phaseTag := "Runtime(PostCleanup)"
  , preserveUb := true
  , blocks := 4, locals := 6, localInfoSet := 0, localInfoCleared := 6
  , assigns := 5, placeMentions := 1
  , hasDerefCopyAssign := true, hasDerefPlaceMention := false }

def obsUbBoundaryOptimizedPreserveUb : PlaceMentionProbeObservation :=
  { probeName := "ub_boundary_probe"
  , phaseTag := "Runtime(Optimized)"
  , preserveUb := true
  , blocks := 2, locals := 4, localInfoSet := 0, localInfoCleared := 4
  , assigns := 2, placeMentions := 1
  , hasDerefCopyAssign := true, hasDerefPlaceMention := false }

def obsMatchWildcardBuilt : PlaceMentionProbeObservation :=
  { probeName := "match_wildcard_probe"
  , phaseTag := "Built"
  , preserveUb := false
  , blocks := 4, locals := 6, localInfoSet := 6, localInfoCleared := 0
  , assigns := 5, placeMentions := 1
  , hasDerefCopyAssign := false, hasDerefPlaceMention := true }

def obsMatchWildcardPostCleanupDefault : PlaceMentionProbeObservation :=
  { probeName := "match_wildcard_probe"
  , phaseTag := "Runtime(PostCleanup)"
  , preserveUb := false
  , blocks := 4, locals := 6, localInfoSet := 0, localInfoCleared := 6
  , assigns := 5, placeMentions := 0
  , hasDerefCopyAssign := false, hasDerefPlaceMention := false }

def obsMatchWildcardPostCleanupPreserveUb : PlaceMentionProbeObservation :=
  { probeName := "match_wildcard_probe"
  , phaseTag := "Runtime(PostCleanup)"
  , preserveUb := true
  , blocks := 4, locals := 6, localInfoSet := 0, localInfoCleared := 6
  , assigns := 5, placeMentions := 1
  , hasDerefCopyAssign := false, hasDerefPlaceMention := true }

def obsAssignUnderscoreBuilt : PlaceMentionProbeObservation :=
  { probeName := "assign_underscore_probe"
  , phaseTag := "Built"
  , preserveUb := false
  , blocks := 1, locals := 4, localInfoSet := 4, localInfoCleared := 0
  , assigns := 3, placeMentions := 1
  , hasDerefCopyAssign := false, hasDerefPlaceMention := true }

def obsAssignUnderscorePostCleanupDefault : PlaceMentionProbeObservation :=
  { probeName := "assign_underscore_probe"
  , phaseTag := "Runtime(PostCleanup)"
  , preserveUb := false
  , blocks := 1, locals := 4, localInfoSet := 0, localInfoCleared := 4
  , assigns := 3, placeMentions := 0
  , hasDerefCopyAssign := false, hasDerefPlaceMention := false }

def obsAssignUnderscorePostCleanupPreserveUb : PlaceMentionProbeObservation :=
  { probeName := "assign_underscore_probe"
  , phaseTag := "Runtime(PostCleanup)"
  , preserveUb := true
  , blocks := 1, locals := 4, localInfoSet := 0, localInfoCleared := 4
  , assigns := 3, placeMentions := 1
  , hasDerefCopyAssign := false, hasDerefPlaceMention := true }

def bodyRetainsPointerCheck (o : PlaceMentionProbeObservation) : Bool :=
  o.hasDerefCopyAssign || o.hasDerefPlaceMention

/-- Observed `rustc_public` summary record from
    `artifacts/v3/rustc_public_cleanup_default.json` and
    `artifacts/v3/rustc_public_cleanup_opt0_preserve_ub.json`. -/
structure RustcPublicObservation where
  itemName : String
  opt0PreserveUb : Bool
  blocks : Nat
  locals : Nat
  storageLive : Nat
  storageDead : Nat
  placeMentions : Nat
  useRetagYes : Nat
  useRetagNo : Nat
  drops : Nat
  resumes : Nat
  deriving DecidableEq, Repr

def rpPartialInitDefault : RustcPublicObservation :=
  { itemName := "cleanup_subject::partial_init_move_cleanup"
  , opt0PreserveUb := false
  , blocks := 16, locals := 15
  , storageLive := 0, storageDead := 0, placeMentions := 0
  , useRetagYes := 10, useRetagNo := 1, drops := 6, resumes := 1 }

def rpPartialInitOpt0PreserveUb : RustcPublicObservation :=
  { itemName := "cleanup_subject::partial_init_move_cleanup"
  , opt0PreserveUb := true
  , blocks := 17, locals := 22
  , storageLive := 14, storageDead := 14, placeMentions := 0
  , useRetagYes := 15, useRetagNo := 1, drops := 6, resumes := 1 }

def rpUbProbeDefault : RustcPublicObservation :=
  { itemName := "cleanup_subject::ub_boundary_probe"
  , opt0PreserveUb := false
  , blocks := 1, locals := 3
  , storageLive := 0, storageDead := 0, placeMentions := 0
  , useRetagYes := 1, useRetagNo := 0, drops := 0, resumes := 0 }

def rpUbProbeOpt0PreserveUb : RustcPublicObservation :=
  { itemName := "cleanup_subject::ub_boundary_probe"
  , opt0PreserveUb := true
  , blocks := 4, locals := 6
  , storageLive := 3, storageDead := 3, placeMentions := 1
  , useRetagYes := 5, useRetagNo := 0, drops := 0, resumes := 0 }

/-- Observed feature-ladder capture record comparing `direct_mir_driver_v3` and
    `charon --ullbc --mir elaborated` on `feature_ladder_subject.rs`. -/
structure FeatureLadderObservation where
  ownerName : String
  directCapturedAtHookElab : Bool
  directCapturedAtAfterAnalysisElab : Bool
  directCapturedAtOptimized : Bool
  directPromotedCount : Nat
  charonUllbcHasBody : Bool
  deriving DecidableEq, Repr

def ladderPromotedRefCheck : FeatureLadderObservation :=
  { ownerName := "promoted_ref_check"
  , directCapturedAtHookElab := true
  , directCapturedAtAfterAnalysisElab := true
  , directCapturedAtOptimized := true
  , directPromotedCount := 1
  , charonUllbcHasBody := true }

def ladderClosureBody : FeatureLadderObservation :=
  { ownerName := "closure_offset_apply::{closure#0}"
  , directCapturedAtHookElab := true
  , directCapturedAtAfterAnalysisElab := true
  , directCapturedAtOptimized := true
  , directPromotedCount := 0
  , charonUllbcHasBody := true }

def ladderAssocConstStep : FeatureLadderObservation :=
  { ownerName := "<u32 as StepBound>::STEP"
  , directCapturedAtHookElab := true
  , directCapturedAtAfterAnalysisElab := true
  , directCapturedAtOptimized := false
  , directPromotedCount := 0
  , charonUllbcHasBody := true }

def ladderAsyncCoroutineClosure : FeatureLadderObservation :=
  { ownerName := "async_step_probe::{closure#0}"
  , directCapturedAtHookElab := true
  , directCapturedAtAfterAnalysisElab := false
  , directCapturedAtOptimized := true
  , directPromotedCount := 0
  , charonUllbcHasBody := false }

theorem direct_mir_driver_v3_supports_all_eight_claim_families :
    (allClaimFamilies.all (routeSupportsClaim .directMirDriverV3)) = true := by
  rfl

theorem charon_llbc_serves_safe_functional_and_layout_slices_only :
    routeSupportsClaim .charonLlbcElaborated .functionalReturnAndPanicSafety = true ∧
    routeSupportsClaim .charonLlbcElaborated .loopTerminationAndFuel = true ∧
    routeSupportsClaim .charonLlbcElaborated .layoutCastAndConstRequired = true ∧
    routeSupportsClaim .charonLlbcElaborated .dropOrderAndUnwindCleanup = false ∧
    routeSupportsClaim .charonLlbcElaborated .aliasingAndRetagSensitivity = false ∧
    routeSupportsClaim .charonLlbcElaborated .validityAndUnusedLoad = false := by
  decide

theorem place_mention_discriminator_distinguishes_let_underscore_from_match_and_assign :
    bodyRetainsPointerCheck obsUbBoundaryPostCleanupDefault = true ∧
    bodyRetainsPointerCheck obsUbBoundaryOptimizedDefault = false ∧
    bodyRetainsPointerCheck obsUbBoundaryOptimizedPreserveUb = true ∧
    bodyRetainsPointerCheck obsMatchWildcardPostCleanupDefault = false ∧
    bodyRetainsPointerCheck obsMatchWildcardPostCleanupPreserveUb = true ∧
    bodyRetainsPointerCheck obsAssignUnderscorePostCleanupDefault = false ∧
    bodyRetainsPointerCheck obsAssignUnderscorePostCleanupPreserveUb = true := by
  decide

theorem local_info_preserved_only_at_mir_built :
    obsUbBoundaryBuilt.localInfoSet = obsUbBoundaryBuilt.locals ∧
    obsMatchWildcardBuilt.localInfoSet = obsMatchWildcardBuilt.locals ∧
    obsAssignUnderscoreBuilt.localInfoSet = obsAssignUnderscoreBuilt.locals ∧
    obsUbBoundaryPostCleanupDefault.localInfoSet = 0 ∧
    obsUbBoundaryPostCleanupPreserveUb.localInfoSet = 0 ∧
    obsMatchWildcardPostCleanupPreserveUb.localInfoSet = 0 := by
  decide

theorem rustc_public_default_erases_storage_and_unused_load_checks :
    rpPartialInitDefault.storageLive = 0 ∧
    rpPartialInitDefault.storageDead = 0 ∧
    rpUbProbeDefault.placeMentions = 0 ∧
    rpUbProbeDefault.blocks = 1 ∧
    rpPartialInitOpt0PreserveUb.storageLive = 14 ∧
    rpUbProbeOpt0PreserveUb.placeMentions = 1 ∧
    rpUbProbeOpt0PreserveUb.blocks = 4 := by
  decide

theorem async_coroutine_requires_hook_before_state_transform_and_blocks_charon :
    ladderAsyncCoroutineClosure.directCapturedAtHookElab = true ∧
    ladderAsyncCoroutineClosure.directCapturedAtAfterAnalysisElab = false ∧
    ladderAsyncCoroutineClosure.directCapturedAtOptimized = true ∧
    ladderAsyncCoroutineClosure.charonUllbcHasBody = false ∧
    ladderPromotedRefCheck.directPromotedCount = 1 := by
  decide

#print axioms direct_mir_driver_v3_supports_all_eight_claim_families
#print axioms charon_llbc_serves_safe_functional_and_layout_slices_only
#print axioms place_mention_discriminator_distinguishes_let_underscore_from_match_and_assign
#print axioms local_info_preserved_only_at_mir_built
#print axioms rustc_public_default_erases_storage_and_unused_load_checks
#print axioms async_coroutine_requires_hook_before_state_transform_and_blocks_charon

end AnnealResearch.ClaimCaptureClosure
