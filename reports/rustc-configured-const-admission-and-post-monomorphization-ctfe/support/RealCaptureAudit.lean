import Std
import AnnealResearch.Execution

set_option Elab.async false

/-!
# Real, Matched Compiler Capture Audit (`FE-F2`)

This module mechanizes the positive empirical findings from the Follow-Up 2 (`FE-F2`)
matched compiler capture probe across `direct_mir_driver` / `direct_mir_driver_v2`
(`rustc_driver::Callbacks`) and `charon 0.1.210` on the shared pinned toolchain
`rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (`x86_64-unknown-linux-gnu`,
`rustc` SHA-256 `c0575015cb2b0648bff9042dc2e68f139fb0b16c981cdca96efba2e91ac409d8`,
`charon` SHA-256 `88542ca0b2bf52429fd5b9f2bf29f0f1183ba2279854567ab13d82bc789a8d47`):

1. **`combined_hook_and_demand_captures_all_modes`**: Combining `override_queries`
   interception of `mir_drops_elaborated_and_const_checked` with `after_analysis`
   owner demand captures the 6 selected local `Runtime(PostCleanup)` bodies across
   standard, `force_opt_before_elab` (`elab_stolen_before_opt = true`),
   cold-incremental, and warm-incremental runs, whereas `after_analysis`-only reading
   fails when `optimized_mir` steals the `Steal<Body>` first and passive hooks alone
   fail on a warm incremental cache (`hookEvents = 0`).
2. **`independent_completion_oracle_sound`**: Requiring
   `processExitCode == 0 ∧ monoCollectionCompleted == true ∧ hasErrorsAtAfterAnalysis == false`
   accepts `probe_a0_direct_full`, `probe_a1_direct_full`, `probe_b0_direct_full`, and
   `probe_unused_b1_direct_full`, while rejecting `probe_b1_direct_full`
   (`processExitCode = 1`, `provisionalHookWritten = true`,
   `monoCollectionCompleted = false`) and `probe_b1_direct_stop_after_analysis`.
3. **`unused_failing_mention_excluded_by_mono_reachability`**: On
   `probe_unused_b1_direct_full`, the polymorphic `after_analysis_owners` table
   contains 8 owners including `never_instantiated` (mentioning `checked::<B, 1>`),
   whereas `collected_mono_items` contains only `entry`, `checked::<B, 0>`,
   `<B as Bound>::marker`, and `<A as Bound>::marker`; entry-scoped monomorphic
   obligation discharge therefore succeeds without evaluating the unreachable
   `<B, 1>` inline constant.
4. **`ullbc_elaborated_preserves_unwind_while_llbc_drops_it`**: On
   `partial_init_move_cleanup` and `partial_field_reinit_cleanup`
   (`cleanup_subject.rs`, SHA-256 `04b073d7d46ffd95dee0730259844032959160e8fcc8e67565df5c25704f41c5`),
   both `direct_mir_driver` (`Runtime(PostCleanup)`) and `charon`
   `ullbc_elaborated_default` (`--ullbc --mir elaborated`) retain normal and
   unwind drop blocks (`totalDrops = 6` and `3`, `resumes = 1`), whereas `charon`
   `llbc_elaborated_default` (`--mir elaborated`) omits the unwind cleanup blocks
   during control-flow structuring (`unwindDropBlocks = 0`, `resumes = 0`).
5. **`crate_svh_binding_distinguishes_substituted_dep`**: On `dep_control_rlib_orig`
   vs `dep_control_rlib_substituted` (`dep_subject.rs`, SHA-256
   `a65859527362b9ed7002c555bfbbe9913b9e45ae7a46a9999bba4bc49d545220`), local
   `sourceSha256`, `ownerDefPathHash`, and `calleeDefPathHash` are identical, while
   `externalCrateSvh` differs (`16466527938559560516` / `16377899976409579846` vs
   `9991835327327507104`), so `AdmissibleDepCrateBinding` rejects the substituted
   `.rlib` and `AdmissibleDepBodyClosure` flags missing MIR
   (`nonInlineMirAvailable = false`) on `dep_provider::dep_non_inline`.
6. **`admissible_capture_transfers_entry_safety`**: Non-circularly separates
   (i) `AdmissibleCaptureBinding` (structural/completion/dependency-binding admission,
   which admits both safe and unsafe captured bodies), (ii) `ProducerCompilationCorrespondence`
   (`entryHasRuntimeUB = capturedModelHasUB`), and (iii) a separate semantic `Execution.NoUB`
   proof on the captured model (`capturedModelStep`), showing that all three are required
   to transfer `Execution.NoUB` to `capturedEntryStep` while `admittedUnsafeEntrySubject`
   remains structurally admitted yet violates `Execution.NoUB`.

*Authored by an AI agent acting on joshlf's behalf.*
-/

namespace AnnealResearch.RealCaptureAudit

/-! ## 1. Query Hook Ordering, `Steal<Body>`, and Incremental Cache Runs -/

/-- Observed capture metrics for a `direct_mir_driver` run on `cleanup_subject.rs`
(6 local HIR body owners: `EffectLog::record`, `<Guard<'a> as Drop>::drop`,
`may_unwind_op`, `partial_init_move_cleanup`, `partial_field_reinit_cleanup`,
`ub_boundary_probe`). -/
structure CaptureModeRun where
  runId : Nat
  expectedOwners : Nat
  hookEvents : Nat
  hookPostCleanupBodies : Nat
  afterAnalysisDemand : Bool
  elabStolenBeforeOpt : Bool
  elabStolenAfterOpt : Bool
  afterAnalysisUnstolenBodies : Nat

/-- Passive query hooks alone capture all selected local owners iff
`hookPostCleanupBodies` matches `expectedOwners` without requiring `afterAnalysisDemand`. -/
noncomputable def PassiveHooksOnlyCaptures (r : CaptureModeRun) : Bool :=
  Nat.beq r.hookPostCleanupBodies r.expectedOwners

/-- Reading `tcx.mir_drops_elaborated_and_const_checked` in `after_analysis` without
a pre-steal query hook succeeds iff `afterAnalysisDemand` runs while
`elabStolenBeforeOpt` is `false` and all selected local owners remain unstolen. -/
noncomputable def AfterAnalysisOnlyCaptures (r : CaptureModeRun) : Bool :=
  r.afterAnalysisDemand &&
  !r.elabStolenBeforeOpt &&
  Nat.beq r.afterAnalysisUnstolenBodies r.expectedOwners

/-- Combining `override_queries` on `mir_drops_elaborated_and_const_checked` with
active `after_analysis` owner demand captures `Runtime(PostCleanup)` for the selected
local owners whenever `afterAnalysisDemand` is enabled and either the query hook
recorded all bodies prior to theft or `after_analysis` read all unstolen bodies directly. -/
noncomputable def CombinedHookAndDemandCaptures (r : CaptureModeRun) : Bool :=
  r.afterAnalysisDemand &&
  (Nat.beq r.hookPostCleanupBodies r.expectedOwners ||
   (!r.elabStolenBeforeOpt && Nat.beq r.afterAnalysisUnstolenBodies r.expectedOwners))

/-- `cleanup_direct_default` (`out_cleanup_default.json`,
SHA-256 `ad4669031b409d41f25d153053ce67f305a229200cd116524ce6ba54b3ceeaa4`). -/
noncomputable def runCleanupDefault : CaptureModeRun :=
  { runId := 1
    expectedOwners := 6
    hookEvents := 12
    hookPostCleanupBodies := 6
    afterAnalysisDemand := true
    elabStolenBeforeOpt := false
    elabStolenAfterOpt := true
    afterAnalysisUnstolenBodies := 6 }

/-- `cleanup_direct_force_opt_before_elab` (`out_cleanup_force_opt_first.json`,
SHA-256 `e624a3f4fd8c5e049d8f86449b55890ba4cc1a5201df4b7423012c96b38d7920`):
`tcx.optimized_mir` steals `mir_drops_elaborated_and_const_checked` before
`after_analysis` reads it (`elabStolenBeforeOpt = true`), but `hook_mir_drops_elaborated`
already intercepted all 6 `Runtime(PostCleanup)` bodies before theft. -/
noncomputable def runCleanupForceOptBeforeElab : CaptureModeRun :=
  { runId := 2
    expectedOwners := 6
    hookEvents := 12
    hookPostCleanupBodies := 6
    afterAnalysisDemand := true
    elabStolenBeforeOpt := true
    elabStolenAfterOpt := true
    afterAnalysisUnstolenBodies := 0 }

/-- `cleanup_incremental_cold` (`out_cleanup_incr_cold.json`): cold incremental cache
populations invoke all 12 hooks (6 `Built`, 6 `Runtime(PostCleanup)`). -/
noncomputable def runCleanupIncrementalCold : CaptureModeRun :=
  { runId := 3
    expectedOwners := 6
    hookEvents := 12
    hookPostCleanupBodies := 6
    afterAnalysisDemand := true
    elabStolenBeforeOpt := false
    elabStolenAfterOpt := true
    afterAnalysisUnstolenBodies := 6 }

/-- `cleanup_incremental_warm_passive` (`out_cleanup_incr_warm_passive.json`): on a
warm incremental cache with `--driver-passive-hooks-only`, zero query hooks fire
(`hookEvents = 0`). -/
noncomputable def runCleanupIncrementalWarmPassive : CaptureModeRun :=
  { runId := 4
    expectedOwners := 6
    hookEvents := 0
    hookPostCleanupBodies := 0
    afterAnalysisDemand := false
    elabStolenBeforeOpt := false
    elabStolenAfterOpt := false
    afterAnalysisUnstolenBodies := 0 }

/-- `cleanup_incremental_warm` (`out_cleanup_incr_warm.json`): active owner demand in
`after_analysis` forces `mir_drops_elaborated_and_const_checked` and `mir_built`
providers to execute even when the incremental cache is warm (`hookEvents = 12`). -/
noncomputable def runCleanupIncrementalWarm : CaptureModeRun :=
  { runId := 5
    expectedOwners := 6
    hookEvents := 12
    hookPostCleanupBodies := 6
    afterAnalysisDemand := true
    elabStolenBeforeOpt := false
    elabStolenAfterOpt := false
    afterAnalysisUnstolenBodies := 6 }

/-- **Theorem 1 (`FE-F2`)**: Combining `override_queries` with `after_analysis` owner
demand captures `Runtime(PostCleanup)` across standard, `force_opt_before_elab`
(`elabStolenBeforeOpt = true`), cold-incremental, and warm-incremental runs, whereas
`after_analysis`-only fails on `force_opt_before_elab` and passive-hooks-only fails
on warm incremental (`hookEvents = 0`). -/
theorem combined_hook_and_demand_captures_all_modes :
    CombinedHookAndDemandCaptures runCleanupDefault = true ∧
    CombinedHookAndDemandCaptures runCleanupForceOptBeforeElab = true ∧
    CombinedHookAndDemandCaptures runCleanupIncrementalCold = true ∧
    CombinedHookAndDemandCaptures runCleanupIncrementalWarm = true ∧
    runCleanupForceOptBeforeElab.elabStolenBeforeOpt = true ∧
    AfterAnalysisOnlyCaptures runCleanupForceOptBeforeElab = false ∧
    runCleanupIncrementalWarmPassive.hookEvents = 0 ∧
    PassiveHooksOnlyCaptures runCleanupIncrementalWarmPassive = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Independent Completion Oracle and Reachable Monomorphized Obligations -/

/-- Observed capture record for Family 2 (`experiments/configured-admission/probe.rs`,
SHA-256 `3ada61fe22ea9ee0047c440d76c3a13564f23026fbfdbe37320f0707e083c3fb`). -/
structure ProbeCaptureRun where
  runId : Nat
  sourceSha256Hi : Nat
  processExitCode : Nat
  provisionalHookWritten : Bool
  monoCollectionCompleted : Bool
  stopAfterAnalysis : Bool
  hasErrorsAtAfterAnalysis : Bool
  hookEvents : Nat
  polymorphicOwnersCount : Nat
  includesNeverInstantiatedOwner : Bool
  entryDefPathHashHi : Nat
  entryDefPathHashLo : Nat
  entryCheckedTypeArgId : Nat
  entryCheckedConstArg : Nat
  selectedMarkerDefPathHashLo : Nat
  collectedMonoItemsCount : Nat
  monoHasEntry : Bool
  monoHasCheckedA1 : Bool
  monoHasCheckedB0 : Bool
  monoHasCheckedB1 : Bool

/-- Independent completion oracle: requires process exit code `0`, completed
monomorphization collection (`monoCollectionCompleted = true`), and zero diagnostics
at `after_analysis` (`hasErrorsAtAfterAnalysis = false`). -/
noncomputable def IndependentCompletionOracle (r : ProbeCaptureRun) : Bool :=
  Nat.beq r.processExitCode 0 &&
  r.monoCollectionCompleted &&
  !r.hasErrorsAtAfterAnalysis

/-- Entry-scoped monomorphic obligation discharge: requires
`IndependentCompletionOracle r`, presence of `entry` in `collected_mono_items`, and
satisfaction of `N <= <T as Bound>::LIMIT` for every reachable monomorphized
`checked::<T, N>` instance in `collected_mono_items` (`1 <= 1` for `<A, 1>`,
`0 <= 0` for `<B, 0>`, and `1 <= 0` for `<B, 1>`). -/
noncomputable def EntryScopedMonoObligationsHold (r : ProbeCaptureRun) : Bool :=
  IndependentCompletionOracle r &&
  r.monoHasEntry &&
  (!r.monoHasCheckedA1 || Nat.ble 1 1) &&
  (!r.monoHasCheckedB0 || Nat.ble 0 0) &&
  (!r.monoHasCheckedB1 || Nat.ble 1 0)

/-- `probe_a0_direct_full` (`out_probe_a0_full.json`,
SHA-256 `3039559a6a301b6fe620727028e0b8c19cf6c6b662735598f7b8485c624f9b05`). -/
noncomputable def probeA0DirectFull : ProbeCaptureRun :=
  { runId := 10
    sourceSha256Hi := 0x3ada61fe22ea9ee0
    processExitCode := 0
    provisionalHookWritten := true
    monoCollectionCompleted := true
    stopAfterAnalysis := false
    hasErrorsAtAfterAnalysis := false
    hookEvents := 12
    polymorphicOwnersCount := 6
    includesNeverInstantiatedOwner := false
    entryDefPathHashHi := 17723421528714699607
    entryDefPathHashLo := 4570208110444831709
    entryCheckedTypeArgId := 1
    entryCheckedConstArg := 1
    selectedMarkerDefPathHashLo := 6764858275740784439
    collectedMonoItemsCount := 2
    monoHasEntry := false
    monoHasCheckedA1 := false
    monoHasCheckedB0 := false
    monoHasCheckedB1 := false }

/-- `probe_a1_direct_full` (`out_probe_a1_full.json`,
SHA-256 `27c2100dcc8eeb36999ff0fd80d3b555840e7de6fdbd51b4b2893a5d35f5788f`). -/
noncomputable def probeA1DirectFull : ProbeCaptureRun :=
  { runId := 11
    sourceSha256Hi := 0x3ada61fe22ea9ee0
    processExitCode := 0
    provisionalHookWritten := true
    monoCollectionCompleted := true
    stopAfterAnalysis := false
    hasErrorsAtAfterAnalysis := false
    hookEvents := 15
    polymorphicOwnersCount := 7
    includesNeverInstantiatedOwner := false
    entryDefPathHashHi := 17723421528714699607
    entryDefPathHashLo := 4570208110444831709
    entryCheckedTypeArgId := 1
    entryCheckedConstArg := 1
    selectedMarkerDefPathHashLo := 6764858275740784439
    collectedMonoItemsCount := 4
    monoHasEntry := true
    monoHasCheckedA1 := true
    monoHasCheckedB0 := false
    monoHasCheckedB1 := false }

/-- `probe_b0_direct_full` (`out_probe_b0_full.json`,
SHA-256 `6b098f83a7c37f6a1abbf6de7be927426120a29b3352d4b8353bd1ebd6ffcec4`). -/
noncomputable def probeB0DirectFull : ProbeCaptureRun :=
  { runId := 12
    sourceSha256Hi := 0x3ada61fe22ea9ee0
    processExitCode := 0
    provisionalHookWritten := true
    monoCollectionCompleted := true
    stopAfterAnalysis := false
    hasErrorsAtAfterAnalysis := false
    hookEvents := 15
    polymorphicOwnersCount := 7
    includesNeverInstantiatedOwner := false
    entryDefPathHashHi := 17723421528714699607
    entryDefPathHashLo := 4570208110444831709
    entryCheckedTypeArgId := 2
    entryCheckedConstArg := 0
    selectedMarkerDefPathHashLo := 2167899770915204058
    collectedMonoItemsCount := 4
    monoHasEntry := true
    monoHasCheckedA1 := false
    monoHasCheckedB0 := true
    monoHasCheckedB1 := false }

/-- `probe_b1_direct_stop_after_analysis` (`out_probe_b1_stop.json`,
SHA-256 `b4514ffcbabd321a84a9eb907214c4faa0f076bc100e34cf4ec7ea4f1f8e4928`). -/
noncomputable def probeB1DirectStopAfterAnalysis : ProbeCaptureRun :=
  { runId := 13
    sourceSha256Hi := 0x3ada61fe22ea9ee0
    processExitCode := 0
    provisionalHookWritten := true
    monoCollectionCompleted := false
    stopAfterAnalysis := true
    hasErrorsAtAfterAnalysis := false
    hookEvents := 15
    polymorphicOwnersCount := 7
    includesNeverInstantiatedOwner := false
    entryDefPathHashHi := 17723421528714699607
    entryDefPathHashLo := 4570208110444831709
    entryCheckedTypeArgId := 2
    entryCheckedConstArg := 1
    selectedMarkerDefPathHashLo := 2167899770915204058
    collectedMonoItemsCount := 0
    monoHasEntry := false
    monoHasCheckedA1 := false
    monoHasCheckedB0 := false
    monoHasCheckedB1 := false }

/-- `probe_b1_direct_full` (`out_probe_b1_full.json`,
SHA-256 `2965fbea37f58e6f670b0bfbc492d6b95cd3b9f2831088883e53e43e574fbb3f`):
writes the provisional hook file before `collect_and_partition_mono_items` aborts on
`E0080` (`processExitCode = 1`, `monoCollectionCompleted = false`). -/
noncomputable def probeB1DirectFull : ProbeCaptureRun :=
  { runId := 14
    sourceSha256Hi := 0x3ada61fe22ea9ee0
    processExitCode := 1
    provisionalHookWritten := true
    monoCollectionCompleted := false
    stopAfterAnalysis := false
    hasErrorsAtAfterAnalysis := false
    hookEvents := 15
    polymorphicOwnersCount := 7
    includesNeverInstantiatedOwner := false
    entryDefPathHashHi := 17723421528714699607
    entryDefPathHashLo := 4570208110444831709
    entryCheckedTypeArgId := 2
    entryCheckedConstArg := 1
    selectedMarkerDefPathHashLo := 2167899770915204058
    collectedMonoItemsCount := 0
    monoHasEntry := false
    monoHasCheckedA1 := false
    monoHasCheckedB0 := false
    monoHasCheckedB1 := false }

/-- `probe_unused_b1_direct_full` (`out_probe_unused_b1_full.json`,
SHA-256 `bf2ce339f89257929dc6459849df8800c2f0dcfc005bd30519d57af920411128`):
includes `never_instantiated` in `after_analysis_owners`, while `collected_mono_items`
contains only `entry`, `checked::<B, 0>`, `<B as Bound>::marker`, and
`<A as Bound>::marker`. -/
noncomputable def probeUnusedB1DirectFull : ProbeCaptureRun :=
  { runId := 15
    sourceSha256Hi := 0x3ada61fe22ea9ee0
    processExitCode := 0
    provisionalHookWritten := true
    monoCollectionCompleted := true
    stopAfterAnalysis := false
    hasErrorsAtAfterAnalysis := false
    hookEvents := 18
    polymorphicOwnersCount := 8
    includesNeverInstantiatedOwner := true
    entryDefPathHashHi := 17723421528714699607
    entryDefPathHashLo := 4570208110444831709
    entryCheckedTypeArgId := 2
    entryCheckedConstArg := 0
    selectedMarkerDefPathHashLo := 2167899770915204058
    collectedMonoItemsCount := 4
    monoHasEntry := true
    monoHasCheckedA1 := false
    monoHasCheckedB0 := true
    monoHasCheckedB1 := false }

/-- **Theorem 2 (`FE-F2`)**: Requiring
`processExitCode == 0 ∧ monoCollectionCompleted == true ∧ hasErrorsAtAfterAnalysis == false`
accepts `probe_a0_direct_full`, `probe_a1_direct_full`, `probe_b0_direct_full`, and
`probe_unused_b1_direct_full` while rejecting `probe_b1_direct_full`
(`processExitCode = 1`, `provisionalHookWritten = true`,
`monoCollectionCompleted = false`) and `probe_b1_direct_stop_after_analysis`. -/
theorem independent_completion_oracle_sound :
    IndependentCompletionOracle probeA0DirectFull = true ∧
    IndependentCompletionOracle probeA1DirectFull = true ∧
    IndependentCompletionOracle probeB0DirectFull = true ∧
    IndependentCompletionOracle probeUnusedB1DirectFull = true ∧
    probeB1DirectFull.processExitCode = 1 ∧
    probeB1DirectFull.provisionalHookWritten = true ∧
    probeB1DirectFull.monoCollectionCompleted = false ∧
    IndependentCompletionOracle probeB1DirectFull = false ∧
    IndependentCompletionOracle probeB1DirectStopAfterAnalysis = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 3 (`FE-F2`)**: On `probe_unused_b1_direct_full`, the polymorphic owner
table includes `never_instantiated` (mentioning `checked::<B, 1>`), while
`collectedMonoItems` contains `entry` and `checked::<B, 0>` and excludes
`checked::<B, 1>`, so entry-scoped monomorphic obligation discharge succeeds without
requiring the unreachable `<B, 1>` const check. -/
theorem unused_failing_mention_excluded_by_mono_reachability :
    probeUnusedB1DirectFull.polymorphicOwnersCount = 8 ∧
    probeUnusedB1DirectFull.includesNeverInstantiatedOwner = true ∧
    probeUnusedB1DirectFull.monoHasEntry = true ∧
    probeUnusedB1DirectFull.monoHasCheckedB0 = true ∧
    probeUnusedB1DirectFull.monoHasCheckedB1 = false ∧
    EntryScopedMonoObligationsHold probeUnusedB1DirectFull = true ∧
    EntryScopedMonoObligationsHold probeA1DirectFull = true ∧
    EntryScopedMonoObligationsHold probeB0DirectFull = true ∧
    EntryScopedMonoObligationsHold probeB1DirectFull = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Direct MIR vs Charon ULLBC vs Charon LLBC on Unwind Drop Ladders -/

/-- Observed control-flow and drop metrics for `partial_init_move_cleanup` (`ownerId = 1`)
and `partial_field_reinit_cleanup` (`ownerId = 2`) across `direct_mir_driver`
(`routeId = 1`), `charon` `ullbc_elaborated_default` (`routeId = 2`), and `charon`
`llbc_elaborated_default` (`routeId = 3`). -/
structure CleanupBodyCapture where
  routeId : Nat
  ownerId : Nat
  blocks : Nat
  locals : Nat
  normalDropBlocks : Nat
  unwindDropBlocks : Nat
  totalDrops : Nat
  calls : Nat
  switches : Nat
  returns : Nat
  resumes : Nat

/-- A captured body retains both normal and unwind drop cleanup blocks iff it has at
least one normal drop block, at least one unwind drop block, an exact sum
`totalDrops = normalDropBlocks + unwindDropBlocks`, and an explicit unwind resume
terminator (`resumes >= 1`). -/
noncomputable def PreservesNormalAndUnwindCleanup (c : CleanupBodyCapture) : Bool :=
  Nat.ble 1 c.normalDropBlocks &&
  Nat.ble 1 c.unwindDropBlocks &&
  Nat.beq c.totalDrops (c.normalDropBlocks + c.unwindDropBlocks) &&
  Nat.ble 1 c.resumes

/-- `partial_init_move_cleanup` in `direct_mir_driver` (`Runtime(PostCleanup)`):
`blocks = 17`, `locals = 22`, `drops = 6` (`3` normal + `3` unwind), `resumes = 1`. -/
noncomputable def directMirPartialInitMove : CleanupBodyCapture :=
  { routeId := 1, ownerId := 1, blocks := 17, locals := 22,
    normalDropBlocks := 3, unwindDropBlocks := 3, totalDrops := 6,
    calls := 3, switches := 4, returns := 1, resumes := 1 }

/-- `partial_field_reinit_cleanup` in `direct_mir_driver` (`Runtime(PostCleanup)`):
`blocks = 9`, `locals = 24`, `drops = 3` (`1` normal + `2` unwind), `resumes = 1`. -/
noncomputable def directMirPartialFieldReinit : CleanupBodyCapture :=
  { routeId := 1, ownerId := 2, blocks := 9, locals := 24,
    normalDropBlocks := 1, unwindDropBlocks := 2, totalDrops := 3,
    calls := 3, switches := 1, returns := 1, resumes := 1 }

/-- `partial_init_move_cleanup` in `charon` `ullbc_elaborated_default`
(`cleanup_ullbc_elaborated_default.ullbc`,
SHA-256 `c31337969368212329dd87dd61031ce016bdc14bb2b83e8706d1b9d0291b9b52`):
`drops = 6` (`3` normal + `3` unwind), `resumes = 1` (`unwind_continue`). -/
noncomputable def charonUllbcPartialInitMove : CleanupBodyCapture :=
  { routeId := 2, ownerId := 1, blocks := 18, locals := 21,
    normalDropBlocks := 3, unwindDropBlocks := 3, totalDrops := 6,
    calls := 3, switches := 4, returns := 1, resumes := 1 }

/-- `partial_field_reinit_cleanup` in `charon` `ullbc_elaborated_default`
(`cleanup_ullbc_elaborated_default.ullbc`):
`drops = 3` (`1` normal at `bb9` + `2` unwind at `bb3, bb4`), `resumes = 1`
(`bb7: unwind_continue`). -/
noncomputable def charonUllbcPartialFieldReinit : CleanupBodyCapture :=
  { routeId := 2, ownerId := 2, blocks := 11, locals := 24,
    normalDropBlocks := 1, unwindDropBlocks := 2, totalDrops := 3,
    calls := 3, switches := 1, returns := 1, resumes := 1 }

/-- `partial_init_move_cleanup` in `charon` `llbc_elaborated_default`
(`cleanup_llbc_elaborated_default.llbc`,
SHA-256 `719ea24b12d7c21129e2ee119c4a56c4755420354d9bac0e9c4dd65016f4dfa8`):
LLBC control-flow reconstruction omits all unwind blocks (`unwindDropBlocks = 0`,
`resumes = 0`). -/
noncomputable def charonLlbcPartialInitMove : CleanupBodyCapture :=
  { routeId := 3, ownerId := 1, blocks := 1, locals := 21,
    normalDropBlocks := 3, unwindDropBlocks := 0, totalDrops := 3,
    calls := 3, switches := 1, returns := 1, resumes := 0 }

/-- `partial_field_reinit_cleanup` in `charon` `llbc_elaborated_default`
(`cleanup_llbc_elaborated_default.llbc`):
LLBC control-flow reconstruction omits `bb1, bb3, bb4, bb6, bb7, bb8`, leaving only
the normal-return `drop pair_4` statement (`unwindDropBlocks = 0`, `resumes = 0`). -/
noncomputable def charonLlbcPartialFieldReinit : CleanupBodyCapture :=
  { routeId := 3, ownerId := 2, blocks := 1, locals := 24,
    normalDropBlocks := 1, unwindDropBlocks := 0, totalDrops := 1,
    calls := 3, switches := 0, returns := 1, resumes := 0 }

/-- **Theorem 4 (`FE-F2`)**: On `partial_init_move_cleanup` and
`partial_field_reinit_cleanup`, `direct_mir_driver` (`Runtime(PostCleanup)`) and
`charon` `ullbc_elaborated_default` retain normal and unwind drop blocks
(`totalDrops = 6` and `3`, `resumes = 1`), whereas `llbc_elaborated_default` omits
the unwind cleanup blocks (`unwindDropBlocks = 0`, `resumes = 0`). -/
theorem ullbc_elaborated_preserves_unwind_while_llbc_drops_it :
    directMirPartialInitMove.totalDrops = 6 ∧
    directMirPartialInitMove.resumes = 1 ∧
    directMirPartialFieldReinit.totalDrops = 3 ∧
    directMirPartialFieldReinit.resumes = 1 ∧
    charonUllbcPartialInitMove.totalDrops = 6 ∧
    charonUllbcPartialInitMove.resumes = 1 ∧
    charonUllbcPartialFieldReinit.totalDrops = 3 ∧
    charonUllbcPartialFieldReinit.resumes = 1 ∧
    PreservesNormalAndUnwindCleanup directMirPartialInitMove = true ∧
    PreservesNormalAndUnwindCleanup directMirPartialFieldReinit = true ∧
    PreservesNormalAndUnwindCleanup charonUllbcPartialInitMove = true ∧
    PreservesNormalAndUnwindCleanup charonUllbcPartialFieldReinit = true ∧
    charonLlbcPartialInitMove.unwindDropBlocks = 0 ∧
    charonLlbcPartialInitMove.resumes = 0 ∧
    charonLlbcPartialFieldReinit.unwindDropBlocks = 0 ∧
    charonLlbcPartialFieldReinit.resumes = 0 ∧
    PreservesNormalAndUnwindCleanup charonLlbcPartialInitMove = false ∧
    PreservesNormalAndUnwindCleanup charonLlbcPartialFieldReinit = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 4. External Crate SVH Binding and Missing-MIR Detection -/

/-- Observed cross-crate binding record for `dep_subject.rs` (`call_both_deps`
calling `dep_provider::dep_non_inline` and `dep_provider::dep_inlined`). -/
structure DepCaptureBinding where
  runId : Nat
  sourceSha256Hi : Nat
  ownerDefPathHashHi : Nat
  ownerDefPathHashLo : Nat
  calleeNonInlineDefPathHashHi : Nat
  calleeNonInlineDefPathHashLo : Nat
  calleeInlinedDefPathHashHi : Nat
  calleeInlinedDefPathHashLo : Nat
  externalCrateSvh : Nat
  externalCrateSvhMatrixHi : Nat
  externalCrateSvhLo : Nat
  nonInlineMirAvailable : Bool
  inlinedMirAvailable : Bool

/-- `dep_control_rmeta_only` (`out_dep_rmeta_only.json`, `libdep_only_meta.rmeta`
SHA-256 `f6910af38fad2cedbeedc0b4b24f14cf5a97add7573aec3fde312881e51148ad`). -/
noncomputable def depControlRmetaOnly : DepCaptureBinding :=
  { runId := 20
    sourceSha256Hi := 0xa65859527362b9ed
    ownerDefPathHashHi := 13620298541707722769
    ownerDefPathHashLo := 6145011225190168512
    calleeNonInlineDefPathHashHi := 16703889901102367156
    calleeNonInlineDefPathHashLo := 5774153523600403242
    calleeInlinedDefPathHashHi := 16703889901102367156
    calleeInlinedDefPathHashLo := 10380015184174581091
    externalCrateSvh := 12494866476077678016
    externalCrateSvhMatrixHi := 12494866476077678016
    externalCrateSvhLo := 17908043999388265497
    nonInlineMirAvailable := false
    inlinedMirAvailable := false }

/-- `dep_control_rlib_orig` (`out_dep_rlib_orig.json`, `libdep_orig.rlib`
SHA-256 `a57d0d74450fc677ab990387e8fc4afe04fe12965dac9d8f925391c86355bd22`).
Both `externalCrateSvh` and `externalCrateSvhMatrixHi` record the exact `Svh` high word
(`16377899976409579846`) observed in `artifacts/original/out_dep_rlib_orig.json`. -/
noncomputable def depControlRlibOrig : DepCaptureBinding :=
  { runId := 21
    sourceSha256Hi := 0xa65859527362b9ed
    ownerDefPathHashHi := 13620298541707722769
    ownerDefPathHashLo := 6145011225190168512
    calleeNonInlineDefPathHashHi := 16703889901102367156
    calleeNonInlineDefPathHashLo := 5774153523600403242
    calleeInlinedDefPathHashHi := 16703889901102367156
    calleeInlinedDefPathHashLo := 10380015184174581091
    externalCrateSvh := 16377899976409579846
    externalCrateSvhMatrixHi := 16377899976409579846
    externalCrateSvhLo := 1561246519524117238
    nonInlineMirAvailable := false
    inlinedMirAvailable := true }

/-- `dep_control_rlib_substituted` (`out_dep_rlib_substituted.json`, `libdep_alt.rlib`
SHA-256 `f3747c524d9e338f74b1b47c61612e0afeeda5eea6c54179799619146f0e514c`):
compiled from `dep_provider_alt.rs` (`--crate-name=dep_provider`), preserving
`ownerDefPathHash` and both `calleeDefPathHash` fingerprints while changing
`tcx.crate_hash(dep_provider)` (`externalCrateSvh = 9991835327327507104`). -/
noncomputable def depControlRlibSubstituted : DepCaptureBinding :=
  { runId := 22
    sourceSha256Hi := 0xa65859527362b9ed
    ownerDefPathHashHi := 13620298541707722769
    ownerDefPathHashLo := 6145011225190168512
    calleeNonInlineDefPathHashHi := 16703889901102367156
    calleeNonInlineDefPathHashLo := 5774153523600403242
    calleeInlinedDefPathHashHi := 16703889901102367156
    calleeInlinedDefPathHashLo := 10380015184174581091
    externalCrateSvh := 9991835327327507104
    externalCrateSvhMatrixHi := 9991835327327507104
    externalCrateSvhLo := 4490030146421802882
    nonInlineMirAvailable := false
    inlinedMirAvailable := true }

/-- Crate-level binding check requiring exact match of local `sourceSha256`,
`ownerDefPathHash`, `calleeDefPathHash`, and `externalCrateSvh`. -/
noncomputable def AdmissibleDepCrateBinding
    (expectedSvh : Nat) (b : DepCaptureBinding) : Bool :=
  Nat.beq b.sourceSha256Hi depControlRlibOrig.sourceSha256Hi &&
  Nat.beq b.ownerDefPathHashHi depControlRlibOrig.ownerDefPathHashHi &&
  Nat.beq b.ownerDefPathHashLo depControlRlibOrig.ownerDefPathHashLo &&
  Nat.beq b.calleeNonInlineDefPathHashHi depControlRlibOrig.calleeNonInlineDefPathHashHi &&
  Nat.beq b.calleeNonInlineDefPathHashLo depControlRlibOrig.calleeNonInlineDefPathHashLo &&
  Nat.beq b.calleeInlinedDefPathHashHi depControlRlibOrig.calleeInlinedDefPathHashHi &&
  Nat.beq b.calleeInlinedDefPathHashLo depControlRlibOrig.calleeInlinedDefPathHashLo &&
  Nat.beq b.externalCrateSvh expectedSvh

/-- Full capture binding admissibility for a cross-crate call surface: requires both
`AdmissibleDepCrateBinding` and `is_mir_available == true` for every referenced
callee whose body is not separately discharged. -/
noncomputable def AdmissibleDepBodyClosure
    (expectedSvh : Nat) (b : DepCaptureBinding) : Bool :=
  AdmissibleDepCrateBinding expectedSvh b &&
  b.nonInlineMirAvailable &&
  b.inlinedMirAvailable

/-- **Theorem 5 (`FE-F2`)**: On `dep_control_rlib_orig` vs
`dep_control_rlib_substituted`, local `sourceSha256`, `ownerDefPathHash`, and
`calleeDefPathHash` are identical, while `externalCrateSvh` differs
(`16377899976409579846` vs `9991835327327507104` in `out_dep_rlib_orig.json` vs
`out_dep_rlib_substituted.json`), so `AdmissibleDepCrateBinding` rejects the substituted
`.rlib` and `AdmissibleDepBodyClosure` flags missing MIR
(`nonInlineMirAvailable = false`) on `dep_non_inline`. -/
theorem crate_svh_binding_distinguishes_substituted_dep :
    depControlRlibOrig.sourceSha256Hi = depControlRlibSubstituted.sourceSha256Hi ∧
    depControlRlibOrig.ownerDefPathHashHi = depControlRlibSubstituted.ownerDefPathHashHi ∧
    depControlRlibOrig.ownerDefPathHashLo = depControlRlibSubstituted.ownerDefPathHashLo ∧
    depControlRlibOrig.calleeNonInlineDefPathHashHi =
      depControlRlibSubstituted.calleeNonInlineDefPathHashHi ∧
    depControlRlibOrig.calleeNonInlineDefPathHashLo =
      depControlRlibSubstituted.calleeNonInlineDefPathHashLo ∧
    depControlRlibOrig.calleeInlinedDefPathHashHi =
      depControlRlibSubstituted.calleeInlinedDefPathHashHi ∧
    depControlRlibOrig.calleeInlinedDefPathHashLo =
      depControlRlibSubstituted.calleeInlinedDefPathHashLo ∧
    depControlRlibOrig.externalCrateSvh = 16377899976409579846 ∧
    depControlRlibSubstituted.externalCrateSvh = 9991835327327507104 ∧
    depControlRlibOrig.externalCrateSvh ≠ depControlRlibSubstituted.externalCrateSvh ∧
    depControlRlibOrig.externalCrateSvhMatrixHi ≠
      depControlRlibSubstituted.externalCrateSvhMatrixHi ∧
    AdmissibleDepCrateBinding 16377899976409579846 depControlRlibOrig = true ∧
    AdmissibleDepCrateBinding 16377899976409579846 depControlRlibSubstituted = false ∧
    depControlRlibOrig.nonInlineMirAvailable = false ∧
    AdmissibleDepBodyClosure 16377899976409579846 depControlRlibOrig = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro h
    have hbeq :
        Nat.beq depControlRlibOrig.externalCrateSvh depControlRlibOrig.externalCrateSvh =
        Nat.beq depControlRlibOrig.externalCrateSvh depControlRlibSubstituted.externalCrateSvh :=
      congrArg (Nat.beq depControlRlibOrig.externalCrateSvh) h
    change true = false at hbeq
    exact Bool.noConfusion hbeq
  · intro h
    have hbeq :
        Nat.beq depControlRlibOrig.externalCrateSvhMatrixHi
          depControlRlibOrig.externalCrateSvhMatrixHi =
        Nat.beq depControlRlibOrig.externalCrateSvhMatrixHi
          depControlRlibSubstituted.externalCrateSvhMatrixHi :=
      congrArg (Nat.beq depControlRlibOrig.externalCrateSvhMatrixHi) h
    change true = false at hbeq
    exact Bool.noConfusion hbeq

/-! ## 5. Non-Circular Separation of Capture Admission, Producer Correspondence, and `Execution.NoUB` -/

/-- Complete capture binding bundle for an entry point and its referenced callees.
Separates:
- `capturedModelHasUB`: whether the captured MIR model's semantics reaches UB, and
- `entryHasRuntimeUB`: whether the compiled target execution reaches runtime UB. -/
structure CapturedEntrySubject where
  modeRun : CaptureModeRun
  probeRun : ProbeCaptureRun
  depBinding : DepCaptureBinding
  externalCalleeBodiesVerified : Bool
  capturedModelHasUB : Bool := false
  entryHasRuntimeUB : Bool

/-- Full capture binding predicate (`AdmissibleCaptureBinding`): requires
1. Combined hook + `after_analysis` demand capture of `Runtime(PostCleanup)` bodies,
2. Entry-scoped monomorphic completion and const obligation discharge,
3. Exact `externalCrateSvh` binding for external dependencies, and
4. Either `is_mir_available == true` for all referenced callees or a separate
   verified external-crate capture (`externalCalleeBodiesVerified = true`).
Crucially, `AdmissibleCaptureBinding` does NOT inspect `capturedModelHasUB` or
`entryHasRuntimeUB`: structurally admitted unsafe bodies remain representable. -/
noncomputable def AdmissibleCaptureBinding
    (expectedSvh : Nat) (s : CapturedEntrySubject) : Bool :=
  CombinedHookAndDemandCaptures s.modeRun &&
  EntryScopedMonoObligationsHold s.probeRun &&
  AdmissibleDepCrateBinding expectedSvh s.depBinding &&
  ((s.depBinding.nonInlineMirAvailable && s.depBinding.inlinedMirAvailable) ||
   s.externalCalleeBodiesVerified)

/-- Non-circular producer and compilation correspondence boundary: if the capture
satisfies `AdmissibleCaptureBinding`, then the compiled target's runtime UB behavior
(`entryHasRuntimeUB`) matches the captured MIR model's UB behavior
(`capturedModelHasUB`). Producer correspondence alone does NOT assert safety. -/
def ProducerCompilationCorrespondence
    (expectedSvh : Nat) (s : CapturedEntrySubject) : Prop :=
  AdmissibleCaptureBinding expectedSvh s = true →
    s.entryHasRuntimeUB = s.capturedModelHasUB

abbrev EntryExecState : Type := Nat × Bool

noncomputable def initEntryExecState : EntryExecState := (0, false)

def capturedEntryBad (st : EntryExecState) : Prop := st.2 = true

/-- Step relation of the captured MIR model (`capturedModelHasUB`). -/
def capturedModelStep (s : CapturedEntrySubject) (u v : EntryExecState) : Prop :=
  u = initEntryExecState ∧ v = (1, s.capturedModelHasUB)

/-- Step relation of the compiled target entry surface (`entryHasRuntimeUB`). -/
def capturedEntryStep (s : CapturedEntrySubject) (u v : EntryExecState) : Prop :=
  u = initEntryExecState ∧ v = (1, s.entryHasRuntimeUB)

/-- Canonical admitted safe entry capture for `probe_a1_direct_full` with separately
supplied external-callee verification (`capturedModelHasUB = false`). -/
noncomputable def admittedA1EntrySubject : CapturedEntrySubject :=
  { modeRun := runCleanupDefault
    probeRun := probeA1DirectFull
    depBinding := depControlRlibOrig
    externalCalleeBodiesVerified := true
    capturedModelHasUB := false
    entryHasRuntimeUB := false }

/-- Structurally admitted UNSAFE entry capture (`AdmissibleCaptureBinding = true` and
`ProducerCompilationCorrespondence` holds, yet `capturedModelHasUB = true` and
`entryHasRuntimeUB = true`). Demonstrates that capture admission and producer fidelity
do not by themselves imply program safety without a semantic `Execution.NoUB` proof. -/
noncomputable def admittedUnsafeEntrySubject : CapturedEntrySubject :=
  { modeRun := runCleanupDefault
    probeRun := probeA1DirectFull
    depBinding := depControlRlibOrig
    externalCalleeBodiesVerified := true
    capturedModelHasUB := true
    entryHasRuntimeUB := true }

/-- **Theorem 6 (`FE-F2`)**:
1. Both `admittedA1EntrySubject` (safe) and `admittedUnsafeEntrySubject` (unsafe)
   satisfy `AdmissibleCaptureBinding 16377899976409579846 ... = true` and
   `ProducerCompilationCorrespondence`, while `admittedUnsafeEntrySubject` violates
   `Execution.NoUB` (`¬ Execution.NoUB`), demonstrating that capture admission and
   producer correspondence do not smuggle in safety.
2. For any `CapturedEntrySubject`, combining (i) `AdmissibleCaptureBinding`,
   (ii) `ProducerCompilationCorrespondence`, and (iii) a semantic proof of
   `Execution.NoUB` on the captured model (`capturedModelStep s`) transfers
   `Execution.NoUB` to the compiled entry surface (`capturedEntryStep s`). -/
theorem admissible_capture_transfers_entry_safety :
    AdmissibleCaptureBinding 16377899976409579846 admittedA1EntrySubject = true ∧
    AdmissibleCaptureBinding 16377899976409579846 admittedUnsafeEntrySubject = true ∧
    ProducerCompilationCorrespondence 16377899976409579846 admittedUnsafeEntrySubject ∧
    ¬ Execution.NoUB (capturedEntryStep admittedUnsafeEntrySubject)
        capturedEntryBad initEntryExecState ∧
    Execution.NoUB (capturedModelStep admittedA1EntrySubject)
      capturedEntryBad initEntryExecState ∧
    Execution.NoUB (capturedEntryStep admittedA1EntrySubject)
      capturedEntryBad initEntryExecState ∧
    ∀ (expectedSvh : Nat) (s : CapturedEntrySubject),
      AdmissibleCaptureBinding expectedSvh s = true →
      ProducerCompilationCorrespondence expectedSvh s →
      Execution.NoUB (capturedModelStep s) capturedEntryBad initEntryExecState →
      Execution.NoUB (capturedEntryStep s) capturedEntryBad initEntryExecState := by
  have hUnsafeNotNoUB :
      ¬ Execution.NoUB (capturedEntryStep admittedUnsafeEntrySubject)
          capturedEntryBad initEntryExecState := by
    have hReach :
        Execution.Reach (capturedEntryStep admittedUnsafeEntrySubject)
          initEntryExecState (1, true) :=
      Execution.Reach.tail (Execution.Reach.refl initEntryExecState) ⟨rfl, rfl⟩
    exact Execution.bad_prefix_not_noUB (Bad := capturedEntryBad) hReach rfl
  have hModelSafeA1 :
      Execution.NoUB (capturedModelStep admittedA1EntrySubject)
        capturedEntryBad initEntryExecState := by
    apply Execution.invariant_noUB
      (Invariant := fun st : EntryExecState => st.2 = false) rfl
    · intro u v _ hStep
      rcases hStep with ⟨_, hv⟩
      subst hv
      rfl
    · intro st hInv hBad
      exact Bool.noConfusion (Eq.trans (Eq.symm hInv) hBad)
  have hTransfer :
      ∀ (expectedSvh : Nat) (s : CapturedEntrySubject),
        AdmissibleCaptureBinding expectedSvh s = true →
        ProducerCompilationCorrespondence expectedSvh s →
        Execution.NoUB (capturedModelStep s) capturedEntryBad initEntryExecState →
        Execution.NoUB (capturedEntryStep s) capturedEntryBad initEntryExecState := by
    intro expectedSvh s hAdm hCorr hModelNoUB
    have hModelFalse : s.capturedModelHasUB = false := by
      cases hub : s.capturedModelHasUB with
      | false => rfl
      | true =>
        have hReach :
            Execution.Reach (capturedModelStep s)
              initEntryExecState (1, s.capturedModelHasUB) :=
          Execution.Reach.tail (Execution.Reach.refl initEntryExecState) ⟨rfl, rfl⟩
        have hBad : capturedEntryBad (1, s.capturedModelHasUB) := hub
        exact False.elim (hModelNoUB (1, s.capturedModelHasUB) hReach hBad)
    have hTargetFalse : s.entryHasRuntimeUB = false :=
      Eq.trans (hCorr hAdm) hModelFalse
    apply Execution.invariant_noUB
      (Invariant := fun st : EntryExecState => st.2 = false) rfl
    · intro u v _ hStep
      rcases hStep with ⟨_, hv⟩
      subst hv
      exact hTargetFalse
    · intro st hInv hBad
      exact Bool.noConfusion (Eq.trans (Eq.symm hInv) hBad)
  exact ⟨rfl, rfl, (fun _ => rfl), hUnsafeNotNoUB, hModelSafeA1,
    hTransfer 16377899976409579846 admittedA1EntrySubject rfl (fun _ => rfl) hModelSafeA1,
    hTransfer⟩

#print axioms combined_hook_and_demand_captures_all_modes
#print axioms independent_completion_oracle_sound
#print axioms unused_failing_mention_excluded_by_mono_reachability
#print axioms ullbc_elaborated_preserves_unwind_while_llbc_drops_it
#print axioms crate_svh_binding_distinguishes_substituted_dep
#print axioms admissible_capture_transfers_entry_safety

end AnnealResearch.RealCaptureAudit
