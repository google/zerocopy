import AnnealResearch.MirSemanticBoundary

set_option Elab.async false

namespace AnnealResearch.MirSemanticBoundaryControls

open AnnealResearch.MirSemanticBoundary

/-!
# Adversarial Negative Controls for the Candidate MIR Semantic Boundary (`FE-F3`)

This companion module proves six machine-checked negative-control theorems over the
bounded operational models in `AnnealResearch.MirSemanticBoundary`:

1. `drop_condition_mutation_preserves_return_but_faults_or_leaks`: mutating an elaborated
   drop flag (`_20`) preserves the normal return value (`105`) while either faulting with
   a double-drop of an uninitialized field (`¬ Execution.NoUB` at `bb11` / `pc = 4`) or
   leaking a live field destructor (`trace = [2]` instead of `[1, 2]` when `bb11` is skipped).
2. `unwind_edge_omission_matches_completed_return_but_fails_unwind_trace`: omitting
   unwind cleanup edges (modeling Charon's default `cleanup_llbc_elaborated_default.llbc`)
   agrees with `Runtime(PostCleanup)` on normal return (`triggerPanic = false`), but
   leaks `pair.second`'s destructor on unwind (`triggerPanic = true`, `trace = [10, 1]`
   instead of `[10, 1, 2]`).
3. `effect_order_swap_preserves_drop_count_but_violates_destruction_order`: reversing
   struct field drop order (`pair.second` before `pair.first`, yielding `[2, 1]` instead of
   Rust's declaration-order `[1, 2]`) preserves the return value (`105`), `Execution.NoUB`,
   and the aggregate per-tag drop-count pair `(1, 1)` (`AnalysisDropView` from `FE-04` /
   `MirCaptureDialects.lean`), while violating the ordered destruction trace
   (`[2, 1] ≠ [1, 2]`).
4. `default_post_cleanup_without_preserve_ub_loses_place_mention_and_switch_ub`:
   separates `match_wildcard_probe` (`hasPrecedingDerefLoad = false`, `PlaceMention((*_1))`
   only) from `ub_boundary_probe` (`hasPrecedingDerefLoad = true`, `_3 = copy (*_1)` before
   `PlaceMention(_3)`): at default `Runtime(PostCleanup)` (`preserveUb = false, optimizedPhase = false`),
   `RemovePlaceMention` strips `PlaceMention`, losing `ptrValid = false` detection on
   `match_wildcard_probe` while `ub_boundary_probe` retains `_3 = copy (*_1)` until
   dead-store elimination in default `Runtime(Optimized)` (`preserveUb = false, optimizedPhase = true`),
   where both `_3 = copy (*_1)` and `SwitchInt` are eliminated.
5. `optimized_mir_strips_storage_liveness_markers`: capturing `optimized_mir`
   (`MirPhase::Runtime(RuntimePhase::Optimized)`) at default `-C opt-level=0` runs
   `RemoveStorageMarkers` (`mir_opt_level() == 1`), stripping `StorageLive`/`StorageDead`
   and losing dead-local access UB detection in the storage-lifecycle model.
6. `erased_with_retag_flag_conflates_deref_temp_with_user_copy`: illustrative bounded
   alias-invalidation control showing that erasing the `WithRetag` boolean on
   `Rvalue::Use(Operand::Copy(_), WithRetag)` after `Derefer` + `EraseDerefTemps`
   treats synthetic `WithRetag::No` deref-temp copies as `WithRetag::Yes` retags,
   inflating retag counts (`15 -> 16`, `9 -> 11`) and invalidating a protected reader tag
   in the bounded alias model.

*Authored by an AI agent acting on joshlf's behalf.*
-/

theorem not_noUB_of_five_step_bad {S : Type} {f : S → Option S} {isBad : S → Bool}
    {s0 s1 s2 s3 s4 s5 : S}
    (h1 : f s0 = some s1) (h2 : f s1 = some s2) (h3 : f s2 = some s3)
    (h4 : f s3 = some s4) (h5 : f s4 = some s5)
    (hbad : isBad s5 = true) :
    ¬ Execution.NoUB (StepFromFn f) (fun s => isBad s = true) s0 :=
  Execution.bad_prefix_not_noUB
    (Execution.Reach.tail
      (Execution.Reach.tail
        (Execution.Reach.tail
          (Execution.Reach.tail
            (Execution.Reach.tail (Execution.Reach.refl s0) h1) h2) h3) h4) h5)
    hbad

/-!
## Negative Control 1: Drop-Flag Condition Mutation
-/

/-- Adversarial mutation of `elaboratedPartialInitStep true false` that fails to clear
    `dropFlag20` (`_20 := false`) at `pc = 1` (`bb1`) when `pair.first` (`_5.0`) is moved
    into `moved_first` (`_12`). At `pc = 4` (`bb6 -> bb11`), `switchInt(copy _20)` then
    attempts `drop((_5.0))` on the uninitialized field and faults (`bad := true`). -/
noncomputable def mutatedDropFlagTrueStep (s : CleanupState) : Option CleanupState :=
  bif Nat.beq s.pc 1 then
    some { s with
      pc := 2
      firstInit := false
      movedInit := true
      movedTag := s.firstTag
      dropFlag20 := true
      dropFlag21 := true
      trace := s.trace ++ [10] }
  else
    elaboratedPartialInitStep true false s

/-- Adversarial mutation of `elaboratedPartialInitStep false false` that initializes
    `dropFlag20 := false` (`_20 = false`) at `pc = 0` (`bb0`) even though `pair.first` is
    initialized and never moved. At `pc = 4` (`bb6`), `switchInt(copy _20)` skips `bb11`
    (`drop((_5.0))`) and branches directly to `pc = 6` (`bb10: drop((_5.1))`), leaking
    `pair.first`. -/
noncomputable def mutatedDropFlagFalseStep (s : CleanupState) : Option CleanupState :=
  bif Nat.beq s.pc 0 then
    some { s with
      pc := 1
      firstInit := true
      secondInit := true
      firstTag := 1
      secondTag := 2
      dropFlag20 := false
      dropFlag21 := false }
  else
    elaboratedPartialInitStep false false s

/-- Control Theorem 1: Mutating the elaborated drop flag `_20` (`dropFlag20`) preserves
    the normal return value `105` in both directions, but:
    - leaving `dropFlag20 = true` after moving `pair.first` causes an uninitialized/double-drop
      fault at `pc = 4` (`bb6 -> bb11`, `¬ Execution.NoUB`), and
    - setting `dropFlag20 = false` when `pair.first` was not moved skips `bb11` and leaks
      `pair.first`'s destructor (`trace = [2]` instead of `[1, 2]`). -/
theorem drop_condition_mutation_preserves_return_but_faults_or_leaks :
    (runSteps mutatedDropFlagTrueStep 8 initialCleanupState).retVal =
      (runSteps (elaboratedPartialInitStep true false) 8 initialCleanupState).retVal ∧
    ¬ Execution.NoUB
      (StepFromFn mutatedDropFlagTrueStep)
      (fun s => s.bad = true)
      initialCleanupState ∧
    (runSteps mutatedDropFlagFalseStep 8 initialCleanupState).retVal =
      (runSteps (elaboratedPartialInitStep false false) 8 initialCleanupState).retVal ∧
    Execution.NoUB
      (StepFromFn mutatedDropFlagFalseStep)
      (fun s => s.bad = true)
      initialCleanupState ∧
    (runSteps mutatedDropFlagFalseStep 8 initialCleanupState).trace = [2] ∧
    (runSteps (elaboratedPartialInitStep false false) 8 initialCleanupState).trace = [1, 2] ∧
    (runSteps mutatedDropFlagFalseStep 8 initialCleanupState).trace ≠
      (runSteps (elaboratedPartialInitStep false false) 8 initialCleanupState).trace := by
  refine ⟨rfl, ?_, rfl, ?_, rfl, rfl, ?_⟩
  · exact not_noUB_of_five_step_bad rfl rfl rfl rfl rfl rfl
  · exact noUB_of_boundedAllSafe (fuel := 8) rfl
  · intro h
    change ([2] : List Nat) = [1, 2] at h
    injection h with hhd _
    injection hhd with h0
    exact Nat.noConfusion h0

#print axioms drop_condition_mutation_preserves_return_but_faults_or_leaks

/-!
## Negative Control 2: Unwind Cleanup Edge Omission (`cleanup_llbc_elaborated_default.llbc`)
-/

/-- Transition function modeling Charon's reconstructed `cleanup_llbc_elaborated_default.llbc`,
    where `on_unwind` cleanup edges on calls/drops and `UnwindResume` blocks (`bb16`, `bb15`,
    `bb14`, `bb7`) are omitted: when `may_unwind_op` unwinds at `pc = 3` (`bb5`,
    `triggerPanic = true`), execution terminates immediately in `.unwindResume` (`pc = 7`)
    without running the unwind drop ladder at `pc = 5 -> 8`. -/
noncomputable def llbcOmittedUnwindStep (moveFirstEarly triggerPanic : Bool) (s : CleanupState) :
    Option CleanupState :=
  bif Nat.beq s.pc 3 then
    bif triggerPanic then
      some { s with pc := 7, outcome := .unwindResume }
    else
      some { s with pc := 4, retVal := 105 }
  else
    elaboratedPartialInitStep moveFirstEarly triggerPanic s

/-- Control Theorem 2: Omitting unwind cleanup edges matches `Runtime(PostCleanup)`
    on completed normal returns (`triggerPanic = false`), producing the exact same
    observation `{ trace := [10, 1, 2], retVal := 105, outcome := .normalReturn }`,
    but diverges on panicking executions (`triggerPanic = true`) by leaking `pair.second`
    (`trace = [10, 1]` instead of `[10, 1, 2]`). -/
theorem unwind_edge_omission_matches_completed_return_but_fails_unwind_trace :
    (runSteps (llbcOmittedUnwindStep true false) 8 initialCleanupState).obs =
      (runSteps (elaboratedPartialInitStep true false) 8 initialCleanupState).obs ∧
    (runSteps (llbcOmittedUnwindStep true true) 8 initialCleanupState).trace = [10, 1] ∧
    (runSteps (elaboratedPartialInitStep true true) 8 initialCleanupState).trace = [10, 1, 2] ∧
    (runSteps (llbcOmittedUnwindStep true true) 8 initialCleanupState).trace ≠
      (runSteps (elaboratedPartialInitStep true true) 8 initialCleanupState).trace := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  change ([10, 1] : List Nat) = [10, 1, 2] at h
  injection h with _ h1
  injection h1 with _ h2
  cases h2

#print axioms unwind_edge_omission_matches_completed_return_but_fails_unwind_trace

/-!
## Negative Control 3: Wrong Reverse-Declaration Field Drop Order vs. Aggregate Drop Counts
-/

/-- Adversarial wrong-order transition function for `partial_init_move_cleanup false false`
    that reverses the `bb6 -> bb11 (drop _5.0) -> bb10 (drop _5.1) -> bb8` field drop ladder
    so that `pair.second` (`secondTag = 2` at `pc = 4`) is dropped BEFORE `pair.first`
    (`firstTag = 1` at `pc = 6`), producing `[2, 1]` instead of Rust's declaration-order
    struct field drop sequence `[1, 2]`. -/
noncomputable def swappedFieldDropOrderStep (s : CleanupState) : Option CleanupState :=
  bif Nat.beq s.pc 4 then
    bif s.secondInit then
      some { s with
        pc := 6
        secondInit := false
        trace := s.trace ++ [s.secondTag] }
    else
      some { s with pc := 7, bad := true }
  else bif Nat.beq s.pc 6 then
    bif s.dropFlag20 then
      bif s.firstInit then
        some { s with
          pc := 7
          firstInit := false
          dropFlag20 := false
          trace := s.trace ++ [s.firstTag]
          outcome := .normalReturn }
      else
        some { s with pc := 7, bad := true }
    else
      some { s with pc := 7, outcome := .normalReturn }
  else
    elaboratedPartialInitStep false false s

/-- Counts occurrences of destructor `tag` in an effect trace. -/
noncomputable def countTag (tag : Nat) (xs : List Nat) : Nat :=
  List.recOn xs 0 (fun x _ ih => bif Nat.beq x tag then ih + 1 else ih)

/-- Aggregate drop-count summary `(drops_of_first, drops_of_second)` corresponding to
    `FE-04`'s `AnalysisDropView = (Nat × Nat)` in `MirCaptureDialects.lean`. -/
noncomputable def dropCountSummary (trace : List Nat) : Nat × Nat :=
  (countTag 1 trace, countTag 2 trace)

/-- Control Theorem 3: Reversing aggregate struct field drop order so `pair.second` (tag `2`)
    is dropped before `pair.first` (tag `1`) preserves the return value (`105`), normal return
    status, `Execution.NoUB`, and the per-tag drop-count pair `(1, 1)` used by `FE-04`'s
    `AnalysisDropView`, yet violates Rust's declaration-order field destruction trace
    (`[2, 1] ≠ [1, 2]`). -/
theorem effect_order_swap_preserves_drop_count_but_violates_destruction_order :
    (runSteps swappedFieldDropOrderStep 8 initialCleanupState).retVal =
      (runSteps (elaboratedPartialInitStep false false) 8 initialCleanupState).retVal ∧
    Execution.NoUB
      (StepFromFn swappedFieldDropOrderStep)
      (fun s => s.bad = true)
      initialCleanupState ∧
    dropCountSummary (runSteps swappedFieldDropOrderStep 8 initialCleanupState).trace = (1, 1) ∧
    dropCountSummary (runSteps (elaboratedPartialInitStep false false) 8 initialCleanupState).trace = (1, 1) ∧
    (runSteps swappedFieldDropOrderStep 8 initialCleanupState).trace = [2, 1] ∧
    (runSteps (elaboratedPartialInitStep false false) 8 initialCleanupState).trace = [1, 2] ∧
    (runSteps swappedFieldDropOrderStep 8 initialCleanupState).trace ≠
      (runSteps (elaboratedPartialInitStep false false) 8 initialCleanupState).trace := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · exact noUB_of_boundedAllSafe (fuel := 8) rfl
  · intro h
    change ([2, 1] : List Nat) = [1, 2] at h
    injection h with h1 _
    injection h1 with h0
    exact Nat.noConfusion h0

#print axioms effect_order_swap_preserves_drop_count_but_violates_destruction_order

/-!
## Negative Control 4: Phase-Accurate Loss of `PlaceMention` (`match_wildcard_probe`) vs. `_3 = copy (*_1)` and `SwitchInt` (`ub_boundary_probe`)
-/

/-- Transition function for `ub_boundary_probe` (`let _ = unsafe { *ptr };`), where
    `Built` and `Runtime(PostCleanup)` emit `_3 = copy (*_1)` before `PlaceMention(_3)`.
    Even when `RemovePlaceMention` strips `PlaceMention(_3)` at default `Runtime(PostCleanup)`
    (`preserveUb = false, optimizedPhase = false`), the dead load `_3 = copy (*_1)` remains
    present (`!s.optimizedPhase`) and still checks `s.ptrValid`, and is only eliminated at
    default `Runtime(Optimized)` (`preserveUb = false, optimizedPhase = true`) after
    dead-store elimination removes `_3 = copy (*_1)`. -/
noncomputable def ubBoundaryWithLoadStep (s : UbProbeState) : Option UbProbeState :=
  bif Nat.beq s.pc 0 then
    bif (s.preserveUb || !s.optimizedPhase) then
      bif s.ptrValid then
        some { s with pc := 1, placeMentionChecked := s.preserveUb }
      else
        some { s with pc := 3, placeMentionChecked := s.preserveUb, bad := true }
    else
      some { s with pc := 1, placeMentionChecked := false }
  else
    ubProbeStep s

/-- Control Theorem 4:
    - On `match_wildcard_probe` (`ubProbeStep`, which emits `PlaceMention((*_1))` without
      `_3 = copy (*_1)`), default `Runtime(PostCleanup)` (`preserveUb = false, optimizedPhase = false`)
      strips `PlaceMention((*_1))` (`placeMentionChecked = false`), so `ptrValid = false`
      spuriously satisfies `Execution.NoUB` right at `Runtime(PostCleanup)`.
    - On `ub_boundary_probe` (`ubBoundaryWithLoadStep`, which emits `_3 = copy (*_1)` before
      `PlaceMention(_3)`), default `Runtime(PostCleanup)` strips `PlaceMention(_3)`
      (`placeMentionChecked = false`) but retains `_3 = copy (*_1)` (so `ptrValid = false`
      still triggers `¬ Execution.NoUB` at `Runtime(PostCleanup)`), and only loses both
      `_3 = copy (*_1)` and `SwitchInt` at default `Runtime(Optimized)` (`preserveUb = false,
      optimizedPhase = true`).
    - Capturing `Runtime(PostCleanup)` with `-Z mir-preserve-ub`
      (`preserveUb = true, optimizedPhase = false`) rejects both faults across both probes. -/
theorem default_post_cleanup_without_preserve_ub_loses_place_mention_and_switch_ub :
    Execution.NoUB
      (StepFromFn ubProbeStep)
      (fun s => s.bad = true)
      (initialUbProbeState false false false true) ∧
    ¬ Execution.NoUB
      (StepFromFn ubBoundaryWithLoadStep)
      (fun s => s.bad = true)
      (initialUbProbeState false false false true) ∧
    Execution.NoUB
      (StepFromFn ubBoundaryWithLoadStep)
      (fun s => s.bad = true)
      (initialUbProbeState false true false true) ∧
    (runSteps ubProbeStep 5 (initialUbProbeState false false false true)).placeMentionChecked = false ∧
    (runSteps ubProbeStep 5 (initialUbProbeState false false false true)).switchDiscrChecked = true ∧
    ¬ Execution.NoUB
      (StepFromFn ubProbeStep)
      (fun s => s.bad = true)
      (initialUbProbeState false false true false) ∧
    Execution.NoUB
      (StepFromFn ubProbeStep)
      (fun s => s.bad = true)
      (initialUbProbeState false true false true) ∧
    Execution.NoUB
      (StepFromFn ubProbeStep)
      (fun s => s.bad = true)
      (initialUbProbeState false true true false) ∧
    (runSteps ubProbeStep 5 (initialUbProbeState false true false false)).outcome = .normalReturn ∧
    (runSteps ubProbeStep 5 (initialUbProbeState false true false false)).placeMentionChecked = false ∧
    (runSteps ubProbeStep 5 (initialUbProbeState false true false false)).switchDiscrChecked = false ∧
    ¬ Execution.NoUB
      (StepFromFn ubProbeStep)
      (fun s => s.bad = true)
      (initialUbProbeState true false false true) ∧
    ¬ Execution.NoUB
      (StepFromFn ubProbeStep)
      (fun s => s.bad = true)
      (initialUbProbeState true false true false) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · exact noUB_of_boundedAllSafe (fuel := 5) rfl
  · exact not_noUB_of_one_step_bad rfl rfl
  · exact noUB_of_boundedAllSafe (fuel := 5) rfl
  · exact not_noUB_of_two_step_bad rfl rfl rfl
  · exact noUB_of_boundedAllSafe (fuel := 5) rfl
  · exact noUB_of_boundedAllSafe (fuel := 5) rfl
  · exact not_noUB_of_one_step_bad rfl rfl
  · exact not_noUB_of_two_step_bad rfl rfl rfl

#print axioms default_post_cleanup_without_preserve_ub_loses_place_mention_and_switch_ub

/-!
## Negative Control 5: `optimized_mir` (`RemoveStorageMarkers`) Loses Dead-Local UB Detection
-/

/-- Multi-step operational state for a local variable storage-liveness lifecycle
    (`StorageLive(_x)` -> `Assign(_x, 42)` -> `StorageDead(_x)` -> dead-local access `Use(_x)`). -/
structure StorageMarkerState where
  pc : Nat
  retainStorageMarkers : Bool
  localAllocated : Bool
  localValue : Nat
  outcome : ExecOutcome
  bad : Bool

noncomputable def initialStorageMarkerState (retainStorageMarkers : Bool) : StorageMarkerState :=
  { pc := 0
    retainStorageMarkers := retainStorageMarkers
    localAllocated := false
    localValue := 0
    outcome := .running
    bad := false }

/-- Multi-step transition function comparing `Runtime(PostCleanup)` (`retainStorageMarkers = true`,
    preserving `StorageLive` and `StorageDead` markers: `14/14` in `partial_init_move_cleanup`,
    `17/17` in `partial_field_reinit_cleanup`, `3/3` in `ub_boundary_probe`) against
    `Runtime(Optimized)` (`retainStorageMarkers = false`, where `RemoveStorageMarkers` runs at
    default `-C opt-level=0` because `mir_opt_level() == 1` and strips all `StorageLive` and
    `StorageDead` markers to `0/0`). -/
noncomputable def storageLifecycleStep (s : StorageMarkerState) : Option StorageMarkerState :=
  bif Nat.beq s.pc 0 then
    some { s with pc := 1, localAllocated := true }
  else bif Nat.beq s.pc 1 then
    bif s.localAllocated then
      some { s with pc := 2, localValue := 42 }
    else
      some { s with pc := 4, bad := true }
  else bif Nat.beq s.pc 2 then
    bif s.retainStorageMarkers then
      some { s with pc := 3, localAllocated := false }
    else
      some { s with pc := 3, localAllocated := true }
  else bif Nat.beq s.pc 3 then
    bif s.localAllocated then
      some { s with pc := 4, outcome := .normalReturn }
    else
      some { s with pc := 4, bad := true }
  else
    none

/-- Control Theorem 5: Capturing `Runtime(PostCleanup)` (`retainStorageMarkers = true`)
    rejects a dead-local access after `StorageDead` (`¬ Execution.NoUB`), whereas capturing
    `Runtime(Optimized)` (`retainStorageMarkers = false`, after `RemoveStorageMarkers`)
    strips `StorageDead` and spuriously admits the dead-local access (`Execution.NoUB`). -/
theorem optimized_mir_strips_storage_liveness_markers :
    ¬ Execution.NoUB
      (StepFromFn storageLifecycleStep)
      (fun s => s.bad = true)
      (initialStorageMarkerState true) ∧
    Execution.NoUB
      (StepFromFn storageLifecycleStep)
      (fun s => s.bad = true)
      (initialStorageMarkerState false) ∧
    (runSteps storageLifecycleStep 6 (initialStorageMarkerState false)).outcome = .normalReturn := by
  refine ⟨?_, ?_, rfl⟩
  · exact not_noUB_of_four_step_bad rfl rfl rfl rfl rfl
  · exact noUB_of_boundedAllSafe (fuel := 6) rfl

#print axioms optimized_mir_strips_storage_liveness_markers

/-!
## Negative Control 6: Illustrative Alias-Invalidation Model for `WithRetag` (`Derefer` + `EraseDerefTemps`)
-/

/-- Bounded illustrative operational state tracking `Rvalue::Use(Operand::Copy(_), WithRetag)`
    execution after `Derefer` (`deref_separator.rs`) and `EraseDerefTemps` (`erase_deref_temps.rs`).
    Models a protected sibling/reader tag (`protectedReaderTagAlive`) that remains valid across
    synthetic `WithRetag::No` deref-temp copies (`_19 = no_retag copy (_12.1: &mut EffectLog)`),
    but is invalidated if erasing `WithRetag` treats those synthetic copies as `WithRetag::Yes`
    mutable retags. -/
structure RetagTraceState where
  pc : Nat
  preserveWithRetagFlag : Bool
  userCopyCount : Nat
  derefTempCopyCount : Nat
  retagsEmitted : Nat
  protectedReaderTagAlive : Bool
  outcome : ExecOutcome
  bad : Bool

noncomputable def initialRetagTraceState (preserveWithRetagFlag : Bool) (userCopyCount derefTempCopyCount : Nat) :
    RetagTraceState :=
  { pc := 0
    preserveWithRetagFlag := preserveWithRetagFlag
    userCopyCount := userCopyCount
    derefTempCopyCount := derefTempCopyCount
    retagsEmitted := 0
    protectedReaderTagAlive := false
    outcome := .running
    bad := false }

/-- Illustrative 3-step transition modeling `WithRetag::Yes` vs `WithRetag::No`:
    - Step `pc = 0 -> 1`: executes `userCopyCount` user copies carrying `WithRetag::Yes`
      and establishes an active protected tag (`protectedReaderTagAlive := true`).
    - Step `pc = 1 -> 2`: executes `derefTempCopyCount` synthetic `LocalInfo::DerefTemp` copies
      lowered by `EraseDerefTemps` from `Rvalue::CopyForDeref` to
      `Rvalue::Use(Operand::Copy(_), WithRetag::No)`:
      - When `preserveWithRetagFlag = true`, `WithRetag::No` performs a tag-preserving copy
        without emitting a retag, leaving `protectedReaderTagAlive = true`.
      - When `preserveWithRetagFlag = false`, erasing `WithRetag` conflates `WithRetag::No`
        with `WithRetag::Yes`, emitting `derefTempCopyCount` extra retags and invalidating
        `protectedReaderTagAlive` whenever `derefTempCopyCount > 0`.
    - Step `pc = 2 -> 3`: reads through the protected tag; succeeds with `.normalReturn` iff
      `protectedReaderTagAlive = true`, and faults (`bad := true`) if the tag was invalidated. -/
noncomputable def retagCopyStep (s : RetagTraceState) : Option RetagTraceState :=
  bif Nat.beq s.pc 0 then
    some { s with
      pc := 1
      retagsEmitted := s.userCopyCount
      protectedReaderTagAlive := true }
  else bif Nat.beq s.pc 1 then
    bif s.preserveWithRetagFlag then
      some { s with pc := 2 }
    else
      some { s with
        pc := 2
        retagsEmitted := s.retagsEmitted + s.derefTempCopyCount
        protectedReaderTagAlive := Nat.beq s.derefTempCopyCount 0 }
  else bif Nat.beq s.pc 2 then
    bif s.protectedReaderTagAlive then
      some { s with pc := 3, outcome := .normalReturn }
    else
      some { s with pc := 3, bad := true }
  else
    none

/-- Control Theorem 6: On the empirical `Runtime(PostCleanup)` copy counts of
    `partial_init_move_cleanup` (`15` `WithRetag::Yes`, `1` `WithRetag::No`) and
    `partial_field_reinit_cleanup` (`9` `WithRetag::Yes`, `2` `WithRetag::No`), preserving
    the `WithRetag` boolean (`preserveWithRetagFlag = true`) keeps `protectedReaderTagAlive = true`
    and satisfies `Execution.NoUB` with exact user retag counts (`15` and `9`), whereas
    erasing `WithRetag` (`preserveWithRetagFlag = false`) inflates retag counts (`16` and `11`),
    invalidates `protectedReaderTagAlive` at `pc = 1`, and faults on the subsequent read at
    `pc = 2` (`¬ Execution.NoUB`). -/
theorem erased_with_retag_flag_conflates_deref_temp_with_user_copy :
    Execution.NoUB
      (StepFromFn retagCopyStep)
      (fun s => s.bad = true)
      (initialRetagTraceState true 15 1) ∧
    (runSteps retagCopyStep 4 (initialRetagTraceState true 15 1)).retagsEmitted = 15 ∧
    ¬ Execution.NoUB
      (StepFromFn retagCopyStep)
      (fun s => s.bad = true)
      (initialRetagTraceState false 15 1) ∧
    (runSteps retagCopyStep 4 (initialRetagTraceState false 15 1)).retagsEmitted = 16 ∧
    Execution.NoUB
      (StepFromFn retagCopyStep)
      (fun s => s.bad = true)
      (initialRetagTraceState true 9 2) ∧
    (runSteps retagCopyStep 4 (initialRetagTraceState true 9 2)).retagsEmitted = 9 ∧
    ¬ Execution.NoUB
      (StepFromFn retagCopyStep)
      (fun s => s.bad = true)
      (initialRetagTraceState false 9 2) ∧
    (runSteps retagCopyStep 4 (initialRetagTraceState false 9 2)).retagsEmitted = 11 := by
  refine ⟨?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl⟩
  · exact noUB_of_boundedAllSafe (fuel := 4) rfl
  · exact not_noUB_of_three_step_bad rfl rfl rfl rfl
  · exact noUB_of_boundedAllSafe (fuel := 4) rfl
  · exact not_noUB_of_three_step_bad rfl rfl rfl rfl

#print axioms erased_with_retag_flag_conflates_deref_temp_with_user_copy

end AnnealResearch.MirSemanticBoundaryControls
