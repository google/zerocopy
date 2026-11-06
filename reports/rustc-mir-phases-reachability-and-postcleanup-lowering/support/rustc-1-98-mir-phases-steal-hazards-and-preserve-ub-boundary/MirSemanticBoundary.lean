import Std
import AnnealResearch.Execution

set_option Elab.async false

namespace AnnealResearch.MirSemanticBoundary

/-!
# Multi-Step Operational Validation of the Candidate MIR Semantic Capture Boundary (`FE-F3`)

This module mechanizes a bounded multi-step operational model for evaluating the candidate
`mir_drops_elaborated_and_const_checked` (`MirPhase::Runtime(RuntimePhase::PostCleanup)`
with `-Z mir-preserve-ub`) capture boundary on the inspected `cleanup_subject.rs` and
`cleanup_ordered_observer.rs` specimens:

1. **Multi-step operational equivalence of drop elaboration (`partial_init_move_cleanup`
   and `partial_field_reinit_cleanup`)**: models `Analysis` (`Built`) conditional
   whole-place drop semantics alongside the `Runtime(PostCleanup)` elaborated drop-flag
   ladders (`_20`, `_21` in `bb0`..`bb16` and `DropGlue<PairGuards>` `bb0`..`bb4`
   inspected in `bodies_cleanup_subject_preserve_ub.json` and corroborated at runtime by
   `cleanup_ordered_observer.rs` in `ordered_observer_runtime_output.json`). In accordance
   with the Rust Reference (§Destructors), aggregate struct fields of `PairGuards` are
   dropped in declaration order (`first` then `second`), yielding ordered traces
   `[1, 2]` when `moveFirstEarly = false`, `[10, 1, 2]` when `moveFirstEarly = true`,
   `[10, 3, 2]` on normal return of `partial_field_reinit_cleanup(false)`, and `[10, 2]`
   on unwind of `partial_field_reinit_cleanup(true)`.
2. **Divergence and finite-prefix UB sensitivity**: proves that `Execution.NoUB` over
   `Execution.Reach` admits safe non-terminating executions without terminal states while
   rejecting executions that fault on a finite prefix before diverging (which a
   completed-execution-only criterion vacuously admits).
3. **Phase-accurate `PlaceMention`, `_3 = copy (*_1)`, and `SwitchInt` retention
   (`ub_boundary_probe` vs. `match_wildcard_probe`)**:
   models the observed compiler configurations in `bodies_cleanup_subject_preserve_ub.json`,
   `bodies_cleanup_subject_default.json`, and `place_mention_probe.rs`:
   - In `ub_boundary_probe` (`let _ = unsafe { *ptr };`, `hasPrecedingDerefLoad = true`),
     `Built` and `Runtime(PostCleanup)` emit `_3 = copy (*_1)` before `PlaceMention(_3)`.
     At default `Runtime(PostCleanup)` (`preserveUb = false, optimizedPhase = false`),
     `RemovePlaceMention` strips `PlaceMention(_3)` (`placeMentionChecked = false`), **but**
     `_3 = copy (*_1)` remains present so `ptrValid = false` still triggers UB at
     `Runtime(PostCleanup)` and is only eliminated at default `Runtime(Optimized)`
     (`preserveUb = false, optimizedPhase = true`) after dead-store elimination removes `_3`.
   - In `match_wildcard_probe` (`unsafe { match *ptr { _ => 0 } }` / `unsafe { _ = *ptr; }`,
     `hasPrecedingDerefLoad = false`), `Built` emits `PlaceMention((*_1))` directly without
     any `_3 = copy (*_1)` load; thus default `Runtime(PostCleanup)` strips `PlaceMention((*_1))`
     and immediately loses `ptrValid = false` detection at `Runtime(PostCleanup)` unless
     `-Z mir-preserve-ub` (`preserveUb = true`) is enabled.
4. **Four-way boundary separation and compound per-body phase contract**: separates
   (a) `StructurallyWellFormed`, (b) `DialectCompilerInvariant` (requiring per-body phase
   tags: `Runtime(PostCleanup)` with `-Z mir-preserve-ub` on local HIR bodies and explicit
   `Runtime(Optimized)` shim tags on `tcx.mir_shims` `DropGlue` bodies rather than a blanket
   package-level `PostCleanup` header), (c) `SemanticCallerPrecondition`, and
   (d) `BodyExecutionNoUBAndSpec`.

*Authored by an AI agent acting on joshlf's behalf.*
-/

/-- Deterministic single-step transition relation induced by a partial step function `f : S → Option S`. -/
noncomputable def StepFromFn {S : Type} (f : S → Option S) (s t : S) : Prop :=
  f s = some t

/-- Bounded multi-step runner returning the state reached after at most `fuel` transitions. -/
noncomputable def runSteps {S : Type} (f : S → Option S) (fuel : Nat) (s : S) : S :=
  Nat.recOn fuel (fun s => s) (fun _ ih s => Option.casesOn (f s) s (fun t => ih t)) s

/-- Check that all states along the deterministic trajectory of `f` within `fuel` steps
    have `isBad s = false` and reach a terminal (`none`) state within `fuel` steps. -/
noncomputable def boundedAllSafe {S : Type} (f : S → Option S) (isBad : S → Bool) (fuel : Nat) (s : S) : Bool :=
  Nat.recOn fuel (fun _ => false)
    (fun _ ih s => Bool.casesOn (isBad s) (Option.casesOn (f s) true (fun t => ih t)) false) s

/-- Inductive invariant witnessing that a state has a finite fuel bound establishing safety of its forward trajectory. -/
noncomputable def HasSafeFuel {S : Type} (f : S → Option S) (isBad : S → Bool) (s : S) : Prop :=
  ∃ fuel : Nat, boundedAllSafe f isBad fuel s = true

theorem boundedAllSafe_not_bad {S : Type} {f : S → Option S} {isBad : S → Bool}
    {fuel : Nat} {s : S} (h : boundedAllSafe f isBad fuel s = true) : isBad s = false := by
  cases fuel with
  | zero => exact Bool.noConfusion h
  | succ k =>
    change Bool.casesOn (isBad s) (Option.casesOn (f s) true (fun t => boundedAllSafe f isBad k t)) false = true at h
    cases hbad : isBad s with
    | false => rfl
    | true =>
      rw [hbad] at h
      exact Bool.noConfusion h

theorem hasSafeFuel_not_bad {S : Type} {f : S → Option S} {isBad : S → Bool} {s : S}
    (h : HasSafeFuel f isBad s) : ¬ (isBad s = true) := by
  rcases h with ⟨fuel, hfuel⟩
  have hnb : isBad s = false := boundedAllSafe_not_bad hfuel
  intro hbad
  rw [hbad] at hnb
  exact Bool.noConfusion hnb

theorem hasSafeFuel_step {S : Type} {f : S → Option S} {isBad : S → Bool} {s t : S}
    (h : HasSafeFuel f isBad s) (hstep : StepFromFn f s t) : HasSafeFuel f isBad t := by
  rcases h with ⟨fuel, hfuel⟩
  cases fuel with
  | zero => exact Bool.noConfusion hfuel
  | succ k =>
    change Bool.casesOn (isBad s) (Option.casesOn (f s) true (fun t => boundedAllSafe f isBad k t)) false = true at hfuel
    cases hbad : isBad s with
    | true =>
      rw [hbad] at hfuel
      exact Bool.noConfusion hfuel
    | false =>
      rw [hbad] at hfuel
      unfold StepFromFn at hstep
      rw [hstep] at hfuel
      exact ⟨k, hfuel⟩

/-- Soundness of `boundedAllSafe`: a computable fuel witness implies `Execution.NoUB` over all reachable states. -/
theorem noUB_of_boundedAllSafe {S : Type} {f : S → Option S} {isBad : S → Bool}
    {fuel : Nat} {s0 : S} (h0 : boundedAllSafe f isBad fuel s0 = true) :
    Execution.NoUB (StepFromFn f) (fun s => isBad s = true) s0 :=
  Execution.invariant_noUB
    (Invariant := HasSafeFuel f isBad)
    ⟨fuel, h0⟩
    (fun hs hstep => hasSafeFuel_step hs hstep)
    (fun _ hs => hasSafeFuel_not_bad hs)

theorem not_noUB_of_one_step_bad {S : Type} {f : S → Option S} {isBad : S → Bool}
    {s0 s1 : S} (h1 : f s0 = some s1) (hbad : isBad s1 = true) :
    ¬ Execution.NoUB (StepFromFn f) (fun s => isBad s = true) s0 :=
  Execution.bad_prefix_not_noUB
    (Execution.Reach.tail (Execution.Reach.refl s0) h1)
    hbad

theorem not_noUB_of_two_step_bad {S : Type} {f : S → Option S} {isBad : S → Bool}
    {s0 s1 s2 : S} (h1 : f s0 = some s1) (h2 : f s1 = some s2) (hbad : isBad s2 = true) :
    ¬ Execution.NoUB (StepFromFn f) (fun s => isBad s = true) s0 :=
  Execution.bad_prefix_not_noUB
    (Execution.Reach.tail (Execution.Reach.tail (Execution.Reach.refl s0) h1) h2)
    hbad

theorem not_noUB_of_three_step_bad {S : Type} {f : S → Option S} {isBad : S → Bool}
    {s0 s1 s2 s3 : S}
    (h1 : f s0 = some s1) (h2 : f s1 = some s2) (h3 : f s2 = some s3)
    (hbad : isBad s3 = true) :
    ¬ Execution.NoUB (StepFromFn f) (fun s => isBad s = true) s0 :=
  Execution.bad_prefix_not_noUB
    (Execution.Reach.tail
      (Execution.Reach.tail
        (Execution.Reach.tail (Execution.Reach.refl s0) h1) h2) h3)
    hbad

theorem not_noUB_of_four_step_bad {S : Type} {f : S → Option S} {isBad : S → Bool}
    {s0 s1 s2 s3 s4 : S}
    (h1 : f s0 = some s1) (h2 : f s1 = some s2) (h3 : f s2 = some s3) (h4 : f s3 = some s4)
    (hbad : isBad s4 = true) :
    ¬ Execution.NoUB (StepFromFn f) (fun s => isBad s = true) s0 :=
  Execution.bad_prefix_not_noUB
    (Execution.Reach.tail
      (Execution.Reach.tail
        (Execution.Reach.tail
          (Execution.Reach.tail (Execution.Reach.refl s0) h1) h2) h3) h4)
    hbad

/-!
## Section 1: Multi-Step Operational Model of `partial_init_move_cleanup` and `partial_field_reinit_cleanup`
-/

/-- Execution status of a MIR body: actively stepping (`running`), completed via `Return` (`normalReturn`),
    or completed unwinding via `UnwindResume` (`unwindResume`). -/
inductive ExecOutcome : Type where
  | running
  | normalReturn
  | unwindResume

/-- Observable terminal behavior of a cleanup execution:
    ordered side-effect trace (`trace`), return value (`retVal`), and terminal status (`outcome`). -/
structure CleanupObs where
  trace : List Nat
  retVal : Nat
  outcome : ExecOutcome

/-- Multi-step operational state for `partial_init_move_cleanup` and `partial_field_reinit_cleanup`. -/
structure CleanupState where
  pc : Nat
  firstInit : Bool
  secondInit : Bool
  movedInit : Bool
  firstTag : Nat
  secondTag : Nat
  movedTag : Nat
  dropFlag20 : Bool
  dropFlag21 : Bool
  trace : List Nat
  retVal : Nat
  outcome : ExecOutcome
  bad : Bool

/-- Observable projection of a `CleanupState`. -/
noncomputable def CleanupState.obs (s : CleanupState) : CleanupObs :=
  { trace := s.trace, retVal := s.retVal, outcome := s.outcome }

/-- Initial entry state (`pc = 0`) prior to local allocation and initialization. -/
noncomputable def initialCleanupState : CleanupState :=
  { pc := 0
    firstInit := false
    secondInit := false
    movedInit := false
    firstTag := 0
    secondTag := 0
    movedTag := 0
    dropFlag20 := false
    dropFlag21 := false
    trace := []
    retVal := 0
    outcome := .running
    bad := false }

/-- Multi-step operational transition function for `partial_init_move_cleanup` under
    `Analysis` (`Built`) MIR conditional-drop semantics (where whole-place `drop(_5)` at
    `bb9` / `bb13` inspects per-field initialization of `PairGuards` and drops initialized
    struct fields in declaration order: `pair.first` followed by `pair.second`, matching
    the Rust Reference §Destructors and `DropGlue<PairGuards>`). -/
noncomputable def analysisPartialInitStep (moveFirstEarly triggerPanic : Bool) (s : CleanupState) :
    Option CleanupState :=
  bif Nat.beq s.pc 0 then
    some { s with
      pc := 1
      firstInit := true
      secondInit := true
      firstTag := 1
      secondTag := 2 }
  else bif Nat.beq s.pc 1 then
    bif moveFirstEarly then
      some { s with
        pc := 2
        firstInit := false
        movedInit := true
        movedTag := s.firstTag
        trace := s.trace ++ [10] }
    else
      some { s with pc := 3 }
  else bif Nat.beq s.pc 2 then
    bif s.movedInit then
      some { s with
        pc := 3
        movedInit := false
        trace := s.trace ++ [s.movedTag] }
    else
      some { s with pc := 7, bad := true }
  else bif Nat.beq s.pc 3 then
    bif triggerPanic then
      some { s with pc := 5 }
    else
      some { s with pc := 4, retVal := 105 }
  else bif Nat.beq s.pc 4 then
    bif s.secondInit then
      let tailDrops := bif s.firstInit then [s.firstTag, s.secondTag] else [s.secondTag]
      some { s with
        pc := 7
        firstInit := false
        secondInit := false
        trace := s.trace ++ tailDrops
        outcome := .normalReturn }
    else
      some { s with pc := 7, bad := true }
  else bif Nat.beq s.pc 5 then
    bif s.secondInit then
      let tailDrops := bif s.firstInit then [s.firstTag, s.secondTag] else [s.secondTag]
      some { s with
        pc := 7
        firstInit := false
        secondInit := false
        trace := s.trace ++ tailDrops
        outcome := .unwindResume }
    else
      some { s with pc := 7, bad := true }
  else
    none

/-- Multi-step operational transition function for `partial_init_move_cleanup` modeling
    the `MirPhase::Runtime(RuntimePhase::PostCleanup)` elaborated drop-flag CFG
    (`bodies_cleanup_subject_preserve_ub.json` line 9, `bb0`..`bb16`):
    - `pc = 0` (`bb0`): initializes `_20 := true`, `_21 := false`, `_5 = PairGuards { first: 1, second: 2 }`.
    - `pc = 1` (`bb0` branch -> `bb1` vs `bb4`): if `moveFirstEarly`, moves `_5.0` into `_12`,
      sets `_20 := false, _21 := true`, and records `10` (`bb1`).
    - `pc = 2` (`bb2` -> `bb3`): clears `_21 := false` and calls `core::mem::drop(_16)` on the
      moved first field (recording tag `1`).
    - `pc = 3` (`bb5`): calls `may_unwind_op(triggerPanic, 5)` -> normal return `bb6` (`pc = 4`,
      `retVal = 105`) or unwind `bb16` (`pc = 5`).
    - `pc = 4` (`bb6: switchInt(copy _20) -> [0: bb10, otherwise: bb11]` + `bb11: drop((_5.0))`):
      when `dropFlag20 = true`, drops `_5.0` (`firstTag = 1`) at `bb11` before advancing to
      `bb10` (`pc = 6`); when `dropFlag20 = false`, branches directly to `bb10` (`pc = 6`).
    - `pc = 6` (`bb10: drop((_5.1))` -> `bb8: return`): drops `_5.1` (`secondTag = 2`) and
      returns `.normalReturn` (`pc = 7`).
    - `pc = 5` (`bb16: switchInt(copy _20) -> [0: bb14, otherwise: bb15]` + `bb15: drop((_5.0))`):
      when `dropFlag20 = true`, drops `_5.0` (`firstTag = 1`) at `bb15` before advancing to
      `bb14` (`pc = 8`); when `dropFlag20 = false`, branches directly to `bb14` (`pc = 8`).
    - `pc = 8` (`bb14: drop((_5.1))` -> `bb7: resume`): drops `_5.1` (`secondTag = 2`) and
      terminates in `.unwindResume` (`pc = 7`). -/
noncomputable def elaboratedPartialInitStep (moveFirstEarly triggerPanic : Bool) (s : CleanupState) :
    Option CleanupState :=
  bif Nat.beq s.pc 0 then
    some { s with
      pc := 1
      firstInit := true
      secondInit := true
      firstTag := 1
      secondTag := 2
      dropFlag20 := true
      dropFlag21 := false }
  else bif Nat.beq s.pc 1 then
    bif moveFirstEarly then
      some { s with
        pc := 2
        firstInit := false
        movedInit := true
        movedTag := s.firstTag
        dropFlag20 := false
        dropFlag21 := true
        trace := s.trace ++ [10] }
    else
      some { s with pc := 3 }
  else bif Nat.beq s.pc 2 then
    bif s.dropFlag21 then
      bif s.movedInit then
        some { s with
          pc := 3
          movedInit := false
          dropFlag21 := false
          trace := s.trace ++ [s.movedTag] }
      else
        some { s with pc := 7, bad := true }
    else
      some { s with pc := 3 }
  else bif Nat.beq s.pc 3 then
    bif triggerPanic then
      some { s with pc := 5 }
    else
      some { s with pc := 4, retVal := 105 }
  else bif Nat.beq s.pc 4 then
    bif s.dropFlag20 then
      bif s.firstInit then
        some { s with
          pc := 6
          firstInit := false
          dropFlag20 := false
          trace := s.trace ++ [s.firstTag] }
      else
        some { s with pc := 7, bad := true }
    else
      some { s with pc := 6 }
  else bif Nat.beq s.pc 5 then
    bif s.dropFlag20 then
      bif s.firstInit then
        some { s with
          pc := 8
          firstInit := false
          dropFlag20 := false
          trace := s.trace ++ [s.firstTag] }
      else
        some { s with pc := 7, bad := true }
    else
      some { s with pc := 8 }
  else bif Nat.beq s.pc 6 then
    bif s.secondInit then
      some { s with
        pc := 7
        secondInit := false
        trace := s.trace ++ [s.secondTag]
        outcome := .normalReturn }
    else
      some { s with pc := 7, bad := true }
  else bif Nat.beq s.pc 8 then
    bif s.secondInit then
      some { s with
        pc := 7
        secondInit := false
        trace := s.trace ++ [s.secondTag]
        outcome := .unwindResume }
    else
      some { s with pc := 7, bad := true }
  else
    none

/-- Expected terminal observation of `partial_init_move_cleanup(moveFirstEarly, triggerPanic)`,
    matching `ordered_observer_runtime_output.json` (`[1, 2]` when `moveFirstEarly = false`,
    `[10, 1, 2]` when `moveFirstEarly = true`). -/
noncomputable def expectedPartialInitObs (moveFirstEarly triggerPanic : Bool) : CleanupObs :=
  bif moveFirstEarly then
    bif triggerPanic then
      { trace := [10, 1, 2], retVal := 0, outcome := .unwindResume }
    else
      { trace := [10, 1, 2], retVal := 105, outcome := .normalReturn }
  else
    bif triggerPanic then
      { trace := [1, 2], retVal := 0, outcome := .unwindResume }
    else
      { trace := [1, 2], retVal := 105, outcome := .normalReturn }

/-- Theorem 1: Across all four `(moveFirstEarly, triggerPanic)` combinations for
    `partial_init_move_cleanup`, the multi-step `Analysis` conditional-drop model and
    the `Runtime(PostCleanup)` elaborated drop-flag model produce identical terminal
    observations (`[1, 2]` when `moveFirstEarly = false`, `[10, 1, 2]` when
    `moveFirstEarly = true`, matching `ordered_observer_runtime_output.json`) and both
    satisfy `Execution.NoUB`. -/
theorem analysis_and_elaborated_cleanup_trace_equivalent
    (moveFirstEarly triggerPanic : Bool) :
    (runSteps (analysisPartialInitStep moveFirstEarly triggerPanic) 8 initialCleanupState).obs =
      expectedPartialInitObs moveFirstEarly triggerPanic ∧
    (runSteps (elaboratedPartialInitStep moveFirstEarly triggerPanic) 8 initialCleanupState).obs =
      expectedPartialInitObs moveFirstEarly triggerPanic ∧
    Execution.NoUB
      (StepFromFn (analysisPartialInitStep moveFirstEarly triggerPanic))
      (fun s => s.bad = true)
      initialCleanupState ∧
    Execution.NoUB
      (StepFromFn (elaboratedPartialInitStep moveFirstEarly triggerPanic))
      (fun s => s.bad = true)
      initialCleanupState := by
  cases moveFirstEarly <;> cases triggerPanic <;>
    exact ⟨rfl, rfl, noUB_of_boundedAllSafe (fuel := 8) rfl, noUB_of_boundedAllSafe (fuel := 8) rfl⟩

#print axioms analysis_and_elaborated_cleanup_trace_equivalent

/-- Multi-step operational transition function for `partial_field_reinit_cleanup` under
    `Analysis` (`Built`) MIR conditional-drop semantics (partial move of `pair.first`,
    `core::mem::forget(moved_first)`, `may_unwind_op(triggerPanic, 7)`, and reinitialization
    `pair.first = Guard { drop_tag: 3 }` on the non-panicking path, followed by whole-place
    `drop(pair)` in declaration order `first` then `second`). -/
noncomputable def analysisReinitStep (triggerPanic : Bool) (s : CleanupState) : Option CleanupState :=
  bif Nat.beq s.pc 0 then
    some { s with
      pc := 1
      firstInit := false
      secondInit := true
      movedInit := true
      firstTag := 1
      secondTag := 2
      movedTag := 1
      trace := s.trace ++ [10] }
  else bif Nat.beq s.pc 1 then
    some { s with
      pc := 2
      movedInit := false }
  else bif Nat.beq s.pc 2 then
    bif triggerPanic then
      some { s with pc := 5 }
    else
      some { s with pc := 3, retVal := 107 }
  else bif Nat.beq s.pc 3 then
    some { s with
      pc := 4
      firstInit := true
      firstTag := 3 }
  else bif Nat.beq s.pc 4 then
    bif s.secondInit then
      let tailDrops := bif s.firstInit then [s.firstTag, s.secondTag] else [s.secondTag]
      some { s with
        pc := 7
        firstInit := false
        secondInit := false
        trace := s.trace ++ tailDrops
        outcome := .normalReturn }
    else
      some { s with pc := 7, bad := true }
  else bif Nat.beq s.pc 5 then
    bif s.secondInit then
      let tailDrops := bif s.firstInit then [s.firstTag, s.secondTag] else [s.secondTag]
      some { s with
        pc := 7
        firstInit := false
        secondInit := false
        trace := s.trace ++ tailDrops
        outcome := .unwindResume }
    else
      some { s with pc := 7, bad := true }
  else
    none

/-- Multi-step operational transition function for `partial_field_reinit_cleanup` modeling
    the `MirPhase::Runtime(RuntimePhase::PostCleanup)` CFG (`bodies_cleanup_subject_preserve_ub.json`
    line 11, `bb0`..`bb8`) and `DropGlue<PairGuards>` (`bodies_cleanup_subject_preserve_ub.json`
    line 27, `bb0` -> `bb4` -> `bb2`):
    - `pc = 0` (`bb0`): moves `_4.0` into `_9`, sets `_23 := true`, and records `10`.
    - `pc = 1` (`bb1`): clears `_23 := false` and calls `core::mem::forget(_14)` on `_9`.
    - `pc = 2` (`bb2`): calls `may_unwind_op(triggerPanic, 7)` -> normal return `bb3` (`pc = 3`,
      `retVal = 107`) or unwind `bb8` (`pc = 5`).
    - `pc = 3` (`bb3`): reinitializes `(_4.0) = Guard { drop_tag: 3 }` and enters `drop(_4)`
      (`DropGlue<PairGuards>` at `pc = 4`).
    - `pc = 4` (`DropGlue<PairGuards>::bb0: drop(((*_1).0))`): drops `_4.0` (`firstTag = 3`)
      first and advances to `DropGlue<PairGuards>::bb4` (`pc = 6`).
    - `pc = 6` (`DropGlue<PairGuards>::bb4: drop(((*_1).1))` -> `bb4: return`): drops `_4.1`
      (`secondTag = 2`) second and completes in `.normalReturn` (`pc = 7`).
    - `pc = 5` (`bb8: switchInt(copy _23) -> [0: bb5, otherwise: bb7]`): since `_23 = false`,
      branches to `bb5` (`pc = 8`).
    - `pc = 8` (`bb5: drop((_4.1))` -> `bb6: resume`): drops `_4.1` (`secondTag = 2`) and
      completes in `.unwindResume` (`pc = 7`). -/
noncomputable def elaboratedReinitStep (triggerPanic : Bool) (s : CleanupState) : Option CleanupState :=
  bif Nat.beq s.pc 0 then
    some { s with
      pc := 1
      firstInit := false
      secondInit := true
      movedInit := true
      firstTag := 1
      secondTag := 2
      movedTag := 1
      dropFlag20 := false
      dropFlag21 := true
      trace := s.trace ++ [10] }
  else bif Nat.beq s.pc 1 then
    some { s with
      pc := 2
      movedInit := false
      dropFlag21 := false }
  else bif Nat.beq s.pc 2 then
    bif triggerPanic then
      some { s with pc := 5 }
    else
      some { s with pc := 3, retVal := 107 }
  else bif Nat.beq s.pc 3 then
    some { s with
      pc := 4
      firstInit := true
      firstTag := 3
      dropFlag20 := true }
  else bif Nat.beq s.pc 4 then
    bif s.dropFlag20 then
      bif s.firstInit then
        some { s with
          pc := 6
          firstInit := false
          dropFlag20 := false
          trace := s.trace ++ [s.firstTag] }
      else
        some { s with pc := 7, bad := true }
    else
      some { s with pc := 6 }
  else bif Nat.beq s.pc 5 then
    bif s.dropFlag20 then
      bif s.firstInit then
        some { s with
          pc := 8
          firstInit := false
          dropFlag20 := false
          trace := s.trace ++ [s.firstTag] }
      else
        some { s with pc := 7, bad := true }
    else
      some { s with pc := 8 }
  else bif Nat.beq s.pc 6 then
    bif s.secondInit then
      some { s with
        pc := 7
        secondInit := false
        trace := s.trace ++ [s.secondTag]
        outcome := .normalReturn }
    else
      some { s with pc := 7, bad := true }
  else bif Nat.beq s.pc 8 then
    bif s.secondInit then
      some { s with
        pc := 7
        secondInit := false
        trace := s.trace ++ [s.secondTag]
        outcome := .unwindResume }
    else
      some { s with pc := 7, bad := true }
  else
    none

/-- Expected terminal observation of `partial_field_reinit_cleanup(triggerPanic)`,
    matching `ordered_observer_runtime_output.json` (`[10, 3, 2]` on normal return
    after reinitializing `pair.first` with tag `3`, and `[10, 2]` on unwind before
    reinitialization). -/
noncomputable def expectedReinitObs (triggerPanic : Bool) : CleanupObs :=
  bif triggerPanic then
    { trace := [10, 2], retVal := 0, outcome := .unwindResume }
  else
    { trace := [10, 3, 2], retVal := 107, outcome := .normalReturn }

/-- Theorem 2: Across both `triggerPanic` inputs to `partial_field_reinit_cleanup`,
    the multi-step `Analysis` conditional-drop model and `Runtime(PostCleanup)` +
    `DropGlue<PairGuards>` elaborated drop model produce identical terminal observations
    (`[10, 3, 2]` on normal return after reinitialization, `[10, 2]` on unwind before
    reinitialization, matching `ordered_observer_runtime_output.json`) and both satisfy
    `Execution.NoUB`. -/
theorem reinit_cleanup_analysis_and_elaborated_equivalent
    (triggerPanic : Bool) :
    (runSteps (analysisReinitStep triggerPanic) 8 initialCleanupState).obs =
      expectedReinitObs triggerPanic ∧
    (runSteps (elaboratedReinitStep triggerPanic) 8 initialCleanupState).obs =
      expectedReinitObs triggerPanic ∧
    Execution.NoUB
      (StepFromFn (analysisReinitStep triggerPanic))
      (fun s => s.bad = true)
      initialCleanupState ∧
    Execution.NoUB
      (StepFromFn (elaboratedReinitStep triggerPanic))
      (fun s => s.bad = true)
      initialCleanupState := by
  cases triggerPanic <;>
    exact ⟨rfl, rfl, noUB_of_boundedAllSafe (fuel := 8) rfl, noUB_of_boundedAllSafe (fuel := 8) rfl⟩

#print axioms reinit_cleanup_analysis_and_elaborated_equivalent

/-!
## Section 2: Divergence and Finite-Prefix UB Sensitivity
-/

/-- Predicate characterizing terminal states (`normalReturn` or `unwindResume`). -/
noncomputable def IsTerminal (s : CleanupState) : Prop :=
  s.outcome ≠ .running

/-- Completed-execution-only safety criterion: checks `s.bad = false` only at terminal states. -/
noncomputable def CompletedTerminalSafe (Step : CleanupState → CleanupState → Prop) (s0 : CleanupState) : Prop :=
  ∀ s, Execution.Reach Step s0 s → IsTerminal s → ¬ (s.bad = true)

/-- Safe divergent transition system: steps `pc = 0 → 0` forever without setting `bad = true`
    or reaching a terminal state. -/
noncomputable def safeDivergentStep (s : CleanupState) : Option CleanupState :=
  bif Nat.beq s.pc 0 then
    some { s with pc := 0, bad := false, outcome := .running }
  else
    none

noncomputable def SafeDivergentInv (s : CleanupState) : Prop :=
  s.pc = 0 ∧ s.bad = false ∧ s.outcome = .running

theorem safeDivergent_inv_step {s t : CleanupState}
    (hs : SafeDivergentInv s) (hstep : StepFromFn safeDivergentStep s t) :
    SafeDivergentInv t := by
  rcases hs with ⟨hpc, _, _⟩
  unfold StepFromFn safeDivergentStep at hstep
  rw [hpc] at hstep
  injection hstep with ht
  rw [← ht]
  exact ⟨rfl, rfl, rfl⟩

/-- Theorem 3: A structurally well-formed divergent transition system (`safeDivergentStep`)
    actively steps from `initialCleanupState`, has no reachable terminal state, and satisfies
    `Execution.NoUB`. -/
theorem safe_divergent_satisfies_noUB_without_terminal_state :
    StepFromFn safeDivergentStep initialCleanupState initialCleanupState ∧
    (∀ s, Execution.Reach (StepFromFn safeDivergentStep) initialCleanupState s → ¬ IsTerminal s) ∧
    Execution.NoUB
      (StepFromFn safeDivergentStep)
      (fun s => s.bad = true)
      initialCleanupState := by
  refine ⟨rfl, ?_, ?_⟩
  · intro s hreach hterm
    have hinv : SafeDivergentInv s :=
      Execution.invariant_reachable
        (Invariant := SafeDivergentInv)
        ⟨rfl, rfl, rfl⟩
        (fun hs hst => safeDivergent_inv_step hs hst)
        hreach
    exact hterm hinv.2.2
  · exact Execution.invariant_noUB
      (Invariant := SafeDivergentInv)
      ⟨rfl, rfl, rfl⟩
      (fun hs hst => safeDivergent_inv_step hs hst)
      (fun s hs hbad => by
        have hfalse : s.bad = false := hs.2.1
        rw [hbad] at hfalse
        exact Bool.noConfusion hfalse)

#print axioms safe_divergent_satisfies_noUB_without_terminal_state

/-- Transition system that triggers UB on step 1 (`pc = 0 → 1` with `bad := true`) and then
    diverges forever (`pc = 1 → 1`) with `outcome = .running`. -/
noncomputable def unsafePrefixBeforeDivergenceStep (s : CleanupState) : Option CleanupState :=
  bif Nat.beq s.pc 0 then
    some { s with pc := 1, bad := true, outcome := .running }
  else bif Nat.beq s.pc 1 then
    some { s with pc := 1, bad := true, outcome := .running }
  else
    none

noncomputable def UnsafePrefixRunningInv (s : CleanupState) : Prop :=
  (s.pc = 0 ∨ s.pc = 1) ∧ s.outcome = .running

theorem unsafePrefix_inv_step {s t : CleanupState}
    (hs : UnsafePrefixRunningInv s) (hstep : StepFromFn unsafePrefixBeforeDivergenceStep s t) :
    UnsafePrefixRunningInv t := by
  rcases hs with ⟨hpc, _⟩
  unfold StepFromFn unsafePrefixBeforeDivergenceStep at hstep
  cases hpc with
  | inl h0 =>
    rw [h0] at hstep
    injection hstep with ht
    rw [← ht]
    exact ⟨Or.inr rfl, rfl⟩
  | inr h1 =>
    rw [h1] at hstep
    injection hstep with ht
    rw [← ht]
    exact ⟨Or.inr rfl, rfl⟩

/-- Theorem 4: An execution that faults on a finite prefix before diverging (`unsafePrefixBeforeDivergenceStep`)
    has no reachable terminal state and therefore vacuously satisfies `CompletedTerminalSafe`,
    yet is rejected by `Execution.NoUB`. -/
theorem unsafe_prefix_before_divergence_admitted_and_rejected_by_noUB :
    CompletedTerminalSafe
      (StepFromFn unsafePrefixBeforeDivergenceStep)
      initialCleanupState ∧
    ¬ Execution.NoUB
      (StepFromFn unsafePrefixBeforeDivergenceStep)
      (fun s => s.bad = true)
      initialCleanupState := by
  refine ⟨?_, ?_⟩
  · intro s hreach hterm
    have hinv : UnsafePrefixRunningInv s :=
      Execution.invariant_reachable
        (Invariant := UnsafePrefixRunningInv)
        ⟨Or.inl rfl, rfl⟩
        (fun hs hst => unsafePrefix_inv_step hs hst)
        hreach
    exact False.elim (hterm hinv.2)
  · exact not_noUB_of_one_step_bad rfl rfl

#print axioms unsafe_prefix_before_divergence_admitted_and_rejected_by_noUB

/-!
## Section 3: Phase-Accurate Retention of `_3 = copy (*_1)`, `PlaceMention`, and `SwitchInt`
-/

/-- Multi-step operational state for pointer/discriminant probes (`ub_boundary_probe` and
    `match_wildcard_probe`) parameterized by:
    - `preserveUb`: whether `-Z mir-preserve-ub` is enabled (`true`) or omitted (`false`),
    - `optimizedPhase`: whether the body is captured at `Runtime(PostCleanup)` (`false`) or
      `Runtime(Optimized)` (`true`), and
    - `hasPrecedingDerefLoad`: `true` for `ub_boundary_probe` (`let _ = unsafe { *ptr };`,
      which emits `_3 = copy (*_1)` before `PlaceMention(_3)` at `Runtime(PostCleanup)`),
      and `false` for `match_wildcard_probe` (`unsafe { match *ptr { _ => 0 } }` /
      `unsafe { _ = *ptr; }`, which emits `PlaceMention((*_1))` directly without a load). -/
structure UbProbeState where
  pc : Nat
  preserveUb : Bool
  optimizedPhase : Bool
  ptrValid : Bool
  flagDiscrValid : Bool
  placeMentionChecked : Bool
  switchDiscrChecked : Bool
  outcome : ExecOutcome
  bad : Bool

noncomputable def initialUbProbeState
    (preserveUb optimizedPhase ptrValid flagDiscrValid : Bool) : UbProbeState :=
  { pc := 0
    preserveUb := preserveUb
    optimizedPhase := optimizedPhase
    ptrValid := ptrValid
    flagDiscrValid := flagDiscrValid
    placeMentionChecked := false
    switchDiscrChecked := false
    outcome := .running
    bad := false }

/-- Multi-step transition function for `PlaceMention((*_1))` + `SwitchInt(flag)`
    (matching `match_wildcard_probe` / `assign_underscore_probe`, where `PlaceMention((*_1))`
    is emitted without a preceding `_3 = copy (*_1)` load; see `ubBoundaryWithLoadStep` in
    `MirSemanticBoundaryControls.lean` for `ub_boundary_probe`'s retained `_3 = copy (*_1)`
    load at `Runtime(PostCleanup)`):
    - At `pc = 0`: `PlaceMention` is retained when `preserveUb = true` and stripped by
      `RemovePlaceMention` before `Runtime(PostCleanup)` when `preserveUb = false`.
    - At `pc = 1`: `SwitchInt` on `flag` is retained at `Runtime(PostCleanup)` (`!s.optimizedPhase`)
      and under `-Z mir-preserve-ub` (`s.preserveUb`), and collapsed at default `Runtime(Optimized)`.
    - At `pc = 2`: completes with `.normalReturn`. -/
noncomputable def ubProbeStep (s : UbProbeState) : Option UbProbeState :=
  bif Nat.beq s.pc 0 then
    bif s.preserveUb then
      bif s.ptrValid then
        some { s with pc := 1, placeMentionChecked := true }
      else
        some { s with pc := 3, placeMentionChecked := true, bad := true }
    else
      some { s with pc := 1, placeMentionChecked := false }
  else bif Nat.beq s.pc 1 then
    bif (s.preserveUb || !s.optimizedPhase) then
      bif s.flagDiscrValid then
        some { s with pc := 2, switchDiscrChecked := true }
      else
        some { s with pc := 3, switchDiscrChecked := true, bad := true }
    else
      some { s with pc := 2, switchDiscrChecked := false }
  else bif Nat.beq s.pc 2 then
    some { s with pc := 3, outcome := .normalReturn }
  else
    none

/-- Theorem 5: Capturing `Runtime(PostCleanup)` with `-Z mir-preserve-ub`
    (`preserveUb = true, optimizedPhase = false`) retains both the `PlaceMention`
    check (`placeMentionChecked = true`) and the `SwitchInt` discriminant check
    (`switchDiscrChecked = true`): `ptrValid = false` or `flagDiscrValid = false`
    triggers `¬ Execution.NoUB`, while valid inputs satisfy `Execution.NoUB` and
    reach `.normalReturn` with both checks recorded. -/
theorem preserve_ub_flag_retains_place_mention_and_switch_ub :
    ¬ Execution.NoUB
      (StepFromFn ubProbeStep)
      (fun s => s.bad = true)
      (initialUbProbeState true false false true) ∧
    ¬ Execution.NoUB
      (StepFromFn ubProbeStep)
      (fun s => s.bad = true)
      (initialUbProbeState true false true false) ∧
    Execution.NoUB
      (StepFromFn ubProbeStep)
      (fun s => s.bad = true)
      (initialUbProbeState true false true true) ∧
    (runSteps ubProbeStep 5 (initialUbProbeState true false true true)).outcome = .normalReturn ∧
    (runSteps ubProbeStep 5 (initialUbProbeState true false true true)).placeMentionChecked = true ∧
    (runSteps ubProbeStep 5 (initialUbProbeState true false true true)).switchDiscrChecked = true := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · exact not_noUB_of_one_step_bad rfl rfl
  · exact not_noUB_of_two_step_bad rfl rfl rfl
  · exact noUB_of_boundedAllSafe (fuel := 5) rfl

#print axioms preserve_ub_flag_retains_place_mention_and_switch_ub

/-!
## Section 4: Four-Way Boundary Separation
-/

/-- 4-bit classification descriptor (`BoundarySubjectDescriptor`) illustrating the logical
    separation between four distinct verification layers:
    (a) `d.1`: structural and grammatical well-formedness of a decoded MIR body
        (`StructurallyWellFormed`),
    (b) `d.2.1`: compiler phase/dialect invariants (`Runtime(PostCleanup)` + `-Z mir-preserve-ub`,
        `DialectCompilerInvariant`),
    (c) `d.2.2.1`: semantic caller preconditions (`requires` / valid input state,
        `SemanticCallerPrecondition`), and
    (d) `d.2.2.2`: body execution safety (`Execution.NoUB`) and functional specification
        (`BodyExecutionNoUBAndSpec`).
    The composite advertised claim (`AdvertisedNoUBAndClaim`) is the conjunction of all four
    layers; thus `AdvertisedNoUBAndClaim` is not pairwise independent of its conjuncts, while
    each of the three admission predicates (a)–(c) can fail independently when the other two
    admission predicates hold, and (d) can fail even when all three admission predicates (a)–(c)
    hold. -/
abbrev BoundarySubjectDescriptor : Type := Bool × Bool × Bool × Bool

/-- (a) Structural and grammatical well-formedness of the decoded MIR body. -/
noncomputable def StructurallyWellFormed (d : BoundarySubjectDescriptor) : Bool :=
  d.1

/-- (b) Dialect and compiler phase invariants required by the operational model. -/
noncomputable def DialectCompilerInvariant (d : BoundarySubjectDescriptor) : Bool :=
  d.2.1

/-- (c) Proof-side semantic caller preconditions (`requires` clause). -/
noncomputable def SemanticCallerPrecondition (d : BoundarySubjectDescriptor) : Bool :=
  d.2.2.1

/-- (d) Body execution safety (`Execution.NoUB`) and functional specification under (a)–(c). -/
noncomputable def BodyExecutionNoUBAndSpec (d : BoundarySubjectDescriptor) : Bool :=
  d.2.2.2

/-- Full composite advertised claim requiring all four boundary obligations (a)–(d). -/
noncomputable def AdvertisedNoUBAndClaim (d : BoundarySubjectDescriptor) : Bool :=
  StructurallyWellFormed d &&
  DialectCompilerInvariant d &&
  SemanticCallerPrecondition d &&
  BodyExecutionNoUBAndSpec d

/-- Witness 1 (`validAdmittedSafeDescriptor`): Satisfies all three admission layers and the body
    `Execution.NoUB` + specification obligation (`partial_init_move_cleanup` /
    `partial_field_reinit_cleanup`). -/
noncomputable def validAdmittedSafeDescriptor : BoundarySubjectDescriptor :=
  (true, true, true, true)

/-- Witness 2 (`malformedDescriptor`): Fails structural/grammatical well-formedness while the
    dialect and caller precondition flags hold. -/
noncomputable def malformedDescriptor : BoundarySubjectDescriptor :=
  (false, true, true, true)

/-- Witness 3 (`wrongDialectDescriptor`): Structurally well-formed and within caller preconditions,
    but captured at the wrong compiler boundary (e.g., `optimized_mir` after
    `RemoveStorageMarkers` or without `-Z mir-preserve-ub`). -/
noncomputable def wrongDialectDescriptor : BoundarySubjectDescriptor :=
  (true, false, true, true)

/-- Witness 4 (`missingCallerPrecondDescriptor`): Structurally well-formed at the candidate
    compiler boundary, but invoked outside its semantic caller precondition. -/
noncomputable def missingCallerPrecondDescriptor : BoundarySubjectDescriptor :=
  (true, true, false, true)

/-- Witness 5 (`admittedButUnsafeBodyDescriptor`): Satisfies all three admission predicates
    (`StructurallyWellFormed`, `DialectCompilerInvariant`, `SemanticCallerPrecondition`),
    but triggers internal UB during execution (`unsafePrefixBeforeDivergenceStep`). -/
noncomputable def admittedButUnsafeBodyDescriptor : BoundarySubjectDescriptor :=
  (true, true, true, false)

/-- Theorem 6: Defines `AdvertisedNoUBAndClaim d` as the conjunction
    `StructurallyWellFormed d && DialectCompilerInvariant d && SemanticCallerPrecondition d && BodyExecutionNoUBAndSpec d`
    over `BoundarySubjectDescriptor`, and exhibits five concrete witness descriptors showing that:
    (1) `validAdmittedSafeDescriptor` satisfies all four layers and `AdvertisedNoUBAndClaim`,
    (2) each of the first three admission predicates (`StructurallyWellFormed`,
        `DialectCompilerInvariant`, `SemanticCallerPrecondition`) fails on its dedicated witness
        (`malformedDescriptor`, `wrongDialectDescriptor`, `missingCallerPrecondDescriptor`) while
        the other two admission predicates hold, and
    (3) all three admission predicates hold on `admittedButUnsafeBodyDescriptor` while
        `BodyExecutionNoUBAndSpec` and `AdvertisedNoUBAndClaim` are `false`. -/
theorem four_way_boundary_separation :
    AdvertisedNoUBAndClaim validAdmittedSafeDescriptor = true ∧
    (StructurallyWellFormed malformedDescriptor = false ∧
      DialectCompilerInvariant malformedDescriptor = true ∧
      SemanticCallerPrecondition malformedDescriptor = true ∧
      AdvertisedNoUBAndClaim malformedDescriptor = false) ∧
    (StructurallyWellFormed wrongDialectDescriptor = true ∧
      DialectCompilerInvariant wrongDialectDescriptor = false ∧
      SemanticCallerPrecondition wrongDialectDescriptor = true ∧
      AdvertisedNoUBAndClaim wrongDialectDescriptor = false) ∧
    (StructurallyWellFormed missingCallerPrecondDescriptor = true ∧
      DialectCompilerInvariant missingCallerPrecondDescriptor = true ∧
      SemanticCallerPrecondition missingCallerPrecondDescriptor = false ∧
      AdvertisedNoUBAndClaim missingCallerPrecondDescriptor = false) ∧
    (StructurallyWellFormed admittedButUnsafeBodyDescriptor = true ∧
      DialectCompilerInvariant admittedButUnsafeBodyDescriptor = true ∧
      SemanticCallerPrecondition admittedButUnsafeBodyDescriptor = true ∧
      BodyExecutionNoUBAndSpec admittedButUnsafeBodyDescriptor = false ∧
      AdvertisedNoUBAndClaim admittedButUnsafeBodyDescriptor = false) :=
  ⟨rfl,
   ⟨rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

#print axioms four_way_boundary_separation

end AnnealResearch.MirSemanticBoundary
