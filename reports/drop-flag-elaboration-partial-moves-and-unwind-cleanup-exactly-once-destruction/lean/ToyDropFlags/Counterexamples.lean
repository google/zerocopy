import ToyDropFlags.Examples

/-!
# Counterexamples, non-vacuity witnesses and positive controls

All fully proved by kernel evaluation of concrete runs or of the exhaustive run tree.
Tightness counterexamples are stated in canonical form: every *other* hypothesis of the result
holds, the named hypothesis fails, and the result's conclusion fails.
-/

namespace Toy.DropFlags

/-! ## The standard elaboration is correct on the example programs (all runs checked) -/

theorem progJoin_stdElab_correct : ElabCorrect .abort .std (stdMap progJoin .fine) progJoin :=
  elabCorrect_of_explore _ _ _ _ (by decide)
theorem progCleanup_stdElab_correct :
    ElabCorrect .abort .std (stdMap progCleanup .fine) progCleanup :=
  elabCorrect_of_explore _ _ _ _ (by decide)
theorem progPartial_stdElab_correct :
    ElabCorrect .abort .std (stdMap progPartial .fine) progPartial :=
  elabCorrect_of_explore _ _ _ _ (by decide)
theorem progReinit_stdElab_correct :
    ElabCorrect .abort .std (stdMap progReinit .fine) progReinit :=
  elabCorrect_of_explore _ _ _ _ (by decide)
theorem progUnwind_stdElab_correct_abort :
    ElabCorrect .abort .std (stdMap progUnwind .fine) progUnwind :=
  elabCorrect_of_explore _ _ _ _ (by decide)
theorem progShare_stdElab_correct :
    ElabCorrect .abort .std (stdMap progShare .fine) progShare :=
  elabCorrect_of_explore _ _ _ _ (by decide)
theorem progMultiStepCleanup_stdElab_correct :
    ElabCorrect .abort .std (stdMap progMultiStepCleanup .fine) progMultiStepCleanup :=
  elabCorrect_of_explore _ _ _ _ (by decide)
theorem progUnwindToRet_stdElab_correct :
    ElabCorrect .abort .std (stdMap progUnwindToRet .fine) progUnwindToRet :=
  elabCorrect_of_explore _ _ _ _ (by decide)

/-! ## Non-vacuity of the hypotheses of the exactly-once theorem -/

/-- `progCleanup` satisfies every hypothesis of the exactly-once theorem and its standard
elaboration tests a dynamic flag on a cleanup path. -/
theorem exactlyOnce_hypotheses_hold_progCleanup :
    Forward progCleanup ∧ PlacesAreMovePaths progCleanup ∧ MovesFromInit progCleanup ∧
    InitsIntoUninit progCleanup ∧ NoNormalPathToResume progCleanup ∧
    flagSet progCleanup (stdMap progCleanup .fine) = [x] := by decide

/-- `progJoin` satisfies every hypothesis of the exactly-once theorem (a dynamic flag at a
normal-path join). -/
theorem exactlyOnce_hypotheses_hold_progJoin :
    Forward progJoin ∧ PlacesAreMovePaths progJoin ∧ MovesFromInit progJoin ∧
    InitsIntoUninit progJoin ∧ NoNormalPathToResume progJoin := by decide

/-- `progMultiStepCleanup` (cleanup code of more than one node) satisfies every hypothesis of the
exactly-once theorem. -/
theorem exactlyOnce_hypotheses_hold_progMultiStepCleanup :
    Forward progMultiStepCleanup ∧ PlacesAreMovePaths progMultiStepCleanup ∧
    MovesFromInit progMultiStepCleanup ∧ InitsIntoUninit progMultiStepCleanup ∧
    NoNormalPathToResume progMultiStepCleanup := by decide

/-! ## Each hypothesis of the exactly-once theorem is needed (canonical form) -/

/-- Without `Forward`: a back edge re-runs an `init`; the one-pass analysis does not see the back
edge, so the move checker accepts, and the first value leaks. -/
theorem stdElab_fails_without_forward :
    ¬ Forward progLoop ∧ PlacesAreMovePaths progLoop ∧ MovesFromInit progLoop ∧
    InitsIntoUninit progLoop ∧ NoNormalPathToResume progLoop ∧
    ¬ ElabCorrect .abort .std (stdMap progLoop .fine) progLoop := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun h => ?_⟩
  have := h [true, false, false]
  revert this; decide

/-- Without `PlacesAreMovePaths`: moving a field out of a struct with its own destructor; the
struct's destructor and its other field leak. -/
theorem stdElab_fails_without_placesAreMovePaths :
    Forward progDropStruct ∧ ¬ PlacesAreMovePaths progDropStruct ∧
    MovesFromInit progDropStruct ∧ InitsIntoUninit progDropStruct ∧
    NoNormalPathToResume progDropStruct ∧
    ¬ ElabCorrect .abort .std (stdMap progDropStruct .fine) progDropStruct := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun h => ?_⟩
  have := h []
  revert this; decide

/-- Without `MovesFromInit`: a use after move hands the same value to two consumers. -/
theorem stdElab_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧ InitsIntoUninit progUseAfterMove ∧
    NoNormalPathToResume progUseAfterMove ∧
    ¬ ElabCorrect .abort .std (stdMap progUseAfterMove .fine) progUseAfterMove := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun h => ?_⟩
  have := h []
  revert this; decide

/-- Without `InitsIntoUninit`: an overwrite loses the first value. -/
theorem stdElab_fails_without_initsIntoUninit :
    Forward progOverwrite ∧ PlacesAreMovePaths progOverwrite ∧ MovesFromInit progOverwrite ∧
    ¬ InitsIntoUninit progOverwrite ∧ NoNormalPathToResume progOverwrite ∧
    ¬ ElabCorrect .abort .std (stdMap progOverwrite .fine) progOverwrite := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun h => ?_⟩
  have := h []
  revert this; decide

/-- Without `NoNormalPathToResume`: a `resume` reached normally runs drops without landing pads;
a destructor panic there (a first panic, so the abort rule does not apply) leaves the frame and
the remaining local leaks. -/
theorem stdElab_fails_without_noNormalPathToResume :
    Forward progResumeNormal ∧ PlacesAreMovePaths progResumeNormal ∧
    MovesFromInit progResumeNormal ∧ InitsIntoUninit progResumeNormal ∧
    ¬ NoNormalPathToResume progResumeNormal ∧
    ¬ ElabCorrect .abort .std (stdMap progResumeNormal .fine) progResumeNormal := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun h => ?_⟩
  have := h [true]
  revert this; decide

/-! ## The characterization fails without its hypotheses

The standard decision map is always compatible (`stdDecision_compatible`), so each program above
also breaks the equivalence "elaboration-correct ↔ all decisions compatible". -/

theorem not_iff_of_compatible_not_correct {P Q : Prop} (hq : Q) (hp : ¬ P) : ¬ (P ↔ Q) :=
  fun h => hp (h.2 hq)

theorem characterization_fails_without_forward :
    ¬ Forward progLoop ∧ PlacesAreMovePaths progLoop ∧ MovesFromInit progLoop ∧
    InitsIntoUninit progLoop ∧ NoNormalPathToResume progLoop ∧
    ¬ (ElabCorrect .abort .std (stdMap progLoop .fine) progLoop ↔
       AllCompatible progLoop (stdMap progLoop .fine)) :=
  have h := stdElab_fails_without_forward
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    not_iff_of_compatible_not_correct (by decide) h.2.2.2.2.2⟩

theorem characterization_fails_without_placesAreMovePaths :
    Forward progDropStruct ∧ ¬ PlacesAreMovePaths progDropStruct ∧
    MovesFromInit progDropStruct ∧ InitsIntoUninit progDropStruct ∧
    NoNormalPathToResume progDropStruct ∧
    ¬ (ElabCorrect .abort .std (stdMap progDropStruct .fine) progDropStruct ↔
       AllCompatible progDropStruct (stdMap progDropStruct .fine)) :=
  have h := stdElab_fails_without_placesAreMovePaths
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    not_iff_of_compatible_not_correct (by decide) h.2.2.2.2.2⟩

theorem characterization_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧ InitsIntoUninit progUseAfterMove ∧
    NoNormalPathToResume progUseAfterMove ∧
    ¬ (ElabCorrect .abort .std (stdMap progUseAfterMove .fine) progUseAfterMove ↔
       AllCompatible progUseAfterMove (stdMap progUseAfterMove .fine)) :=
  have h := stdElab_fails_without_movesFromInit
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    not_iff_of_compatible_not_correct (by decide) h.2.2.2.2.2⟩

theorem characterization_fails_without_initsIntoUninit :
    Forward progOverwrite ∧ PlacesAreMovePaths progOverwrite ∧ MovesFromInit progOverwrite ∧
    ¬ InitsIntoUninit progOverwrite ∧ NoNormalPathToResume progOverwrite ∧
    ¬ (ElabCorrect .abort .std (stdMap progOverwrite .fine) progOverwrite ↔
       AllCompatible progOverwrite (stdMap progOverwrite .fine)) :=
  have h := stdElab_fails_without_initsIntoUninit
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    not_iff_of_compatible_not_correct (by decide) h.2.2.2.2.2⟩

theorem characterization_fails_without_noNormalPathToResume :
    Forward progResumeNormal ∧ PlacesAreMovePaths progResumeNormal ∧
    MovesFromInit progResumeNormal ∧ InitsIntoUninit progResumeNormal ∧
    ¬ NoNormalPathToResume progResumeNormal ∧
    ¬ (ElabCorrect .abort .std (stdMap progResumeNormal .fine) progResumeNormal ↔
       AllCompatible progResumeNormal (stdMap progResumeNormal .fine)) :=
  have h := stdElab_fails_without_noNormalPathToResume
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    not_iff_of_compatible_not_correct (by decide) h.2.2.2.2.2⟩

/-! ## Tightness of the elaboration conditions: one defect at a time -/

/-- (a) A static drop at a join where one predecessor moved the value: double drop. The
elaboration differs from the standard one only in the decision for `x` at node 3. -/
theorem staticDrop_at_join_double_drops :
    Forward progJoin ∧ MoveChecked progJoin ∧ NoNormalPathToResume progJoin ∧
    mayInit progJoin .fine 3 x = true ∧ mustInit progJoin .fine 3 x = false ∧
    (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin [true]).log =
      [.create 0, .consume 0, .drop 0] ∧
    ¬ NoDoubleDrop
      (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin [true]).log := by
  decide

/-- (a') Nothing at the same join: leak on the branch that did not move. -/
theorem staticSkip_at_join_leaks :
    Forward progJoin ∧ MoveChecked progJoin ∧ NoNormalPathToResume progJoin ∧
    (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .skip) progJoin
      [false, false]).outcome = .returned ∧
    (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .skip) progJoin
      [false, false]).log = [.create 0] ∧
    ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .skip) progJoin
      [false, false]).log := by
  decide

/-- (b) The argument flag of a call is cleared only on the call's normal edge: when the call
panics after consuming `x`, the shared cleanup still sees the flag set and drops `x` again.
Only `clearArgsBeforeCall` differs from the standard configuration. -/
theorem argFlagNotClearedOnUnwind_double_drops :
    Forward progCleanup ∧ MoveChecked progCleanup ∧ NoNormalPathToResume progCleanup ∧
    (runElab .abort { FlagConfig.std with clearArgsBeforeCall := false }
      (stdMap progCleanup .fine) progCleanup [false, true, false]).outcome = .unwound ∧
    (runElab .abort { FlagConfig.std with clearArgsBeforeCall := false }
      (stdMap progCleanup .fine) progCleanup [false, true, false]).log =
      [.create 0, .consume 0, .drop 0] ∧
    ¬ NoDoubleDrop (runElab .abort { FlagConfig.std with clearArgsBeforeCall := false }
      (stdMap progCleanup .fine) progCleanup [false, true, false]).log := by
  decide

/-- On `progPartial` (straight-line code, no flag tested) the granularity of the *flag updates*
has no effect at all: the run trees coincide with the standard elaboration's. -/
theorem flagConfig_gran_inert_on_progPartial :
    explore .abort
      (elaborate { FlagConfig.std with gran := .wholeKill } (stdMap progPartial .fine) progPartial)
      (fuelFor progPartial) =
      explore .abort (stdElab progPartial) (fuelFor progPartial) ∧
    explore .abort
      (elaborate { FlagConfig.std with gran := .wholeKeep } (stdMap progPartial .fine) progPartial)
      (fuelFor progPartial) =
      explore .abort (stdElab progPartial) (fuelFor progPartial) := by
  decide

/-- A conditional initialization followed by a conditional partial move: at the `ret`, both
fields of `x` need a dynamic flag, so the granularity of the flag updates matters. -/
def progPartialFlag : SProg :=
  { locals := [pairT], nodes := [.branch 1 4, .init x 2, .branch 3 4, .move x0 4, .ret] }

theorem progPartialFlag_stdElab_correct :
    ElabCorrect .abort .std (stdMap progPartialFlag .fine) progPartialFlag :=
  elabCorrect_of_explore _ _ _ _ (by decide)

/-- (c, analysis) Whole-local *analysis* that treats a partial move as a move of the whole local:
the static decisions computed from it drop nothing at the `ret` of `progPartial`, and the
remaining field leaks. Only the analysis granularity of the decision map differs from the
standard elaboration (flag maintenance is standard; on this program it is inert anyway). -/
theorem wholeKillAnalysis_leaks_remaining_field :
    Forward progPartial ∧ MoveChecked progPartial ∧ NoNormalPathToResume progPartial ∧
    (runElab .abort .std (stdMap progPartial .wholeKill) progPartial []).outcome = .returned ∧
    (runElab .abort .std (stdMap progPartial .wholeKill) progPartial []).log =
      [.create 0, .create 1, .consume 0] ∧
    ¬ NoLeak (runElab .abort .std (stdMap progPartial .wholeKill) progPartial []).log := by
  decide

/-- (c, flags) Whole-local *flag updates* that clear the flags of the whole local at a partial
move: with the standard (fine) decisions, the flag test for the unmoved field `.1` fails and
that field leaks. Only `gran` of the flag configuration differs. -/
theorem wholeKillFlags_leaks_remaining_field :
    Forward progPartialFlag ∧ MoveChecked progPartialFlag ∧ NoNormalPathToResume progPartialFlag ∧
    (runElab .abort { FlagConfig.std with gran := .wholeKill } (stdMap progPartialFlag .fine)
      progPartialFlag [true, true]).outcome = .returned ∧
    (runElab .abort { FlagConfig.std with gran := .wholeKill } (stdMap progPartialFlag .fine)
      progPartialFlag [true, true]).log = [.create 0, .create 1, .consume 0] ∧
    ¬ NoLeak (runElab .abort { FlagConfig.std with gran := .wholeKill }
      (stdMap progPartialFlag .fine) progPartialFlag [true, true]).log := by
  decide

/-- (c', analysis) Whole-local analysis that ignores partial moves: the static decision drops
the moved field. Only the analysis granularity of the decision map differs. -/
theorem wholeKeepAnalysis_drops_moved_field :
    Forward progPartial ∧ MoveChecked progPartial ∧ NoNormalPathToResume progPartial ∧
    (runElab .abort .std (stdMap progPartial .wholeKeep) progPartial []).log =
      [.create 0, .create 1, .consume 0, .drop 1, .drop 0] ∧
    ¬ NoDoubleDrop (runElab .abort .std (stdMap progPartial .wholeKeep) progPartial []).log := by
  decide

/-- (c', flags) Flag updates that ignore partial moves: with the standard decisions, the flag of
the moved field `.0` stays set and the field is dropped again. Only `gran` differs. -/
theorem wholeKeepFlags_drops_moved_field :
    Forward progPartialFlag ∧ MoveChecked progPartialFlag ∧ NoNormalPathToResume progPartialFlag ∧
    (runElab .abort { FlagConfig.std with gran := .wholeKeep } (stdMap progPartialFlag .fine)
      progPartialFlag [true, true, false]).log =
      [.create 0, .create 1, .consume 0, .drop 1, .drop 0] ∧
    ¬ NoDoubleDrop (runElab .abort { FlagConfig.std with gran := .wholeKeep }
      (stdMap progPartialFlag .fine) progPartialFlag [true, true, false]).log := by
  decide

/-- (d) A re-initialization after a move that does not set the flag: the new value leaks. Only
the flag update of the `init` at node 3 is omitted. -/
theorem reinitWithoutFlagSet_leaks :
    Forward progReinit ∧ MoveChecked progReinit ∧ NoNormalPathToResume progReinit ∧
    (runElab .abort { FlagConfig.std with initSetsFlags := fun j => j != 3 }
      (stdMap progReinit .fine) progReinit [true]).outcome = .returned ∧
    (runElab .abort { FlagConfig.std with initSetsFlags := fun j => j != 3 }
      (stdMap progReinit .fine) progReinit [true]).log = [.create 0, .consume 0, .create 1] ∧
    ¬ NoLeak (runElab .abort { FlagConfig.std with initSetsFlags := fun j => j != 3 }
      (stdMap progReinit .fine) progReinit [true]).log := by
  decide

/-! ## Double panic -/

/-- Under the continue-unwinding rule, a destructor panic during cleanup leaves the frame: the
cleanup ladder of `progUnwind` drops field `.1` of `x`, whose destructor panics, and field `.0`
is never destroyed. On this run no value is destroyed twice. -/
theorem continueUnwind_leaks_partially_dropped :
    Forward progUnwind ∧ MoveChecked progUnwind ∧ NoNormalPathToResume progUnwind ∧
    (runElab .continueUnwind .std (stdMap progUnwind .fine) progUnwind [true, true]).outcome =
      .unwound ∧
    (runElab .continueUnwind .std (stdMap progUnwind .fine) progUnwind [true, true]).log =
      [.create 0, .create 1, .drop 1] ∧
    NoDoubleDrop
      (runElab .continueUnwind .std (stdMap progUnwind .fine) progUnwind [true, true]).log ∧
    ¬ NoLeak
      (runElab .continueUnwind .std (stdMap progUnwind .fine) progUnwind [true, true]).log := by
  decide

/-- Under the abort rule the same input aborts (and aborted runs are exempt from NoLeak). -/
theorem abort_on_same_input :
    (runElab .abort .std (stdMap progUnwind .fine) progUnwind [true, true]).outcome = .aborted := by
  decide

/-- Every hypothesis of the continue-unwinding NoDoubleDrop theorem holds for `progUnwind`, and
every run of its standard elaboration under that rule terminates without a double drop. -/
theorem continueUnwind_noDoubleDrop_holds_progUnwind :
    Forward progUnwind ∧ PlacesAreMovePaths progUnwind ∧ MovesFromInit progUnwind ∧
    (explore .continueUnwind (stdElab progUnwind) (fuelFor progUnwind)).all
      (fun r => decide (NoDoubleDrop r.log) && r.outcome.terminated) = true := by
  decide

/-! ## Hypotheses of the continue-unwinding NoDoubleDrop theorem (canonical form) -/

/-- A back edge re-runs a `move`; the one-pass analysis does not see the back edge. -/
def progLoopMove : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .move x 2, .branch 1 3, .ret] }

/-- An `init` of a field of a struct that has its own destructor. -/
def progInitInsideDrop : SProg :=
  { locals := [dropT], nodes := [.init x0 1, .ret] }

theorem noDoubleDrop_continueUnwind_fails_without_forward :
    ¬ Forward progLoopMove ∧ PlacesAreMovePaths progLoopMove ∧ MovesFromInit progLoopMove ∧
    ¬ (∀ inp, NoDoubleDrop
          (runElab .continueUnwind .std (stdMap progLoopMove .fine) progLoopMove inp).log ∧
        (runElab .continueUnwind .std (stdMap progLoopMove .fine) progLoopMove inp).outcome.terminated
          = true) := by
  refine ⟨by decide, by decide, by decide, fun h => ?_⟩
  have := (h [true, false]).1
  revert this; decide

theorem noDoubleDrop_continueUnwind_fails_without_placesAreMovePaths :
    Forward progInitInsideDrop ∧ ¬ PlacesAreMovePaths progInitInsideDrop ∧
    MovesFromInit progInitInsideDrop ∧
    ¬ (∀ inp, NoDoubleDrop (runElab .continueUnwind .std (stdMap progInitInsideDrop .fine)
          progInitInsideDrop inp).log ∧
        (runElab .continueUnwind .std (stdMap progInitInsideDrop .fine)
          progInitInsideDrop inp).outcome.terminated = true) := by
  refine ⟨by decide, by decide, by decide, fun h => ?_⟩
  have := (h []).1
  revert this; decide

theorem noDoubleDrop_continueUnwind_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧
    ¬ (∀ inp, NoDoubleDrop (runElab .continueUnwind .std (stdMap progUseAfterMove .fine)
          progUseAfterMove inp).log ∧
        (runElab .continueUnwind .std (stdMap progUseAfterMove .fine)
          progUseAfterMove inp).outcome.terminated = true) := by
  refine ⟨by decide, by decide, by decide, fun h => ?_⟩
  have := (h []).1
  revert this; decide

/-! ## Necessity results need well-formed places -/

/-- A place that does not follow its local's type (`.1` of a leaf). -/
def badPlace : Place := ⟨0, [true]⟩

/-- An `init` through an ill-typed place on one branch: the analysis treats `x` as may-init at
the `ret`, but no value is created. -/
def progIllTyped : SProg :=
  { locals := [.leaf], nodes := [.branch 1 2, .init badPlace 2, .ret] }

/-- Without `PlacesAreMovePaths`, eliding the flag at a may-init/not-must-init drop point by doing
nothing does not leak: every run of that elaboration is good. -/
theorem staticSkip_correct_without_placesAreMovePaths :
    ¬ PlacesAreMovePaths progIllTyped ∧ isDropPoint progIllTyped 2 = true ∧
    mayInit progIllTyped .fine 2 x = true ∧ mustInit progIllTyped .fine 2 x = false ∧
    ElabCorrect .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip) progIllTyped :=
  ⟨by decide, by decide, by decide, by decide, elabCorrect_of_explore _ _ _ _ (by decide)⟩

/-- Canonical counterexample for the static-choice theorem without `PlacesAreMovePaths`. -/
theorem staticChoice_necessity_fails_without_placesAreMovePaths :
    ¬ PlacesAreMovePaths progIllTyped ∧ isDropPoint progIllTyped 2 = true ∧
    mayInit progIllTyped .fine 2 x = true ∧ mustInit progIllTyped .fine 2 x = false ∧
    ¬ ((∃ inp, ¬ NoDoubleDrop (runElab .abort .std
          (overrideAt (stdMap progIllTyped .fine) 2 x .drop) progIllTyped inp).log) ∧
       (∃ inp,
          (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip) progIllTyped
            inp).outcome.complete = true ∧
          ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip)
            progIllTyped inp).log)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨_, ⟨inp, hc, hl⟩⟩
  have h := staticSkip_correct_without_placesAreMovePaths.2.2.2.2 inp
  exact hl (h.1.2 hc)

/-- `progJoin` with the join moved off the drop point (node 3 is a branch whose two edges both go
to the `ret`). -/
def progJoinOff : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .branch 2 3, .move x 3, .branch 4 4, .ret] }

/-- A program whose drop point sees `x` definitely uninitialized. -/
def progMoved : SProg := { locals := [.leaf], nodes := [.init x 1, .move x 2, .ret] }

/-- A program whose drop point sees `x` definitely initialized. -/
def progKept : SProg := { locals := [.leaf], nodes := [.init x 1, .ret] }

theorem progJoinOff_override_correct :
    ElabCorrect .abort .std (overrideAt (stdMap progJoinOff .fine) 3 x .drop) progJoinOff :=
  elabCorrect_of_explore _ _ _ _ (by decide)
theorem progMoved_skip_correct :
    ElabCorrect .abort .std (overrideAt (stdMap progMoved .fine) 2 x .skip) progMoved :=
  elabCorrect_of_explore _ _ _ _ (by decide)
theorem progKept_drop_correct :
    ElabCorrect .abort .std (overrideAt (stdMap progKept .fine) 1 x .drop) progKept :=
  elabCorrect_of_explore _ _ _ _ (by decide)

/-- Canonical counterexample without `isDropPoint`: at node 3 of `progJoinOff`, `x` is may-init
and not must-init, but node 3 is not a drop point, so overriding its decision changes nothing and
every run of the "unconditional drop" override is good. -/
theorem staticChoice_necessity_fails_at_non_drop_point :
    PlacesAreMovePaths progJoinOff ∧ ¬ (isDropPoint progJoinOff 3 = true) ∧
    mayInit progJoinOff .fine 3 x = true ∧ mustInit progJoinOff .fine 3 x = false ∧
    ¬ ((∃ inp, ¬ NoDoubleDrop (runElab .abort .std
          (overrideAt (stdMap progJoinOff .fine) 3 x .drop) progJoinOff inp).log) ∧
       (∃ inp,
          (runElab .abort .std (overrideAt (stdMap progJoinOff .fine) 3 x .skip) progJoinOff
            inp).outcome.complete = true ∧
          ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progJoinOff .fine) 3 x .skip)
            progJoinOff inp).log)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨⟨inp, hdd⟩, _⟩
  exact hdd (progJoinOff_override_correct inp).1.1

/-- Canonical counterexample without `mayInit`: doing nothing for a definitely-uninitialized
atom is correct, so the "nothing leaks" half fails. -/
theorem staticChoice_necessity_fails_without_mayInit :
    PlacesAreMovePaths progMoved ∧ isDropPoint progMoved 2 = true ∧
    ¬ (mayInit progMoved .fine 2 x = true) ∧ mustInit progMoved .fine 2 x = false ∧
    ¬ ((∃ inp, ¬ NoDoubleDrop (runElab .abort .std
          (overrideAt (stdMap progMoved .fine) 2 x .drop) progMoved inp).log) ∧
       (∃ inp,
          (runElab .abort .std (overrideAt (stdMap progMoved .fine) 2 x .skip) progMoved
            inp).outcome.complete = true ∧
          ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progMoved .fine) 2 x .skip)
            progMoved inp).log)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨_, ⟨inp, hc, hl⟩⟩
  exact hl ((progMoved_skip_correct inp).1.2 hc)

/-- Canonical counterexample without `¬ mustInit`: an unconditional drop of a
definitely-initialized atom is correct, so the "double drop" half fails. -/
theorem staticChoice_necessity_fails_without_notMustInit :
    PlacesAreMovePaths progKept ∧ isDropPoint progKept 1 = true ∧
    mayInit progKept .fine 1 x = true ∧ ¬ (mustInit progKept .fine 1 x = false) ∧
    ¬ ((∃ inp, ¬ NoDoubleDrop (runElab .abort .std
          (overrideAt (stdMap progKept .fine) 1 x .drop) progKept inp).log) ∧
       (∃ inp,
          (runElab .abort .std (overrideAt (stdMap progKept .fine) 1 x .skip) progKept
            inp).outcome.complete = true ∧
          ¬ NoLeak (runElab .abort .std (overrideAt (stdMap progKept .fine) 1 x .skip)
            progKept inp).log)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨⟨inp, hdd⟩, _⟩
  exact hdd (progKept_drop_correct inp).1.1

/-- Canonical counterexample for "may-init implies forward-reachable and atom" without its
premise: node 1 below is neither may-init for `x` nor forward-reachable. -/
theorem forwardReachable_fails_without_mayInit :
    ¬ (mayInit { locals := [.leaf], nodes := [.ret, .init x 2, .ret] } .fine 1 x = true) ∧
    ¬ (ForwardReachable { locals := [.leaf], nodes := [.ret, .init x 2, .ret] } 1 = true ∧
       x ∈ allAtoms ({ locals := [.leaf], nodes := [.ret, .init x 2, .ret] } : SProg).locals) := by
  decide

/-- Canonical counterexample for the necessity half of the characterization without
`PlacesAreMovePaths`: every run of the "nothing" override is exactly-once, but the override is
not compatible at node 2. -/
theorem allCompatible_necessity_fails_without_placesAreMovePaths :
    ¬ PlacesAreMovePaths progIllTyped ∧
    (∀ inp, ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip) progIllTyped inp)) ∧
    ¬ AllCompatible progIllTyped (overrideAt (stdMap progIllTyped .fine) 2 x .skip) :=
  ⟨by decide, fun inp => (staticSkip_correct_without_placesAreMovePaths.2.2.2.2 inp).1,
    by decide⟩

/-- Canonical counterexample for the necessity half without the exactly-once hypothesis. -/
theorem allCompatible_necessity_fails_without_exactlyOnce :
    PlacesAreMovePaths progJoin ∧
    ¬ (∀ inp, ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin inp)) ∧
    ¬ AllCompatible progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop) := by
  refine ⟨by decide, fun h => ?_, by decide⟩
  have := h [true]
  revert this; decide

/-- Canonical counterexample for the flag lower bound without `PlacesAreMovePaths`. -/
theorem flagSubset_fails_without_placesAreMovePaths :
    ¬ PlacesAreMovePaths progIllTyped ∧
    (∀ inp, ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip) progIllTyped inp)) ∧
    ¬ (∀ a ∈ flagSet progIllTyped (stdMap progIllTyped .fine),
        a ∈ flagSet progIllTyped (overrideAt (stdMap progIllTyped .fine) 2 x .skip)) :=
  ⟨by decide, fun inp => (staticSkip_correct_without_placesAreMovePaths.2.2.2.2 inp).1,
    by decide⟩

/-- Canonical counterexample for the flag lower bound without the exactly-once hypothesis. -/
theorem flagSubset_fails_without_exactlyOnce :
    PlacesAreMovePaths progJoin ∧
    ¬ (∀ inp, ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin inp)) ∧
    ¬ (∀ a ∈ flagSet progJoin (stdMap progJoin .fine),
        a ∈ flagSet progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop)) :=
  ⟨allCompatible_necessity_fails_without_exactlyOnce.1,
    allCompatible_necessity_fails_without_exactlyOnce.2.1, by decide⟩

/-- Canonical counterexample for "fewer flags is not exactly-once" without
`PlacesAreMovePaths`. -/
theorem fewerFlags_fails_without_placesAreMovePaths :
    ¬ PlacesAreMovePaths progIllTyped ∧
    (flagSet progIllTyped (overrideAt (stdMap progIllTyped .fine) 2 x .skip)).length <
      (flagSet progIllTyped (stdMap progIllTyped .fine)).length ∧
    ¬ (∃ inp, ¬ ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progIllTyped .fine) 2 x .skip) progIllTyped inp)) :=
  ⟨by decide, by decide,
    fun ⟨inp, h⟩ => h (staticSkip_correct_without_placesAreMovePaths.2.2.2.2 inp).1⟩

/-- Canonical counterexample for "fewer flags is not exactly-once" without "strictly fewer":
the standard map itself. -/
theorem fewerFlags_fails_without_lt :
    PlacesAreMovePaths progJoin ∧
    ¬ ((flagSet progJoin (stdMap progJoin .fine)).length <
        (flagSet progJoin (stdMap progJoin .fine)).length) ∧
    ¬ (∃ inp, ¬ ExactlyOnce (runElab .abort .std (stdMap progJoin .fine) progJoin inp)) :=
  ⟨by decide, by decide, fun ⟨inp, h⟩ => h (progJoin_stdElab_correct inp).1⟩

/-! ## Non-vacuity witnesses for the other main results -/

/-- The static-choice theorem's hypotheses hold at node 3 of `progJoin` for `x` (both halves of
its conclusion are exhibited by `staticDrop_at_join_double_drops`, `staticSkip_at_join_leaks`). -/
theorem staticChoice_hypotheses_hold_progJoin :
    PlacesAreMovePaths progJoin ∧ isDropPoint progJoin 3 = true ∧
    mayInit progJoin .fine 3 x = true ∧ mustInit progJoin .fine 3 x = false := by decide

/-- "May-init implies forward-reachable and atom" at node 3 of `progJoin`. -/
theorem mayInit_witness_progJoin :
    mayInit progJoin .fine 3 x = true ∧ ForwardReachable progJoin 3 = true ∧
    x ∈ allAtoms progJoin.locals := by decide

/-- Testing `x` at every drop point of `progJoin` is elaboration-correct. -/
theorem testEverywhere_correct_progJoin :
    ElabCorrect .abort .std (fun _ _ => .test) progJoin :=
  elabCorrect_of_explore _ _ _ _ (by decide)

/-- The hypotheses of the necessity half of the characterization (and of the flag lower bound)
hold for a non-standard decision map: testing `x` everywhere in `progJoin`. -/
theorem allCompatible_necessity_hypotheses_hold_progJoin :
    PlacesAreMovePaths progJoin ∧
    ∀ inp, ExactlyOnce (runElab .abort .std (fun _ _ => .test) progJoin inp) :=
  ⟨by decide, fun inp => (testEverywhere_correct_progJoin inp).1⟩

/-- The flag-lower-bound hypotheses with a correct decision map other than the standard one:
testing `x` everywhere in `progJoin`; its flag set contains the standard one. -/
theorem stdFlagSet_subset_witness_progJoin :
    PlacesAreMovePaths progJoin ∧
    (∀ inp, ExactlyOnce (runElab .abort .std (fun _ _ => .test) progJoin inp)) ∧
    flagSet progJoin (fun _ _ => .test) = [x] ∧
    flagSet progJoin (stdMap progJoin .fine) = [x] :=
  ⟨by decide, fun inp => (testEverywhere_correct_progJoin inp).1, by decide, by decide⟩

/-- The fewer-flags hypotheses: the decision map that drops `x` unconditionally at the join of
`progJoin` tests no atom, the standard map tests one, and the smaller map has a run that is not
exactly-once. -/
theorem fewerFlags_hypotheses_hold_progJoin :
    PlacesAreMovePaths progJoin ∧
    (flagSet progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop)).length <
      (flagSet progJoin (stdMap progJoin .fine)).length ∧
    ∃ inp, ¬ ExactlyOnce
      (runElab .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin inp) :=
  ⟨by decide, by decide, ⟨[true], by decide⟩⟩

/-! ## The lower bound is relative to same-CFG, one-flag-per-atom elaboration -/

/-- A hand-written flag-free target program for `progJoin` that duplicates the join: the
branch that moved `x` returns directly, the other drops `x` unconditionally. -/
def dupNode : Nat → TNode Nat
  | 0 => .init x 1
  | 1 => .branch 2 4
  | 2 => .move x 3
  | 3 => .ret
  | 4 => .drop x 5 (some 6)
  | 5 => .ret
  | 6 => .resume
  | _ => .abort

/-- The duplicated program. -/
def dupProg : TProg Nat := { locals := progJoin.locals, entry := 0, node := dupNode }

/-- The duplicated program contains no flag test at any label. -/
theorem dupProg_no_flag_test : ∀ l a t f, dupProg.node l ≠ .test a t f := by
  intro l a t f h
  simp only [dupProg] at h
  unfold dupNode at h
  split at h <;> cases h

/-- On every input, the flag-free duplicated program behaves exactly like the standard
elaboration of `progJoin` (same outcome, same log), yet the standard elaboration tests one
flag. -/
theorem dupProg_matches_stdElab_progJoin :
    explore .abort dupProg 10 = explore .abort (stdElab progJoin) (fuelFor progJoin) ∧
    flagSet progJoin (stdMap progJoin .fine) = [x] := by
  decide

/-- Corollary form: equal runs on every input. -/
theorem dupProg_run_eq (inp : List Bool) :
    run .abort dupProg 10 inp = runElab .abort .std (stdMap progJoin .fine) progJoin inp :=
  run_eq_of_explore_eq _ _ _ _ _ dupProg_matches_stdElab_progJoin.1 inp

/-- A hand-written target program for `progShare` that uses the flag of `x.0` for both fields
(they are always moved together). -/
def shareNode : Nat → TNode Nat
  | 0 => .init x 1
  | 1 => .setFlags [(x0, true)] 2
  | 2 => .branch 3 6
  | 3 => .move x0 4
  | 4 => .move x1 5
  | 5 => .setFlags [(x0, false)] 6
  | 6 => .test x0 7 13
  | 7 => .drop x1 8 (some 10)
  | 8 => .drop x0 9 (some 12)
  | 9 => .ret
  | 10 => .drop x0 11 none
  | 11 => .resume
  | 12 => .resume
  | 13 => .ret
  | _ => .abort

/-- The shared-flag program. -/
def shareProg : TProg Nat := { locals := progShare.locals, entry := 0, node := shareNode }

/-- The shared-flag program tests only the flag of `x.0`. -/
theorem shareProg_tests_only_x0 : ∀ l a t f, shareProg.node l = .test a t f → a = x0 := by
  intro l a t f h
  simp only [shareProg] at h
  unfold shareNode at h
  split at h <;> first | (cases h; rfl) | cases h

/-- On every input, the one-flag program behaves exactly like the standard elaboration of
`progShare`, which tests two flags. -/
theorem shareProg_matches_stdElab_progShare :
    explore .abort shareProg 16 = explore .abort (stdElab progShare) (fuelFor progShare) ∧
    flagSet progShare (stdMap progShare .fine) = [x0, x1] := by
  decide

/-- A hand-written flag-free target program for `progJoin` that keeps a single shared `ret` but
drops `x` early, on the branch that did not move it, before the two branches merge. -/
def earlyDropNode : Nat → TNode Nat
  | 0 => .init x 1
  | 1 => .branch 2 3
  | 2 => .move x 4
  | 3 => .drop x 4 (some 5)
  | 4 => .ret
  | 5 => .resume
  | _ => .abort

/-- The early-drop program. -/
def earlyDropProg : TProg Nat := { locals := progJoin.locals, entry := 0, node := earlyDropNode }

/-- The early-drop program contains no flag test at any label. -/
theorem earlyDropProg_no_flag_test : ∀ l a t f, earlyDropProg.node l ≠ .test a t f := by
  intro l a t f h
  simp only [earlyDropProg] at h
  unfold earlyDropNode at h
  split at h <;> cases h

/-- On every input, the early-drop program behaves exactly like the standard elaboration of
`progJoin` (which tests one flag), without duplicating the exit. -/
theorem earlyDropProg_matches_stdElab_progJoin :
    explore .abort earlyDropProg 10 = explore .abort (stdElab progJoin) (fuelFor progJoin) := by
  decide

/-! ## The "least flag set" corollary needs every hypothesis of the exactly-once theorem

Its conclusion starts with "the standard map is elaboration-correct", so each counterexample to
the exactly-once theorem is also a counterexample here (canonical form). -/

theorem stdFlagLeast_fails_without_forward :
    ¬ Forward progLoop ∧ PlacesAreMovePaths progLoop ∧ MovesFromInit progLoop ∧
    InitsIntoUninit progLoop ∧ NoNormalPathToResume progLoop ∧
    ¬ (ElabCorrect .abort .std (stdMap progLoop .fine) progLoop ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progLoop →
         ∀ a ∈ flagSet progLoop (stdMap progLoop .fine), a ∈ flagSet progLoop d) :=
  have h := stdElab_fails_without_forward
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun hc => h.2.2.2.2.2 hc.1⟩

theorem stdFlagLeast_fails_without_placesAreMovePaths :
    Forward progDropStruct ∧ ¬ PlacesAreMovePaths progDropStruct ∧
    MovesFromInit progDropStruct ∧ InitsIntoUninit progDropStruct ∧
    NoNormalPathToResume progDropStruct ∧
    ¬ (ElabCorrect .abort .std (stdMap progDropStruct .fine) progDropStruct ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progDropStruct →
         ∀ a ∈ flagSet progDropStruct (stdMap progDropStruct .fine),
           a ∈ flagSet progDropStruct d) :=
  have h := stdElab_fails_without_placesAreMovePaths
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun hc => h.2.2.2.2.2 hc.1⟩

theorem stdFlagLeast_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧ InitsIntoUninit progUseAfterMove ∧
    NoNormalPathToResume progUseAfterMove ∧
    ¬ (ElabCorrect .abort .std (stdMap progUseAfterMove .fine) progUseAfterMove ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progUseAfterMove →
         ∀ a ∈ flagSet progUseAfterMove (stdMap progUseAfterMove .fine),
           a ∈ flagSet progUseAfterMove d) :=
  have h := stdElab_fails_without_movesFromInit
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun hc => h.2.2.2.2.2 hc.1⟩

theorem stdFlagLeast_fails_without_initsIntoUninit :
    Forward progOverwrite ∧ PlacesAreMovePaths progOverwrite ∧ MovesFromInit progOverwrite ∧
    ¬ InitsIntoUninit progOverwrite ∧ NoNormalPathToResume progOverwrite ∧
    ¬ (ElabCorrect .abort .std (stdMap progOverwrite .fine) progOverwrite ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progOverwrite →
         ∀ a ∈ flagSet progOverwrite (stdMap progOverwrite .fine), a ∈ flagSet progOverwrite d) :=
  have h := stdElab_fails_without_initsIntoUninit
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun hc => h.2.2.2.2.2 hc.1⟩

theorem stdFlagLeast_fails_without_noNormalPathToResume :
    Forward progResumeNormal ∧ PlacesAreMovePaths progResumeNormal ∧
    MovesFromInit progResumeNormal ∧ InitsIntoUninit progResumeNormal ∧
    ¬ NoNormalPathToResume progResumeNormal ∧
    ¬ (ElabCorrect .abort .std (stdMap progResumeNormal .fine) progResumeNormal ∧
       ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d progResumeNormal →
         ∀ a ∈ flagSet progResumeNormal (stdMap progResumeNormal .fine),
           a ∈ flagSet progResumeNormal d) :=
  have h := stdElab_fails_without_noNormalPathToResume
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun hc => h.2.2.2.2.2 hc.1⟩

/-! ## The sufficiency theorem needs each of its hypotheses (canonical form)

The standard map is compatible on every program (`stdDecision_compatible`), so each
counterexample to the exactly-once theorem, with `d := stdMap s .fine`, satisfies the
compatibility hypothesis while its conclusion fails. -/

theorem stdMap_allCompatible (s : SProg) : AllCompatible s (stdMap s .fine) :=
  fun _ _ _ _ _ _ => stdDecision_compatible _ _

theorem sufficiency_fails_without_forward :
    ¬ Forward progLoop ∧ PlacesAreMovePaths progLoop ∧ MovesFromInit progLoop ∧
    InitsIntoUninit progLoop ∧ NoNormalPathToResume progLoop ∧
    AllCompatible progLoop (stdMap progLoop .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progLoop .fine) progLoop :=
  have h := stdElab_fails_without_forward
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, stdMap_allCompatible _, h.2.2.2.2.2⟩

theorem sufficiency_fails_without_placesAreMovePaths :
    Forward progDropStruct ∧ ¬ PlacesAreMovePaths progDropStruct ∧
    MovesFromInit progDropStruct ∧ InitsIntoUninit progDropStruct ∧
    NoNormalPathToResume progDropStruct ∧
    AllCompatible progDropStruct (stdMap progDropStruct .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progDropStruct .fine) progDropStruct :=
  have h := stdElab_fails_without_placesAreMovePaths
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, stdMap_allCompatible _, h.2.2.2.2.2⟩

theorem sufficiency_fails_without_movesFromInit :
    Forward progUseAfterMove ∧ PlacesAreMovePaths progUseAfterMove ∧
    ¬ MovesFromInit progUseAfterMove ∧ InitsIntoUninit progUseAfterMove ∧
    NoNormalPathToResume progUseAfterMove ∧
    AllCompatible progUseAfterMove (stdMap progUseAfterMove .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progUseAfterMove .fine) progUseAfterMove :=
  have h := stdElab_fails_without_movesFromInit
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, stdMap_allCompatible _, h.2.2.2.2.2⟩

theorem sufficiency_fails_without_initsIntoUninit :
    Forward progOverwrite ∧ PlacesAreMovePaths progOverwrite ∧ MovesFromInit progOverwrite ∧
    ¬ InitsIntoUninit progOverwrite ∧ NoNormalPathToResume progOverwrite ∧
    AllCompatible progOverwrite (stdMap progOverwrite .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progOverwrite .fine) progOverwrite :=
  have h := stdElab_fails_without_initsIntoUninit
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, stdMap_allCompatible _, h.2.2.2.2.2⟩

theorem sufficiency_fails_without_noNormalPathToResume :
    Forward progResumeNormal ∧ PlacesAreMovePaths progResumeNormal ∧
    MovesFromInit progResumeNormal ∧ InitsIntoUninit progResumeNormal ∧
    ¬ NoNormalPathToResume progResumeNormal ∧
    AllCompatible progResumeNormal (stdMap progResumeNormal .fine) ∧
    ¬ ElabCorrect .abort .std (stdMap progResumeNormal .fine) progResumeNormal :=
  have h := stdElab_fails_without_noNormalPathToResume
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, stdMap_allCompatible _, h.2.2.2.2.2⟩

/-- Without compatibility: an unconditional drop at the join of `progJoin`, on a program
satisfying the other five hypotheses. -/
theorem sufficiency_fails_without_allCompatible :
    Forward progJoin ∧ PlacesAreMovePaths progJoin ∧ MovesFromInit progJoin ∧
    InitsIntoUninit progJoin ∧ NoNormalPathToResume progJoin ∧
    ¬ AllCompatible progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop) ∧
    ¬ ElabCorrect .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin :=
  ⟨by decide, by decide, by decide, by decide, by decide, allCompatible_neg, elabCorrect_neg⟩

/-- All hypotheses of the sufficiency theorem hold for a non-standard decision map: testing `x`
at every drop point of `progJoin`. -/
theorem sufficiency_hypotheses_hold_progJoin_testEverywhere :
    Forward progJoin ∧ PlacesAreMovePaths progJoin ∧ MovesFromInit progJoin ∧
    InitsIntoUninit progJoin ∧ NoNormalPathToResume progJoin ∧
    AllCompatible progJoin (fun _ _ => .test) := by decide

end Toy.DropFlags
