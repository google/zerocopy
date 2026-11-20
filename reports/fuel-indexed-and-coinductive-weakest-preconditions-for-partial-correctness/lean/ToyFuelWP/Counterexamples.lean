import ToyFuelWP.Examples

/-!
# Counterexamples, non-vacuity witnesses and positive controls (fully proved)

Every tightness counterexample is stated in canonical form: a concrete
instance in which all hypotheses of the named theorem other than the dropped
one hold, and the conclusion fails (often the dropped hypothesis is also shown
to fail). Every non-vacuity theorem exhibits a concrete instance satisfying all
hypotheses of the named theorem.

This module does not import `ToyFuelWP.Statements`.
-/

namespace Toy.FuelWP

/-! ## Partial correctness: every fuel ⇔ greatest fixpoint -/

/-- Counterexample for `wpGfp_of_forall_wpFuel` with "every fuel" weakened to
"one fixed fuel": for every fuel `n`, the state `n` of `downToStuckSys`
satisfies `wpFuel … n …` but not `wpFuel … m …` for every `m` (it fails at
`m = n + 1`), and not `wpGfp`. (The state depends on `n`; by
`wpGfp_of_forall_wpFuel` no single state can work for all `n`.) -/
theorem fixed_fuel_wpFuel_not_imp_wpGfp (n : Nat) :
    wpFuel downToStuckSys n (fun _ => True) n ∧
      ¬ (∀ m, wpFuel downToStuckSys m (fun _ => True) n) ∧
      ¬ wpGfp downToStuckSys (fun _ => True) n :=
  ⟨downToStuckSys_wpFuel n n (Nat.le_refl n), fun h => downToStuckSys_not_wpFuel n (h (n + 1)),
    downToStuckSys_not_wpGfp n⟩

/-- Counterexample for the hypothesis `h : wpGfp S Q s` of `wpFuel_of_wpGfp`
(instance `S := stuckSys`, `Q := True`, `s := ()`, `n := 1`): the hypothesis
fails and so does the conclusion `wpFuel stuckSys 1 (fun _ => True) ()`. -/
theorem stuckSys_not_wpGfp_not_wpFuel_one :
    ¬ wpGfp stuckSys (fun _ => True) () ∧ ¬ wpFuel stuckSys 1 (fun _ => True) () :=
  ⟨wpGfp_neg_stuck, wpFuel_neg_stuck⟩

/-- Non-vacuity for `forall_wpFuel_iff_wpGfp`, `wpFuel_of_wpGfp` and
`wpGfp_of_forall_wpFuel`: both sides hold for a terminating run (`chainSys`
from `3`, postcondition `(· = 0)`) and for a diverging run (`loopSys`,
postcondition `False`). -/
theorem nonvacuity_forall_wpFuel_and_wpGfp :
    ((∀ n, wpFuel chainSys n (fun s => s = 0) 3) ∧ wpGfp chainSys (fun s => s = 0) 3) ∧
      ((∀ n, wpFuel loopSys n (fun _ => False) ()) ∧ wpGfp loopSys (fun _ => False) ()) :=
  ⟨⟨fun n => chainSys_wpFuel n 3, chainSys_wpGfp 3⟩,
    ⟨fun n => wpFuel_of_alwaysDiverges loopSys_alwaysDiverges n _, wpGfp_pos_loop_false⟩⟩

/-! ## Fuel monotonicity -/

/-- Counterexample for the hypothesis `n ≤ m` of `wpFuel_antitone`: with
`n = 1`, `m = 0`, `wpFuel stuckSys 0 …` holds and `wpFuel stuckSys 1 …` fails,
so partial-correctness fuel WP is not monotone. -/
theorem wpFuel_not_monotone_stuck :
    ¬ (1 ≤ 0) ∧ wpFuel stuckSys 0 (fun _ => True) () ∧ ¬ wpFuel stuckSys 1 (fun _ => True) () :=
  ⟨by decide, trivial, wpFuel_neg_stuck⟩

/-- Counterexample for the hypothesis `n ≤ m` of `wpFuelTotal_monotone`: with
`n = 1`, `m = 0`, `wpFuelTotal doneSys 1 …` holds and `wpFuelTotal doneSys 0 …`
fails, so total-correctness fuel WP is not antitone. -/
theorem wpFuelTotal_not_antitone_done :
    ¬ (1 ≤ 0) ∧ wpFuelTotal doneSys 1 (fun _ => True) () ∧
      ¬ wpFuelTotal doneSys 0 (fun _ => True) () :=
  ⟨by decide, doneSys_wpFuelTotal_one, fun h => h⟩

/-- Canonical counterexample for the hypothesis `h : wpFuel S m Q s` of
`wpFuel_antitone` (instance `S := stuckSys`, `Q := True`, `s := ()`, `n := 1`,
`m := 2`): the other hypothesis `1 ≤ 2` holds, `h` fails, and the conclusion
`wpFuel stuckSys 1 (fun _ => True) ()` fails. -/
theorem wpFuel_antitone_drop_h :
    1 ≤ 2 ∧ ¬ wpFuel stuckSys 2 (fun _ => True) () ∧ ¬ wpFuel stuckSys 1 (fun _ => True) () := by
  refine ⟨by decide, fun h => ?_, wpFuel_neg_stuck⟩
  obtain ⟨_, ht⟩ := (h.2 (fun hf => hf)).1
  exact ht

/-- Canonical counterexample for the hypothesis `h : wpFuelTotal S n Q s` of
`wpFuelTotal_monotone` (instance `S := stuckSys`, `Q := True`, `s := ()`,
`n := 1`, `m := 2`): the other hypothesis `1 ≤ 2` holds, `h` fails, and the
conclusion `wpFuelTotal stuckSys 2 (fun _ => True) ()` fails. -/
theorem wpFuelTotal_monotone_drop_h :
    1 ≤ 2 ∧ ¬ wpFuelTotal stuckSys 1 (fun _ => True) () ∧
      ¬ wpFuelTotal stuckSys 2 (fun _ => True) () := by
  refine ⟨by decide, fun h => ?_, fun h => ?_⟩
  · obtain ⟨_, ht⟩ := (h.2 (fun hf => hf)).1
    exact ht
  · obtain ⟨_, ht⟩ := (h.2 (fun hf => hf)).1
    exact ht

/-- Counterexample for the hypothesis `h` of `wpGfp_of_wpFuelTotal`
(`h : wpFuelTotal S n Q s`) and of `wpLfp_of_exists_wpFuelTotal`
(`h : ∃ n, wpFuelTotal S n Q s`); neither theorem has other hypotheses. At a
stuck state, `wpFuelTotal` fails at every fuel and both conclusions (`wpGfp`,
`wpLfp`) fail. -/
theorem stuckSys_no_total_no_partial :
    (∀ n, ¬ wpFuelTotal stuckSys n (fun _ => True) ()) ∧
      ¬ wpGfp stuckSys (fun _ => True) () ∧ ¬ wpLfp stuckSys (fun _ => True) () := by
  refine ⟨fun n h => ?_, wpGfp_neg_stuck, wpLfp_neg_stuck⟩
  cases n with
  | zero => exact h
  | succ n =>
    obtain ⟨_, ht⟩ := (h.2 (fun hf => hf)).1
    exact ht

/-- Non-vacuity for `wpFuel_antitone`: `1 ≤ 3` and `wpFuel loopSys 3 …`. -/
theorem nonvacuity_wpFuel_antitone : 1 ≤ 3 ∧ wpFuel loopSys 3 (fun _ => False) () :=
  ⟨by decide, wpFuel_of_alwaysDiverges loopSys_alwaysDiverges 3 _⟩

/-- Non-vacuity for `wpFuelTotal_monotone`, `wpGfp_of_wpFuelTotal`,
`wpLfp_of_exists_wpFuelTotal` and `wpFuelTotal_iff_wpFuel_and_no_reach`:
`4 ≤ 6` and `wpFuelTotal chainSys 4 (· = 0) 3`. -/
theorem nonvacuity_wpFuelTotal : 4 ≤ 6 ∧ wpFuelTotal chainSys 4 (fun s => s = 0) 3 :=
  ⟨by decide, chainSys_wpFuelTotal 3⟩

/-- Non-vacuity for `wpFuel_iff_forall_reach_lt`: an instance where the
left-hand side holds although an error is reachable (at distance `3`), and one
where it fails (fuel `4`). -/
theorem nonvacuity_wpFuel_iff_forall_reach_lt :
    wpFuel downToStuckSys 3 (fun _ => True) 3 ∧ ¬ wpFuel downToStuckSys 4 (fun _ => True) 3 :=
  ⟨wpFuel_pos_error_out_of_range, wpFuel_neg_error_in_range⟩

/-! ## Total correctness -/

/-- **Unbounded choice: total correctness without a uniform fuel bound.**
Counterexample for the finite-branching hypotheses of
`exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom`,
`exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching`,
`exists_wpFuelTotal_iff_wpLfp_of_deterministic` and
`exists_wpFuelTotal_of_wpGfp_of_not_hasInfiniteRun_of_finitelyBranchingFrom`.
In `countdownSys` (`x := ?; while x > 0 do x := x - 1`) the state `start` is not
finitely branching and the system is not deterministic, yet `start` satisfies
`wpLfp`, `wpGfp` and has no infinite run; but no fuel `n` gives
`wpFuelTotal countdownSys n (fun _ => True) start`. -/
theorem countdown_wpLfp_without_uniform_fuel :
    ¬ FinitelyBranchingFrom countdownSys .start ∧ ¬ FinitelyBranching countdownSys ∧
      ¬ Deterministic countdownSys ∧
      wpLfp countdownSys (fun _ => True) .start ∧ wpGfp countdownSys (fun _ => True) .start ∧
      ¬ HasInfiniteRun countdownSys .start ∧
      ¬ ∃ n, wpFuelTotal countdownSys n (fun _ => True) .start := by
  refine ⟨countdownSys_not_finitelyBranchingFrom_start, finitelyBranching_neg_countdown,
    deterministic_neg_countdown, countdownSys_start_wpLfp, ?_, ?_, ?_⟩
  · refine ⟨wpLfp countdownSys (fun _ => True), fun t ht => (wpLfp_unfold _ _ _).mp ht,
      countdownSys_start_wpLfp⟩
  · exact fun h => not_wpLfp_of_hasInfiniteRun h _ countdownSys_start_wpLfp
  · rintro ⟨n, hn⟩
    exact countdownSys_start_no_fuel n hn

/-- Canonical counterexample for the hypotheses `hfb : FinitelyBranching S` of
`exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching` and `hdet : Deterministic S`
of `exists_wpFuelTotal_iff_wpLfp_of_deterministic` (neither corollary has other
hypotheses): `countdownSys` is neither finitely branching nor deterministic,
and the equivalence fails at `start`. -/
theorem countdown_exists_wpFuelTotal_iff_wpLfp_fails :
    ¬ FinitelyBranching countdownSys ∧ ¬ Deterministic countdownSys ∧
      ¬ ((∃ n, wpFuelTotal countdownSys n (fun _ => True) .start) ↔
        wpLfp countdownSys (fun _ => True) .start) :=
  ⟨finitelyBranching_neg_countdown, deterministic_neg_countdown,
    fun h => countdown_wpLfp_without_uniform_fuel.2.2.2.2.2.2 (h.mpr countdownSys_start_wpLfp)⟩

/-- Counterexample for the hypotheses `wpLfp S Q s` of
`exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom` and
`¬ HasInfiniteRun S s` of the König form: `loopSys` is finitely branching and
satisfies `wpGfp`, but has an infinite run, fails `wpLfp`, and no fuel works. -/
theorem loop_finitelyBranching_no_total_fuel :
    FinitelyBranching loopSys ∧ FinitelyBranchingFrom loopSys () ∧
      wpGfp loopSys (fun _ => True) () ∧ HasInfiniteRun loopSys () ∧
      ¬ wpLfp loopSys (fun _ => True) () ∧
      ¬ ∃ n, wpFuelTotal loopSys n (fun _ => True) () :=
  ⟨finitelyBranching_pos_loop, finitelyBranchingFrom_of_finitelyBranching finitelyBranching_pos_loop (),
    wpGfp_of_alwaysDiverges loopSys_alwaysDiverges _, loopSys_hasInfiniteRun, wpLfp_neg_loop,
    fun ⟨n, hn⟩ => not_wpFuelTotal_of_hasInfiniteRun loopSys_hasInfiniteRun n _ hn⟩

/-- Counterexample for the hypothesis `wpGfp S Q s` of the König form:
`stuckSys` is finitely branching and has no infinite run (its only run ends
at once, in an error), but it fails `wpGfp`, so no fuel works. -/
theorem stuck_finitelyBranching_no_infinite_run_no_total_fuel :
    FinitelyBranchingFrom stuckSys () ∧ ¬ HasInfiniteRun stuckSys () ∧
      ¬ wpGfp stuckSys (fun _ => True) () ∧
      ¬ ∃ n, wpFuelTotal stuckSys n (fun _ => True) () :=
  ⟨fun _ _ _ _ => ⟨[], fun _ h => h.elim⟩, stuckSys_not_hasInfiniteRun, wpGfp_neg_stuck,
    fun ⟨n, hn⟩ => stuckSys_no_total_no_partial.1 n hn⟩

/-- Non-vacuity for `exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom`:
(i) `chainSys` from `3`; (ii) the countdown state `count 3` of `countdownSys`,
which is finitely branching locally although the system is not globally. -/
theorem nonvacuity_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom :
    (FinitelyBranchingFrom chainSys 3 ∧ wpLfp chainSys (fun s => s = 0) 3) ∧
      (FinitelyBranchingFrom countdownSys (.count 3) ∧
        wpLfp countdownSys (fun _ => True) (.count 3)) :=
  ⟨⟨finitelyBranchingFrom_of_finitelyBranching chainSys_finitelyBranching 3, chainSys_wpLfp 3⟩,
    ⟨finitelyBranchingFrom_pos_countdown_count, countdownSys_count_wpLfp 3⟩⟩

/-- Non-vacuity for the global-finite-branching and deterministic corollaries:
`chainSys` is deterministic and finitely branching, and `3` satisfies `wpLfp`. -/
theorem nonvacuity_exists_wpFuelTotal_iff_wpLfp_corollaries :
    Deterministic chainSys ∧ FinitelyBranching chainSys ∧ wpLfp chainSys (fun s => s = 0) 3 :=
  ⟨chainSys_deterministic, chainSys_finitelyBranching, chainSys_wpLfp 3⟩

/-- Non-vacuity for `wpLfp_iff_wpGfp_and_not_hasInfiniteRun`: both sides hold
at the infinitely branching state `countdownSys.start`; the left side fails and
`wpGfp` holds at the diverging `loopSys`. -/
theorem nonvacuity_wpLfp_iff_wpGfp_and_not_hasInfiniteRun :
    (wpLfp countdownSys (fun _ => True) .start ∧ wpGfp countdownSys (fun _ => True) .start ∧
        ¬ HasInfiniteRun countdownSys .start) ∧
      (¬ wpLfp loopSys (fun _ => True) () ∧ wpGfp loopSys (fun _ => True) () ∧
        HasInfiniteRun loopSys ()) :=
  ⟨⟨countdown_wpLfp_without_uniform_fuel.2.2.2.1, countdown_wpLfp_without_uniform_fuel.2.2.2.2.1,
      countdown_wpLfp_without_uniform_fuel.2.2.2.2.2.1⟩,
    ⟨wpLfp_neg_loop, wpGfp_of_alwaysDiverges loopSys_alwaysDiverges _, loopSys_hasInfiniteRun⟩⟩

/-- Non-vacuity for the König form: `chainSys` from `3` is finitely branching,
satisfies `wpGfp`, and has no infinite run. -/
theorem nonvacuity_koenig_form :
    FinitelyBranchingFrom chainSys 3 ∧ wpGfp chainSys (fun s => s = 0) 3 ∧
      ¬ HasInfiniteRun chainSys 3 :=
  ⟨finitelyBranchingFrom_of_finitelyBranching chainSys_finitelyBranching 3, chainSys_wpGfp 3,
    hasInfiniteRun_neg_chain⟩

/-! ## Divergence and liveness -/

/-- Counterexample for the hypothesis `AlwaysDiverges S s` of
`alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp` (and of
`wpGfp_of_alwaysDiverges`): `doneSys` halts, and fails `wpGfp` for the
postcondition `False`. -/
theorem done_not_every_partial_wp :
    ¬ AlwaysDiverges doneSys () ∧ ¬ wpGfp doneSys (fun _ => False) () ∧
      ¬ wpFuel doneSys 1 (fun _ => False) () :=
  ⟨alwaysDiverges_neg_done, wpGfp_neg_done_false, wpFuel_neg_done_false⟩

/-- Counterexample for the hypothesis `HasInfiniteRun S s` of
`hasInfiniteRun_refutes_every_total_wp`: `doneSys` has no infinite run and
satisfies the total WPs for `True`. -/
theorem done_some_total_wp :
    ¬ HasInfiniteRun doneSys () ∧ wpLfp doneSys (fun _ => True) () ∧
      wpFuelTotal doneSys 1 (fun _ => True) () :=
  ⟨doneSys_not_hasInfiniteRun, doneSys_wpLfp_true, doneSys_wpFuelTotal_one⟩

/-- Non-vacuity for `alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp`,
`wpGfp_false_iff_alwaysDiverges` and `forall_wpGfp_iff_alwaysDiverges`. -/
theorem nonvacuity_alwaysDiverges : AlwaysDiverges loopSys () ∧ AlwaysDiverges spinOrOutSys .spin :=
  ⟨loopSys_alwaysDiverges, spinOrOutSys_alwaysDiverges⟩

/-- Non-vacuity for `hasInfiniteRun_refutes_every_total_wp`, at a state that has
an infinite run without always diverging. -/
theorem nonvacuity_hasInfiniteRun :
    HasInfiniteRun spinOrExitSys .spin ∧ ¬ AlwaysDiverges spinOrExitSys .spin :=
  ⟨spinOrExitSys_hasInfiniteRun, alwaysDiverges_neg_spinOrExit⟩

/-- Counterexample for the hypothesis `hdiv : AlwaysDiverges S s` of
`not_partial_wp_expressible_of_alwaysDiverges_of_not` and of its liveness
specialization `allRunsEventually_not_partial_wp_of_divergent_violation`
(instance `S := doneSys`, `s := ()`, `R := AllRunsEventually doneSys False`):
the other hypothesis `¬ R ()` holds, `hdiv` fails, and all three conjuncts of
the conclusion fail — `R` is expressed by `wpGfp doneSys False`, by
`wpFuel doneSys 1 False`, and by `∀ n, wpFuel doneSys n False`. -/
theorem done_allRunsEventually_false_expressible :
    ¬ AlwaysDiverges doneSys () ∧ ¬ AllRunsEventually doneSys (fun _ => False) () ∧
      (∀ t, wpGfp doneSys (fun _ => False) t ↔ AllRunsEventually doneSys (fun _ => False) t) ∧
      (∀ t, wpFuel doneSys 1 (fun _ => False) t ↔ AllRunsEventually doneSys (fun _ => False) t) ∧
      (∀ t, (∀ n, wpFuel doneSys n (fun _ => False) t) ↔
        AllRunsEventually doneSys (fun _ => False) t) := by
  have hviol : ¬ AllRunsEventually doneSys (fun _ => False) () := by
    intro h
    cases h with
    | now hp => exact hp
    | later hnt _ _ => exact hnt trivial
  refine ⟨alwaysDiverges_neg_done, hviol, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · cases t
    exact ⟨fun h => absurd h wpGfp_neg_done_false, fun h => absurd h hviol⟩
  · cases t
    exact ⟨fun h => absurd h wpFuel_neg_done_false, fun h => absurd h hviol⟩
  · cases t
    exact ⟨fun h => absurd (h 1) wpFuel_neg_done_false, fun h => absurd h hviol⟩

/-- Counterexample for the hypothesis `hviol : ¬ R s` of
`not_partial_wp_expressible_of_alwaysDiverges_of_not` and of its liveness
specialization (instance `S := loopSys`, `s := ()`,
`R := AllRunsEventually loopSys True`): the other hypothesis
`AlwaysDiverges loopSys ()` holds, `hviol` fails, and all three conjuncts of
the conclusion fail — `R` is expressed by `wpGfp loopSys True`, by
`wpFuel loopSys 0 True`, and by `∀ n, wpFuel loopSys n True`. -/
theorem loop_allRunsEventually_true_expressible :
    AlwaysDiverges loopSys () ∧ AllRunsEventually loopSys (fun _ => True) () ∧
      (∀ t, wpGfp loopSys (fun _ => True) t ↔ AllRunsEventually loopSys (fun _ => True) t) ∧
      (∀ t, wpFuel loopSys 0 (fun _ => True) t ↔ AllRunsEventually loopSys (fun _ => True) t) ∧
      (∀ t, (∀ n, wpFuel loopSys n (fun _ => True) t) ↔
        AllRunsEventually loopSys (fun _ => True) t) := by
  refine ⟨loopSys_alwaysDiverges, AllRunsEventually.now trivial, fun t => ?_, fun t => ?_,
    fun t => ?_⟩
  · cases t
    exact ⟨fun _ => AllRunsEventually.now trivial,
      fun _ => wpGfp_of_alwaysDiverges loopSys_alwaysDiverges _⟩
  · cases t
    exact ⟨fun _ => AllRunsEventually.now trivial, fun _ => trivial⟩
  · cases t
    exact ⟨fun _ => AllRunsEventually.now trivial,
      fun _ n => wpFuel_of_alwaysDiverges loopSys_alwaysDiverges n _⟩

/-- Non-vacuity for `not_partial_wp_expressible_of_alwaysDiverges_of_not` and
`allRunsEventually_not_partial_wp_of_divergent_violation`: the two-state
system `spinOrOutSys` at `spin` (with `R := AllRunsEventually spinOrOutSys isOut`)
and the three-state system `startSpinOutSys` at `spin`. -/
theorem nonvacuity_divergent_violation :
    (AlwaysDiverges spinOrOutSys .spin ∧ ¬ AllRunsEventually spinOrOutSys isOut .spin) ∧
      (AlwaysDiverges startSpinOutSys .spin ∧
        ¬ AllRunsEventually startSpinOutSys isOut3 .spin) :=
  ⟨⟨spinOrOutSys_alwaysDiverges, spinOrOutSys_spin_not_allRunsEventually_isOut⟩,
    ⟨startSpinOutSys_spin_alwaysDiverges, startSpinOutSys_spin_not_allRunsEventually⟩⟩

/-- The liveness properties of the two- and three-state impossibilities are not
trivial: each holds somewhere and fails somewhere; in the three-state system it
holds at the non-output state `start` (reached through `later`). -/
theorem nonvacuity_allRunsEventually_isOut_nontrivial :
    (AllRunsEventually spinOrOutSys isOut .out ∧ ¬ AllRunsEventually spinOrOutSys isOut .spin) ∧
      (¬ isOut3 .start ∧ AllRunsEventually startSpinOutSys isOut3 .start ∧
        ¬ AllRunsEventually startSpinOutSys isOut3 .spin) :=
  ⟨⟨spinOrOutSys_out_allRunsEventually_isOut, spinOrOutSys_spin_not_allRunsEventually_isOut⟩,
    ⟨startSpinOutSys_start_allRunsEventually_later.1,
      startSpinOutSys_start_allRunsEventually_later.2,
      startSpinOutSys_spin_not_allRunsEventually⟩⟩

/-! ## Adequacy -/

/-- The empty run prefix of `stuckSys` ends in a stuck state. -/
theorem stuck_reach_not_runEndOk :
    Reach stuckSys () 0 () ∧ ¬ RunEndOk stuckSys (fun _ => True) () :=
  ⟨Reach.refl (), runEndOk_neg_stuck⟩

/-- Canonical counterexample for the hypothesis `h : wpGfp S Q s` of
`wpGfp_adequacy` (which has no other hypothesis), instance `S := stuckSys`,
`Q := True`, `s := ()`: the hypothesis fails and the conclusion fails (the
empty run prefix ends in a stuck state). -/
theorem wpGfp_adequacy_drop_h :
    ¬ wpGfp stuckSys (fun _ => True) () ∧
      ¬ (∀ k t, Reach stuckSys () k t → RunEndOk stuckSys (fun _ => True) t) :=
  ⟨wpGfp_neg_stuck, fun h => runEndOk_neg_stuck (h 0 () (Reach.refl ()))⟩

/-- Canonical counterexample for the hypothesis
`h : ∀ k t, Reach S s k t → RunEndOk S Q t` of `wpGfp_of_forall_reach_runEndOk`
(which has no other hypothesis), instance `S := stuckSys`, `Q := True`,
`s := ()`: the hypothesis fails and the conclusion `wpGfp` fails. -/
theorem wpGfp_of_forall_reach_runEndOk_drop_h :
    ¬ (∀ k t, Reach stuckSys () k t → RunEndOk stuckSys (fun _ => True) t) ∧
      ¬ wpGfp stuckSys (fun _ => True) () :=
  ⟨fun h => runEndOk_neg_stuck (h 0 () (Reach.refl ())), wpGfp_neg_stuck⟩

/-- Every state of `chainSys` is an acceptable end of a run prefix for the
postcondition `(· = 0)`. -/
theorem chainSys_runEndOk (t : Nat) : RunEndOk chainSys (fun s => s = 0) t := by
  refine ⟨fun h => h, fun hnt => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by
    have : t ≠ 0 := hnt
    omega⟩
  exact ⟨j, rfl⟩

/-- Non-vacuity for `wpGfp_adequacy` and `wpGfp_of_forall_reach_runEndOk`.
(i) `chainSys` from `3` with postcondition `(· = 0)`: `wpGfp` holds, every run
prefix is acceptable, and both branches of `RunEndOk` are exercised — a
terminal state (`0`, reached in `3` steps) and a non-terminal one (`3`, the
empty prefix). (ii) `loopSys` with postcondition `False`. -/
theorem nonvacuity_adequacy :
    (wpGfp chainSys (fun s => s = 0) 3 ∧
        (∀ k t, Reach chainSys 3 k t → RunEndOk chainSys (fun s => s = 0) t) ∧
        (Reach chainSys 3 3 0 ∧ chainSys.terminal 0) ∧
        (Reach chainSys 3 0 3 ∧ ¬ chainSys.terminal 3)) ∧
      (wpGfp loopSys (fun _ => False) () ∧
        ∀ k t, Reach loopSys () k t → RunEndOk loopSys (fun _ => False) t) :=
  ⟨⟨chainSys_wpGfp 3, fun _ t _ => chainSys_runEndOk t, ⟨reach_pos_chain, rfl⟩,
      ⟨Reach.refl 3, Nat.succ_ne_zero 2⟩⟩,
    ⟨wpGfp_pos_loop_false, fun _ t _ => by cases t; exact runEndOk_pos_loop⟩⟩

/-! ## Fixpoint (co)induction -/

/-- Canonical counterexample for the hypothesis `hX : PostFixed S Q X` of
`wpGfp_coinduction` (instance `S := stuckSys`, `Q := True`, `X := True`,
`s := ()`): the other hypothesis `X ()` holds, `hX` fails, and the conclusion
`wpGfp stuckSys True ()` fails. -/
theorem wpGfp_coinduction_drop_hX :
    (fun _ : Unit => True) () ∧ ¬ PostFixed stuckSys (fun _ => True) (fun _ => True) ∧
      ¬ wpGfp stuckSys (fun _ => True) () :=
  ⟨trivial, postFixed_neg_stuck, wpGfp_neg_stuck⟩

/-- Canonical counterexample for the hypothesis `hs : X s` of
`wpGfp_coinduction` (instance `S := stuckSys`, `Q := True`, `X := False`,
`s := ()`): the other hypothesis `PostFixed stuckSys True False` holds
(vacuously), `hs` fails, and the conclusion fails. -/
theorem wpGfp_coinduction_drop_hs :
    PostFixed stuckSys (fun _ => True) (fun _ => False) ∧ ¬ (fun _ : Unit => False) () ∧
      ¬ wpGfp stuckSys (fun _ => True) () :=
  ⟨fun _ h => h.elim, fun h => h, wpGfp_neg_stuck⟩

/-- Canonical counterexample for the hypothesis `hX : PreFixed S Q X` of
`wpLfp_induction` (instance `S := doneSys`, `Q := True`, `X := False`,
`s := ()`): the other hypothesis `wpLfp doneSys True ()` holds, `hX` fails,
and the conclusion `X ()` fails. -/
theorem wpLfp_induction_drop_hX :
    wpLfp doneSys (fun _ => True) () ∧ ¬ PreFixed doneSys (fun _ => True) (fun _ => False) ∧
      ¬ (fun _ : Unit => False) () :=
  ⟨doneSys_wpLfp_true, preFixed_neg_done, fun h => h⟩

/-- Canonical counterexample for the hypothesis `hs : wpLfp S Q s` of
`wpLfp_induction` (instance `S := loopSys`, `Q := True`, `X := False`,
`s := ()`): the other hypothesis `PreFixed loopSys True False` holds, `hs`
fails, and the conclusion `X ()` fails. -/
theorem wpLfp_induction_drop_hs :
    PreFixed loopSys (fun _ => True) (fun _ => False) ∧ ¬ wpLfp loopSys (fun _ => True) () ∧
      ¬ (fun _ : Unit => False) () :=
  ⟨fun _ h => (h.2 (fun hf => hf)).2 () trivial, wpLfp_neg_loop, fun h => h⟩

/-- Non-vacuity for `wpGfp_coinduction` and `wpLfp_induction`:
(i) `X := True` is a post-fixed point of `wpStep loopSys False` and holds at
`()`; (ii) `X := isOut` is a (non-trivial) pre-fixed point of
`wpStep spinOrOutSys isOut` and `out` satisfies `wpLfp spinOrOutSys isOut`. -/
theorem nonvacuity_coinduction_induction :
    (PostFixed loopSys (fun _ => False) (fun _ => True) ∧ (fun _ : Unit => True) ()) ∧
      (PreFixed spinOrOutSys isOut isOut ∧ wpLfp spinOrOutSys isOut .out) :=
  ⟨⟨postFixed_pos_loop, trivial⟩, preFixed_pos_spinOrOut_isOut,
    wpLfp_preFixed _ _ _ ⟨fun _ => rfl, fun h => absurd rfl h⟩⟩

/-- `wpStep S Q` can have distinct least and greatest fixpoints: on `loopSys`
with postcondition `True`, `wpGfp` holds and `wpLfp` fails. -/
theorem loopSys_wpLfp_ne_wpGfp :
    wpGfp loopSys (fun _ => True) () ∧ ¬ wpLfp loopSys (fun _ => True) () :=
  ⟨wpGfp_of_alwaysDiverges loopSys_alwaysDiverges _, wpLfp_neg_loop⟩

/-! ## Interpreter step functions -/

/-- The predecessor interpreter `ofStepFn predStep (· = 0)` is totally correct
for `(· = 0)` from every state. -/
theorem ofStepFn_pred_wpLfp (k : Nat) :
    wpLfp (ofStepFn predStep (fun s => s = 0)) (fun s => s = 0) k := by
  induction k with
  | zero =>
    apply wpLfp_preFixed
    exact ⟨fun h => h, fun h => absurd rfl h⟩
  | succ k ih =>
    apply wpLfp_preFixed
    refine ⟨fun h => absurd h (Nat.succ_ne_zero k), fun _ => ⟨⟨k, rfl⟩, ?_⟩⟩
    intro t ht
    have ht' : some k = some t := ht
    cases ht'
    exact ih

/-- Non-vacuity for `exists_wpFuelTotal_iff_wpLfp_ofStepFn`: an interpreter
step function (`predStep`, halting at `0`) and a state at which the right-hand
side holds. -/
theorem nonvacuity_exists_wpFuelTotal_iff_wpLfp_ofStepFn :
    Deterministic (ofStepFn predStep (fun s => s = 0)) ∧
      wpLfp (ofStepFn predStep (fun s => s = 0)) (fun s => s = 0) 3 :=
  ⟨ofStepFn_pred_deterministic, ofStepFn_pred_wpLfp 3⟩

end Toy.FuelWP
