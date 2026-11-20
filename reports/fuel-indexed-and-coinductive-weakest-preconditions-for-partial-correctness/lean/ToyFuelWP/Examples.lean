import ToyFuelWP.Divergence

/-!
# Positive and negative examples for every definition (fully proved)

Each definition of `ToyFuelWP.Defs` gets at least one intended instance it
admits (`*_pos*`) and one it must reject (`*_neg*`). `System` itself imposes no
constraint, so there is nothing for it to reject; the convention it carries
(terminal states halt, their outgoing edges are ignored) is tested by the
`Reach`, `HasInfiniteRun` and `wpGfp` examples on `termLoopSys`.
-/

namespace Toy.FuelWP

/-! ## `CanStep` and `Stuck` -/

theorem canStep_pos_loop : CanStep loopSys () := ⟨(), trivial⟩

theorem canStep_neg_stuck : ¬ CanStep stuckSys () := fun ⟨_, h⟩ => h

/-- `CanStep` is a raw helper that sees the (ignored) edge of a terminal
state, although no run prefix uses that edge. -/
theorem canStep_raw_termLoop :
    termLoopSys.terminal () ∧ CanStep termLoopSys () ∧ ¬ Reach termLoopSys () 1 () := by
  refine ⟨trivial, ⟨(), trivial⟩, fun h => ?_⟩
  cases h with
  | step hnt _ _ => exact hnt trivial

theorem stuck_pos_stuckSys : Stuck stuckSys () := stuckSys_stuck

/-- A terminal state is not stuck. -/
theorem stuck_neg_done : ¬ Stuck doneSys () := fun h => h.1 trivial

/-- A state with a successor is not stuck. -/
theorem stuck_neg_loop : ¬ Stuck loopSys () := fun h => h.2 () trivial

/-! ## `wpStep` -/

/-- At a terminal state only the postcondition matters, not the continuation. -/
theorem wpStep_pos_done : wpStep doneSys (fun _ => True) (fun _ => False) () :=
  ⟨fun _ => trivial, fun h => absurd trivial h⟩

/-- A stuck state fails `wpStep` whatever the postcondition and continuation. -/
theorem wpStep_neg_stuck : ¬ wpStep stuckSys (fun _ => True) (fun _ => True) () := by
  intro h
  obtain ⟨_, ht⟩ := (h.2 (fun hf => hf)).1
  exact ht

/-! ## `wpFuel` (partial correctness, fuel-indexed) -/

/-- Divergence satisfies the partial fuel WP even for the postcondition `False`. -/
theorem wpFuel_pos_loop_false : wpFuel loopSys 7 (fun _ => False) () :=
  wpFuel_of_alwaysDiverges loopSys_alwaysDiverges 7 _

/-- Fuel `0` is vacuous: even a stuck state passes. -/
theorem wpFuel_pos_zero_stuck : wpFuel stuckSys 0 (fun _ => False) () := trivial

/-- A run that reaches an error after `3` steps passes at fuel `3`. -/
theorem wpFuel_pos_error_out_of_range : wpFuel downToStuckSys 3 (fun _ => True) 3 :=
  downToStuckSys_wpFuel 3 3 (Nat.le_refl 3)

theorem wpFuel_neg_stuck : ¬ wpFuel stuckSys 1 (fun _ => True) () := by
  intro h
  obtain ⟨_, ht⟩ := (h.2 (fun hf => hf)).1
  exact ht

/-- A terminal state violating the postcondition fails at fuel `1`. -/
theorem wpFuel_neg_done_false : ¬ wpFuel doneSys 1 (fun _ => False) () :=
  fun h => h.1 trivial

/-- The error `3` steps away is detected at fuel `4`. -/
theorem wpFuel_neg_error_in_range : ¬ wpFuel downToStuckSys 4 (fun _ => True) 3 :=
  downToStuckSys_not_wpFuel 3

/-! ## `wpFuelTotal` (total correctness, fuel-indexed) -/

theorem wpFuelTotal_pos_done : wpFuelTotal doneSys 1 (fun _ => True) () :=
  doneSys_wpFuelTotal_one

theorem wpFuelTotal_pos_chain : wpFuelTotal chainSys 4 (fun s => s = 0) 3 :=
  chainSys_wpFuelTotal 3

/-- Fuel `0` always fails, even at a terminal state. -/
theorem wpFuelTotal_neg_zero_done : ¬ wpFuelTotal doneSys 0 (fun _ => True) () := fun h => h

/-- Divergence fails at every fuel. -/
theorem wpFuelTotal_neg_loop : ¬ wpFuelTotal loopSys 5 (fun _ => True) () :=
  not_wpFuelTotal_of_hasInfiniteRun loopSys_hasInfiniteRun 5 _

/-- Insufficient fuel fails: from `3`, `chainSys` needs fuel `4`. -/
theorem wpFuelTotal_neg_chain_short : ¬ wpFuelTotal chainSys 3 (fun s => s = 0) 3 :=
  fun h => absurd (chainSys_fuel_gt 3 3 h) (Nat.lt_irrefl 3)

/-! ## `PostFixed` and `PreFixed` -/

theorem postFixed_pos_loop : PostFixed loopSys (fun _ => False) (fun _ => True) :=
  fun _ _ => ⟨fun h => absurd h id, fun _ => ⟨⟨(), trivial⟩, fun _ _ => trivial⟩⟩

theorem postFixed_neg_stuck : ¬ PostFixed stuckSys (fun _ => True) (fun _ => True) := by
  intro h
  obtain ⟨_, ht⟩ := ((h () trivial).2 (fun hf => hf)).1
  exact ht

/-- The top predicate is a pre-fixed point of every operator; this example
does not exercise `wpStep` (see `preFixed_pos_spinOrOut_isOut`). -/
theorem preFixed_pos_top : PreFixed loopSys (fun _ => False) (fun _ => True) :=
  fun _ _ => trivial

/-- A non-trivial pre-fixed point: on `spinOrOutSys`, the predicate `isOut` is
closed under `wpStep spinOrOutSys isOut` (at `spin`, the only successor is
`spin`, so `wpStep … isOut spin` would require `isOut spin`). -/
theorem preFixed_pos_spinOrOut_isOut : PreFixed spinOrOutSys isOut isOut := by
  intro s hs
  cases s with
  | spin => exact (hs.2 LO.spin_ne_out).2 .spin ⟨rfl, rfl⟩
  | out => exact hs.1 rfl

theorem preFixed_neg_done : ¬ PreFixed doneSys (fun _ => True) (fun _ => False) :=
  fun h => h () ⟨fun _ => trivial, fun hn => absurd trivial hn⟩

/-! ## `wpGfp` (partial correctness, greatest fixpoint) -/

theorem wpGfp_pos_loop_false : wpGfp loopSys (fun _ => False) () :=
  wpGfp_of_alwaysDiverges loopSys_alwaysDiverges _

theorem wpGfp_pos_chain : wpGfp chainSys (fun s => s = 0) 3 := chainSys_wpGfp 3

/-- The self-loop of a terminal state is ignored: `termLoopSys` satisfies
`wpGfp Q` exactly when `Q` holds there. -/
theorem wpGfp_termLoop_iff (Q : Unit → Prop) : wpGfp termLoopSys Q () ↔ Q () := by
  constructor
  · intro h
    exact ((wpGfp_unfold _ _ _).mp h).1 trivial
  · intro hq
    refine ⟨fun _ => True, fun t _ => ⟨fun _ => hq, fun hn => absurd trivial hn⟩, trivial⟩

theorem wpGfp_neg_stuck : ¬ wpGfp stuckSys (fun _ => True) () := by
  intro h
  obtain ⟨_, ht⟩ := (((wpGfp_unfold _ _ _).mp h).2 (fun hf => hf)).1
  exact ht

theorem wpGfp_neg_done_false : ¬ wpGfp doneSys (fun _ => False) () :=
  fun h => ((wpGfp_unfold _ _ _).mp h).1 trivial

/-- A run that eventually reaches an error is rejected, however far away the
error is. -/
theorem wpGfp_neg_error_far : ¬ wpGfp downToStuckSys (fun _ => True) 1000 :=
  downToStuckSys_not_wpGfp 1000

/-! ## `wpLfp` (total correctness, least fixpoint) -/

theorem wpLfp_pos_chain : wpLfp chainSys (fun s => s = 0) 3 := chainSys_wpLfp 3

/-- Unbounded (infinitely branching) choice followed by a countdown is totally
correct. -/
theorem wpLfp_pos_countdown : wpLfp countdownSys (fun _ => True) .start :=
  countdownSys_start_wpLfp

theorem wpLfp_neg_loop : ¬ wpLfp loopSys (fun _ => True) () :=
  not_wpLfp_of_hasInfiniteRun loopSys_hasInfiniteRun _

theorem wpLfp_neg_stuck : ¬ wpLfp stuckSys (fun _ => True) () := by
  intro h
  obtain ⟨_, ht⟩ := (((wpLfp_unfold _ _ _).mp h).2 (fun hf => hf)).1
  exact ht

/-- `chainSys` halts in `0`, so it is not totally correct for `(· = 1)`. -/
theorem wpLfp_neg_chain_wrong_post : ¬ wpLfp chainSys (fun s => s = 1) 3 := by
  intro h3
  have step : ∀ k, wpLfp chainSys (fun s => s = 1) (k + 1) → wpLfp chainSys (fun s => s = 1) k :=
    fun k h => (((wpLfp_unfold _ _ _).mp h).2 (Nat.succ_ne_zero k)).2 k rfl
  have h0 := step 0 (step 1 (step 2 h3))
  have : (0 : Nat) = 1 := ((wpLfp_unfold _ _ _).mp h0).1 rfl
  exact absurd this (by decide)

/-! ## `Reach` -/

theorem reach_pos_chain : Reach chainSys 3 3 0 :=
  Reach.step (Nat.succ_ne_zero 2) rfl
    (Reach.step (Nat.succ_ne_zero 1) rfl (Reach.step (Nat.succ_ne_zero 0) rfl (Reach.refl 0)))

/-- Run prefixes stop at terminal states. -/
theorem reach_neg_from_terminal (t : Nat) : ¬ Reach chainSys 0 1 t := by
  intro h
  cases h with
  | step hnt _ _ => exact hnt rfl

/-- The outgoing edge of a terminal state is not part of any run prefix. -/
theorem reach_neg_termLoop : ¬ Reach termLoopSys () 1 () := by
  intro h
  cases h with
  | step hnt _ _ => exact hnt trivial

/-! ## `RunEndOk` -/

theorem runEndOk_pos_done : RunEndOk doneSys (fun _ => True) () :=
  ⟨fun _ => trivial, fun h => absurd trivial h⟩

theorem runEndOk_pos_loop : RunEndOk loopSys (fun _ => False) () :=
  ⟨fun h => absurd h id, fun _ => ⟨(), trivial⟩⟩

theorem runEndOk_neg_stuck : ¬ RunEndOk stuckSys (fun _ => True) () := by
  intro h
  obtain ⟨_, ht⟩ := h.2 (fun hf => hf)
  exact ht

theorem runEndOk_neg_done_false : ¬ RunEndOk doneSys (fun _ => False) () :=
  fun h => h.1 trivial

/-! ## `HasInfiniteRun` and `AlwaysDiverges` -/

theorem hasInfiniteRun_pos_loop : HasInfiniteRun loopSys () := loopSys_hasInfiniteRun

/-- A state that may diverge (but may also halt) has an infinite run. -/
theorem hasInfiniteRun_pos_spinOrExit : HasInfiniteRun spinOrExitSys .spin :=
  spinOrExitSys_hasInfiniteRun

theorem hasInfiniteRun_neg_done : ¬ HasInfiniteRun doneSys () := doneSys_not_hasInfiniteRun

/-- A terminal state with a self-loop has no infinite run (it halts). -/
theorem hasInfiniteRun_neg_termLoop : ¬ HasInfiniteRun termLoopSys () := by
  rintro ⟨f, _, hf⟩
  exact (hf 0).1 trivial

theorem hasInfiniteRun_neg_chain : ¬ HasInfiniteRun chainSys 3 :=
  fun h => not_wpLfp_of_hasInfiniteRun h _ (chainSys_wpLfp 3)

theorem alwaysDiverges_pos_loop : AlwaysDiverges loopSys () := loopSys_alwaysDiverges

theorem alwaysDiverges_pos_spinOrOut : AlwaysDiverges spinOrOutSys .spin :=
  spinOrOutSys_alwaysDiverges

/-- A state that *may* halt does not always diverge, although it has an
infinite run (`hasInfiniteRun_pos_spinOrExit`). -/
theorem alwaysDiverges_neg_spinOrExit : ¬ AlwaysDiverges spinOrExitSys .spin := by
  intro h
  have hr : Reach spinOrExitSys .spin 1 .out := Reach.step LO.spin_ne_out rfl (Reach.refl _)
  exact (h 1 .out hr).1 rfl

theorem alwaysDiverges_neg_done : ¬ AlwaysDiverges doneSys () := fun h => h.here.1 trivial

/-- A run that reaches an error does not diverge. -/
theorem alwaysDiverges_neg_error : ¬ AlwaysDiverges downToStuckSys 0 := by
  intro h
  obtain ⟨t, ht⟩ := h.here.2
  have ht' : (0 : Nat) = t + 1 := ht
  omega

/-! ## Finite branching and determinism -/

theorem finitelyBranchingAt_pos_chain : FinitelyBranchingAt chainSys 3 := by
  refine ⟨[2], fun u hu => ?_⟩
  have hu' : (3 : Nat) = u + 1 := hu
  have : u = 2 := by omega
  subst this
  exact List.mem_singleton.mpr rfl

theorem finitelyBranchingAt_neg_countdown : ¬ FinitelyBranchingAt countdownSys .start :=
  countdownSys_not_finitelyBranchingAt_start

/-- Every state reachable from a countdown state is a countdown state. -/
theorem countdownSys_reach_count {s t : CD} {k : Nat} (h : Reach countdownSys s k t)
    (hs : ∃ j, s = .count j) : ∃ j, t = .count j := by
  induction h with
  | refl _ => exact hs
  | step _ hst _ ih =>
    obtain ⟨j, rfl⟩ := hs
    cases hst
    exact ih ⟨_, rfl⟩

theorem countdownSys_finitelyBranchingAt_count (j : Nat) :
    FinitelyBranchingAt countdownSys (.count j) := by
  refine ⟨[.count (j - 1)], fun u hu => ?_⟩
  cases hu
  exact List.mem_singleton.mpr (by simp)

/-- Local finite branching admits a state of a system that is not globally
finitely branching. -/
theorem finitelyBranchingFrom_pos_countdown_count :
    FinitelyBranchingFrom countdownSys (.count 3) := by
  intro k t hr _
  obtain ⟨j, rfl⟩ := countdownSys_reach_count hr ⟨3, rfl⟩
  exact countdownSys_finitelyBranchingAt_count j

theorem finitelyBranchingFrom_neg_countdown_start :
    ¬ FinitelyBranchingFrom countdownSys .start :=
  countdownSys_not_finitelyBranchingFrom_start

theorem finitelyBranching_pos_chain : FinitelyBranching chainSys := chainSys_finitelyBranching

theorem finitelyBranching_pos_loop : FinitelyBranching loopSys :=
  fun _ _ => ⟨[()], fun _ _ => List.mem_singleton.mpr rfl⟩

theorem finitelyBranching_neg_countdown : ¬ FinitelyBranching countdownSys :=
  fun h => countdownSys_not_finitelyBranchingAt_start (h .start (CD.start_ne_count 0))

theorem deterministic_pos_chain : Deterministic chainSys := chainSys_deterministic

/-- Edges leaving terminal states are ignored: a system in which every state is
terminal is deterministic however many edges it has. -/
theorem deterministic_pos_termBranch : Deterministic termBranchSys :=
  fun _ ht => absurd trivial ht

theorem deterministic_neg_spinOrExit : ¬ Deterministic spinOrExitSys := by
  intro h
  exact LO.spin_ne_out (h .spin LO.spin_ne_out .spin .out rfl rfl)

theorem deterministic_neg_countdown : ¬ Deterministic countdownSys := by
  intro h
  have := h .start (CD.start_ne_count 0) (.count 0) (.count 1) (CDStep.choose 0) (CDStep.choose 1)
  cases this

/-- Finite branching is strictly weaker than determinism: `spinOrExitSys` is
finitely branching but not deterministic. -/
theorem spinOrExitSys_finitelyBranching_not_deterministic :
    FinitelyBranching spinOrExitSys ∧ ¬ Deterministic spinOrExitSys := by
  refine ⟨fun _ _ => ⟨[.spin, .out], fun u _ => ?_⟩, deterministic_neg_spinOrExit⟩
  cases u with
  | spin => exact List.Mem.head _
  | out => exact List.Mem.tail _ (List.Mem.head _)

/-! ## `ofStepFn` -/

/-- The predecessor function as an interpreter step. -/
def predStep : Nat → Option Nat
  | 0 => none
  | k + 1 => some k

theorem ofStepFn_pos_pred : (ofStepFn predStep (fun s => s = 0)).step 3 2 := rfl

theorem ofStepFn_neg_pred : ¬ (ofStepFn predStep (fun s => s = 0)).step 3 1 := by
  intro h
  have h' : (some 2 : Option Nat) = some 1 := h
  cases h'

theorem ofStepFn_pred_deterministic : Deterministic (ofStepFn predStep (fun s => s = 0)) :=
  ofStepFn_deterministic _ _

/-! ## `AllRunsEventually` -/

theorem allRunsEventually_pos_out : AllRunsEventually spinOrOutSys isOut .out :=
  spinOrOutSys_out_allRunsEventually_isOut

theorem allRunsEventually_pos_chain : AllRunsEventually chainSys (fun s => s = 0) 2 :=
  AllRunsEventually.later (Nat.succ_ne_zero 1) ⟨1, rfl⟩ (fun t ht => by
    have ht' : (2 : Nat) = t + 1 := ht
    have : t = 1 := by omega
    subst this
    exact AllRunsEventually.later (Nat.succ_ne_zero 0) ⟨0, rfl⟩ (fun u hu => by
      have hu' : (1 : Nat) = u + 1 := hu
      have : u = 0 := by omega
      subst this
      exact AllRunsEventually.now rfl))

theorem allRunsEventually_neg_spin : ¬ AllRunsEventually spinOrOutSys isOut .spin :=
  spinOrOutSys_spin_not_allRunsEventually_isOut

/-- "All runs": a state with one run that reaches `out` and one that spins
forever is rejected. -/
theorem allRunsEventually_neg_spinOrExit : ¬ AllRunsEventually spinOrExitSys isOut .spin := by
  have key : ∀ s, AllRunsEventually spinOrExitSys isOut s → s ≠ .spin := by
    intro s h
    induction h with
    | now hp => intro hs; subst hs; exact LO.spin_ne_out hp
    | later _ _ _ ih => intro hs; subst hs; exact ih .spin rfl rfl
  exact fun h => key .spin h rfl

/-- A run that gets stuck before reaching `P` violates `AllRunsEventually`. -/
theorem allRunsEventually_neg_stuck : ¬ AllRunsEventually stuckSys (fun _ => False) () := by
  intro h
  cases h with
  | now hp => exact hp
  | later _ hc _ => exact canStep_neg_stuck hc

end Toy.FuelWP
