import ToyFuelWP.Defs

/-!
# Concrete toy systems

Small systems used as examples, counterexamples and non-vacuity witnesses.

| system            | states | behaviour |
| :---              | :---   | :--- |
| `loopSys`         | `Unit` | the single state steps to itself forever (divergence) |
| `doneSys`         | `Unit` | the single state is terminal (immediate halt) |
| `stuckSys`        | `Unit` | the single state is non-terminal with no successor (error) |
| `termLoopSys`     | `Unit` | terminal state that also has a self-loop (edge ignored) |
| `chainSys`        | `Nat`  | deterministic countdown `k → k-1`, `0` terminal |
| `downToStuckSys`  | `Nat`  | countdown `k → k-1`, but `0` is stuck instead of terminal |
| `countdownSys`    | `CD`   | unbounded choice of a countdown length, then countdown |
| `spinOrOutSys`    | `LO`   | `spin` loops forever; `out` is terminal |
| `spinOrExitSys`   | `LO`   | `spin` may loop or move to terminal `out` (nondeterministic) |
| `spinOrEmitLoopSys` | `LO` | `spin` and `out` each loop forever; nothing is terminal (output without halting) |
| `startSpinOutSys` | `LO3`  | `start → out`, `spin → spin`, `out` terminal (output reached after one step) |
| `termBranchSys`   | `Bool` | every state terminal, every pair of states joined by an (ignored) edge |
| `fanToStuckSys`   | `CD`   | unbounded choice of a countdown length, then countdown to a stuck `count 0` |
| `propSys P`       | `Unit` | no steps; the single state is terminal exactly when `P` holds |
-/

namespace Toy.FuelWP

/-- One state that steps to itself forever and never halts. -/
def loopSys : System Unit where
  step _ _ := True
  terminal _ := False

/-- One terminal state, no steps. -/
def doneSys : System Unit where
  step _ _ := False
  terminal _ := True

/-- One stuck state: not terminal, no successor. -/
def stuckSys : System Unit where
  step _ _ := False
  terminal _ := False

/-- One terminal state that also has a self-loop; the edge is ignored by every
weakest precondition, run notion and branching notion of the package because
terminal states halt (only the raw helper `CanStep` sees it). -/
def termLoopSys : System Unit where
  step _ _ := True
  terminal _ := True

/-- Deterministic countdown on `Nat`: `k + 1 → k`, and `0` is terminal. -/
def chainSys : System Nat where
  step s t := s = t + 1
  terminal s := s = 0

/-- Countdown on `Nat` that ends in an error: `k + 1 → k`, nothing is terminal,
so `0` is stuck. -/
def downToStuckSys : System Nat where
  step s t := s = t + 1
  terminal _ := False

/-- States of the unbounded-countdown system. -/
inductive CD where
  /-- Initial state: choose a countdown length. -/
  | start
  /-- Countdown with `k` steps remaining. -/
  | count (k : Nat)

/-- Steps of the unbounded-countdown system: from `start` choose any `k`
(an unbounded, countably infinite choice, as in the random assignment
`x := ?`), then count down. -/
inductive CDStep : CD → CD → Prop
  /-- Choose the countdown length `k`. -/
  | choose (k : Nat) : CDStep .start (.count k)
  /-- Count down by one. -/
  | tick (k : Nat) : CDStep (.count (k + 1)) (.count k)

/-- The unbounded-countdown system (`x := ?; while x > 0 do x := x - 1`):
every run halts, but there is no uniform bound on run length. -/
def countdownSys : System CD where
  step := CDStep
  terminal s := s = .count 0

/-- States of the two-state liveness examples. -/
inductive LO where
  /-- A state that has not produced the output. -/
  | spin
  /-- The state that has produced the output. -/
  | out

/-- `spin` steps only to itself; `out` is terminal. -/
def spinOrOutSys : System LO where
  step s t := s = .spin ∧ t = .spin
  terminal s := s = .out

/-- `spin` may step to `spin` or to `out`; `out` is terminal. -/
def spinOrExitSys : System LO where
  step s _ := s = .spin
  terminal s := s = .out

/-- The observation "the output has been produced". -/
def isOut (s : LO) : Prop := s = .out

/-- `spin` and `out` each step only to themselves and nothing is terminal: a
reactive system in which producing the output does not end the run. -/
def spinOrEmitLoopSys : System LO where
  step s t := s = t
  terminal _ := False

/-- States of the three-state liveness example. -/
inductive LO3 where
  /-- A state that produces the output after one step. -/
  | start
  /-- A state that never produces the output. -/
  | spin
  /-- The state that has produced the output. -/
  | out

/-- `start` steps to `out`, `spin` steps to itself, `out` is terminal. -/
def startSpinOutSys : System LO3 where
  step s t := (s = .start ∧ t = .out) ∨ (s = .spin ∧ t = .spin)
  terminal s := s = .out

/-- The observation "the output has been produced" on `LO3`. -/
def isOut3 (s : LO3) : Prop := s = .out

/-- Every state is terminal and every pair of states is joined by an edge;
the edges are ignored because terminal states halt. -/
def termBranchSys : System Bool where
  step _ _ := True
  terminal _ := True

/-- Unbounded choice followed by a countdown that ends in an error: from
`start` choose any `k`, then count down; nothing is terminal, so `count 0` is
stuck. -/
def fanToStuckSys : System CD where
  step := CDStep
  terminal _ := False

/-- A one-state system without steps whose single state is terminal exactly
when the proposition `P` holds. -/
def propSys (P : Prop) : System Unit where
  step _ _ := False
  terminal _ := P

/-! ## Helper facts about the toy systems -/

theorem LO.spin_ne_out : LO.spin ≠ LO.out := by
  intro h
  cases h

theorem loopSys_alwaysDiverges : AlwaysDiverges loopSys () :=
  fun _ _ _ => ⟨fun h => h, ⟨(), trivial⟩⟩

theorem loopSys_hasInfiniteRun : HasInfiniteRun loopSys () :=
  ⟨fun _ => (), rfl, fun _ => ⟨fun h => h, trivial⟩⟩

theorem stuckSys_stuck : Stuck stuckSys () :=
  ⟨fun h => h, fun _ h => h⟩

theorem stuckSys_not_hasInfiniteRun : ¬ HasInfiniteRun stuckSys () := by
  rintro ⟨f, _, hf⟩
  exact (hf 0).2

theorem doneSys_not_hasInfiniteRun : ¬ HasInfiniteRun doneSys () := by
  rintro ⟨f, _, hf⟩
  exact (hf 0).1 trivial

/-- Every state reachable from `spin` in `spinOrOutSys` is `spin`. -/
theorem spinOrOutSys_reach_spin {s t : LO} {k : Nat} (h : Reach spinOrOutSys s k t)
    (hs : s = .spin) : t = .spin := by
  induction h with
  | refl _ => exact hs
  | step _ hst _ ih => exact ih hst.2

theorem spinOrOutSys_alwaysDiverges : AlwaysDiverges spinOrOutSys .spin := by
  intro k t hr
  have ht : t = .spin := spinOrOutSys_reach_spin hr rfl
  subst ht
  exact ⟨LO.spin_ne_out, ⟨.spin, rfl, rfl⟩⟩

theorem spinOrOutSys_hasInfiniteRun : HasInfiniteRun spinOrOutSys .spin :=
  ⟨fun _ => .spin, rfl, fun _ => ⟨LO.spin_ne_out, rfl, rfl⟩⟩

theorem spinOrExitSys_hasInfiniteRun : HasInfiniteRun spinOrExitSys .spin :=
  ⟨fun _ => .spin, rfl, fun _ => ⟨LO.spin_ne_out, rfl⟩⟩

theorem chainSys_deterministic : Deterministic chainSys := by
  intro t _ u v hu hv
  have hu' : t = u + 1 := hu
  have hv' : t = v + 1 := hv
  omega

theorem chainSys_finitelyBranching : FinitelyBranching chainSys :=
  finitelyBranching_of_deterministic chainSys_deterministic

/-- Every `k` is in `wpLfp chainSys (· = 0)`. -/
theorem chainSys_wpLfp (k : Nat) : wpLfp chainSys (fun s => s = 0) k := by
  induction k with
  | zero =>
    apply wpLfp_preFixed
    exact ⟨fun h => h, fun h => absurd rfl h⟩
  | succ k ih =>
    apply wpLfp_preFixed
    refine ⟨fun h => absurd h (Nat.succ_ne_zero k), fun _ => ⟨⟨k, rfl⟩, ?_⟩⟩
    intro t ht
    have ht' : k + 1 = t + 1 := ht
    have hkt : t = k := by omega
    subst hkt
    exact ih

/-- From `k`, `chainSys` halts in `0` within fuel `k + 1`. -/
theorem chainSys_wpFuelTotal (k : Nat) : wpFuelTotal chainSys (k + 1) (fun s => s = 0) k := by
  induction k with
  | zero => exact ⟨fun h => h, fun h => absurd rfl h⟩
  | succ k ih =>
    refine ⟨fun h => absurd h (Nat.succ_ne_zero k), fun _ => ⟨⟨k, rfl⟩, ?_⟩⟩
    intro t ht
    have ht' : k + 1 = t + 1 := ht
    have hkt : t = k := by omega
    subst hkt
    exact ih

theorem chainSys_wpGfp (k : Nat) : wpGfp chainSys (fun s => s = 0) k := by
  refine ⟨wpLfp chainSys (fun s => s = 0), ?_, chainSys_wpLfp k⟩
  intro t ht
  exact (wpLfp_unfold _ _ _).mp ht

/-- `chainSys` satisfies the partial fuel WP for `(· = 0)` at every fuel. -/
theorem chainSys_wpFuel : ∀ (n k : Nat), wpFuel chainSys n (fun s => s = 0) k := by
  intro n
  induction n with
  | zero => intro _; trivial
  | succ n ih =>
    intro k
    cases k with
    | zero => exact ⟨fun h => h, fun h => absurd rfl h⟩
    | succ k =>
      refine ⟨fun h => absurd h (Nat.succ_ne_zero k), fun _ => ⟨⟨k, rfl⟩, ?_⟩⟩
      intro t _
      exact ih t

/-- From `k`, `chainSys` needs more than `k` total fuel. -/
theorem chainSys_fuel_gt {Q : Nat → Prop} :
    ∀ (n k : Nat), wpFuelTotal chainSys n Q k → k < n := by
  intro n
  induction n with
  | zero => intro k h; exact h.elim
  | succ n ih =>
    intro k h
    cases k with
    | zero => exact Nat.succ_pos n
    | succ k =>
      have h2 := (h.2 (Nat.succ_ne_zero k)).2 k rfl
      have := ih k h2
      omega

/-! ### The countdown that ends in an error -/

/-- `downToStuckSys`: from `k`, the partial fuel WP for `True` holds at every
fuel `n ≤ k` (the error at `0` is `k` steps away and invisible at fuel `≤ k`). -/
theorem downToStuckSys_wpFuel : ∀ (n k : Nat), n ≤ k → wpFuel downToStuckSys n (fun _ => True) k := by
  intro n
  induction n with
  | zero => intro _ _; trivial
  | succ n ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨fun _ => trivial, fun _ => ⟨⟨j, rfl⟩, ?_⟩⟩
    intro t ht
    have ht' : j + 1 = t + 1 := ht
    have hjt : t = j := by omega
    subst hjt
    exact ih t (by omega)

/-- `downToStuckSys`: from `k`, the partial fuel WP for `True` fails at fuel
`k + 1` (the run reaches the stuck state `0` after `k` steps). -/
theorem downToStuckSys_not_wpFuel : ∀ (k : Nat), ¬ wpFuel downToStuckSys (k + 1) (fun _ => True) k := by
  intro k
  induction k with
  | zero =>
    intro h
    obtain ⟨t, ht⟩ := (h.2 (fun hf => hf)).1
    have ht' : (0 : Nat) = t + 1 := ht
    omega
  | succ k ih =>
    intro h
    exact ih ((h.2 (fun hf => hf)).2 k rfl)

/-- `downToStuckSys`: no state satisfies the greatest-fixpoint WP for `True`
(every run reaches the stuck state `0`). -/
theorem downToStuckSys_not_wpGfp : ∀ (k : Nat), ¬ wpGfp downToStuckSys (fun _ => True) k := by
  intro k
  induction k with
  | zero =>
    intro h
    obtain ⟨t, ht⟩ := (((wpGfp_unfold _ _ _).mp h).2 (fun hf => hf)).1
    have ht' : (0 : Nat) = t + 1 := ht
    omega
  | succ k ih =>
    intro h
    exact ih ((((wpGfp_unfold _ _ _).mp h).2 (fun hf => hf)).2 k rfl)

/-- Every state is in `wpLfp` of `doneSys` for a true postcondition. -/
theorem doneSys_wpLfp_true : wpLfp doneSys (fun _ => True) () := by
  apply wpLfp_preFixed
  exact ⟨fun _ => trivial, fun h => absurd trivial h⟩

theorem doneSys_wpFuelTotal_one : wpFuelTotal doneSys 1 (fun _ => True) () :=
  ⟨fun _ => trivial, fun h => absurd trivial h⟩

/-! ### The unbounded-countdown system -/

theorem CD.count_succ_ne_zero (k : Nat) : CD.count (k + 1) ≠ CD.count 0 := by
  intro h
  cases h

theorem CD.start_ne_count (k : Nat) : CD.start ≠ CD.count k := by
  intro h
  cases h

/-- Every countdown state is in the total-correctness WP for `True`. -/
theorem countdownSys_count_wpLfp (k : Nat) : wpLfp countdownSys (fun _ => True) (.count k) := by
  induction k with
  | zero =>
    apply wpLfp_preFixed
    exact ⟨fun _ => trivial, fun h => absurd rfl h⟩
  | succ k ih =>
    apply wpLfp_preFixed
    refine ⟨fun _ => trivial, fun _ => ⟨⟨.count k, CDStep.tick k⟩, ?_⟩⟩
    intro t ht
    cases ht
    exact ih

/-- The initial state of `countdownSys` is totally correct for `True`:
every run halts without error. -/
theorem countdownSys_start_wpLfp : wpLfp countdownSys (fun _ => True) .start := by
  apply wpLfp_preFixed
  refine ⟨fun _ => trivial, fun _ => ⟨⟨.count 0, CDStep.choose 0⟩, ?_⟩⟩
  intro t ht
  cases ht
  exact countdownSys_count_wpLfp _

/-- Fuel needed from `count k` is more than `k`. -/
theorem countdownSys_count_fuel_gt {Q : CD → Prop} :
    ∀ (n k : Nat), wpFuelTotal countdownSys n Q (.count k) → k < n := by
  intro n
  induction n with
  | zero => intro k h; exact h.elim
  | succ n ih =>
    intro k h
    cases k with
    | zero => exact Nat.succ_pos n
    | succ k =>
      have h2 := ((h.2 (CD.count_succ_ne_zero k)).2 (.count k) (CDStep.tick k))
      have := ih k h2
      omega

/-- No fuel suffices from `start`. -/
theorem countdownSys_start_no_fuel {Q : CD → Prop} (n : Nat) :
    ¬ wpFuelTotal countdownSys n Q .start := by
  intro h
  cases n with
  | zero => exact h
  | succ n =>
    have h2 := ((h.2 (CD.start_ne_count 0)).2 (.count n) (CDStep.choose n))
    have := countdownSys_count_fuel_gt n n h2
    omega

/-- Every list of `CD` states misses all sufficiently large countdown states. -/
theorem CD.list_misses_count (l : List CD) : ∃ N, ∀ k, N ≤ k → CD.count k ∉ l := by
  induction l with
  | nil => exact ⟨0, fun _ _ h => nomatch h⟩
  | cons a l ih =>
    obtain ⟨N, hN⟩ := ih
    cases a with
    | start =>
      refine ⟨N, fun k hk hmem => ?_⟩
      cases hmem with
      | tail _ h => exact hN k hk h
    | count j =>
      refine ⟨max N (j + 1), fun k hk hmem => ?_⟩
      cases hmem with
      | head => omega
      | tail _ h => exact hN k (by omega) h

/-- `start` has infinitely many successors. -/
theorem countdownSys_not_finitelyBranchingAt_start :
    ¬ FinitelyBranchingAt countdownSys .start := by
  rintro ⟨l, hl⟩
  obtain ⟨N, hN⟩ := CD.list_misses_count l
  exact hN N (Nat.le_refl N) (hl _ (CDStep.choose N))

theorem countdownSys_not_finitelyBranchingFrom_start :
    ¬ FinitelyBranchingFrom countdownSys .start := fun h =>
  countdownSys_not_finitelyBranchingAt_start (h.here (CD.start_ne_count 0))

end Toy.FuelWP
