import ToyFuelWP.Divergence

/-!
# Boundary results (fully proved)

Theorems that mark where the main results stop. None of them is a main
result; each is referenced from the non-claims of a result.

* Law of the excluded miracle for the total-correctness WPs.
* The constructive content of a total-correctness judgement: because
  `wpStep` is written with implications, a judgement only yields
  `¬¬ terminal` at the end of a run unless `terminal` is decidable.
* Escape hatches of the inexpressibility results: a *negated* partial
  weakest precondition can express "eventually outputs" on the two-state
  system, and on deterministic systems without stuck states the conjugate
  `¬ wpGfp S (fun t => ¬ Q t)` is exactly `wpLfp S Q`; conversely total
  correctness does not express liveness on a system that keeps running after
  producing the output; and restricting the state space to exclude the
  always-diverging states can make a positive partial weakest precondition
  coincide with a liveness property.
* Quantifier order of fuel bounds: a fuel bound exists per initial state, not
  uniformly.
* The partial-correctness equivalence `∀ n, wpFuel ↔ wpGfp` does not extend to
  an *angelic* one-step operator over infinitely many successors.

This module does not import `ToyFuelWP.Statements`.
-/

namespace Toy.FuelWP

universe u

variable {σ : Type u}

/-! ## Law of the excluded miracle -/

/-- No state satisfies the least-fixpoint total-correctness WP of the
postcondition `False` (the law of the excluded miracle). Constructive. -/
theorem wpLfp_excluded_miracle (S : System σ) (s : σ) : ¬ wpLfp S (fun _ => False) s := by
  intro h
  refine h (fun _ => False) (fun t ht => ?_)
  have hnt : ¬ S.terminal t := ht.1
  obtain ⟨u, hu⟩ := (ht.2 hnt).1
  exact (ht.2 hnt).2 u hu

/-- No state satisfies the fuel-indexed total-correctness WP of `False` at any
fuel. Constructive. -/
theorem wpFuelTotal_excluded_miracle (S : System σ) (n : Nat) (s : σ) :
    ¬ wpFuelTotal S n (fun _ => False) s := by
  induction n generalizing s with
  | zero => exact fun h => h
  | succ n ih =>
    intro h
    have hnt : ¬ S.terminal s := h.1
    obtain ⟨u, hu⟩ := (h.2 hnt).1
    exact ih u ((h.2 hnt).2 u hu)

/-! ## Constructive content of a total-correctness judgement -/

/-- In the one-state system without steps whose state is terminal exactly when
`P` holds, total correctness at fuel `1` for the postcondition `True` is
exactly `¬¬ P` (constructively). So a total-correctness judgement does not by
itself exhibit a terminal state; it excludes non-termination. With classical
logic, or when `terminal` is decidable, `¬¬ P` gives `P`. -/
theorem wpFuelTotal_propSys_one_iff_not_not (P : Prop) :
    wpFuelTotal (propSys P) 1 (fun _ => True) () ↔ ¬¬ P := by
  constructor
  · intro h hnp
    obtain ⟨_, ht⟩ := (h.2 hnp).1
    exact ht
  · intro hnn
    exact ⟨fun _ => trivial, fun hnp => absurd hnp hnn⟩

/-! ## Escape hatches of the inexpressibility results -/

/-- **Negated partial WP expresses "eventually outputs" on the two-state
system.** On `spinOrOutSys`, `AllRunsEventually spinOrOutSys isOut s` holds
iff `wpGfp spinOrOutSys (fun _ => False) s` fails. The inexpressibility
results rule out only *positive* partial-correctness weakest preconditions. -/
theorem allRunsEventually_isOut_iff_not_wpGfp_false (s : LO) :
    AllRunsEventually spinOrOutSys isOut s ↔ ¬ wpGfp spinOrOutSys (fun _ => False) s := by
  cases s with
  | spin =>
    exact ⟨fun h => absurd h spinOrOutSys_spin_not_allRunsEventually_isOut,
      fun h => absurd (wpGfp_of_alwaysDiverges spinOrOutSys_alwaysDiverges _) h⟩
  | out =>
    exact ⟨fun _ h => ((wpGfp_unfold _ _ _).mp h).1 rfl,
      fun _ => spinOrOutSys_out_allRunsEventually_isOut⟩

/-- Total correctness excludes the greatest-fixpoint WP of the complementary
postcondition, in every system. Constructive. -/
theorem not_wpGfp_not_of_wpLfp (S : System σ) (Q : σ → Prop) (s : σ) (h : wpLfp S Q s) :
    ¬ wpGfp S (fun t => ¬ Q t) s := by
  have key : PreFixed S Q (fun t => ¬ wpGfp S (fun t => ¬ Q t) t) := by
    intro t ht hg
    have hg' := (wpGfp_unfold _ _ _).mp hg
    have hnt : ¬ S.terminal t := fun hterm => hg'.1 hterm (ht.1 hterm)
    obtain ⟨u, hu⟩ := (ht.2 hnt).1
    exact (ht.2 hnt).2 u hu ((hg'.2 hnt).2 u hu)
  exact wpLfp_induction key h

/-- On a deterministic system without stuck states, failure of the
greatest-fixpoint WP of the complementary postcondition implies total
correctness. (Classical.) -/
theorem wpLfp_of_not_wpGfp_not_of_deterministic_of_not_stuck (S : System σ) (Q : σ → Prop)
    (hdet : Deterministic S) (hns : ∀ t, ¬ Stuck S t) (s : σ)
    (h : ¬ wpGfp S (fun t => ¬ Q t) s) : wpLfp S Q s := by
  apply Classical.byContradiction
  intro hl
  apply h
  refine ⟨fun t => ¬ wpLfp S Q t, ?_, hl⟩
  intro t ht
  refine ⟨fun hterm hq => ht (wpLfp_preFixed S Q t ⟨fun _ => hq, fun hn => absurd hterm hn⟩),
    fun hnt => ⟨?_, ?_⟩⟩
  · apply Classical.byContradiction
    intro hc
    exact hns t ⟨hnt, fun u hu => hc ⟨u, hu⟩⟩
  · intro u hu hlu
    apply ht
    apply wpLfp_preFixed S Q t
    refine ⟨fun hterm => absurd hterm hnt, fun _ => ⟨⟨u, hu⟩, fun v hv => ?_⟩⟩
    rw [hdet t hnt v u hv hu]
    exact hlu

/-- **Conjugate escape hatch.** On a deterministic system without stuck
states, the negated partial-correctness WP of the complementary
postcondition, `¬ wpGfp S (fun t => ¬ Q t)`, is exactly the total-correctness
WP `wpLfp S Q`. (Classical.) -/
theorem not_wpGfp_not_iff_wpLfp_of_deterministic_of_not_stuck (S : System σ) (Q : σ → Prop)
    (hdet : Deterministic S) (hns : ∀ t, ¬ Stuck S t) (s : σ) :
    ¬ wpGfp S (fun t => ¬ Q t) s ↔ wpLfp S Q s :=
  ⟨wpLfp_of_not_wpGfp_not_of_deterministic_of_not_stuck S Q hdet hns s,
    not_wpGfp_not_of_wpLfp S Q s⟩

/-- The conjugate identity needs determinism: in the nondeterministic
`spinOrExitSys`, the state `spin` fails `wpGfp spinOrExitSys (fun t => ¬ isOut t)`
(one run reaches `out`) but also fails `wpLfp spinOrExitSys isOut` (another run
spins forever). -/
theorem spinOrExitSys_conjugate_ne_wpLfp :
    ¬ Deterministic spinOrExitSys ∧ (∀ t, ¬ Stuck spinOrExitSys t) ∧
      ¬ wpGfp spinOrExitSys (fun t => ¬ isOut t) .spin ∧ ¬ wpLfp spinOrExitSys isOut .spin := by
  refine ⟨fun h => LO.spin_ne_out (h .spin LO.spin_ne_out .spin .out rfl rfl), ?_, ?_,
    not_wpLfp_of_hasInfiniteRun spinOrExitSys_hasInfiniteRun _⟩
  · intro t ⟨hnt, hno⟩
    cases t with
    | spin => exact hno .spin rfl
    | out => exact hnt rfl
  · intro h
    have hout := ((((wpGfp_unfold _ _ _).mp h).2 LO.spin_ne_out).2) .out rfl
    exact ((wpGfp_unfold _ _ _).mp hout).1 rfl rfl

/-- The conjugate identity needs the absence of stuck states: at the stuck
state of `stuckSys` (a deterministic system) both
`wpGfp stuckSys (fun _ => ¬ True)` and `wpLfp stuckSys (fun _ => True)` fail. -/
theorem stuckSys_conjugate_ne_wpLfp :
    Deterministic stuckSys ∧ Stuck stuckSys () ∧
      ¬ wpGfp stuckSys (fun _ => ¬ True) () ∧ ¬ wpLfp stuckSys (fun _ => True) () := by
  refine ⟨fun _ _ _ _ h _ => h.elim, stuckSys_stuck, ?_, ?_⟩
  · intro h
    obtain ⟨_, ht⟩ := (((wpGfp_unfold _ _ _).mp h).2 (fun hf => hf)).1
    exact ht
  · intro h
    obtain ⟨_, ht⟩ := (((wpLfp_unfold _ _ _).mp h).2 (fun hf => hf)).1
    exact ht

/-- **Total correctness does not express liveness in general.** In
`spinOrEmitLoopSys` (`spin → spin`, `out → out`, nothing terminal), the
property `AllRunsEventually spinOrEmitLoopSys isOut` holds at `out` and fails
at `spin`, and it is not equal to `wpGfp spinOrEmitLoopSys Q`,
`wpLfp spinOrEmitLoopSys Q` or `wpFuelTotal spinOrEmitLoopSys n Q` for any
`n` and `Q`. (Every state always diverges, so every total-correctness WP is
false everywhere and every partial-correctness WP is true everywhere.) -/
theorem spinOrEmitLoopSys_allRunsEventually_not_wp_expressible :
    (AllRunsEventually spinOrEmitLoopSys isOut .out ∧
        ¬ AllRunsEventually spinOrEmitLoopSys isOut .spin) ∧
      (¬ ∃ Q : LO → Prop,
        ∀ s, wpGfp spinOrEmitLoopSys Q s ↔ AllRunsEventually spinOrEmitLoopSys isOut s) ∧
      (¬ ∃ Q : LO → Prop,
        ∀ s, wpLfp spinOrEmitLoopSys Q s ↔ AllRunsEventually spinOrEmitLoopSys isOut s) ∧
      (¬ ∃ (n : Nat) (Q : LO → Prop),
        ∀ s, wpFuelTotal spinOrEmitLoopSys n Q s ↔ AllRunsEventually spinOrEmitLoopSys isOut s) := by
  have hdiv : ∀ s, AlwaysDiverges spinOrEmitLoopSys s := fun _ _ _ _ => ⟨fun h => h, ⟨_, rfl⟩⟩
  have hiff : ∀ s, AllRunsEventually spinOrEmitLoopSys isOut s ↔ s = .out := by
    intro s
    constructor
    · intro h
      induction h with
      | now hp => exact hp
      | later _ _ _ ih => exact ih _ rfl
    · intro hs
      exact AllRunsEventually.now hs
  have hout : AllRunsEventually spinOrEmitLoopSys isOut .out := (hiff .out).mpr rfl
  have hspin : ¬ AllRunsEventually spinOrEmitLoopSys isOut .spin :=
    fun h => LO.spin_ne_out ((hiff .spin).mp h)
  refine ⟨⟨hout, hspin⟩, ?_, ?_, ?_⟩
  · exact (not_partial_wp_expressible_of_alwaysDiverges_of_not spinOrEmitLoopSys
      (AllRunsEventually spinOrEmitLoopSys isOut) .spin (hdiv .spin) hspin).1
  · rintro ⟨Q, hQ⟩
    exact not_wpLfp_of_alwaysDiverges (hdiv .out) Q ((hQ .out).mpr hout)
  · rintro ⟨n, Q, hQ⟩
    exact not_wpFuelTotal_of_alwaysDiverges (hdiv .out) n Q ((hQ .out).mpr hout)

/-- **Domain-restriction escape hatch.** The inexpressibility results quantify
over every state. Restricted to the states other than the always-diverging
`spin`, the liveness property `AllRunsEventually startSpinOutSys isOut3`
coincides with the positive partial-correctness WP
`wpGfp startSpinOutSys isOut3` (both hold at `start` and at `out`). -/
theorem startSpinOutSys_wpGfp_iff_allRunsEventually_off_spin (s : LO3) (hs : s ≠ .spin) :
    wpGfp startSpinOutSys isOut3 s ↔ AllRunsEventually startSpinOutSys isOut3 s := by
  have hpost : PostFixed startSpinOutSys isOut3 (fun t => t ≠ .spin) := by
    intro t ht
    refine ⟨fun hterm => hterm, fun hnt => ?_⟩
    cases t with
    | spin => exact absurd rfl ht
    | out => exact absurd rfl hnt
    | start =>
      refine ⟨⟨.out, Or.inl ⟨rfl, rfl⟩⟩, fun u hu => ?_⟩
      rcases hu with ⟨_, h2⟩ | ⟨h1, _⟩
      · subst h2
        exact fun h => nomatch h
      · cases h1
  have hare : AllRunsEventually startSpinOutSys isOut3 s := by
    cases s with
    | spin => exact absurd rfl hs
    | start => exact startSpinOutSys_start_allRunsEventually_later.2
    | out => exact AllRunsEventually.now rfl
  exact ⟨fun _ => hare, fun _ => ⟨fun t => t ≠ .spin, hpost, hs⟩⟩

/-! ## Quantifier order of fuel bounds -/

/-- **A fuel bound exists per initial state, not uniformly.** In the
deterministic `chainSys`, every state `k` satisfies
`wpFuelTotal chainSys (k + 1) (· = 0) k`, but no single fuel works for all
states. -/
theorem chainSys_fuel_per_state_not_uniform :
    (∀ k, ∃ n, wpFuelTotal chainSys n (fun s => s = 0) k) ∧
      ¬ ∃ n, ∀ k, wpFuelTotal chainSys n (fun s => s = 0) k :=
  ⟨fun k => ⟨k + 1, chainSys_wpFuelTotal k⟩,
    fun ⟨n, h⟩ => Nat.lt_irrefl n (chainSys_fuel_gt n n (h n))⟩

/-! ## Angelic contrast to the partial-correctness equivalence -/

/-- An *angelic* one-step operator: at a non-terminal state, *some* successor
satisfies the continuation. Not used by any main result; defined only to show
where the partial-correctness equivalence stops. -/
def wpStepAngelic (S : System σ) (Q X : σ → Prop) (s : σ) : Prop :=
  (S.terminal s → Q s) ∧ (¬ S.terminal s → ∃ t, S.step s t ∧ X t)

/-- Fuel iterates of `wpStepAngelic` from `True`. -/
def wpFuelAngelic (S : System σ) : Nat → (σ → Prop) → σ → Prop
  | 0, _ => fun _ => True
  | n + 1, Q => wpStepAngelic S Q (wpFuelAngelic S n Q)

/-- Greatest fixpoint of `wpStepAngelic` (union of post-fixed predicates). -/
def wpGfpAngelic (S : System σ) (Q : σ → Prop) (s : σ) : Prop :=
  ∃ X : σ → Prop, (∀ t, X t → wpStepAngelic S Q X t) ∧ X s

/-- Positive example: in `spinOrExitSys`, `spin` can choose to move to the
terminal `out`, so it satisfies the angelic step for `isOut` with any
continuation that holds at `out`. -/
theorem wpStepAngelic_pos_spinOrExit :
    wpStepAngelic spinOrExitSys isOut (fun t => t = .out) .spin :=
  ⟨fun h => absurd h LO.spin_ne_out, fun _ => ⟨.out, rfl, rfl⟩⟩

/-- Negative example: a stuck state has no successor to choose. -/
theorem wpStepAngelic_neg_stuck : ¬ wpStepAngelic stuckSys (fun _ => True) (fun _ => True) () :=
  fun h => by
    obtain ⟨_, ht, _⟩ := h.2 (fun hf => hf)
    exact ht

/-- Positive example: angelic fuel `0` is vacuous. -/
theorem wpFuelAngelic_pos_zero_stuck : wpFuelAngelic stuckSys 0 (fun _ => True) () := trivial

/-- Negative example: a stuck state fails the angelic fuel WP at fuel `1`. -/
theorem wpFuelAngelic_neg_stuck : ¬ wpFuelAngelic stuckSys 1 (fun _ => True) () :=
  fun h => by
    obtain ⟨_, ht, _⟩ := h.2 (fun hf => hf)
    exact ht

/-- Positive example: `spin` in `spinOrExitSys` satisfies the angelic
greatest-fixpoint WP for `isOut` (it can always choose to reach `out`). -/
theorem wpGfpAngelic_pos_spinOrExit : wpGfpAngelic spinOrExitSys isOut .spin := by
  refine ⟨fun _ => True, fun t _ => ?_, trivial⟩
  cases t with
  | spin => exact ⟨fun h => absurd h LO.spin_ne_out, fun _ => ⟨.out, rfl, trivial⟩⟩
  | out => exact ⟨fun _ => rfl, fun h => absurd rfl h⟩

/-- Negative example: a stuck state fails the angelic greatest-fixpoint WP. -/
theorem wpGfpAngelic_neg_stuck : ¬ wpGfpAngelic stuckSys (fun _ => True) () := by
  rintro ⟨X, hX, hs⟩
  obtain ⟨_, ht, _⟩ := (hX () hs).2 (fun hf => hf)
  exact ht

theorem fanToStuckSys_wpFuelAngelic_count :
    ∀ (m k : Nat), m ≤ k → wpFuelAngelic fanToStuckSys m (fun _ => True) (.count k) := by
  intro m
  induction m with
  | zero => intro _ _; trivial
  | succ m ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨fun h => h.elim, fun _ => ⟨.count j, CDStep.tick j, ih j (by omega)⟩⟩

theorem fanToStuckSys_not_wpGfpAngelic_count {X : CD → Prop}
    (hX : ∀ t, X t → wpStepAngelic fanToStuckSys (fun _ => True) X t) :
    ∀ k, ¬ X (.count k) := by
  intro k
  induction k with
  | zero =>
    intro hx
    obtain ⟨t, ht, _⟩ := (hX _ hx).2 (fun h => h)
    cases ht
  | succ k ih =>
    intro hx
    obtain ⟨t, ht, hxt⟩ := (hX _ hx).2 (fun h => h)
    cases ht
    exact ih hxt

/-- **The partial-correctness equivalence fails for an angelic operator with
infinite branching.** In `fanToStuckSys` (from `start` choose any countdown
length; the countdown ends in a stuck state), `start` satisfies the angelic
fuel WP for `True` at every fuel (choose a countdown longer than the fuel),
but not the angelic greatest-fixpoint WP (every choice eventually gets
stuck). Contrast `forall_wpFuel_iff_wpGfp`, which holds for the demonic
operator `wpStep` with no branching assumption. -/
theorem fanToStuckSys_angelic_forall_fuel_not_gfp :
    (∀ n, wpFuelAngelic fanToStuckSys n (fun _ => True) .start) ∧
      ¬ wpGfpAngelic fanToStuckSys (fun _ => True) .start := by
  refine ⟨fun n => ?_, ?_⟩
  · cases n with
    | zero => trivial
    | succ n =>
      exact ⟨fun h => h.elim,
        fun _ => ⟨.count n, CDStep.choose n, fanToStuckSys_wpFuelAngelic_count n n (Nat.le_refl n)⟩⟩
  · rintro ⟨X, hX, hs⟩
    obtain ⟨t, ht, hxt⟩ := (hX _ hs).2 (fun h => h)
    cases ht with
    | choose k => exact fanToStuckSys_not_wpGfpAngelic_count hX k hxt

end Toy.FuelWP
