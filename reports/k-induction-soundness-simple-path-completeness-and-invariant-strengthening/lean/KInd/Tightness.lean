import KInd.Soundness
import KInd.Systems
import KInd.Completeness
import KInd.Separation
import KInd.BMC
import KInd.Strengthening

/-!
# Hypothesis-tightness counterexamples and non-vacuity witnesses

Each counterexample is stated in canonical form: a concrete instance satisfies all the other
hypotheses of the named result and its conclusion fails. Each non-vacuity witness is a concrete
instance satisfying all hypotheses of the named result.
-/

namespace Toy.KInd

theorem stuck_not_invariant : ¬ Invariant Stuck.I Stuck.T Stuck.P :=
  fun h => h ⟨0, by decide⟩ (reachable_of_init trivial)

theorem stuck_step_one : Step Stuck.T Stuck.P 1 :=
  step_one_iff.mpr (fun _ _ _ h => h.elim)

theorem oneEdge_base_one : Base OneEdge.I OneEdge.T OneEdge.P 1 := by
  rw [base_iff_reachIn]
  intro j hj s hs
  have : j = 0 := by omega
  subst this
  exact reachIn_zero_iff.mp hs

/-! ## `kind_sound`, `kind_simple_sound`, `kind_success_mono` -/

/-- `kind_sound` needs `Base`: in `Stuck` (depth `1`), `Step 1` holds and `P` is not
invariant. -/
theorem kind_sound_needs_base :
    Step Stuck.T Stuck.P 1 ∧ ¬ Invariant Stuck.I Stuck.T Stuck.P :=
  ⟨stuck_step_one, stuck_not_invariant⟩

/-- `kind_sound` needs the step: in `OneEdge` (depth `1`), `Base 1` holds and `P` is not
invariant. (Also used for `kind_simple_sound`.) -/
theorem kind_sound_needs_step :
    Base OneEdge.I OneEdge.T OneEdge.P 1 ∧ ¬ Invariant OneEdge.I OneEdge.T OneEdge.P :=
  ⟨oneEdge_base_one, oneEdge_not_invariant⟩

/-- The depth of `Base` in `kind_sound` cannot be lowered: in `OneEdge`, `Base 1` and `Step 2`
hold (no path has two transitions), but `P` is not invariant. So `Base (k - 1) ∧ Step k` does
not suffice at `k = 2`. -/
theorem kind_sound_base_depth_tight :
    Base OneEdge.I OneEdge.T OneEdge.P 1 ∧ Step OneEdge.T OneEdge.P 2 ∧
      ¬ Invariant OneEdge.I OneEdge.T OneEdge.P :=
  ⟨oneEdge_base_one, step_two_iff.mpr (by decide), oneEdge_not_invariant⟩

/-- `kind_simple_sound` needs `Base`: in `Stuck` (depth `1`), `SimpleStep 1` holds and `P` is
not invariant. -/
theorem kind_simple_sound_needs_base :
    SimpleStep Stuck.T Stuck.P 1 ∧ ¬ Invariant Stuck.I Stuck.T Stuck.P :=
  ⟨stuck_step_one.simpleStep, stuck_not_invariant⟩

/-- Non-vacuity of `kind_sound` (and of `kinductive_futureSafe_strengthening` at `k = 1`):
`TwoInd` passes `Base 2` and `Step 2`. -/
theorem nonvacuity_kind_sound :
    Base TwoInd.I TwoInd.T TwoInd.P 2 ∧ Step TwoInd.T TwoInd.P 2 :=
  ⟨one_induction_fails_two_induction_succeeds.2.1, one_induction_fails_two_induction_succeeds.2.2.1⟩

/-- Non-vacuity of `kind_simple_sound`, on an instance where plain k-induction fails at every
depth: `SelfLoop` passes `Base 2` and `SimpleStep 2`. -/
theorem nonvacuity_kind_simple_sound :
    Base SelfLoop.I SelfLoop.T SelfLoop.P 2 ∧ SimpleStep SelfLoop.T SelfLoop.P 2 ∧
      ¬ Step SelfLoop.T SelfLoop.P 2 :=
  ⟨selfLoop_simple_kind_succeeds_at_two.1, selfLoop_simple_kind_succeeds_at_two.2,
    plain_kind_incomplete_every_depth.2 2⟩

/-- `kind_success_mono` needs `Base k`: in `Stuck` (`k = 1`, `k' = 2`), `Step 1` and `1 ≤ 2`
hold but `Base 2` fails. -/
theorem kind_success_mono_needs_base :
    Step Stuck.T Stuck.P 1 ∧ (1 : Nat) ≤ 2 ∧
      ¬ (Base Stuck.I Stuck.T Stuck.P 2 ∧ Step Stuck.T Stuck.P 2) :=
  ⟨stuck_step_one, by decide, fun ⟨hb, _⟩ => hb 0 (by decide) (fun _ => ⟨0, by decide⟩) trivial
    (fun i hi => absurd hi (Nat.not_lt_zero _)) 0 (Nat.le_refl 0)⟩

/-- `kind_success_mono` needs `Step k` for its first conjunct: in `OneEdge` (`k = 1`, `k' = 2`),
`Base 1` and `1 ≤ 2` hold but `Base 2` fails. -/
theorem kind_success_mono_needs_step :
    Base OneEdge.I OneEdge.T OneEdge.P 1 ∧ (1 : Nat) ≤ 2 ∧
      ¬ (Base OneEdge.I OneEdge.T OneEdge.P 2 ∧ Step OneEdge.T OneEdge.P 2) := by
  refine ⟨oneEdge_base_one, by decide, fun ⟨hb, _⟩ => ?_⟩
  rw [base_iff_reachIn] at hb
  have hr : ReachIn OneEdge.I OneEdge.T 1 ⟨1, by decide⟩ := by
    simp only [reachIn_succ_iff, reachIn_zero_iff]
    decide
  exact absurd (hb 1 (by decide) _ hr) (by decide)

/-- `kind_success_mono` needs `Step k` for its second conjunct even when `P` is invariant: in
`SelfLoop` (`k = 1`, `k' = 2`), `Base 1` and `1 ≤ 2` hold and `P` is invariant (so `Base 2`
holds), but `Step 2` fails. -/
theorem kind_success_mono_needs_step_invariant :
    Base SelfLoop.I SelfLoop.T SelfLoop.P 1 ∧ (1 : Nat) ≤ 2 ∧
      Invariant SelfLoop.I SelfLoop.T SelfLoop.P ∧
      ¬ (Base SelfLoop.I SelfLoop.T SelfLoop.P 2 ∧ Step SelfLoop.T SelfLoop.P 2) :=
  ⟨base_of_invariant selfLoop_invariant 1, by decide, selfLoop_invariant,
    fun ⟨_, hs⟩ => plain_kind_incomplete_every_depth.2 2 hs⟩

/-- `kind_success_mono` needs `k ≤ k'`: in `TwoInd` (`k = 2`, `k' = 1`), `Base 2` and `Step 2`
hold but `Step 1` fails. -/
theorem kind_success_mono_needs_le :
    Base TwoInd.I TwoInd.T TwoInd.P 2 ∧ Step TwoInd.T TwoInd.P 2 ∧ ¬ ((2 : Nat) ≤ 1) ∧
      ¬ (Base TwoInd.I TwoInd.T TwoInd.P 1 ∧ Step TwoInd.T TwoInd.P 1) :=
  ⟨one_induction_fails_two_induction_succeeds.2.1, one_induction_fails_two_induction_succeeds.2.2.1,
    by decide, fun ⟨_, hs⟩ => one_induction_fails_two_induction_succeeds.1 hs⟩

/-- Non-vacuity of `kind_success_mono` with a strict depth increase: `TwoInd` passes `Base 2`
and `Step 2`, and `2 ≤ 3`. -/
theorem nonvacuity_kind_success_mono :
    Base TwoInd.I TwoInd.T TwoInd.P 2 ∧ Step TwoInd.T TwoInd.P 2 ∧ (2 : Nat) ≤ 3 :=
  ⟨one_induction_fails_two_induction_succeeds.2.1, one_induction_fails_two_induction_succeeds.2.2.1,
    by decide⟩

/-- `Step.mono` needs `Step k`: in `SelfLoop`, `1 ≤ 2` holds but `Step 2` fails. -/
theorem step_mono_needs_step : (1 : Nat) ≤ 2 ∧ ¬ Step SelfLoop.T SelfLoop.P 2 :=
  ⟨by decide, plain_kind_incomplete_every_depth.2 2⟩

/-- `Step.mono` needs `k ≤ k'`: in `TwoInd`, `Step 2` holds but `Step 1` fails. -/
theorem step_mono_needs_le :
    Step TwoInd.T TwoInd.P 2 ∧ ¬ ((2 : Nat) ≤ 1) ∧ ¬ Step TwoInd.T TwoInd.P 1 :=
  ⟨one_induction_fails_two_induction_succeeds.2.2.1, by decide,
    one_induction_fails_two_induction_succeeds.1⟩

/-- Non-vacuity of `Step.mono`: `Step 2` holds for `TwoInd`, and `2 ≤ 3`. -/
theorem nonvacuity_step_mono : Step TwoInd.T TwoInd.P 2 ∧ (2 : Nat) ≤ 3 :=
  ⟨one_induction_fails_two_induction_succeeds.2.2.1, by decide⟩

/-- `SimpleStep.mono` needs `SimpleStep k`: in the chain without initial states on `Fin 3`,
`1 ≤ 2` holds but `SimpleStep 2` fails. -/
theorem simpleStep_mono_needs_step :
    (1 : Nat) ≤ 2 ∧ ¬ SimpleStep (NoInitChain.T 2) (NoInitChain.P 2) 2 :=
  ⟨by decide, (simple_kind_depth_card_optimal_without_init 2).2⟩

/-- `SimpleStep.mono` needs `k ≤ k'`: in `SelfLoop`, `SimpleStep 2` holds but `SimpleStep 1`
fails (the simple path `1 → 2`). -/
theorem simpleStep_mono_needs_le :
    SimpleStep SelfLoop.T SelfLoop.P 2 ∧ ¬ ((2 : Nat) ≤ 1) ∧ ¬ SimpleStep SelfLoop.T SelfLoop.P 1 :=
  ⟨selfLoop_simple_kind_succeeds_at_two.2, by decide, by rw [simpleStep_one_iff]; decide⟩

/-- Non-vacuity of `SimpleStep.mono`, on an instance where the plain step fails: `SimpleStep 2`
holds for `SelfLoop`, `2 ≤ 3`, and `Step 2` fails. -/
theorem nonvacuity_simpleStep_mono :
    SimpleStep SelfLoop.T SelfLoop.P 2 ∧ (2 : Nat) ≤ 3 ∧ ¬ Step SelfLoop.T SelfLoop.P 2 :=
  ⟨selfLoop_simple_kind_succeeds_at_two.2, by decide, plain_kind_incomplete_every_depth.2 2⟩

/-! ## Loop removal -/

/-- Non-vacuity of `exists_simple_reachIn` with a non-simple witness path: in `SelfLoop`, the
initial state is reached in three transitions (around its self-loop). -/
theorem nonvacuity_exists_simple_reachIn : ReachIn SelfLoop.I SelfLoop.T 3 ⟨0, by decide⟩ := by
  simp only [reachIn_succ_iff, reachIn_zero_iff]
  decide

/-- `exists_simple_reachIn` needs its reachability premise: the unreachable state `1` of
`SelfLoop` has no simple path from an initial state (with at most `0` transitions, or any
number). -/
theorem loop_removal_needs_reachIn :
    ¬ ∃ m', m' ≤ 0 ∧ ∃ π : Nat → Fin 3, SelfLoop.I (π 0) ∧ IsPath SelfLoop.T m' π ∧
      IsSimple m' π ∧ π m' = ⟨1, by decide⟩ := by
  rintro ⟨m', hm', π, h0, hp, -, he⟩
  have hreach : Reachable SelfLoop.I SelfLoop.T ⟨1, by decide⟩ := ⟨m', π, h0, hp, he⟩
  have := (selfLoop_reachable_iff _).mp hreach
  exact absurd this (by decide)

/-! ## Completeness on finite systems -/

theorem oneEdge_not_base_two : ¬ Base OneEdge.I OneEdge.T OneEdge.P 2 :=
  fun hb => kind_success_mono_needs_step.2.2 ⟨hb, by
    -- `Step 2` holds vacuously: no path has two transitions
    intro π hp _
    have h0 : OneEdge.T (π 0) (π 1) := hp 0 (by decide)
    have h1 : OneEdge.T (π 1) (π 2) := hp 1 (by decide)
    simp only [OneEdge.T] at h0 h1
    exfalso
    omega⟩

/-- `simple_kind_complete_fin` needs `Invariant`: in the two-state system `OneEdge`, the
conclusion `Base 2 ∧ SimpleStep 2` fails (its `P` is not invariant). -/
theorem simple_kind_complete_fin_needs_invariant :
    ¬ (Base OneEdge.I OneEdge.T OneEdge.P 2 ∧ SimpleStep OneEdge.T OneEdge.P 2) :=
  fun ⟨hb, _⟩ => oneEdge_not_base_two hb

/-- `simple_kind_complete_fin_pred_of_init` needs `Invariant`: `OneEdge` (states `Fin (1 + 1)`)
has an initial state but `SimpleStep 1` fails. -/
theorem simple_kind_complete_fin_pred_of_init_needs_invariant :
    (∃ s, OneEdge.I s) ∧ ¬ SimpleStep OneEdge.T OneEdge.P 1 := by
  refine ⟨⟨⟨0, by decide⟩, rfl⟩, ?_⟩
  rw [simpleStep_one_iff]
  decide

/-- Non-vacuity of `simple_kind_complete_fin` and `simple_kind_complete_fin_pred_of_init`:
`SelfLoop` (states `Fin (2 + 1)`) has an initial state and an invariant `P`. -/
theorem nonvacuity_simple_kind_complete_fin :
    (∃ s, SelfLoop.I s) ∧ Invariant SelfLoop.I SelfLoop.T SelfLoop.P :=
  ⟨⟨⟨0, by decide⟩, rfl⟩, selfLoop_invariant⟩

/-- Non-vacuity of `simpleStep_of_card_le`: `n = k = 3` for `SelfLoop`. -/
theorem nonvacuity_simpleStep_of_card_le :
    (3 : Nat) ≤ 3 ∧ SimpleStep SelfLoop.T SelfLoop.P 3 :=
  ⟨Nat.le_refl 3, simpleStep_of_card_le _ _ (Nat.le_refl 3)⟩

/-! ## BMC -/

/-- Positive control for `bmc_incomplete_of_not_reachDiameterBound`: at `k = 2`, which bounds the
diameter of `Chain`, the property `ReachWithin Chain.I Chain.T 2` is invariant. -/
theorem chain_reachWithin_two_invariant :
    Invariant Chain.I Chain.T (ReachWithin Chain.I Chain.T 2) :=
  fun s hs => chain_reachDiameterBound_two s hs

/-- Degenerate instance of `bmc_complete_of_reachRecurrenceBound` (with `r = k = 0`). -/
theorem nonvacuity_bmc_complete_of_reachRecurrenceBound_zero :
    ReachRecurrenceBound SelfLoop.I SelfLoop.T 0 ∧ BMC SelfLoop.I SelfLoop.T SelfLoop.P 0 :=
  ⟨selfLoop_reachRecurrenceBound_zero, selfLoop_reachDiameterBound_zero_bmc_zero.2⟩

/-- Non-vacuity of `bmc_complete_fin` (`n = 3`, depth `2`). -/
theorem nonvacuity_bmc_complete_fin : BMC SelfLoop.I SelfLoop.T SelfLoop.P (3 - 1) :=
  bmc_of_invariant selfLoop_invariant _

/-- `bmc_complete_fin` needs its BMC hypothesis, and depth `n - 1` cannot be lowered to
`n - 2`: `Chain` (`n = 3`) passes `BMC 1` but `P` is not invariant. -/
theorem bmc_complete_fin_depth_tight :
    BMC Chain.I Chain.T Chain.P 1 ∧ ¬ BMC Chain.I Chain.T Chain.P (3 - 1) ∧
      ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_bmc_one, fun h => chain_not_invariant (bmc_complete_fin h), chain_not_invariant⟩

/-! ## Base checks of exact length (non-total transition relations) -/

/-- **A base check over paths of exact length only is unsound without totality.** In `OneEdge`
(state `1` has no successor), at depth `3` every path from an initial state with exactly `2`
transitions satisfies `P` (there is none) and `Step 3` holds (no path has `3` transitions), but
`P` is not invariant; `Base 3`, which also checks shorter paths, fails. -/
theorem exact_length_base_unsound_without_totality :
    ¬ (∀ s, ∃ t, OneEdge.T s t) ∧
      (∀ π : Nat → Fin 2, OneEdge.I (π 0) → IsPath OneEdge.T 2 π →
        ∀ i, i ≤ 2 → OneEdge.P (π i)) ∧
      Step OneEdge.T OneEdge.P 3 ∧ ¬ Invariant OneEdge.I OneEdge.T OneEdge.P ∧
      ¬ Base OneEdge.I OneEdge.T OneEdge.P 3 := by
  refine ⟨?_, ?_, ?_, oneEdge_not_invariant, fun hb => oneEdge_not_invariant
    (kind_sound hb ?_)⟩
  · intro h
    obtain ⟨t, ht⟩ := h ⟨1, by decide⟩
    simp only [OneEdge.T] at ht
    omega
  · intro π _ hp
    have h0 : OneEdge.T (π 0) (π 1) := hp 0 (by decide)
    have h1 : OneEdge.T (π 1) (π 2) := hp 1 (by decide)
    simp only [OneEdge.T] at h0 h1
    omega
  · intro π hp _
    have h0 : OneEdge.T (π 0) (π 1) := hp 0 (by decide)
    have h1 : OneEdge.T (π 1) (π 2) := hp 1 (by decide)
    simp only [OneEdge.T] at h0 h1
    omega
  · intro π hp _
    have h0 : OneEdge.T (π 0) (π 1) := hp 0 (by decide)
    have h1 : OneEdge.T (π 1) (π 2) := hp 1 (by decide)
    simp only [OneEdge.T] at h0 h1
    omega

/-- Non-vacuity of `base_iff_exactBase_of_total`: every state of the infinite counter `NatSucc`
has a successor. -/
theorem nonvacuity_base_iff_exactBase_of_total : ∀ s, ∃ t, NatSucc.T s t :=
  fun s => ⟨s + 1, rfl⟩

/-! ## `kind_simple_sound` at depth `2` (where `SimpleStep` is strictly weaker than `Step`) -/

/-- `kind_simple_sound` needs `Base`, at depth `2`: in `SelfLoop` with `P := (· = 1)`,
`SimpleStep 2` holds (no simple path has two `P`-states), `Step 2` fails, and `P` is not
invariant. -/
theorem kind_simple_sound_needs_base_k2 :
    SimpleStep SelfLoop.T (fun s => s.val = 1) 2 ∧
      ¬ Step SelfLoop.T (fun s => s.val = 1) 2 ∧
      ¬ Invariant SelfLoop.I SelfLoop.T (fun s => s.val = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [simpleStep_two_iff]; decide
  · rw [step_two_iff]; decide
  · intro h
    have := h ⟨0, by decide⟩ (reachable_of_init rfl)
    exact absurd this (by decide)

/-- `kind_simple_sound` needs the step, at depth `2`: `Chain` passes `Base 2` but `P` is not
invariant. -/
theorem kind_simple_sound_needs_step_k2 :
    Base Chain.I Chain.T Chain.P 2 ∧ ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_bmc_one, chain_not_invariant⟩

/-- The base depth in `kind_simple_sound` cannot be lowered: in `OneEdge`, `Base 1` and
`SimpleStep 2` hold but `P` is not invariant. -/
theorem kind_simple_sound_base_depth_tight :
    Base OneEdge.I OneEdge.T OneEdge.P 1 ∧ SimpleStep OneEdge.T OneEdge.P 2 ∧
      ¬ Invariant OneEdge.I OneEdge.T OneEdge.P :=
  ⟨kind_sound_base_depth_tight.1, kind_sound_base_depth_tight.2.1.simpleStep,
    kind_sound_base_depth_tight.2.2⟩

/-! ## Escape hatches for fixed-depth and every-depth incompleteness -/

/-- In `Ladder k`, the invariant has a 1-inductive strengthening (`Q := (· = 0)`), so ordinary
induction with this lemma proves it. -/
theorem ladder_inductive_strengthening (k : Nat) :
    Initiation (Ladder.I k) (fun s => s.val = 0) ∧
      Consecution (Ladder.T k) (fun s => s.val = 0) ∧
      ∀ s : Fin (k + 2), s.val = 0 → Ladder.P k s := by
  refine ⟨fun _ h => h, ?_, ?_⟩
  · intro s t hs hst
    simp only [Ladder.T] at hst
    omega
  · intro s hs
    simp only [Ladder.P]
    omega

/-- In `Ladder k`, only the initial state is reachable, so `0` bounds the reachability diameter
and `BMC 0` already proves the invariant (via `bmc_complete_of_reachDiameterBound`). -/
theorem ladder_reachDiameterBound_zero_bmc_zero (k : Nat) :
    ReachDiameterBound (Ladder.I k) (Ladder.T k) 0 ∧ BMC (Ladder.I k) (Ladder.T k) (Ladder.P k) 0 := by
  have hreach : ∀ s, Reachable (Ladder.I k) (Ladder.T k) s → s.val = 0 :=
    invariant_of_inductive (ladder_inductive_strengthening k).1 (ladder_inductive_strengthening k).2.1
      (fun _ h => h)
  refine ⟨fun s hs => reachWithin_zero_iff.mpr (hreach s hs), ?_⟩
  rw [bmc_iff_reachWithin]
  intro s hs
  have := reachWithin_zero_iff.mp hs
  simp only [Ladder.I] at this
  simp only [Ladder.P]
  omega

/-- The acyclicity escape hatch applies, for instance, to `Chain` (`0 → 1 → 2`): the plain step
holds at depth `3` for every property. -/
theorem chain_step_three_of_acyclic (P : Fin 3 → Prop) : Step Chain.T P 3 := by
  apply step_card_of_acyclic
  intro m π hp heq
  have hmono : ∀ i, i ≤ m + 1 → (π i).val = (π 0).val + i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have := hp i (by omega)
      have := ih (by omega)
      simp only [Chain.T] at *
      omega
  have := hmono (m + 1) (Nat.le_refl _)
  rw [← heq] at this
  omega

/-! ## Infinite state types -/

/-- Positive control for `simple_kind_incomplete_every_depth_infinite`: on the same infinite
system, BMC at depth `0` proves the invariant (`0` bounds the reachability diameter). -/
theorem natDescent_bmc_zero_proves_invariant :
    ReachDiameterBound NatDescent.I NatDescent.T 0 ∧
      BMC NatDescent.I NatDescent.T NatDescent.P 0 ∧
      Invariant NatDescent.I NatDescent.T NatDescent.P := by
  have hd := simple_kind_incomplete_every_depth_infinite.2.2.1
  have hb : BMC NatDescent.I NatDescent.T NatDescent.P 0 := by
    rw [bmc_iff_reachWithin]
    intro s hs
    have := reachWithin_zero_iff.mp hs
    simp only [NatDescent.I] at this
    simp only [NatDescent.P]
    omega
  exact ⟨hd, hb, bmc_complete_of_reachDiameterBound hd (Nat.le_refl 0) hb⟩

/-! ## BMC thresholds: canonical counterexamples and non-vacuity -/

theorem chain_not_bmc_two : ¬ BMC Chain.I Chain.T Chain.P 2 :=
  fun h => chain_not_invariant (bmc_complete_fin h)

theorem chain_not_reachRecurrenceBound_one : ¬ ReachRecurrenceBound Chain.I Chain.T 1 :=
  fun h => chain_not_reachDiameterBound_one (reachDiameterBound_of_reachRecurrenceBound h)

/-- `bmc_complete_of_reachDiameterBound` needs `hd` (`d = 1`, `k = 1` on `Chain`). -/
theorem bmc_reachDiameter_needs_hd :
    ¬ ReachDiameterBound Chain.I Chain.T 1 ∧ (1 : Nat) ≤ 1 ∧
      BMC Chain.I Chain.T Chain.P 1 ∧ ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_not_reachDiameterBound_one, Nat.le_refl 1, chain_bmc_one, chain_not_invariant⟩

/-- `bmc_complete_of_reachDiameterBound` needs `hk` (`d = 2`, `k = 1` on `Chain`). -/
theorem bmc_reachDiameter_needs_hk :
    ReachDiameterBound Chain.I Chain.T 2 ∧ ¬ ((2 : Nat) ≤ 1) ∧
      BMC Chain.I Chain.T Chain.P 1 ∧ ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_reachDiameterBound_two, by decide, chain_bmc_one, chain_not_invariant⟩

/-- `bmc_complete_of_reachDiameterBound` needs `hb` (`d = 2`, `k = 2` on `Chain`). -/
theorem bmc_reachDiameter_needs_hb :
    ReachDiameterBound Chain.I Chain.T 2 ∧ (2 : Nat) ≤ 2 ∧
      ¬ BMC Chain.I Chain.T Chain.P 2 ∧ ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_reachDiameterBound_two, Nat.le_refl 2, chain_not_bmc_two, chain_not_invariant⟩

/-- Non-vacuity of `bmc_complete_of_reachDiameterBound` with `0 < d < k`: `Triangle` has
reachability-diameter bound `1`, `1 ≤ 2`, and `BMC 2` holds for `P := True`. -/
theorem nonvacuity_bmc_complete_of_reachDiameterBound :
    ReachDiameterBound Triangle.I Triangle.T 1 ∧ (1 : Nat) ≤ 2 ∧
      BMC Triangle.I Triangle.T (fun _ => True) 2 :=
  ⟨triangle_isReachDiameter_one.1, by decide, fun _ _ _ _ _ _ _ => trivial⟩

/-- `bmc_complete_of_reachRecurrenceBound` needs `hr` (`r = 1`, `k = 1` on `Chain`). -/
theorem bmc_reachRecurrence_needs_hr :
    ¬ ReachRecurrenceBound Chain.I Chain.T 1 ∧ (1 : Nat) ≤ 1 ∧
      BMC Chain.I Chain.T Chain.P 1 ∧ ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_not_reachRecurrenceBound_one, Nat.le_refl 1, chain_bmc_one, chain_not_invariant⟩

/-- `bmc_complete_of_reachRecurrenceBound` needs `hk` (`r = 2`, `k = 1` on `Chain`). -/
theorem bmc_reachRecurrence_needs_hk :
    ReachRecurrenceBound Chain.I Chain.T 2 ∧ ¬ ((2 : Nat) ≤ 1) ∧
      BMC Chain.I Chain.T Chain.P 1 ∧ ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_reachRecurrenceBound_two, by decide, chain_bmc_one, chain_not_invariant⟩

/-- `bmc_complete_of_reachRecurrenceBound` needs `hb` (`r = 2`, `k = 2` on `Chain`). -/
theorem bmc_reachRecurrence_needs_hb :
    ReachRecurrenceBound Chain.I Chain.T 2 ∧ (2 : Nat) ≤ 2 ∧
      ¬ BMC Chain.I Chain.T Chain.P 2 ∧ ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_reachRecurrenceBound_two, Nat.le_refl 2, chain_not_bmc_two, chain_not_invariant⟩

/-- `reachDiameterBound_of_reachRecurrenceBound` needs `hr` (`r = 1` on `Chain`): `1` does not
bound the reachability diameter of `Chain`. -/
theorem reachDiameterBound_of_reachRecurrenceBound_needs_hr :
    ¬ ReachDiameterBound Chain.I Chain.T 1 :=
  chain_not_reachDiameterBound_one

/-- Non-vacuity of `bmc_complete_of_reachRecurrenceBound` (and of
`reachDiameterBound_of_reachRecurrenceBound`) with `0 < r < k`: `Triangle` has reachability
recurrence bound `2`, `2 ≤ 3`, and `BMC 3` holds for `P := True`. -/
theorem nonvacuity_bmc_complete_of_reachRecurrenceBound :
    ReachRecurrenceBound Triangle.I Triangle.T 2 ∧ (2 : Nat) ≤ 3 ∧
      BMC Triangle.I Triangle.T (fun _ => True) 3 :=
  ⟨triangle_isReachRecurrenceDiameter_two.1, by decide, fun _ _ _ _ _ _ _ => trivial⟩

/-- `isReachDiameter_le_of_reachRecurrenceBound` needs `hd` (`d = 3`, `r = 2` on `Chain`). -/
theorem isReachDiameter_le_needs_hd :
    ReachRecurrenceBound Chain.I Chain.T 2 ∧ ¬ ((3 : Nat) ≤ 2) :=
  ⟨chain_reachRecurrenceBound_two, by decide⟩

/-- `isReachDiameter_le_of_reachRecurrenceBound` needs `hr` (`d = 2`, `r = 1` on `Chain`). -/
theorem isReachDiameter_le_needs_hr :
    IsReachDiameter Chain.I Chain.T 2 ∧ ¬ ((2 : Nat) ≤ 1) :=
  ⟨chain_isReachDiameter_two, by decide⟩

/-- Non-vacuity of `isReachDiameter_le_of_reachRecurrenceBound` (with `d < r`): `Triangle` has
reachability diameter `1` and reachability recurrence bound `2`. -/
theorem nonvacuity_isReachDiameter_le_of_reachRecurrenceBound :
    IsReachDiameter Triangle.I Triangle.T 1 ∧ ReachRecurrenceBound Triangle.I Triangle.T 2 :=
  ⟨triangle_isReachDiameter_one, triangle_isReachRecurrenceDiameter_two.1⟩

/-- `bmc_incomplete_of_not_reachDiameterBound` needs `¬ ReachDiameterBound I T k`: at `k = 2`,
which bounds the reachability diameter of `Chain`, the conclusion fails. -/
theorem bmc_incomplete_needs_not_reachDiameterBound :
    ReachDiameterBound Chain.I Chain.T 2 ∧
      ¬ (BMC Chain.I Chain.T (ReachWithin Chain.I Chain.T 2) 2 ∧
          ¬ Invariant Chain.I Chain.T (ReachWithin Chain.I Chain.T 2)) :=
  ⟨chain_reachDiameterBound_two, fun h => h.2 chain_reachWithin_two_invariant⟩

/-! ## Explicit strengthening of a k-inductive property at depth `k + 1 = 2` -/

/-- `simple_kinductive_futureSafe_strengthening` needs `Base (k+1)` (here `k = 1`): in `Stuck`,
`SimpleStep 2` holds (no transitions) but the conclusion fails. -/
theorem futureSafe_strengthening_needs_base_k1 :
    SimpleStep Stuck.T Stuck.P 2 ∧
      ¬ (Initiation Stuck.I (FutureSafe Stuck.T Stuck.P 1) ∧
          Consecution Stuck.T (FutureSafe Stuck.T Stuck.P 1) ∧
          ∀ s, FutureSafe Stuck.T Stuck.P 1 s → Stuck.P s) :=
  ⟨(stuck_step_one.mono (by decide)).simpleStep,
    fun ⟨hi, _, hP⟩ => hP ⟨0, by decide⟩ (hi ⟨0, by decide⟩ trivial)⟩

/-- `simple_kinductive_futureSafe_strengthening` needs `SimpleStep (k+1)` (here `k = 1`): `Chain`
passes `Base 2` but the conclusion fails. -/
theorem futureSafe_strengthening_needs_step_k1 :
    Base Chain.I Chain.T Chain.P 2 ∧
      ¬ (Initiation Chain.I (FutureSafe Chain.T Chain.P 1) ∧
          Consecution Chain.T (FutureSafe Chain.T Chain.P 1) ∧
          ∀ s, FutureSafe Chain.T Chain.P 1 s → Chain.P s) := by
  refine ⟨chain_bmc_one, fun ⟨hi, hc, hP⟩ => ?_⟩
  have h0 : FutureSafe Chain.T Chain.P 1 ⟨0, by decide⟩ := hi ⟨0, by decide⟩ rfl
  have h1 : FutureSafe Chain.T Chain.P 1 ⟨1, by decide⟩ := hc _ ⟨1, by decide⟩ h0 (by decide)
  have h2 : FutureSafe Chain.T Chain.P 1 ⟨2, by decide⟩ := hc _ ⟨2, by decide⟩ h1 (by decide)
  exact absurd (hP _ h2) (by decide)

/-- Non-vacuity of `simple_kinductive_futureSafe_strengthening` on an instance where the plain
step fails: `SelfLoop` passes `Base 2` and `SimpleStep 2` but not `Step 2`. -/
theorem nonvacuity_simple_kinductive_futureSafe_strengthening :
    Base SelfLoop.I SelfLoop.T SelfLoop.P 2 ∧ SimpleStep SelfLoop.T SelfLoop.P 2 ∧
      ¬ Step SelfLoop.T SelfLoop.P 2 :=
  ⟨selfLoop_simple_kind_succeeds_at_two.1, selfLoop_simple_kind_succeeds_at_two.2,
    plain_kind_incomplete_every_depth.2 2⟩

/-! ## Simple-path constraint on a projection of the state -/

theorem not_isSimple_two_bool (g : Nat → Bool) : ¬ IsSimple 2 g := by
  intro h
  have key : ∀ a b c : Bool, a = b ∨ a = c ∨ b = c := by decide
  rcases key (g 0) (g 1) (g 2) with e | e | e
  · exact absurd (h 0 1 (by decide) (by decide) e) (by decide)
  · exact absurd (h 0 2 (by decide) (by decide) e) (by decide)
  · exact absurd (h 1 2 (by decide) (by decide) e) (by decide)

/-- **Imposing the simple-path constraint on a projection of the state is unsound.** In `Chain`,
`Base 2` holds and the step at depth `2` restricted to paths whose *projections*
`s ↦ decide (s.val = 2)` are pairwise distinct holds (vacuously: a projection to `Bool` cannot
take three distinct values), but `P` is not invariant. Compare `kind_simple_sound`, where
distinctness is required of the full states. -/
theorem projected_simple_step_unsound :
    Base Chain.I Chain.T Chain.P 2 ∧
      (∀ π : Nat → Fin 3, IsPath Chain.T 2 π → IsSimple 2 (fun i => decide ((π i).val = 2)) →
        (∀ i, i < 2 → Chain.P (π i)) → Chain.P (π 2)) ∧
      ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_bmc_one, fun _ _ hs _ => absurd hs (not_isSimple_two_bool _), chain_not_invariant⟩

end Toy.KInd
