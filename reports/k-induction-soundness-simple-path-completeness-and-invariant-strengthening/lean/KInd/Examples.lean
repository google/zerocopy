import KInd.Soundness
import KInd.Systems
import KInd.Completeness
import KInd.Separation
import KInd.BMC
import KInd.Strengthening
import KInd.Tightness

/-!
# Positive and negative examples for every definition

Each definition gets at least one intended instance it admits and one it must reject.
-/

namespace Toy.KInd

/-- The path `0, 1, 2` in `Fin 3`. -/
abbrev chainPath : Nat → Fin 3 := countUpTo 2 3 (by decide)

/-! ### `IsPath` -/

theorem isPath_pos : IsPath Chain.T 2 chainPath := by
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> decide

/-- A constant path is not a `Chain` path: `Chain` has no self-loops. -/
theorem isPath_neg : ¬ IsPath Chain.T 1 (fun _ => (0 : Fin 3)) :=
  fun h => absurd (h 0 (by decide)) (by decide)

/-- Values beyond the last index are ignored: a path of `0` transitions is any single state. -/
theorem isPath_zero_any (T : Fin 3 → Fin 3 → Prop) (π : Nat → Fin 3) : IsPath T 0 π :=
  fun i hi => absurd hi (Nat.not_lt_zero i)

/-! ### `IsSimple` -/

theorem isSimple_pos : IsSimple 2 chainPath := countUpTo_simple _

theorem isSimple_neg : ¬ IsSimple 1 (fun _ => (0 : Fin 3)) :=
  fun h => absurd (h 0 1 (by decide) (by decide) rfl) (by decide)

/-! ### `ReachIn`, `Reachable`, `ReachWithin` -/

theorem reachIn_pos : ReachIn Chain.I Chain.T 2 ⟨2, by decide⟩ := chain_reachIn_two

theorem reachIn_neg : ¬ ReachIn Chain.I Chain.T 1 ⟨2, by decide⟩ := by
  simp only [reachIn_succ_iff, reachIn_zero_iff]
  decide

theorem reachable_pos : Reachable Chain.I Chain.T ⟨2, by decide⟩ := ⟨2, chain_reachIn_two⟩

/-- The state `1` of `SelfLoop` has a self-loop and an edge to `2`, but is not reachable. -/
theorem reachable_neg : ¬ Reachable SelfLoop.I SelfLoop.T ⟨1, by decide⟩ :=
  fun h => absurd ((selfLoop_reachable_iff _).mp h) (by decide)

theorem reachWithin_pos : ReachWithin Chain.I Chain.T 2 ⟨2, by decide⟩ :=
  ⟨2, Nat.le_refl 2, chain_reachIn_two⟩

theorem reachWithin_neg : ¬ ReachWithin Chain.I Chain.T 1 ⟨2, by decide⟩ :=
  chain_not_reachWithin_one

/-! ### `Invariant` -/

theorem invariant_pos : Invariant SelfLoop.I SelfLoop.T SelfLoop.P := selfLoop_invariant

theorem invariant_neg : ¬ Invariant Chain.I Chain.T Chain.P := chain_not_invariant

/-! ### `Base` and `BMC` -/

theorem base_pos : Base TwoInd.I TwoInd.T TwoInd.P 2 := nonvacuity_kind_sound.1

/-- `Base 3` of `Chain` covers the path `0, 1, 2`, which ends outside `P`. -/
theorem base_neg : ¬ Base Chain.I Chain.T Chain.P 3 :=
  fun h => absurd (h 2 (by decide) chainPath (by decide) isPath_pos 2 (Nat.le_refl 2))
    (by decide)

/-- `Base 0` is vacuous: it holds even for the empty property. -/
theorem base_zero_vacuous : Base Stuck.I Stuck.T Stuck.P 0 :=
  fun j hj => absurd hj (Nat.not_lt_zero j)

theorem bmc_pos : BMC Chain.I Chain.T Chain.P 1 := chain_bmc_one

theorem bmc_neg : ¬ BMC Chain.I Chain.T Chain.P 2 :=
  fun h => chain_not_invariant (bmc_complete_fin h)

/-! ### `Step` and `SimpleStep` -/

theorem step_pos : Step TwoInd.T TwoInd.P 2 := nonvacuity_kind_sound.2

theorem step_neg : ¬ Step TwoInd.T TwoInd.P 1 := one_induction_fails_two_induction_succeeds.1

theorem simpleStep_pos : SimpleStep SelfLoop.T SelfLoop.P 2 :=
  selfLoop_simple_kind_succeeds_at_two.2

/-- The simple path `1 → 2` of `SelfLoop` starts in `P` and ends outside it. -/
theorem simpleStep_neg : ¬ SimpleStep SelfLoop.T SelfLoop.P 1 := by
  rw [simpleStep_one_iff]
  decide

/-- `SimpleStep` is strictly weaker than `Step`: on `SelfLoop` at depth `2` the former holds and
the latter fails. -/
theorem simpleStep_not_step : SimpleStep SelfLoop.T SelfLoop.P 2 ∧ ¬ Step SelfLoop.T SelfLoop.P 2 :=
  ⟨simpleStep_pos, plain_kind_incomplete_every_depth.2 2⟩

/-! ### `ReachDiameterBound`, `IsReachDiameter`, `ReachRecurrenceBound`, `IsReachRecurrenceDiameter` -/

theorem reachDiameterBound_pos : ReachDiameterBound Chain.I Chain.T 2 := chain_reachDiameterBound_two

theorem reachDiameterBound_neg : ¬ ReachDiameterBound Chain.I Chain.T 1 := chain_not_reachDiameterBound_one

theorem isReachDiameter_pos : IsReachDiameter Chain.I Chain.T 2 := chain_isReachDiameter_two

/-- `3` bounds the reachability diameter of `Chain` but is not the least bound. -/
theorem isReachDiameter_neg : ¬ IsReachDiameter Chain.I Chain.T 3 :=
  fun h => absurd (h.2 2 chain_reachDiameterBound_two) (by decide)

theorem reachRecurrenceBound_pos : ReachRecurrenceBound Chain.I Chain.T 2 := chain_reachRecurrenceBound_two

theorem reachRecurrenceBound_neg : ¬ ReachRecurrenceBound Chain.I Chain.T 1 :=
  fun h => absurd (h 2 chainPath (by decide) isPath_pos isSimple_pos) (by decide)

theorem isReachRecurrenceDiameter_pos : IsReachRecurrenceDiameter Chain.I Chain.T 2 :=
  ⟨chain_reachRecurrenceBound_two, fun _ h => h 2 chainPath (by decide) isPath_pos isSimple_pos⟩

theorem isReachRecurrenceDiameter_neg : ¬ IsReachRecurrenceDiameter Chain.I Chain.T 3 :=
  fun h => absurd (h.2 2 chain_reachRecurrenceBound_two) (by decide)

/-- Convention: with no initial state, the reachability diameter and the reachability
recurrence diameter are both `0` (nothing is reachable), for any transition relation. -/
theorem isReachDiameter_no_init {σ : Type} (T : σ → σ → Prop) :
    IsReachDiameter (fun _ => False) T 0 :=
  ⟨fun _ ⟨_, _, h0, _, _⟩ => h0.elim, fun _ _ => Nat.zero_le _⟩

theorem isReachRecurrenceDiameter_no_init {σ : Type} (T : σ → σ → Prop) :
    IsReachRecurrenceDiameter (fun _ => False) T 0 :=
  ⟨fun _ _ h0 _ _ => h0.elim, fun _ _ => Nat.zero_le _⟩

/-- The reachability notions ignore unreachable parts of the graph: `SelfLoop` has reachability
diameter `0` and reachability recurrence bound `0`, although its unreachable edge `1 → 2` gives
it graph-theoretic diameter and recurrence diameter at least `1`. -/
theorem selfLoop_reach_diameters_zero :
    IsReachDiameter SelfLoop.I SelfLoop.T 0 ∧ IsReachRecurrenceDiameter SelfLoop.I SelfLoop.T 0 :=
  ⟨⟨selfLoop_reachDiameterBound_zero_bmc_zero.1, fun _ _ => Nat.zero_le _⟩,
   ⟨selfLoop_reachRecurrenceBound_zero, fun _ _ => Nat.zero_le _⟩⟩

/-! ### `Initiation`, `Consecution`, `FutureSafe` -/

theorem initiation_pos : Initiation SelfLoop.I SelfLoop.P := by
  unfold Initiation
  decide

theorem initiation_neg : ¬ Initiation Chain.I (fun s => s.val ≠ 0) := by
  unfold Initiation
  decide

theorem consecution_pos : Consecution SelfLoop.T (fun s => s.val = 0) := by
  unfold Consecution
  decide

theorem consecution_neg : ¬ Consecution TwoInd.T TwoInd.P := by
  rw [← step_one_iff]
  exact step_neg

theorem futureSafe_pos : FutureSafe TwoInd.T TwoInd.P 1 ⟨0, by decide⟩ :=
  (twoInd_futureSafe_one_iff _).mpr rfl

theorem futureSafe_neg : ¬ FutureSafe TwoInd.T TwoInd.P 1 ⟨1, by decide⟩ :=
  fun h => absurd ((twoInd_futureSafe_one_iff _).mp h) (by decide)

end Toy.KInd
