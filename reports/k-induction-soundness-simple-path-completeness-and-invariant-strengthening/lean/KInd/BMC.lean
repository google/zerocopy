import KInd.Soundness
import KInd.Finite
import KInd.Systems
import KInd.Completeness

/-!
# Bounded model checking and completeness thresholds

`BMC I T P k` checks all paths from initial states with at most `k` transitions. All diameters
here are the initialized (reachability) notions defined in `KInd.Basic`. Only safety
properties (`□ P`) are treated.

* `bmc_complete_of_reachDiameterBound`: if every reachable state is reachable within `d`
  transitions and `d ≤ k`, then `BMC k` implies safety.
* `reachDiameterBound_of_reachRecurrenceBound`: a bound on the length of simple paths from
  initial states is a reachability-diameter bound; hence `bmc_complete_of_reachRecurrenceBound`
  and `isReachDiameter_le_of_reachRecurrenceBound`.
* `bmc_complete_fin`: in a system with `n` states, `BMC (n - 1)` implies safety. On an infinite
  state type no depth is complete in general (`bmc_incomplete_every_depth_infinite`).
* `bmc_complete_all_props_iff_reachDiameterBound`: `BMC k` implies safety *for every property*
  exactly when `k` bounds the reachability diameter; below it, the property "reachable within `k`
  steps" passes `BMC k` but is not invariant (`bmc_incomplete_of_not_reachDiameterBound`).
-/

namespace Toy.KInd

universe u

section General

variable {σ : Type u} {I : σ → Prop} {T : σ → σ → Prop} {P : σ → Prop}

theorem reachWithin_zero_iff {s : σ} : ReachWithin I T 0 s ↔ I s := by
  constructor
  · rintro ⟨j, hj, hr⟩
    have : j = 0 := by omega
    subst this
    exact reachIn_zero_iff.mp hr
  · intro h
    exact ⟨0, Nat.le_refl 0, reachIn_zero_iff.mpr h⟩

theorem reachWithin_succ_iff {k : Nat} {s : σ} :
    ReachWithin I T (k + 1) s ↔ ReachWithin I T k s ∨ ReachIn I T (k + 1) s := by
  constructor
  · rintro ⟨j, hj, hr⟩
    by_cases h : j = k + 1
    · subst h; exact Or.inr hr
    · exact Or.inl ⟨j, by omega, hr⟩
  · rintro (⟨j, hj, hr⟩ | hr)
    · exact ⟨j, by omega, hr⟩
    · exact ⟨k + 1, Nat.le_refl _, hr⟩

theorem bmc_iff_reachWithin {k : Nat} : BMC I T P k ↔ ∀ s, ReachWithin I T k s → P s := by
  rw [bmc_iff_reachIn]
  constructor
  · rintro h s ⟨j, hj, hr⟩
    exact h j hj s hr
  · intro h j hj s hr
    exact h s ⟨j, hj, hr⟩

theorem ReachDiameterBound.mono {d d' : Nat} (h : ReachDiameterBound I T d) (hd : d ≤ d') :
    ReachDiameterBound I T d' := by
  intro s hs
  obtain ⟨j, hj, hr⟩ := h s hs
  exact ⟨j, by omega, hr⟩

theorem ReachRecurrenceBound.mono {r r' : Nat} (h : ReachRecurrenceBound I T r) (hr : r ≤ r') :
    ReachRecurrenceBound I T r' :=
  fun j π h0 hp hs => Nat.le_trans (h j π h0 hp hs) hr

/-- **BMC is complete at any depth bounding the reachability diameter.** If every reachable
state is reachable from an initial state in at most `d` transitions, `d ≤ k`, and no path from an
initial state with at most `k` transitions reaches a `¬P` state, then `P` is invariant. -/
theorem bmc_complete_of_reachDiameterBound {d k : Nat} (hd : ReachDiameterBound I T d)
    (hk : d ≤ k) (hb : BMC I T P k) : Invariant I T P :=
  fun s hs =>
    let ⟨j, hj, π, h0, hp, he⟩ := hd s hs
    he ▸ hb j (Nat.lt_succ_of_le (Nat.le_trans hj hk)) π h0 hp j (Nat.le_refl j)

/-- **A reachability-recurrence bound is a reachability-diameter bound.** If every simple path
from an initial state has at most `r` transitions, then every reachable state is reachable from
an initial state in at most `r` transitions. -/
theorem reachDiameterBound_of_reachRecurrenceBound {r : Nat} (hr : ReachRecurrenceBound I T r) :
    ReachDiameterBound I T r := by
  rintro s ⟨m, hm⟩
  obtain ⟨m', -, π, h0, hp, hs, he⟩ := exists_simple_reachIn hm
  exact ⟨m', hr m' π h0 hp hs, π, h0, hp, he⟩

/-- **BMC is complete at any depth bounding the reachability recurrence diameter.** If every
simple path from an initial state has at most `r` transitions, `r ≤ k`, and `BMC I T P k` holds,
then `P` is invariant. -/
theorem bmc_complete_of_reachRecurrenceBound {r k : Nat} (hr : ReachRecurrenceBound I T r)
    (hk : r ≤ k) (hb : BMC I T P k) : Invariant I T P :=
  bmc_complete_of_reachDiameterBound (reachDiameterBound_of_reachRecurrenceBound hr) hk hb

/-- Any lower bound on all reachability-diameter bounds is at most every reachability-recurrence
bound. (Only this minimality property of the reachability diameter is needed below.) -/
theorem le_of_reachDiameter_lower_bound_of_reachRecurrenceBound {d r : Nat}
    (hd : ∀ d', ReachDiameterBound I T d' → d ≤ d') (hr : ReachRecurrenceBound I T r) : d ≤ r :=
  hd r (reachDiameterBound_of_reachRecurrenceBound hr)

/-- **The reachability diameter is at most every reachability-recurrence bound.** If `d` is the
reachability diameter and every simple path from an initial state has at most `r` transitions,
then `d ≤ r`. In particular the reachability diameter is at most the reachability recurrence
diameter (`isReachDiameter_le_of_isReachRecurrenceDiameter`). -/
theorem isReachDiameter_le_of_reachRecurrenceBound {d r : Nat} (hd : IsReachDiameter I T d)
    (hr : ReachRecurrenceBound I T r) : d ≤ r :=
  le_of_reachDiameter_lower_bound_of_reachRecurrenceBound hd.2 hr

/-- The reachability diameter is at most the reachability recurrence diameter (when both
exist; on an infinite state type the latter need not exist even when the former does, see
`starChain_reachDiameter_one_no_reachRecurrenceBound`). -/
theorem isReachDiameter_le_of_isReachRecurrenceDiameter {d r : Nat} (hd : IsReachDiameter I T d)
    (hr : IsReachRecurrenceDiameter I T r) : d ≤ r :=
  isReachDiameter_le_of_reachRecurrenceBound hd hr.1

/-- **Below a reachability-diameter bound, BMC is incomplete for some property.** If `k` does not
bound the reachability diameter, the property `ReachWithin I T k` ("reachable within `k`
transitions") passes `BMC k` but is not invariant. (`Invariant I T (ReachWithin I T k)` is
definitionally `ReachDiameterBound I T k`.) -/
theorem bmc_incomplete_of_not_reachDiameterBound {k : Nat} (h : ¬ ReachDiameterBound I T k) :
    BMC I T (ReachWithin I T k) k ∧ ¬ Invariant I T (ReachWithin I T k) :=
  ⟨fun _ hj π h0 hp i hi =>
      ⟨i, Nat.le_of_lt_succ (Nat.lt_of_le_of_lt hi hj), π, h0, hp.mono hi, rfl⟩,
   h⟩

/-- `ReachWithin I T k` always passes `BMC k`. -/
theorem bmc_reachWithin_self {k : Nat} :
    BMC I T (ReachWithin I T k) k :=
  fun _ hj π h0 hp i hi => ⟨i, Nat.le_of_lt_succ (Nat.lt_of_le_of_lt hi hj), π, h0, hp.mono hi, rfl⟩

theorem not_reachDiameterBound_of_lt_isReachDiameter {d k : Nat} (hd : IsReachDiameter I T d) (hk : k < d) :
    ¬ ReachDiameterBound I T k :=
  fun h => absurd (hd.2 k h) (by omega)

/-- **Reachability-diameter bounds are exactly the depths at which BMC is complete for every
safety property.** For a transition system and a depth `k`: `BMC k` implies safety for every
state predicate `P : σ → Prop` if and only if every reachable state is reachable within `k`
transitions. -/
theorem bmc_complete_all_props_iff_reachDiameterBound {k : Nat} :
    (∀ P : σ → Prop, BMC I T P k → Invariant I T P) ↔ ReachDiameterBound I T k :=
  ⟨fun h => h (ReachWithin I T k) (bmc_reachWithin_self),
   fun hd _ hb => bmc_complete_of_reachDiameterBound hd (Nat.le_refl k) hb⟩

end General

/-- **BMC is complete at depth `n - 1` for systems with `n` states.** -/
theorem bmc_complete_fin {n : Nat} {I : Fin n → Prop} {T : Fin n → Fin n → Prop}
    {P : Fin n → Prop} (hb : BMC I T P (n - 1)) : Invariant I T P :=
  bmc_complete_of_reachRecurrenceBound (reachRecurrenceBound_fin I T) (Nat.le_refl _) hb

/-! ## Concrete thresholds and counterexamples -/

theorem chain_reachIn_two : ReachIn Chain.I Chain.T 2 ⟨2, by decide⟩ := by
  simp only [reachIn_succ_iff, reachIn_zero_iff]
  decide

theorem chain_not_reachWithin_one : ¬ ReachWithin Chain.I Chain.T 1 ⟨2, by decide⟩ := by
  simp only [reachWithin_succ_iff, reachWithin_zero_iff, reachIn_succ_iff, reachIn_zero_iff]
  decide

theorem chain_not_invariant : ¬ Invariant Chain.I Chain.T Chain.P :=
  fun h => absurd (h _ ⟨2, chain_reachIn_two⟩) (by decide)

theorem chain_reachDiameterBound_two : ReachDiameterBound Chain.I Chain.T 2 := by
  suffices h : ∀ s, ReachWithin Chain.I Chain.T 2 s from fun s _ => h s
  simp only [reachWithin_succ_iff, reachWithin_zero_iff, reachIn_succ_iff, reachIn_zero_iff]
  decide

theorem chain_not_reachDiameterBound_one : ¬ ReachDiameterBound Chain.I Chain.T 1 :=
  fun h => chain_not_reachWithin_one (h _ ⟨2, chain_reachIn_two⟩)

theorem chain_isReachDiameter_two : IsReachDiameter Chain.I Chain.T 2 := by
  refine ⟨chain_reachDiameterBound_two, fun d' hd' => ?_⟩
  refine Classical.byContradiction fun hlt => ?_
  exact chain_not_reachDiameterBound_one (hd'.mono (by omega))

theorem chain_reachRecurrenceBound_two : ReachRecurrenceBound Chain.I Chain.T 2 :=
  reachRecurrenceBound_fin Chain.I Chain.T

theorem chain_bmc_one : BMC Chain.I Chain.T Chain.P 1 := by
  rw [bmc_iff_reachWithin]
  simp only [reachWithin_succ_iff, reachWithin_zero_iff, reachIn_succ_iff, reachIn_zero_iff]
  decide

/-- **BMC below the reachability diameter does not imply safety** (concrete instance). `Chain`
has reachability diameter `2`; `BMC 1` holds for `P`, but `P` is not invariant. -/
theorem chain_bmc_below_diameter :
    IsReachDiameter Chain.I Chain.T 2 ∧ BMC Chain.I Chain.T Chain.P 1 ∧
      ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_isReachDiameter_two, chain_bmc_one, chain_not_invariant⟩

/-- Same instance, phrased against the reachability recurrence bound: `2` bounds the reachability
recurrence diameter of
`Chain`, `BMC 1` holds, and `P` is not invariant. -/
theorem chain_bmc_below_reachRecurrenceBound :
    ReachRecurrenceBound Chain.I Chain.T 2 ∧ BMC Chain.I Chain.T Chain.P 1 ∧
      ¬ Invariant Chain.I Chain.T Chain.P :=
  ⟨chain_reachRecurrenceBound_two, chain_bmc_one, chain_not_invariant⟩

theorem oneEdge_not_reachRecurrenceBound_zero : ¬ ReachRecurrenceBound OneEdge.I OneEdge.T 0 := by
  intro h
  have := h 1 (countUpTo 1 2 (by decide)) (by decide)
    (by intro i hi; have : i = 0 := by omega
        subst this; decide)
    (countUpTo_simple _)
  omega

theorem oneEdge_isReachRecurrenceDiameter_one : IsReachRecurrenceDiameter OneEdge.I OneEdge.T 1 :=
  ⟨reachRecurrenceBound_fin OneEdge.I OneEdge.T, fun r' hr' =>
    hr' 1 (countUpTo 1 2 (by decide)) (by decide)
      (by intro i hi; have : i = 0 := by omega
          subst this; decide)
      (countUpTo_simple _)⟩

/-- **Off-by-one: the base check at depth equal to the reachability recurrence diameter is
unsound.** `OneEdge` has reachability recurrence diameter `1`; `Base 1` (paths with at most one state) holds for `P`,
but `P` is not invariant. The correct threshold check is `BMC 1 = Base 2`, which fails here. -/
theorem base_at_recurrence_diameter_unsound :
    IsReachRecurrenceDiameter OneEdge.I OneEdge.T 1 ∧ Base OneEdge.I OneEdge.T OneEdge.P 1 ∧
      ¬ Invariant OneEdge.I OneEdge.T OneEdge.P ∧ ¬ BMC OneEdge.I OneEdge.T OneEdge.P 1 := by
  have hr : ReachIn OneEdge.I OneEdge.T 1 ⟨1, by decide⟩ := by
    simp only [reachIn_succ_iff, reachIn_zero_iff]
    decide
  refine ⟨oneEdge_isReachRecurrenceDiameter_one, ?_, ?_, ?_⟩
  · rw [base_iff_reachIn]
    intro j hj s hs
    have : j = 0 := by omega
    subst this
    rw [reachIn_zero_iff] at hs
    simp only [OneEdge.P]
    omega
  · exact fun h => absurd (h _ ⟨1, hr⟩) (by decide)
  · rw [bmc_iff_reachIn]
    exact fun h => absurd (h 1 (Nat.le_refl 1) _ hr) (by decide)

theorem triangle_isReachDiameter_one : IsReachDiameter Triangle.I Triangle.T 1 := by
  have hb : ReachDiameterBound Triangle.I Triangle.T 1 := by
    suffices h : ∀ s, ReachWithin Triangle.I Triangle.T 1 s from fun s _ => h s
    simp only [reachWithin_succ_iff, reachWithin_zero_iff, reachIn_succ_iff, reachIn_zero_iff]
    decide
  refine ⟨hb, fun d' hd' => Classical.byContradiction fun hlt => ?_⟩
  have h0 : ReachDiameterBound Triangle.I Triangle.T 0 := by
    have : d' = 0 := by omega
    exact this ▸ hd'
  have hr : ReachIn Triangle.I Triangle.T 1 ⟨1, by decide⟩ := by
    simp only [reachIn_succ_iff, reachIn_zero_iff]
    decide
  have := h0 _ ⟨1, hr⟩
  rw [reachWithin_zero_iff] at this
  exact absurd this (by decide)

theorem triangle_isReachRecurrenceDiameter_two : IsReachRecurrenceDiameter Triangle.I Triangle.T 2 :=
  ⟨reachRecurrenceBound_fin Triangle.I Triangle.T, fun r' hr' =>
    hr' 2 (countUpTo 2 3 (by decide)) (by decide)
      (by intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl <;> decide)
      (countUpTo_simple _)⟩

/-- **The reachability diameter can be strictly smaller than the reachability recurrence
diameter** (smallest instance). `Triangle` has reachability diameter `1` and reachability
recurrence diameter `2`, so BMC at depth `1` is already complete for it. -/
theorem triangle_reachDiameter_one_reachRecurrenceDiameter_two :
    IsReachDiameter Triangle.I Triangle.T 1 ∧ IsReachRecurrenceDiameter Triangle.I Triangle.T 2 :=
  ⟨triangle_isReachDiameter_one, triangle_isReachRecurrenceDiameter_two⟩

/-! ## Non-vacuity witnesses -/

theorem selfLoop_reachable_iff (s : Fin 3) : Reachable SelfLoop.I SelfLoop.T s ↔ s.val = 0 := by
  constructor
  · exact invariant_of_inductive (Q := fun s : Fin 3 => s.val = 0) (fun s hs => hs)
      (by unfold Consecution; decide) (fun _ h => h) s
  · intro h
    exact reachable_of_init h

/-- `SelfLoop` has reachability-diameter bound `0` and passes `BMC 0`; by `bmc_complete_of_reachDiameterBound`
this proves its invariant, although plain k-induction fails on it at every depth. -/
theorem selfLoop_reachDiameterBound_zero_bmc_zero :
    ReachDiameterBound SelfLoop.I SelfLoop.T 0 ∧ BMC SelfLoop.I SelfLoop.T SelfLoop.P 0 := by
  refine ⟨fun s hs => reachWithin_zero_iff.mpr ((selfLoop_reachable_iff s).mp hs), ?_⟩
  rw [bmc_iff_reachWithin]
  simp only [reachWithin_zero_iff]
  decide

/-- `SelfLoop` has reachability recurrence bound `0`: the only transition from the initial state is its
self-loop, so no simple path from it has a transition. -/
theorem selfLoop_reachRecurrenceBound_zero : ReachRecurrenceBound SelfLoop.I SelfLoop.T 0 := by
  intro j π h0 hp hs
  refine Classical.byContradiction fun hj => ?_
  have h01 : SelfLoop.T (π 0) (π 1) := hp 0 (by omega)
  have : π 0 = π 1 := by
    simp only [SelfLoop.I] at h0
    simp only [SelfLoop.T] at h01
    apply Fin.ext
    omega
  have := hs 0 1 (by omega) (by omega) this
  omega

/-! ## Infinite and parametric systems -/

theorem natSucc_path_val {m : Nat} {π : Nat → Nat} (h0 : NatSucc.I (π 0))
    (hp : IsPath NatSucc.T m π) : ∀ i, i ≤ m → π i = i := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih =>
    intro hi
    have hstep := hp i (by omega)
    have hprev := ih (by omega)
    simp only [NatSucc.T] at hstep
    omega

theorem natSucc_reachIn_self (m : Nat) : ReachIn NatSucc.I NatSucc.T m m :=
  ⟨fun t => t, rfl, fun _ _ => rfl, rfl⟩

/-- **No BMC depth is complete on an infinite state type in general.** On the infinite counter
`NatSucc`, for every depth `k` there is no reachability-diameter bound `k`, and the property
`s ≤ k` passes `BMC k` but is not invariant. -/
theorem bmc_incomplete_every_depth_infinite (k : Nat) :
    ¬ ReachDiameterBound NatSucc.I NatSucc.T k ∧
      BMC NatSucc.I NatSucc.T (fun s => s ≤ k) k ∧
      ¬ Invariant NatSucc.I NatSucc.T (fun s => s ≤ k) := by
  have hbmc : BMC NatSucc.I NatSucc.T (fun s => s ≤ k) k := by
    intro j hj π h0 hp i hi
    have := natSucc_path_val h0 hp i hi
    omega
  have hninv : ¬ Invariant NatSucc.I NatSucc.T (fun s => s ≤ k) := by
    intro hinv
    have : k + 1 ≤ k := hinv (k + 1) ⟨k + 1, natSucc_reachIn_self (k + 1)⟩
    omega
  have hnd : ¬ ReachDiameterBound NatSucc.I NatSucc.T k := fun hd =>
    hninv (bmc_complete_of_reachDiameterBound hd (Nat.le_refl k) hbmc)
  exact ⟨hnd, hbmc, hninv⟩

theorem finChain_path_val {m j : Nat} {π : Nat → Fin (m + 2)}
    (h0 : FinChain.I m (π 0)) (hp : IsPath (FinChain.T m) j π) :
    ∀ i, i ≤ j → (π i).val = i := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih =>
    intro hi
    have hstep := hp i (by omega)
    have hprev := ih (by omega)
    simp only [FinChain.T] at hstep
    omega

/-- **Depth `n - 1` in `bmc_complete_fin` cannot be lowered, for any `n ≥ 2`.** The chain on
`Fin (m + 2)` (so `n = m + 2`) passes `BMC m` (depth `n - 2`) but `P` is not invariant. -/
theorem bmc_complete_fin_depth_tight_all (m : Nat) :
    BMC (FinChain.I m) (FinChain.T m) (FinChain.P m) m ∧
      ¬ Invariant (FinChain.I m) (FinChain.T m) (FinChain.P m) := by
  refine ⟨?_, ?_⟩
  · intro j hj π h0 hp i hi
    have := finChain_path_val h0 hp i hi
    simp only [FinChain.P]
    omega
  · intro hinv
    have hr : ReachIn (FinChain.I m) (FinChain.T m) (m + 1) ⟨m + 1, by omega⟩ :=
      ⟨countUpTo (m + 1) (m + 2) (by omega), rfl,
        by intro i hi; simp only [FinChain.T, countUpTo_val]; omega,
        by apply Fin.ext; simp only [countUpTo_val]; omega⟩
    have := hinv ⟨m + 1, by omega⟩ ⟨m + 1, hr⟩
    simp only [FinChain.P] at this
    omega

/-- **On an infinite state type a finite reachability diameter does not give a finite
reachability recurrence bound.** `StarChain` has reachability diameter `1`, but no
`r` bounds the length of its simple paths from the initial state. -/
theorem starChain_reachDiameter_one_no_reachRecurrenceBound :
    IsReachDiameter StarChain.I StarChain.T 1 ∧
      ¬ ∃ r, ReachRecurrenceBound StarChain.I StarChain.T r := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro s _
    by_cases hs : s = 0
    · subst hs; exact ⟨0, by decide, reachIn_zero_iff.mpr rfl⟩
    · refine ⟨1, Nat.le_refl 1, fun i => if i = 0 then 0 else s, rfl, ?_, rfl⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      exact Or.inl ⟨rfl, Nat.pos_of_ne_zero hs⟩
  · intro d' hd'
    by_cases h0 : d' = 0
    · subst h0
      have hr1 : Reachable StarChain.I StarChain.T 1 :=
        ⟨1, fun i => if i = 0 then 0 else 1, rfl,
          by
            intro i hi
            have hi0 : i = 0 := by omega
            subst hi0
            exact Or.inl ⟨rfl, Nat.le_refl 1⟩,
          rfl⟩
      have := reachWithin_zero_iff.mp (hd' 1 hr1)
      simp only [StarChain.I] at this
      omega
    · omega
  · rintro ⟨r, hr⟩
    have hle := hr (r + 1) (fun i => i) rfl
      (by
        intro i _
        by_cases hi : i = 0
        · subst hi; exact Or.inl ⟨rfl, Nat.le_refl 1⟩
        · exact Or.inr ⟨Nat.pos_of_ne_zero hi, rfl⟩)
      (by intro i j _ _ hij; exact hij)
    omega

theorem triangleN_isReachDiameter_one (m : Nat) :
    IsReachDiameter (TriangleN.I m) (TriangleN.T m) 1 := by
  refine ⟨?_, ?_⟩
  · intro s _
    by_cases hs : s.val = 0
    · exact ⟨0, Nat.zero_le 1, reachIn_zero_iff.mpr hs⟩
    · refine ⟨1, Nat.le_refl 1, fun i => if i = 0 then ⟨0, by omega⟩ else s, rfl, ?_, rfl⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      show (0 : Nat) < s.val
      omega
  · intro d' hd'
    refine Classical.byContradiction fun hlt => ?_
    have hd0 : d' = 0 := by omega
    subst hd0
    have hr1 : Reachable (TriangleN.I m) (TriangleN.T m) ⟨1, by omega⟩ :=
      ⟨1, fun i => if i = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩, rfl,
        by
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          show (0 : Nat) < 1
          omega,
        rfl⟩
    have := reachWithin_zero_iff.mp (hd' _ hr1)
    simp only [TriangleN.I] at this
    omega

theorem triangleN_isReachRecurrenceDiameter (m : Nat) :
    IsReachRecurrenceDiameter (TriangleN.I m) (TriangleN.T m) (m + 1) := by
  refine ⟨?_, ?_⟩
  · intro j π _ _ hs
    have := hs.lt_card
    omega
  · intro r' hr'
    exact hr' (m + 1) (countUpTo (m + 1) (m + 2) (by omega))
      (by simp only [TriangleN.I, countUpTo_val]; omega)
      (by intro i hi; simp only [TriangleN.T, countUpTo_val]; omega)
      (countUpTo_simple _)

/-- **The reachability diameter can be smaller than the reachability recurrence diameter by
`n - 2` in an `n`-state system, for every `n ≥ 2`.** In `TriangleN m` (`n = m + 2` states,
transitions `s → t` for `s < t`), the reachability diameter is `1` and the reachability
recurrence diameter is `m + 1 = n - 1`. -/
theorem reachDiameter_lt_reachRecurrenceDiameter_family (m : Nat) :
    IsReachDiameter (TriangleN.I m) (TriangleN.T m) 1 ∧
      IsReachRecurrenceDiameter (TriangleN.I m) (TriangleN.T m) (m + 1) :=
  ⟨triangleN_isReachDiameter_one m, triangleN_isReachRecurrenceDiameter m⟩

end Toy.KInd
