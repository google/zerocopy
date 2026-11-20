import KInd.Soundness
import KInd.Systems
import KInd.Separation
import KInd.Completeness

/-!
# Inductive invariants and strengthening

* `invariant_of_inductive_strengthening`: if `P` and `Q` hold initially and `P ∧ Q` is
  preserved by every transition, then `P` is invariant (lemma strengthening).
* `reachable_strongest_inductive_invariant`: the reachable set is inductive and contained in
  every inductive set containing the initial states. Consequently every invariant `P`, of every
  transition system (finite or not), has a 1-inductive strengthening, namely
  `P ∧ Reachable` (`invariant_iff_reachable_strengthening_inductive`).
* `futureSafe_forever_weakest_inductive_strengthening`: dually, "every path from here stays in
  `P`" is the weakest predicate that is preserved by transitions and implies `P`.
* `simple_kinductive_futureSafe_strengthening`: if `P` passes `Base (k+1)` and the simple-path
  step `SimpleStep (k+1)`, then `FutureSafe T P k` ("`P` holds now and for the next `k` steps on
  every path") is a 1-inductive strengthening of `P`, given explicitly. The plain-step version
  `kinductive_futureSafe_strengthening` is a corollary.
-/

namespace Toy.KInd

universe u

section General

variable {σ : Type u} {I : σ → Prop} {T : σ → σ → Prop} {P : σ → Prop}

/-- **Inductive strengthening.** If every initial state satisfies `P` and `Q`, and the
conjunction `P ∧ Q` is preserved by every transition, then every reachable state satisfies
`P`. -/
theorem invariant_of_inductive_strengthening {Q : σ → Prop} (hIP : Initiation I P)
    (hIQ : Initiation I Q) (hcons : Consecution T (fun s => P s ∧ Q s)) :
    Invariant I T P :=
  invariant_of_inductive (Q := fun s => P s ∧ Q s) (fun s hs => ⟨hIP s hs, hIQ s hs⟩) hcons
    (fun _ h => h.1)

/-- **The reachable set is the strongest inductive invariant.** It contains the initial
states, is preserved by every transition, and is contained in every predicate that contains the
initial states and is preserved by every transition. -/
theorem reachable_strongest_inductive_invariant :
    Initiation I (Reachable I T) ∧ Consecution T (Reachable I T) ∧
      ∀ Q : σ → Prop, Initiation I Q → Consecution T Q → ∀ s, Reachable I T s → Q s :=
  ⟨fun _ hs => reachable_of_init hs, fun _ _ hs hst => hs.step hst,
    fun _ hinit hcons => invariant_of_inductive hinit hcons (fun _ h => h)⟩

/-- **Every invariant has an explicit 1-inductive strengthening.** For every transition system
and property `P`: `P` is invariant iff `P ∧ Reachable` satisfies initiation and consecution. -/
theorem invariant_iff_reachable_strengthening_inductive :
    Invariant I T P ↔
      Initiation I (fun s => P s ∧ Reachable I T s) ∧
        Consecution T (fun s => P s ∧ Reachable I T s) := by
  constructor
  · intro h
    refine ⟨fun s hs => ⟨h s (reachable_of_init hs), reachable_of_init hs⟩, ?_⟩
    intro s t ⟨_, hr⟩ hst
    exact ⟨h t (hr.step hst), hr.step hst⟩
  · rintro ⟨hinit, hcons⟩
    exact invariant_of_inductive hinit hcons (fun _ h => h.1)

/-- Inductive invariants are complete for safety: `P` is invariant iff some `Q` with
initiation and consecution implies `P`. -/
theorem invariant_iff_exists_inductive_strengthening :
    Invariant I T P ↔ ∃ Q : σ → Prop, Initiation I Q ∧ Consecution T Q ∧ ∀ s, Q s → P s := by
  constructor
  · intro h
    obtain ⟨hi, hc⟩ := invariant_iff_reachable_strengthening_inductive.mp h
    exact ⟨_, hi, hc, fun _ h => h.1⟩
  · rintro ⟨Q, hi, hc, hQP⟩
    exact invariant_of_inductive hi hc hQP

/-- Prepending a transition `s → π 0` to a path with `j` transitions gives a path with `j + 1`
transitions. -/
theorem IsPath.cons {j : Nat} {s : σ} {π : Nat → σ} (hst : T s (π 0)) (hp : IsPath T j π) :
    IsPath T (j + 1) (fun i => if i = 0 then s else π (i - 1)) := by
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0
    simp only [ite_true, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    exact hst
  · have e : i + 1 - 1 = i - 1 + 1 := by omega
    simp only [hi0, Nat.add_one_ne_zero, ite_false, e]
    exact hp (i - 1) (by omega)

/-- If every path of at most `m + 1` transitions from `s` ends in `P`, then every path of at most
`m` transitions from a successor of `s` does. -/
theorem FutureSafe.of_step {m : Nat} {s t : σ} (h : FutureSafe T P (m + 1) s) (hst : T s t) :
    FutureSafe T P m t := by
  intro j hj π h0 hp
  have := h (j + 1) (by omega) _ rfl (IsPath.cons (h0 ▸ hst) hp)
  simpa using this

/-- **The weakest 1-inductive strengthening.** The predicate "every path from `s`, of any length,
ends in a `P`-state" (`fun s => ∀ m, FutureSafe T P m s`) is preserved by every transition and
implies `P`; it contains every predicate that is preserved by every transition and implies `P`;
and it holds in every initial state exactly when `P` is invariant. -/
theorem futureSafe_forever_weakest_inductive_strengthening :
    Consecution T (fun s => ∀ m, FutureSafe T P m s) ∧
      (∀ s, (∀ m, FutureSafe T P m s) → P s) ∧
      (∀ Q : σ → Prop, Consecution T Q → (∀ s, Q s → P s) →
        ∀ s, Q s → ∀ m, FutureSafe T P m s) ∧
      (Initiation I (fun s => ∀ m, FutureSafe T P m s) ↔ Invariant I T P) := by
  refine ⟨fun s t hs hst m => (hs (m + 1)).of_step hst, ?_, ?_, ?_⟩
  · intro s h
    exact h 0 0 (Nat.le_refl 0) (fun _ => s) rfl (fun i hi => absurd hi (Nat.not_lt_zero _))
  · intro Q hcons hQP s hQ m j _ π h0 hp
    have hall : ∀ i, i ≤ j → Q (π i) := by
      intro i
      induction i with
      | zero => intro _; exact h0 ▸ hQ
      | succ i ih => intro hi; exact hcons _ _ (ih (by omega)) (hp i (by omega))
    exact hQP _ (hall j (Nat.le_refl j))
  · constructor
    · rintro h s ⟨m, π, h0, hp, rfl⟩
      exact h (π 0) h0 m m (Nat.le_refl m) π rfl hp
    · intro h s hs m j _ π h0 hp
      exact h _ ⟨j, π, h0 ▸ hs, hp, rfl⟩

/-- **A property that passes simple-path k-induction at depth `k + 1` has an explicit 1-inductive
strengthening.** If `P` passes `Base (k+1)` and `SimpleStep (k+1)`, then `FutureSafe T P k`
(every path of at most `k` transitions from the state ends in `P`) satisfies initiation and
consecution and implies `P`. -/
theorem simple_kinductive_futureSafe_strengthening {k : Nat} (hb : Base I T P (k + 1))
    (hs : SimpleStep T P (k + 1)) :
    Initiation I (FutureSafe T P k) ∧ Consecution T (FutureSafe T P k) ∧
      ∀ s, FutureSafe T P k s → P s := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs0 j hj π h0 hp
    exact hb j (by omega) π (h0 ▸ hs0) hp j (Nat.le_refl j)
  · intro s t hQ hst j hj π h0 hp
    let ρ : Nat → σ := fun i => if i = 0 then s else π (i - 1)
    have hρ : IsPath T (j + 1) ρ := IsPath.cons (h0 ▸ hst) hp
    have hlast : ρ (j + 1) = π j := by simp [ρ]
    by_cases hjk : j + 1 ≤ k
    · exact hlast ▸ hQ (j + 1) hjk ρ rfl hρ
    · have hjk' : j = k := by omega
      subst j
      -- remove loops from the `(k + 1)`-transition path `ρ` from `s` to `π k`
      have hreach : ReachIn (fun x => x = s) T (k + 1) (π k) := ⟨ρ, rfl, hρ, hlast⟩
      obtain ⟨m', hm', ρ', hρ0, hρp, hρs, hρe⟩ := exists_simple_reachIn hreach
      by_cases hm'k : m' ≤ k
      · exact hρe ▸ hQ m' hm'k ρ' hρ0 hρp
      · have hm'eq : m' = k + 1 := by omega
        subst m'
        exact hρe ▸ hs ρ' hρp hρs (fun i hi => hQ i (by omega) ρ' hρ0 (hρp.mono (by omega)))
  · intro s h
    exact h 0 (Nat.zero_le _) (fun _ => s) rfl (fun i hi => absurd hi (Nat.not_lt_zero _))

/-- The plain-step version: if `P` passes `Base (k+1)` and `Step (k+1)`, then `FutureSafe T P k`
is a 1-inductive strengthening of `P` (a corollary, since `Step` implies `SimpleStep`). -/
theorem kinductive_futureSafe_strengthening {k : Nat} (hb : Base I T P (k + 1))
    (hs : Step T P (k + 1)) :
    Initiation I (FutureSafe T P k) ∧ Consecution T (FutureSafe T P k) ∧
      ∀ s, FutureSafe T P k s → P s :=
  simple_kinductive_futureSafe_strengthening hb hs.simpleStep

end General

/-! ## Tightness counterexamples -/

/-- Dropping `Initiation I P` from `invariant_of_inductive_strengthening`: in `Stuck` with
`Q := True`, `Q` holds initially and `P ∧ Q` is (vacuously) preserved, but `P` is not
invariant. -/
theorem strengthening_needs_init_P :
    Initiation Stuck.I (fun _ => True) ∧
      Consecution Stuck.T (fun s => Stuck.P s ∧ True) ∧
      ¬ Invariant Stuck.I Stuck.T Stuck.P :=
  ⟨fun _ _ => trivial, fun _ _ _ h => h.elim,
    fun h => h ⟨0, by decide⟩ (reachable_of_init trivial)⟩

theorem oneEdge_reachable_one : Reachable OneEdge.I OneEdge.T ⟨1, by decide⟩ :=
  Reachable.step (I := OneEdge.I) (T := OneEdge.T) (s := ⟨0, by decide⟩)
    (reachable_of_init rfl) (by decide)

theorem oneEdge_not_invariant : ¬ Invariant OneEdge.I OneEdge.T OneEdge.P :=
  fun h => absurd (h _ oneEdge_reachable_one) (by decide)

/-- Dropping `Initiation I Q`: in `OneEdge` with `Q := False`, `P` holds initially and
`P ∧ Q` is (vacuously) preserved, but `P` is not invariant. -/
theorem strengthening_needs_init_Q :
    Initiation OneEdge.I OneEdge.P ∧
      Consecution OneEdge.T (fun s => OneEdge.P s ∧ False) ∧
      ¬ Invariant OneEdge.I OneEdge.T OneEdge.P :=
  ⟨fun _ h => h, fun _ _ h _ => h.2.elim, oneEdge_not_invariant⟩

/-- Dropping consecution: in `OneEdge` with `Q := True`, `P` and `Q` hold initially, but `P`
is not invariant. -/
theorem strengthening_needs_consecution :
    Initiation OneEdge.I OneEdge.P ∧ Initiation OneEdge.I (fun _ => True) ∧
      ¬ Invariant OneEdge.I OneEdge.T OneEdge.P :=
  ⟨fun _ h => h, fun _ _ => trivial, oneEdge_not_invariant⟩

/-- Non-vacuity of `invariant_of_inductive_strengthening` with a genuine strengthening: in
`TwoInd`, `P` alone is not preserved by transitions, but with `Q := (· ≠ 1)` all hypotheses
hold. -/
theorem nonvacuity_inductive_strengthening :
    Initiation TwoInd.I TwoInd.P ∧ Initiation TwoInd.I (fun s => s.val ≠ 1) ∧
      Consecution TwoInd.T (fun s => TwoInd.P s ∧ s.val ≠ 1) ∧
      ¬ Consecution TwoInd.T TwoInd.P := by
  unfold Initiation Consecution
  decide

/-- Dropping `Base (k+1)` from `simple_kinductive_futureSafe_strengthening` (with `k = 0`): in
`Stuck`, `SimpleStep 1` holds (no transitions) but the conclusion fails (initiation fails). -/
theorem futureSafe_strengthening_needs_base :
    SimpleStep Stuck.T Stuck.P 1 ∧
      ¬ (Initiation Stuck.I (FutureSafe Stuck.T Stuck.P 0) ∧
          Consecution Stuck.T (FutureSafe Stuck.T Stuck.P 0) ∧
          ∀ s, FutureSafe Stuck.T Stuck.P 0 s → Stuck.P s) := by
  refine ⟨(step_one_iff.mpr (fun _ _ _ h => h.elim)).simpleStep, fun ⟨hi, _, hP⟩ => ?_⟩
  exact hP ⟨0, by decide⟩ (hi ⟨0, by decide⟩ trivial)

/-- Dropping `SimpleStep (k+1)` (with `k = 0`): in `OneEdge`, `Base 1` holds but the conclusion fails
(consecution of `FutureSafe T P 0`, which is `P`, fails along `0 → 1`). -/
theorem futureSafe_strengthening_needs_step :
    Base OneEdge.I OneEdge.T OneEdge.P 1 ∧
      ¬ (Initiation OneEdge.I (FutureSafe OneEdge.T OneEdge.P 0) ∧
          Consecution OneEdge.T (FutureSafe OneEdge.T OneEdge.P 0) ∧
          ∀ s, FutureSafe OneEdge.T OneEdge.P 0 s → OneEdge.P s) := by
  refine ⟨?_, fun ⟨hi, hc, hP⟩ => ?_⟩
  · rw [base_iff_reachIn]
    intro j hj s hs
    have : j = 0 := by omega
    subst this
    exact reachIn_zero_iff.mp hs
  · have h0 := hi ⟨0, by decide⟩ rfl
    have h1 := hc _ ⟨1, by decide⟩ h0 (by decide)
    exact absurd (hP _ h1) (by decide)

/-- In `TwoInd` (where `P` is 2-inductive but not 1-inductive), the strengthening
`FutureSafe T P 1` is exactly the state `0`: it excludes the unreachable state `1`, whose
successor violates `P`. -/
theorem twoInd_futureSafe_one_iff (s : Fin 3) :
    FutureSafe TwoInd.T TwoInd.P 1 s ↔ s.val = 0 := by
  constructor
  · intro h
    have h0 := h 0 (by decide) (fun _ => s) rfl (fun i hi => absurd hi (Nat.not_lt_zero _))
    have h1 : ∀ t, TwoInd.T s t → TwoInd.P t := fun t hst =>
      h 1 (Nat.le_refl 1) (fun i => if i = 0 then s else t) rfl
        (by intro i hi; have : i = 0 := by omega
            subst this; simpa using hst)
    clear h
    revert h0 h1
    revert s
    decide
  · intro hs j hj π h0 hp
    have hπ : ∀ i, i ≤ j → (π i).val = 0 := by
      intro i
      induction i with
      | zero => intro _; rw [h0]; exact hs
      | succ i ih =>
        intro hi
        have := hp i (by omega)
        have := ih (by omega)
        simp only [TwoInd.T] at *
        omega
    simp only [TwoInd.P]
    have := hπ j (Nat.le_refl j)
    omega

/-- `FutureSafe Branch4.T Branch4.P 1` is exactly the initial state `0`. -/
theorem branch4_futureSafe_one_iff (s : Fin 4) :
    FutureSafe Branch4.T Branch4.P 1 s ↔ s.val = 0 := by
  constructor
  · intro h
    have h0 := h 0 (by decide) (fun _ => s) rfl (fun i hi => absurd hi (Nat.not_lt_zero _))
    have h1 : ∀ t, Branch4.T s t → Branch4.P t := fun t hst =>
      h 1 (Nat.le_refl 1) (fun i => if i = 0 then s else t) rfl
        (by
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          simpa using hst)
    clear h
    revert h0 h1 s
    decide
  · intro hs j hj π h0 hp
    have hπ : ∀ i, i ≤ j → (π i).val = 0 := by
      intro i
      induction i with
      | zero => intro _; rw [h0]; exact hs
      | succ i ih =>
        intro hi
        have := hp i (by omega)
        have := ih (by omega)
        simp only [Branch4.T] at *
        omega
    simp only [Branch4.P]
    have := hπ j (Nat.le_refl j)
    omega

/-- **The converse of `simple_kinductive_futureSafe_strengthening` fails.** In `Branch4`,
`FutureSafe T P 1` is a 1-inductive strengthening of `P`, but `SimpleStep 2` fails (on the simple
path `1 → 2 → 3`). -/
theorem branch4_futureSafe_inductive_without_simpleStep :
    ¬ SimpleStep Branch4.T Branch4.P 2 ∧
      Initiation Branch4.I (FutureSafe Branch4.T Branch4.P 1) ∧
      Consecution Branch4.T (FutureSafe Branch4.T Branch4.P 1) ∧
      ∀ s, FutureSafe Branch4.T Branch4.P 1 s → Branch4.P s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [simpleStep_two_iff]
    decide
  · intro s hs
    exact (branch4_futureSafe_one_iff s).mpr hs
  · intro s t hs hst
    have h0 := (branch4_futureSafe_one_iff s).mp hs
    apply (branch4_futureSafe_one_iff t).mpr
    simp only [Branch4.T] at hst
    omega
  · intro s hs
    have h0 := (branch4_futureSafe_one_iff s).mp hs
    simp only [Branch4.P]
    omega

end Toy.KInd
