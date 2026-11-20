import ToyFuelWP.Divergence

/-!
# How much classical logic the main results need (fully proved)

The main results are stated in Lean's logic, which includes classical
axioms. This module records, by proofs that use no classical axiom, which
statements *cannot* be proved constructively:

* the finite-branching completeness statements for total correctness imply
  the limited principle of omniscience (`LimitedPrincipleOfOmniscience`);
* "total correctness = partial correctness + no infinite run" implies
  Markov's principle (`MarkovPrinciple`); its forward direction alone is
  provable with no axioms (`wpGfp_and_not_hasInfiniteRun_of_wpLfp`);
* a disjunctive form of greatest-fixpoint adequacy implies excluded middle.

Neither principle is derivable in constructive (intuitionistic) mathematics:
Kripke models refute both (D. Bridges, E. Palmgren and H. Ishihara,
"Constructive Mathematics", Stanford Encyclopedia of Philosophy, substantive
revision of 25 August 2022: section 1 for LPO and section 2 for Markov's
principle, citing Bridges and Richman 1987). So the statements above cannot be proved by
constructive reasoning alone, while the reductions themselves use no
classical axiom. Each reduction takes the statement of a
main result as a hypothesis `H`, so nothing here depends on how the main
results are proved. By contrast, for deterministic systems with decidable
terminal states, finite-branching completeness is provable with no axioms at
all (`exists_wpFuelTotal_of_wpLfp_of_deterministic_of_decidable_terminal`).

This module does not import `ToyFuelWP.Statements`.
-/

namespace Toy.FuelWP

universe u

/-- The limited principle of omniscience: every Boolean sequence either has a
`true` entry or is constantly `false`. -/
def LimitedPrincipleOfOmniscience : Prop :=
  ∀ B : Nat → Bool, (∃ k, B k = true) ∨ ∀ k, B k = false

/-- Markov's principle: a Boolean sequence that is not constantly `false` has
a `true` entry. -/
def MarkovPrinciple : Prop :=
  ∀ B : Nat → Bool, ¬ (∀ k, B k = false) → ∃ k, B k = true

/-! ## Bounded search -/

/-- `findTrue B n` checks whether `B k = true` for some `k < n`. -/
def findTrue (B : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 =>
    match B n with
    | true => true
    | false => findTrue B n

theorem findTrue_true_iff (B : Nat → Bool) (n : Nat) :
    findTrue B n = true ↔ ∃ k, k < n ∧ B k = true := by
  induction n with
  | zero => exact ⟨fun h => (nomatch h), fun ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    constructor
    · intro h
      cases hbn : B n with
      | true => exact ⟨n, Nat.lt_succ_self n, hbn⟩
      | false =>
        have h' : findTrue B n = true := by dsimp [findTrue] at h; rw [hbn] at h; exact h
        obtain ⟨k, hk, hbk⟩ := ih.mp h'
        exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n), hbk⟩
    · rintro ⟨k, hk, hbk⟩
      dsimp [findTrue]
      cases hbn : B n with
      | true => rfl
      | false =>
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
        | inl hlt => exact ih.mpr ⟨k, hlt, hbk⟩
        | inr heq =>
          subst heq
          rw [hbn] at hbk
          exact nomatch hbk

/-! ## The limited principle of omniscience from finite-branching completeness -/

/-- States of the search system used for the reduction. -/
inductive LPOState where
  /-- Initial state: either halt immediately or start searching. -/
  | start
  /-- Halted. -/
  | done
  /-- Searching at index `k`. -/
  | search (k : Nat)

/-- The search system for a Boolean sequence `B`: `start` steps to `done`,
and to `search 0` exactly when `B` has a `true` entry; `search k` steps to
`search (k + 1)` and is terminal exactly when `B k = true`. It is finitely
branching (at most two successors, listed as `[done, search 0]`), but whether
`search 0` is really a successor of `start` is undecidable in general. -/
def lpoSys (B : Nat → Bool) : System LPOState where
  step s t :=
    match s, t with
    | .start, .done => True
    | .start, .search 0 => ∃ k, B k = true
    | .search k, .search j => j = k + 1
    | _, _ => False
  terminal s :=
    match s with
    | .done => True
    | .search k => B k = true
    | .start => False

theorem lpoSys_finitelyBranching (B : Nat → Bool) : FinitelyBranching (lpoSys B) := by
  intro s _
  cases s with
  | start =>
    refine ⟨[.done, .search 0], fun u hu => ?_⟩
    cases u with
    | start => exact hu.elim
    | done => exact List.Mem.head _
    | search k =>
      cases k with
      | zero => exact List.Mem.tail _ (List.Mem.head _)
      | succ _ => exact hu.elim
  | done => exact ⟨[], fun u hu => hu.elim⟩
  | search k =>
    refine ⟨[.search (k + 1)], fun u hu => ?_⟩
    cases u with
    | start => exact hu.elim
    | done => exact hu.elim
    | search j =>
      have hj : j = k + 1 := hu
      subst hj
      exact List.Mem.head _

theorem lpoSys_wpLfp_search_of_witness (B : Nat → Bool) {k : Nat} (hk : B k = true) :
    ∀ d, d ≤ k → wpLfp (lpoSys B) (fun _ => True) (.search (k - d)) := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [Nat.sub_zero]
    exact wpLfp_preFixed _ _ _ ⟨fun _ => trivial, fun hnt => absurd hk hnt⟩
  | succ d ih =>
    intro hdk
    have ih' := ih (Nat.le_of_succ_le hdk)
    cases h : B (k - (d + 1)) with
    | true =>
      exact wpLfp_preFixed _ _ _ ⟨fun _ => trivial, fun hnt => absurd h hnt⟩
    | false =>
      have hsucc : k - (d + 1) + 1 = k - d := by
        have hpos : 1 ≤ k - d := Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hdk)
        rw [Nat.sub_succ]
        cases hkd : k - d with
        | zero => rw [hkd] at hpos; exact absurd hpos (Nat.not_succ_le_zero 0)
        | succ _ => rfl
      apply wpLfp_preFixed
      refine ⟨fun _ => trivial, fun _ => ⟨⟨.search (k - (d + 1) + 1), rfl⟩, fun u hu => ?_⟩⟩
      cases u with
      | start => exact hu.elim
      | done => exact hu.elim
      | search j =>
        have hj : j = k - (d + 1) + 1 := hu
        rw [hj, hsucc]
        exact ih'

theorem lpoSys_wpLfp_start (B : Nat → Bool) : wpLfp (lpoSys B) (fun _ => True) .start := by
  apply wpLfp_preFixed
  refine ⟨fun _ => trivial, fun _ => ⟨⟨.done, trivial⟩, fun u hu => ?_⟩⟩
  cases u with
  | start => exact hu.elim
  | done => exact wpLfp_preFixed _ _ _ ⟨fun _ => trivial, fun hnt => absurd trivial hnt⟩
  | search k =>
    cases k with
    | zero =>
      obtain ⟨m, hm⟩ := hu
      have h0 := lpoSys_wpLfp_search_of_witness B hm m (Nat.le_refl m)
      rw [Nat.sub_self] at h0
      exact h0
    | succ _ => exact hu.elim

theorem lpoSys_wpFuelTotal_search_bound (B : Nat → Bool) :
    ∀ (m j : Nat), wpFuelTotal (lpoSys B) m (fun _ => True) (.search j) →
      ∃ k, j ≤ k ∧ k < j + m ∧ B k = true := by
  intro m
  induction m with
  | zero => intro _ h; exact h.elim
  | succ m ih =>
    intro j h
    cases hb : B j with
    | true => exact ⟨j, Nat.le_refl j, Nat.lt_add_of_pos_right (Nat.succ_pos m), hb⟩
    | false =>
      have hnt : ¬ (lpoSys B).terminal (.search j) := fun ht => by
        have ht' : B j = true := ht
        rw [hb] at ht'
        exact nomatch ht'
      have hstep : wpFuelTotal (lpoSys B) m (fun _ => True) (.search (j + 1)) :=
        (h.2 hnt).2 (.search (j + 1)) rfl
      obtain ⟨k, hjk, hkm, hbk⟩ := ih (j + 1) hstep
      refine ⟨k, Nat.le_trans (Nat.le_succ j) hjk, ?_, hbk⟩
      rw [Nat.add_succ, ← Nat.succ_add]
      exact hkm

/-- A fuel bound for `start` in the search system decides the sequence. -/
theorem lpo_of_lpoSys_fuel_bound (B : Nat → Bool) (n : Nat)
    (hn : wpFuelTotal (lpoSys B) n (fun _ => True) .start) :
    (∃ k, B k = true) ∨ ∀ k, B k = false := by
  cases hf : findTrue B n with
  | true =>
    obtain ⟨k, _, hbk⟩ := (findTrue_true_iff B n).mp hf
    exact Or.inl ⟨k, hbk⟩
  | false =>
    apply Or.inr
    intro k
    cases hbk : B k with
    | false => rfl
    | true =>
      cases n with
      | zero => exact hn.elim
      | succ n =>
        have hs0 : wpFuelTotal (lpoSys B) n (fun _ => True) (.search 0) :=
          (hn.2 (fun h => h)).2 (.search 0) ⟨k, hbk⟩
        obtain ⟨j, _, hjn, hbj⟩ := lpoSys_wpFuelTotal_search_bound B n 0 hs0
        rw [Nat.zero_add] at hjn
        have hft : findTrue B (n + 1) = true :=
          (findTrue_true_iff B (n + 1)).mpr ⟨j, Nat.lt_trans hjn (Nat.lt_succ_self n), hbj⟩
        rw [hf] at hft
        exact nomatch hft

/-- **Local finite-branching completeness implies LPO.** The statement of
`exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom` (for systems on types
in `Type`) implies the limited principle of omniscience. The reduction uses no
classical axiom; so that statement is not provable constructively. -/
theorem lpo_of_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom
    (H : ∀ {σ : Type} (S : System σ) (Q : σ → Prop) (s : σ),
      FinitelyBranchingFrom S s → wpLfp S Q s → ∃ n, wpFuelTotal S n Q s) :
    LimitedPrincipleOfOmniscience := by
  intro B
  obtain ⟨n, hn⟩ := H (lpoSys B) (fun _ => True) .start
    (finitelyBranchingFrom_of_finitelyBranching (lpoSys_finitelyBranching B) .start)
    (lpoSys_wpLfp_start B)
  exact lpo_of_lpoSys_fuel_bound B n hn

/-- **Global finite-branching completeness implies LPO.** -/
theorem lpo_of_exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching
    (H : ∀ {σ : Type} (S : System σ) (Q : σ → Prop),
      FinitelyBranching S → ∀ s, (∃ n, wpFuelTotal S n Q s) ↔ wpLfp S Q s) :
    LimitedPrincipleOfOmniscience := by
  intro B
  obtain ⟨n, hn⟩ := (H (lpoSys B) (fun _ => True) (lpoSys_finitelyBranching B) .start).mpr
    (lpoSys_wpLfp_start B)
  exact lpo_of_lpoSys_fuel_bound B n hn

/-- **The König form implies LPO.** The statement of
`exists_wpFuelTotal_of_wpGfp_of_not_hasInfiniteRun_of_finitelyBranchingFrom`
implies the limited principle of omniscience, without classical axioms. -/
theorem lpo_of_koenig_form
    (H : ∀ {σ : Type} (S : System σ) (Q : σ → Prop) (s : σ),
      FinitelyBranchingFrom S s → wpGfp S Q s → ¬ HasInfiniteRun S s →
        ∃ n, wpFuelTotal S n Q s) :
    LimitedPrincipleOfOmniscience := by
  apply lpo_of_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom
  intro σ S Q s hfb hlfp
  exact H S Q s hfb ⟨wpLfp S Q, fun t ht => (wpLfp_unfold S Q t).mp ht, hlfp⟩
    (fun hr => not_wpLfp_of_hasInfiniteRun hr Q hlfp)

/-! ## Markov's principle from "total = partial + termination" -/

/-- Deterministic search chain: `k` steps to `k + 1` and is terminal exactly
when `B k = true`. Step and terminal predicates are decidable. -/
def markovSys (B : Nat → Bool) : System Nat where
  step k j := j = k + 1
  terminal k := B k = true

theorem markovSys_wpGfp (B : Nat → Bool) : wpGfp (markovSys B) (fun _ => True) 0 :=
  ⟨fun _ => True, fun k _ => ⟨fun _ => trivial, fun _ => ⟨⟨k + 1, rfl⟩, fun _ _ => trivial⟩⟩,
    trivial⟩

theorem markovSys_not_hasInfiniteRun_of_not_all_false (B : Nat → Bool)
    (h : ¬ ∀ i, B i = false) : ¬ HasInfiniteRun (markovSys B) 0 := by
  rintro ⟨f, hf0, hf⟩
  have hfi : ∀ i, f i = i := by
    intro i
    induction i with
    | zero => exact hf0
    | succ i ih =>
      have hs : f (i + 1) = f i + 1 := (hf i).2
      rw [hs, ih]
  apply h
  intro i
  cases hb : B i with
  | false => rfl
  | true =>
    have hnt : ¬ B (f i) = true := (hf i).1
    rw [hfi i] at hnt
    exact absurd hb hnt

/-- **"Total = partial + termination" implies Markov's principle.** The
statement of `wpLfp_iff_wpGfp_and_not_hasInfiniteRun` (for systems on types in
`Type`) implies Markov's principle, even restricted to the deterministic
system `markovSys B` with decidable step and terminal predicates. The
reduction uses no axioms. -/
theorem markov_of_wpLfp_iff_wpGfp_and_not_hasInfiniteRun
    (H : ∀ {σ : Type} (S : System σ) (Q : σ → Prop) (s : σ),
      wpLfp S Q s ↔ wpGfp S Q s ∧ ¬ HasInfiniteRun S s) :
    MarkovPrinciple := by
  intro B hnotall
  have hlfp : wpLfp (markovSys B) (fun _ => True) 0 :=
    (H (markovSys B) (fun _ => True) 0).mpr
      ⟨markovSys_wpGfp B, markovSys_not_hasInfiniteRun_of_not_all_false B hnotall⟩
  have hpre : PreFixed (markovSys B) (fun _ => True) (fun k => ∃ m, k ≤ m ∧ B m = true) := by
    intro k hk
    cases hb : B k with
    | true => exact ⟨k, Nat.le_refl k, hb⟩
    | false =>
      have hnt : ¬ (markovSys B).terminal k := fun ht => by
        have ht' : B k = true := ht
        rw [hb] at ht'
        exact nomatch ht'
      obtain ⟨m, hkm, hbm⟩ := (hk.2 hnt).2 (k + 1) rfl
      exact ⟨m, Nat.le_trans (Nat.le_succ k) hkm, hbm⟩
  obtain ⟨m, _, hbm⟩ := wpLfp_induction hpre hlfp
  exact ⟨m, hbm⟩

/-- **The forward direction of "total = partial + termination" is
constructive.** For every system, `wpLfp S Q s` implies `wpGfp S Q s` and the
absence of an infinite run from `s`, with no axioms. (Only the backward
direction implies Markov's principle,
`markov_of_wpLfp_iff_wpGfp_and_not_hasInfiniteRun`.) -/
theorem wpGfp_and_not_hasInfiniteRun_of_wpLfp {σ : Type u} (S : System σ) (Q : σ → Prop)
    (s : σ) (h : wpLfp S Q s) : wpGfp S Q s ∧ ¬ HasInfiniteRun S s :=
  ⟨⟨wpLfp S Q, fun t ht => (wpLfp_unfold S Q t).mp ht, h⟩,
    fun hinf => not_wpLfp_of_hasInfiniteRun hinf Q h⟩

/-! ## Excluded middle from disjunctive adequacy -/

/-- **Disjunctive adequacy implies excluded middle.** If, for every one-state
system, `wpGfp` implied that every run prefix ends *either* in a terminal
state satisfying `Q` *or* in a non-terminal state with a successor, then every
proposition would be decided. This is why `RunEndOk` and `wpStep` are written
with implications. No axioms. -/
theorem em_of_disjunctive_adequacy
    (H : ∀ (S : System Unit) (Q : Unit → Prop) (s : Unit), wpGfp S Q s →
      ∀ k t, Reach S s k t → (S.terminal t ∧ Q t) ∨ (¬ S.terminal t ∧ CanStep S t)) :
    ∀ P : Prop, P ∨ ¬ P := by
  intro P
  let S : System Unit := { step := fun _ _ => True, terminal := fun _ => P }
  have hg : wpGfp S (fun _ => True) () :=
    ⟨fun _ => True, fun _ _ => ⟨fun _ => trivial, fun _ => ⟨⟨(), trivial⟩, fun _ _ => trivial⟩⟩,
      trivial⟩
  rcases H S (fun _ => True) () hg 0 () (Reach.refl ()) with ⟨hp, _⟩ | ⟨hnp, _⟩
  · exact Or.inl hp
  · exact Or.inr hnp

/-! ## The constructive special case -/

/-- **Deterministic systems with decidable terminal states need no classical
logic.** For a deterministic system in which every state is decidably
terminal or not, total correctness implies a fuel bound, with no axioms. -/
theorem exists_wpFuelTotal_of_wpLfp_of_deterministic_of_decidable_terminal {σ : Type u}
    (S : System σ) (Q : σ → Prop) (hdet : Deterministic S)
    (hdec : ∀ t, S.terminal t ∨ ¬ S.terminal t) (s : σ) (h : wpLfp S Q s) :
    ∃ n, wpFuelTotal S n Q s := by
  have key : PreFixed S Q (fun t => ∃ n, wpFuelTotal S n Q t) := by
    intro t ht
    cases hdec t with
    | inl hterm => exact ⟨1, fun _ => ht.1 hterm, fun hnt => absurd hterm hnt⟩
    | inr hnt =>
      obtain ⟨u, htu⟩ := (ht.2 hnt).1
      obtain ⟨n, hn⟩ := (ht.2 hnt).2 u htu
      refine ⟨n + 1, fun hterm => absurd hterm hnt, fun _ => ⟨⟨u, htu⟩, fun v htv => ?_⟩⟩
      rw [hdet t hnt v u htv htu]
      exact hn
  exact wpLfp_induction key h

end Toy.FuelWP
