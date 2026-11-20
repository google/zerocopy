import ToyPredTrans.Basic

/-!
# Main results

This file contains the main results on the correspondence between healthiness laws of
predicate transformers and relational semantics, with their proofs.

No example, counterexample, non-vacuity theorem or positive control in this project imports
this file; they are established independently in `Programs`, `Witnesses`, `Algebra`,
`MonotoneNormalForm` and `SmallStateSpaces`.  Consequences of the results below are
collected in `Corollaries`.

Axiom footprints: the five statements about `wlp`, `wp` and `relOf` use only `propext` and
`Quot.sound` (no `Classical.choice`); `refinedBy_wp_iff` uses no axioms.
`strict_wp_iff_totalOn` uses classical logic, which it implies; the proof of
`omegaContinuous_wp_iff_finiteImage_on_term` uses choice, and its backward direction implies
the limited principle of omniscience (see `Witnesses`).
-/

namespace Toy.PredTrans

universe u

variable {σ : Type u}

/-! ## Characterization of `wlp` by universal conjunctivity -/

/-- **Universally conjunctive transformers are exactly the `wlp`s, with the relation exposed.**
A transformer distributes over the conjunction of every family of postconditions (including
the empty family) if and only if it equals the `wlp` of the relation `relOf T` read off from
it, where `relOf T s s' ↔ ∀ Q, T Q s → Q s'` (`s'` satisfies every postcondition `T`
establishes from `s`). -/
theorem conjAll_iff_eq_wlp_relOf (T : Transformer σ) : ConjAll T ↔ T = wlp (relOf T) := by
  constructor
  · intro h
    apply trans_ext
    intro Q s
    constructor
    · intro hTQ s' hr
      exact hr Q hTQ
    · intro himp
      have hset := (conjAll_iff_set T).mp h (fun P => T P s) s
      have hK : T (fun t => ∀ P, T P s → P t) s := hset.mpr fun _ hp => hp
      exact monotone_of_conjNonempty (conjNonempty_of_conjAll h) _ Q himp s hK
  · intro h
    rw [h]
    exact conjAll_wlp _

/-- **The relation is recovered from its `wlp`.**  `relOf` is a left inverse of `wlp`; in
particular `wlp` is injective, so the relation representing a universally conjunctive
transformer is unique. -/
theorem relOf_wlp (R : Rel σ) : relOf (wlp R) = R := by
  apply rel_ext
  intro s s'
  constructor
  · intro h
    exact h (R s) (fun _ hr => hr)
  · intro hr Q hQ
    exact hQ s' hr

/-! ## Characterization of `wp` by positive conjunctivity -/

/-- **Positively conjunctive transformers are exactly the `wp`s, with relation and termination
predicate exposed.**  A transformer distributes over the conjunction of every *nonempty*
family of postconditions if and only if it equals `wp (relOf T) (termOf T)`, where
`termOf T = T (fun _ => True)`. -/
theorem conjNonempty_iff_eq_wp_relOf_termOf (T : Transformer σ) :
    ConjNonempty T ↔ T = wp (relOf T) (termOf T) := by
  constructor
  · intro h
    apply trans_ext
    intro Q s
    constructor
    · intro hTQ
      exact ⟨monotone_of_conjNonempty h Q (fun _ => True) (fun _ _ => trivial) s hTQ,
        fun s' hr => hr Q hTQ⟩
    · intro hh
      obtain ⟨htop, himp⟩ := hh
      have hset := (conjNonempty_iff_set T).mp h (fun P => T P s) ⟨fun _ => True, htop⟩ s
      have hK : T (fun t => ∀ P, T P s → P t) s := hset.mpr fun _ hp => hp
      exact monotone_of_conjNonempty h _ Q himp s hK
  · intro h
    rw [h]
    exact conjNonempty_wp _ _

/-- **What `relOf` recovers from a `wp`.**  The relation read off from `wp R term` is the chaos
normal form of `R`: it agrees with `R` on non-aborting start states and relates every aborting
start state to every state. -/
theorem relOf_wp (R : Rel σ) (term : Pred σ) :
    relOf (wp R term) = fun s s' => term s → R s s' := by
  apply rel_ext
  intro s s'
  constructor
  · intro h ht
    exact h (R s) ⟨ht, fun _ hr => hr⟩
  · intro h Q hQ
    exact hQ.2 s' (h hQ.1)

/-- **Uniqueness of the relational representation of a `wp`.**  Two relational programs have
the same `wp` if and only if they have the same non-abortion predicate and their relations
agree on non-aborting start states.  Nothing is determined about the relations outside the
non-abortion predicate. -/
theorem wp_eq_wp_iff (R R' : Rel σ) (term term' : Pred σ) :
    wp R term = wp R' term' ↔ term = term' ∧ ∀ s, term s → ∀ s', (R s s' ↔ R' s s') := by
  constructor
  · intro h
    have ht : term = term' := by
      have := congrArg termOf h
      rwa [termOf_wp, termOf_wp] at this
    refine ⟨ht, fun s hs s' => ⟨fun hr => ?_, fun hr' => ?_⟩⟩
    · have h1 : wp R' term' (R' s) s := ⟨ht ▸ hs, fun _ h' => h'⟩
      have h2 : wp R term (R' s) s := (congrFun (congrFun h (R' s)) s).mpr h1
      exact h2.2 s' hr
    · have h1 : wp R term (R s) s := ⟨hs, fun _ h' => h'⟩
      have h2 : wp R' term' (R s) s := (congrFun (congrFun h (R s)) s).mp h1
      exact h2.2 s' hr'
  · intro hh
    obtain ⟨ht, hR⟩ := hh
    subst ht
    apply trans_ext
    intro Q s
    constructor
    · intro hw
      exact ⟨hw.1, fun s' hr => hw.2 s' ((hR s hw.1 s').mpr hr)⟩
    · intro hw
      exact ⟨hw.1, fun s' hr => hw.2 s' ((hR s hw.1 s').mp hr)⟩

/-! ## Strictness and miracles -/

/-- **Strictness of a `wp` is absence of miracles.**  `wp R term` satisfies the law of the
excluded miracle if and only if every non-aborting start state has at least one
`R`-successor. -/
theorem strict_wp_iff_totalOn (R : Rel σ) (term : Pred σ) :
    Strict (wp R term) ↔ TotalOn R term := by
  constructor
  · intro h s hs
    apply Classical.byContradiction
    intro hne
    exact h s ⟨hs, fun s' hr => hne ⟨s', hr⟩⟩
  · intro h s hw
    obtain ⟨s', hr⟩ := h s hw.1
    exact hw.2 s' hr

/-! ## Continuity and bounded nondeterminism -/

/-- Auxiliary: for an increasing chain of predicates `Q`, if every point of a list that
satisfies `A` satisfies some member of the chain, then all such points satisfy one common
member of the chain. -/
theorem list_chain_bound {Q : Nat → Pred σ} (hQ : Chain Q) (A : σ → Prop) (l : List σ)
    (h : ∀ x, x ∈ l → A x → ∃ n, Q n x) : ∃ N, ∀ x, x ∈ l → A x → Q N x := by
  induction l with
  | nil => exact ⟨0, fun x hx => (by cases hx)⟩
  | cons a l ih =>
    obtain ⟨N, hN⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases ha : A a
    · obtain ⟨n, hn⟩ := h a List.mem_cons_self ha
      refine ⟨N + n, fun x hx hAx => ?_⟩
      rcases List.mem_cons.mp hx with e | hx'
      · rw [e]
        exact hQ.mono (Nat.le_add_left n N) _ hn
      · exact hQ.mono (Nat.le_add_right N n) _ (hN x hx' hAx)
    · refine ⟨N, fun x hx hAx => ?_⟩
      rcases List.mem_cons.mp hx with e | hx'
      · rw [e] at hAx
        exact absurd hAx ha
      · exact hN x hx' hAx

/-- **ω-continuity of a `wp` is bounded nondeterminism.**  `wp R term` is ω-continuous if and
only if every non-aborting start state has a finite `R`-image (all successors contained in one
list).  No hypothesis on the state type is needed. -/
theorem omegaContinuous_wp_iff_finiteImage_on_term (R : Rel σ) (term : Pred σ) :
    OmegaContinuous (wp R term) ↔ ∀ s, term s → FiniteImage R s := by
  constructor
  · intro h s hs
    apply Classical.byContradiction
    intro hfin
    have hex : ∀ l : List σ, ∃ s', R s s' ∧ ¬ s' ∈ l := by
      intro l
      apply Classical.byContradiction
      intro hne
      apply hfin
      refine ⟨l, fun s' hr => ?_⟩
      apply Classical.byContradiction
      intro hnm
      exact hne ⟨s', hr, hnm⟩
    let f : List σ → σ := fun l => Classical.choose (hex l)
    have hf : ∀ l, R s (f l) ∧ ¬ f l ∈ l := fun l => Classical.choose_spec (hex l)
    let xs : Nat → List σ := fun n => Nat.rec [] (fun _ acc => f acc :: acc) n
    have hxs_succ : ∀ n, xs (n + 1) = f (xs n) :: xs n := fun n => rfl
    have hmem : ∀ n k, k < n → f (xs k) ∈ xs n := by
      intro n
      induction n with
      | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
      | succ n ih =>
        intro k hk
        rw [hxs_succ]
        by_cases hkn : k = n
        · rw [hkn]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih k (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkn))
    have hinj : ∀ k n, k < n → f (xs n) ≠ f (xs k) := by
      intro k n hkn heq
      apply (hf (xs n)).2
      rw [heq]
      exact hmem n k hkn
    have hQ : Chain (fun (n : Nat) (t : σ) => ∀ k, n ≤ k → t ≠ f (xs k)) :=
      fun n t ht k hk => ht k (Nat.le_of_succ_le hk)
    have hunion : ∀ t, ∃ n, ∀ k, n ≤ k → t ≠ f (xs k) := by
      intro t
      by_cases ht : ∃ k, t = f (xs k)
      · obtain ⟨k, hk⟩ := ht
        refine ⟨k + 1, fun j hj heq => ?_⟩
        rw [hk] at heq
        exact hinj k j hj heq.symm
      · exact ⟨0, fun k _ heq => ht ⟨k, heq⟩⟩
    obtain ⟨n, hn⟩ := h _ hQ s ⟨hs, fun s' _ => hunion s'⟩
    exact hn.2 (f (xs n)) (hf (xs n)).1 n (Nat.le_refl n) rfl
  · intro h Q hQ s hw
    obtain ⟨l, hl⟩ := h s hw.1
    obtain ⟨N, hN⟩ := list_chain_bound hQ (R s) l (fun x _ hr => hw.2 x hr)
    exact ⟨N, hw.1, fun s' hr => hN s' (hl s' hr) hr⟩

/-! ## Refinement -/

/-- **Refinement of `wp`s, relationally.**  `wp R₁ t₁` is refined by `wp R₂ t₂` if and only if
the second program does not abort wherever the first does not, and on the non-aborting start
states of the first program every outcome of the second is an outcome of the first.  No
normal form is assumed; the comparison of relations is restricted to `t₁`-states. -/
theorem refinedBy_wp_iff (R₁ R₂ : Rel σ) (t₁ t₂ : Pred σ) :
    RefinedBy (wp R₁ t₁) (wp R₂ t₂) ↔
      (∀ s, t₁ s → t₂ s) ∧ (∀ s, t₁ s → ∀ s', R₂ s s' → R₁ s s') := by
  constructor
  · intro h
    refine ⟨fun s hs => (h (fun _ => True) s ⟨hs, fun _ _ => trivial⟩).1, ?_⟩
    intro s hs s' hR
    exact (h (R₁ s) s ⟨hs, fun _ hr => hr⟩).2 s' hR
  · intro hh Q s hw
    exact ⟨hh.1 s hw.1, fun s' hr => hw.2 s' (hh.2 s hw.1 s' hr)⟩

end Toy.PredTrans
