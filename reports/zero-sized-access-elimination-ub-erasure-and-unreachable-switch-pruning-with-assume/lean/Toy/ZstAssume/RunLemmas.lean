import Toy.ZstAssume.Transforms

/-!
# Basic facts about `run` and behaviours

Fully proved helper lemmas used by the definition examples, counterexamples,
non-vacuity theorems and positive controls.
-/

namespace Toy.ZstAssume

theorem run_zero (K : ZContract) (P : Prog) (c : Cfg) : run K P 0 c = .running c [] := rfl

theorem run_succ_next {K : ZContract} {P : Prog} {c c' : Cfg} {o : Option Int} (n : Nat)
    (h : step K P c = .next o c') : run K P (n + 1) c = (run K P n c').cons o := by
  simp [run, h]

theorem run_succ_halt {K : ZContract} {P : Prog} {c : Cfg} {s : State} (n : Nat)
    (h : step K P c = .halt s) : run K P (n + 1) c = .done [] s := by
  simp [run, h]

theorem run_succ_ub {K : ZContract} {P : Prog} {c : Cfg} (n : Nat)
    (h : step K P c = .ub) : run K P (n + 1) c = .ub [] := by
  simp [run, h]

/-- Termination is stable under more fuel. -/
theorem run_done_add {K : ZContract} {P : Prog} :
    ∀ (n k : Nat) (c : Cfg) (t : List Int) (s : State),
      run K P n c = .done t s → run K P (n + k) c = .done t s
  | 0, _, _, _, _, h => by simp [run] at h
  | n + 1, k, c, t, s, h => by
    rw [Nat.add_right_comm]
    cases hs : step K P c with
    | next o c' =>
      rw [run_succ_next _ hs] at h ⊢
      cases hr : run K P n c' with
      | done t' s' =>
        rw [run_done_add n k c' t' s' hr]
        rw [hr] at h
        exact h
      | ub t' => rw [hr] at h; simp [Outcome.cons] at h
      | running c'' t' => rw [hr] at h; simp [Outcome.cons] at h
    | halt s' => rw [run_succ_halt _ hs] at h ⊢; exact h
    | ub => rw [run_succ_ub _ hs] at h; simp at h

/-- UB is stable under more fuel. -/
theorem run_ub_add {K : ZContract} {P : Prog} :
    ∀ (n k : Nat) (c : Cfg) (t : List Int),
      run K P n c = .ub t → run K P (n + k) c = .ub t
  | 0, _, _, _, h => by simp [run] at h
  | n + 1, k, c, t, h => by
    rw [Nat.add_right_comm]
    cases hs : step K P c with
    | next o c' =>
      rw [run_succ_next _ hs] at h ⊢
      cases hr : run K P n c' with
      | done t' s' => rw [hr] at h; simp [Outcome.cons] at h
      | ub t' =>
        rw [run_ub_add n k c' t' hr]
        rw [hr] at h
        exact h
      | running c'' t' => rw [hr] at h; simp [Outcome.cons] at h
    | halt s' => rw [run_succ_halt _ hs] at h; simp at h
    | ub => rw [run_succ_ub _ hs] at h ⊢; exact h

theorem run_done_mono {K : ZContract} {P : Prog} {n m : Nat} {c : Cfg} {t : List Int}
    {s : State} (h : run K P n c = .done t s) (hnm : n ≤ m) : run K P m c = .done t s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact run_done_add n k c t s h

theorem run_ub_mono {K : ZContract} {P : Prog} {n m : Nat} {c : Cfg} {t : List Int}
    (h : run K P n c = .ub t) (hnm : n ≤ m) : run K P m c = .ub t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact run_ub_add n k c t h

/-- A terminating run determines the behaviour. -/
theorem hasBehFrom_iff_of_run_done {K : ZContract} {P : Prog} {c : Cfg} {n : Nat}
    {t : List Int} {s : State} (h : run K P n c = .done t s) (b : Beh) :
    HasBehFrom K P c b ↔ b = .term t := by
  constructor
  · intro hb
    cases b with
    | term t' =>
      obtain ⟨m, s', hm⟩ := hb
      have e₁ := run_done_mono h (Nat.le_max_left n m)
      have e₂ := run_done_mono hm (Nat.le_max_right n m)
      rw [e₁] at e₂
      cases e₂
      rfl
    | wrong t' =>
      obtain ⟨m, hm⟩ := hb
      have e₁ := run_done_mono h (Nat.le_max_left n m)
      have e₂ := run_ub_mono hm (Nat.le_max_right n m)
      rw [e₁] at e₂
      cases e₂
    | div t' =>
      have := hb.1 n
      rw [h] at this
      simp [Outcome.isRunning] at this
    | react f =>
      have := hb.1 n
      rw [h] at this
      simp [Outcome.isRunning] at this
  · rintro rfl
    exact ⟨n, s, h⟩

/-- A run reaching UB determines the behaviour. -/
theorem hasBehFrom_iff_of_run_ub {K : ZContract} {P : Prog} {c : Cfg} {n : Nat}
    {t : List Int} (h : run K P n c = .ub t) (b : Beh) :
    HasBehFrom K P c b ↔ b = .wrong t := by
  constructor
  · intro hb
    cases b with
    | term t' =>
      obtain ⟨m, s', hm⟩ := hb
      have e₁ := run_ub_mono h (Nat.le_max_left n m)
      have e₂ := run_done_mono hm (Nat.le_max_right n m)
      rw [e₁] at e₂
      cases e₂
    | wrong t' =>
      obtain ⟨m, hm⟩ := hb
      have e₁ := run_ub_mono h (Nat.le_max_left n m)
      have e₂ := run_ub_mono hm (Nat.le_max_right n m)
      rw [e₁] at e₂
      cases e₂
      rfl
    | div t' =>
      have := hb.1 n
      rw [h] at this
      simp [Outcome.isRunning] at this
    | react f =>
      have := hb.1 n
      rw [h] at this
      simp [Outcome.isRunning] at this
  · rintro rfl
    exact ⟨n, h⟩

/-- A run that is still running with empty trace at every fuel diverges silently. -/
theorem hasBehFrom_iff_of_silent {K : ZContract} {P : Prog} {c : Cfg}
    (h : ∀ n, ∃ c', run K P n c = .running c' []) (b : Beh) :
    HasBehFrom K P c b ↔ b = .div [] := by
  constructor
  · intro hb
    cases b with
    | term t' =>
      obtain ⟨m, s', hm⟩ := hb
      obtain ⟨c', hc'⟩ := h m
      rw [hm] at hc'
      cases hc'
    | wrong t' =>
      obtain ⟨m, hm⟩ := hb
      obtain ⟨c', hc'⟩ := h m
      rw [hm] at hc'
      cases hc'
    | div t' =>
      obtain ⟨N, hN⟩ := hb.2
      obtain ⟨c', hc'⟩ := h N
      have := hN N (Nat.le_refl N)
      rw [hc'] at this
      simp [Outcome.trace] at this
      rw [this]
    | react f =>
      obtain ⟨m, hm⟩ := hb.2 1
      obtain ⟨c', hc'⟩ := h m
      rw [hc'] at hm
      simp [Outcome.trace, prefixOf] at hm
  · rintro rfl
    refine ⟨fun n => ?_, 0, fun n _ => ?_⟩
    · obtain ⟨c', hc'⟩ := h n
      rw [hc']
      rfl
    · obtain ⟨c', hc'⟩ := h n
      rw [hc']
      rfl

theorem improvesPP_refl (b : Beh) : ImprovesPP b b := Or.inl rfl

theorem improvesWT_of_improvesPP {bt bs : Beh} (h : ImprovesPP bt bs) : ImprovesWT bt bs := by
  rcases h with h | ⟨t, ht, _⟩
  · exact Or.inl h
  · exact Or.inr ⟨t, ht⟩

theorem refinesPP_refl (K : ZContract) (P : Prog) : RefinesPP K P P :=
  fun _ bt h => ⟨bt, h, improvesPP_refl bt⟩

theorem refinesWT_refl (K : ZContract) (P : Prog) : RefinesWT K P P :=
  fun _ bt h => ⟨bt, h, Or.inl rfl⟩

/-- Prefix-preserving refinement implies whole-trace refinement. -/
theorem refinesWT_of_refinesPP {K : ZContract} {src tgt : Prog} (h : RefinesPP K src tgt) :
    RefinesWT K src tgt := by
  intro σ bt hbt
  obtain ⟨bs, hbs, himp⟩ := h σ bt hbt
  exact ⟨bs, hbs, improvesWT_of_improvesPP himp⟩

/-- Prefix-preserving equivalence implies whole-trace equivalence. -/
theorem equivWT_of_equivPP {K : ZContract} {p q : Prog} (h : EquivPP K p q) : EquivWT K p q :=
  ⟨refinesWT_of_refinesPP h.1, refinesWT_of_refinesPP h.2⟩

theorem prefix_nil (u : List Int) : [] <+: u := ⟨u, rfl⟩

theorem hasPrefix_nil (b : Beh) : b.HasPrefix [] := by
  cases b <;> simp [Beh.HasPrefix, prefixOf]

end Toy.ZstAssume
