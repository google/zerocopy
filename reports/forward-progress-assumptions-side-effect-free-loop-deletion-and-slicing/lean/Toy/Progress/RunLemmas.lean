import Toy.Progress.Semantics

/-!
# Basic facts about `run`

Fully proved helper lemmas used by the definition examples, counterexamples and
non-vacuity theorems of this package.
-/

namespace Toy.Progress

theorem run_zero (c : Cmd) (s : State) : run 0 c s = (c, s, []) := rfl

theorem run_skip (n : Nat) (s : State) : run n .skip s = (.skip, s, []) := by
  cases n <;> rfl

theorem run_succ_of_step {c c' : Cmd} {s s' : State} {o : List Val} (n : Nat)
    (h : step c s = some (c', s', o)) :
    run (n + 1) c s = ((run n c' s').1, (run n c' s').2.1, o ++ (run n c' s').2.2) := by
  simp [run, h]

theorem step_eq_none_iff (c : Cmd) (s : State) : step c s = none ↔ c = .skip := by
  cases c with
  | seq c₁ c₂ =>
    simp only [step, reduceCtorEq, iff_false]
    split <;> simp
  | _ => simp [step]

theorem run_add (m n : Nat) (c : Cmd) (s : State) :
    run (m + n) c s =
      ((run n (run m c s).1 (run m c s).2.1).1,
       (run n (run m c s).1 (run m c s).2.1).2.1,
       (run m c s).2.2 ++ (run n (run m c s).1 (run m c s).2.1).2.2) := by
  induction m generalizing c s with
  | zero => simp [run_zero]
  | succ m ih =>
    rw [Nat.succ_add]
    cases h : step c s with
    | none =>
      have hc : c = .skip := (step_eq_none_iff c s).1 h
      subst hc
      simp [run_skip]
    | some r =>
      obtain ⟨c', s', o⟩ := r
      rw [run_succ_of_step _ h, run_succ_of_step _ h, ih]
      simp [List.append_assoc]

theorem run_of_run_skip {m n : Nat} {c : Cmd} {s s' : State} {t : List Val}
    (h : run m c s = (.skip, s', t)) (hmn : m ≤ n) : run n c s = (.skip, s', t) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [run_add, h]
  simp [run_skip]

theorem traceAt_prefix {m n : Nat} (c : Cmd) (s : State) (hmn : m ≤ n) :
    ∃ u, traceAt n c s = traceAt m c s ++ u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact ⟨_, by unfold traceAt; rw [run_add]⟩

theorem termsWith_unique {c : Cmd} {s s₁ s₂ : State} {t₁ t₂ : List Val}
    (h₁ : TermsWith c s t₁ s₁) (h₂ : TermsWith c s t₂ s₂) : t₁ = t₂ ∧ s₁ = s₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e₁ := run_of_run_skip h₁ (Nat.le_max_left n₁ n₂)
  have e₂ := run_of_run_skip h₂ (Nat.le_max_right n₁ n₂)
  rw [e₁] at e₂
  simp only [Prod.mk.injEq, true_and] at e₂
  exact ⟨e₂.2, e₂.1⟩

theorem length_traceAt_le_of_run_skip {m : Nat} {c : Cmd} {s s' : State} {t : List Val}
    (h : run m c s = (.skip, s', t)) (n : Nat) : (traceAt n c s).length ≤ t.length := by
  rcases Nat.le_total n m with hnm | hmn
  · obtain ⟨u, hu⟩ := traceAt_prefix c s hnm
    have : traceAt m c s = t := by simp [traceAt, h]
    rw [this] at hu
    rw [hu]; simp
  · have := run_of_run_skip h hmn
    simp [traceAt, this]

theorem length_prefixOf (f : Nat → Val) (k : Nat) : (prefixOf f k).length = k := by
  simp [prefixOf]

/-- A run that reaches `skip` has exactly one observable behaviour. -/
theorem obsBeh_of_run_skip {m : Nat} {c : Cmd} {s s' : State} {t : List Val}
    (h : run m c s = (.skip, s', t)) (b : Beh) : ObsBeh c s b ↔ b = .term t := by
  cases b with
  | term t' =>
    simp only [ObsBeh, Beh.term.injEq]
    constructor
    · rintro ⟨s'', h'⟩
      exact (termsWith_unique h' ⟨m, h⟩).1
    · rintro rfl; exact ⟨s', m, h⟩
  | div t' =>
    simp only [ObsBeh, reduceCtorEq, iff_false, not_and]
    intro hd
    exact absurd (by simp [h]) (hd m)
  | react f =>
    simp only [ObsBeh, reduceCtorEq, iff_false]
    intro hr
    obtain ⟨n, hn⟩ := hr (t.length + 1)
    have h1 := length_traceAt_le_of_run_skip h n
    rw [hn, length_prefixOf] at h1
    omega

/-- A run that never reaches `skip` and never emits has exactly the behaviour `div []`. -/
theorem obsBeh_of_silent {c : Cmd} {s : State}
    (h : ∀ n, (run n c s).1 ≠ .skip ∧ traceAt n c s = []) (b : Beh) :
    ObsBeh c s b ↔ b = .div [] := by
  cases b with
  | term t =>
    simp only [ObsBeh, reduceCtorEq, iff_false, not_exists]
    intro s' ⟨n, hn⟩
    exact (h n).1 (by simp [hn])
  | div t =>
    simp only [ObsBeh, Beh.div.injEq]
    constructor
    · rintro ⟨_, N, hN⟩
      rw [← hN N (Nat.le_refl N)]; exact (h N).2
    · rintro rfl
      exact ⟨fun n => (h n).1, 0, fun n _ => (h n).2⟩
  | react f =>
    simp only [ObsBeh, reduceCtorEq, iff_false]
    intro hr
    obtain ⟨n, hn⟩ := hr 1
    rw [(h n).2] at hn
    simp [prefixOf] at hn

theorem silent_of_step {c c' : Cmd} {s s' : State}
    (hs : step c s = some (c', s', []))
    (h : ∀ n, (run n c' s').1 ≠ .skip ∧ traceAt n c' s' = []) :
    ∀ n, (run n c s).1 ≠ .skip ∧ traceAt n c s = [] := by
  intro n
  cases n with
  | zero =>
    refine ⟨?_, rfl⟩
    intro hc
    simp only [run_zero] at hc
    subst hc
    simp [step] at hs
  | succ n =>
    simp only [traceAt, run_succ_of_step n hs, List.nil_append]
    exact h n

theorem terminates_of_termsWith {c : Cmd} {s s' : State} {t : List Val}
    (h : TermsWith c s t s') : Terminates c s := ⟨t, s', h⟩

theorem not_diverges_of_termsWith {c : Cmd} {s s' : State} {t : List Val}
    (h : TermsWith c s t s') : ¬ Diverges c s := by
  obtain ⟨n, hn⟩ := h
  intro hd
  exact hd n (by simp [hn])

theorem termsWith_of_step {c c' : Cmd} {s s' s'' : State} {o t : List Val}
    (hs : step c s = some (c', s', o)) (h : TermsWith c' s' t s'') :
    TermsWith c s (o ++ t) s'' := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [run_succ_of_step n hs, hn]⟩

theorem termsWith_skip (s : State) : TermsWith .skip s [] s := ⟨0, rfl⟩

/-! ### The spinning loop `while 1 do skip` -/

/-- The three configurations of `spin mp ;; k`. -/
def InSpinSeq (mp : Bool) (k c : Cmd) : Prop :=
  c = .seq (spin mp) k ∨
  c = .seq (.ite (.num 1) (.seq .skip (spin mp)) .skip) k ∨
  c = .seq (.seq .skip (spin mp)) k

theorem spinSeq_inv (mp : Bool) (k : Cmd) (s : State) :
    ∀ n c, InSpinSeq mp k c →
      InSpinSeq mp k (run n c s).1 ∧ (run n c s).2.1 = s ∧ (run n c s).2.2 = [] := by
  intro n
  induction n with
  | zero => intro c h; exact ⟨h, rfl, rfl⟩
  | succ n ih =>
    intro c h
    rcases h with rfl | rfl | rfl
    · rw [run_succ_of_step n (c' := .seq (.ite (.num 1) (.seq .skip (spin mp)) .skip) k)
        (s' := s) (o := []) (by simp [step, spin])]
      have := ih _ (Or.inr (Or.inl rfl))
      simpa using this
    · rw [run_succ_of_step n (c' := .seq (.seq .skip (spin mp)) k)
        (s' := s) (o := []) (by simp [step, Exp.eval])]
      have := ih _ (Or.inr (Or.inr rfl))
      simpa using this
    · rw [run_succ_of_step n (c' := .seq (spin mp) k)
        (s' := s) (o := []) (by simp [step])]
      have := ih _ (Or.inl rfl)
      simpa using this

theorem spinSeq_silent (mp : Bool) (k : Cmd) (s : State) :
    ∀ n, (run n (.seq (spin mp) k) s).1 ≠ .skip ∧ traceAt n (.seq (spin mp) k) s = [] := by
  intro n
  obtain ⟨h1, -, h3⟩ := spinSeq_inv mp k s n _ (Or.inl rfl)
  refine ⟨?_, h3⟩
  intro h
  rw [h] at h1
  rcases h1 with h1 | h1 | h1 <;> cases h1

/-- The three configurations of a bare `spin mp`. -/
def InSpin (mp : Bool) (c : Cmd) : Prop :=
  c = spin mp ∨ c = .ite (.num 1) (.seq .skip (spin mp)) .skip ∨ c = .seq .skip (spin mp)

theorem spin_inv (mp : Bool) (s : State) :
    ∀ n c, InSpin mp c →
      InSpin mp (run n c s).1 ∧ (run n c s).2.1 = s ∧ (run n c s).2.2 = [] := by
  intro n
  induction n with
  | zero => intro c h; exact ⟨h, rfl, rfl⟩
  | succ n ih =>
    intro c h
    rcases h with rfl | rfl | rfl
    · rw [run_succ_of_step n (c' := .ite (.num 1) (.seq .skip (spin mp)) .skip)
        (s' := s) (o := []) (by simp [step, spin])]
      have := ih _ (Or.inr (Or.inl rfl))
      simpa using this
    · rw [run_succ_of_step n (c' := .seq .skip (spin mp))
        (s' := s) (o := []) (by simp [step, Exp.eval])]
      have := ih _ (Or.inr (Or.inr rfl))
      simpa using this
    · rw [run_succ_of_step n (c' := spin mp)
        (s' := s) (o := []) (by simp [step])]
      have := ih _ (Or.inl rfl)
      simpa using this

theorem spin_silent (mp : Bool) (s : State) :
    ∀ n, (run n (spin mp) s).1 ≠ .skip ∧ traceAt n (spin mp) s = [] := by
  intro n
  obtain ⟨h1, -, h3⟩ := spin_inv mp s n _ (Or.inl rfl)
  refine ⟨?_, h3⟩
  intro h
  rw [h] at h1
  rcases h1 with h1 | h1 | h1 <;> cases h1

theorem obsBeh_spin (mp : Bool) (s : State) (b : Beh) : ObsBeh (spin mp) s b ↔ b = .div [] :=
  obsBeh_of_silent (spin_silent mp s) b

theorem obsBeh_spinSeq (mp : Bool) (k : Cmd) (s : State) (b : Beh) :
    ObsBeh (.seq (spin mp) k) s b ↔ b = .div [] :=
  obsBeh_of_silent (spinSeq_silent mp k s) b

theorem not_terminates_spin (mp : Bool) (s : State) : ¬ Terminates (spin mp) s := by
  rintro ⟨t, s', n, hn⟩
  exact (spin_silent mp s n).1 (by simp [hn])

theorem silentlyDiverges_spin (mp : Bool) (s : State) : SilentlyDiverges (spin mp) s :=
  ⟨[], (obsBeh_spin mp s _).2 rfl⟩

theorem silentlyDiverges_spinSeq (mp : Bool) (k : Cmd) (s : State) :
    SilentlyDiverges (.seq (spin mp) k) s :=
  ⟨[], (obsBeh_spinSeq mp k s _).2 rfl⟩

/-! ### Single statements -/

theorem obsBeh_skip (s : State) (b : Beh) : ObsBeh .skip s b ↔ b = .term [] :=
  obsBeh_of_run_skip (m := 0) rfl b

theorem obsBeh_emit (e : Exp) (s : State) (b : Beh) :
    ObsBeh (.emit e) s b ↔ b = .term [e.eval s] :=
  obsBeh_of_run_skip (m := 1) rfl b

theorem not_silentlyDiverges_of_termsWith {c : Cmd} {s s' : State} {t : List Val}
    (h : TermsWith c s t s') : ¬ SilentlyDiverges c s := by
  rintro ⟨u, hd, -⟩
  exact not_diverges_of_termsWith h hd

theorem obsBeh_of_termsWith {c : Cmd} {s s' : State} {t : List Val}
    (h : TermsWith c s t s') (b : Beh) : ObsBeh c s b ↔ b = .term t := by
  obtain ⟨n, hn⟩ := h
  exact obsBeh_of_run_skip hn b

/-! ### Big-step rules for terminating runs -/

theorem termsWith_assign (x : Var) (e : Exp) (s : State) :
    TermsWith (.assign x e) s [] (State.update s x (e.eval s)) := ⟨1, rfl⟩

theorem termsWith_emit (e : Exp) (s : State) : TermsWith (.emit e) s [e.eval s] s := ⟨1, rfl⟩

theorem run_seq_of_run_skip (c₂ : Cmd) :
    ∀ n c₁ s s' o, run n c₁ s = (.skip, s', o) →
      ∃ m, run m (.seq c₁ c₂) s = (.seq .skip c₂, s', o) := by
  intro n
  induction n with
  | zero =>
    intro c₁ s s' o h
    simp only [run_zero, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨0, rfl⟩
  | succ n ih =>
    intro c₁ s s' o h
    cases hs : step c₁ s with
    | none =>
      have hc : c₁ = .skip := (step_eq_none_iff c₁ s).1 hs
      subst hc
      rw [run_skip] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨0, rfl⟩
    | some r =>
      obtain ⟨c₁', s₁, o₁⟩ := r
      rw [run_succ_of_step n hs] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨m, hm⟩ := ih c₁' s₁ s' (run n c₁' s₁).2.2 (by rw [← h1, ← h2])
      refine ⟨m + 1, ?_⟩
      have hstep : step (.seq c₁ c₂) s = some (.seq c₁' c₂, s₁, o₁) := by simp [step, hs]
      rw [run_succ_of_step m hstep, hm]
      simp [h3]

theorem termsWith_seq {c₁ c₂ : Cmd} {s s₁ s₂ : State} {t₁ t₂ : List Val}
    (h₁ : TermsWith c₁ s t₁ s₁) (h₂ : TermsWith c₂ s₁ t₂ s₂) :
    TermsWith (.seq c₁ c₂) s (t₁ ++ t₂) s₂ := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := run_seq_of_run_skip c₂ n c₁ s s₁ t₁ hn
  obtain ⟨k, hk⟩ := h₂
  refine ⟨m + (k + 1), ?_⟩
  rw [run_add, hm]
  simp only
  rw [run_succ_of_step k (c' := c₂) (s' := s₁) (o := []) (by simp [step]), hk]
  simp

theorem termsWith_ite_true {b : Exp} {c₁ c₂ : Cmd} {s s' : State} {t : List Val}
    (hb : b.eval s ≠ 0) (h : TermsWith c₁ s t s') : TermsWith (.ite b c₁ c₂) s t s' := by
  have := termsWith_of_step (c := .ite b c₁ c₂) (c' := c₁) (s := s) (s' := s) (o := [])
    (by simp [step, hb]) h
  simpa using this

theorem termsWith_ite_false {b : Exp} {c₁ c₂ : Cmd} {s s' : State} {t : List Val}
    (hb : b.eval s = 0) (h : TermsWith c₂ s t s') : TermsWith (.ite b c₁ c₂) s t s' := by
  have := termsWith_of_step (c := .ite b c₁ c₂) (c' := c₂) (s := s) (s' := s) (o := [])
    (by simp [step, hb]) h
  simpa using this

theorem termsWith_loop_exit {mp : Bool} {b : Exp} {body : Cmd} {s : State}
    (hb : b.eval s = 0) : TermsWith (.loop mp b body) s [] s := by
  have := termsWith_of_step (c := .loop mp b body) (s := s) (s' := s) (o := []) (by simp [step])
    (termsWith_ite_false (c₁ := .seq body (.loop mp b body)) hb (termsWith_skip s))
  simpa using this

theorem termsWith_loop_iter {mp : Bool} {b : Exp} {body : Cmd} {s s₁ s₂ : State}
    {t₁ t₂ : List Val} (hb : b.eval s ≠ 0) (h₁ : TermsWith body s t₁ s₁)
    (h₂ : TermsWith (.loop mp b body) s₁ t₂ s₂) :
    TermsWith (.loop mp b body) s (t₁ ++ t₂) s₂ := by
  have := termsWith_of_step (c := .loop mp b body) (s := s) (s' := s) (o := []) (by simp [step])
    (termsWith_ite_true (c₂ := .skip) hb (termsWith_seq h₁ h₂))
  simpa using this

end Toy.Progress
