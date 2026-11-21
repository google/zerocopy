import Toy.Progress.BigStep

/-!
# Silent iteration of a loop and progress violations

Proof infrastructure for the per-loop semantics: a progress violation makes the whole run
silently diverge, and conversely every silently diverging run eventually enters a loop
that silently iterates (the innermost loop that fails to make progress).
-/

namespace Toy.Progress

/-! ## Silent iteration implies silent divergence -/

theorem silentlyIterates_spin (s : State) : SilentlyIterates (.num 1) .skip s :=
  ⟨fun _ => s, fun _ => [], rfl, fun _ => ⟨by simp [Exp.eval], termsWith_skip s⟩, 0, fun _ _ => rfl⟩

/-- One complete iteration of a loop, from loop entry back to loop entry. -/
theorem run_loop_iter {mp : Bool} {b : Exp} {body : Cmd} {s s₁ : State} {t : List Val}
    (hb : b.eval s ≠ 0) (h : BigStep body s t s₁) :
    ∃ m, run m (.loop mp b body) s = (.loop mp b body, s₁, t) := by
  obtain ⟨m, hm⟩ := run_seq_of_bigStep (.loop mp b body) h
  refine ⟨2 + m, ?_⟩
  rw [run_add]
  have h2 : run 2 (.loop mp b body) s = (.seq body (.loop mp b body), s, []) := by
    simp [run, step, hb]
  rw [h2]; simp [hm]

theorem not_terminates_of_silentlyIterates {mp : Bool} {b : Exp} {body : Cmd} {s : State}
    (h : SilentlyIterates b body s) : ¬ Terminates (.loop mp b body) s := by
  obtain ⟨σ, o, h0, hit, -⟩ := h
  have key : ∀ c s' t s'', BigStep c s' t s'' → c = .loop mp b body → ∀ i, s' = σ i → False := by
    intro c s' t s'' hb
    induction hb with
    | loopExit hb =>
      intro hc i hi
      cases hc; subst hi; exact (hit i).1 hb
    | loopIter _ h₁ _ _ ih₂ =>
      intro hc i hi
      cases hc; subst hi
      have := (bigStep_det h₁ (termsWith_iff_bigStep.1 (hit i).2)).2
      exact ih₂ rfl (i + 1) this
    | _ => intro hc; cases hc
  rintro ⟨t, s', ht⟩
  exact key _ _ _ _ (termsWith_iff_bigStep.1 ht) rfl 0 h0.symm

theorem silentlyDiverges_of_silentlyIterates {mp : Bool} {b : Exp} {body : Cmd} {s : State}
    (h : SilentlyIterates b body s) : SilentlyDiverges (.loop mp b body) s := by
  have hnt := not_terminates_of_silentlyIterates (mp := mp) h
  obtain ⟨σ, o, h0, hit, N, hN⟩ := h
  have hA : ∀ c s' t, Partial c s' t → c = .loop mp b body → ∀ i, s' = σ i →
      (∀ j, i ≤ j → o j = []) → t = [] := by
    intro c s' t hp
    induction hp with
    | nil => intros; rfl
    | loopBody _ hp _ =>
      intro hc i hi hz
      cases hc; subst hi
      have := reach_le_of_bigStep (termsWith_iff_bigStep.1 (hit i).2) (reach_of_partial hp)
      rw [hz i (Nat.le_refl i)] at this
      exact List.prefix_nil.1 this
    | loopIter _ h₁ _ ih₂ =>
      intro hc i hi hz
      cases hc; subst hi
      obtain ⟨e₁, e₂⟩ := bigStep_det h₁ (termsWith_iff_bigStep.1 (hit i).2)
      rw [e₁, hz i (Nat.le_refl i), ih₂ rfl (i + 1) e₂ (fun j hj => hz j (by omega))]; rfl
    | _ => intro hc; cases hc
  have hB : ∀ i K, (∀ t, Partial (.loop mp b body) (σ (i + 1)) t → t.length ≤ K) →
      ∀ t, Partial (.loop mp b body) (σ i) t → t.length ≤ (o i).length + K := by
    intro i K hK t hp
    cases hp with
    | nil => simp
    | loopBody _ hp =>
      have := (reach_le_of_bigStep (termsWith_iff_bigStep.1 (hit i).2) (reach_of_partial hp)).length_le
      omega
    | loopIter _ h₁ hp =>
      obtain ⟨rfl, rfl⟩ := bigStep_det h₁ (termsWith_iff_bigStep.1 (hit i).2)
      have := hK _ hp
      simp; omega
  have hC : ∀ k i, i + k = N → ∃ K, ∀ t, Partial (.loop mp b body) (σ i) t → t.length ≤ K := by
    intro k
    induction k with
    | zero =>
      intro i hi
      exact ⟨0, fun t hp => by
        rw [hA _ _ _ hp rfl i rfl (fun j hj => hN j (by omega))]; simp⟩
    | succ k ih =>
      intro i hi
      obtain ⟨K, hK⟩ := ih (i + 1) (by omega)
      exact ⟨_, hB i K hK⟩
  obtain ⟨K, hK⟩ := hC N 0 (by omega)
  rw [h0] at hK
  exact silentlyDiverges_iff_bounded.2 ⟨hnt, K, fun u hu => hK u (partial_of_reach hu)⟩

theorem silentlyDiverges_seq_of_left {c₁ c₂ : Cmd} {s : State} (h : SilentlyDiverges c₁ s) :
    SilentlyDiverges (.seq c₁ c₂) s := by
  have hnt := (silentlyDiverges_iff_bounded.1 h).1
  obtain ⟨t, ht⟩ := h
  exact ⟨t, (obsBeh_seq_of_not_terminates hnt _).2 ht⟩

theorem silentlyDiverges_of_head {c : Cmd} {s : State} (h : SilentlyDiverges c.head s) :
    SilentlyDiverges c s := by
  induction c with
  | seq c₁ c₂ ih _ => exact silentlyDiverges_seq_of_left (ih h)
  | _ => exact h

/-- A progress violation makes the whole run silently diverge. -/
theorem silentlyDiverges_of_progressViolation {c : Cmd} {s : State}
    (h : ProgressViolation c s) : SilentlyDiverges c s := by
  obtain ⟨n, b, body, hh, hsi⟩ := h
  have h1 : SilentlyDiverges (run n c s).1.head (run n c s).2.1 := by
    rw [hh]; exact silentlyDiverges_of_silentlyIterates hsi
  exact (silentlyDiverges_iff_of_run (m := n) (c' := (run n c s).1) (s' := (run n c s).2.1)
    (t₀ := (run n c s).2.2) rfl).2 (silentlyDiverges_of_head h1)

/-! ## Every silent divergence is caused by a silently iterating loop -/

/-- States in which a loop is re-entered after finitely many complete iterations. -/
inductive LoopReach (b : Exp) (body : Cmd) (s : State) : State → List Val → Prop
  | refl : LoopReach b body s s []
  | step {s₁ s₂ : State} {t₁ t₂ : List Val} : LoopReach b body s s₁ t₁ → b.eval s₁ ≠ 0 →
      BigStep body s₁ t₂ s₂ → LoopReach b body s s₂ (t₁ ++ t₂)

theorem run_of_loopReach {mp : Bool} {b : Exp} {body : Cmd} {s s' : State} {t : List Val}
    (h : LoopReach b body s s' t) : ∃ m, run m (.loop mp b body) s = (.loop mp b body, s', t) := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step _ hb h₂ ih =>
    obtain ⟨m₁, hm₁⟩ := ih
    obtain ⟨m₂, hm₂⟩ := run_loop_iter (mp := mp) hb h₂
    exact ⟨m₁ + m₂, by rw [run_add, hm₁]; simp [hm₂]⟩

open Classical in
/-- Proof device: the result of one iteration of `body` from `s`, if it terminates. -/
noncomputable def iterNext (body : Cmd) (s : State) : List Val × State :=
  if h : Terminates body s then
    (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else ([], s)

theorem iterNext_spec {body : Cmd} {s : State} (h : Terminates body s) :
    TermsWith body s (iterNext body s).1 (iterNext body s).2 := by
  simp only [iterNext, h, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec h)

/-- Proof device: the state at the start of iteration `i`. -/
noncomputable def iterState (body : Cmd) (s : State) : Nat → State
  | 0 => s
  | i + 1 => (iterNext body (iterState body s i)).2

/-- Proof device: the output of the first `j` iterations. -/
def iterTrace (o : Nat → List Val) : Nat → List Val
  | 0 => []
  | j + 1 => iterTrace o j ++ o j

theorem iterTrace_length_mono (o : Nat → List Val) {i j : Nat} (h : i ≤ j) :
    (iterTrace o i).length ≤ (iterTrace o j).length := by
  induction j with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := ih (by omega); simp [iterTrace]; omega
    · rw [h]; exact Nat.le_refl _

/-- **Every silently diverging run eventually enters a loop that silently iterates.** -/
theorem exists_head_silentlyIterates : ∀ (c : Cmd) (s : State), SilentlyDiverges c s →
    ∃ n mp b body, (run n c s).1.head = .loop mp b body ∧
      SilentlyIterates b body (run n c s).2.1 := by
  intro c
  induction c with
  | skip =>
    intro s h
    exact absurd ⟨[], s, termsWith_skip s⟩ (silentlyDiverges_iff_bounded.1 h).1
  | assign x e =>
    intro s h
    exact absurd ⟨[], _, termsWith_assign x e s⟩ (silentlyDiverges_iff_bounded.1 h).1
  | emit e =>
    intro s h
    exact absurd ⟨_, s, termsWith_emit e s⟩ (silentlyDiverges_iff_bounded.1 h).1
  | seq c₁ c₂ ih₁ ih₂ =>
    intro s h
    by_cases h₁ : Terminates c₁ s
    · obtain ⟨t₁, s₁, ht₁⟩ := h₁
      obtain ⟨m, hm⟩ := run_seq_of_bigStep c₂ (termsWith_iff_bigStep.1 ht₁)
      obtain ⟨n, mp, b, body, hh, hsi⟩ := ih₂ s₁ ((silentlyDiverges_iff_of_run hm).1 h)
      refine ⟨m + n, mp, b, body, ?_, ?_⟩
      · rw [run_add, hm]; exact hh
      · rw [run_add, hm]; exact hsi
    · have h₁' : SilentlyDiverges c₁ s := by
        obtain ⟨t, ht⟩ := h
        exact ⟨t, (obsBeh_seq_of_not_terminates h₁ _).1 ht⟩
      obtain ⟨n, mp, b, body, hh, hsi⟩ := ih₁ s h₁'
      obtain ⟨m, hm⟩ := run_seq_lift c₂ n c₁ s
      refine ⟨m, mp, b, body, ?_, ?_⟩
      · rw [hm]; exact hh
      · rw [hm]; exact hsi
  | ite b c₁ c₂ ih₁ ih₂ =>
    intro s h
    have hr : run 1 (.ite b c₁ c₂) s = (if b.eval s = 0 then c₂ else c₁, s, []) := by
      simp [run, step]
    have h' := (silentlyDiverges_iff_of_run hr).1 h
    have key : ∀ d : Cmd, (∀ s, SilentlyDiverges d s → ∃ n mp b body,
        (run n d s).1.head = .loop mp b body ∧ SilentlyIterates b body (run n d s).2.1) →
        run 1 (.ite b c₁ c₂) s = (d, s, []) → SilentlyDiverges d s →
        ∃ n mp b' body, (run n (.ite b c₁ c₂) s).1.head = .loop mp b' body ∧
          SilentlyIterates b' body (run n (.ite b c₁ c₂) s).2.1 := by
      intro d ihd hrd hd
      obtain ⟨n, mp, b', body, hh, hsi⟩ := ihd s hd
      refine ⟨1 + n, mp, b', body, ?_, ?_⟩
      · rw [run_add, hrd]; exact hh
      · rw [run_add, hrd]; exact hsi
    by_cases hb : b.eval s = 0
    · simp only [hb, ↓reduceIte] at hr h'; exact key c₂ ih₂ hr h'
    · simp only [hb, ↓reduceIte] at hr h'; exact key c₁ ih₁ hr h'
  | loop mp b body ih =>
    intro s h
    have hnt := (silentlyDiverges_iff_bounded.1 h).1
    by_cases hall : ∀ s' t, LoopReach b body s s' t → b.eval s' ≠ 0 ∧ Terminates body s'
    · -- The loop itself completes every iteration: it silently iterates.
      let σ := iterState body s
      let o : Nat → List Val := fun i => (iterNext body (σ i)).1
      have hreach : ∀ i, LoopReach b body s (σ i) (iterTrace o i) := by
        intro i
        induction i with
        | zero => exact .refl
        | succ i ihi =>
          have hg := hall _ _ ihi
          exact .step ihi hg.1 (termsWith_iff_bigStep.1 (iterNext_spec hg.2))
      have hit : ∀ i, b.eval (σ i) ≠ 0 ∧ TermsWith body (σ i) (o i) (σ (i + 1)) := by
        intro i
        have hg := hall _ _ (hreach i)
        exact ⟨hg.1, iterNext_spec hg.2⟩
      obtain ⟨K, hK⟩ := (silentlyDiverges_iff_bounded.1 h).2
      have hbound : ∀ j, (iterTrace o j).length ≤ K := by
        intro j
        obtain ⟨m, hm⟩ := run_of_loopReach (mp := mp) (hreach j)
        exact hK _ ⟨m, by simp [traceAt, hm]⟩
      have hsil : ∃ N, ∀ i, N ≤ i → o i = [] := by
        refine Classical.byContradiction fun hno => ?_
        have hinf : ∀ N, ∃ i, N ≤ i ∧ o i ≠ [] := by
          intro N
          refine Classical.byContradiction fun hne => hno ⟨N, fun i hi => ?_⟩
          exact Classical.byContradiction fun hoi => hne ⟨i, hi, hoi⟩
        have hgrow : ∀ k, ∃ j, k ≤ (iterTrace o j).length := by
          intro k
          induction k with
          | zero => exact ⟨0, Nat.zero_le _⟩
          | succ k ihk =>
            obtain ⟨j, hj⟩ := ihk
            obtain ⟨i, hi, hoi⟩ := hinf j
            refine ⟨i + 1, ?_⟩
            have h1 := iterTrace_length_mono o hi
            have h2 : (o i).length ≠ 0 := fun h0 => hoi (List.eq_nil_of_length_eq_zero h0)
            simp [iterTrace]; omega
        obtain ⟨j, hj⟩ := hgrow (K + 1)
        have := hbound j
        omega
      exact ⟨0, mp, b, body, rfl, σ, o, rfl, hit, hsil⟩
    · -- Some iteration is entered and does not complete: recurse into the body.
      have hex : ∃ s' t, LoopReach b body s s' t ∧ ¬ (b.eval s' ≠ 0 ∧ Terminates body s') := by
        refine Classical.byContradiction fun hne => hall fun s' t hr => ?_
        exact Classical.byContradiction fun hn => hne ⟨s', t, hr, hn⟩
      obtain ⟨s', t, hr, hbad⟩ := hex
      obtain ⟨m, hm⟩ := run_of_loopReach (mp := mp) hr
      by_cases hb : b.eval s' = 0
      · exact absurd ⟨t ++ [], s', termsWith_of_run hm (termsWith_loop_exit hb)⟩ hnt
      · have hbody : ¬ Terminates body s' := fun ht => hbad ⟨hb, ht⟩
        have h2 : run 2 (.loop mp b body) s' = (.seq body (.loop mp b body), s', []) := by
          simp [run, step, hb]
        have hm2 : run (m + 2) (.loop mp b body) s = (.seq body (.loop mp b body), s', t) := by
          rw [run_add, hm]; simp [h2]
        have hsd : SilentlyDiverges body s' := by
          obtain ⟨u, hu⟩ := (silentlyDiverges_iff_of_run hm2).1 h
          exact ⟨u, (obsBeh_seq_of_not_terminates hbody _).1 hu⟩
        obtain ⟨n, mp', b', body', hh, hsi⟩ := ih s' hsd
        obtain ⟨m', hm'⟩ := run_seq_lift (.loop mp b body) n body s'
        refine ⟨m + 2 + m', mp', b', body', ?_, ?_⟩
        · rw [run_add, hm2]; simp only [hm']; exact hh
        · rw [run_add, hm2]; simp only [hm']; exact hsi

end Toy.Progress
