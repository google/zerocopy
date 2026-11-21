import Toy.Progress.Iteration

/-!
# Positive and negative examples for the semantic definitions
-/

namespace Toy.Progress

/-- `while 1 do emit 7` with progress flag `mp`: runs forever and emits forever. -/
def beep (mp : Bool) : Cmd := .loop mp (.num 1) (.emit (.num 7))

/-! ### Single steps and runs -/

/-- Positive example: `step` unfolds a loop into a conditional. -/
theorem step_example (s : State) :
    step (spin false) s = some (.ite (.num 1) (.seq .skip (spin false)) .skip, s, []) := rfl

/-- Positive example: an `emit` step outputs the value of its expression. -/
theorem run_emit_example (s : State) :
    run 5 (.seq (.assign 0 (.num 3)) (.emit (.var 0))) s
      = (.skip, State.update s 0 3, [3]) := by
  simp [run, step, Exp.eval, State.update]

/-- Negative example: `skip` does not step. -/
theorem step_skip_none (s : State) : step .skip s = none := rfl

/-! ### Termination and divergence -/

/-- Positive example: `emit 1` terminates. -/
theorem terminates_example (s : State) : Terminates (.emit (.num 1)) s :=
  ⟨[1], s, 1, rfl⟩

/-- Positive example: `while 1 do skip` diverges. -/
theorem diverges_spin (mp : Bool) (s : State) : Diverges (spin mp) s :=
  fun n => (spin_silent mp s n).1

/-- Negative example: `while 1 do skip` does not terminate. -/
theorem terminates_example_neg (s : State) : ¬ Terminates (spin false) s :=
  not_terminates_spin false s

/-! ### `beep`: an infinite trace -/

theorem run_four_beep (mp : Bool) (s : State) : run 4 (beep mp) s = (beep mp, s, [7]) := by
  simp [run, step, beep, Exp.eval]

theorem run_mul_four_beep (mp : Bool) (s : State) (n : Nat) :
    run (4 * n) (beep mp) s = (beep mp, s, List.replicate n 7) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, run_add, ih]
    simp [run_four_beep, List.replicate_succ']

theorem prefixOf_const (v k : Nat) : prefixOf (fun _ => v) k = List.replicate k v := by
  simp [prefixOf, List.map_const']

/-- Positive example: `while 1 do emit 7` has the reactive behaviour `7, 7, 7, …`. -/
theorem obsBeh_beep_react (mp : Bool) (s : State) : ObsBeh (beep mp) s (.react fun _ => 7) := by
  intro k
  refine ⟨4 * k, ?_⟩
  simp [traceAt, run_mul_four_beep, prefixOf_const]

/-- Negative example: an emitting infinite loop is not a silent divergence (with any
finite trace). -/
theorem not_silentlyDiverges_beep (mp : Bool) (s : State) : ¬ SilentlyDiverges (beep mp) s := by
  rintro ⟨t, -, N, hN⟩
  have h := hN (4 * (N + t.length + 1)) (by omega)
  simp only [traceAt, run_mul_four_beep] at h
  have := congrArg List.length h
  simp at this
  omega

/-! ### Observable behaviours -/

/-- Positive example: `while 1 do skip ;; emit 1` silently diverges with empty trace. -/
theorem obsBeh_example_div (s : State) :
    ObsBeh (.seq (spin false) (.emit (.num 1))) s (.div []) :=
  (obsBeh_spinSeq false _ s _).2 rfl

/-- Negative example: `while 1 do skip ;; emit 1` never emits `1`. -/
theorem obsBeh_example_neg (s : State) :
    ¬ ObsBeh (.seq (spin false) (.emit (.num 1))) s (.term [1]) := by
  rw [obsBeh_spinSeq]; simp

/-! ### Forward-progress behaviours -/

/-- Positive example: under forward progress a silent infinite loop admits every
behaviour (here: terminating after emitting `42`). The flag is irrelevant. -/
theorem fpBeh_example_ub (s : State) :
    FPBeh (.seq (spin false) (.emit (.num 1))) s (.term [42]) :=
  Or.inl (silentlyDiverges_spinSeq false _ s)

/-- Negative example: a terminating program has no extra forward-progress behaviours. -/
theorem fpBeh_example_neg (s : State) : ¬ FPBeh (.emit (.num 1)) s (.term [2]) := by
  rintro (h | h)
  · exact not_silentlyDiverges_of_termsWith (c := .emit (.num 1)) ⟨1, rfl⟩ h
  · rw [obsBeh_emit] at h; simp [Exp.eval] at h

/-- Negative example: an emitting infinite loop is not undefined under forward progress. -/
theorem fpBeh_beep_neg (s : State) : ¬ FPBeh (beep false) s (.term []) := by
  rintro (h | h)
  · exact not_silentlyDiverges_beep false s h
  · obtain ⟨s', n, hn⟩ := h
    have h4 := run_mul_four_beep false s n
    have hle : n ≤ 4 * n := by omega
    have := run_of_run_skip hn hle
    rw [h4] at this
    simp [beep] at this

/-! ### Per-loop (mixed) behaviours -/

/-- Positive example: entering a *flagged* silent infinite loop is a progress violation,
so every behaviour is admitted. -/
theorem mixedBeh_example_ub (s : State) :
    MixedBeh (.seq (spin true) (.emit (.num 1))) s (.term [42]) :=
  Or.inl ⟨0, .num 1, .skip, rfl, silentlyIterates_spin s⟩

theorem not_progressViolation_spinSeq_false (k : Cmd) (s : State) :
    ¬ ProgressViolation (.seq (spin false) k) s := by
  rintro ⟨n, b, body, hh, -⟩
  obtain ⟨h1, -, -⟩ := spinSeq_inv false k s n _ (Or.inl rfl)
  rcases h1 with h1 | h1 | h1 <;> rw [h1] at hh <;> simp [Cmd.head, spin] at hh

/-- Negative example: the same loop *unflagged* is divergence-observable: no undefined
behaviour, and the only behaviour is `div []`. -/
theorem mixedBeh_example_neg (s : State) :
    ¬ MixedBeh (.seq (spin false) (.emit (.num 1))) s (.term [42]) := by
  rintro (h | h)
  · exact not_progressViolation_spinSeq_false _ s h
  · rw [obsBeh_spinSeq] at h; simp at h

/-- The four configurations of `beep mp`. -/
def InBeep (mp : Bool) (c : Cmd) : Prop :=
  c = beep mp ∨ c = .ite (.num 1) (.seq (.emit (.num 7)) (beep mp)) .skip ∨
  c = .seq (.emit (.num 7)) (beep mp) ∨ c = .seq .skip (beep mp)

theorem beep_inv (mp : Bool) (s : State) :
    ∀ n c, InBeep mp c → InBeep mp (run n c s).1 ∧ (run n c s).2.1 = s := by
  intro n
  induction n with
  | zero => intro c h; exact ⟨h, rfl⟩
  | succ n ih =>
    intro c h
    rcases h with rfl | rfl | rfl | rfl
    · rw [run_succ_of_step n (c' := .ite (.num 1) (.seq (.emit (.num 7)) (beep mp)) .skip)
        (s' := s) (o := []) (by simp [step, beep])]
      simpa using ih _ (Or.inr (Or.inl rfl))
    · rw [run_succ_of_step n (c' := .seq (.emit (.num 7)) (beep mp))
        (s' := s) (o := []) (by simp [step, Exp.eval])]
      simpa using ih _ (Or.inr (Or.inr (Or.inl rfl)))
    · rw [run_succ_of_step n (c' := .seq .skip (beep mp))
        (s' := s) (o := [7]) (by simp [step, Exp.eval])]
      simpa using ih _ (Or.inr (Or.inr (Or.inr rfl)))
    · rw [run_succ_of_step n (c' := beep mp)
        (s' := s) (o := []) (by simp [step])]
      simpa using ih _ (Or.inl rfl)

/-- Negative example: a flagged loop that keeps emitting is not a progress violation. -/
theorem not_progressViolation_beep (s : State) : ¬ ProgressViolation (beep true) s := by
  rintro ⟨n, b, body, hh, hsi⟩
  obtain ⟨h1, h2⟩ := beep_inv true s n _ (Or.inl rfl)
  rw [h2] at hsi
  rcases h1 with h1 | h1 | h1 | h1 <;> rw [h1] at hh <;> simp [Cmd.head, beep] at hh
  obtain ⟨rfl, rfl⟩ := hh
  obtain ⟨σ, o, -, hit, N, hN⟩ := hsi
  have := (termsWith_unique (hit N).2 (termsWith_emit (.num 7) (σ N))).1
  rw [hN N (Nat.le_refl N)] at this
  simp at this

/-- `x0 = 0` -/
def x0IsZero : Exp := .eq (.var 0) (.num 0)

/-- A flagged loop whose body enters the *unflagged* loop `while 1 do skip` and would
then exit: `while⁺ x0 = 0 do (while⁻ 1 do skip ;; x0 := 1)` (`⁺`/`⁻`: flag set/unset). -/
def flaggedOverUnflagged : Cmd := .loop true x0IsZero (.seq (spin false) (.assign 0 (.num 1)))

/-- The configurations of `flaggedOverUnflagged` run from a state with `x0 = 0`. -/
def InFlaggedOverUnflagged (c : Cmd) : Prop :=
  c = flaggedOverUnflagged ∨
  c = .ite x0IsZero (.seq (.seq (spin false) (.assign 0 (.num 1))) flaggedOverUnflagged) .skip ∨
  ∃ d, InSpin false d ∧ c = .seq (.seq d (.assign 0 (.num 1))) flaggedOverUnflagged

theorem flaggedOverUnflagged_inv {s : State} (h0 : s 0 = 0) :
    ∀ n c, InFlaggedOverUnflagged c →
      InFlaggedOverUnflagged (run n c s).1 ∧ (run n c s).2.1 = s ∧ (run n c s).2.2 = [] := by
  intro n
  induction n with
  | zero => intro c h; exact ⟨h, rfl, rfl⟩
  | succ n ih =>
    intro c h
    rcases h with rfl | rfl | ⟨d, hd, rfl⟩
    · rw [run_succ_of_step n (c' := .ite x0IsZero
          (.seq (.seq (spin false) (.assign 0 (.num 1))) flaggedOverUnflagged) .skip)
        (s' := s) (o := []) (by simp [step, flaggedOverUnflagged])]
      simpa using ih _ (Or.inr (Or.inl rfl))
    · rw [run_succ_of_step n (c' := .seq (.seq (spin false) (.assign 0 (.num 1)))
          flaggedOverUnflagged) (s' := s) (o := []) (by simp [step, x0IsZero, Exp.eval, h0])]
      simpa using ih _ (Or.inr (Or.inr ⟨_, Or.inl rfl, rfl⟩))
    · rcases hd with rfl | rfl | rfl
      · rw [run_succ_of_step n (c' := .seq (.seq (.ite (.num 1) (.seq .skip (spin false)) .skip)
            (.assign 0 (.num 1))) flaggedOverUnflagged) (s' := s) (o := []) (by simp [step, spin])]
        simpa using ih _ (Or.inr (Or.inr ⟨_, Or.inr (Or.inl rfl), rfl⟩))
      · rw [run_succ_of_step n (c' := .seq (.seq (.seq .skip (spin false)) (.assign 0 (.num 1)))
            flaggedOverUnflagged) (s' := s) (o := []) (by simp [step, Exp.eval])]
        simpa using ih _ (Or.inr (Or.inr ⟨_, Or.inr (Or.inr rfl), rfl⟩))
      · rw [run_succ_of_step n (c' := .seq (.seq (spin false) (.assign 0 (.num 1)))
            flaggedOverUnflagged) (s' := s) (o := []) (by simp [step])]
        simpa using ih _ (Or.inr (Or.inr ⟨_, Or.inl rfl, rfl⟩))

/-- Negative example (the obligation belongs to the innermost diverging loop): a flagged
loop whose body silently diverges inside a nested *unflagged* loop is not a progress
violation, because the flagged loop never completes an iteration. -/
theorem not_progressViolation_flaggedOverUnflagged {s : State} (h0 : s 0 = 0) :
    ¬ ProgressViolation flaggedOverUnflagged s := by
  rintro ⟨n, b, body, hh, hsi⟩
  obtain ⟨h1, h2, -⟩ := flaggedOverUnflagged_inv h0 n _ (Or.inl rfl)
  rw [h2] at hsi
  rcases h1 with h1 | h1 | ⟨d, hd, h1⟩
  · rw [h1] at hh
    simp only [flaggedOverUnflagged, Cmd.head, Cmd.loop.injEq, true_and] at hh
    obtain ⟨rfl, rfl⟩ := hh
    obtain ⟨σ, o, hσ, hit, -⟩ := hsi
    have ht := (hit 0).2
    rw [hσ] at ht
    obtain ⟨t₁, s₁, t₂, hb₁, -, -⟩ := bigStep_seq_inv (termsWith_iff_bigStep.1 ht)
    exact not_terminates_spin false s ⟨t₁, s₁, termsWith_of_bigStep hb₁⟩
  · rw [h1] at hh; simp [Cmd.head] at hh
  · rw [h1] at hh
    rcases hd with rfl | rfl | rfl <;> simp [Cmd.head, spin] at hh

/-- Under the per-loop semantics, `flaggedOverUnflagged` run from a state with `x0 = 0` is
defined and has exactly the behaviour `div []`, as its unflagged inner loop would alone. -/
theorem mixedBeh_flaggedOverUnflagged {s : State} (h0 : s 0 = 0) (b : Beh) :
    MixedBeh flaggedOverUnflagged s b ↔ b = .div [] := by
  have hs : ∀ n, (run n flaggedOverUnflagged s).1 ≠ .skip ∧
      traceAt n flaggedOverUnflagged s = [] := by
    intro n
    obtain ⟨h1, -, h3⟩ := flaggedOverUnflagged_inv h0 n _ (Or.inl rfl)
    refine ⟨fun h => ?_, h3⟩
    rw [h] at h1
    rcases h1 with h1 | h1 | ⟨d, -, h1⟩
    · simp [flaggedOverUnflagged] at h1
    · cases h1
    · cases h1
  constructor
  · rintro (h | h)
    · exact absurd h (not_progressViolation_flaggedOverUnflagged h0)
    · exact (obsBeh_of_silent hs b).1 h
  · intro hb; exact Or.inr ((obsBeh_of_silent hs b).2 hb)

/-- The same nest with the flags swapped: `while⁻ x0 = 0 do (while⁺ 1 do skip ;; x0 := 1)`. -/
def unflaggedOverFlagged : Cmd := .loop false x0IsZero (.seq (spin true) (.assign 0 (.num 1)))

/-- Positive example: a *flagged* inner loop that silently iterates is a progress
violation even inside an unflagged outer loop. -/
theorem progressViolation_unflaggedOverFlagged {s : State} (h0 : s 0 = 0) :
    ProgressViolation unflaggedOverFlagged s := by
  have hr : run 2 unflaggedOverFlagged s =
      (.seq (.seq (spin true) (.assign 0 (.num 1))) unflaggedOverFlagged, s, []) := by
    simp [run, step, unflaggedOverFlagged, x0IsZero, Exp.eval, h0]
  refine ⟨2, .num 1, .skip, ?_, ?_⟩
  · rw [hr]; rfl
  · rw [hr]; exact silentlyIterates_spin s

/-! ### Refinement -/

/-- Positive example: refinement is reflexive. -/
theorem refines_refl (sem : Cmd → State → Beh → Prop) (c : Cmd) : Refines sem c c :=
  fun _ _ h => h

/-- Negative example: adding an output is not a refinement. -/
theorem refines_example_neg : ¬ Refines ObsBeh .skip (.emit (.num 1)) := by
  intro h
  have := h (fun _ => 0) (.term [1]) ((obsBeh_emit _ _ _).2 (by simp [Exp.eval]))
  rw [obsBeh_skip] at this; simp at this

/-! ### Dead variables -/

/-- Positive example: variable `1` is dead at the entry of `emit x0`. -/
theorem deadAtEntry_example : DeadAtEntry [1] (.emit (.var 0)) := by
  intro s₁ s₂ h b
  rw [obsBeh_emit, obsBeh_emit]
  simp [Exp.eval, h 0 (by decide)]

/-- Negative example: variable `0` is not dead at the entry of `emit x0`. -/
theorem deadAtEntry_example_neg : ¬ DeadAtEntry [0] (.emit (.var 0)) := by
  intro h
  have := (h (fun _ => 0) (State.update (fun _ => 0) 0 1)
    (by intro y hy; simp [State.update]; intro e; subst e; simp at hy) (.term [0])).1
    ((obsBeh_emit _ _ _).2 rfl)
  rw [obsBeh_emit] at this
  simp [Exp.eval, State.update] at this

/-- Every variable set is dead at the entry of `skip`. -/
theorem deadAtEntry_skip (X : List Var) : DeadAtEntry X .skip := by
  intro s₁ s₂ _ b
  rw [obsBeh_skip, obsBeh_skip]

/-! ### Reachable loop-entry states -/

/-- Positive example: the state after `x0 := 0` is reachable. -/
theorem reachableAt_example (s : State) :
    ReachableAt (.assign 0 (.num 0)) (State.update s 0 0) :=
  ⟨s, [], 1, rfl⟩

theorem reachableAt_assign_zero {s₁ : State} (h : ReachableAt (.assign 0 (.num 0)) s₁) :
    s₁ 0 = 0 := by
  obtain ⟨s₀, t, ht⟩ := h
  have := (termsWith_unique ht (⟨1, rfl⟩ : TermsWith (.assign 0 (.num 0)) s₀ []
    (State.update s₀ 0 0))).2
  subst this
  simp [State.update]

/-- Negative example: no state with `x0 = 1` is reachable after `x0 := 0`. -/
theorem reachableAt_example_neg : ¬ ReachableAt (.assign 0 (.num 0)) (fun _ => 1) := by
  intro h
  have := reachableAt_assign_zero h
  simp at this

/-- Negative example: nothing is reachable after a diverging prefix. -/
theorem reachableAt_spin_neg (s₁ : State) : ¬ ReachableAt (spin false) s₁ := by
  rintro ⟨s₀, t, ht⟩
  exact not_terminates_spin false s₀ ⟨t, s₁, ht⟩

end Toy.Progress
