import Toy.Progress.RunLemmas

/-!
# Big-step characterizations of runs

Proof infrastructure for the main results. Terminating runs are characterized by a
big-step relation `BigStep`, finite execution prefixes by `Partial`, and the observable
behaviours of a command are shown to be determined by two sets: the traces of its
terminating runs and the traces it reaches after finitely many steps (`Reach`).
-/

namespace Toy.Progress

/-! ## Terminating runs as a big-step relation -/

/-- Big-step semantics of terminating runs: `BigStep c s t s'` iff `c` run from `s`
terminates in `s'` having emitted `t` (`termsWith_iff_bigStep`). -/
inductive BigStep : Cmd → State → List Val → State → Prop
  | skip (s : State) : BigStep .skip s [] s
  | assign (x : Var) (e : Exp) (s : State) : BigStep (.assign x e) s [] (State.update s x (e.eval s))
  | emit (e : Exp) (s : State) : BigStep (.emit e) s [e.eval s] s
  | seq {c₁ c₂ : Cmd} {s s₁ s₂ : State} {t₁ t₂ : List Val} :
      BigStep c₁ s t₁ s₁ → BigStep c₂ s₁ t₂ s₂ → BigStep (.seq c₁ c₂) s (t₁ ++ t₂) s₂
  | iteT {b : Exp} {c₁ c₂ : Cmd} {s s' : State} {t : List Val} :
      b.eval s ≠ 0 → BigStep c₁ s t s' → BigStep (.ite b c₁ c₂) s t s'
  | iteF {b : Exp} {c₁ c₂ : Cmd} {s s' : State} {t : List Val} :
      b.eval s = 0 → BigStep c₂ s t s' → BigStep (.ite b c₁ c₂) s t s'
  | loopExit {mp : Bool} {b : Exp} {body : Cmd} {s : State} :
      b.eval s = 0 → BigStep (.loop mp b body) s [] s
  | loopIter {mp : Bool} {b : Exp} {body : Cmd} {s s₁ s₂ : State} {t₁ t₂ : List Val} :
      b.eval s ≠ 0 → BigStep body s t₁ s₁ → BigStep (.loop mp b body) s₁ t₂ s₂ →
      BigStep (.loop mp b body) s (t₁ ++ t₂) s₂

theorem termsWith_of_bigStep {c : Cmd} {s s' : State} {t : List Val}
    (h : BigStep c s t s') : TermsWith c s t s' := by
  induction h with
  | skip s => exact termsWith_skip s
  | assign x e s => exact termsWith_assign x e s
  | emit e s => exact termsWith_emit e s
  | seq _ _ ih₁ ih₂ => exact termsWith_seq ih₁ ih₂
  | iteT hb _ ih => exact termsWith_ite_true hb ih
  | iteF hb _ ih => exact termsWith_ite_false hb ih
  | loopExit hb => exact termsWith_loop_exit hb
  | loopIter hb _ _ ih₁ ih₂ => exact termsWith_loop_iter hb ih₁ ih₂

theorem bigStep_skip_inv {s s' : State} {t : List Val} (h : BigStep .skip s t s') :
    t = [] ∧ s' = s := by
  cases h; exact ⟨rfl, rfl⟩

/-- Expansion: a big-step run of the successor configuration extends backwards over a
small step. -/
theorem bigStep_of_step {c c' : Cmd} {s s' s'' : State} {o t : List Val}
    (hs : step c s = some (c', s', o)) (h : BigStep c' s' t s'') :
    BigStep c s (o ++ t) s'' := by
  induction c generalizing c' s s' s'' o t with
  | skip => simp [step] at hs
  | assign x e =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    obtain ⟨rfl, rfl⟩ := bigStep_skip_inv h
    exact .assign x e _
  | emit e =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    obtain ⟨rfl, rfl⟩ := bigStep_skip_inv h
    exact .emit e _
  | seq c₁ c₂ ih₁ _ =>
    simp only [step] at hs
    cases h₁ : step c₁ s with
    | none =>
      rw [h₁] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      have hc : c₁ = .skip := (step_eq_none_iff c₁ s).1 h₁
      subst hc
      simpa using BigStep.seq (.skip _) h
    | some r =>
      obtain ⟨c₁', s₁, o₁⟩ := r
      rw [h₁] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      cases h with
      | seq ha hb =>
        have := BigStep.seq (ih₁ h₁ ha) hb
        simpa [List.append_assoc] using this
  | ite b c₁ c₂ _ _ =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    by_cases hb : b.eval s = 0
    · simp only [hb, ↓reduceIte] at h; exact .iteF hb h
    · simp only [hb, ↓reduceIte] at h; exact .iteT hb h
  | loop mp b body _ =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    cases h with
    | iteT hb h =>
      cases h with
      | seq ha hl => simpa using BigStep.loopIter hb ha hl
    | iteF hb h =>
      obtain ⟨rfl, rfl⟩ := bigStep_skip_inv h
      simpa using (BigStep.loopExit (mp := mp) (body := body) hb)

theorem bigStep_of_run {n : Nat} {c : Cmd} {s s' : State} {t : List Val}
    (h : run n c s = (.skip, s', t)) : BigStep c s t s' := by
  induction n generalizing c s t with
  | zero =>
    simp only [run_zero, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .skip _
  | succ n ih =>
    cases hs : step c s with
    | none =>
      have hc : c = .skip := (step_eq_none_iff c s).1 hs
      subst hc
      rw [run_skip] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact .skip _
    | some r =>
      obtain ⟨c', s₁, o⟩ := r
      rw [run_succ_of_step n hs] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := ih (c := c') (s := s₁) (t := (run n c' s₁).2.2) (by rw [← h1, ← h2])
      rw [← h3]
      exact bigStep_of_step hs this

theorem termsWith_iff_bigStep {c : Cmd} {s s' : State} {t : List Val} :
    TermsWith c s t s' ↔ BigStep c s t s' :=
  ⟨fun ⟨_, h⟩ => bigStep_of_run h, termsWith_of_bigStep⟩

theorem bigStep_det {c : Cmd} {s s₁ s₂ : State} {t₁ t₂ : List Val}
    (h₁ : BigStep c s t₁ s₁) (h₂ : BigStep c s t₂ s₂) : t₁ = t₂ ∧ s₁ = s₂ :=
  termsWith_unique (termsWith_of_bigStep h₁) (termsWith_of_bigStep h₂)

/-- A big-step run changes only variables the command may write. -/
theorem bigStep_agreeOff {c : Cmd} {s s' : State} {t : List Val} (h : BigStep c s t s') :
    AgreeOff c.writes s s' := by
  induction h with
  | skip => intro y _; rfl
  | assign x e s =>
    intro y hy
    simp only [Cmd.writes, List.mem_singleton] at hy
    simp [State.update, hy]
  | emit => intro y _; rfl
  | seq _ _ ih₁ ih₂ =>
    intro y hy
    simp only [Cmd.writes, List.mem_append, not_or] at hy
    rw [ih₁ y hy.1, ih₂ y hy.2]
  | iteT _ _ ih =>
    intro y hy
    simp only [Cmd.writes, List.mem_append, not_or] at hy
    exact ih y hy.1
  | iteF _ _ ih =>
    intro y hy
    simp only [Cmd.writes, List.mem_append, not_or] at hy
    exact ih y hy.2
  | loopExit => intro y _; rfl
  | loopIter _ _ _ ih₁ ih₂ =>
    intro y hy
    rw [ih₁ y hy, ih₂ y hy]

/-- An emit-free command emits nothing on a terminating run. -/
theorem bigStep_emitFree {c : Cmd} {s s' : State} {t : List Val} (h : BigStep c s t s')
    (hE : EmitFree c) : t = [] := by
  induction h with
  | skip | assign | loopExit => rfl
  | emit => simp [EmitFree, Cmd.noEmit] at hE
  | seq _ _ ih₁ ih₂ =>
    simp only [EmitFree, Cmd.noEmit, Bool.and_eq_true] at hE
    rw [ih₁ hE.1, ih₂ hE.2]; rfl
  | iteT _ _ ih =>
    simp only [EmitFree, Cmd.noEmit, Bool.and_eq_true] at hE
    exact ih hE.1
  | iteF _ _ ih =>
    simp only [EmitFree, Cmd.noEmit, Bool.and_eq_true] at hE
    exact ih hE.2
  | loopIter _ _ _ ih₁ ih₂ =>
    rw [ih₁ hE, ih₂ hE]; rfl

/-! ## Running a sequence -/

/-- Running `c₁ ;; c₂` follows the run of `c₁` step for step. -/
theorem run_seq_lift (c₂ : Cmd) :
    ∀ n c₁ s, ∃ m, run m (.seq c₁ c₂) s =
      (.seq (run n c₁ s).1 c₂, (run n c₁ s).2.1, (run n c₁ s).2.2) := by
  intro n
  induction n with
  | zero => intro c₁ s; exact ⟨0, rfl⟩
  | succ n ih =>
    intro c₁ s
    cases hs : step c₁ s with
    | none =>
      have hc : c₁ = .skip := (step_eq_none_iff c₁ s).1 hs
      subst hc
      exact ⟨0, by rw [run_skip]; rfl⟩
    | some r =>
      obtain ⟨c₁', s₁, o₁⟩ := r
      obtain ⟨m, hm⟩ := ih c₁' s₁
      refine ⟨m + 1, ?_⟩
      have hstep : step (.seq c₁ c₂) s = some (.seq c₁' c₂, s₁, o₁) := by simp [step, hs]
      rw [run_succ_of_step m hstep, hm, run_succ_of_step n hs]

/-- After a terminating run of `c₁`, the sequence `c₁ ;; c₂` reaches `c₂`. -/
theorem run_seq_of_bigStep {c₁ : Cmd} (c₂ : Cmd) {s s₁ : State} {t₁ : List Val}
    (h : BigStep c₁ s t₁ s₁) : ∃ m, run m (.seq c₁ c₂) s = (c₂, s₁, t₁) := by
  obtain ⟨n, hn⟩ := termsWith_of_bigStep h
  obtain ⟨m, hm⟩ := run_seq_lift c₂ n c₁ s
  rw [hn] at hm
  refine ⟨m + 1, ?_⟩
  rw [run_add, hm]
  simp [run, step]

/-- Composing a run prefix with a terminating run of the reached configuration. -/
theorem termsWith_of_run {m : Nat} {c c' : Cmd} {s s' s'' : State} {t t' : List Val}
    (h : run m c s = (c', s', t)) (h' : TermsWith c' s' t' s'') :
    TermsWith c s (t ++ t') s'' := by
  obtain ⟨n, hn⟩ := h'
  exact ⟨m + n, by rw [run_add, h]; simp [hn]⟩

theorem terminates_iff_of_run {m : Nat} {c c' : Cmd} {s s' : State} {t : List Val}
    (h : run m c s = (c', s', t)) : Terminates c s ↔ Terminates c' s' := by
  constructor
  · rintro ⟨t₁, s₁, n, hn⟩
    rcases Nat.le_total n m with hnm | hmn
    · have := run_of_run_skip hn hnm
      rw [h] at this
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl, rfl⟩ := this
      exact ⟨[], _, termsWith_skip _⟩
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [run_add, h] at hn
      have h1 : (run d c' s').1 = .skip := congrArg Prod.fst hn
      exact ⟨_, _, d, Prod.ext h1 rfl⟩
  · rintro ⟨t₁, s₁, h₁⟩
    exact ⟨_, _, termsWith_of_run h h₁⟩

theorem diverges_iff_not_terminates (c : Cmd) (s : State) : Diverges c s ↔ ¬ Terminates c s := by
  constructor
  · rintro hd ⟨t, s', n, hn⟩
    exact hd n (by simp [hn])
  · intro hnt n hn
    exact hnt ⟨(run n c s).2.2, (run n c s).2.1, n, Prod.ext hn rfl⟩

/-! ## Finite execution prefixes -/

/-- `Reach c s t`: after finitely many steps from `(c, s)` the emitted output is `t`. -/
def Reach (c : Cmd) (s : State) (t : List Val) : Prop := ∃ n, traceAt n c s = t

/-- Finite execution prefixes, structurally: `Partial c s t` iff `Reach c s t`
(`reach_iff_partial`). -/
inductive Partial : Cmd → State → List Val → Prop
  | nil (c : Cmd) (s : State) : Partial c s []
  | emit (e : Exp) (s : State) : Partial (.emit e) s [e.eval s]
  | seqL {c₁ c₂ : Cmd} {s : State} {t : List Val} : Partial c₁ s t → Partial (.seq c₁ c₂) s t
  | seqR {c₁ c₂ : Cmd} {s s₁ : State} {t₁ t₂ : List Val} :
      BigStep c₁ s t₁ s₁ → Partial c₂ s₁ t₂ → Partial (.seq c₁ c₂) s (t₁ ++ t₂)
  | iteT {b : Exp} {c₁ c₂ : Cmd} {s : State} {t : List Val} :
      b.eval s ≠ 0 → Partial c₁ s t → Partial (.ite b c₁ c₂) s t
  | iteF {b : Exp} {c₁ c₂ : Cmd} {s : State} {t : List Val} :
      b.eval s = 0 → Partial c₂ s t → Partial (.ite b c₁ c₂) s t
  | loopBody {mp : Bool} {b : Exp} {body : Cmd} {s : State} {t : List Val} :
      b.eval s ≠ 0 → Partial body s t → Partial (.loop mp b body) s t
  | loopIter {mp : Bool} {b : Exp} {body : Cmd} {s s₁ : State} {t₁ t₂ : List Val} :
      b.eval s ≠ 0 → BigStep body s t₁ s₁ → Partial (.loop mp b body) s₁ t₂ →
      Partial (.loop mp b body) s (t₁ ++ t₂)

theorem partial_skip_inv {s : State} {t : List Val} (h : Partial .skip s t) : t = [] := by
  cases h; rfl

theorem partial_of_step {c c' : Cmd} {s s' : State} {o t : List Val}
    (hs : step c s = some (c', s', o)) (h : Partial c' s' t) : Partial c s (o ++ t) := by
  induction c generalizing c' s s' o t with
  | skip => simp [step] at hs
  | assign x e =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    rw [partial_skip_inv h]; exact .nil _ _
  | emit e =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    rw [partial_skip_inv h]; exact .emit e _
  | seq c₁ c₂ ih₁ _ =>
    simp only [step] at hs
    cases h₁ : step c₁ s with
    | none =>
      rw [h₁] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      have hc : c₁ = .skip := (step_eq_none_iff c₁ s).1 h₁
      subst hc
      simpa using Partial.seqR (.skip _) h
    | some r =>
      obtain ⟨c₁', s₁, o₁⟩ := r
      rw [h₁] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      cases h with
      | nil => exact .seqL (by simpa using ih₁ h₁ (.nil _ _))
      | seqL h => exact .seqL (ih₁ h₁ h)
      | seqR ha hb =>
        have := Partial.seqR (c₂ := c₂) (bigStep_of_step h₁ ha) hb
        simpa [List.append_assoc] using this
  | ite b c₁ c₂ _ _ =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    by_cases hb : b.eval s = 0
    · simp only [hb, ↓reduceIte] at h; exact .iteF hb h
    · simp only [hb, ↓reduceIte] at h; exact .iteT hb h
  | loop mp b body _ =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    cases h with
    | nil => exact .nil _ _
    | iteT hb h =>
      cases h with
      | nil => exact .nil _ _
      | seqL h => simpa using Partial.loopBody (mp := mp) hb h
      | seqR ha hl => simpa using Partial.loopIter hb ha hl
    | iteF hb h =>
      rw [partial_skip_inv h]; exact .nil _ _

theorem partial_of_reach {c : Cmd} {s : State} {t : List Val} (h : Reach c s t) :
    Partial c s t := by
  obtain ⟨n, rfl⟩ := h
  induction n generalizing c s with
  | zero => exact .nil _ _
  | succ n ih =>
    cases hs : step c s with
    | none =>
      have hc : c = .skip := (step_eq_none_iff c s).1 hs
      subst hc
      simp only [traceAt, run_skip]; exact .nil _ _
    | some r =>
      obtain ⟨c', s', o⟩ := r
      simp only [traceAt, run_succ_of_step n hs]
      exact partial_of_step hs (ih (c := c') (s := s'))

theorem reach_nil (c : Cmd) (s : State) : Reach c s [] := ⟨0, rfl⟩

theorem reach_of_step {c c' : Cmd} {s s' : State} {o t : List Val}
    (hs : step c s = some (c', s', o)) (h : Reach c' s' t) : Reach c s (o ++ t) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n + 1, by simp [traceAt, run_succ_of_step n hs]⟩

theorem reach_of_run {m : Nat} {c c' : Cmd} {s s' : State} {t₀ t : List Val}
    (hr : run m c s = (c', s', t₀)) (h : Reach c' s' t) : Reach c s (t₀ ++ t) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨m + n, by simp [traceAt, run_add, hr]⟩

theorem reach_seqL {c₁ : Cmd} (c₂ : Cmd) {s : State} {t : List Val} (h : Reach c₁ s t) :
    Reach (.seq c₁ c₂) s t := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨m, hm⟩ := run_seq_lift c₂ n c₁ s
  exact ⟨m, by simp [traceAt, hm]⟩

theorem reach_seqR {c₁ c₂ : Cmd} {s s₁ : State} {t₁ t₂ : List Val} (h₁ : BigStep c₁ s t₁ s₁)
    (h₂ : Reach c₂ s₁ t₂) : Reach (.seq c₁ c₂) s (t₁ ++ t₂) := by
  obtain ⟨m, hm⟩ := run_seq_of_bigStep c₂ h₁
  exact reach_of_run hm h₂

theorem reach_of_partial {c : Cmd} {s : State} {t : List Val} (h : Partial c s t) :
    Reach c s t := by
  induction h with
  | nil c s => exact reach_nil c s
  | emit e s => exact ⟨1, rfl⟩
  | seqL _ ih => exact reach_seqL _ ih
  | seqR h₁ _ ih => exact reach_seqR h₁ ih
  | @iteT b c₁ c₂ s t hb _ ih =>
    simpa using reach_of_step (c := .ite b c₁ c₂) (s' := s) (o := []) (by simp [step, hb]) ih
  | @iteF b c₁ c₂ s t hb _ ih =>
    simpa using reach_of_step (c := .ite b c₁ c₂) (s' := s) (o := []) (by simp [step, hb]) ih
  | @loopBody mp b body s t hb _ ih =>
    have h1 := reach_seqL (.loop mp b body) ih
    have h2 := reach_of_step (c := .ite b (.seq body (.loop mp b body)) .skip) (s := s) (s' := s)
      (o := []) (by simp [step, hb]) h1
    simpa using reach_of_step (c := .loop mp b body) (s := s) (s' := s) (o := []) (by simp [step]) h2
  | @loopIter mp b body s s₁ t₁ t₂ hb h₁ _ ih =>
    have h1 := reach_seqR h₁ ih
    have h2 := reach_of_step (c := .ite b (.seq body (.loop mp b body)) .skip) (s := s) (s' := s)
      (o := []) (by simp [step, hb]) h1
    simpa using reach_of_step (c := .loop mp b body) (s := s) (s' := s) (o := []) (by simp [step]) h2

theorem reach_iff_partial {c : Cmd} {s : State} {t : List Val} : Reach c s t ↔ Partial c s t :=
  ⟨partial_of_reach, reach_of_partial⟩

/-! ## Reached traces form a prefix chain, closed under prefixes -/

theorem step_output_length {c c' : Cmd} {s s' : State} {o : List Val}
    (hs : step c s = some (c', s', o)) : o.length ≤ 1 := by
  induction c generalizing c' s' o with
  | skip => simp [step] at hs
  | assign | emit | ite | loop =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, -, rfl⟩ := hs; simp
  | seq c₁ c₂ ih₁ _ =>
    simp only [step] at hs
    cases h₁ : step c₁ s with
    | none =>
      rw [h₁] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, -, rfl⟩ := hs; simp
    | some r =>
      obtain ⟨c₁', s₁, o₁⟩ := r
      rw [h₁] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, -, rfl⟩ := hs; exact ih₁ h₁

theorem traceAt_succ (n : Nat) (c : Cmd) (s : State) :
    ∃ d, traceAt (n + 1) c s = traceAt n c s ++ d ∧ d.length ≤ 1 := by
  refine ⟨(run 1 (run n c s).1 (run n c s).2.1).2.2, by simp [traceAt, run_add], ?_⟩
  cases hs : step (run n c s).1 (run n c s).2.1 with
  | none =>
    have := (step_eq_none_iff _ _).1 hs
    rw [this, run_skip]; simp
  | some r =>
    obtain ⟨c', s', o⟩ := r
    rw [run_succ_of_step 0 hs]
    simpa [run_zero] using step_output_length hs

theorem reach_chain {c : Cmd} {s : State} {u v : List Val} (hu : Reach c s u)
    (hv : Reach c s v) : u <+: v ∨ v <+: u := by
  obtain ⟨m, rfl⟩ := hu
  obtain ⟨n, rfl⟩ := hv
  rcases Nat.le_total m n with h | h
  · obtain ⟨d, hd⟩ := traceAt_prefix c s h
    exact Or.inl ⟨d, hd.symm⟩
  · obtain ⟨d, hd⟩ := traceAt_prefix c s h
    exact Or.inr ⟨d, hd.symm⟩

theorem reach_of_prefix {c : Cmd} {s : State} {u v : List Val} (hv : Reach c s v)
    (huv : u <+: v) : Reach c s u := by
  obtain ⟨n, rfl⟩ := hv
  induction n generalizing u with
  | zero =>
    simp only [traceAt, run_zero, List.prefix_nil] at huv
    subst huv; exact reach_nil c s
  | succ n ih =>
    obtain ⟨d, hd, hlen⟩ := traceAt_succ n c s
    rw [hd] at huv
    by_cases hl : u.length ≤ (traceAt n c s).length
    · exact ih (List.prefix_of_prefix_length_le huv (List.prefix_append _ _) hl)
    · have hl2 := huv.length_le
      simp only [List.length_append] at hl2
      have : u = traceAt n c s ++ d := huv.eq_of_length (by simp; omega)
      exact ⟨n + 1, by rw [hd, this]⟩

theorem reach_le_of_bigStep {c : Cmd} {s s' : State} {t u : List Val}
    (h : BigStep c s t s') (hu : Reach c s u) : u <+: t := by
  obtain ⟨m, hm⟩ := termsWith_of_bigStep h
  have ht : Reach c s t := ⟨m, by simp [traceAt, hm]⟩
  rcases reach_chain hu ht with h1 | h1
  · exact h1
  · obtain ⟨n, rfl⟩ := hu
    have := length_traceAt_le_of_run_skip hm n
    exact (h1.eq_of_length (Nat.le_antisymm h1.length_le this)) ▸ List.prefix_refl _


/-! ## Observable behaviours are determined by terminating and reached traces -/

theorem obsBeh_term_iff {c : Cmd} {s : State} {t : List Val} :
    ObsBeh c s (.term t) ↔ ∃ s', BigStep c s t s' := by
  simp only [ObsBeh, termsWith_iff_bigStep]

theorem obsBeh_div_iff {c : Cmd} {s : State} {t : List Val} :
    ObsBeh c s (.div t) ↔ ¬ Terminates c s ∧ Reach c s t ∧ ∀ u, Reach c s u → u <+: t := by
  simp only [ObsBeh, diverges_iff_not_terminates]
  constructor
  · rintro ⟨hnt, N, hN⟩
    refine ⟨hnt, ⟨N, hN N (Nat.le_refl N)⟩, ?_⟩
    rintro u ⟨m, rfl⟩
    rcases Nat.le_total m N with h | h
    · obtain ⟨d, hd⟩ := traceAt_prefix c s h
      rw [← hN N (Nat.le_refl N), hd]; exact List.prefix_append _ _
    · rw [hN m h]; exact List.prefix_refl _
  · rintro ⟨hnt, ⟨N, hN⟩, hmax⟩
    refine ⟨hnt, N, fun n hn => ?_⟩
    obtain ⟨d, hd⟩ := traceAt_prefix c s hn
    have h1 := hmax _ ⟨n, rfl⟩
    rw [hd, hN] at h1 ⊢
    exact (h1.eq_of_length (Nat.le_antisymm h1.length_le (by simp))).symm ▸ rfl

theorem obsBeh_react_iff {c : Cmd} {s : State} {f : Nat → Val} :
    ObsBeh c s (.react f) ↔ ∀ k, Reach c s (prefixOf f k) := Iff.rfl

theorem terminates_iff_bigStep {c : Cmd} {s : State} :
    Terminates c s ↔ ∃ t s', BigStep c s t s' := by
  simp only [Terminates, termsWith_iff_bigStep]

/-- Two runs with the same terminating traces and the same reached traces have the same
observable behaviours. -/
theorem obsBeh_congr {c c' : Cmd} {s s' : State}
    (hT : ∀ t, (∃ s₁, BigStep c s t s₁) ↔ (∃ s₁, BigStep c' s' t s₁))
    (hR : ∀ t, Reach c s t ↔ Reach c' s' t) : ∀ b, ObsBeh c s b ↔ ObsBeh c' s' b := by
  have hTerm : Terminates c s ↔ Terminates c' s' := by
    simp only [terminates_iff_bigStep]
    exact ⟨fun ⟨t, h⟩ => ⟨t, (hT t).1 h⟩, fun ⟨t, h⟩ => ⟨t, (hT t).2 h⟩⟩
  intro b
  cases b with
  | term t => simp only [obsBeh_term_iff]; exact hT t
  | div t =>
    simp only [obsBeh_div_iff, hTerm, hR]
  | react f => simp only [obsBeh_react_iff, hR]

theorem exists_max_of_bounded {c : Cmd} {s : State} :
    ∀ K, (∀ u, Reach c s u → u.length ≤ K) → ∃ t, Reach c s t ∧ ∀ u, Reach c s u → u <+: t := by
  intro K
  induction K with
  | zero =>
    intro hK
    refine ⟨[], reach_nil c s, fun u hu => ?_⟩
    have := hK u hu
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 this)]; exact List.prefix_refl _
  | succ K ih =>
    intro hK
    by_cases hex : ∃ u, Reach c s u ∧ u.length = K + 1
    · obtain ⟨u, hu, hl⟩ := hex
      refine ⟨u, hu, fun v hv => ?_⟩
      rcases reach_chain hv hu with h | h
      · exact h
      · have := hK v hv
        rw [h.eq_of_length (by have := h.length_le; omega)]; exact List.prefix_refl _
    · refine ih fun u hu => ?_
      have := hK u hu
      have : u.length ≠ K + 1 := fun h => hex ⟨u, hu, h⟩
      omega

theorem silentlyDiverges_iff_bounded {c : Cmd} {s : State} :
    SilentlyDiverges c s ↔ ¬ Terminates c s ∧ ∃ K, ∀ u, Reach c s u → u.length ≤ K := by
  constructor
  · rintro ⟨t, ht⟩
    rw [obsBeh_div_iff] at ht
    exact ⟨ht.1, t.length, fun u hu => (ht.2.2 u hu).length_le⟩
  · rintro ⟨hnt, K, hK⟩
    obtain ⟨t, ht, hmax⟩ := exists_max_of_bounded K hK
    exact ⟨t, obsBeh_div_iff.2 ⟨hnt, ht, hmax⟩⟩

theorem length_prefixOf' (f : Nat → Val) (k : Nat) : (prefixOf f k).length = k := by
  simp [prefixOf]

theorem getElem_prefixOf (f : Nat → Val) (k i : Nat) (h : i < (prefixOf f k).length) :
    (prefixOf f k)[i] = f i := by
  simp [prefixOf]

theorem eq_of_reach_of_length_eq {c : Cmd} {s : State} {u v : List Val} (hu : Reach c s u)
    (hv : Reach c s v) (hl : u.length = v.length) : u = v := by
  rcases reach_chain hu hv with h | h
  · exact h.eq_of_length hl
  · exact (h.eq_of_length hl.symm).symm

theorem not_reach_react_of_bounded {c : Cmd} {s : State} {t : List Val} {f : Nat → Val}
    (hb : ∀ u, Reach c s u → u <+: t) : ¬ ObsBeh c s (.react f) := by
  intro h
  have := (hb _ (h (t.length + 1))).length_le
  rw [length_prefixOf'] at this
  omega

/-- The language is deterministic: a run has at most one observable behaviour. -/
theorem obsBeh_unique {c : Cmd} {s : State} {b₁ b₂ : Beh} (h₁ : ObsBeh c s b₁)
    (h₂ : ObsBeh c s b₂) : b₁ = b₂ := by
  cases b₁ with
  | term t₁ =>
    rw [obsBeh_term_iff] at h₁
    obtain ⟨s₁, h₁⟩ := h₁
    cases b₂ with
    | term t₂ =>
      obtain ⟨s₂, h₂⟩ := obsBeh_term_iff.1 h₂
      rw [(bigStep_det h₁ h₂).1]
    | div t₂ =>
      exact absurd ⟨t₁, s₁, termsWith_of_bigStep h₁⟩ (obsBeh_div_iff.1 h₂).1
    | react f =>
      exact absurd h₂ (not_reach_react_of_bounded fun u hu => reach_le_of_bigStep h₁ hu)
  | div t₁ =>
    rw [obsBeh_div_iff] at h₁
    cases b₂ with
    | term t₂ =>
      obtain ⟨s₂, h₂⟩ := obsBeh_term_iff.1 h₂
      exact absurd ⟨t₂, s₂, termsWith_of_bigStep h₂⟩ h₁.1
    | div t₂ =>
      rw [obsBeh_div_iff] at h₂
      rw [eq_of_reach_of_length_eq h₁.2.1 h₂.2.1
        (Nat.le_antisymm (h₂.2.2 _ h₁.2.1).length_le (h₁.2.2 _ h₂.2.1).length_le)]
    | react f => exact absurd h₂ (not_reach_react_of_bounded h₁.2.2)
  | react f =>
    cases b₂ with
    | term t₂ =>
      obtain ⟨s₂, h₂⟩ := obsBeh_term_iff.1 h₂
      exact absurd h₁ (not_reach_react_of_bounded fun u hu => reach_le_of_bigStep h₂ hu)
    | div t₂ => exact absurd h₁ (not_reach_react_of_bounded (obsBeh_div_iff.1 h₂).2.2)
    | react g =>
      congr 1
      funext i
      have he := eq_of_reach_of_length_eq (h₁ (i + 1)) (h₂ (i + 1))
        (by rw [length_prefixOf', length_prefixOf'])
      have := congrArg (fun l => l[i]?) he
      simpa [prefixOf] using this

/-- Every run has an observable behaviour. -/
theorem obsBeh_exists (c : Cmd) (s : State) : ∃ b, ObsBeh c s b := by
  by_cases ht : Terminates c s
  · obtain ⟨t, s', h⟩ := ht
    exact ⟨.term t, s', h⟩
  · by_cases hb : ∃ K, ∀ u, Reach c s u → u.length ≤ K
    · obtain ⟨t, ht'⟩ := silentlyDiverges_iff_bounded.2 ⟨ht, hb⟩
      exact ⟨.div t, ht'⟩
    · have hunb : ∀ i, ∃ u, Reach c s u ∧ i < u.length := by
        intro i
        refine Classical.byContradiction fun hne => hb ⟨i, fun u hu => ?_⟩
        exact Nat.le_of_not_lt fun hl => hne ⟨u, hu, hl⟩
      let f : Nat → Val := fun i =>
        (Classical.choose (hunb i))[i]'(Classical.choose_spec (hunb i)).2
      refine ⟨.react f, fun k => ?_⟩
      obtain ⟨u, hu, hl⟩ := hunb k
      have hw : Reach c s (u.take k) := reach_of_prefix hu (List.take_prefix k u)
      have hlen : (u.take k).length = k := by simp; omega
      suffices u.take k = prefixOf f k by rw [← this]; exact hw
      apply List.ext_getElem (by rw [hlen, length_prefixOf'])
      intro i h₁ h₂
      rw [getElem_prefixOf, List.getElem_take]
      have hi : i < u.length := by rw [hlen] at h₁; omega
      have hci := Classical.choose_spec (hunb i)
      show u[i] = (Classical.choose (hunb i))[i]'hci.2
      rcases reach_chain hu hci.1 with h | h
      · exact h.getElem hi
      · exact (h.getElem hci.2).symm

/-- Because the language is deterministic and `ObsBeh` has no undefined behaviour,
divergence-observable refinement is behavioural equivalence. -/
theorem refines_obsBeh_iff_equiv (src tgt : Cmd) :
    Refines ObsBeh src tgt ↔ ∀ s b, ObsBeh src s b ↔ ObsBeh tgt s b := by
  constructor
  · intro h s b
    obtain ⟨b₀, hb₀⟩ := obsBeh_exists tgt s
    have hs := h s b₀ hb₀
    exact ⟨fun hb => (obsBeh_unique hs hb) ▸ hb₀, fun hb => h s b hb⟩
  · intro h s b hb; exact (h s b).2 hb

/-- `t` is a finite prefix of the behaviour `b`. -/
def BehPrefix (t : List Val) : Beh → Prop
  | .term u => t <+: u
  | .div u => t <+: u
  | .react f => t = prefixOf f t.length

theorem reach_of_bigStep {c : Cmd} {s s' : State} {t : List Val} (h : BigStep c s t s') :
    Reach c s t := by
  obtain ⟨m, hm⟩ := termsWith_of_bigStep h
  exact ⟨m, by simp [traceAt, hm]⟩

/-- The reached traces are exactly the finite prefixes of the behaviour. -/
theorem reach_iff_behPrefix {c : Cmd} {s : State} {t : List Val} :
    Reach c s t ↔ ∃ b, ObsBeh c s b ∧ BehPrefix t b := by
  constructor
  · intro hr
    obtain ⟨b, hb⟩ := obsBeh_exists c s
    refine ⟨b, hb, ?_⟩
    cases b with
    | term u =>
      obtain ⟨s₁, h₁⟩ := obsBeh_term_iff.1 hb
      exact reach_le_of_bigStep h₁ hr
    | div u => exact (obsBeh_div_iff.1 hb).2.2 t hr
    | react f =>
      exact eq_of_reach_of_length_eq hr (hb t.length) (by rw [length_prefixOf'])
  · rintro ⟨b, hb, hp⟩
    cases b with
    | term u =>
      obtain ⟨s₁, h₁⟩ := obsBeh_term_iff.1 hb
      exact reach_of_prefix (reach_of_bigStep h₁) hp
    | div u => exact reach_of_prefix (obsBeh_div_iff.1 hb).2.1 hp
    | react f =>
      have : t = prefixOf f t.length := hp
      rw [this]; exact hb _

theorem reach_of_obsBeh_iff {c c' : Cmd} {s s' : State}
    (h : ∀ b, ObsBeh c s b ↔ ObsBeh c' s' b) {t : List Val} (hr : Reach c s t) :
    Reach c' s' t := by
  obtain ⟨b, hb, hp⟩ := reach_iff_behPrefix.1 hr
  exact reach_iff_behPrefix.2 ⟨b, (h b).1 hb, hp⟩

/-! ## Behaviours across a run prefix and across sequencing -/

theorem reach_of_run_inv {m : Nat} {c c' : Cmd} {s s' : State} {t₀ u : List Val}
    (hr : run m c s = (c', s', t₀)) (hu : Reach c s u) :
    u <+: t₀ ∨ ∃ v, Reach c' s' v ∧ u = t₀ ++ v := by
  obtain ⟨n, rfl⟩ := hu
  rcases Nat.le_total n m with h | h
  · obtain ⟨d, hd⟩ := traceAt_prefix c s h
    have : traceAt m c s = t₀ := by simp [traceAt, hr]
    exact Or.inl ⟨d, by rw [← this, hd]⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact Or.inr ⟨traceAt d c' s', ⟨d, rfl⟩, by simp [traceAt, run_add, hr]⟩

theorem silentlyDiverges_iff_of_run {m : Nat} {c c' : Cmd} {s s' : State} {t₀ : List Val}
    (hr : run m c s = (c', s', t₀)) : SilentlyDiverges c s ↔ SilentlyDiverges c' s' := by
  rw [silentlyDiverges_iff_bounded, silentlyDiverges_iff_bounded, terminates_iff_of_run hr]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, fun v hv => by
      have := hK _ (reach_of_run hr hv); simp at this; omega⟩
  · rintro ⟨K, hK⟩
    refine ⟨t₀.length + K, fun u hu => ?_⟩
    rcases reach_of_run_inv hr hu with h | ⟨v, hv, rfl⟩
    · have := h.length_le; omega
    · have := hK v hv; simp; omega

theorem termsWith_iff_of_run {m : Nat} {c c' : Cmd} {s s' s'' : State} {t₀ t : List Val}
    (hr : run m c s = (c', s', t₀)) : TermsWith c s (t₀ ++ t) s'' ↔ TermsWith c' s' t s'' := by
  constructor
  · rintro ⟨n, hn⟩
    rcases Nat.le_total n m with h | h
    · have := run_of_run_skip hn h
      rw [hr] at this
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl, he⟩ := this
      have : t = [] := by simpa using he.symm
      subst this
      exact termsWith_skip _
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [run_add, hr] at hn
      simp only [Prod.mk.injEq, List.append_cancel_left_eq] at hn
      exact ⟨d, Prod.ext hn.1 (Prod.ext hn.2.1 hn.2.2)⟩
  · exact termsWith_of_run hr

/-- A silent run prefix does not change the observable behaviours. -/
theorem obsBeh_of_run_nil {m : Nat} {c c' : Cmd} {s s' : State}
    (hr : run m c s = (c', s', [])) : ∀ b, ObsBeh c s b ↔ ObsBeh c' s' b := by
  apply obsBeh_congr
  · intro t
    simp only [← termsWith_iff_bigStep]
    exact ⟨fun ⟨s₁, h⟩ => ⟨s₁, (termsWith_iff_of_run (t := t) hr).1 (by simpa using h)⟩,
      fun ⟨s₁, h⟩ => ⟨s₁, by simpa using (termsWith_iff_of_run (t := t) hr).2 h⟩⟩
  · intro t
    constructor
    · intro h
      rcases reach_of_run_inv hr h with h | ⟨v, hv, rfl⟩
      · rw [List.prefix_nil.1 h]; exact reach_nil _ _
      · simpa using hv
    · intro h; simpa using reach_of_run hr h

theorem bigStep_seq_inv {c₁ c₂ : Cmd} {s s' : State} {t : List Val}
    (h : BigStep (.seq c₁ c₂) s t s') :
    ∃ t₁ s₁ t₂, BigStep c₁ s t₁ s₁ ∧ BigStep c₂ s₁ t₂ s' ∧ t = t₁ ++ t₂ := by
  cases h with
  | seq h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

theorem partial_seq_inv {c₁ c₂ : Cmd} {s : State} {t : List Val}
    (h : Partial (.seq c₁ c₂) s t) :
    Partial c₁ s t ∨ ∃ t₁ s₁ t₂, BigStep c₁ s t₁ s₁ ∧ Partial c₂ s₁ t₂ ∧ t = t₁ ++ t₂ := by
  cases h with
  | nil => exact Or.inl (.nil _ _)
  | seqL h => exact Or.inl h
  | seqR h₁ h₂ => exact Or.inr ⟨_, _, _, h₁, h₂, rfl⟩

/-- Congruence of sequencing: continuations with the same behaviours from every state
reached by `c₁` give sequences with the same behaviours. -/
theorem obsBeh_seq_congr {c₁ c₂ c₂' : Cmd} {s : State}
    (h : ∀ t₁ s₁, BigStep c₁ s t₁ s₁ → ∀ b, ObsBeh c₂ s₁ b ↔ ObsBeh c₂' s₁ b) :
    ∀ b, ObsBeh (.seq c₁ c₂) s b ↔ ObsBeh (.seq c₁ c₂') s b := by
  have hsym : ∀ t₁ s₁, BigStep c₁ s t₁ s₁ → ∀ b, ObsBeh c₂' s₁ b ↔ ObsBeh c₂ s₁ b :=
    fun t₁ s₁ h₁ b => (h t₁ s₁ h₁ b).symm
  have dir : ∀ d d' : Cmd, (∀ t₁ s₁, BigStep c₁ s t₁ s₁ → ∀ b, ObsBeh d s₁ b ↔ ObsBeh d' s₁ b) →
      (∀ t, (∃ s', BigStep (.seq c₁ d) s t s') → ∃ s', BigStep (.seq c₁ d') s t s') ∧
      (∀ t, Reach (.seq c₁ d) s t → Reach (.seq c₁ d') s t) := by
    intro d d' hd
    refine ⟨fun t ⟨s', hs⟩ => ?_, fun t ht => ?_⟩
    · obtain ⟨t₁, s₁, t₂, h₁, h₂, rfl⟩ := bigStep_seq_inv hs
      obtain ⟨s'', h₂'⟩ := obsBeh_term_iff.1 ((hd t₁ s₁ h₁ (.term t₂)).1 (obsBeh_term_iff.2 ⟨_, h₂⟩))
      exact ⟨s'', .seq h₁ h₂'⟩
    · rcases partial_seq_inv (partial_of_reach ht) with hp | ⟨t₁, s₁, t₂, h₁, h₂, rfl⟩
      · exact reach_seqL _ (reach_of_partial hp)
      · exact reach_seqR h₁ (reach_of_obsBeh_iff (hd t₁ s₁ h₁) (reach_of_partial h₂))
  obtain ⟨hT₁, hR₁⟩ := dir c₂ c₂' h
  obtain ⟨hT₂, hR₂⟩ := dir c₂' c₂ hsym
  exact obsBeh_congr (fun t => ⟨hT₁ t, hT₂ t⟩) (fun t => ⟨hR₁ t, hR₂ t⟩)

/-- After a silent terminating run of `c₁`, the behaviours of `c₁ ;; c₂` are those of
`c₂` from the reached state. -/
theorem obsBeh_seq_of_bigStep_nil {c₁ c₂ : Cmd} {s s₁ : State} (h : BigStep c₁ s [] s₁) :
    ∀ b, ObsBeh (.seq c₁ c₂) s b ↔ ObsBeh c₂ s₁ b := by
  obtain ⟨m, hm⟩ := run_seq_of_bigStep c₂ h
  exact obsBeh_of_run_nil hm

/-- If `c₁` does not terminate, `c₁ ;; c₂` behaves as `c₁`. -/
theorem obsBeh_seq_of_not_terminates {c₁ c₂ : Cmd} {s : State} (h : ¬ Terminates c₁ s) :
    ∀ b, ObsBeh (.seq c₁ c₂) s b ↔ ObsBeh c₁ s b := by
  have hnb : ∀ t s', ¬ BigStep c₁ s t s' := fun t s' hb => h ⟨t, s', termsWith_of_bigStep hb⟩
  apply obsBeh_congr
  · intro t
    exact ⟨fun ⟨_, hs⟩ => by obtain ⟨t₁, s₁, _, h₁, -⟩ := bigStep_seq_inv hs; exact absurd h₁ (hnb _ _),
      fun ⟨_, hs⟩ => absurd hs (hnb _ _)⟩
  · intro t
    constructor
    · intro ht
      rcases partial_seq_inv (partial_of_reach ht) with hp | ⟨_, _, _, h₁, -⟩
      · exact reach_of_partial hp
      · exact absurd h₁ (hnb _ _)
    · exact reach_seqL _

theorem partial_emitFree {c : Cmd} {s : State} {t : List Val} (h : Partial c s t)
    (hE : EmitFree c) : t = [] := by
  induction h with
  | nil => rfl
  | emit => simp [EmitFree, Cmd.noEmit] at hE
  | seqL _ ih =>
    simp only [EmitFree, Cmd.noEmit, Bool.and_eq_true] at hE; exact ih hE.1
  | seqR h₁ _ ih =>
    simp only [EmitFree, Cmd.noEmit, Bool.and_eq_true] at hE
    rw [bigStep_emitFree h₁ hE.1, ih hE.2]; rfl
  | iteT _ _ ih => simp only [EmitFree, Cmd.noEmit, Bool.and_eq_true] at hE; exact ih hE.1
  | iteF _ _ ih => simp only [EmitFree, Cmd.noEmit, Bool.and_eq_true] at hE; exact ih hE.2
  | loopBody _ _ ih => exact ih hE
  | loopIter _ h₁ _ ih =>
    rw [bigStep_emitFree h₁ hE, ih hE]; rfl

/-- A non-terminating emit-free command has the single behaviour `div []`. -/
theorem obsBeh_emitFree_not_terminates {c : Cmd} {s : State} (hE : EmitFree c)
    (h : ¬ Terminates c s) : ∀ b, ObsBeh c s b ↔ b = .div [] := by
  have hd : ObsBeh c s (.div []) := obsBeh_div_iff.2 ⟨h, reach_nil c s, fun u hu => by
    rw [partial_emitFree (partial_of_reach hu) hE]; exact List.prefix_refl _⟩
  intro b
  exact ⟨fun hb => obsBeh_unique hb hd, fun hb => hb ▸ hd⟩

theorem obsBeh_seq_emitFree_not_terminates {c₁ c₂ : Cmd} {s : State} (hE : EmitFree c₁)
    (h : ¬ Terminates c₁ s) : ∀ b, ObsBeh (.seq c₁ c₂) s b ↔ b = .div [] := by
  intro b
  rw [obsBeh_seq_of_not_terminates h]
  exact obsBeh_emitFree_not_terminates hE h b

end Toy.Progress
