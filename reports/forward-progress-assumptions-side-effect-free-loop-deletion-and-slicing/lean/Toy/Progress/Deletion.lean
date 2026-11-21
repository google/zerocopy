import Toy.Progress.Examples

/-!
# Deleting a side-effect-free loop

Programs have the shape `p ;; while b do body ;; k`; deletion replaces it by `p ;; k`.
`p` determines the states in which the loop is entered (`ReachableAt p`).
-/

namespace Toy.Progress

/-! ## Shared helpers -/

theorem not_refines_obs_of_termsWith {src tgt : Cmd} {s s₁ s₂ : State} {t₁ t₂ : List Val}
    (h₁ : TermsWith src s t₁ s₁) (h₂ : TermsWith tgt s t₂ s₂) (hne : t₁ ≠ t₂) :
    ¬ Refines ObsBeh src tgt := by
  intro h
  have := h s (.term t₂) ((obsBeh_of_termsWith h₂ _).2 rfl)
  rw [obsBeh_of_termsWith h₁] at this
  exact hne (by simpa using this.symm)

theorem not_refines_fp_of_termsWith {src tgt : Cmd} {s s₁ s₂ : State} {t₁ t₂ : List Val}
    (h₁ : TermsWith src s t₁ s₁) (h₂ : TermsWith tgt s t₂ s₂) (hne : t₁ ≠ t₂) :
    ¬ Refines FPBeh src tgt := by
  intro h
  rcases h s (.term t₂) (Or.inr ((obsBeh_of_termsWith h₂ _).2 rfl)) with h | h
  · exact not_silentlyDiverges_of_termsWith h₁ h
  · rw [obsBeh_of_termsWith h₁] at h
    exact hne (by simpa using h.symm)

/-- Loop body that emits: `emit 7 ;; x0 := 1`. -/
def emitBody : Cmd := .seq (.emit (.num 7)) (.assign 0 (.num 1))

/-- Emit-free loop body that writes the variable read afterwards: `x0 := 1`. -/
def resetBody : Cmd := .assign 0 (.num 1)

/-- Emit-free loop body whose written variable `x1` is dead before `emit x0`. -/
def countBody : Cmd := .assign 1 (.add (.var 1) (.num 1))

/-- `while x0 = 0 do x1 := x1 + 1` -/
def countLoop : Cmd := .loop false x0IsZero countBody

/-- `countLoop` silently iterates from the all-zero state: `x0` stays `0`. -/
theorem silentlyIterates_countLoop :
    SilentlyIterates x0IsZero countBody (fun _ => 0) := by
  refine ⟨fun i => State.update (fun _ => 0) 1 i, fun _ => [], ?_, fun i => ⟨?_, ?_⟩, 0,
    fun _ _ => rfl⟩
  · funext y; simp [State.update]
  · simp [x0IsZero, Exp.eval, State.update]
  · have := termsWith_assign 1 (.add (.var 1) (.num 1)) (State.update (fun _ => 0) 1 i)
    have he : State.update (State.update (fun _ => 0) 1 i) 1
        ((Exp.add (.var 1) (.num 1)).eval (State.update (fun _ => 0) 1 i)) =
        State.update (fun _ => 0) 1 (i + 1) := by
      funext y; by_cases hy : y = 1 <;> simp [State.update, Exp.eval, hy]
    rw [he] at this
    exact this

/-- `countLoop` does not terminate from the all-zero state. -/
theorem not_terminates_countLoop : ¬ Terminates countLoop (fun _ => 0) :=
  not_terminates_of_silentlyIterates silentlyIterates_countLoop

/-- `DeadAtEntry` implies `DeadAfterPrefix` for every prefix. -/
theorem deadAfterPrefix_of_deadAtEntry (p : Cmd) {X : List Var} {k : Cmd}
    (h : DeadAtEntry X k) : DeadAfterPrefix p X k :=
  fun s₁ s₂ _ ha => h s₁ s₂ ha

/-- `x2 := 1` -/
def setX2 : Cmd := .assign 2 (.num 1)

/-- `if x2 = 0 then emit x1 else emit x0` -/
def guardedEmit : Cmd := .ite (.eq (.var 2) (.num 0)) (.emit (.var 1)) (.emit (.var 0))

/-- Positive example for `DeadAfterPrefix` that is a negative example for `DeadAtEntry`:
after `x2 := 1`, variable `x1` is dead before `if x2 = 0 then emit x1 else emit x0`, but
it is not dead from arbitrary states. -/
theorem deadAfterPrefix_example_not_deadAtEntry :
    ¬ DeadAtEntry countBody.writes guardedEmit ∧ DeadAfterPrefix setX2 countBody.writes guardedEmit := by
  refine ⟨?_, ?_⟩
  · intro hDead
    let s₁ : State := fun _ => 0
    let s₂ : State := State.update s₁ 1 9
    have hAg : AgreeOff countBody.writes s₁ s₂ := by
      intro y hy
      have hy1 : y ≠ 1 := by simpa [countBody, Cmd.writes] using hy
      simp [s₂, State.update, hy1]
    have hb₁ : ObsBeh guardedEmit s₁ (.term [0]) := by
      have ht : TermsWith guardedEmit s₁ [0] s₁ :=
        termsWith_ite_true (by simp [s₁, Exp.eval]) (termsWith_emit (.var 1) s₁)
      exact (obsBeh_of_termsWith ht _).2 rfl
    have hb₂ : TermsWith guardedEmit s₂ [9] s₂ :=
      termsWith_ite_true (by simp [s₂, s₁, State.update, Exp.eval]) (termsWith_emit (.var 1) s₂)
    have := (hDead s₁ s₂ hAg (.term [0])).1 hb₁
    rw [obsBeh_of_termsWith hb₂] at this
    simp at this
  · intro s₁ s₂ ⟨s₀, t, ht⟩ hAg b
    have hs₁ : s₁ = State.update s₀ 2 1 :=
      (termsWith_unique ht (termsWith_assign 2 (.num 1) s₀)).2
    have h2₁ : s₁ 2 = 1 := by simp [hs₁, State.update]
    have h2₂ : s₂ 2 = 1 := by
      rw [← hAg 2 (by simp [countBody, Cmd.writes]), h2₁]
    have h0 : s₁ 0 = s₂ 0 := hAg 0 (by simp [countBody, Cmd.writes])
    have ht₁ : TermsWith guardedEmit s₁ [s₁ 0] s₁ :=
      termsWith_ite_false (by simp [Exp.eval, h2₁]) (termsWith_emit (.var 0) s₁)
    have ht₂ : TermsWith guardedEmit s₂ [s₂ 0] s₂ :=
      termsWith_ite_false (by simp [Exp.eval, h2₂]) (termsWith_emit (.var 0) s₂)
    rw [obsBeh_of_termsWith ht₁, obsBeh_of_termsWith ht₂, h0]

theorem fpBeh_iff_of_obsBeh_iff {c c' : Cmd} {s : State} (h : ∀ b, ObsBeh c s b ↔ ObsBeh c' s b)
    (b : Beh) : FPBeh c s b ↔ FPBeh c' s b := by
  simp only [FPBeh, SilentlyDiverges, h]

/-- At a loop-entry state from which the emit-free loop terminates, and at which the
variables it writes are dead before `k`, running the loop before `k` is invisible. -/
theorem obsBeh_seq_loop_of_terminates {mp : Bool} {b : Exp} {body k : Cmd} {s₁ : State}
    (hEmit : EmitFree body)
    (hDead : ∀ s₂, AgreeOff body.writes s₁ s₂ → ∀ bh, ObsBeh k s₁ bh ↔ ObsBeh k s₂ bh)
    (hT : Terminates (.loop mp b body) s₁) :
    ∀ bh, ObsBeh (.seq (.loop mp b body) k) s₁ bh ↔ ObsBeh k s₁ bh := by
  obtain ⟨t, s₂, h⟩ := terminates_iff_bigStep.1 hT
  have ht : t = [] := bigStep_emitFree h (show EmitFree (.loop mp b body) from hEmit)
  subst ht
  intro bh
  have ha : AgreeOff (Cmd.loop mp b body).writes s₁ s₂ := bigStep_agreeOff h
  rw [obsBeh_seq_of_bigStep_nil h]
  exact (hDead s₂ ha bh).symm

theorem termsWith_loop_x0IsZero (mp : Bool) (body : Cmd) (s₁ s₂ : State) (t : List Val)
    (h0 : s₁ 0 = 0) (hb : TermsWith body s₁ t s₂) (h2 : s₂ 0 ≠ 0) :
    TermsWith (.loop mp x0IsZero body) s₁ t s₂ := by
  have := termsWith_loop_iter (mp := mp) (b := x0IsZero) (by simp [x0IsZero, Exp.eval, h0]) hb
    (termsWith_loop_exit (mp := mp) (body := body) (s := s₂) (by simp [x0IsZero, Exp.eval, h2]))
  simpa using this

/-! ## Result: deletion is unsound when divergence is observable -/

/-- **Deleting `while 1 do skip` before `emit 1` is not a refinement under the
divergence-observable semantics**, for either loop flag `mp`. From every state, the
target `emit 1` terminates emitting `[1]`, while the source silently diverges with empty
trace (`div []`) and never terminates emitting `[1]`; hence no refinement. -/
theorem loopDeletion_spin_not_refines_divergenceObservable (mp : Bool) :
    (∀ s, ObsBeh (.emit (.num 1)) s (.term [1]) ∧
          ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.div []) ∧
          ¬ ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.term [1])) ∧
    ¬ Refines ObsBeh (.seq (spin mp) (.emit (.num 1))) (.emit (.num 1)) := by
  have key : ∀ s, ObsBeh (.emit (.num 1)) s (.term [1]) ∧
      ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.div []) ∧
      ¬ ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.term [1]) := by
    intro s
    refine ⟨(obsBeh_emit _ _ _).2 rfl, (obsBeh_spinSeq _ _ _ _).2 rfl, ?_⟩
    rw [obsBeh_spinSeq]; simp
  exact ⟨key, fun h => (key (fun _ => 0)).2.2 (h _ _ (key (fun _ => 0)).1)⟩

/-- Positive control: the same deletion *is* a refinement under forward progress. -/
theorem loopDeletion_spin_refines_forwardProgress (mp : Bool) :
    Refines FPBeh (.seq (spin mp) (.emit (.num 1))) (.emit (.num 1)) :=
  fun s _ _ => Or.inl (silentlyDiverges_spinSeq mp _ s)

/-! ## Result: deletion is sound under forward progress -/

/-- **Under forward progress, deleting an emit-free loop whose written variables are dead
before the continuation is a refinement**, for every prefix `p`, condition `b`, flag `mp`
and continuation `k`. Deadness is required only in states reachable at the end of `p`
(`DeadAfterPrefix`). No termination hypothesis is needed. -/
theorem deleteEmitFreeLoop_withDeadWrites_refines_forwardProgress
    (p k : Cmd) (mp : Bool) (b : Exp) (body : Cmd)
    (hEmit : EmitFree body) (hDead : DeadAfterPrefix p body.writes k) :
    Refines FPBeh (.seq p (.seq (.loop mp b body) k)) (.seq p k) := by
  have hE : EmitFree (Cmd.loop mp b body) := hEmit
  intro s₀ bh hbh
  by_cases hp : Terminates p s₀
  · obtain ⟨t₁, s₁, h₁⟩ := terminates_iff_bigStep.1 hp
    have hr : ReachableAt p s₁ := ⟨s₀, t₁, termsWith_of_bigStep h₁⟩
    by_cases hL : Terminates (.loop mp b body) s₁
    · have heq := obsBeh_seq_congr (c₁ := p) (c₂ := .seq (.loop mp b body) k) (c₂' := k)
        (s := s₀) (fun t s h => by
          obtain ⟨-, rfl⟩ := bigStep_det h₁ h
          exact obsBeh_seq_loop_of_terminates hEmit (fun s₂ ha => hDead _ s₂ hr ha) hL)
      exact (fpBeh_iff_of_obsBeh_iff heq bh).2 hbh
    · -- The loop silently diverges at `s₁`, so the source silently diverges.
      obtain ⟨m, hm⟩ := run_seq_of_bigStep (.seq (.loop mp b body) k) h₁
      exact Or.inl ((silentlyDiverges_iff_of_run hm).2
        ⟨[], (obsBeh_seq_emitFree_not_terminates hE hL _).2 rfl⟩)
  · have heq : ∀ bh, ObsBeh (.seq p (.seq (.loop mp b body) k)) s₀ bh ↔ ObsBeh (.seq p k) s₀ bh :=
      fun bh => by rw [obsBeh_seq_of_not_terminates hp, obsBeh_seq_of_not_terminates hp]
    exact (fpBeh_iff_of_obsBeh_iff heq bh).2 hbh

/-- Non-vacuity: with `p = skip`, the emit-free body `x1 := x1 + 1` writes only `x1`,
which is dead before `emit x0`; and the loop `while x0 = 0 do x1 := x1 + 1` does not
terminate from the reachable all-zero state, so the deletion removes a loop that can
diverge. -/
theorem deleteLoop_hypotheses_nonvacuous :
    EmitFree countBody ∧ DeadAfterPrefix .skip countBody.writes (.emit (.var 0)) ∧
    ReachableAt .skip (fun _ => 0) ∧ ¬ Terminates countLoop (fun _ => 0) :=
  ⟨by decide, deadAfterPrefix_of_deadAtEntry _ deadAtEntry_example,
    ⟨fun _ => 0, [], termsWith_skip _⟩, not_terminates_countLoop⟩

theorem termsWith_emitBody (s : State) : TermsWith emitBody s [7] (State.update s 0 1) :=
  termsWith_seq (termsWith_emit (.num 7) s) (termsWith_assign 0 (.num 1) s)

theorem termsWith_resetBody (s : State) : TermsWith resetBody s [] (State.update s 0 1) :=
  termsWith_assign 0 (.num 1) s

theorem termsWith_prefix_emitBody (s : State) :
    TermsWith (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero emitBody) .skip)) s
      [7] (State.update (State.update s 0 0) 0 1) := by
  have hL : TermsWith (.loop false x0IsZero emitBody) (State.update s 0 0) [7]
      (State.update (State.update s 0 0) 0 1) :=
    termsWith_loop_x0IsZero false emitBody _ _ [7] (by simp [State.update])
      (termsWith_emitBody _) (by simp [State.update])
  exact termsWith_seq (termsWith_assign 0 (.num 0) s) (termsWith_seq hL (termsWith_skip _))

theorem termsWith_prefix_resetBody (s : State) :
    TermsWith (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero resetBody) (.emit (.var 0))))
      s [1] (State.update (State.update s 0 0) 0 1) := by
  have hL : TermsWith (.loop false x0IsZero resetBody) (State.update s 0 0) []
      (State.update (State.update s 0 0) 0 1) :=
    termsWith_loop_x0IsZero false resetBody _ _ [] (by simp [State.update])
      (termsWith_resetBody _) (by simp [State.update])
  exact termsWith_seq (termsWith_assign 0 (.num 0) s)
    (termsWith_seq hL (termsWith_emit (.var 0) _))

theorem termsWith_prefix_skip (s : State) :
    TermsWith (.seq (.assign 0 (.num 0)) .skip) s [] (State.update s 0 0) :=
  termsWith_seq (termsWith_assign 0 (.num 0) s) (termsWith_skip _)

theorem termsWith_prefix_emit (s : State) :
    TermsWith (.seq (.assign 0 (.num 0)) (.emit (.var 0))) s [0] (State.update s 0 0) :=
  termsWith_seq (termsWith_assign 0 (.num 0) s) (termsWith_emit (.var 0) _)

/-- Counterexample (`hEmit` is needed): with the emitting body `emit 7 ;; x0 := 1`
(written variable `x0` dead before `skip`), deleting the loop after `x0 := 0` drops the
output `7`, so it is not a forward-progress refinement. -/
theorem deleteLoop_forwardProgress_needs_emitFree :
    DeadAfterPrefix (.assign 0 (.num 0)) emitBody.writes .skip ∧
    ¬ Refines FPBeh (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero emitBody) .skip))
        (.seq (.assign 0 (.num 0)) .skip) :=
  ⟨deadAfterPrefix_of_deadAtEntry _ (deadAtEntry_skip _),
    not_refines_fp_of_termsWith (termsWith_prefix_emitBody (fun _ => 0))
    (termsWith_prefix_skip (fun _ => 0)) (by simp)⟩

/-- Counterexample (`hDead` is needed): the emit-free body `x0 := 1` writes `x0`, which
`emit x0` reads; deleting the loop changes the output from `[1]` to `[0]`. -/
theorem deleteLoop_forwardProgress_needs_deadWrites :
    EmitFree resetBody ∧
    ¬ Refines FPBeh
        (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero resetBody) (.emit (.var 0))))
        (.seq (.assign 0 (.num 0)) (.emit (.var 0))) :=
  ⟨by decide, not_refines_fp_of_termsWith (termsWith_prefix_resetBody (fun _ => 0))
    (termsWith_prefix_emit (fun _ => 0)) (by simp)⟩

/-! ## Result: exact condition when divergence is observable -/

/-- **Exact condition for deletion under the divergence-observable semantics.** For an
emit-free loop whose written variables are dead before `k` in every state reachable at
the end of `p`, deleting it from `p ;; loop ;; k` is a refinement iff at every reachable
loop-entry state the loop terminates **or the continuation `k` itself silently diverges
without emitting** (`ObsBeh k s₁ (div [])`). `hEmit` and `hDead` are fixed hypotheses
outside the equivalence. -/
theorem deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff
    (p k : Cmd) (mp : Bool) (b : Exp) (body : Cmd)
    (hEmit : EmitFree body) (hDead : DeadAfterPrefix p body.writes k) :
    Refines ObsBeh (.seq p (.seq (.loop mp b body) k)) (.seq p k) ↔
      ∀ s₁, ReachableAt p s₁ →
        Terminates (.loop mp b body) s₁ ∨ ObsBeh k s₁ (.div []) := by
  have hE : EmitFree (Cmd.loop mp b body) := hEmit
  constructor
  · intro href s₁ ⟨s₀, t₁, ht₁⟩
    by_cases hL : Terminates (.loop mp b body) s₁
    · exact Or.inl hL
    right
    have h₁ := termsWith_iff_bigStep.1 ht₁
    have heqv := (refines_obsBeh_iff_equiv _ _).1 href s₀
    obtain ⟨m, hm⟩ := run_seq_of_bigStep (.seq (.loop mp b body) k) h₁
    have hsrcL := obsBeh_seq_emitFree_not_terminates (c₂ := k) hE hL
    -- From `s₀` the source emits at most `t₁` and never terminates.
    have hRsrc : ∀ u, Reach (.seq p (.seq (.loop mp b body) k)) s₀ u → u <+: t₁ := by
      intro u hu
      rcases reach_of_run_inv hm hu with h | ⟨v, hv, rfl⟩
      · exact h
      · obtain ⟨bv, hbv, hpre⟩ := reach_iff_behPrefix.1 hv
        rw [hsrcL] at hbv
        subst hbv
        rw [List.prefix_nil.1 hpre]; simp
    have hTsrc : ¬ Terminates (.seq p (.seq (.loop mp b body) k)) s₀ := by
      rw [terminates_iff_of_run hm]
      rintro ⟨t, s', ht⟩
      have := (hsrcL (.term t)).1 ⟨s', ht⟩
      cases this
    refine obsBeh_div_iff.2 ⟨?_, reach_nil k s₁, fun v hv => ?_⟩
    · rintro ⟨t₂, s₂, ht₂⟩
      have htgt : ObsBeh (.seq p k) s₀ (.term (t₁ ++ t₂)) :=
        ⟨s₂, termsWith_of_bigStep (.seq h₁ (termsWith_iff_bigStep.1 ht₂))⟩
      obtain ⟨s₃, h₃⟩ := (heqv _).2 htgt
      exact hTsrc ⟨_, _, h₃⟩
    · have h1 : Reach (.seq p k) s₀ (t₁ ++ v) := reach_seqR h₁ hv
      have h2 := hRsrc _ (reach_of_obsBeh_iff (fun b => (heqv b).symm) h1)
      have := h2.length_le
      simp only [List.length_append] at this
      have hv0 : v.length = 0 := by omega
      rw [List.eq_nil_of_length_eq_zero hv0]
      exact List.nil_prefix
  · intro hcond s₀ bh hbh
    refine (obsBeh_seq_congr (c₁ := p) (s := s₀) (fun t₁ s₁ h₁ bh' => ?_) bh).2 hbh
    have hr : ReachableAt p s₁ := ⟨s₀, t₁, termsWith_of_bigStep h₁⟩
    by_cases hL : Terminates (.loop mp b body) s₁
    · exact obsBeh_seq_loop_of_terminates hEmit (fun s₂ ha => hDead s₁ s₂ hr ha) hL bh'
    · have hk := (hcond s₁ hr).resolve_left hL
      rw [obsBeh_seq_emitFree_not_terminates hE hL]
      exact ⟨fun h => h ▸ hk, fun h => obsBeh_unique h hk⟩

theorem loop_x0IsZero_terminates_after_reset (body : Cmd) (s₁ : State)
    (hr : ReachableAt (.assign 0 (.num 0)) s₁)
    (hb : ∀ s, s 0 = 0 → ∃ t, TermsWith body s t (State.update s 0 1)) :
    Terminates (.loop false x0IsZero body) s₁ := by
  have h0 := reachableAt_assign_zero hr
  obtain ⟨t, ht⟩ := hb s₁ h0
  exact ⟨t, _, termsWith_loop_x0IsZero false body s₁ _ t h0 ht (by simp [State.update])⟩

/-- Counterexample (`hEmit` is needed for the characterization): the emitting loop
terminates at every reachable entry, yet deletion is not a refinement. -/
theorem deleteLoop_divergenceObservable_iff_needs_emitFree :
    DeadAfterPrefix (.assign 0 (.num 0)) emitBody.writes .skip ∧
    ¬ (Refines ObsBeh (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero emitBody) .skip))
          (.seq (.assign 0 (.num 0)) .skip) ↔
        ∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ →
          Terminates (.loop false x0IsZero emitBody) s₁ ∨ ObsBeh .skip s₁ (.div [])) := by
  refine ⟨deadAfterPrefix_of_deadAtEntry _ (deadAtEntry_skip _), fun hiff => ?_⟩
  refine not_refines_obs_of_termsWith (termsWith_prefix_emitBody (fun _ => 0))
    (termsWith_prefix_skip (fun _ => 0)) (by simp) (hiff.2 fun s₁ hr => Or.inl ?_)
  exact loop_x0IsZero_terminates_after_reset emitBody s₁ hr fun s _ =>
    ⟨[7], termsWith_emitBody s⟩

/-- Counterexample (`hDead` is needed for the characterization): the emit-free loop
`while x0 = 0 do x0 := 1` terminates at every reachable entry, yet deleting it before
`emit x0` is not a refinement. -/
theorem deleteLoop_divergenceObservable_iff_needs_deadWrites :
    EmitFree resetBody ∧
    ¬ (Refines ObsBeh
          (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero resetBody) (.emit (.var 0))))
          (.seq (.assign 0 (.num 0)) (.emit (.var 0))) ↔
        ∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ →
          Terminates (.loop false x0IsZero resetBody) s₁ ∨
            ObsBeh (.emit (.var 0)) s₁ (.div [])) := by
  refine ⟨by decide, fun hiff => ?_⟩
  refine not_refines_obs_of_termsWith (termsWith_prefix_resetBody (fun _ => 0))
    (termsWith_prefix_emit (fun _ => 0)) (by simp) (hiff.2 fun s₁ hr => Or.inl ?_)
  exact loop_x0IsZero_terminates_after_reset resetBody s₁ hr fun s _ =>
    ⟨[], termsWith_resetBody s⟩

/-- **The "terminates at every reachable entry" condition alone is not necessary.**
With `k = while 1 do skip`, deleting the (everywhere diverging) loop `while 1 do skip`
before it is a divergence-observable refinement: both programs have the single
behaviour `div []`. This refutes the reading "deletion is a refinement iff the loop
terminates from every reachable entry state". -/
theorem deleteLoop_refines_divergenceObservable_without_termination :
    EmitFree .skip ∧ DeadAfterPrefix .skip Cmd.skip.writes (spin false) ∧
    Refines ObsBeh (.seq .skip (.seq (spin false) (spin false))) (.seq .skip (spin false)) ∧
    ∀ s₁, ReachableAt .skip s₁ ∧ ¬ Terminates (spin false) s₁ := by
  refine ⟨by decide, ?_, ?_, fun s₁ => ⟨⟨s₁, [], 0, rfl⟩, not_terminates_spin false s₁⟩⟩
  · intro s₁ s₂ _ _ b
    rw [obsBeh_spin, obsBeh_spin]
  · intro s b hb
    have htgt := obsBeh_of_silent (silent_of_step (c := .seq .skip (spin false)) (c' := spin false) (s := s) (s' := s)
      rfl (spin_silent false s)) b
    have hsrc := obsBeh_of_silent (silent_of_step (c := .seq .skip (.seq (spin false) (spin false)))
      (c' := .seq (spin false) (spin false)) (s := s) (s' := s) rfl (spinSeq_silent false (spin false) s)) b
    exact hsrc.2 (htgt.1 hb)

/-- **Termination at every reachable entry characterizes deletion when the continuation
cannot silently diverge immediately.** Adding the hypothesis that `k` never has the
behaviour `div []` from a reachable entry state turns the exact condition into: deletion
is a divergence-observable refinement iff the loop terminates from every reachable
entry state. -/
theorem deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates
    (p k : Cmd) (mp : Bool) (b : Exp) (body : Cmd)
    (hEmit : EmitFree body) (hDead : DeadAfterPrefix p body.writes k)
    (hNoSilentK : ∀ s₁, ReachableAt p s₁ → ¬ ObsBeh k s₁ (.div [])) :
    Refines ObsBeh (.seq p (.seq (.loop mp b body) k)) (.seq p k) ↔
      ∀ s₁, ReachableAt p s₁ → Terminates (.loop mp b body) s₁ := by
  rw [deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff p k mp b body hEmit hDead]
  exact ⟨fun h s₁ hr => (h s₁ hr).resolve_right (hNoSilentK s₁ hr),
    fun h s₁ hr => Or.inl (h s₁ hr)⟩

/-- Non-vacuity with both sides of the equivalences true: with `p = x0 := 1`, the body
`x1 := x1 + 1` and `k = emit x0`, all hypotheses of both characterizations hold, the loop
`while x0 = 0 do x1 := x1 + 1` terminates at every reachable entry state although it
does not terminate from the (unreachable) all-zero state, and deletion is a
divergence-observable refinement. -/
theorem deleteLoop_iff_terminates_nonvacuous :
    EmitFree countBody ∧ DeadAfterPrefix (.assign 0 (.num 1)) countBody.writes (.emit (.var 0)) ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 1)) s₁ → ¬ ObsBeh (.emit (.var 0)) s₁ (.div [])) ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 1)) s₁ → Terminates countLoop s₁) ∧
    ¬ Terminates countLoop (fun _ => 0) ∧
    Refines ObsBeh (.seq (.assign 0 (.num 1)) (.seq countLoop (.emit (.var 0))))
      (.seq (.assign 0 (.num 1)) (.emit (.var 0))) := by
  have hE : EmitFree countBody := by decide
  have hD := deadAfterPrefix_of_deadAtEntry (.assign 0 (.num 1)) deadAtEntry_example
  have hT : ∀ s₁, ReachableAt (.assign 0 (.num 1)) s₁ → Terminates countLoop s₁ := by
    rintro s₁ ⟨s₀, t, ht⟩
    have hs : s₁ = State.update s₀ 0 1 :=
      (termsWith_unique ht (termsWith_assign 0 (.num 1) s₀)).2
    exact ⟨[], s₁, termsWith_loop_exit (by simp [hs, x0IsZero, Exp.eval, State.update])⟩
  refine ⟨hE, hD, fun s₁ _ h => (by rw [obsBeh_emit] at h; cases h), hT,
    not_terminates_countLoop, ?_⟩
  exact (deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff _ _ false x0IsZero
    countBody hE hD).2 fun s₁ hr => Or.inl (hT s₁ hr)

/-- Counterexample (`hNoSilentK` is needed): with `k = while 1 do skip`, the remaining
hypotheses hold but deletion is a refinement although the loop never terminates. -/
theorem deleteLoop_iff_terminates_needs_continuation_not_silent :
    EmitFree .skip ∧ DeadAfterPrefix .skip Cmd.skip.writes (spin false) ∧
    ¬ (Refines ObsBeh (.seq .skip (.seq (spin false) (spin false))) (.seq .skip (spin false)) ↔
        ∀ s₁, ReachableAt .skip s₁ → Terminates (spin false) s₁) := by
  obtain ⟨h1, h2, h3, h4⟩ := deleteLoop_refines_divergenceObservable_without_termination
  exact ⟨h1, h2, fun hiff =>
    (h4 (fun _ => 0)).2 (hiff.1 h3 (fun _ => 0) (h4 (fun _ => 0)).1)⟩

/-- `hNoSilentK` excludes only the behaviour `div []`: the continuation
`emit 1 ;; while 1 do skip` satisfies it although it silently diverges (after emitting). -/
theorem noSilentK_admits_emit_then_spin (s : State) :
    ¬ ObsBeh (.seq (.emit (.num 1)) (spin false)) s (.div []) ∧
    SilentlyDiverges (.seq (.emit (.num 1)) (spin false)) s := by
  refine ⟨fun h => ?_, ?_⟩
  · have hr : Reach (.seq (.emit (.num 1)) (spin false)) s [1] := by
      simpa [Exp.eval] using reach_seqR (BigStep.emit (.num 1) s) (reach_nil (spin false) s)
    have := (obsBeh_div_iff.1 h).2.2 _ hr
    simp at this
  · obtain ⟨m, hm⟩ := run_seq_of_bigStep (spin false) (BigStep.emit (.num 1) s)
    exact (silentlyDiverges_iff_of_run hm).2 (silentlyDiverges_spin false s)

/-- Counterexample (`hEmit` is needed): the emitting loop terminates at every reachable
entry and `k = skip` never silently diverges, yet deletion is not a refinement. -/
theorem deleteLoop_iff_terminates_needs_emitFree :
    DeadAfterPrefix (.assign 0 (.num 0)) emitBody.writes .skip ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ → ¬ ObsBeh .skip s₁ (.div [])) ∧
    ¬ (Refines ObsBeh (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero emitBody) .skip))
          (.seq (.assign 0 (.num 0)) .skip) ↔
        ∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ →
          Terminates (.loop false x0IsZero emitBody) s₁) := by
  refine ⟨deadAfterPrefix_of_deadAtEntry _ (deadAtEntry_skip _),
    fun s₁ _ h => (by rw [obsBeh_skip] at h; cases h), fun hiff => ?_⟩
  exact not_refines_obs_of_termsWith (termsWith_prefix_emitBody (fun _ => 0))
    (termsWith_prefix_skip (fun _ => 0)) (by simp) (hiff.2 fun s₁ hr =>
      loop_x0IsZero_terminates_after_reset emitBody s₁ hr fun s _ => ⟨[7], termsWith_emitBody s⟩)

/-- Counterexample (`hDead` is needed): the loop `while x0 = 0 do x0 := 1` terminates at
every reachable entry and `k = emit x0` never silently diverges, yet deletion is not a
refinement. -/
theorem deleteLoop_iff_terminates_needs_deadWrites :
    EmitFree resetBody ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ → ¬ ObsBeh (.emit (.var 0)) s₁ (.div [])) ∧
    ¬ (Refines ObsBeh
          (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero resetBody) (.emit (.var 0))))
          (.seq (.assign 0 (.num 0)) (.emit (.var 0))) ↔
        ∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ →
          Terminates (.loop false x0IsZero resetBody) s₁) := by
  refine ⟨by decide, fun s₁ _ h => (by rw [obsBeh_emit] at h; cases h), fun hiff => ?_⟩
  exact not_refines_obs_of_termsWith (termsWith_prefix_resetBody (fun _ => 0))
    (termsWith_prefix_emit (fun _ => 0)) (by simp) (hiff.2 fun s₁ hr =>
      loop_x0IsZero_terminates_after_reset resetBody s₁ hr fun s _ =>
        ⟨[], termsWith_resetBody s⟩)

/-! ## Result: divergence-observable refinement is strictly stronger -/

/-- Every divergence-observable refinement is a forward-progress refinement. -/
theorem refines_forwardProgress_of_refines_divergenceObservable (src tgt : Cmd)
    (h : Refines ObsBeh src tgt) : Refines FPBeh src tgt :=
  fun s b hb => hb.elim (fun ⟨t, ht⟩ => Or.inl ⟨t, h s (.div t) ht⟩) (fun hb => Or.inr (h s b hb))

/-- **Divergence-observable refinement is strictly stronger than forward-progress
refinement**: every divergence-observable refinement is a forward-progress refinement,
and some forward-progress refinement (deleting `while 1 do skip` before `emit 1`) is not
a divergence-observable refinement. -/
theorem refines_forwardProgress_of_refines_divergenceObservable_strict :
    (∀ src tgt, Refines ObsBeh src tgt → Refines FPBeh src tgt) ∧
    ∃ src tgt, Refines FPBeh src tgt ∧ ¬ Refines ObsBeh src tgt :=
  ⟨refines_forwardProgress_of_refines_divergenceObservable,
    .seq (spin false) (.emit (.num 1)), .emit (.num 1),
    loopDeletion_spin_refines_forwardProgress false,
    (loopDeletion_spin_not_refines_divergenceObservable false).2⟩

/-- The analogous transfer into the per-loop semantics fails: flagging a loop is a
divergence-observable refinement (flags are ignored by `ObsBeh`) but not a per-loop
refinement (it introduces a progress violation). -/
theorem refines_divergenceObservable_not_imp_refines_mixed :
    Refines ObsBeh (spin false) (spin true) ∧ ¬ Refines MixedBeh (spin false) (spin true) := by
  refine ⟨fun s b hb => (obsBeh_spin false s b).2 ((obsBeh_spin true s b).1 hb), fun h => ?_⟩
  have hpv : ProgressViolation (spin true) (fun _ => 0) :=
    ⟨0, .num 1, .skip, rfl, silentlyIterates_spin _⟩
  rcases h (fun _ => 0) (.term [42]) (Or.inl hpv) with h | h
  · obtain ⟨n, b, body, hh, -⟩ := h
    obtain ⟨h1, -, -⟩ := spin_inv false (fun _ => 0) n _ (Or.inl rfl)
    rcases h1 with h1 | h1 | h1 <;> rw [h1] at hh <;> simp [Cmd.head, spin] at hh
  · rw [obsBeh_spin] at h; cases h

/-- Non-vacuity: removing a dead store is a divergence-observable refinement. -/
theorem refines_divergenceObservable_example :
    Refines ObsBeh (.seq (.assign 1 (.num 5)) (.emit (.num 1))) (.emit (.num 1)) := by
  intro s b hb
  rw [obsBeh_emit] at hb
  rw [obsBeh_of_termsWith (termsWith_seq (termsWith_assign 1 (.num 5) s)
    (termsWith_emit (.num 1) _))]
  simpa [Exp.eval] using hb

/-- Counterexample (the hypothesis is needed): adding an output is not a
forward-progress refinement. -/
theorem refines_forwardProgress_needs_hypothesis : ¬ Refines FPBeh .skip (.emit (.num 1)) :=
  not_refines_fp_of_termsWith (s := fun _ => 0) (termsWith_skip _) (termsWith_emit (.num 1) _)
    (by simp [Exp.eval])

end Toy.Progress
