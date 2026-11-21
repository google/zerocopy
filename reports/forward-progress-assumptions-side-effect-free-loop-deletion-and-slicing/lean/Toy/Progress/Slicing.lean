import Toy.Progress.Deletion

/-!
# Slicing with respect to all `emit` statements

`IsSlice ts R c c' R'` says that `c'` is a slice of `c`: `c'` is obtained from `c` by
replacing sub-commands with `skip`, `R` is the set of variables relevant *after* `c`,
and `R'` (an over-approximation of) the set relevant *before* it. The slicing criterion
is the set of **all** `emit` statements: no `emit` may be removed.

* Data dependence: a kept assignment `x := e` makes the variables of `e` relevant; a
  kept `emit e` makes the variables of `e` relevant.
* Control dependence: a kept conditional or loop makes the variables of its condition
  relevant; a kept loop needs a relevant set `I` that is invariant across its body.
* Deletion (`drop`): any emit-free sub-command that writes no relevant variable may be
  replaced by `skip`. With `ts = false` (classic, termination-insensitive slicing)
  this is all; with `ts = true` (semantic termination-guarded slicing) the dropped
  sub-command must also terminate from every state. The termination premise is a
  semantic, undecidable condition, not a syntactic control-dependence analysis: it lets
  a slice drop a loop that terminates from every state (`isTerminationSensitiveSlice_drops_terminating_loop`),
  which a control-flow-graph analysis of non-termination-sensitive control dependence
  would keep.

`IsSlice` is a relation, not an algorithm: a command has many slices, and every
command is a slice of itself (`isSlice_refl`).

At the top level nothing is relevant after the program (final states are not
observable), so `R = ∅`.
-/

namespace Toy.Progress

/-- Sets of variables, as predicates. -/
abbrev VarSet := Var → Prop

/-- The slice relation; `ts` selects termination-sensitive dropping (see module doc). -/
inductive IsSlice (ts : Bool) : VarSet → Cmd → Cmd → VarSet → Prop
  | skip (R : VarSet) : IsSlice ts R .skip .skip R
  | assign (R R' : VarSet) (x : Var) (e : Exp)
      (h : ∀ y, (R y ∧ y ≠ x) ∨ y ∈ e.vars → R' y) :
      IsSlice ts R (.assign x e) (.assign x e) R'
  | emit (R R' : VarSet) (e : Exp) (h : ∀ y, R y ∨ y ∈ e.vars → R' y) :
      IsSlice ts R (.emit e) (.emit e) R'
  | seq (R R₁ R' : VarSet) (c₁ c₁' c₂ c₂' : Cmd) :
      IsSlice ts R c₂ c₂' R₁ → IsSlice ts R₁ c₁ c₁' R' →
      IsSlice ts R (.seq c₁ c₂) (.seq c₁' c₂') R'
  | ite (R R₁ R₂ R' : VarSet) (b : Exp) (c₁ c₁' c₂ c₂' : Cmd) :
      IsSlice ts R c₁ c₁' R₁ → IsSlice ts R c₂ c₂' R₂ →
      (∀ y, R₁ y ∨ R₂ y ∨ y ∈ b.vars → R' y) →
      IsSlice ts R (.ite b c₁ c₂) (.ite b c₁' c₂') R'
  | loop (R I I' : VarSet) (mp : Bool) (b : Exp) (c c' : Cmd) :
      (∀ y, R y ∨ y ∈ b.vars → I y) → IsSlice ts I c c' I' → (∀ y, I' y → I y) →
      IsSlice ts R (.loop mp b c) (.loop mp b c') I
  | drop (R : VarSet) (c : Cmd) :
      EmitFree c → (∀ y, y ∈ c.writes → ¬ R y) → (ts = true → ∀ s, Terminates c s) →
      IsSlice ts R c .skip R

/-- `c'` is a classic (termination-insensitive) slice of `c` w.r.t. all `emit`s. -/
def IsClassicSlice (c c' : Cmd) : Prop := ∃ R', IsSlice false (fun _ => False) c c' R'

/-- `c'` is a termination-guarded slice of `c` w.r.t. all `emit`s: every dropped
sub-command terminates from every state. -/
def IsTerminationSensitiveSlice (c c' : Cmd) : Prop :=
  ∃ R', IsSlice true (fun _ => False) c c' R'

/-! ### Examples -/

/-- Positive example: a classic slice may delete the possibly-diverging loop
`while x0 = 0 do x1 := x1 + 1` before `emit 1`. -/
theorem isClassicSlice_example :
    IsClassicSlice (.seq countLoop (.emit (.num 1))) (.seq .skip (.emit (.num 1))) :=
  ⟨fun _ => False, .seq _ _ _ _ _ _ _
    (.emit _ _ _ (by intro y h; simp [Exp.vars] at h))
    (.drop _ _ (by decide) (by simp) (by simp))⟩

/-- Positive example: a termination-sensitive slice that keeps the loop and its
condition but drops the irrelevant, always-terminating body. -/
theorem isTerminationSensitiveSlice_example :
    IsTerminationSensitiveSlice (.seq countLoop (.emit (.num 1)))
      (.seq (.loop false x0IsZero .skip) (.emit (.num 1))) :=
  ⟨fun y => y = 0, .seq _ (fun _ => False) _ _ _ _ _
    (.emit _ _ _ (by intro y h; simp [Exp.vars] at h))
    (.loop _ (fun y => y = 0) (fun y => y = 0) _ _ _ _
      (by intro y h; simpa [x0IsZero, Exp.vars] using h)
      (.drop _ _ (by decide) (by simp [countBody, Cmd.writes])
        (fun _ s => ⟨_, _, termsWith_assign _ _ s⟩))
      (fun _ h => h))⟩

/-- Positive example: every command is a (trivial) slice of itself. -/
theorem isSlice_refl (ts : Bool) (c : Cmd) : ∀ R, ∃ R', IsSlice ts R c c R' := by
  induction c with
  | skip => exact fun R => ⟨R, .skip R⟩
  | assign x e => exact fun R => ⟨fun _ => True, .assign _ _ _ _ (fun _ _ => trivial)⟩
  | emit e => exact fun R => ⟨fun _ => True, .emit _ _ _ (fun _ _ => trivial)⟩
  | seq c₁ c₂ ih₁ ih₂ =>
    intro R
    obtain ⟨R₁, h₂⟩ := ih₂ R
    obtain ⟨R', h₁⟩ := ih₁ R₁
    exact ⟨R', .seq _ _ _ _ _ _ _ h₂ h₁⟩
  | ite b c₁ c₂ ih₁ ih₂ =>
    intro R
    obtain ⟨R₁, h₁⟩ := ih₁ R
    obtain ⟨R₂, h₂⟩ := ih₂ R
    exact ⟨fun _ => True, .ite _ _ _ _ _ _ _ _ _ h₁ h₂ (fun _ _ => trivial)⟩
  | loop mp b c ih =>
    intro R
    obtain ⟨I', h⟩ := ih (fun _ => True)
    exact ⟨fun _ => True, .loop _ _ _ _ _ _ _ (fun _ _ => trivial) h (fun _ _ => trivial)⟩

theorem isClassicSlice_refl (c : Cmd) : IsClassicSlice c c := isSlice_refl false c _

theorem isTerminationSensitiveSlice_refl (c : Cmd) : IsTerminationSensitiveSlice c c :=
  isSlice_refl true c _

/-- Negative example: an `emit` can never be sliced away. -/
theorem not_isSlice_drop_emit (ts : Bool) (R R' : VarSet) (e : Exp) :
    ¬ IsSlice ts R (.emit e) .skip R' := by
  intro h
  cases h with
  | drop _ _ hE _ _ => simp [EmitFree, Cmd.noEmit] at hE

/-- Negative example (data dependence): the assignment that defines an emitted variable
cannot be dropped. -/
theorem not_isClassicSlice_drop_definition :
    ¬ IsClassicSlice (.seq (.assign 0 (.num 5)) (.emit (.var 0)))
      (.seq .skip (.emit (.var 0))) := by
  rintro ⟨R', h⟩
  cases h with
  | seq _ R₁ _ _ _ _ _ h₂ h₁ =>
    cases h₂ with
    | emit _ _ _ hR =>
      cases h₁ with
      | drop _ _ _ hw _ => exact hw 0 (by simp [Cmd.writes]) (hR 0 (by simp [Exp.vars]))

/-- Negative example (control dependence): the assignment that defines the condition
guarding a kept `emit` cannot be dropped. -/
theorem not_isClassicSlice_drop_guard_definition :
    ¬ IsClassicSlice (.seq (.assign 1 (.num 0)) (.ite (.var 1) (.emit (.num 1)) .skip))
      (.seq .skip (.ite (.var 1) (.emit (.num 1)) .skip)) := by
  rintro ⟨R', h⟩
  cases h with
  | seq _ R₁ _ _ _ _ _ h₂ h₁ =>
    cases h₂ with
    | ite _ _ _ _ _ _ _ _ _ _ _ hR =>
      cases h₁ with
      | drop _ _ _ hw _ =>
        exact hw 1 (by simp [Cmd.writes]) (hR 1 (Or.inr (Or.inr (by simp [Exp.vars]))))

/-- Negative example (termination sensitivity): no termination-sensitive slice deletes
`while 1 do skip`, which never terminates. -/
theorem not_isTerminationSensitiveSlice_spin :
    ¬ IsTerminationSensitiveSlice (.seq (spin false) (.emit (.num 1)))
      (.seq .skip (.emit (.num 1))) := by
  rintro ⟨R', h⟩
  unfold spin at h
  cases h with
  | seq _ R₁ _ _ _ _ _ _ h₁ =>
    cases h₁ with
    | drop _ _ _ _ ht => exact not_terminates_spin false (fun _ => 0) (ht rfl _)

/-- Positive example (the termination premise is semantic): a termination-sensitive slice
may drop `while x0 = 0 do x0 := 1`, which terminates from every state, before `emit 1`. -/
theorem isTerminationSensitiveSlice_drops_terminating_loop :
    IsTerminationSensitiveSlice (.seq (.loop false x0IsZero resetBody) (.emit (.num 1)))
      (.seq .skip (.emit (.num 1))) := by
  refine ⟨fun _ => False, .seq _ _ _ _ _ _ _
    (.emit _ _ _ (by intro y h; simp [Exp.vars] at h))
    (.drop _ _ (by decide) (by simp) (fun _ s => ?_))⟩
  by_cases h0 : s 0 = 0
  · exact ⟨[], _, termsWith_loop_x0IsZero false resetBody s _ [] h0 (termsWith_resetBody s)
      (by simp [State.update])⟩
  · exact ⟨[], s, termsWith_loop_exit (by simp [x0IsZero, Exp.eval, h0])⟩

/-! ## Simulation lemmas for slices -/

/-- Two states agree on every variable of the set `R`. -/
def AgreeOn (R : VarSet) (s s' : State) : Prop := ∀ y, R y → s y = s' y

theorem agreeOn_mono {R R' : VarSet} {s s' : State} (h : AgreeOn R' s s') (hRR' : ∀ y, R y → R' y) :
    AgreeOn R s s' := fun y hy => h y (hRR' y hy)

theorem eval_eq_of_agree {e : Exp} {s s' : State} (h : ∀ y, y ∈ e.vars → s y = s' y) :
    e.eval s = e.eval s' := by
  induction e with
  | num n => rfl
  | var x => exact h x (by simp [Exp.vars])
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eq a b iha ihb =>
    simp only [Exp.vars, List.mem_append] at h
    simp only [Exp.eval, iha (fun y hy => h y (Or.inl hy)), ihb (fun y hy => h y (Or.inr hy))]

theorem drop_agree {c : Cmd} {R : VarSet} {s s₁ s' : State} {t : List Val}
    (hw : ∀ y, y ∈ c.writes → ¬ R y) (hb : BigStep c s t s₁) (ha : AgreeOn R s s') :
    AgreeOn R s₁ s' := by
  intro y hy
  rw [← bigStep_agreeOff hb y (fun hm => hw y hm hy)]
  exact ha y hy

/-- Forward simulation of terminating runs: the slice reproduces every terminating run
of the original, from any state agreeing on the variables relevant before. -/
theorem slice_bigStep_fwd {ts : Bool} {c : Cmd} {s : State} {t : List Val} {s₁ : State}
    (hB : BigStep c s t s₁) :
    ∀ {R R' : VarSet} {c' : Cmd} {s' : State}, IsSlice ts R c c' R' → AgreeOn R' s s' →
      ∃ s₁', BigStep c' s' t s₁' ∧ AgreeOn R s₁ s₁' := by
  have hdrop : ∀ {c : Cmd} {R : VarSet} {s s₁ s' : State} {t : List Val}, EmitFree c →
      (∀ y, y ∈ c.writes → ¬ R y) → BigStep c s t s₁ → AgreeOn R s s' →
      ∃ s₁', BigStep .skip s' t s₁' ∧ AgreeOn R s₁ s₁' := by
    intro c R s s₁ s' t hE hw hb ha
    rw [bigStep_emitFree hb hE]
    exact ⟨s', .skip s', drop_agree hw hb ha⟩
  induction hB with
  | skip s =>
    intro R R' c' s' hS ha
    cases hS with
    | skip => exact ⟨s', .skip s', ha⟩
    | drop _ _ hE hw _ => exact hdrop hE hw (.skip s) ha
  | assign x e s =>
    intro R R' c' s' hS ha
    cases hS with
    | assign _ _ _ _ h =>
      refine ⟨_, .assign x e s', fun y hy => ?_⟩
      by_cases hyx : y = x
      · subst hyx
        simp only [State.update, ↓reduceIte]
        exact eval_eq_of_agree fun z hz => ha z (h z (Or.inr hz))
      · simp only [State.update, hyx, ↓reduceIte]
        exact ha y (h y (Or.inl ⟨hy, hyx⟩))
    | drop _ _ hE hw _ => exact hdrop hE hw (.assign x e s) ha
  | emit e s =>
    intro R R' c' s' hS ha
    cases hS with
    | emit _ _ _ h =>
      refine ⟨s', ?_, fun y hy => ha y (h y (Or.inl hy))⟩
      rw [eval_eq_of_agree (e := e) fun z hz => ha z (h z (Or.inr hz))]
      exact .emit e s'
    | drop _ _ hE _ _ => simp [EmitFree, Cmd.noEmit] at hE
  | seq h₁ h₂ ih₁ ih₂ =>
    intro R R' c' s' hS ha
    cases hS with
    | seq _ R₁ _ _ _ _ _ hS₂ hS₁ =>
      obtain ⟨s₁', hb₁, ha₁⟩ := ih₁ hS₁ ha
      obtain ⟨s₂', hb₂, ha₂⟩ := ih₂ hS₂ ha₁
      exact ⟨s₂', .seq hb₁ hb₂, ha₂⟩
    | drop _ _ hE hw _ => exact hdrop hE hw (.seq h₁ h₂) ha
  | iteT hb h ih =>
    intro R R' c' s' hS ha
    cases hS with
    | ite _ R₁ R₂ _ b _ _ _ _ hS₁ hS₂ hR =>
      obtain ⟨s₁', hb₁, ha₁⟩ := ih hS₁ (agreeOn_mono ha fun y hy => hR y (Or.inl hy))
      refine ⟨s₁', .iteT ?_ hb₁, ha₁⟩
      rwa [← eval_eq_of_agree fun z hz => ha z (hR z (Or.inr (Or.inr hz)))]
    | drop _ _ hE hw _ => exact hdrop hE hw (.iteT hb h) ha
  | iteF hb h ih =>
    intro R R' c' s' hS ha
    cases hS with
    | ite _ R₁ R₂ _ b _ _ _ _ hS₁ hS₂ hR =>
      obtain ⟨s₁', hb₁, ha₁⟩ := ih hS₂ (agreeOn_mono ha fun y hy => hR y (Or.inr (Or.inl hy)))
      refine ⟨s₁', .iteF ?_ hb₁, ha₁⟩
      rwa [← eval_eq_of_agree fun z hz => ha z (hR z (Or.inr (Or.inr hz)))]
    | drop _ _ hE hw _ => exact hdrop hE hw (.iteF hb h) ha
  | loopExit hb =>
    intro R R' c' s' hS ha
    cases hS with
    | loop _ I I' _ b _ _ hRI hS' hI =>
      refine ⟨s', .loopExit ?_, fun y hy => ha y (hRI y (Or.inl hy))⟩
      rwa [← eval_eq_of_agree fun z hz => ha z (hRI z (Or.inr hz))]
    | drop _ _ hE hw _ => exact hdrop hE hw (.loopExit hb) ha
  | loopIter hb h₁ h₂ ih₁ ih₂ =>
    intro R R' c' s' hS ha
    have hS0 := hS
    cases hS with
    | loop _ I I' _ _ _ _ hRI hS' hI =>
      obtain ⟨s₁', hb₁, ha₁⟩ := ih₁ hS' (agreeOn_mono ha hI)
      obtain ⟨s₂', hb₂, ha₂⟩ := ih₂ hS0 ha₁
      refine ⟨s₂', .loopIter ?_ hb₁ hb₂, ha₂⟩
      rwa [← eval_eq_of_agree fun z hz => ha z (hRI z (Or.inr hz))]
    | drop _ _ hE hw _ => exact hdrop hE hw (.loopIter hb h₁ h₂) ha

/-- Forward simulation of finite execution prefixes. -/
theorem slice_partial_fwd {ts : Bool} {c : Cmd} {s : State} {t : List Val}
    (hP : Partial c s t) :
    ∀ {R R' : VarSet} {c' : Cmd} {s' : State}, IsSlice ts R c c' R' → AgreeOn R' s s' →
      Partial c' s' t := by
  have hdrop : ∀ {c : Cmd} {s s' : State} {t : List Val}, EmitFree c → Partial c s t →
      Partial .skip s' t := by
    intro c s s' t hE hp
    rw [partial_emitFree hp hE]; exact .nil _ _
  induction hP with
  | nil => intros; exact .nil _ _
  | emit e s =>
    intro R R' c' s' hS ha
    cases hS with
    | emit _ _ _ h =>
      rw [eval_eq_of_agree (e := e) fun z hz => ha z (h z (Or.inr hz))]
      exact .emit e s'
    | drop _ _ hE _ _ => simp [EmitFree, Cmd.noEmit] at hE
  | seqL h ih =>
    intro R R' c' s' hS ha
    cases hS with
    | seq _ R₁ _ _ _ _ _ hS₂ hS₁ => exact .seqL (ih hS₁ ha)
    | drop _ _ hE _ _ => exact hdrop hE (.seqL h)
  | seqR h₁ h₂ ih =>
    intro R R' c' s' hS ha
    cases hS with
    | seq _ R₁ _ _ _ _ _ hS₂ hS₁ =>
      obtain ⟨s₁', hb₁, ha₁⟩ := slice_bigStep_fwd h₁ hS₁ ha
      exact .seqR hb₁ (ih hS₂ ha₁)
    | drop _ _ hE _ _ => exact hdrop hE (.seqR h₁ h₂)
  | iteT hb h ih =>
    intro R R' c' s' hS ha
    cases hS with
    | ite _ R₁ R₂ _ b _ _ _ _ hS₁ hS₂ hR =>
      refine .iteT ?_ (ih hS₁ (agreeOn_mono ha fun y hy => hR y (Or.inl hy)))
      rwa [← eval_eq_of_agree fun z hz => ha z (hR z (Or.inr (Or.inr hz)))]
    | drop _ _ hE _ _ => exact hdrop hE (.iteT hb h)
  | iteF hb h ih =>
    intro R R' c' s' hS ha
    cases hS with
    | ite _ R₁ R₂ _ b _ _ _ _ hS₁ hS₂ hR =>
      refine .iteF ?_ (ih hS₂ (agreeOn_mono ha fun y hy => hR y (Or.inr (Or.inl hy))))
      rwa [← eval_eq_of_agree fun z hz => ha z (hR z (Or.inr (Or.inr hz)))]
    | drop _ _ hE _ _ => exact hdrop hE (.iteF hb h)
  | loopBody hb h ih =>
    intro R R' c' s' hS ha
    cases hS with
    | loop _ I I' _ _ _ _ hRI hS' hI =>
      refine .loopBody ?_ (ih hS' (agreeOn_mono ha hI))
      rwa [← eval_eq_of_agree fun z hz => ha z (hRI z (Or.inr hz))]
    | drop _ _ hE _ _ => exact hdrop hE (.loopBody hb h)
  | loopIter hb h₁ h₂ ih =>
    intro R R' c' s' hS ha
    have hS0 := hS
    cases hS with
    | loop _ I I' _ _ _ _ hRI hS' hI =>
      obtain ⟨s₁', hb₁, ha₁⟩ := slice_bigStep_fwd h₁ hS' (agreeOn_mono ha hI)
      refine .loopIter ?_ hb₁ (ih hS0 ha₁)
      rwa [← eval_eq_of_agree fun z hz => ha z (hRI z (Or.inr hz))]
    | drop _ _ hE _ _ => exact hdrop hE (.loopIter hb h₁ h₂)

/-- Backward simulation of terminating runs for termination-sensitive slices: the
original reproduces every terminating run of the slice, since every dropped sub-command
terminates silently without changing relevant variables. -/
theorem slice_bigStep_bwd {c' : Cmd} {s' : State} {t : List Val} {s₁' : State}
    (hB : BigStep c' s' t s₁') :
    ∀ {R R' : VarSet} {c : Cmd} {s : State}, IsSlice true R c c' R' → AgreeOn R' s s' →
      ∃ s₁, BigStep c s t s₁ ∧ AgreeOn R s₁ s₁' := by
  induction hB with
  | skip s' =>
    intro R R' c s hS ha
    cases hS with
    | skip => exact ⟨s, .skip s, ha⟩
    | drop _ _ hE hw hT =>
      obtain ⟨t₀, s₁, h₁⟩ := hT rfl s
      have hb := termsWith_iff_bigStep.1 h₁
      have := bigStep_emitFree hb hE
      subst this
      exact ⟨s₁, hb, drop_agree hw hb ha⟩
  | assign x e s' =>
    intro R R' c s hS ha
    cases hS with
    | assign _ _ _ _ h =>
      refine ⟨_, .assign x e s, fun y hy => ?_⟩
      by_cases hyx : y = x
      · subst hyx
        simp only [State.update, ↓reduceIte]
        exact eval_eq_of_agree fun z hz => ha z (h z (Or.inr hz))
      · simp only [State.update, hyx, ↓reduceIte]
        exact ha y (h y (Or.inl ⟨hy, hyx⟩))
  | emit e s' =>
    intro R R' c s hS ha
    cases hS with
    | emit _ _ _ h =>
      refine ⟨s, ?_, fun y hy => ha y (h y (Or.inl hy))⟩
      rw [← eval_eq_of_agree (e := e) fun z hz => ha z (h z (Or.inr hz))]
      exact .emit e s
  | seq h₁ h₂ ih₁ ih₂ =>
    intro R R' c s hS ha
    cases hS with
    | seq _ R₁ _ _ _ _ _ hS₂ hS₁ =>
      obtain ⟨s₁, hb₁, ha₁⟩ := ih₁ hS₁ ha
      obtain ⟨s₂, hb₂, ha₂⟩ := ih₂ hS₂ ha₁
      exact ⟨s₂, .seq hb₁ hb₂, ha₂⟩
  | iteT hb h ih =>
    intro R R' c s hS ha
    cases hS with
    | ite _ R₁ R₂ _ b _ _ _ _ hS₁ hS₂ hR =>
      obtain ⟨s₁, hb₁, ha₁⟩ := ih hS₁ (agreeOn_mono ha fun y hy => hR y (Or.inl hy))
      refine ⟨s₁, .iteT ?_ hb₁, ha₁⟩
      rwa [eval_eq_of_agree fun z hz => ha z (hR z (Or.inr (Or.inr hz)))]
  | iteF hb h ih =>
    intro R R' c s hS ha
    cases hS with
    | ite _ R₁ R₂ _ b _ _ _ _ hS₁ hS₂ hR =>
      obtain ⟨s₁, hb₁, ha₁⟩ := ih hS₂ (agreeOn_mono ha fun y hy => hR y (Or.inr (Or.inl hy)))
      refine ⟨s₁, .iteF ?_ hb₁, ha₁⟩
      rwa [eval_eq_of_agree fun z hz => ha z (hR z (Or.inr (Or.inr hz)))]
  | loopExit hb =>
    intro R R' c s hS ha
    cases hS with
    | loop _ I I' _ b _ _ hRI hS' hI =>
      refine ⟨s, .loopExit ?_, fun y hy => ha y (hRI y (Or.inl hy))⟩
      rwa [eval_eq_of_agree fun z hz => ha z (hRI z (Or.inr hz))]
  | loopIter hb h₁ h₂ ih₁ ih₂ =>
    intro R R' c s hS ha
    have hS0 := hS
    cases hS with
    | loop _ I I' _ _ _ _ hRI hS' hI =>
      obtain ⟨s₁, hb₁, ha₁⟩ := ih₁ hS' (agreeOn_mono ha hI)
      obtain ⟨s₂, hb₂, ha₂⟩ := ih₂ hS0 ha₁
      refine ⟨s₂, .loopIter ?_ hb₁ hb₂, ha₂⟩
      rwa [eval_eq_of_agree fun z hz => ha z (hRI z (Or.inr hz))]

/-- Backward simulation of finite execution prefixes for termination-sensitive slices. -/
theorem slice_partial_bwd {c' : Cmd} {s' : State} {t : List Val} (hP : Partial c' s' t) :
    ∀ {R R' : VarSet} {c : Cmd} {s : State}, IsSlice true R c c' R' → AgreeOn R' s s' →
      Partial c s t := by
  induction hP with
  | nil => intros; exact .nil _ _
  | emit e s' =>
    intro R R' c s hS ha
    cases hS with
    | emit _ _ _ h =>
      rw [← eval_eq_of_agree (e := e) fun z hz => ha z (h z (Or.inr hz))]
      exact .emit e s
  | seqL h ih =>
    intro R R' c s hS ha
    cases hS with
    | seq _ R₁ _ _ _ _ _ hS₂ hS₁ => exact .seqL (ih hS₁ ha)
  | seqR h₁ h₂ ih =>
    intro R R' c s hS ha
    cases hS with
    | seq _ R₁ _ _ _ _ _ hS₂ hS₁ =>
      obtain ⟨s₁, hb₁, ha₁⟩ := slice_bigStep_bwd h₁ hS₁ ha
      exact .seqR hb₁ (ih hS₂ ha₁)
  | iteT hb h ih =>
    intro R R' c s hS ha
    cases hS with
    | ite _ R₁ R₂ _ b _ _ _ _ hS₁ hS₂ hR =>
      refine .iteT ?_ (ih hS₁ (agreeOn_mono ha fun y hy => hR y (Or.inl hy)))
      rwa [eval_eq_of_agree fun z hz => ha z (hR z (Or.inr (Or.inr hz)))]
  | iteF hb h ih =>
    intro R R' c s hS ha
    cases hS with
    | ite _ R₁ R₂ _ b _ _ _ _ hS₁ hS₂ hR =>
      refine .iteF ?_ (ih hS₂ (agreeOn_mono ha fun y hy => hR y (Or.inr (Or.inl hy))))
      rwa [eval_eq_of_agree fun z hz => ha z (hR z (Or.inr (Or.inr hz)))]
  | loopBody hb h ih =>
    intro R R' c s hS ha
    cases hS with
    | loop _ I I' _ _ _ _ hRI hS' hI =>
      refine .loopBody ?_ (ih hS' (agreeOn_mono ha hI))
      rwa [eval_eq_of_agree fun z hz => ha z (hRI z (Or.inr hz))]
  | loopIter hb h₁ h₂ ih =>
    intro R R' c s hS ha
    have hS0 := hS
    cases hS with
    | loop _ I I' _ _ _ _ hRI hS' hI =>
      obtain ⟨s₁, hb₁, ha₁⟩ := slice_bigStep_bwd h₁ hS' (agreeOn_mono ha hI)
      refine .loopIter ?_ hb₁ (ih hS0 ha₁)
      rwa [eval_eq_of_agree fun z hz => ha z (hRI z (Or.inr hz))]


/-! ## Result: classic slices preserve terminating runs -/

/-- **A classic slice preserves the trace of every terminating run**: if `c'` is a classic
slice of `c` w.r.t. all `emit`s and `c` terminates from `s` emitting `t`, then `c'`
terminates from `s` emitting `t`. -/
theorem classicSlice_preserves_terminating_traces (c c' : Cmd)
    (hSlice : IsClassicSlice c c') :
    ∀ s t, ObsBeh c s (.term t) → ObsBeh c' s (.term t) := by
  obtain ⟨R', hS⟩ := hSlice
  intro s t h
  obtain ⟨s₁, hb⟩ := obsBeh_term_iff.1 h
  obtain ⟨s₁', hb', -⟩ := slice_bigStep_fwd hb hS (fun _ _ => rfl)
  exact obsBeh_term_iff.2 ⟨s₁', hb'⟩

/-- Non-vacuity: a classic slice that deletes a loop, and a terminating run of the
original (from a state with `x0 ≠ 0`). -/
theorem classicSlice_preserves_terminating_traces_nonvacuous :
    IsClassicSlice (.seq countLoop (.emit (.num 1))) (.seq .skip (.emit (.num 1))) ∧
    ObsBeh (.seq countLoop (.emit (.num 1))) (fun _ => 1) (.term [1]) := by
  refine ⟨isClassicSlice_example, ⟨fun _ => 1, ?_⟩⟩
  exact termsWith_seq (termsWith_loop_exit (by simp [x0IsZero, Exp.eval]))
    (termsWith_emit (.num 1) _)

/-- Counterexample (the slice hypothesis is needed): `skip` is not a slice of `emit 1`,
and it does not preserve the terminating trace `[1]`. -/
theorem classicSlice_preserves_terminating_traces_needs_slice :
    ¬ IsClassicSlice (.emit (.num 1)) .skip ∧
    ObsBeh (.emit (.num 1)) (fun _ => 0) (.term [1]) ∧
    ¬ ObsBeh .skip (fun _ => 0) (.term [1]) := by
  refine ⟨fun ⟨R', h⟩ => not_isSlice_drop_emit _ _ _ _ h, (obsBeh_emit _ _ _).2 rfl, ?_⟩
  rw [obsBeh_skip]; simp

/-! ## Result: classic slices may terminate where the original diverges -/

/-- **A classic slice can terminate although the original diverges**: `skip ;; emit 1` is
a classic slice of `while 1 do skip ;; emit 1`; from every state the original silently
diverges and the slice terminates emitting `[1]`, so the slice is not a
divergence-observable refinement. -/
theorem classicSlice_spin_terminates_while_original_diverges :
    IsClassicSlice (.seq (spin false) (.emit (.num 1))) (.seq .skip (.emit (.num 1))) ∧
    (∀ s, ObsBeh (.seq (spin false) (.emit (.num 1))) s (.div []) ∧
          ObsBeh (.seq .skip (.emit (.num 1))) s (.term [1])) ∧
    ¬ Refines ObsBeh (.seq (spin false) (.emit (.num 1))) (.seq .skip (.emit (.num 1))) := by
  have hT : ∀ s, TermsWith (.seq .skip (.emit (.num 1))) s [1] s := fun s =>
    termsWith_seq (termsWith_skip s) (termsWith_emit (.num 1) s)
  refine ⟨⟨fun _ => False, .seq _ _ _ _ _ _ _
      (.emit _ _ _ (by intro y h; simp [Exp.vars] at h))
      (.drop _ _ (by decide) (by simp [spin, Cmd.writes]) (by simp))⟩,
    fun s => ⟨(obsBeh_spinSeq false _ s _).2 rfl, (obsBeh_of_termsWith (hT s) _).2 rfl⟩, ?_⟩
  intro h
  have := h (fun _ => 0) _ ((obsBeh_of_termsWith (hT _) _).2 rfl)
  rw [obsBeh_spinSeq] at this
  simp at this

/-! ## Result: termination-sensitive slices preserve all behaviours -/

/-- **A termination-sensitive slice preserves every observable behaviour**, including
silent divergence and infinite traces: from every state, `c'` and `c` have the same
divergence-observable behaviours. -/
theorem terminationSensitiveSlice_preserves_obsBeh (c c' : Cmd)
    (hSlice : IsTerminationSensitiveSlice c c') :
    ∀ s b, ObsBeh c' s b ↔ ObsBeh c s b := by
  obtain ⟨R', hS⟩ := hSlice
  intro s
  refine obsBeh_congr (fun t => ⟨fun ⟨s₁, h⟩ => ?_, fun ⟨s₁, h⟩ => ?_⟩)
    (fun t => ⟨fun h => ?_, fun h => ?_⟩)
  · obtain ⟨s₂, h', -⟩ := slice_bigStep_bwd h hS (fun _ _ => rfl); exact ⟨s₂, h'⟩
  · obtain ⟨s₂, h', -⟩ := slice_bigStep_fwd h hS (fun _ _ => rfl); exact ⟨s₂, h'⟩
  · exact reach_of_partial (slice_partial_bwd (partial_of_reach h) hS (fun _ _ => rfl))
  · exact reach_of_partial (slice_partial_fwd (partial_of_reach h) hS (fun _ _ => rfl))

/-- Non-vacuity: a termination-sensitive slice that removes the loop body. -/
theorem terminationSensitiveSlice_preserves_obsBeh_nonvacuous :
    IsTerminationSensitiveSlice (.seq countLoop (.emit (.num 1)))
      (.seq (.loop false x0IsZero .skip) (.emit (.num 1))) :=
  isTerminationSensitiveSlice_example

/-- Counterexample (termination sensitivity is needed): the classic slice `skip ;; emit 1` of
`while 1 do skip ;; emit 1` does not preserve behaviours. -/
theorem terminationSensitiveSlice_needs_terminationSensitivity :
    IsClassicSlice (.seq (spin false) (.emit (.num 1))) (.seq .skip (.emit (.num 1))) ∧
    ¬ (∀ s b, ObsBeh (.seq .skip (.emit (.num 1))) s b ↔
        ObsBeh (.seq (spin false) (.emit (.num 1))) s b) := by
  obtain ⟨h1, h2, h3⟩ := classicSlice_spin_terminates_while_original_diverges
  exact ⟨h1, fun h => h3 fun s b hb => (h s b).1 hb⟩

/-! ## Result: classic slices are forward-progress refinements -/

/-- **Under forward progress, every classic slice is a refinement**: a run of the original
that gets stuck in a deleted (emit-free) loop silently diverges and is undefined, and
otherwise the slice reproduces the original's trace (finite or infinite). -/
theorem classicSlice_refines_forwardProgress (c c' : Cmd)
    (hSlice : IsClassicSlice c c') : Refines FPBeh c c' := by
  obtain ⟨R', hS⟩ := hSlice
  intro s b hb
  by_cases hsd : SilentlyDiverges c s
  · exact Or.inl hsd
  have hT : ∀ t s₁, BigStep c s t s₁ → ∃ s₁', BigStep c' s t s₁' := fun t s₁ h => by
    obtain ⟨s₁', h', -⟩ := slice_bigStep_fwd h hS (fun _ _ => rfl); exact ⟨s₁', h'⟩
  have hR : ∀ u, Reach c s u → Reach c' s u := fun u h =>
    reach_of_partial (slice_partial_fwd (partial_of_reach h) hS (fun _ _ => rfl))
  -- The slice has exactly the observable behaviours of the original.
  have heq : ∀ b, ObsBeh c' s b ↔ ObsBeh c s b := by
    by_cases hterm : Terminates c s
    · obtain ⟨t₀, s₀, h₀⟩ := terminates_iff_bigStep.1 hterm
      obtain ⟨s₀', h₀'⟩ := hT t₀ s₀ h₀
      refine obsBeh_congr (fun t => ⟨fun ⟨s₁, h⟩ => ?_, fun ⟨s₁, h⟩ => hT t s₁ h⟩)
        (fun u => ⟨fun h => ?_, hR u⟩)
      · rw [(bigStep_det h h₀').1]; exact ⟨s₀, h₀⟩
      · exact reach_of_prefix (reach_of_bigStep h₀) (reach_le_of_bigStep h₀' h)
    · have hunb : ∀ K, ∃ v, Reach c s v ∧ K < v.length := by
        intro K
        refine Classical.byContradiction fun hne => hsd ?_
        exact silentlyDiverges_iff_bounded.2 ⟨hterm, K, fun v hv =>
          Nat.le_of_not_lt fun hl => hne ⟨v, hv, hl⟩⟩
      have hnt' : ∀ t s₁, ¬ BigStep c' s t s₁ := by
        intro t s₁ h
        obtain ⟨v, hv, hl⟩ := hunb t.length
        have := (reach_le_of_bigStep h (hR v hv)).length_le
        omega
      refine obsBeh_congr (fun t => ⟨fun ⟨s₁, h⟩ => absurd h (hnt' _ _),
          fun ⟨s₁, h⟩ => absurd ⟨t, s₁, termsWith_of_bigStep h⟩ hterm⟩)
        (fun u => ⟨fun h => ?_, hR u⟩)
      obtain ⟨v, hv, hl⟩ := hunb u.length
      rcases reach_chain h (hR v hv) with h' | h'
      · exact reach_of_prefix hv h'
      · have := h'.length_le; omega
  rcases hb with ⟨t, ht⟩ | hb
  · exact Or.inl ⟨t, (heq _).1 ht⟩
  · exact Or.inr ((heq b).1 hb)

/-- Non-vacuity: a classic slice that deletes `while x0 = 0 do x1 := x1 + 1`. -/
theorem classicSlice_refines_forwardProgress_nonvacuous :
    IsClassicSlice (.seq countLoop (.emit (.num 1))) (.seq .skip (.emit (.num 1))) :=
  isClassicSlice_example

/-- Counterexample (the slice hypothesis is needed): dropping the definition of an
emitted variable (not a classic slice, `not_isClassicSlice_drop_definition`) is not a
forward-progress refinement. -/
theorem classicSlice_refines_forwardProgress_needs_slice :
    ¬ IsClassicSlice (.seq (.assign 0 (.num 5)) (.emit (.var 0)))
      (.seq .skip (.emit (.var 0))) ∧
    ¬ Refines FPBeh (.seq (.assign 0 (.num 5)) (.emit (.var 0))) (.seq .skip (.emit (.var 0))) :=
  ⟨not_isClassicSlice_drop_definition,
   not_refines_fp_of_termsWith (s := fun _ => 0)
    (termsWith_seq (termsWith_assign 0 (.num 5) _) (termsWith_emit (.var 0) _))
    (termsWith_seq (termsWith_skip _) (termsWith_emit (.var 0) _)) (by decide)⟩

end Toy.Progress
