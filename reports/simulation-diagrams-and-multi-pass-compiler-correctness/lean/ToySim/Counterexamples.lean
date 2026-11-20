import ToySim.Systems

/-!
# Tightness counterexamples (all fully proved)

Each theorem has the canonical form "a concrete instance satisfies all the
other hypotheses of a result, and the conclusion of that result fails".
Every theorem in this file is proved outright from the definitions.
-/

namespace Toy.Sim

variable {E Res : Type}

/-- `NoBackwardSim L₁ L₂`: there is no backward simulation from `L₁` to `L₂`,
for any index type, index order, and relation. -/
def NoBackwardSim (L₁ L₂ : LTS E Res) : Prop :=
  ¬ ∃ (I : Type) (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop),
      IsBackwardSim L₁ L₂ ord R

/-- `NoBackwardSim` refutes the conclusion of the flip lemma for every forward
relation `R`. -/
theorem not_flip_conclusion_of_noBackwardSim {L₁ L₂ : LTS E Res} {I : Type}
    (R : I → L₁.State → L₂.State → Prop) (h : NoBackwardSim L₁ L₂) :
    ¬ ∃ (I' : Type) (ord' : I' → I' → Prop) (R' : I' → L₁.State → L₂.State → Prop),
        IsBackwardSim L₁ L₂ ord' R' ∧ ∀ i s₁ s₂, R i s₁ s₂ → ∃ i', R' i' s₁ s₂ :=
  fun ⟨I', ord', R', hb, _⟩ => h ⟨I', ord', R', hb⟩

/-- If the source has an initial state and no stuck state, and the target has
a terminating behaviour the source lacks, then no backward simulation exists
and the target does not refine the source. -/
theorem extra_terminates_no_backwardSim_not_refinedBy {L₁ L₂ : LTS E Res}
    (hns : ∀ s, ¬ Stuck L₁ s) (hinit : ∃ s, L₁.init s) {t : List E} {r : Res}
    (h₂ : HasBehavior L₂ (.terminates t r)) (h₁ : ¬ HasBehavior L₁ (.terminates t r)) :
    NoBackwardSim L₁ L₂ ∧ ¬ RefinedBy L₁ L₂ :=
  ⟨no_backwardSim_of_extra_terminates (safe_of_no_stuck hns) hinit h₂ h₁,
   not_refinedBy_of_extra_behavior (neverGoesWrong_of_no_stuck hns hinit) h₂ h₁⟩

/-- A one-pass pipeline whose first language has an initial state and no stuck
state, and whose last language has a terminating behaviour the first lacks:
the first language never goes wrong, the last does not refine it, and the two
do not have the same behaviours. -/
theorem pipeline_fails_of_extra_terminates {L₁ L₂ : LTS E Res} {I : Type}
    {ord : I → I → Prop} {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsForwardSim L₁ L₂ ord R) (hns : ∀ s, ¬ Stuck L₁ s) (hinit : ∃ s, L₁.init s)
    {t : List E} {r : Res}
    (h₂ : HasBehavior L₂ (.terminates t r)) (h₁ : ¬ HasBehavior L₁ (.terminates t r)) :
    FSimChain L₁ L₂ ∧ NeverGoesWrong L₁ ∧ ¬ RefinedBy L₁ L₂ ∧
    ¬ (HasBehavior L₂ (.terminates t r) ↔ HasBehavior L₁ (.terminates t r)) :=
  ⟨fsimChain_of_isForwardSim hsim, neverGoesWrong_of_no_stuck hns hinit,
    (extra_terminates_no_backwardSim_not_refinedBy hns hinit h₂ h₁).2,
    fun h => h₁ (h.1 h₂)⟩

namespace Cex
open Ex

/-! ## Shared ingredients -/

/-- The always-true relation with a one-point index. -/
abbrev relTrue {α β : Type} : Unit → α → β → Prop := fun _ _ _ => True

/-- The always-false relation with a one-point index. -/
abbrev relFalse {α β : Type} : Unit → α → β → Prop := fun _ _ _ => False

/-- The identity relation with a one-point index. -/
abbrev relEq {α : Type} : Unit → α → α → Prop := fun _ s s' => s = s'

/-- The empty order on the one-point index (well-founded). -/
abbrev emptyOrd : Unit → Unit → Prop := fun _ _ => False

/-- The full order on the one-point index (not well-founded). -/
abbrev fullOrd : Unit → Unit → Prop := fun _ _ => True

theorem wf_emptyOrd : WellFounded emptyOrd :=
  ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩

theorem not_wf_fullOrd : ¬ WellFounded fullOrd := by
  intro h
  have key : ∀ a : Unit, Acc fullOrd a → False := by
    intro a ha
    induction ha with
    | intro a _ ih => exact ih a trivial
  exact key () (h.apply ())

theorem done_receptive (M : Nat → Nat → Prop) (r : Nat) : Receptive M (Done r) :=
  fun _ _ _ _ h _ => h.elim

theorem done_determinate (M : Nat → Nat → Prop) (r : Nat) : Determinate M (Done r) where
  labels := fun _ _ _ _ _ h _ => h.elim
  functional := fun _ _ _ _ h _ => h.elim
  init := fun _ _ _ _ => rfl
  finalNoStep := fun _ _ _ _ _ h => h
  finalDet := by
    intro s r₁ r₂ h h'
    have h1 : r₁ = r := h
    have h2 : r₂ = r := h'
    rw [h1, h2]

theorem done_no_stuck (r : Nat) (s : (Done r).State) : ¬ Stuck (Done r) s :=
  fun h => h.2 r rfl

theorem loop_no_stuck (s : Loop.State) : ¬ Stuck Loop s :=
  fun h => h.1 none () rfl

theorem loop_receptive (M : Nat → Nat → Prop) : Receptive M Loop := by
  intro s a s₁ b h _
  cases h

theorem noInit_determinate (M : Nat → Nat → Prop) : Determinate M NoInit where
  labels := fun _ _ _ _ _ h _ => h.elim
  functional := fun _ _ _ _ h _ => h.elim
  init := fun _ _ _ _ => rfl
  finalNoStep := fun _ _ _ _ _ h => h
  finalDet := fun _ _ _ h _ => h.elim

theorem done_lacks {r : Nat} {b : Behavior Nat Nat} (hne : b ≠ .terminates [] r) :
    ¬ HasBehavior (Done r) b :=
  fun h => hne ((done_behavior r b).1 h)

theorem loop_lacks {b : Behavior Nat Nat} (hne : b ≠ .diverges []) :
    ¬ HasBehavior Loop b :=
  fun h => hne ((loop_behavior b).1 h)

theorem oneStep_lacks {e : Option Nat} {r : Nat} {b : Behavior Nat Nat}
    (hne : b ≠ .terminates (obs e) r) : ¬ HasBehavior (OneStep e r) b :=
  fun h => hne ((oneStep_behavior e r b).1 h)

theorem done_has (r : Nat) : HasBehavior (Done r) (.terminates [] r) :=
  (done_behavior r _).2 rfl

theorem loop_has : HasBehavior Loop (.diverges []) :=
  (loop_behavior _).2 rfl

theorem oneStep_has (e : Option Nat) (r : Nat) :
    HasBehavior (OneStep e r) (.terminates (obs e) r) :=
  (oneStep_behavior e r _).2 rfl

/-- No execution of `Done r` emits an event. -/
theorem done_no_event_run {r : Nat} {s s' : (Done r).State} {a : Nat} {t : List Nat} :
    ¬ Star (Done r) s (a :: t) s' := by
  intro h
  have := (Star.of_noStep (L := Done r) (fun _ _ h => h) h).1
  cases this

/-! ## Forward simulation and preservation of behaviours -/

/-- **No measure (infinite stuttering).**  With an index order that is not
well-founded, all three forward clauses hold between a source that diverges
silently and a target that terminates at once: the target matches every
source step by doing nothing.  Silent divergence is not preserved. -/
theorem cex_fsim_without_wf_divergence_not_preserved :
    ¬ WellFounded fullOrd ∧
    FSimInit Loop (Done 0) relTrue ∧
    FSimFinal Loop (Done 0) relTrue ∧
    FSimStep Loop (Done 0) fullOrd relTrue ∧
    HasBehavior Loop (.diverges []) ∧
    ¬ HasBehavior (Done 0) (.diverges []) ∧
    HasBehavior (Done 0) (.terminates [] 0) ∧
    (∀ t, (Behavior.diverges [] : Behavior Nat Nat) ≠ .goesWrong t) := by
  refine ⟨not_wf_fullOrd, ?_, ?_, ?_, loop_has, done_lacks (by simp), done_has 0,
    (fun _ h => by cases h)⟩
  · exact fun _ _ => ⟨(), (), trivial, trivial⟩
  · exact fun _ _ _ _ _ h => h.elim
  · intro i s₁ s₂ e s₁' _ hstep
    have he : e = none := hstep
    subst he
    exact ⟨(), s₂, Or.inr ⟨Star.refl s₂, trivial⟩, trivial⟩

/-- **Initial-state clause dropped (terminating source).**  The forward final
clause and step diagram hold vacuously for the empty relation between a
terminating source and a target with no initial state; the source run is not
simulated and termination is not preserved. -/
theorem cex_fsim_without_init_clause :
    WellFounded emptyOrd ∧
    FSimFinal (Done 0) NoInit relFalse ∧
    FSimStep (Done 0) NoInit emptyOrd relFalse ∧
    (Done 0).init () ∧ Star (Done 0) () [] () ∧
    (¬ ∃ (i₀ i : Unit) (s₀' s' : NoInit.State),
        NoInit.init s₀' ∧ relFalse i₀ () s₀' ∧ Star NoInit s₀' [] s' ∧ relFalse i () s') ∧
    HasBehavior (Done 0) (.terminates [] 0) ∧
    ¬ HasBehavior NoInit (.terminates [] 0) ∧
    (∀ t, (Behavior.terminates [] 0 : Behavior Nat Nat) ≠ .goesWrong t) := by
  refine ⟨wf_emptyOrd, ?_, ?_, trivial, Star.refl _, ?_, done_has 0, ?_, (fun _ h => by cases h)⟩
  · exact fun _ _ _ _ h _ => h.elim
  · exact fun _ _ _ _ _ h _ => h.elim
  · rintro ⟨_, _, _, _, h, _⟩
    exact h
  · intro h
    have := (noInit_behavior _).1 h
    simp at this

/-- **Initial-state clause dropped (diverging source).** -/
theorem cex_fsim_without_init_clause_diverges :
    WellFounded emptyOrd ∧
    FSimStep Loop NoInit emptyOrd relFalse ∧
    HasBehavior Loop (.diverges []) ∧
    ¬ HasBehavior NoInit (.diverges []) ∧
    (∀ t, (Behavior.diverges [] : Behavior Nat Nat) ≠ .goesWrong t) := by
  refine ⟨wf_emptyOrd, ?_, loop_has, ?_, (fun _ h => by cases h)⟩
  · exact fun _ _ _ _ _ h _ => h.elim
  · intro h
    have := (noInit_behavior _).1 h
    simp at this

/-- **Final-state clause dropped.**  The always-true relation between two
programs that terminate at once with different results satisfies the forward
initial-state clause and step diagram; termination with result `0` is not
preserved. -/
theorem cex_fsim_without_final_clause :
    WellFounded emptyOrd ∧
    FSimInit (Done 0) (Done 1) relTrue ∧
    FSimStep (Done 0) (Done 1) emptyOrd relTrue ∧
    HasBehavior (Done 0) (.terminates [] 0) ∧
    ¬ HasBehavior (Done 1) (.terminates [] 0) ∧
    (∀ t, (Behavior.terminates [] 0 : Behavior Nat Nat) ≠ .goesWrong t) := by
  refine ⟨wf_emptyOrd, ?_, ?_, done_has 0, done_lacks (by simp), (fun _ h => by cases h)⟩
  · exact fun _ _ => ⟨(), (), trivial, trivial⟩
  · exact fun _ _ _ _ _ _ h => h.elim

/-- The relation used when the step diagram is dropped: only the source state
before its step is related to the target. -/
abbrev relBefore : Unit → Bool → Unit → Prop := fun _ s _ => s = false

/-- **Step diagram dropped (terminating source).**  A source that emits the
event `7` and returns `0`, a target that returns `0` at once, and a relation
that only covers the source's initial state: the forward initial-state and
final clauses hold; the source run with trace `[7]` is not simulated and its
terminating behaviour is not preserved. -/
theorem cex_fsim_without_step_diagram :
    WellFounded emptyOrd ∧
    FSimInit (OneStep (some 7) 0) (Done 0) relBefore ∧
    FSimFinal (OneStep (some 7) 0) (Done 0) relBefore ∧
    (OneStep (some 7) 0).init false ∧ Star (OneStep (some 7) 0) false [7] true ∧
    (¬ ∃ (i₀ i : Unit) (s₀' s' : (Done 0).State),
        (Done 0).init s₀' ∧ relBefore i₀ false s₀' ∧ Star (Done 0) s₀' [7] s' ∧
          relBefore i true s') ∧
    HasBehavior (OneStep (some 7) 0) (.terminates [7] 0) ∧
    ¬ HasBehavior (Done 0) (.terminates [7] 0) ∧
    (∀ t, (Behavior.terminates [7] 0 : Behavior Nat Nat) ≠ .goesWrong t) := by
  refine ⟨wf_emptyOrd, ?_, ?_, rfl, ?_, ?_, oneStep_has (some 7) 0, done_lacks (by simp),
    (fun _ h => by cases h)⟩
  · intro s hs
    exact ⟨(), (), trivial, hs⟩
  · intro _ s _ r hR hfin
    have h1 : s = false := hR
    have h2 : s = true := hfin.1
    rw [h1] at h2
    cases h2
  · exact Star.single (L := OneStep (some 7) 0) ⟨rfl, rfl, rfl⟩
  · rintro ⟨_, _, _, _, _, _, hrun, _⟩
    exact done_no_event_run hrun

/-- **Step diagram dropped (diverging source).** -/
theorem cex_fsim_without_step_diagram_diverges :
    WellFounded emptyOrd ∧
    FSimInit Loop (Done 0) relTrue ∧
    HasBehavior Loop (.diverges []) ∧
    ¬ HasBehavior (Done 0) (.diverges []) ∧
    (∀ t, (Behavior.diverges [] : Behavior Nat Nat) ≠ .goesWrong t) :=
  ⟨wf_emptyOrd, fun _ _ => ⟨(), (), trivial, trivial⟩, loop_has, done_lacks (by simp),
    (fun _ h => by cases h)⟩

/-- **Going wrong is not preserved by a forward simulation.**  A source that
is stuck at once is forward-simulated (vacuously) by a target that terminates
normally; the source's going-wrong behaviour is not a target behaviour. -/
theorem cex_forwardSim_goesWrong_not_preserved :
    IsForwardSim StuckNow (Done 0) emptyOrd relTrue ∧
    HasBehavior StuckNow (.goesWrong []) ∧
    ¬ HasBehavior (Done 0) (.goesWrong []) ∧
    FSimChain StuckNow (Done 0) := by
  have hsim : IsForwardSim StuckNow (Done 0) emptyOrd relTrue :=
    ⟨wf_emptyOrd, fun _ _ => ⟨(), (), trivial, trivial⟩, fun _ _ _ _ _ h => h.elim,
      fun _ _ _ _ _ _ h => h.elim⟩
  exact ⟨hsim, (stuckNow_behavior _).2 rfl, done_lacks (by simp), fsimChain_of_isForwardSim hsim⟩

/-- **A going-wrong source may be simulated by a target with no behaviour at
all in this model.**  The stuck source is forward-simulated by a target whose
only run emits events forever; that target has no behaviour here, so "some
target behaviour improves on the source behaviour" fails. -/
theorem cex_forwardSim_goesWrong_target_without_behavior :
    IsForwardSim StuckNow Chatter emptyOrd relTrue ∧
    HasBehavior StuckNow (.goesWrong []) ∧
    ∀ b, ¬ HasBehavior Chatter b := by
  refine ⟨⟨wf_emptyOrd, ?_, ?_, ?_⟩, (stuckNow_behavior _).2 rfl, chatter_no_behavior⟩
  · exact fun _ _ => ⟨(), (), trivial, trivial⟩
  · exact fun _ _ _ _ _ h => h.elim
  · exact fun _ _ _ _ _ _ h => h.elim

/-- **Run not from an initial state.**  The forward clauses say nothing about
source states that are not reachable from an initial state: here the source
has no initial state, the relation is empty, and the (empty) run from the
source's only state is not simulated. -/
theorem cex_partial_run_from_non_initial_state :
    FSimInit NoInit (Done 0) relFalse ∧
    FSimStep NoInit (Done 0) emptyOrd relFalse ∧
    Star NoInit () [] () ∧
    (¬ ∃ (i₀ i : Unit) (s₀' s' : (Done 0).State),
        (Done 0).init s₀' ∧ relFalse i₀ () s₀' ∧ Star (Done 0) s₀' [] s' ∧
          relFalse i () s') := by
  refine ⟨fun _ h => h.elim, fun _ _ _ _ _ h _ => h.elim, Star.refl _, ?_⟩
  rintro ⟨_, _, _, _, _, h, _⟩
  exact h

/-- **No source run.**  Without a source run with trace `t` ending in `s`,
the conclusion of the partial-run theorem can fail: the identity simulation
on a program without steps, and the trace `[7]`. -/
theorem cex_partial_run_without_source_run :
    FSimInit (Done 0) (Done 0) relEq ∧
    FSimStep (Done 0) (Done 0) emptyOrd relEq ∧
    (Done 0).init () ∧
    (¬ ∃ (i₀ i : Unit) (s₀' s' : (Done 0).State),
        (Done 0).init s₀' ∧ relEq i₀ () s₀' ∧ Star (Done 0) s₀' [7] s' ∧ relEq i () s') := by
  refine ⟨(isForwardSim_id (Done 0)).init, (isForwardSim_id (Done 0)).step, trivial, ?_⟩
  rintro ⟨_, _, _, _, _, _, hrun, _⟩
  exact done_no_event_run hrun

/-- **No source behaviour.**  A forward simulation does not give the target
behaviours that the source does not have: the identity simulation on a
program that returns `0`, and the behaviours "return `1`" and "diverge". -/
theorem cex_preservation_without_source_behavior :
    IsForwardSim (Done 0) (Done 0) emptyOrd relEq ∧
    ¬ HasBehavior (Done 0) (.terminates [] 1) ∧
    ¬ HasBehavior (Done 0) (.diverges []) ∧
    FSimChain (Done 0) (Done 0) ∧
    (∀ t, (Behavior.terminates [] 1 : Behavior Nat Nat) ≠ .goesWrong t) ∧
    (∀ t, (Behavior.diverges [] : Behavior Nat Nat) ≠ .goesWrong t) :=
  ⟨isForwardSim_id (Done 0), done_lacks (by simp), done_lacks (by simp), FSimChain.nil _,
    (fun _ h => by cases h), (fun _ h => by cases h)⟩

/-! ## Vertical composition -/

/-- **First step diagram dropped.**  The second relation is a forward
simulation (the identity), the first satisfies every clause except the step
diagram, and the composite fails the step diagram (so it is not a forward
simulation). -/
theorem cex_comp_without_first_step_diagram :
    WellFounded emptyOrd ∧
    FSimInit (OneStep (some 7) 0) (Done 0) relBefore ∧
    FSimFinal (OneStep (some 7) 0) (Done 0) relBefore ∧
    IsForwardSim (Done 0) (Done 0) emptyOrd relEq ∧
    ¬ FSimStep (OneStep (some 7) 0) (Done 0)
        (compOrd emptyOrd emptyOrd) (compRel relBefore relEq) ∧
    ¬ IsForwardSim (OneStep (some 7) 0) (Done 0)
        (compOrd emptyOrd emptyOrd) (compRel relBefore relEq) := by
  have hno : ¬ FSimStep (OneStep (some 7) 0) (Done 0)
      (compOrd emptyOrd emptyOrd) (compRel relBefore relEq) := by
    intro h
    obtain ⟨_, s₃', hmove, _⟩ :=
      h ((), ()) false () (some 7) true ⟨(), rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
    rcases hmove with hp | ⟨hs, _⟩
    · exact done_no_event_run hp.star
    · exact done_no_event_run hs
  exact ⟨wf_emptyOrd, cex_fsim_without_step_diagram.2.1, cex_fsim_without_step_diagram.2.2.1,
    isForwardSim_id (Done 0), hno, fun h => hno h.step⟩

/-- **Second step diagram dropped.**  The first relation is a forward
simulation (the identity), the second satisfies every clause except the step
diagram, and the composite fails the step diagram (so it is not a forward
simulation). -/
theorem cex_comp_without_second_step_diagram :
    IsForwardSim (OneStep (some 7) 0) (OneStep (some 7) 0) emptyOrd relEq ∧
    WellFounded emptyOrd ∧
    FSimInit (OneStep (some 7) 0) (Done 0) relBefore ∧
    FSimFinal (OneStep (some 7) 0) (Done 0) relBefore ∧
    ¬ FSimStep (OneStep (some 7) 0) (Done 0)
        (compOrd emptyOrd emptyOrd) (compRel relEq relBefore) ∧
    ¬ IsForwardSim (OneStep (some 7) 0) (Done 0)
        (compOrd emptyOrd emptyOrd) (compRel relEq relBefore) := by
  have hno : ¬ FSimStep (OneStep (some 7) 0) (Done 0)
      (compOrd emptyOrd emptyOrd) (compRel relEq relBefore) := by
    intro h
    obtain ⟨_, s₃', hmove, _⟩ :=
      h ((), ()) false () (some 7) true ⟨false, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
    rcases hmove with hp | ⟨hs, _⟩
    · exact done_no_event_run hp.star
    · exact done_no_event_run hs
  exact ⟨isForwardSim_id (OneStep (some 7) 0), wf_emptyOrd,
    cex_fsim_without_step_diagram.2.1, cex_fsim_without_step_diagram.2.2.1, hno,
    fun h => hno h.step⟩

/-- **First initial-state clause dropped.**  The second relation is a forward
simulation (the identity on `NoInit`); the first satisfies every clause except
the initial-state clause; the composite fails the initial-state clause (so it
is not a forward simulation). -/
theorem cex_comp_without_first_init :
    WellFounded emptyOrd ∧
    FSimFinal (Done 0) NoInit relFalse ∧
    FSimStep (Done 0) NoInit emptyOrd relFalse ∧
    IsForwardSim NoInit NoInit emptyOrd relEq ∧
    ¬ FSimInit (Done 0) NoInit (compRel relFalse relEq) ∧
    ¬ IsForwardSim (Done 0) NoInit (compOrd emptyOrd emptyOrd) (compRel relFalse relEq) := by
  have hno : ¬ FSimInit (Done 0) NoInit (compRel relFalse relEq) := by
    intro h
    obtain ⟨_, _, hinit, _⟩ := h () trivial
    exact hinit
  exact ⟨wf_emptyOrd, cex_fsim_without_init_clause.2.1, cex_fsim_without_init_clause.2.2.1,
    isForwardSim_id NoInit, hno, fun h => hno h.init⟩

/-- **Second initial-state clause dropped.**  The first relation is a forward
simulation (the identity on `Done 0`); the second satisfies every clause except
the initial-state clause; the composite fails the initial-state clause. -/
theorem cex_comp_without_second_init :
    IsForwardSim (Done 0) (Done 0) emptyOrd relEq ∧
    WellFounded emptyOrd ∧
    FSimFinal (Done 0) NoInit relFalse ∧
    FSimStep (Done 0) NoInit emptyOrd relFalse ∧
    ¬ FSimInit (Done 0) NoInit (compRel relEq relFalse) ∧
    ¬ IsForwardSim (Done 0) NoInit (compOrd emptyOrd emptyOrd) (compRel relEq relFalse) := by
  have hno : ¬ FSimInit (Done 0) NoInit (compRel relEq relFalse) := by
    intro h
    obtain ⟨_, _, hinit, _⟩ := h () trivial
    exact hinit
  exact ⟨isForwardSim_id (Done 0), wf_emptyOrd, cex_fsim_without_init_clause.2.1,
    cex_fsim_without_init_clause.2.2.1, hno, fun h => hno h.init⟩

/-- **First final-state clause dropped.**  The second relation is a forward
simulation (the identity on `Done 1`); the first satisfies every clause except
the final-state clause; the composite fails the final-state clause. -/
theorem cex_comp_without_first_final :
    WellFounded emptyOrd ∧
    FSimInit (Done 0) (Done 1) relTrue ∧
    FSimStep (Done 0) (Done 1) emptyOrd relTrue ∧
    IsForwardSim (Done 1) (Done 1) emptyOrd relEq ∧
    ¬ FSimFinal (Done 0) (Done 1) (compRel relTrue relEq) ∧
    ¬ IsForwardSim (Done 0) (Done 1) (compOrd emptyOrd emptyOrd) (compRel relTrue relEq) := by
  have hno : ¬ FSimFinal (Done 0) (Done 1) (compRel relTrue relEq) := by
    intro h
    have h01 : (0 : Nat) = 1 := h ((), ()) () () 0 ⟨(), trivial, rfl⟩ rfl
    simp at h01
  exact ⟨wf_emptyOrd, cex_fsim_without_final_clause.2.1, cex_fsim_without_final_clause.2.2.1,
    isForwardSim_id (Done 1), hno, fun h => hno h.final⟩

/-- **Second final-state clause dropped.**  The first relation is a forward
simulation (the identity on `Done 0`); the second satisfies every clause except
the final-state clause; the composite fails the final-state clause. -/
theorem cex_comp_without_second_final :
    IsForwardSim (Done 0) (Done 0) emptyOrd relEq ∧
    WellFounded emptyOrd ∧
    FSimInit (Done 0) (Done 1) relTrue ∧
    FSimStep (Done 0) (Done 1) emptyOrd relTrue ∧
    ¬ FSimFinal (Done 0) (Done 1) (compRel relEq relTrue) ∧
    ¬ IsForwardSim (Done 0) (Done 1) (compOrd emptyOrd emptyOrd) (compRel relEq relTrue) := by
  have hno : ¬ FSimFinal (Done 0) (Done 1) (compRel relEq relTrue) := by
    intro h
    have h01 : (0 : Nat) = 1 := h ((), ()) () () 0 ⟨(), rfl, trivial⟩ rfl
    simp at h01
  exact ⟨isForwardSim_id (Done 0), wf_emptyOrd, cex_fsim_without_final_clause.2.1,
    cex_fsim_without_final_clause.2.2.1, hno, fun h => hno h.final⟩

/-- Three states in a row: `root → left → right` by silent steps; `right` is
final with result `0`. -/
abbrev Chain3 : LTS Nat Nat where
  State := Three
  step := fun s e s' =>
    e = none ∧ ((s = .root ∧ s' = .left) ∨ (s = .left ∧ s' = .right))
  init := fun s => s = .root
  final := fun s r => s = .right ∧ r = 0

/-- First-pass relation for the order counterexample: the single source step
is matched by the two steps of `Chain3`. -/
def chainRel₁ : Unit → Bool → Three → Prop :=
  fun _ s s' => (s = false ∧ s' = .root) ∨ (s = true ∧ s' = .right)

/-- Second-pass relation for the order counterexample: the target never
moves, and the index counts the remaining steps of `Chain3`. -/
def chainRel₂ : Nat → Three → Unit → Prop :=
  fun i s _ => (s = .root ∧ i = 2) ∨ (s = .left ∧ i = 1) ∨ (s = .right ∧ i = 0)

/-- The successor order on `Nat`: well-founded but not transitive. -/
def succOrd : Nat → Nat → Prop := fun i' i => i' + 1 = i

/-- The lexicographic order *without* transitive closure on the first
component. -/
def naiveCompOrd {I₁ I₂ : Type} (ord₁ : I₁ → I₁ → Prop) (ord₂ : I₂ → I₂ → Prop) :
    I₂ × I₁ → I₂ × I₁ → Prop :=
  fun p q => ord₂ p.1 q.1 ∨ (p.1 = q.1 ∧ ord₁ p.2 q.2)

theorem wf_succOrd : WellFounded succOrd := by
  refine Subrelation.wf (r := fun i' i : Nat => i' < i) ?_ Nat.lt_wfRel.wf
  intro a b h
  have h' : a + 1 = b := h
  show a < b
  omega

/-- When the second-pass order is transitive, `compOrd` and `naiveCompOrd`
coincide, so the transitive closure only matters for non-transitive orders
such as `succOrd`. -/
theorem compOrd_iff_naiveCompOrd_of_transitive {I₁ I₂ : Type} {ord₁ : I₁ → I₁ → Prop}
    {ord₂ : I₂ → I₂ → Prop} (htrans : ∀ a b c, ord₂ a b → ord₂ b c → ord₂ a c)
    (p q : I₂ × I₁) : compOrd ord₁ ord₂ p q ↔ naiveCompOrd ord₁ ord₂ p q :=
  compOrd_iff_lex_of_transitive htrans p q

/-- `succOrd` is not transitive. -/
theorem succOrd_not_transitive : ¬ ∀ a b c, succOrd a b → succOrd b c → succOrd a c := by
  intro h
  have h' : (0 : Nat) + 1 = 2 := h 0 1 2 rfl rfl
  omega

theorem chain3_plus : Plus Chain3 .root [] .right :=
  ⟨none, .left, [], ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩,
    Star.single (L := Chain3) (e := none) ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩

theorem oneStep_chain3_isForwardSim :
    IsForwardSim (OneStep none 0) Chain3 emptyOrd chainRel₁ where
  wf := wf_emptyOrd
  init := by
    intro s hs
    exact ⟨(), .root, rfl, Or.inl ⟨hs, rfl⟩⟩
  final := by
    intro _ s s' r hR hfin
    have hs : s = true := hfin.1
    rcases hR with ⟨h, _⟩ | ⟨_, h'⟩
    · rw [hs] at h; cases h
    · exact ⟨h', hfin.2⟩
  step := by
    intro _ s s' e s₁ hR hstep
    obtain ⟨hs, he, hs₁⟩ := hstep
    rcases hR with ⟨_, h'⟩ | ⟨h, _⟩
    · subst h' he hs₁
      exact ⟨(), .right, Or.inl chain3_plus, Or.inr ⟨rfl, rfl⟩⟩
    · rw [hs] at h; cases h

theorem chain3_done_isForwardSim :
    IsForwardSim Chain3 (Done 0) succOrd chainRel₂ where
  wf := wf_succOrd
  init := by
    intro s hs
    exact ⟨2, (), trivial, Or.inl ⟨hs, rfl⟩⟩
  final := by
    intro _ s s' r _ hfin
    exact hfin.2
  step := by
    intro i s s' e s₁ hR hstep
    obtain ⟨he, hmove⟩ := hstep
    subst he
    rcases hmove with ⟨hs, hs₁⟩ | ⟨hs, hs₁⟩
    · subst hs hs₁
      rcases hR with ⟨_, hi⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · subst hi
        exact ⟨1, s', Or.inr ⟨Star.refl s', rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · cases h
      · cases h
    · subst hs hs₁
      rcases hR with ⟨h, _⟩ | ⟨_, hi⟩ | ⟨h, _⟩
      · cases h
      · subst hi
        exact ⟨0, s', Or.inr ⟨Star.refl s', rfl⟩, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      · cases h

/-- **The transitive closure in the composite order is necessary.**  Two
forward simulations whose composite relation fails the step diagram for the
naive lexicographic order (no transitive closure), because one source step
expands to two middle steps that each stutter in the last system.  With
`compOrd` the same composite relation satisfies the step diagram. -/
theorem cex_comp_naive_lex_order_fails :
    IsForwardSim (OneStep none 0) Chain3 emptyOrd chainRel₁ ∧
    IsForwardSim Chain3 (Done 0) succOrd chainRel₂ ∧
    ¬ FSimStep (OneStep none 0) (Done 0)
        (naiveCompOrd emptyOrd succOrd) (compRel chainRel₁ chainRel₂) ∧
    FSimStep (OneStep none 0) (Done 0)
        (compOrd emptyOrd succOrd) (compRel chainRel₁ chainRel₂) := by
  refine ⟨oneStep_chain3_isForwardSim, chain3_done_isForwardSim, ?_, ?_⟩
  · intro h
    obtain ⟨i', s₃', hmove, hR'⟩ :=
      h (2, ()) false () none true
        ⟨.root, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩ ⟨rfl, rfl, rfl⟩
    -- the composite relation at the source's final state forces index `0`
    have hi' : i'.1 = 0 := by
      obtain ⟨s₂, h₁, h₂⟩ := hR'
      rcases h₁ with ⟨h, _⟩ | ⟨_, hs₂⟩
      · cases h
      · subst hs₂
        rcases h₂ with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hi⟩
        · cases h
        · cases h
        · exact hi
    rcases hmove with hp | ⟨_, hord⟩
    · obtain ⟨_, _, _, hstep, _, _⟩ := hp
      exact hstep
    · rcases hord with h | ⟨h, _⟩
      · have h' : i'.1 + 1 = 2 := h
        omega
      · have h' : i'.1 = 2 := h
        omega
  · intro i s₁ s₃ e s₁' hR hstep
    obtain ⟨hs, he, hs₁⟩ := hstep
    subst hs he hs₁
    obtain ⟨s₂, h₁, h₂⟩ := hR
    rcases h₁ with ⟨_, hs₂⟩ | ⟨h, _⟩
    · subst hs₂
      rcases h₂ with ⟨_, hi⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · refine ⟨(0, ()), s₃, Or.inr ⟨Star.refl s₃, Or.inl ?_⟩,
          .right, Or.inr ⟨rfl, rfl⟩, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
        rw [hi]
        exact Relation.TransGen.tail (Relation.TransGen.single (rfl : succOrd 0 1))
          (rfl : succOrd 1 2)
      · cases h
      · cases h
    · cases h

/-! ## Flipping a forward simulation, and end-to-end refinement

Each theorem below gives a forward simulation together with all hypotheses of
the flip lemma except one, and shows that no backward simulation exists and
that the target does not refine the source.  A one-pass pipeline is a chain,
so these are also counterexamples for the end-to-end theorem. -/

/-- **Well-foundedness dropped.**  The three forward clauses hold with a
non-well-founded order between a diverging source and a target that
terminates at once; source is receptive and target determinate for every
matching relation; no backward simulation exists. -/
theorem cex_flip_without_wf (M : Nat → Nat → Prop) :
    FSimInit Loop (Done 0) relTrue ∧
    FSimFinal Loop (Done 0) relTrue ∧
    FSimStep Loop (Done 0) fullOrd relTrue ∧
    Receptive M Loop ∧ Determinate M (Done 0) ∧
    NoBackwardSim Loop (Done 0) ∧ ¬ RefinedBy Loop (Done 0) := by
  obtain ⟨_, h1, h2, h3, _, _, _⟩ := cex_fsim_without_wf_divergence_not_preserved
  have key := extra_terminates_no_backwardSim_not_refinedBy
    (L₁ := Loop) (L₂ := Done 0) loop_no_stuck ⟨(), trivial⟩ (done_has 0)
    (loop_lacks (by simp))
  exact ⟨h1, h2, h3, loop_receptive M, done_determinate M 0, key.1, key.2⟩

/-- **Forward initial-state clause dropped.** -/
theorem cex_flip_without_init_clause (M : Nat → Nat → Prop) :
    WellFounded emptyOrd ∧
    FSimFinal (Done 0) NoInit relFalse ∧
    FSimStep (Done 0) NoInit emptyOrd relFalse ∧
    Receptive M (Done 0) ∧ Determinate M NoInit ∧
    NoBackwardSim (Done 0) NoInit ∧ ¬ RefinedBy (Done 0) NoInit := by
  obtain ⟨_, h1, h2, _⟩ := cex_fsim_without_init_clause
  refine ⟨wf_emptyOrd, h1, h2, done_receptive M 0, noInit_determinate M, ?_, ?_⟩
  · rintro ⟨I, ord, R, hb⟩
    obtain ⟨_, h⟩ := hb.initExists ⟨(), trivial⟩
    exact h
  · exact not_refinedBy_of_extra_behavior (done_neverGoesWrong 0)
      ((noInit_behavior _).2 rfl) (done_lacks (by simp))

/-- **Forward final-state clause dropped.** -/
theorem cex_flip_without_final_clause (M : Nat → Nat → Prop) :
    WellFounded emptyOrd ∧
    FSimInit (Done 0) (Done 1) relTrue ∧
    FSimStep (Done 0) (Done 1) emptyOrd relTrue ∧
    Receptive M (Done 0) ∧ Determinate M (Done 1) ∧
    NoBackwardSim (Done 0) (Done 1) ∧ ¬ RefinedBy (Done 0) (Done 1) := by
  obtain ⟨_, h1, h2, _⟩ := cex_fsim_without_final_clause
  have key := extra_terminates_no_backwardSim_not_refinedBy
    (L₁ := Done 0) (L₂ := Done 1) (done_no_stuck 0) ⟨(), trivial⟩ (done_has 1)
    (done_lacks (by simp))
  exact ⟨wf_emptyOrd, h1, h2, done_receptive M 0, done_determinate M 1, key.1, key.2⟩

/-- **Forward step diagram dropped.** -/
theorem cex_flip_without_step_diagram :
    WellFounded emptyOrd ∧
    FSimInit (OneStep (some 7) 0) (Done 0) relBefore ∧
    FSimFinal (OneStep (some 7) 0) (Done 0) relBefore ∧
    Receptive Eq (OneStep (some 7) 0) ∧ Determinate Eq (Done 0) ∧
    NoBackwardSim (OneStep (some 7) 0) (Done 0) ∧
    ¬ RefinedBy (OneStep (some 7) 0) (Done 0) := by
  obtain ⟨_, h1, h2, _⟩ := cex_fsim_without_step_diagram
  have key := extra_terminates_no_backwardSim_not_refinedBy
    (L₁ := OneStep (some 7) 0) (L₂ := Done 0) (oneStep_no_stuck (some 7) 0) ⟨false, rfl⟩
    (done_has 0) (oneStep_lacks (by simp))
  exact ⟨wf_emptyOrd, h1, h2, receptive_eq _, done_determinate Eq 0, key.1, key.2⟩

theorem twoBranch_stepFunctional {e₁ e₂ : Option Nat} (r₁ r₂ : Nat) (hne : e₁ ≠ e₂) :
    StepFunctional (TwoBranch e₁ e₂ r₁ r₂) := by
  intro s e s₁ s₂ h₁ h₂
  obtain ⟨_, h₁⟩ := h₁
  obtain ⟨_, h₂⟩ := h₂
  rcases h₁ with ⟨he, hs₁⟩ | ⟨he, hs₁⟩ <;> rcases h₂ with ⟨he', hs₂⟩ | ⟨he', hs₂⟩
  · rw [hs₁, hs₂]
  · exact absurd (he.symm.trans he') hne
  · exact absurd (he'.symm.trans he) hne
  · rw [hs₁, hs₂]

theorem twoBranch_stepLabelsMatch (M : Nat → Nat → Prop) {e₁ e₂ : Option Nat} (r₁ r₂ : Nat)
    (h₁₁ : LabelMatch M e₁ e₁) (h₁₂ : LabelMatch M e₁ e₂)
    (h₂₁ : LabelMatch M e₂ e₁) (h₂₂ : LabelMatch M e₂ e₂) :
    StepLabelsMatch M (TwoBranch e₁ e₂ r₁ r₂) := by
  intro s e s₁ e' s₂ h h'
  obtain ⟨_, h⟩ := h
  obtain ⟨_, h'⟩ := h'
  rcases h with ⟨he, _⟩ | ⟨he, _⟩ <;> rcases h' with ⟨he', _⟩ | ⟨he', _⟩ <;>
    (rw [he, he']; assumption)

/-- **Non-receptive source.**  The source can only receive the input `0`; the
target can receive `0` or `1` and is determinate when any two inputs match.
A forward simulation exists, yet the target has the behaviour "receive `1`,
return `1`" that the source does not allow, and no backward simulation
exists. -/
theorem cex_flip_nonreceptive_source :
    IsForwardSim (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) emptyOrd branchRel ∧
    Determinate AnyInput (TwoBranch (some 0) (some 1) 0 1) ∧
    ¬ Receptive AnyInput (OneStep (some 0) 0) ∧
    HasBehavior (TwoBranch (some 0) (some 1) 0 1) (.terminates [1] 1) ∧
    ¬ HasBehavior (OneStep (some 0) 0) (.terminates [1] 1) ∧
    NoBackwardSim (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) ∧
    ¬ RefinedBy (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) := by
  have hextra : HasBehavior (TwoBranch (some 0) (some 1) 0 1) (.terminates [1] 1) :=
    twoBranch_right_behavior (some 0) (some 1) 0 1
  have hlack : ¬ HasBehavior (OneStep (some 0) 0) (.terminates [1] 1) :=
    oneStep_lacks (by simp)
  have key := extra_terminates_no_backwardSim_not_refinedBy
    (oneStep_no_stuck (some 0) 0) ⟨false, rfl⟩ hextra hlack
  refine ⟨oneStep_twoBranch_isForwardSim _ _ _ _, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hextra, hlack,
    key.1, key.2⟩
  · exact twoBranch_stepLabelsMatch AnyInput 0 1 trivial trivial trivial trivial
  · exact twoBranch_stepFunctional 0 1 (by simp)
  · exact twoBranch_initDeterminate _ _ _ _
  · exact twoBranch_finalNoStep _ _ _ _
  · exact twoBranch_finalDeterminate _ _ _ _
  · intro h
    obtain ⟨s₂, hstep⟩ := h false 0 true 1 ⟨rfl, rfl, rfl⟩ trivial
    have : some 1 = some 0 := hstep.2.1
    simp at this

/-- **Target labels do not match.**  The target offers a silent step and an
event from the same state; every other determinacy clause holds, and the
source is receptive (events only match themselves).  A forward simulation
exists, yet the target has an extra behaviour and no backward simulation
exists. -/
theorem cex_flip_target_labels_mismatch :
    IsForwardSim (OneStep none 0) (TwoBranch none (some 1) 0 1) emptyOrd branchRel ∧
    Receptive Eq (OneStep none 0) ∧
    ¬ StepLabelsMatch Eq (TwoBranch none (some 1) 0 1) ∧
    StepFunctional (TwoBranch none (some 1) 0 1) ∧
    InitDeterminate (TwoBranch none (some 1) 0 1) ∧
    FinalNoStep (TwoBranch none (some 1) 0 1) ∧
    FinalDeterminate (TwoBranch none (some 1) 0 1) ∧
    HasBehavior (TwoBranch none (some 1) 0 1) (.terminates [1] 1) ∧
    ¬ HasBehavior (OneStep none 0) (.terminates [1] 1) ∧
    NoBackwardSim (OneStep none 0) (TwoBranch none (some 1) 0 1) ∧
    ¬ RefinedBy (OneStep none 0) (TwoBranch none (some 1) 0 1) := by
  have hextra : HasBehavior (TwoBranch none (some 1) 0 1) (.terminates [1] 1) :=
    twoBranch_right_behavior none (some 1) 0 1
  have hlack : ¬ HasBehavior (OneStep none 0) (.terminates [1] 1) :=
    oneStep_lacks (by simp)
  have key := extra_terminates_no_backwardSim_not_refinedBy
    (oneStep_no_stuck none 0) ⟨false, rfl⟩ hextra hlack
  refine ⟨oneStep_twoBranch_isForwardSim _ _ _ _, receptive_eq _, ?_,
    twoBranch_stepFunctional 0 1 (by simp), twoBranch_initDeterminate _ _ _ _,
    twoBranch_finalNoStep _ _ _ _, twoBranch_finalDeterminate _ _ _ _, hextra, hlack,
    key.1, key.2⟩
  intro h
  exact h .root none .left (some 1) .right ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩ ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- **Target offers two unmatched events.**  The target offers the events `0`
and `1` from the same state, which do not match when events only match
themselves; every other determinacy clause holds and the source is receptive
for `Eq`.  A forward simulation exists, yet the target has an extra behaviour
and no backward simulation exists.  (Event-versus-event case of
`StepLabelsMatch`; `cex_flip_target_labels_mismatch` is the silent-versus-event
case.) -/
theorem cex_flip_target_event_labels_mismatch :
    IsForwardSim (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) emptyOrd branchRel ∧
    Receptive Eq (OneStep (some 0) 0) ∧
    ¬ StepLabelsMatch Eq (TwoBranch (some 0) (some 1) 0 1) ∧
    StepFunctional (TwoBranch (some 0) (some 1) 0 1) ∧
    InitDeterminate (TwoBranch (some 0) (some 1) 0 1) ∧
    FinalNoStep (TwoBranch (some 0) (some 1) 0 1) ∧
    FinalDeterminate (TwoBranch (some 0) (some 1) 0 1) ∧
    HasBehavior (TwoBranch (some 0) (some 1) 0 1) (.terminates [1] 1) ∧
    ¬ HasBehavior (OneStep (some 0) 0) (.terminates [1] 1) ∧
    NoBackwardSim (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) ∧
    ¬ RefinedBy (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) := by
  obtain ⟨hsim, hdet, _, hextra, hlack, hno, hnref⟩ := cex_flip_nonreceptive_source
  refine ⟨hsim, receptive_eq _, ?_, hdet.functional, hdet.init, hdet.finalNoStep,
    hdet.finalDet, hextra, hlack, hno, hnref⟩
  intro h
  have h01 : (0 : Nat) = 1 :=
    h .root (some 0) .left (some 1) .right ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩ ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  simp at h01

/-- **Nondeterministic target.**  The target has two silent steps from its
initial state, leading to different results; every other determinacy clause
holds and the source is receptive.  A forward simulation exists, yet the
target has the extra behaviour "return `1`" and no backward simulation
exists. -/
theorem cex_flip_target_not_functional :
    IsForwardSim (OneStep none 0) (TwoBranch none none 0 1) emptyOrd branchRel ∧
    Receptive Eq (OneStep none 0) ∧
    StepLabelsMatch Eq (TwoBranch none none 0 1) ∧
    ¬ StepFunctional (TwoBranch none none 0 1) ∧
    InitDeterminate (TwoBranch none none 0 1) ∧
    FinalNoStep (TwoBranch none none 0 1) ∧
    FinalDeterminate (TwoBranch none none 0 1) ∧
    HasBehavior (TwoBranch none none 0 1) (.terminates [] 1) ∧
    ¬ HasBehavior (OneStep none 0) (.terminates [] 1) ∧
    NoBackwardSim (OneStep none 0) (TwoBranch none none 0 1) ∧
    ¬ RefinedBy (OneStep none 0) (TwoBranch none none 0 1) := by
  have hextra : HasBehavior (TwoBranch none none 0 1) (.terminates [] 1) :=
    twoBranch_right_behavior none none 0 1
  have hlack : ¬ HasBehavior (OneStep none 0) (.terminates [] 1) :=
    oneStep_lacks (by simp)
  have key := extra_terminates_no_backwardSim_not_refinedBy
    (oneStep_no_stuck none 0) ⟨false, rfl⟩ hextra hlack
  refine ⟨oneStep_twoBranch_isForwardSim _ _ _ _, receptive_eq _,
    twoBranch_stepLabelsMatch Eq 0 1 trivial trivial trivial trivial, ?_,
    twoBranch_initDeterminate _ _ _ _, twoBranch_finalNoStep _ _ _ _,
    twoBranch_finalDeterminate _ _ _ _, hextra, hlack, key.1, key.2⟩
  intro h
  have := h .root none .left .right ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩ ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  cases this

/-- The relation used for the two-initial-states counterexample: the source
state is related to the target's first initial state only. -/
abbrev relToFalse : Unit → Unit → Bool → Prop := fun _ _ s' => s' = false

/-- **Target with two initial states.**  Every determinacy clause except
uniqueness of the initial state holds.  A forward simulation exists, yet the
target has the extra behaviour "return `1`" and no backward simulation
exists. -/
theorem cex_flip_target_two_initial_states (M : Nat → Nat → Prop) :
    IsForwardSim (Done 0) TwoInits emptyOrd relToFalse ∧
    Receptive M (Done 0) ∧
    StepLabelsMatch M TwoInits ∧ StepFunctional TwoInits ∧
    ¬ InitDeterminate TwoInits ∧
    FinalNoStep TwoInits ∧ FinalDeterminate TwoInits ∧
    HasBehavior TwoInits (.terminates [] 1) ∧
    ¬ HasBehavior (Done 0) (.terminates [] 1) ∧
    NoBackwardSim (Done 0) TwoInits ∧ ¬ RefinedBy (Done 0) TwoInits := by
  have hextra : HasBehavior TwoInits (.terminates [] 1) :=
    ⟨true, true, trivial, Star.refl _, Or.inr ⟨rfl, rfl⟩⟩
  have hlack : ¬ HasBehavior (Done 0) (.terminates [] 1) := done_lacks (by simp)
  have key := extra_terminates_no_backwardSim_not_refinedBy
    (done_no_stuck 0) ⟨(), trivial⟩ hextra hlack
  refine ⟨⟨wf_emptyOrd, ?_, ?_, ?_⟩, done_receptive M 0, ?_, ?_, ?_, ?_, ?_, hextra, hlack,
    key.1, key.2⟩
  · exact fun _ _ => ⟨(), false, trivial, rfl⟩
  · intro _ _ s' r hR hfin
    have hs : s' = false := hR
    have hr : r = 0 := hfin
    exact Or.inl ⟨hs, hr⟩
  · exact fun _ _ _ _ _ _ h => h.elim
  · exact fun _ _ _ _ _ h _ => h.elim
  · exact fun _ _ _ _ h _ => h.elim
  · intro h
    have := h false true trivial trivial
    cases this
  · exact fun _ _ _ _ _ h => h
  · intro s r r' h h'
    rcases h with ⟨hs, hr⟩ | ⟨hs, hr⟩ <;> rcases h' with ⟨hs', hr'⟩ | ⟨hs', hr'⟩
    · rw [hr, hr']
    · rw [hs] at hs'; cases hs'
    · rw [hs] at hs'; cases hs'
    · rw [hr, hr']

/-- **Target final state that can still step.**  The target's initial state
is final with result `0` and can also step silently to a state that is final
with result `1`; every determinacy clause except "final states do not step"
holds.  A forward simulation exists, yet the target has the extra behaviour
"return `0`" and no backward simulation exists. -/
theorem cex_flip_target_final_state_steps :
    IsForwardSim (OneStep none 1) FinalSteps emptyOrd relEq ∧
    Receptive Eq (OneStep none 1) ∧
    StepLabelsMatch Eq FinalSteps ∧ StepFunctional FinalSteps ∧
    InitDeterminate FinalSteps ∧
    ¬ FinalNoStep FinalSteps ∧ FinalDeterminate FinalSteps ∧
    HasBehavior FinalSteps (.terminates [] 0) ∧
    ¬ HasBehavior (OneStep none 1) (.terminates [] 0) ∧
    NoBackwardSim (OneStep none 1) FinalSteps ∧ ¬ RefinedBy (OneStep none 1) FinalSteps := by
  have hextra : HasBehavior FinalSteps (.terminates [] 0) :=
    ⟨false, false, rfl, Star.refl _, Or.inl ⟨rfl, rfl⟩⟩
  have hlack : ¬ HasBehavior (OneStep none 1) (.terminates [] 0) := oneStep_lacks (by simp)
  have key := extra_terminates_no_backwardSim_not_refinedBy
    (oneStep_no_stuck none 1) ⟨false, rfl⟩ hextra hlack
  refine ⟨⟨wf_emptyOrd, ?_, ?_, ?_⟩, receptive_eq _, ?_, ?_, ?_, ?_, ?_, hextra, hlack,
    key.1, key.2⟩
  · intro s hs
    exact ⟨(), s, hs, rfl⟩
  · intro _ s s' r hR hfin
    have hss : s = s' := hR
    subst hss
    exact Or.inr hfin
  · intro _ s s' e s₁ hR hstep
    have hss : s = s' := hR
    subst hss
    exact ⟨(), s₁, Or.inl (Plus.single (L := FinalSteps) hstep), rfl⟩
  · intro s e₁ s₁ e₂ s₂ h₁ h₂
    rw [h₁.2.1, h₂.2.1]
    trivial
  · intro s e s₁ s₂ h₁ h₂
    rw [h₁.2.2, h₂.2.2]
  · intro s s' hs hs'
    have h1 : s = false := hs
    have h2 : s' = false := hs'
    rw [h1, h2]
  · intro h
    exact h false 0 (Or.inl ⟨rfl, rfl⟩) none true ⟨rfl, rfl, rfl⟩
  · intro s r r' h h'
    rcases h with ⟨hs, hr⟩ | ⟨hs, hr⟩ <;> rcases h' with ⟨hs', hr'⟩ | ⟨hs', hr'⟩
    · rw [hr, hr']
    · rw [hs] at hs'; cases hs'
    · rw [hs] at hs'; cases hs'
    · rw [hr, hr']

/-- **Target final state with two results.**  Every determinacy clause except
uniqueness of the result holds.  A forward simulation exists, yet the target
has the extra behaviour "return `1`" and no backward simulation exists. -/
theorem cex_flip_target_two_results (M : Nat → Nat → Prop) :
    IsForwardSim (Done 0) TwoResults emptyOrd relTrue ∧
    Receptive M (Done 0) ∧
    StepLabelsMatch M TwoResults ∧ StepFunctional TwoResults ∧
    InitDeterminate TwoResults ∧ FinalNoStep TwoResults ∧
    ¬ FinalDeterminate TwoResults ∧
    HasBehavior TwoResults (.terminates [] 1) ∧
    ¬ HasBehavior (Done 0) (.terminates [] 1) ∧
    NoBackwardSim (Done 0) TwoResults ∧ ¬ RefinedBy (Done 0) TwoResults := by
  have hextra : HasBehavior TwoResults (.terminates [] 1) :=
    ⟨(), (), trivial, Star.refl _, Or.inr rfl⟩
  have hlack : ¬ HasBehavior (Done 0) (.terminates [] 1) := done_lacks (by simp)
  have key := extra_terminates_no_backwardSim_not_refinedBy
    (done_no_stuck 0) ⟨(), trivial⟩ hextra hlack
  refine ⟨⟨wf_emptyOrd, ?_, ?_, ?_⟩, done_receptive M 0, ?_, ?_, ?_, ?_, ?_, hextra, hlack,
    key.1, key.2⟩
  · exact fun _ _ => ⟨(), (), trivial, trivial⟩
  · intro _ _ _ r _ hfin
    have hr : r = 0 := hfin
    exact Or.inl hr
  · exact fun _ _ _ _ _ _ h => h.elim
  · exact fun _ _ _ _ _ h _ => h.elim
  · exact fun _ _ _ _ h _ => h.elim
  · exact fun _ _ _ _ => rfl
  · exact fun _ _ _ _ _ h => h
  · intro h
    have := h () 0 1 (Or.inl rfl) (Or.inr rfl)
    simp at this

/-- **No chain at all.**  Receptiveness of the first language and determinacy
of the last do not by themselves give refinement. -/
theorem cex_pipeline_without_chain (M : Nat → Nat → Prop) :
    Receptive M (Done 0) ∧ Determinate M (Done 1) ∧
    ¬ FSimChain (Done 0) (Done 1) ∧ ¬ RefinedBy (Done 0) (Done 1) ∧
    NeverGoesWrong (Done 0) ∧
    ¬ (HasBehavior (Done 1) (.terminates [] 1) ↔ HasBehavior (Done 0) (.terminates [] 1)) := by
  refine ⟨done_receptive M 0, done_determinate M 1, ?_,
    not_refinedBy_of_extra_behavior (done_neverGoesWrong 0) (done_has 1) (done_lacks (by simp)),
    done_neverGoesWrong 0, fun h => done_lacks (by simp) (h.1 (done_has 1))⟩
  intro hchain
  -- a chain preserves "some initial state is final with result 0"
  have key : ∀ {L L' : LTS Nat Nat}, FSimChain L L' →
      (∃ s, L.init s ∧ L.final s 0) → ∃ s, L'.init s ∧ L'.final s 0 := by
    intro L L' h
    induction h with
    | nil L => exact id
    | cons ord R hsim _ ih =>
      rintro ⟨s, hs, hfin⟩
      obtain ⟨i, s₂, hs₂, hR⟩ := hsim.init s hs
      exact ih ⟨s₂, hs₂, hsim.final i s s₂ 0 hR hfin⟩
  obtain ⟨_, _, hfin⟩ := key hchain ⟨(), trivial, rfl⟩
  have : (0 : Nat) = 1 := hfin
  simp at this

/-! ## Counterexamples for the pipeline theorems, in canonical form

Each theorem below states, for a one-pass pipeline (a chain with one link),
every hypothesis of the end-to-end theorems except one, together with
"the first language never goes wrong", and shows that refinement fails and
that the two languages do not have the same behaviours (for an explicit
behaviour).  With `M = Eq` they also serve the deterministic-last-language
form. -/

/-- **Pipeline without a receptive first language.** -/
theorem cex_pipeline_nonreceptive_first :
    FSimChain (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) ∧
    Determinate AnyInput (TwoBranch (some 0) (some 1) 0 1) ∧
    ¬ Receptive AnyInput (OneStep (some 0) 0) ∧
    NeverGoesWrong (OneStep (some 0) 0) ∧
    ¬ RefinedBy (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) ∧
    ¬ (HasBehavior (TwoBranch (some 0) (some 1) 0 1) (.terminates [1] 1) ↔
        HasBehavior (OneStep (some 0) 0) (.terminates [1] 1)) := by
  obtain ⟨hsim, hdet, hnrec, hextra, hlack, _, _⟩ := cex_flip_nonreceptive_source
  obtain ⟨hc, hng, hnref, hniff⟩ := pipeline_fails_of_extra_terminates hsim
    (oneStep_no_stuck (some 0) 0) ⟨false, rfl⟩ hextra hlack
  exact ⟨hc, hdet, hnrec, hng, hnref, hniff⟩

/-- **Pipeline whose last language offers a silent step and an event from the
same state.** -/
theorem cex_pipeline_last_labels_mismatch :
    FSimChain (OneStep none 0) (TwoBranch none (some 1) 0 1) ∧
    Receptive Eq (OneStep none 0) ∧
    ¬ StepLabelsMatch Eq (TwoBranch none (some 1) 0 1) ∧
    StepFunctional (TwoBranch none (some 1) 0 1) ∧
    InitDeterminate (TwoBranch none (some 1) 0 1) ∧
    FinalNoStep (TwoBranch none (some 1) 0 1) ∧
    FinalDeterminate (TwoBranch none (some 1) 0 1) ∧
    NeverGoesWrong (OneStep none 0) ∧
    ¬ RefinedBy (OneStep none 0) (TwoBranch none (some 1) 0 1) ∧
    ¬ (HasBehavior (TwoBranch none (some 1) 0 1) (.terminates [1] 1) ↔
        HasBehavior (OneStep none 0) (.terminates [1] 1)) := by
  obtain ⟨hsim, hrec, h1, h2, h3, h4, h5, hextra, hlack, _, _⟩ := cex_flip_target_labels_mismatch
  obtain ⟨hc, hng, hnref, hniff⟩ := pipeline_fails_of_extra_terminates hsim
    (oneStep_no_stuck none 0) ⟨false, rfl⟩ hextra hlack
  exact ⟨hc, hrec, h1, h2, h3, h4, h5, hng, hnref, hniff⟩

/-- **Pipeline whose last language offers two unmatched events from the same
state.** -/
theorem cex_pipeline_last_event_labels_mismatch :
    FSimChain (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) ∧
    Receptive Eq (OneStep (some 0) 0) ∧
    ¬ StepLabelsMatch Eq (TwoBranch (some 0) (some 1) 0 1) ∧
    StepFunctional (TwoBranch (some 0) (some 1) 0 1) ∧
    InitDeterminate (TwoBranch (some 0) (some 1) 0 1) ∧
    FinalNoStep (TwoBranch (some 0) (some 1) 0 1) ∧
    FinalDeterminate (TwoBranch (some 0) (some 1) 0 1) ∧
    NeverGoesWrong (OneStep (some 0) 0) ∧
    ¬ RefinedBy (OneStep (some 0) 0) (TwoBranch (some 0) (some 1) 0 1) ∧
    ¬ (HasBehavior (TwoBranch (some 0) (some 1) 0 1) (.terminates [1] 1) ↔
        HasBehavior (OneStep (some 0) 0) (.terminates [1] 1)) := by
  obtain ⟨hsim, hrec, h1, h2, h3, h4, h5, hextra, hlack, _, _⟩ :=
    cex_flip_target_event_labels_mismatch
  obtain ⟨hc, hng, hnref, hniff⟩ := pipeline_fails_of_extra_terminates hsim
    (oneStep_no_stuck (some 0) 0) ⟨false, rfl⟩ hextra hlack
  exact ⟨hc, hrec, h1, h2, h3, h4, h5, hng, hnref, hniff⟩

/-- **Pipeline whose last language is not functional.** -/
theorem cex_pipeline_last_not_functional :
    FSimChain (OneStep none 0) (TwoBranch none none 0 1) ∧
    Receptive Eq (OneStep none 0) ∧
    StepLabelsMatch Eq (TwoBranch none none 0 1) ∧
    ¬ StepFunctional (TwoBranch none none 0 1) ∧
    InitDeterminate (TwoBranch none none 0 1) ∧
    FinalNoStep (TwoBranch none none 0 1) ∧
    FinalDeterminate (TwoBranch none none 0 1) ∧
    NeverGoesWrong (OneStep none 0) ∧
    ¬ RefinedBy (OneStep none 0) (TwoBranch none none 0 1) ∧
    ¬ (HasBehavior (TwoBranch none none 0 1) (.terminates [] 1) ↔
        HasBehavior (OneStep none 0) (.terminates [] 1)) := by
  obtain ⟨hsim, hrec, h1, h2, h3, h4, h5, hextra, hlack, _, _⟩ := cex_flip_target_not_functional
  obtain ⟨hc, hng, hnref, hniff⟩ := pipeline_fails_of_extra_terminates hsim
    (oneStep_no_stuck none 0) ⟨false, rfl⟩ hextra hlack
  exact ⟨hc, hrec, h1, h2, h3, h4, h5, hng, hnref, hniff⟩

/-- **Pipeline whose last language has two initial states.** -/
theorem cex_pipeline_last_two_initial_states (M : Nat → Nat → Prop) :
    FSimChain (Done 0) TwoInits ∧
    Receptive M (Done 0) ∧
    StepLabelsMatch M TwoInits ∧ StepFunctional TwoInits ∧
    ¬ InitDeterminate TwoInits ∧
    FinalNoStep TwoInits ∧ FinalDeterminate TwoInits ∧
    NeverGoesWrong (Done 0) ∧
    ¬ RefinedBy (Done 0) TwoInits ∧
    ¬ (HasBehavior TwoInits (.terminates [] 1) ↔ HasBehavior (Done 0) (.terminates [] 1)) := by
  obtain ⟨hsim, hrec, h1, h2, h3, h4, h5, hextra, hlack, _, _⟩ :=
    cex_flip_target_two_initial_states M
  obtain ⟨hc, hng, hnref, hniff⟩ := pipeline_fails_of_extra_terminates hsim
    (done_no_stuck 0) ⟨(), trivial⟩ hextra hlack
  exact ⟨hc, hrec, h1, h2, h3, h4, h5, hng, hnref, hniff⟩

/-- **Pipeline whose last language has a final state that can step.** -/
theorem cex_pipeline_last_final_state_steps :
    FSimChain (OneStep none 1) FinalSteps ∧
    Receptive Eq (OneStep none 1) ∧
    StepLabelsMatch Eq FinalSteps ∧ StepFunctional FinalSteps ∧
    InitDeterminate FinalSteps ∧
    ¬ FinalNoStep FinalSteps ∧ FinalDeterminate FinalSteps ∧
    NeverGoesWrong (OneStep none 1) ∧
    ¬ RefinedBy (OneStep none 1) FinalSteps ∧
    ¬ (HasBehavior FinalSteps (.terminates [] 0) ↔
        HasBehavior (OneStep none 1) (.terminates [] 0)) := by
  obtain ⟨hsim, hrec, h1, h2, h3, h4, h5, hextra, hlack, _, _⟩ := cex_flip_target_final_state_steps
  obtain ⟨hc, hng, hnref, hniff⟩ := pipeline_fails_of_extra_terminates hsim
    (oneStep_no_stuck none 1) ⟨false, rfl⟩ hextra hlack
  exact ⟨hc, hrec, h1, h2, h3, h4, h5, hng, hnref, hniff⟩

/-- **Pipeline whose last language has a final state with two results.** -/
theorem cex_pipeline_last_two_results (M : Nat → Nat → Prop) :
    FSimChain (Done 0) TwoResults ∧
    Receptive M (Done 0) ∧
    StepLabelsMatch M TwoResults ∧ StepFunctional TwoResults ∧
    InitDeterminate TwoResults ∧ FinalNoStep TwoResults ∧
    ¬ FinalDeterminate TwoResults ∧
    NeverGoesWrong (Done 0) ∧
    ¬ RefinedBy (Done 0) TwoResults ∧
    ¬ (HasBehavior TwoResults (.terminates [] 1) ↔ HasBehavior (Done 0) (.terminates [] 1)) := by
  obtain ⟨hsim, hrec, h1, h2, h3, h4, h5, hextra, hlack, _, _⟩ := cex_flip_target_two_results M
  obtain ⟨hc, hng, hnref, hniff⟩ := pipeline_fails_of_extra_terminates hsim
    (done_no_stuck 0) ⟨(), trivial⟩ hextra hlack
  exact ⟨hc, hrec, h1, h2, h3, h4, h5, hng, hnref, hniff⟩

/-- **No chain, for the preservation direction.**  Without a chain of forward
simulations, a terminating behaviour of the first language need not be a
behaviour of the last. -/
theorem cex_pipeline_preserves_without_chain :
    ¬ FSimChain (Done 0) (Done 1) ∧
    HasBehavior (Done 0) (.terminates [] 0) ∧
    (∀ t, (Behavior.terminates [] 0 : Behavior Nat Nat) ≠ .goesWrong t) ∧
    ¬ HasBehavior (Done 1) (.terminates [] 0) :=
  ⟨(cex_pipeline_without_chain Eq).2.2.1, done_has 0, (fun _ h => by cases h),
    done_lacks (by simp)⟩

/-! ## Backward simulation gives refinement

One counterexample per clause of a backward simulation: the other five
clauses hold and the target does not refine the source. -/

/-- **Well-foundedness dropped.**  The source terminates at once, the target
diverges silently, and the source matches every target step by doing nothing. -/
theorem cex_bsim_without_wf :
    BSimInitExists (Done 0) Loop ∧
    BSimInitMatch (Done 0) Loop relTrue ∧
    BSimFinal (Done 0) Loop relTrue ∧
    BSimProgress (Done 0) Loop relTrue ∧
    BSimStep (Done 0) Loop fullOrd relTrue ∧
    ¬ RefinedBy (Done 0) Loop := by
  refine ⟨fun _ => ⟨(), trivial⟩, fun _ _ _ _ => ⟨(), (), trivial, trivial⟩, ?_, ?_, ?_,
    not_refinedBy_of_extra_behavior (done_neverGoesWrong 0) loop_has (done_lacks (by simp))⟩
  · exact fun _ _ _ _ _ _ h => h.elim
  · exact fun _ _ _ _ _ => Or.inr ⟨none, (), rfl⟩
  · intro _ s₁ _ e _ _ _ hstep
    have he : e = none := hstep
    subst he
    exact ⟨(), s₁, Or.inr ⟨Star.refl s₁, trivial⟩, trivial⟩

/-- **"Target has an initial state" dropped.** -/
theorem cex_bsim_without_initExists :
    WellFounded emptyOrd ∧
    BSimInitMatch (Done 0) NoInit relFalse ∧
    BSimFinal (Done 0) NoInit relFalse ∧
    BSimProgress (Done 0) NoInit relFalse ∧
    BSimStep (Done 0) NoInit emptyOrd relFalse ∧
    ¬ RefinedBy (Done 0) NoInit := by
  refine ⟨wf_emptyOrd, fun _ _ _ h => h.elim, fun _ _ _ _ h _ _ => h.elim,
    fun _ _ _ h _ => h.elim, fun _ _ _ _ _ h _ _ => h.elim,
    not_refinedBy_of_extra_behavior (done_neverGoesWrong 0)
      ((noInit_behavior _).2 rfl) (done_lacks (by simp))⟩

/-- **Initial-state matching dropped.** -/
theorem cex_bsim_without_initMatch :
    WellFounded emptyOrd ∧
    BSimInitExists (Done 0) (Done 1) ∧
    BSimFinal (Done 0) (Done 1) relFalse ∧
    BSimProgress (Done 0) (Done 1) relFalse ∧
    BSimStep (Done 0) (Done 1) emptyOrd relFalse ∧
    ¬ RefinedBy (Done 0) (Done 1) :=
  ⟨wf_emptyOrd, fun _ => ⟨(), trivial⟩, fun _ _ _ _ h _ _ => h.elim,
    fun _ _ _ h _ => h.elim, fun _ _ _ _ _ h _ _ => h.elim,
    not_refinedBy_of_extra_behavior (done_neverGoesWrong 0) (done_has 1) (done_lacks (by simp))⟩

/-- **Final-state clause dropped.** -/
theorem cex_bsim_without_final_clause :
    WellFounded emptyOrd ∧
    BSimInitExists (Done 0) (Done 1) ∧
    BSimInitMatch (Done 0) (Done 1) relTrue ∧
    BSimProgress (Done 0) (Done 1) relTrue ∧
    BSimStep (Done 0) (Done 1) emptyOrd relTrue ∧
    ¬ RefinedBy (Done 0) (Done 1) :=
  ⟨wf_emptyOrd, fun _ => ⟨(), trivial⟩, fun _ _ _ _ => ⟨(), (), trivial, trivial⟩,
    fun _ _ _ _ _ => Or.inl ⟨1, rfl⟩, fun _ _ _ _ _ _ _ h => h.elim,
    not_refinedBy_of_extra_behavior (done_neverGoesWrong 0) (done_has 1) (done_lacks (by simp))⟩

/-- **Progress clause dropped.**  The target is stuck at once while the
source terminates normally. -/
theorem cex_bsim_without_progress :
    WellFounded emptyOrd ∧
    BSimInitExists (Done 0) StuckNow ∧
    BSimInitMatch (Done 0) StuckNow relTrue ∧
    BSimFinal (Done 0) StuckNow relTrue ∧
    BSimStep (Done 0) StuckNow emptyOrd relTrue ∧
    ¬ RefinedBy (Done 0) StuckNow :=
  ⟨wf_emptyOrd, fun _ => ⟨(), trivial⟩, fun _ _ _ _ => ⟨(), (), trivial, trivial⟩,
    fun _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ _ h => h.elim,
    not_refinedBy_of_extra_behavior (done_neverGoesWrong 0)
      ((stuckNow_behavior _).2 rfl) (done_lacks (by simp))⟩

/-- **Backward step diagram dropped.**  The target emits the event `7` before
returning `0`; the source returns `0` at once; the relation only covers the
target's initial state. -/
theorem cex_bsim_without_step_diagram :
    WellFounded emptyOrd ∧
    BSimInitExists (Done 0) (OneStep (some 7) 0) ∧
    BSimInitMatch (Done 0) (OneStep (some 7) 0) relToFalse ∧
    BSimFinal (Done 0) (OneStep (some 7) 0) relToFalse ∧
    BSimProgress (Done 0) (OneStep (some 7) 0) relToFalse ∧
    ¬ RefinedBy (Done 0) (OneStep (some 7) 0) := by
  refine ⟨wf_emptyOrd, fun _ => ⟨false, rfl⟩, ?_, ?_, ?_,
    not_refinedBy_of_extra_behavior (done_neverGoesWrong 0) (oneStep_has (some 7) 0)
      (done_lacks (by simp))⟩
  · intro _ s₂ _ h₂
    exact ⟨(), (), trivial, h₂⟩
  · intro _ _ s₂ r hR _ hfin
    have h1 : s₂ = false := hR
    have h2 : s₂ = true := hfin.1
    rw [h1] at h2
    cases h2
  · intro _ _ s₂ hR _
    have h1 : s₂ = false := hR
    exact Or.inr ⟨some 7, true, h1, rfl, rfl⟩

/-! ## Remaining hypotheses -/

theorem not_wf_of_refl {α : Type} {r : α → α → Prop} {a : α} (h : r a a) :
    ¬ WellFounded r := by
  intro hwf
  have key : ∀ x, Acc r x → x = a → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro hxa
      exact ih a (hxa ▸ h) rfl
  exact key a (hwf.apply a) rfl

/-- **Both index orders must be well-founded** for the composite order to be
well-founded. -/
theorem cex_compOrd_wf_needs_both :
    WellFounded emptyOrd ∧
    ¬ WellFounded (compOrd fullOrd emptyOrd) ∧
    ¬ WellFounded (compOrd emptyOrd fullOrd) :=
  ⟨wf_emptyOrd,
   not_wf_of_refl (a := ((), ())) (Or.inr ⟨rfl, trivial⟩),
   not_wf_of_refl (a := ((), ())) (Or.inl (Relation.TransGen.single trivial))⟩

/-- **First index order not well-founded** (canonical form for
`isForwardSim_comp`).  The first pass satisfies every forward clause except
well-foundedness (with the full order on a one-point index); the second pass
is a forward simulation; the composite order is not well-founded, so the
composite is not a forward simulation. -/
theorem cex_comp_without_first_wf :
    FSimInit (Done 0) (Done 0) relEq ∧ FSimFinal (Done 0) (Done 0) relEq ∧
    FSimStep (Done 0) (Done 0) fullOrd relEq ∧
    IsForwardSim (Done 0) (Done 0) emptyOrd relEq ∧
    ¬ WellFounded (compOrd fullOrd emptyOrd) ∧
    ¬ IsForwardSim (Done 0) (Done 0) (compOrd fullOrd emptyOrd) (compRel relEq relEq) :=
  ⟨(isForwardSim_id (Done 0)).init, (isForwardSim_id (Done 0)).final,
    fun _ _ _ _ _ _ h => h.elim, isForwardSim_id (Done 0), cex_compOrd_wf_needs_both.2.1,
    fun h => cex_compOrd_wf_needs_both.2.1 h.wf⟩

/-- **Second index order not well-founded** (canonical form for
`isForwardSim_comp`). -/
theorem cex_comp_without_second_wf :
    IsForwardSim (Done 0) (Done 0) emptyOrd relEq ∧
    FSimInit (Done 0) (Done 0) relEq ∧ FSimFinal (Done 0) (Done 0) relEq ∧
    FSimStep (Done 0) (Done 0) fullOrd relEq ∧
    ¬ WellFounded (compOrd emptyOrd fullOrd) ∧
    ¬ IsForwardSim (Done 0) (Done 0) (compOrd emptyOrd fullOrd) (compRel relEq relEq) :=
  ⟨isForwardSim_id (Done 0), (isForwardSim_id (Done 0)).init, (isForwardSim_id (Done 0)).final,
    fun _ _ _ _ _ _ h => h.elim, cex_compOrd_wf_needs_both.2.2,
    fun h => cex_compOrd_wf_needs_both.2.2 h.wf⟩

/-- **A source that goes wrong.**  When the source can go wrong, refinement
(and a backward simulation, and a one-pass pipeline with receptive source and
determinate target) do not give behaviour inclusion: the target returns `0`
while the source's only behaviour is to go wrong at once. -/
theorem cex_inclusion_needs_source_never_goes_wrong (M : Nat → Nat → Prop) :
    RefinedBy StuckNow (Done 0) ∧
    IsBackwardSim StuckNow (Done 0) emptyOrd relTrue ∧
    FSimChain StuckNow (Done 0) ∧ Receptive M StuckNow ∧ Determinate M (Done 0) ∧
    HasBehavior (Done 0) (.terminates [] 0) ∧
    ¬ HasBehavior StuckNow (.terminates [] 0) ∧
    ¬ (HasBehavior (Done 0) (.terminates [] 0) ↔ HasBehavior StuckNow (.terminates [] 0)) := by
  have hstuck : ¬ Safe StuckNow () :=
    Stuck.not_safe (L := StuckNow) ⟨fun _ _ h => h, fun _ h => h⟩
  have hlack : ¬ HasBehavior StuckNow (.terminates [] 0) := by
    intro h
    have := (stuckNow_behavior _).1 h
    simp at this
  refine ⟨?_, ⟨wf_emptyOrd, fun _ => ⟨(), trivial⟩, fun _ _ _ _ => ⟨(), (), trivial, trivial⟩,
      fun _ _ _ _ _ hs _ => absurd hs hstuck, fun _ _ _ _ hs => absurd hs hstuck,
      fun _ _ _ _ _ _ _ h => h.elim⟩,
    FSimChain.cons _ _ cex_forwardSim_goesWrong_not_preserved.1 (FSimChain.nil _),
    fun _ _ _ _ h _ => h.elim, done_determinate M 0, done_has 0, hlack,
    fun h => hlack (h.1 (done_has 0))⟩
  · intro b _
    exact ⟨.goesWrong [], (stuckNow_behavior _).2 rfl, improves_goesWrong_nil b⟩

/-- **No refinement.**  A source that never goes wrong does not by itself
make target behaviours source behaviours. -/
theorem cex_inclusion_without_refinement :
    NeverGoesWrong (Done 0) ∧
    HasBehavior (Done 1) (.terminates [] 1) ∧
    ¬ HasBehavior (Done 0) (.terminates [] 1) :=
  ⟨done_neverGoesWrong 0, done_has 1, done_lacks (by simp)⟩

/-- **No target behaviour.**  Refinement (and a backward simulation) from a
source that never goes wrong does not make a behaviour that the target does
not have into a source behaviour: the identity on `Done 0` and the behaviour
"return `1`". -/
theorem cex_inclusion_without_target_behavior :
    RefinedBy (Done 0) (Done 0) ∧
    IsBackwardSim (Done 0) (Done 0) emptyOrd relEq ∧
    NeverGoesWrong (Done 0) ∧
    ¬ HasBehavior (Done 0) (.terminates [] 1) :=
  ⟨RefinedBy.refl _, ⟨wf_emptyOrd, fun _ => ⟨(), trivial⟩,
      fun _ _ _ _ => ⟨(), (), trivial, rfl⟩,
      fun _ _ _ _ _ _ hfin => ⟨(), Star.refl _, hfin⟩,
      fun _ _ _ _ _ => Or.inl ⟨0, rfl⟩,
      fun _ _ _ _ _ _ _ h => h.elim⟩,
    done_neverGoesWrong 0, done_lacks (by simp)⟩

/-! ## The refinement preorder is not symmetric -/

/-- **`Improves` is not symmetric.**  Going wrong at once is improved by
terminating, but not conversely. -/
theorem cex_improves_not_symmetric :
    Improves (.goesWrong [] : Behavior Nat Nat) (.terminates [] 0) ∧
    ¬ Improves (.terminates [] 0 : Behavior Nat Nat) (.goesWrong []) := by
  refine ⟨improves_goesWrong_nil _, ?_⟩
  rintro (h | ⟨t, h, _⟩) <;> cases h

/-- **`RefinedBy` is not symmetric.**  A program that goes wrong at once is
refined by a program that terminates normally, but not conversely. -/
theorem cex_refinedBy_not_symmetric :
    RefinedBy StuckNow (Done 0) ∧ ¬ RefinedBy (Done 0) StuckNow := by
  refine ⟨?_, not_refinedBy_of_extra_behavior (done_neverGoesWrong 0)
    ((stuckNow_behavior _).2 rfl) (done_lacks (by simp))⟩
  intro b _
  exact ⟨.goesWrong [], (stuckNow_behavior _).2 rfl, improves_goesWrong_nil b⟩

/-! ## Both hypotheses of transitivity and antisymmetry are needed -/

theorem not_improves_terminates_0_1 :
    ¬ Improves (.terminates [] 0 : Behavior Nat Nat) (.terminates [] 1) := by
  rintro (h | ⟨t, h, _⟩)
  · simp at h
  · cases h

/-- **`Improves.trans` needs both hypotheses.**  First component: the second
hypothesis holds (`terminates [] 1` improves itself) and the conclusion fails
(`terminates [] 0` does not improve `terminates [] 1`).  Second component: the
first hypothesis holds and the conclusion fails. -/
theorem cex_improves_trans_needs_both :
    (Improves (.terminates [] 1 : Behavior Nat Nat) (.terminates [] 1) ∧
      ¬ Improves (.terminates [] 0 : Behavior Nat Nat) (.terminates [] 1)) ∧
    (Improves (.terminates [] 0 : Behavior Nat Nat) (.terminates [] 0) ∧
      ¬ Improves (.terminates [] 0 : Behavior Nat Nat) (.terminates [] 1)) :=
  ⟨⟨Improves.refl _, not_improves_terminates_0_1⟩,
    ⟨Improves.refl _, not_improves_terminates_0_1⟩⟩

/-- **`Improves.antisymm` needs both hypotheses.**  Going wrong at once is
improved by terminating, yet the two behaviours differ.  (Read with
`b₁ = goesWrong []`, `b₂ = terminates [] 0` this drops the second hypothesis;
read with the roles swapped it drops the first.) -/
theorem cex_improves_antisymm_needs_both :
    Improves (.goesWrong [] : Behavior Nat Nat) (.terminates [] 0) ∧
    (Behavior.goesWrong [] : Behavior Nat Nat) ≠ .terminates [] 0 :=
  ⟨improves_goesWrong_nil _, fun h => by cases h⟩

/-- **`RefinedBy.trans` needs both hypotheses.**  First component: the second
hypothesis holds (`Done 1` refines itself) and the conclusion fails
(`Done 1` does not refine `Done 0`).  Second component: the first hypothesis
holds and the conclusion fails. -/
theorem cex_refinedBy_trans_needs_both :
    (RefinedBy (Done 1) (Done 1) ∧ ¬ RefinedBy (Done 0) (Done 1)) ∧
    (RefinedBy (Done 0) (Done 0) ∧ ¬ RefinedBy (Done 0) (Done 1)) :=
  ⟨⟨RefinedBy.refl _, (cex_pipeline_without_chain Eq).2.2.2.1⟩,
    ⟨RefinedBy.refl _, (cex_pipeline_without_chain Eq).2.2.2.1⟩⟩

end Cex

end Toy.Sim
