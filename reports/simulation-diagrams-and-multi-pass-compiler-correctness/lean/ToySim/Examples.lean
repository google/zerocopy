import ToySim.Counterexamples

/-!
# Definition examples and non-vacuity witnesses (all fully proved)

* For every definition: at least one intended instance it admits (`_pos`) and
  one instance it must reject (`_neg`).
* For every main result: a concrete instance satisfying all its hypotheses
  (`nonvacuous_…`).

Every theorem in this file is proved outright from the definitions.
-/

namespace Toy.Sim.Examples
open Ex Cex

/-! ## Executions -/

theorem obs_pos : obs (some 3) = [3] ∧ obs (none : Option Nat) = [] := ⟨rfl, rfl⟩

theorem obs_neg : obs (some 3) ≠ ([] : List Nat) := by simp

/-- `Src` can run from `start` to `done 5` emitting exactly `[5]`. -/
theorem star_pos : Star Src .start [5] (.done 5) := (src_boot_read 5).star

/-- A system without steps cannot emit an event. -/
theorem star_neg : ¬ Star (Done 0) () [7] () := done_no_event_run

theorem plus_pos : Plus Tgt .ready [5] (.done 5) := tgt_read_ret 5

/-- `Plus` requires at least one step: a system without steps has no `Plus`,
although it has the empty `Star`. -/
theorem plus_neg : ¬ Plus (Done 0) () [] () ∧ Star (Done 0) () [] () :=
  ⟨fun ⟨_, _, _, h, _, _⟩ => h, Star.refl _⟩

theorem silentDiv_pos : SilentDiv Loop () := ⟨fun _ => (), rfl, fun _ => rfl⟩

/-- Neither a terminated program nor a program that emits events forever
diverges silently. -/
theorem silentDiv_neg : ¬ SilentDiv (Done 0) () ∧ ¬ SilentDiv Chatter () := by
  refine ⟨fun ⟨_, _, hf⟩ => hf 0, ?_⟩
  rintro ⟨f, _, hf⟩
  exact absurd (hf 0) (by simp)

/-- A state with no step that is not final is stuck. -/
theorem stuck_pos : Stuck StuckNow () ∧ Stuck Crash true :=
  ⟨⟨fun _ _ h => h, fun _ h => h⟩, ⟨fun _ _ h => Bool.noConfusion h.1, fun _ h => h⟩⟩

/-- A final state is not stuck, and a state that can step is not stuck. -/
theorem stuck_neg : ¬ Stuck (Done 0) () ∧ ¬ Stuck Loop () :=
  ⟨done_no_stuck 0 (), loop_no_stuck ()⟩

/-- Admitted by `Safe`: states of programs that never go wrong, and also the
initial state of `EmitThenStuck`, which emits an event and then gets stuck.
`Safe` only looks at silent steps, so it is strictly weaker than "never goes
wrong" (`EmitThenStuck` has the going-wrong behaviour `goesWrong [1]`). -/
theorem safe_pos : Safe Src .start ∧ Safe (Done 0) () ∧
    (Safe EmitThenStuck false ∧ HasBehavior EmitThenStuck (.goesWrong [1])) := by
  refine ⟨safe_of_no_stuck src_no_stuck _, done_all_safe 0 (), ?_, ?_⟩
  · intro s' hs'
    rcases hs'.inv with ⟨_, rfl⟩ | ⟨e, s₁, t₁, hstep, _, ht⟩
    · exact Or.inr ⟨some 1, true, rfl, rfl, rfl⟩
    · obtain ⟨_, he, _⟩ := hstep
      subst he
      simp at ht
  · exact Or.inl ⟨false, true, rfl, Star.single (L := EmitThenStuck) ⟨rfl, rfl, rfl⟩,
      fun _ _ h => Bool.noConfusion h.1, fun _ h => h⟩

/-- A state that can step, but silently reaches a stuck state, is not safe. -/
theorem safe_neg : ¬ Safe Crash false ∧ ¬ Stuck Crash false := by
  constructor
  · intro h
    rcases h true (Star.single (L := Crash) (e := none) ⟨rfl, rfl, rfl⟩) with ⟨r, hr⟩ | ⟨e, s, hs⟩
    · exact hr
    · exact Bool.noConfusion hs.1
  · intro h
    exact h.1 none true ⟨rfl, rfl, rfl⟩

/-! ## Behaviours -/

theorem trace_pos : (Behavior.terminates [1, 2] 0 : Behavior Nat Nat).trace = [1, 2] ∧
    (Behavior.goesWrong [3] : Behavior Nat Nat).trace = [3] := ⟨rfl, rfl⟩

/-- One example of each kind of behaviour, including the convention that a
program without initial state goes wrong with the empty trace. -/
theorem hasBehavior_pos :
    HasBehavior Src (.terminates [5] 5) ∧
    HasBehavior Loop (.diverges []) ∧
    HasBehavior Crash (.goesWrong []) ∧
    HasBehavior NoInit (.goesWrong []) := by
  refine ⟨⟨.start, .done 5, rfl, star_pos, rfl⟩, loop_has, ?_, (noInit_behavior _).2 rfl⟩
  exact Or.inl ⟨false, true, rfl, Star.single (L := Crash) (e := none) ⟨rfl, rfl, rfl⟩,
    fun _ _ h => Bool.noConfusion h.1, fun _ h => h⟩

/-- A program has only the behaviours its runs produce; a program whose only
run emits events forever has none in this model. -/
theorem hasBehavior_neg :
    ¬ HasBehavior (Done 0) (.terminates [] 1) ∧
    ¬ HasBehavior (Done 0) (.goesWrong []) ∧
    ¬ HasBehavior Loop (.terminates [] 0) ∧
    ∀ b, ¬ HasBehavior Chatter b :=
  ⟨done_lacks (by simp), done_lacks (by simp), loop_lacks (by simp), chatter_no_behavior⟩

/-- A source that goes wrong after `[1]` permits a target that continues with
more events and terminates. -/
theorem improves_pos :
    Improves (.goesWrong [1] : Behavior Nat Nat) (.terminates [1, 2] 0) ∧
    Improves (.diverges [4] : Behavior Nat Nat) (.diverges [4]) :=
  ⟨Or.inr ⟨[1], rfl, ⟨[2], rfl⟩⟩, Improves.refl _⟩

/-- Going wrong after `[1]` does not permit a target whose trace does not
start with `[1]`; and a source behaviour that does not go wrong permits only
itself. -/
theorem improves_neg :
    ¬ Improves (.goesWrong [1] : Behavior Nat Nat) (.terminates [2] 0) ∧
    ¬ Improves (.diverges [] : Behavior Nat Nat) (.terminates [] 0) ∧
    ¬ Improves (.terminates [] 0 : Behavior Nat Nat) (.terminates [] 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (h | ⟨t, h, hpre⟩)
    · cases h
    · cases h
      obtain ⟨u, hu⟩ := hpre
      simp [Behavior.trace] at hu
  · rintro (h | ⟨t, h, _⟩) <;> cases h
  · rintro (h | ⟨t, h, _⟩)
    · simp at h
    · cases h

theorem refinedBy_pos : RefinedBy StuckNow (Done 0) ∧ RefinedBy Src Src :=
  ⟨cex_refinedBy_not_symmetric.1, RefinedBy.refl Src⟩

/-- **Limit of the model.**  A target with no behaviour at all refines every
source vacuously.  `Chatter` emits the event `0` forever; since behaviours
with infinitely many events are not modelled, `RefinedBy` puts no constraint
on such a target. -/
theorem refinedBy_vacuous_for_target_without_behavior (L : LTS Nat Nat) :
    RefinedBy L Chatter :=
  fun b hb => absurd hb (chatter_no_behavior b)

theorem refinedBy_neg : ¬ RefinedBy (Done 0) StuckNow ∧ ¬ RefinedBy (Done 0) (Done 1) :=
  ⟨cex_refinedBy_not_symmetric.2, (cex_pipeline_without_chain Eq).2.2.2.1⟩

theorem neverGoesWrong_pos : NeverGoesWrong Src ∧ NeverGoesWrong Loop :=
  ⟨src_neverGoesWrong, loop_neverGoesWrong⟩

/-- Stuck at once, stuck after a silent step, and "no initial state" all count
as going wrong. -/
theorem neverGoesWrong_neg :
    ¬ NeverGoesWrong StuckNow ∧ ¬ NeverGoesWrong Crash ∧ ¬ NeverGoesWrong NoInit :=
  ⟨fun h => h [] ((stuckNow_behavior _).2 rfl), fun h => h [] hasBehavior_pos.2.2.1,
    fun h => h [] ((noInit_behavior _).2 rfl)⟩

/-! ## Forward simulation clauses -/

theorem fsimInit_pos : FSimInit Src Tgt SrcTgtRel := srcTgt_isForwardSim.init

theorem fsimInit_neg : ¬ FSimInit (Done 0) NoInit relFalse := by
  intro h
  obtain ⟨_, _, h', _⟩ := h () trivial
  exact h'

theorem fsimFinal_pos : FSimFinal Src Tgt SrcTgtRel := srcTgt_isForwardSim.final

theorem fsimFinal_neg : ¬ FSimFinal (Done 0) (Done 1) relTrue := by
  intro h
  have h' : (0 : Nat) = 1 := h () () () 0 trivial rfl
  simp at h'

/-- The step diagram for `Src` and `Tgt` uses both alternatives: the target
stutters on the source's start-up step and takes two steps on the read. -/
theorem fsimStep_pos : FSimStep Src Tgt (fun i' i : Nat => i' < i) SrcTgtRel :=
  srcTgt_isForwardSim.step

theorem fsimStep_neg : ¬ FSimStep (OneStep (some 7) 0) (Done 0) emptyOrd relBefore := by
  intro h
  obtain ⟨_, _, hmove, _⟩ := h () false () (some 7) true rfl ⟨rfl, rfl, rfl⟩
  rcases hmove with hp | ⟨hs, _⟩
  · exact done_no_event_run hp.star
  · exact done_no_event_run hs

theorem isForwardSim_pos :
    IsForwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtRel ∧
    IsForwardSim Src Src (fun (_ _ : Unit) => False) (fun _ s s' => s = s') :=
  ⟨srcTgt_isForwardSim, isForwardSim_id Src⟩

/-- No forward simulation whatsoever relates a silently diverging source to a
target that terminates at once: with a well-founded order the target cannot
stutter forever. -/
theorem isForwardSim_neg :
    ¬ ∃ (I : Type) (ord : I → I → Prop) (R : I → Loop.State → (Done 0).State → Prop),
        IsForwardSim Loop (Done 0) ord R := by
  rintro ⟨I, ord, R, hsim⟩
  have key : ∀ i, ¬ R i () () := by
    intro i
    induction i using hsim.wf.induction with
    | _ i ih =>
      intro hR
      obtain ⟨i', s₂', hmove, hR'⟩ := hsim.step i () () none () hR rfl
      rcases hmove with hp | ⟨_, hord⟩
      · obtain ⟨_, _, _, hstep, _, _⟩ := hp
        exact hstep
      · exact ih i' hord hR'
  obtain ⟨i, s₂, _, hR⟩ := hsim.init () trivial
  exact key i hR

/-! ## Backward simulation clauses -/

theorem bsimInitExists_pos : BSimInitExists Src Tgt := srcTgt_isBackwardSim.initExists

theorem bsimInitExists_neg : ¬ BSimInitExists (Done 0) NoInit := by
  intro h
  obtain ⟨_, h'⟩ := h ⟨(), trivial⟩
  exact h'

theorem bsimInitMatch_pos : BSimInitMatch Src Tgt SrcTgtBackRel :=
  srcTgt_isBackwardSim.initMatch

theorem bsimInitMatch_neg : ¬ BSimInitMatch (Done 0) (Done 1) relFalse := by
  intro h
  obtain ⟨_, _, _, h'⟩ := h () () trivial trivial
  exact h'

theorem bsimFinal_pos : BSimFinal Src Tgt SrcTgtBackRel := srcTgt_isBackwardSim.final

theorem bsimFinal_neg : ¬ BSimFinal (Done 0) (Done 1) relTrue := by
  intro h
  obtain ⟨_, _, hfin⟩ := h () () () 1 trivial (done_all_safe 0 ()) rfl
  have h' : (1 : Nat) = 0 := hfin
  simp at h'

theorem bsimProgress_pos : BSimProgress Src Tgt SrcTgtBackRel :=
  srcTgt_isBackwardSim.progress

theorem bsimProgress_neg : ¬ BSimProgress (Done 0) StuckNow relTrue := by
  intro h
  rcases h () () () trivial (done_all_safe 0 ()) with ⟨_, h'⟩ | ⟨_, _, h'⟩
  · exact h'
  · exact h'

/-- The backward step diagram for `Src` and `Tgt` uses both alternatives: the
source takes two steps on the target's read and stutters on the target's
final silent step. -/
theorem bsimStep_pos : BSimStep Src Tgt (fun i' i : Nat => i' < i) SrcTgtBackRel :=
  srcTgt_isBackwardSim.step

theorem bsimStep_neg : ¬ BSimStep (Done 0) (OneStep (some 7) 0) emptyOrd relToFalse := by
  intro h
  obtain ⟨_, _, hmove, _⟩ :=
    h () () false (some 7) true rfl (done_all_safe 0 ()) ⟨rfl, rfl, rfl⟩
  rcases hmove with hp | ⟨hs, _⟩
  · exact done_no_event_run hp.star
  · exact done_no_event_run hs

theorem isBackwardSim_pos :
    IsBackwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtBackRel := srcTgt_isBackwardSim

/-- No backward simulation relates a source returning `0` to a target
returning `1`. -/
theorem isBackwardSim_neg : NoBackwardSim (Done 0) (Done 1) :=
  (cex_flip_without_final_clause Eq).2.2.2.2.2.1

theorem noBackwardSim_pos : NoBackwardSim (OneStep none 0) (TwoBranch none none 0 1) :=
  cex_flip_target_not_functional.2.2.2.2.2.2.2.2.2.1

theorem noBackwardSim_neg : ¬ NoBackwardSim Src Tgt :=
  fun h => h ⟨Nat, _, _, srcTgt_isBackwardSim⟩

/-! ## Receptiveness and determinacy -/

theorem labelMatch_pos :
    LabelMatch (Eq : Nat → Nat → Prop) (some 1) (some 1) ∧
    LabelMatch AnyInput (some 0) (some 1) ∧
    LabelMatch (Eq : Nat → Nat → Prop) none none :=
  ⟨rfl, trivial, trivial⟩

/-- A silent label never matches an event, whatever the event relation; and
with `Eq` two different events do not match. -/
theorem labelMatch_neg :
    ¬ LabelMatch AnyInput none (some 1) ∧
    ¬ LabelMatch AnyInput (some 1) none ∧
    ¬ LabelMatch (Eq : Nat → Nat → Prop) (some 0) (some 1) := by
  refine ⟨fun h => h, fun h => h, ?_⟩
  intro h
  have h' : (0 : Nat) = 1 := h
  simp at h'

/-- `Src` accepts every input value; and every system is receptive when
events only match themselves. -/
theorem receptive_pos : Receptive AnyInput Src ∧ Receptive Eq (OneStep (some 0) 0) :=
  ⟨src_receptive, receptive_eq _⟩

/-- A program that accepts only the input `0` is not receptive when all
inputs match. -/
theorem receptive_neg : ¬ Receptive AnyInput (OneStep (some 0) 0) :=
  cex_flip_nonreceptive_source.2.2.1

theorem stepLabelsMatch_pos : StepLabelsMatch AnyInput Tgt := tgt_determinate.labels

theorem stepLabelsMatch_neg : ¬ StepLabelsMatch Eq (TwoBranch none (some 1) 0 1) :=
  cex_flip_target_labels_mismatch.2.2.1

theorem stepFunctional_pos : StepFunctional Tgt := tgt_determinate.functional

theorem stepFunctional_neg :
    ¬ StepFunctional (TwoBranch none none 0 1) ∧ ¬ StepFunctional Mid :=
  ⟨cex_flip_target_not_functional.2.2.2.1, mid_not_stepFunctional⟩

theorem initDeterminate_pos : InitDeterminate Tgt := tgt_determinate.init

theorem initDeterminate_neg : ¬ InitDeterminate TwoInits :=
  (cex_flip_target_two_initial_states Eq).2.2.2.2.1

theorem finalNoStep_pos : FinalNoStep Tgt := tgt_determinate.finalNoStep

theorem finalNoStep_neg : ¬ FinalNoStep FinalSteps :=
  cex_flip_target_final_state_steps.2.2.2.2.2.1

theorem finalDeterminate_pos : FinalDeterminate Tgt := tgt_determinate.finalDet

theorem finalDeterminate_neg : ¬ FinalDeterminate TwoResults :=
  (cex_flip_target_two_results Eq).2.2.2.2.2.2.1

/-- `Tgt` is determinate even though the environment chooses the input. -/
theorem determinate_pos : Determinate AnyInput Tgt := tgt_determinate

theorem determinate_neg : ¬ Determinate AnyInput Mid :=
  fun h => mid_not_stepFunctional h.functional

/-- Receptiveness is not monotone in the matching relation: a system that is
receptive when events only match themselves need not be receptive when all
events match. -/
theorem receptive_not_monotone :
    Receptive Eq (OneStep (some 0) 0) ∧ ¬ Receptive AnyInput (OneStep (some 0) 0) :=
  ⟨receptive_eq _, receptive_neg⟩

/-- Determinacy is not antitone in the matching relation: `Tgt` is
determinate when all inputs match but not when events only match themselves
(it offers two different events from the same state). -/
theorem determinate_not_antitone :
    Determinate AnyInput Tgt ∧ ¬ Determinate Eq Tgt := by
  refine ⟨tgt_determinate, ?_⟩
  intro h
  have hl := h.labels .ready (some 0) (.got 0) (some 1) (.got 1) (TgtStep.read 0) (TgtStep.read 1)
  have h' : (0 : Nat) = 1 := hl
  simp at h'

/-! ## Composition data and chains -/

theorem transGen_succOrd_lt {a b : Nat} (h : Relation.TransGen succOrd a b) : a < b := by
  induction h with
  | single h =>
    have h' : a + 1 = _ := h
    omega
  | tail _ h ih =>
    have h' : _ + 1 = _ := h
    omega

/-- The composite order decreases when the first component decreases through
several steps of the second-pass order (whatever happens to the second
component), or when the first component is unchanged and the second
decreases. -/
theorem compOrd_pos :
    compOrd (fun i' i : Nat => i' < i) succOrd (0, 9) (2, 0) ∧
    compOrd (fun i' i : Nat => i' < i) succOrd (1, 3) (1, 4) :=
  ⟨Or.inl (Relation.TransGen.tail (Relation.TransGen.single (rfl : succOrd 0 1))
      (rfl : succOrd 1 2)),
   Or.inr ⟨rfl, Nat.lt_succ_self 3⟩⟩

theorem compOrd_neg :
    ¬ compOrd (fun i' i : Nat => i' < i) succOrd (1, 4) (1, 4) ∧
    ¬ compOrd (fun i' i : Nat => i' < i) succOrd (2, 0) (1, 5) := by
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact absurd (transGen_succOrd_lt h) (Nat.lt_irrefl 1)
    · exact absurd h (Nat.lt_irrefl 4)
  · rintro (h | ⟨h, _⟩)
    · have := transGen_succOrd_lt h
      have h' : (2 : Nat) < 1 := this
      omega
    · have h' : (2 : Nat) = 1 := h
      omega

theorem compRel_pos : compRel SrcMidRel MidTgtRel ((), 1) .start .ready :=
  ⟨.ready, .start, .ready⟩

/-- The composite relation keeps track of both indices. -/
theorem compRel_neg : ¬ compRel SrcMidRel MidTgtRel ((), 0) .start .ready := by
  rintro ⟨s₂, h₁, _⟩
  cases h₁

theorem fsimChain_pos : FSimChain Src Tgt ∧ FSimChain Src Src :=
  ⟨FSimChain.cons _ _ srcMid_isForwardSim
      (FSimChain.cons _ _ midTgt_isForwardSim (FSimChain.nil Tgt)),
   FSimChain.nil Src⟩

theorem fsimChain_neg : ¬ FSimChain (Done 0) (Done 1) :=
  (cex_pipeline_without_chain Eq).2.2.1

/-! ## Non-vacuity witnesses for the main results -/

/-- Hypotheses of the partial-run theorem hold together (`Src`, `Tgt`, the
run `start ⟶ done 5` with trace `[5]`). -/
theorem nonvacuous_partial_run_simulated :
    FSimInit Src Tgt SrcTgtRel ∧
    FSimStep Src Tgt (fun i' i : Nat => i' < i) SrcTgtRel ∧
    Src.init .start ∧ Star Src .start [5] (.done 5) :=
  ⟨srcTgt_isForwardSim.init, srcTgt_isForwardSim.step, rfl, star_pos⟩

/-- Hypotheses of the termination-preservation theorem hold together. -/
theorem nonvacuous_preserve_terminates :
    FSimInit Src Tgt SrcTgtRel ∧
    FSimStep Src Tgt (fun i' i : Nat => i' < i) SrcTgtRel ∧
    FSimFinal Src Tgt SrcTgtRel ∧
    HasBehavior Src (.terminates [5] 5) :=
  ⟨srcTgt_isForwardSim.init, srcTgt_isForwardSim.step, srcTgt_isForwardSim.final,
    hasBehavior_pos.1⟩

/-- Relation from `Spin` to `Loop`: the target stutters on the first source
step (index `1 → 0`) and then follows the source loop step for step. -/
def spinRel : Nat → Bool → Unit → Prop :=
  fun i s _ => (s = false ∧ i = 1) ∨ (s = true ∧ i = 0)

/-- Hypotheses of the divergence-preservation theorem hold together, in an
instance that uses both stuttering and real target steps. -/
theorem nonvacuous_preserve_diverges :
    WellFounded (fun i' i : Nat => i' < i) ∧
    FSimInit Spin Loop spinRel ∧
    FSimStep Spin Loop (fun i' i : Nat => i' < i) spinRel ∧
    HasBehavior Spin (.diverges []) := by
  refine ⟨Nat.lt_wfRel.wf, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨1, (), trivial, Or.inl ⟨hs, rfl⟩⟩
  · intro i s s₂ e s' hR hstep
    obtain ⟨he, hs'⟩ := hstep
    subst he hs'
    rcases hR with ⟨_, hi⟩ | ⟨_, hi⟩
    · subst hi
      exact ⟨0, s₂, Or.inr ⟨Star.refl s₂, Nat.zero_lt_one⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨0, (), Or.inl (Plus.single (L := Loop) (e := none) rfl), Or.inr ⟨rfl, rfl⟩⟩
  · refine ⟨false, false, rfl, Star.refl _, fun n => decide (0 < n), rfl, ?_⟩
    intro n
    exact ⟨rfl, by simp⟩

/-- Hypotheses of the bundled behaviour-preservation theorem hold together. -/
theorem nonvacuous_isForwardSim_preserves :
    IsForwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtRel ∧
    HasBehavior Src (.terminates [5] 5) ∧
    (∀ t, (Behavior.terminates [5] 5 : Behavior Nat Nat) ≠ .goesWrong t) :=
  ⟨srcTgt_isForwardSim, hasBehavior_pos.1, fun _ h => by cases h⟩

/-- Hypotheses of vertical composition hold together, with a first pass that
stutters and a second pass that does not. -/
theorem nonvacuous_comp :
    IsForwardSim Src Mid (fun i' i : Nat => i' < i) SrcMidRel ∧
    IsForwardSim Mid Tgt (fun _ _ : Unit => False) MidTgtRel :=
  ⟨srcMid_isForwardSim, midTgt_isForwardSim⟩

/-- Hypotheses of the flip lemma hold together, with a non-trivial matching
relation (any two inputs match). -/
theorem nonvacuous_flip :
    IsForwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtRel ∧
    Receptive AnyInput Src ∧ Determinate AnyInput Tgt :=
  ⟨srcTgt_isForwardSim, src_receptive, tgt_determinate⟩

/-- A backward simulation exists in an instance where the source stutters. -/
theorem nonvacuous_backwardSim :
    IsBackwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtBackRel ∧
    NeverGoesWrong Src :=
  ⟨srcTgt_isBackwardSim, src_neverGoesWrong⟩

/-- Hypotheses of the end-to-end theorem hold together for a two-pass
pipeline `Src ⟶ Mid ⟶ Tgt` whose intermediate language `Mid` is *not*
determinate; the first language also never goes wrong. -/
theorem nonvacuous_pipeline :
    FSimChain Src Tgt ∧ Receptive AnyInput Src ∧ Determinate AnyInput Tgt ∧
    NeverGoesWrong Src ∧
    IsForwardSim Src Mid (fun i' i : Nat => i' < i) SrcMidRel ∧
    IsForwardSim Mid Tgt (fun _ _ : Unit => False) MidTgtRel ∧
    ¬ Determinate AnyInput Mid :=
  ⟨fsimChain_pos.1, src_receptive, tgt_determinate, src_neverGoesWrong,
    srcMid_isForwardSim, midTgt_isForwardSim, determinate_neg⟩

/-- Hypotheses of "refinement is inclusion for a safe source" hold together. -/
theorem nonvacuous_refinedBy_neverGoesWrong :
    RefinedBy Src Src ∧ NeverGoesWrong Src :=
  ⟨RefinedBy.refl Src, src_neverGoesWrong⟩

theorem loop_determinate_eq : Determinate Eq Loop where
  labels := by
    intro s e₁ s₁ e₂ s₂ h₁ h₂
    have he₁ : e₁ = none := h₁
    have he₂ : e₂ = none := h₂
    rw [he₁, he₂]
    trivial
  functional := fun _ _ _ _ _ _ => rfl
  init := fun _ _ _ _ => rfl
  finalNoStep := fun _ _ h => h.elim
  finalDet := fun _ _ _ h => h.elim

theorem spinLoop_isForwardSim :
    IsForwardSim Spin Loop (fun i' i : Nat => i' < i) spinRel :=
  ⟨nonvacuous_preserve_diverges.1, nonvacuous_preserve_diverges.2.1,
    fun _ _ _ _ _ h => h.elim, nonvacuous_preserve_diverges.2.2.1⟩

/-- Hypotheses of the deterministic-target forms of the flip lemma and of the
end-to-end theorem hold together (`Spin` simulated by the deterministic
`Loop`). -/
theorem nonvacuous_deterministic_target :
    IsForwardSim Spin Loop (fun i' i : Nat => i' < i) spinRel ∧
    FSimChain Spin Loop ∧ Determinate Eq Loop :=
  ⟨spinLoop_isForwardSim,
    FSimChain.cons _ _ spinLoop_isForwardSim (FSimChain.nil Loop), loop_determinate_eq⟩

/-- Hypotheses of "a pipeline preserves non-going-wrong behaviours" hold
together. -/
theorem nonvacuous_pipeline_preserves :
    FSimChain Src Tgt ∧ HasBehavior Src (.terminates [5] 5) ∧
    (∀ t, (Behavior.terminates [5] 5 : Behavior Nat Nat) ≠ .goesWrong t) :=
  ⟨fsimChain_pos.1, hasBehavior_pos.1, fun _ h => by cases h⟩

/-- A plain relation between `Src` and `Tgt` (no index). -/
def srcTgtPlainRel : SrcSt → TgtSt → Prop
  | .start, .ready => True
  | .ready, .ready => True
  | .done n, .done m => n = m
  | _, _ => False

/-- A measure on `Src` states: `1` before the start-up step, `0` afterwards. -/
def srcMeasure : SrcSt → Nat
  | .start => 1
  | _ => 0

/-- Hypotheses of the "measure on source states" form hold together for
`Src` and `Tgt`. -/
theorem nonvacuous_measure_form :
    (∀ s₁, Src.init s₁ → ∃ s₂, Tgt.init s₂ ∧ srcTgtPlainRel s₁ s₂) ∧
    (∀ s₁ s₂ r, srcTgtPlainRel s₁ s₂ → Src.final s₁ r → Tgt.final s₂ r) ∧
    (∀ s₁ s₂ e s₁', srcTgtPlainRel s₁ s₂ → Src.step s₁ e s₁' →
      ∃ s₂', (Plus Tgt s₂ (obs e) s₂' ∨
          (Star Tgt s₂ (obs e) s₂' ∧ srcMeasure s₁' < srcMeasure s₁)) ∧
        srcTgtPlainRel s₁' s₂') := by
  refine ⟨?_, ?_, ?_⟩
  · intro s₁ hs
    have hs' : s₁ = .start := hs
    subst hs'
    exact ⟨.ready, rfl, trivial⟩
  · intro s₁ s₂ r hR hfin
    have hs : s₁ = .done r := hfin
    subst hs
    cases s₂ with
    | ready => exact hR.elim
    | got n => exact hR.elim
    | done m =>
      have hrm : r = m := hR
      rw [hrm]
  · intro s₁ s₂ e s₁' hR hstep
    cases hstep with
    | boot =>
      cases s₂ with
      | ready => exact ⟨.ready, Or.inr ⟨Star.refl _, Nat.zero_lt_one⟩, trivial⟩
      | got n => exact hR.elim
      | done m => exact hR.elim
    | read n =>
      cases s₂ with
      | ready => exact ⟨.done n, Or.inl (tgt_read_ret n), rfl⟩
      | got m => exact hR.elim
      | done m => exact hR.elim

/-! ## Positive control: the conclusions hold in the witness instance

Proved directly from the definitions, without using any main result. -/

theorem tgt_star_ready {t : List Nat} {s : Tgt.State} (h : Star Tgt .ready t s) :
    (t = [] ∧ s = .ready) ∨ ∃ n, t = [n] ∧ (s = .got n ∨ s = .done n) := by
  rcases h.inv with h | ⟨e, s₁, t₁, hstep, hrest, rfl⟩
  · exact Or.inl h
  · cases hstep with
    | read n =>
      refine Or.inr ⟨n, ?_⟩
      rcases hrest.inv with ⟨ht, hs⟩ | ⟨e', s₂, t₂, hstep', hrest', ht⟩
      · subst ht hs
        exact ⟨by simp, Or.inl rfl⟩
      · cases hstep' with
        | ret _ =>
          obtain ⟨ht₂, hs⟩ := Star.of_noStep (L := Tgt) (fun _ _ h => by cases h) hrest'
          subst ht₂ hs ht
          exact ⟨by simp, Or.inr rfl⟩

/-- The behaviours of `Tgt` are exactly "read `n`, return `n`". -/
theorem tgt_behavior (b : Behavior Nat Nat) :
    HasBehavior Tgt b ↔ ∃ n, b = .terminates [n] n := by
  constructor
  · intro h
    cases b with
    | terminates t r =>
      obtain ⟨s₀, s, h₀, hstar, hfin⟩ := h
      have h₀' : s₀ = .ready := h₀
      have hs : s = .done r := hfin
      subst h₀' hs
      rcases tgt_star_ready hstar with ⟨_, h⟩ | ⟨n, ht, h | h⟩
      · cases h
      · cases h
      · cases h
        exact ⟨_, by rw [ht]⟩
    | diverges t =>
      obtain ⟨s₀, s, h₀, hstar, f, hf0, hf⟩ := h
      have h₀' : s₀ = .ready := h₀
      subst h₀'
      exfalso
      have key : ∀ n x, TgtStep (.got n) none x → x = .done n := by
        intro n x hx
        cases hx
        rfl
      have h0 := hf 0
      have h1 := hf 1
      rw [hf0] at h0
      rcases tgt_star_ready hstar with ⟨_, h⟩ | ⟨n, _, h | h⟩
      · rw [h] at h0
        cases h0
      · rw [h] at h0
        rw [key n _ h0] at h1
        cases h1
      · rw [h] at h0
        cases h0
    | goesWrong t =>
      rcases h with ⟨s₀, s, h₀, hstar, hstuck⟩ | ⟨_, hno⟩
      · have h₀' : s₀ = .ready := h₀
        subst h₀'
        exfalso
        rcases tgt_star_ready hstar with ⟨_, h⟩ | ⟨n, _, h | h⟩
        · subst h
          exact hstuck.1 (some 0) (.got 0) (TgtStep.read 0)
        · subst h
          exact hstuck.1 none (.done n) (TgtStep.ret n)
        · subst h
          exact hstuck.2 n rfl
      · exact (hno .ready rfl).elim
  · rintro ⟨n, rfl⟩
    exact ⟨.ready, .done n, rfl, (tgt_read_ret n).star, rfl⟩

/-- **Positive control.**  In the witness instance (receptive source,
determinate target, forward simulation), the target does refine the source,
and every target behaviour is a source behaviour. -/
theorem positive_control_src_tgt :
    RefinedBy Src Tgt ∧ ∀ b, HasBehavior Tgt b → HasBehavior Src b := by
  have incl : ∀ b, HasBehavior Tgt b → HasBehavior Src b := by
    intro b hb
    obtain ⟨n, rfl⟩ := (tgt_behavior b).1 hb
    exact ⟨.start, .done n, rfl, (src_boot_read n).star, rfl⟩
  exact ⟨fun b hb => ⟨b, incl b hb, Improves.refl b⟩, incl⟩

/-- **Positive control for the "no measure" counterexample.**  With a
well-founded order, the silently diverging source `Spin` is forward-simulated
by `Loop` (stuttering once, then step for step), and `Loop` does diverge
silently: silent divergence is preserved. -/
theorem positive_control_diverges :
    IsForwardSim Spin Loop (fun i' i : Nat => i' < i) spinRel ∧
    HasBehavior Spin (.diverges []) ∧ HasBehavior Loop (.diverges []) :=
  ⟨spinLoop_isForwardSim, nonvacuous_preserve_diverges.2.2.2, loop_has⟩

/-- The behaviours of `Src` and `Tgt` coincide.  Proved directly from the
definitions. -/
theorem src_tgt_same_behaviors : ∀ b, HasBehavior Tgt b ↔ HasBehavior Src b := by
  intro b
  constructor
  · exact positive_control_src_tgt.2 b
  · intro hb
    have srcStar : ∀ {t : List Nat} {s : SrcSt}, Star Src .start t s →
        (t = [] ∧ (s = .start ∨ s = .ready)) ∨ ∃ n, t = [n] ∧ s = .done n := by
      intro t s h
      rcases h.inv with ⟨rfl, rfl⟩ | ⟨e, s₁, t₁, hs, hr, rfl⟩
      · exact Or.inl ⟨rfl, Or.inl rfl⟩
      · cases hs with
        | boot =>
          rcases hr.inv with ⟨rfl, rfl⟩ | ⟨e', s₂, t₂, hs', hr', rfl⟩
          · exact Or.inl ⟨rfl, Or.inr rfl⟩
          · cases hs' with
            | read n =>
              obtain ⟨rfl, rfl⟩ := Star.of_noStep (L := Src) (fun _ _ h => by cases h) hr'
              exact Or.inr ⟨n, by simp, rfl⟩
    cases b with
    | terminates t r =>
      obtain ⟨s₀, s, h₀, hstar, hfin⟩ := hb
      have h₀' : s₀ = .start := h₀
      have hs : s = .done r := hfin
      subst h₀' hs
      rcases srcStar hstar with ⟨_, h | h⟩ | ⟨n, rfl, h⟩
      · cases h
      · cases h
      · cases h
        exact (tgt_behavior _).2 ⟨r, rfl⟩
    | diverges t =>
      obtain ⟨s₀, s, h₀, hstar, f, hf0, hf⟩ := hb
      have h₀' : s₀ = .start := h₀
      subst h₀'
      have h0 := hf 0
      have h1 := hf 1
      rw [hf0] at h0
      rcases srcStar hstar with ⟨_, rfl | rfl⟩ | ⟨n, _, rfl⟩
      · have hf1 : ∀ x, SrcStep .start none x → x = .ready := fun _ h => by cases h; rfl
        rw [hf1 _ h0] at h1
        cases h1
      · cases h0
      · cases h0
    | goesWrong t =>
      exact absurd hb (src_neverGoesWrong t)

/-- **Positive control for the flip counterexamples.**  In the witness
instance (forward simulation, receptive source, determinate target) a
backward simulation exists, it contains the forward relation, and the target
refines the source. -/
theorem positive_control_flip :
    IsForwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtRel ∧
    Receptive AnyInput Src ∧ Determinate AnyInput Tgt ∧
    IsBackwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtBackRel ∧
    (∀ i s₁ s₂, SrcTgtRel i s₁ s₂ → ∃ i', SrcTgtBackRel i' s₁ s₂) ∧
    ¬ NoBackwardSim Src Tgt ∧ RefinedBy Src Tgt :=
  ⟨srcTgt_isForwardSim, src_receptive, tgt_determinate, srcTgt_isBackwardSim,
    srcTgtRel_sub_srcTgtBackRel, noBackwardSim_neg, positive_control_src_tgt.1⟩

/-! ## Further non-vacuity witnesses -/

/-- Hypotheses of the flip lemma hold together, and its conclusion holds in
the same instance with the backward relation `SrcTgtBackRel` exposed. -/
theorem nonvacuous_flip_with_conclusion :
    IsForwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtRel ∧
    Receptive AnyInput Src ∧ Determinate AnyInput Tgt ∧
    IsBackwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtBackRel ∧
    (∀ i s₁ s₂, SrcTgtRel i s₁ s₂ → ∃ i', SrcTgtBackRel i' s₁ s₂) :=
  ⟨srcTgt_isForwardSim, src_receptive, tgt_determinate, srcTgt_isBackwardSim,
    srcTgtRel_sub_srcTgtBackRel⟩

/-- Hypotheses of both "refinement is inclusion" theorems hold together, for
a pair of different systems, with an explicit target behaviour. -/
theorem nonvacuous_refinement_inclusion :
    RefinedBy Src Tgt ∧
    IsBackwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtBackRel ∧
    NeverGoesWrong Src ∧ HasBehavior Tgt (.terminates [5] 5) :=
  ⟨positive_control_src_tgt.1, srcTgt_isBackwardSim, src_neverGoesWrong,
    (tgt_behavior _).2 ⟨5, rfl⟩⟩

/-- Hypotheses of the end-to-end behaviour-equality theorem hold together for
the two-pass pipeline `Src ⟶ Mid ⟶ Tgt` (whose intermediate language is not
determinate), and its conclusion holds for every behaviour. -/
theorem nonvacuous_pipeline_behaviors_iff :
    FSimChain Src Tgt ∧ Receptive AnyInput Src ∧ Determinate AnyInput Tgt ∧
    NeverGoesWrong Src ∧ ¬ Determinate AnyInput Mid ∧
    (∀ b, HasBehavior Tgt b ↔ HasBehavior Src b) :=
  ⟨fsimChain_pos.1, src_receptive, tgt_determinate, src_neverGoesWrong, determinate_neg,
    src_tgt_same_behaviors⟩

/-- A two-pass instance of vertical composition in which one source step is
matched by two middle steps that each stutter in the last system, so that the
composite order genuinely uses the transitive closure of the second order:
`OneStep none 0 ⟶ Chain3 ⟶ Done 0`.  The composite step diagram holds. -/
theorem nonvacuous_comp_transGen :
    IsForwardSim (OneStep none 0) Chain3 emptyOrd chainRel₁ ∧
    IsForwardSim Chain3 (Done 0) succOrd chainRel₂ ∧
    Relation.TransGen succOrd 0 2 ∧ ¬ succOrd 0 2 ∧
    FSimStep (OneStep none 0) (Done 0) (compOrd emptyOrd succOrd) (compRel chainRel₁ chainRel₂) :=
  ⟨oneStep_chain3_isForwardSim, chain3_done_isForwardSim,
    Relation.TransGen.tail (Relation.TransGen.single (rfl : succOrd 0 1)) (rfl : succOrd 1 2),
    by intro h; have : (0 : Nat) + 1 = 2 := h; omega,
    cex_comp_naive_lex_order_fails.2.2.2⟩

/-- Hypotheses of the transitivity and antisymmetry lemmas hold together in
non-trivial instances: a composable chain of `Improves` steps
(`goesWrong [] ⟶ goesWrong [1] ⟶ terminates [1, 2] 0`), a mutual `Improves`
pair (necessarily equal behaviours), and a composable chain of refinements
(`StuckNow ⟶ Src ⟶ Tgt`). -/
theorem nonvacuous_preorder :
    (Improves (.goesWrong [] : Behavior Nat Nat) (.goesWrong [1]) ∧
      Improves (.goesWrong [1] : Behavior Nat Nat) (.terminates [1, 2] 0)) ∧
    (Improves (.diverges [4] : Behavior Nat Nat) (.diverges [4]) ∧
      Improves (.diverges [4] : Behavior Nat Nat) (.diverges [4])) ∧
    (RefinedBy StuckNow Src ∧ RefinedBy Src Tgt) :=
  ⟨⟨improves_goesWrong_nil _, improves_pos.1⟩, ⟨Improves.refl _, Improves.refl _⟩,
    ⟨fun b _ => ⟨.goesWrong [], (stuckNow_behavior _).2 rfl, improves_goesWrong_nil b⟩,
      positive_control_src_tgt.1⟩⟩

/-! ## The matching-relation lemmas: witnesses and necessity of their hypotheses -/

/-- Hypotheses of `Receptive.anti`, `Determinate.mono` and `LabelMatch.mono`
hold together in instances with a non-trivial inclusion `Eq ⊆ AnyInput`. -/
theorem nonvacuous_matching_lemmas :
    (Receptive AnyInput Src ∧ (∀ a b : Nat, Eq a b → AnyInput a b)) ∧
    (Determinate Eq Loop ∧ (∀ a b : Nat, Eq a b → AnyInput a b)) ∧
    ((∀ a b : Nat, Eq a b → AnyInput a b) ∧
      LabelMatch (Eq : Nat → Nat → Prop) (some 0) (some 0)) :=
  ⟨⟨src_receptive, fun _ _ _ => trivial⟩, ⟨loop_determinate_eq, fun _ _ _ => trivial⟩,
    ⟨fun _ _ _ => trivial, rfl⟩⟩

/-- Each hypothesis of the matching-relation lemmas is needed: without
`Receptive M L` (resp. `Determinate M L`) the conclusion can fail even with
the trivial inclusion; and `LabelMatch.mono` fails without the inclusion or
without the premise `LabelMatch M e₁ e₂`. -/
theorem cex_matching_lemmas :
    ((∀ a b : Nat, AnyInput a b → AnyInput a b) ∧ ¬ Receptive AnyInput (OneStep (some 0) 0)) ∧
    ((∀ a b : Nat, AnyInput a b → AnyInput a b) ∧ ¬ Determinate AnyInput Mid) ∧
    (LabelMatch AnyInput (some 0) (some 1) ∧
      ¬ LabelMatch (Eq : Nat → Nat → Prop) (some 0) (some 1)) ∧
    ((∀ a b : Nat, Eq a b → Eq a b) ∧
      ¬ LabelMatch (Eq : Nat → Nat → Prop) (some 0) (some 1)) :=
  ⟨⟨fun _ _ h => h, receptive_neg⟩, ⟨fun _ _ h => h, determinate_neg⟩,
    ⟨trivial, labelMatch_neg.2.2⟩, ⟨fun _ _ h => h, labelMatch_neg.2.2⟩⟩

end Toy.Sim.Examples
