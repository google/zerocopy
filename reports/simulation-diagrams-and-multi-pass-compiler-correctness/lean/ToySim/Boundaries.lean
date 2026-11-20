import ToySim.Examples

/-!
# Boundary facts (all fully proved)

Concrete instances that delimit what the main results say.  They are cited
from the non-claims of the result cards.  Every theorem in this file is proved
outright from the definitions.
-/

namespace Toy.Sim.Boundary
open Ex Cex Examples

/-! ## Refinement is a preorder, not a partial order -/

/-- `RefinedBy` is not antisymmetric: `StuckNow` and `NoInit` refine each
other but are different systems. -/
theorem refinedBy_not_antisymmetric :
    RefinedBy StuckNow NoInit ∧ RefinedBy NoInit StuckNow ∧ StuckNow ≠ NoInit := by
  refine ⟨fun b _ => ⟨.goesWrong [], (stuckNow_behavior _).2 rfl, improves_goesWrong_nil b⟩,
    fun b _ => ⟨.goesWrong [], (noInit_behavior _).2 rfl, improves_goesWrong_nil b⟩, ?_⟩
  intro heq
  have h1 : ∃ s, StuckNow.init s := ⟨(), trivial⟩
  rw [congrArg (fun L : LTS Nat Nat => ∃ s, L.init s) heq] at h1
  obtain ⟨_, h2⟩ := h1
  exact h2

/-- Two initial states and no step: `false` is stuck, `true` is final with
result `0`.  Its behaviours include `goesWrong []` and `terminates [] 0`. -/
abbrev StuckOrDone : LTS Nat Nat where
  State := Bool
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun s r => s = true ∧ r = 0

/-- **Mutual refinement does not imply equal behaviour sets.**
`StuckOrDone` and `StuckNow` refine each other (because `goesWrong []` is
improved by every behaviour), yet only `StuckOrDone` can terminate. -/
theorem mutual_refinedBy_different_behaviors :
    RefinedBy StuckOrDone StuckNow ∧ RefinedBy StuckNow StuckOrDone ∧
    HasBehavior StuckOrDone (.terminates [] 0) ∧
    ¬ HasBehavior StuckNow (.terminates [] 0) := by
  refine ⟨?_, ?_, ⟨true, true, trivial, Star.refl _, ⟨rfl, rfl⟩⟩, ?_⟩
  · intro b hb
    rw [(stuckNow_behavior b).1 hb]
    exact ⟨.goesWrong [], Or.inl ⟨false, false, trivial, Star.refl _,
      fun _ _ h => h, fun _ h => Bool.noConfusion h.1⟩, Improves.refl _⟩
  · intro b _
    exact ⟨.goesWrong [], (stuckNow_behavior _).2 rfl, improves_goesWrong_nil b⟩
  · intro h
    have h' := (stuckNow_behavior _).1 h
    cases h'

/-! ## Runs with infinitely many events are invisible to `RefinedBy` -/

/-- Two initial states: `false` is final with result `0` and has no step;
`true` emits the event `0` forever. -/
abbrev DoneOrChatter : LTS Nat Nat where
  State := Bool
  step := fun s e s' => s = true ∧ e = some 0 ∧ s' = true
  init := fun _ => True
  final := fun s r => s = false ∧ r = 0

/-- The only behaviour of `DoneOrChatter` is "return `0`": its run that emits
events forever is not a behaviour in this model. -/
theorem doneOrChatter_behavior (b : Behavior Nat Nat) :
    HasBehavior DoneOrChatter b ↔ b = .terminates [] 0 := by
  have inv : ∀ {t : List Nat} {s : Bool}, Star DoneOrChatter true t s → s = true :=
    fun h => Star.invariant (L := DoneOrChatter) (fun s => s = true)
      (fun _ _ _ _ h => h.2.2) h rfl
  have fromFalse : ∀ {t : List Nat} {s : Bool}, Star DoneOrChatter false t s →
      t = [] ∧ s = false :=
    fun h => Star.of_noStep (L := DoneOrChatter) (fun _ _ h => Bool.noConfusion h.1) h
  constructor
  · intro h
    cases b with
    | terminates t r =>
      obtain ⟨s₀, s, _, hstar, hfin⟩ := h
      cases s₀ with
      | false =>
        obtain ⟨rfl, _⟩ := fromFalse hstar
        rw [hfin.2]
      | true =>
        have hs := inv hstar
        rw [hs] at hfin
        exact Bool.noConfusion hfin.1
    | diverges t =>
      obtain ⟨_, _, _, _, f, _, hf⟩ := h
      exact absurd (hf 0).2.1 (by simp)
    | goesWrong t =>
      rcases h with ⟨_, s, _, _, hstuck⟩ | ⟨_, hno⟩
      · cases s with
        | false => exact (hstuck.2 0 ⟨rfl, rfl⟩).elim
        | true => exact (hstuck.1 (some 0) true ⟨rfl, rfl, rfl⟩).elim
      · exact (hno false trivial).elim
  · rintro rfl
    exact ⟨false, false, trivial, Star.refl _, ⟨rfl, rfl⟩⟩

/-- **`RefinedBy` and behaviour equality ignore runs that emit infinitely
many events, also in a target that has modelled behaviours.**
`DoneOrChatter` has exactly the behaviours of `Done 0` and refines it,
although it has a run from an initial state that emits the event `0` forever.
No backward simulation from `Done 0` to `DoneOrChatter` exists: a backward
simulation constrains every target step, including the steps of that run. -/
theorem refinedBy_blind_to_infinite_event_runs :
    (∀ b, HasBehavior DoneOrChatter b ↔ HasBehavior (Done 0) b) ∧
    RefinedBy (Done 0) DoneOrChatter ∧
    (∃ f : Nat → DoneOrChatter.State, DoneOrChatter.init (f 0) ∧
        ∀ n, DoneOrChatter.step (f n) (some 0) (f (n + 1))) ∧
    NoBackwardSim (Done 0) DoneOrChatter := by
  have same : ∀ b, HasBehavior DoneOrChatter b ↔ HasBehavior (Done 0) b := by
    intro b
    rw [doneOrChatter_behavior, done_behavior]
  refine ⟨same, fun b hb => ⟨b, (same b).1 hb, Improves.refl b⟩,
    ⟨fun _ => true, trivial, fun _ => ⟨rfl, rfl, rfl⟩⟩, ?_⟩
  rintro ⟨I, ord, R, hb⟩
  obtain ⟨i, s₁, _, hR⟩ := hb.initMatch () true trivial trivial
  obtain ⟨_, _, hmove, _⟩ :=
    hb.step i s₁ true (some 0) true hR (done_all_safe 0 s₁) ⟨rfl, rfl, rfl⟩
  rcases hmove with hp | ⟨hs, _⟩
  · exact done_no_event_run hp.star
  · exact done_no_event_run hs

/-! ## Refinement may remove termination from a source that never goes wrong -/

/-- From the initial state `root`, a silent step leads to `left` (final with
result `0`) and another silent step leads to `right`, which loops silently
forever. -/
abbrev TermOrDiverge : LTS Nat Nat where
  State := Three
  step := fun s e s' =>
    e = none ∧ ((s = .root ∧ (s' = .left ∨ s' = .right)) ∨ (s = .right ∧ s' = .right))
  init := fun s => s = .root
  final := fun s r => s = .left ∧ r = 0

/-- **Refinement does not preserve termination, even for a source that never
goes wrong.**  `TermOrDiverge` may return `0` or diverge silently; `Loop`,
which always diverges, refines it. -/
theorem refinedBy_may_drop_termination :
    NeverGoesWrong TermOrDiverge ∧
    HasBehavior TermOrDiverge (.terminates [] 0) ∧
    HasBehavior TermOrDiverge (.diverges []) ∧
    RefinedBy TermOrDiverge Loop ∧ ¬ HasBehavior Loop (.terminates [] 0) := by
  have hdiv : HasBehavior TermOrDiverge (.diverges []) := by
    refine ⟨.root, .root, rfl, Star.refl _,
      fun n => match n with | 0 => Three.root | _ + 1 => Three.right, rfl, ?_⟩
    intro n
    cases n with
    | zero => exact ⟨rfl, Or.inl ⟨rfl, Or.inr rfl⟩⟩
    | succ n => exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  have hns : ∀ s, ¬ Stuck TermOrDiverge s := by
    intro s h
    cases s with
    | root => exact h.1 none .left ⟨rfl, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    | left => exact h.2 0 ⟨rfl, rfl⟩
    | right => exact h.1 none .right ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  refine ⟨neverGoesWrong_of_no_stuck hns ⟨.root, rfl⟩,
    ⟨.root, .left, rfl, Star.single (L := TermOrDiverge) ⟨rfl, Or.inl ⟨rfl, Or.inl rfl⟩⟩,
      ⟨rfl, rfl⟩⟩, hdiv, ?_, loop_lacks (by simp)⟩
  intro b hb
  rw [(loop_behavior b).1 hb]
  exact ⟨_, hdiv, Improves.refl _⟩

/-! ## Forward simulations cannot remove source behaviours -/

/-- Relation for a backward simulation from `TwoBranch none none 0 1` to
`Done 0`: the target's only state is related to the source's initial state. -/
def chooseRel : Unit → Three → Unit → Prop := fun _ s _ => s = .root

/-- **A pass that resolves observable nondeterminism of a source that never
goes wrong cannot be verified by a forward simulation.**  The source may
return `0` or `1` and never goes wrong; the deterministic target `Done 0`
refines it, and a backward simulation exists; but no forward simulation
exists, because a forward simulation would have to preserve the source
behaviour "return `1`". -/
theorem resolving_nondeterminism_needs_backward_simulation :
    NeverGoesWrong (TwoBranch none none 0 1) ∧ Determinate Eq (Done 0) ∧
    IsBackwardSim (TwoBranch none none 0 1) (Done 0) emptyOrd chooseRel ∧
    RefinedBy (TwoBranch none none 0 1) (Done 0) ∧
    ¬ ∃ (I : Type) (ord : I → I → Prop)
        (R : I → (TwoBranch none none 0 1).State → (Done 0).State → Prop),
        IsForwardSim (TwoBranch none none 0 1) (Done 0) ord R := by
  have hleft : Star (TwoBranch none none 0 1) .root [] .left :=
    Star.single (L := TwoBranch none none 0 1) ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  have hns : ∀ s, ¬ Stuck (TwoBranch none none 0 1) s := by
    intro s h
    cases s with
    | root => exact h.1 none .left ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | left => exact h.2 0 (Or.inl ⟨rfl, rfl⟩)
    | right => exact h.2 1 (Or.inr ⟨rfl, rfl⟩)
  refine ⟨neverGoesWrong_of_no_stuck hns ⟨.root, rfl⟩, done_determinate Eq 0, ?_, ?_, ?_⟩
  · refine ⟨wf_emptyOrd, fun _ => ⟨(), trivial⟩, fun _ _ _ _ => ⟨(), .root, rfl, rfl⟩,
      ?_, fun _ _ _ _ _ => Or.inl ⟨0, rfl⟩, fun _ _ _ _ _ _ _ h => h.elim⟩
    intro i s₁ s₂ r hR _ hfin
    have hs : s₁ = .root := hR
    have hr : r = 0 := hfin
    subst hs hr
    exact ⟨.left, hleft, Or.inl ⟨rfl, rfl⟩⟩
  · intro b hb
    rw [(done_behavior 0 b).1 hb]
    exact ⟨.terminates [] 0, ⟨.root, .left, rfl, hleft, Or.inl ⟨rfl, rfl⟩⟩, Improves.refl _⟩
  · rintro ⟨I, ord, R, hsim⟩
    obtain ⟨i, s₂, _, hR⟩ := hsim.init .root rfl
    obtain ⟨i', s₂', _, hR'⟩ := hsim.step i .root s₂ none .right hR ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
    have h1 : (1 : Nat) = 0 := hsim.final i' .right s₂' 1 hR' (Or.inr ⟨rfl, rfl⟩)
    simp at h1

/-! ## Determinacy is required of unreachable states as well -/

/-- Two states: `false` (initial) is final with result `0` and has no step;
`true` is unreachable and has silent steps to both states. -/
abbrev DoneWithJunk : LTS Nat Nat where
  State := Bool
  step := fun s e _ => s = true ∧ e = none
  init := fun s => s = false
  final := fun s r => s = false ∧ r = 0

/-- **Nondeterminism confined to unreachable states need not break the
conclusion of the flip lemma.**  `DoneWithJunk` is not determinate (its
unreachable state has two successors for the same label), yet it
forward-simulates `Done 0` and a backward simulation containing the forward
relation exists.  So `Determinate` is sufficient, not necessary, for the
conclusion in a given instance. -/
theorem flip_conclusion_with_unreachable_nondeterminism :
    IsForwardSim (Done 0) DoneWithJunk emptyOrd relToFalse ∧
    ¬ StepFunctional DoneWithJunk ∧ ¬ Determinate Eq DoneWithJunk ∧
    IsBackwardSim (Done 0) DoneWithJunk emptyOrd relToFalse ∧
    (∀ i s₁ s₂, relToFalse i s₁ s₂ → ∃ i', relToFalse i' s₁ s₂) := by
  have hnf : ¬ StepFunctional DoneWithJunk := by
    intro h
    have := h true none true false ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    cases this
  refine ⟨⟨wf_emptyOrd, fun _ _ => ⟨(), false, rfl, rfl⟩, ?_, fun _ _ _ _ _ _ h => h.elim⟩,
    hnf, fun h => hnf h.functional, ?_, fun i _ _ h => ⟨i, h⟩⟩
  · intro _ _ s' r hR hfin
    exact ⟨hR, hfin⟩
  · refine ⟨wf_emptyOrd, fun _ => ⟨false, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro _ s₂ _ h₂
      exact ⟨(), (), trivial, h₂⟩
    · intro _ s₁ _ r _ _ hfin
      exact ⟨s₁, Star.refl _, hfin.2⟩
    · intro _ _ s₂ hR _
      exact Or.inl ⟨0, hR, rfl⟩
    · intro _ _ s₂ e s₂' hR _ hstep
      exact Bool.noConfusion (hR.symm.trans hstep.1)

end Toy.Sim.Boundary
