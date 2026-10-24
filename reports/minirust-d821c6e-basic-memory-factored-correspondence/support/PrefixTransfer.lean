import AnnealResearch.Execution

/-!
Safety transfer is directed from target safety to source safety. The source is
the reference execution subject; the target may factor one source transition
into a finite path, or match it with zero target transitions. Every source
configuration remains a boundary, including configurations that record UB.

`Step` must already represent one justified execution subject, as in Execution.
These results do not resolve strategy or prediction quantifiers. They neither
classify allowed stops nor establish progress, termination, or fairness.
-/

namespace AnnealResearch.PrefixTransfer

open Execution

universe u v

/-- A local simulation of every source edge, with badness visible at every
related boundary. A target path may have length zero. -/
structure StutteringSimulation {S : Type u} {T : Type v}
    (SourceStep : S → S → Prop) (TargetStep : T → T → Prop)
    (SourceBad : S → Prop) (TargetBad : T → Prop)
    (Related : S → T → Prop) : Prop where
  step : ∀ {s s' t}, Related s t → SourceStep s s' →
    ∃ t', Reach TargetStep t t' ∧ Related s' t'
  bad : ∀ {s t}, Related s t → SourceBad s → TargetBad t

section Transfer

variable {S : Type u} {T : Type v}
variable {SourceStep : S → S → Prop} {TargetStep : T → T → Prop}
variable {SourceBad : S → Prop} {TargetBad : T → Prop}
variable {Related : S → T → Prop}
variable {sourceInitial reached : S} {targetInitial : T}

/-- Every finite source prefix has a related reachable target boundary. -/
theorem reachable_coverage
    (sim : StutteringSimulation SourceStep TargetStep SourceBad TargetBad Related)
    (initialRelated : Related sourceInitial targetInitial)
    (path : Reach SourceStep sourceInitial reached) :
    ∃ targetReached, Reach TargetStep targetInitial targetReached ∧
      Related reached targetReached := by
  induction path with
  | refl => exact ⟨targetInitial, Reach.refl _, initialRelated⟩
  | tail _ edge ih =>
    obtain ⟨targetBoundary, targetPath, related⟩ := ih
    obtain ⟨nextBoundary, segment, nextRelated⟩ := sim.step related edge
    exact ⟨nextBoundary, targetPath.trans segment, nextRelated⟩

/-- A source bad prefix must have a target bad prefix. This is stronger than
agreement on completed executions or on compressed-command endpoints. -/
theorem bad_prefix_coverage
    (sim : StutteringSimulation SourceStep TargetStep SourceBad TargetBad Related)
    (initialRelated : Related sourceInitial targetInitial)
    (path : Reach SourceStep sourceInitial reached) (bad : SourceBad reached) :
    ∃ targetReached, Reach TargetStep targetInitial targetReached ∧
      TargetBad targetReached := by
  obtain ⟨targetReached, targetPath, related⟩ :=
    reachable_coverage sim initialRelated path
  exact ⟨targetReached, targetPath, sim.bad related bad⟩

/-- This formulation needs only prefix coverage; it does not require a local
simulation or a fixed bound on the number of target steps. -/
theorem sourceSafety_of_coverage
    (covered : ∀ s, Reach SourceStep sourceInitial s →
      ∃ t, Reach TargetStep targetInitial t ∧ Related s t)
    (badReflects : ∀ {s t}, Related s t → SourceBad s → TargetBad t)
    (targetSafe : NoUB TargetStep TargetBad targetInitial) :
    NoUB SourceStep SourceBad sourceInitial := by
  intro s sourcePath sourceBad
  obtain ⟨t, targetPath, related⟩ := covered s sourcePath
  exact targetSafe t targetPath (badReflects related sourceBad)

/-- Target safety implies source safety. No hypothesis about allowed stops or
progress is needed, and no such conclusion is made. -/
theorem sourceSafety
    (sim : StutteringSimulation SourceStep TargetStep SourceBad TargetBad Related)
    (initialRelated : Related sourceInitial targetInitial)
    (targetSafe : NoUB TargetStep TargetBad targetInitial) :
    NoUB SourceStep SourceBad sourceInitial := by
  apply sourceSafety_of_coverage
    (fun _ path => reachable_coverage sim initialRelated path) sim.bad targetSafe

end Transfer

/- Safety alone leaves stop classification and reachable progress open. The
unsupported state is safe but has neither an allowed stop nor an outgoing edge. -/
theorem safety_does_not_establish_progress :
    NoUB PrefixExamples.Step PrefixExamples.Bad .unsupported ∧
    ¬ ReachableProgress PrefixExamples.Step PrefixExamples.Allowed .unsupported := by
  constructor
  · exact PrefixExamples.unsupported_noUB
  · intro progress
    exact PrefixExamples.unsupported_not_verified
      ⟨PrefixExamples.unsupported_noUB, progress⟩

namespace ZeroStep

-- The source loops; the target is already stopped. The simulation is legal
-- because finite-prefix safety transfer does not transfer termination.
def SourceStep (_ _ : Unit) : Prop := True
def TargetStep (_ _ : Unit) : Prop := False
def Bad (_ : Unit) : Prop := False
def Related (_ _ : Unit) : Prop := True

theorem simulation :
    StutteringSimulation SourceStep TargetStep Bad Bad Related := by
  constructor
  · intro s s' t _ _
    exact ⟨t, Reach.refl _, True.intro⟩
  · intro s t _ bad
    exact bad

def CanStop {X : Type u} (Step : X → X → Prop) (initial : X) : Prop :=
  ∃ stopped, Reach Step initial stopped ∧ ¬ ∃ next, Step stopped next

theorem target_can_stop : CanStop TargetStep () := by
  refine ⟨(), Reach.refl _, ?_⟩
  rintro ⟨next, edge⟩
  exact edge

theorem source_cannot_stop : ¬ CanStop SourceStep () := by
  rintro ⟨stopped, _, noNext⟩
  exact noNext ⟨(), True.intro⟩

theorem target_safe : NoUB TargetStep Bad () := by
  intro reached path bad
  exact bad

theorem source_safe : NoUB SourceStep Bad () :=
  sourceSafety simulation True.intro target_safe

theorem zero_step_matching_does_not_transfer_termination :
    StutteringSimulation SourceStep TargetStep Bad Bad Related ∧
    CanStop TargetStep () ∧ ¬ CanStop SourceStep () :=
  ⟨simulation, target_can_stop, source_cannot_stop⟩

end ZeroStep

namespace HiddenBad

inductive State where
  | entry
  | bad
  | spin
  | done
  deriving DecidableEq

inductive SourceStep : State → State → Prop where
  | enterBad : SourceStep .entry .bad
  | leaveBad : SourceStep .bad .spin
  | loop : SourceStep .spin .spin
  | finish : SourceStep .entry .done

def SourceBad (s : State) : Prop := s = .bad
def TargetStep (_ _ : Unit) : Prop := False
def TargetBad (_ : Unit) : Prop := False

-- Both subjects can finish with output zero. Only the source also has a bad
-- prefix followed by an infinite suffix. Completed output sets miss that prefix.
def SourceOutput (s : State) (n : Nat) : Prop := s = .done ∧ n = 0
def TargetOutput (_ : Unit) (n : Nat) : Prop := n = 0

def CompletedOutput {X : Type u} (Step : X → X → Prop)
    (Output : X → Nat → Prop) (initial : X) (n : Nat) : Prop :=
  ∃ stopped, Reach Step initial stopped ∧ Output stopped n

theorem completed_output_agreement (n : Nat) :
    CompletedOutput SourceStep SourceOutput .entry n ↔
    CompletedOutput TargetStep TargetOutput () n := by
  constructor
  · rintro ⟨stopped, _, _, output⟩
    exact ⟨(), Reach.refl _, output⟩
  · rintro ⟨stopped, _, output⟩
    exact ⟨.done, Reach.tail (Reach.refl _) SourceStep.finish, rfl, output⟩

theorem target_safe : NoUB TargetStep TargetBad () := by
  intro reached path bad
  exact bad

theorem source_unsafe : ¬ NoUB SourceStep SourceBad .entry := by
  exact bad_prefix_not_noUB
    (Reach.tail (Reach.refl _) SourceStep.enterBad) rfl

def divergentSuffix : Nat → State
  | 0 => .bad
  | _ + 1 => .spin

theorem divergent_suffix_steps (n : Nat) :
    SourceStep (divergentSuffix n) (divergentSuffix (n + 1)) := by
  cases n with
  | zero => exact SourceStep.leaveBad
  | succ n => exact SourceStep.loop

theorem hidden_bad_prefix_before_divergence :
    Reach SourceStep .entry (divergentSuffix 0) ∧
    SourceBad (divergentSuffix 0) ∧
    (∀ n, SourceStep (divergentSuffix n) (divergentSuffix (n + 1))) ∧
    ¬ NoUB SourceStep SourceBad .entry :=
  ⟨Reach.tail (Reach.refl _) SourceStep.enterBad, rfl,
    divergent_suffix_steps, source_unsafe⟩

theorem output_agreement_does_not_transfer_safety :
    (∀ n, CompletedOutput SourceStep SourceOutput .entry n ↔
      CompletedOutput TargetStep TargetOutput () n) ∧
    NoUB TargetStep TargetBad () ∧ ¬ NoUB SourceStep SourceBad .entry :=
  ⟨completed_output_agreement, target_safe, source_unsafe⟩

-- Relating just the outer endpoints of entry → bad → spin would discard UB.
-- The local simulation obligation rejects that proposed compression at bad.
def OuterBoundary (s : State) (_ : Unit) : Prop := s ≠ .bad

theorem omitted_bad_boundary_rejects_simulation :
    ¬ StutteringSimulation SourceStep TargetStep SourceBad TargetBad OuterBoundary := by
  intro sim
  have entryRelated : OuterBoundary .entry () := by
    intro impossible
    cases impossible
  obtain ⟨target, _, badRelated⟩ := sim.step entryRelated SourceStep.enterBad
  exact badRelated rfl

-- Even if one tries to relate the bad boundary, target safety and bad reflection
-- rule out a simulation that covers this source initial configuration.
theorem no_bad_reflecting_cover
    (Related : State → Unit → Prop)
    (initialRelated : Related .entry ()) :
    ¬ StutteringSimulation SourceStep TargetStep SourceBad TargetBad Related := by
  intro sim
  exact source_unsafe (sourceSafety sim initialRelated target_safe)

end HiddenBad

#print axioms reachable_coverage
#print axioms bad_prefix_coverage
#print axioms sourceSafety_of_coverage
#print axioms sourceSafety
#print axioms safety_does_not_establish_progress
#print axioms ZeroStep.zero_step_matching_does_not_transfer_termination
#print axioms ZeroStep.source_safe
#print axioms HiddenBad.completed_output_agreement
#print axioms HiddenBad.hidden_bad_prefix_before_divergence
#print axioms HiddenBad.output_agreement_does_not_transfer_safety
#print axioms HiddenBad.omitted_bad_boundary_rejects_simulation
#print axioms HiddenBad.no_bad_reflecting_cover

end AnnealResearch.PrefixTransfer
