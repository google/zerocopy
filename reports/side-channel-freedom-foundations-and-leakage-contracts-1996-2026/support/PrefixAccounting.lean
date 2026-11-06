import AnnealResearch.PrefixTransfer

/-!
Property-specific coverage experiment. Source-bad-prefix reflection and target
upper bounds quantify in different directions. Metrics here are supplied Nat
functions on instrumented states: a concrete instance must justify that they
really count cumulative work and peak depth, including intermediate states.
No Rust, ISA, termination, fairness, or physical-time interpretation is assumed.
-/

namespace AnnealResearch.PrefixAccounting

open Execution

universe u v

structure Accounting {S : Type u} {T : Type v}
    (SourceStep : S → S → Prop) (TargetStep : T → T → Prop)
    (sourceInitial : S) (targetInitial : T) (Related : S → T → Prop)
    (sourceCost sourcePeak : S → Nat) (targetCost targetPeak : T → Nat)
    (costMap peakMap : Nat → Nat) : Prop where
  cover : ∀ t, Reach TargetStep targetInitial t →
    ∃ s, Reach SourceStep sourceInitial s ∧ Related s t
  cost : ∀ s t, Related s t → targetCost t ≤ costMap (sourceCost s)
  peak : ∀ s t, Related s t → targetPeak t ≤ peakMap (sourcePeak s)

/-- Every target prefix, including an administrative intermediate prefix, needs
coverage. Source upper bounds and monotonicity then transport in the indicated
direction. Cost and peak remain independent obligations. -/
theorem upper_bounds {S : Type u} {T : Type v}
    {SourceStep : S → S → Prop} {TargetStep : T → T → Prop}
    {sourceInitial : S} {targetInitial : T} {Related : S → T → Prop}
    {sourceCost sourcePeak : S → Nat} {targetCost targetPeak : T → Nat}
    {costMap peakMap : Nat → Nat} {costBound peakBound : Nat}
    (account : Accounting SourceStep TargetStep sourceInitial targetInitial
      Related sourceCost sourcePeak targetCost targetPeak costMap peakMap)
    (costMono : ∀ a b, a ≤ b → costMap a ≤ costMap b)
    (peakMono : ∀ a b, a ≤ b → peakMap a ≤ peakMap b)
    (sourceCostBound : ∀ s, Reach SourceStep sourceInitial s → sourceCost s ≤ costBound)
    (sourcePeakBound : ∀ s, Reach SourceStep sourceInitial s → sourcePeak s ≤ peakBound) :
    ∀ t, Reach TargetStep targetInitial t →
      targetCost t ≤ costMap costBound ∧ targetPeak t ≤ peakMap peakBound := by
  intro t targetPath
  obtain ⟨s, sourcePath, related⟩ := account.cover t targetPath
  exact ⟨Nat.le_trans (account.cost s t related)
      (costMono _ _ (sourceCostBound s sourcePath)),
    Nat.le_trans (account.peak s t related)
      (peakMono _ _ (sourcePeakBound s sourcePath))⟩

namespace ExtraTarget

inductive SourceStep : Bool → Bool → Prop where
  | finish : SourceStep false true

inductive Target where
  | loop (charged : Nat)
  | done (charged : Nat)
  deriving DecidableEq

inductive TargetStep : Target → Target → Prop where
  | admin (n : Nat) : TargetStep (.loop n) (.loop (n + 1))
  | finish (n : Nat) : TargetStep (.loop n) (.done (n + 1))

def Related : Bool → Target → Prop
  | false, .loop _ => True
  | true, .done _ => True
  | _, _ => False

def SourceCost (s : Bool) : Nat := if s then 1 else 0

def TargetCost : Target → Nat
  | .loop n | .done n => n

def SourceBad (_ : Bool) : Prop := False
def TargetBad (_ : Target) : Prop := False

/-- This is the existing source-to-target safety simulation. It can ignore any
number of charged target-only administrative iterations. -/
theorem safety_simulation : PrefixTransfer.StutteringSimulation
    SourceStep TargetStep SourceBad TargetBad Related := by
  constructor
  · intro s s' t related edge
    cases edge
    cases t with
    | loop n =>
      exact ⟨.done (n + 1), Reach.tail (Reach.refl _) (TargetStep.finish n), trivial⟩
    | done n => exact False.elim related
  · intro s t _ bad
    exact bad

theorem source_safe : NoUB SourceStep SourceBad false := by
  intro _ _ bad
  exact bad

theorem target_safe : NoUB TargetStep TargetBad (.loop 0) := by
  intro _ _ bad
  exact bad

theorem source_cost_bound : ∀ s, Reach SourceStep false s → SourceCost s ≤ 1 := by
  intro s _
  cases s <;> decide

theorem loop_reachable (n : Nat) : Reach TargetStep (.loop 0) (.loop n) := by
  induction n with
  | zero => exact Reach.refl _
  | succ n ih => exact Reach.tail ih (TargetStep.admin n)

theorem unbounded_target_cost (bound : Nat) :
    ∃ t, Reach TargetStep (.loop 0) t ∧ bound < TargetCost t := by
  exact ⟨.loop (bound + 1), loop_reachable _, Nat.lt_succ_self _⟩

theorem no_target_cost_bound (bound : Nat) :
    ¬ (∀ t, Reach TargetStep (.loop 0) t → TargetCost t ≤ bound) := by
  intro bounded
  obtain ⟨t, path, exceeds⟩ := unbounded_target_cost bound
  exact (Nat.not_le_of_gt exceeds) (bounded t path)

def SourceOutput (s : Bool) (output : Nat) : Prop := s = true ∧ output = 0
def TargetOutput (t : Target) (output : Nat) : Prop :=
  (∃ n, t = .done n) ∧ output = 0

def CompletedOutput {S : Type u} (Step : S → S → Prop)
    (Output : S → Nat → Prop) (initial : S) (output : Nat) : Prop :=
  ∃ final, Reach Step initial final ∧ Output final output

theorem completed_output_agreement (output : Nat) :
    CompletedOutput SourceStep SourceOutput false output ↔
      CompletedOutput TargetStep TargetOutput (.loop 0) output := by
  constructor
  · rintro ⟨_, _, _, outputZero⟩
    exact ⟨.done 1, Reach.tail (Reach.refl _) (TargetStep.finish 0), ⟨0 + 1, rfl⟩,
      outputZero⟩
  · rintro ⟨_, _, _, outputZero⟩
    exact ⟨true, Reach.tail (Reach.refl _) SourceStep.finish, rfl, outputZero⟩

/-- Actual infinite enabled target execution with unbounded charged work; no
claim that fairness forces this choice, or that every target run diverges. -/
theorem infinite_admin_steps (n : Nat) :
    TargetStep (.loop n) (.loop (n + 1)) := TargetStep.admin n

theorem safety_and_output_do_not_bound_target :
    PrefixTransfer.StutteringSimulation SourceStep TargetStep SourceBad TargetBad Related ∧
    NoUB SourceStep SourceBad false ∧ NoUB TargetStep TargetBad (.loop 0) ∧
    (∀ s, Reach SourceStep false s → SourceCost s ≤ 1) ∧
    (∀ output, CompletedOutput SourceStep SourceOutput false output ↔
      CompletedOutput TargetStep TargetOutput (.loop 0) output) ∧
    (∀ bound, ¬ (∀ t, Reach TargetStep (.loop 0) t → TargetCost t ≤ bound)) :=
  ⟨safety_simulation, source_safe, target_safe, source_cost_bound,
    completed_output_agreement, no_target_cost_bound⟩

end ExtraTarget

#print axioms upper_bounds
#print axioms ExtraTarget.safety_simulation
#print axioms ExtraTarget.source_safe
#print axioms ExtraTarget.target_safe
#print axioms ExtraTarget.source_cost_bound
#print axioms ExtraTarget.loop_reachable
#print axioms ExtraTarget.unbounded_target_cost
#print axioms ExtraTarget.no_target_cost_bound
#print axioms ExtraTarget.completed_output_agreement
#print axioms ExtraTarget.infinite_admin_steps
#print axioms ExtraTarget.safety_and_output_do_not_bound_target

end AnnealResearch.PrefixAccounting
