import AnnealResearch.CostStack
import AnnealResearch.PrefixAccounting
import AnnealResearch.Observations

/-!
Binding the owned operational call/return experiment to accounting and actual
finite event paths. The observation policy charges every transition and exposes
return/UB events. No branch/address/ISA model is claimed for this language.
The public input selects recursion depth; the secret is unused by this program.
Thus the positive NI theorem is narrow and intentionally simple. The separate
Observations controls demonstrate why safety/output/cost bounds do not suffice
for other programs. No equality between source and target cost traces is claimed.
-/

namespace AnnealResearch.OperationalObservations

open Execution
open Observations

abbrev CS := CostStack.SourceState
abbrev CT := CostStack.TargetState

def AccountRelated (s : CS) (t : CT) : Prop :=
  s = t.source ∧ CostStack.Accounting t

/-- A concrete instance of the generic theorem covers pending administrative
prefixes. The family-specific CostStack theorem additionally removes +1 slack. -/
theorem accounting_instance (n : Nat) :
    PrefixAccounting.Accounting CostStack.SourceStep CostStack.TargetStep
      (CostStack.sourceInitial n) (CostStack.targetInitial n) AccountRelated
      (fun s => s.work) (fun s => s.peak) CostStack.total (fun t => t.source.peak)
      (fun work => 2 * work + 1) id := by
  constructor
  · intro t path
    exact ⟨t.source, CostStack.target_prefix_projection path,
      rfl, CostStack.target_accounting path⟩
  · intro s t related
    obtain ⟨rfl, account⟩ := related
    have equation := account.1
    have phaseBound : CostStack.phaseCost t.armed ≤ 1 := by
      cases t.armed <;> decide
    dsimp [CostStack.total]
    omega
  · intro s t related
    obtain ⟨rfl, _⟩ := related
    exact Nat.le_refl _

theorem generic_accounting_applies (n : Nat) :
    ∀ t, Reach CostStack.TargetStep (CostStack.targetInitial n) t →
      CostStack.total t ≤ 2 * CostStack.sourceBudget n + 1 ∧
      t.source.peak ≤ n + 1 := by
  apply PrefixAccounting.upper_bounds (accounting_instance n)
  · intro a b h
    omega
  · intro a b h
    exact h
  · intro s path
    exact (CostStack.source_prefix_bounds path).1
  · intro s path
    exact (CostStack.source_prefix_bounds path).2.2

universe u

inductive LoggedPath {S : Type u} (Step : S → S → Prop)
    (emit : S → S → List Event) : S → List Event → S → Prop where
  | refl (s : S) : LoggedPath Step emit s [] s
  | tail {initial current next : S} {events : List Event} :
      LoggedPath Step emit initial events current → Step current next →
      LoggedPath Step emit initial (events ++ emit current next) next

theorem LoggedPath.erase {S : Type u} {Step : S → S → Prop}
    {emit : S → S → List Event} {initial final : S} {events : List Event}
    (path : LoggedPath Step emit initial events final) : Reach Step initial final := by
  induction path with
  | refl => exact Reach.refl _
  | tail _ edge ih => exact Reach.tail ih edge

theorem log_reachable {S : Type u} {Step : S → S → Prop}
    (emit : S → S → List Event) {initial final : S}
    (path : Reach Step initial final) :
    ∃ events, LoggedPath Step emit initial events final := by
  induction path with
  | refl => exact ⟨[], LoggedPath.refl _⟩
  | tail _ edge ih =>
    obtain ⟨events, logged⟩ := ih
    exact ⟨_, LoggedPath.tail logged edge⟩

/-- This proves that event charges count actual transitions, instead of merely
assigning a convenient cost to completed output summaries. -/
theorem logged_cost {S : Type u} {Step : S → S → Prop}
    {emit : S → S → List Event} (charge : S → Nat)
    (charged : ∀ {s t}, Step s t → traceCost (emit s t) + charge s = charge t)
    {initial final : S} {events : List Event}
    (path : LoggedPath Step emit initial events final) :
    traceCost events + charge initial = charge final := by
  induction path with
  | refl => simp [traceCost]
  | tail _ edge ih =>
    have stepCharge := charged edge
    rw [traceCost_append]
    omega

def outcomeEvents : CostStack.Core → List Event
  | .done => [Event.outcome (.returned 0)]
  | .bad => [Event.outcome .ub]
  | _ => []

def coreEmission (core : CostStack.Core) : List Event :=
  Event.cost 1 :: outcomeEvents core

def sourceEmit (_ : CS) (next : CS) : List Event := coreEmission next.core
def targetEmit (_ : CT) (next : CT) : List Event :=
  if next.armed then [Event.cost 1] else coreEmission next.source.core

theorem emission_cost (core : CostStack.Core) : traceCost (coreEmission core) = 1 := by
  cases core <;> rfl

theorem target_emission_cost (s t : CT) : traceCost (targetEmit s t) = 1 := by
  cases phase : t.armed <;> simp [targetEmit, phase, emission_cost, traceCost]

theorem source_step_charge {s t : CS} (edge : CostStack.SourceStep s t) :
    traceCost (sourceEmit s t) + s.work = t.work := by
  rw [sourceEmit, emission_cost]
  cases edge
  dsimp
  omega

theorem target_step_charge {s t : CT} (edge : CostStack.TargetStep s t) :
    traceCost (targetEmit s t) + CostStack.total s = CostStack.total t := by
  rw [target_emission_cost]
  cases edge with
  | prepare sourceEdge => dsimp [CostStack.total]; omega
  | execute sourceEdge =>
    cases sourceEdge
    dsimp [CostStack.total]
    omega

def sourceRuns : TraceSet Input Event := fun input events =>
  ∃ final, LoggedPath CostStack.SourceStep sourceEmit
    (CostStack.sourceInitial input.publicSize) events final

def targetRuns : TraceSet Input Event := fun input events =>
  ∃ final, LoggedPath CostStack.TargetStep targetEmit
    (CostStack.targetInitial input.publicSize) events final

theorem source_operational_noninterference : FiniteNoninterference PublicRelated sourceRuns := by
  intro left right related events
  change left.publicSize = right.publicSize at related
  unfold sourceRuns
  rw [related]

theorem target_operational_noninterference : FiniteNoninterference PublicRelated targetRuns := by
  intro left right related events
  change left.publicSize = right.publicSize at related
  unfold targetRuns
  rw [related]

theorem source_observed_bounds (input : Input) {events : List Event} {final : CS}
    (path : LoggedPath CostStack.SourceStep sourceEmit
      (CostStack.sourceInitial input.publicSize) events final) :
    traceCost events ≤ 2 * input.publicSize + 2 ∧ final.peak ≤ input.publicSize + 1 := by
  have charged := logged_cost (fun s : CS => s.work) source_step_charge path
  have bounds := CostStack.source_prefix_bounds path.erase
  dsimp [CostStack.sourceInitial] at charged
  dsimp [CostStack.sourceBudget, CostStack.total] at bounds
  omega

theorem target_observed_bounds (input : Input) {events : List Event} {final : CT}
    (path : LoggedPath CostStack.TargetStep targetEmit
      (CostStack.targetInitial input.publicSize) events final) :
    traceCost events ≤ 4 * input.publicSize + 4 ∧ final.source.peak ≤ input.publicSize + 1 := by
  have charged := logged_cost CostStack.total target_step_charge path
  have bounds := CostStack.target_prefix_bounds path.erase
  dsimp [CostStack.total, CostStack.targetInitial, CostStack.embed,
    CostStack.sourceInitial] at charged
  dsimp [CostStack.sourceBudget, CostStack.total] at bounds
  omega

/-- Nonvacuous operational traces for every public n; event costs are exact. -/
theorem complete_observed_witnesses (n : Nat) :
    ∃ s sourceEvents targetEvents,
      LoggedPath CostStack.SourceStep sourceEmit (CostStack.sourceInitial n) sourceEvents s ∧
      LoggedPath CostStack.TargetStep targetEmit (CostStack.targetInitial n) targetEvents
        (CostStack.embed s) ∧
      CostStack.SourceOutput s 0 ∧
      traceCost sourceEvents = 2 * n + 2 ∧ traceCost targetEvents = 4 * n + 4 := by
  obtain ⟨s, sourcePath, output, targetPath, _, targetCost, _⟩ := CostStack.target_completion n
  obtain ⟨sourceEvents, sourceLog⟩ := log_reachable sourceEmit sourcePath
  obtain ⟨targetEvents, targetLog⟩ := log_reachable targetEmit targetPath
  have sourceCost := logged_cost (fun s : CS => s.work) source_step_charge sourceLog
  have targetCostEq := logged_cost CostStack.total target_step_charge targetLog
  have budget := (CostStack.source_reachable sourcePath).budget
  rw [output.1] at budget
  dsimp [CostStack.sourceInitial] at sourceCost
  dsimp [CostStack.total, CostStack.targetInitial, CostStack.embed,
    CostStack.sourceInitial] at targetCostEq
  dsimp [CostStack.remaining, CostStack.sourceBudget] at budget
  dsimp [CostStack.total, CostStack.embed, CostStack.sourceBudget] at targetCost
  exact ⟨s, sourceEvents, targetEvents, sourceLog, targetLog, output, by omega, by omega⟩

#print axioms accounting_instance
#print axioms generic_accounting_applies
#print axioms LoggedPath.erase
#print axioms log_reachable
#print axioms logged_cost
#print axioms source_step_charge
#print axioms target_step_charge
#print axioms source_operational_noninterference
#print axioms target_operational_noninterference
#print axioms source_observed_bounds
#print axioms target_observed_bounds
#print axioms complete_observed_witnesses

end AnnealResearch.OperationalObservations
