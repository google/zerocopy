import AnnealResearch.OperationalObservations
import AnnealResearch.ObservationAdapters

/-!
Operational binding of the publicly uniform cost-expansion adapter to the
owned CostStack two-phase machine. Actual source logged paths compile to actual
target paths with exactly the expanded events. Every target logged prefix is
covered, including the extra cost emitted by an armed administrative state.

Operation logging emits cost plus outcome atomically. Event-level PrefixClosure
therefore admits observations between the final cost and its return/UB outcome;
these need not themselves end at an operational configuration. Exact image
coverage below uses that policy explicitly on both sides.

The result concerns this owned, unit-cost call/return/fault/spin language and its
specified logging functions. It is not a compiler/ISA/Rust correspondence,
physical timing theorem, infinite-trace equivalence, probabilistic result, or
new safety theorem. The existing source-bad-prefix simulation remains separate
from the reverse target-prefix coverage needed here.
-/

namespace AnnealResearch.OperationalAdapter

open Execution
open Observations
open OperationalObservations
open ObservationAdapters

universe u v

theorem prefix_append_left {Visible : Type u} (left : List Visible)
    {first last : List Visible} (pre : Prefix first last) :
    Prefix (left ++ first) (left ++ last) := by
  induction left with
  | nil => exact pre
  | cons event rest ih => exact Prefix.cons ih

theorem expand_append (first second : List Event) :
    expand (first ++ second) = expand first ++ expand second := by
  induction first with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [expand, ih]

/-- Outcomes are retained once; the preceding charged event is duplicated. -/
theorem expand_core_emission (core : CostStack.Core) :
    expand (coreEmission core) = Event.cost 1 :: coreEmission core := by
  cases core <;> rfl

/-- Concatenation retains the emissions of every actual intermediate step. -/
theorem logged_trans {S : Type u} {Step : S → S → Prop}
    {emit : S → S → List Event} {initial middle final : S}
    {first second : List Event}
    (before : LoggedPath Step emit initial first middle)
    (after : LoggedPath Step emit middle second final) :
    LoggedPath Step emit initial (first ++ second) final := by
  induction after with
  | refl => simpa using before
  | tail previous edge ih =>
      simpa [List.append_assoc] using LoggedPath.tail ih edge

/-- One source operation expands to an actual prepare/execute target segment. -/
theorem compile_logged_edge {s s' : CS} (edge : CostStack.SourceStep s s') :
    LoggedPath CostStack.TargetStep targetEmit
      (CostStack.embed s) (expand (sourceEmit s s')) (CostStack.embed s') := by
  have sourceEdge := edge
  cases edge with
  | execute coreEdge =>
      have prepared := LoggedPath.tail (emit := targetEmit)
        (LoggedPath.refl (CostStack.embed _))
        (CostStack.TargetStep.prepare sourceEdge)
      have executed := LoggedPath.tail prepared (CostStack.TargetStep.execute sourceEdge)
      simpa [CostStack.embed, targetEmit, sourceEmit, expand_core_emission,
        List.append_assoc] using executed

/-- Every actual source finite path has an exact expanded operational target
path, with the same endpoint core, useful work, and peak at a ready boundary. -/
theorem compile_logged_path {initial final : CS} {events : List Event}
    (path : LoggedPath CostStack.SourceStep sourceEmit initial events final) :
    LoggedPath CostStack.TargetStep targetEmit
      (CostStack.embed initial) (expand events) (CostStack.embed final) := by
  induction path with
  | refl => exact LoggedPath.refl _
  | tail previous edge ih =>
      simpa [expand_append] using logged_trans ih (compile_logged_edge edge)

def pendingEvents (armed : Bool) : List Event :=
  if armed then [Event.cost 1] else []

/-- Exact reverse accounting of actual target logs. Preparing has emitted one
additional cost, while projecting to the same reachable source configuration. -/
theorem target_log_decomposition {initial : CS} {final : CT} {targetEvents : List Event}
    (path : LoggedPath CostStack.TargetStep targetEmit
      (CostStack.embed initial) targetEvents final) :
    ∃ sourceEvents,
      LoggedPath CostStack.SourceStep sourceEmit initial sourceEvents final.source ∧
      targetEvents = expand sourceEvents ++ pendingEvents final.armed := by
  induction path with
  | refl =>
      exact ⟨[], LoggedPath.refl _, by simp [CostStack.embed, expand, pendingEvents]⟩
  | tail previous edge ih =>
      obtain ⟨sourceEvents, sourceLog, equation⟩ := ih
      cases edge with
      | prepare sourceEdge =>
          refine ⟨sourceEvents, sourceLog, ?_⟩
          simp [pendingEvents] at equation
          simp [targetEmit, pendingEvents, equation]
      | execute sourceEdge =>
          refine ⟨sourceEvents ++ sourceEmit _ _, LoggedPath.tail sourceLog sourceEdge, ?_⟩
          simp [pendingEvents] at equation
          simp [targetEmit, pendingEvents, equation, expand_append,
            sourceEmit, expand_core_emission, List.append_assoc]

/-- A pending cost is genuinely the prefix of the next enabled source
operation's expansion, even when that operation also emits an outcome. -/
theorem pending_cost_prefix (s next : CS) :
    Prefix [Event.cost 1] (expand (sourceEmit s next)) := by
  rw [sourceEmit, expand_core_emission]
  exact Prefix.cons Prefix.nil

/-- Every actual target logged prefix is covered by expansion of an actual
source logged prefix. For an armed state, the source witness takes the enabled
next step; a zero-step source projection alone would miss its pending cost. -/
theorem target_logged_prefix_covered {initial : CS} {final : CT}
    {targetEvents : List Event}
    (path : LoggedPath CostStack.TargetStep targetEmit
      (CostStack.embed initial) targetEvents final) :
    ∃ sourceEvents sourceFinal,
      LoggedPath CostStack.SourceStep sourceEmit initial sourceEvents sourceFinal ∧
      Prefix targetEvents (expand sourceEvents) := by
  obtain ⟨sourceEvents, sourceLog, equation⟩ := target_log_decomposition path
  cases phase : final.armed with
  | false =>
      refine ⟨sourceEvents, final.source, sourceLog, ?_⟩
      simp [pendingEvents, phase] at equation
      rw [equation]
      exact Prefix.refl _
  | true =>
      have account := CostStack.target_accounting path.erase
      obtain ⟨next, edge⟩ := account.2 phase
      refine ⟨sourceEvents ++ sourceEmit final.source next, next,
        LoggedPath.tail sourceLog edge, ?_⟩
      simp [pendingEvents, phase] at equation
      rw [equation, expand_append]
      exact prefix_append_left (expand sourceEvents) (pending_cost_prefix _ _)

/-- Forward operational coverage after applying event-level prefix policies. -/
theorem adapter_image_covered :
    TraceCoverage (AdapterImage (PrefixClosure sourceRuns) expansionAdapter)
      (PrefixClosure targetRuns) := by
  intro input targetTrace admitted
  obtain ⟨sourceTrace, ⟨sourceWhole, ⟨sourceFinal, sourceLog⟩, sourcePrefix⟩,
    adapted⟩ := admitted
  refine ⟨expand sourceWhole,
    ⟨CostStack.embed sourceFinal, compile_logged_path sourceLog⟩, ?_⟩
  exact prefix_trans adapted (expand_preserves_prefix sourcePrefix)

/-- Reverse operational coverage includes target configurations in the middle
of the expansion and event prefixes inside an atomic cost/outcome emission. -/
theorem target_prefixes_covered :
    TraceCoverage (PrefixClosure targetRuns)
      (AdapterImage (PrefixClosure sourceRuns) expansionAdapter) := by
  intro input targetTrace admitted
  obtain ⟨targetWhole, ⟨targetFinal, targetLog⟩, targetPrefix⟩ := admitted
  obtain ⟨sourceEvents, sourceFinal, sourceLog, covered⟩ :=
    target_logged_prefix_covered targetLog
  refine ⟨sourceEvents,
    ⟨sourceEvents, ⟨sourceFinal, sourceLog⟩, Prefix.refl _⟩, ?_⟩
  exact prefix_trans targetPrefix covered

/-- Exact image equality binds the previously declared adapter to the actual
operational source and target run sets, under explicit event-prefix closure. -/
theorem operational_adapter_exact_image :
    TraceSetEquivalent (AdapterImage (PrefixClosure sourceRuns) expansionAdapter)
      (PrefixClosure targetRuns) :=
  equivalence_of_bidirectional_coverage adapter_image_covered target_prefixes_covered

theorem source_prefix_noninterference :
    FiniteNoninterference PublicRelated (PrefixClosure sourceRuns) := by
  intro left right related events
  constructor
  · rintro ⟨whole, admitted, pre⟩
    exact ⟨whole, (source_operational_noninterference left right related whole).mp admitted, pre⟩
  · rintro ⟨whole, admitted, pre⟩
    exact ⟨whole, (source_operational_noninterference left right related whole).mpr admitted, pre⟩

/-- Application of the adapter theorem now uses operational exact-image
coverage rather than an independently declared target trace set. The secret
remains unused by the deliberately narrow positive operational family. -/
theorem target_prefix_noninterference_via_adapter :
    FiniteNoninterference PublicRelated (PrefixClosure targetRuns) :=
  target_noninterference_of_adapter_image source_prefix_noninterference
    expansion_adapter_public_uniform operational_adapter_exact_image

#print axioms prefix_append_left
#print axioms expand_append
#print axioms expand_core_emission
#print axioms logged_trans
#print axioms compile_logged_edge
#print axioms compile_logged_path
#print axioms target_log_decomposition
#print axioms pending_cost_prefix
#print axioms target_logged_prefix_covered
#print axioms adapter_image_covered
#print axioms target_prefixes_covered
#print axioms operational_adapter_exact_image
#print axioms source_prefix_noninterference
#print axioms target_prefix_noninterference_via_adapter

end AnnealResearch.OperationalAdapter
