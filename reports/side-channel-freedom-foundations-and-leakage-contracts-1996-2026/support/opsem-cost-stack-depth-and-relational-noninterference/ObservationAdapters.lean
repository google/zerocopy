import AnnealResearch.Observations

/-!
Finite possibilistic observation adapters. This extends the previous sufficient
criterion from literal source/target trace-set equality to equality with the
relational image of the source under a publicly uniform adapter. An adapter may
expand an observation and admit intermediate prefixes; it need not be a function.

The theorem is conditional on an adequate observation relation and exact image
coverage of actual target observations. The concrete target below is a declared
trace set, not the execution of a compiler or transformed machine. An operational
binding theorem remains necessary before using it for such a transformation.
These are not Rust/ISA, all-pairs observational determinism, infinite-trace,
termination, UB-safety, or general probabilistic-security claims.
-/

namespace AnnealResearch.ObservationAdapters

open Observations

universe u v w

abbrev Adapter (Inputs : Type u) (SourceVisible : Type v) (TargetVisible : Type w) :=
  Inputs → List SourceVisible → List TargetVisible → Prop

def PublicUniform {Inputs : Type u} {SourceVisible : Type v} {TargetVisible : Type w}
    (Related : Inputs → Inputs → Prop)
    (adapter : Adapter Inputs SourceVisible TargetVisible) : Prop :=
  ∀ left right, Related left right → ∀ sourceTrace targetTrace,
    adapter left sourceTrace targetTrace ↔ adapter right sourceTrace targetTrace

def AdapterImage {Inputs : Type u} {SourceVisible : Type v} {TargetVisible : Type w}
    (source : TraceSet Inputs SourceVisible)
    (adapter : Adapter Inputs SourceVisible TargetVisible) :
    TraceSet Inputs TargetVisible :=
  fun input targetTrace => ∃ sourceTrace,
    source input sourceTrace ∧ adapter input sourceTrace targetTrace

/-- Uniform relational images preserve finite trace-set noninterference.
The source run-set quantifier remains existential membership, rather than an
assertion that every possible pair of nondeterministic runs agrees. -/
theorem adapter_image_noninterference
    {Inputs : Type u} {SourceVisible : Type v} {TargetVisible : Type w}
    {Related : Inputs → Inputs → Prop}
    {source : TraceSet Inputs SourceVisible}
    {adapter : Adapter Inputs SourceVisible TargetVisible}
    (sourceNI : FiniteNoninterference Related source)
    (uniform : PublicUniform Related adapter) :
    FiniteNoninterference Related (AdapterImage source adapter) := by
  intro left right related targetTrace
  constructor
  · rintro ⟨sourceTrace, admitted, adapted⟩
    exact ⟨sourceTrace, (sourceNI left right related sourceTrace).mp admitted,
      (uniform left right related sourceTrace targetTrace).mp adapted⟩
  · rintro ⟨sourceTrace, admitted, adapted⟩
    exact ⟨sourceTrace, (sourceNI left right related sourceTrace).mpr admitted,
      (uniform left right related sourceTrace targetTrace).mpr adapted⟩

theorem target_noninterference_of_adapter_image
    {Inputs : Type u} {SourceVisible : Type v} {TargetVisible : Type w}
    {Related : Inputs → Inputs → Prop}
    {source : TraceSet Inputs SourceVisible}
    {target : TraceSet Inputs TargetVisible}
    {adapter : Adapter Inputs SourceVisible TargetVisible}
    (sourceNI : FiniteNoninterference Related source)
    (uniform : PublicUniform Related adapter)
    (exactImage : TraceSetEquivalent (AdapterImage source adapter) target) :
    FiniteNoninterference Related target :=
  finite_noninterference_of_trace_equivalence exactImage
    (adapter_image_noninterference sourceNI uniform)

theorem target_noninterference_of_adapter_coverage
    {Inputs : Type u} {SourceVisible : Type v} {TargetVisible : Type w}
    {Related : Inputs → Inputs → Prop}
    {source : TraceSet Inputs SourceVisible}
    {target : TraceSet Inputs TargetVisible}
    {adapter : Adapter Inputs SourceVisible TargetVisible}
    (sourceNI : FiniteNoninterference Related source)
    (uniform : PublicUniform Related adapter)
    (imageCovered : TraceCoverage (AdapterImage source adapter) target)
    (targetCovered : TraceCoverage target (AdapterImage source adapter)) :
    FiniteNoninterference Related target :=
  target_noninterference_of_adapter_image sourceNI uniform
    (equivalence_of_bidirectional_coverage imageCovered targetCovered)

theorem prefix_trans {Visible : Type v} {first middle last : List Visible}
    (firstPart : Prefix first middle) (secondPart : Prefix middle last) :
    Prefix first last := by
  induction firstPart generalizing last with
  | nil => exact Prefix.nil
  | cons part ih =>
    cases secondPart with
    | cons rest => exact Prefix.cons (ih rest)

theorem prefix_tail {Visible : Type v} {event : Visible} {first last : List Visible}
    (pre : Prefix (event :: first) (event :: last)) : Prefix first last := by
  cases pre with
  | cons part => exact part

/-- Every charged event is duplicated; branch, address, and outcome events are
retained once. This is an observation transformation, not machine execution. -/
def expand : List Event → List Event
  | [] => []
  | Event.cost units :: rest => Event.cost units :: Event.cost units :: expand rest
  | event :: rest => event :: expand rest

theorem expand_preserves_prefix {first last : List Event}
    (pre : Prefix first last) : Prefix (expand first) (expand last) := by
  induction pre with
  | nil => exact Prefix.nil
  | @cons event first last part ih =>
    cases event with
    | cost units => exact Prefix.cons (Prefix.cons ih)
    | branch taken => exact Prefix.cons ih
    | address location => exact Prefix.cons ih
    | outcome result => exact Prefix.cons ih

theorem expanded_cost (trace : List Event) :
    traceCost (expand trace) = 2 * traceCost trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp only [expand, traceCost, ih] <;> omega

/-- The relational adapter includes prefixes ending between the two copies of
a charged event. It is identical for every input, hence for public-related ones. -/
def expansionAdapter : Adapter Input Event Event :=
  fun _ sourceTrace targetTrace => Prefix targetTrace (expand sourceTrace)

theorem expansion_adapter_public_uniform : PublicUniform PublicRelated expansionAdapter := by
  intro left right related sourceTrace targetTrace
  exact Iff.rfl

def expandedPrefixes : TraceSet Input Event :=
  fun input trace => Prefix trace (expand (constantTrace input.publicSize))

theorem expanded_prefix_closed {input : Input} {first last : List Event}
    (admitted : expandedPrefixes input last) (pre : Prefix first last) :
    expandedPrefixes input first := prefix_trans pre admitted

/-- Both directions bind the declared target set to the adapter image.
Taking the full source trace supplies backward coverage, including target
prefixes that stop inside the expansion of the last source cost event. -/
theorem expanded_image_equivalent :
    TraceSetEquivalent (AdapterImage constantPrefixes expansionAdapter) expandedPrefixes := by
  intro input targetTrace
  constructor
  · rintro ⟨sourceTrace, admitted, adapted⟩
    exact prefix_trans adapted (expand_preserves_prefix admitted)
  · intro admitted
    exact ⟨constantTrace input.publicSize, constant_family_actual_complete input, admitted⟩

theorem expanded_family_noninterference :
    FiniteNoninterference PublicRelated expandedPrefixes :=
  target_noninterference_of_adapter_image constant_family_noninterference
    expansion_adapter_public_uniform expanded_image_equivalent

theorem complete_expanded_witness (input : Input) :
    expandedPrefixes input (expand (constantTrace input.publicSize)) ∧
    traceCost (expand (constantTrace input.publicSize)) = 2 * input.publicSize := by
  constructor
  · exact Prefix.refl _
  · rw [expanded_cost, constant_family_cost]

theorem between_duplicate_cost_prefix (n : Nat) :
    expandedPrefixes (leftInput (n + 1))
      [Event.branch false, Event.address 0, Event.cost 1] :=
  Prefix.cons (Prefix.cons (Prefix.cons Prefix.nil))

/-- The complete one-unit source observation is not a target prefix: its return
event appears where the target still has the second charged event. Thus literal
trace-set equality fails even though the public-adapter theorem proves NI. -/
theorem expansion_is_not_literal_trace_equivalence :
    ¬ TraceSetEquivalent constantPrefixes expandedPrefixes := by
  intro equivalent
  have pre := (equivalent (leftInput 1) (constantTrace 1)).mp
    (constant_family_actual_complete (leftInput 1))
  change Prefix
    [Event.branch false, Event.address 0, Event.cost 1, Event.outcome (Outcome.returned 0)]
    [Event.branch false, Event.address 0, Event.cost 1, Event.cost 1,
      Event.outcome (Outcome.returned 0)] at pre
  have impossible : Event.outcome (Outcome.returned 0) = Event.cost 1 :=
    Prefix.head_eq (prefix_tail (prefix_tail (prefix_tail pre)))
  cases impossible

/-- A secret-dependent adapter can leak even from the constant source family.
Ignoring the source trace does not make the adapter publicly uniform. -/
def secretAdapter : Adapter Input Event Event :=
  fun input _ targetTrace => Prefix targetTrace [Event.branch input.secret]

theorem secret_adapter_actual_distinguishing_trace :
    AdapterImage constantPrefixes secretAdapter (rightInput 0) [Event.branch true] ∧
    ¬ AdapterImage constantPrefixes secretAdapter (leftInput 0) [Event.branch true] := by
  constructor
  · exact ⟨[], Prefix.nil, Prefix.refl _⟩
  · rintro ⟨sourceTrace, admitted, adapted⟩
    have impossible : Event.branch true = Event.branch false := Prefix.head_eq adapted
    cases impossible

theorem secret_adapter_not_noninterference :
    ¬ FiniteNoninterference PublicRelated (AdapterImage constantPrefixes secretAdapter) := by
  intro ni
  exact secret_adapter_actual_distinguishing_trace.2
    ((ni (leftInput 0) (rightInput 0) (inputs_related 0)
      [Event.branch true]).mpr secret_adapter_actual_distinguishing_trace.1)

theorem secret_adapter_not_public_uniform : ¬ PublicUniform PublicRelated secretAdapter := by
  intro uniform
  have adapted : secretAdapter (leftInput 0) [] [Event.branch true] :=
    (uniform (leftInput 0) (rightInput 0) (inputs_related 0) []
      [Event.branch true]).mpr (Prefix.refl _)
  have impossible : Event.branch true = Event.branch false := Prefix.head_eq adapted
  cases impossible

#print axioms adapter_image_noninterference
#print axioms target_noninterference_of_adapter_image
#print axioms target_noninterference_of_adapter_coverage
#print axioms expand_preserves_prefix
#print axioms expanded_cost
#print axioms expansion_adapter_public_uniform
#print axioms expanded_prefix_closed
#print axioms expanded_image_equivalent
#print axioms expanded_family_noninterference
#print axioms complete_expanded_witness
#print axioms between_duplicate_cost_prefix
#print axioms expansion_is_not_literal_trace_equivalence
#print axioms secret_adapter_actual_distinguishing_trace
#print axioms secret_adapter_not_noninterference
#print axioms secret_adapter_not_public_uniform

end AnnealResearch.ObservationAdapters
