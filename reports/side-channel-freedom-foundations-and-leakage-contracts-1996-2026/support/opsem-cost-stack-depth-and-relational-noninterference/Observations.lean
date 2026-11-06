import Std

/-!
Bounded relational-observation research. These are owned mathematical models,
not Rust, an ISA, a compiler, or an authoritative constant-time policy.

The generic property below is finite-trace-set (possibilistic) noninterference:
related inputs admit the same set of finite visible observations. It does not
require all pairs of nondeterministic runs to have identical observations.
Choice resolution and any prophecy interpretation must already be justified
when supplying a trace set. The weighted example is separately identified.

Outcomes are visible events. The concrete examples supply every finite prefix
of finite complete traces. The generic theorem compares every supplied finite
trace, but neither constructs infinite runs nor proves termination, fairness,
probabilistic security, or equality of infinite observations. It also supplies
no UB-safety theorem: that remains a separate obligation for any instantiation.
-/

namespace AnnealResearch.Observations

universe u v

/-- A run set after applying the chosen observation projection. -/
abbrev TraceSet (Input : Type u) (Visible : Type v) :=
  Input → List Visible → Prop

def FiniteNoninterference {Input : Type u} {Visible : Type v}
    (Related : Input → Input → Prop) (runs : TraceSet Input Visible) : Prop :=
  ∀ left right, Related left right →
    ∀ trace, runs left trace ↔ runs right trace

/-- Every observation of the first subject has a matching observation of the
second subject at the same input. This is existential matching within a run set. -/
def TraceCoverage {Input : Type u} {Visible : Type v}
    (first second : TraceSet Input Visible) : Prop :=
  ∀ input trace, first input trace → second input trace

def TraceSetEquivalent {Input : Type u} {Visible : Type v}
    (first second : TraceSet Input Visible) : Prop :=
  ∀ input trace, first input trace ↔ second input trace

theorem equivalence_of_bidirectional_coverage
    {Input : Type u} {Visible : Type v}
    {source target : TraceSet Input Visible}
    (forward : TraceCoverage source target)
    (backward : TraceCoverage target source) :
    TraceSetEquivalent source target := by
  intro input trace
  exact ⟨forward input trace, backward input trace⟩

/-- A sufficient preservation theorem. Both coverage directions concern the
same observation alphabet, input domain, outcome policy, and justified choices. -/
theorem finite_noninterference_of_trace_equivalence
    {Input : Type u} {Visible : Type v}
    {Related : Input → Input → Prop}
    {source target : TraceSet Input Visible}
    (equivalent : TraceSetEquivalent source target)
    (sourceNI : FiniteNoninterference Related source) :
    FiniteNoninterference Related target := by
  intro left right related trace
  constructor
  · intro observed
    exact (equivalent right trace).mp
      ((sourceNI left right related trace).mp
        ((equivalent left trace).mpr observed))
  · intro observed
    exact (equivalent left trace).mp
      ((sourceNI left right related trace).mpr
        ((equivalent right trace).mpr observed))

theorem finite_noninterference_of_bidirectional_coverage
    {Input : Type u} {Visible : Type v}
    {Related : Input → Input → Prop}
    {source target : TraceSet Input Visible}
    (forward : TraceCoverage source target)
    (backward : TraceCoverage target source)
    (sourceNI : FiniteNoninterference Related source) :
    FiniteNoninterference Related target :=
  finite_noninterference_of_trace_equivalence
    (equivalence_of_bidirectional_coverage forward backward) sourceNI

/-- An explicit prefix relation avoids assigning acceptance to only completed
outputs. A prefix can expose a branch or address before any outcome appears. -/
inductive Prefix {Visible : Type v} : List Visible → List Visible → Prop where
  | nil {whole} : Prefix [] whole
  | cons {event pre whole} : Prefix pre whole →
      Prefix (event :: pre) (event :: whole)

theorem Prefix.refl {Visible : Type v} (trace : List Visible) :
    Prefix trace trace := by
  induction trace with
  | nil => exact Prefix.nil
  | cons event rest ih => exact Prefix.cons ih

theorem Prefix.head_eq {Visible : Type v} {a b : Visible}
    {restA restB : List Visible} (pre : Prefix (a :: restA) (b :: restB)) : a = b := by
  cases pre
  rfl

def PrefixClosure {Input : Type u} {Visible : Type v}
    (runs : TraceSet Input Visible) : TraceSet Input Visible :=
  fun input trace => ∃ complete, runs input complete ∧ Prefix trace complete

theorem prefix_closure_equivalent
    {Input : Type u} {Visible : Type v}
    {source target : TraceSet Input Visible}
    (equivalent : TraceSetEquivalent source target) :
    TraceSetEquivalent (PrefixClosure source) (PrefixClosure target) := by
  intro input trace
  constructor
  · rintro ⟨complete, admitted, pre⟩
    exact ⟨complete, (equivalent input complete).mp admitted, pre⟩
  · rintro ⟨complete, admitted, pre⟩
    exact ⟨complete, (equivalent input complete).mpr admitted, pre⟩

inductive Outcome where
  | returned (value : Nat)
  | panic
  | abort
  | ub
  | blocked
  deriving DecidableEq, Repr

inductive Event where
  | branch (taken : Bool)
  | address (location : Nat)
  | cost (units : Nat)
  | outcome (result : Outcome)
  deriving DecidableEq, Repr

structure Input where
  publicSize : Nat
  secret : Bool
  deriving DecidableEq, Repr

def PublicRelated (left right : Input) : Prop := left.publicSize = right.publicSize

def leftInput (n : Nat) : Input := ⟨n, false⟩
def rightInput (n : Nat) : Input := ⟨n, true⟩

theorem inputs_related (n : Nat) : PublicRelated (leftInput n) (rightInput n) := rfl

def work : Nat → List Event
  | 0 => []
  | n + 1 => Event.cost 1 :: work n

def traceCost : List Event → Nat
  | [] => 0
  | Event.cost units :: rest => units + traceCost rest
  | _ :: rest => traceCost rest

theorem work_cost (n : Nat) : traceCost (work n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [work, traceCost, ih, Nat.add_comm]

theorem traceCost_append (first second : List Event) :
    traceCost (first ++ second) = traceCost first + traceCost second := by
  induction first with
  | nil => simp [traceCost]
  | cons event rest ih =>
    cases event <;> simp [traceCost, ih, Nat.add_assoc]

/-- A deterministic family for arbitrary public n. Branch, address, every unit
of logical cost, and the returned value are included in the visible trace. -/
def constantTrace (n : Nat) : List Event :=
  [Event.branch false, Event.address 0] ++ work n ++
    [Event.outcome (Outcome.returned 0)]

def constantPrefixes : TraceSet Input Event :=
  fun input trace => Prefix trace (constantTrace input.publicSize)

theorem constant_family_noninterference :
    FiniteNoninterference PublicRelated constantPrefixes := by
  intro left right related trace
  change left.publicSize = right.publicSize at related
  change Prefix trace (constantTrace left.publicSize) ↔
    Prefix trace (constantTrace right.publicSize)
  rw [related]

theorem constant_family_actual_complete (input : Input) :
    constantPrefixes input (constantTrace input.publicSize) := Prefix.refl _

theorem constant_family_cost (n : Nat) : traceCost (constantTrace n) = n := by
  simp [constantTrace, traceCost_append, traceCost, work_cost]

/-- The mutant keeps output and exact total cost while exposing the secret in
both a branch and an address. No ISA timing assertion is being made. -/
def branchAddressTrace (input : Input) : List Event :=
  [Event.branch input.secret, Event.address (if input.secret then 1 else 0)] ++
    work input.publicSize ++ [Event.outcome (Outcome.returned 0)]

def branchAddressPrefixes : TraceSet Input Event :=
  fun input trace => Prefix trace (branchAddressTrace input)

theorem mutant_same_output_and_common_cost_bound (input : Input) :
    (∃ before, constantTrace input.publicSize =
      before ++ [Event.outcome (Outcome.returned 0)]) ∧
    (∃ before, branchAddressTrace input =
      before ++ [Event.outcome (Outcome.returned 0)]) ∧
    traceCost (constantTrace input.publicSize) ≤ input.publicSize ∧
    traceCost (branchAddressTrace input) ≤ input.publicSize := by
  refine ⟨⟨[Event.branch false, Event.address 0] ++ work input.publicSize, ?_⟩,
    ⟨[Event.branch input.secret, Event.address (if input.secret then 1 else 0)] ++
      work input.publicSize, ?_⟩, ?_, ?_⟩
  · simp [constantTrace]
  · simp [branchAddressTrace]
  · simp [constant_family_cost]
  · simp [branchAddressTrace, traceCost_append, traceCost, work_cost]

theorem true_branch_prefix (n : Nat) :
    branchAddressPrefixes (rightInput n) [Event.branch true] :=
  Prefix.cons Prefix.nil

theorem false_branch_excludes_true (n : Nat) :
    ¬ branchAddressPrefixes (leftInput n) [Event.branch true] := by
  intro pre
  have impossible : Event.branch true = Event.branch false := Prefix.head_eq pre
  cases impossible

theorem constant_excludes_true_branch (input : Input) :
    ¬ constantPrefixes input [Event.branch true] := by
  intro pre
  have impossible : Event.branch true = Event.branch false := Prefix.head_eq pre
  cases impossible

theorem branch_address_mutant_not_noninterference :
    ¬ FiniteNoninterference PublicRelated branchAddressPrefixes := by
  intro ni
  exact false_branch_excludes_true 0
    ((ni (leftInput 0) (rightInput 0) (inputs_related 0)
      [Event.branch true]).mpr (true_branch_prefix 0))

/-- Nondeterminism adds a secret-dependent alternative while retaining every
source run. Forward/existential matching therefore does not establish NI. -/
def addsLeak : TraceSet Input Event :=
  fun input trace => constantPrefixes input trace ∨ branchAddressPrefixes input trace

theorem source_covered_by_addsLeak : TraceCoverage constantPrefixes addsLeak := by
  intro input trace observed
  exact Or.inl observed

theorem matching_actual_complete_run (input : Input) :
    ∃ trace, constantPrefixes input trace ∧ addsLeak input trace :=
  ⟨constantTrace input.publicSize, constant_family_actual_complete input,
    Or.inl (constant_family_actual_complete input)⟩

theorem addsLeak_actual_distinguishing_trace :
    addsLeak (rightInput 0) [Event.branch true] ∧
    ¬ addsLeak (leftInput 0) [Event.branch true] := by
  constructor
  · exact Or.inr (true_branch_prefix 0)
  · intro observed
    cases observed with
    | inl source => exact constant_excludes_true_branch _ source
    | inr mutant => exact false_branch_excludes_true 0 mutant

theorem forward_matching_does_not_preserve_noninterference :
    FiniteNoninterference PublicRelated constantPrefixes ∧
    TraceCoverage constantPrefixes addsLeak ∧
    ¬ FiniteNoninterference PublicRelated addsLeak := by
  refine ⟨constant_family_noninterference, source_covered_by_addsLeak, ?_⟩
  intro ni
  exact addsLeak_actual_distinguishing_trace.2
    ((ni (leftInput 0) (rightInput 0) (inputs_related 0)
      [Event.branch true]).mpr addsLeak_actual_distinguishing_trace.1)

/-- A source with both visible choices under either secret is possibilistically
noninterfering, although its arbitrary pairs of runs need not match. -/
def twoChoices : TraceSet Input Event :=
  fun _ trace => Prefix trace [Event.branch false] ∨ Prefix trace [Event.branch true]

def selectsSecret : TraceSet Input Event :=
  fun input trace => Prefix trace [Event.branch input.secret]

theorem twoChoices_noninterference : FiniteNoninterference PublicRelated twoChoices := by
  intro left right related trace
  exact Iff.rfl

theorem selectsSecret_covered_by_twoChoices : TraceCoverage selectsSecret twoChoices := by
  intro input trace observed
  cases input with
  | mk publicSize secret =>
    cases secret with
    | false => exact Or.inl observed
    | true => exact Or.inr observed

theorem selectsSecret_actual_distinguishing_trace :
    selectsSecret (rightInput 0) [Event.branch true] ∧
    ¬ selectsSecret (leftInput 0) [Event.branch true] := by
  constructor
  · exact Prefix.refl _
  · intro pre
    have impossible : Event.branch true = Event.branch false := Prefix.head_eq pre
    cases impossible

/-- Reverse coverage (target trace-set inclusion in source) also is insufficient:
secret-dependent restriction can destroy possibilistic noninterference. -/
theorem trace_refinement_does_not_preserve_noninterference :
    FiniteNoninterference PublicRelated twoChoices ∧
    TraceCoverage selectsSecret twoChoices ∧
    ¬ FiniteNoninterference PublicRelated selectsSecret := by
  refine ⟨twoChoices_noninterference, selectsSecret_covered_by_twoChoices, ?_⟩
  intro ni
  exact selectsSecret_actual_distinguishing_trace.2
    ((ni (leftInput 0) (rightInput 0) (inputs_related 0)
      [Event.branch true]).mpr selectsSecret_actual_distinguishing_trace.1)

/-- Comparing identical sampled bits alone does not justify a distributional
claim if the bit's law can depend on the secret. The trace function below ignores
the input, so every same-bit pair agrees. The finite law does not. -/
def coinTrace (_ : Input) (coin : Bool) : List Event := [Event.branch coin]

def coinWeight (input : Input) (coin : Bool) : Nat :=
  if input.secret = coin then 2 else 0

def eventMass (input : Input) (trace : List Event) : Nat :=
  (if coinTrace input false = trace then coinWeight input false else 0) +
    (if coinTrace input true = trace then coinWeight input true else 0)

theorem same_coin_observations (left right : Input) (coin : Bool) :
    coinTrace left coin = coinTrace right coin := rfl

theorem coin_law_normalized (input : Input) :
    coinWeight input false + coinWeight input true = 2 := by
  cases input with
  | mk publicSize secret => cases secret <;> simp [coinWeight]

theorem same_coin_but_distinguishing_distribution :
    (∀ coin, coinTrace (leftInput 0) coin = coinTrace (rightInput 0) coin) ∧
    eventMass (leftInput 0) [Event.branch true] = 0 ∧
    eventMass (rightInput 0) [Event.branch true] = 2 := by
  constructor
  · intro coin
    exact same_coin_observations _ _ _
  · decide

/- The common total weight is two, so the last masses represent probabilities
zero and one. This is an explicit input-dependent-law counterexample, not a claim
that pointwise equality under a common input-independent law is insufficient.
No probability library, randomized compiler, or general coupling theorem is used.
-/

#print axioms finite_noninterference_of_trace_equivalence
#print axioms finite_noninterference_of_bidirectional_coverage
#print axioms prefix_closure_equivalent
#print axioms constant_family_noninterference
#print axioms constant_family_actual_complete
#print axioms constant_family_cost
#print axioms mutant_same_output_and_common_cost_bound
#print axioms branch_address_mutant_not_noninterference
#print axioms matching_actual_complete_run
#print axioms addsLeak_actual_distinguishing_trace
#print axioms forward_matching_does_not_preserve_noninterference
#print axioms trace_refinement_does_not_preserve_noninterference
#print axioms coin_law_normalized
#print axioms same_coin_but_distinguishing_distribution

end AnnealResearch.Observations
