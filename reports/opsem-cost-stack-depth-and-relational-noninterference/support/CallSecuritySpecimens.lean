import AnnealResearch.Observations
import AnnealResearch.Execution

/-!
Two owned finite-state, two-call specimens. This is not a Rust/ISA semantics,
probabilistic experiment, UB-safety result or arbitrary-context security claim.

Step is declared independently of observations/security. Each actual step emits
one tagged event. The two subjects share their straight-line administration;
the retained and fresh second-address constructors differ explicitly. The
first bit remains stored through the final return. All run sets below use
actual Execution.Reach, not prefixes selected from completed words.
-/

namespace AnnealResearch.CallSecuritySpecimens

inductive Mode where
  | retained
  | fresh
  deriving DecidableEq, Repr

inductive Call where
  | first
  | second
  deriving DecidableEq, Repr

structure Visible where
  call : Call
  event : Observations.Event
  deriving DecidableEq, Repr

abbrev Trace := List Visible

def bitLocation (bit : Bool) : Nat := if bit then 1 else 0

def address (call : Call) (bit : Bool) : Visible :=
  ⟨call, .address (bitLocation bit)⟩

def charge (call : Call) : Visible := ⟨call, .cost 1⟩

def returned (call : Call) : Visible := ⟨call, .outcome (.returned 0)⟩

/-- Boolean xor, presented by its two ordinary Boolean cases. -/
def xorBit (bit secret : Bool) : Bool := if secret then !bit else bit

theorem xorBit_cancel (bit secret : Bool) :
    xorBit (xorBit bit secret) secret = bit := by
  cases bit <;> cases secret <;> rfl

inductive Phase where
  | firstAddress
  | firstCost
  | firstReturn
  | secondAddress
  | secondCost
  | secondReturn
  | finished
  deriving DecidableEq, Repr

structure Config where
  secret : Bool
  phase : Phase
  retainedBit : Option Bool
  history : Trace
  deriving DecidableEq, Repr

def root (secret : Bool) : Config := ⟨secret, .firstAddress, none, []⟩

/-- No observation equality or future-completion predicate guards Step. -/
inductive Step : Mode → Config → Config → Prop where
  | address1 (mode : Mode) (secret bit : Bool) (history : Trace) :
      Step mode ⟨secret, .firstAddress, none, history⟩
        ⟨secret, .firstCost, some bit, history ++ [address .first bit]⟩
  | cost1 (mode : Mode) (secret bit : Bool) (history : Trace) :
      Step mode ⟨secret, .firstCost, some bit, history⟩
        ⟨secret, .firstReturn, some bit, history ++ [charge .first]⟩
  | return1 (mode : Mode) (secret bit : Bool) (history : Trace) :
      Step mode ⟨secret, .firstReturn, some bit, history⟩
        ⟨secret, .secondAddress, some bit, history ++ [returned .first]⟩
  | address2Retained (secret bit : Bool) (history : Trace) :
      Step .retained ⟨secret, .secondAddress, some bit, history⟩
        ⟨secret, .secondCost, some bit,
          history ++ [address .second (xorBit bit secret)]⟩
  | address2Fresh (secret bit choice : Bool) (history : Trace) :
      Step .fresh ⟨secret, .secondAddress, some bit, history⟩
        ⟨secret, .secondCost, some bit,
          history ++ [address .second (xorBit choice secret)]⟩
  | cost2 (mode : Mode) (secret bit : Bool) (history : Trace) :
      Step mode ⟨secret, .secondCost, some bit, history⟩
        ⟨secret, .secondReturn, some bit, history ++ [charge .second]⟩
  | return2 (mode : Mode) (secret bit : Bool) (history : Trace) :
      Step mode ⟨secret, .secondReturn, some bit, history⟩
        ⟨secret, .finished, some bit, history ++ [returned .second]⟩

def observe (config : Config) : Trace := config.history

def project (which : Call) (trace : Trace) : Trace :=
  trace.filter (fun item => decide (item.call = which))

def Runs (mode : Mode) : Observations.TraceSet Bool Visible :=
  fun secret trace => ∃ reached,
    Execution.Reach (Step mode) (root secret) reached ∧ observe reached = trace

/-- A marginal existentially projects the same whole-program root executions.
It is not a contract at every fixed intermediate state. -/
def CallRuns (mode : Mode) (which : Call) : Observations.TraceSet Bool Visible :=
  fun secret localTrace => ∃ whole,
    Runs mode secret whole ∧ project which whole = localTrace

def PublicRelated (_left _right : Bool) : Prop := True

/-- Independent normal-completion observation, including the actual phase. -/
def Completed (mode : Mode) (secret : Bool) (trace : Trace) : Prop :=
  ∃ reached, Execution.Reach (Step mode) (root secret) reached ∧
    reached.phase = .finished ∧ observe reached = trace

def logicalCost (trace : Trace) : Nat :=
  Observations.traceCost (trace.map (fun item => item.event))

def returnedValues : Trace → List Nat
  | [] => []
  | item :: rest =>
      match item.event with
      | .outcome (.returned value) => value :: returnedValues rest
      | _ => returnedValues rest

/- Normal forms are proof aids declared after the actual execution/observers. -/
def firstTrace (bit : Bool) : Trace :=
  [address .first bit, charge .first, returned .first]

def completeTrace (firstBit secondBit : Bool) : Trace :=
  firstTrace firstBit ++
    [address .second secondBit, charge .second, returned .second]

def afterAddress1 (secret bit : Bool) : Config :=
  ⟨secret, .firstCost, some bit, [address .first bit]⟩

def afterCost1 (secret bit : Bool) : Config :=
  ⟨secret, .firstReturn, some bit, [address .first bit, charge .first]⟩

/-- The actual first return is the between-call entry, with the first bit kept. -/
def between (secret bit : Bool) : Config :=
  ⟨secret, .secondAddress, some bit, firstTrace bit⟩

def afterAddress2 (secret firstBit secondBit : Bool) : Config :=
  ⟨secret, .secondCost, some firstBit,
    firstTrace firstBit ++ [address .second secondBit]⟩

def afterCost2 (secret firstBit secondBit : Bool) : Config :=
  ⟨secret, .secondReturn, some firstBit,
    firstTrace firstBit ++ [address .second secondBit, charge .second]⟩

def completed (secret firstBit secondBit : Bool) : Config :=
  ⟨secret, .finished, some firstBit, completeTrace firstBit secondBit⟩

/-- This describes root-derived forms; it is not a guard in Step. -/
def SecondAllowed (mode : Mode) (secret firstBit secondBit : Bool) : Prop :=
  match mode with
  | .retained => secondBit = xorBit firstBit secret
  | .fresh => True

inductive Shape (mode : Mode) (secret : Bool) : Config → Prop where
  | initial : Shape mode secret (root secret)
  | firstAddress (bit : Bool) : Shape mode secret (afterAddress1 secret bit)
  | firstCost (bit : Bool) : Shape mode secret (afterCost1 secret bit)
  | firstReturned (bit : Bool) : Shape mode secret (between secret bit)
  | secondAddress (firstBit secondBit : Bool)
      (allowed : SecondAllowed mode secret firstBit secondBit) :
      Shape mode secret (afterAddress2 secret firstBit secondBit)
  | secondCost (firstBit secondBit : Bool)
      (allowed : SecondAllowed mode secret firstBit secondBit) :
      Shape mode secret (afterCost2 secret firstBit secondBit)
  | secondReturned (firstBit secondBit : Bool)
      (allowed : SecondAllowed mode secret firstBit secondBit) :
      Shape mode secret (completed secret firstBit secondBit)

theorem step_preserves_secret_emits_one {mode : Mode} {before after : Config}
    (edge : Step mode before after) :
    after.secret = before.secret ∧
      ∃ event, after.history = before.history ++ [event] := by
  cases edge <;> exact ⟨rfl, _, rfl⟩

theorem shape_step {mode : Mode} {secret : Bool} {before after : Config}
    (shape : Shape mode secret before) (edge : Step mode before after) :
    Shape mode secret after := by
  cases shape with
  | initial =>
      cases edge
      exact Shape.firstAddress _
  | firstAddress bit =>
      cases edge
      exact Shape.firstCost bit
  | firstCost bit =>
      cases edge
      exact Shape.firstReturned bit
  | firstReturned bit =>
      cases edge with
      | address2Retained => exact Shape.secondAddress bit _ rfl
      | address2Fresh => exact Shape.secondAddress bit _ True.intro
  | secondAddress firstBit secondBit allowed =>
      cases edge
      exact Shape.secondCost firstBit secondBit allowed
  | secondCost firstBit secondBit allowed =>
      cases edge
      exact Shape.secondReturned firstBit secondBit allowed
  | secondReturned firstBit secondBit allowed => cases edge

theorem reachable_shape {mode : Mode} {secret : Bool} {reached : Config}
    (path : Execution.Reach (Step mode) (root secret) reached) :
    Shape mode secret reached := by
  apply Execution.invariant_reachable (Invariant := Shape mode secret) Shape.initial ?_ path
  intro before after shape edge
  exact shape_step shape edge

theorem reachable_phase_bit {mode : Mode} {secret : Bool} {reached : Config}
    (path : Execution.Reach (Step mode) (root secret) reached) :
    reached.secret = secret ∧
      ((reached.phase = .firstAddress ∧ reached.retainedBit = none ∧
          reached.history = []) ∨ ∃ bit, reached.retainedBit = some bit) := by
  have shape := reachable_shape path
  constructor
  · cases shape <;> rfl
  · cases shape with
    | initial => exact Or.inl ⟨rfl, rfl, rfl⟩
    | firstAddress bit => exact Or.inr ⟨bit, rfl⟩
    | firstCost bit => exact Or.inr ⟨bit, rfl⟩
    | firstReturned bit => exact Or.inr ⟨bit, rfl⟩
    | secondAddress firstBit secondBit allowed => exact Or.inr ⟨firstBit, rfl⟩
    | secondCost firstBit secondBit allowed => exact Or.inr ⟨firstBit, rfl⟩
    | secondReturned firstBit secondBit allowed => exact Or.inr ⟨firstBit, rfl⟩

theorem finished_no_successor {mode : Mode} {config : Config}
    (finished : config.phase = .finished) :
    ¬ ∃ successor, Step mode config successor := by
  rintro ⟨successor, edge⟩
  cases edge <;> cases finished

/- Actual paths: no default poststate/success extraction. -/
theorem address1_reachable (mode : Mode) (secret bit : Bool) :
    Execution.Reach (Step mode) (root secret) (afterAddress1 secret bit) :=
  Execution.Reach.tail (Execution.Reach.refl _) (Step.address1 mode secret bit [])

theorem cost1_reachable (mode : Mode) (secret bit : Bool) :
    Execution.Reach (Step mode) (root secret) (afterCost1 secret bit) :=
  Execution.Reach.tail (address1_reachable mode secret bit)
    (Step.cost1 mode secret bit [address .first bit])

theorem between_reachable (mode : Mode) (secret bit : Bool) :
    Execution.Reach (Step mode) (root secret) (between secret bit) :=
  Execution.Reach.tail (cost1_reachable mode secret bit)
    (Step.return1 mode secret bit [address .first bit, charge .first])

theorem second_address_edge (mode : Mode) (secret firstBit secondBit : Bool)
    (allowed : SecondAllowed mode secret firstBit secondBit) :
    Step mode (between secret firstBit)
      (afterAddress2 secret firstBit secondBit) := by
  cases mode with
  | retained =>
      change secondBit = xorBit firstBit secret at allowed
      subst secondBit
      exact Step.address2Retained secret firstBit (firstTrace firstBit)
  | fresh =>
      simpa only [between, afterAddress2, xorBit_cancel] using
        (Step.address2Fresh secret firstBit (xorBit secondBit secret)
          (firstTrace firstBit))

theorem address2_reachable (mode : Mode) (secret firstBit secondBit : Bool)
    (allowed : SecondAllowed mode secret firstBit secondBit) :
    Execution.Reach (Step mode) (root secret)
      (afterAddress2 secret firstBit secondBit) :=
  Execution.Reach.tail (between_reachable mode secret firstBit)
    (second_address_edge mode secret firstBit secondBit allowed)

theorem cost2_reachable (mode : Mode) (secret firstBit secondBit : Bool)
    (allowed : SecondAllowed mode secret firstBit secondBit) :
    Execution.Reach (Step mode) (root secret)
      (afterCost2 secret firstBit secondBit) :=
  Execution.Reach.tail (address2_reachable mode secret firstBit secondBit allowed)
    (Step.cost2 mode secret firstBit
      (firstTrace firstBit ++ [address .second secondBit]))

theorem completed_reachable (mode : Mode) (secret firstBit secondBit : Bool)
    (allowed : SecondAllowed mode secret firstBit secondBit) :
    Execution.Reach (Step mode) (root secret)
      (completed secret firstBit secondBit) :=
  Execution.Reach.tail (cost2_reachable mode secret firstBit secondBit allowed)
    (Step.return2 mode secret firstBit
      (firstTrace firstBit ++ [address .second secondBit, charge .second]))

/-- Each separate Boolean choice really supplies a path; no distribution or
common-random-choice security law is asserted. -/
theorem actual_normal_completions (secret firstBit secondChoice : Bool) :
    Execution.Reach (Step .retained) (root secret)
      (completed secret firstBit (xorBit firstBit secret)) ∧
    Execution.Reach (Step .fresh) (root secret)
      (completed secret firstBit (xorBit secondChoice secret)) :=
  ⟨completed_reachable .retained secret firstBit _ rfl,
    completed_reachable .fresh secret firstBit _ True.intro⟩

theorem finished_shape {mode : Mode} {secret : Bool} {config : Config}
    (path : Execution.Reach (Step mode) (root secret) config)
    (finished : config.phase = .finished) :
    ∃ firstBit secondBit, SecondAllowed mode secret firstBit secondBit ∧
      config = completed secret firstBit secondBit := by
  cases reachable_shape path with
  | initial => cases finished
  | firstAddress bit => cases finished
  | firstCost bit => cases finished
  | firstReturned bit => cases finished
  | secondAddress firstBit secondBit allowed => cases finished
  | secondCost firstBit secondBit allowed => cases finished
  | secondReturned firstBit secondBit allowed =>
      exact ⟨firstBit, secondBit, allowed, rfl⟩

theorem completed_trace_iff (mode : Mode) (secret : Bool) (trace : Trace) :
    Completed mode secret trace ↔
      ∃ firstBit secondBit, SecondAllowed mode secret firstBit secondBit ∧
        trace = completeTrace firstBit secondBit := by
  constructor
  · rintro ⟨config, path, finished, observed⟩
    rcases finished_shape path finished with ⟨firstBit, secondBit, allowed, rfl⟩
    exact ⟨firstBit, secondBit, allowed, observed.symm⟩
  · rintro ⟨firstBit, secondBit, allowed, rfl⟩
    exact ⟨completed secret firstBit secondBit,
      completed_reachable mode secret firstBit secondBit allowed, rfl, rfl⟩

theorem retained_complete_catalogue (secret : Bool) (trace : Trace) :
    Completed .retained secret trace ↔
      trace = completeTrace false (xorBit false secret) ∨
      trace = completeTrace true (xorBit true secret) := by
  rw [completed_trace_iff]
  constructor
  · rintro ⟨firstBit, secondBit, allowed, observed⟩
    change secondBit = xorBit firstBit secret at allowed
    subst secondBit
    cases firstBit with
    | false => exact Or.inl observed
    | true => exact Or.inr observed
  · rintro (observed | observed)
    · exact ⟨false, xorBit false secret, rfl, observed⟩
    · exact ⟨true, xorBit true secret, rfl, observed⟩

theorem fresh_complete_catalogue (secret : Bool) (trace : Trace) :
    Completed .fresh secret trace ↔
      ∃ firstBit secondBit, trace = completeTrace firstBit secondBit := by
  rw [completed_trace_iff]
  constructor
  · rintro ⟨firstBit, secondBit, allowed, observed⟩
    exact ⟨firstBit, secondBit, observed⟩
  · rintro ⟨firstBit, secondBit, observed⟩
    exact ⟨firstBit, secondBit, True.intro, observed⟩

theorem completed_return_cost (mode : Mode) (secret : Bool) (trace : Trace)
    (complete : Completed mode secret trace) :
    returnedValues trace = [0, 0] ∧ logicalCost trace = 2 := by
  rcases (completed_trace_iff mode secret trace).mp complete with
    ⟨firstBit, secondBit, allowed, rfl⟩
  exact ⟨rfl, rfl⟩

/-- Marginal matching may choose a different whole root execution. In particular
second-call matching may change the actual first bit; this is the weak premise. -/
theorem retained_marginal_matching (which : Call) (targetSecret : Bool)
    {sourceSecret : Bool} {source : Config}
    (path : Execution.Reach (Step .retained) (root sourceSecret) source) :
    ∃ target, Execution.Reach (Step .retained) (root targetSecret) target ∧
      project which (observe target) = project which (observe source) := by
  have shape := reachable_shape path
  cases which with
  | first =>
      cases shape with
      | initial => exact ⟨root targetSecret, Execution.Reach.refl _, rfl⟩
      | firstAddress bit =>
          exact ⟨afterAddress1 targetSecret bit,
            address1_reachable .retained targetSecret bit, rfl⟩
      | firstCost bit =>
          exact ⟨afterCost1 targetSecret bit,
            cost1_reachable .retained targetSecret bit, rfl⟩
      | firstReturned bit =>
          exact ⟨between targetSecret bit,
            between_reachable .retained targetSecret bit, rfl⟩
      | secondAddress firstBit secondBit allowed =>
          exact ⟨between targetSecret firstBit,
            between_reachable .retained targetSecret firstBit, rfl⟩
      | secondCost firstBit secondBit allowed =>
          exact ⟨between targetSecret firstBit,
            between_reachable .retained targetSecret firstBit, rfl⟩
      | secondReturned firstBit secondBit allowed =>
          exact ⟨between targetSecret firstBit,
            between_reachable .retained targetSecret firstBit, rfl⟩
  | second =>
      cases shape with
      | initial => exact ⟨root targetSecret, Execution.Reach.refl _, rfl⟩
      | firstAddress bit => exact ⟨root targetSecret, Execution.Reach.refl _, rfl⟩
      | firstCost bit => exact ⟨root targetSecret, Execution.Reach.refl _, rfl⟩
      | firstReturned bit => exact ⟨root targetSecret, Execution.Reach.refl _, rfl⟩
      | secondAddress firstBit secondBit allowed =>
          exact ⟨afterAddress2 targetSecret (xorBit secondBit targetSecret) secondBit,
            address2_reachable .retained targetSecret _ secondBit
              (xorBit_cancel secondBit targetSecret).symm, rfl⟩
      | secondCost firstBit secondBit allowed =>
          exact ⟨afterCost2 targetSecret (xorBit secondBit targetSecret) secondBit,
            cost2_reachable .retained targetSecret _ secondBit
              (xorBit_cancel secondBit targetSecret).symm, rfl⟩
      | secondReturned firstBit secondBit allowed =>
          exact ⟨completed targetSecret (xorBit secondBit targetSecret) secondBit,
            completed_reachable .retained targetSecret _ secondBit
              (xorBit_cancel secondBit targetSecret).symm, rfl⟩

theorem retained_marginal_coverage (which : Call) (left right : Bool)
    (trace : Trace) (observed : CallRuns .retained which left trace) :
    CallRuns .retained which right trace := by
  rcases observed with ⟨whole, ⟨source, path, wholeObserved⟩, localObserved⟩
  rcases retained_marginal_matching which right path with
    ⟨target, targetPath, sameLocal⟩
  refine ⟨observe target, ⟨target, targetPath, rfl⟩, ?_⟩
  exact sameLocal.trans ((congrArg (project which) wholeObserved).trans localObserved)

theorem retained_marginals_noninterference (which : Call) :
    Observations.FiniteNoninterference PublicRelated (CallRuns .retained which) := by
  intro left right related trace
  exact ⟨retained_marginal_coverage which left right trace,
    retained_marginal_coverage which right left trace⟩

def distinguishing : Trace :=
  [address .first false, charge .first, returned .first, address .second false]

theorem retained_true_excludes_distinguishing :
    ¬ Runs .retained true distinguishing := by
  rintro ⟨source, path, observed⟩
  cases reachable_shape path with
  | initial => simp [observe, root, distinguishing] at observed
  | firstAddress bit => simp [observe, afterAddress1, distinguishing] at observed
  | firstCost bit => simp [observe, afterCost1, distinguishing] at observed
  | firstReturned bit => simp [observe, between, firstTrace, distinguishing] at observed
  | secondAddress firstBit secondBit allowed =>
      change secondBit = xorBit firstBit true at allowed
      subst secondBit
      cases firstBit <;>
        simp [observe, afterAddress2, firstTrace, distinguishing, address,
          bitLocation, xorBit] at observed
  | secondCost firstBit secondBit allowed =>
      simp [observe, afterCost2, firstTrace, distinguishing] at observed
  | secondReturned firstBit secondBit allowed =>
      simp [observe, completed, completeTrace, firstTrace, distinguishing] at observed

theorem retained_distinguishing_prefix :
    Runs .retained false distinguishing ∧
      ¬ Runs .retained true distinguishing :=
  ⟨⟨afterAddress2 false false false,
      address2_reachable .retained false false false rfl, rfl⟩,
    retained_true_excludes_distinguishing⟩

theorem retained_not_noninterference :
    ¬ Observations.FiniteNoninterference PublicRelated (Runs .retained) := by
  intro secure
  exact retained_distinguishing_prefix.2
    ((secure false true True.intro distinguishing).mp
      retained_distinguishing_prefix.1)

/-- Full fresh matching preserves every actual event prefix, including within
calls. Its second choice is existentially matched, not fixed to a common seed. -/
theorem fresh_prefix_matching (targetSecret : Bool)
    {sourceSecret : Bool} {source : Config}
    (path : Execution.Reach (Step .fresh) (root sourceSecret) source) :
    ∃ target, Execution.Reach (Step .fresh) (root targetSecret) target ∧
      observe target = observe source := by
  cases reachable_shape path with
  | initial => exact ⟨root targetSecret, Execution.Reach.refl _, rfl⟩
  | firstAddress bit =>
      exact ⟨afterAddress1 targetSecret bit,
        address1_reachable .fresh targetSecret bit, rfl⟩
  | firstCost bit =>
      exact ⟨afterCost1 targetSecret bit,
        cost1_reachable .fresh targetSecret bit, rfl⟩
  | firstReturned bit =>
      exact ⟨between targetSecret bit,
        between_reachable .fresh targetSecret bit, rfl⟩
  | secondAddress firstBit secondBit allowed =>
      exact ⟨afterAddress2 targetSecret firstBit secondBit,
        address2_reachable .fresh targetSecret firstBit secondBit True.intro, rfl⟩
  | secondCost firstBit secondBit allowed =>
      exact ⟨afterCost2 targetSecret firstBit secondBit,
        cost2_reachable .fresh targetSecret firstBit secondBit True.intro, rfl⟩
  | secondReturned firstBit secondBit allowed =>
      exact ⟨completed targetSecret firstBit secondBit,
        completed_reachable .fresh targetSecret firstBit secondBit True.intro, rfl⟩

theorem fresh_trace_coverage (left right : Bool) (trace : Trace)
    (observed : Runs .fresh left trace) : Runs .fresh right trace := by
  rcases observed with ⟨source, path, observed⟩
  rcases fresh_prefix_matching right path with ⟨target, targetPath, sameTrace⟩
  exact ⟨target, targetPath, sameTrace.trans observed⟩

theorem fresh_all_microevent_prefixes_noninterference :
    Observations.FiniteNoninterference PublicRelated (Runs .fresh) := by
  intro left right related trace
  exact ⟨fresh_trace_coverage left right trace,
    fresh_trace_coverage right left trace⟩

/- Substantive source-ordered audits. Helper calls/operational steps are not
separately counted as new security endpoints. No generic composition theorem
or probability/termination/source-adequacy result is claimed here. -/
#print axioms step_preserves_secret_emits_one
#print axioms reachable_shape
#print axioms reachable_phase_bit
#print axioms finished_no_successor
#print axioms actual_normal_completions
#print axioms completed_trace_iff
#print axioms retained_complete_catalogue
#print axioms fresh_complete_catalogue
#print axioms completed_return_cost
#print axioms retained_marginal_matching
#print axioms retained_marginals_noninterference
#print axioms retained_distinguishing_prefix
#print axioms retained_not_noninterference
#print axioms fresh_prefix_matching
#print axioms fresh_all_microevent_prefixes_noninterference

end AnnealResearch.CallSecuritySpecimens
