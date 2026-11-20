import Init

/-!
# Generic operational safety and partial correctness

This file defines reusable infrastructure for relations that have not yet
been given a concrete language semantics. It is not an interpreter or a model
of Rust or MIR. A future semantics must supply its own states, transition
relation, terminal outcomes, and proofs that its relation is complete.

Terminal outcomes distinguish successful returns from undefined behavior,
blocked proof obligations, and unsupported cases. `Safe` rejects each of the
three non-success outcomes and requires every finitely reachable state to have
an explicit transition or terminal outcome. This lets infinite executions be
safe without treating a missing transition or an unimplemented case as success.
-/

universe u v w x

namespace Miri.OperationalSafety

/-- A terminal result of a semantics supplied by a client. -/
inductive Outcome (Value : Type v) (UB : Type w) (Obligation : Type x) : Type (max v w x) where
  /-- A computation returned a value. -/
  | returned : Value → Outcome Value UB Obligation
  /-- The computation reached an undefined-behavior outcome. -/
  | undefinedBehavior : UB → Outcome Value UB Obligation
  /-- A required semantic or verification obligation remains blocked. -/
  | blocked : Obligation → Outcome Value UB Obligation
  /-- The computation reached a case not supported by the supplied semantics. -/
  | unsupported : Obligation → Outcome Value UB Obligation
  deriving Inhabited

/-- Whether a terminal result is a successful return. -/
def Outcome.isReturn : Outcome Value UB Obligation → Prop
  | .returned _ => True
  | .undefinedBehavior _ | .blocked _ | .unsupported _ => False

/-- A small-step transition system with explicit terminal outcomes. -/
structure System (State : Type u) (Value : Type v) (UB : Type w) (Obligation : Type x) where
  /-- One permitted finite transition. Multiple successors encode nondeterminism. -/
  step : State → State → Prop
  /-- A terminal outcome permitted at a state. -/
  terminal : State → Outcome Value UB Obligation → Prop

namespace System

variable {State : Type u} {Value : Type v} {UB : Type w} {Obligation : Type x}
variable (sys : System State Value UB Obligation)

/-- Finite reachability, including the zero-step path. -/
inductive Reaches : State → State → Prop where
  | refl (state : State) : Reaches state state
  | step {start middle finish : State} :
      Reaches start middle → sys.step middle finish → Reaches start finish

/-- A terminal result reachable after finitely many transitions. -/
def ReachesOutcome (start : State) (outcome : Outcome Value UB Obligation) : Prop :=
  ∃ final, Reaches sys start final ∧ sys.terminal final outcome

/-- A state can make progress when it can step or has an explicit terminal result. -/
def CanProgress (state : State) : Prop :=
  (∃ next, sys.step state next) ∨ (∃ outcome, sys.terminal state outcome)

/-- Progress holds at every state reachable by a finite path from `start`.

This premise rules out unclassified dead ends. Divergent states satisfy it by
having at least one successor, even if no terminal result is ever produced. -/
def CompleteFrom (start : State) : Prop :=
  ∀ state, Reaches sys start state → CanProgress sys state

/-- UB freedom excludes UB outcomes after every permitted finite execution.
This property alone does not certify semantic coverage or resolve unsupported cases. -/
def NoUndefinedBehavior (start : State) : Prop :=
  ∀ reason, ¬ ReachesOutcome sys start (.undefinedBehavior reason)

/-- Safety over all finite paths and all terminal outcomes.

`Safe` requires explicit progress at every reachable state and permits only
successful terminal returns. Because quantification is over every successor
and every terminal outcome, this definition is demonic with respect to
nondeterminism. It does not require termination. -/
def Safe (start : State) : Prop :=
  CompleteFrom sys start ∧
    ∀ outcome, ReachesOutcome sys start outcome → outcome.isReturn

/-- Partial correctness: every reachable successful return satisfies `post`.

This assertion is conditional on return; it does not claim that a return is
reachable. -/
def PartialCorrect (start : State) (post : Value → Prop) : Prop :=
  ∀ value, ReachesOutcome sys start (.returned value) → post value

/-- Every finite reachable state satisfies an invariant preserved by each step. -/
theorem invariant_of_step_preserved {start : State} (invariant : State → Prop)
    (initial : invariant start)
    (preserved : ∀ {before after}, invariant before → sys.step before after → invariant after)
    {state : State} (reachable : Reaches sys start state) : invariant state := by
  induction reachable with
  | refl => exact initial
  | step _ hstep ih => exact preserved ih hstep

/-- A local property of all reachable successful terminal states proves partial correctness. -/
theorem partialCorrect_of_terminal_spec {start : State} (post : Value → Prop)
    (spec : ∀ {final value}, Reaches sys start final → sys.terminal final (.returned value) → post value) :
    PartialCorrect sys start post := by
  intro value outcome
  rcases outcome with ⟨final, reachable, hterminal⟩
  exact spec reachable hterminal

/-- Certified safety implies UB freedom; its progress/coverage requirements
are additional requirements for accepting a Safe result. -/
theorem noUndefinedBehavior_of_safe {start : State} (safe : Safe sys start) :
    NoUndefinedBehavior sys start := by
  intro reason reachable
  exact safe.2 _ reachable

/-- A safe system cannot reach an undefined-behavior outcome. -/
theorem no_reachable_ub {start : State} (safe : Safe sys start) (reason : UB)
    (reachable : ReachesOutcome sys start (.undefinedBehavior reason)) : False := by
  exact safe.2 _ reachable

/-- A safe system cannot reach a blocked obligation. -/
theorem no_reachable_blocked {start : State} (safe : Safe sys start) (goal : Obligation)
    (reachable : ReachesOutcome sys start (.blocked goal)) : False := by
  exact safe.2 _ reachable

/-- A safe system cannot reach an unsupported case. -/
theorem no_reachable_unsupported {start : State} (safe : Safe sys start) (goal : Obligation)
    (reachable : ReachesOutcome sys start (.unsupported goal)) : False := by
  exact safe.2 _ reachable

end System

/-- An infinite run, represented by a state at each natural-number time. -/
def InfiniteRun {State : Type u} {Value : Type v} {UB : Type w} {Obligation : Type x}
    (sys : System State Value UB Obligation) (start : State) : Prop :=
  ∃ run : Nat → State, run 0 = start ∧ ∀ n, sys.step (run n) (run (n + 1))

namespace System

variable {State : Type u} {Value : Type v} {UB : Type w} {Obligation : Type x}
variable (sys : System State Value UB Obligation)

/-- Invariants are an optional proof method for operational safety.
Each permitted transition must preserve the invariant; progress excludes
unclassified dead ends and terminalSuccess excludes unresolved outcomes. -/
theorem safe_of_invariant {start : State} (invariant : State → Prop)
    (initial : invariant start)
    (progress : ∀ {state}, Reaches sys start state → CanProgress sys state)
    (preserved : ∀ {before after}, invariant before → sys.step before after → invariant after)
    (terminalSuccess : ∀ {state outcome}, invariant state → sys.terminal state outcome → outcome.isReturn) :
    Safe sys start := by
  refine ⟨?_, ?_⟩
  · intro state reachable
    exact progress reachable
  · intro outcome houtcome
    rcases houtcome with ⟨final, hreach, hterminal⟩
    exact terminalSuccess (invariant_of_step_preserved sys invariant initial preserved hreach) hterminal

end System

end Miri.OperationalSafety
