import Miri.Interpreter.RunLoop

/-!
Finite-prefix safety for the actual scheduler iteration. These definitions are
conditional on the supplied machine operations and permitted choices; they do
not assert that an arbitrary hook implementation covers pinned Miri. In
particular, excluding UB alone does not discharge unsupported operations.
-/
namespace Miri.Interpreter.RunLoop

variable {S C Callback : Type}

/-- A finite execution prefix, retaining every choice as a witness. Only
successful iterations continue; errors are observable outcomes, not steps. -/
inductive Prefix (hooks : RunLoopHooks S C Callback)
    (allowed : S → C → Prop) : S → List C → S → Prop where
  | nil (state) : Prefix hooks allowed state [] state
  | cons {start middle finish choice choices} :
      allowed start choice →
      iteration hooks choice start = (middle, .ok ()) →
      Prefix hooks allowed middle choices finish →
      Prefix hooks allowed start (choice :: choices) finish

/-- All states reached after a permitted finite prefix, including the initial
state. No fuel or termination assumption restricts this relation. -/
def Reachable (hooks : RunLoopHooks S C Callback) (allowed : S → C → Prop)
    (initial : S → Prop) (state : S) : Prop :=
  ∃ start choices, initial start ∧ Prefix hooks allowed start choices state

/-- An error outcome with a complete finite choice witness. -/
def ReachesError (hooks : RunLoopHooks S C Callback) (allowed : S → C → Prop)
    (initial : S → Prop) (error : StepError) : Prop :=
  ∃ before after choice, Reachable hooks allowed initial before ∧
    allowed before choice ∧ iteration hooks choice before = (after, .error error)

/-- Exclude UB on every permitted finite prefix. This is a statement about the
specified operations and choices, not a coverage certificate for Rust. -/
def UBFreedomFrom (hooks : RunLoopHooks S C Callback) (allowed : S → C → Prop)
    (initial : S → Prop) : Prop :=
  ∀ error, ReachesError hooks allowed initial error → reportsUB error = false

/-- Witness of a UB outcome; unlike failed proof search, it establishes a
permitted execution ending in UB. -/
def UBReachable (hooks : RunLoopHooks S C Callback) (allowed : S → C → Prop)
    (initial : S → Prop) : Prop :=
  ∃ error, ReachesError hooks allowed initial error ∧ reportsUB error = true

theorem prefix_preserves (hooks : RunLoopHooks S C Callback)
    (allowed : S → C → Prop) (invariant : S → Prop)
    (preserved : ∀ before after choice, invariant before → allowed before choice →
      iteration hooks choice before = (after, .ok ()) → invariant after)
    {start finish choices} (execution : Prefix hooks allowed start choices finish)
    (atStart : invariant start) : invariant finish := by
  induction execution with
  | nil => exact atStart
  | cons hallowed hstep _ ih =>
    exact ih (preserved _ _ _ atStart hallowed hstep)

/-- Optional invariant proof rule. UB freedom itself is defined directly by
outcomes above, without requiring an invariant or program termination. -/
theorem ubFreedomFrom_of_invariant (hooks : RunLoopHooks S C Callback)
    (allowed : S → C → Prop) (initial invariant : S → Prop)
    (initialized : ∀ state, initial state → invariant state)
    (preserved : ∀ before after choice, invariant before → allowed before choice →
      iteration hooks choice before = (after, .ok ()) → invariant after)
    (excludesUB : ∀ before after choice error, invariant before → allowed before choice →
      iteration hooks choice before = (after, .error error) → reportsUB error = false) :
    UBFreedomFrom hooks allowed initial := by
  intro error herror
  rcases herror with ⟨before, after, choice, ⟨start, choices, hinit, hprefix⟩, hallowed, hstep⟩
  exact excludesUB before after choice error
    (prefix_preserves hooks allowed invariant preserved hprefix (initialized start hinit))
    hallowed hstep

theorem not_ubFreedomFrom_of_ubReachable (hooks : RunLoopHooks S C Callback)
    (allowed : S → C → Prop) (initial : S → Prop)
    (witness : UBReachable hooks allowed initial) :
    ¬ UBFreedomFrom hooks allowed initial := by
  intro safe
  rcases witness with ⟨error, reachable, htrue⟩
  have hfalse := safe error reachable
  simp [htrue] at hfalse

/-- Outcome exclusion and absence of a permitted UB witness are equivalent.
Neither side asserts implementation completeness or resolves unknown errors. -/
theorem ubFreedomFrom_iff_not_ubReachable (hooks : RunLoopHooks S C Callback)
    (allowed : S → C → Prop) (initial : S → Prop) :
    UBFreedomFrom hooks allowed initial ↔ ¬ UBReachable hooks allowed initial := by
  constructor
  · intro safe witness
    exact not_ubFreedomFrom_of_ubReachable hooks allowed initial witness safe
  · intro noWitness error reachable
    cases h : reportsUB error with
    | false => rfl
    | true => exact False.elim (noWitness ⟨error, reachable, h⟩)

end Miri.Interpreter.RunLoop
