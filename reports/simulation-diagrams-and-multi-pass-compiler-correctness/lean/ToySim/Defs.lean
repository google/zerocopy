/-!
# Labelled transition systems, finite-trace behaviours, and refinement

A toy model of the small-step semantics framework used by multi-pass verified
compilers: programs are labelled transition systems with silent steps, and the
observable meaning of a program is the set of its *behaviours*.

Modelling gaps relative to production developments (stated once here, repeated
on the result cards):

* a step carries at most one event (`Option E`), not a list of events;
* behaviours with infinitely many events ("reactive" behaviours) are not
  modelled: only termination, silent divergence after a finite trace, and
  going wrong after a finite trace;
* there is no global environment, memory model, or symbol table.
-/

namespace Toy.Sim

/-- A labelled transition system with silent steps.

`step s none s'` is a silent (internal) step; `step s (some a) s'` emits the
observable event `a`.  `init` selects the initial states and `final s r` says
that `s` is a final state carrying result `r`.

Captures: the small-step semantics of one program in one language of a
compiler pipeline (source, intermediate, or target).  Nothing is assumed
about determinism, and final states are not assumed to be stuck. -/
structure LTS (E Res : Type) where
  /-- The type of program states. -/
  State : Type
  /-- One transition; the label is `none` for a silent step. -/
  step : State → Option E → State → Prop
  /-- Initial states. -/
  init : State → Prop
  /-- `final s r`: `s` is a final state with result `r`. -/
  final : State → Res → Prop

variable {E Res : Type}

/-- The trace contributed by one step label: empty for a silent step, the
single event otherwise. -/
def obs : Option E → List E
  | none => []
  | some a => [a]

@[simp] theorem obs_none : obs (none : Option E) = [] := rfl
@[simp] theorem obs_some (a : E) : obs (some a) = [a] := rfl

/-- `Star L s t s'`: zero or more steps of `L` from `s` to `s'` whose
concatenated trace is `t`.

Captures: a finite partial execution.  The trace equation is an explicit
premise so that case analysis never has to unify against an append. -/
inductive Star (L : LTS E Res) : L.State → List E → L.State → Prop where
  | refl (s : L.State) : Star L s [] s
  | step {s s' s'' : L.State} {e : Option E} {t t' : List E}
      (h : L.step s e s') (hs : Star L s' t s'') (ht : t' = obs e ++ t) :
      Star L s t' s''

/-- `Plus L s t s'`: one or more steps of `L` from `s` to `s'` with trace `t`.

Captures: a finite execution that makes progress. -/
def Plus (L : LTS E Res) (s : L.State) (t : List E) (s'' : L.State) : Prop :=
  ∃ e s' t', L.step s e s' ∧ Star L s' t' s'' ∧ t = obs e ++ t'

/-- `SilentDiv L s`: there is an infinite run of silent steps starting at `s`,
given as a function from step index to state.

Captures: divergence without further observable events. -/
def SilentDiv (L : LTS E Res) (s : L.State) : Prop :=
  ∃ f : Nat → L.State, f 0 = s ∧ ∀ n, L.step (f n) none (f (n + 1))

/-- `Stuck L s`: `s` has no outgoing step and is not final.

Captures: the state where a program "goes wrong" (undefined behaviour). -/
def Stuck (L : LTS E Res) (s : L.State) : Prop :=
  (∀ e s', ¬ L.step s e s') ∧ (∀ r, ¬ L.final s r)

/-- `Safe L s`: every state reachable from `s` by silent steps is final or
can step.

Captures: "`s` does not go wrong before its next observable event"
(silent-prefix safety, as in CompCert's `Smallstep.safe`).  This is the side
condition under which a backward simulation constrains the target.  It is
*not* whole-program safety: a state that emits an event and then gets stuck is
`Safe` (see `Toy.Sim.Examples.safe_pos`).  Whole-program absence of going
wrong is `NeverGoesWrong`. -/
def Safe (L : LTS E Res) (s : L.State) : Prop :=
  ∀ s', Star L s [] s' → (∃ r, L.final s' r) ∨ (∃ e s'', L.step s' e s'')

/-- Observable behaviours of a program, restricted to finite traces.

* `terminates t r`: emits `t`, then stops in a final state with result `r`;
* `diverges t`: emits `t`, then runs silently forever;
* `goesWrong t`: emits `t`, then is stuck in a non-final state.

Not modelled: behaviours that emit infinitely many events. -/
inductive Behavior (E Res : Type) where
  | terminates (t : List E) (r : Res)
  | diverges (t : List E)
  | goesWrong (t : List E)

/-- The finite event trace of a behaviour. -/
def Behavior.trace : Behavior E Res → List E
  | .terminates t _ => t
  | .diverges t => t
  | .goesWrong t => t

/-- `HasBehavior L b`: the program `L` can exhibit behaviour `b`.

A program with *no* initial state is assigned the behaviour `goesWrong []`
(second disjunct of the last clause): a program that cannot even start is
treated as undefined, so that a compiler is unconstrained on it.

Captures: the set of behaviours of a whole program.  A program may have
several behaviours (nondeterminism) and, because behaviours with infinitely
many events are not modelled, may have none (a program whose every run emits
events forever). -/
def HasBehavior (L : LTS E Res) : Behavior E Res → Prop
  | .terminates t r => ∃ s₀ s, L.init s₀ ∧ Star L s₀ t s ∧ L.final s r
  | .diverges t => ∃ s₀ s, L.init s₀ ∧ Star L s₀ t s ∧ SilentDiv L s
  | .goesWrong t =>
      (∃ s₀ s, L.init s₀ ∧ Star L s₀ t s ∧ Stuck L s) ∨ (t = [] ∧ ∀ s, ¬ L.init s)

/-- `Improves b₁ b₂`: the (target) behaviour `b₂` is permitted by the (source)
behaviour `b₁`.  Either they are equal, or `b₁` goes wrong after a trace `t`
and the trace of `b₂` extends `t`.

Captures: undefined-behaviour-aware behaviour refinement at the level of a
single behaviour.  Once the source goes wrong, the target may do anything
that is consistent with the events already emitted. -/
def Improves (b₁ b₂ : Behavior E Res) : Prop :=
  b₁ = b₂ ∨ ∃ t, b₁ = .goesWrong t ∧ t <+: b₂.trace

/-- `RefinedBy src tgt`: every behaviour of `tgt` improves on some behaviour of
`src`.

Captures: end-to-end compiler correctness ("the compiled program only does
what the source program allows, where a source that goes wrong allows
anything consistent with the trace so far") for the behaviours that are
modelled.  Target runs that emit infinitely many events are not behaviours
here and are therefore not constrained by `RefinedBy`. -/
def RefinedBy (src tgt : LTS E Res) : Prop :=
  ∀ b₂, HasBehavior tgt b₂ → ∃ b₁, HasBehavior src b₁ ∧ Improves b₁ b₂

/-- `NeverGoesWrong L`: `L` has no going-wrong behaviour.  In particular `L`
has at least one initial state.

Captures: a whole program free of undefined behaviour along every run
(whole-program safety; compare the much weaker per-state `Safe`).  Runs that
emit infinitely many events are not behaviours here, so they are not
constrained by this property. -/
def NeverGoesWrong (L : LTS E Res) : Prop :=
  ∀ t, ¬ HasBehavior L (.goesWrong t)

end Toy.Sim
