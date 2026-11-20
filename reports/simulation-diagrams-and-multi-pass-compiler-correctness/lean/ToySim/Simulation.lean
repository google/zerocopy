import ToySim.Defs

/-!
# Simulation diagrams, receptiveness, determinacy

Each clause of a simulation is a separately named proposition so that results
can name exactly the clauses they use.  A simulation is given by

* an index type `I` with an order `ord` (the "measure" that bounds stuttering),
* a relation `R : I → L₁.State → L₂.State → Prop` between source and target
  states.

Throughout, `L₁` is the source (before the pass) and `L₂` the target (after).
-/

namespace Toy.Sim

variable {E Res : Type}

/-! ## Forward simulation: source step ⇒ target steps -/

section Forward
variable (L₁ L₂ : LTS E Res) {I : Type}

/-- Forward clause for initial states: every initial source state is related
to some initial target state. -/
def FSimInit (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂

/-- Forward clause for final states: a target state related to a final source
state is itself final, with the same result (no trailing target steps). -/
def FSimFinal (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂ r, R i s₁ s₂ → L₁.final s₁ r → L₂.final s₂ r

/-- Forward step diagram with stuttering: every source step from a related
pair is matched by target steps with the same trace, reaching a related pair.
Either the target makes at least one step, or it makes zero or more steps and
the index decreases in `ord`.

Well-foundedness of `ord` is *not* part of this clause. -/
def FSimStep (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
    ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
      R i' s₁' s₂'

/-- A forward simulation from `L₁` to `L₂`: the three forward clauses plus
well-foundedness of the index order.

Captures: the proof obligation discharged for one compiler pass in the
"source step ⇒ target steps" direction. -/
structure IsForwardSim (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop) :
    Prop where
  wf : WellFounded ord
  init : FSimInit L₁ L₂ R
  final : FSimFinal L₁ L₂ R
  step : FSimStep L₁ L₂ ord R

end Forward

/-! ## Backward simulation: target step ⇒ source steps -/

section Backward
variable (L₁ L₂ : LTS E Res) {I : Type}

/-- Backward clause: if the source has an initial state, so does the target. -/
def BSimInitExists : Prop :=
  (∃ s₁, L₁.init s₁) → ∃ s₂, L₂.init s₂

/-- Backward clause for initial states: given any initial source state, every
initial target state is related to some (possibly different) initial source
state. -/
def BSimInitMatch (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ s₁ s₂, L₁.init s₁ → L₂.init s₂ → ∃ i s₁', L₁.init s₁' ∧ R i s₁' s₂

/-- Backward clause for final states: if the target state is final and the
related source state is safe, the source can silently reach a final state with
the same result. -/
def BSimFinal (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂ r, R i s₁ s₂ → Safe L₁ s₁ → L₂.final s₂ r →
    ∃ s₁', Star L₁ s₁ [] s₁' ∧ L₁.final s₁' r

/-- Backward progress clause: a target state related to a safe source state is
final or can step. -/
def BSimProgress (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂, R i s₁ s₂ → Safe L₁ s₁ →
    (∃ r, L₂.final s₂ r) ∨ (∃ e s₂', L₂.step s₂ e s₂')

/-- Backward step diagram with stuttering: every target step from a pair
whose source state is safe is matched by source steps with the same trace.
Either the source makes at least one step, or it makes zero or more steps and
the index decreases in `ord`.

Well-foundedness of `ord` is *not* part of this clause. -/
def BSimStep (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂ e s₂', R i s₁ s₂ → Safe L₁ s₁ → L₂.step s₂ e s₂' →
    ∃ i' s₁', (Plus L₁ s₁ (obs e) s₁' ∨ (Star L₁ s₁ (obs e) s₁' ∧ ord i' i)) ∧
      R i' s₁' s₂'

/-- A backward simulation from `L₁` (source) to `L₂` (target).

Captures: the proof obligation in the "target step ⇒ source steps" direction,
conditional on the source state being safe.  This is the direction that
behaviour refinement needs. -/
structure IsBackwardSim (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop) :
    Prop where
  wf : WellFounded ord
  initExists : BSimInitExists L₁ L₂
  initMatch : BSimInitMatch L₁ L₂ R
  final : BSimFinal L₁ L₂ R
  progress : BSimProgress L₁ L₂ R
  step : BSimStep L₁ L₂ ord R

end Backward

/-! ## Receptiveness and determinacy -/

/-- Lift a matching relation on events to step labels: a silent label matches
only a silent label, and two events match when `M` relates them.

`M a b` is read "`a` and `b` are alternative responses of the environment to
the same interaction" (for example, two different values returned by the same
read).  `M = Eq` means the environment never has a choice. -/
def LabelMatch (M : E → E → Prop) : Option E → Option E → Prop
  | none, none => True
  | some a, some b => M a b
  | _, _ => False

/-- `Receptive M L`: whenever `L` can emit an event `a` from a state, it can
also emit, from the same state, every event `b` that matches `a`.

Captures: the program does not get to refuse an alternative response of the
environment.  For `M = Eq` every system is receptive.  The condition
quantifies over every state of `L`, reachable or not. -/
def Receptive (M : E → E → Prop) (L : LTS E Res) : Prop :=
  ∀ s a s₁ b, L.step s (some a) s₁ → M a b → ∃ s₂, L.step s (some b) s₂

/-- `StepLabelsMatch M L`: any two steps from the same state carry matching
labels.  In particular a state cannot offer both a silent step and an event,
nor two events that are not alternative responses to the same interaction.

No algebraic axiom on `M` is assumed, but this clause constrains `M` on the
events of `L`: taking the same step twice forces `M a a` for every event `a`
that `L` can emit, and two events `a`, `b` offered by the same state force
both `M a b` and `M b a` (`Toy.Sim.StepLabelsMatch.refl_symm`). -/
def StepLabelsMatch (M : E → E → Prop) (L : LTS E Res) : Prop :=
  ∀ s e₁ s₁ e₂ s₂, L.step s e₁ s₁ → L.step s e₂ s₂ → LabelMatch M e₁ e₂

/-- `StepFunctional L`: the successor state is determined by the label. -/
def StepFunctional (L : LTS E Res) : Prop :=
  ∀ s e s₁ s₂, L.step s e s₁ → L.step s e s₂ → s₁ = s₂

/-- `InitDeterminate L`: there is at most one initial state. -/
def InitDeterminate (L : LTS E Res) : Prop :=
  ∀ s s', L.init s → L.init s' → s = s'

/-- `FinalNoStep L`: final states have no outgoing step. -/
def FinalNoStep (L : LTS E Res) : Prop :=
  ∀ s r, L.final s r → ∀ e s', ¬ L.step s e s'

/-- `FinalDeterminate L`: a final state has at most one result. -/
def FinalDeterminate (L : LTS E Res) : Prop :=
  ∀ s r r', L.final s r → L.final s r' → r = r'

/-- `Determinate M L`: the only nondeterminism of `L` is the environment's
choice among matching events.  All five clauses quantify over every state of
`L`, reachable or not.

Captures: a target language whose internal execution is deterministic
(for `M = Eq`: `L` is deterministic outright). -/
structure Determinate (M : E → E → Prop) (L : LTS E Res) : Prop where
  labels : StepLabelsMatch M L
  functional : StepFunctional L
  init : InitDeterminate L
  finalNoStep : FinalNoStep L
  finalDet : FinalDeterminate L

/-! ## Vertical composition data -/

section Compose
variable {I₁ I₂ : Type}

/-- The composite index order for two stacked simulations with index orders
`ord₁` (first pass) and `ord₂` (second pass): lexicographic on `I₂ × I₁`, with
the *transitive closure* of `ord₂` on the first component.  The transitive
closure is needed because one step of the first pass may expand to several
steps of the middle language, each of which may stutter in the second pass. -/
def compOrd (ord₁ : I₁ → I₁ → Prop) (ord₂ : I₂ → I₂ → Prop) :
    I₂ × I₁ → I₂ × I₁ → Prop :=
  fun p q => Relation.TransGen ord₂ p.1 q.1 ∨ (p.1 = q.1 ∧ ord₁ p.2 q.2)

/-- The composite relation for two stacked simulations: relational composition
through some state of the middle language. -/
def compRel {S₁ S₂ S₃ : Type} (R₁ : I₁ → S₁ → S₂ → Prop) (R₂ : I₂ → S₂ → S₃ → Prop) :
    I₂ × I₁ → S₁ → S₃ → Prop :=
  fun p s₁ s₃ => ∃ s₂, R₁ p.2 s₁ s₂ ∧ R₂ p.1 s₂ s₃

end Compose

/-! ## Pipelines -/

/-- `FSimChain L L'`: there is a finite chain of languages from `L` to `L'`
in which every link carries a forward simulation (zero links allowed).

Captures: a multi-pass compiler in which each pass has been proved correct by
a forward simulation.  Nothing is assumed about the intermediate languages. -/
inductive FSimChain : LTS E Res → LTS E Res → Prop where
  | nil (L : LTS E Res) : FSimChain L L
  | cons {L₁ L₂ L₃ : LTS E Res} {I : Type} (ord : I → I → Prop)
      (R : I → L₁.State → L₂.State → Prop) :
      IsForwardSim L₁ L₂ ord R → FSimChain L₂ L₃ → FSimChain L₁ L₃

end Toy.Sim
