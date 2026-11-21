import Toy.Progress.Syntax

/-!
# Small-step execution and the three behaviour semantics

The language is deterministic, so from each initial state a command has exactly one
run. Runs are explored by a fuel-indexed iteration `run n` of a small-step function;
termination, divergence and infinite traces are defined from all finite prefixes of
the run (no coinductive definitions are used).

* `ObsBeh` — divergence-observable semantics: terminating with a finite trace,
  diverging silently after a finite trace, or reacting forever with an infinite trace
  are three distinct observable behaviours.
* `FPBeh` — forward-progress semantics: a run that eventually stops emitting while
  never terminating is undefined behaviour, which allows every behaviour.
* `MixedBeh` — per-loop semantics: undefined behaviour arises only when a loop whose
  progress flag is set is entered and then itself fails to make progress: it completes
  infinitely many iterations of its own body and, from some iteration on, emits nothing.
  Divergence *inside* one iteration (for example in a nested loop) is attributed to the
  nested loop, never to the enclosing one.

Final states are not observable; only the emitted trace is. Because the language is
deterministic and `ObsBeh` has no undefined-behaviour case, every run has exactly one
divergence-observable behaviour (`obsBeh_exists`, `obsBeh_unique`), so `Refines ObsBeh`
is behavioural equivalence (`refines_obsBeh_iff_equiv`).
-/

namespace Toy.Progress

/-- One small step. `none` exactly for `skip` (the terminated configuration). The list
component is the emitted output of the step (empty or a single value). -/
def step : Cmd → State → Option (Cmd × State × List Val)
  | .skip, _ => none
  | .assign x e, s => some (.skip, State.update s x (e.eval s), [])
  | .emit e, s => some (.skip, s, [e.eval s])
  | .seq c₁ c₂, s =>
      match step c₁ s with
      | none => some (c₂, s, [])
      | some (c₁', s', o) => some (.seq c₁' c₂, s', o)
  | .ite b c₁ c₂, s => some (if b.eval s = 0 then c₂ else c₁, s, [])
  | .loop mp b body, s => some (.ite b (.seq body (.loop mp b body)) .skip, s, [])

/-- `run n c s` performs up to `n` steps from `(c, s)` (stopping early at `skip`) and
returns the reached configuration together with the output emitted so far. -/
def run : Nat → Cmd → State → Cmd × State × List Val
  | 0, c, s => (c, s, [])
  | n + 1, c, s =>
      match step c s with
      | none => (c, s, [])
      | some (c', s', o) =>
          let r := run n c' s'
          (r.1, r.2.1, o ++ r.2.2)

/-- The output emitted during the first `n` steps. -/
def traceAt (n : Nat) (c : Cmd) (s : State) : List Val := (run n c s).2.2

/-- `TermsWith c s t s'`: the run of `c` from `s` terminates in final state `s'` having
emitted exactly `t`. -/
def TermsWith (c : Cmd) (s : State) (t : List Val) (s' : State) : Prop :=
  ∃ n, run n c s = (.skip, s', t)

/-- The run of `c` from `s` terminates. -/
def Terminates (c : Cmd) (s : State) : Prop := ∃ t s', TermsWith c s t s'

/-- The run of `c` from `s` never reaches `skip`. -/
def Diverges (c : Cmd) (s : State) : Prop := ∀ n, (run n c s).1 ≠ .skip

/-- Observable behaviours. `term t`: terminates having emitted `t`. `div t`: runs
forever, emitting exactly `t` in total. `react f`: runs forever emitting the infinite
sequence `f 0, f 1, …`. -/
inductive Beh where
  | term (t : List Val)
  | div (t : List Val)
  | react (f : Nat → Val)

/-- The first `k` elements of an infinite sequence. -/
def prefixOf (f : Nat → Val) (k : Nat) : List Val := (List.range k).map f

/-- Divergence-observable behaviours of `c` from `s` (the semantics used for Rust's
`loop {}` and by CompCert-style behaviour sets). Because each step emits at most one
value, `react f` holds iff every finite prefix of `f` is emitted at some point. -/
def ObsBeh (c : Cmd) (s : State) : Beh → Prop
  | .term t => ∃ s', TermsWith c s t s'
  | .div t => Diverges c s ∧ ∃ N, ∀ n, N ≤ n → traceAt n c s = t
  | .react f => ∀ k, ∃ n, traceAt n c s = prefixOf f k

/-- The run of `c` from `s` never terminates and eventually stops emitting. -/
def SilentlyDiverges (c : Cmd) (s : State) : Prop := ∃ t, ObsBeh c s (.div t)

/-- Forward-progress behaviours: a silently diverging run is undefined behaviour and
admits every behaviour; otherwise the behaviours are the observable ones. This is the
thread-level reading of a forward-progress assumption: every run must eventually
terminate or perform an observable effect again. -/
def FPBeh (c : Cmd) (s : State) (b : Beh) : Prop :=
  SilentlyDiverges c s ∨ ObsBeh c s b

/-- The command that executes next in a configuration: the leftmost component of a
left-nested sequence. A loop is *entered* when it is the head. -/
def Cmd.head : Cmd → Cmd
  | .seq c₁ _ => c₁.head
  | c => c

/-- `SilentlyIterates b body s`: the loop `while b do body`, entered in state `s`, completes
infinitely many iterations of its own body — before each iteration the condition is true,
and every run of `body` terminates — and from some iteration on, no iteration emits.
Divergence inside a single run of `body` (for example in a nested loop) does *not* make
the enclosing loop silently iterate. -/
def SilentlyIterates (b : Exp) (body : Cmd) (s : State) : Prop :=
  ∃ σ : Nat → State, ∃ o : Nat → List Val, σ 0 = s ∧
    (∀ i, b.eval (σ i) ≠ 0 ∧ TermsWith body (σ i) (o i) (σ (i + 1))) ∧
    ∃ N, ∀ i, N ≤ i → o i = []

/-- `ProgressViolation c s`: at some point of the run of `c` from `s`, a loop whose
progress flag is `true` is entered (it is the head of the configuration) and from the
state at which it is entered that loop silently iterates (`SilentlyIterates`): the
progress obligation belongs to the innermost loop that fails to make progress, and only
that loop's own flag is consulted. -/
def ProgressViolation (c : Cmd) (s : State) : Prop :=
  ∃ n b body, (run n c s).1.head = .loop true b body ∧
    SilentlyIterates b body (run n c s).2.1

/-- Per-loop (mixed) behaviours: a progress violation is undefined behaviour and admits
every behaviour; otherwise the behaviours are the observable ones. A loop whose flag is
`false` is divergence-observable even when it runs inside a flagged loop: if it silently
iterates forever, the enclosing flagged loop never completes an iteration, so no flagged
loop silently iterates. -/
def MixedBeh (c : Cmd) (s : State) (b : Beh) : Prop :=
  ProgressViolation c s ∨ ObsBeh c s b

/-- Refinement under a behaviour semantics `sem`: from every initial state, every
behaviour of the target `tgt` is a behaviour of the source `src`. -/
def Refines (sem : Cmd → State → Beh → Prop) (src tgt : Cmd) : Prop :=
  ∀ s b, sem tgt s b → sem src s b

/-- Two states agree on every variable outside `X`. -/
def AgreeOff (X : List Var) (s₁ s₂ : State) : Prop := ∀ y, y ∉ X → s₁ y = s₂ y

/-- `DeadAtEntry X k`: the variables in `X` are (semantically) dead at the entry of `k`,
i.e. the observable behaviours of `k` do not depend on their initial values. -/
def DeadAtEntry (X : List Var) (k : Cmd) : Prop :=
  ∀ s₁ s₂, AgreeOff X s₁ s₂ → ∀ b, ObsBeh k s₁ b ↔ ObsBeh k s₂ b

/-- `ReachableAt p s₁`: `s₁` is the state at the end of some terminating run of the
prefix `p`; for a program `p ;; L ;; k`, these are exactly the states in which the
loop `L` is entered. -/
def ReachableAt (p : Cmd) (s₁ : State) : Prop := ∃ s₀ t, TermsWith p s₀ t s₁

/-- `DeadAfterPrefix p X k`: the variables in `X` are dead at the entry of `k` in every
state reachable at the end of `p` (`ReachableAt p`): from such a state, changing the
variables in `X` does not change the observable behaviours of `k`. Implied by
`DeadAtEntry X k` (`deadAfterPrefix_of_deadAtEntry`), and strictly weaker. -/
def DeadAfterPrefix (p : Cmd) (X : List Var) (k : Cmd) : Prop :=
  ∀ s₁ s₂, ReachableAt p s₁ → AgreeOff X s₁ s₂ → ∀ b, ObsBeh k s₁ b ↔ ObsBeh k s₂ b

end Toy.Progress
