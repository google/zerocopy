/-!
# Programs, the reference interleaving semantics, and oracle-driven generators

A toy model of the gap between "for every interleaving" and "for every run
produced by a scheduler".

* `Prog α` — straight-line concurrent programs over an action alphabet `α`:
  atomic actions, sequential composition and (nestable) binary parallel
  composition.
* `Interleavings p` — the reference semantics: the list of all interleavings,
  defined structurally (concatenation for `seq`, shuffle for `par`).
* `Gen O α := O → Prog α → List α` — a *generated* semantics: a run function
  driven by an oracle (a scheduler's choices) of type `O`.
* `Complete gen p` / `Sound gen p` — the two halves of adequacy of a generator
  with respect to the reference semantics.

No weak memory, no fairness, no infinite executions: every program is finite and
terminating, and a trace is a finite list of actions.
-/

namespace Toy.SchedAdequacy

/-- Straight-line concurrent programs over an action alphabet `α`.
`act x` performs the atomic action `x`; `seq p q` runs `p` to completion and then
`q`; `par p q` runs `p` and `q` concurrently (every interleaving of their
actions). There is no empty program: every program performs at least one
action. -/
inductive Prog (α : Type) where
  | act : α → Prog α
  | seq : Prog α → Prog α → Prog α
  | par : Prog α → Prog α → Prog α
  deriving Repr, DecidableEq

namespace Prog

variable {α : Type}

/-- Number of atomic actions in a program (every trace of `p` has this length). -/
def size : Prog α → Nat
  | act _ => 1
  | seq p q => size p + size q
  | par p q => size p + size q

/-- The actions of a program in syntactic (left-to-right) order: a canonical
representative of the multiset of actions every trace performs. -/
def actions : Prog α → List α
  | act x => [x]
  | seq p q => actions p ++ actions q
  | par p q => actions p ++ actions q

/-- `true` iff the program contains a parallel composition anywhere. -/
def hasPar : Prog α → Bool
  | act _ => false
  | seq p q => hasPar p || hasPar q
  | par _ _ => true

end Prog

open Prog

/-- `NoNestedPar p`: no parallel composition occurs inside either component of
another parallel composition. Parallel compositions may still occur in sequence
(`seq (par a b) (par c d)`) and may have sequential components
(`par (seq a b) (seq c d)`). This is the syntactic class on which the
shared-choice generator `runShared` is intended to coincide with the per-step
generator. -/
def NoNestedPar {α : Type} : Prog α → Prop
  | .act _ => True
  | .seq p q => NoNestedPar p ∧ NoNestedPar q
  | .par p q => p.hasPar = false ∧ q.hasPar = false

/-- Decision procedure for `NoNestedPar`. -/
def decNoNestedPar {α : Type} : (p : Prog α) → Decidable (NoNestedPar p)
  | .act _ => isTrue trivial
  | .seq p q =>
      match decNoNestedPar p, decNoNestedPar q with
      | isTrue hp, isTrue hq => isTrue ⟨hp, hq⟩
      | isFalse hp, _ => isFalse fun h => hp h.1
      | _, isFalse hq => isFalse fun h => hq h.2
  | .par p q => inferInstanceAs (Decidable (p.hasPar = false ∧ q.hasPar = false))

instance {α : Type} (p : Prog α) : Decidable (NoNestedPar p) := decNoNestedPar p

/-! ## Reference semantics -/

/-- `shuffleAux x rec ys` is the list of shuffles of `x :: xs` with `ys`, where
`rec = shuffle xs`. Written this way so that `shuffle` is structurally recursive
(and therefore evaluable by `decide`). -/
def shuffleAux {α : Type} (x : α) (rec : List α → List (List α)) : List α → List (List α)
  | [] => (rec []).map (x :: ·)
  | y :: ys => (rec (y :: ys)).map (x :: ·) ++ (shuffleAux x rec ys).map (y :: ·)

/-- All interleavings (shuffles) of two lists: every merge that preserves the
relative order of each list. With repeated elements the result may contain
duplicates; only membership matters. -/
def shuffle {α : Type} : List α → List α → List (List α)
  | [], ys => [ys]
  | x :: xs, ys => shuffleAux x (shuffle xs) ys

/-- The reference semantics: all interleavings of a program, defined
structurally. `seq` concatenates a trace of each side; `par` shuffles a trace of
each side. This is the meaning of "for every interleaving" in this package. -/
def Interleavings {α : Type} : Prog α → List (List α)
  | .act x => [[x]]
  | .seq p q => (Interleavings p).flatMap fun s => (Interleavings q).map (s ++ ·)
  | .par p q => (Interleavings p).flatMap fun s => (Interleavings q).flatMap fun t => shuffle s t

/-! ## Generated semantics -/

/-- A scheduler oracle: a finite list of binary choices (`false` = left,
`true` = right). An exhausted oracle answers `false`. -/
abbrev Oracle := List Bool

/-- A generated semantics: an oracle-indexed run function. -/
abbrev Gen (O α : Type) := O → Prog α → List α

/-- `Complete gen p`: every interleaving of `p` is produced by some oracle.
Completeness is what lets a claim about *all generated runs* be read as a claim
about *all interleavings*. -/
def Complete {O α : Type} (gen : Gen O α) (p : Prog α) : Prop :=
  ∀ t ∈ Interleavings p, ∃ o, gen o p = t

/-- `Sound gen p`: every run produced by any oracle is an interleaving of `p`.
Soundness is what lets a claim that *some generated run* exhibits a behaviour be
read as a claim about *some interleaving*. -/
def Sound {O α : Type} (gen : Gen O α) (p : Prog α) : Prop :=
  ∀ o, gen o p ∈ Interleavings p

/-! ### (G1) Per-step oracle: a fresh choice at every scheduling point -/

/-- One small step of the per-step semantics. Descends from the root to an
enabled atomic action, consuming one fresh oracle bit at every `par` node on the
way (`false` = left component, `true` = right component). Returns the action,
the residual program (`none` if the program has finished) and the remaining
oracle. A `par` node whose component finishes is replaced by the other
component, so every `par` node of a residual program is a genuine choice. -/
def stepPerNode {α : Type} : Prog α → Oracle → α × Option (Prog α) × Oracle
  | .act x, o => (x, none, o)
  | .seq p q, o =>
      match stepPerNode p o with
      | (x, none, o') => (x, some q, o')
      | (x, some p', o') => (x, some (.seq p' q), o')
  | .par p q, o =>
      if o.headD false then
        match stepPerNode q o.tail with
        | (x, none, o') => (x, some p, o')
        | (x, some q', o') => (x, some (.par p q'), o')
      else
        match stepPerNode p o.tail with
        | (x, none, o') => (x, some q, o')
        | (x, some p', o') => (x, some (.par p' q), o')

/-- Iterate `stepPerNode` with an explicit fuel bound (structural recursion, so
that concrete runs are evaluable by `decide`). -/
def runPerStepAux {α : Type} : Nat → Oracle → Prog α → List α
  | 0, _, _ => []
  | n + 1, o, p =>
      match stepPerNode p o with
      | (x, none, _) => [x]
      | (x, some p', o') => x :: runPerStepAux n o' p'

/-- (G1) The per-step generator: run to completion, with a fresh oracle choice
at every scheduling point. Fuel `size p` suffices because every step performs
exactly one action and removes it from the residual program; `perStep_sound`
(every run is an interleaving, hence has `size p` actions) depends on this. -/
def runPerStep {α : Type} : Gen Oracle α := fun o p => runPerStepAux p.size o p

/-! ### (G2) Shared choice: one bit per step, passed unchanged into nested `par` -/

/-- `true` iff the next step crosses at least one `par` node (the step is a
scheduling point). -/
def needsChoice {α : Type} : Prog α → Bool
  | .act _ => false
  | .seq p _ => needsChoice p
  | .par _ _ => true

/-- One small step of the shared-choice semantics: a single choice bit `b` is
used at *every* `par` node on the root-to-action path of this step, i.e. it is
reused by a parent `par` node and by the `par` nodes nested below it on that
path (`false` = leftmost at every such node, `true` = rightmost). The step
descends into only one component of each `par` node; the bit is never given to
two sibling subtrees. -/
def stepShared {α : Type} : Prog α → Bool → α × Option (Prog α)
  | .act x, _ => (x, none)
  | .seq p q, b =>
      match stepShared p b with
      | (x, none) => (x, some q)
      | (x, some p') => (x, some (.seq p' q))
  | .par p q, b =>
      if b then
        match stepShared q b with
        | (x, none) => (x, some p)
        | (x, some q') => (x, some (.par p q'))
      else
        match stepShared p b with
        | (x, none) => (x, some q)
        | (x, some p') => (x, some (.par p' q))

/-- Iterate `stepShared` with explicit fuel; one oracle bit is consumed per step
that crosses a `par` node, none otherwise. -/
def runSharedAux {α : Type} : Nat → Oracle → Prog α → List α
  | 0, _, _ => []
  | n + 1, o, p =>
      let bo : Bool × Oracle := if needsChoice p then (o.headD false, o.tail) else (false, o)
      match stepShared p bo.1 with
      | (x, none) => [x]
      | (x, some p') => x :: runSharedAux n bo.2 p'

/-- (G2) The shared-choice generator: one oracle bit per scheduling step, reused
at every `par` node on that step's root-to-action path (a parent `par` and the
`par` nodes nested below it on the path, not sibling subtrees). This models a
semantics that passes one scheduler choice down into nested parallel
compositions instead of drawing a fresh choice at each of them. Unlike
`Interleavings`, the set of runs depends on how `par` is parenthesized and
ordered (see `shared_depends_on_parenthesization`). Fuel `size p` suffices for
the same reason as for `runPerStep`. -/
def runShared {α : Type} : Gen Oracle α := fun o p => runSharedAux p.size o p

/-! ### Scheduling points and (G3) a deterministic scheduler -/

/-- An upper bound on the number of oracle bits any run of `runPerStep` or
`runShared` consumes: a `par` node whose components have `m` and `n` actions is
crossed by at most `m + n - 1` steps while both components are live (once one
component finishes, the node disappears). It counts per-node choices, not steps:
on a right-nested chain of `k` parallel actions it is `k (k - 1) / 2` (not proved here
for general `k`; `schedPoints_spine4` proves `k = 4`), whereas `runShared` never reads more than
`size p - 1` bits (`shared_oracleBounded_size_pred`). -/
def schedPoints {α : Type} : Prog α → Nat
  | .act _ => 0
  | .seq p q => schedPoints p + schedPoints q
  | .par p q => schedPoints p + schedPoints q + (p.size + q.size - 1)

/-- The fixed alternating choice sequence `false, true, false, …` of length `n`. -/
def alternating (n : Nat) : Oracle := (List.range n).map fun i => i % 2 == 1

/-- (G3) A deterministic scheduler: the per-step semantics driven by a fixed
alternating choice sequence; the supplied oracle is ignored, so it generates
exactly one run per program. It alternates consumed oracle bits, not threads: a
step that crosses two nested `par` nodes consumes two bits, so under nested
parallel composition one outer component can run to completion before the other
steps (`runRoundRobin_nested_runs_left_first`). -/
def runRoundRobin {α : Type} : Gen Oracle α := fun _ p => runPerStep (alternating (schedPoints p)) p

/-- A generator that ignores sequencing: it runs the per-step semantics on the
program with every `seq` replaced by `par`. Used as a complete-but-unsound
countermodel (it can produce orders the program forbids). -/
def seqToPar {α : Type} : Prog α → Prog α
  | .act x => .act x
  | .seq p q => .par (seqToPar p) (seqToPar q)
  | .par p q => .par (seqToPar p) (seqToPar q)

/-- See `seqToPar`. -/
def runIgnoringSeq {α : Type} : Gen Oracle α := fun o p => runPerStep o (seqToPar p)

end Toy.SchedAdequacy
