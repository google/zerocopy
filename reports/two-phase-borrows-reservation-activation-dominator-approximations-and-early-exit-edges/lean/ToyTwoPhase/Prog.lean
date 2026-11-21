import ToyTwoPhase.Relations

/-!
# Programs with one two-phase loan

One place `x`, one two-phase mutable loan `r` with a unique reservation node `R` and a unique
activation node `A`, and shared references `s ∈ {s0, s1}` to `x`. Each node carries one
statement; branching is by successor lists (nondeterministic, path-insensitive). Unwinding
(cleanup) edges are listed separately from normal edges.
-/

namespace Toy.TwoPhase

variable {n : Nat}

/-- Names of shared references to `x`. -/
inductive SRef | s0 | s1
  deriving DecidableEq, Repr

/-- Statements other than the reservation and activation of `r`. -/
inductive Stmt
  /-- no effect -/
  | nop
  /-- read `x` directly (not through `r`) -/
  | readX
  /-- write `x` directly (not through `r`) -/
  | writeX
  /-- create shared reference `s` to `x` (reads `x`) -/
  | borrowShared (s : SRef)
  /-- read `x` through `s` -/
  | useShared (s : SRef)
  /-- write `x` through `r` -/
  | writeThrough
  /-- the loan `r` ends -/
  | endLoan
  deriving DecidableEq, Repr

/-- The effect executed at a node: `reserve` at `R`, `activate` at `A`, otherwise the node's
statement. -/
inductive Op
  | reserve | activate | readX | writeX | borrowShared (s : SRef) | useShared (s : SRef)
  | writeThrough | endLoan | nop
  deriving DecidableEq, Repr

/-- A program: a CFG over `Fin n` with entry `entry`, normal successors `succ`, unwinding
successors `unw`, reservation node `R`, activation node `A` (`R ≠ A`) and a statement per node
(ignored at `R` and `A`). -/
structure Prog (n : Nat) where
  entry : Fin n
  succ : Edges n
  unw : Edges n
  R : Fin n
  A : Fin n
  stmt : Fin n → Stmt
  hRA : R ≠ A

namespace Prog

/-- The effect executed at node `i`. -/
def op (p : Prog n) (i : Fin n) : Op :=
  if i = p.R then .reserve
  else if i = p.A then .activate
  else match p.stmt i with
    | .nop => .nop
    | .readX => .readX
    | .writeX => .writeX
    | .borrowShared s => .borrowShared s
    | .useShared s => .useShared s
    | .writeThrough => .writeThrough
    | .endLoan => .endLoan

/-- All edges: normal and unwinding. Execution, dominance and both liveness notions use these. -/
def edges (p : Prog n) : Edges n := fun i => p.succ i ++ p.unw i

/-- Nodes that end the current loan for the phase and liveness notions: `R` and `endLoan`. -/
def isKill (p : Prog n) (i : Fin n) : Bool :=
  match p.op i with
  | .reserve | .endLoan => true
  | _ => false

/-- Uses of `r`: the activation and writes through `r`. -/
def isUse (p : Prog n) (i : Fin n) : Bool :=
  match p.op i with
  | .activate | .writeThrough => true
  | _ => false

end Prog

/-- Reads of `x` that the checkers test against the loan: direct reads and creation of a
shared reference. (A read through an existing shared reference, `useShared`, is an access to
that reference; it is not tested against `r`.) -/
def Op.isRead : Op → Bool
  | .readX | .borrowShared _ => true
  | _ => false

/-! ## Path-defined phase and liveness -/

/-- `MaybeActive p L` (the path-level phase fact, read as an in-fact: it describes the point
just before `L` executes): some walk from `entry` to `L` passes `A` and, strictly between that
occurrence of `A` and `L`, passes neither `R` nor an `endLoan`. It is the meet-over-paths
solution of the gen/kill problem "generate at `A`, kill at `R` and `endLoan`". It does not
check that `R` executed before that `A`, so it can hold at nodes where the permission of `r`
is never `active` in the reference semantics (an `A` executed with no reservation is a no-op
there; see `maybeActive_pEndBeforeA_run_init`). -/
def MaybeActive (p : Prog n) (L : Fin n) : Prop :=
  ∃ pre mid : List (Fin n), IsWalk p.edges (pre ++ p.A :: (mid ++ [L])) ∧
    (pre ++ p.A :: (mid ++ [L])).head? = some p.entry ∧ ∀ x ∈ mid, p.isKill x = false

/-- `LoanLive p L`: some walk from `L` reaches a use of `r` (`A` or `writeThrough`) without
passing `R` or an `endLoan` before that use (`L` itself counts as passed unless it is the use). -/
def LoanLive (p : Prog n) (L : Fin n) : Prop :=
  ∃ (π : List (Fin n)) (U : Fin n), p.isUse U = true ∧ IsWalk p.edges (π ++ [U]) ∧
    (π ++ [U]).head? = some L ∧ ∀ x ∈ π, p.isKill x = false

/-- `SharedLive p s L`: some walk from `L` reaches `useShared s` without passing
`borrowShared s` before it. -/
def SharedLive (p : Prog n) (s : SRef) (L : Fin n) : Prop :=
  ∃ (π : List (Fin n)) (U : Fin n), p.op U = .useShared s ∧ IsWalk p.edges (π ++ [U]) ∧
    (π ++ [U]).head? = some L ∧ ∀ x ∈ π, p.op x ≠ .borrowShared s

/-- The dominator phase test (the shape of the test in rustc's `is_active`): the loan counts as
active at `L` iff `A` dominates `L` or `R` does not strictly dominate `L`. Strict dominance by
`R` renders "the statement after `R` dominates `L`" at one-statement-per-node granularity. -/
def IsActiveDom (p : Prog n) (L : Fin n) : Prop :=
  Dom p.edges p.entry p.A L ∨ ¬ (p.R ≠ L ∧ Dom p.edges p.entry p.R L)

/-! ## CFG conditions -/

/-- No unwinding edges. -/
def NoUnwind (p : Prog n) : Prop := ∀ i : Fin n, p.unw i = []

/-- `ReentryFree p`: every walk of one or more normal steps from `A` back to `A` passes `R`
strictly in between (the activation cannot be re-executed without a new reservation). -/
def ReentryFree (p : Prog n) : Prop :=
  ∀ mid : List (Fin n), IsWalk p.succ (p.A :: (mid ++ [p.A])) → p.R ∈ mid

/-- `ActivationStaysReachable p`: along normal edges, every node other than `R` that the
reservation reaches without passing `A` or `R` again can still reach `A` without passing `R`.
Precisely: for every normal successor `y ≠ R` of `R` and every node `x ≠ R` reachable from `y`
by a normal walk whose nodes before `x` avoid `A` and `R`, some normal walk from `x` to `A` has
all its nodes before `A` different from `R`. The conditions `y ≠ R` and `x ≠ R` make the
condition constrain nodes other than `R` alone: a normal edge from a region node back to `R`
(a `continue`) is admitted when that region node can also reach `A` without passing `R`
(`activationStaysReachable_pos_continue`), and a self-loop `R → R` is ignored. Branching is
nondeterministic, so this is a reachability condition, not a termination condition: it
excludes an early exit to a node with no normal successor (`activationStaysReachable_neg_exit`),
a region from which `A` is unreachable (`activationStaysReachable_neg_diverge`), and a region
node whose every normal walk to `A` passes `R` (`activationStaysReachable_neg_loopBack`); it
admits loops between `R` and `A` from which `A` stays reachable
(`activationStaysReachable_pos_argLoop`). Unwinding edges are ignored. -/
def ActivationStaysReachable (p : Prog n) : Prop :=
  ∀ y ∈ p.succ p.R, y ≠ p.R → ∀ x : Fin n, x ≠ p.R →
    PathVia p.succ (fun z => z != p.A && z != p.R) y x → PathVia p.succ (fun z => z != p.R) x p.A

/-- `DomRegionReachesA p`: `ActivationStaysReachable p` restricted to nodes `x` that `R`
dominates along normal edges. It is implied by `ActivationStaysReachable p`
(`domRegionReachesA_of_activationStaysReachable`), strictly weaker
(`pJoin_separates_domRegionReachesA`), and still sufficient for R2b
(`isActiveDom_of_maybeActive_of_reentryFree_domRegionReachesA_noUnwind`). -/
def DomRegionReachesA (p : Prog n) : Prop :=
  ∀ y ∈ p.succ p.R, y ≠ p.R → ∀ x : Fin n, x ≠ p.R → Dom p.succ p.entry p.R x →
    PathVia p.succ (fun z => z != p.A && z != p.R) y x → PathVia p.succ (fun z => z != p.R) x p.A

/-- Cleanup nodes: nodes reachable (along any edges) from the target of an unwinding edge. The
source `x` of that unwinding edge ranges over all nodes, including nodes unreachable from
`entry`, and the cleanup walk may return to normal code. -/
def IsCleanup (p : Prog n) (L : Fin n) : Prop :=
  ∃ x : Fin n, ∃ c ∈ p.unw x, PathVia p.edges (fun _ => true) c L

/-- `CleanupReadsUnderDeadLoan p`: no cleanup node reads `x` (`Op.isRead`) while `r` is live. -/
def CleanupReadsUnderDeadLoan (p : Prog n) : Prop :=
  ∀ L : Fin n, IsCleanup p L → (p.op L).isRead = true → ¬ LoanLive p L

end Toy.TwoPhase
