# Two-phase borrows: reservation, activation, dominator approximations and early-exit edges

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Scope.** These are statements about the toy model; they neither establish nor refute the
corresponding claims about rustc's borrow checker, Tree Borrows, or Miri.
Model–system relation: none proved.
Connections to rustc are separate `derived (modeling bridge)` claims (Evidence, modeling bridges),
and the compiler and Miri runs on the public reproducer of rust-lang/rust#160598 are separate
`execution` observations. Lean project: `lean/` (library `ToyTwoPhase`, namespace `Toy.TwoPhase`),
Lean `v4.34.1`, core Lean and `Std` (no Mathlib). Every theorem in the project is proved;
`#print axioms` (via `Lean.collectAxioms`) shows at most `propext`, `Classical.choice` and
`Quot.sound` for every declaration (Evidence).

* **R1a.** For every toy program in which `A` is reachable from the entry, and every node `L`, the
  forward may-analysis (generate at `A`, kill at `R` and at `endLoan`, join by disjunction over all
  edges, `n` iterations from all-`false`) yields `true` at `L` exactly when the path-level phase
  fact `MaybeActive p L` holds (both are in-facts).
* **R1b.** For every toy program (loops and unwinding edges allowed): if the exact-phase checker
  (phase test `MaybeActive`) accepts it, then no walk from the entry reaches UB in the reference
  semantics.
* **R1c.** For every toy program: if the iterative dataflow checker (phase test `dfMaybeActive`)
  accepts it, then the exact-phase checker accepts it and no walk from the entry reaches UB.
* **R1d.** For every toy program in which `A` is reachable from the entry, the iterative dataflow
  checker accepts it if and only if the exact-phase checker accepts it.
* **R2.** There exist toy programs (`pLoopBack`, `pLoop1`, `pDiverge`; 7, 5 and 7 nodes) in which
  `R` dominates `A`, `A` post-dominates `R` along normal edges, and there are no unwinding edges
  (and, in `pLoopBack` and `pDiverge`, every normal walk from `A` back to `A` passes `R`), yet the
  dominator checker accepts and a walk from the entry reaches UB.
* **R2a.** For a toy program whose normal-edge CFG is acyclic, in which `A` post-dominates `R` along
  normal edges and which has no unwinding edges, at every node where the loan may be active the
  dominator test calls the loan active.
* **R2b.** For a toy program in which every normal walk from `A` back to `A` passes `R`, every node
  `x ≠ R` reached from a normal successor `y ≠ R` of `R` along normal edges without passing `A` or `R`
  before `x` can still reach `A` along normal edges without passing `R`, and which has no unwinding
  edges, at every node where the loan may be active the dominator test calls the loan active.
* **R2c.** For a toy program satisfying the three conditions of R2b (`ReentryFree`,
  `ActivationStaysReachable`, no unwinding edges): if the dominator checker accepts it, then no walk
  from the entry reaches UB.
* **R3.** There exists an 8-node acyclic toy program (`pBreak`; no unwinding edges, `R` dominates
  `A`) with an early exit (`break`) from between `R` and `A` that the dominator checker accepts and
  the exact-phase checker rejects, and in which a walk from the entry reaches UB.
* **R4.** There exists a safe 8-node toy program (`pJoin`) in which `R` dominates `A`, that the
  exact-phase checker accepts and the dominator checker rejects.
* **R5a.** For every toy program: if repair (b) (dominator test when the decidable guard `DomGuard`
  holds, otherwise every loan counts as active) accepts it, then the exact-phase checker accepts it
  and no walk from the entry reaches UB.
* **R5c.** For every toy program: if repair (c) (reject when `DomGuard` fails, otherwise the
  dominator checker) accepts it, then repair (b) accepts it; both inclusions (c) ⊆ (b) ⊆ exact-phase
  checker are strict (witnesses `pJoin` and `pBreakDead`).
* **R5d.** The literal repair (b) — the dominator test when `A` post-dominates `R` along normal
  edges, otherwise every loan counts as active — accepts the 7-node looping toy program `pLoopBack`,
  in which a walk from the entry reaches UB.
* **R6b.** In the 5-node toy program `pWriteDuringRes`, which writes to `x` during the reservation,
  a walk from the entry reaches UB, and the exact-phase and dominator checkers flag the write.
* **R6c.** In the 5-node toy program `pSharedDuringRes`, which uses, after the activation, a shared
  reference created during the reservation, a walk from the entry reaches UB, and for each of the
  exact-phase and dominator checkers a node is flagged if and only if it is `A`.
* **R7a.** For a toy program (unwinding edges allowed) in which every normal walk from `A` back to `A`
  passes `R` and every node `x ≠ R` reached from a normal successor `y ≠ R` of `R` along normal edges
  without passing `A` or `R` before `x` can still reach `A` along normal edges without passing `R`, at
  every node that is not a cleanup node and where the loan may be active, the dominator test
  (dominance over all edges) calls the loan active.
* **R7b.** There exists a 9-node toy program (`pCleanup`), satisfying `ReentryFree` and
  `ActivationStaysReachable`, whose cleanup block, shared by an unwinding edge before `A` and one
  after `A`, reads `x` while the loan is live; the dominator checker accepts it and a walk from the
  entry reaches UB.
* **R7c.** For a toy program (unwinding edges allowed) satisfying `ReentryFree` and
  `ActivationStaysReachable`, in which no cleanup node reads `x` while the loan is live: if the
  dominator checker accepts it, then no walk from the entry reaches UB.

Non-claims and escape hatches: Boundaries, and each card.

## Applicability

**Model fidelity.** A toy, not a mirror of any compiler's data structures. It is meant to capture
the phase question a borrow checker answers for a two-phase mutable borrow (`&mut` created by
autoref, argument reborrow or compound assignment): at a read of the borrowed place, is the loan
still a mere reservation? Gaps: one place `x`, one two-phase loan `r`, two shared references; no
regions or lifetimes (liveness is path reachability of a use); one statement per node; branching is
nondeterministic (path-insensitive); no interior mutability, no protectors, no `conflicted` flag on
reservations. Lean `leanprover/lean4:v4.34.1`, no Mathlib.

**Subjects and their relation.** The toy is compared, in `derived (modeling bridge)` prose, with
rustc's `is_active` test and its documented assumptions (rust-lang/rust at commit
`26bfbf28f5f79dff333ce5a232f131b496ec9cfe`), with RFC 2025's reservation rules, and with Tree
Borrows' `Reserved` permission. No embedding, abstraction or simulation between the toy and MIR or
Tree Borrows is defined or proved. Model–system relation: none proved. The Lean 4 toolchain
`v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`) is the checker of every theorem.
The two rustc nightly commits (`8eb778d04094d3af4b26580cab327e0413eb1e02` and
`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`) identify the compiler and the Miri build used for the
separate `execution` observations on the public reproducer of rust-lang/rust#160598 (Evidence); no
theorem refers to them.

### Graphs, walks, dominance (`ToyTwoPhase/Graph.lean`, `ToyTwoPhase/Relations.lean`)

```lean
-- ToyTwoPhase/Graph.lean:16
abbrev Edges (n : Nat) := Fin n → List (Fin n)

-- ToyTwoPhase/Graph.lean:22-25
def IsWalk (E : Edges n) : List (Fin n) → Prop
  | [] => False
  | [_] => True
  | a :: b :: rest => b ∈ E a ∧ IsWalk E (b :: rest)

-- ToyTwoPhase/Graph.lean:39-40
def PathVia (E : Edges n) (ok : Fin n → Bool) (u v : Fin n) : Prop :=
  ∃ π : List (Fin n), IsWalk E (π ++ [v]) ∧ (π ++ [v]).head? = some u ∧ ∀ x ∈ π, ok x = true

-- ToyTwoPhase/Graph.lean:55-56
def pathViaB (E : Edges n) (ok : Fin n → Bool) (u v : Fin n) : Bool :=
  (closeIter E ok u n).contains v
```

`PathVia E ok u v`: a walk `u = x₀ → … → x_k = v` (`k ≥ 0`) whose nodes before the last satisfy
`ok`. The decidable checker `pathViaB` (n iterations of successor closure) agrees with it:

```lean
-- ToyTwoPhase/Graph.lean:257-258
theorem pathViaB_iff {E : Edges n} {ok : Fin n → Bool} {u v : Fin n} :
    pathViaB E ok u v = true ↔ PathVia E ok u v := by …
```

```lean
-- ToyTwoPhase/Relations.lean:55-56
def Dom (E : Edges n) (entry a b : Fin n) : Prop :=
  ∀ π : List (Fin n), IsWalk E π → π.head? = some entry → π.getLast? = some b → a ∈ π

-- ToyTwoPhase/Relations.lean:60-62
def PDom (E : Edges n) (a b : Fin n) : Prop :=
  ∀ (π : List (Fin n)) (x : Fin n), IsWalk E π → π.head? = some b → π.getLast? = some x →
    E x = [] → a ∈ π

-- ToyTwoPhase/Relations.lean:65-66
def Acyclic (E : Edges n) : Prop :=
  ∀ (x : Fin n) (mid : List (Fin n)), ¬ IsWalk E (x :: (mid ++ [x]))
```

* `Dom E entry a b` (`a` dominates `b`): every walk from `entry` to `b` contains `a`; nodes unreachable
  from `entry` are dominated by every node (`dom_unreachable`). Decidable via the proved equivalence
  `dom_iff_not_pathVia`. Examples: `dom_pos`, `dom_neg`.
* `PDom E a b` (`a` post-dominates `b`): every walk from `b` to an exit (a node with no
  `E`-successor) contains `a`. Used with the normal edges `p.succ` (unwinding ignored). Decidable via
  `pdom_iff_not_pathVia`. Examples: `pdom_pos`, `pdom_neg`.
* `Acyclic E`: no walk of one or more steps returns to its start; decidable via `acyclic_iff`.
  Examples: `acyclic_pos`, `acyclic_neg`.

### Programs (`ToyTwoPhase/Prog.lean`)

```lean
-- ToyTwoPhase/Prog.lean:17-18
inductive SRef | s0 | s1
  deriving DecidableEq, Repr

-- ToyTwoPhase/Prog.lean:21-36
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

-- ToyTwoPhase/Prog.lean:40-43
inductive Op
  | reserve | activate | readX | writeX | borrowShared (s : SRef) | useShared (s : SRef)
  | writeThrough | endLoan | nop
  deriving DecidableEq, Repr

-- ToyTwoPhase/Prog.lean:48-57
structure Prog (n : Nat) where
  entry : Fin n
  succ : Edges n
  unw : Edges n
  R : Fin n
  A : Fin n
  stmt : Fin n → Stmt
  hRA : R ≠ A

namespace Prog

-- ToyTwoPhase/Prog.lean:60-70
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

-- ToyTwoPhase/Prog.lean:73
def edges (p : Prog n) : Edges n := fun i => p.succ i ++ p.unw i

-- ToyTwoPhase/Prog.lean:76-79
def isKill (p : Prog n) (i : Fin n) : Bool :=
  match p.op i with
  | .reserve | .endLoan => true
  | _ => false

-- ToyTwoPhase/Prog.lean:82-85
def isUse (p : Prog n) (i : Fin n) : Bool :=
  match p.op i with
  | .activate | .writeThrough => true
  | _ => false

-- ToyTwoPhase/Prog.lean:92-94
def Op.isRead : Op → Bool
  | .readX | .borrowShared _ => true
  | _ => false
```

* A node executes `reserve` at `R`, `activate` at `A`, and its statement elsewhere; so the
  reservation and the activation are unique by construction and `R ≠ A`. There is no program with
  zero or one node (`prog_zero_uninhabited`, `prog_one_uninhabited`).
* `useShared s` is not a read for the checkers: an access through an existing shared reference is an
  access to that reference; conflicts with `r` are caught when the shared reference is created
  (`borrowShared` is a read) or at the activation (the activation check below). In the reference
  semantics `useShared s` *is* a foreign read of `x`.

### Path-level phase, liveness and the dominator test (`ToyTwoPhase/Prog.lean`)

```lean
-- ToyTwoPhase/Prog.lean:105-107
def MaybeActive (p : Prog n) (L : Fin n) : Prop :=
  ∃ pre mid : List (Fin n), IsWalk p.edges (pre ++ p.A :: (mid ++ [L])) ∧
    (pre ++ p.A :: (mid ++ [L])).head? = some p.entry ∧ ∀ x ∈ mid, p.isKill x = false

-- ToyTwoPhase/Prog.lean:111-113
def LoanLive (p : Prog n) (L : Fin n) : Prop :=
  ∃ (π : List (Fin n)) (U : Fin n), p.isUse U = true ∧ IsWalk p.edges (π ++ [U]) ∧
    (π ++ [U]).head? = some L ∧ ∀ x ∈ π, p.isKill x = false

-- ToyTwoPhase/Prog.lean:117-119
def SharedLive (p : Prog n) (s : SRef) (L : Fin n) : Prop :=
  ∃ (π : List (Fin n)) (U : Fin n), p.op U = .useShared s ∧ IsWalk p.edges (π ++ [U]) ∧
    (π ++ [U]).head? = some L ∧ ∀ x ∈ π, p.op x ≠ .borrowShared s

-- ToyTwoPhase/Prog.lean:124-125
def IsActiveDom (p : Prog n) (L : Fin n) : Prop :=
  Dom p.edges p.entry p.A L ∨ ¬ (p.R ≠ L ∧ Dom p.edges p.entry p.R L)
```

* `MaybeActive p L` is the path-level phase fact, read as an in-fact (just before `L` executes):
  some walk from the entry passes `A` and then reaches `L` without passing `R` or an `endLoan` in
  between. It is the meet-over-paths solution of "generate at `A`, kill at `R` and `endLoan`". It
  does not check that `R` ran before that `A` (`maybeActive_pEndBeforeA_run_init`). Examples:
  `maybeActive_pos`, `maybeActive_neg`, `maybeActive_neg_endLoan`, `maybeActive_in_fact_pLoopOK`.
* `LoanLive p L`: some walk from `L` reaches a use of `r` (`A` or `writeThrough`) before passing `R`
  or `endLoan`. It is path-insensitive and looks backward from uses; it has no forward in-scope
  component. Examples:
  `loanLive_pos`, `loanLive_neg`, `loanLive_neg_at_R`.
* `SharedLive p s L`: some walk from `L` reaches `useShared s` before passing `borrowShared s`.
  Examples: `sharedLive_pos`, `sharedLive_neg`.
* `IsActiveDom p L` has the shape of the test in rustc's `is_active`: `A dom L ∨ ¬(succ(R) dom L)`.
  With one statement per node, "the statement after `R` dominates `L`" is rendered as strict
  dominance by `R` (`R ≠ L ∧ R dom L`), a modeling choice. Examples: `isActiveDom_pos`,
  `isActiveDom_neg`.

Decidability: `maybeActive_iff`, `loanLive_iff`, `sharedLive_iff`, `reentryFree_iff` restate the
walk definitions with `PathVia`:

```lean
-- ToyTwoPhase/Decide.lean:14-16
theorem maybeActive_iff (p : Prog n) (L : Fin n) :
    MaybeActive p L ↔ PathVia p.edges (fun _ => true) p.entry p.A ∧
      ∃ y ∈ p.edges p.A, PathVia p.edges (fun x => !p.isKill x) y L := by …

-- ToyTwoPhase/Decide.lean:39-40
theorem loanLive_iff (p : Prog n) (L : Fin n) :
    LoanLive p L ↔ ∃ U : Fin n, p.isUse U = true ∧ PathVia p.edges (fun x => !p.isKill x) L U := by …

-- ToyTwoPhase/Decide.lean:50-52
theorem sharedLive_iff (p : Prog n) (s : SRef) (L : Fin n) :
    SharedLive p s L ↔ ∃ U : Fin n, p.op U = .useShared s ∧
      PathVia p.edges (fun x => p.op x != .borrowShared s) L U := by …

-- ToyTwoPhase/Decide.lean:68-69
theorem reentryFree_iff (p : Prog n) :
    ReentryFree p ↔ ∀ y ∈ p.succ p.A, ¬ PathVia p.succ (fun x => x != p.R) y p.A := by …
```

### CFG conditions (`ToyTwoPhase/Prog.lean`)

```lean
-- ToyTwoPhase/Prog.lean:130
def NoUnwind (p : Prog n) : Prop := ∀ i : Fin n, p.unw i = []

-- ToyTwoPhase/Prog.lean:134-135
def ReentryFree (p : Prog n) : Prop :=
  ∀ mid : List (Fin n), IsWalk p.succ (p.A :: (mid ++ [p.A])) → p.R ∈ mid

-- ToyTwoPhase/Prog.lean:151-153
def ActivationStaysReachable (p : Prog n) : Prop :=
  ∀ y ∈ p.succ p.R, y ≠ p.R → ∀ x : Fin n, x ≠ p.R →
    PathVia p.succ (fun z => z != p.A && z != p.R) y x → PathVia p.succ (fun z => z != p.R) x p.A

-- ToyTwoPhase/Prog.lean:160-162
def DomRegionReachesA (p : Prog n) : Prop :=
  ∀ y ∈ p.succ p.R, y ≠ p.R → ∀ x : Fin n, x ≠ p.R → Dom p.succ p.entry p.R x →
    PathVia p.succ (fun z => z != p.A && z != p.R) y x → PathVia p.succ (fun z => z != p.R) x p.A

-- ToyTwoPhase/Prog.lean:167-168
def IsCleanup (p : Prog n) (L : Fin n) : Prop :=
  ∃ x : Fin n, ∃ c ∈ p.unw x, PathVia p.edges (fun _ => true) c L

-- ToyTwoPhase/Prog.lean:171-172
def CleanupReadsUnderDeadLoan (p : Prog n) : Prop :=
  ∀ L : Fin n, IsCleanup p L → (p.op L).isRead = true → ¬ LoanLive p L
```

* `ReentryFree`: `A` cannot be re-executed along normal edges without passing `R`. Examples:
  `reentryFree_pos`, `reentryFree_neg`.
* `ActivationStaysReachable`: for every normal successor `y ≠ R` of `R` and every node `x ≠ R`
  reached from `y` along normal edges without passing `A` or `R` before `x`, some normal walk from `x`
  reaches `A` without passing `R` before `A`. Both `y = R` and `x = R` are excluded, so the condition
  constrains nodes other than `R`: a normal edge from a region node back to `R` (a `continue`) is
  admitted when that node can also reach `A` without passing `R` (`activationStaysReachable_pos_continue`,
  program `pContinue`), and a normal self-loop `R → R` contributes only the excluded case `y = R`.
  Because branching is nondeterministic this is a reachability condition: it excludes an early exit to
  an exit node, a region from which `A` is unreachable, and a region node whose every normal walk to
  `A` passes `R`; it admits loops between `R` and `A` from which `A` stays reachable. Examples:
  `activationStaysReachable_pos` (`pLoopOK`), `activationStaysReachable_pos_argLoop` (a loop inside
  the argument), `activationStaysReachable_pos_continue` (a `continue` back to `R`), and negatives for
  the three excluded shapes: `activationStaysReachable_neg_exit` (`pBreak`),
  `activationStaysReachable_neg_loopBack` (`pLoopBack`, whose node `4` reaches `A` only through `R`),
  `activationStaysReachable_neg_diverge` (`pDiverge`).
* `DomRegionReachesA`: `ActivationStaysReachable` restricted to nodes `x` that `R` dominates along
  normal edges. It is implied by `ActivationStaysReachable`
  (`domRegionReachesA_of_activationStaysReachable`), strictly weaker (`pJoin_separates_domRegionReachesA`:
  `pJoin` satisfies it and violates `ActivationStaysReachable`), and, with `ReentryFree` and no
  unwinding edges, sufficient for the conclusion of R2b
  (`isActiveDom_of_maybeActive_of_reentryFree_domRegionReachesA_noUnwind`, R2b card). No checker uses
  it as a guard. Examples: `domRegionReachesA_pos` (`pJoin`), `domRegionReachesA_neg` (`pBreak`).
* `IsCleanup`/`CleanupReadsUnderDeadLoan`: cleanup nodes are those reachable (along any edges) from
  the target of an unwinding edge, whose source may be any node; the condition says no cleanup node
  reads `x` while `r` is live. Examples: `isCleanup_pos`, `isCleanup_neg`,
  `cleanupReadsUnderDeadLoan_pos` (`pCleanupRead`), `cleanupReadsUnderDeadLoan_neg` (`pCleanup`).

### Reference semantics (`ToyTwoPhase/Semantics.lean`)

```lean
-- ToyTwoPhase/Semantics.lean:35-36
inductive Perm | none | reserved | active | frozen | invalid
  deriving DecidableEq, Repr

-- ToyTwoPhase/Semantics.lean:39-42
structure SSt where
  created : Bool
  dirty : Bool
  deriving DecidableEq, Repr

-- ToyTwoPhase/Semantics.lean:45-51
structure RState where
  perm : Perm
  sh0 : SSt
  sh1 : SSt
  deriving DecidableEq, Repr

namespace RState

-- ToyTwoPhase/Semantics.lean:53-55
def sh (σ : RState) : SRef → SSt
  | .s0 => σ.sh0
  | .s1 => σ.sh1

-- ToyTwoPhase/Semantics.lean:57-59
def setSh (σ : RState) : SRef → SSt → RState
  | .s0, t => { σ with sh0 := t }
  | .s1, t => { σ with sh1 := t }

-- ToyTwoPhase/Semantics.lean:62
def init : RState := ⟨.none, ⟨false, false⟩, ⟨false, false⟩⟩

-- ToyTwoPhase/Semantics.lean:67-71
inductive Outcome
  | ok (σ : RState)
  | halt
  | ub
  deriving DecidableEq, Repr

-- ToyTwoPhase/Semantics.lean:74-76
def foreignRead : Perm → Perm
  | .active => .frozen
  | q => q

-- ToyTwoPhase/Semantics.lean:79-81
def foreignWrite : Perm → Perm
  | .reserved | .active | .frozen => .invalid
  | q => q

-- ToyTwoPhase/Semantics.lean:83
def SSt.markWrite (t : SSt) : SSt := { t with dirty := t.dirty || t.created }

-- ToyTwoPhase/Semantics.lean:86-104
def exec : Op → RState → Outcome
  | .reserve, σ => .ok { σ with perm := .reserved }
  | .activate, σ =>
    match σ.perm with
    | .reserved | .active =>
      .ok { σ with perm := .active, sh0 := σ.sh0.markWrite, sh1 := σ.sh1.markWrite }
    | .none => .ok σ
    | .frozen | .invalid => .ub
  | .readX, σ => .ok { σ with perm := foreignRead σ.perm }
  | .borrowShared s, σ => .ok (({ σ with perm := foreignRead σ.perm } : RState).setSh s ⟨true, false⟩)
  | .useShared s, σ => if (σ.sh s).dirty then .ub else .ok { σ with perm := foreignRead σ.perm }
  | .writeX, σ => .ok { σ with perm := foreignWrite σ.perm }
  | .writeThrough, σ =>
    match σ.perm with
    | .active => .ok { σ with sh0 := σ.sh0.markWrite, sh1 := σ.sh1.markWrite }
    | .none | .reserved => .halt
    | .frozen | .invalid => .ub
  | .endLoan, σ => .ok { σ with perm := .none }
  | .nop, σ => .ok σ

-- ToyTwoPhase/Semantics.lean:107-113
def run (p : Prog n) : RState → List (Fin n) → Outcome
  | σ, [] => .ok σ
  | σ, i :: rest =>
    match exec (p.op i) σ with
    | .ok σ' => run p σ' rest
    | .halt => .halt
    | .ub => .ub

-- ToyTwoPhase/Semantics.lean:116-117
def Safe (p : Prog n) : Prop :=
  ∀ π : List (Fin n), IsWalk p.edges π → π.head? = some p.entry → run p RState.init π ≠ .ub

-- ToyTwoPhase/Semantics.lean:120-124
def ReachesUB (p : Prog n) (π : List (Fin n)) : Prop :=
  IsWalk p.edges π ∧ π.head? = some p.entry ∧ run p RState.init π = .ub

instance (p : Prog n) (π : List (Fin n)) : Decidable (ReachesUB p π) := by
  unfold ReachesUB; infer_instance
```

* Permissions of `r`: `none → reserved → active`, plus `frozen` and `invalid` (Tree Borrows'
  `Reserved`, `Unique` (formerly `Active`), `Frozen`, `Disabled`, simplified). A foreign write
  invalidates `r` while reserved, active or frozen; a foreign read (including `borrowShared` and
  `useShared`) freezes `r` while active; activating or writing through a `frozen`/`invalid` `r` is UB.
* The activation is the first write through `r`: from `reserved` or `active` it makes `r` active and
  marks every created shared reference dirty (`run_activate_marks_shared_dirty`); `useShared s` on a
  dirty `s` is UB. From `none` the activation is a no-op.
* Property of `exec` (`exec_foreignRead_of_reserved`): while `r` is reserved, a direct read, creating
  a shared reference, or using a clean shared reference causes no UB and leaves `r` reserved
  (non-vacuity `exec_foreignRead_of_reserved_hypotheses_hold_pPush`; tightness of `h`:
  `exec_readX_active_freezes`).
* **Modeling choice:** a `writeThrough` while `r` is `none` or `reserved` *halts* instead of being
  UB. It models that the program has no usable pointer yet (in the source language the `&mut` is
  obtained from the activation, e.g. as an `Option<&mut _>` that is `None` on the other paths, and
  unwrapping `None` stops the execution). `run_halt_reserved_writeThrough` shows the `break` walk of
  `pBreak` halting this way.
* `Safe p`: no walk from the entry (normal and unwinding edges) reaches UB. Positive `safe_pos`
  (`pPush`, by an inductive certificate checked by `certOK`, sound by `safe_of_cert`); negative
  `safe_neg` (`pBreak`).

### Checkers, analysis, repairs (`ToyTwoPhase/Checkers.lean`)

```lean
-- ToyTwoPhase/Checkers.lean:19-22
def Flagged (p : Prog n) (phase : Fin n → Prop) (L : Fin n) : Prop :=
  (p.op L = .writeX ∧ LoanLive p L) ∨
  ((p.op L).isRead = true ∧ LoanLive p L ∧ phase L) ∨
  (L = p.A ∧ (SharedLive p .s0 p.A ∨ SharedLive p .s1 p.A))

-- ToyTwoPhase/Checkers.lean:25-34
def Accepts (p : Prog n) (phase : Fin n → Prop) : Prop :=
  ∀ L : Fin n, ¬ Flagged p phase L

instance (p : Prog n) (phase : Fin n → Prop) [DecidablePred phase] (L : Fin n) :
    Decidable (Flagged p phase L) := by
  unfold Flagged; infer_instance

instance (p : Prog n) (phase : Fin n → Prop) [DecidablePred phase] :
    Decidable (Accepts p phase) := by
  unfold Accepts; infer_instance

-- ToyTwoPhase/Checkers.lean:38
def ExactPhaseAccepts (p : Prog n) : Prop := Accepts p (MaybeActive p)

-- ToyTwoPhase/Checkers.lean:41
def DominatorAccepts (p : Prog n) : Prop := Accepts p (IsActiveDom p)

-- ToyTwoPhase/Checkers.lean:44-50
def AlwaysActiveAccepts (p : Prog n) : Prop := Accepts p (fun _ => True)

instance (p : Prog n) : Decidable (ExactPhaseAccepts p) := by
  unfold ExactPhaseAccepts; infer_instance
instance (p : Prog n) : Decidable (DominatorAccepts p) := by unfold DominatorAccepts; infer_instance
instance (p : Prog n) : Decidable (AlwaysActiveAccepts p) := by
  unfold AlwaysActiveAccepts; infer_instance

-- ToyTwoPhase/Checkers.lean:55-59
def dfOut (p : Prog n) (P : Fin n) (inFact : Bool) : Bool :=
  match p.op P with
  | .activate => true
  | .reserve | .endLoan => false
  | _ => inFact

-- ToyTwoPhase/Checkers.lean:64-66
def dfStep (p : Prog n) (S : List (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun L =>
    (List.finRange n).any fun P => (p.edges P).contains L && dfOut p P (S.contains P)

-- ToyTwoPhase/Checkers.lean:69-71
def dfIter (p : Prog n) : Nat → List (Fin n)
  | 0 => []
  | k + 1 => dfStep p (dfIter p k)

-- ToyTwoPhase/Checkers.lean:75
def dfMaybeActive (p : Prog n) (L : Fin n) : Bool := (dfIter p n).contains L

-- ToyTwoPhase/Checkers.lean:78-81
def IterDataflowAccepts (p : Prog n) : Prop := Accepts p (fun L => dfMaybeActive p L = true)

instance (p : Prog n) : Decidable (IterDataflowAccepts p) := by
  unfold IterDataflowAccepts; infer_instance

-- ToyTwoPhase/Checkers.lean:87-89
def DomGuard (p : Prog n) : Prop := ReentryFree p ∧ ActivationStaysReachable p ∧ NoUnwind p

instance (p : Prog n) : Decidable (DomGuard p) := by unfold DomGuard; infer_instance

-- ToyTwoPhase/Checkers.lean:93-97
def guardedDomPhase (p : Prog n) (L : Fin n) : Prop :=
  if DomGuard p then IsActiveDom p L else True

instance (p : Prog n) : DecidablePred (guardedDomPhase p) := by
  intro L; unfold guardedDomPhase; infer_instance

-- ToyTwoPhase/Checkers.lean:99
def RepairBAccepts (p : Prog n) : Prop := Accepts p (guardedDomPhase p)

-- ToyTwoPhase/Checkers.lean:105
def RepairCAccepts (p : Prog n) : Prop := DomGuard p ∧ DominatorAccepts p

-- ToyTwoPhase/Checkers.lean:108-112
def literalPdomPhase (p : Prog n) (L : Fin n) : Prop :=
  if PDom p.succ p.A p.R then IsActiveDom p L else True

instance (p : Prog n) : DecidablePred (literalPdomPhase p) := by
  intro L; unfold literalPdomPhase; infer_instance

-- ToyTwoPhase/Checkers.lean:114-119
def LiteralRepairBAccepts (p : Prog n) : Prop := Accepts p (literalPdomPhase p)

instance (p : Prog n) : Decidable (RepairBAccepts p) := by unfold RepairBAccepts; infer_instance
instance (p : Prog n) : Decidable (RepairCAccepts p) := by unfold RepairCAccepts; infer_instance
instance (p : Prog n) : Decidable (LiteralRepairBAccepts p) := by
  unfold LiteralRepairBAccepts; infer_instance
```

* Every checker flags (1) every `writeX` under a live loan, (2) every read of `x` under a live loan
  that its phase test calls active, (3) the activation if a shared reference is live there (RFC
  2025's activation check). They differ in the phase test: the **exact-phase checker**
  (`ExactPhaseAccepts`, phase test `MaybeActive`, a walk-defined specification), the **iterative
  dataflow checker** (`IterDataflowAccepts`, phase test `dfMaybeActive`, `n` iterations of the forward
  may-analysis), and the **dominator checker** (`DominatorAccepts`, phase test `IsActiveDom`).
  Examples: `exactPhaseAccepts_pos`, `exactPhaseAccepts_neg`, `iterDataflowAccepts_pos`,
  `iterDataflowAccepts_neg`, `dominatorAccepts_pos`, `dominatorAccepts_neg`, `alwaysActiveAccepts_pos`,
  `alwaysActiveAccepts_neg` (without two-phase treatment `pPush` is rejected), `dfMaybeActive_pos`,
  `dfMaybeActive_neg`.
* Repairs: (a) the exact-phase or iterative dataflow checker; (b) the dominator test guarded by the
  decidable `DomGuard`, falling back to "always active" (`RepairBAccepts`; examples
  `repairBAccepts_pos`, `repairBAccepts_pos_noGuard`, `repairBAccepts_neg`); (c) reject every
  program violating `DomGuard`, else the dominator checker (`RepairCAccepts`; examples
  `repairCAccepts_pos`, `repairCAccepts_pos_argLoop`, `repairCAccepts_neg`). `DomGuard` examples:
  `domGuard_pos`, `domGuard_pos_argLoop`, `domGuard_pos_continue`, `domGuard_neg`. The literal form of (b), guarded by
  `A pdom R` alone (`LiteralRepairBAccepts`), is kept to record that it is unsound (R5d).

### Example programs (`ToyTwoPhase/Programs.lean`)

Node 0 is the entry; `→` normal edges, `⇢` unwinding edges. Definitions are quoted under Evidence.

| Program | Shape | Role |
| :--- | :--- | :--- |
| `pPush` | `0 → R=1 → 2: readX → A=3 → 4: writeThrough` | `v.push(v.len())`; safe, accepted |
| `pLoopOK` | `0 → R=1 → 2: readX → A=3 → 4: writeThrough → {1, 5}` | looping, `DomGuard` holds |
| `pArgLoop` | `0 → R=1 → 2: readX → {2, A=3}`, `3 → 4: writeThrough` | loop inside the argument, `DomGuard` holds |
| `pContinue` | `0 → R=1 → 2: readX → {1, A=3}`, `3 → 4: writeThrough` | `continue` back to `R` inside the argument, `DomGuard` holds |
| `pBreak` | `0 → R=1 → 2 → {A=3, J=4}`, `3 → 4`, `4: borrowShared s0 → 5: useShared s0 → 6: writeThrough → 7: useShared s0` | early exit (`2 → 4` is the `break`) |
| `pBreakHoisted` | `0 → 1 → {R=2, 4}`, `2 → A=3 → 4`, same tail | break hoisted above `R` |
| `pBreakWrite` | `pBreak` with `4: writeX` and `5, 7: nop` | write at the join |
| `pBreakDead` | `0 → R=1 → 2 → {A=3, J=4}`, `3 → 4`, `4: readX → 5` | early exit, `r` dead at `J` |
| `pLoop1` | `0 → R=1 → 2: readX → A=3 → {2, 4}` | `A` re-enters the region |
| `pLoopBack` | `0 → R=1 → 2 → {A=3, 4}`, `3 → {4, 6}`, `4: readX → 5: writeThrough → 1` | break target loops back to `R` and reaches `A` only through `R` |
| `pDiverge` | as `pLoopBack` but `5 → 4` | break target enters a cycle avoiding `A` |
| `pJoin` | `0 → 1 → {R=2, J=5}`, `2 → {A=3, 5}`, `3 → 6`, `5: readX → 6: writeThrough → 7` | join of loan-free path and reserved region |
| `pEndThenRead` | `0 → R=1 → A=2 → 3: endLoan → 4: readX → 5: writeThrough` | read after loan end |
| `pEndBeforeA` | `0 → R=1 → 2: endLoan → A=3 → 4: readX` | activation without a reservation |
| `pWriteDuringRes` | `0 → R=1 → 2: writeX → A=3 → 4: writeThrough` | write during reservation |
| `pSharedDuringRes` | `0 → R=1 → 2: borrowShared s0 → A=3 → 4: useShared s0` | shared reborrow during reservation |
| `pCleanup` | `0 → R=1 → 2 → A=3 → 4 → 5`, `2 ⇢ 6`, `4 ⇢ 6`, `6: readX → 7: writeThrough → 8` | cleanup read under live loan |
| `pCleanupRead` | `0 → R=1 → 2: readX → A=3 → 4: writeThrough → 5`, `2 ⇢ 6`, `4 ⇢ 6`, `6: readX → 7` | cleanup read under dead loan |
| `pUnreachA` | `0 → R=1 → 2`; `A=3 → 4: readX` | `A` unreachable |
| `pUnreachMerge` | `0 → 3: readX → 4: writeThrough`; `R=1 → A=2 → 3` | `A` unreachable, flows into reachable code |

## Findings

### Results at a glance

| Id | Lean name(s) | Kind | Tier | Depth |
| :--- | :--- | :--- | :--- | :--- |
| R1a | `dfMaybeActive_iff_maybeActive_of_activation_reachable` | characterization | T0 | substantive |
| R1b | `exactPhaseAccepts_safe` | theorem | T1 | substantive |
| R1c | `iterDataflowAccepts_exactPhaseAccepts`, `iterDataflowAccepts_safe` | theorem | T1 | shallow |
| R1d | `iterDataflowAccepts_iff_exactPhaseAccepts_of_activation_reachable` | characterization | T0 | shallow |
| R2 | `rdomA_apdomR_noUnwind_reentryFree_insufficient_pLoopBack`, `rdomA_apdomR_noUnwind_insufficient_pLoop1`, `rdomA_apdomR_noUnwind_reentryFree_insufficient_pDiverge` | counterexample | T1 | definitional |
| R2a | `isActiveDom_of_maybeActive_of_acyclic_pdom_noUnwind` | theorem | T1 | shallow |
| R2b | `isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_noUnwind` | theorem | T1 | substantive |
| R2c | `dominatorAccepts_safe_of_reentryFree_activationStaysReachable_noUnwind` | theorem | T1 | shallow |
| R3 | `pBreak_dominatorAccepts_unsafe` | counterexample | T1 | definitional |
| R4 | `pJoin_safe_exactPhaseAccepts_not_dominatorAccepts` | counterexample | T1 | definitional |
| R5a | `repairBAccepts_exactPhaseAccepts`, `repairBAccepts_safe` | theorem | T1 | shallow |
| R5c | `repairCAccepts_repairBAccepts`, `repairs_strict` | theorem | T1 | definitional |
| R5d | `literalRepairB_unsound_pLoopBack` | counterexample | T1 | definitional |
| R6b | `pWriteDuringRes_ub_rejected` | counterexample | T0 | definitional |
| R6c | `pSharedDuringRes_ub_rejected` | counterexample | T0 | definitional |
| R7a | `isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_not_isCleanup` | theorem | T1 | shallow |
| R7b | `pCleanup_dominatorAccepts_unsafe` | counterexample | T1 | definitional |
| R7c | `dominatorAccepts_safe_of_reentryFree_activationStaysReachable_cleanupReadsUnderDeadLoan` | theorem | T1 | shallow |

Every theorem listed is fully proved.

### R1a — the forward may-analysis computes the path-level phase fact

```lean
-- ToyTwoPhase/Results.lean:39-41
theorem dfMaybeActive_iff_maybeActive_of_activation_reachable (p : Prog n)
    (hreach : PathVia p.edges (fun _ => true) p.entry p.A) (L : Fin n) :
    dfMaybeActive p L = true ↔ MaybeActive p L := by …
```

* **Plain claim.** For every toy program in which `A` is reachable from the entry, and every node `L`, the forward may-analysis (generate at `A`, kill at `R` and at `endLoan`, join by disjunction over all edges, `n` iterations from all-`false`) yields `true` at `L` exactly when `MaybeActive p L` holds; both are in-facts, describing the point just before `L` executes.
* **Tier.** T0 — the least fixpoint of a distributive gen/kill problem equals its meet-over-paths solution at reachable points (Kildall 1973; Kam and Ullman 1977; mechanized in general form in CompCert), restated for this phase fact.
* **Depth.** substantive (soundness by induction on iterations; completeness by induction on walks; stabilization within `n` iterations by a cardinality argument on sublists of `Fin n`).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `hreach : PathVia p.edges (fun _ => true) p.entry p.A` | the analysis also propagates facts generated at an unreachable A, which no walk from the entry supports | tight: `dfMaybeActive_ne_maybeActive_pUnreachA` (a 5-node program without cycles in which A is unreachable) |

* **Non-vacuity.** `dfMaybeActive_hypotheses_hold_pBreak` — `A` is reachable in `pBreak`, and the equivalence holds at all 8 nodes.
* **Non-claims.**
  * `dfMaybeActive p L` and `MaybeActive p L` are in-facts, not out-facts: in `pLoopOK`, `MaybeActive` holds at `R` and fails at `A` (`maybeActive_in_fact_pLoopOK`).
  * `MaybeActive` is a path fact, not a semantic one: it does not check that `R` executed before the `A` it starts from, so it can hold where the permission of `r` is never `active` (`maybeActive_pEndBeforeA_run_init`).
  * It is not a statement about rustc's `Borrows` analysis (`compiler/rustc_borrowck/src/dataflow.rs`), a gen/kill dataflow over borrows that kills a borrow where it goes out of scope, a different fact (source).
  * Without `hreach`, the one-way implication `MaybeActive p L → dfMaybeActive p L = true` still holds (`dfMaybeActive_of_maybeActive`); the converse fails (`dfMaybeActive_ne_maybeActive_pUnreachA`).
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** G. A. Kildall, "A Unified Approach to Global Program Optimization", POPL 1973, pp. 194-206, https://doi.org/10.1145/512927.512945; J. B. Kam, J. D. Ullman, "Monotone Data Flow Analysis Frameworks", Acta Informatica 7(3), 1977, pp. 305-317, https://doi.org/10.1007/BF00290339; X. Leroy, "Formal Verification of a Realistic Compiler", Commun. ACM 52(7), 2009, pp. 107-115, https://doi.org/10.1145/1538788.1538814 (CompCert; Kildall's solver mechanized in backend/Kildall.v).
* **Design question.** Can the path-level phase fact be computed by an ordinary forward dataflow pass?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:47-49
theorem dfMaybeActive_ne_maybeActive_pUnreachA :
    ¬ PathVia pUnreachA.edges (fun _ => true) pUnreachA.entry pUnreachA.A ∧
      dfMaybeActive pUnreachA 4 = true ∧ ¬ MaybeActive pUnreachA 4 := by …

-- ToyTwoPhase/Results.lean:54-56
theorem dfMaybeActive_hypotheses_hold_pBreak :
    PathVia pBreak.edges (fun _ => true) pBreak.entry pBreak.A ∧
      ∀ L : Fin 8, (dfMaybeActive pBreak L = true ↔ MaybeActive pBreak L) := by …
```

### R1b — the exact-phase checker is sound

```lean
-- ToyTwoPhase/Results.lean:63
theorem exactPhaseAccepts_safe (p : Prog n) (h : ExactPhaseAccepts p) : Safe p := by …
```

* **Plain claim.** For every toy program (loops and unwinding edges allowed): if the exact-phase checker accepts it — no `writeX` under a live loan, no read of `x` (`readX`, `borrowShared`) under a live loan where `MaybeActive` holds, and no shared reference live at `A` — then no walk from the entry reaches UB in the reference semantics.
* **Tier.** T1 — RFC 2025's rule that reads and shared borrows of the borrowed data are permitted during the reservation phase (quoted in Evidence, Prior art) made precise against a semantics in the style of Tree Borrows' `Reserved` permission; Tree Borrows mechanizes its own semantics, not a borrow-checker phase test.
* **Depth.** substantive (a forward run invariant `RunInv` relating the permission of `r` and the dirty flags to `LoanLive`, `MaybeActive` and `SharedLive`, preserved by every step under the checker's acceptance; `run_ne_ub_of_runInv`).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `h : ExactPhaseAccepts p` | the checker's verdict (the premise) | tight: `exactPhaseAccepts_tight_pBreak` (an 8-node acyclic program without unwinding edges) |

* **Non-vacuity.** `exactPhaseAccepts_hypotheses_hold_pPush` — `v.push(v.len())` (`pPush`), which reads during the reservation, is accepted; without two-phase treatment it is rejected (`alwaysActiveAccepts_neg`).
* **Non-claims.**
  * Safety relies on the toy rule that `writeThrough` while `r` is `none` or `reserved` halts instead of being UB; under a rule making that UB, the program `0 → R=1 → 2: writeThrough → A=3` (no access to `x`) would be accepted and unsafe (not proved here).
  * `Safe` models one two-phase loan `r` with one reservation node and one activation node; it does not cover several interacting loans, a two-phase borrow whose single use is not an activation (rustc's `TwoPhaseActivation::NotActivated` case), or conflicts between shared references and direct writes to `x`.
  * `useShared s` on a never-created `s` is treated as a plain foreign read; programs are not required to create `s` before using it.
  * R1b concerns the exact-phase checker, whose phase test is the walk-defined `MaybeActive`; the iterative checker is treated in R1c and R1d.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** RFC 2025 (rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2025-nested-method-calls.md, feature name nested_method_call); N. Villani, J. Hostert, D. Dreyer, R. Jung, "Tree Borrows", Proc. ACM Program. Lang. 9 (PLDI), Article 188, 2025, https://doi.org/10.1145/3735592 (operational semantics mechanized in Rocq); S. Ho, J. Protzenko, "Aeneas: Rust Verification by Functional Translation", Proc. ACM Program. Lang. 6 (ICFP), Article 116, 2022, https://doi.org/10.1145/3547647 (preprint arXiv:2206.07185): reserved borrows in a value-level semantics.
* **Design question.** Is phase information (plus the activation check) enough to justify reads during a reservation?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:72
theorem exactPhaseAccepts_tight_pBreak : ¬ ExactPhaseAccepts pBreak ∧ ¬ Safe pBreak := …

-- ToyTwoPhase/Results.lean:76
theorem exactPhaseAccepts_hypotheses_hold_pPush : ExactPhaseAccepts pPush := by decide
```

### R1c — the iterative dataflow checker is sound

```lean
-- ToyTwoPhase/Results.lean:82-83
theorem iterDataflowAccepts_exactPhaseAccepts (p : Prog n) (h : IterDataflowAccepts p) :
    ExactPhaseAccepts p := …

-- ToyTwoPhase/Results.lean:87
theorem iterDataflowAccepts_safe (p : Prog n) (h : IterDataflowAccepts p) : Safe p := …
```

* **Plain claim.** For every toy program: if the iterative dataflow checker (phase test `dfMaybeActive`) accepts it, then the exact-phase checker accepts it, and no walk from the entry reaches UB.
* **Tier.** T1 — as R1b, for the checker that runs the forward may-analysis.
* **Depth.** shallow (from `dfMaybeActive_of_maybeActive`, `accepts_of_phase_imp` and R1b).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `h : IterDataflowAccepts p` | the checker's verdict (the premise) | tight: `iterDataflowAccepts_tight_pBreak` (an 8-node acyclic program without unwinding edges) |

* **Non-vacuity.** `iterDataflowAccepts_hypotheses_hold_pPush` — `pPush` is accepted by the iterative dataflow checker.
* **Non-claims.**
  * Without `A` reachable, the converse inclusion can fail (R1d): `pUnreachMerge` is accepted by the exact-phase checker and rejected by the iterative one (`exactPhaseAccepts_not_iterDataflowAccepts_pUnreachMerge`).
  * Safety relies on the toy rule that `writeThrough` while `r` is `none` or `reserved` halts instead of being UB; under a rule making that UB, the program `0 → R=1 → 2: writeThrough → A=3` (no access to `x`) would be accepted and unsafe (not proved here).
  * `Safe` models one two-phase loan `r` with one reservation node and one activation node; it does not cover several interacting loans, a two-phase borrow whose single use is not an activation (rustc's `TwoPhaseActivation::NotActivated` case), or conflicts between shared references and direct writes to `x`.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** G. A. Kildall, "A Unified Approach to Global Program Optimization", POPL 1973, pp. 194-206, https://doi.org/10.1145/512927.512945; RFC 2025 (rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2025-nested-method-calls.md, feature name nested_method_call).
* **Design question.** Is a checker built on an ordinary forward dataflow pass sound against the reference semantics?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:92-93
theorem iterDataflowAccepts_tight_pBreak :
    ¬ IterDataflowAccepts pBreak ∧ ¬ ExactPhaseAccepts pBreak ∧ ¬ Safe pBreak := …

-- ToyTwoPhase/Results.lean:97
theorem iterDataflowAccepts_hypotheses_hold_pPush : IterDataflowAccepts pPush := by decide
```

### R1d — with `A` reachable, the two dataflow-style checkers coincide

```lean
-- ToyTwoPhase/Results.lean:103-105
theorem iterDataflowAccepts_iff_exactPhaseAccepts_of_activation_reachable (p : Prog n)
    (hreach : PathVia p.edges (fun _ => true) p.entry p.A) :
    IterDataflowAccepts p ↔ ExactPhaseAccepts p := …
```

* **Plain claim.** For every toy program in which `A` is reachable from the entry, the iterative dataflow checker accepts it if and only if the exact-phase checker accepts it.
* **Tier.** T0 — a direct consequence of R1a (meet-over-paths equals the fixpoint at reachable points).
* **Depth.** shallow (from R1a and `accepts_of_phase_imp`).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `hreach : PathVia p.edges (fun _ => true) p.entry p.A` | with A unreachable the iterative analysis over-reports and its checker rejects more | tight: `exactPhaseAccepts_not_iterDataflowAccepts_pUnreachMerge` (a 5-node program without cycles in which A is unreachable) |

* **Non-vacuity.** `iterDataflowAccepts_iff_hypotheses_hold_pPush` — `A` is reachable in `pPush`.
* **Non-claims.**
  * When `A` is unreachable, the converse of R1c can fail (`exactPhaseAccepts_not_iterDataflowAccepts_pUnreachMerge`).
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** G. A. Kildall, "A Unified Approach to Global Program Optimization", POPL 1973, pp. 194-206, https://doi.org/10.1145/512927.512945; J. B. Kam, J. D. Ullman, "Monotone Data Flow Analysis Frameworks", Acta Informatica 7(3), 1977, pp. 305-317, https://doi.org/10.1007/BF00290339.
* **Design question.** Does the iterative pass lose precision against the walk-defined phase test?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:112-115
theorem exactPhaseAccepts_not_iterDataflowAccepts_pUnreachMerge :
    ¬ PathVia pUnreachMerge.edges (fun _ => true) pUnreachMerge.entry pUnreachMerge.A ∧
      ExactPhaseAccepts pUnreachMerge ∧ ¬ IterDataflowAccepts pUnreachMerge ∧
      Safe pUnreachMerge := …

-- ToyTwoPhase/Results.lean:121-122
theorem iterDataflowAccepts_iff_hypotheses_hold_pPush :
    PathVia pPush.edges (fun _ => true) pPush.entry pPush.A := by decide
```

### R2 — dominance and post-dominance of the activation do not suffice in looping CFGs

```lean
-- ToyTwoPhase/Results.lean:130-135
theorem rdomA_apdomR_noUnwind_reentryFree_insufficient_pLoopBack :
    Dom pLoopBack.edges pLoopBack.entry pLoopBack.R pLoopBack.A ∧
      PDom pLoopBack.succ pLoopBack.A pLoopBack.R ∧ NoUnwind pLoopBack ∧
      ReentryFree pLoopBack ∧
      LoanLive pLoopBack 4 ∧ MaybeActive pLoopBack 4 ∧ ¬ IsActiveDom pLoopBack 4 ∧
      DominatorAccepts pLoopBack ∧ ReachesUB pLoopBack [0, 1, 2, 3, 4, 5] := by …

-- ToyTwoPhase/Results.lean:140-144
theorem rdomA_apdomR_noUnwind_insufficient_pLoop1 :
    Dom pLoop1.edges pLoop1.entry pLoop1.R pLoop1.A ∧ PDom pLoop1.succ pLoop1.A pLoop1.R ∧
      NoUnwind pLoop1 ∧ ActivationStaysReachable pLoop1 ∧ ¬ ReentryFree pLoop1 ∧
      LoanLive pLoop1 2 ∧ MaybeActive pLoop1 2 ∧ ¬ IsActiveDom pLoop1 2 ∧
      DominatorAccepts pLoop1 ∧ ReachesUB pLoop1 [0, 1, 2, 3, 2, 3] := by …

-- ToyTwoPhase/Results.lean:149-154
theorem rdomA_apdomR_noUnwind_reentryFree_insufficient_pDiverge :
    Dom pDiverge.edges pDiverge.entry pDiverge.R pDiverge.A ∧
      PDom pDiverge.succ pDiverge.A pDiverge.R ∧ NoUnwind pDiverge ∧ ReentryFree pDiverge ∧
      ¬ ActivationStaysReachable pDiverge ∧
      LoanLive pDiverge 4 ∧ MaybeActive pDiverge 4 ∧ ¬ IsActiveDom pDiverge 4 ∧
      DominatorAccepts pDiverge ∧ ReachesUB pDiverge [0, 1, 2, 3, 4, 5] := by …
```

* **Plain claim.** There is a 7-node looping toy program (`pLoopBack`) in which `R` dominates `A`, `A` post-dominates `R` along normal edges, there are no unwinding edges, and every normal walk from `A` back to `A` passes `R`, yet at the read at node 4 the loan is live and may be active while the dominator test calls it reserved, the dominator checker accepts, and the walk `0,1,2,3,4,5` reaches UB. Two further programs show the same: `pLoop1` (5 nodes; `A` re-enters the region without passing `R`, while `ActivationStaysReachable` holds) and `pDiverge` (7 nodes; the `break` target enters a cycle from which `A` is unreachable).
* **Tier.** T1 — exit-based post-dominance says nothing about walks that loop back or never reach an exit, a classical observation (Podgurski and Clarke 1990; Ranganath et al. 2007), instantiated here for the dominator phase test.
* **Depth.** definitional (kernel evaluation of decidable checkers on concrete programs).
* **Hypothesis ledger.** Not applicable (counterexample); every listed property of the program is proved.
* **Positive control.** `dominatorAccepts_safe_pLoopOK` — `pLoopOK`, a looping program satisfying `DomGuard`, is accepted by the dominator checker and is safe.
* **Non-claims.**
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. The package does not claim that rustc accepts any program corresponding to `pLoopBack`, `pLoop1` or `pDiverge`. Model–system relation: none proved.
  * Escape hatches: the three counterexamples are excluded by an acyclic normal CFG (R2a), and by `ReentryFree` together with `ActivationStaysReachable` and no unwinding edges (R2b, R2c). Excluding infeasible paths by a path-sensitive analysis is not examined.
  * R2 does not refute the dominator test under those stronger conditions (R2a, R2b).
* **Prior art.** A. Podgurski, L. A. Clarke, "A Formal Model of Program Dependences and Its Implications for Software Testing, Debugging, and Maintenance", IEEE TSE 16(9), 1990, pp. 965-979, https://doi.org/10.1109/32.58784 (weak control dependence via strong post-dominance, which bounds path length and so accounts for loops); V. P. Ranganath, T. Amtoft, A. Banerjee, J. Hatcliff, M. B. Dwyer, "A New Foundation for Control Dependence and Slicing for Modern Program Structures", ACM TOPLAS 29(5), Article 27, 2007, https://doi.org/10.1145/1275497.1275502 (control dependence for CFGs with non-termination and no unique exit); D. Wasserrab, "Towards Certified Slicing", Archive of Formal Proofs, 2008, https://isa-afp.org/entries/Slicing.html (post-dominance and weak control dependence mechanized in Isabelle/HOL).
* **Design question.** Which CFG conditions make the dominator phase test sound?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:159
theorem dominatorAccepts_safe_pLoopOK : DomGuard pLoopOK ∧ DominatorAccepts pLoopOK ∧ Safe pLoopOK := …
```

### R2a — acyclic CFGs: post-dominance suffices

```lean
-- ToyTwoPhase/Results.lean:205-207
theorem isActiveDom_of_maybeActive_of_acyclic_pdom_noUnwind (p : Prog n)
    (hac : Acyclic p.succ) (hpd : PDom p.succ p.A p.R) (hnu : NoUnwind p)
    (L : Fin n) (hL : MaybeActive p L) : IsActiveDom p L := …
```

* **Plain claim.** For a toy program whose normal-edge CFG is acyclic, in which `A` post-dominates `R` along normal edges and which has no unwinding edges, at every node where the loan may be active the dominator test calls the loan active.
* **Tier.** T1 — the intended dominance argument, made precise for acyclic CFGs.
* **Depth.** shallow given R2b's argument: acyclicity gives `ReentryFree` (`reentryFree_of_acyclic`), and acyclicity with post-dominance gives `ActivationStaysReachable` (`activationStaysReachable_of_acyclic_pdom`, by extending walks until they reach `A`).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `hac : Acyclic p.succ` | back edges let A reach the region without R | tight: `acyclic_tight_pLoop1` (a 5-node program whose normal CFG has one cycle (A → 2) and no unwinding edges) |
  | `hpd : PDom p.succ p.A p.R` | an early exit from between R and A creates a join reached both from the region and from after A | tight: `pdom_tight_pBreak` (an 8-node acyclic program without unwinding edges) |
  | `hnu : NoUnwind p` | unwinding edges into a shared cleanup block create such a join; dominance uses all edges | tight: `unwinding_tight_pCleanup` (a 9-node program with acyclic normal edges and two unwinding edges into one cleanup block) |
  | `hL : MaybeActive p L` | between R and A the dominator test calls the loan reserved | tight: `maybeActive_tight_pPush` (a 5-node straight-line program without unwinding edges) |

* **Non-vacuity.** `acyclic_pdom_hypotheses_hold_pPush` — `pPush` satisfies all hypotheses, at node 4.
* **Non-claims.**
  * `R` dominating `A` is not a hypothesis. In the toy this is possible because `IsActiveDom p L` holds wherever `R` does not strictly dominate `L` and `exec .activate` on a `none` permission is a no-op; this neither establishes nor refutes that `R` dominating `A` can be dropped in rustc or in a semantics where activating an unreserved borrow is UB.
  * Liveness is not a hypothesis.
  * It says nothing about cyclic CFGs; R2 shows `PDom` is then insufficient.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396; A. Podgurski, L. A. Clarke, "A Formal Model of Program Dependences and Its Implications for Software Testing, Debugging, and Maintenance", IEEE TSE 16(9), 1990, pp. 965-979, https://doi.org/10.1109/32.58784 (weak control dependence via strong post-dominance, which bounds path length and so accounts for loops).
* **Design question.** Which CFG conditions make the dominator phase test sound?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:213-215
theorem acyclic_tight_pLoop1 :
    ¬ Acyclic pLoop1.succ ∧ PDom pLoop1.succ pLoop1.A pLoop1.R ∧ NoUnwind pLoop1 ∧
      MaybeActive pLoop1 2 ∧ ¬ IsActiveDom pLoop1 2 := by …

-- ToyTwoPhase/Results.lean:219-221
theorem pdom_tight_pBreak :
    Acyclic pBreak.succ ∧ ¬ PDom pBreak.succ pBreak.A pBreak.R ∧ NoUnwind pBreak ∧
      MaybeActive pBreak 4 ∧ ¬ IsActiveDom pBreak 4 := by …

-- ToyTwoPhase/Results.lean:185-189
theorem unwinding_tight_pCleanup :
    (Acyclic pCleanup.succ ∧ PDom pCleanup.succ pCleanup.A pCleanup.R ∧
      ReentryFree pCleanup ∧ ActivationStaysReachable pCleanup ∧ ¬ NoUnwind pCleanup ∧
      IsCleanup pCleanup 6 ∧ ¬ CleanupReadsUnderDeadLoan pCleanup ∧ MaybeActive pCleanup 6 ∧
      ¬ IsActiveDom pCleanup 6 ∧ DominatorAccepts pCleanup) ∧ ¬ Safe pCleanup := …

-- ToyTwoPhase/Results.lean:225-227
theorem maybeActive_tight_pPush :
    Acyclic pPush.succ ∧ PDom pPush.succ pPush.A pPush.R ∧ NoUnwind pPush ∧
      ¬ MaybeActive pPush 2 ∧ ¬ IsActiveDom pPush 2 := by …

-- ToyTwoPhase/Results.lean:231-233
theorem acyclic_pdom_hypotheses_hold_pPush :
    Acyclic pPush.succ ∧ PDom pPush.succ pPush.A pPush.R ∧ NoUnwind pPush ∧
      MaybeActive pPush 4 := by …
```

### R2b — looping CFGs: re-entry freedom and a reachable activation suffice

```lean
-- ToyTwoPhase/Results.lean:243-245
theorem isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_noUnwind
    (p : Prog n) (hre : ReentryFree p) (hasr : ActivationStaysReachable p) (hnu : NoUnwind p)
    (L : Fin n) (hL : MaybeActive p L) : IsActiveDom p L := …
```

* **Plain claim.** For a toy program in which every normal walk from `A` back to `A` passes `R` (`ReentryFree`), every node `x ≠ R` reached from a normal successor `y ≠ R` of `R` along normal edges without passing `A` or `R` before `x` can still reach `A` along normal edges without passing `R` (`ActivationStaysReachable`), and which has no unwinding edges, at every node where the loan may be active the dominator test calls the loan active.
* **Tier.** T1 — the intended dominance argument, made precise for looping CFGs under this package's conditions.
* **Depth.** substantive (`isActiveDom_of_maybeActive_of_succWalks`: a walk to `L` avoiding `A` passes `R`; from its last `R`, `ActivationStaysReachable` leads back to `A` avoiding `R`, and with the kill-free walk from `A` to `L` this gives a walk from `A` to `A` avoiding `R`, contradicting `ReentryFree`).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `hre : ReentryFree p` | A re-entering the region without R reaches region nodes after activation | tight: `reentryFree_tight_pLoop1` (a 5-node program whose normal CFG has one cycle (A → 2) and no unwinding edges) |
  | `hasr : ActivationStaysReachable p` | an early exit, an exit back to R from a region node that cannot reach A without passing R, or a region from which A is unreachable creates a join reachable from both sides | tight: `activationStaysReachable_tight_pLoopBack` (a 7-node program whose `break` target loops back to R, with no unwinding edges) |
  | `hnu : NoUnwind p` | as in R2a | tight: `unwinding_tight_pCleanup` (a 9-node program with acyclic normal edges and two unwinding edges into one cleanup block) |
  | `hL : MaybeActive p L` | between R and A the dominator test calls the loan reserved | tight: `maybeActive_tight_pLoopOK` (a 6-node program with one cycle through R and no unwinding edges) |

* **Non-vacuity.** `reentryFree_activationStaysReachable_hypotheses_hold_pArgLoop` — `pArgLoop` (a loop between `R` and `A`; cyclic normal CFG) satisfies all hypotheses, at node 4.
* **Non-claims.**
  * `ActivationStaysReachable` is a reachability condition over nondeterministic branching: it does not ask loops between `R` and `A` to terminate, and it admits a loop inside the argument from which `A` stays reachable (`activationStaysReachable_pos_argLoop`) and a `continue` back to `R` from a region node that can still reach `A` without passing `R` (`reentryFree_activationStaysReachable_hypotheses_hold_pContinue`: `pContinue` satisfies all hypotheses at node 4, satisfies `DomGuard`, is accepted by the dominator checker and by repairs (b) and (c), and is safe).
  * `R` dominating `A` is not a hypothesis. In the toy this is possible because `IsActiveDom p L` holds wherever `R` does not strictly dominate `L` and `exec .activate` on a `none` permission is a no-op; this neither establishes nor refutes that `R` dominating `A` can be dropped in rustc or in a semantics where activating an unreserved borrow is UB.
  * `ActivationStaysReachable` is a sufficient condition, not the weakest condition on the CFG alone: `DomRegionReachesA`, its restriction to nodes dominated by `R` along normal edges, is strictly weaker (`pJoin_separates_domRegionReachesA`) and also yields the conclusion together with `ReentryFree` and no unwinding edges (`isActiveDom_of_maybeActive_of_reentryFree_domRegionReachesA_noUnwind`, by the same walk argument, `isActiveDom_of_maybeActive_of_domRegion`). No minimality claim is made for either condition. Each listed hypothesis is tight in the sense of the ledger.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396; A. Podgurski, L. A. Clarke, "A Formal Model of Program Dependences and Its Implications for Software Testing, Debugging, and Maintenance", IEEE TSE 16(9), 1990, pp. 965-979, https://doi.org/10.1109/32.58784 (weak control dependence via strong post-dominance, which bounds path length and so accounts for loops); V. P. Ranganath, T. Amtoft, A. Banerjee, J. Hatcliff, M. B. Dwyer, "A New Foundation for Control Dependence and Slicing for Modern Program Structures", ACM TOPLAS 29(5), Article 27, 2007, https://doi.org/10.1145/1275497.1275502 (control dependence for CFGs with non-termination and no unique exit).
* **Design question.** Which CFG conditions make the dominator phase test sound?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:167-170
theorem reentryFree_tight_pLoop1 :
    (¬ ReentryFree pLoop1 ∧ ActivationStaysReachable pLoop1 ∧ NoUnwind pLoop1 ∧
      ¬ IsCleanup pLoop1 2 ∧ CleanupReadsUnderDeadLoan pLoop1 ∧ MaybeActive pLoop1 2 ∧
      ¬ IsActiveDom pLoop1 2 ∧ DominatorAccepts pLoop1) ∧ ¬ Safe pLoop1 := …

-- ToyTwoPhase/Results.lean:175-178
theorem activationStaysReachable_tight_pLoopBack :
    (ReentryFree pLoopBack ∧ ¬ ActivationStaysReachable pLoopBack ∧ NoUnwind pLoopBack ∧
      ¬ IsCleanup pLoopBack 4 ∧ CleanupReadsUnderDeadLoan pLoopBack ∧ MaybeActive pLoopBack 4 ∧
      ¬ IsActiveDom pLoopBack 4 ∧ DominatorAccepts pLoopBack) ∧ ¬ Safe pLoopBack := …

-- ToyTwoPhase/Results.lean:250-252
theorem maybeActive_tight_pLoopOK :
    ReentryFree pLoopOK ∧ ActivationStaysReachable pLoopOK ∧ NoUnwind pLoopOK ∧
      ¬ MaybeActive pLoopOK 2 ∧ ¬ IsActiveDom pLoopOK 2 := by …

-- ToyTwoPhase/Results.lean:257-259
theorem reentryFree_activationStaysReachable_hypotheses_hold_pArgLoop :
    ReentryFree pArgLoop ∧ ActivationStaysReachable pArgLoop ∧ NoUnwind pArgLoop ∧
      ¬ Acyclic pArgLoop.succ ∧ MaybeActive pArgLoop 4 := by …

-- ToyTwoPhase/Results.lean:265-268
theorem reentryFree_activationStaysReachable_hypotheses_hold_pContinue :
    ReentryFree pContinue ∧ ActivationStaysReachable pContinue ∧ NoUnwind pContinue ∧
      MaybeActive pContinue 4 ∧ DomGuard pContinue ∧ DominatorAccepts pContinue ∧
      RepairBAccepts pContinue ∧ RepairCAccepts pContinue ∧ Safe pContinue := …

-- ToyTwoPhase/Results.lean:276-278
theorem isActiveDom_of_maybeActive_of_reentryFree_domRegionReachesA_noUnwind
    (p : Prog n) (hre : ReentryFree p) (hdr : DomRegionReachesA p) (hnu : NoUnwind p)
    (L : Fin n) (hL : MaybeActive p L) : IsActiveDom p L := …

-- ToyTwoPhase/Results.lean:284-286
theorem pJoin_separates_domRegionReachesA :
    (ReentryFree pJoin ∧ DomRegionReachesA pJoin ∧ NoUnwind pJoin ∧ MaybeActive pJoin 6) ∧
      ¬ ActivationStaysReachable pJoin := by …
```

### R2c — the dominator checker is sound under the R2b conditions

```lean
-- ToyTwoPhase/Results.lean:293-295
theorem dominatorAccepts_safe_of_reentryFree_activationStaysReachable_noUnwind (p : Prog n)
    (hre : ReentryFree p) (hasr : ActivationStaysReachable p) (hnu : NoUnwind p)
    (h : DominatorAccepts p) : Safe p := …
```

* **Plain claim.** For a toy program satisfying `ReentryFree` and `ActivationStaysReachable` and having no unwinding edges: if the dominator checker accepts it, then no walk from the entry reaches UB.
* **Tier.** T1.
* **Depth.** shallow (R2b, `accepts_of_phase_imp`, R1b).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `hre : ReentryFree p` | as R2b | tight: `reentryFree_tight_pLoop1` (a 5-node program whose normal CFG has one cycle (A → 2) and no unwinding edges) |
  | `hasr : ActivationStaysReachable p` | as R2b | tight: `activationStaysReachable_tight_pLoopBack` (a 7-node program whose `break` target loops back to R, with no unwinding edges) |
  | `hnu : NoUnwind p` | as R2b | tight: `unwinding_tight_pCleanup` (a 9-node program with acyclic normal edges and two unwinding edges into one cleanup block) |
  | `h : DominatorAccepts p` | the checker's verdict (the premise) | tight: `dominatorAccepts_tight_pWriteDuringRes` (a 5-node straight-line program without unwinding edges) |

* **Non-vacuity.** `dominatorAccepts_safe_pLoopOK` — `pLoopOK` satisfies `DomGuard` (all three CFG conditions), is accepted, and is safe.
* **Non-claims.**
  * Safety relies on the toy rule that `writeThrough` while `r` is `none` or `reserved` halts instead of being UB; under a rule making that UB, the program `0 → R=1 → 2: writeThrough → A=3` (no access to `x`) would be accepted and unsafe (not proved here).
  * `Safe` models one two-phase loan `r` with one reservation node and one activation node; it does not cover several interacting loans, a two-phase borrow whose single use is not an activation (rustc's `TwoPhaseActivation::NotActivated` case), or conflicts between shared references and direct writes to `x`.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396; RFC 2025 (rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2025-nested-method-calls.md, feature name nested_method_call).
* **Design question.** Which CFG conditions make the dominator phase test sound?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:194-197
theorem dominatorAccepts_tight_pWriteDuringRes :
    (ReentryFree pWriteDuringRes ∧ ActivationStaysReachable pWriteDuringRes ∧
      NoUnwind pWriteDuringRes ∧ CleanupReadsUnderDeadLoan pWriteDuringRes ∧
      ¬ DominatorAccepts pWriteDuringRes) ∧ ¬ Safe pWriteDuringRes := …
```

### R3 — early exit: the dominator checker accepts an unsafe program

```lean
-- ToyTwoPhase/Results.lean:311-320
theorem pBreak_dominatorAccepts_unsafe :
    Acyclic pBreak.succ ∧ NoUnwind pBreak ∧ ReentryFree pBreak ∧
      Dom pBreak.edges pBreak.entry pBreak.R pBreak.A ∧
      ¬ PDom pBreak.succ pBreak.A pBreak.R ∧
      (pBreak.R ≠ 4 ∧ Dom pBreak.edges pBreak.entry pBreak.R 4) ∧
      ¬ Dom pBreak.edges pBreak.entry pBreak.A 4 ∧ ¬ IsActiveDom pBreak 4 ∧
      LoanLive pBreak 4 ∧ MaybeActive pBreak 4 ∧
      DominatorAccepts pBreak ∧ ¬ ExactPhaseAccepts pBreak ∧
      ReachesUB pBreak [0, 1, 2, 3, 4, 5, 6] ∧
      run pBreak RState.init [0, 1, 2, 4, 5, 6] = .halt := by …
```

* **Plain claim.** In the 8-node acyclic program `pBreak` (no unwinding edges, `R` dominates `A`, `ReentryFree`), the edge `2 → 4` from between `R` and `A` to the join `4` (the `break`) makes `A` fail to post-dominate `R`; at the join, `R` strictly dominates it and `A` does not, so the dominator test calls the loan reserved although it is live and may be active; the dominator checker accepts, the exact-phase checker rejects, the fall-through walk `0,1,2,3,4,5,6` (which does not take the edge `2 → 4`) reaches UB, and the walk that takes the `break` halts at the write through `r`.
* **Tier.** T1 — a toy rendering of the reproducer of rust-lang/rust#160598.
* **Depth.** definitional.
* **Hypothesis ledger.** Not applicable (counterexample); every listed property of the program is proved.
* **Positive control.** `pBreakHoisted_rejected` (break hoisted above `R`: `A` post-dominates `R`, `DomGuard` holds, the exact-phase and dominator checkers reject) and `pBreakWrite_rejected` (a write at the join: the exact-phase and dominator checkers reject).
* **Non-claims.**
  * `pBreak` does not show that every early exit between `R` and `A` causes UB: `pBreakDead`, in which `r` is dead at the join, is safe and accepted (`repairs_strict`).
  * It does not show that early exits to an exit node are the only shape that defeats the dominator test: loops (R2) and unwinding edges (R7b) are others.
  * The toy program is not a translation of the issue's Rust program; the correspondence is a modeling bridge (Evidence, modeling bridges).
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust#160598, "is_active can be unsound when the activation does not dominate the reservation", https://github.com/rust-lang/rust/issues/160598 (open at fetch, 2026-11-21); rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396.
* **Design question.** Where does the dominator test fail on structured code?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:326-329
theorem pBreakHoisted_rejected :
    PDom pBreakHoisted.succ pBreakHoisted.A pBreakHoisted.R ∧ DomGuard pBreakHoisted ∧
      ¬ DominatorAccepts pBreakHoisted ∧ ¬ ExactPhaseAccepts pBreakHoisted ∧
      ReachesUB pBreakHoisted [0, 1, 2, 3, 4, 5, 6] := by …

-- ToyTwoPhase/Results.lean:334-335
theorem pBreakWrite_rejected :
    ¬ DominatorAccepts pBreakWrite ∧ ¬ ExactPhaseAccepts pBreakWrite := by …
```

### R4 — the dominator test is also incomplete

```lean
-- ToyTwoPhase/Results.lean:345-351
theorem pJoin_safe_exactPhaseAccepts_not_dominatorAccepts :
    Dom pJoin.edges pJoin.entry pJoin.R pJoin.A ∧ ¬ MaybeActive pJoin 5 ∧ IsActiveDom pJoin 5 ∧
      LoanLive pJoin 5 ∧ ExactPhaseAccepts pJoin ∧ ¬ DominatorAccepts pJoin ∧
      run pJoin RState.init [0, 1, 2, 3] = .ok ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ ∧
      run pJoin RState.init [0, 1, 2, 3, 6] = .ok ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ ∧
      run pJoin RState.init [0, 1, 5, 6] = .halt ∧
      run pJoin RState.init [0, 1, 2, 5, 6] = .halt ∧ Safe pJoin := …
```

* **Plain claim.** The 8-node program `pJoin`, in which `R` dominates `A`, is safe and accepted by the exact-phase checker but rejected by the dominator checker: its join `5` is reached from a path without `R` (no loan) and from the reserved region (loan reserved, not active), so `R` does not strictly dominate it. The write through `r` at node 6 executes with `r` active on the walk through `A`; on the two walks that reach node 6 without `A`, that write halts.
* **Tier.** T1.
* **Depth.** definitional.
* **Hypothesis ledger.** Not applicable (counterexample); every listed property of the program is proved.
* **Positive control.** `pPush_safe_accepted` — `pPush` is safe and accepted by the exact-phase and dominator checkers.
* **Non-claims.**
  * `pJoin`'s safety relies on the halting rule for `writeThrough` on the two walks that reach node 6 without `A` (proved in the theorem).
  * No incompleteness witness satisfying `DomGuard` is given. A straight-line program that reads after `endLoan` and then writes through `r` without a new reservation (the shape of `pEndThenRead`) is accepted by the exact-phase checker and rejected by the dominator checker because the toy `LoanLive` has no forward in-scope component (not proved here); it is not recorded as a result.
  * Incompleteness relative to the exact-phase checker in the toy; the size of the gap on real programs is not examined.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396.
* **Design question.** Does the dominator approximation lose precision in both directions?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:358
theorem pPush_safe_accepted : Safe pPush ∧ ExactPhaseAccepts pPush ∧ DominatorAccepts pPush := …
```

### R5a — repair (b) is contained in the exact-phase checker and is sound

```lean
-- ToyTwoPhase/Results.lean:365-366
theorem repairBAccepts_exactPhaseAccepts (p : Prog n) (h : RepairBAccepts p) :
    ExactPhaseAccepts p := by …

-- ToyTwoPhase/Results.lean:377
theorem repairBAccepts_safe (p : Prog n) (h : RepairBAccepts p) : Safe p := …
```

* **Plain claim.** For every toy program: if repair (b) (the dominator test when `DomGuard` holds, otherwise every loan counts as active) accepts it, then the exact-phase checker accepts it, and no walk from the entry reaches UB.
* **Tier.** T1.
* **Depth.** shallow (R2b and R1b).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `h : RepairBAccepts p` | the repair's verdict (the premise) | tight: `repairBAccepts_tight_pBreak` (an 8-node acyclic program without unwinding edges) |

* **Non-vacuity.** `repairBAccepts_pos` — `pLoopOK` (`DomGuard` holds) is accepted by repair (b); `repairBAccepts_pos_noGuard` shows acceptance of `pBreakDead`, where `DomGuard` fails.
* **Non-claims.**
  * Safety relies on the toy rule that `writeThrough` while `r` is `none` or `reserved` halts instead of being UB; under a rule making that UB, the program `0 → R=1 → 2: writeThrough → A=3` (no access to `x`) would be accepted and unsafe (not proved here).
  * `Safe` models one two-phase loan `r` with one reservation node and one activation node; it does not cover several interacting loans, a two-phase borrow whose single use is not an activation (rustc's `TwoPhaseActivation::NotActivated` case), or conflicts between shared references and direct writes to `x`.
  * Repair (b) falls back to treating every loan as active when `DomGuard` fails; on such programs it rejects reads during a reservation (`repairBAccepts_neg`).
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396.
* **Design question.** How do candidate repairs compare in what they accept?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:382-383
theorem repairBAccepts_tight_pBreak :
    ¬ RepairBAccepts pBreak ∧ ¬ ExactPhaseAccepts pBreak ∧ ¬ Safe pBreak := …

-- ToyTwoPhase/DefExamples.lean:152
theorem repairBAccepts_pos : RepairBAccepts pLoopOK := by decide
```

### R5c — repair (c) ⊆ repair (b) ⊆ exact-phase checker, both strict

```lean
-- ToyTwoPhase/Results.lean:388-389
theorem repairCAccepts_repairBAccepts (p : Prog n) (h : RepairCAccepts p) :
    RepairBAccepts p := by …

-- ToyTwoPhase/Results.lean:408-411
theorem repairs_strict :
    (Safe pJoin ∧ ExactPhaseAccepts pJoin ∧ ¬ RepairBAccepts pJoin) ∧
      (Safe pBreakDead ∧ ¬ LoanLive pBreakDead 4 ∧ ExactPhaseAccepts pBreakDead ∧
        RepairBAccepts pBreakDead ∧ ¬ RepairCAccepts pBreakDead) := …
```

* **Plain claim.** For every toy program: if repair (c) (reject when `DomGuard` fails, otherwise the dominator checker) accepts it, then repair (b) accepts it — by construction, since both use the guard `DomGuard`. Both inclusions repair (c) ⊆ repair (b) ⊆ exact-phase checker are strict: `pJoin` (8 nodes) is safe and accepted by the exact-phase checker but not by repair (b); the `break`-in-argument program `pBreakDead` (6 nodes), in which `r` is dead at the join, is safe and accepted by the exact-phase checker and by repair (b) but not by repair (c).
* **Tier.** T1.
* **Depth.** definitional (the inclusion unfolds the shared guard; the witnesses are evaluated).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `h : RepairCAccepts p` | the repair's verdict (premise of the inclusion) | tight: `repairCAccepts_tight_pJoin` (an 8-node acyclic program without unwinding edges) |

* **Non-vacuity.** `repairCAccepts_pos` — `pLoopOK` is accepted by repair (c); so is the loop-in-argument program `pArgLoop` (`repairCAccepts_pos_argLoop`).
* **Non-claims.**
  * The inclusion repair (c) ⊆ repair (b) holds because both use `DomGuard`; the strict ordering is proved for this package's definitions and neither establishes nor refutes comparability between other formulations of "reject early exits" and guarded dominator repairs.
  * A literal form of repair (c) — reject when some edge leaves the region of nodes reachable from `R` avoiding `A` other than into `A` — would accept `pLoop1` (no such edge) and `pDiverge` (the cycle stays inside the region), both unsafe and accepted by the dominator checker (R2); no literal repair (c) checker is defined in Lean (not proved here).
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396.
* **Design question.** How do candidate repairs compare in what they accept?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:399-401
theorem repairCAccepts_tight_pJoin :
    ¬ RepairCAccepts pJoin ∧ ¬ RepairBAccepts pJoin ∧ ¬ ActivationStaysReachable pJoin ∧
      ¬ DomGuard pJoin := by …

-- ToyTwoPhase/DefExamples.lean:158
theorem repairCAccepts_pos : RepairCAccepts pLoopOK := by decide
```

### R5d — the literal post-dominance guard is unsound

```lean
-- ToyTwoPhase/Results.lean:419-421
theorem literalRepairB_unsound_pLoopBack :
    PDom pLoopBack.succ pLoopBack.A pLoopBack.R ∧ LiteralRepairBAccepts pLoopBack ∧
      ReachesUB pLoopBack [0, 1, 2, 3, 4, 5] := by …
```

* **Plain claim.** The literal repair (b) — the dominator test guarded by `A` post-dominating `R` along normal edges, otherwise every loan counts as active — accepts the 7-node looping program `pLoopBack`, which reaches UB on the walk `0,1,2,3,4,5`.
* **Tier.** T1.
* **Depth.** definitional.
* **Hypothesis ledger.** Not applicable (counterexample); every listed property of the program is proved.
* **Positive control.** `literalRepairB_rejects_pBreak` — the literal repair (b) rejects the early-exit program `pBreak`, where its guard fails.
* **Non-claims.**
  * The guarded repair with `DomGuard` (R5a) is sound; the counterexample concerns the guard `A` post-dominates `R` alone.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396; A. Podgurski, L. A. Clarke, "A Formal Model of Program Dependences and Its Implications for Software Testing, Debugging, and Maintenance", IEEE TSE 16(9), 1990, pp. 965-979, https://doi.org/10.1109/32.58784 (weak control dependence via strong post-dominance, which bounds path length and so accounts for loops).
* **Design question.** How do candidate repairs compare in what they accept?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:426-427
theorem literalRepairB_rejects_pBreak :
    ¬ PDom pBreak.succ pBreak.A pBreak.R ∧ ¬ LiteralRepairBAccepts pBreak := by …
```

### R6b — a write during the reservation is UB and is flagged

```lean
-- ToyTwoPhase/Results.lean:436-440
theorem pWriteDuringRes_ub_rejected :
    ¬ MaybeActive pWriteDuringRes 2 ∧ ¬ IsActiveDom pWriteDuringRes 2 ∧
      ReachesUB pWriteDuringRes [0, 1, 2, 3] ∧
      Flagged pWriteDuringRes (MaybeActive pWriteDuringRes) 2 ∧
      Flagged pWriteDuringRes (IsActiveDom pWriteDuringRes) 2 := by …
```

* **Plain claim.** In the 5-node `pWriteDuringRes`, a write to `x` during the reservation is followed by the activation; the walk `0,1,2,3` reaches UB at the activation; the exact-phase and dominator checkers flag the write, although neither phase test calls the loan active there.
* **Tier.** T0 — RFC 2025's rule that mutation is not permitted during the reservation, reproduced by the toy semantics and checkers.
* **Depth.** definitional.
* **Hypothesis ledger.** Not applicable (counterexample); every listed property of the program is proved.
* **Positive control.** `pPush_safe_accepted` — `pPush` (a read, not a write, during the reservation) is safe and accepted by the exact-phase and dominator checkers.
* **Non-claims.**
  * Tree Borrows' `conflicted` flag, protectors and interior mutability are not modeled.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** RFC 2025 (rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2025-nested-method-calls.md, feature name nested_method_call); N. Villani, J. Hostert, D. Dreyer, R. Jung, "Tree Borrows", Proc. ACM Program. Lang. 9 (PLDI), Article 188, 2025, https://doi.org/10.1145/3735592 (operational semantics mechanized in Rocq).
* **Design question.** What may a reservation permit, measured against a reference aliasing semantics?
* **Basis.** execution (Lean kernel check).

### R6c — a shared reborrow created during the reservation and used after the activation is UB

```lean
-- ToyTwoPhase/Results.lean:447-452
theorem pSharedDuringRes_ub_rejected :
    ¬ MaybeActive pSharedDuringRes 2 ∧ ReachesUB pSharedDuringRes [0, 1, 2, 3, 4] ∧
      (∀ L : Fin 5, Flagged pSharedDuringRes (MaybeActive pSharedDuringRes) L ↔
        L = pSharedDuringRes.A) ∧
      (∀ L : Fin 5, Flagged pSharedDuringRes (IsActiveDom pSharedDuringRes) L ↔
        L = pSharedDuringRes.A) := by …
```

* **Plain claim.** In the 5-node `pSharedDuringRes`, a shared reference created during the reservation is used after the activation; the walk `0,1,2,3,4` reaches UB at the use (the activation is a write through `r`); the exact-phase and dominator checkers reject, and for each of these two checkers a node is flagged if and only if it is `A` (the activation check).
* **Tier.** T0 — RFC 2025's activation check and Tree Borrows' treatment of activation as the first local write, reproduced by the toy.
* **Depth.** definitional.
* **Hypothesis ledger.** Not applicable (counterexample); every listed property of the program is proved.
* **Positive control.** `pPush_safe_accepted` — `pPush` is safe and accepted by the exact-phase and dominator checkers.
* **Non-claims.**
  * In Tree Borrows, a foreign read on a protected `Reserved` reference sets its `conflicted` flag, and a later local write is then UB (Tree Borrows §3.1, documentation); the toy omits protectors and `conflicted` and so does not model protected function-argument references.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** RFC 2025 (rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/2025-nested-method-calls.md, feature name nested_method_call); N. Villani, J. Hostert, D. Dreyer, R. Jung, "Tree Borrows", Proc. ACM Program. Lang. 9 (PLDI), Article 188, 2025, https://doi.org/10.1145/3735592 (operational semantics mechanized in Rocq).
* **Design question.** What may a reservation permit, measured against a reference aliasing semantics?
* **Basis.** execution (Lean kernel check).

### R7a — unwinding edges: the dominator test is sound outside cleanup nodes

```lean
-- ToyTwoPhase/Results.lean:460-462
theorem isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_not_isCleanup
    (p : Prog n) (hre : ReentryFree p) (hasr : ActivationStaysReachable p) (L : Fin n)
    (hnc : ¬ IsCleanup p L) (hL : MaybeActive p L) : IsActiveDom p L := …
```

* **Plain claim.** For a toy program (unwinding edges allowed) in which every normal walk from `A` back to `A` passes `R` (`ReentryFree`) and every node `x ≠ R` reached from a normal successor `y ≠ R` of `R` along normal edges without passing `A` or `R` before `x` can still reach `A` along normal edges without passing `R` (`ActivationStaysReachable`), at every node `L` that is not a cleanup node and where the loan may be active, the dominator test (dominance over all edges) calls the loan active.
* **Tier.** T1.
* **Depth.** shallow given R2b's argument: every walk ending at a non-cleanup node consists of normal edges (`isWalk_succ_of_not_isCleanup`).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `hre : ReentryFree p` | as R2b | tight: `reentryFree_tight_pLoop1` (a 5-node program whose normal CFG has one cycle (A → 2) and no unwinding edges) |
  | `hasr : ActivationStaysReachable p` | as R2b | tight: `activationStaysReachable_tight_pLoopBack` (a 7-node program whose `break` target loops back to R, with no unwinding edges) |
  | `hnc : ¬ IsCleanup p L` | a cleanup block joins walks from before and after A | tight: `unwinding_tight_pCleanup` (a 9-node program with acyclic normal edges and two unwinding edges into one cleanup block) |
  | `hL : MaybeActive p L` | between R and A the dominator test calls the loan reserved | tight: `maybeActive_tight_pCleanupRead` (an 8-node program with acyclic normal edges and two unwinding edges) |

* **Non-vacuity.** `notCleanup_hypotheses_hold_pCleanupRead` — `pCleanupRead` has unwinding edges and satisfies all hypotheses at node 4.
* **Non-claims.**
  * `IsCleanup` marks every node reachable from the target of any unwinding edge, including edges whose source is unreachable from the entry, and including normal code reached from a cleanup block.
  * R7a, R7b and R7c neither establish nor refute whether real MIR cleanup code (which runs drop glue rather than arbitrary reads and writes through `r`) can defeat rustc's `is_active`.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396.
* **Design question.** Is "ignoring unwinding edges" safe, and under what condition?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:466-469
theorem maybeActive_tight_pCleanupRead :
    ¬ NoUnwind pCleanupRead ∧ ReentryFree pCleanupRead ∧ ActivationStaysReachable pCleanupRead ∧
      ¬ IsCleanup pCleanupRead 2 ∧ ¬ MaybeActive pCleanupRead 2 ∧
      ¬ IsActiveDom pCleanupRead 2 := by …

-- ToyTwoPhase/Results.lean:474-476
theorem notCleanup_hypotheses_hold_pCleanupRead :
    ¬ NoUnwind pCleanupRead ∧ ReentryFree pCleanupRead ∧ ActivationStaysReachable pCleanupRead ∧
      ¬ IsCleanup pCleanupRead 4 ∧ MaybeActive pCleanupRead 4 := by …
```

### R7b — a cleanup read under a live loan defeats the dominator test

```lean
-- ToyTwoPhase/Results.lean:482-486
theorem pCleanup_dominatorAccepts_unsafe :
    ReentryFree pCleanup ∧ ActivationStaysReachable pCleanup ∧
      ¬ CleanupReadsUnderDeadLoan pCleanup ∧ (pCleanup.op 6).isRead = true ∧
      LoanLive pCleanup 6 ∧ MaybeActive pCleanup 6 ∧ ¬ IsActiveDom pCleanup 6 ∧
      DominatorAccepts pCleanup ∧ ReachesUB pCleanup [0, 1, 2, 3, 4, 6, 7] := by …
```

* **Plain claim.** The 9-node `pCleanup`, satisfying `ReentryFree` and `ActivationStaysReachable`, has a cleanup block shared by an unwinding edge before `A` and one after `A` that reads `x` while `r` is live; there the dominator test calls the loan reserved, the dominator checker accepts, and the walk `0,1,2,3,4,6,7` reaches UB.
* **Tier.** T1.
* **Depth.** definitional.
* **Hypothesis ledger.** Not applicable (counterexample); every listed property of the program is proved.
* **Positive control.** `pCleanupRead_hypotheses_hold_safe` — `pCleanupRead`, whose cleanup block reads `x` after the last use of `r`, satisfies `CleanupReadsUnderDeadLoan`, is accepted and is safe.
* **Non-claims.**
  * Cleanup is modeled as ordinary nodes reached through unwinding edges; whether real MIR cleanup code can take the shape of `pCleanup` (a read of the borrowed place followed by a write through `r`) is not examined.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396.
* **Design question.** Is "ignoring unwinding edges" safe, and under what condition?
* **Basis.** execution (Lean kernel check).

Witnesses (statements):

```lean
-- ToyTwoPhase/Results.lean:492-495
theorem pCleanupRead_hypotheses_hold_safe :
    ¬ NoUnwind pCleanupRead ∧ ReentryFree pCleanupRead ∧ ActivationStaysReachable pCleanupRead ∧
      CleanupReadsUnderDeadLoan pCleanupRead ∧ DominatorAccepts pCleanupRead ∧
      LoanLive pCleanupRead 2 ∧ Safe pCleanupRead := …
```

### R7c — unwinding edges: the dominator checker is sound when cleanup reads happen under a dead loan

```lean
-- ToyTwoPhase/Results.lean:503-505
theorem dominatorAccepts_safe_of_reentryFree_activationStaysReachable_cleanupReadsUnderDeadLoan
    (p : Prog n) (hre : ReentryFree p) (hasr : ActivationStaysReachable p)
    (hcl : CleanupReadsUnderDeadLoan p) (h : DominatorAccepts p) : Safe p := …
```

* **Plain claim.** For a toy program (unwinding edges allowed) satisfying `ReentryFree` and `ActivationStaysReachable` along normal edges, in which no cleanup node reads `x` while `r` is live: if the dominator checker accepts it, then no walk from the entry reaches UB.
* **Tier.** T1.
* **Depth.** shallow (R7a via `not_isCleanup_of_cleanupReadsUnderDeadLoan`, then `accepts_of_phase_imp` and R1b).
* **Hypothesis ledger.**

  | Hypothesis | Why | Tightness |
  | :--- | :--- | :--- |
  | `hre : ReentryFree p` | as R2b | tight: `reentryFree_tight_pLoop1` (a 5-node program whose normal CFG has one cycle (A → 2) and no unwinding edges) |
  | `hasr : ActivationStaysReachable p` | as R2b | tight: `activationStaysReachable_tight_pLoopBack` (a 7-node program whose `break` target loops back to R, with no unwinding edges) |
  | `hcl : CleanupReadsUnderDeadLoan p` | a cleanup block reading x under a live loan joins walks from before and after A | tight: `unwinding_tight_pCleanup` (a 9-node program with acyclic normal edges and two unwinding edges into one cleanup block) |
  | `h : DominatorAccepts p` | the checker's verdict (the premise) | tight: `dominatorAccepts_tight_pWriteDuringRes` (a 5-node straight-line program without unwinding edges) |

* **Non-vacuity.** `pCleanupRead_hypotheses_hold_safe` — `pCleanupRead` has unwinding edges, satisfies all hypotheses (including acceptance, with a read during the reservation at node 2), and is safe.
* **Non-claims.**
  * Safety relies on the toy rule that `writeThrough` while `r` is `none` or `reserved` halts instead of being UB; under a rule making that UB, the program `0 → R=1 → 2: writeThrough → A=3` (no access to `x`) would be accepted and unsafe (not proved here).
  * `Safe` models one two-phase loan `r` with one reservation node and one activation node; it does not cover several interacting loans, a two-phase borrow whose single use is not an activation (rustc's `TwoPhaseActivation::NotActivated` case), or conflicts between shared references and direct writes to `x`.
  * R7c holds because `CleanupReadsUnderDeadLoan` makes every read of `x` under a live loan a non-cleanup node, where R7a applies.
  * These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's borrow checker. Model–system relation: none proved.
* **Prior art.** rust-lang/rust 26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_borrowck/src/path_utils.rs L60-120 (is_active; assumption comment L88-93); compiler/rustc_borrowck/src/lib.rs L1323-1328 (check_access_for_conflict); compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs L390-396.
* **Design question.** Is "ignoring unwinding edges" safe, and under what condition?
* **Basis.** execution (Lean kernel check).

## Boundaries

### Non-claims (all results)

* **Toy model.** These are statements about the toy model; they neither establish nor refute the
  corresponding claims about rustc's borrow checker, Polonius, Tree Borrows or Miri.
  Model–system relation: none proved.
  No embedding, abstraction or simulation between the toy and MIR is defined.
* **Liveness.** Loan and shared-reference liveness are path reachability of a later use, not NLL
  region inference; no lifetimes, no outlives constraints, no loans other than `r`. `LoanLive` has no
  forward in-scope component; rustc's `Borrows` analysis (`compiler/rustc_borrowck/src/dataflow.rs` at
  the commit above) kills a borrow where it goes out of scope (source).
* **Branching.** All branches are nondeterministic; a run is any walk. Data-dependent infeasibility
  (e.g. `Option` being `None` on one path) is modeled by the halting `writeThrough` rule, not by guards.
* **Reference semantics.** It tracks conflicts involving `r`. Direct writes to `x` do not affect shared
  references; shared references never conflict with each other; `endLoan` is an explicit statement.
  `conflicted` reservations, protectors, interior mutability (`ReservedIM`) and retags are not modeled.
* **Phase-test rendering.** `IsActiveDom` renders "the statement after `R` dominates `L`" as strict
  dominance by `R` at one-statement-per-node granularity; multi-statement blocks are not modeled.
* **Repairs.** (b) and (c) are this package's formulations with the guard `DomGuard`; the literal
  guard `A pdom R` alone is unsound in looping CFGs (R5d).
* **Unwinding.** Cleanup nodes are ordinary nodes reached through unwinding edges; the shape of real
  cleanup code is not examined (R7a–R7c).
* **Degenerate sizes and arithmetic.** There is no program with zero or one node
  (`prog_zero_uninhabited`, `prog_one_uninhabited`). No statement in a card uses truncating
  arithmetic.

### Escape hatches

* The counterexamples of R2, R3 and R7b are excluded, respectively, by `ReentryFree` together with
  `ActivationStaysReachable` (R2b), by post-dominance in an acyclic CFG (R2a) or
  `ActivationStaysReachable` (R2b), and by `CleanupReadsUnderDeadLoan` (R7c).
* R4's incompleteness witness `pJoin` violates `ActivationStaysReachable` and hence `DomGuard`
  (`repairCAccepts_tight_pJoin`). No incompleteness witness satisfying `DomGuard` is given (R4
  non-claims).

### Not examined

* A characterization of the CFGs on which the dominator test is sound is not given. R2b and its
  variant give sufficient conditions: `ReentryFree` and no unwinding edges together with
  `ActivationStaysReachable` (R2b) or with the strictly weaker `DomRegionReachesA`
  (`isActiveDom_of_maybeActive_of_reentryFree_domRegionReachesA_noUnwind`,
  `pJoin_separates_domRegionReachesA`). No minimality claim is made for either condition.

### Unknown tightness, disproved and dropped statements

* Every hypothesis of every theorem and characterization card (R1a–R1d, R2a–R2c, R5a, R5c, R7a, R7c)
  is recorded as tight, with the proved counterexample named in its ledger; no hypothesis has
  `unknown` tightness.
* No result statement was found false, and none was dropped for lack of a proof.

## Evidence

### Kernel-check record

Toolchain `leanprover/lean4:v4.34.1` (release tag commit `5045d0056413266e57c625dcd7c365b10e377c52`
of leanprover/lean4), core Lean and `Std`, no Mathlib, no `axiom`/`opaque`/`sorry`/`native_decide`.
Concrete facts are proved by `decide`, using the decidable checkers `pathViaB`
(`pathViaB_iff`) and the safety certificate check `certOK` (`safe_of_cert`); certificates are
computed by `explore`, whose correctness is not needed because `certOK` is checked.
Basis for every card: execution (Lean kernel check).

Support files:

* `audit/axioms.json` — for each of the 628 declarations of the `ToyTwoPhase` library, the axioms
  it depends on (Lean's `collectAxioms`); every entry is a subset of `propext`, `Classical.choice`,
  `Quot.sound`.
* `audit/statements.json` — for each of the 220 Lean names referenced by `results.json`, the
  statement hash, the closure hash and the closure size, computed as described under Revalidation.
* `evidence/Audit.lean` prints every theorem of the `ToyTwoPhase` modules with its axioms;
  `evidence/axioms.txt` records its output (311 theorems, each depending on a subset of `propext`,
  `Classical.choice`, `Quot.sound`).

Per-name record (from `audit/statements.json` and `audit/axioms.json`; the 23 main theorems of the
cards first, marked "(main)", then every other referenced name in alphabetical order; "Cards"
lists the cards whose `results.json` entry references the name; "none" means no axioms):

| Lean name (namespace `Toy.TwoPhase`) | Kind | Cards | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `dfMaybeActive_iff_maybeActive_of_activation_reachable` | theorem | R1a (main) | `Classical.choice`, `Quot.sound`, `propext` | `06abf723a7b1f89d8be6d8f0de140eb38ceae4aae1dc0689a74feb4540a0d0db` | `b5fc42253fa0cf21eb4b95ac685b532e6aaf981f5d5fe5b146411daedb7d9326` (54) |
| `dominatorAccepts_safe_of_reentryFree_activationStaysReachable_cleanupReadsUnderDeadLoan` | theorem | R7c (main) | `Classical.choice`, `Quot.sound`, `propext` | `1580f795547451836147de7436e6258b63dd9a4a39111916deb439499df7f0c6` | `2c28fac427e4602fd5480bef6c433dc723be6d36ead8d96426905580d02b808c` (109) |
| `dominatorAccepts_safe_of_reentryFree_activationStaysReachable_noUnwind` | theorem | R2c (main) | `Classical.choice`, `Quot.sound`, `propext` | `0699e4bf151129e3a27d3cf89802e578332a28e2373b3d7b805a7fc7355f67e2` | `cadbca4f311baab02f251fb5c7641c930ec6cb006248b461cf7b3029456715ad` (108) |
| `exactPhaseAccepts_safe` | theorem | R1b (main) | `Quot.sound`, `propext` | `a2a5889286f538fd34687691fd9fbf3b51e0b45c3dcb04eee4cc1f2bd3aa41b2` | `8cb20ef6cff61c57f8bdd4ad519d0ad16e6ed87b88ab0d88443ec6a80d2f7bd9` (103) |
| `isActiveDom_of_maybeActive_of_acyclic_pdom_noUnwind` | theorem | R2a (main) | `Classical.choice`, `Quot.sound`, `propext` | `a79f7ae55510e7b7befc1430fd017e42cffa7a07562878fac5d4f774f9d47e78` | `5238653604f513b0c24b34ec12d00c0025205cab151e926dbe0e0dff8d10fcae` (50) |
| `isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_not_isCleanup` | theorem | R7a (main) | `Classical.choice`, `Quot.sound`, `propext` | `ca1be06940ec5a95b69b2315694af90d6fdb905f4f77599ebecb480837b7ba69` | `6c05518dba8e3dee0b84c9cb13c294e74876889afebb15bb03d6d6a5365aacf0` (51) |
| `isActiveDom_of_maybeActive_of_reentryFree_activationStaysReachable_noUnwind` | theorem | R2b (main) | `Classical.choice`, `Quot.sound`, `propext` | `f96939f17f4e0cdb37c268d377531a7f48e29660d12f92f027dd547d6c32978a` | `e68a5a3ae845cf5c51d10b739ebdca63daf0b73e06f6f3866e51409882973539` (51) |
| `iterDataflowAccepts_exactPhaseAccepts` | theorem | R1c (main) | `Classical.choice`, `Quot.sound`, `propext` | `4218ffa640fef80faf48918ceb493eda4da65f5a3d235d7804644fe75101c128` | `7ce715d6470faffe5bbc9b04cf3c13978670789a48a10a883799a2882adea815` (65) |
| `iterDataflowAccepts_iff_exactPhaseAccepts_of_activation_reachable` | theorem | R1d (main) | `Classical.choice`, `Quot.sound`, `propext` | `dfc74928aa6bdd718269df96b25f8a95dafd7526b0e6230823c0c01d70126bbc` | `33fddad26f02082d35695fb2a761540fe4303112aca370651e957384e7ee9f4c` (66) |
| `iterDataflowAccepts_safe` | theorem | R1c (main) | `Classical.choice`, `Quot.sound`, `propext` | `b04057f08ff45beb2f0ce1e52ef76018aee7bd31b04074d1979f989363d5ed94` | `5a4fe064c592d3db4cd4ee10810b45d279189a8fe1225a0b6030eedbcfd6f9a2` (110) |
| `literalRepairB_unsound_pLoopBack` | theorem | R5d (main) | `Classical.choice`, `Quot.sound`, `propext` | `7ea65f0b329a2c13c44525decb604649c62cf19939b084e6223008dae1868b04` | `1c6a9525339393c30369675df34ec7c039044e9f5d80043bc32bf1128b2e2b69` (121) |
| `pBreak_dominatorAccepts_unsafe` | theorem | R3 (main) | `Classical.choice`, `Quot.sound`, `propext` | `067288b49544d50947e66a3857b033690675718bfdb56dfd2f7389885f32e89f` | `a7c79fe731942c770c5c04aadf2cdaf765293931efe6dc18c595e87e41f04422` (115) |
| `pCleanup_dominatorAccepts_unsafe` | theorem | R7b (main) | `Classical.choice`, `Quot.sound`, `propext` | `020d66f5f04046d8e1e9be64c2ead8a330f51a88d4a048291c2270586d154c92` | `e8077efb7719e97151fe18370cb6f51fa951732332501e60e197bd9812d944b6` (115) |
| `pJoin_safe_exactPhaseAccepts_not_dominatorAccepts` | theorem | R4 (main) | `Classical.choice`, `Quot.sound`, `propext` | `2cd40917235b348794bfb1a6f147142d75a4531b309ff2d4037ed08dbea5c39b` | `56120dfdf3eb9d8e9ad6b41ba2914badba47230ab449d2ea49c577d91b17ab61` (111) |
| `pSharedDuringRes_ub_rejected` | theorem | R6c (main) | `Classical.choice`, `Quot.sound`, `propext` | `0cbc25bf010cf889692427a30d3296e06d0f997a6406090aac3d0f805920edf7` | `c9c24082cc4e9e03dcd4c3343dd9c0159b3c134e18d14b8ccdf68c5a04123768` (108) |
| `pWriteDuringRes_ub_rejected` | theorem | R6b (main) | `Classical.choice`, `Quot.sound`, `propext` | `435094f818754566fdf08eff52761fe02b8406e2f1409e9bf5fc76bbc473eb6e` | `3aa95a84e3d904586168913967ca103f05455aff1acb08d7d2d469d8d199257f` (108) |
| `rdomA_apdomR_noUnwind_insufficient_pLoop1` | theorem | R2 (main) | `Classical.choice`, `Quot.sound`, `propext` | `45a0fdb3a3385390807dfa09a1ab867fa63ffbbb54907122da2a43c9e9fbc182` | `1fcee851828a44b35695b583cd89336a0e3a8e4d320c8c7d8fdf12bf6ed4acbb` (115) |
| `rdomA_apdomR_noUnwind_reentryFree_insufficient_pDiverge` | theorem | R2 (main) | `Classical.choice`, `Quot.sound`, `propext` | `72119b9c66f5fa10879e92af2e91b398b790ecef8b4321e126f8f7273a2141b6` | `3d449277f08431feb354443ffedd577770f31276ab1aed79ff3de3a7fc38b39f` (115) |
| `rdomA_apdomR_noUnwind_reentryFree_insufficient_pLoopBack` | theorem | R2 (main) | `Classical.choice`, `Quot.sound`, `propext` | `c61093f4fe5c95da560c62e56fcc3110294ca44f3d13bdfa5a1a5fbccbc2b275` | `9c897f419a91e7f07977d1778c52a253e9669dbf37f647260063587a0a2c06b2` (113) |
| `repairBAccepts_exactPhaseAccepts` | theorem | R5a (main) | `Classical.choice`, `Quot.sound`, `propext` | `3f9524a94d43f200f4db4dd61a55ac3310b28b67ff58c0b207a29b0a90f70507` | `17221ac0cf14ecbb4ddb8f9b36ace90ac73b893b5dec3f186bb17aa078286b9c` (78) |
| `repairBAccepts_safe` | theorem | R5a (main) | `Classical.choice`, `Quot.sound`, `propext` | `5b0d003012622b14649b70995efe41290afb275e8ac7cac43c97699a5e6b07ee` | `a9e8973b25f7e22ef8cdc0fe8b00367be8ead7d78bd930aedd55deefd89e4c16` (123) |
| `repairCAccepts_repairBAccepts` | theorem | R5c (main) | `Classical.choice`, `Quot.sound`, `propext` | `4a2de9058906c5df482f01653fb60069c5f7b0a758fc9bc28775fb7c65c2f710` | `8b81c533ff27dfe63898788c3004baf265091d1d3e4a7bf0d209d223ba47c317` (78) |
| `repairs_strict` | theorem | R3, R5c (main) | `Classical.choice`, `Quot.sound`, `propext` | `42f75535b4f926ef690799cd7fb157257642667f628a968d7cd85270d27ab96a` | `eaee8467d8d00849df4f185eb43100cfbf8f600124f05814c21a5c755a448461` (135) |
| `Accepts` | def | R1b | `propext` | `efd9c21b8ae556a1185f627fae4ff1b864f5095c049b8a9effbf8d6857bd3d48` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `accepts_of_phase_imp` | theorem | R1c | `propext` | `249e661ec1ca56d90f851492283a47b60fe8109fe5c6b793e5734c154c657b86` | `2e78973a4f0a94702dcd6e64e0745241d1ab6e2d21b2b0f28f527ef24e755d63` (53) |
| `ActivationStaysReachable` | def | R2 | none | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `activationStaysReachable_neg_diverge` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `238f0542dd605d828cca1923e5413a329ba453d2a04497b4ae323aa8783e1fa7` | `66285ce46d4726ad246d76c1387daefb21d1ed2250179e8586bb29b0e57f7263` (27) |
| `activationStaysReachable_neg_exit` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `9b426d3adc3f535f9a5de0239db18de32e65003d048dce0a8b716b450185a94a` | `323b93884d0a4fb4300b09f53864c6888918d4cb15960c480cb75159252da86c` (27) |
| `activationStaysReachable_neg_loopBack` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `639905b99917e56bf8811467bb9736b16a60f51d5c11fe2f547566457dbc42d2` | `7d6c51d995cb3a37ec4579d2e42f9323c981789bffb0df39db5ad5dbd1e36f26` (27) |
| `activationStaysReachable_of_acyclic_pdom` | theorem | R2a | `Classical.choice`, `Quot.sound`, `propext` | `5c2465350ce31ce507ed547a99d409a3011c1af81ce862ac0bf8d61616445a31` | `21e31be1dcdec63fdb163a121a4c0f88e7338c93f6112777c97fbad767e1174d` (24) |
| `activationStaysReachable_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `18db85c5920ee2dd7f0d2b46c443a379d48d4868f8990689d3e1e8d5a7add530` | `c9d14c6cf05937fea1dddfa074b3456a87794ed58b7d871c922d3654a606d602` (27) |
| `activationStaysReachable_pos_argLoop` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `1174234280b63040d90e1177cc64dce09867985fec1ac676618ae9ffab3533a0` | `015bfa5005dc5d22c98ada4247c801a3442553bc1c61317f7293e0a7c55a4ab3` (27) |
| `activationStaysReachable_pos_continue` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `7c60186eb2b38798c0a61a6c16af0b03d44bd469152ca12ba5831670bb3d3308` | `e577960502e9de8e84936532fdc7d3c06c57f52e92a2fc396583eaff78e3dfd2` (27) |
| `activationStaysReachable_tight_pLoopBack` | theorem | R2b, R2c, R7a, R7c | `Classical.choice`, `Quot.sound`, `propext` | `eb067d674d8cbbf0517a4e710fefae6a88173122ce480234b767051d17d06a1c` | `5af7da66d80dfbd58782e0c8c29ef762c166d2fa98f0ce0310f68d336a301cb9` (116) |
| `Acyclic` | def | R2a | none | `9a536fd25c4c4cbb4a73db21cb6dbe5c9ff6fc594080bde0d8f5efd2da0130b5` | `51d01d6bfa38438815c51578fc6dc65bdba9821a69845fb23911d7d63c02a9f9` (1) |
| `acyclic_iff` | theorem | R1b | `Quot.sound`, `propext` | `0cb5b39342080455daeb745034ec5f64afacc6c5eea8f807803f78cade543dbe` | `c62f9354850c64b6581915370ebeb81a40eb15e9a1fe0096cc19f2afa02bb36d` (6) |
| `acyclic_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `e7cdb2a59cb0b6d8501a4bfc0dd74d03d902d35f961a4600c92bdb2f6c47923d` | `c83ddf5953d9d97f172f11bad4844174228ae3b49caaf92a08a1d57dec79a5a3` (24) |
| `acyclic_pdom_hypotheses_hold_pPush` | theorem | R2a | `Classical.choice`, `Quot.sound`, `propext` | `bddc8d37195e2a4a1223cc07eb0a0da09ef1c52653dffb9428611477d1a28bf3` | `753e18979ebf02b3cc2a4c1d718f3c42fb83b29195497b65d5a9c6a0625be621` (53) |
| `acyclic_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `a2be0ecb512453e324d511d22a4c2a888fb45842f1da9952394a051c90048914` | `5f66deaefccbb3345bebe96949638ac795fc58dd27db084c9d8eee92ca78b4e5` (24) |
| `acyclic_tight_pLoop1` | theorem | R2a | `Classical.choice`, `Quot.sound`, `propext` | `258759e7ece7aa919e967e9eee3f24a1732dc90d0dc471f3ccb7bfe406a5dcba` | `a89f79ca9065bd37c9db2a3b8f489e071842c6d20211702cb32e1fa43f5a19ac` (55) |
| `AlwaysActiveAccepts` | def | R1b | `propext` | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `alwaysActiveAccepts_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `81dfba5ea78b9ba5f8950c7c79d86c1d5e79db313b479badf2a8c8d32ff9a103` | `e0ee4505f0a64909a9be3fd040937d843ede0b9277c7414dc3e96b339dae8ee8` (59) |
| `alwaysActiveAccepts_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `29879dd5aa4c57f6549e5481f3204f25d793d51157042ac0136b6b3effb8952b` | `7da1bc21347a63d7631759cb6ff8aa862c53ae00bb8fe5c1bfbf2ccbd4f33976` (59) |
| `certOK` | def | R1d | `propext` | `191fc71affed9e22b5933001a5e19975a49032c515e48e36af50e7441db434d4` | `e95e699337a38dad01d2bd0435461afded08c2dd40f44495ba9de70cab17634a` (24) |
| `CleanupReadsUnderDeadLoan` | def | R7b | `propext` | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `cleanupReadsUnderDeadLoan_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `cf0aa3798d61415d77478f1330e88f1d0805f6e6f34538a91c0588744f1e03fc` | `cc5b9ed111f9cfd0ec138611cc1c5b334aeb83d8be4d67ee5ba822508ecea2d5` (58) |
| `cleanupReadsUnderDeadLoan_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `58d62c17f8b251228abfc2d560bc5d35f1afefa8cb53975289a5a17787147e9f` | `9ca6f766798d8ac37e64caae8d4dbc164cc4f01fbca6f0a16ad30cb8ec388e9a` (58) |
| `dfIter` | def | R1a | `propext` | `fad5c792aeab0a36afc49e6714f11e045fabac8e5f1e1c6c8acaf9da208a4ee9` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `dfMaybeActive` | def | R1a | `propext` | `c03e2994e780ee6257be47fca102d2f8d953d7b2bfb1b2de790659d63dc160d7` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `dfMaybeActive_hypotheses_hold_pBreak` | theorem | R1a | `Classical.choice`, `Quot.sound`, `propext` | `2efb3fbb9e35991d979605592c1ebee1d20d1d737c3f79f192a14c6e4ace12dc` | `840c6463609e27d707052f85022464465edde442f3ba8465e23acc7b6bafb5e4` (59) |
| `dfMaybeActive_iff_genReach` | theorem | R1a | `Classical.choice`, `Quot.sound`, `propext` | `a6bda852cb920a603b199d78f2a5d46238bcc8ec2f0e93fb858b8e15999703bd` | `36704c53914fa2cd712eb65a86dbb9ac9a6ea109a496fe7c59ff77e1cac913ec` (53) |
| `dfMaybeActive_ne_maybeActive_pUnreachA` | theorem | R1a | `Classical.choice`, `Quot.sound`, `propext` | `eaf1a0442376382d03def755e9643f7a564b4324507f9e7f31007f52db0ee564` | `703d0eb227a93c95263d7789e5db2f29b3d4d33682429189898bd3c8915b8555` (59) |
| `dfMaybeActive_neg` | theorem | R1b | `propext` | `fecaa793c10dc6cd77cdebbe3bd2742ef7cb16d7e6b1ada065aba31d547f5e88` | `f04ec47c2820abf6cccbddee0a379a7ab4789001391f956c4ff2fd98eb9f5bde` (50) |
| `dfMaybeActive_of_maybeActive` | theorem | R1a, R1c | `Classical.choice`, `Quot.sound`, `propext` | `da3efb781db6af4c797071813d1245866974366efc3a2c6ab2214192aeb2419b` | `2f899b6f0b6fc72022b5ce997e5727d126f053559078189ae01a1d3b4e92474d` (53) |
| `dfMaybeActive_pos` | theorem | R1b | `propext` | `b3a3af9ba689afd91fe3a9c1d4a910ddb67ace8940c268ad29a2569ccead8d97` | `f04ec47c2820abf6cccbddee0a379a7ab4789001391f956c4ff2fd98eb9f5bde` (50) |
| `dfOut` | def | R1a | `propext` | `522b092b3f50510d3aa34e2cbbf825075a6b7e9f45e38adf90d709eceb58f6d7` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `dfStep` | def | R1a | `propext` | `da3dcd9015ee34088648db118cefc490d42e18b3b691b81cec38a08797868422` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `Dom` | def | R2 | none | `64da0fe1dbbd59794ff304a98f9f0b9bb75440bd20440aee0e291114e96919d1` | `51d01d6bfa38438815c51578fc6dc65bdba9821a69845fb23911d7d63c02a9f9` (1) |
| `dom_iff_not_pathVia` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `360e4008a6e49904d278b3fa72385ec0e5af08e388a954cdf50508c1a9b95499` | `8d818396377820f709aaeb682f3c0b1b7d4527afc9a5f5267cdfd7b545ffe101` (6) |
| `dom_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `1c2b1fafb764fc1bfa5e2e5b565f93a1fb6d7b2d4232216721aaf05a8fff7a42` | `93ff47fdd601218cd1473afcf2a189352e3ac661f798862749ecbbb408c18b67` (28) |
| `dom_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `36018f06882f6d8e9ca46cc8416fdf4a77a688894add9bbd0bf61a1760a930d9` | `6b96092876c3a51698428e7c72d3bb663bb49e1ce0f247789e5715b66a335f0a` (29) |
| `dom_unreachable` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `c408e22b98fff7787a495733abe3ad53c3f02f60063800620fd8a108cbac4b6c` | `daa951fdfb2bfa47db1a18bda33fe093df46b0e8c0a77b8853302bb73e039d09` (27) |
| `DomGuard` | def | R2 | none | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `domGuard_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `7eb269743064476ebd8308987132f02f63928b7c3e1e186d07347fa715fcd77c` | `195652edacbef8a3c2376f82d345e00bdb000585e32a5207ffa72e069c816955` (31) |
| `domGuard_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `40de72decc56c8715e1434aae3f1515de9e64c62921542df60dfd3efea200ac6` | `a3d0c5242b50bb61127aab6fac19f37bf039a381225efe5b2226fd4560ac5fdd` (31) |
| `domGuard_pos_argLoop` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `e43f6b5c56e43cb7079180ca58dd544464c99be2bdaa86a6b0eaa31c77ba9878` | `873619bc0a3586fc8605c35598fe8c46db3f647cf47cfd4f6c6602d9b26d5422` (31) |
| `domGuard_pos_continue` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `c012aaa502e54b9262efc6df92c513206d1a4c551b05920e261fdbcd728ec831` | `c2556823cb96cedf17286b036b75c8e51f6ba9b85a9918ac558b86a1e4a32422` (31) |
| `DominatorAccepts` | def | R2 | `propext` | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `dominatorAccepts_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `3c20fba03ad857902573a0ac18e95eab64440c0de4fcbdf0b51c8e066ac0e8c6` | `cc1053cd497043515ab611f88aa8f6f7cf8ace3308577e4f84b4c82aa4a69f12` (62) |
| `dominatorAccepts_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `7fcfa5ec90279ece9f387fa42eba1eaf6d2d566dad06f8b5026347380be13b3f` | `1274a8e2782f02429a86e754f820a630203e17fcf3f5ed14463a65440a916888` (62) |
| `dominatorAccepts_safe_pLoopOK` | theorem | R2, R2c | `Classical.choice`, `Quot.sound`, `propext` | `f4836ffbbeb8cfeb7bc7256ac3afe7e7f16ded7a06451555829e83cb2298ea4c` | `a999f4ad51fe7674ebce42e852b7ca73f89a33d12123a115fc124e20539f64f4` (114) |
| `dominatorAccepts_tight_pWriteDuringRes` | theorem | R2c, R7c | `Classical.choice`, `Quot.sound`, `propext` | `0b0188cde50f0e4701f4ac2dd29d95602fbd1a6b85ac20959b3358b4b7f01ce5` | `701db8ecbca339a5c93fe7b79528a39efd4914cfdfac18950862f1aaa9d5adf9` (115) |
| `DomRegionReachesA` | def | R2b | none | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `domRegionReachesA_neg` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `057ac17411b45e1e4d08da1add0d00d9c335648127ff5107df0e4955255b4e61` | `8089480c222b6c945ef0eea3b4e601714ef0ad2524cae0ff7c71c6bac0e200e5` (29) |
| `domRegionReachesA_of_activationStaysReachable` | theorem | R2b | none | `745efa0223f20d49c838b0c80165bb04e36f8c768793c14523f219604a71ad81` | `7fc875a0fa049dd37727950b856509c4326dbe0968cbef36852ea41a182a1416` (25) |
| `domRegionReachesA_pos` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `81aa78c9f5e6ef3e5fd0127ea778242f87cec38e3dfc3e3b86c8c3a33d3639bc` | `c437ac87bcc1f2c43edf95c7e012c9979c4ca4604223b4396c118129d797af50` (29) |
| `Edges` | abbrev | R1b | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `edges_eq_succ_of_noUnwind` | theorem | R2a | `Quot.sound`, `propext` | `e4005b807a946904810d8e28a58eaa7f921ca81c2be64c67d6d6b672ade0a966` | `2c1ed8b20d0382393f81645a6056e5ae6216bff91986ad33c52430cbe009a0f8` (18) |
| `ExactPhaseAccepts` | def | R1b | `propext` | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `exactPhaseAccepts_hypotheses_hold_pPush` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `62622ea7b3431ccfc4b42c87198e55cbd54ec29640efb2afc1b0a28647327a01` | `7c539713e20e07358d297b030d83e633b9ed6c52405ba33100b3c09370db4697` (61) |
| `exactPhaseAccepts_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `d1d8809429c452f974ed452b0dde8924f9c49f94efa0e57fe1695b1ead049161` | `8ba3c814cfabf8f99b7f092a4b166b296db0d2587c53b024f7162d7ec9bd5fe1` (61) |
| `exactPhaseAccepts_no_active_live_shared` | theorem | R1b | `Quot.sound`, `propext` | `814feec33af54815583900fd91e3acd394c76881ead15b3723485fa58cef388f` | `302a30252b1bc73a18e8175e4a3bf64258a74573d3ce4996cecbff10a3ae9fd2` (56) |
| `exactPhaseAccepts_not_iterDataflowAccepts_pUnreachMerge` | theorem | R1d | `Classical.choice`, `Quot.sound`, `propext` | `e77edbfe0e909824e00aeb547213308c77c52ef2a8fa4a9c54fcd09f670cbb1d` | `d718357330347c3f98d655bd3d746742c354e40ba0882c433a039231adad87b6` (118) |
| `exactPhaseAccepts_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `62622ea7b3431ccfc4b42c87198e55cbd54ec29640efb2afc1b0a28647327a01` | `7c539713e20e07358d297b030d83e633b9ed6c52405ba33100b3c09370db4697` (61) |
| `exactPhaseAccepts_tight_pBreak` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `c6a5653973c19711d92717ee4260f0344567ed167683193eab07200d4f447577` | `bfcc86b4bce9008f75392c7f6c6eb92523449f349a885c7db4cb8bd4d465129c` (108) |
| `exec` | def | R1b | `propext` | `d93aa53909b07259da6c11991ccea9f985433f28cd092e39beb656fe8e41b087` | `49fac851233cf39d138421e96d9b30e27adf7190c4bcc06722a5659a67df6f02` (27) |
| `exec_foreignRead_of_reserved` | theorem | R1b | `propext` | `58892bec90f63b05e7b429f1d86ce080c1e39d3015e1d69401f106a759d79db9` | `0e9f7010f2b6023ebe2cb381625a750a711bc9a0a68e5b7b057e898d93825f61` (54) |
| `exec_foreignRead_of_reserved_hypotheses_hold_pPush` | theorem | R1b | `propext` | `207c2598e1c3e6909e3129162b1735b2d72f1028e7a8a54566e5e0b2ccb25e00` | `46e6e2cf8896b6b8e45a961554a0b60d1b2eed6d49b7c8e9d06b54a0bee680c4` (84) |
| `exec_readX_active_freezes` | theorem | R1b | `propext` | `9dd0dca0caa6aaf24be44877ed1e80daa6fb9e916ee3a29f8f19f8811765c38d` | `0e9f7010f2b6023ebe2cb381625a750a711bc9a0a68e5b7b057e898d93825f61` (54) |
| `explore` | def | R1d | `propext` | `99c2eb2a7e1e97553fd2d9d18ed286b8ff90aa7e2f3b17d0053f7b16919d3490` | `e95e699337a38dad01d2bd0435461afded08c2dd40f44495ba9de70cab17634a` (24) |
| `Flagged` | def | R1b | `propext` | `b40bfd57fda9002ec16d784eac376f9d92e7d3e27009ce3dcbda55544734ed0e` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `foreignRead` | def | R1b | `propext` | `c521feba7551dac65964f69d9e03d07ae1982adad92e3a25d2eb8713c2de4113` | `345bd3fedbc078e3152dd3500f0adbf5c1474fb3f5a89ec4d0ff9f2abf35d84e` (6) |
| `foreignWrite` | def | R6b | `propext` | `c521feba7551dac65964f69d9e03d07ae1982adad92e3a25d2eb8713c2de4113` | `345bd3fedbc078e3152dd3500f0adbf5c1474fb3f5a89ec4d0ff9f2abf35d84e` (6) |
| `GenReach` | def | R1a | `propext` | `8d836e97def2ba349213615a7ec45223200ea642f26276a15a26e2c0c7ffd5b5` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `guardedDomPhase` | def | R5a | `Classical.choice`, `Quot.sound`, `propext` | `8d836e97def2ba349213615a7ec45223200ea642f26276a15a26e2c0c7ffd5b5` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `IsActiveDom` | def | R2 | none | `8d836e97def2ba349213615a7ec45223200ea642f26276a15a26e2c0c7ffd5b5` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `isActiveDom_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `cc27afd4cb1a9efe63eac9f832854a21c0c5547a393f08cc297b5150e6a44974` | `4e77196762a8fda465330332496b327e4f733332c080d9e21a26d2b59295ae11` (30) |
| `isActiveDom_of_maybeActive_of_domRegion` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `f6d9f6b46a9fc016f042ea865ed658b2ab556e0c870b697eb94ac2ae0a2ba070` | `c1f5b4835a2ceb2ceb418d77921755ab1aad1e4c02a6c5748c2d20dc8e303928` (51) |
| `isActiveDom_of_maybeActive_of_reentryFree_domRegionReachesA_noUnwind` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `f6d9f6b46a9fc016f042ea865ed658b2ab556e0c870b697eb94ac2ae0a2ba070` | `c1f5b4835a2ceb2ceb418d77921755ab1aad1e4c02a6c5748c2d20dc8e303928` (51) |
| `isActiveDom_of_maybeActive_of_succWalks` | theorem | R2a | `Classical.choice`, `Quot.sound`, `propext` | `55e2379dd68f61068427e462a5f782cb64707b096cc22aceb989e710c45c6e32` | `190dd0d894efb35f15e0631f4b23ca8fc389f65321e566b1cf97df2afcf4feba` (50) |
| `isActiveDom_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `5fefabe92ab488c23af9b388ceef46416294783495401a9818c64cdc83bb0829` | `4e77196762a8fda465330332496b327e4f733332c080d9e21a26d2b59295ae11` (30) |
| `IsCleanup` | def | R7a | none | `8d836e97def2ba349213615a7ec45223200ea642f26276a15a26e2c0c7ffd5b5` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `isCleanup_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `bb5994fca9d8976995a391e9b9cdc641cae3e2e726b60e1ead0d57ec2bca3909` | `fe14bc4f88700de77517a5ff6f61cf023dc7b71b0709ff705b666b53f2eea2db` (27) |
| `isCleanup_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `8368758f341bd0f3032d3e758b01d1bbbde538fd17720c1df0ba1e777ec40fb4` | `fe14bc4f88700de77517a5ff6f61cf023dc7b71b0709ff705b666b53f2eea2db` (27) |
| `IsWalk` | def | R1b | none | `19c59b30d00a44b57fe78ba5aa3f03c7c4849d1ac7dcded6639cf2f587f1be0f` | `51d01d6bfa38438815c51578fc6dc65bdba9821a69845fb23911d7d63c02a9f9` (1) |
| `isWalk_succ_of_not_isCleanup` | theorem | R7a | `Quot.sound`, `propext` | `381b7e3dae1d3a8cf2eed05b115281b2e2b406cb05add52ed2232b57fc635e7f` | `947b1b4c471c7b91413da5f9cb823ca9a3138ddc93c3d9cccbddb5389c7b055f` (22) |
| `IterDataflowAccepts` | def | R1c | `propext` | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `iterDataflowAccepts_hypotheses_hold_pPush` | theorem | R1c | `Classical.choice`, `Quot.sound`, `propext` | `3c24aefcf6892a57b2d6d1160c9414d43db000153816666b8eec55e2b9601163` | `b62c3dbd95bb8536234e9b81f8fa46eec3efc34d19ed0bdb01f0b460a6839097` (67) |
| `iterDataflowAccepts_iff_hypotheses_hold_pPush` | theorem | R1d | `Classical.choice`, `Quot.sound`, `propext` | `a49754f44eea72b81fe2af408c424bb2a1c91d0c4e59683d397e6d4d3224c754` | `53a457ddfd87e74c8e9fc268234073b646d6abcb5b3de33417c3cf89ff34d230` (28) |
| `iterDataflowAccepts_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `ec12d5d58e5abf2174db97c5c43d459432cf46edeeae4bc8610afb1a9516d299` | `58b0ff78136ecf671485a1a7e6b72f439cb143034bf281d6879b1a0185e76400` (67) |
| `iterDataflowAccepts_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `3c24aefcf6892a57b2d6d1160c9414d43db000153816666b8eec55e2b9601163` | `b62c3dbd95bb8536234e9b81f8fa46eec3efc34d19ed0bdb01f0b460a6839097` (67) |
| `iterDataflowAccepts_tight_pBreak` | theorem | R1c | `Classical.choice`, `Quot.sound`, `propext` | `93f7c61db9b1c3b7021fe81d6d74c6155fd1d0a3272c2504a8478bedda6ca2f9` | `5a73060a73cdb580c3e4f1dd0b67d6337966ad58a3abf1f0b04025d11c749ee5` (117) |
| `literalPdomPhase` | def | R5d | `Classical.choice`, `Quot.sound`, `propext` | `8d836e97def2ba349213615a7ec45223200ea642f26276a15a26e2c0c7ffd5b5` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `literalRepairB_rejects_pBreak` | theorem | R5d | `Classical.choice`, `Quot.sound`, `propext` | `2e92fdd4eda98e4e535f5ed3fd3d352930ca34262f4a8491b7be3275fa704294` | `573997789f06a08c065d741e5f3bd01a5a57d1a887f1e5b48b01c0e6552584a2` (74) |
| `LiteralRepairBAccepts` | def | R5d | `Classical.choice`, `Quot.sound`, `propext` | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `LoanLive` | def | R1b | `propext` | `8d836e97def2ba349213615a7ec45223200ea642f26276a15a26e2c0c7ffd5b5` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `loanLive_iff` | theorem | R1b | `propext` | `5c0a2b8354d9122361e7ecbb524c71cb1743b7af7033362a13dced5b8c9dfce6` | `beb6b0c13674dd9f18d0187227135fcc7fdf17869f324bcf1e140333e26b8269` (48) |
| `loanLive_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `056ebe49188e506bc3775f921ac8d59c306b3624a42572559adbb21e65845c04` | `732280c2abe0178056c03e570cf5efed4a695f9069aa578be6eac482471aa467` (52) |
| `loanLive_neg_at_R` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `5b729db30aaf4e4ffaa5d4a1ae3e1e3fb72222f3801ce69e8f9a64725256ce36` | `1148104c24c3fa8276b452112b7ba36ec837055ee9dc22993c7a80e6f90b1559` (52) |
| `loanLive_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `ea192ad9d64e3e85d4b12674d790324650d5bf6c5f2d5c406dee81cc71b2082d` | `732280c2abe0178056c03e570cf5efed4a695f9069aa578be6eac482471aa467` (52) |
| `MaybeActive` | def | R1a | `propext` | `8d836e97def2ba349213615a7ec45223200ea642f26276a15a26e2c0c7ffd5b5` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `maybeActive_iff` | theorem | R1a | `Quot.sound`, `propext` | `850c346131ec4d3bbcaba769ffe536d561ee4e807a32b944c896ef35687a0cde` | `2f9c962639ed0eed0f7fdf7bc397aab5ba60bc61e93ced372b55787bc4632d73` (46) |
| `maybeActive_in_fact_pLoopOK` | theorem | R1a | `Classical.choice`, `Quot.sound`, `propext` | `dacc353f237f615b52fffdd98c748a782451bfd3e65ea8a67f38ed4964c43c6f` | `ad512de67406f1997e12a3acb41521614ceafd569fc8e20e5f3186fed4fdc825` (50) |
| `maybeActive_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `227a9fdb7d8711e03d36941d65db977e933f97351047f26622b916c0b302d9be` | `042ebc780a9221dfa7353ac4a60a02c531b0d3678393b2191a1a4e48b0e92cef` (50) |
| `maybeActive_neg_endLoan` | theorem | R4 | `Classical.choice`, `Quot.sound`, `propext` | `8a45d2ce2c2c76dc5095def5267ce671fe449f50c584b861fa49f318b6474f8a` | `ced8c480e958e917711b13f1ceb57373f3b2b8645cebf122f0e39db3046215f1` (50) |
| `maybeActive_pEndBeforeA_run_init` | theorem | R1a | `Classical.choice`, `Quot.sound`, `propext` | `e26481244040da7a4dfc16dd41a14bfb1bdc804ed168d7abbdab2eecc691e10f` | `8e75ff42f95f3319c67cac023fdbfb2320c994991999040bf0d9937627922e61` (96) |
| `maybeActive_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `0f0e22b5c45222cfb437d8e52100be68155f828ff883f959e29c3fb73ef12e4c` | `1647eba057f5a2043734e803dfe8baa541e4007fabb982ccc2d74a8fb3283052` (50) |
| `maybeActive_tight_pCleanupRead` | theorem | R7a | `Classical.choice`, `Quot.sound`, `propext` | `1b4841628f9850894c26b2049e1e2c43724e4150cbe9d902c3b0b66d4234f7bc` | `9e1a6df3fa493e3a24391e1d9f02d6f961e4c56be55c4e5ebebe5074cd0cb323` (57) |
| `maybeActive_tight_pLoopOK` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `c539f1e90d3addf5685ba60eed8ec7eaf1fc160e298b32cbd83f2252080d28a7` | `777e36ec2dece82db29fd668a7d544d521f94020209382e7622965415364cc54` (56) |
| `maybeActive_tight_pPush` | theorem | R2a | `Classical.choice`, `Quot.sound`, `propext` | `505a00b14a0fc2f4c9065de6b8ba2da65100066da9f2d6183ad8a39f67138e4a` | `c52e3569be947d1ebfd76bcc674aec0f6f3729f7ae45ce5c8939e4d10450b826` (55) |
| `not_isCleanup_of_cleanupReadsUnderDeadLoan` | theorem | R7c | `propext` | `2f9abe0c0db64ef567b65554f1940c26cf6296f6b3a9c12fcfa8ba318554c929` | `a8f6579762a3de4b031765ae41675d3c3c413a1129fe8d728009d9d7103295fd` (53) |
| `notCleanup_hypotheses_hold_pCleanupRead` | theorem | R7a | `Classical.choice`, `Quot.sound`, `propext` | `fdab7774c55520063601e2d23bc7e469583af2364b7f7bd5562817f4689baaf2` | `8922f9c7fb8035b70ffb65ae68ab24a464d9daf2131ed8698604568389b44d35` (55) |
| `NoUnwind` | def | R2 | none | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `Op` | inductive | R1b | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Op.isRead` | def | R1b | `propext` | `cc54d5ee2ffc2801b6b49d84c81841b264ac6a30aba70d758fb22d589018bdb7` | `e452139d63a49f6b4184da4b0f8c40ec8837dd0c2f767fc21fd5d9d950986bd6` (13) |
| `Outcome` | inductive | R1b | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `pArgLoop` | def | R2b | `propext` | `845c62fea2932f951f8f4319d5faf126919b9ce7151409231658f5e0a239cae4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `PathVia` | def | R1a | none | `6983b34c687dc81e87b998d11360c2cd073994c9a07c662772879fa7306dfb7b` | `51d01d6bfa38438815c51578fc6dc65bdba9821a69845fb23911d7d63c02a9f9` (1) |
| `pathViaB` | def | R1b | none | `bfde9529df6110ec1ca821ed83dc621e64d000f85e35d96e3fee2e298b756347` | `51d01d6bfa38438815c51578fc6dc65bdba9821a69845fb23911d7d63c02a9f9` (1) |
| `pathViaB_iff` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `e84d6bedf323b8bd7d59fdb34277f430e8fcae8974aca7bd3ed51bca713b4561` | `ff74e526cb836f7bf9e19eac576901d8f75bf5d44de0bf4a8d64e416406d3d56` (10) |
| `pBreak` | def | R1a | `propext` | `b71a0d3e445c28b420edafe67866e6c31bc22fb86f6fc1b6e1033afccd044af3` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pBreakDead` | def | R3 | `propext` | `664c64ebde599201c700e7ebdaff41e697c6a8bbce307df2d23f7e3e6a88c1bd` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pBreakHoisted` | def | R3 | `propext` | `b71a0d3e445c28b420edafe67866e6c31bc22fb86f6fc1b6e1033afccd044af3` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pBreakHoisted_rejected` | theorem | R3 | `Classical.choice`, `Quot.sound`, `propext` | `8ec7197f1f048f9e8d7d78cbf16a2dd859b9d71dbf29daadce19a048175bd9e6` | `10e5c07872d88407a0fb5fc4984b8945bd5b5e35589b984dfb9df868613e525e` (117) |
| `pBreakWrite` | def | R3 | `propext` | `b71a0d3e445c28b420edafe67866e6c31bc22fb86f6fc1b6e1033afccd044af3` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pBreakWrite_rejected` | theorem | R3 | `Classical.choice`, `Quot.sound`, `propext` | `5ab5a141288d28533baab788e8c2e3337b0d99766bd1e116064e5a66b2300304` | `76b2bff63b6207d652cf62a98c1f49871fce57df4e0f9a48c0f618817367317c` (64) |
| `pCleanup` | def | R2a | `propext` | `9e9e9abcafc5cd50801fa1b486c5de521a97f7675a1872a094ca526249302bd4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pCleanupRead` | def | R7a | `propext` | `b71a0d3e445c28b420edafe67866e6c31bc22fb86f6fc1b6e1033afccd044af3` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pCleanupRead_hypotheses_hold_safe` | theorem | R7b, R7c | `Classical.choice`, `Quot.sound`, `propext` | `11763c9ccbd8e5798782bff404e8cb4dd42ce039ebdadda586b8f9e34b8b5859` | `359cafa160139e3177f122994785a021894a7cbcefbdb50ac53554ad10e544b4` (115) |
| `pContinue` | def | R2b | `propext` | `845c62fea2932f951f8f4319d5faf126919b9ce7151409231658f5e0a239cae4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pDiverge` | def | R2 | `propext` | `3fe537167904dba6329b4671017756fbbb0f472e7bff599753da77c1656aa925` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `PDom` | def | R2 | none | `179e95696b164019388bc3a577f0dfac3d0eaf401e07ab4b5940758f9cd3c059` | `51d01d6bfa38438815c51578fc6dc65bdba9821a69845fb23911d7d63c02a9f9` (1) |
| `pdom_iff_not_pathVia` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `01d25a7454d70b785d8cbd9d0fe7bd9c64397e10c201d51c4513d2ce6a54fd4b` | `5622a3a2a15b35b7aab5c74e2db6f06b8a7b5cca4624ecc54e51c171d2a8294c` (6) |
| `pdom_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `4086ea6b7c5778e7f06b51d5d3be1ccb312a7529f2f1cbaf27f51a37b6d0e60f` | `4a9e58ec47aff4ac8376ddbbd4b5873287c070eac8efd4075bd7c210466c92e9` (26) |
| `pdom_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `0255e9487f61bba3e5fa4289eb7e85f4aecf7a2d3f2abc1dfd80f52eef507dc9` | `508e3d8abf4983736719fcb508af35efe967a08f2c9847721481e8a228da02b1` (26) |
| `pdom_tight_pBreak` | theorem | R2a | `Classical.choice`, `Quot.sound`, `propext` | `9bf797e49b6d65cc9ec344d8c14d0f5d5896b697023efaf089127780ce3c0278` | `02e6481bb2b79ddebe6f2407fc432fa9a356b91db8f8532b03892bd92c951f81` (55) |
| `pEndBeforeA` | def | R1a | `propext` | `845c62fea2932f951f8f4319d5faf126919b9ce7151409231658f5e0a239cae4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pEndThenRead` | def | R4 | `propext` | `664c64ebde599201c700e7ebdaff41e697c6a8bbce307df2d23f7e3e6a88c1bd` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `Perm` | inductive | R1b | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `pJoin` | def | R4 | `propext` | `b71a0d3e445c28b420edafe67866e6c31bc22fb86f6fc1b6e1033afccd044af3` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pJoin_separates_domRegionReachesA` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `b07e7b1c389f9507259ab9e65d98f6b870d9008261cfab8c0baed6d5935ab088` | `0b7f1c742b0021d550e4743b10f1a64d28f0df2d1466f7ba6939d2f64957f906` (56) |
| `pLoop1` | def | R2 | `propext` | `845c62fea2932f951f8f4319d5faf126919b9ce7151409231658f5e0a239cae4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pLoopBack` | def | R2 | `propext` | `3fe537167904dba6329b4671017756fbbb0f472e7bff599753da77c1656aa925` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pLoopOK` | def | R1a, R2b | `propext` | `664c64ebde599201c700e7ebdaff41e697c6a8bbce307df2d23f7e3e6a88c1bd` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pPush` | def | R1b | `propext` | `845c62fea2932f951f8f4319d5faf126919b9ce7151409231658f5e0a239cae4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pPush_safe_accepted` | theorem | R4, R6b, R6c | `Classical.choice`, `Quot.sound`, `propext` | `a498ead51e5918af8a02031843d62221f467f6d1ef841a04ffb08e46dcdea6d1` | `3828af6fd03165b242bb00ce8b025f080742b93fcf00f5d45f77a17373f66911` (111) |
| `Prog` | structure | R1b | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Prog.edges` | def | R1b | none | `840356c7d50f6d486c387dc6d4ad07d70e6ec0d1d9e93ba1123071d046cbc787` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `Prog.isKill` | def | R1b | `propext` | `4fac87af94ab6f4d54d609d569f526aff71a5fd1413a565174789874062f44dd` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `Prog.isUse` | def | R1b | `propext` | `4fac87af94ab6f4d54d609d569f526aff71a5fd1413a565174789874062f44dd` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `Prog.op` | def | R1b | none | `7e0294df29674e57c5981831aa570898c5ab8ff9c1a32d4b8cfa4b462b302d5f` | `2126bd7051de037f9837ce94bf800223a1fc5f1501d5e2402c792482210ceeee` (24) |
| `prog_one_uninhabited` | theorem | R1b | `Quot.sound`, `propext` | `1f5fcd6c5c252dd09af90bd429eccf196c666dad418a855edb8544d399d7fd72` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `prog_zero_uninhabited` | theorem | R1b | none | `bfef3c028f664ed4f05a07fd5ccfde4d48f5d1007a2c4afc5d9286e7758b380d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pSharedDuringRes` | def | R6c | `propext` | `845c62fea2932f951f8f4319d5faf126919b9ce7151409231658f5e0a239cae4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pUnreachA` | def | R1a | `propext` | `845c62fea2932f951f8f4319d5faf126919b9ce7151409231658f5e0a239cae4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pUnreachMerge` | def | R1d | `propext` | `845c62fea2932f951f8f4319d5faf126919b9ce7151409231658f5e0a239cae4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `pWriteDuringRes` | def | R2c, R6b | `propext` | `845c62fea2932f951f8f4319d5faf126919b9ce7151409231658f5e0a239cae4` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `ReachesUB` | def | R2 | `propext` | `0cb3e1bec48712ed21de8fe35f36391dc0e7fb85cce99aea6df0f701eb8dc4ea` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `ReentryFree` | def | R2 | none | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `reentryFree_activationStaysReachable_hypotheses_hold_pArgLoop` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `cf5e1a1c52bae7c3f31e7bdae61773551576518db0cd26613399ecf224e47075` | `52b4cd47d5721c696a6d9b101111d8b5dfcce9169e074c2d1e5bb0429c6317c6` (55) |
| `reentryFree_activationStaysReachable_hypotheses_hold_pContinue` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `3315a6f9a4c6610b3528f1a888ff69ed049f5c7dda76c2b9b62b177a09b18b17` | `e2a8e947b59b476b534c48c856d54d82c75b4d67eddc6295206b0e8e278141ee` (131) |
| `reentryFree_iff` | theorem | R2b | `Classical.choice`, `Quot.sound`, `propext` | `68d9dcfe21c214b5556fd57bb7327e59c9a654639dd07c748a3f6818cf4941af` | `05a8ed03fb6423b1838bba5e05b68cfc67cddb24cd9b793873958de875758bdb` (22) |
| `reentryFree_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `be26e05d725fd19bc2a9cb7d96c80e320ab7cbe079ee81271fbb6f8fa68a59a6` | `c38a0d3d122d1eb9774b0c0f3b2020263e295a73df839f2430b1814ae31c5e65` (26) |
| `reentryFree_of_acyclic` | theorem | R2a | none | `e847ad68651ef5f369854886fc7c55dbe6133e94600243b469140ea09372bbf8` | `395b2647f5669edce69118b3d2ab8c17204919ef251ebc11edf984fdc16ac938` (22) |
| `reentryFree_pos` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `26f54c7273f54e7a0fe4f70e0098dce3f7d541d65ab0dc1a6465a1079e70a449` | `bf102ff2872d79bbace532ebfc0070a56ed9faba8df9ea124e1022ddb3c438b4` (26) |
| `reentryFree_tight_pLoop1` | theorem | R2b, R2c, R7a, R7c | `Classical.choice`, `Quot.sound`, `propext` | `27f71b8ae416f4a21b729357542710ac35297391e93ed0480c1bf5275a1e1436` | `9673a640eeb5ba43f43229d6391e33bc014bb63750dfaee67d15a76ed43d7ebe` (116) |
| `RepairBAccepts` | def | R5a | `Classical.choice`, `Quot.sound`, `propext` | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `repairBAccepts_neg` | theorem | R5a | `Classical.choice`, `Quot.sound`, `propext` | `3f304c976f12f4824625c23762cc7ba5550744458d2320bfa82708f019810da8` | `9ed5fe670cf2d108a2995294d04b55370330009f6d315872a489494196bddbf1` (81) |
| `repairBAccepts_pos` | theorem | R5a | `Classical.choice`, `Quot.sound`, `propext` | `4ceed38da1218291ee9bda91a6f75f4e3f06d0168f2cdee8798766d5b6f44583` | `e3ba960b67c8e564232c97d84f85670d6bd6bb2f74a7c95b3207c72a7ed090c5` (81) |
| `repairBAccepts_pos_noGuard` | theorem | R5a | `Classical.choice`, `Quot.sound`, `propext` | `044d4b88a7213bc5c40845f1f4ce6be98dd82ee49a77da4518d4ce89b55f33ed` | `8a2d01cc809b0065f0c49cdb84b3d4bc32408b077223bd2fbe2d6adb27f9da07` (81) |
| `repairBAccepts_tight_pBreak` | theorem | R5a | `Classical.choice`, `Quot.sound`, `propext` | `c5bcd21657504b077a4666c7820879b036dfae6801c8a8b569c639dff3096ce1` | `11d53fe9251ed4db5b8922f01fa472b14754b539082cb1401379a813295716a5` (130) |
| `RepairCAccepts` | def | R5c | `propext` | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `repairCAccepts_neg` | theorem | R5c | `Classical.choice`, `Quot.sound`, `propext` | `4c7c75ea73244aedad0934a3b0e047f03918e3f644edbecbd5f95fa74b7945ee` | `a81ea48efd950f3f845fd31870a468a9e6cf28ea7c573f9166a3652ac37ccdb0` (68) |
| `repairCAccepts_pos` | theorem | R5c | `Classical.choice`, `Quot.sound`, `propext` | `c29570ecb99f71878ddf7fdffcd34f41f31a91db1bbb9f6accb71f65ef7a33de` | `a44f726e0a278c879c60fef9587fdf841792ea6c595ebaebf197135b3217cac5` (68) |
| `repairCAccepts_pos_argLoop` | theorem | R5c | `Classical.choice`, `Quot.sound`, `propext` | `c6bd2f682029ebb8c904dedb642e8512c56223df723c22fc5e1c7bdd4fa6d2e6` | `f933034172f39142450b143f0b0417f766b4a1b87cf370152e9d347499220409` (68) |
| `repairCAccepts_tight_pJoin` | theorem | R5c | `Classical.choice`, `Quot.sound`, `propext` | `aa80145d330b2cb009c317ce51c7e12c278b2bf593024956c05e4c88051d39f4` | `056ab8fdc3f5496552e93270d5a89eaca8ac1b3de7fb97bf41f25bf5383b18cc` (83) |
| `RState` | structure | R1b | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `RState.init` | def | R1b | none | `2719b8a662b381314079812638cb40e259e9cdcf516398074a6318298c1392e4` | `e0b994d12afa3a8c6b59ce9a721e982e708932869298494cf09ce4936b2ed007` (10) |
| `RState.setSh` | def | R1b | none | `fbbfc2523cfcc26fca8a2df6e9e26730d2a88ce7f8390c7d3833a018a02b5c52` | `6e95e16b575ec22d64145265c9ad7daed83882abddebd387c487f7c7106cd2bc` (13) |
| `RState.sh` | def | R1b | none | `4656bababce844be3683a958c8578f70421a8fc0edb1ac209c88857ad97fd3d3` | `6e95e16b575ec22d64145265c9ad7daed83882abddebd387c487f7c7106cd2bc` (13) |
| `run` | def | R1b | `propext` | `616463eba37fcc5b829b61742a30e0287fcbc65cab0abba038f7f26cabe2e5c5` | `bb7088dc05fe8ce08786e9197ca33b13cbd1a9b06eb14ea5f4429149c6b56ebe` (28) |
| `run_activate_marks_shared_dirty` | theorem | R6c | `propext` | `0e06f7ab5b20824cd0bc92f77f51d86212c46ae3c1ce98e9cd77d16f7aecc4f6` | `ec6e37410eddcc4e31a65d4e76eca3c83d693f26f18f2baf592681eb36dd004e` (84) |
| `run_halt_reserved_writeThrough` | theorem | R1b | `propext` | `9d7ff5f8263472ae9b23b3db6c7a4c04613e346fd65b28cff6e1c7d03ccf0851` | `2aa88d8a74fe37d70d360b2a92fe2cf6d4cc5a926a14f93a1fcf2e428fc2a863` (84) |
| `run_ne_ub_of_runInv` | theorem | R1b | `Quot.sound`, `propext` | `53e4369e1efa9154f68708885335c2e57c1dd910dd7c862620cf7c693f7e007c` | `b78d61dfb7e380650dcd3e65a8988aa8f164344bc4bcfdd5606cb84f2e3fc2f6` (103) |
| `RunInv` | def | R1b | `propext` | `8a3d162dbb7e35743655852cf07457a2aa5ede9084ed3f423d070047152eb23d` | `e95e699337a38dad01d2bd0435461afded08c2dd40f44495ba9de70cab17634a` (24) |
| `runInv_init` | theorem | R1b | `Quot.sound`, `propext` | `02c304fac04a384784d2915fafe1e024cc166d3f89a2fd235d0bdcba7e2b87cb` | `bb7e24300b2f6a193daac765c568096021afb9ee820a2a072323a93a4c2ffc22` (71) |
| `runInv_step` | theorem | R1b | `Quot.sound`, `propext` | `4efd132895efef5a2944e09a705fccaf7e59c347d153f4ead857f5a78eab6ac1` | `d6de47fa32fc1f27a10a1479a39b1c2afcb4df2b8773ba65736e8e4134913f69` (97) |
| `Safe` | def | R1b | `propext` | `83c0749b1cf6da642686a8cafc53b88513b99c007917d5e9ef98c0d925533f0d` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `safe_neg` | theorem | R1b | `propext` | `ba3e05801ae6af71026551ab9716b0a57caee02abb2fc4a39ae2ce6b48123635` | `9793ea74cac525699f0e5c4dc077930ab521c4eefadf2065c841830ae104fa8d` (92) |
| `safe_of_cert` | theorem | R1d | `Quot.sound`, `propext` | `724de1ca07a7a9da8a7909c9d71539a0b13ba1d974fea10a3bbfca96d375c68e` | `70d69918a2f2d3398826cf57d05849ff90f766663af2edec2efc6e54d6e708a6` (108) |
| `safe_pos` | theorem | R1b | `Quot.sound`, `propext` | `52f03ecdf89058963a4c361b46e66537e28a7e316700b3d92b3a325da629b8fe` | `0c443500ae3d6d1b1c83b68676da557ebf12bfc68290180d1bde58de13b67bc2` (92) |
| `SharedLive` | def | R1b | none | `79d63b81afa9fb53dd1a8f8f56118620d67da653ffa4133eccfdf0442950c395` | `00be9b1be011891a38ddafe982eb85e8a19f6e7bd5962b0de6dbd1df49854d68` (14) |
| `sharedLive_iff` | theorem | R1b | `propext` | `56a92ce7f018e8edc1ee92cc9f10d98b71013ea25936ff6e5d9ba678c60042b5` | `6d55f5f4aebdbfe3d1563a3cafa988a04b7cf747a64cdd2a75c6f70df2d4401d` (126) |
| `sharedLive_neg` | theorem | R1b | `Classical.choice`, `Quot.sound`, `propext` | `cf91a9553f65644235d6b0992ec042accc434c36691edfe90665ccd1c010dd21` | `4870c33c4f9fb67919ad3b8e474f3999f3668e9c71593198ff42e6c58884e9aa` (43) |
| `sharedLive_pos` | theorem | R6c | `Classical.choice`, `Quot.sound`, `propext` | `412396d9f6d93e643f5d6d8da6a949d8af97cf87112d6fd5ced159c95ab63ec7` | `38355127a7b6226072962d5451ee8a7adfe20ca8a16740ffbe60c16b24a6c4dd` (43) |
| `SRef` | inductive | R1b | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `SSt` | structure | R1b | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `SSt.markWrite` | def | R6c | none | `b40c9adc1ecf445d64239b960a5822cd27c921c6ce39f8892a1b26f4eb94c410` | `0cc1cd9396fbf263c13c274d4e654f13a6127d7a6a2b7013c3a4f804291244e2` (2) |
| `Stmt` | inductive | R1b | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `unwinding_tight_pCleanup` | theorem | R2a, R2b, R2c, R7a, R7c | `Classical.choice`, `Quot.sound`, `propext` | `d190cb2d6e05f5798b7e6055444cab5827e1811551378d490c5a9e12c8e0ff11` | `b9070dd467556e7a427d5d1e2e81dcfd3299829820c288b3ebb869c432228fc7` (118) |

### Compiler and Miri runs on the public reproducer (`execution`, separate from the toy)

Support material `probe/` (`issue.rs`, `rustc_output.txt`, `miri_output.txt`), observed 2026-11-21:

* `rustc 1.102.0-nightly (8eb778d04 2026-11-12)`, commit `8eb778d04094d3af4b26580cab327e0413eb1e02`:
  `issue.rs` (the reproducer quoted verbatim from the top-level report of rust-lang/rust#160598)
  compiles and prints `Some(1) Some(2)`, as that top-level report states for an earlier nightly.
* Miri from `rustc 1.101.0-nightly` commit `5c543b0b8c73c7b72bc8284ced4fb22ead15734d`, with
  `-Zmiri-tree-borrows`: `Undefined Behavior: write access through <tag> … is forbidden` at
  `*r.unwrap() = 2`. With default flags (Stacked Borrows) it reports UB at a retag.

### Modeling bridges (`derived (modeling bridge)`, prose, not mechanized)

* **The dominator test.** rustc's `is_active` returns true if `activation_location.dominates(location)`,
  else false if `reserve_location.successor_within_block().dominates(location)`, else true
  (paraphrase of `compiler/rustc_borrowck/src/path_utils.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:102-119`,
  quoted in Prior art). `IsActiveDom` mirrors this with one statement per node (the successor
  within a block of `R` dominates `L` iff `R` strictly dominates `L` at statement granularity).
  Reasoning; not mechanized.
* **The documented assumptions.** The comment at
  `compiler/rustc_borrowck/src/path_utils.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:88-93` (quoted in
  full in Prior art) lists "the reservation R
  dominates the activation A" and "the activation A post-dominates the reservation R (ignoring
  unwinding edges)"; in the toy these read `Dom p.edges p.entry p.R p.A` and `PDom p.succ p.A p.R`.
* **`ReentryFree` in MIR.** The two-phase temporary is assigned at `R` and moved by its single use at
  `A`, which suggests MIR programs satisfy `ReentryFree` (not verified).
* **The early exit.** In rust-lang/rust#160598 the `break 'b` inside the argument corresponds to the
  edge `2 → 4` of `pBreak`; `let s = &v` to `borrowShared s0` at the join; `*r.unwrap() = 2` to
  `writeThrough`. On the `break` path `r` is `None` and `unwrap` panics; the toy models this with
  the halting `writeThrough` rule.
* **Reference semantics.** The permission machine follows Tree Borrows' `Reserved` → `Unique` (on the
  first local write) → `Frozen` (foreign read) / `Disabled` (foreign write), simplified; the
  activation is that first local write.

### Prior art (verified at the source, 2026-11-21)

* **rust-lang/rust#160598**, "is_active can be unsound when the activation does not dominate the
  reservation" (https://github.com/rust-lang/rust/issues/160598). Open; labels `A-borrow-checker`,
  `T-compiler`, `I-unsound`, `C-bug`, `I-prioritize`, `T-types`. Its top-level report gives the
  reproducer (quoted in `probe/issue.rs`), states that the reporter expected it not to typecheck, and
  reports that it compiles and prints `Some(1) Some(2)` on a `1.99.0-nightly` build. A Miri (Tree
  Borrows) UB message and an attribution of the problem to an early exit from between `R` and `A`
  that makes `A` fail to post-dominate `R` appear only in a collapsed `<details>` section that the
  reporter labels "LLM-written explanation of what it thinks is happening" and says they have not
  checked; that section is not relied on here (the Miri result above is from an independent run).
* **rustc source** at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`:
  `compiler/rustc_borrowck/src/path_utils.rs` lines 60–120 (`is_active`; `NotActivated` returns
  false at line 71), the assumption comment
  (`compiler/rustc_borrowck/src/path_utils.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:88-93`):
  ```text
      // Note that we assume that:
      // - the reservation R dominates the activation A
      // - the activation A post-dominates the reservation R (ignoring unwinding edges).
      //
      // This means that there can't be an edge that leaves A and
      // comes back into that diamond unless it passes through R.
  ```
  and the test
  (`compiler/rustc_borrowck/src/path_utils.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:102-119`):
  ```text
      if activation_location.dominates(location, dominators) {
          return true;
      }

      // The reservation starts *on exiting* the reservation block,
      // so check if the location is dominated by R.successor. If so,
      // this point falls in between the reservation and location.
      let reserve_location = borrow_data.reserve_location.successor_within_block();
      if reserve_location.dominates(location, dominators) {
          false
      } else {
          // Otherwise, this point is outside the diamond, so
          // consider the borrow active. This could happen for
          // example if the borrow remains active around a loop (in
          // which case it would be active also for the point R,
          // which would generate an error).
          true
      }
  ```
  `check_access_for_conflict`
  (`compiler/rustc_borrowck/src/lib.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1323-1328`):
  ```text
                  (Read(kind), BorrowKind::Mut { .. }) => {
                      // Reading from mere reservations of mutable-borrows is OK.
                      if !is_active(this.dominators(), borrow, location) {
                          assert!(borrow.kind.is_two_phase_borrow());
                          return ControlFlow::Continue(());
                      }
  ```
  `compiler/rustc_borrowck/src/polonius/legacy/loan_invalidations.rs` lines 390–396 contain the same
  `is_active` check.
* **RFC 2025** (rust-lang/rfcs `text/2025-nested-method-calls.md` at commit
  `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`; feature name `nested_method_call`): "During the
  reservation phase, reads and shared borrows of the borrowed data are permitted (but not mutation)"
  (`text/2025-nested-method-calls.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:14-15`);
  "a write to `lv` at point `P` is illegal if there is any active borrow **or** in-scope reservation of
  `lv` at the point `P`" (`text/2025-nested-method-calls.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:286-288`);
  at the activation point "we must check that there are no active borrows or
  reservations in scope (other than the reservation being upgraded)"
  (`text/2025-nested-method-calls.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:292-293`).
* **RFC 2094** (rust-lang/rfcs `text/2094-nll.md`, non-lexical lifetimes): defers nested method calls
  to RFC 2025.
* **rustc-dev-guide, "Two-phase borrows"** (`src/doc/rustc-dev-guide/src/borrow-check/two-phase-borrows.md`
  in rust-lang/rust at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`): the three sources of
  two-phase borrows; "Between the reservation and the activation point, the two-phase borrow acts as a
  shared borrow. We determine (in `is_active`) if we're at such a point by using the `Dominators` for
  the MIR graph."
  (`src/doc/rustc-dev-guide/src/borrow-check/two-phase-borrows.md@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:93-95`;
  Markdown link brackets around `is_active` and `Dominators` omitted). Its item 2
  (`src/doc/rustc-dev-guide/src/borrow-check/two-phase-borrows.md@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:91-92`)
  says the reservation point lints conflicting shared borrows; the source
  at the same commit (`compiler/rustc_borrowck/src/lib.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1312-1316`,
  the match arm `(Reservation(_), BorrowKind::Fake(_) | BorrowKind::Shared)`) continues
  silently with the comment "This used to be a future compatibility warning"
  (`compiler/rustc_borrowck/src/lib.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1313-1314`). Disagreement preserved;
  the history is in rust-lang/rust#56254 ("[NLL] prohibit "two-phase borrows" with existing
  borrows?", closed, https://github.com/rust-lang/rust/issues/56254) and rust-lang/rust#59159
  ("Tracking issue for `mutable_borrow_reservation_conflict` compatibility lint", closed,
  https://github.com/rust-lang/rust/issues/59159).
* **rust-lang/rust#46901** ("two-phase-borrows need a specification", open,
  https://github.com/rust-lang/rust/issues/46901) and **rust-lang/rust#49434** ("Tracking issue for
  generalized two-phase borrows", open, https://github.com/rust-lang/rust/issues/49434).
* **Tree Borrows** — N. Villani, J. Hostert, D. Dreyer, R. Jung, Proc. ACM Program. Lang. 9 (PLDI),
  Article 188, June 2025, https://doi.org/10.1145/3735592. Introduces the `Reserved` permission for
  mutable references "during their reservation phase": "Reserved allows local and foreign reads … When
  the reference is activated, i.e., when it first experiences a local write, its permission changes to
  a full-fledged Unique"; adds a `conflicted` flag for protected references and `ReservedIM`; "Tree
  Borrows makes no difference between mutable references with or without two-phase treatment by the
  borrow checker". Its core calculus is mechanized in Rocq (with Simuliris) to prove optimizations; it
  contains no borrow-checker phase test.
* **Stacked Borrows** — R. Jung, H.-H. Dang, J. Kang, D. Dreyer, "Stacked Borrows: An Aliasing Model
  for Rust", Proc. ACM Program. Lang. 4 (POPL), Article 41, January 2020,
  https://doi.org/10.1145/3371109. The paper text contains no discussion of two-phase borrows; the
  Tree Borrows paper states: "The original Stacked Borrows model did not support two-phase borrows at
  all. The implementation … treats two-phase borrows basically equivalent to raw pointers."
* **Aeneas** — S. Ho, J. Protzenko, "Aeneas: Rust Verification by Functional Translation", Proc. ACM
  Program. Lang. 6 (ICFP), Article 116, August 2022, https://doi.org/10.1145/3547647 (preprint
  arXiv:2206.07185): models two-phase borrows as "reserved borrows" in a value-level operational
  semantics (created like shared borrows; cannot be copied, dereferenced or written into before
  activation). Not a CFG phase test.
* **Oxide** — A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, "Oxide: The Essence of Rust",
  arXiv:1903.00982: a formal calculus of Rust borrowing with non-lexical lifetimes; whether and how it
  models two-phase borrows was not checked at the source.
* **Dataflow analysis.** G. A. Kildall, "A Unified Approach to Global Program Optimization", POPL 1973,
  https://doi.org/10.1145/512927.512945; J. B. Kam, J. D. Ullman, "Monotone Data Flow Analysis
  Frameworks", Acta Informatica 7(3), 1977, https://doi.org/10.1007/BF00290339 (the fixpoint equals the
  meet-over-paths solution for distributive frameworks); X. Leroy, "Formal Verification of a Realistic
  Compiler", Commun. ACM 52(7), 2009, https://doi.org/10.1145/1538788.1538814 (CompCert, which
  mechanizes Kildall's solver in `backend/Kildall.v`).
* **Post-dominance with loops.** A. Podgurski, L. A. Clarke, IEEE TSE 16(9), 1990,
  https://doi.org/10.1109/32.58784 (weak control dependence, defined through strong post-dominance,
  which additionally bounds path length and so accounts for loops); V. P. Ranganath, T. Amtoft,
  A. Banerjee, J. Hatcliff, M. B. Dwyer, ACM TOPLAS 29(5), Article 27, 2007,
  https://doi.org/10.1145/1275497.1275502 (control dependence for CFGs with non-termination and no
  unique exit); D. Wasserrab, "Towards Certified Slicing", Archive of Formal Proofs, 2008,
  https://isa-afp.org/entries/Slicing.html (post-dominance and weak control dependence mechanized in
  Isabelle/HOL). A condition bounding the length of `A`-avoiding walks from `R` would be close to
  strong post-dominance and would exclude every loop between `R` and `A`; R2b uses the weaker
  reachability condition `ActivationStaysReachable` instead (derived).
* **Novelty search.** Web searches for mechanized treatments of two-phase borrows and of rustc's
  dominator-based phase test found Aeneas and Tree Borrows (above), and no mechanized statement
  relating a dominator phase test to a path-level phase fact or to a reference aliasing semantics.

### Auxiliary definitions and lemmas cited by name

```lean
-- ToyTwoPhase/Lemmas.lean:152-153
def GenReach (p : Prog n) (L : Fin n) : Prop :=
  ∃ y ∈ p.edges p.A, PathVia p.edges (fun x => !p.isKill x) y L
```

```lean
-- ToyTwoPhase/Lemmas.lean:382-386
def RunInv (p : Prog n) (L : Fin n) (σ : RState) : Prop :=
  PathVia p.edges (fun _ => true) p.entry L ∧
  ((σ.perm = .frozen ∨ σ.perm = .invalid) → ¬ LoanLive p L) ∧
  (σ.perm = .active → MaybeActive p L) ∧
  (∀ s, (σ.sh s).dirty = true → ¬ SharedLive p s L)
```

```lean
-- ToyTwoPhase/Results.lean:23-25
theorem accepts_of_phase_imp {p : Prog n} {ph₁ ph₂ : Fin n → Prop}
    (himp : ∀ L, (p.op L).isRead = true → LoanLive p L → ph₁ L → ph₂ L)
    (h : Accepts p ph₂) : Accepts p ph₁ := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:81
theorem activationStaysReachable_neg_diverge : ¬ ActivationStaysReachable pDiverge := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:76
theorem activationStaysReachable_neg_exit : ¬ ActivationStaysReachable pBreak := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:78
theorem activationStaysReachable_neg_loopBack : ¬ ActivationStaysReachable pLoopBack := by …
```

```lean
-- ToyTwoPhase/Lemmas.lean:804-805
theorem activationStaysReachable_of_acyclic_pdom {p : Prog n} (hac : Acyclic p.succ)
    (hpd : PDom p.succ p.A p.R) : ActivationStaysReachable p := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:69
theorem activationStaysReachable_pos : ActivationStaysReachable pLoopOK := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:71
theorem activationStaysReachable_pos_argLoop : ActivationStaysReachable pArgLoop := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:74
theorem activationStaysReachable_pos_continue : ActivationStaysReachable pContinue := by decide
```

```lean
-- ToyTwoPhase/Relations.lean:131-132
theorem acyclic_iff (E : Edges n) :
    Acyclic E ↔ ∀ x : Fin n, ∀ y ∈ E x, ¬ PathVia E (fun _ => true) y x := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:33
theorem acyclic_neg : ¬ Acyclic pLoop1.succ := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:32
theorem acyclic_pos : Acyclic pBreak.succ := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:149
theorem alwaysActiveAccepts_neg : ¬ AlwaysActiveAccepts pPush := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:147
theorem alwaysActiveAccepts_pos : AlwaysActiveAccepts pBreakDead := by decide
```

```lean
-- ToyTwoPhase/Semantics.lean:135-140
def certOK (p : Prog n) (S : List (Fin n × RState)) : Bool :=
  S.all fun q =>
    match exec (p.op q.1) q.2 with
    | .ok σ' => (p.edges q.1).all fun y => S.contains (y, σ')
    | .halt => true
    | .ub => false
```

```lean
-- ToyTwoPhase/DefExamples.lean:89
theorem cleanupReadsUnderDeadLoan_neg : ¬ CleanupReadsUnderDeadLoan pCleanup := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:88
theorem cleanupReadsUnderDeadLoan_pos : CleanupReadsUnderDeadLoan pCleanupRead := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:329-330
theorem dfMaybeActive_iff_genReach (p : Prog n) (L : Fin n) :
    dfMaybeActive p L = true ↔ GenReach p L := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:151
theorem dfMaybeActive_neg : dfMaybeActive pBreak 2 = false := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:336-337
theorem dfMaybeActive_of_maybeActive {p : Prog n} {L : Fin n} (h : MaybeActive p L) :
    dfMaybeActive p L = true := …
```

```lean
-- ToyTwoPhase/DefExamples.lean:150
theorem dfMaybeActive_pos : dfMaybeActive pBreak 4 = true := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:93
theorem domGuard_neg : ¬ DomGuard pBreak := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:90
theorem domGuard_pos : DomGuard pLoopOK := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:91
theorem domGuard_pos_argLoop : DomGuard pArgLoop := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:92
theorem domGuard_pos_continue : DomGuard pContinue := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:85
theorem domRegionReachesA_neg : ¬ DomRegionReachesA pBreak := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:649-651
theorem domRegionReachesA_of_activationStaysReachable {p : Prog n}
    (h : ActivationStaysReachable p) : DomRegionReachesA p :=
  fun y hy hyR x hxR _ hpath => h y hy hyR x hxR hpath
```

```lean
-- ToyTwoPhase/DefExamples.lean:83
theorem domRegionReachesA_pos : DomRegionReachesA pJoin := by decide
```

```lean
-- ToyTwoPhase/Relations.lean:79-80
theorem dom_iff_not_pathVia (E : Edges n) (entry a b : Fin n) :
    Dom E entry a b ↔ ¬ (b ≠ a ∧ PathVia E (fun x => x != a) entry b) := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:26
theorem dom_neg : ¬ Dom pBreak.edges pBreak.entry pBreak.A 4 := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:24
theorem dom_pos : Dom pBreak.edges pBreak.entry pBreak.R pBreak.A := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:28
theorem dom_unreachable : Dom pJoin.edges pJoin.entry 6 4 := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:140
theorem dominatorAccepts_neg : ¬ DominatorAccepts pBreakHoisted := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:139
theorem dominatorAccepts_pos : DominatorAccepts pPush := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:114
theorem edges_eq_succ_of_noUnwind {p : Prog n} (hnu : NoUnwind p) : p.edges = p.succ := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:142
theorem exactPhaseAccepts_neg : ¬ ExactPhaseAccepts pBreak := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:365-367
theorem exactPhaseAccepts_no_active_live_shared {p : Prog n} (h : ExactPhaseAccepts p)
    {s : SRef} {L : Fin n} (hma : MaybeActive p L) (hsl : SharedLive p s L)
    (hl : LoanLive p L) : False := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:141
theorem exactPhaseAccepts_pos : ExactPhaseAccepts pPush := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:111-114
theorem exec_foreignRead_of_reserved (σ : RState) (h : σ.perm = .reserved) :
    exec .readX σ = .ok σ ∧
      (∀ s, exec (.borrowShared s) σ = .ok (σ.setSh s ⟨true, false⟩)) ∧
      (∀ s, (σ.sh s).dirty = false → exec (.useShared s) σ = .ok σ) := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:124-125
theorem exec_foreignRead_of_reserved_hypotheses_hold_pPush :
    ∃ σ : RState, run pPush RState.init [0, 1] = .ok σ ∧ σ.perm = .reserved := …
```

```lean
-- ToyTwoPhase/DefExamples.lean:130-135
theorem exec_readX_active_freezes :
    (⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ : RState).perm ≠ .reserved ∧
    exec .readX ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ =
      .ok ⟨.frozen, ⟨false, false⟩, ⟨false, false⟩⟩ ∧
    exec .readX ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ ≠
      .ok ⟨.active, ⟨false, false⟩, ⟨false, false⟩⟩ := by …
```

```lean
-- ToyTwoPhase/Semantics.lean:181-188
def explore (p : Prog n) : Nat → List (Fin n × RState) → List (Fin n × RState)
  | 0, S => S
  | k + 1, S =>
    let new := S.flatMap fun q =>
      match exec (p.op q.1) q.2 with
      | .ok σ' => (p.edges q.1).map fun y => (y, σ')
      | _ => []
    explore p k (new.foldl (fun acc q => if acc.contains q then acc else acc ++ [q]) S)
```

```lean
-- ToyTwoPhase/DefExamples.lean:62
theorem isActiveDom_neg : ¬ IsActiveDom pPush 2 := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:655-657
theorem isActiveDom_of_maybeActive_of_domRegion (p : Prog n) (hre : ReentryFree p)
    (hdr : DomRegionReachesA p) (hnu : NoUnwind p) (L : Fin n) (hL : MaybeActive p L) :
    IsActiveDom p L := by …
```

```lean
-- ToyTwoPhase/Lemmas.lean:591-594
theorem isActiveDom_of_maybeActive_of_succWalks (p : Prog n) (hre : ReentryFree p)
    (hasr : ActivationStaysReachable p) (L : Fin n)
    (hsucc : ∀ π : List (Fin n), IsWalk p.edges (π ++ [L]) → IsWalk p.succ (π ++ [L]))
    (hL : MaybeActive p L) : IsActiveDom p L := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:61
theorem isActiveDom_pos : IsActiveDom pPush 4 := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:87
theorem isCleanup_neg : ¬ IsCleanup pCleanup 5 := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:86
theorem isCleanup_pos : IsCleanup pCleanup 6 := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:709-710
theorem isWalk_succ_of_not_isCleanup {p : Prog n} {L : Fin n} (hnc : ¬ IsCleanup p L) :
    ∀ π : List (Fin n), IsWalk p.edges (π ++ [L]) → IsWalk p.succ (π ++ [L])
```

```lean
-- ToyTwoPhase/DefExamples.lean:144
theorem iterDataflowAccepts_neg : ¬ IterDataflowAccepts pBreak := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:143
theorem iterDataflowAccepts_pos : IterDataflowAccepts pPush := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:55
theorem loanLive_neg : ¬ LoanLive pBreak 7 := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:57
theorem loanLive_neg_at_R : ¬ LoanLive pLoopOK pLoopOK.R := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:53
theorem loanLive_pos : LoanLive pBreak 4 := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:50-51
theorem maybeActive_in_fact_pLoopOK :
    MaybeActive pLoopOK pLoopOK.R ∧ ¬ MaybeActive pLoopOK pLoopOK.A := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:39
theorem maybeActive_neg : ¬ MaybeActive pPush 2 := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:41
theorem maybeActive_neg_endLoan : ¬ MaybeActive pEndThenRead 4 := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:45-46
theorem maybeActive_pEndBeforeA_run_init :
    MaybeActive pEndBeforeA 4 ∧ run pEndBeforeA RState.init [0, 1, 2, 3] = .ok RState.init := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:37
theorem maybeActive_pos : MaybeActive pBreak 4 := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:732-734
theorem not_isCleanup_of_cleanupReadsUnderDeadLoan {p : Prog n}
    (hcl : CleanupReadsUnderDeadLoan p) {L : Fin n} (hread : (p.op L).isRead = true)
    (hlive : LoanLive p L) : ¬ IsCleanup p L := …
```

```lean
-- ToyTwoPhase/Programs.lean:188-195
def pArgLoop : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [2, 3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:42-50
def pBreak : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4], [5], [6], [7], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .borrowShared .s0, .useShared .s0, .writeThrough,
    .useShared .s0]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:76-83
def pBreakDead : Prog 6 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4], [5], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .readX, .nop]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:54-62
def pBreakHoisted : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2, 4], [3], [4], [5], [6], [7], []]
  unw := mkEdges []
  R := 2
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .borrowShared .s0, .useShared .s0, .writeThrough,
    .useShared .s0]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:65-72
def pBreakWrite : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4], [5], [6], [7], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .writeX, .nop, .writeThrough, .nop]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:165-172
def pCleanup : Prog 9 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], [5], [], [7], [8], []]
  unw := mkEdges [[], [], [6], [], [6], [], [], [], []]
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .nop, .nop, .readX, .writeThrough, .nop]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:177-184
def pCleanupRead : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], [5], [], [7], []]
  unw := mkEdges [[], [], [6], [], [6], [], [], []]
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough, .nop, .readX, .nop]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:200-207
def pContinue : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [1, 3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:109-116
def pDiverge : Prog 7 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4, 6], [5], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .readX, .writeThrough, .nop]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:211-218
def pEndBeforeA : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .endLoan, .nop, .readX]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:132-139
def pEndThenRead : Prog 6 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], [5], []]
  unw := mkEdges []
  R := 1
  A := 2
  stmt := mkStmt [.nop, .nop, .nop, .endLoan, .readX, .writeThrough]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:121-128
def pJoin : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2, 5], [3, 5], [6], [], [6], [7], []]
  unw := mkEdges []
  R := 2
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .nop, .readX, .writeThrough, .nop]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:87-94
def pLoop1 : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [2, 4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .nop]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:98-105
def pLoopBack : Prog 7 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4, 6], [5], [1], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .readX, .writeThrough, .nop]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:30-37
def pLoopOK : Prog 6 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], [1, 5], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough, .nop]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:20-27
def pPush : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:153-160
def pSharedDuringRes : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .borrowShared .s0, .nop, .useShared .s0]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:232-239
def pUnreachA : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .readX]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:222-229
def pUnreachMerge : Prog 5 where
  entry := 0
  succ := mkEdges [[3], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 2
  stmt := mkStmt [.nop, .nop, .nop, .readX, .writeThrough]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Programs.lean:142-149
def pWriteDuringRes : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .writeX, .nop, .writeThrough]
  hRA := by decide
```

```lean
-- ToyTwoPhase/Relations.lean:105-106
theorem pdom_iff_not_pathVia (E : Edges n) (a b : Fin n) :
    PDom E a b ↔ ¬ ∃ x : Fin n, E x = [] ∧ x ≠ a ∧ PathVia E (fun y => y != a) b x := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:31
theorem pdom_neg : ¬ PDom pBreak.succ pBreak.A pBreak.R := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:29
theorem pdom_pos : PDom pPush.succ pPush.A pPush.R := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:13
theorem prog_one_uninhabited (p : Prog 1) : False := …
```

```lean
-- ToyTwoPhase/DefExamples.lean:11
theorem prog_zero_uninhabited (p : Prog 0) : False := p.entry.elim0
```

```lean
-- ToyTwoPhase/DefExamples.lean:68
theorem reentryFree_neg : ¬ ReentryFree pLoop1 := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:755
theorem reentryFree_of_acyclic {p : Prog n} (hac : Acyclic p.succ) : ReentryFree p := …
```

```lean
-- ToyTwoPhase/DefExamples.lean:67
theorem reentryFree_pos : ReentryFree pLoopOK := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:157
theorem repairBAccepts_neg : ¬ RepairBAccepts pBreak := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:155
theorem repairBAccepts_pos_noGuard : ¬ DomGuard pBreakDead ∧ RepairBAccepts pBreakDead := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:160
theorem repairCAccepts_neg : ¬ RepairCAccepts pBreakDead := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:159
theorem repairCAccepts_pos_argLoop : RepairCAccepts pArgLoop := by decide
```

```lean
-- ToyTwoPhase/Lemmas.lean:388
theorem runInv_init (p : Prog n) : RunInv p p.entry RState.init := by …
```

```lean
-- ToyTwoPhase/Lemmas.lean:443-445
theorem runInv_step {p : Prog n} (h : ExactPhaseAccepts p) {L L' : Fin n} {σ σ' : RState}
    (hI : RunInv p L σ) (hex : exec (p.op L) σ = .ok σ') (hL' : L' ∈ p.edges L) :
    RunInv p L' σ' := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:105-106
theorem run_activate_marks_shared_dirty :
    run pSharedDuringRes RState.init [0, 1, 2, 3] = .ok ⟨.active, ⟨true, true⟩, ⟨false, false⟩⟩ := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:101
theorem run_halt_reserved_writeThrough : run pBreak RState.init [0, 1, 2, 4, 5, 6] = .halt := by …
```

```lean
-- ToyTwoPhase/Lemmas.lean:552-554
theorem run_ne_ub_of_runInv {p : Prog n} (h : ExactPhaseAccepts p) :
    ∀ (π : List (Fin n)) (x : Fin n) (σ : RState), IsWalk p.edges (x :: π) → RunInv p x σ →
      run p σ (x :: π) ≠ .ub := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:98
theorem safe_neg : ¬ Safe pBreak := …
```

```lean
-- ToyTwoPhase/Semantics.lean:170-171
theorem safe_of_cert {p : Prog n} (S : List (Fin n × RState)) (hS : certOK p S = true)
    (hinit : (p.entry, RState.init) ∈ S) : Safe p := by …
```

```lean
-- ToyTwoPhase/DefExamples.lean:96
theorem safe_pos : Safe pPush := …
```

```lean
-- ToyTwoPhase/DefExamples.lean:60
theorem sharedLive_neg : ¬ SharedLive pBreak .s0 pBreak.A := by decide
```

```lean
-- ToyTwoPhase/DefExamples.lean:58
theorem sharedLive_pos : SharedLive pSharedDuringRes .s0 pSharedDuringRes.A := by decide
```

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. The primary check, run from the package directory:

```text
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and

1. runs `lake build` there (fails on any error);
2. rejects any Lean source that contains `sorry`, `admit` or `native_decide`, or declares an `axiom`;
3. checks, with Lean's `collectAxioms`, that every declaration of the `ToyTwoPhase` library depends
   on no axioms other than `propext`, `Classical.choice` and `Quot.sound`;
4. for every Lean name referenced by `results.json` (fields `lean`, `lean_names`,
   `nonvacuity_witness_lean`, `positive_control_lean` and hypothesis `counterexample`s) and every
   name recorded in `audit/statements.json`, recomputes the statement hash (SHA-256 of the Lean
   `repr` of the declaration's type) and the closure hash (SHA-256 of the sorted, newline-joined
   lines `name : repr type`, followed by ` := repr value` for non-theorem constants, of every
   package-local constant reachable from that type through types, non-theorem values and
   inductive constructors; theorem bodies are excluded) and compares them, together with the
   closure size, with `audit/statements.json`.

It prints `REVALIDATED` and exits with status 0 if and only if all four checks pass. A passing run
establishes these four properties of the shipped Lean sources; it does not re-check the prose of
this report against the Lean statements.

Manual alternative for the build and the axiom audit:

```text
cd lean && lake build                         # builds every module; fails on any error
lake env lean ../evidence/Audit.lean          # prints every theorem with its axioms
```

Compare the audit output with `evidence/axioms.txt` (every line must list a subset of `propext`,
`Classical.choice`, `Quot.sound`). To re-check the modeling bridges against a newer rustc, diff
`compiler/rustc_borrowck/src/path_utils.rs` (`is_active`) and the `(Read(kind), BorrowKind::Mut { .. })`
arm of `check_access_for_conflict` in `compiler/rustc_borrowck/src/lib.rs` against the text quoted
in Evidence (Prior art) from commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` (`path_utils.rs`
lines 88–93 and 102–119; `lib.rs` lines 1323–1328), and re-run `probe/issue.rs` with `rustc` and
with Miri (`-Zmiri-tree-borrows`).
