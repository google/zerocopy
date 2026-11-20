# Demand-driven red-green query memoization with early cutoff: when incremental fetches equal from-scratch evaluation (Lean 4 toy model)

## Summary

This package is a kernel-checked Lean 4 study of a generic toy model of demand-driven query memoization with red-green re-validation and early cutoff, the scheme used (with different mechanisms) by incremental compilers and build systems. Queries are deterministic programs with dynamic dependencies; a database from the previous input state records, per query, the ordered `(dependency, fingerprint)` trace and the result of one execution; an incremental fetch replays a cached query's recorded dependencies (`markGreen`) and either reuses the cached result (green) or re-executes the query (red). Nine result cards follow, one sentence each.

* **`incremental-fetch-agrees`** (T1): With ordered replay of recorded dependencies (early cutoff on or off), collision-free fingerprints, unchanged query code, and an old database whose every entry is the trace and result of a from-scratch execution in the old input state, every incremental fetch of the revision (from the start database or from any working database produced from it by earlier fetches) agrees with from-scratch evaluation in the new state: when it finishes its outcome (value or panic) is a from-scratch outcome, it finishes whenever from-scratch evaluation finishes at the same fuel, and the two outcomes are equal for all large fuel; all of this follows from a simulation invariant `Inv` that one ordered fetch preserves, and termination of the new state is needed only for the conclusion that the fetch eventually finishes.
* **`early-cutoff-agrees-with-reexecution`** (T1): Under the same hypotheses (ordered replay, collision-free fingerprints, unchanged code, consistent database), the first fetch of a revision returns the same outcome with early cutoff and without it, whenever both finish and for all large fuel; this is a reference corollary of `incremental-fetch-agrees`, and dropping any one of the four hypotheses separates the two modes.
* **`every-replay-order-is-value-sound`** (T1): For every replay order (recorded order stopping at the first change, reversed order, or checking all recorded dependencies) and either cutoff mode, with collision-free fingerprints, unchanged code, and a consistent database, every fetch of the revision that returns a value returns a value that from-scratch evaluation in the new state returns at some fuel, so out-of-order replay can fail only by panicking or by not finishing.
* **`ordered-replay-necessary`** (T1): In concrete instances satisfying every other hypothesis of `incremental-fetch-agrees`, reversed replay and check-all replay execute a recorded dependency that the new inputs made dead, so the incremental fetch panics, or is stuck at every fuel, where from-scratch evaluation returns `0` (ordered replay returns `0` on the same instance).
* **`fingerprint-collision-breaks-reuse`** (T0): Without collision-free fingerprints the incremental fetch can return a stale value, early cutoff can return a different value than re-execution, the fetch can be stuck at every fuel although the new state terminates, and early cutoff can execute a cached query all of whose recorded dependencies are unchanged.
* **`untracked-change-breaks-reuse`** (T0): If the query code differs between the revision that recorded the database and the current one (for example because it reads an untracked revision-wide parameter), the incremental fetch can return a value (`101`) that neither rule set produces from scratch, early cutoff can return a different value than re-execution, and the fetch can be stuck at every fuel although the new state terminates.
* **`inconsistent-database-breaks-reuse`** (T0): Without a consistent recorded database the fetch can reuse a wrong result or be stuck at every fuel although the new state terminates, and, even with a consistent recorded database, a working database not reachable by fetches can make the fetch return a stale result or be stuck at every fuel.
* **`cyclic-new-state-both-diverge`** (T0): When the new state has a live self-dependency, from-scratch evaluation and the ordered incremental fetch (either cutoff mode) are both stuck at every fuel, so agreement holds but the fetch never finishes: termination of the new state is a liveness hypothesis, not a soundness hypothesis, in this model.
* **`early-cutoff-skips-cached-query-with-unchanged-dependencies`** (T1): With early cutoff and any replay order, collision-free fingerprints, and a working database satisfying `Inv`, a query holding a cached entry all of whose recorded dependencies have, in the new state, values with the recorded fingerprints is never executed (not even an execution that panics or runs out of fuel) by any fetch from any working database reachable by fetches, and its slot stays the cached entry or that entry marked green; without early cutoff, or when one of its recorded dependencies changed (even if its own value is unchanged), it is executed.

The hypotheses above are each shown necessary by a kernel-checked counterexample (see each card's hypothesis ledger). What the results do **not** show is listed under **Boundaries**, non-claims first; in particular nothing here is proved about rustc, Salsa, Shake or any other real system, about the amount of work saved, about multiple revisions, or about concurrency.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

### What the theorems are about

All theorems are statements about the Lean definitions in `lean/Toy/RedGreen/*.lean` (quoted under **Findings**, *Core definitions*), and about nothing else. The model is a **generic toy model**, deliberately small:

* keys are queries `Q` or inputs `I` (`Key Q I := Q ⊕ I`); values `V` and fingerprints `F` are arbitrary types (`DecidableEq Q`, `DecidableEq F`);
* a query's code is a `Prog`, an inductive tree of `fetch k (fun v => …)` nodes ending in `ret v` or `panic`. Being inductive, the tree is well-founded: every path from the root is finite. It need not be finite, however: a `fetch` node has one subtree for each value of `V`, so when `V` is infinite (for example `Nat`) the tree can branch infinitely and its paths need not have a common length bound. The set and order of fetched keys can depend on fetched values (dynamic dependencies); code is deterministic by construction;
* from-scratch evaluation `eval` and the incremental `fetch` are fuel-indexed (fuel bounds the nesting depth of fetches); `stuck` means fuel exhausted, and `stuck` at every fuel means non-termination;
* one **revision** is modeled: an old input state `oldInp`, a new input state `newInp`, a database `odb : OldDB` left by the old state, the start working database `start odb`, and the working databases reachable from it by fetches (`Reachable`);
* traces are **per edge**: an `Entry` stores, for each dependency in fetch order, the fingerprint of the value fetched, and `markGreen` fetches each recorded dependency's current value and compares fingerprints (the verifying-trace scheme of Build Systems à la Carte);
* `Replay` selects the order in which `markGreen` checks recorded dependencies (`ordered`, `reversed`, `exhaustive` = recorded order without stopping at the first change, a sequential stand-in for checking all edges); `Config.cutoff` switches early cutoff on or off.

### Real systems the definitions are meant to capture, and the known gaps

The model is meant to capture the common core of demand-driven incremental query systems that re-validate a cached query by replaying its recorded dependencies, such as rustc's dependency graph (`try_mark_green` / `try_mark_previous_green` in `rustc_middle`), Salsa, and Shake. Known gaps, each of which is a reason the theorems do **not** transfer automatically:

* rustc propagates value-free per-node colours and stores one result fingerprint per node; Salsa and Shake compare revision stamps (Salsa additionally compares values when backdating). This model stores a fingerprint per recorded edge and compares the dependency's current value. The correspondence is argued below as `derived (modeling bridge)` only for databases in which every query recorded as a dependency also has its own entry.
* No multiple revisions, garbage collection, persistence, eviction or durability levels; no side outputs (diagnostics); no cycle detection or fixpoint cycle recovery; no concurrency, batching or cancellation; no per-query modifiers (such as rustc's `eval_always`); keys are compared by exact equality (no key fingerprints); panics abort and are not cached as values; fuel bounds call depth, not work.
* `rulesOld = rulesNew` stands for "the same code and configuration produced the database"; untracked reads, side effects and per-call non-determinism are not modeled.

### Subjects and their relationship

`REPORT.json` lists the Lean toolchain used for the kernel checks (`leanprover/lean4` `v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), four primary papers whose definitions and informal claims the cards restate or are compared with, and three upstream repository revisions (rustc-dev-guide, rust-lang/rust, salsa-rs/salsa) whose documentation and source are quoted for the modeling-bridge claims and prior art. The toolchain is the only subject that is executed; the papers and repositories are read, never mechanized. The package is self-contained: a Lake project with no dependencies, **no Mathlib**, using core Lean only (`import Lean` appears only in the build-time audit module and in the revalidation audit file).

### Exact observation versus broader applicability

Exact observation: the Lean kernel accepts every theorem below under `leanprover/lean4:v4.34.1`, using only the axioms recorded under **Evidence**. Everything said about real systems is a separate `derived (modeling bridge)` claim with its reasoning stated; such claims are arguments, not proofs, and were checked only against the quoted upstream revisions.

## Findings

Each card gives the tier, the plain-language claim, the Lean statements quoted verbatim, key definitions unfolded, the hypothesis ledger (each `tight` entry names a theorem in which all other hypotheses hold and the conclusion fails), the depth label, the non-vacuity witness, prior art, and the design question it informs. The machine-readable cards are `results.json`; `support/STATEMENTS.md` quotes the statement of every referenced declaration, including counterexamples and witnesses. Counterexamples cited only in a hypothesis ledger, and the `…_nonvacuous` non-vacuity witnesses, are quoted there and not inline in the cards.

### Core definitions

Quoted verbatim from `lean/Toy/RedGreen/Basic.lean` (namespace `Toy.RedGreen`). Every statement below depends on these definitions; the closure hashes under **Evidence** cover them.

```lean
/-! ## Programs, outcomes, from-scratch evaluation -/

/-- The code of one query, as a tree of fetches.  `fetch k c` asks for the value
of key `k` and continues with `c v`; `ret v` returns `v`; `panic` aborts.  The
continuation may inspect the fetched value, so the set and order of fetched
keys can depend on values (dynamic dependencies).  Models a deterministic
query function `run : Q → (fetch : Key → V) → V` written in monadic style. -/
inductive Prog (K V : Type) : Type where
  | ret : V → Prog K V
  | fetch : K → (V → Prog K V) → Prog K V
  | panic : Prog K V

/-- Outcome of an evaluation: a value, a panic (abort), or `stuck` (fuel
exhausted; for a fixed program, `stuck` at every fuel means non-termination,
i.e. a dependency cycle or unbounded dependency chain). -/
inductive Out (V : Type) : Type where
  | val : V → Out V
  | panic : Out V
  | stuck : Out V
  deriving DecidableEq, Repr

/-- Run a program against a fetch oracle.  A fetch whose answer is `panic` or
`stuck` aborts the program with that outcome. -/
def Prog.run {K V : Type} (f : K → Out V) : Prog K V → Out V
  | .ret v => .val v
  | .panic => .panic
  | .fetch k c =>
    match f k with
    | .val v => (c v).run f
    | .panic => .panic
    | .stuck => .stuck

/-- Run a program against a fetch oracle and record its trace: the ordered list
of `(key, fingerprint of the fetched value)` pairs of the successful fetches. -/
def Prog.runT {K V F : Type} (f : K → Out V) (fp : V → F) : Prog K V → Out V × List (K × F)
  | .ret v => (.val v, [])
  | .panic => (.panic, [])
  | .fetch k c =>
    match f k with
    | .val v =>
      match (c v).runT f fp with
      | (o, tr) => (o, (k, fp v) :: tr)
    | .panic => (.panic, [])
    | .stuck => (.stuck, [])

/-- Keys: queries or inputs. -/
abbrev Key (Q I : Type) := Q ⊕ I

/-- The code of every query. -/
abbrev Rules (Q I V : Type) := Q → Prog (Key Q I) V

/-- From-scratch evaluation with fuel: inputs are read from `inp`; a query runs
its code, fetching dependencies by recursive evaluation with one less fuel.
Fuel `0` gives `stuck` for every key. -/
def eval {Q I V : Type} (rules : Rules Q I V) (inp : I → V) : Nat → Key Q I → Out V
  | 0, _ => .stuck
  | _ + 1, .inr i => .val (inp i)
  | n + 1, .inl q => (rules q).run (eval rules inp n)

/-- The query `k` terminates from scratch in input state `inp`.  Because every
`Prog` is a well-founded tree, failure of this for a query means its dynamic
dependency structure in state `inp` has a cycle (or an unbounded chain).  This
is a property of the *dynamic* dependencies of one state: a cycle in the code
that is not reached in state `inp` does not prevent termination. -/
def Terminates {Q I V : Type} (rules : Rules Q I V) (inp : I → V) (k : Key Q I) : Prop :=
  ∃ n, eval rules inp n k ≠ .stuck

/-- Collision-freedom of the fingerprint function. -/
def FpInjective {V F : Type} (fp : V → F) : Prop :=
  ∀ a b, fp a = fp b → a = b

/-! ## Databases -/

/-- A recorded entry: the ordered `(dependency, fingerprint)` trace of one
execution of a query, and its result value (the result fingerprint is
`fp value`). -/
structure Entry (Q I V F : Type) where
  deps : List (Key Q I × F)
  value : V
  deriving DecidableEq, Repr

/-- The database left by a previous input state: an optional entry per query. -/
abbrev OldDB (Q I V F : Type) := Q → Option (Entry Q I V F)

/-- The per-query slot of the working database during the current revision.
`old e`: an entry from the previous state, not yet validated.  `done e r`: an
entry valid for the current state; `r = true` iff the query's code was run to
completion in this revision (whether or not its result equals the old one),
`r = false` iff it was marked green without running.  (So `r` is not a node
colour in the sense of rustc, where a re-executed query with an unchanged
result is green.)  `none`: no entry yet.  An execution that panics or runs out
of fuel leaves the slot unchanged; `Toy.RedGreen.execLog` records every
execution. -/
inductive Slot (Q I V F : Type) : Type where
  | none : Slot Q I V F
  | old : Entry Q I V F → Slot Q I V F
  | done : Entry Q I V F → Bool → Slot Q I V F
  deriving DecidableEq, Repr

/-- The working database. -/
abbrev DB (Q I V F : Type) := Q → Slot Q I V F

/-- The working database at the start of a revision. -/
def start {Q I V F : Type} (odb : OldDB Q I V F) : DB Q I V F :=
  fun q => match odb q with
    | some e => .old e
    | none => .none

/-- Point update of the working database. -/
def DB.set {Q I V F : Type} [DecidableEq Q] (db : DB Q I V F) (q : Q) (s : Slot Q I V F) :
    DB Q I V F :=
  fun q' => if q' = q then s else db q'

/-! ## The incremental algorithm -/

/-- Order in which `markGreen` replays a query's recorded dependencies.
`ordered`: recorded order, stopping at the first changed dependency (the
algorithm under study).  `reversed`: reverse recorded order, stopping at the
first changed dependency (an out-of-order variant).  `exhaustive`: recorded
order, but checking every recorded dependency even after one has changed (a
sequential stand-in for strategies that check all recorded edges without
stopping at the first change, e.g. in parallel; no concurrency is modeled). -/
inductive Replay : Type where
  | ordered
  | reversed
  | exhaustive
  deriving DecidableEq, Repr

/-- Algorithm configuration: replay order and whether early cutoff is on. -/
structure Config : Type where
  replay : Replay
  cutoff : Bool
  deriving DecidableEq, Repr

/-- Verdict of replaying a query's recorded dependencies. -/
inductive Verdict : Type where
  | green
  | red
  | panic
  | stuck
  deriving DecidableEq, Repr

/-- Was key `d` re-executed in the current revision?  (Inputs never are.) -/
def reexecutedIn {Q I V F : Type} (db : DB Q I V F) : Key Q I → Bool
  | .inl q => match db q with
    | .done _ true => true
    | _ => false
  | .inr _ => false

/-- Has dependency `d`, whose current value is `v`, changed relative to the
recorded fingerprint `f`?  With early cutoff only the fingerprint is compared.
Without early cutoff, a dependency that was re-executed in this revision also
counts as changed, even if it reproduced its old fingerprint. -/
def changedAt {Q I V F : Type} [DecidableEq F] (cutoff : Bool) (fp : V → F) (db : DB Q I V F)
    (d : Key Q I) (v : V) (f : F) : Bool :=
  !(decide (fp v = f)) || (!cutoff && reexecutedIn db d)

/-- Replay a list of recorded dependencies with the stateful fetcher `f`.
`stopAtRed = true`: answer `red` at the first changed dependency.
`stopAtRed = false`: keep checking the remaining dependencies and answer `red`
at the end.  A dependency whose fetch panics or runs out of fuel aborts the
replay with that outcome. -/
def checkDeps {Q I V F : Type} [DecidableEq F] (cutoff stopAtRed : Bool) (fp : V → F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) :
    DB Q I V F → List (Key Q I × F) → Bool → Verdict × DB Q I V F
  | db, [], anyRed => (if anyRed then .red else .green, db)
  | db, (d, fd) :: rest, anyRed =>
    match f db d with
    | (.val v, db₁) =>
      if changedAt cutoff fp db₁ d v fd then
        if stopAtRed then (.red, db₁) else checkDeps cutoff stopAtRed fp f db₁ rest true
      else checkDeps cutoff stopAtRed fp f db₁ rest anyRed
    | (.panic, db₁) => (.panic, db₁)
    | (.stuck, db₁) => (.stuck, db₁)

/-- `tryMarkGreen`: replay recorded dependencies according to the configured
order. -/
def markGreen {Q I V F : Type} [DecidableEq F] (cfg : Config) (fp : V → F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) (db : DB Q I V F)
    (deps : List (Key Q I × F)) : Verdict × DB Q I V F :=
  match cfg.replay with
  | .ordered => checkDeps cfg.cutoff true fp f db deps false
  | .reversed => checkDeps cfg.cutoff true fp f db deps.reverse false
  | .exhaustive => checkDeps cfg.cutoff false fp f db deps false

/-- Run a program with a stateful fetcher, threading the state and recording
the trace of successful fetches. -/
def Prog.runSt {K V F S : Type} (fp : V → F) (f : S → K → Out V × S) :
    Prog K V → S → Out V × List (K × F) × S
  | .ret v, s => (.val v, [], s)
  | .panic, s => (.panic, [], s)
  | .fetch k c, s =>
    match f s k with
    | (.val v, s₁) =>
      match (c v).runSt fp f s₁ with
      | (o, tr, s₂) => (o, (k, fp v) :: tr, s₂)
    | (.panic, s₁) => (.panic, [], s₁)
    | (.stuck, s₁) => (.stuck, [], s₁)

/-- Re-execute query `q` with the stateful fetcher `f`; on success store the
new trace and result as a `done … true` slot. -/
def exec {Q I V F : Type} [DecidableEq Q] (rules : Rules Q I V) (fp : V → F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) (db : DB Q I V F) (q : Q) :
    Out V × DB Q I V F :=
  match (rules q).runSt fp f db with
  | (.val v, tr, db₁) => (.val v, db₁.set q (.done ⟨tr, v⟩ true))
  | (.panic, _, db₁) => (.panic, db₁)
  | (.stuck, _, db₁) => (.stuck, db₁)

/-- The incremental, demand-driven fetch in input state `inp`, with fuel.
Inputs are read directly.  A `done` query returns its stored value.  An `old`
query is replayed by `markGreen`: `green` reuses the stored result and marks
the slot `done … false`; `red` re-executes the query.  A query with no entry is
executed.  Every nested fetch uses one less fuel. -/
def fetch {Q I V F : Type} [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V)
    (fp : V → F) (inp : I → V) : Nat → DB Q I V F → Key Q I → Out V × DB Q I V F
  | 0, db, _ => (.stuck, db)
  | _ + 1, db, .inr i => (.val (inp i), db)
  | n + 1, db, .inl q =>
    match db q with
    | .done e _ => (.val e.value, db)
    | .old e =>
      match markGreen cfg fp (fetch cfg rules fp inp n) db e.deps with
      | (.green, db₁) => (.val e.value, db₁.set q (.done e false))
      | (.red, db₁) => exec rules fp (fetch cfg rules fp inp n) db₁ q
      | (.panic, db₁) => (.panic, db₁)
      | (.stuck, db₁) => (.stuck, db₁)
    | .none => exec rules fp (fetch cfg rules fp inp n) db q

/-! ## Consistency and the simulation invariant -/

/-- Entry `e` is what query `q` records when executed from scratch in input
state `inp`: running `q`'s code against from-scratch values (at some fuel)
succeeds with result `e.value` and trace `e.deps`. -/
def EntryConsistent {Q I V F : Type} (rules : Rules Q I V) (fp : V → F) (inp : I → V) (q : Q)
    (e : Entry Q I V F) : Prop :=
  ∃ n, (rules q).runT (eval rules inp n) fp = (.val e.value, e.deps)

/-- A database consistent with input state `inp`: every recorded entry is
consistent with `inp`.  Queries without entries are unconstrained. -/
def DBConsistent {Q I V F : Type} (rules : Rules Q I V) (fp : V → F) (inp : I → V)
    (odb : OldDB Q I V F) : Prop :=
  ∀ q e, odb q = some e → EntryConsistent rules fp inp q e

/-- The simulation invariant of a working database during a revision from
`oldInp` to `newInp`: `old` slots are consistent with the old state, `done`
slots with the new state. -/
def Inv {Q I V F : Type} (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V)
    (db : DB Q I V F) : Prop :=
  ∀ q, match db q with
    | .none => True
    | .old e => EntryConsistent rules fp oldInp q e
    | .done e _ => EntryConsistent rules fp newInp q e

/-- The working databases reachable from `db₀` by a sequence of incremental
fetches (of any keys, with any fuel) in input state `inp`: the databases seen
during one revision. -/
inductive Reachable {Q I V F : Type} [DecidableEq Q] [DecidableEq F] (cfg : Config)
    (rules : Rules Q I V) (fp : V → F) (inp : I → V) (db₀ : DB Q I V F) : DB Q I V F → Prop where
  | refl : Reachable cfg rules fp inp db₀ db₀
  | step {db : DB Q I V F} (n : Nat) (k : Key Q I) :
      Reachable cfg rules fp inp db₀ db → Reachable cfg rules fp inp db₀ (fetch cfg rules fp inp n db k).2

/-- The incremental fetch of `k` from `db` agrees with from-scratch evaluation
in state `inp`:

* (partial correctness) whenever the fetch finishes (outcome not `stuck`), its
  outcome — value or panic — is the from-scratch outcome at some fuel;
* (adequacy at equal fuel) whenever from-scratch evaluation finishes with fuel
  `n`, the incremental fetch with fuel `n` also finishes. -/
def AgreesWithEval {Q I V F : Type} [DecidableEq Q] [DecidableEq F] (cfg : Config)
    (rules : Rules Q I V) (fp : V → F) (inp : I → V) (db : DB Q I V F) (k : Key Q I) : Prop :=
  (∀ m, (fetch cfg rules fp inp m db k).1 ≠ .stuck →
      ∃ n, eval rules inp n k = (fetch cfg rules fp inp m db k).1) ∧
  (∀ n, eval rules inp n k ≠ .stuck → (fetch cfg rules fp inp n db k).1 ≠ .stuck)
```

The execution log, from `lean/Toy/RedGreen/ExecLog.lean`. The instrumented state `LDB` pairs a working database with the log of executed queries; `checkDepsX`, `markGreenX`, `execX` and `fetchX` are `checkDeps`, `markGreen`, `exec` and `fetch` on that state, with the same control flow:

```lean
/-- State of the instrumented algorithm: the working database and the log of
executed queries, oldest first. -/
abbrev LDB (Q I V F : Type) := DB Q I V F × List Q

/-- `checkDeps` on the instrumented state (same control flow; the log is
threaded through the fetcher). -/
def checkDepsX {Q I V F : Type} [DecidableEq F] (cutoff stopAtRed : Bool) (fp : V → F)
    (f : LDB Q I V F → Key Q I → Out V × LDB Q I V F) :
    LDB Q I V F → List (Key Q I × F) → Bool → Verdict × LDB Q I V F
  | s, [], anyRed => (if anyRed then .red else .green, s)
  | s, (d, fd) :: rest, anyRed =>
    match f s d with
    | (.val v, s₁) =>
      if changedAt cutoff fp s₁.1 d v fd then
        if stopAtRed then (.red, s₁) else checkDepsX cutoff stopAtRed fp f s₁ rest true
      else checkDepsX cutoff stopAtRed fp f s₁ rest anyRed
    | (.panic, s₁) => (.panic, s₁)
    | (.stuck, s₁) => (.stuck, s₁)

/-- `markGreen` on the instrumented state. -/
def markGreenX {Q I V F : Type} [DecidableEq F] (cfg : Config) (fp : V → F)
    (f : LDB Q I V F → Key Q I → Out V × LDB Q I V F) (s : LDB Q I V F)
    (deps : List (Key Q I × F)) : Verdict × LDB Q I V F :=
  match cfg.replay with
  | .ordered => checkDepsX cfg.cutoff true fp f s deps false
  | .reversed => checkDepsX cfg.cutoff true fp f s deps.reverse false
  | .exhaustive => checkDepsX cfg.cutoff false fp f s deps false

/-- `exec` on the instrumented state: appends `q` to the log before running
`q`'s code. -/
def execX {Q I V F : Type} [DecidableEq Q] (rules : Rules Q I V) (fp : V → F)
    (f : LDB Q I V F → Key Q I → Out V × LDB Q I V F) (s : LDB Q I V F) (q : Q) :
    Out V × LDB Q I V F :=
  match (rules q).runSt fp f (s.1, s.2 ++ [q]) with
  | (.val v, tr, s₁) => (.val v, (s₁.1.set q (.done ⟨tr, v⟩ true), s₁.2))
  | (.panic, _, s₁) => (.panic, s₁)
  | (.stuck, _, s₁) => (.stuck, s₁)

/-- `fetch` on the instrumented state (same control flow as `fetch`). -/
def fetchX {Q I V F : Type} [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V)
    (fp : V → F) (inp : I → V) : Nat → LDB Q I V F → Key Q I → Out V × LDB Q I V F
  | 0, s, _ => (.stuck, s)
  | _ + 1, s, .inr i => (.val (inp i), s)
  | n + 1, s, .inl q =>
    match s.1 q with
    | .done e _ => (.val e.value, s)
    | .old e =>
      match markGreenX cfg fp (fetchX cfg rules fp inp n) s e.deps with
      | (.green, s₁) => (.val e.value, (s₁.1.set q (.done e false), s₁.2))
      | (.red, s₁) => execX rules fp (fetchX cfg rules fp inp n) s₁ q
      | (.panic, s₁) => (.panic, s₁)
      | (.stuck, s₁) => (.stuck, s₁)
    | .none => execX rules fp (fetchX cfg rules fp inp n) s q

/-- The queries executed (code started, in order) by
`fetch cfg rules fp inp n db k`. -/
def execLog {Q I V F : Type} [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V)
    (fp : V → F) (inp : I → V) (n : Nat) (db : DB Q I V F) (k : Key Q I) : List Q :=
  (fetchX cfg rules fp inp n (db, []) k).2.2

/-- **Adequacy of the instrumentation.**  The instrumented fetch has exactly
the outcome and working database of `fetch`, and appends `execLog` to the
incoming log. -/
theorem fetchX_eq [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V)
    (fp : V → F) (inp : I → V) (n : Nat) (db : DB Q I V F) (l : List Q) (k : Key Q I) :
    fetchX cfg rules fp inp n (db, l) k =
      ((fetch cfg rules fp inp n db k).1,
        ((fetch cfg rules fp inp n db k).2, l ++ execLog cfg rules fp inp n db k))
```

### Example instances used by several cards

From `lean/Toy/RedGreen/Examples.lean` (proofs of the `odb…` facts are by `decide`). Inputs are `x` and `y` (`inpXY a b` is the state `x = a, y = b`), values and fingerprints are `Nat`, and `fpId` is the identity.

```lean
/-! ## Key types, fingerprints, input states -/

/-- Query keys of examples D and C. -/
inductive QK : Type where
  | top
  | guard
  | risky
  deriving DecidableEq, Repr

/-- Query keys of the remaining examples. -/
inductive Q3 : Type where
  | top
  | a
  | b
  deriving DecidableEq, Repr

/-- Input keys. -/
inductive IK : Type where
  | x
  | y
  deriving DecidableEq, Repr

/-- Identity fingerprints on `Nat` (collision-free). -/
def fpId : Nat → Nat := fun v => v

/-- Parity fingerprints (collide on all values of equal parity). -/
def fpParity : Nat → Nat := fun v => v % 2

/-- Saturating fingerprints: `min v 10` (collide on all values `≥ 10`). -/
def fpSat : Nat → Nat := fun v => min v 10

/-- The input state `x = a, y = b`. -/
def inpXY (a b : Nat) : IK → Nat
  | .x => a
  | .y => b

/-- Generic constructor of a consistent database: execute every query from
scratch in state `inp` (fuel `n`) and record its trace and result; queries that
panic or run out of fuel get no entry. -/
def recordAll {Q I V F : Type} (rules : Rules Q I V) (fp : V → F) (inp : I → V) (n : Nat) :
    OldDB Q I V F :=
  fun q => match (rules q).runT (eval rules inp n) fp with
    | (.val v, tr) => some ⟨tr, v⟩
    | (.panic, _) => none
    | (.stuck, _) => none

/-- `guard` tests whether `x ≠ 0`; `risky` divides by `x` and panics when
`x = 0`; `top` fetches `guard`, and only if it is `1` fetches `risky`.  In a
state with `x = 0`, `risky` is a dead dependency of `top`. -/
def rulesD : Rules QK IK Nat
  | .guard => .fetch (.inr .x) fun v => .ret (if v = 0 then 0 else 1)
  | .risky => .fetch (.inr .x) fun v => if v = 0 then .panic else .ret (100 / v)
  | .top => .fetch (.inl .guard) fun g =>
      if g = 0 then .ret 0 else .fetch (.inl .risky) fun r => .ret r

/-- Like `rulesD`, but when `x = 0` the query `risky` fetches `top` instead of
panicking.  The code contains the cycle `top → risky → top`, yet in every state
at most one direction is live: `top` fetches `risky` only when `x ≠ 0`, and
`risky` fetches `top` only when `x = 0`.  Both states below terminate. -/
def rulesC : Rules QK IK Nat
  | .guard => .fetch (.inr .x) fun v => .ret (if v = 0 then 0 else 1)
  | .risky => .fetch (.inr .x) fun v => if v = 0 then .fetch (.inl .top) .ret else .ret (100 / v)
  | .top => .fetch (.inl .guard) fun g =>
      if g = 0 then .ret 0 else .fetch (.inl .risky) fun r => .ret r

/-- Old state of examples D and C (`x = 5`). -/
def oldD : IK → Nat := inpXY 5 0
/-- New state of examples D and C (`x = 0`). -/
def newD : IK → Nat := inpXY 0 0

/-- Database recorded from scratch in the old state of example D. -/
def odbD : OldDB QK IK Nat Nat := recordAll rulesD fpId oldD 10
/-- Database recorded from scratch in the old state of example C. -/
def odbC : OldDB QK IK Nat Nat := recordAll rulesC fpId oldD 10

/-- `a` reads `x` but always returns `0`; `top` returns `a + y`.  When only `x`
changes, `a` must be re-executed but reproduces its old value, so `top`'s
recorded dependencies are all unchanged. -/
def rulesK : Rules Q3 IK Nat
  | .a => .fetch (.inr .x) fun _ => .ret 0
  | .b => .ret 7
  | .top => .fetch (.inl .a) fun m => .fetch (.inr .y) fun w => .ret (m + w)

def oldK : IK → Nat := inpXY 1 2
def newK : IK → Nat := inpXY 3 2
def odbK : OldDB Q3 IK Nat Nat := recordAll rulesK fpId oldK 10

theorem odbK_top : odbK .top = some ⟨[(.inl .a, 0), (.inr .y, 2)], 2⟩
theorem odbK_a : odbK .a = some ⟨[(.inr .x, 1)], 0⟩
```

The recorded entries of example K as they appear in the start database, used by card 9, from `lean/Toy/RedGreen/Minimal.lean` (proofs by `decide`):

```lean
/-- The recorded entry of `top` in example K. -/
def eK : Entry Q3 IK Nat Nat := ⟨[(.inl .a, 0), (.inr .y, 2)], 2⟩

/-- The recorded entry of `a` in example K. -/
def eKa : Entry Q3 IK Nat Nat := ⟨[(.inr .x, 1)], 0⟩

theorem start_odbK_top : start odbK .top = .old eK
theorem start_odbK_a : start odbK .a = .old eKa
```

The remaining concrete instances (the rule sets, input states, fingerprint functions, entries and databases of the other examples, used by counterexamples, ledger entries and non-vacuity witnesses, such as `rulesH`, `rulesR`, `fpCollide13`, `eF` or `staleDbD`) are not quoted in this report. Most are defined in `lean/Toy/RedGreen/Examples.lean`, the rest next to the theorems that use them (for example `staleDbD` in `lean/Toy/RedGreen/Necessity.lean` and `eF` in `lean/Toy/RedGreen/Minimal.lean`); each rule set has a docstring describing it. Each counterexample statement names these instances and states, as explicit conjuncts, the general hypotheses that hold for them and concrete facts showing that the general conclusion fails.

### 1. `incremental-fetch-agrees` (theorem, tier T1)

**Plain claim.** With ordered replay of recorded dependencies (early cutoff on or off), collision-free fingerprints, unchanged query code (the code that produced the database is the code that runs now), and a database whose every entry is the trace and result of a from-scratch execution in the old input state, every incremental fetch made during the revision (from the start database, or from any working database produced from it by earlier fetches of this algorithm) agrees with from-scratch evaluation in the new input state: whenever it finishes, its outcome (value or panic) is a from-scratch outcome, and it finishes with any fuel at which from-scratch evaluation finishes. Consequently, for each such fetch the two fuel-indexed outcomes are equal for all large fuel, and the fetch finishes for all large fuel when the key terminates from scratch in the new state. All of this follows from a simulation invariant: one ordered-replay fetch from any working database satisfying Inv (old slots consistent with the old state, done slots consistent with the new state) returns a database satisfying Inv and agrees with from-scratch evaluation in the same sense. Termination of the new state is not a hypothesis of agreement: if the key does not terminate from scratch, both sides are stuck at every fuel.

**Tier T1.** Soundness of trace-based re-validation with dynamic dependencies is folklore for build systems and incremental compilers (rustc-dev-guide, Build Systems à la Carte) and has pen-and-paper proofs for related models (the OOPSLA 2015 build system, Adapton's declarative semantics); the mechanized formalizations found (Twelf for self-adjusting computation, Agda for forward build systems, a Coq port of the Build Systems à la Carte abstractions without completed proofs, a mechanized build-language verification) do not cover demand-driven verifying-trace replay with early cutoff. Made precise here in a toy model.

**Lean statement(s).** Quoted verbatim from the sources, docstring included, up to the proof.

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_agrees_with_eval_of_ordered_replay`:

```lean
/-- **Agreement of ordered red-green replay (first demand).**  With ordered
replay (early cutoff on or off), collision-free fingerprints, the same query
code as the one that produced the database, and a database consistent with
the old input state, the incremental fetch of any key at the start of a
revision agrees with from-scratch evaluation in the new state (partial
correctness, and adequacy at equal fuel). -/
theorem fetch_agrees_with_eval_of_ordered_replay (cfg : Config) (hord : cfg.replay = .ordered)
    (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (k : Key Q I) :
    AgreesWithEval cfg rulesNew fp newInp (start odb) k
```

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_agrees_with_eval_during_revision_of_ordered_replay`:

```lean
/-- **Agreement during a whole revision.**  Under the same hypotheses, every
fetch made from a working database reachable from the start of the revision
by earlier fetches (of any keys, with any fuel) agrees with from-scratch
evaluation in the new state. -/
theorem fetch_agrees_with_eval_during_revision_of_ordered_replay (cfg : Config)
    (hord : cfg.replay = .ordered) (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (k : Key Q I) :
    AgreesWithEval cfg rulesNew fp newInp db k
```

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_eventually_eq_eval_during_revision_of_ordered_replay`:

```lean
/-- **Eventual equality during a whole revision.**  Under the same hypotheses,
for every working database reachable from the start of the revision (in
particular the start database itself, `Reachable.refl`), for all sufficiently
large fuel the incremental fetch and from-scratch evaluation have the same
outcome — including the case where both are `stuck` at every fuel. -/
theorem fetch_eventually_eq_eval_during_revision_of_ordered_replay (cfg : Config)
    (hord : cfg.replay = .ordered) (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (k : Key Q I) :
    ∃ N, ∀ m, N ≤ m → (fetch cfg rulesNew fp newInp m db k).1 = eval rulesNew newInp m k
```

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_eventually_finishes_during_revision_of_terminates`:

```lean
/-- **Termination transfer during a whole revision.**  Under the same
hypotheses, if `k` terminates from scratch in the new state, then for every
working database reachable from the start of the revision the incremental
fetch of `k` finishes for all sufficiently large fuel. -/
theorem fetch_eventually_finishes_during_revision_of_terminates (cfg : Config)
    (hord : cfg.replay = .ordered) (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (k : Key Q I)
    (hterm : Terminates rulesNew newInp k) :
    ∃ N, ∀ m, N ≤ m → (fetch cfg rulesNew fp newInp m db k).1 ≠ .stuck
```

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.fetch_simulation_invariant`:

```lean
/-- **Main simulation invariant.**  For ordered replay (with or without early
cutoff) and collision-free fingerprints, one incremental fetch from a working
database satisfying `Inv` (old slots consistent with the old state, done
slots with the new state)

* returns a database that again satisfies `Inv`;
* if it finishes, returns the from-scratch outcome (value or panic) of the new
  state;
* finishes whenever from-scratch evaluation finishes with the same fuel. -/
theorem fetch_simulation_invariant (cfg : Config) (hord : cfg.replay = .ordered)
    (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) :
    ∀ (n : Nat) (db : DB Q I V F) (k : Key Q I), Inv rules fp oldInp newInp db →
      Inv rules fp oldInp newInp (fetch cfg rules fp newInp n db k).2 ∧
      ((fetch cfg rules fp newInp n db k).1 ≠ .stuck →
          ∃ m, eval rules newInp m k = (fetch cfg rules fp newInp n db k).1) ∧
      (eval rules newInp n k ≠ .stuck → (fetch cfg rules fp newInp n db k).1 ≠ .stuck)
```

Key definitions unfolded (all quoted under *Core definitions*):

* `AgreesWithEval cfg rules fp inp db k` is `(∀ m, (fetch cfg rules fp inp m db k).1 ≠ .stuck → ∃ n, eval rules inp n k = (fetch cfg rules fp inp m db k).1) ∧ (∀ n, eval rules inp n k ≠ .stuck → (fetch cfg rules fp inp n db k).1 ≠ .stuck)`: partial correctness (a finished fetch has a from-scratch outcome, value or panic, at some fuel) and adequacy at equal fuel.
* `FpInjective fp` is `∀ a b, fp a = fp b → a = b`.
* `DBConsistent rules fp inp odb` is `∀ q e, odb q = some e → ∃ n, (rules q).runT (eval rules inp n) fp = (.val e.value, e.deps)`: every recorded entry is the trace and result of a from-scratch execution in state `inp`; queries without entries are unconstrained.
* `Inv rules fp oldInp newInp db` is `∀ q, match db q with | .none => True | .old e => EntryConsistent rules fp oldInp q e | .done e _ => EntryConsistent rules fp newInp q e`.
* `Reachable cfg rules fp inp db₀ db` is the least relation containing `db₀` and closed under `db ↦ (fetch cfg rules fp inp n db k).2` for every fuel `n` and key `k`; it includes databases left by fetches that panicked or ran out of fuel.
* `Terminates rules inp k` is `∃ n, eval rules inp n k ≠ .stuck`.

The type variables are implicit section variables `{Q I V F : Type} [DecidableEq Q] [DecidableEq F]`.

Hypothesis ledger:

| Hypothesis | Tightness | Counterexample(s) | Why it is needed |
| :--- | :--- | :--- | :--- |
| `hord : cfg.replay = .ordered (all five theorems)` | tight | `Toy.RedGreen.reversed_replay_executes_dead_dependency_and_panics`, `Toy.RedGreen.exhaustive_replay_executes_dead_dependency_and_panics`, `Toy.RedGreen.reversed_replay_diverges_on_dead_code_cycle`, `Toy.RedGreen.exhaustive_replay_diverges_on_dead_code_cycle` | Replaying recorded dependencies in recorded order and stopping at the first changed one guarantees that every replayed dependency is a genuine dependency of the query in the new state; other orders can execute dependencies that the new inputs have made dead. The panic counterexamples refute agreement and the invariant; the divergence counterexamples refute every theorem of the card, including eventual equality and termination transfer. |
| `hsame : rulesOld = rulesNew (unchanged query code across revisions; the four theorems with a database)` | tight | `Toy.RedGreen.ambient_dependent_code_matches_no_from_scratch_eval`, `Toy.RedGreen.untracked_code_change_diverges_although_new_state_terminates` | The database must have been produced by the code that runs now. Intra-revision determinism is structural (a Prog is a deterministic function of fetched values); this hypothesis excludes untracked changes between revisions, such as a changed revision-wide parameter. The wrong-value counterexample refutes agreement; the divergence counterexample refutes agreement, eventual equality and termination transfer. |
| `hfp : FpInjective fp (all five theorems)` | tight | `Toy.RedGreen.fp_collision_reuses_stale_result`, `Toy.RedGreen.fp_collision_diverges_although_new_state_terminates` | Equal fingerprints must imply equal values; otherwise a changed dependency is taken as unchanged and a stale result is reused, or a stale trace is followed into a cycle. The wrong-value counterexample refutes agreement and the invariant (its start database satisfies Inv by inv_start); the divergence counterexample refutes every theorem of the card. |
| `hcons : DBConsistent rulesOld fp oldInp odb (the four theorems with a database)` | tight | `Toy.RedGreen.inconsistent_db_reuses_wrong_result`, `Toy.RedGreen.inconsistent_db_diverges_although_new_state_terminates` | Reused results are only as good as the recorded entries; an entry that is not the trace and result of a from-scratch execution in the old state can be reused verbatim, or can send replay into a cycle. The wrong-value counterexample refutes agreement; the divergence counterexample refutes agreement, eventual equality and termination transfer. |
| `hreach : Reachable cfg rulesNew fp newInp (start odb) db (revision theorems only)` | tight | `Toy.RedGreen.stale_done_slot_returns_wrong_result`, `Toy.RedGreen.unreachable_db_diverges_although_new_state_terminates` | Restricts the revision theorems to working databases produced by fetches of this algorithm from the start database. Both counterexamples prove non-reachability: a done slot holding an old-state entry violates Inv, which every reachable database satisfies (inv_of_reachable, fully proved); an old slot absent from the start database cannot be created by fetches (reachable_noNewOld). The first returns a stale value; the second is stuck at every fuel although the key terminates, refuting all three revision theorems. |
| `hinv : Inv rules fp oldInp newInp db (fetch_simulation_invariant only)` | tight | `Toy.RedGreen.stale_done_slot_returns_wrong_result` | The invariant's own hypothesis: old slots consistent with the old state, done slots with the new state. A working database whose done slot holds an old-state entry makes the fetch return a value that from-scratch evaluation never returns (at fuel 6 the invariant's second conjunct fails). |
| `hterm : Terminates rulesNew newInp k (termination transfer only)` | tight | `Toy.RedGreen.cyclic_new_state_both_diverge` | Needed only for the conclusion that the incremental fetch eventually finishes; agreement and eventual equality hold without it. |

**Depth: substantive.** The invariant needs a path-agreement argument: ordered replay only visits dependencies that the query's code reaches in the new state, because each earlier dependency reproduced its fingerprint, hence (by injectivity) its value, hence the code took the same branch; panics must be matched and adequacy at equal fuel needs the same argument with fuel accounting. Inv preservation and value soundness alone are fully proved for every replay order (every-replay-order-is-value-sound); given the invariant, the other theorems of the card are shallow.

**Non-vacuity witness.** Example C (three queries, one input x changing from 5 to 0; identity fingerprints; database recorded from scratch at x = 5), for either cutoff mode: it exercises a changed recorded dependency (guard), a recorded dependency that becomes dead (risky), and a code-level cycle top -> risky -> top that is live in neither state; ordered replay returns the from-scratch value 0; after fetching top the working database is reachable, satisfies Inv with a done slot for top, and a fetch of risky from it (which terminates from scratch) agrees. Lean: `Toy.RedGreen.fetch_agrees_with_eval_nonvacuous`, `Toy.RedGreen.fetch_during_revision_nonvacuous`, `Toy.RedGreen.fetch_simulation_invariant_nonvacuous`.

**Prior art.** [S1] rustc-dev-guide, incremental-compilation chapters, [S2] rust-lang/rust, `try_mark_previous_green`, [S3] Salsa book, `maybe_changed_after` and backdating, [S4] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte", ICFP 2018, [S5] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte: Theory and practice", JFP 2020, [S6] Erdweg, Lichter, Weiel, OOPSLA 2015, [S7] Hammer, Khoo, Hicks, Foster, "Adapton", PLDI 2014, [S8] Abadi, Lampson, Lévy, ICFP 1996, [S9] Heydon, Levin, Yu, PLDI 2000, [S10] Mitchell, "Shake before building", ICFP 2012, [S11] Konat, Erdweg, Visser, ASE 2018, [S12] Acar, Ph.D. thesis, 2005, [S13] Acar, Blelloch, Harper, POPL 2002, [S14] Acar, Blume, Donham, JFP 2013, [S15] Spall, Mitchell, Tobin-Hochstadt, CPP 2022, [S16] Lukyanov, Mokhov, CoqPL 2019, [S17] Christakis, Leino, Schulte, FM 2014. Full records and the content relied on are under **Evidence**, *Primary sources*.

**Design question.** Incremental compilers and build systems memoize demand-driven queries and, after an input change, re-validate a query by replaying its recorded dependency trace (red-green marking with early cutoff). Under which conditions does an incremental fetch equal from-scratch evaluation, and which shortcuts break it? This card gives sufficient conditions (ordered replay, collision-free fingerprints, unchanged code, a consistent database, reachable working databases) and shows that termination of the new state is not one of them.

**Non-claims.** See **Boundaries**, card `incremental-fetch-agrees`.

Basis: execution (Lean kernel check) — every theorem named in this card is accepted by the Lean kernel; axioms per theorem are listed under **Evidence**.

Basis: derived (modeling bridge) — the correspondence of `markGreen` with `Replay.ordered` to rustc's `try_mark_previous_green` and to verifying traces with early cutoff in Salsa and Shake is argued under *Modeling bridge to real systems* below, only for databases in which every recorded dependency query has its own entry; it is not proved.

### 2. `early-cutoff-agrees-with-reexecution` (theorem, tier T1)

**Plain claim.** Reference corollary of incremental-fetch-agrees. With ordered replay, collision-free fingerprints, unchanged query code and a database consistent with the old input state, the first incremental fetch of a revision (from the start database) returns the same outcome with early cutoff (a re-executed dependency that reproduces its recorded fingerprint counts as unchanged) and without it (a re-executed dependency always counts as changed): whenever both finish, at any fuels, their outcomes are equal, and for all large fuel their outcomes are equal (no termination hypothesis). The theorem compares the two modes with each other; that each agrees with from-scratch evaluation is incremental-fetch-agrees. Its distinct content is the sharpness of its hypotheses: dropping any one of them separates the two modes.

**Tier T1.** Early cutoff (backdating) is standard in Build Systems à la Carte, Shake, Salsa and rustc and is informally known to be sound; made precise here as agreement of the two cutoff modes of the same toy algorithm. A reference corollary of incremental-fetch-agrees.

**Lean statement(s).** Quoted verbatim from the sources, docstring included, up to the proof.

`Toy/RedGreen/Soundness.lean` — `Toy.RedGreen.early_cutoff_agrees_with_reexecution_of_ordered_replay`:

```lean
/-- **Early cutoff agrees with full re-execution (reference corollary of
`incremental-fetch-agrees`).**  With ordered replay, collision-free
fingerprints, the same query code as the one that produced the database, and
a database consistent with the old input state, the first incremental fetch of
a revision with early cutoff (a re-executed dependency that reproduces its
recorded fingerprint counts as unchanged) and without it (every dependent of a
re-executed query is re-executed) return the same outcome: whenever both
finish, at any fuels, their outcomes are equal; and for all sufficiently large
fuel their outcomes are equal.  Only outcomes are compared; the working
databases the two modes leave behind differ. -/
theorem early_cutoff_agrees_with_reexecution_of_ordered_replay (r : Replay) (hord : r = .ordered)
    (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (k : Key Q I) :
    (∀ m₁ m₂,
      (fetch ⟨r, true⟩ rulesNew fp newInp m₁ (start odb) k).1 ≠ .stuck →
      (fetch ⟨r, false⟩ rulesNew fp newInp m₂ (start odb) k).1 ≠ .stuck →
      (fetch ⟨r, true⟩ rulesNew fp newInp m₁ (start odb) k).1 =
        (fetch ⟨r, false⟩ rulesNew fp newInp m₂ (start odb) k).1) ∧
    (∃ N, ∀ m, N ≤ m →
      (fetch ⟨r, true⟩ rulesNew fp newInp m (start odb) k).1 =
        (fetch ⟨r, false⟩ rulesNew fp newInp m (start odb) k).1)
```

The configuration `⟨r, true⟩` has early cutoff on, `⟨r, false⟩` off; with cutoff off, `changedAt` also counts a dependency as changed when it was re-executed in this revision (`reexecutedIn`), even if it reproduced its recorded fingerprint. The conclusion compares only the first components (outcomes) of the two fetches from the start database `start odb`. `FpInjective` and `DBConsistent` unfold as in `incremental-fetch-agrees`.

Hypothesis ledger:

| Hypothesis | Tightness | Counterexample(s) | Why it is needed |
| :--- | :--- | :--- | :--- |
| `hord : r = .ordered` | tight | `Toy.RedGreen.reversed_replay_breaks_early_cutoff_agreement` | With reversed replay, early cutoff can continue past a re-executed dependency that reproduced its fingerprint and reach a dead dependency that panics, while without early cutoff the same dependency stops the replay and the query is re-executed. |
| `hsame : rulesOld = rulesNew (unchanged query code across revisions)` | tight | `Toy.RedGreen.ambient_dependent_code_breaks_early_cutoff` | If the code changed between revisions, marking a dependent green reuses a result of the old code while re-executing it uses the new code. |
| `hfp : FpInjective fp` | tight | `Toy.RedGreen.fp_collision_breaks_early_cutoff` | Early cutoff decides 'unchanged' by fingerprint equality of a re-executed query's result; a collision there reuses a stale dependent even when the inputs' fingerprints do not collide. |
| `hcons : DBConsistent rulesOld fp oldInp odb` | tight | `Toy.RedGreen.inconsistent_db_breaks_early_cutoff` | Early cutoff reuses the recorded result of the dependent; a wrong recorded result is returned in cutoff mode but recomputed without cutoff. |

**Depth: shallow.** Corollary of the simulation invariant applied to both cutoff modes, plus fuel monotonicity of from-scratch evaluation and a classical case split on termination.

**Non-vacuity witness.** Example K: query a reads x (1 -> 3) and always returns 0; top returns a + y. With early cutoff top is marked green; without it top is re-executed; both return 2. Lean: `Toy.RedGreen.early_cutoff_agrees_nonvacuous`.

**Prior art.** [S4] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte", ICFP 2018, [S5] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte: Theory and practice", JFP 2020, [S10] Mitchell, "Shake before building", ICFP 2012, [S3] Salsa book, `maybe_changed_after` and backdating, [S1] rustc-dev-guide, incremental-compilation chapters, [S2] rust-lang/rust, `try_mark_previous_green`. Full records and the content relied on are under **Evidence**, *Primary sources*.

**Design question.** Incremental compilers and build systems memoize demand-driven queries and, after an input change, re-validate a query by replaying its recorded dependency trace (red-green marking with early cutoff). Under which conditions does an incremental fetch equal from-scratch evaluation, and which shortcuts break it? Reference point: it states that, under the hypotheses of incremental-fetch-agrees, switching early cutoff on or off does not change the first fetch's outcome, and its counterexamples show which hypotheses make the early-cutoff shortcut unsafe.

**Non-claims.** See **Boundaries**, card `early-cutoff-agrees-with-reexecution`.

Basis: execution (Lean kernel check) — every theorem named in this card is accepted by the Lean kernel; axioms per theorem are listed under **Evidence**.

Basis: derived (modeling bridge) — Salsa's backdating compares values (`fp = id` in this model) with revision stamps, which are not modeled; see *Modeling bridge to real systems*.

### 3. `every-replay-order-is-value-sound` (theorem, tier T1)

**Plain claim.** For every replay order (recorded order stopping at the first changed dependency, reversed order, or checking all recorded dependencies) and either cutoff mode, with collision-free fingerprints, unchanged query code and a database consistent with the old input state, every incremental fetch made during the revision (from the start database, or from any working database produced from it by earlier fetches with the same configuration) that returns a value returns a value that from-scratch evaluation in the new state returns at some fuel. Out-of-order replay can therefore fail only by panicking or by not finishing (ordered-replay-necessary), never by returning a wrong value.

**Tier T1.** That a verifying-trace check which requires every recorded dependency to reproduce its fingerprint can only reuse correct results, whatever the checking order, is implicit in the rustc-dev-guide's description of out-of-order checking as a cause of ICEs (crashes) rather than wrong results; made precise and mechanized here in a toy model.

**Lean statement(s).** Quoted verbatim from the sources, docstring included, up to the proof.

`Toy/RedGreen/ValueSound.lean` — `Toy.RedGreen.fetch_value_sound_of_any_replay`:

```lean
/-- **Value soundness for every replay order (card
`every-replay-order-is-value-sound`).**  For any configuration — recorded,
reversed or all-edges replay, early cutoff on or off — collision-free
fingerprints, the same query code as the one that produced the database, and
a database consistent with the old input state: every incremental fetch made
during the revision (from the start database or from any database produced
from it by earlier fetches) that returns a value returns a from-scratch value
of the new state. -/
theorem fetch_value_sound_of_any_replay [DecidableEq Q] [DecidableEq F] (cfg : Config)
    (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (m : Nat) (k : Key Q I) (v : V)
    (hv : (fetch cfg rulesNew fp newInp m db k).1 = .val v) :
    ∃ n, eval rulesNew newInp n k = .val v
```

`cfg : Config` is arbitrary: any `Replay` (`ordered`, `reversed`, `exhaustive`) and either cutoff mode. `hv` is a hypothesis bound before the colon: the theorem concerns fetches that return the value `v`. The conclusion `∃ n, eval rulesNew newInp n k = .val v` says that `v` is the from-scratch value of `k` in the new state at some fuel. `FpInjective`, `DBConsistent` and `Reachable` unfold as in `incremental-fetch-agrees`.

Hypothesis ledger:

| Hypothesis | Tightness | Counterexample(s) | Why it is needed |
| :--- | :--- | :--- | :--- |
| `hsame : rulesOld = rulesNew (unchanged query code across revisions)` | tight | `Toy.RedGreen.ambient_dependent_code_matches_no_from_scratch_eval` | A result of the old code can be reused next to a re-executed result of the new code; the combination is a value that neither rule set produces. |
| `hfp : FpInjective fp` | tight | `Toy.RedGreen.fp_collision_reuses_stale_result` | With a collision a changed dependency looks unchanged and a stale value is reused. |
| `hcons : DBConsistent rulesOld fp oldInp odb` | tight | `Toy.RedGreen.inconsistent_db_reuses_wrong_result` | A wrong recorded result is reused verbatim when its trace replays unchanged. |
| `hreach : Reachable cfg rulesNew fp newInp (start odb) db` | tight | `Toy.RedGreen.stale_done_slot_returns_wrong_result` | A working database not produced by the algorithm (a done slot holding an old-state entry, proved unreachable) returns the stale value. |
| `hv : (fetch cfg rulesNew fp newInp m db k).1 = .val v (the fetch returns the value v)` | tight | `Toy.RedGreen.cyclic_new_state_both_diverge` | Selects the fetches the theorem is about: those that return a value, and binds v to that value. Without it v is unconstrained and the conclusion fails whenever the fetch panics or does not finish. In the counterexample every other hypothesis holds (ordered replay with either cutoff mode, unchanged code, identity fingerprints, a database recorded from scratch, the start database), the fetch is stuck at every fuel, and from-scratch evaluation is stuck at every fuel, so no v is a from-scratch value. |

**Depth: substantive.** Fully proved by a mutual induction over fuel, programs and dependency lists: one fetch preserves Inv and returns only from-scratch values (fetch_inv_and_value_sound); the key step is that a green verdict, in any order, means every recorded dependency reproduced its fingerprint, so (by injectivity and fuel monotonicity) the old entry's code runs along its recorded trace in the new state.

**Non-vacuity witness.** Example K, for every replay order and cutoff mode: after fetching a, the working database is reachable, and fetching top returns the from-scratch value 2. Lean: `Toy.RedGreen.fetch_value_sound_nonvacuous`.

**Prior art.** [S1] rustc-dev-guide, incremental-compilation chapters, [S2] rust-lang/rust, `try_mark_previous_green`, [S4] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte", ICFP 2018, [S5] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte: Theory and practice", JFP 2020, [S7] Hammer, Khoo, Hicks, Foster, "Adapton", PLDI 2014. Full records and the content relied on are under **Evidence**, *Primary sources*.

**Design question.** Incremental compilers and build systems memoize demand-driven queries and, after an input change, re-validate a query by replaying its recorded dependency trace (red-green marking with early cutoff). Under which conditions does an incremental fetch equal from-scratch evaluation, and which shortcuts break it? This card shows that reordering or parallelizing dependency checks affects only panics and termination: the values returned remain from-scratch values.

**Non-claims.** See **Boundaries**, card `every-replay-order-is-value-sound`.

Basis: execution (Lean kernel check) — every theorem named in this card is accepted by the Lean kernel; axioms per theorem are listed under **Evidence**.

Basis: derived (modeling bridge) — this is consistent with the rustc-dev-guide's description of out-of-order try-mark-green visits as causing ICEs (crashes) rather than wrong results; the guide does not state value soundness, and the correspondence is argued, not proved.

### 4. `ordered-replay-necessary` (counterexample, tier T1)

**Plain claim.** Ordered replay cannot be dropped from incremental-fetch-agrees: in concrete instances satisfying every other hypothesis (unchanged code, identity fingerprints, a database recorded from scratch in the old state, the start database), replaying a query's recorded dependencies in reverse order, or checking all of them past the first changed one, executes a recorded dependency that the new inputs have made dead. When that dependency panics, the incremental fetch panics although from scratch the query returns 0. When it closes a code-level cycle that is live in neither state (every query terminates in both states), the incremental fetch is stuck at every fuel although from scratch the query returns 0, so agreement, eventual equality and termination transfer all fail. This holds for both variants and either cutoff mode; on the same instances ordered replay returns 0.

**Tier T1.** The rustc-dev-guide states informally that try-mark-green must visit reads in their original order and that out-of-order visits can execute queries and lead to ICEs; Adapton and the OOPSLA 2015 build system also check dependencies in order. Made precise here with concrete instances satisfying every other hypothesis of incremental-fetch-agrees.

**Lean statement(s).** Quoted verbatim from the sources, docstring included, up to the proof.

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.reversed_replay_executes_dead_dependency_and_panics`:

```lean
/-- **Out-of-order replay executes a dead dependency that panics.**  In example
D all hypotheses of `fetch_agrees_with_eval_of_ordered_replay` other than
ordered replay hold (same code, identity fingerprints, a database recorded
from scratch in the old state).  The recorded dependency `risky` of `top` is
dead in the new state and panics there.  From scratch, `top` evaluates to `0`;
with reversed replay (early cutoff on or off) the incremental fetch panics. -/
theorem reversed_replay_executes_dead_dependency_and_panics (c : Bool) :
    rulesD = rulesD ∧ FpInjective fpId ∧ DBConsistent rulesD fpId oldD odbD ∧
    odbD .top = some ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ ∧
    (rulesD .top).runT (eval rulesD newD 3) fpId = (.val 0, [(.inl .guard, 0)]) ∧
    eval rulesD newD 2 (.inl .risky) = .panic ∧
    eval rulesD newD 3 (.inl .top) = .val 0 ∧
    (fetch ⟨.reversed, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 = .panic ∧
    ¬ AgreesWithEval ⟨.reversed, c⟩ rulesD fpId newD (start odbD) (.inl .top)
```

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.exhaustive_replay_executes_dead_dependency_and_panics`:

```lean
/-- **Checking all recorded dependencies executes a dead dependency that
panics.**  Same instance as `reversed_replay_executes_dead_dependency_and_panics`,
with exhaustive replay (every recorded dependency is checked even after
`guard` has changed). -/
theorem exhaustive_replay_executes_dead_dependency_and_panics (c : Bool) :
    rulesD = rulesD ∧ FpInjective fpId ∧ DBConsistent rulesD fpId oldD odbD ∧
    odbD .top = some ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ ∧
    (rulesD .top).runT (eval rulesD newD 3) fpId = (.val 0, [(.inl .guard, 0)]) ∧
    eval rulesD newD 2 (.inl .risky) = .panic ∧
    eval rulesD newD 3 (.inl .top) = .val 0 ∧
    (fetch ⟨.exhaustive, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 = .panic ∧
    ¬ AgreesWithEval ⟨.exhaustive, c⟩ rulesD fpId newD (start odbD) (.inl .top)
```

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.reversed_replay_diverges_on_dead_code_cycle`:

```lean
/-- **Out-of-order replay diverges on a dead code-level cycle.**  In example C
the code contains the cycle `top → risky → top`, but it is live in neither
state: every query terminates in the old and in the new state, and from
scratch `top` evaluates to `0` in the new state.  All hypotheses of the
theorems of card `incremental-fetch-agrees` other than ordered replay hold
(with `db` the start database).  With reversed replay (early cutoff on or off)
the incremental fetch of `top` is `stuck` at every fuel, so agreement,
eventual equality and termination transfer all fail. -/
theorem reversed_replay_diverges_on_dead_code_cycle (c : Bool) :
    rulesC = rulesC ∧ FpInjective fpId ∧ DBConsistent rulesC fpId oldD odbC ∧
    Reachable ⟨.reversed, c⟩ rulesC fpId newD (start odbC) (start odbC) ∧
    (∀ q, Terminates rulesC oldD (.inl q) ∧ Terminates rulesC newD (.inl q)) ∧
    eval rulesC newD 3 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.reversed, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 = .stuck) ∧
    ¬ AgreesWithEval ⟨.reversed, c⟩ rulesC fpId newD (start odbC) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.reversed, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 =
        eval rulesC newD m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
        (fetch ⟨.reversed, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 ≠ .stuck)
```

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.exhaustive_replay_diverges_on_dead_code_cycle`:

```lean
/-- **Checking all recorded dependencies diverges on a dead code-level
cycle.**  Same instance, exhaustive replay: the incremental fetch of `top` is
`stuck` at every fuel (early cutoff on or off). -/
theorem exhaustive_replay_diverges_on_dead_code_cycle (c : Bool) :
    rulesC = rulesC ∧ FpInjective fpId ∧ DBConsistent rulesC fpId oldD odbC ∧
    Reachable ⟨.exhaustive, c⟩ rulesC fpId newD (start odbC) (start odbC) ∧
    (∀ q, Terminates rulesC oldD (.inl q) ∧ Terminates rulesC newD (.inl q)) ∧
    eval rulesC newD 3 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.exhaustive, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 = .stuck) ∧
    ¬ AgreesWithEval ⟨.exhaustive, c⟩ rulesC fpId newD (start odbC) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.exhaustive, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 =
        eval rulesC newD m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
        (fetch ⟨.exhaustive, c⟩ rulesC fpId newD m (start odbC) (.inl .top)).1 ≠ .stuck)
```

Hypothesis ledger: none (a counterexample card: its theorems are hypothesis-free statements about concrete instances; the hypotheses each instance satisfies are conjuncts of the statement).

**Depth: shallow.** Kernel evaluation of concrete instances, plus short strong inductions on fuel for divergence at every fuel.

**Non-vacuity witness.** Example D (panic) and example C (divergence); each satisfies every hypothesis of incremental-fetch-agrees except ordered replay, proved in the same theorems. Lean: `Toy.RedGreen.reversed_replay_executes_dead_dependency_and_panics`, `Toy.RedGreen.exhaustive_replay_executes_dead_dependency_and_panics`, `Toy.RedGreen.reversed_replay_diverges_on_dead_code_cycle`, `Toy.RedGreen.exhaustive_replay_diverges_on_dead_code_cycle`.

**Positive control.** `Toy.RedGreen.ordered_replay_returns_from_scratch_value_on_dead_dependency`: on both instances, the panic instance (example D) and the divergence instance (example C), in each of which a recorded dependency becomes dead in the new state, ordered replay returns the from-scratch value `0` for either cutoff mode; in example D it also leaves the slot of the dead dependency `risky` equal to its slot in the start database.

`Toy/RedGreen/Replay.lean` — `Toy.RedGreen.ordered_replay_returns_from_scratch_value_on_dead_dependency`:

```lean
/-- **Positive control.**  On the same two instances, ordered replay (early
cutoff on or off) returns the from-scratch value `0`, and in example D leaves
the dead dependency `risky` untouched. -/
theorem ordered_replay_returns_from_scratch_value_on_dead_dependency (c : Bool) :
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).1 = .val 0 ∧
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 (start odbD) (.inl .top)).2 .risky =
      start odbD .risky ∧
    (fetch ⟨.ordered, c⟩ rulesC fpId newD 6 (start odbC) (.inl .top)).1 = .val 0
```

**Prior art.** [S1] rustc-dev-guide, incremental-compilation chapters, [S2] rust-lang/rust, `try_mark_previous_green`, [S5] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte: Theory and practice", JFP 2020, [S7] Hammer, Khoo, Hicks, Foster, "Adapton", PLDI 2014, [S6] Erdweg, Lichter, Weiel, OOPSLA 2015, [S9] Heydon, Levin, Yu, PLDI 2000, [S11] Konat, Erdweg, Visser, ASE 2018. Full records and the content relied on are under **Evidence**, *Primary sources*.

**Design question.** Incremental compilers and build systems memoize demand-driven queries and, after an input change, re-validate a query by replaying its recorded dependency trace (red-green marking with early cutoff). Under which conditions does an incremental fetch equal from-scratch evaluation, and which shortcuts break it? This card shows why replay must follow recorded order and stop at the first changed dependency (the dynamic-dependency sharpness result), and which failures (panics, divergence) out-of-order checking causes.

**Non-claims.** See **Boundaries**, card `ordered-replay-necessary`.

Basis: execution (Lean kernel check) — every theorem named in this card is accepted by the Lean kernel; axioms per theorem are listed under **Evidence**.

Basis: derived (modeling bridge) — the rustc-dev-guide states the in-order requirement and the failure mode informally (quoted under *Modeling bridge to real systems*); the instances here show that failure mode in the model only.

### 5. `fingerprint-collision-breaks-reuse` (counterexample, tier T0)

**Plain claim.** Collision-freedom cannot be dropped. (1) With parity fingerprints, a query returning input x is marked green when x changes from 1 to 3 and returns the stale 1 (either cutoff mode; every other hypothesis of incremental-fetch-agrees and of every-replay-order-is-value-sound holds). (2) With fingerprints min v 10, under which the inputs do not collide but a re-executed query's results 11 and 12 do, early cutoff returns the stale 11 while re-execution returns 12. (3) With parity fingerprints, an input change invisible to the fingerprints makes ordered replay follow a dependency that closes a cycle in the new state, so the fetch is stuck at every fuel although the new state terminates. (4) With fingerprints colliding on 1 and 3, an upstream collision makes early cutoff execute a cached query all of whose recorded dependencies are unchanged in the new state.

**Tier T0.** That fingerprint collisions cause missed updates is stated in the rustc-dev-guide; restated with concrete instances.

**Lean statement(s).** Quoted verbatim from the sources, docstring included, up to the proof.

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.fp_collision_reuses_stale_result`:

```lean
/-- **A fingerprint collision reuses a stale result.**  Example H: `top`
returns input `x`, which changes from `1` to `3`; parity fingerprints collide
on `1` and `3`.  Ordered replay (early cutoff on or off), the same code, a
database recorded from scratch in the old state: all other hypotheses of
`fetch_agrees_with_eval_of_ordered_replay` and of
`fetch_value_sound_of_any_replay` hold.  The incremental fetch marks `top`
green and returns the stale `1`; from scratch it is `3` at every fuel at which
it finishes. -/
theorem fp_collision_reuses_stale_result (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesH = rulesH ∧
    DBConsistent rulesH fpParity oldH odbH ∧ ¬ FpInjective fpParity ∧
    (fetch ⟨.ordered, c⟩ rulesH fpParity newH 4 (start odbH) (.inl .top)).1 = .val 1 ∧
    eval rulesH newH 2 (.inl .top) = .val 3 ∧
    (∀ n, eval rulesH newH n (.inl .top) ≠ .val 1) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesH fpParity newH (start odbH) (.inl .top)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.fp_collision_breaks_early_cutoff`:

```lean
/-- **A collision on a re-executed query breaks early cutoff.**  Example S:
input fingerprints do not collide (`1 ↦ 1`, `2 ↦ 2`) but `a`'s old and new
results `11`, `12` collide under `fpSat`.  All other hypotheses of
`early_cutoff_agrees_with_reexecution_of_ordered_replay` hold.  With early
cutoff `top` is marked green and returns the stale `11`; without it `top` is
re-executed and returns `12` (the from-scratch value). -/
theorem fp_collision_breaks_early_cutoff :
    (Replay.ordered = .ordered) ∧ rulesS = rulesS ∧
    DBConsistent rulesS fpSat oldS odbS ∧ ¬ FpInjective fpSat ∧
    (fetch ⟨.ordered, true⟩ rulesS fpSat newS 6 (start odbS) (.inl .top)).1 = .val 11 ∧
    (fetch ⟨.ordered, false⟩ rulesS fpSat newS 6 (start odbS) (.inl .top)).1 = .val 12 ∧
    eval rulesS newS 3 (.inl .top) = .val 12 ∧
    ¬ (∀ m₁ m₂,
      (fetch ⟨.ordered, true⟩ rulesS fpSat newS m₁ (start odbS) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, false⟩ rulesS fpSat newS m₂ (start odbS) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, true⟩ rulesS fpSat newS m₁ (start odbS) (.inl .top)).1 =
        (fetch ⟨.ordered, false⟩ rulesS fpSat newS m₂ (start odbS) (.inl .top)).1)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.fp_collision_diverges_although_new_state_terminates`:

```lean
/-- **A fingerprint collision can make the incremental fetch diverge although
the new state terminates.**  Under parity fingerprints the change `x : 1 → 3`
is invisible, so `top` replays its old trace and fetches `a`, which in the new
state (`y = 1`) fetches `top`: the incremental fetch is `stuck` at every fuel,
while from scratch `top = 0`.  All other hypotheses of the theorems of card
`incremental-fetch-agrees` hold (with `db` the start database); agreement,
eventual equality and termination transfer all fail. -/
theorem fp_collision_diverges_although_new_state_terminates (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesFpLoop = rulesFpLoop ∧
    ¬ FpInjective fpParity ∧ DBConsistent rulesFpLoop fpParity oldFpLoop odbFpLoop ∧
    Reachable ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop (start odbFpLoop) (start odbFpLoop) ∧
    Terminates rulesFpLoop newFpLoop (.inl .top) ∧
    eval rulesFpLoop newFpLoop 2 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop m (start odbFpLoop) (.inl .top)).1 =
      .stuck) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop (start odbFpLoop) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop m (start odbFpLoop) (.inl .top)).1 =
        eval rulesFpLoop newFpLoop m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesFpLoop fpParity newFpLoop m (start odbFpLoop) (.inl .top)).1 ≠
        .stuck)
```

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.fp_collision_reexecutes_query_with_unchanged_recorded_dependencies`:

```lean
/-- **Collision-freedom is needed.**  Example F: `fpCollide13` collides on `1`
and `3`.  Every other hypothesis holds for `q = top` (its recorded dependency
`b ↦ 30` is unchanged in the new state), yet fetching `top` executes it: the
collision makes `a` look unchanged, so `a` is marked green with the stale `1`;
`b` is re-executed because `y` changed and computes `10` from the stale `a`;
`10` differs from the recorded `30`, so `top` is executed. -/
theorem fp_collision_reexecutes_query_with_unchanged_recorded_dependencies :
    ¬ FpInjective fpCollide13 ∧ Inv rulesF fpCollide13 oldF newF (start odbF) ∧
    start odbF .top = .old eF ∧
    (∀ d f, (d, f) ∈ eF.deps → ∃ n v, eval rulesF newF n d = .val v ∧ fpCollide13 v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesF fpCollide13 newF (start odbF) (start odbF) ∧
    .top ∈ execLog ⟨.ordered, true⟩ rulesF fpCollide13 newF 8 (start odbF) (.inl .top)
```

Hypothesis ledger: none (a counterexample card: its theorems are hypothesis-free statements about concrete instances; the hypotheses each instance satisfies are conjuncts of the statement).

**Depth: shallow.** Kernel evaluation of concrete instances, plus a strong induction on fuel for divergence at every fuel.

**Non-vacuity witness.** Examples H, S, the parity divergence instance and example F; database consistency (and Inv) is proved in the same theorems. Lean: `Toy.RedGreen.fp_collision_reuses_stale_result`, `Toy.RedGreen.fp_collision_breaks_early_cutoff`, `Toy.RedGreen.fp_collision_diverges_although_new_state_terminates`, `Toy.RedGreen.fp_collision_reexecutes_query_with_unchanged_recorded_dependencies`.

**Prior art.** [S1] rustc-dev-guide, incremental-compilation chapters, [S3] Salsa book, `maybe_changed_after` and backdating. Full records and the content relied on are under **Evidence**, *Primary sources*.

**Design question.** Incremental compilers and build systems memoize demand-driven queries and, after an input change, re-validate a query by replaying its recorded dependency trace (red-green marking with early cutoff). Under which conditions does an incremental fetch equal from-scratch evaluation, and which shortcuts break it? This card shows that fingerprint equality must imply value equality, for agreement, for early cutoff, for termination, and for the re-execution savings of early cutoff.

**Non-claims.** See **Boundaries**, card `fingerprint-collision-breaks-reuse`.

Basis: execution (Lean kernel check) — every theorem named in this card is accepted by the Lean kernel; axioms per theorem are listed under **Evidence**.

Basis: derived (modeling bridge) — the rustc-dev-guide names fingerprint collisions as a cause of missed updates; the counterexamples are the model's version, with non-injective fingerprint functions chosen to collide, and say nothing about real hash functions.

### 6. `untracked-change-breaks-reuse` (counterexample, tier T0)

**Plain claim.** Unchanged query code cannot be dropped. If the query code depends on a revision-wide parameter that is not a tracked input (for example a compiler version or a global build flag; 0 when the database was recorded, 1 in the current revision), the code that produced the database (rulesN 0) differs from the code that runs now (rulesN 1). In the new input state the current code gives top = 111 and the recording code gives top = 1, and the incremental fetch returns 101, which neither rule set produces at any fuel: it combines a reused result of the old code with a re-executed result of the new. For another such program early cutoff returns 0 (recorded by the old code) while re-execution returns 1. And a code change between revisions can make the incremental fetch stuck at every fuel although the new state terminates. Every other hypothesis holds in each instance.

**Tier T0.** Build Systems à la Carte (Sec. 6.3) lists untracked dependencies (such as a compiler version) as a source of incorrect builds; restated here with concrete instances in this model.

**Lean statement(s).** Quoted verbatim from the sources, docstring included, up to the proof.

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.ambient_dependent_code_matches_no_from_scratch_eval`:

```lean
/-- **An untracked parameter change makes the incremental result match
neither rule set.**  Example N: the query code depends on a revision-wide
parameter that is not a tracked input (`0` when the database was recorded, `1`
in the current revision), so the code that produced the database (`rulesN 0`)
differs from the code that runs now (`rulesN 1`).  Ordered replay (early cutoff
on or off), identity fingerprints, a database recorded from scratch by
`rulesN 0` in the old state: all hypotheses of
`fetch_agrees_with_eval_of_ordered_replay` except unchanged code hold.  In the
new input state, `rulesN 1` (the current code) gives `top = 111`, and
`rulesN 0` (the code that produced the database) gives `top = 1`; the
incremental fetch returns `101`, which neither rule set produces at any fuel:
it combines a reused `a` computed by `rulesN 0` with a re-executed `top`
computed by `rulesN 1`. -/
theorem ambient_dependent_code_matches_no_from_scratch_eval (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧
    DBConsistent (rulesN 0) fpId oldN odbN ∧ FpInjective fpId ∧ rulesN 0 ≠ rulesN 1 ∧
    eval (rulesN 0) newN 6 (.inl .top) = .val 1 ∧
    eval (rulesN 1) newN 6 (.inl .top) = .val 111 ∧
    (fetch ⟨.ordered, c⟩ (rulesN 1) fpId newN 6 (start odbN) (.inl .top)).1 = .val 101 ∧
    (∀ n, eval (rulesN 0) newN n (.inl .top) ≠ .val 101) ∧
    (∀ n, eval (rulesN 1) newN n (.inl .top) ≠ .val 101) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ (rulesN 1) fpId newN (start odbN) (.inl .top)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.ambient_dependent_code_breaks_early_cutoff`:

```lean
/-- **An untracked parameter change breaks early cutoff.**  Example M: `top`
returns `a + noise`; the database was recorded by `rulesM 0`, the revision runs
`rulesM 1`.  All other hypotheses of
`early_cutoff_agrees_with_reexecution_of_ordered_replay` hold.  `a` is
re-executed and reproduces its fingerprint, so with early cutoff `top` is
marked green and returns `0` (recorded by `rulesM 0`); without it `top` is
re-executed by `rulesM 1` and returns `1`. -/
theorem ambient_dependent_code_breaks_early_cutoff :
    (Replay.ordered = .ordered) ∧
    DBConsistent (rulesM 0) fpId oldM odbM ∧ FpInjective fpId ∧ rulesM 0 ≠ rulesM 1 ∧
    (fetch ⟨.ordered, true⟩ (rulesM 1) fpId newM 6 (start odbM) (.inl .top)).1 = .val 0 ∧
    (fetch ⟨.ordered, false⟩ (rulesM 1) fpId newM 6 (start odbM) (.inl .top)).1 = .val 1 ∧
    ¬ (∀ m₁ m₂,
      (fetch ⟨.ordered, true⟩ (rulesM 1) fpId newM m₁ (start odbM) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, false⟩ (rulesM 1) fpId newM m₂ (start odbM) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, true⟩ (rulesM 1) fpId newM m₁ (start odbM) (.inl .top)).1 =
        (fetch ⟨.ordered, false⟩ (rulesM 1) fpId newM m₂ (start odbM) (.inl .top)).1)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.untracked_code_change_diverges_although_new_state_terminates`:

```lean
/-- **A code change between revisions can make the incremental fetch diverge
although the new state terminates.**  The database was recorded by
`rulesOldLoop` (`top` returns `a`); the current code `rulesNewLoop` has
`top := 0` and `a := top`.  Replaying `top`'s old trace fetches `a`, whose new
code fetches `top`: the incremental fetch is `stuck` at every fuel, while from
scratch `top = 0`.  All other hypotheses of the theorems of card
`incremental-fetch-agrees` hold. -/
theorem untracked_code_change_diverges_although_new_state_terminates (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesOldLoop ≠ rulesNewLoop ∧
    FpInjective fpId ∧ DBConsistent rulesOldLoop fpId (inpXY 0 0) odbOldLoop ∧
    Reachable ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) (start odbOldLoop) (start odbOldLoop) ∧
    Terminates rulesNewLoop (inpXY 1 0) (.inl .top) ∧
    eval rulesNewLoop (inpXY 1 0) 1 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) m (start odbOldLoop) (.inl .top)).1 =
      .stuck) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) (start odbOldLoop) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) m (start odbOldLoop) (.inl .top)).1 =
        eval rulesNewLoop (inpXY 1 0) m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesNewLoop fpId (inpXY 1 0) m (start odbOldLoop) (.inl .top)).1 ≠
        .stuck)
```

Hypothesis ledger: none (a counterexample card: its theorems are hypothesis-free statements about concrete instances; the hypotheses each instance satisfies are conjuncts of the statement).

**Depth: shallow.** Kernel evaluation of concrete instances, fuel monotonicity of from-scratch evaluation (to exclude 101 at every fuel), and a strong induction on fuel for divergence.

**Non-vacuity witness.** Examples N and M and the code-change divergence instance; all other hypotheses of incremental-fetch-agrees, every-replay-order-is-value-sound and early-cutoff-agrees-with-reexecution are proved in the same theorems. Lean: `Toy.RedGreen.ambient_dependent_code_matches_no_from_scratch_eval`, `Toy.RedGreen.ambient_dependent_code_breaks_early_cutoff`, `Toy.RedGreen.untracked_code_change_diverges_although_new_state_terminates`.

**Prior art.** [S18] Mokhov, Mitchell, Peyton Jones, ICFP 2018, Secs. 6.3 and 6.5, [S5] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte: Theory and practice", JFP 2020. Full records and the content relied on are under **Evidence**, *Primary sources*.

**Design question.** Incremental compilers and build systems memoize demand-driven queries and, after an input change, re-validate a query by replaying its recorded dependency trace (red-green marking with early cutoff). Under which conditions does an incremental fetch equal from-scratch evaluation, and which shortcuts break it? This card shows that the code that produced the cache must be the code that runs: every input of a query, including revision-wide parameters, must be tracked.

**Non-claims.** See **Boundaries**, card `untracked-change-breaks-reuse`.

Basis: execution (Lean kernel check) — every theorem named in this card is accepted by the Lean kernel; axioms per theorem are listed under **Evidence**.

### 7. `inconsistent-database-breaks-reuse` (counterexample, tier T0)

**Plain claim.** Neither consistency of the recorded database nor reachability of the working database can be dropped. An entry with the right trace but a wrong result (99 instead of 0; the database is consistent with no input state) is reused verbatim when no recorded dependency changed (either cutoff mode), and with early cutoff also after its dependency was re-executed and reproduced its fingerprint; an inconsistent database whose entries record top as their only dependency makes the fetch stuck at every fuel although the new state terminates. For a consistent recorded database, a working database not reachable from the start database by fetches makes the fetch return a stale result (a done slot holding an old-state entry) or get stuck at every fuel (an old slot recording a self-dependency).

**Tier T0.** That a cache must hold correct entries is a re-derivation; included to show the consistency and reachability hypotheses are necessary.

**Lean statement(s).** Quoted verbatim from the sources, docstring included, up to the proof.

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.inconsistent_db_reuses_wrong_result`:

```lean
/-- **An inconsistent database reuses a wrong result.**  Example B: the entry
for `top` has the right trace but the wrong result `99`, so `odbB` is
consistent with no input state.  Ordered replay (early cutoff on or off),
identity fingerprints, the same code: all other hypotheses of
`fetch_agrees_with_eval_of_ordered_replay` and of
`fetch_value_sound_of_any_replay` hold.  The input does not change between the
two states; every recorded dependency is unchanged, so the incremental fetch
returns the recorded `99`; from scratch `top` is `0`. -/
theorem inconsistent_db_reuses_wrong_result (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesB = rulesB ∧ FpInjective fpId ∧
    (∀ oldInp, ¬ DBConsistent rulesB fpId oldInp odbB) ∧
    (fetch ⟨.ordered, c⟩ rulesB fpId oldB 6 (start odbB) (.inl .top)).1 = .val 99 ∧
    eval rulesB oldB 3 (.inl .top) = .val 0 ∧
    (∀ n, eval rulesB oldB n (.inl .top) ≠ .val 99) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesB fpId oldB (start odbB) (.inl .top)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.inconsistent_db_breaks_early_cutoff`:

```lean
/-- **An inconsistent database breaks early cutoff.**  Same database, input
`x : 1 → 3`: `a` is re-executed and reproduces its fingerprint, so with early
cutoff the wrong recorded `99` is reused; without it `top` is re-executed and
returns `0`. -/
theorem inconsistent_db_breaks_early_cutoff :
    (Replay.ordered = .ordered) ∧ rulesB = rulesB ∧ FpInjective fpId ∧
    (∀ oldInp, ¬ DBConsistent rulesB fpId oldInp odbB) ∧
    (fetch ⟨.ordered, true⟩ rulesB fpId newB 6 (start odbB) (.inl .top)).1 = .val 99 ∧
    (fetch ⟨.ordered, false⟩ rulesB fpId newB 6 (start odbB) (.inl .top)).1 = .val 0 ∧
    ¬ (∀ m₁ m₂,
      (fetch ⟨.ordered, true⟩ rulesB fpId newB m₁ (start odbB) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, false⟩ rulesB fpId newB m₂ (start odbB) (.inl .top)).1 ≠ .stuck →
      (fetch ⟨.ordered, true⟩ rulesB fpId newB m₁ (start odbB) (.inl .top)).1 =
        (fetch ⟨.ordered, false⟩ rulesB fpId newB m₂ (start odbB) (.inl .top)).1)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.inconsistent_db_diverges_although_new_state_terminates`:

```lean
/-- **An inconsistent database can make the incremental fetch diverge although
the new state terminates.**  Every entry of `odbLoop` records `top` as its only
dependency (no input state produces such entries for `rulesZ`, whose queries
fetch nothing); replaying `top` fetches `top`: `stuck` at every fuel, while
from scratch `top = 0`.  All other hypotheses of the theorems of card
`incremental-fetch-agrees` hold. -/
theorem inconsistent_db_diverges_although_new_state_terminates (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesZ = rulesZ ∧ FpInjective fpId ∧
    (∀ oldInp, ¬ DBConsistent rulesZ fpId oldInp odbLoop) ∧
    Reachable ⟨.ordered, c⟩ rulesZ fpId newD (start odbLoop) (start odbLoop) ∧
    Terminates rulesZ newD (.inl .top) ∧
    eval rulesZ newD 1 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesZ fpId newD m (start odbLoop) (.inl .top)).1 = .stuck) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesZ fpId newD (start odbLoop) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.ordered, c⟩ rulesZ fpId newD m (start odbLoop) (.inl .top)).1 =
        eval rulesZ newD m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
        (fetch ⟨.ordered, c⟩ rulesZ fpId newD m (start odbLoop) (.inl .top)).1 ≠ .stuck)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.stale_done_slot_returns_wrong_result`:

```lean
/-- **Reachability is needed: a stale `done` slot returns a wrong result.**
The working database `staleDbD` violates `Inv` (a `done` slot holds an entry
valid only in the old state) and is therefore not reachable from `start odbD`
(every reachable database satisfies `Inv`, `inv_of_reachable`).  Every other
hypothesis of `fetch_agrees_with_eval_during_revision_of_ordered_replay` and of
`fetch_value_sound_of_any_replay` holds, and the incremental fetch returns the
stale `20`, which from-scratch evaluation never returns.  This is also the
counterexample for dropping `Inv` from `fetch_simulation_invariant` (at fuel
`6`, its second conjunct fails). -/
theorem stale_done_slot_returns_wrong_result (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesD = rulesD ∧ FpInjective fpId ∧
    DBConsistent rulesD fpId oldD odbD ∧
    ¬ Inv rulesD fpId oldD newD staleDbD ∧
    ¬ Reachable ⟨.ordered, c⟩ rulesD fpId newD (start odbD) staleDbD ∧
    (fetch ⟨.ordered, c⟩ rulesD fpId newD 6 staleDbD (.inl .top)).1 = .val 20 ∧
    eval rulesD newD 3 (.inl .top) = .val 0 ∧
    (∀ n, eval rulesD newD n (.inl .top) ≠ .val 20) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesD fpId newD staleDbD (.inl .top)
```

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.unreachable_db_diverges_although_new_state_terminates`:

```lean
/-- **Reachability is needed: an unreachable working database can make the
fetch diverge.**  Starting from the empty (hence consistent) database, the
working database `loopDb` (an `old` slot for every query, recording `top` as
its only dependency) is not reachable: fetches never create `old` slots.
Every other hypothesis of the revision theorems of card
`incremental-fetch-agrees` holds, `top` terminates from scratch (`= 0`), and
the incremental fetch from `loopDb` is `stuck` at every fuel. -/
theorem unreachable_db_diverges_although_new_state_terminates (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesZ = rulesZ ∧ FpInjective fpId ∧
    DBConsistent rulesZ fpId oldD odbEmpty ∧
    ¬ Reachable ⟨.ordered, c⟩ rulesZ fpId newD (start odbEmpty) loopDb ∧
    Terminates rulesZ newD (.inl .top) ∧
    eval rulesZ newD 1 (.inl .top) = .val 0 ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesZ fpId newD m loopDb (.inl .top)).1 = .stuck) ∧
    ¬ AgreesWithEval ⟨.ordered, c⟩ rulesZ fpId newD loopDb (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.ordered, c⟩ rulesZ fpId newD m loopDb (.inl .top)).1 =
        eval rulesZ newD m (.inl .top)) ∧
    ¬ (∃ N, ∀ m, N ≤ m → (fetch ⟨.ordered, c⟩ rulesZ fpId newD m loopDb (.inl .top)).1 ≠ .stuck)
```

Hypothesis ledger: none (a counterexample card: its theorems are hypothesis-free statements about concrete instances; the hypotheses each instance satisfies are conjuncts of the statement).

**Depth: shallow.** Kernel evaluation of concrete instances; inconsistency via uniqueness of consistent entries; non-reachability via Inv preservation and the fact that fetches never create old slots; divergence by induction on fuel.

**Non-vacuity witness.** Example B, the self-dependency database, and the unreachable working databases for examples D and the constant program. Lean: `Toy.RedGreen.inconsistent_db_reuses_wrong_result`, `Toy.RedGreen.inconsistent_db_breaks_early_cutoff`, `Toy.RedGreen.inconsistent_db_diverges_although_new_state_terminates`, `Toy.RedGreen.stale_done_slot_returns_wrong_result`, `Toy.RedGreen.unreachable_db_diverges_although_new_state_terminates`.

**Prior art.** [S4] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte", ICFP 2018. Full records and the content relied on are under **Evidence**, *Primary sources*.

**Design question.** Incremental compilers and build systems memoize demand-driven queries and, after an input change, re-validate a query by replaying its recorded dependency trace (red-green marking with early cutoff). Under which conditions does an incremental fetch equal from-scratch evaluation, and which shortcuts break it? This card shows that recorded entries must be faithful from-scratch traces and that the working database must be the one the algorithm produced.

**Non-claims.** See **Boundaries**, card `inconsistent-database-breaks-reuse`.

Basis: execution (Lean kernel check) — every theorem named in this card is accepted by the Lean kernel; axioms per theorem are listed under **Evidence**.

### 8. `cyclic-new-state-both-diverge` (counterexample, tier T0)

**Plain claim.** Termination of the new state is not needed for agreement but is needed for termination transfer: when top fetches itself in the new state (x = 0) but not in the old (x = 1), with a database recorded from scratch, identity fingerprints, unchanged code and ordered replay, from-scratch evaluation and the incremental fetch (either cutoff mode) are both stuck at every fuel, so AgreesWithEval holds while 'the fetch eventually finishes' fails.

**Tier T0.** That cycles make demand-driven evaluation diverge is folklore; that agreement survives them in this fuel-indexed model is a precise restatement rather than a new result.

**Lean statement(s).** Quoted verbatim from the sources, docstring included, up to the proof.

`Toy/RedGreen/Necessity.lean` — `Toy.RedGreen.cyclic_new_state_both_diverge`:

```lean
/-- **A cyclic new state makes both sides diverge, and agreement still
holds.**  Example L: `top` fetches itself when `x = 0`.  The database is
recorded from scratch in the old state (`x = 1`, where `top` terminates);
fingerprints are collision-free; replay is ordered; the code is unchanged.  In
the new state (`x = 0`) `top` does not terminate, from-scratch evaluation and
the incremental fetch (early cutoff on or off) are both `stuck` at every fuel,
and therefore `AgreesWithEval` holds.  So termination of the new state is not
a hypothesis of the agreement theorems; dropping it only defeats
`fetch_eventually_finishes_during_revision_of_terminates`. -/
theorem cyclic_new_state_both_diverge (c : Bool) :
    (⟨.ordered, c⟩ : Config).replay = .ordered ∧ rulesL = rulesL ∧
    FpInjective fpId ∧ DBConsistent rulesL fpId oldL odbL ∧
    Reachable ⟨.ordered, c⟩ rulesL fpId newL (start odbL) (start odbL) ∧
    Terminates rulesL oldL (.inl .top) ∧ ¬ Terminates rulesL newL (.inl .top) ∧
    (∀ m, eval rulesL newL m (.inl .top) = .stuck) ∧
    (∀ m, (fetch ⟨.ordered, c⟩ rulesL fpId newL m (start odbL) (.inl .top)).1 = .stuck) ∧
    AgreesWithEval ⟨.ordered, c⟩ rulesL fpId newL (start odbL) (.inl .top) ∧
    ¬ (∃ N, ∀ m, N ≤ m →
      (fetch ⟨.ordered, c⟩ rulesL fpId newL m (start odbL) (.inl .top)).1 ≠ .stuck)
```

Hypothesis ledger: none (a counterexample card: its theorems are hypothesis-free statements about concrete instances; the hypotheses each instance satisfies are conjuncts of the statement).

**Depth: shallow.** Two short inductions on fuel for a concrete self-dependent program.

**Non-vacuity witness.** Example L; consistency and old-state termination are proved in the same theorem. Lean: `Toy.RedGreen.cyclic_new_state_both_diverge`.

**Prior art.** [S6] Erdweg, Lichter, Weiel, OOPSLA 2015, [S4] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte", ICFP 2018, [S19] Salsa book, cycles. Full records and the content relied on are under **Evidence**, *Primary sources*.

**Design question.** Incremental compilers and build systems memoize demand-driven queries and, after an input change, re-validate a query by replaying its recorded dependency trace (red-green marking with early cutoff). Under which conditions does an incremental fetch equal from-scratch evaluation, and which shortcuts break it? This card shows that termination of the new state (acyclicity, for finite query types) is a liveness hypothesis, not a soundness hypothesis, in this model.

**Non-claims.** See **Boundaries**, card `cyclic-new-state-both-diverge`.

Basis: execution (Lean kernel check) — every theorem named in this card is accepted by the Lean kernel; axioms per theorem are listed under **Evidence**.

Basis: derived (modeling bridge) — systems with cycle detection or fixpoint recovery (for example Salsa's `cycle_fn`/`cycle_initial`) are outside the model; nothing is claimed about them.

### 9. `early-cutoff-skips-cached-query-with-unchanged-dependencies` (theorem, tier T1)

**Plain claim.** With early cutoff and any replay order, collision-free fingerprints, and a working database satisfying the simulation invariant Inv, a query q holding a cached entry e, all of whose recorded dependencies have in the new state values with the recorded fingerprints, is never executed during the rest of the revision: for every working database reachable from the given one by fetches, q's slot is still e unvalidated or e marked green, and no fetch from it executes q, not even an execution that panics or runs out of fuel (executions are observed through the execution log execLog of an instrumented copy of fetch that is proved to have the same outcomes and databases). Without early cutoff this fails (q is executed because a dependency was re-executed, although that dependency reproduced its fingerprint), and even with early cutoff a cached query whose own value is unchanged is executed when one of its recorded dependencies changed.

**Tier T1.** The informal descriptions of early cutoff and backdating (Build Systems à la Carte, Salsa, rustc) state that propagation stops at queries whose dependencies' results did not change; made precise here. Different from the minimality notion of Build Systems à la Carte (Def. 2.1) and the optimality theorems of the OOPSLA 2015 build system, which are not claimed.

**Lean statement(s).** Quoted verbatim from the sources, docstring included, up to the proof.

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps`:

```lean
/-- **Early cutoff never executes a cached query whose recorded dependencies
are unchanged.**  For any replay order with early cutoff, collision-free
fingerprints, and a working database `db₀` satisfying `Inv`: if query `q`
holds the cached entry `e` (`db₀ q = old e`) and every recorded dependency of
`e` has, in the new state, a from-scratch value whose fingerprint is the
recorded one, then for every working database `db` reachable from `db₀` by
incremental fetches, the slot of `q` in `db` is still `old e` or has been
marked green as `done e false`, and no fetch from `db` executes `q`. -/
theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps
    {Q I V F : Type} [DecidableEq Q] [DecidableEq F]
    (r : Replay) (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V)
    (db₀ : DB Q I V F) (hinv : Inv rules fp oldInp newInp db₀)
    (q : Q) (e : Entry Q I V F) (hq : db₀ q = .old e)
    (hunch : ∀ d f, (d, f) ∈ e.deps → ∃ n v, eval rules newInp n d = .val v ∧ fp v = f)
    (db : DB Q I V F) (hreach : Reachable ⟨r, true⟩ rules fp newInp db₀ db)
    (m : Nat) (k : Key Q I) :
    q ∉ execLog ⟨r, true⟩ rules fp newInp m db k ∧ (db q = .old e ∨ db q = .done e false)
```

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies`:

```lean
/-- **Early cutoff is needed.**  Example K with early cutoff off (ordered
replay): every other hypothesis holds for `q = top`, and fetching `top`
executes it (its slot becomes `done … true`), because its dependency `a` was
re-executed, although `a` reproduced its recorded fingerprint. -/
theorem no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .top = .old eK ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, false⟩ rulesK fpId newK (start odbK) (start odbK) ∧
    .top ∈ execLog ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top) ∧
    (fetch ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .top = .done eK true
```

`Toy/RedGreen/Minimal.lean` — `Toy.RedGreen.early_cutoff_reexecutes_query_whose_value_is_unchanged`:

```lean
/-- **Unchanged recorded dependencies are needed — and an unchanged value is
not enough.**  In example K, take `q = a` with its entry `eKa`: every other
hypothesis holds, `a`'s recorded dependency `x` changed (`1 → 3`), and fetching
`top` executes `a`, although `a`'s value (`0`) is the same in both states.
Early cutoff stops propagation at `a`'s dependents, not at `a`. -/
theorem early_cutoff_reexecutes_query_whose_value_is_unchanged :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .a = .old eKa ∧
    ¬ (∀ d f, (d, f) ∈ eKa.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesK fpId newK (start odbK) (start odbK) ∧
    eval rulesK newK 2 (.inl .a) = .val eKa.value ∧
    .a ∈ execLog ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top) ∧
    (fetch ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .a =
      .done ⟨[(.inr .x, 3)], 0⟩ true
```

Key definitions unfolded:

* `execLog cfg rules fp inp n db k` is `(fetchX cfg rules fp inp n (db, []) k).2.2`, the log of an instrumented copy `fetchX` of `fetch` that appends `q` to the log on entering `execX` for `q`, before running `q`'s code; so a query absent from the log was not executed during that fetch, not even partially. `fetchX_eq` (fully proved) states that `fetchX` has exactly the outcome and working database of `fetch` and appends `execLog` to the incoming log.
* `hunch` is spelled out in the statement: every recorded `(d, f)` of `e.deps` has, at some fuel, a from-scratch value `v` in the new state with `fp v = f`.
* `Slot.old e`: a cached entry from the previous state, not yet validated; `Slot.done e false`: the entry `e` marked green (reused without running the query's code); `Slot.done e' true`: the query's code ran to completion in this revision.
* `Inv` and `Reachable` unfold as in `incremental-fetch-agrees`; here `Reachable` starts from the given `db₀`, which need not be a start database.

The conclusion holds for every fuel `m` and every key `k` fetched from `db`.

Hypothesis ledger:

| Hypothesis | Tightness | Counterexample(s) | Why it is needed |
| :--- | :--- | :--- | :--- |
| `cutoff = true (fixed in the statement) (main theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps only)` | tight | `Toy.RedGreen.no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies` | Without early cutoff a re-executed dependency counts as changed even when it reproduces its fingerprint, so its dependents are executed. |
| `hunch : every recorded dependency of e has a new-state value with the recorded fingerprint (main theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps only)` | tight | `Toy.RedGreen.early_cutoff_reexecutes_query_whose_value_is_unchanged` | The precise 'nothing it read changed' condition; a query with a changed recorded dependency is executed even if its own value turns out unchanged. |
| `hinv : Inv rules fp oldInp newInp db₀ (main theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps only)` | tight | `Toy.RedGreen.stale_db_reexecutes_query_with_unchanged_recorded_dependencies` | Fetched dependency values must be new-state values; a stale done slot can make an unchanged dependency look changed. |
| `hfp : FpInjective fp (main theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps only)` | tight | `Toy.RedGreen.fp_collision_reexecutes_query_with_unchanged_recorded_dependencies` | With a collision upstream, a dependency can be recomputed from a stale value to a result with a different fingerprint, although its new-state value has the recorded one. |
| `hq : db₀ q = .old e (main theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps only)` | tight | `Toy.RedGreen.uncached_query_with_unchanged_recorded_dependencies_executes` | Scopes the claim to a query with a cached entry. A query without an entry (slot none) is executed on first demand even when e's recorded dependencies are unchanged. |
| `hreach : Reachable ⟨r, true⟩ rules fp newInp db₀ db (main theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps only)` | tight | `Toy.RedGreen.unreachable_db_reexecutes_query_with_unchanged_recorded_dependencies` | Restricts the claim to working databases produced by fetches from db₀. A database outside this set (proved unreachable: it violates Inv) can make the query execute although its slot is still the cached entry. |

**Depth: substantive.** Needs Inv preservation and value soundness for every replay order (fully proved, every-replay-order-is-value-sound), an argument that the replay of q's recorded dependencies never returns red, and the corresponding argument for the execution log through the instrumented algorithm. The failure instances are kernel evaluations.

**Non-vacuity witness.** Example K, for every replay order: x changes, a is executed and reproduces 0, y is unchanged; top satisfies every hypothesis, fetching top executes only a, and top is marked green. Lean: `Toy.RedGreen.early_cutoff_skips_nonvacuous`.

**Prior art.** [S4] Mokhov, Mitchell, Peyton Jones, "Build systems à la carte", ICFP 2018, [S3] Salsa book, `maybe_changed_after` and backdating, [S1] rustc-dev-guide, incremental-compilation chapters, [S2] rust-lang/rust, `try_mark_previous_green`, [S6] Erdweg, Lichter, Weiel, OOPSLA 2015. Full records and the content relied on are under **Evidence**, *Primary sources*.

**Design question.** Incremental compilers and build systems memoize demand-driven queries and, after an input change, re-validate a query by replaying its recorded dependency trace (red-green marking with early cutoff). Under which conditions does an incremental fetch equal from-scratch evaluation, and which shortcuts break it? This card states exactly how far early cutoff limits re-execution (cached queries whose recorded dependencies are unchanged are never executed), and what it does not limit.

**Non-claims.** See **Boundaries**, card `early-cutoff-skips-cached-query-with-unchanged-dependencies`.

Basis: execution (Lean kernel check) — every theorem named in this card is accepted by the Lean kernel; axioms per theorem are listed under **Evidence**.

### Modeling bridge to real systems

Basis: derived (modeling bridge). None of the statements in this subsection is kernel-checked; each is an argument from the quoted upstream sources (records under **Evidence**) to the model.

* **rustc `try_mark_previous_green` and ordered replay.** In rust-lang/rust at `5c56312f346d7cc8209d9fc0fd660c72e6fc6950`, `compiler/rustc_middle/src/dep_graph/graph.rs`, `fn try_mark_previous_green` (called from `fn try_mark_green`) iterates over the previous session's edge targets of a node in order; a dependency already green is accepted, a red one ends the attempt (`DepNodeColor::Red => return None`), and a dependency of unknown colour is first tried recursively and otherwise forced (re-executed) and its colour re-read. This is the control flow of `markGreen` with `Replay.ordered` and `stopAtRed = true`, with recursive marking corresponding to the nested `fetch`. The mechanisms differ: rustc stores one result fingerprint per node and propagates value-free colours (a forced node is green iff its new result fingerprint equals its own previous one), whereas this model stores a fingerprint per recorded edge and compares the dependency's current value against it. When every query recorded as a dependency in `OldDB` also has its own entry, the recorded edge fingerprint is that dependency's old result fingerprint, so "the re-executed dependency reproduced its fingerprint" and "the dependency is green" coincide; this is argued, not proved. For partial caches no correspondence is claimed (the model's own behaviour is `Toy.RedGreen.partial_cache_example`). `Slot.done e true` records that the query's code ran to completion in this revision; it is not rustc's red colour (a re-executed rustc node with an unchanged result fingerprint is green).
* **Order requirement.** The rustc-dev-guide at `d946d7402d269990f3b64baabaf6592409791c11` (`src/queries/incremental-compilation.md`) states that try-mark-green must visit the reads of a query "in same order as they occurred in the original compilation" and that an out-of-order visit "might visit `subquery2` before `subquery1`, and hence execute it. This can lead to ICEs and other problems in the compiler." `ordered-replay-necessary` exhibits the analogous failure mode in the model (a dead dependency is executed and panics), and `every-replay-order-is-value-sound` shows that in the model such out-of-order visits cause panics or non-termination but never wrong values.
* **Fingerprint collisions.** The same guide (`src/queries/incremental-compilation-in-detail.md`) notes that "two different results could have the same fingerprint and the system would erroneously assume that the result hasn't changed, leading to a missed update"; `fingerprint-collision-breaks-reuse` is the model's version. The guide also states that dependency-graph nodes "are identified by a fingerprint of the query key"; key-fingerprint collisions are not modeled.
* **Salsa.** In salsa-rs/salsa at `496752ea3879af8cf3d71d1e28d76447a0cf6482`, `book/src/plumbing/maybe_changed_after.md` describes verifying a derived query's memo by iterating over each dependency and re-executing (possibly backdating) when one may have changed, and `book/src/plumbing/terminology/backdate.md` defines backdating as marking a recomputed value as last changed in an earlier revision when old and new values compare equal: early cutoff by value comparison with revision stamps. This corresponds to `fp = id` (`FpInjective` holds) in the model, but revision stamps, durability levels and fixed-point cycle recovery (`book/src/cycles.md`: "`cycle_fn` and `cycle_initial`") are not modeled.
* **Shake and Build Systems à la Carte.** Verifying traces with dynamic dependencies and early cutoff are the model of Build Systems à la Carte; Shake's verifying *step* traces differ from verifying traces on change-and-revert sequences across several revisions (JFP 2020, Sec. 5.2.2, Fig. 7), which are outside this single-revision model.
* **Untracked parameters.** `rulesOld = rulesNew` stands for "the same compiler build and configuration produced the incremental cache"; the parameterized programs `rulesN`, `rulesM` stand for query code that reads an untracked revision-wide setting (a compiler version, a global flag), an instance of the untracked dependencies of Build Systems à la Carte (ICFP 2018, Sec. 6.3). They do not model per-call non-determinism.

## Boundaries

Non-claims come first, per card (each is copied from the card's `non_claims` in `results.json`). Status labels: unless stated otherwise, the items are **not examined** (outside the model) or **known not to apply** (refuted by a counterexample in this package).

### Non-claims

**`incremental-fetch-agrees`**

* Per-edge fingerprint traces, not node colours or revision stamps: an Entry stores (dependency, fingerprint) pairs per edge, and markGreen fetches each recorded dependency's current value and compares its fingerprint with the recorded one. rustc instead propagates value-free per-node colours (try_mark_previous_green), and Salsa and Shake compare revision stamps (Salsa with value comparison for backdating). Any correspondence is a modeling bridge (derived, not proved), argued only for databases in which every query recorded as a dependency also has its own entry. For partial caches the model's own behaviour is shown in Toy.RedGreen.partial_cache_example (an entry for top but none for its dependency a, unchanged inputs: cutoff mode executes a and marks top green; no-cutoff mode re-executes top); how a production system treats such a cache is not examined. Change-and-revert sequences across several revisions, which separate verifying traces from step traces (Build Systems à la Carte, JFP 2020, Fig. 7), are outside the single-revision scope.
* Slot.done e true means that the query's code ran to completion in this revision, also when early cutoff then finds its result unchanged; it is not a node colour.
* Agreement is about outcomes only. It says nothing about how many queries are executed, that each query executes at most once per revision, or about time or space; see early-cutoff-skips-cached-query-with-unchanged-dependencies for re-execution.
* Partial correctness is stated as 'equals the from-scratch outcome at some fuel': the incremental fetch can finish with less fuel than from-scratch evaluation (validated slots short-circuit).
* Fuel bounds nesting depth, not work: each nested fetch receives one less fuel independently (including both markGreen and exec when a query turns red, and successive fetches inside one program). Equal-fuel adequacy is a property of this accounting; under a shared step budget it would not hold, because a failed replay followed by re-execution does more work than from-scratch evaluation. No complexity bound is claimed.
* Panicking and fuel-exhausted executions are not memoized: they write no done slot for the aborting query (done slots committed by its sub-fetches before the abort are kept), so demanding such a query again in the same revision executes it again.
* Termination is well-foundedness of the dynamic dependencies of the new state: Q need not be finite, and over an infinite query type an acyclic but unbounded dependency chain also fails Terminates (both sides then diverge). 'Acyclic' is a sufficient description only for finite query types.
* No cycle detection, cycle errors or fixpoint cycle recovery is modeled. In systems that report cycles as errors or compute fixpoints (for example Salsa's cycle_fn/cycle_initial), which member of a cycle is entered first, and what was cached earlier in the revision, could make incremental and from-scratch results differ unless the recovery semantics is independent of entry order (not examined).
* Collision-freedom is exact injectivity of fp on all of V. Nothing is claimed about probabilistic hashing; injectivity on the values of each key would suffice for the arguments used (derived from the proofs, not formalized).
* Unchanged query code is modeled as equality of the old and new rule sets. Untracked reads of revision-wide parameters, side effects, interior mutability, concurrency and per-call non-determinism are not modeled.
* Panics abort: a panicking dependency makes its dependent panic. Systems that catch failures as values are a different model.
* Only one revision is covered: nothing is proved about turning the end-of-revision database into the next revision's start database (garbage collection of unvalidated entries, persistence, eviction, durability levels).
* Ordered replay is required for panics and termination. Other replay orders are value-sound (every-replay-order-is-value-sound); which other orders preserve full agreement for particular program classes (for example static dependencies) is not examined.
* The revision theorems cover only working databases reachable by fetches of this algorithm, with the same configuration, from the start database; databases changed in other ways are excluded, and the hypothesis is needed (see the hreach counterexamples).
* No side outputs: queries produce only an outcome. Diagnostics, warnings or accumulated side outputs emitted during execution are not modeled; a system that reuses green results must persist and replay such outputs separately.
* Keys are compared by exact equality: no hashing or interning of keys across sessions is modeled (rustc identifies dependency-graph nodes by a fingerprint of the query key), and per-query modifiers of production systems (such as rustc's eval_always or no_hash) are not modeled.

**`early-cutoff-agrees-with-reexecution`**

* Mode equivalence, not standalone soundness: the theorem states only that the two cutoff modes agree with each other; agreement of either mode with from-scratch evaluation is incremental-fetch-agrees. Two unsound configurations can also agree with each other (reversed replay with and without early cutoff both panic on example D, Toy.RedGreen.reversed_replay_executes_dead_dependency_and_panics).
* Outcomes of the first fetch only: only the outcome of a fetch from the start database is compared. The working databases the two modes leave behind differ (cutoff mode keeps the old entry marked green, done e false; no-cutoff mode stores a fresh trace, done e' true; Toy.RedGreen.early_cutoff_agrees_nonvacuous), and multi-fetch sessions are not compared directly.
* Per-fuel equality is not claimed: the two modes use different amounts of fuel; only 'whenever both finish' and 'for all large fuel'.
* Says nothing about how much work early cutoff saves; see early-cutoff-skips-cached-query-with-unchanged-dependencies.
* Early cutoff is modeled by fingerprint comparison against the recorded trace; Salsa's backdating compares values and revision stamps. The correspondence is a modeling bridge.
* Inherits the toy-model non-claims of incremental-fetch-agrees (per-edge traces, single revision, fuel as call depth, exact key equality).

**`every-replay-order-is-value-sound`**

* Values only: with out-of-order replay a fetch may panic or never finish where from-scratch evaluation returns a value (ordered-replay-necessary); the theorem says nothing about panics, termination or fuel.
* Reachable includes working databases left behind by earlier fetches that panicked or ran out of fuel (Reachable.step does not require the earlier fetch to finish), so value soundness also holds for every later fetch of the revision after an out-of-order fetch has aborted; it says nothing about the outcome of the aborted fetch itself.
* The all-edges variant is a sequential stand-in for checking all recorded edges without stopping at the first change; concurrent scheduling is not modeled.
* Collision-freedom is exact injectivity of fp on all of V.
* Inherits the toy-model non-claims of incremental-fetch-agrees (per-edge traces, single revision, fuel as call depth, exact key equality).

**`ordered-replay-necessary`**

* The failures are panics and divergence, not wrong values: no replay order returns a wrong value (every-replay-order-is-value-sound, proved).
* Only two variants are covered: reverse recorded order with stop-at-first-change, and recorded order without stopping (a sequential stand-in for checking all recorded edges, for example in parallel). Other orders and real concurrent scheduling are not modeled.
* Escape hatch (derived, not proved here): if a query issues independent requests together as one unconditional batch, then whenever the batch is reached in the new state with all earlier batches unchanged, all of its members are live dependencies. Checking the members of one batch in any order or concurrently, while proceeding across batches in recorded order and stopping at the first batch containing a changed dependency, therefore cannot execute a dead dependency. This model has no batches.
* Escape hatch (derived, not proved here): a concurrent checker that isolates panics of speculatively started dependency checks, never waits on a speculative check before all earlier recorded dependencies are confirmed unchanged, and cancels outstanding checks once a confirmed-prefix dependency is found changed avoids both failure modes shown here; in both examples the first recorded dependency (guard) is already found changed before the dead dependency would have to be awaited.
* Escape hatch (derived, not proved for such models): if query code has no static cycles, the divergence instance cannot be built; if errors are ordinary values rather than panics, the panic instance only wastes the computation of an error value. In both cases out-of-order checking in these instances costs work, not correctness.
* If failures of dead dependencies were caught and treated as 'changed', the panic variant would disappear; the divergence variant would remain (not proved for such a model).
* Nothing is claimed for programs with static dependencies, where every recorded dependency is live whenever the query runs.

**`fingerprint-collision-breaks-reuse`**

* Says nothing about the probability of collisions with real hash functions.
* Does not show that every collision is harmful; only that injectivity cannot be dropped entirely.
* Escape hatch: systems that keep values and compare them by a lawful equality (as in Salsa's backdating) correspond to fp = id, for which FpInjective holds.
* FpInjective requires injectivity on all of V; injectivity on the values of each key would suffice for the arguments used (derived from the proofs, not formalized), so per-key or domain-separated fingerprints are not excluded by these counterexamples.
* Only result fingerprints are modeled; keys are compared exactly. Systems that identify dependency-graph nodes by a fingerprint of the query key (rustc-dev-guide, incremental-compilation-in-detail.md) can also suffer key-fingerprint collisions, which are not covered here.

**`untracked-change-breaks-reuse`**

* Models an untracked change between revisions, not per-call or relational non-determinism: rulesN 0 and rulesN 1 are two deterministic rule sets, each fixed for a whole revision. Under per-invocation non-determinism (as in the non-deterministic task model of Build Systems à la Carte, Sec. 6.3, where each execution may produce any result from a possible set), 101 (a computed with parameter 0, top with parameter 1) is a valid from-scratch outcome (Toy.RedGreen.per_query_parameter_choice_gives_101), and that paper states that most of the build systems it studies can deal with non-determinism.
* Escape hatch: promoting the parameter to a tracked input (so that its change is replayed like any input change), or discarding the database when the code or its parameters change (compare self-tracking, Build Systems à la Carte Sec. 6.5), restores the hypothesis rulesOld = rulesNew (derived). Marking an impure query as always re-executed is a further option, not modeled.
* Does not quantify how far the incremental result can be from any from-scratch result.

**`inconsistent-database-breaks-reuse`**

* Does not model partial writes, corruption detection, or recovery.
* Partial and evicted caches are consistent: DBConsistent constrains only queries with an entry, and a missing entry (odb q = none) does not violate it (Toy.RedGreen.dbConsistent_partial_cache).
* In the two reachability counterexamples the recorded database is consistent; what fails is reachability of the working database (and, for the stale done slot, the invariant Inv). Non-reachability is proved, via inv_of_reachable and via the fact that fetches never create old slots respectively.

**`cyclic-new-state-both-diverge`**

* Termination is well-foundedness of the dynamic dependencies of the new state: Q need not be finite, and over an infinite query type an acyclic but unbounded dependency chain also fails Terminates (both sides then diverge). 'Acyclic' is a sufficient description only for finite query types.
* No cycle detection, cycle errors or fixpoint cycle recovery is modeled. In systems that report cycles as errors or compute fixpoints (for example Salsa's cycle_fn/cycle_initial), which member of a cycle is entered first, and what was cached earlier in the revision, could make incremental and from-scratch results differ unless the recovery semantics is independent of entry order (not examined).
* Does not show that divergence is the only effect of cycles in other models.

**`early-cutoff-skips-cached-query-with-unchanged-dependencies`**

* Scope of the hypothesis ledger: the hypotheses listed for this card are those of the main theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps. The other two theorems listed under this card (no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies and early_cutoff_reexecutes_query_whose_value_is_unchanged) are hypothesis-free statements about the concrete example K and serve as the counterexamples for dropping early cutoff and hunch.
* Not minimality in the sense of Build Systems à la Carte (Def. 2.1: tasks executed at most once per build and only if they transitively depend on changed inputs) and not optimality: it does not say that the algorithm executes the fewest queries possible, that each query executes at most once (an aborted execution is executed again on the next demand), or that queries outside the demanded key's dependencies are untouched.
* Recorded dependencies are still fetched and compared: not executing q's code does not skip validating q when q is demanded; while q's slot is old e, markGreen still fetches every recorded dependency of q (no coarse-grained skipping such as durability levels is modeled). Once a fetch has marked q green (slot done e false), later demands of q in the same revision return the stored value immediately, without running markGreen again.
* Uncached queries execute on demand: the theorem applies only to queries with a cached entry in the starting working database; a query without an entry is executed when demanded (Toy.RedGreen.uncached_query_with_unchanged_recorded_dependencies_executes).
* Executions are observed through execLog, the log of an instrumented copy of fetch proved to have the same outcomes and working databases as fetch (Toy.RedGreen.fetchX_eq). Slots alone do not record executions that panic or run out of fuel (Toy.RedGreen.execLog_example_aborted_execution).
* The converse (a demanded query with a changed recorded dependency is executed) is not stated.
* It is about direct recorded dependencies; transitive formulations follow only by reasoning not given here.
* Inherits the toy-model non-claims of incremental-fetch-agrees (per-edge traces, single revision, fuel as call depth, exact key equality).

### Escape hatches

Escape hatches say which hypotheses, if weakened in a specific way, would *not* re-create the counterexamples. All are `derived`, none is proved in this package:

* **Ordered replay** (`ordered-replay-necessary`): unconditional batches checked in any order but proceeding across batches in recorded order; speculative concurrent checking with panic isolation that never awaits a check before all earlier recorded dependencies are confirmed unchanged and cancels outstanding checks once a confirmed-prefix dependency is changed; query code without static cycles together with errors as values; catching failures of dead dependencies as "changed" (removes the panic variant, not the divergence variant).
* **Unchanged code** (`untracked-change-breaks-reuse`): promote the parameter to a tracked input, or discard the database when the code or its parameters change (compare self-tracking, Build Systems à la Carte, Sec. 6.5).
* **Collision-freedom** (`fingerprint-collision-breaks-reuse`): systems that compare values by a lawful equality correspond to `fp = id`; injectivity on the values of each key would suffice for the arguments used (derived from the proofs, not formalized).

### Hypotheses with `unknown` tightness

None. Every hypothesis of every card is `tight`, with a kernel-checked counterexample in which all other hypotheses hold and the conclusion fails (`cutoff = true` is a parameter fixed in the statement rather than a hypothesis, and has a counterexample with `cutoff = false`).

### Disproved or dropped draft statements

None. Every statement of the nine cards is proved; no statement was weakened, disproved, or removed.

### Other attractive stronger conclusions that are not established

* That rustc, Salsa or Shake is correct, or behaves as the model does on any input (only modeling-bridge arguments are given).
* Minimality or optimality in the sense of Build Systems à la Carte (Def. 2.1) or of the OOPSLA 2015 build system.
* Agreement for working databases not produced by this algorithm, or after a change of configuration within a revision.
* Any bound on time, space, number of executions, or fuel beyond "the incremental fetch finishes with any fuel at which from-scratch evaluation finishes".

## Evidence

### Kernel-check record

Toolchain: `leanprover/lean4:v4.34.1` (tag `v4.34.1` of `leanprover/lean4`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, as reported by the GitHub API). No Mathlib, no Lake dependencies. Evidence acquired on the `observed_at` date of `REPORT.json`.

All 651 non-internal declarations of the library depend only on axioms among `propext`, `Classical.choice`, `Quot.sound` (`audit/axioms.json`); no declaration depends on `sorryAx`, and no `axiom` or `opaque` is declared. The table lists every declaration referenced by `results.json`, with its axioms and the statement and closure hashes recorded in `audit/statements.json` (hash definitions under **Revalidation**).

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.RedGreen.fetch_agrees_with_eval_of_ordered_replay` | result of `incremental-fetch-agrees` | `Quot.sound`, `propext` | `2b2bc708d6c8b7883db4cc1a1efc8d399c308a256626cc75eff5d79e2a064dd3` | `6b85ed08c4a1b0b6fa42c327cafe8bb050c2472f79422c49eab54e567e368004` (88) |
| `Toy.RedGreen.fetch_agrees_with_eval_during_revision_of_ordered_replay` | result of `incremental-fetch-agrees` | `Quot.sound`, `propext` | `a98780774c6070a743108ccda1591376775b8dc4e38f07b70d6b48a464bb8261` | `7a38138b944018a19d1351877d74fa98bca2187c699146add175b4998069e2ad` (91) |
| `Toy.RedGreen.fetch_eventually_eq_eval_during_revision_of_ordered_replay` | result of `incremental-fetch-agrees` | `Classical.choice`, `Quot.sound`, `propext` | `04e2eb381ec061124075476bdb8c9921ecf58b48f5bc1e5560595e122bc48a47` | `617467728a5e1febc6b56073eee58b90ef80665aecd2a13c2e66c06bf09f380f` (90) |
| `Toy.RedGreen.fetch_eventually_finishes_during_revision_of_terminates` | result of `incremental-fetch-agrees` | `Quot.sound`, `propext` | `a16aa298a5fe729d7ba87fb0e4756f866bf7fbb54ef473a5b6e75e8147381be9` | `d4c381c7e056986639f1ee96b6b01f292f5ab5dd1c5cf1ab7ed00f99b1240221` (91) |
| `Toy.RedGreen.fetch_simulation_invariant` | result of `incremental-fetch-agrees` | `Quot.sound`, `propext` | `b61143a435733c1462aab215e54ceab07f1e0d421b004497b034e016c0b96682` | `80867184b2c6408ffa9953deb1485530fa8e20acd3c763a516c9df15fc92aa6e` (85) |
| `Toy.RedGreen.fetch_agrees_with_eval_nonvacuous` | non-vacuity witness of `incremental-fetch-agrees` | `propext` | `a6e92d52f75846804ff43295fe8774db834525cdfd923697e409695c08b2d2f5` | `45e8dc97ebccc10e36c3f5245364c225aab26fee042afb76edda02b816cb1d85` (112) |
| `Toy.RedGreen.fetch_during_revision_nonvacuous` | non-vacuity witness of `incremental-fetch-agrees` | `propext` | `e7b2d832158207570b37dc9253c4d1dd78a23eea01bda1ac1d2e7879a669143e` | `a5efea3655045688f540c19eb6f6b80a6c13f942fd7f6b6fe1e95d4b1d1ee48b` (116) |
| `Toy.RedGreen.fetch_simulation_invariant_nonvacuous` | non-vacuity witness of `incremental-fetch-agrees` | `Quot.sound`, `propext` | `9fec7d6c3fc5d099f856467adcf9fcbc3f4bdce54bd2491013e491792d8951f8` | `9c167aef36b9619b798a55aa43257fe9b5ca77e971ea53f08b82ba1e8b29adbc` (113) |
| `Toy.RedGreen.reversed_replay_executes_dead_dependency_and_panics` | counterexample in `incremental-fetch-agrees`; result of `ordered-replay-necessary` | `Quot.sound`, `propext` | `a2e86efccafeb6d1cc6f5090a46031f666a0fe1aff4db6bd0d7ca4bfb20d2fb1` | `326d79264433dc64341d0dfebf27200012703d219dd3abec39e993fbb39a8bfe` (113) |
| `Toy.RedGreen.exhaustive_replay_executes_dead_dependency_and_panics` | counterexample in `incremental-fetch-agrees`; result of `ordered-replay-necessary` | `Quot.sound`, `propext` | `5abfd682e7dc3a1e212ec5915c7cce906cc0ffcf3a0301682326a8e8360a0e45` | `326d79264433dc64341d0dfebf27200012703d219dd3abec39e993fbb39a8bfe` (113) |
| `Toy.RedGreen.reversed_replay_diverges_on_dead_code_cycle` | counterexample in `incremental-fetch-agrees`; result of `ordered-replay-necessary` | `Quot.sound`, `propext` | `8bd5314208598567853ae1a7627fae897351cc1f0fd4024655c8842dc8a56645` | `84d237dac21001c3160c909de49edc070902bf948d79b818ebbefa5c5979fd7f` (117) |
| `Toy.RedGreen.exhaustive_replay_diverges_on_dead_code_cycle` | counterexample in `incremental-fetch-agrees`; result of `ordered-replay-necessary` | `Quot.sound`, `propext` | `2bbe84856d61e45f1e1fd19766b089441dd2d73f5fd2f8d35ecd6e31ac0d77f7` | `84d237dac21001c3160c909de49edc070902bf948d79b818ebbefa5c5979fd7f` (117) |
| `Toy.RedGreen.ambient_dependent_code_matches_no_from_scratch_eval` | counterexample in `incremental-fetch-agrees`; counterexample in `every-replay-order-is-value-sound`; result of `untracked-change-breaks-reuse` | `Quot.sound`, `propext` | `54e03b2e5f031e10291fd8a8e0c705246bac7700fc9ade3361644da1a7eefe70` | `d32961ddefc87c79e00ad84fc82759acb3d0efbe0d77c0059bd494088eeaa54b` (113) |
| `Toy.RedGreen.untracked_code_change_diverges_although_new_state_terminates` | counterexample in `incremental-fetch-agrees`; result of `untracked-change-breaks-reuse` | `Quot.sound`, `propext` | `4392bca79c4ec19b900e8cd46e5e08a0dea94cc27187fce676eed29ef80f02f6` | `f2e707b99fe6d2af0e52c4c0e6ac0e476abc05d283b1e3d19aed51de8c4627c3` (116) |
| `Toy.RedGreen.fp_collision_reuses_stale_result` | counterexample in `incremental-fetch-agrees`; counterexample in `every-replay-order-is-value-sound`; result of `fingerprint-collision-breaks-reuse` | `Quot.sound`, `propext` | `8ebbc673035dd579334a746fce90a98465dee828903d371248602500ed9d18c3` | `4439eef8c0a43af3adc9074fbe4fc9c3178f8ad0beea1ea5219d3e12a894b2bb` (113) |
| `Toy.RedGreen.fp_collision_diverges_although_new_state_terminates` | counterexample in `incremental-fetch-agrees`; result of `fingerprint-collision-breaks-reuse` | `Quot.sound`, `propext` | `13930a091f4d395428ed5620dedae2282b60c1d3254c38a36b94cfba92fc254f` | `125b10495efcb5fb37d7b69bfe55212f2352e1e6b275b9d9de3e7987b235eb24` (117) |
| `Toy.RedGreen.inconsistent_db_reuses_wrong_result` | counterexample in `incremental-fetch-agrees`; counterexample in `every-replay-order-is-value-sound`; result of `inconsistent-database-breaks-reuse` | `Quot.sound`, `propext` | `1b4f4ee813f732e293b7136e89c041d620b25f67202066fa27dc25021a21e6da` | `9bb5792c01c3a4190bd509bcd1ef60219bb3c362a8f79585f9426f8132d59711` (111) |
| `Toy.RedGreen.inconsistent_db_diverges_although_new_state_terminates` | counterexample in `incremental-fetch-agrees`; result of `inconsistent-database-breaks-reuse` | `Quot.sound`, `propext` | `be79fd6aa83587a393233e9f55842a4e9c3a3cdeb1f06e42bab36a5b75b0ef2d` | `33d7c0f43f8f5521e2e2c48237af3ecd2fc782511f40501a37953290a1f18610` (113) |
| `Toy.RedGreen.stale_done_slot_returns_wrong_result` | counterexample in `incremental-fetch-agrees`; counterexample in `every-replay-order-is-value-sound`; result of `inconsistent-database-breaks-reuse` | `Quot.sound`, `propext` | `61509ed7c7827f2687b325d210bf94ba91169e128d64f22428d697970c5dd670` | `0c00dbb252fe49473bd018082367ca18b0e50cf555c7faad3a999ab414c6f451` (119) |
| `Toy.RedGreen.unreachable_db_diverges_although_new_state_terminates` | counterexample in `incremental-fetch-agrees`; result of `inconsistent-database-breaks-reuse` | `Quot.sound`, `propext` | `0848324cff22f197ab35602fb34e0736fb0974e7623d0771c4f23a0e0cad16d3` | `cdefec8d2e0853ffde3ee91743fe22a926324f81acfc45cf8a55fac262570c5c` (115) |
| `Toy.RedGreen.cyclic_new_state_both_diverge` | counterexample in `incremental-fetch-agrees`; counterexample in `every-replay-order-is-value-sound`; result of `cyclic-new-state-both-diverge` | `Quot.sound`, `propext` | `3d8c070d1fbd9789464fccfad23e18da05f5c605df9b3d118adad455278ab91d` | `b615e4a291ca16739d488d26fffc30fd8d34c09ce75422e12470698837707758` (117) |
| `Toy.RedGreen.early_cutoff_agrees_with_reexecution_of_ordered_replay` | result of `early-cutoff-agrees-with-reexecution` | `Classical.choice`, `Quot.sound`, `propext` | `feed991f212d314e5cae8048bfdab12d85ed8f12b7f28e29c8d8495874e714f3` | `c10d656d37c8edf7b2a7d4f3df4503856294ff6fccf98b245ca292090f5c2071` (87) |
| `Toy.RedGreen.early_cutoff_agrees_nonvacuous` | non-vacuity witness of `early-cutoff-agrees-with-reexecution` | `propext` | `c44b13a0bb7b161751dbaa6ae5382621ef2b20d079561ad632d30499625a7875` | `2bd1743d7667624e8bcc7cf61a4e4fb0550397873322ac087e89b10e138f34f9` (113) |
| `Toy.RedGreen.reversed_replay_breaks_early_cutoff_agreement` | counterexample in `early-cutoff-agrees-with-reexecution` | `propext` | `1c0fab81048de828b9abb25506a9bd56f33da284a2d2eba306f81c12f7f640f8` | `bb988e6e62d4453abc47306964bbab18413e7687e2859970586f44c1f7da1655` (113) |
| `Toy.RedGreen.ambient_dependent_code_breaks_early_cutoff` | counterexample in `early-cutoff-agrees-with-reexecution`; result of `untracked-change-breaks-reuse` | `propext` | `456fcc5f418e3f960faf440da68dfb1c77c4fb0f0ed168ecf4ebd4dec7e97d8e` | `d1c8c165cd4c2b50494e9368a20dc04575a5758a7cc1a72141c0ea7d51bd8faa` (112) |
| `Toy.RedGreen.fp_collision_breaks_early_cutoff` | counterexample in `early-cutoff-agrees-with-reexecution`; result of `fingerprint-collision-breaks-reuse` | `propext` | `282baa4dd5467cbe1a4dd299e48c00e09b5dd95fd652a573ac1603495854e78e` | `5fcb0544b1a6b77a0482fc3867acd2c5307dd64c232be7d55f868ac2e5dda0cc` (112) |
| `Toy.RedGreen.inconsistent_db_breaks_early_cutoff` | counterexample in `early-cutoff-agrees-with-reexecution`; result of `inconsistent-database-breaks-reuse` | `Quot.sound`, `propext` | `f0fecc7f2d640c36a044907c004f5c783e30e62b977344c66d768d557c41f879` | `131e9f6c8c6ce55e75077f0882c964336d3ec010429eac9218c46a0d682852b4` (110) |
| `Toy.RedGreen.fetch_value_sound_of_any_replay` | result of `every-replay-order-is-value-sound` | `Quot.sound`, `propext` | `852ea791639389c4bf7dd67b87cfc7065d1428d19c32d6b4af29934b7ecdc3e1` | `617467728a5e1febc6b56073eee58b90ef80665aecd2a13c2e66c06bf09f380f` (90) |
| `Toy.RedGreen.fetch_value_sound_nonvacuous` | non-vacuity witness of `every-replay-order-is-value-sound` | `propext` | `93e639f8049e8c768f1ddc47e06e6d27b969c959766921cd7b01d802fc4d1315` | `a485beda9c8f5bcbf6090bec9dadb62b0f0eeea0c5ef57a0647e2c27a19af83a` (115) |
| `Toy.RedGreen.ordered_replay_returns_from_scratch_value_on_dead_dependency` | positive control of `ordered-replay-necessary` | `propext` | `de7ac4f90731c0c34b31fd747985188b26c2f6c3847275931365cf7092519915` | `ba9772e4c4ef684f69ccca69567b005f051c07604d56f07bdcf712557b9a4b1c` (111) |
| `Toy.RedGreen.fp_collision_reexecutes_query_with_unchanged_recorded_dependencies` | result of `fingerprint-collision-breaks-reuse`; counterexample in `early-cutoff-skips-cached-query-with-unchanged-dependencies` | `propext` | `dd3d6ee4a619899fec93b4092c654c88431f85894b26f6f73411a3f865685899` | `a0618256cd44c8cc85e0d8a9c556154f015e04566f593fdd7626bd928dd89799` (132) |
| `Toy.RedGreen.early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps` | result of `early-cutoff-skips-cached-query-with-unchanged-dependencies` | `Quot.sound`, `propext` | `4a16c8a18df3458293afe6c0df0e46cdd490bb9962beab45991aebfffa6ba0d7` | `4a534f2718b726f2c755d185e46baeeadfe6f16728fb14ae4e20f25e8e9dff72` (103) |
| `Toy.RedGreen.no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies` | result of `early-cutoff-skips-cached-query-with-unchanged-dependencies`; counterexample in `early-cutoff-skips-cached-query-with-unchanged-dependencies` | `propext` | `ce93476ffb0db4697fa3612419bffdc5c507a81917156f9a8651192daee3a8b7` | `cc973fbcbd9aa466db3cb3185b9713e6ca54d369502026c504bbf0ea7fa1ae5c` (132) |
| `Toy.RedGreen.early_cutoff_reexecutes_query_whose_value_is_unchanged` | result of `early-cutoff-skips-cached-query-with-unchanged-dependencies`; counterexample in `early-cutoff-skips-cached-query-with-unchanged-dependencies` | `propext` | `9a02ce05b80bfab3b36753a6080e8e0259c53344468c6f587bba28be78d993e8` | `91776b9edceb057e87181f974ad5da068643dce38096d86500f25f357261503c` (132) |
| `Toy.RedGreen.early_cutoff_skips_nonvacuous` | non-vacuity witness of `early-cutoff-skips-cached-query-with-unchanged-dependencies` | `propext` | `941ea74451e6bb5dfcb230f725efe11d293026a8c45ac82348cdd0bef86f7985` | `cc973fbcbd9aa466db3cb3185b9713e6ca54d369502026c504bbf0ea7fa1ae5c` (132) |
| `Toy.RedGreen.stale_db_reexecutes_query_with_unchanged_recorded_dependencies` | counterexample in `early-cutoff-skips-cached-query-with-unchanged-dependencies` | `Quot.sound`, `propext` | `789d6d5a61d50da28885654797ee32ffd650db98a805df8624cc619072bd6e14` | `73a09b565081b71ba7361f4e992ebce13aa5c7bb320acd9102eccb34bf6f0bc7` (133) |
| `Toy.RedGreen.uncached_query_with_unchanged_recorded_dependencies_executes` | counterexample in `early-cutoff-skips-cached-query-with-unchanged-dependencies` | `propext` | `a199fc8a9fa8b00888e523491614d2926af4ec9bf43bb669c486f6a29c9ba55a` | `a8204201b2cdc084580170d870cf9c6e9586da2a0d32641754a283b3a812f8c0` (134) |
| `Toy.RedGreen.unreachable_db_reexecutes_query_with_unchanged_recorded_dependencies` | counterexample in `early-cutoff-skips-cached-query-with-unchanged-dependencies` | `Quot.sound`, `propext` | `334ef438971d877ab704fbdefee52194fbb8b110bcfb6bb945ba0a687a8014eb` | `73a09b565081b71ba7361f4e992ebce13aa5c7bb320acd9102eccb34bf6f0bc7` (133) |

Note on `Classical.choice`: `fetch_eventually_eq_eval_during_revision_of_ordered_replay` and `early_cutoff_agrees_with_reexecution_of_ordered_replay` use `Classical.choice` through the helper `eventually_eq_eval_of_agrees` (a classical case split on whether the key terminates). `fetch_simulation_invariant`, `early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps` and the other results use at most `propext` and `Quot.sound`.

Proof structure of the two longest proofs (recorded for auditability; the kernel check is the evidence). `fetch_simulation_invariant` is proved by recursion on the fuel: `fetch_inv_and_value_sound` (one fetch preserves `Inv` and returns only from-scratch values, for every replay order) gives the first conjunct and the value case; panics and adequacy at equal fuel are proved by simulation lemmas for `Prog.runSt`, `exec` and `checkDeps` with ordered replay, in which each replayed dependency that reproduced its fingerprint has, by injectivity, its recorded value, so the query's code takes the recorded branch in the new state. `early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps` is proved by showing that the predicate "`Inv` holds, `q`'s slot is `old e` or `done e false`, and `q` is not in the log" is preserved by every step of the instrumented algorithm `fetchX` (the replay of `e`'s recorded dependencies never answers `red`, because each fetched dependency value equals its new-state value, whose fingerprint is the recorded one), transported to `fetch` and `execLog` by `fetchX_eq`, and extended to all reachable databases by induction on `Reachable`.

### Primary sources

Each record states what is relied on. Papers were identified by DOI; the three repository revisions were resolved through the GitHub API and the quoted passages were checked against the files at those revisions. Labels are those used in the cards.

* **[S1]** rustc-dev-guide (rust-lang/rustc-dev-guide) at commit d946d7402d269990f3b64baabaf6592409791c11, src/queries/incremental-compilation.md: "it is important that we visit each node in `reads(Q)` in same order as they occurred in the original compilation", and of an out-of-order visit: "it might visit `subquery2` before `subquery1`, and hence execute it. This can lead to ICEs and other problems in the compiler." src/queries/incremental-compilation-in-detail.md at the same commit: "two different results could have the same fingerprint and the system would erroneously assume that the result hasn't changed, leading to a missed update"; the same file states that nodes in the dependency graph "are identified by a fingerprint of the query key". Documentation, prose only.
* **[S2]** rust-lang/rust at commit 5c56312f346d7cc8209d9fc0fd660c72e6fc6950, compiler/rustc_middle/src/dep_graph/graph.rs, fn try_mark_previous_green (called from fn try_mark_green): iterates over the previous session's edge targets of the node in order; a dependency already Green is accepted, a Red dependency ends the attempt (`DepNodeColor::Red => return None`), and a dependency of unknown colour is first recursively tried and otherwise forced (re-executed) and its colour re-read. Colours are per node; the dependent compares no dependency values. Source, prose only.
* **[S3]** salsa-rs/salsa at commit 496752ea3879af8cf3d71d1e28d76447a0cf6482: book/src/plumbing/maybe_changed_after.md (for a derived query, iterate over each dependency and check whether it may have changed; if so re-execute, possibly backdating) and book/src/plumbing/terminology/backdate.md ("*Backdating* is when we mark a value that was computed in revision R as having last changed in some earlier revision", done when the old and new values compare equal: early cutoff by value comparison, with revision stamps). Documentation, prose only.
* **[S4]** A. Mokhov, N. Mitchell, S. Peyton Jones, "Build systems à la carte", Proc. ACM Program. Lang. 2(ICFP), Article 79, pp. 79:1-79:29, 2018, doi:10.1145/3236774. Defines minimality (Def. 2.1, p. 79:3: a build system is minimal if it "executes tasks at most once per build and only if they transitively depend on inputs that changed since the previous build"), correctness (Def. 3.1, p. 79:11), monadic tasks with dynamic dependencies, early cutoff, and verifying and constructive traces; the models are executable Haskell specifications and the paper gives no proofs.
* **[S5]** A. Mokhov, N. Mitchell, S. Peyton Jones, "Build systems à la carte: Theory and practice", J. Funct. Program. 30, e11, 2020, doi:10.1017/S0956796820000088. Extended version of the conference paper; no proofs. Sec. 5.2 states that for monadic tasks the recorded dependencies are known only from previous executions and that, after a common first request, later requests may differ; Sec. 5.2.2 "Verifying step traces" (p. 25) describes Shake's step traces, which have "slightly different early cutoff semantics" from verifying traces, illustrated by Fig. 7 (p. 26): after a change and a revert, verifying traces skip a rebuild that step traces perform. Sec. 8.3 "Impure computations" (pp. 43-44) and Sec. 8.8 "Self-tracking" (p. 48) correspond to Secs. 6.3 and 6.5 of the conference version.
* **[S6]** S. Erdweg, M. Lichter, M. Weiel, "A sound and optimal incremental build system with dynamic dependencies", OOPSLA 2015, pp. 89-106, doi:10.1145/2814270.2814316. Pen-and-paper proofs (Appendix A) of soundness (Thm. 5.3: results are totally consistent and form a well-formed dependency graph) and optimality (Thms. 5.7, 5.8: minimal builder executions and consistency checks) for a build algorithm with dynamically discovered dependencies that checks requirements in their recorded order; the formal algorithm excludes cyclic builds and optimality relies on a stability assumption (Assumption 4.2). Not duplicated here: this package proves no optimality and models demand-driven queries with fingerprint traces rather than file stamps.
* **[S7]** M. A. Hammer, Khoo Yit Phang, M. Hicks, J. S. Foster, "Adapton: composable, demand-driven incremental computation", PLDI 2014, pp. 156-166, doi:10.1145/2594291.2594324 (the second author's name as printed in the paper's byline). Sec. 5: dirty outgoing edges are traversed in the order they were added; at the first inconsistent edge the thunk is re-evaluated and its remaining edges need not be checked, which avoids re-evaluating conditionally forced thunks. Soundness (Thm. 4.3, from-scratch consistency) is proved pen-and-paper for a declarative incremental semantics, not for the traversal algorithm.
* **[S8]** M. Abadi, B. Lampson, J.-J. Lévy, "Analysis and caching of dependencies", ICFP 1996, pp. 83-91, doi:10.1145/232627.232638. Early work on recording the dependencies of functional computations for caching; cited as background, not compared in detail here.
* **[S9]** A. Heydon, R. Levin, Y. Yu, "Caching function calls using precise dependencies", PLDI 2000, pp. 311-320, doi:10.1145/349299.349341. The Vesta build system's functional language caches expensive function calls by recording, in the abstract's words, "precise dependencies that are both dynamic and fine-grained"; dynamic-dependency caching for builds; not compared in detail here.
* **[S10]** N. Mitchell, "Shake before building: replacing make with Haskell", ICFP 2012, pp. 55-66, doi:10.1145/2364527.2364538. Introduces the Shake build system with monadic (dynamic) dependencies and early cutoff; the JFP 2020 version of Build Systems à la Carte (Sec. 5.2.2) attributes Shake's verifying step traces to it.
* **[S11]** G. Konat, S. Erdweg, E. Visser, "Scalable incremental building with dynamic task dependencies", ASE 2018, pp. 76-86, doi:10.1145/3238147.3238196. An incremental build algorithm for dynamic task dependencies, following the OOPSLA 2015 system; not compared in detail here.
* **[S12]** U. A. Acar, "Self-Adjusting Computation", Ph.D. thesis, Carnegie Mellon University, 2005, technical report CMU-CS-05-129. According to its abstract, formalizes change propagation over dynamic dependence graphs and proves it correct; a different model, not compared in detail here.
* **[S13]** U. A. Acar, G. E. Blelloch, R. Harper, "Adaptive functional programming", POPL 2002, pp. 247-259, doi:10.1145/503272.503296. Change propagation over dynamic dependence graphs; cited for context, not compared in detail here.
* **[S14]** U. A. Acar, M. Blume, J. Donham, "A consistent semantics of self-adjusting computation", J. Funct. Program. 23(3):249-292, 2013, doi:10.1017/S0956796813000099. According to its abstract, proves consistency of change propagation with memoization against from-scratch evaluation, with mechanized proofs in Twelf; a different model, not compared in detail here.
* **[S15]** S. Spall, N. Mitchell, S. Tobin-Hochstadt, "Forward build systems, formally", CPP 2022, pp. 130-142, doi:10.1145/3497775.3503687. Agda proofs for forward build systems (Rattle); a different model without demand-driven re-validation of recorded query traces.
* **[S16]** G. Lukyanov, A. Mokhov, "Towards a Coq Formalisation of Build Systems", talk with extended abstract at CoqPL 2019 (workshop co-located with POPL 2019; not an archival publication). Per its abstract, translates the Build Systems à la Carte abstractions to Coq with adjustments for task acyclicity, as ongoing work without completed correctness proofs.
* **[S17]** M. Christakis, K. R. M. Leino, W. Schulte, "Formalizing and verifying a modern build language", FM 2014, LNCS vol. 8442, pp. 643-657, doi:10.1007/978-3-319-06410-9_43. Mechanized formalization and verification of a build language (CloudMake); a different model (no demand-driven re-validation of recorded traces), not compared in detail here.
* **[S18]** A. Mokhov, N. Mitchell, S. Peyton Jones, "Build systems à la carte", Proc. ACM Program. Lang. 2(ICFP), Article 79, 2018, doi:10.1145/3236774, Sec. 6.3 "Impure Computations" (pp. 79:23-79:24) and Sec. 6.5 "Self-tracking" (p. 79:25). Sec. 6.3 separates untracked dependencies ("C compilation will explicitly list the source.c file as a dependency, but it may not record that the version of gcc is also a dependency"), non-determinism (tasks producing a result from a possible set, with an adjusted correctness definition; "Most of the implementations in §5 can deal with non-determinism, apart from Buck") and volatility. Sec. 6.5 describes build systems that recompute a task when the task itself changes. The untracked-change instances here are of the first kind, not of the second.
* **[S19]** salsa-rs/salsa at commit 496752ea3879af8cf3d71d1e28d76447a0cf6482, book/src/cycles.md: "Salsa also supports recovering from query cycles via fixed-point iteration, using `cycle_fn` and `cycle_initial` or explicitly defining a fallback value with `cycle_result`." Documentation; cited for the cycle-recovery boundary only.

## Revalidation

### Full revalidation (recommended)

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

The script never modifies the package: it copies `lean/` to a temporary directory and then

1. runs `lake build` (which also compiles `Toy/RedGreen/Audit.lean`; that module fails the build unless every declaration of the project depends only on `propext`, `Quot.sound`, `Classical.choice`);
2. checks that no Lean source contains `sorry`, `admit`, `native_decide`, or declares an `axiom`;
3. runs a generated Lean program that computes, with Lean's `collectAxioms`, the axioms of every declaration of the library and requires them to be among `propext`, `Classical.choice`, `Quot.sound`;
4. for every Lean name referenced by `results.json` (result names, counterexamples, non-vacuity witnesses, positive controls), recomputes two SHA-256 hashes and compares them with `audit/statements.json`: the **statement hash**, the SHA-256 of Lean's `repr` of the declaration's type; and the **closure hash**, the SHA-256 of the newline-joined, sorted list of entries `name : repr(type)` (followed by ` := repr(value)` for non-theorems) for every package constant reachable from the statement's type through types, definition values and constructors of inductive types (theorem bodies are excluded). A matching closure hash means that neither the statement nor any package definition it depends on has changed. The hashes depend on Lean's `repr` and are therefore specific to the pinned toolchain.

It prints `ok   lake build`, `ok   axioms (… declarations)`, `ok   statement hashes (38 hashed names; 0 referenced names exist but carry no recorded hash)` and finally `REVALIDATED`, and exits with status 0 iff all checks pass.

### Manual commands

```sh
cd lean
lake build                              # prints "AUDIT OK: … declarations checked; all depend only on propext, Quot.sound, Classical.choice."
lake env lean RevalidationAudit.lean    # prints the axioms of each of the 38 declarations referenced by results.json
```

`lean/RevalidationAudit.lean` is outside the library target; it imports `Toy` and issues one `#print axioms` per referenced declaration. The expected axiom sets are those in the **Evidence** table; `audit/axioms.json` records the axioms of every declaration of the library.

### Cheap checks after a change elsewhere

* **New Lean toolchain:** rerun `python3 support/revalidate.py .` after editing `lean/lean-toolchain`; the build and axiom checks are meaningful, but statement and closure hashes may change merely because `repr` output changed, in which case the statements must be compared by reading.
* **Modeling-bridge claims for a newer rustc:** diff `fn try_mark_previous_green` and `fn try_mark_green` in `compiler/rustc_middle/src/dep_graph/graph.rs` against rust-lang/rust `5c56312f346d7cc8209d9fc0fd660c72e6fc6950`; the bridge depends on in-order iteration over previous edges, stopping at the first red dependency, and forcing dependencies of unknown colour. Recheck the two quoted passages of the rustc-dev-guide.
* **Salsa:** recheck `book/src/plumbing/maybe_changed_after.md`, `book/src/plumbing/terminology/backdate.md` and `book/src/cycles.md` against `496752ea3879af8cf3d71d1e28d76447a0cf6482`.

A passing revalidation re-establishes only the kernel checks and hashes; it does not re-examine the modeling-bridge arguments or the citations.
