/-
Toy.RedGreen.Basic
==================

A generic toy model of demand-driven query memoization with red-green
re-validation and early cutoff.

* Keys are query keys `Q` or input keys `I` (`Key Q I := Q ⊕ I`).
* A query's code is a `Prog`: a tree of `fetch k (fun v => ...)` nodes ending in
  `ret v` or `panic`.  Which keys it fetches may depend on fetched values
  (dynamic dependencies).
* `eval` is fuel-indexed from-scratch evaluation.
* A database entry records the ordered list of `(dependency, fingerprint)` pairs
  a query fetched in a previous input state, and its result.
* `fetch` is the incremental, demand-driven fetch.  For a query with an entry
  from the previous state it replays the recorded dependencies (`markGreen`);
  if all are unchanged the old result is reused ("green"), otherwise the query
  is re-executed ("red").  With early cutoff, a dependency counts as unchanged
  when its current fingerprint equals the recorded one, even if it was
  re-executed.

Traces are per edge: an entry stores, for each dependency in fetch order, the
fingerprint of the value fetched, and validation fetches the dependency's
current value and compares fingerprints.  This is the verifying-trace scheme
of Build Systems à la Carte; it differs from systems that propagate value-free
node colours (rustc) or compare revision stamps (Salsa, Shake's step traces).

No Mathlib; only core Lean.
-/

namespace Toy.RedGreen

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

end Toy.RedGreen
