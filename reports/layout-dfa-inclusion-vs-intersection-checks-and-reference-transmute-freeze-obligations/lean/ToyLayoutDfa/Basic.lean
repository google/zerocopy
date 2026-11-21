/-!
# Layout automata over a 257-symbol byte alphabet, and two product explorations

This module fixes the vocabulary of the package (namespace `Toy.LayoutDfa`).

* `Sym` is the alphabet of abstract bytes: the 256 initialised byte values plus one
  symbol `uninit` for an uninitialised byte (257 symbols in total).
* A `Layout` is a finite automaton over `Sym`: natural-number states, a start state, one
  accept state, and a list of labelled edges. It is meant to capture the representation
  of a fixed-size type's bit validity as an automaton whose accepted words are exactly the
  valid byte strings of the type (an initialised position contributes the byte values it
  admits; a position that may be uninitialised also has an `uninit` edge).
* Two divergences from textbook automata and from the rustc encoding are deliberate and
  are stated here once. (1) A `Layout` is a *partial* automaton (a state may lack an edge
  for a symbol) with a *single terminal* accept state: a run stops when it reaches the
  accept state, and edges out of the accept state are never followed (`Path`). Textbook
  DFAs have a total transition function and a set of non-terminal accept states.
  (2) Nothing forces initialisation monotonicity: a state may have an `uninit` edge
  without edges for the 256 byte values (rustc's uninit byte range covers every value).
* Automata are not deterministic, acyclic or fixed-size by construction; these are
  separate named properties (`Deterministic`, `Acyclic`, `ReachableLiveAcyclic`, `FixedSize`,
  `ReachableLive`) so
  that every theorem names exactly the ones it uses.
* `forallCheck A B` and `existsCheck A B` are product explorations of a source automaton
  `A` and a destination automaton `B`. Both stop with success when the destination reaches
  its accept state (truncation), follow an `uninit` edge of the destination when the source
  has reached its accept state (extension), and otherwise compare edges with equal labels:
  `forallCheck` requires a matching destination edge for *every* source edge, `existsCheck`
  for *some* source edge. Both are pure recursive functions of a state pair and a step
  budget (`fuel`); no memo table is modelled. The budget `fuelFor B` counts the entries of
  the edge list of `B`, duplicates and unreachable edges included.
* Degenerate sizes: `FixedSize 0` holds exactly for automata whose language is `{[]}` or
  empty, and `fit 0 s = []` discards the whole source word.
-/

namespace Toy.LayoutDfa

/-- The abstract-byte alphabet: an initialised byte value `byte b` (`b : Fin 256`) or
the uninitialised byte `uninit`. 257 symbols in total. -/
inductive Sym where
  | byte (b : Fin 256)
  | uninit
  deriving DecidableEq, Repr

/-- A layout automaton: natural-number states, a start state, one accept state and a
finite list of edges `(source, label, target)`. Meant to capture a type's bit-validity
automaton (one state per byte offset and branch; the accepted words are the valid byte
strings). Nothing here forces determinism, acyclicity or a fixed word length. -/
structure Layout where
  start : Nat
  accept : Nat
  edges : List (Nat × Sym × Nat)
  deriving Repr

namespace Layout

/-- The edges leaving state `q`, as `(label, target)` pairs, in list order. -/
def out (A : Layout) (q : Nat) : List (Sym × Nat) :=
  A.edges.filterMap (fun e => if e.1 = q then some (e.2.1, e.2.2) else none)

/-- `Path A q w r`: reading the word `w` from state `q` can end in state `r`, where no
step leaves the accept state (the accept state is terminal: a run stops there). -/
inductive Path (A : Layout) : Nat → List Sym → Nat → Prop
  | nil (q : Nat) : Path A q [] q
  | cons {q : Nat} {a : Sym} {q' : Nat} {w : List Sym} {r : Nat} :
      q ≠ A.accept → (q, a, q') ∈ A.edges → Path A q' w r → Path A q (a :: w) r

/-- `Accepts A q w`: some run on `w` from `q` ends in the accept state. -/
def Accepts (A : Layout) (q : Nat) (w : List Sym) : Prop :=
  A.Path q w A.accept

/-- The language of `A`: the words accepted from the start state. Meant to capture the
set of valid byte strings of the type that `A` represents. -/
def Lang (A : Layout) (w : List Sym) : Prop :=
  A.Accepts A.start w

/-- Determinism: from every state, reachable or not (including the accept state), at most
one target per label. Meant to capture the "D" in DFA (edge labels out of a state are
pairwise distinct or lead to the same state). -/
def Deterministic (A : Layout) : Prop :=
  ∀ e₁ ∈ A.edges, ∀ e₂ ∈ A.edges, e₁.1 = e₂.1 → e₁.2.1 = e₂.2.1 → e₁.2.2 = e₂.2.2

/-- Fixed size `n`: every accepted word has length exactly `n`. Meant to capture
"the type has size `n`". An automaton with empty language is `FixedSize n` for every `n`;
`FixedSize 0` holds exactly when the language is `{[]}` or empty. -/
def FixedSize (A : Layout) (n : Nat) : Prop :=
  ∀ w, A.Lang w → w.length = n

/-- Every state reachable from the start (by a run that does not leave the accept state),
the start state itself included, can still reach the accept state. Meant to capture "the
automaton has no dead branches reachable from its start" (the reachable part is
co-reachable). Because the start state is reachable by the empty run, this also requires
the language to be non-empty (`inhabited_of_reachableLive`): an uninhabited automaton such
as `⟨0, 1, []⟩` is not `ReachableLive`. -/
def ReachableLive (A : Layout) : Prop :=
  ∀ w q, A.Path A.start w q → ∃ v, A.Accepts q v

/-- No non-empty run from any state, reachable or unreachable, live or dead, returns to the
state it started from. Meant to capture "the layout has no loops"; runs never leave the
accept state, so this constrains cycles through non-accept states only. Neither implied by
nor implying `FixedSize` (`fixedSize_acyclic_incomparable`). -/
def Acyclic (A : Layout) : Prop :=
  ∀ q w, w ≠ [] → ¬ A.Path q w q

/-- No non-empty run returns to a state `p` that is reachable from the start state and from
which the accept state is reachable (a state of the reachable live part). Cycles through
unreachable states, or through reachable states that cannot reach the accept state, are
allowed. Implied by `Acyclic` (`reachableLiveAcyclic_of_acyclic`) and by `FixedSize`
(`reachableLiveAcyclic_of_fixedSize`), and strictly weaker than each
(`reachableLiveAcyclic_strictly_weaker_than_both`). -/
def ReachableLiveAcyclic (A : Layout) : Prop :=
  ∀ (pre : List Sym) (p : Nat) (c v : List Sym), c ≠ [] →
    A.Path A.start pre p → A.Path p c p → A.Accepts p v → False

/-- Determinism restricted to states that are reachable from the start state and are not
the accept state (the only states whose out-edges a run or a check ever follows). Weaker
than `Deterministic`, which constrains every state, reachable or not, including the
out-edges of the accept state. -/
def ReachableDeterministic (A : Layout) : Prop :=
  ∀ w q, A.Path A.start w q → q ≠ A.accept →
    ∀ e₁ ∈ A.edges, ∀ e₂ ∈ A.edges, e₁.1 = q → e₂.1 = q → e₁.2.1 = e₂.2.1 → e₁.2.2 = e₂.2.2

end Layout

open Layout

/-- The step budget used by both checks: one more than the length of the destination's
edge list. Every recursive step of either check traverses one destination edge. The count
is of list entries, so duplicate and unreachable edges enlarge the budget; on cyclic
destinations the checks' answers can therefore depend on the representation of the edge
list (`checks_depend_on_edge_list_representation`). -/
def fuelFor (B : Layout) : Nat := B.edges.length + 1

/-- The universal product exploration with step budget `fuel`, at source state `qa` and
destination state `qb`:
* budget exhausted: `false`;
* destination at its accept state: `true` (truncation);
* source at its accept state: `true` iff some `uninit` edge out of `qb` leads to success
  (extension);
* otherwise: for every edge `(s, qa')` out of `qa` there is an edge `(t, qb')` out of `qb`
  with `t = s` from which the exploration succeeds. -/
def forallAux (A B : Layout) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, qa, qb =>
    if qb = B.accept then true
    else if qa = A.accept then
      (B.out qb).any (fun p => p.1 == Sym.uninit && forallAux A B fuel qa p.2)
    else
      (A.out qa).all (fun p =>
        (B.out qb).any (fun r => r.1 == p.1 && forallAux A B fuel p.2 r.2))

/-- The universal check: `forallAux` from the two start states with budget `fuelFor B`.
Meant to capture a transmutability check run *without* a programmer validity promise. -/
def forallCheck (A B : Layout) : Bool :=
  forallAux A B (fuelFor B) A.start B.start

/-- The existential product exploration: identical to `forallAux` except that in the last
case *some* edge out of `qa` (rather than every edge) must have a matching edge out of `qb`
from which the exploration succeeds. -/
def existsAux (A B : Layout) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, qa, qb =>
    if qb = B.accept then true
    else if qa = A.accept then
      (B.out qb).any (fun p => p.1 == Sym.uninit && existsAux A B fuel qa p.2)
    else
      (A.out qa).any (fun p =>
        (B.out qb).any (fun r => r.1 == p.1 && existsAux A B fuel p.2 r.2))

/-- The existential check: `existsAux` from the two start states with budget `fuelFor B`.
Meant to capture a transmutability check run *with* a programmer validity promise. -/
def existsCheck (A B : Layout) : Bool :=
  existsAux A B (fuelFor B) A.start B.start

/-- The destination-size view of a source byte string `s`: its first `n` symbols, padded
with `uninit` up to length `n` when `s` is shorter. Uses truncated subtraction
`n - s.length` (zero when `s` is at least `n` long). Meant to capture a union-style
transmute into an `n`-byte destination: truncation drops trailing source bytes, extension
fills trailing destination bytes with uninitialised bytes. -/
def fit (n : Nat) (s : List Sym) : List Sym :=
  s.take n ++ List.replicate (n - s.length) Sym.uninit

/-- Language inclusion `L(A) ⊆ L(B)`. -/
def Subset (A B : Layout) : Prop :=
  ∀ s, A.Lang s → B.Lang s

/-- Non-empty intersection `L(A) ∩ L(B) ≠ ∅`. -/
def Meets (A B : Layout) : Prop :=
  ∃ s, A.Lang s ∧ B.Lang s

/-- Every valid source string, viewed at destination size `n` (`fit n`), is a valid
destination string. Meant to capture soundness of an unconditional union-style value
transmute from the type of `A` into an `n`-byte type with automaton `B`. -/
def FitSubset (A B : Layout) (n : Nat) : Prop :=
  ∀ s, A.Lang s → B.Lang (fit n s)

/-- Some valid source string, viewed at destination size `n` (`fit n`), is a valid
destination string. Meant to capture satisfiability of a programmer validity promise
("this particular source value is valid at the destination") for the given pair. -/
def FitMeets (A B : Layout) (n : Nat) : Prop :=
  ∃ s, A.Lang s ∧ B.Lang (fit n s)

end Toy.LayoutDfa
