/-
Toy.SCT.Check
=============

The decision procedure: compute the composition closure of the call-site graphs by fixpoint
iteration on a finite list, then test every idempotent loop for a strict self-arc.
-/
import Toy.SCT.Graph

namespace Toy.SCT

variable {nf k : Nat}

/-- Append `x` to `l` unless it already occurs. -/
def addNew {α : Type} [DecidableEq α] (x : α) (l : List α) : List α :=
  if x ∈ l then l else l ++ [x]

/-- The call-site graphs without duplicates (first occurrences, in order). -/
def dedupGraphs (l : List (SCG nf k)) : List (SCG nf k) :=
  l.foldl (fun acc G => addNew G acc) []

/-- One iteration step of closure computation: `S` together with every composite `G ; H` of graphs
`G, H ∈ S` with `G.dst = H.src` (no duplicates are added). -/
def closureStep (S : List (SCG nf k)) : List (SCG nf k) :=
  S.foldl (fun acc G => S.foldl (fun acc' H => if G.dst = H.src then addNew (G.comp H) acc' else acc')
    acc) S

/-- Fixpoint iteration with fuel: `some S` as soon as one iteration step adds nothing new to `S`, and `none`
if the fuel runs out first. -/
def closureIter : Nat → List (SCG nf k) → Option (List (SCG nf k))
  | 0, _ => none
  | n + 1, S =>
    if (closureStep S).all (fun G => decide (G ∈ S)) then some S else closureIter n (closureStep S)

/-- Fuel for the fixpoint iteration: one more than the number `nf * nf * 3 ^ (k * k)` of distinct
size-change graphs (a source, a target, and one of three labels per arc). -/
def closureFuel (nf k : Nat) : Nat := nf * nf * 3 ^ (k * k) + 1

/-- The idempotent-loop test on one graph: if `G` is a loop and `G ; G = G`, then `G` has a strict
self-arc. -/
def idemTest (G : SCG nf k) : Bool :=
  !(decide (G.src = G.dst) && decide (G.comp G = G)) || decide G.HasStrictSelfArc

/-- **The size-change checker.** Compute the closure of the program's call-site graphs by fixpoint
iteration (with fuel `closureFuel nf k`), and accept iff the iteration reached a fixpoint and every
graph of the closure passes `idemTest`. Running out of fuel means rejection. -/
def checkSCT (P : Prog nf k) : Bool :=
  match closureIter (closureFuel nf k) (dedupGraphs P.calls) with
  | none => false
  | some S => S.all idemTest

end Toy.SCT
