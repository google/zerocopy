import ToyMonitor.Basic

/-!
# Footprint strategies: computational interpretations of assertions

A *strategy* is the monitor's computational interpretation of contracts: given a
contract and the heap fragment the current frame owns, it either fails or returns
the list of addresses whose ownership is to be transferred.

A strategy sees only the contract and the current fragment; it cannot see the code
that will run afterwards. This is what makes a monitor *online*.
-/

namespace Toy.Monitor

/-- A footprint strategy: contract ↦ owned fragment ↦ footprint (or failure). -/
abbrev Strategy := Assn → Heap → Option (List Addr)

/-- A strategy is sound when every footprint it returns is a genuine footprint. -/
def StrategySound (s : Strategy) : Prop :=
  ∀ A g F, s A g = some F → IsFootprint A g F

/-- Witness recovery: whenever *some* sub-fragment `g'` of `g` satisfies `A`, the
strategy's single answer `s A g` is a footprint (of allocated addresses of `g`) that
carves out exactly that `g'`. Because `s A g` cannot depend on `g'`, this is a
uniqueness-including notion of completeness: if `A` has two different witnesses inside
one `g`, no strategy recovers both (`precise_of_recoversEveryWitness`). It is the notion
a whole-run completeness argument needs: the monitor must hand the callee exactly the
fragment the callee was statically given. It is strictly stronger than
`ExistsFootprintComplete` (finding *some* footprint whenever one exists), which the
backtracking strategy satisfies for every assertion, precise or not. -/
def RecoversEveryWitness (s : Strategy) (A : Assn) : Prop :=
  ∀ g g', Heap.Sub g' g → sat A g' →
    ∃ F, s A g = some F ∧ (∀ a ∈ F, (g a).isSome = true) ∧ g.restrict F = g'

/-- Existential footprint completeness: whenever some sub-fragment of `g` satisfies `A`,
the strategy returns *some* genuine footprint of `A` in `g` (not necessarily the one the
caller had in mind). -/
def ExistsFootprintComplete (s : Strategy) (A : Assn) : Prop :=
  ∀ g g', Heap.Sub g' g → sat A g' → ∃ F, s A g = some F ∧ IsFootprint A g F

/-- Greedy, consumption-style footprint computation:
`cell` reads the byte; `sep A B` computes `A`'s footprint, removes it, and computes
`B`'s footprint in the remainder (so the two parts are disjoint by construction);
`or A B` commits to `A` if `A` succeeds and otherwise tries `B` (no backtracking
into a disjunct once it has succeeded). -/
def fpGreedy : Assn → Heap → Option (List Addr)
  | .cell p P, g =>
    match g p with
    | some v => if P v then some [p] else none
    | none => none
  | .pure b, _ => if b then some [] else none
  | .sep A B, g =>
    match fpGreedy A g with
    | none => none
    | some F₁ =>
      match fpGreedy B (g.remove F₁) with
      | none => none
      | some F₂ => some (F₁ ++ F₂)
  | .or A B, g =>
    match fpGreedy A g with
    | some F => some F
    | none => fpGreedy B g

/-- The same as `fpGreedy` but with right-biased disjunction (tries `B` first). -/
def fpGreedyR : Assn → Heap → Option (List Addr)
  | .cell p P, g =>
    match g p with
    | some v => if P v then some [p] else none
    | none => none
  | .pure b, _ => if b then some [] else none
  | .sep A B, g =>
    match fpGreedyR A g with
    | none => none
    | some F₁ =>
      match fpGreedyR B (g.remove F₁) with
      | none => none
      | some F₂ => some (F₁ ++ F₂)
  | .or A B, g =>
    match fpGreedyR B g with
    | some F => some F
    | none => fpGreedyR A g

/-- All consumption-style footprints (exhaustive search with backtracking). -/
def fpAll : Assn → Heap → List (List Addr)
  | .cell p P, g =>
    match g p with
    | some v => if P v then [[p]] else []
    | none => []
  | .pure b, _ => if b then [[]] else []
  | .sep A B, g =>
    (fpAll A g).flatMap (fun F₁ => (fpAll B (g.remove F₁)).map (fun F₂ => F₁ ++ F₂))
  | .or A B, g => fpAll A g ++ fpAll B g

/-- Backtracking strategy: the first footprint found by exhaustive search. -/
def fpSearch : Strategy := fun A g => (fpAll A g).head?

/-- A strategy that handles only atomic contracts (`cell`, `pure`) and fails on
`sep` / `or`. Used for fully proved concrete instances. -/
def fpAtom : Assn → Heap → Option (List Addr)
  | .cell p P, g =>
    match g p with
    | some v => if P v then some [p] else none
    | none => none
  | .pure b, _ => if b then some [] else none
  | .sep _ _, _ => none
  | .or _ _, _ => none

end Toy.Monitor
