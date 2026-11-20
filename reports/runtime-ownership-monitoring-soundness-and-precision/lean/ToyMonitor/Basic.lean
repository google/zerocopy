/-!
# Heaps, ownership assertions, and their static (separation-logic) meaning

A toy byte-addressed heap and a small assertion language in the style of the
ownership contracts used by separation-logic specification languages:
points-to / ownership atoms, pure conditions, separating conjunction, and
(general, possibly imprecise) disjunction.

The semantics is *exact* (linear, non-intuitionistic): an assertion describes a
heap fragment completely, so `owned p` holds of a fragment containing exactly one
cell, at `p`.
-/

namespace Toy.Monitor

/-- Addresses. One address stands for one byte. -/
abbrev Addr := Nat

/-- Byte values. -/
abbrev Val := Nat

/-- A heap, or a heap fragment: a partial map from addresses to values
(`none` = the address is not part of the fragment / not allocated). -/
abbrev Heap := Addr → Option Val

namespace Heap

/-- The empty fragment. -/
def empty : Heap := fun _ => none

/-- The one-cell fragment `p ↦ v`. -/
def single (p : Addr) (v : Val) : Heap := fun a => if a = p then some v else none

/-- Two fragments have disjoint domains. -/
def Disjoint (g₁ g₂ : Heap) : Prop := ∀ a, g₁ a = none ∨ g₂ a = none

/-- Union of fragments (left-biased; only used on disjoint fragments). -/
def union (g₁ g₂ : Heap) : Heap := fun a =>
  match g₁ a with
  | some v => some v
  | none => g₂ a

/-- `Sub g₁ g`: `g₁` is a sub-fragment of `g` (every cell of `g₁` is a cell of `g`,
with the same value). -/
def Sub (g₁ g : Heap) : Prop := ∀ a v, g₁ a = some v → g a = some v

/-- Restriction of `g` to the addresses listed in `F`. -/
def restrict (g : Heap) (F : List Addr) : Heap := fun a => if a ∈ F then g a else none

/-- `g` with the addresses listed in `F` removed. -/
def remove (g : Heap) (F : List Addr) : Heap := fun a => if a ∈ F then none else g a

/-- Domain-preserving store: overwrite the value at an allocated address `a`;
a store to an unallocated address leaves the heap unchanged. -/
def write (h : Heap) (a : Addr) (v : Val) : Heap := fun b =>
  if b = a then (match h a with
                 | some _ => some v
                 | none => none)
  else h b

end Heap

/-- Contract assertions.

* `cell p P` — ownership of the single byte at `p`, whose current value satisfies
  the (pure, decidable) predicate `P`. `owned p` and `pointsTo p v` are instances.
* `pure b` — a pure condition, holding of the empty fragment iff `b` holds.
* `sep A B` — separating conjunction.
* `or A B` — disjunction (in general imprecise). -/
inductive Assn where
  | cell (p : Addr) (P : Val → Bool)
  | pure (b : Bool)
  | sep (A B : Assn)
  | or (A B : Assn)

/-- `owned p`: ownership of the byte at `p`, any value. -/
def Assn.owned (p : Addr) : Assn := .cell p (fun _ => true)

/-- `pointsTo p v`: ownership of the byte at `p`, holding `v`. -/
def Assn.pointsTo (p : Addr) (v : Val) : Assn := .cell p (fun w => w == v)

/-- The empty-heap assertion. -/
def Assn.emp : Assn := .pure true

/-- Static meaning of assertions: `sat A g` says the fragment `g` satisfies `A`
(exact separation-logic semantics; the separating conjunction quantifies over all
splittings of `g` into two disjoint fragments). -/
def sat : Assn → Heap → Prop
  | .cell p P, g => ∃ v, g p = some v ∧ P v = true ∧ ∀ a, a ≠ p → g a = none
  | .pure b, g => b = true ∧ ∀ a, g a = none
  | .sep A B, g => ∃ g₁ g₂, Heap.Disjoint g₁ g₂ ∧ (∀ a, g a = Heap.union g₁ g₂ a) ∧
      sat A g₁ ∧ sat B g₂
  | .or A B, g => sat A g ∨ sat B g

/-- Separating conjunction of arbitrary heap predicates: `g` splits into disjoint
fragments satisfying `P` and `R` respectively. -/
def SepP (P R : Heap → Prop) (g : Heap) : Prop :=
  ∃ g₁ g₂, Heap.Disjoint g₁ g₂ ∧ (∀ a, g a = Heap.union g₁ g₂ a) ∧ P g₁ ∧ R g₂

/-- `IsFootprint A g F`: the address list `F` is a footprint of `A` inside the
fragment `g` — every listed address is allocated in `g`, and the restriction of `g`
to `F` satisfies `A`. This is what a run-time monitor must compute when it
transfers ownership for a contract `A` out of the fragment `g`. -/
def IsFootprint (A : Assn) (g : Heap) (F : List Addr) : Prop :=
  (∀ a ∈ F, (g a).isSome = true) ∧ sat A (g.restrict F)

/-- Precision (O'Hearn–Yang–Reynolds): in every heap there is at most one
sub-fragment satisfying `A`. -/
def Precise (A : Assn) : Prop :=
  ∀ g g₁ g₂, Heap.Sub g₁ g → Heap.Sub g₂ g → sat A g₁ → sat A g₂ → g₁ = g₂

/-- Disjunction-precision: every disjunction occurring in `A` is precise.
(Atoms are always precise and `sep` preserves precision, so this is equivalent to
every sub-assertion of `A` being precise.) It is a sufficient condition for the
greedy footprint computation `fpGreedy` to recover every witness
(`RecoversEveryWitness`), not a necessary one: `fpGreedy` is order-sensitive on
disjunctions, and it recovers every witness of the precise assertion `CFlip`, which
is not `DisjPrecise` (`fpGreedy_recoversEveryWitness_CFlip_not_disjPrecise`). -/
def DisjPrecise : Assn → Prop
  | .cell _ _ => True
  | .pure _ => True
  | .sep A B => DisjPrecise A ∧ DisjPrecise B
  | .or A B => Precise (.or A B) ∧ DisjPrecise A ∧ DisjPrecise B

end Toy.Monitor
