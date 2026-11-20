import Toy.SepAC.Algebra

/-!
# Syntax Trees, Environments, Denotation, and Right-Nested Normal Forms

Reified syntax trees for separating-conjunction spines, total and list-backed atom
environments, leaf-atom extraction, `Tree.unitCount` / `Tree.unitFree`, and both unital
(`denoteAtoms`) and unit-free (`denoteNonEmpty`) right-nested list-fold normal forms.
-/

namespace Toy.SepAC

universe u

/-- Reified syntax tree of a separating-conjunction spine:
- `atom i` stands for the `i`-th opaque assertion in the environment;
- `unit` stands for a syntactic occurrence of `emp`;
- `node l r` stands for a binary `sep` application `l ∗ r`.

Together with `Tree.denote`, `listEnv`, and `Tree.atoms`, this mirrors the `SepAC.Tree`
normalizer representation of `AeneasVerif/aeneas` PR `#1551` (`Normalize.lean`, lines 20–33
at commit `1d8f9aa0121faca8ff113c1b9b742b333e3e1519`), parameterized over an arbitrary
carrier, binary operator, and unit element `(P, sep, emp)`. -/
inductive Tree where
  | atom (i : Nat)
  | unit
  | node (l r : Tree)
  deriving DecidableEq, Repr

/-- Boolean predicate testing whether a reified `Tree` contains no `Tree.unit` leaves.
Isolates pure associative-commutative rearrangement of `∗` from `emp`-unit elimination. -/
def Tree.unitFree : Tree → Bool
  | .atom _ => true
  | .unit => false
  | .node l r => l.unitFree && r.unitFree

/-- Number of `Tree.unit` leaves in a reified `Tree`. Together with
`l.atoms.isPerm r.atoms = true`, equal unit counts (`l.unitCount = r.unitCount`) is
sufficient for `l.denote sep emp env = r.denote sep emp env` in every associative-commutative
model (`SepAssoc` + `SepComm`, no unit law on `emp`), and is the exact condition when
quantified universally over all associative-commutative models, `emp`, and environments
(though not necessary in a single fixed model where `emp` happens to be a unit). -/
def Tree.unitCount : Tree → Nat
  | .atom _ => 0
  | .unit => 1
  | .node l r => l.unitCount + r.unitCount

/-- `t.unitFree = true` holds if and only if `t` has zero `Tree.unit` leaves. -/
theorem Tree.unitFree_iff_unitCount_eq_zero (t : Tree) :
    t.unitFree = true ↔ t.unitCount = 0 := by
  induction t with
  | atom _ => simp [Tree.unitFree, Tree.unitCount]
  | unit => simp [Tree.unitFree, Tree.unitCount]
  | node l r ihl ihr =>
    simp only [Tree.unitFree, Tree.unitCount, Bool.and_eq_true, Nat.add_eq_zero_iff, ihl, ihr]

/-- Semantic evaluation of a reified `Tree` over carrier `P` with binary operation `sep`,
distinguished element `emp`, and total atom environment `env : Nat → P`. -/
def Tree.denote {P : Type u} (sep : P → P → P) (emp : P) (env : Nat → P) : Tree → P
  | .atom i => env i
  | .unit => emp
  | .node l r => sep (l.denote sep emp env) (r.denote sep emp env)

/-- Environment adapter interpreting a finite `List P` with out-of-bounds fallback `emp`
(`xs.getD i emp`). Bridges finite reification tables to total environments `Nat → P`. -/
def listEnv {P : Type u} (emp : P) (xs : List P) : Nat → P :=
  fun i => xs.getD i emp

/-- Left-to-right list of atom indices appearing in `t`, erasing all `Tree.unit` leaves. -/
def Tree.atoms : Tree → List Nat
  | .atom i => [i]
  | .unit => []
  | .node l r => l.atoms ++ r.atoms

/-- Canonical unital normal-form evaluation: right-nested fold of atom indices terminated
by `emp`, `i₁ ∗ (i₂ ∗ … ∗ (iₖ ∗ emp))`. -/
def denoteAtoms {P : Type u} (sep : P → P → P) (emp : P) (env : Nat → P) (is : List Nat) : P :=
  is.foldr (fun i acc => sep (env i) acc) emp

/-- Canonical unit-free normal-form evaluation for a non-empty atom list `head :: tail`:
right-nested fold `i₁ ∗ (i₂ ∗ … ∗ iₖ)` with no trailing `emp` factor. -/
def denoteNonEmpty {P : Type u} (sep : P → P → P) (env : Nat → P) : Nat → List Nat → P
  | head, [] => env head
  | head, next :: rest => sep (env head) (denoteNonEmpty sep env next rest)

/-! ## Positive and negative examples for syntax, denotation, and normal forms -/

theorem unitFree_pos_example :
    (Tree.node (.atom 0) (.atom 1)).unitFree = true := rfl

theorem unitFree_neg_example :
    (Tree.node (.atom 0) .unit).unitFree = false := rfl

theorem unitCount_pos_example :
    (Tree.node (.node (.atom 0) .unit) .unit).unitCount = 2 := rfl

theorem unitCount_neg_example :
    (Tree.node (.atom 0) .unit).unitCount ≠ 0 := by decide

theorem denote_pos_example :
    (Tree.node (.node (.atom 0) .unit) (.atom 1)).denote Nat.add 0 (fun i => i + 10) = 21 := rfl

theorem denote_neg_example :
    (Tree.node (.atom 0) (.atom 1)).denote (@List.append Nat) [] (fun i => [i]) ≠
      (Tree.node (.atom 1) (.atom 0)).denote (@List.append Nat) [] (fun i => [i]) := by
  decide

theorem listEnv_pos_example :
    listEnv 0 [10, 20, 30] 1 = 20 := rfl

theorem listEnv_neg_example :
    listEnv 0 [10, 20] 5 ≠ 10 := by decide

theorem atoms_pos_example :
    (Tree.node (.node (.atom 2) .unit) (.atom 0)).atoms = [2, 0] := rfl

theorem atoms_neg_example :
    Tree.unit.atoms ≠ [0] := by decide

theorem denoteAtoms_pos_example :
    denoteAtoms Nat.add 0 (fun i => i + 1) [0, 1, 2] = 6 := rfl

theorem denoteAtoms_neg_example :
    denoteAtoms Bool.and false (fun _ => true) [0] ≠ true := by decide

theorem denoteNonEmpty_pos_example :
    denoteNonEmpty Nat.add (fun i => i + 1) 0 [1, 2] = 6 := rfl

theorem denoteNonEmpty_neg_example :
    denoteNonEmpty (@List.append Nat) (fun i => [i]) 0 [1] ≠ [1, 0] := by decide

end Toy.SepAC
