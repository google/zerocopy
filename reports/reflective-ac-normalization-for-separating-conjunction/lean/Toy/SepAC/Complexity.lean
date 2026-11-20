import Toy.SepAC.Entailment

/-!
# Decidability, Tree Size Bounds, and Quasilinear Merge-Sort Permutation Check

Core Lean `v4.34.1` provides `List.Perm` and `List.isPerm` in `Init.Data.List.Basic`
(with `List.isPerm_iff` in `Init.Data.List.Perm`), implemented structurally via
`l₂.contains a && l₁.isPerm (l₂.erase a)` ($O(m^2)$ comparisons on $m$ atoms), while
`Tree.atoms` uses `List.append` ($O(|t|^2)$ cons steps on left-nested spines).

This module defines:
- `Tree.size` and `Tree.atomCount`,
- linear-traversal accumulator extraction `Tree.atomsAcc` / `Tree.atomsFast` (avoiding `++`),
- merge-sort permutation decision `checkPermSort` ($O(|t|)$ extraction followed by
  $O(m \log m)$ `List.mergeSort` with $m = \text{atomCount} \le \text{size}$),

and proves in full (using standard axioms only) that `checkPermSort` computes the exact same boolean as
`l.atoms.isPerm r.atoms` and satisfies `atomsFast.length = atomCount ≤ size`.

Note on Lean `v4.34.1` kernel reduction: core `List.mergeSort` (`Init.Data.List.Sort.Basic`)
is defined by well-founded recursion (`termination_by xs => xs.length`) and replaced at
runtime by a tail-recursive implementation via the `@[csimp]` theorem
`List.mergeSort_eq_mergeSortTR₂` (`Init.Data.List.Sort.Impl`). On the instances probed by
`support/KernelReductionProbe.lean`, the kernel does not reduce `checkPermSort l r` to `true`
(so `Eq.refl true` does not prove it), whereas the probed structurally recursive
`List.isPerm` and core `Lean.Data.AC.sort` (insertion sort) instances do reduce.
-/

namespace Toy.SepAC

/-- Total constructor count of a syntax tree `t` (`atom`, `unit`, and `node` each count `1`). -/
def Tree.size : Tree → Nat
  | .atom _ => 1
  | .unit => 1
  | .node l r => 1 + l.size + r.size

/-- Number of `Tree.atom` leaves in `t` (`Tree.unit` contributes `0`). -/
def Tree.atomCount : Tree → Nat
  | .atom _ => 1
  | .unit => 0
  | .node l r => l.atomCount + r.atomCount

/-- Difference-list / accumulator traversal extracting leaf atom indices without
intermediate `List.append` allocations. -/
def Tree.atomsAcc : Tree → List Nat → List Nat
  | .atom i, acc => i :: acc
  | .unit, acc => acc
  | .node l r, acc => l.atomsAcc (r.atomsAcc acc)

/-- Accumulator-based atom extraction `t.atomsAcc []` (visiting each `Tree` constructor once). -/
def Tree.atomsFast (t : Tree) : List Nat :=
  t.atomsAcc []

/-- Boolean permutation check sorting both accumulator-extracted atom lists with core
Lean's `List.mergeSort (· ≤ ·)` and testing structural list equality. -/
def checkPermSort (l r : Tree) : Bool :=
  (l.atomsFast.mergeSort (· ≤ ·)) == (r.atomsFast.mergeSort (· ≤ ·))

/-! ## Positive and negative examples for size and fast permutation definitions -/

theorem treeSize_pos_example :
    (Tree.node (.atom 0) .unit).size = 3 := rfl

theorem treeSize_neg_example :
    Tree.unit.size ≠ 0 := by decide

theorem atomCount_pos_example :
    (Tree.node (.atom 0) (.node .unit (.atom 2))).atomCount = 2 := rfl

theorem atomCount_neg_example :
    Tree.unit.atomCount ≠ 1 := by decide

theorem atomsAcc_pos_example :
    (Tree.node (.atom 0) (.atom 1)).atomsAcc [9] = [0, 1, 9] := rfl

theorem atomsAcc_neg_example :
    Tree.unit.atomsAcc [9] ≠ [] := by decide

theorem atomsFast_pos_example :
    (Tree.node (.node (.atom 3) .unit) (.atom 1)).atomsFast = [3, 1] := rfl

theorem atomsFast_neg_example :
    (Tree.node (.atom 0) (.atom 1)).atomsFast ≠ [1, 0] := by decide

/-! ## Structural lemmas and Result 5 (fully proved) -/

theorem atomsAcc_eq_atoms_append (t : Tree) (acc : List Nat) :
    t.atomsAcc acc = t.atoms ++ acc := by
  induction t generalizing acc with
  | atom i => rfl
  | unit => rfl
  | node l r ihl ihr =>
    simp [Tree.atomsAcc, Tree.atoms, ihl, ihr, List.append_assoc]

theorem atomsFast_eq_atoms (t : Tree) :
    t.atomsFast = t.atoms := by
  unfold Tree.atomsFast
  rw [atomsAcc_eq_atoms_append, List.append_nil]

theorem atoms_length_eq_atomCount (t : Tree) :
    t.atoms.length = t.atomCount := by
  induction t with
  | atom _ => rfl
  | unit => rfl
  | node l r ihl ihr =>
    simp [Tree.atoms, Tree.atomCount, ihl, ihr]

theorem atomCount_le_size (t : Tree) :
    t.atomCount ≤ t.size := by
  induction t with
  | atom _ => exact Nat.le_refl 1
  | unit => exact Nat.zero_le 1
  | node l r ihl ihr =>
    unfold Tree.atomCount Tree.size
    omega

/-- Merge-sort equality on `List Nat` coincides with `List.isPerm`. -/
theorem mergeSort_beq_eq_isPerm (xs ys : List Nat) :
    ((xs.mergeSort (· ≤ ·)) == (ys.mergeSort (· ≤ ·))) = xs.isPerm ys := by
  have hTrans : ∀ a b c : Nat, decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    omega
  have hTotal : ∀ a b : Nat, (decide (a ≤ b) || decide (b ≤ a)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  have hAnti : ∀ a b : Nat, a ∈ xs.mergeSort (· ≤ ·) → b ∈ ys.mergeSort (· ≤ ·) →
      decide (a ≤ b) = true → decide (b ≤ a) = true → a = b := by
    intro a b _ _ hab hba
    simp only [decide_eq_true_eq] at *
    omega
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, List.isPerm_iff]
  constructor
  · intro hSortEq
    have hp₁ : (xs.mergeSort (· ≤ ·)).Perm xs := List.mergeSort_perm xs (· ≤ ·)
    have hp₂ : (ys.mergeSort (· ≤ ·)).Perm ys := List.mergeSort_perm ys (· ≤ ·)
    exact hp₁.symm.trans (hSortEq ▸ hp₂)
  · intro hPerm
    have hp₁ : (xs.mergeSort (· ≤ ·)).Perm xs := List.mergeSort_perm xs (· ≤ ·)
    have hp₂ : (ys.mergeSort (· ≤ ·)).Perm ys := List.mergeSort_perm ys (· ≤ ·)
    have hSortPerm : (xs.mergeSort (· ≤ ·)).Perm (ys.mergeSort (· ≤ ·)) :=
      hp₁.trans (hPerm.trans hp₂.symm)
    exact List.Perm.eq_of_pairwise hAnti
      (List.pairwise_mergeSort hTrans hTotal xs)
      (List.pairwise_mergeSort hTrans hTotal ys)
      hSortPerm

/-- **Result 5: Quasilinear merge-sort check equivalence and linear atom-count bounds.**
For every pair of trees `l, r : Tree`, `checkPermSort l r` computes the exact same
`Bool` as `l.atoms.isPerm r.atoms`, accumulator extraction `atomsFast` equals `atoms`,
and the extracted list length equals `atomCount` and is bounded by `Tree.size`. -/
theorem checkPermSort_eq_isPerm_and_size_bounds (l r : Tree) :
    checkPermSort l r = l.atoms.isPerm r.atoms ∧
    l.atomsFast = l.atoms ∧
    r.atomsFast = r.atoms ∧
    l.atomsFast.length = l.atomCount ∧
    l.atomCount ≤ l.size ∧
    r.atomsFast.length = r.atomCount ∧
    r.atomCount ≤ r.size := by
  have hfl : l.atomsFast = l.atoms := atomsFast_eq_atoms l
  have hfr : r.atomsFast = r.atoms := atomsFast_eq_atoms r
  refine ⟨?_, hfl, hfr, ?_, atomCount_le_size l, ?_, atomCount_le_size r⟩
  · unfold checkPermSort
    rw [hfl, hfr]
    exact mergeSort_beq_eq_isPerm l.atoms r.atoms
  · rw [hfl, atoms_length_eq_atomCount]
  · rw [hfr, atoms_length_eq_atomCount]

theorem checkPermSort_pos_example :
    checkPermSort (.node (.node (.atom 2) .unit) (.atom 0)) (.node (.atom 0) (.atom 2)) = true := by
  rw [(checkPermSort_eq_isPerm_and_size_bounds _ _).1]
  rfl

theorem checkPermSort_neg_example :
    checkPermSort (.node (.atom 0) (.atom 0)) (.atom 0) = false := by
  rw [(checkPermSort_eq_isPerm_and_size_bounds _ _).1]
  rfl

/-- Decidability instance witness: propositional atom-list permutation `l.atoms.Perm r.atoms`
is decidable via `checkPermSort l r = true`. -/
def decideTreePerm (l r : Tree) : Decidable (l.atoms.Perm r.atoms) :=
  decidable_of_iff (checkPermSort l r = true) (by
    rw [(checkPermSort_eq_isPerm_and_size_bounds l r).1, List.isPerm_iff])

/-- Non-vacuity witness for `checkPermSort_eq_isPerm_and_size_bounds`: distinct trees
with unit leaves and swapped atoms satisfy `checkPermSort l r = true` and strict
inequality `l.atomCount < l.size`. -/
theorem checkPermSort_nonvacuous :
    let l : Tree := .node (.node (.atom 2) .unit) (.atom 0)
    let r : Tree := .node (.atom 0) (.atom 2)
    l ≠ r ∧ checkPermSort l r = true ∧ l.atomCount < l.size :=
  ⟨by decide, checkPermSort_pos_example, by decide⟩

end Toy.SepAC
