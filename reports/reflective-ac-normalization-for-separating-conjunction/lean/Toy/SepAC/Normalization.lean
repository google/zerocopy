import Toy.SepAC.Syntax

/-!
# Soundness, Exact Characterizations, and Tightness of Reflective AC and ACU Normalization

Separates three layers of reflective normalization over `Tree`, giving both minimal
sufficiency theorems and exact `↔` characterizations of the required algebraic laws:

1. **Monoid flattening (`denote_eq_denoteAtoms_of_assoc_units`)**: flattening `Tree.node`
   and eliminating `Tree.unit` into the right-nested list fold `denoteAtoms` is sound for
   all environments and trees if and only if `SepAssoc`, `LeftUnit`, and `RightUnit` hold
   (`denote_eq_denoteAtoms_iff_assoc_units`).
2. **Full ACU permutation soundness (`acu_denote_eq_of_isPerm`)**: deciding equality of
   arbitrary `Tree`s via `List.isPerm` on `Tree.atoms` is sound for all environments and
   trees if and only if `SepAssoc`, `SepComm`, and `RightUnit` hold
   (`acu_denote_eq_of_isPerm_iff`, with `LeftUnit` derived via
   `leftUnit_of_comm_of_rightUnit`).
3. **Unit-law-free AC permutation soundness (`ac_denote_eq_of_unitCount_eq_of_isPerm` and
   `ac_denote_eq_of_unitFree_of_isPerm`)**: when two trees have equal `Tree.unit` leaf counts
   (`l.unitCount = r.unitCount`, in particular when both are `unitFree`), `List.isPerm`
   soundness holds for all environments and trees if and only if `SepAssoc` and `SepComm`
   hold (`ac_denote_eq_of_unitCount_eq_of_isPerm_iff`,
   `ac_denote_eq_of_unitFree_of_isPerm_iff`), with **no** unit law on `emp`.

Every hypothesis of every soundness theorem has a fully proved canonical tightness
counterexample satisfying all remaining hypotheses and refuting the conclusion.
-/

namespace Toy.SepAC

universe u

/-! ## Result 1a: Monoid flattening and unit elimination (exposing `denoteAtoms`) -/

/-- Distributivity of `denoteAtoms` over list append under `SepAssoc` and `LeftUnit`. -/
theorem denoteAtoms_append {P : Type u} (sep : P → P → P) (emp : P)
    (hAssoc : SepAssoc sep) (hLeftUnit : LeftUnit sep emp)
    (env : Nat → P) (xs ys : List Nat) :
    denoteAtoms sep emp env (xs ++ ys) =
      sep (denoteAtoms sep emp env xs) (denoteAtoms sep emp env ys) := by
  induction xs with
  | nil => exact (hLeftUnit _).symm
  | cons x xs ih =>
    show sep (env x) (denoteAtoms sep emp env (xs ++ ys)) =
      sep (sep (env x) (denoteAtoms sep emp env xs)) (denoteAtoms sep emp env ys)
    rw [ih, hAssoc]

/-- **Monoid flattening to right-nested fold (`denoteAtoms`).**
If `sep` satisfies `SepAssoc`, `LeftUnit`, and `RightUnit` (no commutativity assumed),
every syntax tree `t` has the same denotation as the canonical right-nested fold
`denoteAtoms sep emp env t.atoms`. -/
theorem denote_eq_denoteAtoms_of_assoc_units {P : Type u}
    (sep : P → P → P) (emp : P)
    (hAssoc : SepAssoc sep) (hLeftUnit : LeftUnit sep emp) (hRightUnit : RightUnit sep emp)
    (env : Nat → P) (t : Tree) :
    t.denote sep emp env = denoteAtoms sep emp env t.atoms := by
  induction t with
  | atom i => exact (hRightUnit (env i)).symm
  | unit => rfl
  | node l r ihl ihr =>
    show sep (l.denote sep emp env) (r.denote sep emp env) =
      denoteAtoms sep emp env (l.atoms ++ r.atoms)
    rw [denoteAtoms_append sep emp hAssoc hLeftUnit, ihl, ihr]

/-- **Joint necessity (converse of `denote_eq_denoteAtoms_of_assoc_units`).**
If flattening to `denoteAtoms` holds for every environment and syntax tree over `(sep, emp)`,
then `SepAssoc sep`, `LeftUnit sep emp`, and `RightUnit sep emp` all hold. -/
theorem assoc_units_of_denote_eq_denoteAtoms {P : Type u}
    (sep : P → P → P) (emp : P)
    (h : ∀ (env : Nat → P) (t : Tree),
      t.denote sep emp env = denoteAtoms sep emp env t.atoms) :
    SepAssoc sep ∧ LeftUnit sep emp ∧ RightUnit sep emp := by
  have hR : RightUnit sep emp := fun x => (h (fun _ => x) (.atom 0)).symm
  refine ⟨fun x y z => ?_, fun x => ?_, hR⟩
  · have h1 := h (fun i => if i = 0 then x else if i = 1 then y else z)
      (.node (.node (.atom 0) (.atom 1)) (.atom 2))
    exact h1.trans (by
      show sep x (sep y (sep z emp)) = sep x (sep y z)
      rw [hR z])
  · have h1 := h (fun _ => x) (.node .unit (.atom 0))
    exact h1.trans (hR x)

/-- **Exact algebraic characterization of monoid flattening (`R1a-iff`).**
Flattening `Tree.denote` to `denoteAtoms` is universally sound for `(sep, emp)` if and
only if `SepAssoc sep`, `LeftUnit sep emp`, and `RightUnit sep emp` hold. -/
theorem denote_eq_denoteAtoms_iff_assoc_units {P : Type u}
    (sep : P → P → P) (emp : P) :
    (∀ (env : Nat → P) (t : Tree),
      t.denote sep emp env = denoteAtoms sep emp env t.atoms) ↔
      SepAssoc sep ∧ LeftUnit sep emp ∧ RightUnit sep emp :=
  ⟨assoc_units_of_denote_eq_denoteAtoms sep emp,
   fun ⟨hA, hL, hR⟩ env t => denote_eq_denoteAtoms_of_assoc_units sep emp hA hL hR env t⟩

/-- Non-vacuity witness for `denote_eq_denoteAtoms_of_assoc_units`: list concatenation on
`List Nat` with `[]` satisfies `SepAssoc`, `LeftUnit`, and `RightUnit` while violating
`SepComm`. -/
theorem denote_eq_denoteAtoms_of_assoc_units_nonvacuous :
    SepAssoc (@List.append Nat) ∧
    LeftUnit (@List.append Nat) [] ∧
    RightUnit (@List.append Nat) [] ∧
    ¬ SepComm (@List.append Nat) :=
  ⟨listAppend_sepAssoc, listAppend_leftUnit, listAppend_rightUnit, listAppend_not_sepComm⟩

/-- Canonical tightness of `SepAssoc` in `denote_eq_denoteAtoms_of_assoc_units`:
`NonAssocCarrier.op` satisfies both `LeftUnit` and `RightUnit` (and even `SepComm`),
yet `((0 ∗ 0) ∗ 1)` denotes `.b` whereas `denoteAtoms` on `[0, 0, 1]` evaluates to `.a`. -/
theorem nonAssoc_tight_flattening_sepAssoc :
    LeftUnit NonAssocCarrier.op .emp ∧
    RightUnit NonAssocCarrier.op .emp ∧
    (let env : Nat → NonAssocCarrier := fun i => if i == 0 then .a else .b
     let t : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 1)
     t.denote NonAssocCarrier.op .emp env ≠ denoteAtoms NonAssocCarrier.op .emp env t.atoms) := by
  refine ⟨leftUnit_of_comm_of_rightUnit nonAssocOp_sepComm nonAssocOp_rightUnit,
    nonAssocOp_rightUnit, ?_⟩
  decide

/-- Canonical tightness of `LeftUnit` in `denote_eq_denoteAtoms_of_assoc_units`:
`leftProj` on `Bool` with `emp = false` satisfies `SepAssoc` and `RightUnit`, yet
`(unit ∗ atom 0)` at `env 0 = true` denotes `false` whereas `denoteAtoms` evaluates to `true`. -/
theorem leftProj_tight_flattening_leftUnit :
    SepAssoc (@leftProj Bool) ∧
    RightUnit (@leftProj Bool) false ∧
    (let env : Nat → Bool := fun _ => true
     let t : Tree := .node .unit (.atom 0)
     t.denote leftProj false env ≠ denoteAtoms leftProj false env t.atoms) := by
  refine ⟨fun _ _ _ => rfl, leftProj_rightUnit, ?_⟩
  decide

/-- Canonical tightness of `RightUnit` in `denote_eq_denoteAtoms_of_assoc_units`:
`rightProj` on `Bool` with `emp = false` satisfies `SepAssoc` and `LeftUnit`, yet
`atom 0` at `env 0 = true` denotes `true` whereas `denoteAtoms` evaluates to `false`. -/
theorem rightProj_tight_flattening_rightUnit :
    SepAssoc (@rightProj Bool) ∧
    LeftUnit (@rightProj Bool) false ∧
    (let env : Nat → Bool := fun _ => true
     let t : Tree := .atom 0
     t.denote rightProj false env ≠ denoteAtoms rightProj false env t.atoms) := by
  refine ⟨fun _ _ _ => rfl, rightProj_leftUnit, ?_⟩
  decide

/-! ## Result 1b: Full reflective ACU kernel soundness (`List.isPerm` on `Tree.atoms`) -/

/-- Permutation invariance of `denoteAtoms` under `SepAssoc` and `SepComm`. -/
theorem denoteAtoms_perm {P : Type u} (sep : P → P → P) (emp : P)
    (hAssoc : SepAssoc sep) (hComm : SepComm sep)
    (env : Nat → P) {xs ys : List Nat} (h : xs.Perm ys) :
    denoteAtoms sep emp env xs = denoteAtoms sep emp env ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => exact congrArg (sep (env x)) ih
  | swap x y l =>
    show sep (env y) (sep (env x) _) = sep (env x) (sep (env y) _)
    rw [← hAssoc, ← hAssoc, hComm (env y) (env x)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Reflective ACU normalization soundness.**
If `sep` satisfies `SepAssoc`, `SepComm`, and `RightUnit sep emp` (`LeftUnit` following by
`leftUnit_of_comm_of_rightUnit`), then boolean permutation equality
`l.atoms.isPerm r.atoms = true` implies `l.denote sep emp env = r.denote sep emp env`. -/
theorem acu_denote_eq_of_isPerm {P : Type u}
    (sep : P → P → P) (emp : P)
    (hAssoc : SepAssoc sep) (hComm : SepComm sep) (hRightUnit : RightUnit sep emp)
    (env : Nat → P) {l r : Tree}
    (hPerm : l.atoms.isPerm r.atoms = true) :
    l.denote sep emp env = r.denote sep emp env := by
  have hLeftUnit := leftUnit_of_comm_of_rightUnit hComm hRightUnit
  rw [denote_eq_denoteAtoms_of_assoc_units sep emp hAssoc hLeftUnit hRightUnit,
      denote_eq_denoteAtoms_of_assoc_units sep emp hAssoc hLeftUnit hRightUnit]
  exact denoteAtoms_perm sep emp hAssoc hComm env (List.isPerm_iff.mp hPerm)

/-- **Joint necessity (converse of `acu_denote_eq_of_isPerm`).**
If the `List.isPerm` kernel is sound for `(sep, emp)` over all environments and trees,
then `SepAssoc sep`, `SepComm sep`, and `RightUnit sep emp` all hold. -/
theorem acu_laws_of_denote_eq_of_isPerm {P : Type u}
    (sep : P → P → P) (emp : P)
    (h : ∀ (env : Nat → P) (l r : Tree),
      l.atoms.isPerm r.atoms = true → l.denote sep emp env = r.denote sep emp env) :
    SepAssoc sep ∧ SepComm sep ∧ RightUnit sep emp := by
  refine ⟨fun x y z => ?_, fun x y => ?_, fun x => ?_⟩
  · exact h (fun i => if i = 0 then x else if i = 1 then y else z)
      (.node (.node (.atom 0) (.atom 1)) (.atom 2))
      (.node (.atom 0) (.node (.atom 1) (.atom 2)))
      (by decide)
  · exact h (fun i => if i = 0 then x else y)
      (.node (.atom 0) (.atom 1)) (.node (.atom 1) (.atom 0)) (by decide)
  · exact h (fun _ => x) (.node (.atom 0) .unit) (.atom 0) (by decide)

/-- **Exact algebraic characterization of the `List.isPerm` ACU kernel (`R1b-iff`).**
For fixed `(sep, emp)`, `l.atoms.isPerm r.atoms = true → l.denote = r.denote` holds for
all environments and trees if and only if `SepAssoc sep`, `SepComm sep`, and
`RightUnit sep emp` hold. -/
theorem acu_denote_eq_of_isPerm_iff {P : Type u}
    (sep : P → P → P) (emp : P) :
    (∀ (env : Nat → P) (l r : Tree),
      l.atoms.isPerm r.atoms = true → l.denote sep emp env = r.denote sep emp env) ↔
      SepAssoc sep ∧ SepComm sep ∧ RightUnit sep emp :=
  ⟨acu_laws_of_denote_eq_of_isPerm sep emp,
   fun ⟨hA, hC, hR⟩ env _ _ hPerm => acu_denote_eq_of_isPerm sep emp hA hC hR env hPerm⟩

/-- Non-vacuity witness for `acu_denote_eq_of_isPerm`: the 3-state disjoint single-cell heap
model `CellModel` satisfies `SepAssoc`, `SepComm`, and `RightUnit`, and two non-identical
trees with `unit` and swapped atoms satisfy `l.atoms.isPerm r.atoms = true`. -/
theorem acu_denote_eq_of_isPerm_nonvacuous :
    SepAssoc CellModel.sep ∧
    SepComm CellModel.sep ∧
    RightUnit CellModel.sep .empty ∧
    (let l : Tree := .node (.node (.atom 0) .unit) (.atom 1)
     let r : Tree := .node (.atom 1) (.atom 0)
     l ≠ r ∧ l.atoms.isPerm r.atoms = true) := by
  refine ⟨cellModel_sepAssoc, cellModel_sepComm, cellModel_rightUnit, ?_⟩
  decide

/-! ## Result 2: Canonical tightness counterexamples for ACU soundness -/

/-- **Tightness of `SepComm` (Result 2a: without commutativity).**
List concatenation on `List Nat` with unit `[]` satisfies `SepAssoc`, `RightUnit`, and
`LeftUnit` while violating `SepComm`, and `(atom 0 ∗ atom 1)` vs `(atom 1 ∗ atom 0)` have
permutation-equal atom lists `[0, 1]` and `[1, 0]`, yet denote `[0, 1] ≠ [1, 0]`. -/
theorem listAppend_tight_isPerm_sepComm :
    SepAssoc (@List.append Nat) ∧
    RightUnit (@List.append Nat) [] ∧
    LeftUnit (@List.append Nat) [] ∧
    ¬ SepComm (@List.append Nat) ∧
    (let env : Nat → List Nat := fun i => [i]
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .node (.atom 1) (.atom 0)
     l.atoms.isPerm r.atoms = true ∧
       l.denote List.append [] env ≠ r.denote List.append [] env) := by
  refine ⟨listAppend_sepAssoc, listAppend_rightUnit, listAppend_leftUnit,
    listAppend_not_sepComm, ?_⟩
  decide

/-- **Tightness of `SepAssoc` (Result 2b: without associativity).**
On the minimal 3-element carrier `NonAssocCarrier` (minimality proved by
`atMostTwo_comm_unital_sepAssoc`), `NonAssocCarrier.op` is commutative with two-sided
unit `.emp` and fails `SepAssoc`, and `((atom 0 ∗ atom 0) ∗ atom 1)` vs
`(atom 0 ∗ (atom 0 ∗ atom 1))` have permutation-equal atom lists `[0, 0, 1]`, yet denote
`.b ≠ .a`. -/
theorem nonAssoc_tight_isPerm_sepAssoc :
    SepComm NonAssocCarrier.op ∧
    RightUnit NonAssocCarrier.op .emp ∧
    LeftUnit NonAssocCarrier.op .emp ∧
    ¬ SepAssoc NonAssocCarrier.op ∧
    (let env : Nat → NonAssocCarrier := fun i => if i == 0 then .a else .b
     let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 1)
     let r : Tree := .node (.atom 0) (.node (.atom 0) (.atom 1))
     l.atoms.isPerm r.atoms = true ∧
       l.denote NonAssocCarrier.op .emp env ≠ r.denote NonAssocCarrier.op .emp env) := by
  refine ⟨nonAssocOp_sepComm, nonAssocOp_rightUnit,
    leftUnit_of_comm_of_rightUnit nonAssocOp_sepComm nonAssocOp_rightUnit,
    nonAssocOp_not_sepAssoc, ?_⟩
  decide

/-- **Tightness of `RightUnit` (Result 2c: without the unit law).**
`Bool.and` with distinguished element `emp = false` satisfies `SepAssoc` and `SepComm`
while violating `RightUnit Bool.and false`, and `atom 0` vs `(atom 0 ∗ unit)` have
permutation-equal atom lists `[0]`, yet at `env 0 = true` they denote `true ≠ false`. -/
theorem boolAndFalse_tight_isPerm_rightUnit :
    SepAssoc Bool.and ∧
    SepComm Bool.and ∧
    ¬ RightUnit Bool.and false ∧
    (let env : Nat → Bool := fun _ => true
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) .unit
     l.atoms.isPerm r.atoms = true ∧
       l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  refine ⟨boolAnd_sepAssoc, boolAnd_sepComm, boolAndFalse_not_rightUnit, ?_⟩
  decide

/-- **Tightness of `hPerm` in `acu_denote_eq_of_isPerm`.**
`Bool.and` with `emp = true` satisfies `SepAssoc`, `SepComm`, and `RightUnit`, yet
`atom 0` and `atom 1` (with `isPerm = false`) denote `true ≠ false` under
`env 0 = true, env 1 = false`. -/
theorem boolAndTrue_tight_isPerm_perm :
    SepAssoc Bool.and ∧
    SepComm Bool.and ∧
    RightUnit Bool.and true ∧
    (let env : Nat → Bool := fun i => i == 0
     let l : Tree := .atom 0
     let r : Tree := .atom 1
     l.atoms.isPerm r.atoms = false ∧
       l.denote Bool.and true env ≠ r.denote Bool.and true env) := by
  refine ⟨boolAnd_sepAssoc, boolAnd_sepComm, boolAndTrue_rightUnit, ?_⟩
  decide

/-! ## Result 1c: Unit-law-free AC soundness (equal `unitCount` and `unitFree` specialization) -/

/-- Adjoin a fresh unit `none` to an arbitrary magma `(P, sep)`. -/
private def optSep {P : Type u} (sep : P → P → P) : Option P → Option P → Option P
  | none, y => y
  | some a, none => some a
  | some a, some b => some (sep a b)

private theorem optSep_assoc {P : Type u} (sep : P → P → P) (hA : SepAssoc sep) :
    SepAssoc (optSep sep) := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp only [optSep] <;> exact congrArg some (hA _ _ _)

private theorem optSep_comm {P : Type u} (sep : P → P → P) (hC : SepComm sep) :
    SepComm (optSep sep) := by
  intro x y
  cases x <;> cases y <;> simp only [optSep] <;> exact congrArg some (hC _ _)

private theorem optSep_rightUnit {P : Type u} (sep : P → P → P) :
    RightUnit (optSep sep) none := by
  intro x
  cases x <;> rfl

private theorem denote_optSep {P : Type u} (sep : P → P → P) (emp : P) (env : Nat → P)
    (t : Tree) (h : t.unitFree = true) :
    t.denote (optSep sep) none (fun i => some (env i)) = some (t.denote sep emp env) := by
  induction t with
  | atom i => rfl
  | unit => simp [Tree.unitFree] at h
  | node l r ihl ihr =>
    simp only [Tree.unitFree, Bool.and_eq_true] at h
    simp [Tree.denote, ihl h.1, ihr h.2, optSep]

private theorem unitFree_ac_denote_eq {P : Type u} (sep : P → P → P) (emp : P)
    (hAssoc : SepAssoc sep) (hComm : SepComm sep)
    (env : Nat → P) {l r : Tree}
    (hUFL : l.unitFree = true) (hUFR : r.unitFree = true)
    (hPerm : l.atoms.isPerm r.atoms = true) :
    l.denote sep emp env = r.denote sep emp env := by
  have h := acu_denote_eq_of_isPerm (optSep sep) none
    (optSep_assoc sep hAssoc) (optSep_comm sep hComm) (optSep_rightUnit sep)
    (fun i => some (env i)) hPerm
  rw [denote_optSep sep emp env l hUFL, denote_optSep sep emp env r hUFR] at h
  exact Option.some.inj h

/-- Replace every `Tree.unit` leaf by atom index `0` and shift all existing atom indices up by `1`. -/
def shiftTree : Tree → Tree
  | .atom i => .atom (i + 1)
  | .unit => .atom 0
  | .node l r => .node (shiftTree l) (shiftTree r)

/-- Environment adapter pairing `shiftTree` with `(emp, env)`: `0 ↦ emp`, `i + 1 ↦ env i`. -/
def shiftEnv {P : Type u} (emp : P) (env : Nat → P) : Nat → P
  | 0 => emp
  | i + 1 => env i

theorem denote_shift {P : Type u} (sep : P → P → P) (emp e' : P) (env : Nat → P) (t : Tree) :
    (shiftTree t).denote sep e' (shiftEnv emp env) = t.denote sep emp env := by
  induction t with
  | atom i => rfl
  | unit => rfl
  | node l r ihl ihr => simp [shiftTree, Tree.denote, ihl, ihr]

theorem unitFree_shift (t : Tree) : (shiftTree t).unitFree = true := by
  induction t with
  | atom i => rfl
  | unit => rfl
  | node l r ihl ihr => simp [shiftTree, Tree.unitFree, ihl, ihr]

theorem count_shift_zero (t : Tree) : (shiftTree t).atoms.count 0 = t.unitCount := by
  induction t with
  | atom i => simp [shiftTree, Tree.atoms, Tree.unitCount]
  | unit => simp [shiftTree, Tree.atoms, Tree.unitCount]
  | node l r ihl ihr => simp [shiftTree, Tree.atoms, Tree.unitCount, List.count_append, ihl, ihr]

theorem count_shift_succ (t : Tree) (k : Nat) :
    (shiftTree t).atoms.count (k + 1) = t.atoms.count k := by
  induction t with
  | atom i => simp [shiftTree, Tree.atoms, List.count_cons]
  | unit => simp [shiftTree, Tree.atoms]
  | node l r ihl ihr => simp [shiftTree, Tree.atoms, List.count_append, ihl, ihr]

/-- **Equal-unit-count reflective AC soundness (no unit law on `emp`).**
If `sep` is associative and commutative (`emp` completely unconstrained), and `l` and `r`
contain the same number of `Tree.unit` leaves (`l.unitCount = r.unitCount`) and
permutation-equal atom lists (`l.atoms.isPerm r.atoms = true`), then
`l.denote sep emp env = r.denote sep emp env` (`emp` behaves as one additional atom). -/
theorem ac_denote_eq_of_unitCount_eq_of_isPerm {P : Type u}
    (sep : P → P → P) (emp : P)
    (hAssoc : SepAssoc sep) (hComm : SepComm sep)
    (env : Nat → P) {l r : Tree}
    (hUnitCount : l.unitCount = r.unitCount)
    (hPerm : l.atoms.isPerm r.atoms = true) :
    l.denote sep emp env = r.denote sep emp env := by
  have hc : ∀ a, l.atoms.count a = r.atoms.count a :=
    List.perm_iff_count.mp (List.isPerm_iff.mp hPerm)
  have hP : (shiftTree l).atoms.isPerm (shiftTree r).atoms = true := by
    apply List.isPerm_iff.mpr
    apply List.perm_iff_count.mpr
    intro a
    cases a with
    | zero => rw [count_shift_zero, count_shift_zero, hUnitCount]
    | succ k => rw [count_shift_succ, count_shift_succ, hc k]
  have h := unitFree_ac_denote_eq sep emp hAssoc hComm (shiftEnv emp env)
    (unitFree_shift l) (unitFree_shift r) hP
  rw [denote_shift sep emp emp env l, denote_shift sep emp emp env r] at h
  exact h

/-- **Unit-free reflective AC soundness (specialization of `ac_denote_eq_of_unitCount_eq_of_isPerm`).**
If `sep` is associative and commutative (`emp` unconstrained), and both `l` and `r` contain
no `Tree.unit` leaves (`l.unitFree = true`, `r.unitFree = true`), then
`l.atoms.isPerm r.atoms = true` implies `l.denote sep emp env = r.denote sep emp env`. -/
theorem ac_denote_eq_of_unitFree_of_isPerm {P : Type u}
    (sep : P → P → P) (emp : P)
    (hAssoc : SepAssoc sep) (hComm : SepComm sep)
    (env : Nat → P) {l r : Tree}
    (hUFL : l.unitFree = true) (hUFR : r.unitFree = true)
    (hPerm : l.atoms.isPerm r.atoms = true) :
    l.denote sep emp env = r.denote sep emp env := by
  have hUC : l.unitCount = r.unitCount := by
    rw [(Tree.unitFree_iff_unitCount_eq_zero l).mp hUFL,
        (Tree.unitFree_iff_unitCount_eq_zero r).mp hUFR]
  exact ac_denote_eq_of_unitCount_eq_of_isPerm sep emp hAssoc hComm env hUC hPerm

/-- **Joint necessity (converse of `ac_denote_eq_of_unitFree_of_isPerm`).**
If unit-free `List.isPerm` soundness holds for `(sep, emp)` over all environments and
unit-free trees, then `SepAssoc sep` and `SepComm sep` hold. -/
theorem ac_laws_of_unitFree_denote_eq_of_isPerm {P : Type u}
    (sep : P → P → P) (emp : P)
    (h : ∀ (env : Nat → P) (l r : Tree),
      l.unitFree = true → r.unitFree = true → l.atoms.isPerm r.atoms = true →
      l.denote sep emp env = r.denote sep emp env) :
    SepAssoc sep ∧ SepComm sep := by
  refine ⟨fun x y z => ?_, fun x y => ?_⟩
  · exact h (fun i => if i = 0 then x else if i = 1 then y else z)
      (.node (.node (.atom 0) (.atom 1)) (.atom 2))
      (.node (.atom 0) (.node (.atom 1) (.atom 2)))
      rfl rfl (by decide)
  · exact h (fun i => if i = 0 then x else y)
      (.node (.atom 0) (.atom 1)) (.node (.atom 1) (.atom 0))
      rfl rfl (by decide)

/-- **Joint necessity (converse of `ac_denote_eq_of_unitCount_eq_of_isPerm`).**
If equal-unit-count `List.isPerm` soundness holds for `(sep, emp)` over all environments
and trees, then `SepAssoc sep` and `SepComm sep` hold. -/
theorem ac_laws_of_unitCount_denote_eq_of_isPerm {P : Type u}
    (sep : P → P → P) (emp : P)
    (h : ∀ (env : Nat → P) (l r : Tree),
      l.unitCount = r.unitCount → l.atoms.isPerm r.atoms = true →
      l.denote sep emp env = r.denote sep emp env) :
    SepAssoc sep ∧ SepComm sep :=
  ac_laws_of_unitFree_denote_eq_of_isPerm sep emp (fun env l r hUFL hUFR hPerm =>
    h env l r (by
      rw [(Tree.unitFree_iff_unitCount_eq_zero l).mp hUFL,
          (Tree.unitFree_iff_unitCount_eq_zero r).mp hUFR]) hPerm)

/-- **Exact algebraic characterization of equal-unit-count AC reflection (`R1c-iff`).** -/
theorem ac_denote_eq_of_unitCount_eq_of_isPerm_iff {P : Type u}
    (sep : P → P → P) (emp : P) :
    (∀ (env : Nat → P) (l r : Tree),
      l.unitCount = r.unitCount → l.atoms.isPerm r.atoms = true →
      l.denote sep emp env = r.denote sep emp env) ↔
      SepAssoc sep ∧ SepComm sep :=
  ⟨ac_laws_of_unitCount_denote_eq_of_isPerm sep emp,
   fun ⟨hA, hC⟩ env _ _ hUC hPerm =>
     ac_denote_eq_of_unitCount_eq_of_isPerm sep emp hA hC env hUC hPerm⟩

/-- **Exact algebraic characterization of unit-free AC reflection (`R1c-iff`).** -/
theorem ac_denote_eq_of_unitFree_of_isPerm_iff {P : Type u}
    (sep : P → P → P) (emp : P) :
    (∀ (env : Nat → P) (l r : Tree),
      l.unitFree = true → r.unitFree = true → l.atoms.isPerm r.atoms = true →
      l.denote sep emp env = r.denote sep emp env) ↔
      SepAssoc sep ∧ SepComm sep :=
  ⟨ac_laws_of_unitFree_denote_eq_of_isPerm sep emp,
   fun ⟨hA, hC⟩ env _ _ hUFL hUFR hPerm =>
     ac_denote_eq_of_unitFree_of_isPerm sep emp hA hC env hUFL hUFR hPerm⟩

/-- Non-vacuity witness for `ac_denote_eq_of_unitCount_eq_of_isPerm` (also demonstrating
that `unitFree` is sufficient, not necessary, when unit counts match): over
`(Nat, +, emp := 99)` where `RightUnit Nat.add 99` fails, `(atom 0 ∗ unit)` and
`(unit ∗ atom 0)` are both non-unit-free, share `unitCount = 1` and `isPerm = true`, and
denote equally in every environment. -/
theorem ac_denote_eq_of_unitCount_eq_of_isPerm_nonvacuous :
    SepAssoc Nat.add ∧
    SepComm Nat.add ∧
    ¬ RightUnit Nat.add 99 ∧
    (let l : Tree := .node (.atom 0) .unit
     let r : Tree := .node .unit (.atom 0)
     l.unitFree = false ∧ r.unitFree = false ∧
     l.unitCount = r.unitCount ∧ l.atoms.isPerm r.atoms = true ∧
     ∀ env : Nat → Nat, l.denote Nat.add 99 env = r.denote Nat.add 99 env) := by
  refine ⟨natAdd_sepAssoc, natAdd_sepComm, ?_, by decide, by decide, rfl, by decide, ?_⟩
  · intro h
    have h0 := h 0
    cases h0
  · intro env
    exact Nat.add_comm (env 0) 99

/-- Canonical tightness of `SepAssoc` in `ac_denote_eq_of_unitCount_eq_of_isPerm`. -/
theorem nonAssoc_tight_unitCount_sepAssoc :
    SepComm NonAssocCarrier.op ∧
    (let env : Nat → NonAssocCarrier := fun i => if i == 0 then .a else .b
     let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 1)
     let r : Tree := .node (.atom 0) (.node (.atom 0) (.atom 1))
     l.unitCount = r.unitCount ∧ l.atoms.isPerm r.atoms = true ∧
       l.denote NonAssocCarrier.op .emp env ≠ r.denote NonAssocCarrier.op .emp env) := by
  refine ⟨nonAssocOp_sepComm, rfl, ?_⟩
  decide

/-- Canonical tightness of `SepComm` in `ac_denote_eq_of_unitCount_eq_of_isPerm`. -/
theorem listAppend_tight_unitCount_sepComm :
    SepAssoc (@List.append Nat) ∧
    (let env : Nat → List Nat := fun i => [i]
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .node (.atom 1) (.atom 0)
     l.unitCount = r.unitCount ∧ l.atoms.isPerm r.atoms = true ∧
       l.denote List.append [] env ≠ r.denote List.append [] env) := by
  refine ⟨listAppend_sepAssoc, rfl, ?_⟩
  decide

/-- Canonical tightness of `l.unitCount = r.unitCount` in
`ac_denote_eq_of_unitCount_eq_of_isPerm`. -/
theorem boolAndFalse_tight_unitCount_eq :
    SepAssoc Bool.and ∧
    SepComm Bool.and ∧
    (let env : Nat → Bool := fun _ => true
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) .unit
     l.unitCount ≠ r.unitCount ∧ l.atoms.isPerm r.atoms = true ∧
       l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  refine ⟨boolAnd_sepAssoc, boolAnd_sepComm, ?_⟩
  decide

/-- Canonical tightness of `hPerm` in `ac_denote_eq_of_unitCount_eq_of_isPerm`. -/
theorem boolAndFalse_tight_unitCount_perm :
    SepAssoc Bool.and ∧
    SepComm Bool.and ∧
    (let env : Nat → Bool := fun i => i == 0
     let l : Tree := .atom 0
     let r : Tree := .atom 1
     l.unitCount = r.unitCount ∧ l.atoms.isPerm r.atoms = false ∧
       l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  refine ⟨boolAnd_sepAssoc, boolAnd_sepComm, rfl, ?_⟩
  decide

/-- Non-vacuity witness for `ac_denote_eq_of_unitFree_of_isPerm`: `(Nat, +, emp := 99)`
satisfies `SepAssoc` and `SepComm` while violating `RightUnit Nat.add 99`, and two
unit-free trees satisfy `l.atoms.isPerm r.atoms = true`. -/
theorem ac_denote_eq_of_unitFree_of_isPerm_nonvacuous :
    SepAssoc Nat.add ∧
    SepComm Nat.add ∧
    ¬ RightUnit Nat.add 99 ∧
    (let l : Tree := .node (.node (.atom 0) (.atom 1)) (.atom 2)
     let r : Tree := .node (.atom 2) (.node (.atom 0) (.atom 1))
     l.unitFree = true ∧ r.unitFree = true ∧ l.atoms.isPerm r.atoms = true) := by
  refine ⟨natAdd_sepAssoc, natAdd_sepComm, ?_, ?_⟩
  · intro h
    have h0 := h 0
    cases h0
  · decide

/-- Canonical tightness of `SepAssoc` in `ac_denote_eq_of_unitFree_of_isPerm`. -/
theorem nonAssoc_tight_unitFree_sepAssoc :
    SepComm NonAssocCarrier.op ∧
    (let env : Nat → NonAssocCarrier := fun i => if i == 0 then .a else .b
     let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 1)
     let r : Tree := .node (.atom 0) (.node (.atom 0) (.atom 1))
     l.unitFree = true ∧ r.unitFree = true ∧ l.atoms.isPerm r.atoms = true ∧
       l.denote NonAssocCarrier.op .emp env ≠ r.denote NonAssocCarrier.op .emp env) := by
  refine ⟨nonAssocOp_sepComm, ?_⟩
  decide

/-- Canonical tightness of `SepComm` in `ac_denote_eq_of_unitFree_of_isPerm`. -/
theorem listAppend_tight_unitFree_sepComm :
    SepAssoc (@List.append Nat) ∧
    (let env : Nat → List Nat := fun i => [i]
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .node (.atom 1) (.atom 0)
     l.unitFree = true ∧ r.unitFree = true ∧ l.atoms.isPerm r.atoms = true ∧
       l.denote List.append [] env ≠ r.denote List.append [] env) := by
  refine ⟨listAppend_sepAssoc, ?_⟩
  decide

/-- Canonical tightness of `l.unitFree = true` in `ac_denote_eq_of_unitFree_of_isPerm`:
dropping `l.unitFree = true` while keeping `r.unitFree = true` fails when `emp` is not a unit. -/
theorem boolAndFalse_tight_unitFree_left :
    SepAssoc Bool.and ∧
    SepComm Bool.and ∧
    (let env : Nat → Bool := fun _ => true
     let l : Tree := .node (.atom 0) .unit
     let r : Tree := .atom 0
     r.unitFree = true ∧ l.atoms.isPerm r.atoms = true ∧
       l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  refine ⟨boolAnd_sepAssoc, boolAnd_sepComm, ?_⟩
  decide

/-- Canonical tightness of `r.unitFree = true` in `ac_denote_eq_of_unitFree_of_isPerm`:
dropping `r.unitFree = true` while keeping `l.unitFree = true` fails when `emp` is not a unit. -/
theorem boolAndFalse_tight_unitFree_right :
    SepAssoc Bool.and ∧
    SepComm Bool.and ∧
    (let env : Nat → Bool := fun _ => true
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) .unit
     l.unitFree = true ∧ l.atoms.isPerm r.atoms = true ∧
       l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  refine ⟨boolAnd_sepAssoc, boolAnd_sepComm, ?_⟩
  decide

/-- Canonical tightness of `hPerm` in `ac_denote_eq_of_unitFree_of_isPerm`. -/
theorem boolAndFalse_tight_unitFree_perm :
    SepAssoc Bool.and ∧
    SepComm Bool.and ∧
    (let env : Nat → Bool := fun i => i == 0
     let l : Tree := .atom 0
     let r : Tree := .atom 1
     l.unitFree = true ∧ r.unitFree = true ∧ l.atoms.isPerm r.atoms = false ∧
       l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  refine ⟨boolAnd_sepAssoc, boolAnd_sepComm, ?_⟩
  decide

end Toy.SepAC
