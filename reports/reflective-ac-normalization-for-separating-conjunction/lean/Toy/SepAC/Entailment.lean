import Toy.SepAC.FreeMonoid

/-!
# Frame Cancellation for Separation-Logic Entailment

Unbundled entailment and compatibility laws (`EntailsRefl`, `EntailsTrans`,
`SepMonoRight`, `SepMonoLeft`, `AffineEntails`), mutual-entailment counterparts
(`Bientails`, `SepAssocBientails`, `SepCommBientails`, `RightUnitBientails`,
`LeftUnitBientails`), executable maximal sub-multiset cancellation (`cancelAtoms`) with
its full multiset-difference specification (`cancelAtoms_spec`, `cancelAtoms_count`,
`cancelAtoms_disjoint`), and two general arbitrary-sub-multiset soundness theorems:

1. **Extensional ACU frame cancellation (`acu_entails_of_common_perm_of_sepMonoRight`)**:
   when `sep` satisfies propositional equality laws (`SepAssoc`, `SepComm`, `RightUnit`),
   reducing `entails (l.denote ...) (r.denote ...)` to `entails (denoteAtoms ... ls)
   (denoteAtoms ... rs)` after removing any common sub-multiset `common` (`l.atoms ~ common
   ++ ls`, `r.atoms ~ common ++ rs`) requires **only** `SepMonoRight` — neither
   `EntailsRefl`, nor `EntailsTrans`, nor `SepMonoLeft` is needed. Maximal cancellation
   via `cancelAtoms` follows as an immediate corollary
   (`acu_entails_of_cancelAtoms_of_sepMonoRight`).
2. **Mutual-entailment ACU frame cancellation
   (`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`)**: when `sep` is ACU
   only up to `Bientails entails` rather than `=`, `EntailsTrans` becomes strictly
   necessary and tight, while `EntailsRefl` and `SepMonoLeft` remain derivable. Maximal
   cancellation follows as a corollary
   (`bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`).

Also proves:
- the non-monotonicity counterexample over a genuine preorder (`capOne_tight_commonPerm_sepMonoRight`),
- a sufficiency-only witness showing no converse holds for entailment cancellation
  (`totalRelation_cancel_sound_without_laws`),
- converse failure of maximal `cancelAtoms` in both a **linear** single-cell model
  (`cellModel_cancelAtoms_converse_fails`, with affine control `affineCellEntails_residual_holds`)
  and an **affine** two-cell model (`twoCellModel_affine_cancelAtoms_converse_fails`),
- and a witness that partial cancellation succeeds where maximal `cancelAtoms` fails
  (`partial_cancellation_succeeds_where_cancelAtoms_fails`).
-/

namespace Toy.SepAC

universe u

/-! ## Unbundled entailment and compatibility laws -/

/-- Reflexivity of entailment: `x ⊢ x`. -/
def EntailsRefl {P : Type u} (entails : P → P → Prop) : Prop :=
  ∀ x : P, entails x x

/-- Transitivity of entailment: `x ⊢ y → y ⊢ z → x ⊢ z`. -/
def EntailsTrans {P : Type u} (entails : P → P → Prop) : Prop :=
  ∀ x y z : P, entails x y → entails y z → entails x z

/-- Right monotonicity (left framing) of `sep` with respect to `entails`:
`x ⊢ y → f ∗ x ⊢ f ∗ y`. -/
def SepMonoRight {P : Type u} (sep : P → P → P) (entails : P → P → Prop) : Prop :=
  ∀ f x y : P, entails x y → entails (sep f x) (sep f y)

/-- Left monotonicity (right framing) of `sep` with respect to `entails`:
`x ⊢ y → x ∗ f ⊢ y ∗ f`. -/
def SepMonoLeft {P : Type u} (sep : P → P → P) (entails : P → P → Prop) : Prop :=
  ∀ x y f : P, entails x y → entails (sep x f) (sep y f)

/-- Affinity (weakening to `emp`): every assertion entails `emp` (`∀ x, x ⊢ emp`).
Distinguishes affine separation logics (where `emp` is top for `⊢`) from linear
separation logics (where exclusive ownership does not entail `emp`). -/
def AffineEntails {P : Type u} (emp : P) (entails : P → P → Prop) : Prop :=
  ∀ x : P, entails x emp

/-- Mutual entailment (`x ⊣⊢ y`): the intersection of `entails` with its converse
(`entails x y ∧ entails y x`, i.e. the symmetric interior/core, not the symmetric closure).
Forms an equivalence relation when `entails` is a preorder (reflexive and transitive). -/
def Bientails {P : Type u} (entails : P → P → Prop) (x y : P) : Prop :=
  entails x y ∧ entails y x

/-- Associativity of `sep` up to mutual entailment `Bientails entails`.
Captures separation logics whose assertions are not quotiented by `propext`/`funext`. -/
def SepAssocBientails {P : Type u} (sep : P → P → P) (entails : P → P → Prop) : Prop :=
  ∀ x y z : P, Bientails entails (sep (sep x y) z) (sep x (sep y z))

/-- Commutativity of `sep` up to mutual entailment `Bientails entails`. -/
def SepCommBientails {P : Type u} (sep : P → P → P) (entails : P → P → Prop) : Prop :=
  ∀ x y : P, Bientails entails (sep x y) (sep y x)

/-- Right unit law for `emp` up to mutual entailment `Bientails entails`. -/
def RightUnitBientails {P : Type u} (sep : P → P → P) (emp : P) (entails : P → P → Prop) : Prop :=
  ∀ x : P, Bientails entails (sep x emp) x

/-- Left unit law for `emp` up to mutual entailment `Bientails entails`. -/
def LeftUnitBientails {P : Type u} (sep : P → P → P) (emp : P) (entails : P → P → Prop) : Prop :=
  ∀ x : P, Bientails entails (sep emp x) x

/-! ## Executable maximal sub-multiset cancellation and its full specification -/

/-- Strip one occurrence of each atom index in `xs` that appears in `ys` (scanning `xs`
left-to-right and erasing the first matching entry in `ys`), returning the residual
pair `(leftover_xs, leftover_ys)`. Computes maximal index-based multiset cancellation. -/
def cancelAtoms : List Nat → List Nat → List Nat × List Nat
  | [], ys => ([], ys)
  | x :: xs, ys =>
    if ys.contains x then
      cancelAtoms xs (ys.erase x)
    else
      let (xs', ys') := cancelAtoms xs ys
      (x :: xs', ys')

/-- **Decomposition specification of `cancelAtoms`:** there exists a common cancelled list
`common` such that `xs ~ common ++ (cancelAtoms xs ys).1` and
`ys ~ common ++ (cancelAtoms xs ys).2`. -/
theorem cancelAtoms_spec (xs ys : List Nat) :
    ∃ common : List Nat,
      xs.Perm (common ++ (cancelAtoms xs ys).1) ∧
      ys.Perm (common ++ (cancelAtoms xs ys).2) := by
  induction xs generalizing ys with
  | nil => exact ⟨[], List.Perm.refl _, List.Perm.refl _⟩
  | cons x xs ih =>
    by_cases hc : ys.contains x = true
    · obtain ⟨c, h1, h2⟩ := ih (ys.erase x)
      have hmem : x ∈ ys := List.contains_iff_mem.mp hc
      refine ⟨x :: c, ?_, ?_⟩
      · simp only [cancelAtoms, hc, ↓reduceIte]
        exact List.Perm.cons x h1
      · simp only [cancelAtoms, hc, ↓reduceIte]
        exact (List.perm_cons_erase hmem).trans (List.Perm.cons x h2)
    · obtain ⟨c, h1, h2⟩ := ih ys
      have hc' : ys.contains x = false := by simpa using hc
      refine ⟨c, ?_, ?_⟩
      · simp only [cancelAtoms, hc', Bool.false_eq_true, ↓reduceIte]
        exact (List.Perm.cons x h1).trans List.perm_middle.symm
      · simp only [cancelAtoms, hc', Bool.false_eq_true, ↓reduceIte]
        exact h2

/-- **Exact multiset-difference specification of `cancelAtoms`:** for every atom index `a`,
the residual multiplicities equal `xs.count a - ys.count a` and `ys.count a - xs.count a`. -/
theorem cancelAtoms_count (xs ys : List Nat) (a : Nat) :
    (cancelAtoms xs ys).1.count a = xs.count a - ys.count a ∧
    (cancelAtoms xs ys).2.count a = ys.count a - xs.count a := by
  induction xs generalizing ys with
  | nil =>
    simp [cancelAtoms]
  | cons x xs ih =>
    by_cases hc : ys.contains x = true
    · simp only [cancelAtoms, hc, ↓reduceIte]
      have ⟨h1, h2⟩ := ih (ys.erase x)
      have hmem : x ∈ ys := List.contains_iff_mem.mp hc
      have hpos : 0 < ys.count x := List.count_pos_iff.mpr hmem
      rw [h1, h2, List.count_erase, List.count_cons]
      by_cases hax : a = x
      · subst hax
        simp only [beq_self_eq_true, ↓reduceIte]
        omega
      · have hne1 : (x == a) = false := beq_false_of_ne (Ne.symm hax)
        simp only [hne1, Bool.false_eq_true, ↓reduceIte]
        omega
    · have hc' : ys.contains x = false := by simpa using hc
      simp only [cancelAtoms, hc', Bool.false_eq_true, ↓reduceIte]
      have ⟨h1, h2⟩ := ih ys
      have hnotmem : x ∉ ys := by
        intro hmem
        exact hc (List.contains_iff_mem.mpr hmem)
      have hzero : ys.count x = 0 := List.count_eq_zero.mpr hnotmem
      rw [List.count_cons, List.count_cons, h1, h2]
      by_cases hax : a = x
      · subst hax
        simp only [beq_self_eq_true, ↓reduceIte]
        omega
      · have hne : (x == a) = false := beq_false_of_ne (Ne.symm hax)
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        omega

/-- **Maximality (disjointness) of `cancelAtoms` residuals:** no atom index appears in
both residuals of `cancelAtoms xs ys`. -/
theorem cancelAtoms_disjoint (xs ys : List Nat) (a : Nat) :
    a ∈ (cancelAtoms xs ys).1 → a ∉ (cancelAtoms xs ys).2 := by
  intro hmem1 hmem2
  have hpos1 : 0 < (cancelAtoms xs ys).1.count a := List.count_pos_iff.mpr hmem1
  have hpos2 : 0 < (cancelAtoms xs ys).2.count a := List.count_pos_iff.mpr hmem2
  have ⟨hc1, hc2⟩ := cancelAtoms_count xs ys a
  omega

/-! ## Derived laws (and why they are omitted from main theorem hypotheses) -/

/-- Under propositional commutativity `SepComm`, `SepMonoLeft` is derivable from
`SepMonoRight` with no order assumptions on `entails`. -/
theorem sepMonoLeft_of_comm_of_monoRight {P : Type u} {sep : P → P → P} {entails : P → P → Prop}
    (hComm : SepComm sep) (hMonoR : SepMonoRight sep entails) :
    SepMonoLeft sep entails := by
  intro x y f hxy
  rw [hComm x f, hComm y f]
  exact hMonoR f x y hxy

/-- Under `EntailsTrans` and `RightUnitBientails`, `EntailsRefl` is derivable:
`x ⊢ sep x emp ⊢ x` yields `x ⊢ x`. -/
theorem entailsRefl_of_trans_of_rightUnitBientails {P : Type u}
    {sep : P → P → P} {emp : P} {entails : P → P → Prop}
    (hTrans : EntailsTrans entails) (hUnit : RightUnitBientails sep emp entails) :
    EntailsRefl entails := by
  intro x
  exact hTrans x (sep x emp) x (hUnit x).2 (hUnit x).1

/-- Under `EntailsTrans` and `SepCommBientails`, `SepMonoLeft` is derivable from
`SepMonoRight`. -/
theorem sepMonoLeft_of_trans_of_commBientails_of_monoRight {P : Type u}
    {sep : P → P → P} {entails : P → P → Prop}
    (hTrans : EntailsTrans entails) (hComm : SepCommBientails sep entails)
    (hMonoR : SepMonoRight sep entails) :
    SepMonoLeft sep entails := by
  intro x y f hxy
  have h1 : entails (sep x f) (sep f x) := (hComm x f).1
  have h2 : entails (sep f x) (sep f y) := hMonoR f x y hxy
  have h3 : entails (sep f y) (sep y f) := (hComm f y).1
  exact hTrans _ _ _ h1 (hTrans _ _ _ h2 h3)

/-- Under `EntailsTrans` and `SepCommBientails`, `LeftUnitBientails` is derivable from
`RightUnitBientails`. -/
theorem leftUnitBientails_of_trans_of_commBientails_of_rightUnitBientails {P : Type u}
    {sep : P → P → P} {emp : P} {entails : P → P → Prop}
    (hTrans : EntailsTrans entails) (hComm : SepCommBientails sep entails)
    (hRight : RightUnitBientails sep emp entails) :
    LeftUnitBientails sep emp entails := by
  intro x
  exact ⟨hTrans _ _ _ (hComm emp x).1 (hRight x).1,
    hTrans _ _ _ (hRight x).2 (hComm x emp).1⟩

/-! ## Concrete relations and algebras for examples and counterexamples -/

/-- Capacity-`1` score on `Nat`: `0 ↦ 0`, `1 ↦ 1`, and `n + 2 ↦ 0` (overflow resets).
Models a non-local capacity-bounded assertion where adding a resource overflows. -/
def capOneScore : Nat → Nat
  | 0 => 0
  | 1 => 1
  | _ + 2 => 0

/-- Preorder on `Nat` induced by `capOneScore`: reflexive and transitive, but not
monotone under `Nat.add` (`0 ⊢ 1`, yet `1 + 0 ⊬ 1 + 1`). -/
def capOneEntails (x y : Nat) : Prop :=
  capOneScore x ≤ capOneScore y

/-- Asymmetric operation `2 * (x % 2) + y` on `Nat`: monotone in `y` (`SepMonoRight`
under `≤`), not commutative, and not monotone in `x` (`SepMonoLeft` fails at `1 ≤ 2`). -/
def parityBiasOp (x y : Nat) : Nat :=
  2 * (x % 2) + y

/-- Syntax-depth-tagged value `(val, depth)` with `sep (v₁, d₁) (v₂, d₂) = (v₁ + v₂, max d₁ d₂ + 1)`
and `emp = (0, 0)`. Used to separate single-step `Bientails` (`|d₁ - d₂| ≤ 1`) from
multi-step normalization when `EntailsTrans` is omitted. -/
abbrev TaggedNat := Nat × Nat

def taggedEmp : TaggedNat := (0, 0)

def taggedSep (x y : TaggedNat) : TaggedNat :=
  (x.1 + y.1, max x.2 y.2 + 1)

/-- Non-transitive proximity relation on `TaggedNat`: equal values and tag distance `≤ 1`. -/
def tagDistLeOne (x y : TaggedNat) : Prop :=
  x.1 = y.1 ∧ x.2 ≤ y.2 + 1 ∧ y.2 ≤ x.2 + 1

/-- Preorder on `TaggedNat` ignoring the syntax-depth tag: genuine setoid model where
`taggedSep x taggedEmp ≠ x` propositionally, yet `RightUnitBientails` holds. -/
def taggedValLe (x y : TaggedNat) : Prop :=
  x.1 ≤ y.1

/-- **Non-affine (linear-logic)** entailment order on `CellModel`: `.conflict` is bottom
(`conflict ⊢ x`), and `.empty` and `.owned` are incomparable except to themselves
(`owned ⊬ empty`, so `¬ AffineEntails CellModel.empty CellModel.entails`). -/
def CellModel.entails : CellModel → CellModel → Prop
  | .conflict, _ => True
  | .empty, .empty => True
  | .owned, .owned => True
  | _, _ => False

/-- **Affine** entailment order on `CellModel`: `.conflict` is bottom and `.empty` is top
(`∀ x, x ⊢ empty`). Control relation showing the 1-cell linear witness residual
`owned ⊢ empty` becomes valid under affine entailment. -/
def affineCellEntails : CellModel → CellModel → Prop
  | .conflict, _ => True
  | _, .empty => True
  | .owned, .owned => True
  | _, _ => False

/-- Boolean helper for **affine** subset entailment on `TwoCellModel`: `.conflict` entails
everything, everything entails `.empty`, and `.both` entails `.cellA`, `.cellB`, `.both`. -/
def TwoCellModel.entailsBool : TwoCellModel → TwoCellModel → Bool
  | .conflict, _ => true
  | _, .empty => true
  | .cellA, .cellA => true
  | .cellB, .cellB => true
  | .both, .cellA => true
  | .both, .cellB => true
  | .both, .both => true
  | _, _ => false

/-- **Affine** entailment order on `TwoCellModel`: `.conflict` is bottom, `.empty` is top
(`AffineEntails TwoCellModel.empty TwoCellModel.entails`), and otherwise `x ⊢ y` iff `y`'s
owned cells are a subset of `x`'s owned cells. -/
def TwoCellModel.entails (x y : TwoCellModel) : Prop :=
  TwoCellModel.entailsBool x y = true

/-! ## Positive and negative examples for entailment definitions -/

theorem natLe_entailsRefl : EntailsRefl Nat.le := Nat.le_refl

theorem natLt_not_entailsRefl : ¬ EntailsRefl Nat.lt := by
  intro h
  exact Nat.lt_irrefl 0 (h 0)

theorem natLe_entailsTrans : EntailsTrans Nat.le := fun _ _ _ => Nat.le_trans

theorem tagDistLeOne_not_entailsTrans : ¬ EntailsTrans tagDistLeOne := by
  intro h
  have h01 : tagDistLeOne (0, 0) (0, 1) := ⟨rfl, by omega, by omega⟩
  have h12 : tagDistLeOne (0, 1) (0, 2) := ⟨rfl, by omega, by omega⟩
  have h02 := h (0, 0) (0, 1) (0, 2) h01 h12
  rcases h02 with ⟨_, _, hbad⟩
  omega

theorem natAdd_le_sepMonoRight : SepMonoRight Nat.add Nat.le := by
  intro f x y hxy
  exact Nat.add_le_add_left hxy f

theorem capOne_not_sepMonoRight : ¬ SepMonoRight Nat.add capOneEntails := by
  intro h
  have h01 : capOneEntails 0 1 := Nat.zero_le 1
  have hbad : capOneEntails (Nat.add 1 0) (Nat.add 1 1) := h 1 0 1 h01
  cases hbad

theorem natAdd_le_sepMonoLeft : SepMonoLeft Nat.add Nat.le := by
  intro x y f hxy
  exact Nat.add_le_add_right hxy f

/-- `parityBiasOp` satisfies `SepMonoRight` under `Nat.le` yet violates `SepMonoLeft`,
demonstrating that `SepComm` is genuinely required in `sepMonoLeft_of_comm_of_monoRight`. -/
theorem parityBiasOp_monoRight_and_not_monoLeft :
    SepMonoRight parityBiasOp Nat.le ∧ ¬ SepMonoLeft parityBiasOp Nat.le := by
  refine ⟨?_, ?_⟩
  · intro f x y hxy
    exact Nat.add_le_add_left hxy (2 * (f % 2))
  · intro h
    have h12 : Nat.le 1 2 := Nat.le_succ 1
    have hbad : Nat.le 2 0 := h 1 2 0 h12
    cases hbad

theorem twoCellModel_affineEntails :
    AffineEntails TwoCellModel.empty TwoCellModel.entails := by
  intro x
  cases x <;> rfl

theorem cellModel_not_affineEntails :
    ¬ AffineEntails CellModel.empty CellModel.entails := by
  intro h
  exact h .owned

theorem bientails_pos_example : Bientails taggedValLe (3, 0) (3, 5) :=
  ⟨Nat.le_refl 3, Nat.le_refl 3⟩

theorem bientails_neg_example : ¬ Bientails taggedValLe (2, 0) (3, 0) := by
  rintro ⟨_, hba⟩
  unfold taggedValLe at hba
  omega

theorem taggedSep_assocBientails_valLe : SepAssocBientails taggedSep taggedValLe := by
  intro x y z
  unfold Bientails taggedValLe taggedSep
  omega

theorem nonAssoc_not_assocBientails_eq : ¬ SepAssocBientails NonAssocCarrier.op Eq := by
  intro h
  exact nonAssocOp_not_sepAssoc (fun x y z => (h x y z).1)

theorem taggedSep_commBientails_valLe : SepCommBientails taggedSep taggedValLe := by
  intro x y
  unfold Bientails taggedValLe taggedSep
  omega

theorem listAppend_not_commBientails_eq : ¬ SepCommBientails (@List.append Nat) Eq := by
  intro h
  exact listAppend_not_sepComm (fun x y => (h x y).1)

theorem taggedSep_rightUnitBientails_valLe :
    RightUnitBientails taggedSep taggedEmp taggedValLe ∧
      ¬ RightUnit taggedSep taggedEmp := by
  refine ⟨?_, ?_⟩
  · intro x
    unfold Bientails taggedValLe taggedSep taggedEmp
    omega
  · intro h
    have h0 := congrArg Prod.snd (h (0, 0))
    simp [taggedSep, taggedEmp] at h0

theorem boolAndFalse_not_rightUnitBientails_eq :
    ¬ RightUnitBientails Bool.and false Eq := by
  intro h
  exact boolAndFalse_not_rightUnit (fun x => (h x).1)

theorem leftUnitBientails_pos_example :
    LeftUnitBientails taggedSep taggedEmp taggedValLe := by
  intro x
  unfold Bientails taggedValLe taggedSep taggedEmp
  omega

theorem leftUnitBientails_neg_example :
    ¬ LeftUnitBientails (@leftProj Bool) false Eq := by
  intro h
  exact leftProj_not_leftUnit (fun x => (h x).1)

theorem cancelAtoms_pos_example :
    cancelAtoms [0, 1, 0, 2] [2, 0, 3] = ([1, 0], [3]) := rfl

theorem cancelAtoms_neg_example :
    cancelAtoms [0, 0] [1] ≠ ([], []) := by decide

theorem cellModel_entailsRefl : EntailsRefl CellModel.entails := by
  intro x
  cases x <;> trivial

theorem cellModel_entailsTrans : EntailsTrans CellModel.entails := by
  intro x y z hxy hyz
  cases x <;> cases y <;> cases z <;> first | trivial | cases hxy | cases hyz

theorem cellModel_sepMonoRight : SepMonoRight CellModel.sep CellModel.entails := by
  intro f x y hxy
  cases f <;> cases x <;> cases y <;> first | trivial | cases hxy

theorem twoCellModel_entailsRefl : EntailsRefl TwoCellModel.entails := by
  intro x
  cases x <;> rfl

theorem twoCellModel_entailsTrans : EntailsTrans TwoCellModel.entails := by
  intro x y z
  unfold TwoCellModel.entails
  cases x <;> cases y <;> cases z <;> decide

theorem twoCellModel_sepMonoRight : SepMonoRight TwoCellModel.sep TwoCellModel.entails := by
  intro f x y
  unfold TwoCellModel.entails
  cases f <;> cases x <;> cases y <;> decide

theorem twoCellModel_entails_pos_example :
    TwoCellModel.entails .both .cellA := rfl

theorem twoCellModel_entails_neg_example :
    ¬ TwoCellModel.entails .cellA .cellB := by
  unfold TwoCellModel.entails
  decide

theorem affineCellEntails_pos_example :
    affineCellEntails .owned .empty := trivial

theorem affineCellEntails_neg_example :
    ¬ affineCellEntails .empty .owned := fun h => h

/-! ## Result 4a: Arbitrary common sub-multiset frame cancellation (propositional ACU) -/

/-- **General reflective frame cancellation under propositional-equality ACU.**
If `sep` satisfies `SepAssoc`, `SepComm`, and `RightUnit sep emp` (propositional equality),
and `entails` satisfies `SepMonoRight sep entails`, then for **any** common sub-multiset
`common` and residuals `ls, rs` satisfying `l.atoms.Perm (common ++ ls)` and
`r.atoms.Perm (common ++ rs)`, `entails (l.denote ...) (r.denote ...)` follows from
`entails (denoteAtoms ... ls) (denoteAtoms ... rs)`. Neither `EntailsRefl`, nor
`EntailsTrans`, nor `SepMonoLeft` is required. -/
theorem acu_entails_of_common_perm_of_sepMonoRight {P : Type u}
    (sep : P → P → P) (emp : P) (entails : P → P → Prop)
    (hAssoc : SepAssoc sep) (hComm : SepComm sep) (hRightUnit : RightUnit sep emp)
    (hMonoRight : SepMonoRight sep entails)
    (env : Nat → P) {l r : Tree} (common ls rs : List Nat)
    (hl : l.atoms.Perm (common ++ ls)) (hr : r.atoms.Perm (common ++ rs))
    (hResidual : entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env rs)) :
    entails (l.denote sep emp env) (r.denote sep emp env) := by
  have hLeftUnit := leftUnit_of_comm_of_rightUnit hComm hRightUnit
  rw [denote_eq_denoteAtoms_of_assoc_units sep emp hAssoc hLeftUnit hRightUnit,
      denote_eq_denoteAtoms_of_assoc_units sep emp hAssoc hLeftUnit hRightUnit,
      denoteAtoms_perm sep emp hAssoc hComm env hl,
      denoteAtoms_perm sep emp hAssoc hComm env hr,
      denoteAtoms_append sep emp hAssoc hLeftUnit,
      denoteAtoms_append sep emp hAssoc hLeftUnit]
  exact hMonoRight _ _ _ hResidual

/-- **Maximal `cancelAtoms` corollary of `acu_entails_of_common_perm_of_sepMonoRight`.**
Instantiates arbitrary sub-multiset cancellation at the maximal common sub-multiset
witnessed by `cancelAtoms_spec`. -/
theorem acu_entails_of_cancelAtoms_of_sepMonoRight {P : Type u}
    (sep : P → P → P) (emp : P) (entails : P → P → Prop)
    (hAssoc : SepAssoc sep) (hComm : SepComm sep) (hRightUnit : RightUnit sep emp)
    (hMonoRight : SepMonoRight sep entails)
    (env : Nat → P) {l r : Tree}
    (hResidual : entails
      (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).1)
      (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).2)) :
    entails (l.denote sep emp env) (r.denote sep emp env) := by
  obtain ⟨common, hl, hr⟩ := cancelAtoms_spec l.atoms r.atoms
  exact acu_entails_of_common_perm_of_sepMonoRight sep emp entails
    hAssoc hComm hRightUnit hMonoRight env common _ _ hl hr hResidual

/-- Non-vacuity witness for `acu_entails_of_common_perm_of_sepMonoRight` in `CellModel`
(using non-maximal partial cancellation `common = [0]`, `ls = [0, 0]`, `rs = [0]`). -/
theorem acu_entails_of_common_perm_nonvacuous :
    SepAssoc CellModel.sep ∧
    SepComm CellModel.sep ∧
    RightUnit CellModel.sep .empty ∧
    SepMonoRight CellModel.sep CellModel.entails ∧
    (let env : Nat → CellModel := fun _ => .owned
     let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 0)
     let r : Tree := .node (.atom 0) (.atom 0)
     l.atoms.Perm ([0] ++ [0, 0]) ∧
     r.atoms.Perm ([0] ++ [0]) ∧
     CellModel.entails
       (denoteAtoms CellModel.sep .empty env [0, 0])
       (denoteAtoms CellModel.sep .empty env [0])) :=
  ⟨cellModel_sepAssoc, cellModel_sepComm, cellModel_rightUnit, cellModel_sepMonoRight,
   List.Perm.refl _, List.Perm.refl _, trivial⟩

/-- Witness demonstrating that `acu_entails_of_common_perm_of_sepMonoRight` (and its
`cancelAtoms` corollary) applies even when `entails` is neither reflexive nor transitive:
`x + 2 = y` on `(Nat, +, 0)` satisfies `SepMonoRight`, violates both `EntailsRefl` and
`EntailsTrans`, and satisfies all hypotheses at `l = (0 ∗ 1)`, `r = (1 ∗ 2)`,
`common = [1]`, `ls = [0]`, `rs = [2]`. -/
theorem stepByTwo_nonPreorder_satisfies_cancel_hypotheses :
    let entails : Nat → Nat → Prop := fun x y => x + 2 = y
    let env : Nat → Nat := fun i => i
    let l : Tree := .node (.atom 0) (.atom 1)
    let r : Tree := .node (.atom 1) (.atom 2)
    ¬ EntailsRefl entails ∧
    ¬ EntailsTrans entails ∧
    SepAssoc Nat.add ∧
    SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
    SepMonoRight Nat.add entails ∧
    l.atoms.Perm ([1] ++ [0]) ∧
    r.atoms.Perm ([1] ++ [2]) ∧
    entails (denoteAtoms Nat.add 0 env [0]) (denoteAtoms Nat.add 0 env [2]) ∧
    entails
      (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).1)
      (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).2) := by
  refine ⟨?_, ?_, natAdd_sepAssoc, natAdd_sepComm, Nat.add_zero, ?_, ?_, List.Perm.refl _,
    by decide, by decide⟩
  · intro h
    have h0 := h 0
    omega
  · intro h
    have h1 := h 0 2 4 rfl rfl
    omega
  · intro f x y hxy
    change (f + x) + 2 = f + y
    omega
  · exact List.Perm.swap 1 0 []

/-- **Sufficiency-only witness (no converse for entailment cancellation):**
Over `NonAssocCarrier` (which violates `SepAssoc`), the total relation `fun _ _ => True`
trivially makes every cancellation goal hold without `SepAssoc`, showing that the
hypotheses of `acu_entails_of_common_perm_of_sepMonoRight` and its `Bientails` variant
are sufficient, not necessary, for a particular `(sep, entails)`. -/
theorem totalRelation_cancel_sound_without_laws :
    ¬ SepAssoc NonAssocCarrier.op ∧
    ∀ (env : Nat → NonAssocCarrier) (l r : Tree),
      (fun (_ _ : NonAssocCarrier) => True)
        (l.denote NonAssocCarrier.op .emp env)
        (r.denote NonAssocCarrier.op .emp env) :=
  ⟨nonAssocOp_not_sepAssoc, fun _ _ _ => trivial⟩

/-! ## Canonical tightness counterexamples for `acu_entails_of_common_perm_of_sepMonoRight` -/

/-- **Tightness of `SepMonoRight` (Result 4c: frame cancellation fails without monotonicity,
even over a reflexive, transitive preorder on a commutative monoid).**
On `(Nat, +, 0)`, `capOneEntails` satisfies `EntailsRefl` and `EntailsTrans` while
violating `SepMonoRight`, and for `l = atom 0` vs `r = atom 0 ∗ atom 0` at `env 0 = 1`,
cancelling `common = [0]` (matching `cancelAtoms`) leaves `0 ⊢ 1` (true), whereas `1 ⊢ 2`
fails. -/
theorem capOne_tight_commonPerm_sepMonoRight :
    EntailsRefl capOneEntails ∧
    EntailsTrans capOneEntails ∧
    SepAssoc Nat.add ∧
    SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
    ¬ SepMonoRight Nat.add capOneEntails ∧
    (let env : Nat → Nat := fun _ => 1
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) (.atom 0)
     l.atoms.Perm ([0] ++ []) ∧
     r.atoms.Perm ([0] ++ [0]) ∧
     capOneEntails (denoteAtoms Nat.add 0 env []) (denoteAtoms Nat.add 0 env [0]) ∧
     capOneEntails
       (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).1)
       (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).2) ∧
     ¬ capOneEntails (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) := by
  refine ⟨fun _ => Nat.le_refl _, fun _ _ _ => Nat.le_trans,
    natAdd_sepAssoc, natAdd_sepComm, Nat.add_zero, capOne_not_sepMonoRight,
    List.Perm.refl _, List.Perm.refl _, ?_, ?_, ?_⟩
  · show capOneScore 0 ≤ capOneScore 1; decide
  · show capOneScore 0 ≤ capOneScore 1; decide
  · show ¬ (capOneScore 1 ≤ capOneScore 2); decide

/-- Canonical tightness of `SepAssoc` in `acu_entails_of_common_perm_of_sepMonoRight`. -/
theorem nonAssoc_tight_commonPerm_sepAssoc :
    SepComm NonAssocCarrier.op ∧
    RightUnit NonAssocCarrier.op .emp ∧
    SepMonoRight NonAssocCarrier.op Eq ∧
    (let env : Nat → NonAssocCarrier := fun i => if i == 0 then .a else .b
     let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 1)
     let r : Tree := .node (.atom 0) (.node (.atom 0) (.atom 1))
     l.atoms.Perm ([0, 0, 1] ++ []) ∧
     r.atoms.Perm ([0, 0, 1] ++ []) ∧
     denoteAtoms NonAssocCarrier.op .emp env [] = denoteAtoms NonAssocCarrier.op .emp env [] ∧
     l.denote NonAssocCarrier.op .emp env ≠ r.denote NonAssocCarrier.op .emp env) := by
  refine ⟨nonAssocOp_sepComm, nonAssocOp_rightUnit,
    fun f _ _ h => congrArg (NonAssocCarrier.op f) h,
    List.Perm.refl _, List.Perm.refl _, rfl, ?_⟩
  decide

/-- Canonical tightness of `SepComm` in `acu_entails_of_common_perm_of_sepMonoRight`. -/
theorem listAppend_tight_commonPerm_sepComm :
    SepAssoc (@List.append Nat) ∧
    RightUnit (@List.append Nat) [] ∧
    SepMonoRight (@List.append Nat) Eq ∧
    (let env : Nat → List Nat := fun i => [i]
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .node (.atom 1) (.atom 0)
     l.atoms.Perm ([0, 1] ++ []) ∧
     r.atoms.Perm ([0, 1] ++ []) ∧
     denoteAtoms List.append [] env [] = denoteAtoms List.append [] env [] ∧
     l.denote List.append [] env ≠ r.denote List.append [] env) := by
  refine ⟨listAppend_sepAssoc, listAppend_rightUnit,
    fun f _ _ h => congrArg (List.append f) h,
    List.Perm.refl _, List.Perm.swap 0 1 [], rfl, ?_⟩
  decide

/-- Canonical tightness of `RightUnit` in `acu_entails_of_common_perm_of_sepMonoRight`. -/
theorem boolAndFalse_tight_commonPerm_rightUnit :
    SepAssoc Bool.and ∧
    SepComm Bool.and ∧
    SepMonoRight Bool.and Eq ∧
    (let env : Nat → Bool := fun _ => true
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) .unit
     l.atoms.Perm ([0] ++ []) ∧
     r.atoms.Perm ([0] ++ []) ∧
     denoteAtoms Bool.and false env [] = denoteAtoms Bool.and false env [] ∧
     l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  refine ⟨boolAnd_sepAssoc, boolAnd_sepComm,
    fun f _ _ h => congrArg (Bool.and f) h,
    List.Perm.refl _, List.Perm.refl _, rfl, ?_⟩
  decide

/-- Canonical tightness of `hl : l.atoms.Perm (common ++ ls)` in
`acu_entails_of_common_perm_of_sepMonoRight`. -/
theorem natAdd_tight_commonPerm_leftPerm :
    SepAssoc Nat.add ∧
    SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
    SepMonoRight Nat.add Nat.le ∧
    (let env : Nat → Nat := fun _ => 1
     let l : Tree := .atom 0
     let r : Tree := .unit
     ¬ l.atoms.Perm ([] ++ []) ∧
     r.atoms.Perm ([] ++ []) ∧
     Nat.le (denoteAtoms Nat.add 0 env []) (denoteAtoms Nat.add 0 env []) ∧
     ¬ Nat.le (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) := by
  refine ⟨natAdd_sepAssoc, natAdd_sepComm, Nat.add_zero, natAdd_le_sepMonoRight,
    ?_, List.Perm.refl _, Nat.le_refl 0, ?_⟩
  · intro h
    have hlen := h.length_eq
    cases hlen
  · intro h
    cases h

/-- Canonical tightness of `hr : r.atoms.Perm (common ++ rs)` in
`acu_entails_of_common_perm_of_sepMonoRight`. -/
theorem natAdd_tight_commonPerm_rightPerm :
    SepAssoc Nat.add ∧
    SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
    SepMonoRight Nat.add Nat.le ∧
    (let env : Nat → Nat := fun _ => 1
     let l : Tree := .atom 0
     let r : Tree := .unit
     l.atoms.Perm ([] ++ [0]) ∧
     ¬ r.atoms.Perm ([] ++ [0]) ∧
     Nat.le (denoteAtoms Nat.add 0 env [0]) (denoteAtoms Nat.add 0 env [0]) ∧
     ¬ Nat.le (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) := by
  refine ⟨natAdd_sepAssoc, natAdd_sepComm, Nat.add_zero, natAdd_le_sepMonoRight,
    List.Perm.refl _, ?_, Nat.le_refl _, ?_⟩
  · intro h
    have hlen := h.length_eq
    cases hlen
  · intro h
    cases h

/-- Canonical tightness of `hResidual` in `acu_entails_of_common_perm_of_sepMonoRight`. -/
theorem natAdd_tight_commonPerm_residual :
    SepAssoc Nat.add ∧
    SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
    SepMonoRight Nat.add Nat.le ∧
    (let env : Nat → Nat := fun i => i + 1
     let l : Tree := .atom 1
     let r : Tree := .atom 0
     l.atoms.Perm ([] ++ [1]) ∧
     r.atoms.Perm ([] ++ [0]) ∧
     ¬ Nat.le (denoteAtoms Nat.add 0 env [1]) (denoteAtoms Nat.add 0 env [0]) ∧
     ¬ Nat.le (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) := by
  refine ⟨natAdd_sepAssoc, natAdd_sepComm, Nat.add_zero, natAdd_le_sepMonoRight,
    List.Perm.refl _, List.Perm.refl _, ?_, ?_⟩
  · intro h
    have h' : Nat.le 2 1 := h
    cases Nat.le_of_succ_le_succ h'
  · intro h
    have h' : Nat.le 2 1 := h
    cases Nat.le_of_succ_le_succ h'

/-! ## Result 4b: General arbitrary-sub-multiset cancellation under `Bientails` ACU -/

private theorem bi_trans {P : Type u} {entails : P → P → Prop} (hT : EntailsTrans entails)
    {x y z : P} (h1 : Bientails entails x y) (h2 : Bientails entails y z) :
    Bientails entails x z :=
  ⟨hT _ _ _ h1.1 h2.1, hT _ _ _ h2.2 h1.2⟩

private theorem bi_symm {P : Type u} {entails : P → P → Prop} {x y : P}
    (h : Bientails entails x y) : Bientails entails y x :=
  ⟨h.2, h.1⟩

private theorem bi_congr_right {P : Type u} {sep : P → P → P} {entails : P → P → Prop}
    (hM : SepMonoRight sep entails) {f x y : P} (h : Bientails entails x y) :
    Bientails entails (sep f x) (sep f y) :=
  ⟨hM _ _ _ h.1, hM _ _ _ h.2⟩

private theorem bi_congr_left {P : Type u} {sep : P → P → P} {entails : P → P → Prop}
    (hML : SepMonoLeft sep entails) {x y f : P} (h : Bientails entails x y) :
    Bientails entails (sep x f) (sep y f) :=
  ⟨hML _ _ _ h.1, hML _ _ _ h.2⟩

/-- **General reflective frame cancellation under mutual-entailment (`Bientails`) ACU.**
When `sep` satisfies associativity, commutativity, and right unit only up to `Bientails
entails` (rather than propositional `=`), adding `EntailsTrans entails` alongside
`SepMonoRight` suffices to derive `entails (l.denote ...) (r.denote ...)` from `entails`
on the residuals `ls, rs` of any common sub-multiset `common` (`EntailsRefl` and
`SepMonoLeft` being derived). -/
theorem bientails_acu_entails_of_common_perm_of_trans_sepMonoRight {P : Type u}
    (sep : P → P → P) (emp : P) (entails : P → P → Prop)
    (hTrans : EntailsTrans entails)
    (hAssoc : SepAssocBientails sep entails)
    (hComm : SepCommBientails sep entails)
    (hRightUnit : RightUnitBientails sep emp entails)
    (hMonoRight : SepMonoRight sep entails)
    (env : Nat → P) {l r : Tree} (common ls rs : List Nat)
    (hl : l.atoms.Perm (common ++ ls)) (hr : r.atoms.Perm (common ++ rs))
    (hResidual : entails (denoteAtoms sep emp env ls) (denoteAtoms sep emp env rs)) :
    entails (l.denote sep emp env) (r.denote sep emp env) := by
  have hRefl := entailsRefl_of_trans_of_rightUnitBientails hTrans hRightUnit
  have hML := sepMonoLeft_of_trans_of_commBientails_of_monoRight hTrans hComm hMonoRight
  have hLU := leftUnitBientails_of_trans_of_commBientails_of_rightUnitBientails
    hTrans hComm hRightUnit
  let dA := denoteAtoms sep emp env
  have bRefl : ∀ x : P, Bientails entails x x := fun x => ⟨hRefl x, hRefl x⟩
  have hApp : ∀ xs ys : List Nat, Bientails entails (dA (xs ++ ys)) (sep (dA xs) (dA ys)) := by
    intro xs ys
    induction xs with
    | nil => exact bi_symm (hLU _)
    | cons x xs ih =>
      exact bi_trans hTrans (bi_congr_right hMonoRight ih) (bi_symm (hAssoc _ _ _))
  have hFlat : ∀ t : Tree, Bientails entails (t.denote sep emp env) (dA t.atoms) := by
    intro t
    induction t with
    | atom i => exact bi_symm (hRightUnit _)
    | unit => exact bRefl _
    | node a b iha ihb =>
      exact bi_trans hTrans (bi_congr_left hML iha)
        (bi_trans hTrans (bi_congr_right hMonoRight ihb) (bi_symm (hApp _ _)))
  have hPermBi : ∀ {xs ys : List Nat}, xs.Perm ys → Bientails entails (dA xs) (dA ys) := by
    intro xs ys h
    induction h with
    | nil => exact bRefl _
    | cons x _ ih => exact bi_congr_right hMonoRight ih
    | swap x y l =>
      exact bi_trans hTrans (bi_symm (hAssoc _ _ _))
        (bi_trans hTrans (bi_congr_left hML (hComm _ _)) (hAssoc _ _ _))
    | trans _ _ ih1 ih2 => exact bi_trans hTrans ih1 ih2
  have hl' := bi_trans hTrans (hFlat l) (bi_trans hTrans (hPermBi hl) (hApp _ _))
  have hr' := bi_trans hTrans (hFlat r) (bi_trans hTrans (hPermBi hr) (hApp _ _))
  exact hTrans _ _ _ hl'.1 (hTrans _ _ _ (hMonoRight _ _ _ hResidual) hr'.2)

/-- **Maximal `cancelAtoms` corollary of
`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`.** -/
theorem bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight {P : Type u}
    (sep : P → P → P) (emp : P) (entails : P → P → Prop)
    (hTrans : EntailsTrans entails)
    (hAssoc : SepAssocBientails sep entails)
    (hComm : SepCommBientails sep entails)
    (hRightUnit : RightUnitBientails sep emp entails)
    (hMonoRight : SepMonoRight sep entails)
    (env : Nat → P) {l r : Tree}
    (hResidual : entails
      (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).1)
      (denoteAtoms sep emp env (cancelAtoms l.atoms r.atoms).2)) :
    entails (l.denote sep emp env) (r.denote sep emp env) := by
  obtain ⟨common, hl, hr⟩ := cancelAtoms_spec l.atoms r.atoms
  exact bientails_acu_entails_of_common_perm_of_trans_sepMonoRight sep emp entails
    hTrans hAssoc hComm hRightUnit hMonoRight env common _ _ hl hr hResidual

/-- Non-vacuity witness for `bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`:
`(TaggedNat, taggedSep, taggedEmp, taggedValLe)` satisfies all hypotheses while violating
propositional `RightUnit` (so `acu_entails_of_common_perm_of_sepMonoRight` does not apply). -/
theorem bientails_acu_entails_of_common_perm_nonvacuous :
    EntailsTrans taggedValLe ∧
    SepAssocBientails taggedSep taggedValLe ∧
    SepCommBientails taggedSep taggedValLe ∧
    RightUnitBientails taggedSep taggedEmp taggedValLe ∧
    SepMonoRight taggedSep taggedValLe ∧
    ¬ RightUnit taggedSep taggedEmp ∧
    (let env : Nat → TaggedNat := fun i => (i + 1, 0)
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .node (.atom 1) (.atom 2)
     l.atoms.Perm ([1] ++ [0]) ∧
     r.atoms.Perm ([1] ++ [2]) ∧
     taggedValLe (denoteAtoms taggedSep taggedEmp env [0])
       (denoteAtoms taggedSep taggedEmp env [2])) := by
  refine ⟨fun _ _ _ => Nat.le_trans,
    taggedSep_assocBientails_valLe,
    taggedSep_commBientails_valLe,
    taggedSep_rightUnitBientails_valLe.1,
    ?_,
    taggedSep_rightUnitBientails_valLe.2,
    List.Perm.swap 1 0 [],
    List.Perm.refl _,
    ?_⟩
  · intro f x y hxy
    unfold taggedValLe taggedSep at *
    omega
  · show (0 + 1) + 0 ≤ (2 + 1) + 0
    omega

/-- **Canonical tightness of `EntailsTrans` in
`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`.** -/
theorem tagDistLeOne_tight_bientails_commonPerm_trans :
    EntailsRefl tagDistLeOne ∧
    SepAssocBientails taggedSep tagDistLeOne ∧
    SepCommBientails taggedSep tagDistLeOne ∧
    RightUnitBientails taggedSep taggedEmp tagDistLeOne ∧
    SepMonoRight taggedSep tagDistLeOne ∧
    (let env : Nat → TaggedNat := fun _ => (1, 0)
     let l : Tree := .atom 0
     let r : Tree := .node (.node (.atom 0) .unit) .unit
     l.atoms.Perm ([0] ++ []) ∧
     r.atoms.Perm ([0] ++ []) ∧
     tagDistLeOne (denoteAtoms taggedSep taggedEmp env [])
       (denoteAtoms taggedSep taggedEmp env []) ∧
     ¬ tagDistLeOne
       (l.denote taggedSep taggedEmp env)
       (r.denote taggedSep taggedEmp env)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, List.Perm.refl _, List.Perm.refl _, ?_, ?_⟩
  · intro x
    exact ⟨rfl, by omega, by omega⟩
  · intro x y z
    simp only [Bientails, tagDistLeOne, taggedSep]
    omega
  · intro x y
    simp only [Bientails, tagDistLeOne, taggedSep]
    omega
  · intro x
    simp only [Bientails, tagDistLeOne, taggedSep, taggedEmp]
    omega
  · intro f x y hxy
    rcases hxy with ⟨hv, h1, h2⟩
    simp only [tagDistLeOne, taggedSep]
    omega
  · simp [denoteAtoms, taggedEmp, tagDistLeOne]
  · rintro ⟨_, _, hbad⟩
    simp [Tree.denote, taggedSep, taggedEmp] at hbad

/-- Canonical tightness of `SepAssocBientails` in
`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`. -/
theorem nonAssoc_tight_bientails_commonPerm_sepAssoc :
    EntailsTrans (@Eq NonAssocCarrier) ∧
    SepCommBientails NonAssocCarrier.op Eq ∧
    RightUnitBientails NonAssocCarrier.op .emp Eq ∧
    SepMonoRight NonAssocCarrier.op Eq ∧
    (let env : Nat → NonAssocCarrier := fun i => if i == 0 then .a else .b
     let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 1)
     let r : Tree := .node (.atom 0) (.node (.atom 0) (.atom 1))
     l.atoms.Perm ([0, 0, 1] ++ []) ∧
     r.atoms.Perm ([0, 0, 1] ++ []) ∧
     denoteAtoms NonAssocCarrier.op .emp env [] = denoteAtoms NonAssocCarrier.op .emp env [] ∧
     l.denote NonAssocCarrier.op .emp env ≠ r.denote NonAssocCarrier.op .emp env) := by
  refine ⟨fun _ _ _ => Eq.trans,
    fun x y => ⟨nonAssocOp_sepComm x y, nonAssocOp_sepComm y x⟩,
    fun x => ⟨nonAssocOp_rightUnit x, (nonAssocOp_rightUnit x).symm⟩,
    fun f _ _ h => congrArg (NonAssocCarrier.op f) h,
    List.Perm.refl _, List.Perm.refl _, rfl, ?_⟩
  decide

/-- Canonical tightness of `SepCommBientails` in
`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`. -/
theorem listAppend_tight_bientails_commonPerm_sepComm :
    EntailsTrans (@Eq (List Nat)) ∧
    SepAssocBientails (@List.append Nat) Eq ∧
    RightUnitBientails (@List.append Nat) [] Eq ∧
    SepMonoRight (@List.append Nat) Eq ∧
    (let env : Nat → List Nat := fun i => [i]
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .node (.atom 1) (.atom 0)
     l.atoms.Perm ([0, 1] ++ []) ∧
     r.atoms.Perm ([0, 1] ++ []) ∧
     denoteAtoms List.append [] env [] = denoteAtoms List.append [] env [] ∧
     l.denote List.append [] env ≠ r.denote List.append [] env) := by
  refine ⟨fun _ _ _ => Eq.trans,
    fun x y z => ⟨listAppend_sepAssoc x y z, (listAppend_sepAssoc x y z).symm⟩,
    fun x => ⟨listAppend_rightUnit x, (listAppend_rightUnit x).symm⟩,
    fun f _ _ h => congrArg (List.append f) h,
    List.Perm.refl _, List.Perm.swap 0 1 [], rfl, ?_⟩
  decide

/-- Canonical tightness of `RightUnitBientails` in
`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`. -/
theorem boolAndFalse_tight_bientails_commonPerm_rightUnit :
    EntailsTrans (@Eq Bool) ∧
    SepAssocBientails Bool.and Eq ∧
    SepCommBientails Bool.and Eq ∧
    SepMonoRight Bool.and Eq ∧
    (let env : Nat → Bool := fun _ => true
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) .unit
     l.atoms.Perm ([0] ++ []) ∧
     r.atoms.Perm ([0] ++ []) ∧
     denoteAtoms Bool.and false env [] = denoteAtoms Bool.and false env [] ∧
     l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  refine ⟨fun _ _ _ => Eq.trans,
    fun x y z => ⟨boolAnd_sepAssoc x y z, (boolAnd_sepAssoc x y z).symm⟩,
    fun x y => ⟨boolAnd_sepComm x y, boolAnd_sepComm y x⟩,
    fun f _ _ h => congrArg (Bool.and f) h,
    List.Perm.refl _, List.Perm.refl _, rfl, ?_⟩
  decide

/-- Canonical tightness of `SepMonoRight` in
`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`. -/
theorem capOne_tight_bientails_commonPerm_sepMonoRight :
    EntailsTrans capOneEntails ∧
    SepAssocBientails Nat.add capOneEntails ∧
    SepCommBientails Nat.add capOneEntails ∧
    RightUnitBientails Nat.add 0 capOneEntails ∧
    ¬ SepMonoRight Nat.add capOneEntails ∧
    (let env : Nat → Nat := fun _ => 1
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) (.atom 0)
     l.atoms.Perm ([0] ++ []) ∧
     r.atoms.Perm ([0] ++ [0]) ∧
     capOneEntails (denoteAtoms Nat.add 0 env []) (denoteAtoms Nat.add 0 env [0]) ∧
     ¬ capOneEntails (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) := by
  refine ⟨fun _ _ _ => Nat.le_trans,
    fun x y z => by rw [natAdd_sepAssoc x y z]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
    fun x y => by rw [natAdd_sepComm x y]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
    fun x => ⟨Nat.le_refl _, Nat.le_refl _⟩,
    capOne_not_sepMonoRight,
    List.Perm.refl _, List.Perm.refl _, ?_, ?_⟩
  · show capOneScore 0 ≤ capOneScore 1; decide
  · show ¬ (capOneScore 1 ≤ capOneScore 2); decide

/-- Canonical tightness of `hl : l.atoms.Perm (common ++ ls)` in
`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`. -/
theorem natAdd_tight_bientails_commonPerm_leftPerm :
    EntailsTrans Nat.le ∧
    SepAssocBientails Nat.add Nat.le ∧
    SepCommBientails Nat.add Nat.le ∧
    RightUnitBientails Nat.add 0 Nat.le ∧
    SepMonoRight Nat.add Nat.le ∧
    (let env : Nat → Nat := fun _ => 1
     let l : Tree := .atom 0
     let r : Tree := .unit
     ¬ l.atoms.Perm ([] ++ []) ∧
     r.atoms.Perm ([] ++ []) ∧
     Nat.le (denoteAtoms Nat.add 0 env []) (denoteAtoms Nat.add 0 env []) ∧
     ¬ Nat.le (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) :=
  ⟨natLe_entailsTrans,
   fun x y z => by rw [natAdd_sepAssoc x y z]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
   fun x y => by rw [natAdd_sepComm x y]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
   fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩,
   natAdd_le_sepMonoRight,
   natAdd_tight_commonPerm_leftPerm.2.2.2.2⟩

/-- Canonical tightness of `hr : r.atoms.Perm (common ++ rs)` in
`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`. -/
theorem natAdd_tight_bientails_commonPerm_rightPerm :
    EntailsTrans Nat.le ∧
    SepAssocBientails Nat.add Nat.le ∧
    SepCommBientails Nat.add Nat.le ∧
    RightUnitBientails Nat.add 0 Nat.le ∧
    SepMonoRight Nat.add Nat.le ∧
    (let env : Nat → Nat := fun _ => 1
     let l : Tree := .atom 0
     let r : Tree := .unit
     l.atoms.Perm ([] ++ [0]) ∧
     ¬ r.atoms.Perm ([] ++ [0]) ∧
     Nat.le (denoteAtoms Nat.add 0 env [0]) (denoteAtoms Nat.add 0 env [0]) ∧
     ¬ Nat.le (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) :=
  ⟨natLe_entailsTrans,
   fun x y z => by rw [natAdd_sepAssoc x y z]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
   fun x y => by rw [natAdd_sepComm x y]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
   fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩,
   natAdd_le_sepMonoRight,
   natAdd_tight_commonPerm_rightPerm.2.2.2.2⟩

/-- Canonical tightness of `hResidual` in
`bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`. -/
theorem natAdd_tight_bientails_commonPerm_residual :
    EntailsTrans Nat.le ∧
    SepAssocBientails Nat.add Nat.le ∧
    SepCommBientails Nat.add Nat.le ∧
    RightUnitBientails Nat.add 0 Nat.le ∧
    SepMonoRight Nat.add Nat.le ∧
    (let env : Nat → Nat := fun i => i + 1
     let l : Tree := .atom 1
     let r : Tree := .atom 0
     l.atoms.Perm ([] ++ [1]) ∧
     r.atoms.Perm ([] ++ [0]) ∧
     ¬ Nat.le (denoteAtoms Nat.add 0 env [1]) (denoteAtoms Nat.add 0 env [0]) ∧
     ¬ Nat.le (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) :=
  ⟨natLe_entailsTrans,
   fun x y z => by rw [natAdd_sepAssoc x y z]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
   fun x y => by rw [natAdd_sepComm x y]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
   fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩,
   natAdd_le_sepMonoRight,
   natAdd_tight_commonPerm_residual.2.2.2.2⟩

/-! ## Result 4d: Converse failure of maximal cancellation (linear, affine, and partial vs maximal) -/

/-- **Maximal cancellation converse failure in a linear single-cell conflict model:**
In `(CellModel, CellModel.sep, .empty, CellModel.entails)`, all ACU, preorder, and
monotonicity laws hold (while `AffineEntails` fails: `owned ⊬ empty`). The goal
`(owned ∗ owned) ⊢ owned` holds because `owned ∗ owned = conflict`, yet maximal
cancellation (`cancelAtoms`) produces the false residual `owned ⊢ empty`. -/
theorem cellModel_cancelAtoms_converse_fails :
    EntailsRefl CellModel.entails ∧
    EntailsTrans CellModel.entails ∧
    SepAssoc CellModel.sep ∧
    SepComm CellModel.sep ∧
    RightUnit CellModel.sep .empty ∧
    SepMonoRight CellModel.sep CellModel.entails ∧
    ¬ AffineEntails CellModel.empty CellModel.entails ∧
    (let env : Nat → CellModel := fun _ => .owned
     let l : Tree := .node (.atom 0) (.atom 0)
     let r : Tree := .atom 0
     CellModel.entails
       (l.denote CellModel.sep .empty env)
       (r.denote CellModel.sep .empty env) ∧
     ¬ CellModel.entails
       (denoteAtoms CellModel.sep .empty env (cancelAtoms l.atoms r.atoms).1)
       (denoteAtoms CellModel.sep .empty env (cancelAtoms l.atoms r.atoms).2)) := by
  refine ⟨cellModel_entailsRefl, cellModel_entailsTrans,
    cellModel_sepAssoc, cellModel_sepComm, cellModel_rightUnit,
    cellModel_sepMonoRight, cellModel_not_affineEntails, ⟨trivial, ?_⟩⟩
  intro h
  exact h

/-- **Affine control on `CellModel`:** under the affine order `affineCellEntails`
(`AffineEntails CellModel.empty affineCellEntails`), the residual `owned ⊢ empty` of
`cellModel_cancelAtoms_converse_fails` becomes valid, showing why a single-cell linear
witness does not transfer directly to affine separation logics. -/
theorem affineCellEntails_residual_holds :
    EntailsRefl affineCellEntails ∧
    EntailsTrans affineCellEntails ∧
    SepMonoRight CellModel.sep affineCellEntails ∧
    AffineEntails CellModel.empty affineCellEntails ∧
    (let env : Nat → CellModel := fun _ => .owned
     let l : Tree := .node (.atom 0) (.atom 0)
     let r : Tree := .atom 0
     affineCellEntails
       (l.denote CellModel.sep .empty env)
       (r.denote CellModel.sep .empty env) ∧
     affineCellEntails
       (denoteAtoms CellModel.sep .empty env (cancelAtoms l.atoms r.atoms).1)
       (denoteAtoms CellModel.sep .empty env (cancelAtoms l.atoms r.atoms).2)) := by
  refine ⟨?_, ?_, ?_, ?_, trivial, trivial⟩
  · intro x; cases x <;> trivial
  · intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;> first | trivial | cases hxy | cases hyz
  · intro f x y hxy
    cases f <;> cases x <;> cases y <;> first | trivial | cases hxy
  · intro x; cases x <;> trivial

/-- **Maximal cancellation converse failure in an affine two-cell conflict model:**
In `(TwoCellModel, TwoCellModel.sep, .empty, TwoCellModel.entails)`, all ACU, preorder,
monotonicity, AND affinity laws hold (`AffineEntails TwoCellModel.empty TwoCellModel.entails`).
At `env 0 = .cellA`, `env 1 = .cellB`, `l = atom 0 ∗ atom 0`, `r = atom 0 ∗ atom 1`, the
original entailment `conflict ⊢ both` holds, yet maximal cancellation (`cancelAtoms`)
produces the false non-`emp` residual `cellA ⊢ cellB`. -/
theorem twoCellModel_affine_cancelAtoms_converse_fails :
    SepAssoc TwoCellModel.sep ∧
    SepComm TwoCellModel.sep ∧
    RightUnit TwoCellModel.sep .empty ∧
    EntailsRefl TwoCellModel.entails ∧
    EntailsTrans TwoCellModel.entails ∧
    SepMonoRight TwoCellModel.sep TwoCellModel.entails ∧
    AffineEntails TwoCellModel.empty TwoCellModel.entails ∧
    (let env : Nat → TwoCellModel := fun i => if i == 0 then .cellA else .cellB
     let l : Tree := .node (.atom 0) (.atom 0)
     let r : Tree := .node (.atom 0) (.atom 1)
     TwoCellModel.entails
       (l.denote TwoCellModel.sep .empty env)
       (r.denote TwoCellModel.sep .empty env) ∧
     ¬ TwoCellModel.entails
       (denoteAtoms TwoCellModel.sep .empty env (cancelAtoms l.atoms r.atoms).1)
       (denoteAtoms TwoCellModel.sep .empty env (cancelAtoms l.atoms r.atoms).2)) := by
  refine ⟨twoCellModel_sepAssoc, twoCellModel_sepComm, twoCellModel_rightUnit,
    twoCellModel_entailsRefl, twoCellModel_entailsTrans, twoCellModel_sepMonoRight,
    twoCellModel_affineEntails, ?_⟩
  unfold TwoCellModel.entails
  decide

/-- **Partial cancellation succeeds where maximal `cancelAtoms` fails:**
In `CellModel` with `env _ = .owned`, `l = ((atom 0 ∗ atom 0) ∗ atom 0)`, and
`r = (atom 0 ∗ atom 0)`:
- maximal cancellation (`cancelAtoms`) cancels `[0, 0]` and leaves the **false** residual
  `owned ⊢ empty`;
- cancelling only the smaller common sub-multiset `common = [0]` leaves the **true**
  residual `conflict ⊢ owned` (covered by `acu_entails_of_common_perm_of_sepMonoRight`). -/
theorem partial_cancellation_succeeds_where_cancelAtoms_fails :
    let env : Nat → CellModel := fun _ => .owned
    let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 0)
    let r : Tree := .node (.atom 0) (.atom 0)
    ¬ CellModel.entails
        (denoteAtoms CellModel.sep .empty env (cancelAtoms l.atoms r.atoms).1)
        (denoteAtoms CellModel.sep .empty env (cancelAtoms l.atoms r.atoms).2) ∧
    l.atoms.Perm ([0] ++ [0, 0]) ∧
    r.atoms.Perm ([0] ++ [0]) ∧
    CellModel.entails
      (denoteAtoms CellModel.sep .empty env [0, 0])
      (denoteAtoms CellModel.sep .empty env [0]) := by
  refine ⟨?_, List.Perm.refl _, List.Perm.refl _, trivial⟩
  intro h
  exact h

end Toy.SepAC
