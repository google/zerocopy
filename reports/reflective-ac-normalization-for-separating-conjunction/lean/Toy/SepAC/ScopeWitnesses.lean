import Toy.SepAC.Entailment

/-!
# Scope witnesses

Concrete, fully proved instances that delimit the scope of claims made about the other
modules:

* Two-element models (and the three-state `CellModel` under `affineCellEntails`) in which
  maximal cancellation `cancelAtoms` is already not invertible. The `CellModel` and
  `TwoCellModel` witnesses of `R4d` are therefore illustrative, not minimal.
* A non-idempotent ACU model with an absorbing element in which `List.isPerm` is still
  complete for one fixed generator environment, so incompleteness in such models holds
  only for some environments.
* Counterexamples in the canonical form "all other hypotheses hold and the conclusion
  fails" for the hypotheses of the `cancelAtoms` corollaries
  `acu_entails_of_cancelAtoms_of_sepMonoRight` and
  `bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`.
* Non-vacuity witnesses (all hypotheses hold together) for those two corollaries and for
  `unitCount_eq_and_isPerm_of_forall_ac_denote_eq`.
-/

namespace Toy.SepAC

/-! ## Two-element and single-cell witnesses for non-invertible maximal cancellation -/

/-- Implication order on `Bool`: `x` entails `y` iff `x = true` implies `y = true`. -/
def boolImp (x y : Bool) : Prop := x = true → y = true

/-- Positive example: `false` entails `true` under `boolImp`. -/
theorem boolImp_pos_example : boolImp false true := fun _ => rfl

/-- Negative example: `true` does not entail `false` under `boolImp`. -/
theorem boolImp_neg_example : ¬ boolImp true false := fun h => Bool.noConfusion (h rfl)

/-- **Linear two-element witness:** in `(Bool, Bool.or, false)` with the implication order,
all ACU, preorder, and right-monotonicity laws hold and `AffineEntails` fails, yet
`(atom 0 ∗ atom 0) ⊢ (atom 0 ∗ atom 1)` holds at `env 0 = true`, `env 1 = false` while the
`cancelAtoms` residual `true ⊢ false` fails. -/
theorem boolOr_linear_cancelAtoms_converse_fails :
    EntailsRefl boolImp ∧ EntailsTrans boolImp ∧ SepAssoc Bool.or ∧ SepComm Bool.or ∧
    RightUnit Bool.or false ∧ SepMonoRight Bool.or boolImp ∧ ¬ AffineEntails false boolImp ∧
    (let env : Nat → Bool := fun i => if i == 0 then true else false
     let l : Tree := .node (.atom 0) (.atom 0)
     let r : Tree := .node (.atom 0) (.atom 1)
     boolImp (l.denote Bool.or false env) (r.denote Bool.or false env) ∧
     ¬ boolImp (denoteAtoms Bool.or false env (cancelAtoms l.atoms r.atoms).1)
               (denoteAtoms Bool.or false env (cancelAtoms l.atoms r.atoms).2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x h; exact h
  · intro x y z h1 h2 h; exact h2 (h1 h)
  · intro x y z; cases x <;> cases y <;> cases z <;> rfl
  · intro x y; cases x <;> cases y <;> rfl
  · intro x; cases x <;> rfl
  · intro f x y h; cases f <;> cases x <;> cases y <;> simp_all [boolImp]
  · intro h; have := h true rfl; cases this
  · refine ⟨?_, ?_⟩
    · intro _; rfl
    · intro h; have := h rfl; cases this

/-- **Affine two-element witness:** in `(Bool, Bool.and, true)` with the implication order
(every element entails the unit `true`), all ACU, preorder, right-monotonicity, and
`AffineEntails` laws hold, yet `(atom 0 ∗ atom 1) ⊢ (atom 0 ∗ atom 0)` holds at
`env 0 = false`, `env 1 = true` while the `cancelAtoms` residual `true ⊢ false` fails. -/
theorem boolAnd_affine_cancelAtoms_converse_fails :
    EntailsRefl boolImp ∧ EntailsTrans boolImp ∧ SepAssoc Bool.and ∧ SepComm Bool.and ∧
    RightUnit Bool.and true ∧ SepMonoRight Bool.and boolImp ∧ AffineEntails true boolImp ∧
    (let env : Nat → Bool := fun i => if i == 0 then false else true
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .node (.atom 0) (.atom 0)
     boolImp (l.denote Bool.and true env) (r.denote Bool.and true env) ∧
     ¬ boolImp (denoteAtoms Bool.and true env (cancelAtoms l.atoms r.atoms).1)
               (denoteAtoms Bool.and true env (cancelAtoms l.atoms r.atoms).2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x h; exact h
  · intro x y z h1 h2 h; exact h2 (h1 h)
  · intro x y z; cases x <;> cases y <;> cases z <;> rfl
  · intro x y; cases x <;> cases y <;> rfl
  · intro x; cases x <;> rfl
  · intro f x y h; cases f <;> cases x <;> cases y <;> simp_all [boolImp]
  · intro x _; rfl
  · refine ⟨?_, ?_⟩
    · intro h; cases h
    · intro h; have := h rfl; cases this

/-- **Affine witness in the three-state single-cell model:** under `affineCellEntails`
(every state entails `empty`), all ACU, preorder, right-monotonicity, and `AffineEntails`
laws hold, yet at `env = fun _ => owned` the goal `(0 ∗ 0) ⊢ ((0 ∗ 0) ∗ 0)` holds
(`conflict ⊢ conflict`) while the `cancelAtoms` residual `empty ⊢ owned` fails. -/
theorem cellModel_affine_cancelAtoms_converse_fails :
    EntailsRefl affineCellEntails ∧ EntailsTrans affineCellEntails ∧
    SepAssoc CellModel.sep ∧ SepComm CellModel.sep ∧ RightUnit CellModel.sep CellModel.empty ∧
    SepMonoRight CellModel.sep affineCellEntails ∧
    AffineEntails CellModel.empty affineCellEntails ∧
    (let env : Nat → CellModel := fun _ => .owned
     let l : Tree := .node (.atom 0) (.atom 0)
     let r : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 0)
     affineCellEntails (l.denote CellModel.sep CellModel.empty env)
       (r.denote CellModel.sep CellModel.empty env) ∧
     ¬ affineCellEntails
         (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).1)
         (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).2)) := by
  obtain ⟨hR, hT, hM, hA, -⟩ := affineCellEntails_residual_holds
  obtain ⟨hAs, hC, hRU, -⟩ := acu_denote_eq_of_isPerm_nonvacuous
  refine ⟨hR, hT, hAs, hC, hRU, hM, hA, ?_⟩
  refine ⟨?_, ?_⟩
  · simp [Tree.denote, CellModel.sep, affineCellEntails]
  · simp [Tree.atoms, cancelAtoms, denoteAtoms, CellModel.sep, affineCellEntails]

/-! ## An absorbing element does not by itself break completeness -/

/-- `Bag` with an adjoined absorbing element `none`: `some a ∗ some b = some (a ∗ b)`, and
any product involving `none` is `none`. -/
def optBagSep : Option Bag → Option Bag → Option Bag
  | some a, some b => some (Bag.sep a b)
  | _, _ => none

/-- Under the generator environment `fun i => some (Bag.single i)`, every tree denotes
`some` of its `Bag` denotation; the absorbing element is never reached. -/
theorem optBag_denote (t : Tree) :
    t.denote optBagSep (some Bag.emp) (fun i => some (Bag.single i)) =
      some (t.denote Bag.sep Bag.emp Bag.single) := by
  induction t with
  | atom i => rfl
  | unit => rfl
  | node l r ihl ihr => simp [Tree.denote, ihl, ihr, optBagSep]

/-- **Absorbing but complete for one environment:** `optBagSep` has the absorbing element
`none`, the generator `some (Bag.single 0)` is not pointwise idempotent, and `List.isPerm`
is complete for the fixed environment `fun i => some (Bag.single i)`. -/
theorem optBag_absorbing_but_complete :
    (∀ x, optBagSep none x = none ∧ optBagSep x none = none) ∧
    ¬ IdemElem optBagSep (some (Bag.single 0)) ∧
    ∀ l r : Tree,
      l.denote optBagSep (some Bag.emp) (fun i => some (Bag.single i)) =
        r.denote optBagSep (some Bag.emp) (fun i => some (Bag.single i)) →
      l.atoms.isPerm r.atoms = true := by
  refine ⟨?_, ?_, ?_⟩
  · intro x; cases x <;> simp [optBagSep]
  · intro h
    have h' : Bag.sep (Bag.single 0) (Bag.single 0) = Bag.single 0 := by
      simpa [IdemElem, optBagSep] using h
    have := congrArg (fun b => b.count 0) h'
    simp [Bag.sep, Bag.single] at this
  · intro l r h
    rw [optBag_denote, optBag_denote] at h
    exact isPerm_of_bag_denote_eq (Option.some.inj h)

/-! ## Tightness of the hypotheses of the `cancelAtoms` corollaries

Each statement below has the form "all other hypotheses of the corollary hold and the
conclusion fails". In every case the trees are those of the corresponding counterexample
for the common-sub-multiset theorem, and `cancelAtoms l.atoms r.atoms` evaluates to the
`(ls, rs)` pair used there. -/

/-- Tightness of `SepAssoc sep` in `acu_entails_of_cancelAtoms_of_sepMonoRight`. -/
theorem nonAssoc_tight_cancelAtoms_sepAssoc :
    SepComm NonAssocCarrier.op ∧
    RightUnit NonAssocCarrier.op .emp ∧
    SepMonoRight NonAssocCarrier.op Eq ∧
    (let env : Nat → NonAssocCarrier := fun i => if i == 0 then .a else .b
     let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 1)
     let r : Tree := .node (.atom 0) (.node (.atom 0) (.atom 1))
     denoteAtoms NonAssocCarrier.op .emp env (cancelAtoms l.atoms r.atoms).1 =
       denoteAtoms NonAssocCarrier.op .emp env (cancelAtoms l.atoms r.atoms).2 ∧
     l.denote NonAssocCarrier.op .emp env ≠ r.denote NonAssocCarrier.op .emp env) := by
  obtain ⟨h1, h2, h3, h4⟩ := nonAssoc_tight_commonPerm_sepAssoc
  exact ⟨h1, h2, h3, rfl, h4.2.2.2⟩

/-- Tightness of `SepComm sep` in `acu_entails_of_cancelAtoms_of_sepMonoRight`. -/
theorem listAppend_tight_cancelAtoms_sepComm :
    SepAssoc (@List.append Nat) ∧
    RightUnit (@List.append Nat) [] ∧
    SepMonoRight (@List.append Nat) Eq ∧
    (let env : Nat → List Nat := fun i => [i]
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .node (.atom 1) (.atom 0)
     denoteAtoms List.append [] env (cancelAtoms l.atoms r.atoms).1 =
       denoteAtoms List.append [] env (cancelAtoms l.atoms r.atoms).2 ∧
     l.denote List.append [] env ≠ r.denote List.append [] env) := by
  obtain ⟨h1, h2, h3, h4⟩ := listAppend_tight_commonPerm_sepComm
  exact ⟨h1, h2, h3, rfl, h4.2.2.2⟩

/-- Tightness of `RightUnit sep emp` in `acu_entails_of_cancelAtoms_of_sepMonoRight`. -/
theorem boolAndFalse_tight_cancelAtoms_rightUnit :
    SepAssoc Bool.and ∧
    SepComm Bool.and ∧
    SepMonoRight Bool.and Eq ∧
    (let env : Nat → Bool := fun _ => true
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) .unit
     denoteAtoms Bool.and false env (cancelAtoms l.atoms r.atoms).1 =
       denoteAtoms Bool.and false env (cancelAtoms l.atoms r.atoms).2 ∧
     l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  obtain ⟨h1, h2, h3, h4⟩ := boolAndFalse_tight_commonPerm_rightUnit
  exact ⟨h1, h2, h3, rfl, h4.2.2.2⟩

/-- Tightness of the residual hypothesis in `acu_entails_of_cancelAtoms_of_sepMonoRight`. -/
theorem natAdd_tight_cancelAtoms_residual :
    SepAssoc Nat.add ∧
    SepComm Nat.add ∧
    RightUnit Nat.add 0 ∧
    SepMonoRight Nat.add Nat.le ∧
    (let env : Nat → Nat := fun i => i + 1
     let l : Tree := .atom 1
     let r : Tree := .atom 0
     ¬ Nat.le (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).1)
         (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).2) ∧
     ¬ Nat.le (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := natAdd_tight_commonPerm_residual
  exact ⟨h1, h2, h3, h4, h5.2.2.1, h5.2.2.2⟩

/-- Tightness of `EntailsTrans entails` in
`bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`. -/
theorem tagDistLeOne_tight_bientails_cancelAtoms_trans :
    SepAssocBientails taggedSep tagDistLeOne ∧
    SepCommBientails taggedSep tagDistLeOne ∧
    RightUnitBientails taggedSep taggedEmp tagDistLeOne ∧
    SepMonoRight taggedSep tagDistLeOne ∧
    (let env : Nat → TaggedNat := fun _ => (1, 0)
     let l : Tree := .atom 0
     let r : Tree := .node (.node (.atom 0) .unit) .unit
     tagDistLeOne (denoteAtoms taggedSep taggedEmp env (cancelAtoms l.atoms r.atoms).1)
       (denoteAtoms taggedSep taggedEmp env (cancelAtoms l.atoms r.atoms).2) ∧
     ¬ tagDistLeOne (l.denote taggedSep taggedEmp env) (r.denote taggedSep taggedEmp env)) := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := tagDistLeOne_tight_bientails_commonPerm_trans
  exact ⟨h1, h2, h3, h4, h5.2.2.1, h5.2.2.2⟩

/-- Tightness of `SepAssocBientails sep entails` in
`bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`. -/
theorem nonAssoc_tight_bientails_cancelAtoms_sepAssoc :
    EntailsTrans (@Eq NonAssocCarrier) ∧
    SepCommBientails NonAssocCarrier.op Eq ∧
    RightUnitBientails NonAssocCarrier.op .emp Eq ∧
    SepMonoRight NonAssocCarrier.op Eq ∧
    (let env : Nat → NonAssocCarrier := fun i => if i == 0 then .a else .b
     let l : Tree := .node (.node (.atom 0) (.atom 0)) (.atom 1)
     let r : Tree := .node (.atom 0) (.node (.atom 0) (.atom 1))
     denoteAtoms NonAssocCarrier.op .emp env (cancelAtoms l.atoms r.atoms).1 =
       denoteAtoms NonAssocCarrier.op .emp env (cancelAtoms l.atoms r.atoms).2 ∧
     l.denote NonAssocCarrier.op .emp env ≠ r.denote NonAssocCarrier.op .emp env) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := nonAssoc_tight_bientails_commonPerm_sepAssoc
  exact ⟨h1, h2, h3, h4, rfl, h5.2.2.2⟩

/-- Tightness of `SepCommBientails sep entails` in
`bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`. -/
theorem listAppend_tight_bientails_cancelAtoms_sepComm :
    EntailsTrans (@Eq (List Nat)) ∧
    SepAssocBientails (@List.append Nat) Eq ∧
    RightUnitBientails (@List.append Nat) [] Eq ∧
    SepMonoRight (@List.append Nat) Eq ∧
    (let env : Nat → List Nat := fun i => [i]
     let l : Tree := .node (.atom 0) (.atom 1)
     let r : Tree := .node (.atom 1) (.atom 0)
     denoteAtoms List.append [] env (cancelAtoms l.atoms r.atoms).1 =
       denoteAtoms List.append [] env (cancelAtoms l.atoms r.atoms).2 ∧
     l.denote List.append [] env ≠ r.denote List.append [] env) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := listAppend_tight_bientails_commonPerm_sepComm
  exact ⟨h1, h2, h3, h4, rfl, h5.2.2.2⟩

/-- Tightness of `RightUnitBientails sep emp entails` in
`bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`. -/
theorem boolAndFalse_tight_bientails_cancelAtoms_rightUnit :
    EntailsTrans (@Eq Bool) ∧
    SepAssocBientails Bool.and Eq ∧
    SepCommBientails Bool.and Eq ∧
    SepMonoRight Bool.and Eq ∧
    (let env : Nat → Bool := fun _ => true
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) .unit
     denoteAtoms Bool.and false env (cancelAtoms l.atoms r.atoms).1 =
       denoteAtoms Bool.and false env (cancelAtoms l.atoms r.atoms).2 ∧
     l.denote Bool.and false env ≠ r.denote Bool.and false env) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := boolAndFalse_tight_bientails_commonPerm_rightUnit
  exact ⟨h1, h2, h3, h4, rfl, h5.2.2.2⟩

/-- Tightness of `SepMonoRight sep entails` in
`bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`. -/
theorem capOne_tight_bientails_cancelAtoms_sepMonoRight :
    EntailsTrans capOneEntails ∧
    SepAssocBientails Nat.add capOneEntails ∧
    SepCommBientails Nat.add capOneEntails ∧
    RightUnitBientails Nat.add 0 capOneEntails ∧
    ¬ SepMonoRight Nat.add capOneEntails ∧
    (let env : Nat → Nat := fun _ => 1
     let l : Tree := .atom 0
     let r : Tree := .node (.atom 0) (.atom 0)
     capOneEntails (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).1)
       (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).2) ∧
     ¬ capOneEntails (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := capOne_tight_bientails_commonPerm_sepMonoRight
  exact ⟨h1, h2, h3, h4, h5, h6.2.2.1, h6.2.2.2⟩

/-- Tightness of the residual hypothesis in
`bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`. -/
theorem natAdd_tight_bientails_cancelAtoms_residual :
    EntailsTrans Nat.le ∧
    SepAssocBientails Nat.add Nat.le ∧
    SepCommBientails Nat.add Nat.le ∧
    RightUnitBientails Nat.add 0 Nat.le ∧
    SepMonoRight Nat.add Nat.le ∧
    (let env : Nat → Nat := fun i => i + 1
     let l : Tree := .atom 1
     let r : Tree := .atom 0
     ¬ Nat.le (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).1)
         (denoteAtoms Nat.add 0 env (cancelAtoms l.atoms r.atoms).2) ∧
     ¬ Nat.le (l.denote Nat.add 0 env) (r.denote Nat.add 0 env)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := natAdd_tight_bientails_commonPerm_residual
  exact ⟨h1, h2, h3, h4, h5, h6.2.2.1, h6.2.2.2⟩

/-! ## Non-vacuity of the hypotheses of supporting theorems -/

/-- **Non-vacuity of `unitCount_eq_and_isPerm_of_forall_ac_denote_eq`:** the distinct trees
`atom 0 ∗ unit` and `unit ∗ atom 0` denote equally in every associative-commutative model,
for every `emp` and every environment. -/
theorem unitCount_converse_hypothesis_nonvacuous :
    let l : Tree := .node (.atom 0) .unit
    let r : Tree := .node .unit (.atom 0)
    l ≠ r ∧
    ∀ (P : Type) (sep : P → P → P) (emp : P), SepAssoc sep → SepComm sep →
      ∀ env : Nat → P, l.denote sep emp env = r.denote sep emp env := by
  intro l r
  refine ⟨by decide, ?_⟩
  intro P sep emp hA hC env
  exact ac_denote_eq_of_unitCount_eq_of_isPerm sep emp hA hC env rfl rfl

/-- **Non-vacuity of `acu_entails_of_cancelAtoms_of_sepMonoRight`:** in `CellModel` with the
affine order `affineCellEntails`, all hypotheses hold for `l = atom 0 ∗ atom 0`, `r = atom 0`
at `env = fun _ => owned`, including the `cancelAtoms` residual `owned ⊢ empty`. -/
theorem acu_entails_of_cancelAtoms_nonvacuous :
    SepAssoc CellModel.sep ∧ SepComm CellModel.sep ∧ RightUnit CellModel.sep CellModel.empty ∧
    SepMonoRight CellModel.sep affineCellEntails ∧
    (let env : Nat → CellModel := fun _ => .owned
     let l : Tree := .node (.atom 0) (.atom 0)
     let r : Tree := .atom 0
     affineCellEntails
       (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).1)
       (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).2)) := by
  obtain ⟨-, -, hM, -, h⟩ := affineCellEntails_residual_holds
  obtain ⟨hAs, hC, hRU, -⟩ := acu_denote_eq_of_isPerm_nonvacuous
  exact ⟨hAs, hC, hRU, hM, h.2⟩

/-- **Non-vacuity of `bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight`:** the same
`CellModel` instance with `affineCellEntails` satisfies `EntailsTrans`, the three `Bientails`
ACU laws, `SepMonoRight`, and the `cancelAtoms` residual. -/
theorem bientails_acu_entails_of_cancelAtoms_nonvacuous :
    EntailsTrans affineCellEntails ∧
    SepAssocBientails CellModel.sep affineCellEntails ∧
    SepCommBientails CellModel.sep affineCellEntails ∧
    RightUnitBientails CellModel.sep CellModel.empty affineCellEntails ∧
    SepMonoRight CellModel.sep affineCellEntails ∧
    (let env : Nat → CellModel := fun _ => .owned
     let l : Tree := .node (.atom 0) (.atom 0)
     let r : Tree := .atom 0
     affineCellEntails
       (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).1)
       (denoteAtoms CellModel.sep CellModel.empty env (cancelAtoms l.atoms r.atoms).2)) := by
  obtain ⟨hR, hT, hM, -, h⟩ := affineCellEntails_residual_holds
  obtain ⟨hAs, hC, hRU, -⟩ := acu_denote_eq_of_isPerm_nonvacuous
  refine ⟨hT, ?_, ?_, ?_, hM, h.2⟩
  · intro x y z; rw [hAs x y z]; exact ⟨hR _, hR _⟩
  · intro x y; rw [hC x y]; exact ⟨hR _, hR _⟩
  · intro x; rw [hRU x]; exact ⟨hR _, hR _⟩

end Toy.SepAC
