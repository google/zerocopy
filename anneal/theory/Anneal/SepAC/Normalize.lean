-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Anneal.PureLift.LoanGraph
public import Anneal.PureLift.SpatialPin

public section

/-!
# Reflective ACU Separating-Conjunction Normalization (`Normalize`)

Zero-TCB, metaprogramming-free reflective ACU normalization and deterministic
multiset cancellation for separating conjunctions (`∗`) over arbitrary 6-law
preorders without requiring PCM-level equality or `funext` quotients.

**Relationship to `Anneal.Core.SepPCM`:** `Anneal.Core.SepPCM` provides
boolean-certificate AC reflection (`sepAC_equiv_of_boolCertCut`, scaling to
256-atom PCM goals) for `ExplPCM`-backed `SepProp`. `Anneal.SepAC.Normalize`
complements it by generalizing ACU normalization and pairwise cancellation to
arbitrary `(sep, emp, entails)` preorders—including list-backed carriers such
as `PermSpatialProp` whose underlying lists do not satisfy `h₁ ++ h₂ = h₂ ++
h₁`—while `Anneal.SepAC.RangeSpan` also supplies a `SepACULaws` instance for
`Anneal.Core.SepProp`. Closing `normSepFuel` directly by `rfl` (insertion sort)
scales up to ~48–56 reversed atoms at Lean's default `maxRecDepth`; larger
PCM goals should use `Anneal.Core.SepPCM.sepAC_equiv_of_boolCertCut`.

1. **Unbundled Separation-Algebra Laws (`SepACULaws`):**
   - `EntailsRefl`, `EntailsTrans`, `SepMonoRight`, `SepMonoLeft`,
     `AffineEntails`, `Bientails`, `SepAssocBientails`, `SepCommBientails`,
     `RightUnitBientails`, and `LeftUnitBientails`.
   - `SepACULaws sep emp entails` bundles the minimal core (`refl`, `trans`,
     `monoRight`, `assoc`, `comm`, `rightUnit`) and derives `SepMonoLeft`,
     `LeftUnitBientails`, and `Bientails` congruence (`sep_bientails_congr`).
2. **Deep-Embedded `SepExpr`, Canonical Sorting, & Reflective ACU Soundness:**
   - `SepExpr` (`emp | atom idx | sep l r`), fuel-indexed `evalSepExprFuel` and
     `flattenSepFuel` (`@Nat.rec`), `evalAtomList` (`List.foldr`),
     `insertSortedNat` (`List.foldr`), `sortNatList` (`List.foldr`), and
     `normSepFuel` (`0` `noncomputable`, `0` `._unsafe_rec`).
   - Constructive `ListPerm` (`[]` zero axioms) proves
     `evalAtomList_perm_bientails`, `evalSepExprFuel_norm_bientails`, and
     `sepAC_bientails_of_norm_eq`: any two `SepExpr` trees with
     `normSepFuel fuel e₁ = normSepFuel fuel e₂` are mutually entailing by
     `rfl`.
3. **Executable Pairwise Multiset Cancellation (`cancelAtoms`):**
   - `containsNat`, `eraseFirstNat` (`List.foldr`), and `cancelAtoms`
     (`List.foldr`, `0` `._unsafe_rec`) with constructive decomposition
     `cancelAtoms_spec`.
   - `sepAC_entails_of_cancelAtoms`: reduces `evalSepExprFuel ... lhs ⊢
     evalSepExprFuel ... rhs` to entailment between the uncancelled residuals.
   - `sepAC_affine_entails_of_cancel_nil`: under `AffineEntails`, closes
     entailment directly by `rfl` whenever `(cancelAtoms ...).2 = []`.
4. **`Anneal.PureLift.SpatialProp` Linear Separation-Algebra Bridge:**
   - `PermSpatialProp Val` (permutation-closed `SpatialProp Val`),
     `PermSpatialEntails`, `permSpatialEmp`, `permSpatialPointsTo` (`[propext]`
     only), `permSpatialSepConj` (lifting `Anneal.PureLift.spatialSepConj`),
     `permSpatialSepConj_of_spatialSepConj`, `permSpatialProp_sepACULaws`, and
     `not_affineEntails_permSpatialProp` (`[propext]` only).

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and every authored declaration
compiles using at most `[propext]` (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.SepAC

open Anneal.PureLift

/-! ## Part I: Unbundled Separation-Algebra Laws -/

/-- Reflexivity of entailment: `x ⊢ x`. -/
@[expose] def EntailsRefl {P : Type} (entails : P → P → Prop) : Prop :=
  ∀ x : P, entails x x

/-- Transitivity of entailment: `x ⊢ y → y ⊢ z → x ⊢ z`. -/
@[expose] def EntailsTrans {P : Type} (entails : P → P → Prop) : Prop :=
  ∀ x y z : P, entails x y → entails y z → entails x z

/-- Right monotonicity (left framing) of `sep`: `x ⊢ y → f ∗ x ⊢ f ∗ y`. -/
@[expose] def SepMonoRight {P : Type} (sep : P → P → P)
    (entails : P → P → Prop) : Prop :=
  ∀ f x y : P, entails x y → entails (sep f x) (sep f y)

/-- Left monotonicity (right framing) of `sep`: `x ⊢ y → x ∗ f ⊢ y ∗ f`. -/
@[expose] def SepMonoLeft {P : Type} (sep : P → P → P)
    (entails : P → P → Prop) : Prop :=
  ∀ x y f : P, entails x y → entails (sep x f) (sep y f)

/-- Affinity (weakening to `emp`): `∀ x, x ⊢ emp`. -/
@[expose] def AffineEntails {P : Type} (emp : P)
    (entails : P → P → Prop) : Prop :=
  ∀ x : P, entails x emp

/-- Mutual entailment (`x ⊣⊢ y`): `entails x y ∧ entails y x`. -/
@[expose] def Bientails {P : Type} (entails : P → P → Prop) (x y : P) : Prop :=
  entails x y ∧ entails y x

/-- Associativity of `sep` up to `Bientails`. -/
@[expose] def SepAssocBientails {P : Type} (sep : P → P → P)
    (entails : P → P → Prop) : Prop :=
  ∀ x y z : P, Bientails entails (sep (sep x y) z) (sep x (sep y z))

/-- Commutativity of `sep` up to `Bientails`. -/
@[expose] def SepCommBientails {P : Type} (sep : P → P → P)
    (entails : P → P → Prop) : Prop :=
  ∀ x y : P, Bientails entails (sep x y) (sep y x)

/-- Right unit law for `emp` up to `Bientails`. -/
@[expose] def RightUnitBientails {P : Type} (sep : P → P → P) (emp : P)
    (entails : P → P → Prop) : Prop :=
  ∀ x : P, Bientails entails (sep x emp) x

/-- Left unit law for `emp` up to `Bientails`. -/
@[expose] def LeftUnitBientails {P : Type} (sep : P → P → P) (emp : P)
    (entails : P → P → Prop) : Prop :=
  ∀ x : P, Bientails entails (sep emp x) x

/-- Minimal ACU separation-algebra bundle (omitting derivable `SepMonoLeft` and
`LeftUnitBientails`). -/
structure SepACULaws {P : Type} (sep : P → P → P) (emp : P)
    (entails : P → P → Prop) : Prop where
  refl : EntailsRefl entails
  trans : EntailsTrans entails
  monoRight : SepMonoRight sep entails
  assoc : SepAssocBientails sep entails
  comm : SepCommBientails sep entails
  rightUnit : RightUnitBientails sep emp entails

/-- Reflexivity of `Bientails` (`[]` zero axioms). -/
theorem bientails_refl {P : Type} {entails : P → P → Prop}
    (hRefl : EntailsRefl entails) (x : P) : Bientails entails x x :=
  ⟨hRefl x, hRefl x⟩

/-- Symmetry of `Bientails` (`[]` zero axioms). -/
theorem bientails_symm {P : Type} {entails : P → P → Prop} {x y : P}
    (h : Bientails entails x y) : Bientails entails y x :=
  ⟨h.2, h.1⟩

/-- Transitivity of `Bientails` (`[]` zero axioms). -/
theorem bientails_trans {P : Type} {entails : P → P → Prop}
    (hTrans : EntailsTrans entails) {x y z : P}
    (hxy : Bientails entails x y) (hyz : Bientails entails y z) :
    Bientails entails x z :=
  ⟨hTrans x y z hxy.1 hyz.1, hTrans z y x hyz.2 hxy.2⟩

/-- Derives `SepMonoLeft` from `EntailsTrans`, `SepCommBientails`, and
`SepMonoRight` (`[]` zero axioms). -/
theorem sepMonoLeft_of_laws {P : Type} {sep : P → P → P} {emp : P}
    {entails : P → P → Prop} (hL : SepACULaws sep emp entails) :
    SepMonoLeft sep entails := by
  intro x y f hxy
  exact hL.trans (sep x f) (sep f x) (sep y f)
    (hL.comm x f).1
    (hL.trans (sep f x) (sep f y) (sep y f)
      (hL.monoRight f x y hxy)
      (hL.comm f y).1)

/-- Derives `LeftUnitBientails` from `SepACULaws` (`[]` zero axioms). -/
theorem leftUnit_of_laws {P : Type} {sep : P → P → P} {emp : P}
    {entails : P → P → Prop} (hL : SepACULaws sep emp entails) :
    LeftUnitBientails sep emp entails := by
  intro x
  exact bientails_trans hL.trans (hL.comm emp x) (hL.rightUnit x)

/-- Congruence of `sep` with respect to `Bientails` (`[]` zero axioms). -/
theorem sep_bientails_congr {P : Type} {sep : P → P → P} {emp : P}
    {entails : P → P → Prop} (hL : SepACULaws sep emp entails)
    {x₁ x₂ y₁ y₂ : P}
    (hx : Bientails entails x₁ x₂) (hy : Bientails entails y₁ y₂) :
    Bientails entails (sep x₁ y₁) (sep x₂ y₂) := by
  have hML := sepMonoLeft_of_laws hL
  refine ⟨?_, ?_⟩
  · exact hL.trans (sep x₁ y₁) (sep x₂ y₁) (sep x₂ y₂)
      (hML x₁ x₂ y₁ hx.1) (hL.monoRight x₂ y₁ y₂ hy.1)
  · exact hL.trans (sep x₂ y₂) (sep x₁ y₂) (sep x₁ y₁)
      (hML x₂ x₁ y₂ hx.2) (hL.monoRight x₁ y₂ y₁ hy.2)

/-! ## Part II: Constructive List Permutation (`ListPerm`, `[]` Zero Axioms) -/

/-- Constructive inductive list permutation relation (`[]` zero axioms). -/
inductive ListPerm {α : Type} : List α → List α → Prop where
  | nil : ListPerm [] []
  | cons (x : α) {l₁ l₂ : List α} :
      ListPerm l₁ l₂ → ListPerm (x :: l₁) (x :: l₂)
  | swap (x y : α) (l : List α) : ListPerm (y :: x :: l) (x :: y :: l)
  | trans {l₁ l₂ l₃ : List α} :
      ListPerm l₁ l₂ → ListPerm l₂ l₃ → ListPerm l₁ l₃

/-- Reflexivity of `ListPerm` (`[]` zero axioms). -/
theorem listPerm_refl {α : Type} : ∀ l : List α, ListPerm l l
  | [] => .nil
  | x :: xs => .cons x (listPerm_refl xs)

/-- Symmetry of `ListPerm` (`[]` zero axioms). -/
theorem listPerm_symm {α : Type} {l₁ l₂ : List α} (h : ListPerm l₁ l₂) :
    ListPerm l₂ l₁ := by
  induction h with
  | nil => exact .nil
  | cons x _ ih => exact .cons x ih
  | swap x y l => exact .swap y x l
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

/-- Left-append congruence for `ListPerm` (`[]` zero axioms). -/
theorem listPerm_append_left {α : Type} :
    ∀ (zs : List α) {xs ys : List α},
      ListPerm xs ys → ListPerm (zs ++ xs) (zs ++ ys)
  | [], _, _, h => h
  | z :: zs, _, _, h => .cons z (listPerm_append_left zs h)

/-- Right-append congruence for `ListPerm` (`[]` zero axioms). -/
theorem listPerm_append_right {α : Type} {xs ys : List α} (zs : List α)
    (h : ListPerm xs ys) : ListPerm (xs ++ zs) (ys ++ zs) := by
  induction h with
  | nil => exact listPerm_refl zs
  | cons x _ ih => exact .cons x ih
  | swap x y l => exact .swap x y (l ++ zs)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Moving an element across a prefix (`xs ++ x :: ys ~ x :: (xs ++ ys)`, `[]`
zero axioms). -/
theorem listPerm_middle {α : Type} :
    ∀ (x : α) (xs ys : List α), ListPerm (xs ++ x :: ys) (x :: (xs ++ ys))
  | _, [], _ => listPerm_refl _
  | x, z :: xs, ys =>
    .trans (.cons z (listPerm_middle x xs ys)) (.swap x z (xs ++ ys))

private theorem listAppend_nil_sep {α : Type} : ∀ xs : List α, xs ++ [] = xs
  | [] => rfl
  | x :: xs => congrArg (List.cons x) (listAppend_nil_sep xs)

/-- Commutativity of list append up to `ListPerm` (`[]` zero axioms). -/
theorem listPerm_append_comm {α : Type} :
    ∀ (xs ys : List α), ListPerm (xs ++ ys) (ys ++ xs)
  | [], ys => by
    rw [listAppend_nil_sep ys]
    exact listPerm_refl ys
  | x :: xs, ys =>
    .trans (.cons x (listPerm_append_comm xs ys))
      (listPerm_symm (listPerm_middle x ys xs))

/-! ## Part III: Deep-Embedded `SepExpr`, Canonical Sorting, & Cancellation -/

/-- Deep-embedded separating-conjunction syntax tree over atom indices `Nat`. -/
inductive SepExpr where
  | emp
  | atom (idx : Nat)
  | sep (l r : SepExpr)

/-- Computable fuel-bounded denotation of `SepExpr` into `(P, sep, emp)` via
`@Nat.rec` (`0` `noncomputable`, `0` `._unsafe_rec`). For any `fuel` exceeding
the tree depth of `e`, `evalSepExprFuel sep emp env fuel e` unfolds by `rfl`
to the exact separating-conjunction expression. -/
@[expose] def evalSepExprFuel {P : Type} (sep : P → P → P) (emp : P)
    (env : Nat → P) (fuel : Nat) (e : SepExpr) : P :=
  @Nat.rec (fun _ => SepExpr → P)
    (fun _ => emp)
    (fun _ ih expr =>
      match expr with
      | .emp => emp
      | .atom i => env i
      | .sep l r => sep (ih l) (ih r))
    fuel e

/-- Denotation of a flat atom-index list via `List.foldr` (`0`
`._unsafe_rec`). -/
@[expose] def evalAtomList {P : Type} (sep : P → P → P) (emp : P)
    (env : Nat → P) (xs : List Nat) : P :=
  List.foldr (fun idx acc => sep (env idx) acc) emp xs

/-- Computable fuel-bounded flattening of `SepExpr` into its atom-index list
via `@Nat.rec` (`0` `noncomputable`, `0` `._unsafe_rec`). -/
@[expose] def flattenSepFuel (fuel : Nat) (e : SepExpr) : List Nat :=
  @Nat.rec (fun _ => SepExpr → List Nat)
    (fun _ => [])
    (fun _ ih expr =>
      match expr with
      | .emp => []
      | .atom i => [i]
      | .sep l r => ih l ++ ih r)
    fuel e

/-- Paramorphic `List.foldr` helper for `insertSortedNat` (`0`
`._unsafe_rec`). -/
@[expose] def insertSortedNatAux (x : Nat) (xs : List Nat) :
    List Nat × List Nat :=
  List.foldr
    (fun hd acc =>
      (if Nat.ble x hd then x :: hd :: acc.2 else hd :: acc.1, hd :: acc.2))
    ([x], [])
    xs

/-- Inserts `x` into a sorted `List Nat` via `List.foldr` (`0` `noncomputable`,
`0` `._unsafe_rec`). -/
@[expose] def insertSortedNat (x : Nat) (xs : List Nat) : List Nat :=
  (insertSortedNatAux x xs).1

/-- Sorts a `List Nat` canonically via `List.foldr insertSortedNat` (`0`
`._unsafe_rec`). -/
@[expose] def sortNatList (xs : List Nat) : List Nat :=
  List.foldr insertSortedNat [] xs

/-- Canonical ACU normal form of a `SepExpr` at depth bound `fuel` (`0`
`._unsafe_rec`). -/
@[expose] def normSepFuel (fuel : Nat) (e : SepExpr) : List Nat :=
  sortNatList (flattenSepFuel fuel e)

/-- Computable membership test on `List Nat` via `List.foldr` (`0`
`._unsafe_rec`). -/
@[expose] def containsNat (x : Nat) (ys : List Nat) : Bool :=
  List.foldr (fun y ih => Nat.beq x y || ih) false ys

/-- Paramorphic `List.foldr` helper for `eraseFirstNat` (`0`
`._unsafe_rec`). -/
@[expose] def eraseFirstNatAux (x : Nat) (ys : List Nat) :
    List Nat × List Nat :=
  List.foldr
    (fun y acc =>
      (if Nat.beq x y then acc.2 else y :: acc.1, y :: acc.2))
    ([], [])
    ys

/-- Computable first-occurrence erasure on `List Nat` via `List.foldr` (`0`
`noncomputable`, `0` `._unsafe_rec`). -/
@[expose] def eraseFirstNat (x : Nat) (ys : List Nat) : List Nat :=
  (eraseFirstNatAux x ys).1

/-- Executable maximal sub-multiset cancellation on atom-index lists via
`List.foldr` (`0` `._unsafe_rec`): removes one occurrence of each shared index
and returns `(residualLhs, residualRhs)`. -/
@[expose] def cancelAtoms (xs ys : List Nat) : List Nat × List Nat :=
  List.foldr
    (fun x ih ys' =>
      if containsNat x ys' then
        ih (eraseFirstNat x ys')
      else
        let res := ih ys'
        (x :: res.1, res.2))
    (fun ys' => ([], ys'))
    xs ys

private theorem natEq_of_beq_sep : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (natEq_of_beq_sep h)

private theorem insertSortedNatAux_snd (x : Nat) :
    ∀ xs : List Nat, (insertSortedNatAux x xs).2 = xs
  | [] => rfl
  | hd :: tl => congrArg (List.cons hd) (insertSortedNatAux_snd x tl)

private theorem eraseFirstNatAux_snd (x : Nat) :
    ∀ ys : List Nat, (eraseFirstNatAux x ys).2 = ys
  | [] => rfl
  | y :: yt => congrArg (List.cons y) (eraseFirstNatAux_snd x yt)

/-- `insertSortedNat x xs` is a permutation of `x :: xs` (`[]` zero axioms). -/
theorem listPerm_insertSortedNat (x : Nat) :
    ∀ xs : List Nat, ListPerm (insertSortedNat x xs) (x :: xs)
  | [] => listPerm_refl [x]
  | hd :: tl => by
    change ListPerm
      (if Nat.ble x hd then
        x :: hd :: (insertSortedNatAux x tl).2
      else
        hd :: (insertSortedNatAux x tl).1)
      (x :: hd :: tl)
    rw [insertSortedNatAux_snd x tl]
    cases Nat.ble x hd with
    | true => exact listPerm_refl (x :: hd :: tl)
    | false =>
      exact .trans (.cons hd (listPerm_insertSortedNat x tl)) (.swap x hd tl)

/-- `sortNatList xs` is a permutation of `xs` (`[]` zero axioms). -/
theorem listPerm_sortNatList :
    ∀ xs : List Nat, ListPerm (sortNatList xs) xs
  | [] => .nil
  | x :: xs =>
    .trans (listPerm_insertSortedNat x (sortNatList xs))
      (.cons x (listPerm_sortNatList xs))

/-- Erasing a contained element decomposes `ys` into `x :: eraseFirstNat x ys`
up to `ListPerm` (`[]` zero axioms). -/
theorem eraseFirstNat_perm_of_contains (x : Nat) :
    ∀ {ys : List Nat},
      containsNat x ys = true → ListPerm ys (x :: eraseFirstNat x ys)
  | [], h => Bool.noConfusion h
  | y :: yt, h => by
    change (Nat.beq x y || containsNat x yt) = true at h
    change ListPerm (y :: yt)
      (x :: (if Nat.beq x y then
        (eraseFirstNatAux x yt).2
      else
        y :: (eraseFirstNatAux x yt).1))
    rw [eraseFirstNatAux_snd x yt]
    cases hEq : Nat.beq x y with
    | true =>
      have hxy : x = y := natEq_of_beq_sep hEq
      rw [hxy]
      exact listPerm_refl (y :: yt)
    | false =>
      rw [hEq] at h
      exact .trans (.cons y (eraseFirstNat_perm_of_contains x h))
        (.swap x y (eraseFirstNat x yt))

/-- Full constructive decomposition specification of `cancelAtoms` (`[]` zero
axioms): there exists a common cancelled list `common` such that
`xs ~ common ++ (cancelAtoms xs ys).1` and
`ys ~ common ++ (cancelAtoms xs ys).2`. -/
theorem cancelAtoms_spec :
    ∀ (xs ys : List Nat),
      ∃ common : List Nat,
        ListPerm xs (common ++ (cancelAtoms xs ys).1) ∧
        ListPerm ys (common ++ (cancelAtoms xs ys).2)
  | [], ys => ⟨[], .nil, listPerm_refl ys⟩
  | x :: xs, ys => by
    change ∃ common : List Nat,
      ListPerm (x :: xs)
        (common ++
          (if containsNat x ys then
            cancelAtoms xs (eraseFirstNat x ys)
          else
            let res := cancelAtoms xs ys
            (x :: res.1, res.2)).1) ∧
      ListPerm ys
        (common ++
          (if containsNat x ys then
            cancelAtoms xs (eraseFirstNat x ys)
          else
            let res := cancelAtoms xs ys
            (x :: res.1, res.2)).2)
    cases hc : containsNat x ys with
    | true =>
      cases cancelAtoms_spec xs (eraseFirstNat x ys) with
      | intro common hC =>
        refine ⟨x :: common, .cons x hC.1, ?_⟩
        exact .trans (eraseFirstNat_perm_of_contains x hc) (.cons x hC.2)
    | false =>
      cases cancelAtoms_spec xs ys with
      | intro common hC =>
        refine ⟨common, ?_, hC.2⟩
        exact .trans (.cons x hC.1)
          (listPerm_symm (listPerm_middle x common (cancelAtoms xs ys).1))

/-! ## Part IV: Reflective ACU Normalization & Cancellation Soundness -/

/-- `evalAtomList` maps list append to `sep` up to `Bientails` (`[]` zero
axioms). -/
theorem evalAtomList_append_bientails {P : Type} {sep : P → P → P} {emp : P}
    {entails : P → P → Prop} (hL : SepACULaws sep emp entails) (env : Nat → P) :
    ∀ (xs ys : List Nat),
      Bientails entails
        (evalAtomList sep emp env (xs ++ ys))
        (sep (evalAtomList sep emp env xs) (evalAtomList sep emp env ys))
  | [], ys => bientails_symm (leftUnit_of_laws hL (evalAtomList sep emp env ys))
  | x :: xs, ys => by
    change Bientails entails
      (sep (env x) (evalAtomList sep emp env (xs ++ ys)))
      (sep (sep (env x) (evalAtomList sep emp env xs))
        (evalAtomList sep emp env ys))
    have hIh := evalAtomList_append_bientails hL env xs ys
    have hStep := sep_bientails_congr hL (bientails_refl hL.refl (env x)) hIh
    exact bientails_trans hL.trans hStep
      (bientails_symm (hL.assoc (env x)
        (evalAtomList sep emp env xs) (evalAtomList sep emp env ys)))

/-- Flattening a `SepExpr` at depth bound `fuel` preserves denotation up to
`Bientails` (`[]` zero axioms). -/
theorem evalSepExprFuel_flatten_bientails {P : Type} {sep : P → P → P} {emp : P}
    {entails : P → P → Prop} (hL : SepACULaws sep emp entails) (env : Nat → P) :
    ∀ (fuel : Nat) (e : SepExpr),
      Bientails entails
        (evalSepExprFuel sep emp env fuel e)
        (evalAtomList sep emp env (flattenSepFuel fuel e))
  | 0, _ => bientails_refl hL.refl emp
  | _ + 1, .emp => bientails_refl hL.refl emp
  | _ + 1, .atom i => bientails_symm (hL.rightUnit (env i))
  | fuel + 1, .sep l r => by
    change Bientails entails
      (sep (evalSepExprFuel sep emp env fuel l)
        (evalSepExprFuel sep emp env fuel r))
      (evalAtomList sep emp env
        (flattenSepFuel fuel l ++ flattenSepFuel fuel r))
    have hLR := sep_bientails_congr hL
      (evalSepExprFuel_flatten_bientails hL env fuel l)
      (evalSepExprFuel_flatten_bientails hL env fuel r)
    exact bientails_trans hL.trans hLR
      (bientails_symm (evalAtomList_append_bientails hL env
        (flattenSepFuel fuel l) (flattenSepFuel fuel r)))

/-- `evalAtomList` respects `ListPerm` up to `Bientails` (`[]` zero axioms). -/
theorem evalAtomList_perm_bientails {P : Type} {sep : P → P → P} {emp : P}
    {entails : P → P → Prop} (hL : SepACULaws sep emp entails) (env : Nat → P)
    {xs ys : List Nat} (hPerm : ListPerm xs ys) :
    Bientails entails
      (evalAtomList sep emp env xs)
      (evalAtomList sep emp env ys) := by
  induction hPerm with
  | nil => exact bientails_refl hL.refl emp
  | cons x _ ih =>
    exact sep_bientails_congr hL (bientails_refl hL.refl (env x)) ih
  | swap x y l =>
    let rest := evalAtomList sep emp env l
    have h1 := bientails_symm (hL.assoc (env y) (env x) rest)
    have h2 := sep_bientails_congr hL (hL.comm (env y) (env x))
      (bientails_refl hL.refl rest)
    have h3 := hL.assoc (env x) (env y) rest
    exact bientails_trans hL.trans h1 (bientails_trans hL.trans h2 h3)
  | trans _ _ ih₁ ih₂ => exact bientails_trans hL.trans ih₁ ih₂

/-- Canonical normalization `normSepFuel` preserves denotation up to
`Bientails` (`[]` zero axioms). -/
theorem evalSepExprFuel_norm_bientails {P : Type} {sep : P → P → P} {emp : P}
    {entails : P → P → Prop} (hL : SepACULaws sep emp entails) (env : Nat → P)
    (fuel : Nat) (e : SepExpr) :
    Bientails entails
      (evalSepExprFuel sep emp env fuel e)
      (evalAtomList sep emp env (normSepFuel fuel e)) :=
  bientails_trans hL.trans
    (evalSepExprFuel_flatten_bientails hL env fuel e)
    (evalAtomList_perm_bientails hL env
      (listPerm_symm (listPerm_sortNatList (flattenSepFuel fuel e))))

/-- Reflective ACU bientailment rule (`[]` zero axioms): any two `SepExpr`s
whose sorted normal forms match (`rfl`) denote mutually entailing assertions.
-/
theorem sepAC_bientails_of_norm_eq {P : Type} {sep : P → P → P} {emp : P}
    {entails : P → P → Prop} (hL : SepACULaws sep emp entails) (env : Nat → P)
    {fuel : Nat} {e₁ e₂ : SepExpr}
    (hNorm : normSepFuel fuel e₁ = normSepFuel fuel e₂) :
    Bientails entails
      (evalSepExprFuel sep emp env fuel e₁)
      (evalSepExprFuel sep emp env fuel e₂) := by
  have h1 := evalSepExprFuel_norm_bientails hL env fuel e₁
  have h2 := evalSepExprFuel_norm_bientails hL env fuel e₂
  rw [hNorm] at h1
  exact bientails_trans hL.trans h1 (bientails_symm h2)

/-- Reflective linear/affine framing rule (`[]` zero axioms): cancels all
common atom indices between `normSepFuel fuel lhs` and `normSepFuel fuel rhs`,
leaving only the residual entailment between `(cancelAtoms ...).1` and
`(cancelAtoms ...).2`. -/
theorem sepAC_entails_of_cancelAtoms {P : Type} {sep : P → P → P} {emp : P}
    {entails : P → P → Prop} (hL : SepACULaws sep emp entails) (env : Nat → P)
    {fuel : Nat} {lhs rhs : SepExpr}
    (hRes :
      entails
        (evalAtomList sep emp env
          (cancelAtoms (normSepFuel fuel lhs) (normSepFuel fuel rhs)).1)
        (evalAtomList sep emp env
          (cancelAtoms (normSepFuel fuel lhs) (normSepFuel fuel rhs)).2)) :
    entails
      (evalSepExprFuel sep emp env fuel lhs)
      (evalSepExprFuel sep emp env fuel rhs) := by
  cases cancelAtoms_spec (normSepFuel fuel lhs) (normSepFuel fuel rhs) with
  | intro common hSpec =>
    let res := cancelAtoms (normSepFuel fuel lhs) (normSepFuel fuel rhs)
    have hLNorm := (evalSepExprFuel_norm_bientails hL env fuel lhs).1
    have hLPerm := (evalAtomList_perm_bientails hL env hSpec.1).1
    have hLApp := (evalAtomList_append_bientails hL env common res.1).1
    have hFrame := hL.monoRight (evalAtomList sep emp env common)
      (evalAtomList sep emp env res.1) (evalAtomList sep emp env res.2) hRes
    have hRApp := (evalAtomList_append_bientails hL env common res.2).2
    have hRPerm := (evalAtomList_perm_bientails hL env hSpec.2).2
    have hRNorm := (evalSepExprFuel_norm_bientails hL env fuel rhs).2
    exact hL.trans _ _ _ hLNorm
      (hL.trans _ _ _ hLPerm
        (hL.trans _ _ _ hLApp
          (hL.trans _ _ _ hFrame
            (hL.trans _ _ _ hRApp
              (hL.trans _ _ _ hRPerm hRNorm)))))

/-- Reflective affine framing shortcut (`[]` zero axioms): when `entails` is
affine (`AffineEntails emp entails`) and every atom of `rhs` cancels against
`lhs` (`(cancelAtoms (normSepFuel fuel lhs) (normSepFuel fuel rhs)).2 = []`),
`lhs ⊢ rhs` holds by `rfl`. -/
theorem sepAC_affine_entails_of_cancel_nil {P : Type} {sep : P → P → P}
    {emp : P} {entails : P → P → Prop} (hL : SepACULaws sep emp entails)
    (hAff : AffineEntails emp entails) (env : Nat → P)
    {fuel : Nat} {lhs rhs : SepExpr}
    (hNil :
      (cancelAtoms (normSepFuel fuel lhs) (normSepFuel fuel rhs)).2 = []) :
    entails
      (evalSepExprFuel sep emp env fuel lhs)
      (evalSepExprFuel sep emp env fuel rhs) := by
  apply sepAC_entails_of_cancelAtoms hL env
  rw [hNil]
  exact hAff _

/-! ## Part V: `Anneal.PureLift.SpatialProp` Linear Separation-Algebra Bridge -/

/-- Permutation-closed `Anneal.PureLift.SpatialProp Val`: the exact subclass
of list-backed `SpatialBlock` assertions closed under heaplet reordering so
associativity, commutativity, and right-unit laws all hold simultaneously. -/
structure PermSpatialProp (Val : Type) where
  pred : SpatialProp Val
  permClosed :
    ∀ {h₁ h₂ : List (SpatialBlock Val)},
      ListPerm h₁ h₂ → pred h₁ → pred h₂

/-- Entailment between `PermSpatialProp Val` heaplet predicates. -/
@[expose] def PermSpatialEntails {Val : Type}
    (P Q : PermSpatialProp Val) : Prop :=
  ∀ h : List (SpatialBlock Val), P.pred h → Q.pred h

private theorem blocksDisjoint_symm {Val : Type}
    {h1 h2 : List (SpatialBlock Val)} (h : blocksDisjoint h1 h2) :
    blocksDisjoint h2 h1 := by
  intro b2 b1 hb2 hb1
  have h12 := h b1 b2 hb1 hb2
  exact ⟨fun heq => h12.1 heq.symm, fun heq => h12.2 heq.symm⟩

private theorem listPerm_mem {α : Type} {l₁ l₂ : List α} (hP : ListPerm l₁ l₂) :
    ∀ {x : α}, x ∈ l₁ → x ∈ l₂ := by
  induction hP with
  | nil => intro _ hx; exact hx
  | cons a _ ih =>
    intro x hx
    cases hx with
    | head => exact List.Mem.head _
    | tail _ htl => exact List.Mem.tail a (ih htl)
  | swap a b l =>
    intro x hx
    cases hx with
    | head => exact List.Mem.tail a (List.Mem.head _)
    | tail _ htl =>
      cases htl with
      | head => exact List.Mem.head _
      | tail _ htl2 => exact List.Mem.tail a (List.Mem.tail b htl2)
  | trans _ _ ih₁ ih₂ => intro _ hx; exact ih₂ (ih₁ hx)

private theorem listPerm_length_eq {α : Type} {l₁ l₂ : List α}
    (hP : ListPerm l₁ l₂) : l₁.length = l₂.length := by
  induction hP with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih
  | swap _ _ _ => rfl
  | trans _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂

private theorem listPerm_nil_left_eq {α : Type} {l : List α}
    (hP : ListPerm [] l) : l = [] := by
  cases l with
  | nil => rfl
  | cons a _ =>
    have hMem : a ∈ ([] : List α) := listPerm_mem (listPerm_symm hP) (.head _)
    nomatch hMem

private theorem listPerm_singleton_left_eq {α : Type} {a : α} {l : List α}
    (hP : ListPerm [a] l) : l = [a] := by
  cases l with
  | nil =>
    have hLen := listPerm_length_eq hP
    nomatch hLen
  | cons x xs =>
    cases xs with
    | cons _ _ =>
      have hLen := listPerm_length_eq hP
      injection hLen with hZ
      nomatch hZ
    | nil =>
      have hMem : x ∈ [a] := listPerm_mem (listPerm_symm hP) (.head _)
      cases hMem with
      | head => rfl
      | tail _ hNil => nomatch hNil

private theorem mem_append_left_sep {α : Type} {x : α} :
    ∀ {xs ys : List α}, x ∈ xs → x ∈ xs ++ ys
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ h => .tail _ (mem_append_left_sep h)

private theorem mem_append_right_sep {α : Type} {x : α} :
    ∀ (xs : List α) {ys : List α}, x ∈ ys → x ∈ xs ++ ys
  | [], _, h => h
  | _ :: xs, _, h => .tail _ (mem_append_right_sep xs h)

private theorem mem_append_elim_sep {α : Type} {x : α} :
    ∀ {xs ys : List α}, x ∈ xs ++ ys → x ∈ xs ∨ x ∈ ys
  | [], _, h => Or.inr h
  | _ :: _, _, .head _ => Or.inl (.head _)
  | _ :: _, _, .tail _ h =>
    match mem_append_elim_sep h with
    | Or.inl hx => Or.inl (.tail _ hx)
    | Or.inr hy => Or.inr hy

private theorem blocksDisjoint_perm_left {Val : Type}
    {h1 h1' h2 : List (SpatialBlock Val)}
    (hP : ListPerm h1 h1') (hD : blocksDisjoint h1 h2) :
    blocksDisjoint h1' h2 := by
  intro b1 b2 hb1 hb2
  exact hD b1 b2 (listPerm_mem (listPerm_symm hP) hb1) hb2

private theorem blocksDisjoint_perm_right {Val : Type}
    {h1 h2 h2' : List (SpatialBlock Val)}
    (hP : ListPerm h2 h2') (hD : blocksDisjoint h1 h2) :
    blocksDisjoint h1 h2' := by
  intro b1 b2 hb1 hb2
  exact hD b1 b2 hb1 (listPerm_mem (listPerm_symm hP) hb2)

private theorem listAppend_assoc_sep {α : Type} :
    ∀ (xs ys zs : List α), (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | x :: xs, ys, zs => congrArg (List.cons x) (listAppend_assoc_sep xs ys zs)

/-- Empty heaplet lifted into `PermSpatialProp Val`. -/
@[expose] def permSpatialEmp {Val : Type} : PermSpatialProp Val where
  pred := spatialEmp
  permClosed hP hNil := by
    rw [hNil] at hP
    exact listPerm_nil_left_eq hP

/-- Single-block points-to assertion lifted into `PermSpatialProp Val`
(`[propext]` only). -/
@[expose] def permSpatialPointsTo {Val : Type} (bid : BlockId)
    (perm : SpatialPerm) (cells : List (CellVal Val)) :
    PermSpatialProp Val where
  pred := spatialPointsTo bid perm cells
  permClosed := by
    intro h₁ h₂ hP hPt
    cases h₁ with
    | nil => exact False.elim hPt
    | cons b rest =>
      cases rest with
      | cons _ _ => exact False.elim hPt
      | nil =>
        have hEq : h₂ = [b] := listPerm_singleton_left_eq hP
        rw [hEq]
        exact hPt

/-- Permutation-closed separating conjunction over `PermSpatialProp Val`. -/
@[expose] def permSpatialSepConj {Val : Type}
    (P Q : PermSpatialProp Val) : PermSpatialProp Val where
  pred blocks :=
    ∃ h1 h2 : List (SpatialBlock Val),
      ListPerm blocks (h1 ++ h2) ∧ blocksDisjoint h1 h2 ∧
        P.pred h1 ∧ Q.pred h2
  permClosed hP hSep := by
    cases hSep with
    | intro h1 hR =>
      cases hR with
      | intro h2 hC =>
        exact ⟨h1, h2, .trans (listPerm_symm hP) hC.1, hC.2.1,
          hC.2.2.1, hC.2.2.2⟩

/-- Every ordered `Anneal.PureLift.spatialSepConj` witness lifts directly into
`permSpatialSepConj` (`[]` zero axioms). -/
theorem permSpatialSepConj_of_spatialSepConj {Val : Type}
    {P Q : PermSpatialProp Val} {h : List (SpatialBlock Val)}
    (hSep : spatialSepConj P.pred Q.pred h) :
    (permSpatialSepConj P Q).pred h := by
  cases hSep with
  | intro h1 hRest =>
    cases hRest with
    | intro h2 hConj =>
      refine ⟨h1, h2, ?_, hConj.2.1, hConj.2.2.1, hConj.2.2.2⟩
      rw [hConj.1]
      exact listPerm_refl (h1 ++ h2)

/-- `PermSpatialProp Val` with `permSpatialSepConj`, `permSpatialEmp`, and
`PermSpatialEntails` satisfies the complete `SepACULaws` contract (`[]` zero
axioms), enabling reflective ACU normalization and `cancelAtoms` framing
directly on `Anneal.PureLift.SpatialBlock` heaplets. -/
theorem permSpatialProp_sepACULaws (Val : Type) :
    SepACULaws (@permSpatialSepConj Val) (@permSpatialEmp Val)
      (@PermSpatialEntails Val) := by
  refine ⟨fun _ _ h => h, fun _ _ _ h12 h23 h hp => h23 h (h12 h hp),
    ?_, ?_, ?_, ?_⟩
  · intro F P Q hPQ h hSep
    cases hSep with
    | intro h1 hR =>
      cases hR with
      | intro h2 hC =>
        exact ⟨h1, h2, hC.1, hC.2.1, hC.2.2.1, hPQ h2 hC.2.2.2⟩
  · intro P Q R
    refine ⟨?_, ?_⟩
    · intro h hL
      cases hL with
      | intro h12 hR1 =>
        cases hR1 with
        | intro h3 hC1 =>
          cases hC1.2.2.1 with
          | intro h1 hR2 =>
            cases hR2 with
            | intro h2 hC2 =>
              have hD12_3 : blocksDisjoint (h1 ++ h2) h3 :=
                blocksDisjoint_perm_left hC2.1 hC1.2.1
              have hD1_23 : blocksDisjoint h1 (h2 ++ h3) := by
                intro b1 b23 hb1 hb23
                cases mem_append_elim_sep hb23 with
                | inl hb2 => exact hC2.2.1 b1 b23 hb1 hb2
                | inr hb3 =>
                  exact hD12_3 b1 b23 (mem_append_left_sep hb1) hb3
              have hD2_3 : blocksDisjoint h2 h3 := by
                intro b2 b3 hb2 hb3
                exact hD12_3 b2 b3 (mem_append_right_sep h1 hb2) hb3
              have hPerm : ListPerm h (h1 ++ (h2 ++ h3)) := by
                rw [← listAppend_assoc_sep h1 h2 h3]
                exact .trans hC1.1 (listPerm_append_right h3 hC2.1)
              exact ⟨h1, h2 ++ h3, hPerm, hD1_23, hC2.2.2.1,
                ⟨h2, h3, listPerm_refl _, hD2_3, hC2.2.2.2, hC1.2.2.2⟩⟩
    · intro h hR
      cases hR with
      | intro h1 hR1 =>
        cases hR1 with
        | intro h23 hC1 =>
          cases hC1.2.2.2 with
          | intro h2 hR2 =>
            cases hR2 with
            | intro h3 hC2 =>
              have hD1_23 : blocksDisjoint h1 (h2 ++ h3) :=
                blocksDisjoint_perm_right hC2.1 hC1.2.1
              have hD1_2 : blocksDisjoint h1 h2 := by
                intro b1 b2 hb1 hb2
                exact hD1_23 b1 b2 hb1 (mem_append_left_sep hb2)
              have hD12_3 : blocksDisjoint (h1 ++ h2) h3 := by
                intro b12 b3 hb12 hb3
                cases mem_append_elim_sep hb12 with
                | inl hb1 =>
                  exact hD1_23 b12 b3 hb1 (mem_append_right_sep h2 hb3)
                | inr hb2 => exact hC2.2.1 b12 b3 hb2 hb3
              have hPerm : ListPerm h ((h1 ++ h2) ++ h3) := by
                rw [listAppend_assoc_sep h1 h2 h3]
                exact .trans hC1.1 (listPerm_append_left h1 hC2.1)
              exact ⟨h1 ++ h2, h3, hPerm, hD12_3,
                ⟨h1, h2, listPerm_refl _, hD1_2, hC1.2.2.1, hC2.2.2.1⟩,
                hC2.2.2.2⟩
  · intro P Q
    have hOneDir :
        ∀ (A B : PermSpatialProp Val),
          PermSpatialEntails (permSpatialSepConj A B)
            (permSpatialSepConj B A) := by
      intro A B h hAB
      cases hAB with
      | intro h1 hR =>
        cases hR with
        | intro h2 hC =>
          exact ⟨h2, h1, .trans hC.1 (listPerm_append_comm h1 h2),
            blocksDisjoint_symm hC.2.1, hC.2.2.2, hC.2.2.1⟩
    exact ⟨hOneDir P Q, hOneDir Q P⟩
  · intro P
    refine ⟨?_, ?_⟩
    · intro h hPE
      cases hPE with
      | intro h1 hR =>
        cases hR with
        | intro h2 hC =>
          have h2Nil : h2 = [] := hC.2.2.2
          rw [h2Nil, listAppend_nil_sep h1] at hC
          exact P.permClosed (listPerm_symm hC.1) hC.2.2.1
    · intro h hP
      refine ⟨h, [], ?_, (fun _ _ _ hb2 => nomatch hb2), hP, rfl⟩
      rw [listAppend_nil_sep h]
      exact listPerm_refl h

/-- `PermSpatialProp Val` is strictly linear (not affine): exclusive ownership
`permSpatialPointsTo` does not entail `permSpatialEmp` (`[propext]` only). -/
theorem not_affineEntails_permSpatialProp (Val : Type) :
    ¬ AffineEntails (@permSpatialEmp Val) (@PermSpatialEntails Val) := by
  intro hAff
  let b : SpatialBlock Val :=
    { blockId := 0
      originLoan := 0
      perm := .readWrite
      provenanceTag := 0
      activeSubSplits := 0
      cells := [] }
  have hEmp : ([b] : List (SpatialBlock Val)) = [] :=
    hAff (permSpatialPointsTo 0 .readWrite []) [b] ⟨rfl, rfl, rfl, rfl⟩
  nomatch hEmp

end Anneal.SepAC

end
