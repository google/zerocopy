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
public import Anneal.CnfOrd.Ord

public section

/-!
# View-Indexed Spatial PCM Over Fixed-Depth Bit Tries
(`Anneal.WavefrontReclaim.SpatialPcm`)

Constructive, zero-axiom (`[]`) resource algebra powering `VSepWpOrdRel`:

- `ResTrie`: fixed-depth bit-path radix trie (`ResTrie.getBits`,
  `ResTrie.modifyBits`, `resTrieMerge`) with commutative/associative partial
  merge (`resTrieMerge_comm`, `resTrieMerge_assoc`).
- `CellFrag` and `ResElem`: partial capability/authority cell fragments
  (idempotent `.capOnly`, exclusive `.authOnly`/`.capAndAuth`), exclusive
  `.checkedOutLoan` tokens, and additive `< ω^ω` Cantor Normal Form
  (`Anneal.CnfOrd`) `.pool` and `.debt` fragments (`ordDebtTree_decomp`).
- `VProp`: upward-closed view-and-resource separation logic (`vemp`, `vowns`,
  `vMinStep`, `vsep`, `poolBackingProp`, `ordDebtProp`, `checkedOutLoanProp`,
  `cellCapProp`, `cellAuthProp`) with commutative/associative separating
  conjunction.

All definitions are computable (`0` `noncomputable`, `0` `._unsafe_rec`,
`0` `omega`, `0` `decide`) and every authored declaration compiles with zero
axioms (`[]`).
-/

namespace Anneal.WavefrontReclaim

open Anneal.CnfOrd

/-! ## 1. Internal Bool and Nat Helpers -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem boolTrueNeFalse (h : true = false) : False :=
  Bool.noConfusion h

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => exact h

/-- Decidable equality on `Bool`. -/
@[expose] def boolEq (a b : Bool) : Bool :=
  match a with
  | false => match b with | false => true | true => false
  | true => match b with | false => false | true => true

/-- Structural equality on `List Bool` bit paths. -/
@[expose] def listBoolBeq (xs ys : List Bool) : Bool :=
  (xs.foldr
    (fun x ih cur =>
      match cur with
      | [] => false
      | y :: ytl => boolEq x y && ih ytl)
    (fun cur =>
      match cur with
      | [] => true
      | _ :: _ => false)) ys

/-- Reflexivity of `listBoolBeq` (`[]`). -/
theorem listBoolBeq_refl (xs : List Bool) : listBoolBeq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x _ ih =>
    cases x <;> exact ih

/-- Soundness of `listBoolBeq` (`[]`). -/
theorem listBoolBeq_eq (xs ys : List Bool) (h : listBoolBeq xs ys = true) :
    xs = ys := by
  revert ys
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons _ _ => exact False.elim (boolFalseNeTrue h)
  | cons x _ ih =>
    intro ys h
    cases ys with
    | nil => exact False.elim (boolFalseNeTrue h)
    | cons y ytl =>
      change (boolEq x y && listBoolBeq _ ytl) = true at h
      have hxy : x = y := by
        have hx := bandLeft h
        cases x with
        | false =>
          cases y with
          | false => rfl
          | true => exact False.elim (boolFalseNeTrue hx)
        | true =>
          cases y with
          | false => exact False.elim (boolFalseNeTrue hx)
          | true => rfl
      rw [hxy, ih ytl (bandRight h)]

private theorem natBle_refl (a : Nat) : Nat.ble a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBle_zero_left (a : Nat) : Nat.ble 0 a = true := by
  cases a <;> rfl

private theorem natBle_trans (a b c : Nat)
    (h1 : Nat.ble a b = true) (h2 : Nat.ble b c = true) :
    Nat.ble a c = true := by
  revert b c
  induction a with
  | zero => intro _ c _ _; exact natBle_zero_left c
  | succ _ ih =>
    intro b c h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h1)
    | succ b' =>
      cases c with
      | zero => exact False.elim (boolFalseNeTrue h2)
      | succ c' => exact ih b' c' h1 h2

/-! ## 2. Fixed-Depth Bit-Path Resource Trie (`ResTrie`) -/

/-- Binary radix trie mapping `Bool` bit-paths to optional resource elements. -/
inductive ResTrie (α : Type) where
  | empty
  | node (val : Option α) (l : ResTrie α) (r : ResTrie α)

/-- Looks up the optional resource stored at bit-path `path` in `t`. -/
@[expose] def ResTrie.getBits {α : Type} (path : List Bool) (t : ResTrie α) :
    Option α :=
  (path.foldr
    (fun b ih cur =>
      match cur with
      | .empty => none
      | .node _ l r =>
        match b with
        | false => ih l
        | true => ih r)
    (fun cur =>
      match cur with
      | .empty => none
      | .node v _ _ => v)) t

/-- Updates the optional resource at bit-path `path` in `t` via `f`, allocating
intermediate nodes as needed. -/
@[expose] def ResTrie.modifyBits {α : Type} (path : List Bool) (f : Option α →
    Option α) (t : ResTrie α) : ResTrie α :=
  (path.foldr
    (fun b ih cur =>
      let v0 := match cur with | .empty => none | .node v _ _ => v
      let l0 := match cur with | .empty => .empty | .node _ l _ => l
      let r0 := match cur with | .empty => .empty | .node _ _ r => r
      match b with
      | false => .node v0 (ih l0) r0
      | true => .node v0 l0 (ih r0))
    (fun cur =>
      match cur with
      | .empty => .node (f none) .empty .empty
      | .node v l r => .node (f v) l r)) t

/-- Looking up any bit-path in `.empty` returns `none`. -/
theorem resTrie_getBits_empty {α : Type} (p : List Bool) :
    ResTrie.getBits p (.empty : ResTrie α) = none := by
  cases p <;> rfl

/-- Looking up `p` immediately after `ResTrie.modifyBits p f t` returns `f
(ResTrie.getBits p t)`. -/
theorem resTrie_getBits_modifyBits_same {α : Type} (p : List Bool) (f : Option
    α → Option α) (t : ResTrie α) :
    ResTrie.getBits p (ResTrie.modifyBits p f t) = f (ResTrie.getBits p t) := by
  revert t
  induction p with
  | nil =>
    intro t
    cases t <;> rfl
  | cons b _ ih =>
    intro t
    cases t with
    | empty =>
      cases b with
      | false =>
        exact Eq.trans (ih .empty) (congrArg f (resTrie_getBits_empty _))
      | true =>
        exact Eq.trans (ih .empty) (congrArg f (resTrie_getBits_empty _))
    | node _ l r =>
      cases b with
      | false => exact ih l
      | true => exact ih r

/-- Modifying path `p` preserves `ResTrie.getBits q` on every distinct
equal-length path `q`. -/
theorem resTrie_getBits_modifyBits_ne {α : Type} (p1 p2 : List Bool)
    (hLen : p1.length = p2.length) (hNe : listBoolBeq p1 p2 = false)
    (f : Option α → Option α) (t : ResTrie α) :
    ResTrie.getBits p2 (ResTrie.modifyBits p1 f t) = ResTrie.getBits p2 t := by
  revert p2 t
  induction p1 with
  | nil =>
    intro p2 hLen hNe _
    cases p2 with
    | nil => exact False.elim (boolTrueNeFalse hNe)
    | cons _ _ => nomatch hLen
  | cons b1 bs1 ih =>
    intro p2 hLen hNe t
    cases p2 with
    | nil => nomatch hLen
    | cons b2 bs2 =>
      have hL : bs1.length = bs2.length := Nat.succ.inj hLen
      change (boolEq b1 b2 && listBoolBeq bs1 bs2) = false at hNe
      cases t with
      | empty =>
        revert hNe
        cases hEqB : boolEq b1 b2 with
        | false =>
          intro hNe; cases b1 with
          | false =>
            cases b2 with
            | false => exact False.elim (boolTrueNeFalse hEqB)
            | true => exact resTrie_getBits_empty bs2
          | true =>
            cases b2 with
            | false => exact resTrie_getBits_empty bs2
            | true => exact False.elim (boolTrueNeFalse hEqB)
        | true =>
          intro hNe
          have hB : b1 = b2 := by
            cases b1 with
            | false =>
              cases b2 with
              | false => rfl
              | true => exact False.elim (boolFalseNeTrue hEqB)
            | true =>
              cases b2 with
              | false => exact False.elim (boolFalseNeTrue hEqB)
              | true => rfl
          rw [hB]
          cases b2 with
          | false =>
            exact Eq.trans (ih bs2 hL hNe .empty) (resTrie_getBits_empty bs2)
          | true =>
            exact Eq.trans (ih bs2 hL hNe .empty) (resTrie_getBits_empty bs2)
      | node _ l r =>
        revert hNe
        cases hEqB : boolEq b1 b2 with
        | false =>
          intro hNe; cases b1 with
          | false =>
            cases b2 with
            | false => exact False.elim (boolTrueNeFalse hEqB)
            | true => rfl
          | true =>
            cases b2 with
            | false => rfl
            | true => exact False.elim (boolTrueNeFalse hEqB)
        | true =>
          intro hNe
          have hB : b1 = b2 := by
            cases b1 with
            | false =>
              cases b2 with
              | false => rfl
              | true => exact False.elim (boolFalseNeTrue hEqB)
            | true =>
              cases b2 with
              | false => exact False.elim (boolFalseNeTrue hEqB)
              | true => rfl
          rw [hB]
          cases b2 with
          | false => exact ih bs2 hL hNe l
          | true => exact ih bs2 hL hNe r

/-! ## 3. Views, 4-Bit Slot Identifiers, and Resource PCM -/

/-- Monotonic step-count view vector (`List Nat`, defaulting out-of-range
indices to `0`). -/
abbrev View : Type := List Nat

/-- Reads index `idx` of view `v` (`0` when `idx ≥ v.length`). -/
@[expose] def viewGet (v : View) (idx : Nat) : Nat :=
  v.foldr
    (fun x ih k => match k with | 0 => x | k' + 1 => ih k')
    (fun _ => 0) idx

/-- Pointwise `≤` order on views (`viewGet v1 i ≤ viewGet v2 i` for all `i`). -/
structure ViewLe (v1 v2 : View) : Prop where
  leAt : ∀ (i : Nat), Nat.ble (viewGet v1 i) (viewGet v2 i) = true

/-- Reflexivity of `ViewLe`. -/
theorem viewLe_refl (v : View) : ViewLe v v :=
  ViewLe.mk (fun i => natBle_refl (viewGet v i))

/-- Transitivity of `ViewLe`. -/
theorem viewLe_trans (v1 v2 v3 : View) (h12 : ViewLe v1 v2) (h23 : ViewLe v2
    v3) : ViewLe v1 v3 :=
  ViewLe.mk (fun i => natBle_trans (viewGet v1 i) (viewGet v2 i) (viewGet v3 i)
    (h12.leAt i) (h23.leAt i))

/-- 4-bit slot identifier `(b0, b1, b2, b3)` indexing up to 16 loans or spatial
cells. -/
abbrev Pos4 : Type := Bool × Bool × Bool × Bool

/-- Expands a 4-bit `Pos4` identifier into its 4-element `List Bool` suffix. -/
@[expose] def pos4ToList (p : Pos4) : List Bool := [p.1, p.2.1, p.2.2.1,
    p.2.2.2]

/-- Computable Boolean equality on `Pos4`. -/
@[expose] def Pos4.beq (a b : Pos4) : Bool := listBoolBeq (pos4ToList a)
    (pos4ToList b)

/-- Reflexivity of `Pos4.beq`. -/
theorem pos4_beq_refl (a : Pos4) : Pos4.beq a a = true :=
    listBoolBeq_refl (pos4ToList a)

/-- Symmetry of `boolEq`. -/
private theorem boolEq_symm (x y : Bool) : boolEq x y = boolEq y x := by
  cases x <;> cases y <;> rfl

/-- Symmetry of `Pos4.beq`. -/
theorem pos4_beq_symm (a b : Pos4) : Pos4.beq a b = Pos4.beq b a := by
  cases a with
  | mk a0 ar1 =>
    cases ar1 with
    | mk a1 ar2 =>
      cases ar2 with
      | mk a2 a3 =>
        cases b with
        | mk b0 br1 =>
          cases br1 with
          | mk b1 br2 =>
            cases br2 with
            | mk b2 b3 =>
              change
                (boolEq a0 b0 && (boolEq a1 b1 && (boolEq a2 b2 &&
                  (boolEq a3 b3 && true)))) =
                (boolEq b0 a0 && (boolEq b1 a1 && (boolEq b2 a2 &&
                  (boolEq b3 a3 && true))))
              rw [boolEq_symm a0 b0, boolEq_symm a1 b1, boolEq_symm a2 b2,
                boolEq_symm a3 b3]

/-- Soundness of `Pos4.beq`: `Pos4.beq a b = true` implies `a = b`. -/
theorem pos4_eq_of_beq (a b : Pos4) (h : Pos4.beq a b = true) : a = b := by
  have hl := listBoolBeq_eq (pos4ToList a) (pos4ToList b) h
  cases a with
  | mk _ ar1 =>
    cases ar1 with
    | mk _ ar2 =>
      cases ar2 with
      | mk _ _ =>
        cases b with
        | mk _ br1 =>
          cases br1 with
          | mk _ br2 =>
            cases br2 with
            | mk _ _ =>
              injection hl with h0 ht1
              injection ht1 with h1 ht2
              injection ht2 with h2 ht3
              injection ht3 with h3 _
              subst h0; subst h1; subst h2; subst h3
              rfl

/-- Canonical 4-bit slot `0` (`0000`). -/
@[expose] def path0 : Pos4 := (false, false, false, false)
/-- Canonical 4-bit slot `1` (`0001`). -/
@[expose] def path1 : Pos4 := (false, false, false, true)
/-- Canonical 4-bit slot `4` (`0100`). -/
@[expose] def path2 : Pos4 := (false, true, false, false)
/-- 6-bit resource-trie path `[true, false, false, false, false, false]` (prefix
`10`) for the pool ordinal capacity. -/
@[expose] def poolPath : List Bool := [true, false, false, false, false, false]
/-- 6-bit resource-trie path `[true, true, false, false, false, false]` (prefix
`11`) for amortized ordinal debt. -/
@[expose] def debtPath : List Bool := [true, true, false, false, false, false]
/-- 6-bit resource-trie path `false :: false :: pos4ToList c` (prefix `00`) for
checked-out loan `c`. -/
@[expose] def checkedLoanPath (c : Pos4) : List Bool := false :: false ::
    pos4ToList c
/-- 6-bit resource-trie path `false :: true :: pos4ToList c` (prefix `01`) for
spatial cell `c`. -/
@[expose] def cellPath (c : Pos4) : List Bool := false :: true :: pos4ToList c

/-- Monadic `Option` bind (`0` `noncomputable`). -/
@[expose] def optBind {α β : Type} (x : Option α) (f : α → Option β) : Option β
    :=
  match x with
  | none => none
  | some a => f a

/-- Spatial cell PCM fragment: idempotent `.capOnly` capability, exclusive
`.authOnly val` authority, or combined `.capAndAuth val`. -/
inductive CellFrag where
  | capOnly
  | authOnly (val : Nat)
  | capAndAuth (val : Nat)

/-- Partial commutative merge on `CellFrag`: `.capOnly` is idempotent and
combines with `.authOnly val` into `.capAndAuth val`; two authorities conflict
(`none`). -/
@[expose] def cellFragMerge (a b : CellFrag) : Option CellFrag :=
  match a with
  | .capOnly =>
    match b with
    | .capOnly => some .capOnly
    | .authOnly v => some (.capAndAuth v)
    | .capAndAuth v => some (.capAndAuth v)
  | .authOnly v =>
    match b with
    | .capOnly => some (.capAndAuth v)
    | .authOnly _ | .capAndAuth _ => none
  | .capAndAuth v =>
    match b with
    | .capOnly => some (.capAndAuth v)
    | .authOnly _ | .capAndAuth _ => none

/-- Commutativity of `cellFragMerge`. -/
theorem cellFragMerge_comm (a b : CellFrag) : cellFragMerge a b =
    cellFragMerge b a := by
  cases a <;> cases b <;> rfl

/-- Associativity of `cellFragMerge` under Kleisli `Option` bind. -/
theorem cellFragMerge_assoc (a b c : CellFrag) :
    optBind (cellFragMerge a b) (fun ab => cellFragMerge ab c) =
      optBind (cellFragMerge b c) (fun bc => cellFragMerge a bc) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Single-node PCM element at a 6-bit `ResTrie` leaf: additive `.pool` /
`.debt` ordinals, exclusive `.checkedOutLoan`, or `.cell` fragment. -/
inductive ResElem where
  | pool (frag : CnfOrd)
  | debt (frag : CnfOrd)
  | checkedOutLoan (scopeId : Nat) (val : Nat)
  | cell (cf : CellFrag)

/-- Partial commutative merge on `ResElem`: adds `.pool` and `.debt` ordinals
via `cnfNatAdd`, rejects duplicate `.checkedOutLoan` tokens, and delegates
`.cell` to `cellFragMerge`. -/
@[expose] def resMerge (r1 r2 : ResElem) : Option ResElem :=
  match r1 with
  | .pool f1 =>
    match r2 with
    | .pool f2 => some (.pool (cnfNatAdd f1 f2))
    | .debt _ | .checkedOutLoan _ _ | .cell _ => none
  | .debt d1 =>
    match r2 with
    | .debt d2 => some (.debt (cnfNatAdd d1 d2))
    | .pool _ | .checkedOutLoan _ _ | .cell _ => none
  | .checkedOutLoan _ _ => none
  | .cell c1 =>
    match r2 with
    | .pool _ | .debt _ | .checkedOutLoan _ _ => none
    | .cell c2 =>
      match cellFragMerge c1 c2 with
      | none => none
      | some cm => some (.cell cm)

/-- Commutativity of `resMerge`. -/
theorem resMerge_comm (r1 r2 : ResElem) : resMerge r1 r2 = resMerge r2 r1 := by
  cases r1 with
  | pool f1 =>
    cases r2 with
    | pool f2 => dsimp only [resMerge]; rw [cnfNatAdd_comm f1 f2]
    | debt _ | checkedOutLoan _ _ | cell _ => rfl
  | debt d1 =>
    cases r2 with
    | debt d2 => dsimp only [resMerge]; rw [cnfNatAdd_comm d1 d2]
    | pool _ | checkedOutLoan _ _ | cell _ => rfl
  | checkedOutLoan _ _ => cases r2 <;> rfl
  | cell c1 =>
    cases r2 with
    | pool _ | debt _ | checkedOutLoan _ _ => rfl
    | cell c2 => dsimp only [resMerge]; rw [cellFragMerge_comm c1 c2]

/-- Associativity of `resMerge` under Kleisli `Option` bind. -/
theorem resMerge_assoc (r1 r2 r3 : ResElem) :
    optBind (resMerge r1 r2) (fun r12 => resMerge r12 r3) =
      optBind (resMerge r2 r3) (fun r23 => resMerge r1 r23) := by
  cases r1 with
  | checkedOutLoan _ _ =>
    cases r2 with
    | pool _ | debt _ | checkedOutLoan _ _ => cases r3 <;> rfl
    | cell c2 =>
      cases r3 with
      | pool _ | debt _ | checkedOutLoan _ _ => rfl
      | cell c3 =>
        dsimp only [optBind, resMerge]
        cases cellFragMerge c2 c3 <;> rfl
  | pool f1 =>
    cases r2 with
    | debt _ | checkedOutLoan _ _ => cases r3 <;> rfl
    | cell c2 =>
      cases r3 with
      | pool _ | debt _ | checkedOutLoan _ _ => rfl
      | cell c3 =>
        dsimp only [optBind, resMerge]
        cases cellFragMerge c2 c3 <;> rfl
    | pool f2 =>
      cases r3 with
      | debt _ | checkedOutLoan _ _ | cell _ => rfl
      | pool f3 => dsimp only [optBind, resMerge]; rw [cnfNatAdd_assoc f1 f2 f3]
  | debt d1 =>
    cases r2 with
    | pool _ | checkedOutLoan _ _ => cases r3 <;> rfl
    | cell c2 =>
      cases r3 with
      | pool _ | debt _ | checkedOutLoan _ _ => rfl
      | cell c3 =>
        dsimp only [optBind, resMerge]
        cases cellFragMerge c2 c3 <;> rfl
    | debt d2 =>
      cases r3 with
      | pool _ | cell _ | checkedOutLoan _ _ => rfl
      | debt d3 => dsimp only [optBind, resMerge]; rw [cnfNatAdd_assoc d1 d2 d3]
  | cell c1 =>
    cases r2 with
    | pool _ | debt _ | checkedOutLoan _ _ => cases r3 <;> rfl
    | cell c2 =>
      cases r3 with
      | pool _ | debt _ | checkedOutLoan _ _ =>
        dsimp only [optBind, resMerge]; cases cellFragMerge c1 c2 <;> rfl
      | cell c3 =>
        dsimp only [optBind, resMerge]
        have hc := cellFragMerge_assoc c1 c2 c3
        dsimp only [optBind] at hc
        revert hc
        cases h12 : cellFragMerge c1 c2 with
        | none =>
          intro hc
          revert hc
          cases h23 : cellFragMerge c2 c3 with
          | none => intro hc; rfl
          | some _ => intro hc; dsimp only at hc; dsimp only; rw [← hc]
        | some _ =>
          intro hc; dsimp only at hc
          revert hc
          cases h23 : cellFragMerge c2 c3 with
          | none => intro hc; dsimp only at hc; dsimp only; rw [hc]
          | some _ => intro hc; dsimp only at hc; dsimp only; rw [hc]

/-- Lifts a partial binary merge `op` to `Option α`, treating `none` as the unit
(`some y` / `some x`) and returning `none` on conflict. -/
@[expose] def optOp {α : Type} (op : α → α → Option α) (x y : Option α) : Option
    (Option
    α) :=
  match x with
  | none => some y
  | some a =>
    match y with
    | none => some (some a)
    | some b =>
      match op a b with
      | none => none
      | some c => some (some c)

private theorem optOp_comm {α : Type} (op : α → α → Option α)
    (hComm : ∀ a b, op a b = op b a) (x y : Option α) :
    optOp op x y = optOp op y x := by
  cases x with
  | none => cases y <;> rfl
  | some a =>
    cases y with
    | none => rfl
    | some b => dsimp only [optOp]; rw [hComm a b]

private theorem optOp_assoc {α : Type} (op : α → α → Option α)
    (hAssoc : ∀ a b c, optBind (op a b) (fun ab => op ab c) =
      optBind (op b c) (fun bc => op a bc))
    (x y z : Option α) :
    optBind (optOp op x y) (fun xy => optOp op xy z) =
      optBind (optOp op y z) (fun yz => optOp op x yz) := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b =>
      cases z with
      | none => rfl
      | some c => dsimp only [optBind, optOp]; cases op b c <;> rfl
  | some a =>
    cases y with
    | none => cases z <;> rfl
    | some b =>
      cases z with
      | none => dsimp only [optBind, optOp]; cases op a b <;> rfl
      | some c =>
        dsimp only [optBind, optOp]
        have h := hAssoc a b c
        dsimp only [optBind] at h
        revert h
        cases h1 : op a b with
        | none =>
          intro h; dsimp only; dsimp only at h
          revert h
          cases h2 : op b c with
          | none => intro h; rfl
          | some _ => intro h; dsimp only; dsimp only at h; rw [← h]
        | some _ =>
          intro h; dsimp only; dsimp only at h
          revert h
          cases h2 : op b c with
          | none => intro h; dsimp only; dsimp only at h; rw [h]
          | some _ => intro h; dsimp only; dsimp only at h; rw [h]

/-- Fixed trie-merge recursion depth `7` (`6`-bit path length plus root node).
-/
@[expose] def resFuel : Nat := 7

/-- Depth-bounded pointwise partial merge of two `ResTrie α` trees up to `fuel`
levels. -/
@[expose] def resTrieMergeFuel {α : Type} (op : α → α →
    Option α) (fuel : Nat) (t1 t2 : ResTrie α) :
    Option (ResTrie α) :=
  @Nat.rec (fun _ => ResTrie α → ResTrie α → Option (ResTrie α))
    (fun a b =>
      match a with
      | .empty => some b
      | .node va la ra =>
        match b with
        | .empty => some (.node va la ra)
        | .node _ _ _ => none)
    (fun _ ih a b =>
      match a with
      | .empty => some b
      | .node va la ra =>
        match b with
        | .empty => some (.node va la ra)
        | .node vb lb rb =>
          match optOp op va vb with
          | none => none
          | some vm =>
            match ih la lb with
            | none => none
            | some lm =>
              match ih ra rb with
              | none => none
              | some rm => some (.node vm lm rm))
    fuel t1 t2

/-- Pointwise partial commutative merge on `ResTrie ResElem` at depth `resFuel`
(`7`). -/
@[expose] def resTrieMerge (t1 t2 : ResTrie ResElem) : Option (ResTrie ResElem)
    :=
  resTrieMergeFuel resMerge resFuel t1 t2

/-- Right identity of `.empty` for `resTrieMerge`. -/
theorem resTrieMerge_empty_right (t : ResTrie ResElem) : resTrieMerge t .empty =
    some t := by
  cases t <;> rfl

/-- Left identity of `.empty` for `resTrieMergeFuel` at arbitrary fuel. -/
theorem resTrieMerge_empty_left_fuel (fuel : Nat) (t : ResTrie ResElem) :
    resTrieMergeFuel resMerge fuel .empty t = some t := by
  cases fuel <;> rfl

private theorem resTrieMergeFuel_empty_right (fuel : Nat) (t : ResTrie ResElem)
    :
    resTrieMergeFuel resMerge fuel t .empty = some t := by
  cases fuel <;> cases t <;> rfl

private theorem resTrieMergeFuel_succ {α : Type} (op : α → α →
    Option α) (n : Nat)
    (va vb : Option α) (la ra lb rb : ResTrie α) :
    resTrieMergeFuel op (n + 1) (.node va la ra) (.node vb lb rb) =
      (match optOp op va vb with
       | none => none
       | some vm =>
         match resTrieMergeFuel op n la lb with
         | none => none
         | some lm =>
           match resTrieMergeFuel op n ra rb with
           | none => none
           | some rm => some (.node vm lm rm)) := rfl

private theorem resTrie_getBits_resTrieMergeFuel (fuel : Nat) (p : List Bool)
    (t1 t2 t : ResTrie ResElem)
    (hDepth : Nat.ble (p.length + 1) fuel = true)
    (hMerge : resTrieMergeFuel resMerge fuel t1 t2 = some t) :
    optOp resMerge (ResTrie.getBits p t1) (ResTrie.getBits p t2) =
      some (ResTrie.getBits p t) := by
  revert fuel t1 t2 t hDepth hMerge
  induction p with
  | nil =>
    intro fuel t1 t2 t hDepth hMerge
    cases fuel with
    | zero => exact False.elim (boolFalseNeTrue hDepth)
    | succ n =>
      cases t1 with
      | empty =>
        rw [resTrieMerge_empty_left_fuel (n + 1) t2] at hMerge
        injection hMerge with hEq
        rw [← hEq]
        rfl
      | node va la ra =>
        cases t2 with
        | empty =>
          rw [resTrieMergeFuel_empty_right (n + 1) (.node va la ra)] at hMerge
          injection hMerge with hEq
          rw [← hEq]
          dsimp only [ResTrie.getBits, List.foldr, optOp]
          cases va <;> rfl
        | node vb lb rb =>
          rw [resTrieMergeFuel_succ] at hMerge
          revert hMerge
          cases hV : optOp resMerge va vb with
          | none => intro hMerge; nomatch hMerge
          | some vm =>
            intro hMerge
            dsimp only at hMerge
            revert hMerge
            cases hL : resTrieMergeFuel resMerge n la lb with
            | none => intro hMerge; nomatch hMerge
            | some lm =>
              intro hMerge
              dsimp only at hMerge
              revert hMerge
              cases hR : resTrieMergeFuel resMerge n ra rb with
              | none => intro hMerge; nomatch hMerge
              | some rm =>
                intro hMerge
                injection hMerge with hT
                rw [← hT]
                exact hV
  | cons b bs ih =>
    intro fuel t1 t2 t hDepth hMerge
    cases fuel with
    | zero => exact False.elim (boolFalseNeTrue hDepth)
    | succ n =>
      cases t1 with
      | empty =>
        rw [resTrieMerge_empty_left_fuel (n + 1) t2] at hMerge
        injection hMerge with hEq
        rw [← hEq, resTrie_getBits_empty (b :: bs)]
        rfl
      | node va la ra =>
        cases t2 with
        | empty =>
          rw [resTrieMergeFuel_empty_right (n + 1) (.node va la ra)] at hMerge
          injection hMerge with hEq
          rw [← hEq, resTrie_getBits_empty (b :: bs)]
          dsimp only [optOp]
          cases ResTrie.getBits (b :: bs) (.node va la ra) <;> rfl
        | node vb lb rb =>
          rw [resTrieMergeFuel_succ] at hMerge
          revert hMerge
          cases hV : optOp resMerge va vb with
          | none => intro hMerge; nomatch hMerge
          | some vm =>
            intro hMerge
            dsimp only at hMerge
            revert hMerge
            cases hL : resTrieMergeFuel resMerge n la lb with
            | none => intro hMerge; nomatch hMerge
            | some lm =>
              intro hMerge
              dsimp only at hMerge
              revert hMerge
              cases hR : resTrieMergeFuel resMerge n ra rb with
              | none => intro hMerge; nomatch hMerge
              | some rm =>
                intro hMerge
                injection hMerge with hT
                rw [← hT]
                cases b with
                | false => exact ih n la lb lm hDepth hL
                | true => exact ih n ra rb rm hDepth hR

/-- Pointwise lookup characterization of `resTrieMerge` along any path strictly
shorter than `resFuel`. -/
theorem resTrie_getBits_resTrieMerge (p : List Bool) (t1 t2 t : ResTrie ResElem)
    (hDepth : Nat.ble (p.length + 1) resFuel = true)
    (hMerge : resTrieMerge t1 t2 = some t) :
    optOp resMerge (ResTrie.getBits p t1) (ResTrie.getBits p t2) =
      some (ResTrie.getBits p t) :=
  resTrie_getBits_resTrieMergeFuel resFuel p t1 t2 t hDepth hMerge

private theorem resTrie_modifyBits_cons {α : Type} (b : Bool) (bs : List Bool)
    (f : Option α → Option α) (t : ResTrie α) :
    ResTrie.modifyBits (b :: bs) f t =
      match b with
      | false =>
        .node (match t with | .empty => none | .node v _ _ => v)
          (ResTrie.modifyBits bs f
            (match t with | .empty => .empty | .node _ l _ => l))
          (match t with | .empty => .empty | .node _ _ r => r)
      | true =>
        .node (match t with | .empty => none | .node v _ _ => v)
          (match t with | .empty => .empty | .node _ l _ => l)
          (ResTrie.modifyBits bs f
            (match t with | .empty => .empty | .node _ _ r => r)) := rfl

/-- Singleton `ResTrie ResElem` storing `e` at `path`. -/
@[expose] def singleRes (path : List Bool) (e : ResElem) : ResTrie ResElem :=
  ResTrie.modifyBits path (fun _ => some e) .empty

/-- Merging `singleRes p elem` into a trie where `p` is absent inserts `elem` at
`p`. -/
theorem resTrieMergeFuel_singleRes_of_getBits_none (fuel : Nat) (p : List Bool)
    (elem : ResElem) (r : ResTrie ResElem)
    (hDepth : Nat.ble (p.length + 1) fuel = true)
    (hNone : ResTrie.getBits p r = none) :
    resTrieMergeFuel resMerge fuel (singleRes p elem) r =
      some (ResTrie.modifyBits p (fun _ => some elem) r) := by
  revert fuel r hDepth hNone
  induction p with
  | nil =>
    intro fuel r hDepth hNone
    cases fuel with
    | zero => exact False.elim (boolFalseNeTrue hDepth)
    | succ n =>
      cases r with
      | empty => rfl
      | node v lr rr =>
        dsimp only [ResTrie.getBits, List.foldr] at hNone
        rw [hNone]
        dsimp only [singleRes, ResTrie.modifyBits, List.foldr]
        rw [resTrieMergeFuel_succ]
        dsimp only [optOp]
        rw [resTrieMerge_empty_left_fuel n lr,
          resTrieMerge_empty_left_fuel n rr]
  | cons b bs ih =>
    intro fuel r hDepth hNone
    cases fuel with
    | zero => exact False.elim (boolFalseNeTrue hDepth)
    | succ n =>
      cases r with
      | empty =>
        dsimp only [singleRes]
        rw [resTrieMergeFuel_empty_right (n + 1)]
      | node v lr rr =>
        dsimp only [singleRes]
        rw [resTrie_modifyBits_cons, resTrie_modifyBits_cons]
        cases b with
        | false =>
          dsimp only
          rw [resTrieMergeFuel_succ]
          dsimp only [optOp]
          have hSub := ih n lr hDepth hNone
          dsimp only [singleRes] at hSub
          rw [hSub]
          dsimp only
          rw [resTrieMerge_empty_left_fuel n rr]
        | true =>
          dsimp only
          rw [resTrieMergeFuel_succ]
          dsimp only [optOp]
          rw [resTrieMerge_empty_left_fuel n lr]
          dsimp only
          have hSub := ih n rr hDepth hNone
          dsimp only [singleRes] at hSub
          rw [hSub]

private theorem resTrieMerge_comm_fuel (fuel : Nat) (t1 t2 : ResTrie ResElem) :
    resTrieMergeFuel resMerge fuel t1 t2 =
      resTrieMergeFuel resMerge fuel t2 t1 := by
  revert t1 t2
  induction fuel with
  | zero =>
    intro a b
    cases a <;> cases b <;> rfl
  | succ _ ih =>
    intro a b
    cases a with
    | empty => cases b <;> rfl
    | node va la ra =>
      cases b with
      | empty => rfl
      | node vb lb rb =>
        rw [resTrieMergeFuel_succ, resTrieMergeFuel_succ,
          optOp_comm resMerge resMerge_comm va vb, ih la lb, ih ra rb]

/-- Commutativity of `resTrieMerge`. -/
theorem resTrieMerge_comm (t1 t2 : ResTrie ResElem) :
    resTrieMerge t1 t2 = resTrieMerge t2 t1 :=
  resTrieMerge_comm_fuel resFuel t1 t2

private theorem resTrieMerge_assoc_fuel (fuel : Nat) (a b c ab abc : ResTrie
    ResElem)
    (hab : resTrieMergeFuel resMerge fuel a b = some ab)
    (habc : resTrieMergeFuel resMerge fuel ab c = some abc) :
    ∃ (bc : ResTrie ResElem),
      resTrieMergeFuel resMerge fuel b c = some bc ∧
      resTrieMergeFuel resMerge fuel a bc = some abc := by
  revert a b c ab abc
  induction fuel with
  | zero =>
    intro a b c ab abc hab habc
    cases a with
    | empty => injection hab with he; rw [← he] at habc; exact ⟨abc, habc, rfl⟩
    | node _ _ _ =>
      cases b with
      | empty => injection hab with he; rw [← he] at habc; exact ⟨c, rfl, habc⟩
      | node _ _ _ => nomatch hab
  | succ fuel' ih =>
    intro a b c ab abc hab habc
    cases a with
    | empty => injection hab with he; rw [← he] at habc; exact ⟨abc, habc, rfl⟩
    | node va la ra =>
      cases b with
      | empty => injection hab with he; rw [← he] at habc; exact ⟨c, rfl, habc⟩
      | node vb lb rb =>
        cases c with
        | empty =>
          cases ab with
          | empty =>
            rw [resTrieMergeFuel_succ] at hab
            revert hab
            cases hv : optOp resMerge va vb with
            | none => intro hab; nomatch hab
            | some _ =>
              intro hab; dsimp only at hab
              revert hab
              cases hl : resTrieMergeFuel resMerge fuel' la lb with
              | none => intro hab; nomatch hab
              | some _ =>
                intro hab; dsimp only at hab
                revert hab
                cases hr : resTrieMergeFuel resMerge fuel' ra rb with
                | none => intro hab; nomatch hab
                | some _ => intro hab; nomatch hab
          | node _ _ _ =>
            injection habc with he; rw [← he]; exact ⟨.node vb lb rb, rfl, hab⟩
        | node vc lc rc =>
          rw [resTrieMergeFuel_succ] at hab
          revert hab
          cases hv12 : optOp resMerge va vb with
          | none => intro hab; nomatch hab
          | some v12 =>
            intro hab; dsimp only at hab
            revert hab
            cases hl12 : resTrieMergeFuel resMerge fuel' la lb with
            | none => intro hab; nomatch hab
            | some l12 =>
              intro hab; dsimp only at hab
              revert hab
              cases hr12 : resTrieMergeFuel resMerge fuel' ra rb with
              | none => intro hab; nomatch hab
              | some r12 =>
                intro hab; dsimp only at hab
                injection hab with hAbEq
                rw [← hAbEq] at habc
                rw [resTrieMergeFuel_succ] at habc
                revert habc
                cases hv123 : optOp resMerge v12 vc with
                | none => intro habc; nomatch habc
                | some v123 =>
                  intro habc; dsimp only at habc
                  revert habc
                  cases hl123 : resTrieMergeFuel resMerge fuel' l12 lc with
                  | none => intro habc; nomatch habc
                  | some l123 =>
                    intro habc; dsimp only at habc
                    revert habc
                    cases hr123 : resTrieMergeFuel resMerge fuel' r12 rc with
                    | none => intro habc; nomatch habc
                    | some r123 =>
                      intro habc; dsimp only at habc
                      injection habc with hAbcEq
                      have hva := optOp_assoc resMerge resMerge_assoc va vb vc
                      dsimp only [optBind] at hva
                      rw [hv12] at hva; dsimp only at hva; rw [hv123] at hva
                      revert hva
                      cases hv23 : optOp resMerge vb vc with
                      | none => intro hva; nomatch hva
                      | some v23 =>
                        intro hva; dsimp only at hva
                        cases ih la lb lc l12 l123 hl12 hl123 with
                        | intro l23 hl23 =>
                          cases ih ra rb rc r12 r123 hr12 hr123 with
                          | intro r23 hr23 =>
                            refine ⟨.node v23 l23 r23, ?_, ?_⟩
                            · rw [resTrieMergeFuel_succ, hv23]
                              dsimp only
                              rw [hl23.1]
                              dsimp only
                              rw [hr23.1]
                            · rw [resTrieMergeFuel_succ, ← hva]
                              dsimp only
                              rw [hl23.2]
                              dsimp only
                              rw [hr23.2]
                              dsimp only
                              exact congrArg some hAbcEq

/-- Left-to-right associativity of `resTrieMerge`: `(a • b) • c = some abc`
yields `b • c = some bc` with `a • bc = some abc`. -/
theorem resTrieMerge_assoc (a b c ab abc : ResTrie ResElem)
    (hab : resTrieMerge a b = some ab) (habc : resTrieMerge ab c = some abc) :
    ∃ (bc : ResTrie ResElem), resTrieMerge b c = some bc ∧
      resTrieMerge a bc = some abc :=
  resTrieMerge_assoc_fuel resFuel a b c ab abc hab habc

/-- Right-to-left associativity of `resTrieMerge`: `a • (b • c) = some abc`
yields `a • b = some ab` with `ab • c = some abc`. -/
theorem resTrieMerge_assoc_rl (a b c bc abc : ResTrie ResElem)
    (hbc : resTrieMerge b c = some bc) (habc : resTrieMerge a bc = some abc) :
    ∃ (ab : ResTrie ResElem), resTrieMerge a b = some ab ∧
      resTrieMerge ab c = some abc := by
  have hcb : resTrieMerge c b = some bc := Eq.trans (resTrieMerge_comm c b) hbc
  have hcb_a : resTrieMerge bc a = some abc :=
    Eq.trans (resTrieMerge_comm bc a) habc
  cases resTrieMerge_assoc c b a bc abc hcb hcb_a with
  | intro ba hba =>
    exact ⟨ba, Eq.trans (resTrieMerge_comm a b) hba.1,
      Eq.trans (resTrieMerge_comm ba c) hba.2⟩

/-- Extension order `r1 ≼ r2` on resource tries (`∃ frame, resTrieMerge r1 frame
= some r2`). -/
structure ResTrieSub (r1 r2 : ResTrie ResElem) : Prop where
  holds : ∃ (frame : ResTrie ResElem), resTrieMerge r1 frame = some r2

/-- Reflexivity of `ResTrieSub`. -/
theorem resTrieSub_refl (r : ResTrie ResElem) : ResTrieSub r r :=
  ResTrieSub.mk ⟨.empty, resTrieMerge_empty_right r⟩

/-- Transitivity of `ResTrieSub`. -/
theorem resTrieSub_trans (a b c : ResTrie ResElem) (hab : ResTrieSub a b) (hbc
    : ResTrieSub b c) :
    ResTrieSub a c := by
  cases hab.holds with
  | intro f1 hf1 =>
    cases hbc.holds with
    | intro f2 hf2 =>
      cases resTrieMerge_assoc a f1 f2 b c hf1 hf2 with
      | intro f hf => exact ResTrieSub.mk ⟨f, hf.2⟩

/-- Upward-closed predicate over `(View, ResTrie ResElem)` monotonic under
`ViewLe` and `ResTrieSub`. -/
structure VProp : Type where
  holds : View → ResTrie ResElem → Prop
  upClosed : ∀ (v1 v2 : View) (r1 r2 : ResTrie ResElem),
    ViewLe v1 v2 → ResTrieSub r1 r2 → holds v1 r1 → holds v2 r2

/-- Semantic entailment `P ⊢ Q` pointwise across all `(View, ResTrie ResElem)`
pairs. -/
structure ventails (P Q : VProp) : Prop where
  imp : ∀ (v : View) (r : ResTrie ResElem), P.holds v r → Q.holds v r

/-- Trivial unit `VProp` holding on every view and resource trie. -/
@[expose] def vemp : VProp where
  holds _ _ := True
  upClosed _ _ _ _ _ _ h := h

/-- Ownership assertion `vowns rt` holding whenever `ResTrieSub rt tot`. -/
@[expose] def vowns (rt : ResTrie ResElem) : VProp where
  holds _ tot := ResTrieSub rt tot
  upClosed _ _ _ _ _ hSub hOwns := resTrieSub_trans rt _ _ hOwns hSub

/-- Monotonic view assertion requiring `minSteps ≤ viewGet v 0`. -/
@[expose] def vMinStep (minSteps : Nat) : VProp where
  holds v _ := Nat.ble minSteps (viewGet v 0) = true
  upClosed v1 v2 _ _ hv _ h :=
    (viewLe_trans [minSteps] v1 v2
      (ViewLe.mk (fun i => match i with | 0 => h | _ + 1 => rfl)) hv).leAt 0

/-- Separating conjunction `P ∗ Q` splitting `r` via `resTrieMerge r1 r2 = some
r`. -/
@[expose] def vsep (P Q : VProp) : VProp where
  holds v r := ∃ (r1 r2 : ResTrie ResElem), resTrieMerge r1 r2 = some r ∧
    P.holds v r1 ∧ Q.holds v r2
  upClosed v1 v2 r1 r2 hv hr hSep := by
    cases hSep with
    | intro a ha =>
      cases ha with
      | intro b hab =>
        cases hr.holds with
        | intro f hf =>
          cases resTrieMerge_assoc a b f r1 r2 hab.1 hf with
          | intro bf hbf =>
            exact ⟨a, bf, hbf.2,
              P.upClosed v1 v2 a a hv (resTrieSub_refl a) hab.2.1,
              Q.upClosed v1 v2 b bf hv (ResTrieSub.mk ⟨f, hbf.1⟩) hab.2.2⟩

/-- Commutativity of `vsep`. -/
theorem vsep_comm (P Q : VProp) : ventails (vsep P Q) (vsep Q P) :=
  ventails.mk (fun _ _ h => by
    cases h with
    | intro r1 hr =>
      cases hr with
      | intro r2 hc =>
        exact ⟨r2, r1, Eq.trans (resTrieMerge_comm r2 r1) hc.1, hc.2.2, hc.2.1⟩)

/-- Left-to-right associativity `(P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)`. -/
theorem vsep_assoc_lr (P Q R : VProp) : ventails (vsep (vsep P Q) R) (vsep P
    (vsep Q R)) :=
  ventails.mk (fun _ _ h => by
    cases h with
    | intro r12 hr =>
      cases hr with
      | intro r3 hc =>
        cases hc.2.1 with
        | intro r1 hr1 =>
          cases hr1 with
          | intro r2 hc1 =>
            cases resTrieMerge_assoc r1 r2 r3 r12 _ hc1.1 hc.1 with
            | intro r23 hr23 =>
              exact ⟨r1, r23, hr23.2, hc1.2.1, ⟨r2, r3, hr23.1, hc1.2.2,
                hc.2.2⟩⟩)

/-- Right-to-left associativity `P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R`. -/
theorem vsep_assoc_rl (P Q R : VProp) : ventails (vsep P (vsep Q R)) (vsep
    (vsep P Q) R) :=
  ventails.mk (fun v r h =>
    (vsep_comm R (vsep P Q)).imp v r
      ((vsep_assoc_lr R P Q).imp v r
        ((vsep_comm Q (vsep R P)).imp v r
          ((vsep_assoc_lr Q R P).imp v r
            ((vsep_comm P (vsep Q R)).imp v r h)))))

/-- Combined resource trie owning both `debtPath ↦ .debt ord` and backing
`poolPath ↦ .pool ord`. -/
@[expose] def ordDebtTree (ord : CnfOrd) : ResTrie ResElem :=
  ResTrie.modifyBits debtPath (fun _ => some (.debt ord)) (singleRes poolPath
    (.pool ord))

/-- Decomposes `ordDebtTree ord` as the disjoint merge of `singleRes debtPath
(.debt ord)` and `singleRes poolPath (.pool ord)`. -/
theorem ordDebtTree_decomp (ord : CnfOrd) :
    resTrieMerge (singleRes debtPath (.debt ord)) (singleRes poolPath (.pool
      ord)) =
      some (ordDebtTree ord) :=
  resTrieMergeFuel_singleRes_of_getBits_none resFuel debtPath (.debt ord)
    (singleRes poolPath (.pool ord)) rfl rfl

/-- Ownership of pool ordinal capacity `cap` at `poolPath`. -/
@[expose] def poolBackingProp (cap : CnfOrd) : VProp :=
  vowns (singleRes poolPath (.pool cap))

/-- Ownership of amortized ordinal debt `ord` together with its backing
`poolPath` share (`ordDebtTree ord`). -/
@[expose] def ordDebtProp (ord : CnfOrd) : VProp :=
  vowns (ordDebtTree ord)

/-- Exclusive ownership token for checked-out loan `lid` at scope `scopeId` with
tracked value `val`. -/
@[expose] def checkedOutLoanProp (lid : Pos4) (scopeId val : Nat) : VProp :=
  vowns (singleRes (checkedLoanPath lid) (.checkedOutLoan scopeId val))

/-- Duplicable capability assertion witnessing existence of spatial cell `cid`.
-/
@[expose] def cellCapProp (cid : Pos4) : VProp :=
  vowns (singleRes (cellPath cid) (.cell .capOnly))

/-- Exclusive authority assertion tracking value `val` at spatial cell `cid`. -/
@[expose] def cellAuthProp (cid : Pos4) (val : Nat) : VProp :=
  vowns (singleRes (cellPath cid) (.cell (.authOnly val)))

/-- Looking up `p` in `singleRes p elem` returns `some elem`. -/
theorem singleRes_getBits_same (p : List Bool) (elem : ResElem) :
    ResTrie.getBits p (singleRes p elem) = some elem :=
  resTrie_getBits_modifyBits_same p (fun _ => some elem) .empty

/-- Looking up `q` in `singleRes p elem` returns `none` for distinct
equal-length paths `p ≠ q`. -/
theorem singleRes_getBits_ne (p q : List Bool) (elem : ResElem)
    (hLen : p.length = q.length) (hNe : listBoolBeq p q = false) :
    ResTrie.getBits q (singleRes p elem) = none :=
  Eq.trans (resTrie_getBits_modifyBits_ne p q hLen hNe (fun _ => some elem)
    .empty)
    (resTrie_getBits_empty q)

/-- Updates index `0` of view `v` to `newStep`. -/
@[expose] def bumpView0 (v : View) (newStep : Nat) : View :=
  match v with
  | [] => [newStep]
  | _ :: tl => newStep :: tl

/-- Reading index `0` after `bumpView0 v newStep` yields `newStep`. -/
theorem viewGet_bumpView0_zero (v : View) (newStep : Nat) :
    viewGet (bumpView0 v newStep) 0 = newStep := by
  cases v <;> rfl

/-- `bumpView0 v newStep` advances `v` under `ViewLe` whenever `viewGet v 0 ≤
newStep`. -/
theorem viewLe_bumpView0 (v : View) (newStep : Nat)
    (hLe : Nat.ble (viewGet v 0) newStep = true) :
    ViewLe v (bumpView0 v newStep) :=
  ViewLe.mk (fun i => by
    cases v with
    | nil =>
      cases i with
      | zero => rfl
      | succ _ => rfl
    | cons x tl =>
      cases i with
      | zero => exact hLe
      | succ k => exact natBle_refl (viewGet tl k))

/-- Eliminates a left `vemp` unit from `(vsep vemp F).holds v r`. -/
theorem vsep_vemp_elim (v : View) (F : VProp) (r : ResTrie ResElem)
    (h : (vsep vemp F).holds v r) : F.holds v r := by
  cases h with
  | intro r1 hr =>
    cases hr with
    | intro r2 hc =>
      exact F.upClosed v v r2 r (viewLe_refl v)
        (ResTrieSub.mk ⟨r1, Eq.trans (resTrieMerge_comm r2 r1) hc.1⟩) hc.2.2

/-- Introduces a left `vemp` unit into `(vsep vemp F).holds v r`. -/
theorem vsep_vemp_intro (v : View) (F : VProp) (r : ResTrie ResElem)
    (hF : F.holds v r) : (vsep vemp F).holds v r :=
  ⟨.empty, r, resTrieMerge_empty_left_fuel resFuel r, True.intro, hF⟩

/-- Weakens `(vsep P F).holds v r` to `F.holds v r` by upward closure. -/
theorem vsep_drop_left (P F : VProp) (v : View) (r : ResTrie ResElem)
    (h : (vsep P F).holds v r) : F.holds v r := by
  cases h with
  | intro r1 hr =>
    cases hr with
    | intro r2 hc =>
      exact F.upClosed v v r2 r (viewLe_refl v)
        (ResTrieSub.mk ⟨r1, Eq.trans (resTrieMerge_comm r2 r1) hc.1⟩) hc.2.2

/-- Merging `.capOnly` and `.authOnly val` at `cellPath cid` yields `.capAndAuth
val`. -/
theorem singleRes_cell_cap_auth_merge (cid : Pos4) (val : Nat) :
    resTrieMerge (singleRes (cellPath cid) (.cell .capOnly))
      (singleRes (cellPath cid) (.cell (.authOnly val))) =
      some (singleRes (cellPath cid) (.cell (.capAndAuth val))) := by
  cases cid with
  | mk b0 r1 =>
    cases r1 with
    | mk b1 r2 =>
      cases r2 with
      | mk b2 b3 =>
        cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

/-- Replaces `.capAndAuth oldVal` with `.capAndAuth newVal` across an arbitrary
compatible resource frame `rRest`. -/
theorem resTrieMergeFuel_singleRes_capAndAuth_swap (fuel : Nat) (p : List Bool)
    (oldVal newVal : Nat) (rRest rIn : ResTrie ResElem)
    (hDepth : Nat.ble (p.length + 1) fuel = true)
    (hIn : resTrieMergeFuel resMerge fuel (singleRes p (.cell (.capAndAuth
      oldVal))) rRest = some rIn) :
    resTrieMergeFuel resMerge fuel (singleRes p (.cell (.capAndAuth newVal)))
      rRest =
      some (ResTrie.modifyBits p (fun _ => some (.cell (.capAndAuth newVal)))
        rIn) := by
  revert fuel rRest rIn hDepth hIn
  induction p with
  | nil =>
    intro fuel rRest rIn hDepth hIn
    cases fuel with
    | zero => exact False.elim (boolFalseNeTrue hDepth)
    | succ n =>
      cases rRest with
      | empty =>
        dsimp only [singleRes, ResTrie.modifyBits, List.foldr] at hIn
        rw [resTrieMergeFuel_empty_right (n + 1)] at hIn
        injection hIn with hEq
        rw [← hEq]
        rfl
      | node vr lr rr =>
        dsimp only [singleRes, ResTrie.modifyBits, List.foldr] at hIn
        rw [resTrieMergeFuel_succ, resTrieMerge_empty_left_fuel n lr,
          resTrieMerge_empty_left_fuel n rr] at hIn
        dsimp only [singleRes, ResTrie.modifyBits, List.foldr]
        rw [resTrieMergeFuel_succ, resTrieMerge_empty_left_fuel n lr,
          resTrieMerge_empty_left_fuel n rr]
        cases vr with
        | none =>
          dsimp only [optOp] at hIn
          injection hIn with hEq
          rw [← hEq]
          rfl
        | some er =>
          cases er with
          | pool _ | debt _ | checkedOutLoan _ _ =>
            dsimp only [optOp, resMerge] at hIn; nomatch hIn
          | cell cf =>
            cases cf with
            | authOnly _ | capAndAuth _ =>
              dsimp only [optOp, resMerge, cellFragMerge] at hIn; nomatch hIn
            | capOnly =>
              dsimp only [optOp, resMerge, cellFragMerge] at hIn
              injection hIn with hEq
              rw [← hEq]
              rfl
  | cons b bs ih =>
    intro fuel rRest rIn hDepth hIn
    cases fuel with
    | zero => exact False.elim (boolFalseNeTrue hDepth)
    | succ n =>
      cases rRest with
      | empty =>
        rw [resTrieMergeFuel_empty_right (n + 1)] at hIn
        injection hIn with hEq
        rw [← hEq]
        rw [resTrieMergeFuel_empty_right (n + 1)]
        dsimp only [singleRes]
        have hIdem : ∀ (q : List Bool) (e1 e2 : ResElem),
            ResTrie.modifyBits q (fun _ => some e2) (ResTrie.modifyBits q (fun
              _ => some e1) .empty) =
              ResTrie.modifyBits q (fun _ => some e2) .empty := by
          intro q e1 e2
          induction q with
          | nil => rfl
          | cons qb qbs ihQ =>
            rw [resTrie_modifyBits_cons, resTrie_modifyBits_cons,
              resTrie_modifyBits_cons]
            cases qb with
            | false => dsimp only; rw [ihQ]
            | true => dsimp only; rw [ihQ]
        rw [hIdem (b :: bs) (.cell (.capAndAuth oldVal)) (.cell (.capAndAuth
          newVal))]
      | node vr lr rr =>
        dsimp only [singleRes] at hIn
        rw [resTrie_modifyBits_cons] at hIn
        dsimp only [singleRes]
        rw [resTrie_modifyBits_cons]
        cases b with
        | false =>
          dsimp only at hIn
          rw [resTrieMergeFuel_succ] at hIn
          dsimp only [optOp] at hIn
          rw [resTrieMerge_empty_left_fuel n rr] at hIn
          cases hSubIn : resTrieMergeFuel resMerge n (singleRes bs (.cell
            (.capAndAuth oldVal))) lr with
          | none =>
            dsimp only [singleRes] at hSubIn
            rw [hSubIn] at hIn
            nomatch hIn
          | some lmIn =>
            have hSubIn' := hSubIn
            dsimp only [singleRes] at hSubIn'
            rw [hSubIn'] at hIn
            dsimp only at hIn
            injection hIn with hEqR
            rw [← hEqR]
            dsimp only
            rw [resTrieMergeFuel_succ]
            dsimp only [optOp]
            have hSwap := ih n lr lmIn hDepth hSubIn
            dsimp only [singleRes] at hSwap
            rw [hSwap]
            dsimp only
            rw [resTrieMerge_empty_left_fuel n rr]
            rfl
        | true =>
          dsimp only at hIn
          rw [resTrieMergeFuel_succ] at hIn
          dsimp only [optOp] at hIn
          rw [resTrieMerge_empty_left_fuel n lr] at hIn
          dsimp only at hIn
          cases hSubIn : resTrieMergeFuel resMerge n (singleRes bs (.cell
            (.capAndAuth oldVal))) rr with
          | none =>
            dsimp only [singleRes] at hSubIn
            rw [hSubIn] at hIn
            nomatch hIn
          | some rmIn =>
            have hSubIn' := hSubIn
            dsimp only [singleRes] at hSubIn'
            rw [hSubIn'] at hIn
            injection hIn with hEqR
            rw [← hEqR]
            dsimp only
            rw [resTrieMergeFuel_succ]
            dsimp only [optOp]
            rw [resTrieMerge_empty_left_fuel n lr]
            dsimp only
            have hSwap := ih n rr rmIn hDepth hSubIn
            dsimp only [singleRes] at hSwap
            rw [hSwap]
            rfl

end Anneal.WavefrontReclaim

end
